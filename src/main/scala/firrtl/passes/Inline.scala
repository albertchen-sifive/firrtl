// See LICENSE for license details.

package firrtl
package passes

import firrtl.ir._
import firrtl.Mappers._
import firrtl.annotations._
import firrtl.analyses.InstanceGraph
import firrtl.stage.RunFirrtlTransformAnnotation
import firrtl.options.RegisteredTransform
import scopt.OptionParser

// Datastructures
import scala.collection.mutable

/** Indicates that something should be inlined */
case class InlineAnnotation(target: Named) extends SingleTargetAnnotation[Named] {
  def duplicate(n: Named) = InlineAnnotation(n)
}

/** Inline instances as indicated by existing [[InlineAnnotation]]s
  * @note Only use on legal Firrtl. Specifically, the restriction of instance loops must have been checked, or else this
  * pass can infinitely recurse.
  */
class InlineInstances extends Transform with RegisteredTransform {
   def inputForm = LowForm
   def outputForm = LowForm
   private [firrtl] val inlineDelim: String = "_"

  def addOptions(parser: OptionParser[AnnotationSeq]): Unit = parser
    .opt[Seq[String]]("inline")
    .abbr("fil")
    .valueName ("<circuit>[.<module>[.<instance>]][,..],")
    .action( (x, c) => {
              val newAnnotations = x.map { value =>
                value.split('.') match {
                  case Array(circuit) =>
                    InlineAnnotation(CircuitName(circuit))
                  case Array(circuit, module) =>
                    InlineAnnotation(ModuleName(module, CircuitName(circuit)))
                  case Array(circuit, module, inst) =>
                    InlineAnnotation(ComponentName(inst, ModuleName(module, CircuitName(circuit))))
                }
              }
              c ++ newAnnotations :+ RunFirrtlTransformAnnotation(new InlineInstances) } )
    .text(
      """Inline one or more module (comma separated, no spaces) module looks like "MyModule" or "MyModule.myinstance""")

   private def collectAnns(circuit: Circuit, anns: Iterable[Annotation]): (Set[ModuleName], Set[ComponentName]) =
     anns.foldLeft(Set.empty[ModuleName], Set.empty[ComponentName]) {
       case ((modNames, instNames), ann) => ann match {
         case InlineAnnotation(CircuitName(c)) =>
           (circuit.modules.collect {
             case Module(_, name, _, _) if name != circuit.main => ModuleName(name, CircuitName(c))
           }.toSet, instNames)
         case InlineAnnotation(ModuleName(mod, cir)) => (modNames + ModuleName(mod, cir), instNames)
         case InlineAnnotation(ComponentName(com, mod)) => (modNames, instNames + ComponentName(com, mod))
         case _ => (modNames, instNames)
       }
     }

   def execute(state: CircuitState): CircuitState = {
     // TODO Add error check for more than one annotation for inlining
     val (modNames, instNames) = collectAnns(state.circuit, state.annotations)
     if (modNames.nonEmpty || instNames.nonEmpty) {
       run(state.circuit, modNames, instNames, state.annotations)
     } else {
       state
     }
   }

   // Checks the following properties:
   // 1) All annotated modules exist
   // 2) All annotated modules are InModules (can be inlined)
   // 3) All annotated instances exist, and their modules can be inline
   def check(c: Circuit, moduleNames: Set[ModuleName], instanceNames: Set[ComponentName]): Unit = {
      val errors = mutable.ArrayBuffer[PassException]()
      val moduleMap = new InstanceGraph(c).moduleMap
      def checkExists(name: String): Unit =
         if (!moduleMap.contains(name))
            errors += new PassException(s"Annotated module does not exist: $name")
      def checkExternal(name: String): Unit = moduleMap(name) match {
            case m: ExtModule => errors += new PassException(s"Annotated module cannot be an external module: $name")
            case _ =>
      }
      def checkInstance(cn: ComponentName): Unit = {
         var containsCN = false
         def onStmt(name: String)(s: Statement): Statement = {
            s match {
               case WDefInstance(_, inst_name, module_name, tpe) =>
                  if (name == inst_name) {
                     containsCN = true
                     checkExternal(module_name)
                  }
               case _ =>
            }
            s map onStmt(name)
         }
         onStmt(cn.name)(moduleMap(cn.module.name).asInstanceOf[Module].body)
         if (!containsCN) errors += new PassException(s"Annotated instance does not exist: ${cn.module.name}.${cn.name}")
      }

      moduleNames.foreach{mn => checkExists(mn.name)}
      if (errors.nonEmpty) throw new PassExceptions(errors)
      moduleNames.foreach{mn => checkExternal(mn.name)}
      if (errors.nonEmpty) throw new PassExceptions(errors)
      instanceNames.foreach{cn => checkInstance(cn)}
      if (errors.nonEmpty) throw new PassExceptions(errors)
   }


  def run(c: Circuit, modsToInline: Set[ModuleName], instsToInline: Set[ComponentName], annos: AnnotationSeq): CircuitState = {
    def getInstancesOf(c: Circuit, modules: Set[String]): Set[String] =
      c.modules.foldLeft(Set[String]()) { (set, d) =>
        d match {
          case e: ExtModule => set
          case m: Module =>
            val instances = mutable.HashSet[String]()
            def findInstances(s: Statement): Statement = s match {
              case WDefInstance(info, instName, moduleName, instTpe) if modules.contains(moduleName) =>
                instances += m.name + "." + instName
                s
              case sx => sx map findInstances
            }
            findInstances(m.body)
            instances.toSet ++ set
        }
      }

    // Check annotations and circuit match up
    check(c, modsToInline, instsToInline)
    val flatModules = modsToInline.map(m => m.name)
    val flatInstances = instsToInline.map(i => i.module.name + "." + i.name) ++ getInstancesOf(c, flatModules)
    val iGraph = new InstanceGraph(c)
    val namespaceMap = collection.mutable.Map[String, Namespace]()

    def getInstMap(mod: DefModule): Map[String, String] = mod match {
      case m: Module => getInstMapBody(m.body)
      case _ => Map.empty[String, String]
    }
    def getInstMapBody(stmt: Statement): Map[String, String] = {
      val instMap = mutable.Map.empty[String, String]
      def onStmt(s: Statement): Statement = s.map(onStmt) match {
        case wDef@ WDefInstance(_, instName, modName, _) =>
          instMap += (instName -> modName)
          wDef
        case other => other
      }
      onStmt(stmt)
      instMap.toMap
    }

    /** Add a prefix to all declarations updating a [[Namespace]] and appending to a [[RenameMap]] */
    def appendNamePrefix(
      instMap: Map[String, String],
      currentModule: IsModule,
      parentModule: IsModule,
      prefix: String,
      ns: Namespace,
      renames: RenameMap)(name:String): String = {
      if (prefix.nonEmpty && !ns.tryName(prefix + name))
        throw new Exception(s"Inlining failed. Inlined name '${prefix + name}' already exists")
      if (instMap.contains(name)) {
        val inst = currentModule.instOf(name, instMap(name))
        renames.record(inst, parentModule.instOf(prefix + name, instMap(name)))
      } else {
        renames.record(currentModule.ref(name), parentModule.ref(prefix + name))
      }
      prefix + name
    }

    /** Modify all references */
    def appendRefPrefix(
      instMap: Map[String, String],
      currentModule: IsModule,
      parentModule: IsModule,
      renames: RenameMap)(e: Expression): Expression = e match {
      case wsf@ WSubField(wr@ WRef(ref, _, InstanceKind, _), field, tpe, gen) =>
        val inst = currentModule.instOf(ref, instMap(ref))
        val port = inst.ref(field)
        (renames.get(port), renames.get(inst)) match {
          case (Some(Seq(p)), _)              =>
            p match {
              case ref@ ReferenceTarget(_, _, p, r, Nil) if ref.asPath == parentModule.asPath => WRef(r, tpe, WireKind, gen)
              case ref@ ReferenceTarget(_, _, p, f, Nil) if ref.asPath.dropRight(1) == parentModule.asPath =>
                val (TargetToken.Instance(r), _) = p.last
                wsf.copy(expr = wr.copy(name = r), name = f)
            }
          case (None,           Some(Seq(i))) => wsf.map(appendRefPrefix(instMap, currentModule, parentModule, renames))
          case (None,           None)         => wsf
        }
      case wr@ WRef(name, _, _, _) =>
        val comp = currentModule.ref(name) //ComponentName(name, currentModule)
        renames.get(comp).orElse(Some(Seq(comp))) match {
          case Some(Seq(car: InstanceTarget)) => wr.copy(name=car.instance)
          case Some(Seq(car: ReferenceTarget)) => wr.copy(name=car.ref)
          case c@ Some(_)       => throw new PassException(
            s"Inlining found mlutiple renames for ref $comp -> $c. This should be impossible...")
        }
      case ex => ex.map(appendRefPrefix(instMap, currentModule, parentModule, renames))
    }

    def onStmt(currentModule: IsModule, renames: RenameMap)(s: Statement): Statement = {
      val currentModuleName = currentModule match {
        case m: ModuleTarget => m.module
        case i: InstanceTarget => i.ofModule
      }
      val ns = namespaceMap.getOrElseUpdate(currentModuleName, Namespace(iGraph.moduleMap(currentModuleName)))
      val instMap = getInstMap(iGraph.moduleMap(currentModuleName))
      s match {
        case wDef@ WDefInstance(_, instName, modName, _) if flatInstances.contains(s"${currentModuleName}.$instName") =>
          val toInline = iGraph.moduleMap(modName) match {
            case m: ExtModule => throw new PassException(s"Cannot inline external module ${m.name}")
            case m: Module    => m
          }

          val ports = toInline.ports.map(p => DefWire(p.info, p.name, p.tpe))

          val subRenames = RenameMap()
          val currentInst = currentModule.instOf(instName, modName)
          val bodyx = Block(ports :+ toInline.body) map onStmt(currentInst, subRenames)

          val names = "" +: Uniquify
            .enumerateNames(Uniquify.stmtToType(bodyx)(NoInfo, ""))
            .map(_.mkString("_"))

          /** The returned prefix will not be "prefix unique". It may be the same as other existing prefixes in the namespace.
            * However, prepending this prefix to all inlined components is guaranteed to not conflict with this module's
            * namespace. To make it prefix unique, this requires expanding all names in the namespace to include their
            * prefixes before calling findValidPrefix.
            */
          val safePrefix = Uniquify.findValidPrefix(instName + inlineDelim, names, ns.cloneUnderlying - instName)

          renames.delete(currentModule.instOf(instName, modName))

          val subSubRenames = RenameMap()
          def recName(s: Statement): Statement = s.map(recName).map(appendNamePrefix(getInstMapBody(bodyx), currentInst, currentModule, safePrefix, ns, subSubRenames))
          def recRef(s: Statement): Statement = s.map(recRef).map(appendRefPrefix(getInstMapBody(bodyx), currentInst, currentModule, subSubRenames))

          val renamedBody = bodyx
            .map(recName)
            .map(recRef)

          val seen = mutable.HashSet.empty[IsComponent]
          subRenames.underlying.foreach { case (from: IsComponent, tos) =>
            tos.foreach { case to: IsComponent =>
              seen += to
              subSubRenames.get(to).getOrElse(Seq(to)).foreach { case f: IsComponent =>
                renames.record(from, f)
              }
            }
          }
          subSubRenames.underlying.foreach {
            case (from: IsComponent, tos) if !seen.contains(from) =>
              subSubRenames.get(from).foreach(_.foreach { to =>
                renames.record(from, to)
              })
            case _ =>
          }

          renamedBody
        case sx => sx
            .map(appendRefPrefix(instMap, currentModule, currentModule, renames))
            .map(onStmt(currentModule, renames))
      }
    }

    val renames = RenameMap()
    renames.setCircuit(c.main)
    val flatCircuit = c.copy(modules = c.modules.flatMap {
      case m if flatModules.contains(m.name) => None
      case m                                 => Some(m.map(onStmt(ModuleName(m.name, CircuitName(c.main)), renames)))
    })

    CircuitState(flatCircuit, LowForm, annos, Some(renames))
  }
}
