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
      currentModule: IsModule,
      prefix: String,
      ns: Namespace,
      renames: mutable.HashMap[ReferenceTarget, ReferenceTarget])(s: Statement): Statement = {
        def onName(name: String) = {
          if (prefix.nonEmpty && !ns.tryName(prefix + name))
          throw new Exception(s"Inlining failed. Inlined name '${prefix + name}' already exists")
          renames += (currentModule.ref(name) -> currentModule.ref(prefix + name))
          prefix + name
        }
        s.map(onName).map(appendNamePrefix(currentModule, prefix, ns, renames))
      }

    /** Modify all references */
    def appendRefPrefix(
      currentModule: IsModule,
      renames: mutable.HashMap[ReferenceTarget, ReferenceTarget])(s: Statement): Statement = {
        def onExpr(e: Expression): Expression = e match {
          case wr@ WRef(name, _, _, _) =>
            val comp = currentModule.ref(name) //ComponentName(name, currentModule)
            renames.get(comp) match {
              case Some(car: ReferenceTarget) => wr.copy(name=car.ref)
              case None => wr
            }
          case ex => ex.map(onExpr)
        }
        s.map(onExpr).map(appendRefPrefix(currentModule, renames))
      }

    def fixupRefs(
      instMap: Map[String, String],
      currentModule: IsModule,
      renames: RenameMap)(e: Expression): Expression = e match {
      case wsf@ WSubField(wr@ WRef(ref, _, InstanceKind, _), field, tpe, gen) =>
        val inst = currentModule.instOf(ref, instMap(ref))
        val port = inst.ref(field)
        renames.get(port) match {
          case Some(Seq(p)) =>
            p match {
              case ReferenceTarget(_, _, Seq((TargetToken.Instance(r), TargetToken.OfModule(_))), f, Nil) =>
                wsf.copy(expr = wr.copy(name = r), name = f)
              case ReferenceTarget(_, _, Nil, r, Nil) => WRef(r, tpe, WireKind, gen)
            }
          case None => wsf
        }
      case wr@ WRef(name, _, _, _) =>
        val comp = currentModule.ref(name) //ComponentName(name, currentModule)
        renames.get(comp).getOrElse(Seq(comp)) match {
          case Seq(car: InstanceTarget) => wr.copy(name=car.instance)
          case Seq(car: ReferenceTarget) => wr.copy(name=car.ref)
        }
      case ex => ex.map(fixupRefs(instMap, currentModule, renames))
    }

    val renameMapMap = mutable.HashMap.empty[ModuleTarget, RenameMap]

    def onStmt(currentModule: ModuleTarget)(s: Statement): Statement = {
      val currentModuleName = currentModule.module
      val ns = namespaceMap.getOrElseUpdate(currentModuleName, Namespace(iGraph.moduleMap(currentModuleName)))
      val instMap = getInstMap(iGraph.moduleMap(currentModuleName))
      s match {
        case wDef@ WDefInstance(_, instName, modName, _) if flatInstances.contains(s"${currentModuleName}.$instName") =>
          val toInline = iGraph.moduleMap(modName) match {
            case m: ExtModule => throw new PassException(s"Cannot inline external module ${m.name}")
            case m: Module    => m
          }

          val ports = toInline.ports.map(p => DefWire(p.info, p.name, p.tpe))

          val inlineMod = currentModule.copy(module = modName)
          val bodyx = Block(ports :+ toInline.body) map onStmt(inlineMod)

          val names = "" +: Uniquify
            .enumerateNames(Uniquify.stmtToType(bodyx)(NoInfo, ""))
            .map(_.mkString("_"))

          /** The returned prefix will not be "prefix unique". It may be the same as other existing prefixes in the namespace.
            * However, prepending this prefix to all inlined components is guaranteed to not conflict with this module's
            * namespace. To make it prefix unique, this requires expanding all names in the namespace to include their
            * prefixes before calling findValidPrefix.
            */
          val safePrefix = Uniquify.findValidPrefix(instName + inlineDelim, names, ns.cloneUnderlying - instName)

          val prefixMap = mutable.HashMap.empty[ReferenceTarget, ReferenceTarget]
          val renamedBody = bodyx
            .map(appendNamePrefix(inlineMod, safePrefix, ns, prefixMap))
            .map(appendRefPrefix(inlineMod, prefixMap))

          val instRenames = renameMapMap.getOrElse(inlineMod, RenameMap())
          val prefixRenames = instRenames.andThen()
          prefixMap.foreach { case (from, to) => prefixRenames.record(from, to) }
          val inlineRenames = prefixRenames.andThen()
          inlineRenames.record(currentModule.instOf(instName, modName), currentModule)

          val finalRenameMap = if (renameMapMap.contains(currentModule)) {
            renameMapMap(currentModule) ++ inlineRenames
          } else {
            inlineRenames
          }
          renameMapMap += (currentModule -> finalRenameMap)
          renamedBody
        case sx =>
          val renames = renameMapMap.getOrElse(currentModule, RenameMap())
          sx
          .map(fixupRefs(instMap, currentModule, renames))
          .map(onStmt(currentModule))
      }
    }

    val flatCircuit = c.copy(modules = c.modules.flatMap {
      case m if flatModules.contains(m.name) => None
      case m                                 => Some(m.map(onStmt(ModuleName(m.name, CircuitName(c.main)))))
    })

    val renames = renameMapMap.get(ModuleTarget(c.main, c.main))
    CircuitState(flatCircuit, LowForm, annos, renames)
  }
}
