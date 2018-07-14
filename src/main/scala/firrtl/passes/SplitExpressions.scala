// See LICENSE for license details.

package firrtl
package passes

import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils.{kind, gender, get_info}

// Datastructures
import scala.collection.mutable

// Splits compound expressions into simple expressions
//  and named intermediate nodes
object SplitExpressions extends Pass {
   private def onModule(m: Module): Module = {
      val namespace = Namespace(m)
      def onStmt(s: Statement): Statement = {
        val v = mutable.ArrayBuffer[Statement]()
        // Splits current expression if needed
        // Adds named temporaries to v
        def split(e: Expression): Expression = e match {
          case e: DoPrim =>
            val name = namespace.newTemp
            v += DefNode(get_info(s), name, e)
            WRef(name, e.tpe, kind(e), gender(e))
          case e: Mux =>
            val name = namespace.newTemp
            v += DefNode(get_info(s), name, e)
            WRef(name, e.tpe, kind(e), gender(e))
          case e: ValidIf =>
            val name = namespace.newTemp
            v += DefNode(get_info(s), name, e)
            WRef(name, e.tpe, kind(e), gender(e))
          case _ => e
        }

        def foldCat(ex: Expression): Expression = {
          ex.mapExpr(foldCat) match {
            case e@DoPrim(PrimOps.Cat, args, _, tpe) => (args.head, args(1)) match {
              case (DoPrim(PrimOps.Bits, args1, params1, _), DoPrim(PrimOps.Bits, args2, params2, _))
                if (args1.head == args2.head) && (params1(1) == params2.head + 1) =>
                DoPrim(PrimOps.Bits, args1, Seq(params1.head, params2(1)), tpe)
              case _ => e
            }
            case other => other
          }
        }

        // Recursive. Splits compound nodes
        def splitExp(e: Expression): Expression =
          e map splitExp match {
            case ex: DoPrim => ex map split
            case ex => ex
         }

        def onExp(e: Expression): Expression = splitExp(foldCat(e))

        s map onExp match {
           case x: Block => x map onStmt
           case EmptyStmt => EmptyStmt
           case x =>
             v += x
             v.size match {
               case 1 => v.head
               case _ => Block(v.toSeq)
             }
        }
      }
      Module(m.info, m.name, m.ports, onStmt(m.body))
   }
   def run(c: Circuit): Circuit = {
     val modulesx = c.modules map {
       case m: Module => onModule(m)
       case m: ExtModule => m
     }
     Circuit(c.info, modulesx, c.main)
   }
}
