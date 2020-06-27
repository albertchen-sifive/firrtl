// See LICENSE for license details.

package firrtl.testutils

import sbt._
import sbt.Keys._
import sbt.internal.util.FeedbackProvidedException

import sbt.complete.DefaultParsers.spaceDelimited

case class JQFPluginException(message: String) extends Exception(message)
  with FeedbackProvidedException

object JQFPlugin extends AutoPlugin {
  object autoImport {
    val jqfOutputDirectory = settingKey[File]("")

    val jqfInputDirectory = settingKey[Option[File]]("")

    val jqfExtraArguments = settingKey[Seq[String]](
      "Additional command-line arguments to pass on every mdoc invocation. " +
        "For example, add '--no-link-hygiene' to disable link hygiene."
    )

    val jqfFuzz = inputKey[Unit]("")
  }

  import autoImport._

  override val trigger: PluginTrigger = noTrigger

  override val requires: Plugins = plugins.JvmPlugin
  
  override def projectSettings: Seq[Def.Setting[_]] = Seq(
    jqfOutputDirectory := target.in(Compile).value / "JQF",

    jqfInputDirectory := None,

    jqfExtraArguments := Seq.empty,
    
    jqfFuzz := Def.inputTaskDyn {
      val extraArgs = jqfExtraArguments.value
      val parsed = spaceDelimited("<arg>").parsed
      val defaultArgs = toCmdlineArgs.value
      val args = (defaultArgs ++ parsed).mkString(" ")
      Def.taskDyn {
        runMain.in(Compile).toTask(s" firrtl.fuzzer.JQFFuzz $args")
      }
    }.evaluated,
  )


  private def toCmdlineArgs: Def.Initialize[Task[Seq[String]]] = Def.task {
    Seq(
      "--classpathElements", (Compile / fullClasspathAsJars).value.files.mkString(":"),
      "--outputDirectory", jqfOutputDirectory.value.toString
    ) ++
    jqfInputDirectory.value.map(f => Seq("--inputDirectory", f.toString)).getOrElse(Seq.empty)
  }
}
