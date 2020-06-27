
lazy val root = (project in file("."))
  .enablePlugins(SbtPlugin)
  .settings(
    name := "sbt-jqf",
    sbtPlugin := true,
    libraryDependencies ++= Seq(
      "edu.berkeley.cs.jqf" % "jqf-fuzz" % "1.4",
      "edu.berkeley.cs.jqf" % "jqf-instrument" % "1.4"
    ),
  )
