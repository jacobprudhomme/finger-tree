val scala3Version = "3.2.0"

lazy val root = project
  .in(file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "finger-tree",
    version := "0.1.0",

    scalaVersion := scala3Version
  )
