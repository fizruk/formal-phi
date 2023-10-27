import Lake
open Lake DSL

package «phi-calculus» {
  -- add package configuration options here
}

lean_lib «PhiCalculus» {
  -- add library configuration options here
}

@[default_target]
lean_exe «phi-calculus» {
  root := `Main
}
