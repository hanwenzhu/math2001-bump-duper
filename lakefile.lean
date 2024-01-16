import Lake

open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"main"

package Duper {
  precompileModules := true
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
