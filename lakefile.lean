import Lake

open Lake DSL

require std from git "https://github.com/leanprover/std4.git"@"ff9850c4726f6b9fb8d8e96980c3fcb2900be8bd"

package Duper {
  precompileModules := true
  moreLeanArgs := #["-Dlinter.unusedVariables=false"]
}

lean_lib Duper

@[default_target]
lean_exe duper {
  root := `Main
}
