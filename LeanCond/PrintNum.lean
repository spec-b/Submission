import Lean.Elab.Print

open Lean in
elab "#printNum " n:ident i:num : command => do
  let name := Name.num n.getId i.getNat
  let some decl := (← getEnv).find? name | throwError "no such declaration {name}"
  logInfo m!"{name} : {decl.type} :=\n{decl.value?.getD (.bvar 0)}"
