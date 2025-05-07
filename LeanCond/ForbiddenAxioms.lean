import Std.Tactic.Lint
import LeanCond.PrintNum

namespace Lean

open Elab Command

private def forbiddenAxioms (bad : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let decls ← liftCoreM Std.Tactic.Lint.getDeclsInCurrModule
  decls.forM fun n ↦
    let axs := ((((CollectAxioms.collect n).run env).run {}).2).axioms.toList
    let l := bad.filter fun a ↦ a ∈ axs
    if l.isEmpty then pure ()
    else logError m!"'{n}' depends on: {l}"

open private printAxiomsOf from Lean.Elab.Print
elab tk:"#forbiddenAxioms " ids:ident* : command => withRef tk do
  let ns ← ids.mapM resolveGlobalConstNoOverloadWithInfo
  withRef tk <| forbiddenAxioms ns.toList

private def explainForbiddenAxioms (n : Name) (bad : List Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? n with
  | none => throwError "unknown constant '{n}'"
  | some ci =>
  match ci.value? with
  | none => throwError "constant '{n}' has no value"
  | some e => do
  let deps := e.getUsedConstants
  deps.forM fun d ↦
    let axs := ((((CollectAxioms.collect d).run env).run {}).2).axioms.toList
    let l := bad.filter fun a ↦ a ∈ axs
    if l.isEmpty then pure ()
    else logError m!"'{d}' depends on: {l}"

open private printAxiomsOf from Lean.Elab.Print
elab tk:"#explainForbiddenAxioms " ids:ident* : command => withRef tk do
  let ns ← ids.mapM resolveGlobalConstNoOverloadWithInfo
  match ns.toList with
  | [] => throwError "no constant given"
  | n::ns => withRef tk <| explainForbiddenAxioms n ns

end Lean
