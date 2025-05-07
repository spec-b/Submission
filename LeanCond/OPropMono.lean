import LeanCond.Stable.ODisc
import LeanCond.NatInfty

open NatInfty in
lemma oprop_mono (F : OProp → OProp) : ∀ (P Q : OProp), (P → Q) → (F P → F Q) := by
  rw [forall2_oprop_iff]
  suffices F ⊥ → F ⊤ by simpa
  intro h
  let Z := F ∘ finite
  have hinf : Z ∞ := by simp [h]
  rcases eventually Z hinf with ⟨n, hn⟩
  simpa using hn _ $ n.lt_succ_self

lemma forall_oprop_of_bot (F : OProp → Prop) [∀ P, ODisc (F P)] (h : F ⊥) (P : OProp) : F P :=
  oprop_mono (⟨F ·⟩) ⊥ P False.elim h

#forbiddenAxioms Classical.choice
