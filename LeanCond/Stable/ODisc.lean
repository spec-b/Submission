import LeanCond.OProp
import LeanCond.Stable.Basic

-- Stable P → Stable Q → Stable (P ∨ Q) is false in Cond
-- For example, take P and Q to be the stable propositions
-- corresponding to some "random" complementary subsets of Γ := [0,1].
-- Then if P ∨ Q was stable, it would have to be all of Γ; but it's not
-- (there is no finite cover of Γ by closed subsets,
-- each of which factors through either P or Q).

-- However, *open* propositions are closed under ∨
-- and they are stable (see below), as a kind of replacement.

instance ODisc.stable [hp : ODisc P] : Stable P where
  elim h := by
    obtain ⟨m, α, f', hf⟩ := Cond.Scott_continuity P (fun _ ↦ False) 0 (fun x ↦ (h x).elim)
    cases m
    case zero =>                -- Impossible
      exact (f' Fin.elim0).elim0
    case succ =>                -- P holds
      exact α 0

lemma forall_oprop_iff {F : OProp → Prop} [hF : ∀ P, Stable (F P)] :
    (∀ P, F P) ↔ (F ⊥ ∧ F ⊤) := by
  refine ⟨fun H ↦ ⟨H _, H _⟩, fun H P ↦ ?_⟩
  apply (hF P).elim
  suffices (P ∨ ¬ P) → F P from not_not_map this not_not_lem
  rintro (h|h) <;> [convert H.2; convert H.1] <;> ext <;> simp [h]

lemma forall2_oprop_iff {F : OProp → OProp → Prop} [hF : ∀ P Q, Stable (F P Q)] :
    (∀ P Q, F P Q) ↔ (F ⊥ ⊥ ∧ F ⊥ ⊤ ∧ F ⊤ ⊥ ∧ F ⊤ ⊤) := by
  rw [forall_oprop_iff, forall_oprop_iff, forall_oprop_iff, and_assoc]

section

variable {A : Type u} {B : Type v} [ODisc A] [ODisc B] (f : A → B)

instance : Stable (f.Injective) := by
  dsimp only [Function.Injective]
  infer_instance

instance : Stable (f.Surjective) := by
  dsimp only [Function.Surjective]
  infer_instance

lemma _root_.Function.bijective_iff_injective_and_surjective :
    f.Bijective ↔ f.Injective ∧ f.Surjective :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- TeX: `isomorphism-stable` -/
instance : Stable (f.Bijective) := by
  rw [Function.bijective_iff_injective_and_surjective]
  apply instStableAnd

end
