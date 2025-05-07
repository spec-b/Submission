import LeanCond.PseudoAxioms
import Mathlib.Tactic.LibrarySearch

universe u v

class Compact (X : Sort u) : Prop where
  exists_CHaus_cover : ∃ (K : Sort u) (_ : CHaus K) (f : K → X), f.Surjective

lemma exists_CHaus_cover (X : Sort u) [Compact X] :
  ∃ (K : Sort u) (_ : CHaus K) (f : K → X), f.Surjective := Compact.exists_CHaus_cover

class Hausdorff (X : Sort u) : Prop where
  compact_diagonal : ∀ x y : X, Compact (x = y)

instance compact_diagonal {X : Sort u} [Hausdorff X] (x y : X) :
  Compact (x = y) := Hausdorff.compact_diagonal _ _

protected instance CHaus.Compact (X : Sort u) [CHaus X] : Compact X :=
  ⟨X, inferInstance, id, Function.surjective_id⟩

protected instance CHaus.Hausdorff (X : Sort u) [CHaus X] : Hausdorff X :=
  ⟨fun _ _ ↦ inferInstance⟩

protected instance Prop.Hausdorff (P : Prop) : Hausdorff P where
  compact_diagonal := fun h₁ h₂ ↦
    suffices CHaus (h₁ = h₂) from inferInstance
    Equiv.CHaus True (Equiv.ofIff $ by simp)

def kernel_Setoid {X Y : Sort u} (f : X → Y) : Setoid X where
    r := fun x y ↦ f x = f y
    iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

noncomputable
def Equiv_of_bijective {X : Sort u} {Y : Sort v} (f : X → Y) (f_inj : f.Injective) (f_surj : f.Surjective) :
  X ≃ Y where
  toFun := f
  invFun := fun y ↦ @unique_choice X (fun x ↦ f x = y) $ by
    obtain ⟨x, rfl⟩ := f_surj y
    refine ⟨x, rfl, fun x' h ↦ f_inj h⟩
  left_inv := fun x ↦ by
    apply f_inj
    exact @unique_choice.spec X (fun x' ↦ f x' = f x) _
  right_inv := fun y ↦ @unique_choice.spec X (fun x ↦ f x = y) _

instance Prop.CHaus_of_Compact (P : Prop) [Compact P] : CHaus P := by
  obtain ⟨K, hK, f, hf⟩ := exists_CHaus_cover P
  refine Equiv.CHaus K $ Equiv.ofIff ⟨?_, f⟩
  intro h
  obtain ⟨H, -⟩ := hf h
  exact H

theorem CHaus_of_surjective_of_CHaus_kernel_pair {X Y : Type u} [CHaus X]
  (f : X → Y) (hf : f.Surjective) [H : ∀ x y, CHaus (f x = f y)] :
  CHaus Y := by
  let s : Setoid X := kernel_Setoid f
  have : ∀ x y, CHaus (s.r x y) := H
  refine Equiv.CHaus (Quotient s) (Equiv_of_bijective ?_ ?_ ?_).symm
  . exact Quotient.lift f (fun _ _ ↦ id)
  . apply Quotient.ind₂
    intro x y h
    apply Quotient.sound
    exact h
  . intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨.mk' x, rfl⟩

theorem CHaus_of_Compact_of_Hausdorff (X : Type u) [Compact X] [Hausdorff X] : CHaus X := by
  obtain ⟨K, hK, f, hf⟩ := exists_CHaus_cover X
  exact CHaus_of_surjective_of_CHaus_kernel_pair f hf
