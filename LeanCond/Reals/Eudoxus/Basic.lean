import LeanCond.Reals.Eudoxus.Prereqs

/-! # Eudoxus reals -/

namespace Int

def funDeviatesBy (f : ℤ → ℤ) (C : ℕ) : Prop :=
  ∀ m n, Int.natAbs (f (m + n) - f m - f n) ≤ C

namespace funDeviatesBy

variable {f f₁ f₂ : ℤ → ℤ} {C C₁ C₂ : ℕ}

def add (h₁ : funDeviatesBy f₁ C₁) (h₂ : funDeviatesBy f₂ C₂) :
  funDeviatesBy (f₁ + f₂) (C₁ + C₂) := by
  intro m n
  refine le_trans ?_ (add_le_add (h₁ m n) (h₂ m n))
  refine le_trans (le_of_eq $ congr_arg _ ?_) (Int.natAbs_add_le _ _)
  simp
  abel

def neg (h : funDeviatesBy f C) : funDeviatesBy (-f) C := by
  intro m n
  rw [← Int.natAbs_neg]
  simp [-neg_add_rev, -Int.natAbs_neg, neg_add, ← sub_eq_add_neg]
  apply h

def sub (h₁ : funDeviatesBy f₁ C₁) (h₂ : funDeviatesBy f₂ C₂) :
  funDeviatesBy (f₁ - f₂) (C₁ + C₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

def ofNat (k : ℕ) : funDeviatesBy (k * .) 0 := by
  intro m n
  simp [mul_add]

lemma coeff_zero (h : funDeviatesBy f C) :
  Int.natAbs (f 0) ≤ C := by simpa using h 0 0

end funDeviatesBy

def almost_hom (f : ℤ → ℤ) : Prop :=
  ∃ C, funDeviatesBy f C

end Int

def PreEudoxus : AddSubgroup (ℤ → ℤ) where
  carrier := {f | Int.almost_hom f}
  zero_mem' := ⟨0, fun _ _ ↦ show Int.natAbs (0 - 0 - 0) ≤ _ by simp⟩
  add_mem' {f₁ f₂} := by
    rintro ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    exact ⟨C₁ + C₂, h₁.add h₂⟩
  neg_mem' {f} := by
    rintro ⟨C, h⟩
    exact ⟨C, h.neg⟩

namespace PreEudoxus

private instance Hausdorff : Hausdorff PreEudoxus :=
  inferInstanceAs (_root_.Hausdorff {f : ℤ → ℤ // Int.almost_hom f})

private instance AddCommGroup : AddGroup PreEudoxus := inferInstance

def deviatesBy (f : PreEudoxus) (C : ℕ) : Prop :=
  ∀ m n, Int.natAbs (f.1 (m + n) - f.1 m - f.1 n) ≤ C

lemma deviatesBy.coeff_zero {f : PreEudoxus} {C : ℕ} (h : deviatesBy f C) :
  Int.natAbs (f.1 0) ≤ C := by simpa using h 0 0

def bounded (f : PreEudoxus) : Prop :=
  ∃ C, ∀ n, Int.natAbs (f.1 n) ≤ C

private
lemma bounded_iff_forall.aux1 (f : PreEudoxus) (C : ℕ) (hf : deviatesBy f C) :
    let δ : ℤ → ℤ := fun k ↦ abs (f.1 k) - C;
    ∀ k : ℤ, 2 * δ k ≤ δ (2 * k) := by
  intro δ k
  have H0 := Int.abs_sub_abs_le_abs_sub (2 * f.1 k) (f.1 (2 * k))
  have H1 := hf k k
  rw [← Int.ofNat_le, Int.coe_natAbs] at H1
  simp only [← two_mul, Int.sub_sub] at H1
  rw [← abs_neg, neg_sub] at H1
  have H2 := H0.trans H1
  have abs2 : abs (2 : ℤ) = 2 := by decide
  rw [sub_le_comm, Int.abs_mul, abs2] at H2
  refine le_trans (le_of_eq ?_) (Int.sub_le_sub_right H2 C)
  rw [mul_sub, two_mul (C:ℤ), ← Int.sub_sub]

private
lemma bounded_iff_forall.aux2 (f : PreEudoxus) (C : ℕ) (hf : deviatesBy f C) :
    let δ : ℤ → ℤ := fun k ↦ abs (f.1 k) - C;
    ∀ i k, 2^i * δ k ≤ δ (2^i * k) := by
  intro δ i
  induction i
  case zero => simp only [Nat.zero_eq, pow_zero, one_mul, le_refl, forall_const]
  case succ i IH =>
    intro k
    simp only [pow_succ, mul_assoc]
    refine le_trans ?_ (bounded_iff_forall.aux1 _ _ hf _)
    apply Int.mul_le_mul_of_nonneg_left
    exact IH _
    decide

def bounded_iff_forall (f : PreEudoxus) (C : ℕ) (hf : deviatesBy f C) :
  bounded f ↔ ∀ n, Int.natAbs (f.1 n) ≤ C := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    rintro ⟨C', hC'⟩
    let δ : ℤ → ℤ := fun k ↦ abs (f.1 k) - C
    have hδ : ∀ i k, 2^i * δ k ≤ δ (2^i * k) := bounded_iff_forall.aux2 f C hf
    intro n
    apply Decidable.byContradiction
    rw [← Int.ofNat_le, Int.coe_natAbs, Int.not_le]
    intro H
    specialize hδ C' n
    specialize hC' (2 ^ C' * n)
    rw [← Int.ofNat_le, Int.coe_natAbs] at hC'
    have hδn : 1 ≤ δ n := by rwa [le_sub_iff_add_le', ← Int.lt_iff_add_one_le]
    have h2C' : C' < 2 ^ C' := Nat.lt_pow_self' (by decide) _
    have key : C' < δ (2 ^ C' * n) := by
      rw [← Int.ofNat_lt] at h2C'
      refine lt_of_lt_of_le h2C' (le_trans ?_ hδ)
      have : (2 ^ C' : ℤ) = ↑(2 ^ C' : ℕ) := by
        simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_one (↑(2 ^ C' : ℕ) : ℤ), this]
      exact Int.mul_le_mul_of_nonneg_left hδn (Int.ofNat_nonneg _)
    refine not_lt_of_le (le_trans ?_ hC') key
    apply Int.sub_le_self
    apply Int.ofNat_nonneg
  case mpr =>
    intro H
    exact ⟨C, H⟩

instance bounded.Compact (f : PreEudoxus) : Compact (bounded f) := by
  obtain ⟨C, h⟩ := f.2
  rw [bounded_iff_forall f C h]
  infer_instance

def boundedSubgroup : AddSubgroup PreEudoxus where
  carrier := {f | bounded f}
  zero_mem' := ⟨0, fun _ ↦ le_of_eq $ Int.natAbs_zero⟩
  add_mem' {f₁ f₂} := by
    rintro ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    use C₁ + C₂
    intro n
    exact (Int.natAbs_add_le _ _).trans (add_le_add (h₁ n) (h₂ n))
  neg_mem' {f} := by
    rintro ⟨C, h⟩
    use C
    intro n
    erw [Int.natAbs_neg]
    apply h

instance Setoid : Setoid PreEudoxus where
  r := fun f g ↦ f - g ∈ boundedSubgroup
  iseqv := by
    constructor
    case refl => intro f; rw [sub_self]; exact zero_mem _
    case symm => intro f₁ f₂ h; rw [← neg_sub]; exact neg_mem h
    case trans => intro f₁ f₂ f₃ h₁ h₂; simpa using add_mem h₁ h₂

def isPos (f : PreEudoxus) : Prop :=
  ∀ m, ∃ n > m, f.1 n > f.1 m

lemma isPos_iff_forall (f : PreEudoxus) :
  isPos f ↔ ∀ m N, ∃ k > m, f.1 k > N := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro h m N
    suffices ∀ n : ℕ, ∃ k > m, f.1 k > f.1 m + n by
      obtain ⟨k, h1, h2⟩ := this (N.natAbs + (f.1 m).natAbs)
      refine ⟨k, h1, lt_of_le_of_lt ?_ h2⟩
      rw [Nat.cast_add, ← sub_le_iff_le_add', sub_eq_add_neg, ← Int.natAbs_neg (f.1 m)]
      exact Int.add_le_add Int.le_natAbs Int.le_natAbs
    intro n
    induction n
    case zero =>
      simpa using h m
    case succ n IH =>
      obtain ⟨k, hk0, hfk⟩ := IH
      obtain ⟨N, hNk, hfN⟩ := h k
      refine ⟨N, hk0.trans hNk, ?_⟩
      rw [gt_iff_lt, Int.lt_iff_add_one_le] at hfk hfN ⊢
      refine le_trans (le_of_eq ?_) ((Int.add_le_add_right hfk 1).trans hfN)
      simp only [Nat.cast_succ, add_left_inj, add_assoc]
  case mpr =>
    intro h m
    apply h m

lemma isPos_iff_exists (f : PreEudoxus) (C : ℕ) (hfC : Int.funDeviatesBy f C) :
  isPos f ↔ ∃ n > 0, f.1 n > C := by
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro hf
    rw [isPos_iff_forall] at hf
    apply hf
  case mpr =>
    rintro ⟨N, hN0, hNC⟩
    intro m
    use (m + N)
    simp only [Int.lt_add_of_pos_right m hN0, true_and]
    rw [gt_iff_lt, ← Int.sub_pos] at hNC ⊢
    refine lt_of_lt_of_le hNC ?_
    rw [sub_le_comm]
    specialize hfC m N
    rw [← Int.ofNat_le, ← Int.natAbs_neg] at hfC
    refine le_trans (le_of_eq ?_) (Int.le_natAbs.trans hfC)
    simp only [Int.neg_sub]

instance isPos.ODisc (f : PreEudoxus) : ODisc (isPos f) := by
  obtain ⟨C, h⟩ := f.2
  rw [isPos_iff_exists f C h]
  infer_instance

lemma isPos_of_Rel (f g : PreEudoxus) (H : f ≈ g) (hf : isPos f) : isPos g := by
  rw [isPos_iff_forall] at hf
  intro m
  rcases H with ⟨N, hN⟩
  obtain ⟨k, h1, h2⟩ := hf m (g.1 m + N)
  refine ⟨k, h1, ?_⟩
  calc g.1 m < f.1 k - N := Int.lt_sub_right_of_add_lt h2
    _ ≤ g.1 k := ?_
  apply Int.sub_le_of_sub_le
  specialize hN k
  rw [← Int.ofNat_le] at hN
  exact Int.le_natAbs.trans hN

end PreEudoxus

def Eudoxus : Type := @Quotient PreEudoxus inferInstance

namespace Eudoxus

private instance Hausdorff : Hausdorff Eudoxus where
  compact_diagonal x y := Quotient.inductionOn₂ x y $
    fun a b ↦ by
    rw [Quotient.eq]
    apply PreEudoxus.bounded.Compact

def isPos : Eudoxus → Prop :=
  Quotient.lift PreEudoxus.isPos $ fun _ _ H ↦ propext
    ⟨PreEudoxus.isPos_of_Rel _ _ H, PreEudoxus.isPos_of_Rel _ _ $ Setoid.symm H⟩

instance (x : Eudoxus) : ODisc (isPos x) :=
  Quotient.inductionOn x $ fun _ ↦ PreEudoxus.isPos.ODisc _

private def sub : Eudoxus → Eudoxus → Eudoxus :=
  Quotient.lift₂ (fun f g ↦ ⟦f - g⟧) $ by
  intro f₁ g₁ f₂ g₂ h₁ h₂
  apply Quotient.sound
  show _ ∈ PreEudoxus.boundedSubgroup
  have : (f₁ - g₁) - (f₂ - g₂) = (f₁ - f₂) - (g₁ - g₂) := by
    simp only [sub_eq_add_neg, neg_add_rev, neg_neg, add_left_comm, add_assoc, add_right_inj]
    rw [add_comm]
  rw [this]
  exact AddSubgroup.sub_mem _ h₁ h₂

instance Sub : Sub Eudoxus :=
⟨sub⟩

instance LT : LT Eudoxus :=
⟨fun x y ↦ isPos (y - x)⟩

instance LE : LE Eudoxus :=
⟨fun x y ↦ ¬ y < x⟩

private def ofNat (k : ℕ) : Eudoxus :=
⟦⟨(k * .), 0, Int.funDeviatesBy.ofNat k⟩⟧

instance (k : ℕ) : OfNat Eudoxus k := ⟨ofNat k⟩

end Eudoxus

#forbiddenAxioms Classical.choice
