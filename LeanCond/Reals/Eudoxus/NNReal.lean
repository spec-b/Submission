import LeanCond.Reals.Eudoxus.Prereqs

/-! # Eudoxus nonnegative reals -/

def Nat.almost_hom (f : ℕ → ℕ) : Prop :=
  Monotone f ∧
  ∃ C, ∀ m n, f (m + n) ≤ f m + f n + C ∧ f m + f n ≤ f (m + n) + C

def PreNNEudoxus : AddSubmonoid (ℕ → ℕ) where
  carrier := {f | Nat.almost_hom f}
  zero_mem' := ⟨monotone_const, 0, by simp⟩
  add_mem' {f₁ f₂} := by
    rintro ⟨mono₁, C₁, h₁⟩ ⟨mono₂, C₂, h₂⟩
    refine ⟨mono₁.add mono₂, C₁ + C₂, ?_⟩
    intro m n
    sorry
    -- refine le_trans ?_ (add_le_add (h₁ m n) (h₂ m n))
    -- refine le_trans (le_of_eq $ congr_arg _ ?_) (Int.natAbs_add_le _ _)
    -- simp
    -- abel

namespace PreNNEudoxus

private instance Hausdorff : Hausdorff PreNNEudoxus :=
  inferInstanceAs (_root_.Hausdorff {f : ℕ → ℕ // Nat.almost_hom f})

private instance AddCommMonoid : AddMonoid PreNNEudoxus := inferInstance

def deviatesBy (f : PreNNEudoxus) (C : ℕ) : Prop :=
  ∀ m n, f.1 (m + n) ≤ f.1 m + f.1 n + C ∧ f.1 m + f.1 n ≤ f.1 (m + n) + C

lemma deviatesBy.coeff_zero {f : PreNNEudoxus} {C : ℕ} (h : deviatesBy f C) :
  f.1 0 ≤ C := by simpa only [add_zero, add_comm, Nat.add_le_add_iff_le_right] using (h 0 0).2

def bounded (f : PreNNEudoxus) : Prop :=
  ∃ C, ∀ n, f.1 n ≤ C

private
lemma bounded_iff_forall.aux1 (f : PreNNEudoxus) (C : ℕ) (hf : deviatesBy f C) :
    let δ : ℕ → ℕ := fun k ↦ (f.1 k) - C;
    ∀ k : ℕ, 2 * δ k ≤ δ (2 * k) := by
  sorry
  -- intro δ k
  -- have H0 := Int.abs_sub_abs_le_abs_sub (2 * f.1 k) (f.1 (2 * k))
  -- have H1 := hf k k
  -- rw [← Int.ofNat_le, Int.coe_natAbs] at H1
  -- simp only [← two_mul, Int.sub_sub] at H1
  -- rw [← abs_neg, neg_sub] at H1
  -- have H2 := H0.trans H1
  -- have abs2 : abs (2 : ℤ) = 2 := by decide
  -- rw [sub_le_comm, Int.abs_mul, abs2] at H2
  -- refine le_trans (le_of_eq ?_) (Int.sub_le_sub_right H2 C)
  -- rw [mul_sub, two_mul (C:ℤ), ← Int.sub_sub]

private
lemma bounded_iff_forall.aux2 (f : PreNNEudoxus) (C : ℕ) (hf : deviatesBy f C) :
    let δ : ℕ → ℕ := fun k ↦ (f.1 k) - C;
    ∀ i k, 2^i * δ k ≤ δ (2^i * k) := by
  sorry
  -- intro δ i
  -- induction i
  -- case zero => simp only [Nat.zero_eq, pow_zero, one_mul, le_refl, forall_const]
  -- case succ i IH =>
  --   intro k
  --   simp only [pow_succ, mul_assoc]
  --   refine le_trans ?_ (bounded_iff_forall.aux1 _ _ hf _)
  --   apply Int.mul_le_mul_of_nonneg_left
  --   exact IH _
  --   decide

def bounded_iff_forall (f : PreNNEudoxus) (C : ℕ) (hf : deviatesBy f C) :
  bounded f ↔ ∀ n, (f.1 n) ≤ C := by
  sorry
  -- refine ⟨?mp, ?mpr⟩
  -- case mp =>
  --   rintro ⟨C', hC'⟩
  --   let δ : ℕ → ℕ := fun k ↦ abs (f.1 k) - C
  --   have hδ : ∀ i k, 2^i * δ k ≤ δ (2^i * k) := bounded_iff_forall.aux2 f C hf
  --   intro n
  --   apply Decidable.byContradiction
  --   rw [← Int.ofNat_le, Int.coe_natAbs, Int.not_le]
  --   intro H
  --   specialize hδ C' n
  --   specialize hC' (2 ^ C' * n)
  --   rw [← Int.ofNat_le, Int.coe_natAbs] at hC'
  --   have hδn : 1 ≤ δ n := by rwa [le_sub_iff_add_le', ← Int.lt_iff_add_one_le]
  --   have h2C' : C' < 2 ^ C' := Nat.lt_pow_self' (by decide) _
  --   have key : C' < δ (2 ^ C' * n) := by
  --     rw [← Int.ofNat_lt] at h2C'
  --     refine lt_of_lt_of_le h2C' (le_trans ?_ hδ)
  --     have : (2 ^ C' : ℤ) = ↑(2 ^ C') := by
  --       simp only [Nat.cast_pow, Nat.cast_ofNat]
  --     rw [← mul_one (↑(2 ^ C') : ℤ), this]
  --     exact Int.mul_le_mul_of_nonneg_left hδn (Int.ofNat_nonneg _)
  --   refine not_lt_of_le (le_trans ?_ hC') key
  --   apply Int.sub_le_self
  --   apply Int.ofNat_nonneg
  -- case mpr =>
  --   intro H
  --   exact ⟨C, H⟩

instance bounded.Compact (f : PreNNEudoxus) : Compact (bounded f) := by
  obtain ⟨_, C, h⟩ := f.2
  rw [bounded_iff_forall f C h]
  infer_instance

def boundedSubmonoid : AddSubmonoid PreNNEudoxus where
  carrier := {f | bounded f}
  zero_mem' := ⟨0, fun _ ↦ le_rfl⟩
  add_mem' {f₁ f₂} := by
    rintro ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    use C₁ + C₂
    intro n
    exact add_le_add (h₁ n) (h₂ n)

instance Setoid : Setoid PreNNEudoxus where
  r := fun f g ↦ ∃ b ∈ boundedSubmonoid, f ≤ g + b ∧ g ≤ f + b
  iseqv := by
    constructor
    case refl => intro f; exact ⟨0, zero_mem _, by simp only [add_zero, le_refl, and_self]⟩
    case symm => intro f₁ f₂ h; simpa only [and_comm] using h
    case trans =>
      rintro f₁ f₂ f₃ ⟨b₁, hb₁, h₁⟩ ⟨b₂, hb₂, h₂⟩
      refine ⟨b₁ + b₂, add_mem hb₁ hb₂, ?_⟩
      sorry

instance approx_Compact (f g : PreNNEudoxus) : Compact (f ≈ g) := by
  show Compact (∃ b ∈ boundedSubmonoid, f ≤ g + b ∧ g ≤ f + b)
  obtain ⟨_, Cf, hf⟩ := f.2
  obtain ⟨_, Cg, hg⟩ := g.2
  -- TODO: prove a lemma that shows that `b = Cf + Cg` works
  -- then rewrite using that lemma
  sorry

def isPos (f : PreNNEudoxus) : Prop :=
  ∀ m, ∃ n > m, f.1 n > f.1 m

lemma isPos_iff_forall (f : PreNNEudoxus) :
  isPos f ↔ ∀ m N, ∃ k > m, f.1 k > N := by
  sorry
  -- refine ⟨?mp, ?mpr⟩
  -- case mp =>
  --   intro h m N
  --   suffices ∀ n : ℕ, ∃ k > m, f.1 k > f.1 m + n by
  --     obtain ⟨k, h1, h2⟩ := this (N.natAbs + (f.1 m).natAbs)
  --     refine ⟨k, h1, lt_of_le_of_lt ?_ h2⟩
  --     rw [Nat.cast_add, ← sub_le_iff_le_add', sub_eq_add_neg, ← Int.natAbs_neg (f.1 m)]
  --     exact Int.add_le_add Int.le_natAbs Int.le_natAbs
  --   intro n
  --   induction n
  --   case zero =>
  --     simpa using h m
  --   case succ n IH =>
  --     obtain ⟨k, hk0, hfk⟩ := IH
  --     obtain ⟨N, hNk, hfN⟩ := h k
  --     refine ⟨N, hk0.trans hNk, ?_⟩
  --     rw [gt_iff_lt, Int.lt_iff_add_one_le] at hfk hfN ⊢
  --     refine le_trans (le_of_eq ?_) ((Int.add_le_add_right hfk 1).trans hfN)
  --     simp only [Nat.cast_succ, add_left_inj, add_assoc]
  -- case mpr =>
  --   intro h m
  --   apply h m

lemma isPos_iff_exists (f : PreNNEudoxus) (C : ℕ) (hfC : deviatesBy f C) :
  isPos f ↔ ∃ n > 0, f.1 n > C := by
  sorry
  -- refine ⟨?mp, ?mpr⟩
  -- case mp =>
  --   intro hf
  --   rw [isPos_iff_forall] at hf
  --   apply hf
  -- case mpr =>
  --   rintro ⟨N, hN0, hNC⟩
  --   intro m
  --   use (m + N)
  --   simp only [Int.lt_add_of_pos_right m hN0, true_and]
  --   rw [gt_iff_lt, ← Int.sub_pos] at hNC ⊢
  --   refine lt_of_lt_of_le hNC ?_
  --   rw [sub_le_comm]
  --   specialize hfC m N
  --   rw [← Int.ofNat_le, ← Int.natAbs_neg] at hfC
  --   refine le_trans (le_of_eq ?_) (Int.le_natAbs.trans hfC)
  --   simp only [Int.neg_sub]

instance isPos.ODisc (f : PreNNEudoxus) : ODisc (isPos f) := by
  obtain ⟨_, C, h⟩ := f.2
  rw [isPos_iff_exists f C h]
  infer_instance

lemma isPos_of_Rel (f g : PreNNEudoxus) (H : f ≈ g) (hf : isPos f) : isPos g := by
  sorry
  -- rw [isPos_iff_forall] at hf
  -- intro m
  -- rcases H with ⟨N, hN⟩
  -- obtain ⟨k, h1, h2⟩ := hf m (g.1 m + N)
  -- refine ⟨k, h1, ?_⟩
  -- calc g.1 m < f.1 k - N := Int.lt_sub_right_of_add_lt h2
  --   _ ≤ g.1 k := ?_
  -- apply Int.sub_le_of_sub_le
  -- specialize hN k
  -- rw [← Int.ofNat_le] at hN
  -- exact Int.le_natAbs.trans hN

end PreNNEudoxus

def NNEudoxus : Type := @Quotient PreNNEudoxus inferInstance

namespace Eudoxus

private instance Hausdorff : Hausdorff NNEudoxus where
  compact_diagonal x y := Quotient.inductionOn₂ x y $
    fun a b ↦ by
    rw [Quotient.eq]
    infer_instance

def isPos : NNEudoxus → Prop :=
  Quotient.lift PreNNEudoxus.isPos $ fun _ _ H ↦ propext
    ⟨PreNNEudoxus.isPos_of_Rel _ _ H, PreNNEudoxus.isPos_of_Rel _ _ $ Setoid.symm H⟩

instance (x : NNEudoxus) : ODisc (isPos x) :=
  Quotient.inductionOn x $ fun _ ↦ PreNNEudoxus.isPos.ODisc _

end Eudoxus

#forbiddenAxioms Classical.choice
