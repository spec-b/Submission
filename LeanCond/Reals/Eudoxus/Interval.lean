import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

import LeanCond.Reals.Eudoxus.Basic
import LeanCond.Reals.Eudoxus.RDiv

-- Disable simp lemmas that use choice
attribute [-simp] add_pos_iff add_lt_iff_neg_left lt_add_iff_pos_right add_lt_add_iff_right
attribute [-simp] le_add_iff_nonneg_left lt_add_iff_pos_left
attribute [-simp] le_add_iff_nonneg_right

attribute [simp] Nat.lt_add_one_iff Nat.lt_add_right_iff_pos Nat.lt_add_left_iff_pos
namespace Int

/-
Warning: `adjust` does not produce odd functions, depsite what is claimed in the
"Concentration lemma" (Lemma 4) in arXiv:0301015,
"A natural construction for the real numbers", Norbert A'Campo
-/

def foo (n : ℤ) := n/2

example : Int.almost_hom foo := by
  refine ⟨3, ?_⟩
  intro m n
  dsimp [foo]
  -- obviously true, but I can't be bothered to prove it
  sorry

/-- Adjusting `foo` -/
def bar (n : ℤ) := let C := 3; (foo (3 * C * n)).rdiv (3 * C)

#eval bar 1
#eval bar (-1)

#eval List.and $ (List.range 2).map fun k ↦ (bar (-k:ℤ)) == -bar k

end Int

namespace Int

lemma mul_lt_mul_iff_of_pos_left {a b c : ℤ} (hc : 0 < c) :
    c * a < c * b ↔ a < b := by
  rw [← sub_pos, ← mul_sub, mul_pos_iff]
  simp only [hc, sub_pos, true_and, or_iff_left_iff_imp, and_imp]
  intro h
  exact (h.not_le hc.le).elim

lemma mul_pos_strictMono (k : ℤ) (hk : 0 < k) : StrictMono (k * ·) := by
  intro m n h
  rwa [mul_lt_mul_iff_of_pos_left hk]

end Int

namespace Nat

lemma mul_lt_mul_iff_of_pos_left {a b c : ℕ} (hc : 0 < c) :
    c * a < c * b ↔ a < b := by
  zify
  rw [Int.mul_lt_mul_iff_of_pos_left (Int.coe_nat_pos.mpr hc)]

lemma mul_pos_strictMono (k : ℕ) (hk : 0 < k) : StrictMono (k * ·) := by
  intro m n h
  rwa [mul_lt_mul_iff_of_pos_left hk]

end Nat

namespace PreEudoxus

def adjusted (f : PreEudoxus) : Prop := deviatesBy f 1

instance adjusted.CHaus (f : PreEudoxus) : CHaus (adjusted f) := by
  unfold adjusted deviatesBy
  infer_instance

lemma adjust_helper' (a b c: ℤ) (C k : ℕ) (hk : 2 * C < k)
    (h : Int.natAbs (a - b - c) ≤ C) :
    Int.natAbs (a.rdiv k - b.rdiv k - c.rdiv k) ≤ 1 := by
  have h2 : Int.natAbs 2 = 2 := rfl
  have h' : Int.natAbs (2 * (a - b - c)) < k := by
    rw [Int.natAbs_mul, h2]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h) hk
  rw [← Nat.lt_add_one_iff]
  have h2k0 : 0 < 2 * k := by simpa using lt_of_le_of_lt zero_le' hk
  rw [← (Nat.mul_pos_strictMono (2 * k) h2k0).lt_iff_lt]
  calc
    _ = Int.natAbs (2 * k * (a.rdiv k - b.rdiv k - c.rdiv k)) := by simp [h2, Int.natAbs_mul]
    _ = Int.natAbs (_ - 2 * (a-b-c) + 2 * (a-b-c)) := by rw [Int.sub_add_cancel]
    _ ≤ _ := Int.natAbs_add_le _ _
    _ < (k + k + k) + k := lt_of_lt_of_le (Nat.add_lt_add_left h' _) (Nat.add_le_add_right ?_ _)
    _ = (1 + 1) * k * (1 + 1) := by simp only [add_mul, mul_add, one_mul, mul_one, add_assoc]
  have := Nat.add_lt_add_left h' k
  sorry

lemma adjust_helper (a b c : ℤ) (C : ℕ) (h : Int.natAbs (a - b - c) ≤ C) :
    Int.natAbs (a.rdiv (3 * C) - b.rdiv (3 * C) - c.rdiv (3 * C)) ≤ 1 := by
  by_cases hC : C = 0
  · simp only [hC, Nat.cast_zero, mul_zero, Int.rdiv_zero, sub_self, Int.natAbs_zero, zero_le]
  refine adjust_helper' a b c C (3 * C) ?_ h
  exact Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pos_of_ne_zero hC)

def adjust (f : PreEudoxus) (C : ℕ) (hfC : deviatesBy f C) : PreEudoxus :=
  ⟨fun n ↦ (f.1 (3 * C * n)).rdiv (3 * C), by
    refine ⟨1, ?_⟩
    intro m n
    apply adjust_helper
    rw [mul_add]
    apply hfC⟩

lemma adjust_coeff_zero (f : PreEudoxus) (C : ℕ) (hfC : deviatesBy f C) :
  (adjust f C hfC).1 0 = 0 := by
  dsimp only [adjust]
  cases C
  case zero => simp
  case succ C =>
    simp only [mul_zero]
    have aux : (3 : ℤ) * (C.succ : ℤ) ≠ 0 := by
      intro h
      rw [Int.mul_eq_zero] at h
      simp only [OfNat.ofNat_ne_zero, false_or, Nat.cast_eq_zero] at h
    rw [← abs_eq_zero]
    apply le_antisymm _ (abs_nonneg _)
    apply Int.le_of_lt_add_one; rw [zero_add]
    -- multiply on both sides with `2 * k = 2 * 3 * (C + 1)`
    -- apply (Int.rdiv_existsUnique _ _ aux).unique (Int.rdiv_spec _ _ aux)
    -- simp only [Nat.cast_succ, mul_zero, tsub_le_iff_right, zero_add]
    -- have := hfC.coeff_zero
    sorry

lemma adjust_adjusted (f : PreEudoxus) (C : ℕ) (hfC : deviatesBy f C) :
  adjusted (adjust f C hfC) := by
  intro m n
  apply adjust_helper
  rw [mul_add]
  apply hfC

lemma adjust_approx (f : PreEudoxus) (C : ℕ) (hfC : deviatesBy f C) :
  adjust f C hfC ≈ f := by
  refine ⟨C, ?_⟩
  intro n
  dsimp [adjust]
  sorry

instance _root_.Int.Icc.CHaus (a b : ℤ) : CHaus (Finset.Icc a b) :=
  Equiv.CHaus (Fin (b - a).natAbs) $
  sorry

def L (n : ℤ) : ℤ := min (-1) (n-1)

def U (n : ℤ) : ℤ := max 1 (n+1)

def PreAdjustedIntervalCover := (n : ℤ) → Finset.Icc (L n) (U n)

instance PreAdjustedIntervalCover.CHaus : CHaus PreAdjustedIntervalCover :=
  Pi.CHaus _ _

def AdjustedIntervalCover :=
  { f : PreAdjustedIntervalCover //
    ∀ m n, Int.natAbs ((f (m + n)).1 - (f m).1 - (f n).1) ≤ 1 }

namespace AdjustedIntervalCover

private instance CHaus : CHaus AdjustedIntervalCover :=
  Subtype.CHaus _ _

noncomputable
def PreEudoxus (f : AdjustedIntervalCover) : _root_.PreEudoxus where
  val := fun n ↦ f.1 n
  property := ⟨1, f.2⟩

noncomputable
def proj (f : AdjustedIntervalCover) : {x : Eudoxus // 0 ≤ x ∧ x ≤ 1} where
  val := ⟦f.PreEudoxus⟧
  property := by
    constructor
    . intro h
      obtain ⟨n₀, hn₀, h₀⟩ := h 0
      obtain ⟨n₁, hn₁, h₁⟩ := h n₀
      obtain ⟨n₂, hn₂, h₂⟩ := h n₁
      simp only [Nat.cast_zero, zero_mul, AddSubgroupClass.coe_sub, Pi.sub_apply, zero_sub, gt_iff_lt,
        neg_lt_neg_iff, Int.lt_iff_add_one_le, PreEudoxus] at h₀ h₁ h₂
      have f0 := (f.1 0).2
      have fn₂ := (f.1 n₂).2
      simp only [Finset.mem_Icc, L, U, zero_add, min_le_iff, le_max_iff, zero_sub, or_self] at f0 fn₂
      obtain (H1|H2) := fn₂.1 <;> linarith
    . intro h
      obtain ⟨n₀, hn₀, h₀⟩ := h 0
      obtain ⟨n₁, hn₁, h₁⟩ := h n₀
      obtain ⟨n₂, hn₂, h₂⟩ := h n₁
      simp only [Nat.cast_one, one_mul, AddSubgroupClass.coe_sub, Pi.sub_apply, sub_zero, gt_iff_lt,
        Int.lt_iff_add_one_le, PreEudoxus] at h₀ h₁ h₂
      have f0 := (f.1 0).2
      have fn₂ := (f.1 n₂).2
      simp only [Finset.mem_Icc, L, U, zero_add, min_le_iff, le_max_iff, zero_sub, or_self] at f0 fn₂
      have := abs_of_nonneg (hn₀.le.trans (hn₁.le.trans hn₂.le))
      simp [this] at fn₂
      obtain (H1|H2) := fn₂.2 <;> linarith

lemma proj_surjective : proj.Surjective := by
  rintro ⟨x, h0x, hx1⟩
  induction' x using Quotient.inductionOn with f
  obtain ⟨C, hfC⟩ := f.2
  let g := adjust f C hfC
  have hg : Int.funDeviatesBy g 1 := adjust_adjusted _ _ hfC
  have hgf : ⟦g⟧ = ⟦f⟧ := Quotient.sound (adjust_approx _ _ hfC)
  refine ⟨⟨fun n ↦ ⟨g.1 n, ?B⟩, adjust_adjusted _ _ hfC⟩, ?P⟩
  case P =>
    ext
    apply Quotient.sound
    exact adjust_approx f C hfC
  case B =>
    simp only [Finset.mem_Icc, L, U]
    rw [← hgf] at h0x hx1
    change ¬ (isPos _) at h0x hx1
    rw [isPos_iff_exists] at h0x
    swap; exact 0+1
    swap; exact (Int.funDeviatesBy.ofNat 0).sub hg
    rw [isPos_iff_exists] at hx1
    swap; exact 1+0
    swap; exact hg.sub (Int.funDeviatesBy.ofNat 1)
    simp at h0x hx1
    constructor
    . rw [← not_lt]
      intro H
      sorry
    . sorry

end AdjustedIntervalCover

end PreEudoxus

namespace Eudoxus

open PreEudoxus AdjustedIntervalCover in
instance : Compact {x : Eudoxus // 0 ≤ x ∧ x ≤ 1} where
  exists_CHaus_cover := ⟨AdjustedIntervalCover, inferInstance, proj, proj_surjective⟩

instance : CHaus {x : Eudoxus // 0 ≤ x ∧ x ≤ 1} := CHaus_of_Compact_of_Hausdorff _

end Eudoxus

#forbiddenAxioms Classical.choice

#explainForbiddenAxioms PreEudoxus.AdjustedIntervalCover.proj.proof_1 Classical.choice
