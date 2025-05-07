import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup

import LeanCond.ODiscArrow
import LeanCond.Defs

section cond

instance Int.ODisc : ODisc ℤ := sorry

instance DecidableEq.Hausdorff (X : Type) [DecidableEq X] : Hausdorff X where
  compact_diagonal _ _ := inferInstance

instance Pi.Hausdorff (X : Sort u) (Y : X → Sort v) [ODisc X] [∀ x, Hausdorff (Y x)] :
  Hausdorff ((x : X) → Y x) := by
  constructor
  intro f g
  rw [Function.funext_iff]
  infer_instance

instance Subtype.Hausdorff (X : Sort u) (P : X → Prop) [Hausdorff X] :
  Hausdorff {x // P x} := by
  constructor
  intro x y
  rw [Subtype.ext_iff]
  infer_instance

end cond

section move_me

-- AAHRG!
-- #print axioms Nat.lt_pow_self
-- 'Nat.lt_pow_self' depends on axioms: [propext, Classical.choice, Quot.sound]

theorem Nat.lt_pow_self' {p : ℕ} (hp : 1 < p) (n : ℕ) : n < p ^ n := by
  induction n
  case zero => rw [pow_zero]; decide
  case succ n IH =>
    rw [pow_succ]
    rw [lt_iff_add_one_le] at IH
    refine lt_of_le_of_lt IH ?_
    simpa using Nat.mul_lt_mul_of_pos_left hp (lt_of_lt_of_le (zero_lt_succ _) IH)

lemma Int.sub_pos (a b : ℤ) : 0 < a - b ↔ b < a :=
  ⟨Int.lt_of_sub_pos, Int.sub_pos_of_lt⟩

lemma Int.abs_add (a b : ℤ) : abs (a + b) ≤ abs a + abs b := by
  simp only [← Int.coe_natAbs, ← Int.ofNat_add, Int.ofNat_le]
  apply natAbs_add_le

lemma Int.abs_sub_abs_le_abs_sub (a b : ℤ) : abs a - abs b ≤ abs (a - b) := by
  apply Int.sub_right_le_of_le_add
  simpa only [sub_add_cancel] using abs_add (a - b) b

lemma Int.abs_mul (a b : ℤ) : abs (a * b) = abs a * abs b := by
  simp only [← Int.coe_natAbs, Int.natAbs_mul, Int.ofNat_mul]

end move_me

#forbiddenAxioms Classical.choice
