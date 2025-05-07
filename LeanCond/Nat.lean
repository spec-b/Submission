import Mathlib.Init.Data.Nat.Basic
import Mathlib.Tactic.Basic

/-!
Missing lemmas about `Nat`.
-/

-- move this
@[simp]
lemma Nat.not_add_lt_left (m n : ℕ) : ¬ m + n < m := by
  suffices ¬ m + n < m + 0 by rwa [Nat.add_zero] at this
  rw [Nat.add_lt_add_iff_left]
  apply Nat.not_lt_zero

-- move this
@[simp]
lemma Nat.not_add_lt_right (m n : ℕ) : ¬ m + n < n := by
  rw [Nat.add_comm]
  apply Nat.not_add_lt_left
