import Mathlib.Data.Int.Dvd.Basic
import Mathlib.Data.Int.Order.Basic

import LeanCond.ForbiddenAxioms

import Mathlib.Tactic

namespace Int

section prereqs

lemma abs_eq_neg_self_of_nonpos {p : ℤ} (hp : p ≤ 0) : |p| = -p := by
  apply if_pos
  apply hp.trans
  simpa only [Left.nonneg_neg_iff]

lemma abs_eq_self_of_nonneg {p : ℤ} (hp : 0 ≤ p) : |p| = p := by
  simpa only [abs_neg, neg_neg] using
    abs_eq_neg_self_of_nonpos (neg_nonpos_of_nonneg hp)

-- instance without choice
def LOACG : LinearOrderedAddCommGroup ℤ :=
  { inferInstanceAs (AddCommGroup ℤ) with
    decidableLE := inferInstance,
    add_le_add_left := fun a b h c => add_le_add_left h c,
    le_total := fun a b => le_total a b, }

-- #eval fmod 0 0
-- #eval fmod 17 0

-- #eval fmod 17 10
-- #eval fmod 17 (-10)
-- #eval fmod (-17) 10
-- #eval fmod (-17) (-10)

-- #eval fdiv 17 10
-- #eval fdiv 17 (-10)
-- #eval fdiv (-17) 10
-- #eval fdiv (-17) (-10)

-- lemma fdiv_neg : ∀ (p q : ℤ), q ≠ 0 → ¬ (q ∣ p) → fdiv p (-q) = - fdiv p q - 1
--   | 0,       _      , h => by simp
--   | _,       0      , h => (h rfl).elim
--   | ofNat (Nat.succ m), ofNat (Nat.succ n), h => by
--     intro h'
--     show fdiv (ofNat (Nat.succ m)) -[n+1] = - fdiv (ofNat (Nat.succ m)) (ofNat (Nat.succ n)) - 1
--     dsimp only [fdiv]
--     simp
--   | Nat.succ m,  -[n+1] , h => by sorry
--   | -[m+1],  ofNat n , h => by sorry
--   | -[m+1],  -[n+1]  , h => by simp [fdiv]; sorry

-- lemma fmod_neg : ∀ (p q : ℤ), q ≠ 0 → ¬ (q ∣ p) → fmod p q - fmod p (-q) = q
--   | 0,       _      , h => by simp
--   | _,       0      , h => (h rfl).elim
--   | ofNat (Nat.succ m), ofNat (Nat.succ n), h => by
--     intro h'
--     show fmod (ofNat (Nat.succ m)) (ofNat (Nat.succ n)) - fmod (ofNat (Nat.succ m)) (-[n+1]) = ofNat (Nat.succ n)
--     dsimp only [fmod]
--     simp
--   | Nat.succ m,  -[n+1] , h => by sorry
--   | -[m+1],  ofNat n , h => by sorry
--   | -[m+1],  -[n+1]  , h => by simp [fmod]; sorry

lemma fmod_nonpos' (p : ℤ) {q : ℤ} (hq : q < 0) : fmod p q ≤ 0 := by
  sorry

lemma lt_fmod_of_neg  (p : ℤ) {q : ℤ} (hq : q < 0) : q < fmod p q := by
  sorry

end prereqs

/--
If `m` and `n` are two integers, we denote by `m ÷ n` the *optimal Euclidean division* or `m` and `n`.
For `n = 0`, we set `m ÷ n = 0`.
For `n ≠ 0`, it is `⌊(m/n : ℚ)⌉ = ⌊(m/n + 1/2 : ℚ)⌋`.
In other words, the rational number `m/n` rounded to the nearest integer, where `(2k+1)/2` is rounded down to `k`.
In yet other words, it is the unique integer `r` satisfying `2m - |n| ≤ 2rn < 2m + |n|`.
See also page~4 of~\cite{acampo2003natural}.
-/
def rdiv (p q : ℤ) : ℤ :=
  Int.fdiv (2 * p + q) (2 * q)

@[inherit_doc] infixl:70 " ÷ "   => Int.rdiv
macro_rules | `($x ÷ $y)   => `(binop% Int.rdiv $x $y)

@[simp]
lemma rdiv_zero (p : ℤ) : p ÷ 0 = 0 := by simp [rdiv]

lemma abs_rdiv_two_mul_le (p q : ℤ) (hq : q ≠ 0) :
    |2 * q * (p ÷ q) - 2 * p| ≤ |q| := by
  dsimp [rdiv]
  have h := fdiv_add_fmod (2 * p + q) (2 * q)
  conv_rhs at h => rw [add_comm]
  rw [← sub_eq_sub_iff_add_eq_add] at h
  rw [h]; clear h
  have aux := @abs_sub_le_iff ℤ Int.LOACG
  obtain hq|hq := hq.lt_or_lt
  · have h2q : 2 * q < 0 := by
      simp only [mul_neg_iff, zero_lt_two, hq, and_self, true_or]
    have h1 := fmod_nonpos' (2 * p + q) h2q
    have h2 := lt_fmod_of_neg (2 * p + q) h2q
    rw [abs_eq_neg_self_of_nonpos hq.le, aux, sub_le_comm, Int.sub_neg, ← two_mul, tsub_le_iff_left, Int.add_right_neg]
    refine ⟨h2.le, h1⟩
  · have h2q : 0 < 2 * q := by
      simp only [zero_lt_two, zero_lt_mul_left, hq]
    have h1 := fmod_nonneg' (2 * p + q) h2q
    have h2 := fmod_lt_of_pos (2 * p + q) h2q
    rw [abs_eq_self_of_nonneg hq.le, aux, sub_le_self_iff, tsub_le_iff_left, ← two_mul]
    exact ⟨h1, h2.le⟩

-- #explainForbiddenAxioms Int.abs_rdiv_two_mul_le Classical.choice

-- #forbiddenAxioms Classical.choice

-- @[simp]
-- lemma rdiv_one (p : ℤ) : p.rdiv 1 = p := by simp [rdiv]; sorry

-- /--
-- If `m` and `n` are two integers, we denote by `m ÷ n` the *optimal Euclidean division* or `m` and `n`.
-- For `n = 0`, we set `m ÷ n = 0`.
-- For `n ≠ 0`, it is `⌊(m/n : ℚ)⌉`.
-- In other words, the rational number `m/n` rounded to the nearest integer, where `(2k+1)/2` is rounded down to `k`.
-- In yet other words, it is the unique integer `r` satisfying `2m - |n| ≤ 2rn < 2m + |n|`.
-- See also page~4 of~\cite{acampo2003natural}.
-- -/
-- def rdiv (p q : ℤ) : ℤ :=
--   if q = 0 then 0 else
--   if 2 * (p.emod q) ≤ |q| then p.ediv q else p.ediv q + q.sign

-- @[simp]
-- lemma rdiv_zero (p : ℤ) : p ÷ 0 = 0 := by simp [rdiv]

-- lemma rdiv_spec (p q : ℤ) (hq : q ≠ 0) :
--   2 * p - |q| ≤ 2 * q * (p ÷ q) ∧
--   2 * q * (p ÷ q) < 2 * p + |q| := by
--   dsimp only [rdiv]
--   rw [if_neg hq]
--   have H : 2 * p = 2 * _ := congr_arg (2 * .) (ediv_add_emod p q).symm
--   rw [mul_add, ← mul_assoc] at H
--   have h : Decidable (2 * emod p q ≤ |q|) := inferInstance
--   refine h.casesOn ?N ?P <;> intro h
--   case P =>
--     rw [if_pos h]
--     refine ⟨?_, ?_⟩
--     . apply Int.sub_right_le_of_le_add
--       rw [H]
--       exact Int.add_le_add le_rfl h
--     . rw [H, add_assoc]
--       apply Int.lt_add_of_le_of_pos le_rfl
--       apply Int.add_pos_of_nonneg_of_pos
--       . exact Int.mul_nonneg (by decide) (Int.emod_nonneg p hq)
--       . rwa [Int.abs_eq_natAbs, Int.ofNat_pos, Int.natAbs_pos]
--   case N =>
--     rw [if_neg h]
--     refine ⟨?_, ?_⟩
--     . apply Int.sub_right_le_of_le_add
--       rw [H, mul_add, add_assoc]
--       refine Int.add_le_add le_rfl ?_
--       rw [two_mul, mul_assoc, mul_sign, coe_natAbs, two_mul]
--       refine Int.add_le_add ?_ (Int.emod_lt p hq).le
--       refine le_trans (Int.emod_lt p hq).le ?_
--       exact Int.le_add_of_nonneg_left (abs_nonneg _)
--     . rw [H, add_assoc, mul_add]
--       apply Int.add_lt_add_left
--       rw [mul_assoc, mul_sign, coe_natAbs, two_mul]
--       apply Int.add_lt_add_right
--       exact lt_of_not_le h

-- lemma rdiv_existsUnique (p q : ℤ) (hq : q ≠ 0) :
--     ∃! r, 2 * p - |q| ≤ 2 * q * r ∧ 2 * q * r < 2 * p + |q| := by
--   refine ⟨p ÷ q, rdiv_spec _ _ hq, ?_⟩
--   intro r hr
--   simp only [rdiv, hq, if_false]
--   -- have hpq := ediv_add_emod p q
--   split_ifs
--   case pos h => sorry
--   case neg h => sorry

-- lemma abs_rdiv_two_mul_le (p q : ℤ) (hq : q ≠ 0) :
--   |2 * q * (p ÷ q) - 2 * p| ≤ |q| := by
--   apply max_le
--   · apply Int.sub_right_le_of_le_add
--     rw [add_comm]
--     exact (rdiv_spec _ _ hq).2.le
--   · rw [neg_sub]
--     apply Int.sub_le_of_sub_le
--     exact (rdiv_spec _ _ hq).1

-- lemma rdiv_neg_left (p q : ℤ) (H : q ∣ (2 * p) → q ∣ p) :
--     (-p) ÷ q = - (p ÷ q) := by
--   by_cases hq : q = 0
--   · simp [rdiv, hq]
--   apply (rdiv_existsUnique _ _ hq).unique (rdiv_spec _ _ hq)
--   have aux :
--     -(2 * q * rdiv p q) ≤ -(2 * p - |q|) ∧
--     -(2 * p + |q|) < -(2 * q * rdiv p q) := by
--     have aux := rdiv_spec p q hq
--     exact ⟨Int.neg_le_neg aux.1, Int.neg_lt_neg aux.2⟩
--   apply aux.symm.imp <;> clear aux
--   · intro h
--     convert h.le using 1
--     · simp only [mul_neg, neg_add, ← sub_eq_add_neg]
--     · simp only [mul_neg]
--   · intro h
--     suffices -(2 * q * rdiv p q) ≠ -(2 * p - |q|) by
--       have := h.lt_of_ne this
--       convert this using 1
--       · simp only [mul_neg]
--       · simp only [mul_neg, neg_add, sub_eq_add_neg, neg_neg]
--     clear h; intro h
--     simp only [neg_inj] at h
--     sorry

-- -- TODO: `H` is not sufficient if `q < 0`.
-- -- lemma rdiv_eq_zero (p q : ℤ) (H : q ≠ 0 → (abs q < 2 * p + 2 * q) ∧ 2 * p + abs q ≤ 2 * q) :
-- --   rdiv p q = 0 := by
-- --   apply @Decidable.byCases (q = 0)
-- --   . rintro rfl; rw [rdiv, if_pos]; rfl
-- --   . intro h
-- --     obtain ⟨H1, H2⟩ := H h
-- --     obtain ⟨h1, h2⟩ := rdiv_spec p q h
-- --     have h2 := lt_of_lt_of_le h2 H2
-- --     sorry

-- /-
--   2 * p - abs q ≤ 2 * q * (p ÷ q)
--   2 * q * (p ÷ q) < 2 * p + abs q
--   ------------
--   2 * p - abs q ≤ 2 * q * (p ÷ q)
--   ↔
--   q.sign * (2 * p - abs q) / 2 * q ≤ q.sign * (p ÷ q)
--   ------------
--   2 * q * (p ÷ q) < 2 * p + abs q
--   ↔
--   q.sign * (p ÷ q) < q.sign * (2 * p + abs q) / 2 * q
-- -/

end Int
