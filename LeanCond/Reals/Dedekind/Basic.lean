import Mathlib.Data.Rat.Order
import LeanCond.PseudoAxioms

import Mathlib.Tactic

attribute [-simp] neg_le_neg_iff

instance : ODisc ℚ := sorry

@[ext]
structure Dedekind where
  (L U : ℚ → Prop)
  (finite : (∃ q, L q) ∧ (∃ q, U q))
  (L_mono : ∀ {q₁ q₂}, q₁ ≤ q₂ → L q₂ → L q₁)
  (U_mono : ∀ {q₁ q₂}, q₁ ≤ q₂ → U q₁ → U q₂)
  (L_rounded : ∀ {q}, L q → ∃ q' > q, L q')
  (U_rounded : ∀ {q}, U q → ∃ q' < q, U q')
  (located : ∀ {q₁ q₂}, q₁ < q₂ → L q₁ ∨ U q₂)
  (disjoint : ∀ {q}, ¬ (L q ∧ U q))

namespace Dedekind

protected def neg (x : Dedekind) : Dedekind where
  L q := x.U (-q)
  U q := x.L (-q)
  finite := by
    obtain ⟨⟨q₁, h₁⟩, ⟨q₂, h₂⟩⟩ := x.finite
    refine ⟨⟨-q₂, ?_⟩, ⟨-q₁, ?_⟩⟩ <;> simpa
  L_mono {q₁ q₂} hle hL := x.U_mono (neg_le_neg hle) hL
  U_mono {q₁ q₂} hle hU := x.L_mono (neg_le_neg hle) hU
  L_rounded {q} h := by
    obtain ⟨q', h₁, h₂⟩ := x.U_rounded h
    have := Rat.neg
    refine ⟨-q', ?_, ?_⟩
    · simpa using neg_lt_neg h₁
    · simpa
  U_rounded {q} h := by
    obtain ⟨q', h₁, h₂⟩ := x.L_rounded h
    refine ⟨-q', ?_, ?_⟩
    · simpa using neg_lt_neg h₁
    · simpa
  located {q₁ q₂} h := (x.located (neg_lt_neg h)).symm
  disjoint {q} h := x.disjoint h.symm

instance : Neg Dedekind := ⟨Dedekind.neg⟩

protected lemma neg_neg (x : Dedekind) : -(-x) = x := by
  ext q
  · show L x _ ↔ L x _; rw [neg_neg]
  · show U x _ ↔ U x _; rw [neg_neg]

instance (x : Dedekind) (q : ℚ) : ODisc (x.L q) := by
  let E := {q' : ℚ // q < q' ∧ x.L q} ⊕ {q' : ℚ // q < q' ∧ x.U q'}
  let f : E → {q' : ℚ // q < q'} :=
    Sum.rec (fun x ↦ ⟨x, x.2.1⟩) (fun x ↦ ⟨x, x.2.1⟩)
  have hf : Function.Surjective f := by
    rintro ⟨q', h₁⟩
    cases x.located h₁
    case inl h => exact ⟨Sum.inl ⟨q', h₁, h⟩, rfl⟩
    case inr h => exact ⟨Sum.inr ⟨q', h₁, h⟩, rfl⟩
  obtain ⟨A, _i, p, hp, l, H⟩ := ODisc.collect _ _ _ hf
  let d : E → Bool := Sum.rec (fun _ => true) (fun _ => false)
  have i_dl : ∀ a, ODisc (d (l a) = true) := fun a => Eq.ODisc _ _ _
  suffices L x q ↔ ∃ a, d (l a) = true by
    rw [this]; infer_instance
  constructor
  · intro hLxq
    obtain ⟨q', hq'⟩ := x.L_rounded hLxq
    obtain ⟨a, ha⟩ := hp ⟨q', hq'.1⟩
    use a
    cases aux : l a
    case inl _ => rfl
    case inr u =>
      refine (x.disjoint ⟨hq'.2, ?_⟩).elim
      subst p
      have := (congrArg f aux).symm.trans ha
      simp only [Subtype.mk.injEq] at this
      subst q'
      exact u.2.2
  · rintro ⟨a, ha⟩
    cases aux : l a
    case inl q' => exact q'.2.2
    case inr q' => have := congrArg d aux; rw [ha] at this; contradiction

instance (x : Dedekind) (q : ℚ) : ODisc (x.U q) := by
  rw [← Dedekind.neg_neg x]
  show ODisc (L (-x) (-q))
  infer_instance

protected def LT (x y : Dedekind) : Prop :=
  ∃ q, x.U q ∧ y.L q

instance : LT Dedekind := ⟨Dedekind.LT⟩

protected lemma LT_def (x y : Dedekind) : x < y ↔ ∃ q, x.U q ∧ y.L q := Iff.rfl

protected lemma LT_irrefl (x : Dedekind) : ¬ x < x := by
  rintro ⟨q, hUq, hLq⟩
  exact x.disjoint ⟨hLq, hUq⟩

instance (x y : Dedekind) : ODisc (x < y) := by
  rw [Dedekind.LT_def]
  infer_instance

instance ODisc_LT (x y : Dedekind) : ODisc (x < y) := by
  rw [Dedekind.LT_def];
  infer_instance


-- new


-- Constants 0 and 1
@[reducible] def zero : Dedekind := {
  L := fun q => q < 0,
  U := fun q => q > 0,
  finite :=  by
    constructor
    · simp
      use - 1
      linarith
    · simp
      use 1
      linarith
  L_mono := by
    intro h hle hhle hle0
    linarith [hle, hle0]
  U_mono := fun hle h => h.trans_le hle,
  L_rounded := by
    intro h k
    use (h - h/2)
    constructor
    · linarith
    · simp
      linarith
  U_rounded := by
    intro h k
    use (h - h/2)
    constructor
    · linarith
    · simp
      linarith
  located := fun {q₁ q₂} h => by by_contra hn; push_neg at hn; linarith,
  disjoint := by
    intro h
    simp only [gt_iff_lt, not_and, not_lt]
    exact fun a => le_of_lt a
}

@[reducible] def one : Dedekind := {
  L := fun q => q < 1,
  U := fun q => q > 1,
  finite := by
    constructor
    · simp
      use 0
      linarith
    · simp
      use 2
      linarith
  L_mono := by
    intro h hle hhle hle0
    linarith [hle, hle0]
  U_mono := by
    intro hle h
    intro k j
    linarith
  L_rounded := by
    intro h k
    exact exists_rat_btwn k
  U_rounded := by
    intro h k
    simp only [gt_iff_lt]
    use (h+1)/2
    constructor
    · linarith
    · linarith
  located := fun {q₁ q₂} h => by by_contra hn; push_neg at hn; linarith,
  disjoint := by
    intro h
    simp only [gt_iff_lt, not_and, not_lt]
    intro k
    exact le_of_lt k
}

instance : Zero Dedekind := ⟨zero⟩
instance : One Dedekind := ⟨one⟩

-- Embedding ℚ →  Dedekind
def ofRat (r : ℚ) : Dedekind := {
  L := fun q => q < r,
  U := fun q => q > r,
  finite := by
    constructor
    · simp
      exact exists_rat_lt r
    · simp
      exact exists_rat_gt r
  L_mono := by
    intro h hle hhle hle0
    linarith [hle, hle0]
  U_mono := fun hle h => h.trans_le hle,
  L_rounded := by
    intro h k
    exact exists_rat_btwn k
  U_rounded := by
    intro h k
    simp only [gt_iff_lt]
    use (h+r)/2
    constructor
    · linarith
    · linarith
  located := fun {q₁ q₂} h => by by_contra hn; push_neg at hn; linarith,
  disjoint := by
    intro q
    simp
    intro k
    exact le_of_lt k
}
instance : Coe ℚ Dedekind := ⟨ofRat⟩

-- Arithmetic sorries
def Dadd (x y : Dedekind) : Dedekind := by

  sorry
instance : Add Dedekind := ⟨Dadd⟩

def Dsub (x y : Dedekind) : Dedekind := x + (-y)
instance : Sub Dedekind := ⟨Dsub⟩

def Dmul (x y : Dedekind) : Dedekind := sorry
instance : Mul Dedekind := ⟨Dmul⟩

def pnatInv (n : PNat) : Dedekind := ↑(1/(n : ℚ))
instance : Inv PNat Dedekind := ⟨pnatInv⟩

axiom Dedekind_is_CHaus : CHaus Dedekind

protected def LE (x y : Dedekind) : Prop := ¬ y < x
instance : LE Dedekind := ⟨Dedekind.LE⟩
instance : HasLe Dedekind := ⟨Dedekind.LE⟩
@[simp] lemma LE_def (x y : Dedekind) : x ≤ y ↔ ¬ y < x := Iff.rfl
instance ODisc_LE (x y : Dedekind) : ODisc (x ≤ y) := by
  simp [LE_def]

  sorry

lemma le_antisymm (x y : Dedekind) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := sorry
lemma lt_of_le_not_le (x y : Dedekind) (hxy : x ≤ y) (hne : ¬ y ≤ x) : x < y := sorry

axiom archimedean_pos (x : Dedekind) (hx : 0 < x) : ∃ k : PNat, (k : PNat)⁻¹ < x
axiom archimedean_neg (x : Dedekind) (hx : x < 0)   : ∃ k : PNat, x < -(k : PNat)⁻¹

axiom add_lt_add_iff_left  (a b c : Dedekind) : a + c < b + c ↔ a < b
axiom zero_lt_one          : (0 : Dedekind) < 1
axiom le_of_lt_or_eq       (x y : Dedekind) : x < y ∨ x = y → x ≤ y
axiom lt_iff_le_not_le     (x y : Dedekind) : x < y ↔ x ≤ y ∧ ¬ y ≤ x

-- new


end Dedekind

-- avoiding choice is hopeless with the current state of mathlib

-- #forbiddenAxioms Classical.choice

-- #explainForbiddenAxioms Dedekind.neg.proof_1 Classical.choice
