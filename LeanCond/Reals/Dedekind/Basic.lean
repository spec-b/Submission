import Mathlib.Data.Rat.Order
import LeanCond.PseudoAxioms

import Mathlib.Tactic

universe u v

attribute [-simp] neg_le_neg_iff

instance (q r : ℚ):  ODisc (q < r):= by
exact Decidable.ODisc

instance (q r: ℚ) : ODisc (q ≤ r):= by
exact Decidable.ODisc


instance : ODisc ℚ := by sorry

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

@[simp, reducible]
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

def Dadd (x y : Dedekind) : Dedekind :=
{ L := λ q => ∃ q₁ q₂, x.L q₁ ∧ y.L q₂ ∧ q₁ + q₂ ≥ q
, U := λ q => ∃ q₁ q₂, x.U q₁ ∧ y.U q₂ ∧ q₁ + q₂ ≤ q
, finite := by  -- No comma here
    rcases x.finite with ⟨⟨a, ha⟩, _⟩
    rcases y.finite with ⟨⟨b, hb⟩, _⟩
    refine ⟨⟨a + b, ?_⟩, ⟨a + b, ?_⟩⟩
    · simp [ha, hb]; linarith
    · simp [ha, hb]; linarith
, L_mono := by
    intro a b ab
    simp
    intro i xi j yj bij
    exact ⟨a, b, x.L_mono (le_trans (le_add_left b a))⟩
, U_mono := by
    intro a b ab
    simp
    intro i xi j yj bij
    use a 
    have k1 : x.U a := by sorry 
    use k1 
    use j 
    use yj 
    sorry 
, L_rounded := by
    intro q
    simp
    intro a b hxa hyb hsum

    rcases x.L_rounded hxa with ⟨a', ha', hxa'⟩
    rcases y.L_rounded hyb with ⟨b', hb', hyb'⟩
    use a' + b'
    constructor
    · linarith
      sorry 
    · simp [add_pos]; linarith 
      sorry 
  U_rounded := by
    intro a
    simp
    intros b uxb c uyc hbc
    let m := (b * c + a) / 2
    use m
    constructor
    · have k1 : b * c < m  := by 
        sorry 
      aesop 
      linarith 
    · use b 
      constructor 
      · use uxb 
         
      · use (b/4) 
        aesop 
        · sorry 
        ·  
          sorry  
        sorry
       
, located := by
    intros q₁ q₂ h
    by_cases H : x.L (q₂ - q₁)
    · left; obtain ⟨a, ha⟩ := H; exact (x.L_mono (by linarith) ha)
    · right; have : x.U (q₂ - q₁) := x.located (by linarith); exact this
, disjoint := by
    intros q h
    simp only [not_exists, not_and] at h
    rcases h with ⟨hq, ⟨⟨a, b, hxa, hyb, hsum⟩, ⟨c, d, huc, hud, hsum'⟩⟩⟩
    linarith
}


instance : Add Dedekind := ⟨Dadd⟩

def Dsub (x y : Dedekind) : Dedekind := x + (-y)
instance : Sub Dedekind := ⟨Dsub⟩

def Dmul_pos (x y : Dedekind) (_hx_pos : (0 : Dedekind) < x) (_hy_pos : (0 : Dedekind) < y) : Dedekind := {
  L := fun q => q < 0 ∨ (∃ lx ly, x.L lx ∧ y.L ly ∧ lx > 0 ∧ ly > 0 ∧ q < lx * ly),
  U := fun q => ∃ ux uy, x.U ux ∧ y.U uy ∧ ux > 0 ∧ uy > 0 ∧ q > ux * uy,
  finite := by
    simp

    sorry
    ,
  L_mono := by
    simp
    intro q1 q2 q12 h1
    cases' h1 with h1 h2
    · apply Or.inl
      have h2: q1 ≤ q2 ∧ q2 < 0 := by
        constructor
        · linarith
        · linarith
      sorry
    · apply Or.inr
      have h2: q1 ≤ q2 ∧ q2 > 0 := by
        use q12
        rcases h2 with ⟨h2, k1, k2, hk1, hk2, hq1, hq2⟩


        sorry



    apply Or.inl
    cases' h1 with h1 h2
    · linarith
    · --have k1 : ∃ q, x.L q := x.finite.1
      --rcases k1 with ⟨k, hk⟩
      rcases h2 with ⟨k1, k2, hk1, hk2, hq1, hq2, hlt⟩
      have p1 : q1 < k1 * hk1 := by
        exact LE.le.trans_lt q12 hlt
      have p2: 0 < k1 * hk1 := by
        apply mul_pos
        use hq1
        use hq2


      sorry

  ,
  U_mono := by
    simp
    intro q1 q2 q12 h1 ux x1 ux1 h1pos x1pos ml
    use h1
    use ux
    use x1
    use ux1
    use h1pos
    use x1pos
    exact LT.lt.trans_le ml q12

  ,
  L_rounded := sorry,
  U_rounded := sorry,
  located := sorry,
  disjoint := sorry
}



def Dmul (x y : Dedekind) : Dedekind :=
if 0 ∈ x.L then
  if 0 ∈ y.L then mul_pos x y
  else neg (mul_pos x (neg y))
else
  if 0 ∈ y.L then neg (mul_pos (neg x) y)
  else mul_pos (neg x) (neg y)


instance : Mul Dedekind := ⟨Dmul⟩

def pnatInv (n : PNat) : Dedekind := ↑(1/(n : ℚ))
instance : Inv PNat Dedekind := ⟨pnatInv⟩

axiom Dedekind_is_CHaus : CHaus Dedekind

protected def LE (x y : Dedekind) : Prop := ¬ y < x
instance : LE Dedekind := ⟨Dedekind.LE⟩

@[simp]
@[reducible]
lemma LE_def (x y : Dedekind) : x ≤ y ↔ ¬ y < x := Iff.rfl
instance ODisc_LE (x y : Dedekind) : ODisc (x ≤ y) := by
  simp [LE_def]

  sorry

lemma le_antisymm (x y : Dedekind) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := sorry
lemma lt_of_le_not_le (x y : Dedekind) (hxy : x ≤ y) (hne : ¬ y ≤ x) : x < y := sorry

--axiom archimedean_pos (x : Dedekind) (hx : 0 < x) : ∃ k : PNat, (k : PNat)⁻¹ < x
--axiom archimedean_neg (x : Dedekind) (hx : x < 0)   : ∃ k : PNat, x < -(k : PNat)⁻¹

axiom add_lt_add_iff_left  (a b c : Dedekind) : a + c < b + c ↔ a < b
axiom zero_lt_one          : (0 : Dedekind) < 1
axiom le_of_lt_or_eq       (x y : Dedekind) : x < y ∨ x = y → x ≤ y
axiom lt_iff_le_not_le     (x y : Dedekind) : x < y ↔ x ≤ y ∧ ¬ y ≤ x

-- new


end Dedekind

-- avoiding choice is hopeless with the current state of mathlib

-- #forbiddenAxioms Classical.choice

-- #explainForbiddenAxioms Dedekind.neg.proof_1 Classical.choice


-- new stuff

axiom Dedekind_is_CHaus : CHaus Dedekind


-- The interval I = [-1, 1]
def I_interval : Type := {r : Dedekind // -(1 : Dedekind) ≤ r ∧ r ≤ (1 : Dedekind)}


@[instance] lemma I_interval_is_CHaus_derived : CHaus I_interval := by
  -- I_interval is Subtype P where P r is (-(1) ≤ r ∧ r ≤ (1)).
  -- Need CHaus Real (Dedekind_is_CHaus_ax).
  -- Need ∀ r, CHaus (P r).
  -- P r is (Prop ∧ Prop). (-(1) ≤ r) is ¬(r < -1). This is ODisc (r < -1) → ODisc (¬(r < -1)).
  -- ODisc (r < -1) by odisc_LT. So ODisc (¬(r < -1)).
  -- Propositions that are ODisc are CHaus via Decidable.CHaus if they are Decidable.
  -- Or if ODisc P → CHaus P is an axiom for Props. Let's assume ODisc implies CHaus for Props.
  -- If P is ODisc, P is CHaus (needs P → Decidable P or ODisc P → CHaus P axiom for Props)
  have h_prop_chaus :
  ∀ r : Dedekind, CHaus ((-(1 : Dedekind) ≤ r ∧ r ≤ (1 : Dedekind))) := fun r => by

    apply And.CHaus -- from PseudoAxioms
    · exact Decidable.CHaus (decidableLE (-(1:Dedekind)) r) -- if ODisc implies Decidable for props
      -- Dedekind.odisc_LE implies ODisc (Prop). Assuming ODisc Prop -> CHaus Prop
      -- Assume ODisc P → CHaus P for Props (via Decidable P)
    · exact Decidable.CHaus (decidableLE r (1:Dedekind))
  apply Subtype.CHaus -- from PseudoAxioms
  exact Dedekind.Dedekind_is_CHaus_ax
  exact h_prop_chaus


-- The "zero" element of I
def zero_I_interval : I_interval := ⟨0, by
  constructor
  · simp [Dedekind.LE_def_simp]; intro h_lt_neg_one_zero -- 0 < -1
    -- Need to show 0 < -1 is false. (0 < -1) ↔ ∃q, 0.U q ∧ (-1).L q
    -- 0.U q is q > 0. (-1).L q is q < -1. (q > 0 ∧ q < -1) is false.
    rintro ⟨q_contra, h_U0, h_Lneg1⟩; linarith [h_U0, h_Lneg1]
  · simp [Dedekind.LE_def_simp]; intro h_lt_zero_one -- 1 < 0
    rcases h_lt_zero_one with ⟨q_contra, h_U1, h_L0⟩
    -- h_U1 is q_contra > 1. h_L0 is q_contra < 0. It's a contradiction.
    linarith [h_U1, h_L0]
⟩

-- An open subset U_prop of I_interval containing 0
variable {U_prop : I_interval → Prop} (hU_open_prop : Prop)
variable (hU_zero_mem_prop : U_prop zero_I_interval)
variable (hU_prop_ODisc : ∀ r : I_interval, ODisc (U_prop r))

-- The index set S_val = ℕ⁺ ⊔ {*}
-- PNat_is_ODisc should be from LeanCond.Axioms if Nat.ODisc and Subtype.ODisc exist
instance PNat_ODisc_instance : ODisc PNat := by
  apply Subtype.ODisc; exact Nat.ODisc; exact fun n => Decidable.ODisc (decidableLT 0 n)

instance Unit_ODisc_instance : ODisc Unit := by exact Equiv.ODisc (Fin 1) (Equiv.funUnique PUnit (Fin 1))⁻¹
  -- Unit is Equiv (Fin 1). Use Fin.ODisc and Equiv.ODisc

def S_val := Sum PNat Unit
@[instance]
lemma S_val_is_ODisc : ODisc S_val := by
  apply Sigma'.ODisc -- Sum A B is Σ (b : Bool), if b then A else B.

  sorry -- needs something like Sum.ODisc


-- The family of sets W_sets(j)
def W_nat_set (n : PNat) (r_i : I_interval) : Prop :=
  let r_val := r_i.val
  r_val < -(Dedekind.pnatInv n) ∨ r_val > (Dedekind.pnatInv n)

def W_star_set (r_i : I_interval) : Prop := U_prop r_i

def W_sets (s : S_val) (r_i : I_interval) : Prop :=
  Sum.casesOn s (fun n => W_nat_set n r_i) (fun _ => W_star_set r_i)

@[instance] lemma W_nat_set_ODisc (n : PNat) (r_i : I_interval) : ODisc (W_nat_set n r_i) :=
by unfold W_nat_set; exact Or.ODisc

@[instance] lemma W_star_set_ODisc (r_i : I_interval) : ODisc (W_star_set r_i) :=
by unfold W_star_set; exact hU_prop_ODisc r_i
@[instance] lemma W_sets_ODisc (s : S_val) (r_i : I_interval) : ODisc (W_sets s r_i) :=
by unfold W_sets; cases s <;> simp <;> infer_instance


axiom W_nat_set_is_open (n : PNat) : Prop -- Placeholder for "openness"
axiom W_star_set_is_open : Prop       -- Placeholder for "openness" (hU_open_prop)


lemma squeeze_to_zero_Real (r : Dedekind) (h_squeeze_bounds : ∀ n : PNat, -(Dedekind.pnatInv n) ≤ r ∧ r ≤ (Dedekind.pnatInv n)) : r = (0 : Dedekind) := by
  have hr_le_zero : r ≤ (0 : Dedekind) := by
    apply le_of_not_gt -- classical for Prop: ¬(0 < r)
    intro hr_gt_zero
    rcases Dedekind.archimedean_pos r hr_gt_zero with ⟨k, hk_arch⟩
    have h_upper_bound_k := (h_squeeze_bounds k).right
    have : Dedekind.pnatInv k < r ∧ r ≤ Dedekind.pnatInv k := ⟨hk_arch, h_upper_bound_k⟩
    exact not_lt_of_le this.2 this.1 -- Contradiction from P < Q and Q ≤ P
  have hr_ge_zero : (0 : Dedekind) ≤ r := by
    apply ge_of_not_lt -- classical for Prop: ¬(r < 0)
    intro hr_lt_zero
    rcases Dedekind.archimedean_neg r hr_lt_zero with ⟨k, hk_arch⟩
    have h_lower_bound_k := (h_squeeze_bounds k).left
    have : r < -(Dedekind.pnatInv k) ∧ -(Dedekind.pnatInv k) ≤ r := ⟨hk_arch, h_lower_bound_k⟩
    exact not_lt_of_le this.2 this.1
  exact Dedekind.le_antisymm_dedekind r 0 hr_le_zero hr_ge_zero


lemma cover_lemma_Real : ∀ r_i : I_interval, ∃ j : S_val, W_sets j r_i := by
  intro r_i; let r_val := r_i.val
  by_contra h_not_covered; push_neg at h_not_covered
  have h_not_in_U_prop : ¬ W_star_set r_i := by exact h_not_covered (Sum.inr Unit.unit)
  unfold W_star_set at h_not_in_U_prop
  have h_forall_not_W_nat_set : ∀ (n : PNat), ¬ W_nat_set n r_i := by
    intro n; exact h_not_covered (Sum.inl n)
  have h_squeeze_bounds_val : ∀ n : PNat, -(Dedekind.pnatInv n) ≤ r_val ∧ r_val ≤ (Dedekind.pnatInv n) := by
    intro n; specialize h_forall_not_W_nat_set n; unfold W_nat_set at h_forall_not_W_nat_set
    rw [not_or_distrib] at h_forall_not_W_nat_set; cases h_forall_not_W_nat_set
    split <;> (rw [Dedekind.LE_def_simp] at *; classical; simp_all) -- uses classical for ¬¬P → P
  have h_r_val_is_zero_real : r_val = (0 : Real) := by exact squeeze_to_zero_Real r_val h_squeeze_bounds_val
  have h_r_i_is_zero_I_interval : r_i = zero_I_interval := by ext; exact h_r_val_is_zero_real
  exact h_not_in_U_prop (by rwa [h_r_i_is_zero_I_interval])

def Sigma_W_j_type_Real : Type := Σ' (j : S_val), {x_i : I_interval // W_sets j x_i}


def u_map_Real (val : Σ (j : S_val), {x_i : I_interval // W_sets j x_i}) : I_interval := val.2.val

lemma u_map_is_epi_Real : Function.Surjective u_map_Real := by
  intro y_i; rcases cover_lemma_Real y_i with ⟨j_val, h_W_j_y_i⟩
  use ⟨j_val, ⟨y_i, h_W_j_y_i⟩⟩; simp [u_map_Real]

def is_finite_subset_prop_Real (P_sets : S_val → Prop) : Prop :=
  ∃ (L : List S_val), ∀ s : S_val, (P_sets s ↔ s ∈ L)

theorem finite_subcover_exists_Real :
  ∃ (S_fin_sets_prop : S_val → Prop) (_ : is_finite_subset_prop_Real S_fin_sets_prop),
    ∀ y_i : I_interval, ∃ j : S_val, S_fin_sets_prop j ∧ W_sets j y_i := by
  let X_some := Σ (j : S_val), {x_i : I_interval // W_sets j x_i}
  rcases CHaus.collect I_interval X_some u_map_Real u_map_is_epi_Real with
    ⟨X_prime_type, _hX_prime_CHaus, p_map_fn, hp_map_epi_fn, r_map_fn, hr_comp_eq_p_fn⟩
  let q_idx_fn (val : X_some) : S_val := val.1
  let map_X_prime_to_S_val := q_idx_fn ∘ r_map_fn

  rcases Cond.factor_fin map_X_prime_to_S_val with
    ⟨k_nat, α_map_fn, β_map_fn, h_factor_beta_alpha_fn⟩

  let finset_S_val_fin : Finset S_val := Finset.image β_map_fn Finset.univ
  let S_val_fin_prop (s_v : S_val) : Prop := s_v ∈ finset_S_val_fin

  have S_val_fin_prop_is_finite : is_finite_subset_prop_Real S_val_fin_prop := by
    use finset_S_val_fin.toList
    intro s; rw [Finset.mem_toList]

  use S_val_fin_prop, S_val_fin_prop_is_finite
  intro y_i_target
  rcases hp_map_epi_fn y_i_target with ⟨x_p_val_fn, h_p_x_p_eq_y_i_fn⟩


  have h_y_i_eq_u_r_x_p_fn : y_i_target = u_map_Real (r_map_fn x_p_val_fn) := by
    rw [←h_p_x_p_eq_y_i_fn, ←hr_comp_eq_p_fn]; rfl
  let r_x_p_mapped_val_fn := r_map_fn x_p_val_fn
  let j0_idx_val := q_idx_fn r_x_p_mapped_val_fn
  let actual_val_from_r_x_p_fn := r_x_p_mapped_val_fn.2.val

  have h_u_map_eval_check_fn : u_map_Real r_x_p_mapped_val_fn = actual_val_from_r_x_p_fn := by
    simp [u_map_Real]
  rw [h_u_map_eval_check_fn] at h_y_i_eq_u_r_x_p_fn
  have h_j0_idx_is_beta_alpha_fn : j0_idx_val = β_map_fn (α_map_fn x_p_val_fn) := by
    rw [show map_X_prime_to_S_val = q_idx_fn ∘ r_map_fn by rfl] at h_factor_beta_alpha_fn
    rw [←h_factor_beta_alpha_fn]
    rfl
  have h_j0_idx_in_S_fin_prop_fn : S_val_fin_prop j0_idx_val := by
    unfold S_val_fin_prop; rw [h_j0_idx_is_beta_alpha_fn]
    apply Finset.mem_image_of_mem; exact Finset.mem_univ (α_map_fn x_p_val_fn)
  have h_W_j0_idx_y_i_fn : W_sets j0_idx_val y_i_target := by
    rw [h_y_i_eq_u_r_x_p_fn]; exact r_x_p_mapped_val_fn.2.property
  use j0_idx_val, ⟨h_j0_idx_in_S_fin_prop_fn, h_W_j0_idx_y_i_fn⟩
