import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import LeanCond.Nat
import LeanCond.Stable.ODisc
import LeanCond.Util

-- Disable simp lemmas that use choice
attribute [-simp] add_pos_iff add_lt_iff_neg_left lt_add_iff_pos_right add_lt_add_iff_right

def NatInfty : Type :=
{ f : ℕ → Bool // ∀ n k, f (n+k) → f n }

namespace NatInfty

scoped notation "ℕ∞" => NatInfty

instance : CHaus ℕ∞ := inferInstanceAs (CHaus (Subtype _))

alias ext := Subtype.ext
attribute [ext] ext

def ofNat (n : ℕ) : ℕ∞ :=
⟨fun m => m < n,
 by intros m k hm; rw [decide_eq_true_eq] at hm ⊢; exact lt_of_le_of_lt (Nat.le_add_right m k) hm⟩

theorem ofNat_injective : Function.Injective ofNat := by
  intros n1 n2 h
  rcases Nat.lt_trichotomy n1 n2 with (hn|rfl|hn)
  · have := congr_arg (fun f => f.1 n1) h
    simp [*, ofNat] at *
  · rfl
  · have := congr_arg (fun f => f.1 n2) h
    simp [*, ofNat] at *

theorem eq_ofNat_iff (n : ℕ) (x : ℕ∞) :
    (x = ofNat n) ↔ (¬ x.1 n ∧ ∀ n' < n, x.1 n') := by
  constructor
  · rintro rfl
    simp [ofNat]
  · intro h
    cases' x with x hx
    have : ∀ m, x m = (m < n : Bool) := by
      intro m
      cases' Nat.lt_or_ge m n with hm hm
      · simpa [*] using h.2 m hm
      · rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
        have xnk : ¬ x (n + k) := by
          intro h1
          exact h.1 (hx _ _ h1)
        have : (n + k < n) = (false : Bool) := by simp [*]
        simp [*]
    apply Subtype.ext
    ext m
    apply this

instance (n : ℕ) (x : ℕ∞) : Decidable (x = ofNat n) :=
  decidable_of_iff _ (eq_ofNat_iff n x).symm

def infty : ℕ∞ :=
  ⟨fun _ => true, fun _ _ => id⟩

scoped notation "∞" => infty

theorem infty_ne_ofNat (n) : ∞ ≠ ofNat n := by
  intro h
  have := congr_arg (fun f => f.1 n) h
  simp [ofNat, infty] at this

theorem eq_infty_of_ne_ofNat (x : ℕ∞) (h : ∀ n, x ≠ ofNat n) : x = ∞ := by
  suffices ∀ m, x.1 m by
    apply Subtype.ext
    ext
    apply this
  apply Nat.strongRec
  intro n IH
  apply Decidable.byContradiction
  intro hx
  apply h n
  rw [eq_ofNat_iff]
  exact ⟨hx, IH⟩

def finite (x : ℕ∞) : OProp where
  P := ∃ i, x.1 i = false

def finite' (P : OProp) (x : ℕ∞) : OProp where
  P := P ∧ x.finite

lemma finite_iff (x : ℕ∞) : finite x = ∃ i, x.1 i = false :=
  rfl

lemma finite_iff_exists_ofNat (x : ℕ∞) : x.finite ↔ ∃ n, x = ofNat n := by
  dsimp [finite, ofNat]
  apply Iff.intro
  · intro h
    let k := Nat.find h
    exists k
    apply NatInfty.ext
    ext i
    dsimp
    apply Decidable.byCases (p := i < k)
    · simp (config := {contextual := true})
    · intro hi
      simp only [hi, decide_False]
      obtain ⟨j, rfl⟩ : ∃ j, i = k + j :=
        Nat.exists_eq_add_of_le (by rwa [Nat.not_lt] at hi)
      apply eq_false_of_ne_true
      apply mt (x.2 k j)
      apply ne_true_of_eq_false
      apply Nat.find_spec h
  · rintro ⟨i, rfl⟩
    exists i
    simp

@[simp]
lemma ofNat_finite (n : ℕ) :
  (ofNat n).finite = ⊤ := by
  ext
  simp only [finite_iff_exists_ofNat, OProp.coe_top, iff_true]
  refine ⟨n, rfl⟩

@[simp]
lemma ofNat_finite' (P : OProp) (n : ℕ) :
  (ofNat n).finite' P = P := by
  ext; simp [finite']

@[simp]
lemma infty_finite : ∞.finite = ⊥ := by
  ext; simp [finite, infty]

@[simp]
lemma infty_finite' (P : OProp) : ∞.finite' P = ⊥ := by
  ext; simp [finite']

@[simp]
lemma finite'_Bot (x : ℕ∞) : x.finite' ⊥ = ⊥ := by
  ext; simp [finite']

def succ (f : ℕ∞) : ℕ∞ :=
⟨fun n ↦ match n with
  | .zero => true
  | .succ n => f.1 n,
  fun n k ↦ by
    cases n
    · intro; rfl
    · rw [Nat.succ_add]; apply f.2⟩

@[simp]
lemma ofNat_succ (n : ℕ) :
  (ofNat n).succ = ofNat (n + 1) := by
  apply Subtype.ext
  ext (_|k) <;> simp [ofNat, succ, Nat.succ_eq_add_one, Nat.add_lt_add_iff_right]

@[simp]
lemma infty_succ : ∞.succ = ∞ := by
  apply Subtype.ext
  ext (_|k) <;> rfl

@[simp]
lemma finite_succ (x : ℕ∞) :
  (x.succ).finite = x.finite := by
  ext
  constructor
  · rintro ⟨(_|n), hn⟩
    · simp [succ] at hn
    exists n+1
    dsimp only [succ] at hn
    apply eq_false_of_ne_true
    apply mt (x.2 _ 1)
    exact ne_true_of_eq_false hn
  · rintro ⟨n, hn⟩
    exists n+1

@[simp]
lemma finite'_succ (P : OProp) (x : ℕ∞) :
  (x.succ).finite' P = x.finite' P := by
  simp [finite']

section LE

protected def LE (x y : ℕ∞) : Prop :=
  ∀ n, x.1 n → y.1 n

instance : LE ℕ∞ := ⟨NatInfty.LE⟩

lemma LE_def (x y : ℕ∞) :
  x ≤ y ↔ ∀ n, x.1 n → y.1 n := by
  rfl

lemma LE_infty (x : ℕ∞) : x ≤ ∞ := fun _ _ ↦ rfl

lemma LE_refl (x : ℕ∞) : x ≤ x := fun _ ↦ id

lemma LE_trans {x y z : ℕ∞} : x ≤ y → y ≤ z → x ≤ z := by
  intros hxy hyz n hn
  apply hyz
  apply hxy
  exact hn

lemma Bool.propext {p q : Bool} (h : p ↔ q) : p = q := by
  cases p <;> cases q <;> simp [h]
  simp at h

lemma LE_antisymm {x y : ℕ∞} : x ≤ y → y ≤ x → x = y := by
  intro hxy hyx
  apply Subtype.ext
  ext n
  exact Bool.propext ⟨hxy _, hyx _⟩

lemma ofNat_succ_LE_iff (n : ℕ) (x : ℕ∞) :
  (ofNat (n+1) : ℕ∞) ≤ x ↔ x.1 n := by
  simp [LE_def, ofNat]
  constructor
  · intro h
    apply h
    simp
  · intro h m hm
    rw [Nat.lt_succ_iff] at hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact x.2 _ _ h

instance LE_CHaus (x y : ℕ∞) : CHaus (x ≤ y) := by
  rw [LE_def]; infer_instance

end LE

section open_nhd

variable (U : ℕ∞ → OProp) (hU : U ∞)

def cover : Option ℕ → (ℕ∞ → OProp)
| .some n => fun x => ⟨x = ofNat n⟩
| .none => U

theorem cover_is_cover : ∀ n, ∃ k, cover U k n := by
  intro x
  apply Stable.elim
  rw [not_exists, Option.forall]
  rintro ⟨h1, h2⟩
  obtain rfl := eq_infty_of_ne_ofNat x h2
  contradiction

def Finmax : (m : ℕ) → (xs : Fin m → ℕ) → {n // ∀ i, xs i ≤ n}
| .zero, xs => ⟨0, fun x => Fin.elim0 x⟩
| .succ m, xs => by
  refine ⟨max (xs 0) (Finmax m (xs ∘ Fin.succ)), ?_⟩
  intro i
  rcases Fin.eq_zero_or_eq_succ i with (rfl|⟨j,rfl⟩)
  · simp
  · refine le_trans ?_ (le_max_right _ _)
    apply (Finmax _ (xs ∘ Fin.succ)).2

theorem eventually' : ∃ i, ∀ (n : ℕ∞), n.1 i → U n := by
  rcases finite_subcover (fun k n => cover U k n) (cover_is_cover U hU) with ⟨m, x, hc⟩
  have i := Finmax m (fun j => Option.getD (x j) 0)
  use i
  intro i' hi'
  rcases hc i' with ⟨j, hj⟩
  match hx : x j with
  | none => rwa [hx] at hj
  | some k =>
    obtain rfl : i' = ofNat k := by rwa [hx] at hj
    simp only [ofNat, decide_eq_true_eq] at hi'
    have hki : k ≤ i := by simpa only [hx, Option.getD_some] using i.2 j
    exact (Nat.not_lt_of_le hki hi').elim

theorem eventually : ∃ i, ∀ i' > i, U (ofNat i') :=
  (eventually' U hU).imp fun _ H _ h ↦ H _ (decide_eq_true h)

end open_nhd

end NatInfty

#forbiddenAxioms Classical.choice
