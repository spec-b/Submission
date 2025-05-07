import LeanCond.NatInfty
import LeanCond.Stable.ODisc
import LeanCond.OPropMono

namespace ODiscArrow

-- Disable simp lemmas that use choice
attribute [-simp] add_pos_iff le_add_iff_nonneg_left
attribute [-simp] add_lt_iff_neg_left lt_add_iff_pos_left
attribute [-simp] lt_add_iff_pos_right add_lt_add_iff_right
attribute [-simp] le_add_iff_nonneg_right

attribute [simp] Nat.lt_add_one_iff Nat.lt_add_right_iff_pos Nat.lt_add_left_iff_pos

open NatInfty

section

variable (Z : ℕ∞ → Type u) [∀ n, ODisc (Z n)] (z : Z ∞)

/-- Given a family `Z : ℕ∞ → Type u` and a term `z : Z ∞`,
then `sections Z z n₀` is the type of sections indexed by `[n₀, ∞]` that map `∞` to `z`. -/
def sections (n₀ : ℕ∞) := {x : Π (n : ℕ∞), (n₀ ≤ n) → Z n // x ∞ (LE_infty _) = z}

instance sections.ODisc (n₀ : ℕ∞) : ODisc (sections Z z n₀) :=
  Subtype.ODisc _ _

-- move this
instance _root_.Nonempty.ODisc (X : Sort*) [ODisc X] : ODisc (Nonempty X) := by
  suffices Nonempty X ↔ ∃ _x : X, True by
    rw [this]; infer_instance
  exact ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩

theorem exist :
  ∃ (i : ℕ) (x : Π (n : ℕ∞), (n.1 i) → Z n), x ∞ rfl = z := by
  let U : ℕ∞ → OProp := fun n ↦ ⟨Nonempty (sections Z z n)⟩
  have hU : U ∞ := by
    constructor
    refine ⟨?_, ?_⟩
    · intro n hn
      obtain rfl : n = ∞ := LE_antisymm (LE_infty _) hn
      exact z
    · rfl
  rcases eventually U hU with ⟨i, h⟩
  obtain ⟨x, hx⟩ := h (i+1) i.lt_succ_self
  use i
  refine ⟨?_, ?_⟩
  · intro n hn
    apply x n
    rwa [ofNat_succ_LE_iff]
  · exact hx

theorem uniq
  (i₁ : ℕ) (x₁ : Π (n : ℕ∞), (n.1 i₁) → Z n) (h₁ : x₁ ∞ rfl = z)
  (i₂ : ℕ) (x₂ : Π (n : ℕ∞), (n.1 i₂) → Z n) (h₂ : x₂ ∞ rfl = z) :
  ∃ (i : ℕ) (hi₁ : i₁ ≤ i) (hi₂ : i₂ ≤ i),
    ∀ (n : ℕ∞) (hn : n.1 i),
      x₁ n (n.2 _ (i-i₁) $ by simpa [hi₁]) =
      x₂ n (n.2 _ (i-i₂) $ by simpa [hi₂]) := by
  let U : ℕ∞ → OProp := fun n ↦ ⟨∀ (h₁ : n.1 i₁) (h₂ : n.1 i₂), x₁ n h₁ = x₂ n h₂⟩
  have hU : U ∞ := by
    intro _ _
    exact h₁.trans h₂.symm
  rcases eventually' U hU with ⟨i, h⟩
  let j := max i (max i₁ i₂)
  use j
  simp only [ge_iff_le, max_le_iff, le_max_iff, le_refl, or_true, exists_true_left, true_or]
  intro n hn
  apply h n (n.2 _ (j-i) $ by simpa)

end

private lemma HEq_helper (P : OProp) (X : OProp → Type u) [∀ P, ODisc (X P)]
  (i : ℕ) (x : Π (x : ℕ∞), (x.1 i) → X (x.finite' P))
  (k₁ k₂ : ℕ∞) (h₁) (h₂) (H : k₁ = k₂) :
  HEq (x k₁ h₁) (x k₂ h₂) := by
  induction H; rfl

private lemma HEq_helper' (P : OProp) (X : OProp → Type u) [∀ P, ODisc (X P)]
  (i : ℕ) (x : Π (n : ℕ∞), (n.1 i) → X (n.finite' P))
  (k₁ k₂ : ℕ) (h₁) (h₂) (H : k₁ = k₂) :
  HEq (x (ofNat k₁) h₁) (x (ofNat k₂) h₂) := by
  induction H; rfl

def rel {P : OProp} {X : OProp → Type u} [∀ P, ODisc (X P)] :
  X ⊥ → X P → Prop :=
fun x₀ x₁ ↦ ∃ (i₀ : ℕ) (x : (n : ℕ∞) → (n.1 i₀) → X (n.finite' P)),
  HEq (x ∞ rfl) x₀ ∧
  (∃ (i : ℕ) (hn : i₀ ≤ i), ∀ k, HEq (x (ofNat (i + k + 1)) (by simp [ofNat, le_add_right hn])) x₁)

lemma eventually' (P : OProp) (X : OProp → Type u) [∀ P, ODisc (X P)]
  (i : ℕ) (x : Π (n : ℕ∞), (n.1 i) → X (n.finite' P)) :
  ∃ N, ∀ k,
    HEq (x (ofNat (N + 1 + i)) (by simp [ofNat]))
        (x (ofNat (N + k + 1 + i)) (by simp [ofNat])) := by
  let x' : (n : ℕ∞) → (n.1 i) → X (n.finite' P) := by
    intro n h
    rw [← finite'_succ]
    apply x
    cases i with
    | zero => rfl
    | succ i => apply n.2 i 1 h
  have := uniq (fun n ↦ X (n.finite' P)) (x ∞ rfl) i x rfl i x' ?H
  case H =>
    dsimp
    apply eq_of_heq
    convert cast_heq rfl ?_
    apply HEq_helper
    apply infty_succ
  obtain ⟨N, hn, hn, h⟩ := this
  use N
  refine Nat.rec HEq.rfl ?_
  intro k ih
  refine ih.trans ?_; clear ih
  refine (heq_of_eq <| h ?_ ?_).trans ?_
  · simp only [ofNat, add_assoc, add_left_comm k, add_comm _ (k + i),
      Nat.lt_add_right_iff_pos, decide_eq_true_eq]
    simp [← add_assoc]
  dsimp [Nat.succ_eq_add_one]
  convert cast_heq ?_ ?_
  · apply HEq_helper
    rw [ofNat_succ]; congr 1
    simp [add_assoc, add_comm i 1]
  · rw [ofNat_finite', ofNat_finite']

lemma eventually (P : OProp) (X : OProp → Type u) [∀ P, ODisc (X P)]
  (i : ℕ) (x : Π (n : ℕ∞), (n.1 i) → X (n.finite' P)) :
  ∃! xP : X P,
  ∃ N, ∀ k,
    HEq xP
        (x (ofNat (N + k + 1 + i)) (by simp [ofNat])) := by
  obtain ⟨N, hN⟩ := eventually' P X i x
  let xP : X P := by
      rw [← ofNat_finite' P (N + 1 + i)]
      exact x (ofNat (N + 1 + i)) (by simp [ofNat])
  refine ⟨xP, ⟨N, fun k ↦ (cast_heq _ _).trans (hN k)⟩, ?_⟩
  rintro x' ⟨N', h'⟩
  apply eq_of_heq
  refine HEq.trans ?_ (cast_heq _ _).symm
  refine HEq.trans ?_ (hN N').symm
  refine (h' N).trans ?_
  rw [Nat.add_comm N N']

theorem exists_unique (P : OProp) (X : OProp → Type u) [∀ P, ODisc (X P)] (x₀ : X ⊥) :
  ∃! x₁ : X P, rel x₀ x₁ := by
  refine exists_unique_of_exists_of_unique ?exist ?uniq
  case uniq =>
    rintro x x' ⟨n₀, y, h, n, hn, H⟩ ⟨n₀', y', h', n', hn', H'⟩
    let z : X (∞.finite' P) := y ∞ rfl
    have aux : y' ∞ rfl = z := eq_of_heq (h'.trans h.symm)
    obtain ⟨N, hn, hn', key⟩ := uniq (fun f ↦ X (f.finite' P)) z _ y rfl _ y' aux
    apply eq_of_heq
    refine HEq.trans (H (n' + N)).symm ?_
    refine HEq.trans ?_ (H' (n + N))
    specialize key (ofNat <| n + n' + N + 1) (by simp [ofNat, ← add_assoc])
    refine HEq.trans ?L ((heq_of_eq key).trans ?R)
    case L => apply HEq_helper'; rw [← add_assoc]
    case R => apply HEq_helper'; rw [← add_assoc, add_comm n n']
  case exist =>
    let z : X (∞.finite' P) := by rwa [infty_finite']
    obtain ⟨n, x, H⟩ := exist (fun f ↦ X (f.finite' P)) z
    let w := unique_choice (eventually _ _ _ x)
    obtain ⟨N, hN⟩ : ∃ N, ∀ (k : ℕ), HEq w (x (ofNat (N + k + 1 + n)) _) :=
      unique_choice.spec (eventually _ _ _ x)
    refine ⟨w, ⟨n, x, ?_, ?_⟩⟩
    · rw [H]; apply cast_heq
    · refine ⟨N + n, by simp, ?_⟩
      intro k
      refine HEq.trans ?_ (hN k).symm
      apply HEq_helper'
      simp only [add_assoc, Nat.add_left_comm n k 1, add_comm n 1]

noncomputable
def s (X : OProp → Type u) [∀ P, ODisc (X P)] (x₀ : X ⊥) (P : OProp) : X P :=
unique_choice $ exists_unique P X x₀

lemma hs (X : OProp → Type u) [∀ P, ODisc (X P)] (x₀ : X ⊥) :
  s X x₀ ⊥ = x₀ := by
  obtain ⟨n, x, h₁, N, hN, h₂⟩ := unique_choice.spec $ exists_unique ⊥ X x₀
  let x' : (Σ' (f : ℕ∞), f.1 N) → X ⊥ := fun f ↦
    cast (congr_arg X $ finite'_Bot _) (x f.1 $ f.1.2 _ (N - n) $ by simp [hN, f.2])
  let Z : ℕ∞ → OProp := fun f ↦ if hf : f.1 N then ⟨x' ⟨f, hf⟩ = x₀⟩ else ⊥
  have hZ : Z ∞ := by
    dsimp only [Z]
    rw [dif_pos]; swap; rfl
    apply eq_of_heq
    convert cast_heq rfl ?_
    apply h₁
  obtain ⟨k, H⟩ := NatInfty.eventually Z hZ
  apply eq_of_heq
  refine (h₂ k).symm.trans ?_
  specialize H (N + k + 1) ?_
  · simp [add_assoc, add_comm N]; simp [add_comm _ N]
  dsimp only [Z] at H
  rw [dif_pos] at H; swap; simp [ofNat, add_assoc, add_left_comm _ N]
  dsimp at H
  rw [← H]
  apply (cast_heq _ _).symm

lemma s_unique (X : OProp → Type u) [∀ P, ODisc (X P)] (x₀ : X ⊥)
    (s' : Π (P : OProp), X P) (hs' : s' ⊥ = x₀) :
    s' = s X x₀ := by
  apply funext
  apply forall_oprop_of_bot
  rw [hs', hs]

noncomputable
def s_equiv (X : OProp → Type u) [∀ P, ODisc (X P)] :
  (X ⊥) ≃ (Π (P : OProp), X P) where
  toFun := fun x P ↦ s X x P
  invFun := fun s ↦ s ⊥
  left_inv := fun x ↦ hs X x
  right_inv := fun s ↦ by symm; apply s_unique; rfl

noncomputable
def arrow (X : OProp → Type u) [∀ P, ODisc (X P)] (P : OProp) : X ⊥ → X P :=
  fun x₀ ↦ s X x₀ P

@[simp]
lemma arrow_bot (X : OProp → Type u) [∀ P, ODisc (X P)] : arrow X ⊥ = id := by
  ext x₀
  exact hs X x₀

lemma arrow_const (X : Type u) [ODisc X] : ∀ P, arrow (fun _ ↦ X) P = id := by
  intro P
  ext x₀
  symm
  have := s_unique (fun _ ↦ X) x₀ (fun _ ↦ x₀) rfl
  rw [Function.funext_iff] at this
  apply this

end ODiscArrow

#forbiddenAxioms Classical.choice
