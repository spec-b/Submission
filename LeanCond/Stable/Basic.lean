-- ¬¬-Stable propositions
-- Partially based on Andrej Bauer's
-- "First steps in synthetic computability theory"

import LeanCond.PseudoAxioms

class Stable (p : Prop) where
  elim : ¬¬p → p

lemma not_not_map {P Q : Prop} (h : P → Q) : ¬¬P → ¬¬Q :=
mt (mt h)

lemma not_not_lem {P : Prop} : ¬¬(P ∨ ¬P) := by
  intro hn
  have a : ¬P := mt Or.inl hn
  have b : ¬¬P := mt Or.inr hn
  exact b a

instance : Stable True where
  elim _ := trivial

instance : Stable False where
  elim h := nomatch h           -- Turns out `nomatch` can use decidability

instance [hp : Stable P] [hq : Stable Q] : Stable (P ∧ Q) where
  elim h := ⟨hp.elim $ not_not_map And.left h, hq.elim $ not_not_map And.right h⟩

lemma Stable.not_imp {P Q : Prop} [Stable P] :
  (¬ (P → Q)) ↔ P ∧ ¬ Q := by
  constructor
  · intro h
    constructor
    · apply Stable.elim
      intro hnP
      exact (h (fun hP ↦ (hnP hP).elim))
    · intro hQ
      exact h (fun _ ↦ hQ)
  · rintro ⟨h1, h2⟩ h
    exact h2 (h h1)

instance {X : Sort _} {Q : X → Prop} [hq : ∀ (x : X), Stable (Q x)] :
    Stable (∀ (x : X), Q x) where
  elim h := by
    intro p
    apply (hq _).elim
    intro nq
    apply h
    intro pq
    exact nq (pq p)
