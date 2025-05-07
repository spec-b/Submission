import LeanCond.PseudoAxioms

section collect  -- More useful formulations of collection

variable {X : Type u} {Y : X → Type v}

theorem CHaus.collect' [CHaus X] (hY : ∀ x, Nonempty (Y x)) :
  ∃ (X' : Type u) (_ : CHaus X') (g : X' → X) (_ : g.Surjective) (_ : (x' : X') → Y (g x')), True := by
  have surj : (Sigma.fst : (Σ (x : X), Y x) → X).Surjective := by
    intro x
    rcases hY x with ⟨y⟩
    exact ⟨⟨x, y⟩, rfl⟩
  rcases CHaus.collect X (Σ (x : X), Y x) Sigma.fst surj with ⟨X', hX', g, hg, s, hs⟩
  refine ⟨X', hX', g, hg, ?_, trivial⟩
  intro x'
  have hs' : (s x').fst = g x' := congr_fun hs x'
  rw [← hs']
  exact (s x').snd

theorem ODisc.collect' [ODisc X] (hY : ∀ x, Nonempty (Y x)) :
  ∃ (X' : Type u) (_ : ODisc X') (g : X' → X) (_ : g.Surjective) (_ : (x' : X') → Y (g x')), True := by
  have surj : (Sigma.fst : (Σ (x : X), Y x) → X).Surjective := by
    intro x
    rcases hY x with ⟨y⟩
    exact ⟨⟨x, y⟩, rfl⟩
  rcases ODisc.collect X (Σ (x : X), Y x) Sigma.fst surj with ⟨X', hX', g, hg, s, hs⟩
  refine ⟨X', hX', g, hg, ?_, trivial⟩
  intro x'
  have hs' : (s x').fst = g x' := congr_fun hs x'
  rw [← hs']
  exact (s x').snd

end collect

theorem finite_subcover {X : Type u} [CHaus X] {I : Type u} [ODisc I]
    (Y : I → X → Prop) (h : ∀ x, ∃ i, Y i x) :
    ∃ (m : ℕ) (f : Fin m → I), ∀ x, ∃ j, Y (f j) x := by
  have : ∀ x, Nonempty {i // Y i x} := fun x => by
    rcases h x with ⟨i, hy⟩
    exact ⟨i, hy⟩
  rcases CHaus.collect' this with ⟨X', _, g, hg, s, _⟩
  rcases Cond.factor_fin (fun x' => (s x').val : X' → I) with ⟨m, α, β, hαβ⟩
  refine ⟨m, β, fun x => ?_⟩
  rcases hg x with ⟨x', rfl⟩
  refine ⟨α x', ?_⟩
  have : β (α x') = (s x').val := congr_fun hαβ x'
  rw [this]
  exact (s x').property
