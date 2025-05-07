import Mathlib.Logic.Equiv.Defs
import Mathlib.Init.Function

import LeanCond.ForbiddenAxioms
import LeanCond.FiniteLimits

universe u v

section unique_choice

variable {X : Sort u} {P : X → Prop}

axiom unique_choice (h : ∃! x, P x) : X
axiom unique_choice.spec (h : ∃! x, P x) : P (unique_choice h)

end unique_choice

@[class] axiom CHaus : Sort u → Prop
@[class] axiom ODisc : Sort u → Prop

/-! # Pretopos axioms -/

section eq

variable (X : Sort u)

@[instance] axiom Eq.CHaus [CHaus X] (a b : X) : CHaus (a = b)
@[instance] axiom Eq.ODisc [ODisc X] (a b : X) : ODisc (a = b)

end eq

section fin

variable (n : Nat)

@[instance] axiom Fin.CHaus : CHaus (Fin n)
@[instance] axiom Fin.ODisc : ODisc (Fin n)

end fin

section eql

variable {X : Sort u} {Y : Sort v}

@[instance] axiom Eql.CHaus [CHaus X] [CHaus Y] (f g : X → Y) : CHaus (Eql f g)
@[instance] axiom Eql.ODisc [ODisc X] [ODisc Y] (f g : X → Y) : ODisc (Eql f g)

end eql

section quot

variable {X : Type u} (s : Setoid X)

@[instance] axiom Quotient.CHaus [CHaus X] [∀ x y, CHaus (s.r x y)] : CHaus (Quotient s)
@[instance] axiom Quotient.ODisc [ODisc X] [∀ x y, ODisc (s.r x y)] : ODisc (Quotient s)

end quot

section equiv

variable {X : Sort u} (Y : Sort v)

axiom Equiv.CHaus [CHaus Y] (e : Equiv X Y) : CHaus X
axiom Equiv.ODisc [ODisc Y] (e : Equiv X Y) : ODisc X

end equiv

/-! # Closure under sigma -/

section sigma

variable (X : Sort u) (Y : X → Sort v)

@[instance] axiom Sigma'.CHaus [CHaus X] [∀ x, CHaus (Y x)] : CHaus (Σ' x, Y x)
@[instance] axiom Sigma'.ODisc [ODisc X] [∀ x, ODisc (Y x)] : ODisc (Σ' x, Y x)

end sigma

section pi

variable (X : Sort u) (Y : X → Sort v)

@[instance] protected axiom Pi.CHaus [ODisc X] [∀ x, CHaus (Y x)] : CHaus ((x : X) → Y x)
@[instance] protected axiom Pi.ODisc [CHaus X] [∀ x, ODisc (Y x)] : ODisc ((x : X) → Y x)

end pi

/-! # Collection axioms -/

section collect

variable (Y : Type v) (X : Type u)

axiom CHaus.collect [CHaus Y] (f : X → Y) (hf : f.Surjective) :
  ∃ (Y' : Type v) (_ : CHaus Y') (g : Y' → Y) (_ : g.Surjective) (s : Y' → X), f ∘ s = g
axiom ODisc.collect [ODisc Y] (f : X → Y) (hf : f.Surjective) :
  ∃ (Y' : Type v) (_ : ODisc Y') (g : Y' → Y) (_ : g.Surjective) (s : Y' → X), f ∘ s = g

end collect

/-! # Axioms `F` and `G` -/

section f_and_g

variable {X Y : Type u}

/-- Axiom `F` -/
axiom Cond.factor_fin [CHaus X] [ODisc Y] (f : X → Y) :
  ∃ (n : Nat) (α : X → Fin n) (β : Fin n → Y), β ∘ α = f

/-- Axiom `G` -/
axiom Cond.generate (X : Type u) :
  ∃ (I : Type u) (_ : ODisc I) (K : I → Type u) (_ : ∀ i, CHaus (K i)) (α : (Σ i, K i) → X), α.Surjective

end f_and_g

/-! # Axioms `Scott_continuity` and `Nat.ODisc` -/

-- Every function out of a Pi type depends on only finitely many components
axiom Cond.Scott_continuity (Y : Sort u) [ODisc Y] (X : Y → Sort v) [∀ y, CHaus (X y)]
    (n : ℕ) (f : ((y : Y) → X y) → Fin n) :
  ∃ (m : ℕ) (α : Fin m → Y) (f' : ((i : Fin m) → X (α i)) → Fin n),
    ∀ x, f x = f' (fun i => x (α i))

@[instance] axiom Nat.ODisc : ODisc ℕ
