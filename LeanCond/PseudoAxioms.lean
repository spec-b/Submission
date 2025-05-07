import LeanCond.Axioms

universe u v

section prop

@[instance] axiom Decidable.CHaus {P : Prop} [Decidable P] : CHaus P
@[instance] axiom Decidable.ODisc {P : Prop} [Decidable P] : ODisc P

instance True.CHaus : CHaus True := inferInstance
instance True.ODisc : ODisc True := inferInstance
instance False.CHaus : CHaus False := inferInstance
instance False.ODisc : ODisc False := inferInstance

@[instance] axiom Bool.CHaus : CHaus Bool
@[instance] axiom Bool.ODisc : ODisc Bool

@[instance] axiom And.CHaus {P Q : Prop} [CHaus P] [CHaus Q]  : CHaus (P ∧ Q)
@[instance] axiom And.ODisc {P Q : Prop} [ODisc P] [ODisc Q]  : ODisc (P ∧ Q)
@[instance] axiom Or.CHaus {P Q : Prop} [CHaus P] [CHaus Q]  : CHaus (P ∨ Q)
@[instance] axiom Or.ODisc {P Q : Prop} [ODisc P] [ODisc Q]  : ODisc (P ∨ Q)

end prop

section prod

variable (X Y : Type u)

@[instance] axiom Prod.CHaus [CHaus X] [CHaus Y] : CHaus (X × Y)
@[instance] axiom Prod.ODisc [ODisc X] [ODisc Y] : ODisc (X × Y)

end prod

section finpi

variable {n : Nat} (X : Fin n → Sort u)

instance FinPi.CHaus [∀ i, CHaus (X i)] : CHaus ((i : Fin n) → X i) := inferInstance
instance FinPi.ODisc [∀ i, ODisc (X i)] : ODisc ((i : Fin n) → X i) := inferInstance

end finpi

section lift

variable (P : Sort u) (X : Type u)

@[instance] axiom PLift.CHaus [CHaus P] : CHaus (PLift P)
@[instance] axiom PLift.ODisc [ODisc P] : ODisc (PLift P)
@[instance] axiom ULift.CHaus [CHaus X] : CHaus (ULift.{v} X)
@[instance] axiom ULift.ODisc [ODisc X] : ODisc (ULift.{v} X)

end lift

section sigma

variable (X : Type u) (Y : X → Type v)

@[instance] axiom Sigma.CHaus [CHaus X] [∀ x, CHaus (Y x)] : CHaus (Σ x, Y x)
@[instance] axiom Sigma.ODisc [ODisc X] [∀ x, ODisc (Y x)] : ODisc (Σ x, Y x)

variable (P : Sort u) (Q : P → Prop)

@[instance] axiom Exists.CHaus [CHaus P] [∀ h, CHaus (Q h)] : CHaus (∃ h, Q h)
@[instance] axiom Exists.ODisc [ODisc P] [∀ h, ODisc (Q h)] : ODisc (∃ h, Q h)

variable (X : Type u) (P : X → Prop)

@[instance] axiom Subtype.CHaus [CHaus X] [∀ x, CHaus (P x)] : CHaus {x // P x}
@[instance] axiom Subtype.ODisc [ODisc X] [∀ x, ODisc (P x)] : ODisc {x // P x}

end sigma

section odisc

@[instance] axiom List.ODisc (X : Type u) [ODisc X] : ODisc (List X)
@[instance] axiom Option.ODisc (X : Type u) [ODisc X] : ODisc (Option X)

end odisc