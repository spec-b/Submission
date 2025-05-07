universe u v w

variable {X : Sort u} {Y : Sort v} {Z : Sort w}

structure Pullback (f : X → Z) (g : Y → Z) where
  fst : X
  snd : Y
  w : f fst = g snd

def Eql (f g : X → Y) : Sort (max 1 u) := Pullback f g

inductive Pushout.Rel (f : X → Y) (g : X → Z) : Y ⊕' Z → Y ⊕' Z → Prop
  | mk (x : X) : Pushout.Rel f g (.inl $ f x) (.inr $ g x)

def Pushout (f : X → Y) (g : X → Z) :=
  Quot $ Pushout.Rel f g

def Coeq (f g : X → Y) : Sort (max 1 v) := Pushout f g