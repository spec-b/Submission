import LeanCond.PseudoAxioms
import Mathlib.Order.BoundedOrder

@[ext] structure OProp where
(P : Prop)
[odisc : ODisc P]

instance : CoeSort OProp Prop where
  coe := OProp.P

attribute [instance] OProp.odisc

namespace OProp

instance : Bot OProp := ⟨⟨False⟩⟩

instance : Top OProp := ⟨⟨True⟩⟩

@[simp]
lemma coe_bot : (⊥ : OProp) = False := rfl

@[simp]
lemma coe_top : (⊤ : OProp) = True := rfl

end OProp
