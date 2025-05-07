import LeanCond.ODiscArrow
import LeanCond.OPropMono

universe u

structure ODiscU where
  (carrier : Type u)
  [odisc : ODisc carrier]

namespace ODiscU

instance : CoeSort ODiscU (Type u) where
  coe := ODiscU.carrier

instance (X : ODiscU) : ODisc X := X.odisc

structure GpdFunctor where
  (obj : ODiscU → ODiscU)
  (map : {A B : ODiscU} → (A ≃ B) → (obj A ≃ obj B))
  (map_refl : {A : ODiscU} → map (Equiv.refl A) = Equiv.refl (obj A))
  (map_trans : {A B C : ODiscU} → (f : A ≃ B) → (g : B ≃ C) → map (f.trans g) = (map f).trans (map g))

namespace GpdFunctor

attribute [simp] GpdFunctor.map_refl

variable (F : GpdFunctor)

lemma map_symm {A B : ODiscU} (f : A ≃ B) : F.map f.symm = (F.map f).symm := by
  calc F.map f.symm
      = (F.map f.symm).trans ((F.map f).trans (F.map f).symm) := by simp
    _ = ((F.map f.symm).trans (F.map f)).trans (F.map f).symm := by simp [Equiv.trans_assoc]
    _ = (F.map f).symm := by simp [← F.map_trans]

lemma map_comp {A B C : ODiscU} (f : A ≃ B) (g : B ≃ C) :
    F.map (f.trans g) = F.map g ∘ F.map f := by
  rw [F.map_trans]; rfl

end GpdFunctor

end ODiscU

structure ODiscArrow where
  (src : ODiscU)
  (tgt : ODiscU)
  (map : src → tgt)
  (fam : OProp → ODiscU)
  (src_fam_bot : src ≃ fam ⊥)
  (tgt_fam_top : tgt ≃ fam ⊤)
  (map_eq_arrow : tgt_fam_top ∘ map = ODiscArrow.arrow (fam ·) ⊤ ∘ src_fam_bot)

namespace ODiscArrow

@[simps] noncomputable
def of_fam (f : OProp → ODiscU) : ODiscArrow where
  src := f ⊥
  tgt := f ⊤
  map := ODiscArrow.arrow (f ·) ⊤
  fam := f
  src_fam_bot := Equiv.refl _
  tgt_fam_top := Equiv.refl _
  map_eq_arrow := rfl

-- move this
instance not_CHaus (P : OProp) : CHaus (¬ P) := Pi.CHaus _ _

@[simps]
def of_map {A B : ODiscU} (f : A → B) : ODiscArrow where
  src := A
  tgt := B
  map := f
  fam P := ODiscU.mk <| (b : B) ×' (¬ P → {a : A // f a = b})
  src_fam_bot :=
    { toFun := fun a ↦ ⟨f a, fun _ ↦ ⟨a, rfl⟩⟩,
      invFun := fun x ↦ x.2 id,
      left_inv := by intro b; rfl,
      right_inv := by
        rintro ⟨b, hb⟩
        dsimp
        have := (hb id).2
        simp only [PSigma.mk.injEq, this, true_and]
        apply Function.hfunext rfl
        simp [heq_eq_eq, forall_true_left, Subtype.heq_iff_coe_eq, this] }
  tgt_fam_top :=
    { toFun := fun b ↦ ⟨b, fun h ↦ (h trivial).elim⟩,
      invFun := fun b ↦ b.1,
      left_inv := by intro b; rfl,
      right_inv := by rintro ⟨b, hb⟩; dsimp; congr; ext h; exact (h trivial).elim }
  map_eq_arrow := by
    funext a
    dsimp [arrow]
    have := s_unique (fun P ↦ (b : B) ×' (¬ P → {a : A // f a = b})) ⟨f a, fun _ ↦ ⟨a, rfl⟩⟩
      (fun P ↦ ⟨f a, fun _ ↦ ⟨a, rfl⟩⟩) rfl
    rw [Function.funext_iff] at this
    refine Eq.trans ?_ (this ⊤)
    ext : 1
    · rfl
    · apply Function.hfunext rfl
      intro h
      exact (h trivial).elim

@[simps] noncomputable
def _root_.ODiscU.GpdFunctor.postcomp (F : ODiscU.GpdFunctor) (f : ODiscArrow) : ODiscArrow where
  src := F.obj f.src
  tgt := F.obj f.tgt
  map := (F.map f.tgt_fam_top).symm ∘ arrow ((F.obj ∘ f.fam) ·) ⊤ ∘ F.map f.src_fam_bot
  fam := F.obj ∘ f.fam
  src_fam_bot := F.map f.src_fam_bot
  tgt_fam_top := F.map f.tgt_fam_top
  map_eq_arrow := by simp only [Function.comp_apply, Function.comp_def, Equiv.apply_symm_apply]

end ODiscArrow

namespace ODiscU

variable (F : GpdFunctor.{u})

def admissibleMap (A : ODiscU) (a : F.obj A) (m : Π (B : ODiscU) (_f : A → B), F.obj B) : Prop :=
  m A id = a ∧ ∀ {B₁ B₂ : ODiscU} (f : A → B₁) (e : B₁ ≃ B₂), F.map e (m B₁ f) = m B₂ (e ∘ f)

lemma admissibleMap.map_equiv {A : ODiscU} {a : F.obj A} {m : Π (B : ODiscU) (_f : A → B), F.obj B}
    (h : admissibleMap F A a m) {B : ODiscU} (f : A ≃ B) :
    m B f = F.map f a := by
  have := (h.2 id f).symm
  rwa [h.1] at this

open ODiscArrow in
lemma unique_map (A : ODiscU) (a : F.obj A) (m₁ m₂)
    (h₁ : admissibleMap F A a m₁) (h₂ : admissibleMap F A a m₂) : m₁ = m₂ := by
  ext B f
  let f' := ODiscArrow.of_map f
  let e : OProp → OProp := fun P ↦
    ⟨m₁ (f'.fam P) (arrow (f'.fam ·) P ∘ f'.src_fam_bot) =
    m₂ (f'.fam P) (arrow (f'.fam ·) P ∘ f'.src_fam_bot)⟩
  have he : e ⊥ := by
    simp only [of_map_fam_carrier, OProp.coe_bot, arrow_bot, of_map_src, Function.comp.left_id]
    have H₁ := h₁.map_equiv F (of_map f).src_fam_bot
    have H₂ := h₂.map_equiv F (of_map f).src_fam_bot
    exact H₁.trans H₂.symm
  have := forall_oprop_of_bot (e ·) he ⊤
  dsimp only at this
  rw [← f'.map_eq_arrow, ← h₁.2, ← h₂.2] at this
  exact Equiv.injective _ this

noncomputable
def map {A B : ODiscU} (f : A → B) : F.obj A → F.obj B :=
  (F.postcomp (.of_map f)).map

lemma _root_.Function.Bijective.exists_unique {f : α → β} (hf : f.Bijective) (b : β) :
    ∃! a, f a = b := by
  obtain ⟨a, ha⟩ := hf.surjective b
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply hf.injective
  rw [ha, ha']

@[simps apply]
noncomputable def Equiv.ofBijective' (f : α → β) (hf : f.Bijective) : α ≃ β where
  toFun := f
  invFun b := unique_choice <| hf.exists_unique b
  left_inv a := hf.injective <| unique_choice.spec <| hf.exists_unique (f a)
  right_inv b := unique_choice.spec <| hf.exists_unique b

open ODiscArrow in
noncomputable
def arrow_equiv {A B : ODiscU} (f : A ≃ B) (P : OProp) :=
  Equiv.ofBijective' (arrow ((fam (.of_map f) ·)) P) <| by
    revert P
    rw [forall_oprop_iff]
    constructor
    · simp [Function.bijective_id]
    · have := (of_map f).map_eq_arrow
      rw [← Equiv.comp_symm_eq] at this
      rw [← this]
      exact (Equiv.bijective _).comp (f.bijective.comp <| Equiv.bijective _)

@[simp]
lemma arrow_equiv_bot {A B : ODiscU} (f : A ≃ B) :
    arrow_equiv f ⊥ = Equiv.refl _ := by
  ext
  simp [arrow_equiv, Equiv.ofBijective]
  rfl

open ODiscArrow in
lemma map_equiv {A B : ODiscU} (f : A ≃ B) : map F f = F.map f := by
  dsimp [map, GpdFunctor.postcomp]
  rw [Equiv.symm_comp_eq, ← Equiv.eq_comp_symm, ← F.map_comp, ← F.map_symm, ← F.map_comp]
  have aux : (of_map f).src_fam_bot.symm.trans (f.trans (of_map f).tgt_fam_top) =
    arrow_equiv f ⊤ := by
    have := (of_map f).map_eq_arrow
    rw [← Equiv.comp_symm_eq] at this
    ext x
    exact congrFun this x
  rw [aux]; clear aux
  ext x
  generalize (⊤ : OProp) = P
  revert P
  apply forall_oprop_of_bot
  simp only [arrow_bot, id_eq, arrow_equiv_bot, GpdFunctor.map_refl, Equiv.refl_apply]

section twist

variable {A B C : ODiscU.{u}} (f : A → B) (e : B ≃ C) (P : OProp)

open ODiscArrow in
def arrowTwister : (fam (of_map f) P) ≃ (fam (of_map (⇑e ∘ f)) P) where
  toFun b := ⟨e b.1, fun h ↦ let a := b.2 h; ⟨a, by simp [a.2]⟩⟩
  invFun c := ⟨e.symm c.1, fun h ↦ let a := c.2 h; ⟨a, by simp [← a.2, e.eq_symm_apply]⟩⟩
  left_inv := by
    rintro ⟨b, hb⟩
    dsimp only [of_map_fam_carrier, Function.comp_apply]
    simp only [PSigma.mk.injEq, Equiv.symm_apply_apply, true_and]
    apply Function.hfunext rfl
    rintro h h ⟨⟩
    congr 1
    · ext; simp
    · simp
  right_inv := by
    rintro ⟨c, hc⟩
    dsimp only [of_map_fam_carrier, Function.comp_apply]
    simp only [PSigma.mk.injEq, Equiv.apply_symm_apply, true_and]
    apply Function.hfunext rfl
    rintro h h ⟨⟩
    congr 1
    · ext; simp
    · simp

open ODiscArrow in
lemma arrowTwister_bot : arrowTwister f e ⊥ =
    ((of_map (e ∘ f)).src_fam_bot.symm.trans (of_map f).src_fam_bot).symm := by
  ext a
  dsimp [arrowTwister, of_map]
  ext
  · dsimp
    rw [(a.2 id).2]
  · apply Function.hfunext rfl
    rintro h h ⟨⟩
    dsimp
    congr 1
    · ext; simp [(a.2 id).2]
    · simp [(a.2 id).2]

open ODiscArrow in
lemma arrowTwister_top : arrowTwister f e ⊤ =
    ((of_map f).tgt_fam_top.symm.trans e).trans (of_map (⇑e ∘ f)).tgt_fam_top := by
  ext b
  dsimp [arrowTwister, of_map]
  ext
  · dsimp
  · apply Function.hfunext rfl
    intro h
    exact (h trivial).elim

open ODiscArrow in
lemma arrowTwister_spec :
    arrow (fun Q ↦ (F.obj (fam (of_map (e ∘ f)) Q))) P =
    F.map (arrowTwister f e P) ∘ arrow (fun Q ↦ (F.obj (fam (of_map f) Q))) P ∘
      (F.map ((of_map (⇑e ∘ f)).src_fam_bot.symm.trans (of_map f).src_fam_bot)) := by
  ext x
  revert P
  apply forall_oprop_of_bot
  simp only [arrow_bot, id_eq, of_map_fam_carrier, OProp.coe_bot, Function.comp_apply, of_map_src,
    Function.comp.left_id]
  rw [arrowTwister_bot, ← Function.comp_apply (f := F.map _), ← F.map_comp]
  simp only [Equiv.self_trans_symm, F.map_refl, Equiv.refl_apply]

open ODiscArrow in
lemma map_equiv' :
    map F (e ∘ f) = F.map e ∘ map F f := by
  dsimp [map, GpdFunctor.postcomp]
  rw [Equiv.symm_comp_eq, ← Equiv.eq_comp_symm, ← F.map_symm, ← F.map_symm]
  simp only [Function.comp.assoc, ← F.map_comp]
  simp only [← Function.comp.assoc, ← F.map_comp]
  rw [arrowTwister_spec, Function.comp.assoc, arrowTwister_top]

end twist

@[simp]
lemma map_id (A : ODiscU) : map F (id : A → A) = id := by
  show map F (Equiv.refl A) = Equiv.refl (F.obj A)
  rw [map_equiv, GpdFunctor.map_refl]

lemma map_admissible (A B : ODiscU) (f : A → B) (a : F.obj A) :
    admissibleMap F B (map F f a) (fun C g ↦ map F (g ∘ f) a) := by
  simp [admissibleMap, map_equiv]
  intro B₁ B₂ g e
  rw [Function.comp.assoc, map_equiv']
  rfl

lemma map_comp {A B C : ODiscU} (f : A → B) (g : B → C) :
    map F (g ∘ f) = map F g ∘ map F f := by
  ext a
  revert C
  let m₁ : Π (C : ODiscU) (_ : B → C), F.obj C := fun C g ↦ map F (g ∘ f) a
  let m₂ : Π (C : ODiscU) (_ : B → C), F.obj C := fun C g ↦ map F g (map F f a)
  have := unique_map F B (map F f a) m₁ m₂
    (map_admissible F A B f a) ?_
  · simp only [Function.funext_iff] at this
    exact this
  have := map_admissible F B B id (map F f a)
  rwa [map_id] at this

end ODiscU

#forbiddenAxioms Classical.choice
