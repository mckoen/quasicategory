import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Quasicategory.FunctorToTypes
import Quasicategory.MorphismProperty

/-!

Defines pushout-products and a little bit of API.

Everything here should be generalized and more API should be added.

-/

namespace SSet

open CategoryTheory MonoidalCategory Limits Simplicial

def pushoutProduct_IsPushout {A B X Y : SSet} (f : A ⟶ B) (g : X ⟶ Y) :=
  IsPushout.of_hasPushout (g ▷ A) (X ◁ f)

/-- The pushout-product of `f` and `g`. -/
noncomputable
def pushoutProduct {A B X Y : SSet} (f : A ⟶ B) (g : X ⟶ Y) :
    (pushoutProduct_IsPushout f g).cocone.pt ⟶ Y ⊗ B :=
  (pushoutProduct_IsPushout f g).desc (Y ◁ f) (g ▷ B) rfl

/-- pushout in proof `0079` (for retract diagram) -/
def Λ_pushout (m : ℕ) (i : Fin (m + 1)) :=
  pushoutProduct_IsPushout (hornInclusion m i) (hornInclusion 2 1)

noncomputable
def Λ_pushoutProduct (m : ℕ) (i : Fin (m + 1)) : (Λ_pushout m i).cocone.pt ⟶ Δ[2] ⊗ Δ[m] :=
  pushoutProduct (hornInclusion m i) (hornInclusion 2 1)

inductive bdryPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃m : ℕ⦄ : bdryPushout (pushoutProduct (boundaryInclusion m) (hornInclusion 2 1))

/-- the class of pushout products of `∂Δ[n] ↪ Δ[n]` with `Λ[n, i] ↪ Δ[n]`. -/
def bdryPushoutClass : MorphismProperty SSet := fun _ _ p ↦ bdryPushout p

variable {X Y A B : SSet} (g : X ⟶ Y) (f : A ⟶ B)

section Pushout

variable {s : X ⟶ A} {t : Y ⟶ B} (h : CommSq s g f t)

/-- given a `CommSq s g f t`, we get a map between pushout products
  of `f` with `hornInclusion 2 1` and `g` with `hornInclusion 2 1`. -/
noncomputable
def pushoutDescOfCommSq : (pushoutProduct_IsPushout g (hornInclusion 2 1)).cocone.pt ⟶
    (pushoutProduct_IsPushout f (hornInclusion 2 1)).cocone.pt :=
  IsPushout.desc (pushoutProduct_IsPushout g (hornInclusion 2 1))
    ((Δ[2] ◁ s) ≫ (pushoutProduct_IsPushout f (hornInclusion 2 1)).cocone.inl)
    ((Λ[2, 1] ◁ t) ≫ (pushoutProduct_IsPushout f (hornInclusion 2 1)).cocone.inr)
    (by
     change Λ[2, 1] ◁ s ≫ hornInclusion 2 1 ▷ A ≫ pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f) = (Λ[2, 1] ◁ (g ≫ t)) ≫ _
     rw [Λ[2, 1] ◁ s ≫= (pushoutProduct_IsPushout f (hornInclusion 2 1)).toCommSq.w, ← h.w]
     rfl )

/-- using the above map between pushout products, we get a new `CommSq`. -/
lemma pushoutCommSq_w : (pushoutDescOfCommSq g f h) ≫ pushoutProduct f (hornInclusion 2 1) =
    pushoutProduct g (hornInclusion 2 1) ≫ (Δ[2] ◁ t) := by
  apply Limits.pushout.hom_ext
  · simp [pushoutProduct, pushoutDescOfCommSq, IsPushout.inl_desc]
    rw [← MonoidalCategory.whiskerLeft_comp, h.w, MonoidalCategory.whiskerLeft_comp]
  · simp [pushoutProduct, pushoutDescOfCommSq, IsPushout.inr_desc]
    rw [@whisker_exchange]

/-- the `PushoutCocone` determined by the above `CommSq`. -/
noncomputable
def pushoutCommSq_cocone : PushoutCocone (pushoutDescOfCommSq g f h) (pushoutProduct g (hornInclusion 2 1)) :=
    .mk _ _ (pushoutCommSq_w g f h)

/-- such a `PushoutCocone` gives us a `PushoutCocone` of `Δ[2] ◁ s` and `Δ[2] ◁ g`. -/
noncomputable
def changePushoutCocone (C : PushoutCocone (pushoutDescOfCommSq g f h) (pushoutProduct g (hornInclusion 2 1))) :
    PushoutCocone (Δ[2] ◁ s) (Δ[2] ◁ g) := by
  refine PushoutCocone.mk ((pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f)) ≫ C.inl) C.inr ?_
  have a := C.condition
  dsimp only [pushoutDescOfCommSq, pushoutProduct] at a
  rw [← (IsPushout.inl_desc _ (Δ[2] ◁ g)), Category.assoc, ← a, ← Category.assoc, ← Category.assoc, IsPushout.inl_desc]
  rfl

instance : Functor.IsLeftAdjoint (tensorLeft Δ[2]) where
  exists_rightAdjoint := ⟨FunctorToTypes.rightAdj Δ[2], ⟨FunctorToTypes.adj Δ[2]⟩⟩

noncomputable
instance : PreservesColimitsOfSize (tensorLeft Δ[2]) :=
  Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _

variable (h' : IsPushout s g f t)

instance : IsIso h'.isoPushout.hom := Iso.isIso_hom h'.isoPushout

instance : IsIso (Δ[2] ◁ h'.isoPushout.hom) := whiskerLeft_isIso Δ[2] h'.isoPushout.hom

/-- the `PushoutCocone (Δ[2] ◁ s) (Δ[2] ◁ g)` given
  in `isColimitOfHasPushoutOfPreservesColimit (tensorLeft Δ[2]) s g`. -/
noncomputable
def auxPushoutCocone (s : X ⟶ A) (g : X ⟶ Y) : PushoutCocone (Δ[2] ◁ s) (Δ[2] ◁ g) :=
  PushoutCocone.mk ((tensorLeft Δ[2]).map (pushout.inl s g)) ((tensorLeft Δ[2]).map (pushout.inr s g))
    ((show (tensorLeft Δ[2]).map s ≫ (tensorLeft Δ[2]).map (pushout.inl _ _) = (tensorLeft Δ[2]).map g ≫ (tensorLeft Δ[2]).map (pushout.inr _ _) from by
      simp only [← (tensorLeft Δ[2]).map_comp, pushout.condition]))

noncomputable
def auxIsColimit (s : X ⟶ A) (g : X ⟶ Y) : IsColimit (auxPushoutCocone s g) :=
  (Limits.isColimitOfHasPushoutOfPreservesColimit (tensorLeft Δ[2]) s g)

set_option maxHeartbeats 400000 in
/-- the above `PushoutCocone` is a colimit. -/
noncomputable
def pushoutCommSq_IsColimit' :
    Limits.IsColimit (pushoutCommSq_cocone g f h'.toCommSq) where
  desc C := Δ[2] ◁ h'.isoPushout.hom ≫ (auxIsColimit s g).desc (changePushoutCocone g f h'.toCommSq C)
  fac := sorry
  uniq := sorry

def pushoutCommSq_IsPushout :
    IsPushout (pushoutDescOfCommSq g f h'.toCommSq) (pushoutProduct g (hornInclusion 2 1))
      (pushoutProduct f (hornInclusion 2 1)) ((Δ[2] ◁ t)) where
  w := pushoutCommSq_w g f h'.toCommSq
  isColimit' := ⟨pushoutCommSq_IsColimit' g f h'⟩

end Pushout

section Retract

--variable (h : IsRetract f g)

end Retract

end SSet
