import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.Closed.FunctorToTypes

universe v' v u' u

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct.SSet

variable {X Y A B : SSet} (g : X ⟶ Y) (f : A ⟶ B)

variable {s : X ⟶ A} {t : Y ⟶ B} (h : CommSq s g f t)

/-- given a `CommSq s g f t`, we get a map between the points
  of `g ◫ Λ[2, 1]` and `f ◫ Λ[2, 1]`. -/
@[simp]
noncomputable
def pushoutProductSq_left (g f : Arrow SSet) (h : g ⟶ f) :
    (pt g.hom Λ[2, 1].ι) ⟶ (pt f.hom Λ[2, 1].ι) :=
  (rightFunctor (Arrow.mk Λ[2, 1].ι) ⋙ Arrow.leftFunc).map h

@[simp]
noncomputable
def pushoutProductSq_right := ((rightFunctor (Arrow.mk Λ[2, 1].ι)).obj g).hom

example : (g ◫ Λ[2, 1].ι) = pushoutProductSq_right g := rfl

/-- the `PushoutCocone` determined by the above `CommSq`. -/
noncomputable
def pushoutCommSq_cocone : PushoutCocone (pushoutProductSq_left g f (Arrow.homMk' _ _ h.w)) (g ◫ Λ[2, 1].ι) :=
    .mk _ _ ((rightBifunctor.obj (Arrow.mk Λ[2, 1].ι)).map (Arrow.homMk' s t h.w)).w

instance {S : SSet} : Functor.IsLeftAdjoint (tensorLeft S) where
  exists_rightAdjoint := ⟨FunctorToTypes.rightAdj S, ⟨FunctorToTypes.adj S⟩⟩

noncomputable
instance {S : SSet} : PreservesColimitsOfSize (tensorLeft S) :=
  Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _

noncomputable
instance {S : SSet} : PreservesColimitsOfSize (tensorRight S) := by
  apply preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight S)

variable {g f} (h' : CategoryTheory.IsPushout s g f t)

/-- tensoring preserves pushouts. -/
def whiskerPushoutAux (s : X ⟶ A) (g : X ⟶ Y) (S : SSet) :
    CategoryTheory.IsPushout ((tensorRight S).map s) ((tensorRight S).map g)
      ((tensorRight S).map (pushout.inl s g)) ((tensorRight S).map (pushout.inr s g)) where
  w := by simp only [← (tensorRight S).map_comp, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorRight S) s g⟩

/-- whiskering our original pushout square gives us a pushout square. -/
def whiskerPushout (S : SSet) : CategoryTheory.IsPushout (s ▷ S) (g ▷ S) (f ▷ S) (t ▷ S) :=
  (whiskerPushoutAux s g S).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (whiskerRightIso h'.isoPushout S).symm rfl rfl (by aesop) (by aesop)

variable (C : PushoutCocone (pushoutProductSq_left g f (Arrow.homMk' _ _ h'.w)) (g ◫ Λ[2, 1].ι))

/-- such a `PushoutCocone` gives us a `PushoutCocone` of `Δ[2] ◁ s` and `Δ[2] ◁ g`. -/
noncomputable
def changePushoutCocone :
    PushoutCocone (s ▷ Δ[2]) (g ▷ Δ[2]) := by
  refine PushoutCocone.mk ((pushout.inr (f ▷ Λ[2, 1].toSSet) (A ◁ Λ[2, 1].ι)) ≫ C.inl) C.inr ?_
  simpa [pushout.inr_desc_assoc, Functor.PushoutObjObj.ι] using (pushout.inr _ _) ≫= C.condition

@[simp]
noncomputable
def pushoutCommSq_IsColimit'_desc : B ⊗ Δ[2] ⟶ C.pt :=
  (whiskerPushout h' Δ[2]).desc
    ((pushout.inr (f ▷ Λ[2, 1].toSSet) (A ◁ Λ[2, 1].ι)) ≫ C.inl) C.inr
    (by simpa [pushout.inr_desc_assoc, Functor.PushoutObjObj.ι] using (pushout.inr _ _) ≫= C.condition)

-- needs to be cleaned up
lemma pushoutCommSq_IsColimit'_fac_left :
    (f ◫ Λ[2, 1].ι) ≫ pushoutCommSq_IsColimit'_desc h' C = C.inl := by
  apply pushout.hom_ext
  · apply (whiskerPushout h' _).hom_ext
    ·
      change (f ▷ Λ[2, 1].toSSet ≫ pushout.inl _ _) ≫
        (f ◫ Λ[2, 1].ι) ≫ pushoutCommSq_IsColimit'_desc h' C =
        f ▷ Λ[2, 1].toSSet ≫ pushout.inl _ _ ≫ C.inl
      simp [Functor.PushoutObjObj.ι]
      rw [← Category.assoc _ (pushout.inl _ _), pushout.condition]
      have := C.condition
      sorry
      rw [← Category.assoc, pushout.condition, Category.assoc, Category.assoc,
        ← Category.assoc (pushout.inl _ _)]
      dsimp only [pushoutProduct, pushoutCommSq_IsColimit'_desc]
      rw [pushout.inl_desc]
      simp only [Fin.isValue, PushoutProduct.pt, PushoutCocone.ι_app_left, pushoutProduct,
        PushoutCocone.ι_app_right, IsPushout.inl_desc, IsPushout.cocone_inr]
      exact pushout.condition_assoc C.inl
    · change ((Λ[2, 1] : SSet) ◁ t ≫ pushout.inr _ _) ≫
        (f ◫ Λ[2, 1].ι) ≫ pushoutCommSq_IsColimit'_desc h' C =
        (Λ[2, 1] : SSet) ◁ t ≫ pushout.inr _ _ ≫ C.inl
      rw [Category.assoc, ← Category.assoc (pushout.inr _ _)]
      dsimp only [pushoutProduct, pushoutCommSq_IsColimit'_desc]
      rw [pushout.inr_desc, ← Category.assoc, @whisker_exchange, Category.assoc,
        IsPushout.inr_desc, ← Category.assoc]
      have := pushout.inr (Λ[2, 1].ι ▷ X) (Λ[2, 1].toSSet ◁ g) ≫= C.condition
      dsimp only [pushoutProductSq_left] at this ⊢
      rw [pushout.inr_desc_assoc] at this
      rw [← this]
      aesop
  · simp

lemma pushoutCommSq_IsColimit'_fac_right : Δ[2] ◁ t ≫ pushoutCommSq_IsColimit'_desc h' C = C.inr := by
  simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, pushoutCommSq_IsColimit'_desc,
    PushoutCocone.ι_app_left, PushoutCocone.ι_app_right, IsPushout.inr_desc]

lemma pushoutCommSq_IsColimit'_uniq (m : B ⊗ Δ[2] ⟶ C.pt)
    (fac_left : (f ◫ Λ[2, 1].ι) ≫ m = C.inl)
    (fac_right : t ▷ Δ[2] ≫ m = C.inr) : m = pushoutCommSq_IsColimit'_desc h' C := by
  apply (whiskerPushout h' _).hom_ext
  · have := pushout.inl (Λ[2, 1].ι ▷ A) (Λ[2, 1].toSSet ◁ f) ≫= fac_left
    simp at this
    dsimp only [pushoutCommSq_IsColimit'_desc]
    rw [this]
    simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, PushoutCocone.ι_app_left,
      PushoutCocone.ι_app_right, IsPushout.inl_desc]
  · simpa only [Fin.isValue, PushoutProduct.pt, pushoutProduct, pushoutCommSq_IsColimit'_desc,
      PushoutCocone.ι_app_left, PushoutCocone.ι_app_right, IsPushout.inr_desc]

/-- the above is a colimit. -/
noncomputable
def pushoutCommSq_IsColimit' :
    Limits.IsColimit
      (PushoutCocone.mk (f ◫ Λ[2, 1].ι) (t ▷ Δ[2])
        ((rightBifunctor.obj (Arrow.mk Λ[2, 1].ι)).map (Arrow.homMk' s t h'.w)).w) :=
  PushoutCocone.IsColimit.mk _
    (pushoutCommSq_IsColimit'_desc h')
    (pushoutCommSq_IsColimit'_fac_left h')
    (pushoutCommSq_IsColimit'_fac_right h')
    (pushoutCommSq_IsColimit'_uniq h')

def pushoutCommSq_IsPushout :
    CategoryTheory.IsPushout ((rightFunctor (Arrow.mk Λ[2, 1].ι) ⋙ Arrow.leftFunc).map h) (g ◫ Λ[2, 1].ι)
      (f ◫ Λ[2, 1].ι) (t ▷ Δ[2]) where
  w := ((rightBifunctor.obj (Arrow.mk Λ[2, 1].ι)).map (Arrow.homMk' s t h'.w)).w
  isColimit' := ⟨pushoutCommSq_IsColimit' h'⟩



--IsPushout s g f t
--PreservesColimitsOfShape WalkingSpan F
end CategoryTheory.PushoutProduct.SSet
