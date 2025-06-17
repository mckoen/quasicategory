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
def pushoutProductSq_left : (pt g Λ[2, 1].ι) ⟶ (pt f Λ[2, 1].ι) := by
  convert (rightFunctor (Arrow.mk Λ[2, 1].ι) ⋙ Arrow.leftFunc).map (Arrow.homMk' s t h.w)

@[simp]
noncomputable
def pushoutProductSq_right := ((rightFunctor (Arrow.mk Λ[2, 1].ι)).obj g).hom

example : (g ◫ Λ[2, 1].ι) = pushoutProductSq_right g := rfl

/-- the `PushoutCocone` determined by the above `CommSq`. -/
noncomputable
def pushoutCommSq_cocone : PushoutCocone (pushoutProductSq_left g f h) (g ◫ Λ[2, 1].ι) :=
    .mk _ _ ((rightBifunctor.obj (Arrow.mk Λ[2, 1].ι)).map (Arrow.homMk' s t h.w)).w

instance {S : SSet} : Functor.IsLeftAdjoint (tensorLeft S) where
  exists_rightAdjoint := ⟨FunctorToTypes.rightAdj S, ⟨FunctorToTypes.adj S⟩⟩

noncomputable
instance {S : SSet} : PreservesColimitsOfSize (tensorLeft S) :=
  Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _

variable {g f} (h' : CategoryTheory.IsPushout s g f t)

/-- tensoring preserves pushouts. -/
def whiskerPushoutAux (s : X ⟶ A) (g : X ⟶ Y) (S : SSet) :
    CategoryTheory.IsPushout ((tensorLeft S).map s) ((tensorLeft S).map g)
      ((tensorLeft S).map (pushout.inl s g)) ((tensorLeft S).map (pushout.inr s g)) where
  w := by simp only [← (tensorLeft S).map_comp, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorLeft S) s g⟩

/-- whiskering our original pushout square gives us a pushout square. -/
def whiskerPushout (S : SSet) : CategoryTheory.IsPushout (S ◁ s) (S ◁ g) (S ◁ f) (S ◁ t) :=
  (whiskerPushoutAux s g S).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((whiskerLeftIso S h'.isoPushout).symm) rfl rfl (by aesop) (by aesop)

variable (C : PushoutCocone (pushoutProductSq_left g f h'.toCommSq) (g ◫ Λ[2, 1].ι))

/-- such a `PushoutCocone` gives us a `PushoutCocone` of `Δ[2] ◁ s` and `Δ[2] ◁ g`. -/
noncomputable
def changePushoutCocone :
    PushoutCocone (Δ[2] ◁ s) (Δ[2] ◁ g) :=
  .mk ((pushout.inl (Λ[2, 1].ι ▷ A) (Λ[2, 1].toSSet ◁ f)) ≫ C.inl) C.inr
    (by simpa [pushout.inl_desc_assoc] using (pushout.inl _ _) ≫= C.condition)

@[simp]
noncomputable
def pushoutCommSq_IsColimit'_desc : Δ[2] ⊗ B ⟶ C.pt :=
  (whiskerPushout h' Δ[2]).desc
    ((pushout.inl (Λ[2, 1].ι ▷ A) (Λ[2, 1].toSSet ◁ f)) ≫ C.inl) C.inr
      (by simpa [pushout.inl_desc_assoc] using (pushout.inl _ _) ≫= C.condition)

-- needs to be cleaned up
lemma pushoutCommSq_IsColimit'_fac_left :
    (f ◫ Λ[2, 1].ι) ≫ pushoutCommSq_IsColimit'_desc h' C = C.inl := by
  apply pushout.hom_ext
  · simp
  · apply (whiskerPushout h' _).hom_ext
    ·
      change ((Λ[2, 1] : SSet) ◁ f ≫ PushoutProduct.inr f Λ[2, 1].ι) ≫
        (f ◫ Λ[2, 1].ι) ≫ pushoutCommSq_IsColimit'_desc h' C =
        (Λ[2, 1] : SSet) ◁ f ≫ PushoutProduct.inr f Λ[2, 1].ι ≫ C.inl
      rw [← Category.assoc, ← pushout.condition, Category.assoc, Category.assoc,
        ← Category.assoc (PushoutProduct.inl f Λ[2, 1].ι)]
      dsimp only [PushoutProduct.inl, pushoutProduct, pushoutCommSq_IsColimit'_desc]
      rw [pushout.inl_desc]
      simp only [Fin.isValue, PushoutProduct.pt, PushoutCocone.ι_app_left, pushoutProduct,
        PushoutCocone.ι_app_right, IsPushout.inl_desc, PushoutProduct.inr, IsPushout.cocone_inr]
      exact pushout.condition_assoc C.inl
    · change ((Λ[2, 1] : SSet) ◁ t ≫ PushoutProduct.inr f Λ[2, 1].ι) ≫
        (f ◫ Λ[2, 1].ι) ≫ pushoutCommSq_IsColimit'_desc h' C =
        (Λ[2, 1] : SSet) ◁ t ≫ PushoutProduct.inr f Λ[2, 1].ι ≫ C.inl
      rw [Category.assoc, ← Category.assoc (PushoutProduct.inr f Λ[2, 1].ι)]
      dsimp only [PushoutProduct.inl, pushoutProduct, pushoutCommSq_IsColimit'_desc]
      rw [pushout.inr_desc, ← Category.assoc, @whisker_exchange, Category.assoc,
        IsPushout.inr_desc, ← Category.assoc]
      have := PushoutProduct.inr g Λ[2, 1].ι ≫= C.condition
      dsimp only [PushoutProduct.inr, pushoutProductSq_left] at this ⊢
      rw [pushout.inr_desc_assoc] at this
      rw [← this]
      aesop

lemma pushoutCommSq_IsColimit'_fac_right : Δ[2] ◁ t ≫ pushoutCommSq_IsColimit'_desc h' C = C.inr := by
  simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, pushoutCommSq_IsColimit'_desc,
    PushoutCocone.ι_app_left, PushoutCocone.ι_app_right, IsPushout.inr_desc]

lemma pushoutCommSq_IsColimit'_uniq (m : Δ[2] ⊗ B ⟶ C.pt)
    (fac_left : (f ◫ Λ[2, 1].ι) ≫ m = C.inl)
    (fac_right : Δ[2] ◁ t ≫ m = C.inr) : m = pushoutCommSq_IsColimit'_desc h' C := by
  apply (whiskerPushout h' _).hom_ext
  · have := PushoutProduct.inl f Λ[2, 1].ι ≫= fac_left
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
      (PushoutCocone.mk (f ◫ Λ[2, 1].ι) (Δ[2] ◁ t)
        ((rightBifunctor.obj (Arrow.mk Λ[2, 1].ι)).map (Arrow.homMk' s t h.w)).w) :=
  PushoutCocone.IsColimit.mk _
    (pushoutCommSq_IsColimit'_desc h')
    (pushoutCommSq_IsColimit'_fac_left h')
    (pushoutCommSq_IsColimit'_fac_right h')
    (pushoutCommSq_IsColimit'_uniq h')

def pushoutCommSq_IsPushout :
    CategoryTheory.IsPushout (pushoutProductSq_left g f h'.toCommSq) (g ◫ Λ[2, 1].ι)
      (f ◫ Λ[2, 1].ι) (Δ[2] ◁ t) where
  w := ((rightBifunctor.obj (Arrow.mk Λ[2, 1].ι)).map (Arrow.homMk' s t h'.w)).w
  isColimit' := ⟨pushoutCommSq_IsColimit' h h'⟩



--IsPushout s g f t
--PreservesColimitsOfShape WalkingSpan F
end CategoryTheory.PushoutProduct.SSet
