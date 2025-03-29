import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.Closed.FunctorToTypes

universe v' v u' u

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (g : X ⟶ Y) (f : A ⟶ B)

variable {s : X ⟶ A} {t : Y ⟶ B} (h : CommSq s g f t)

/-- given a `CommSq s g f t`, we get a map between pushout products
  of `f` with `hornInclusion 2 1` and `g` with `hornInclusion 2 1`. -/
noncomputable
def pushoutDescOfCommSq : (pt g (horn 2 1).ι) ⟶ (pt f (horn 2 1).ι) :=
  IsPushout.desc (PushoutProduct.IsPushout g (horn 2 1).ι)
    ((Δ[2] ◁ s) ≫ (PushoutProduct.inl f (horn 2 1).ι))
    (((Λ[2, 1] : SSet) ◁ t) ≫ (PushoutProduct.inr f (horn 2 1).ι))
    (by
     change (Λ[2, 1] : SSet) ◁ s ≫ (horn 2 1).ι ▷ A ≫ pushout.inl ((horn 2 1).ι ▷ A) ((Λ[2, 1] : SSet) ◁ f) = ((Λ[2, 1] : SSet) ◁ (g ≫ t)) ≫ _
     rw [(Λ[2, 1] : SSet) ◁ s ≫= (PushoutProduct.IsPushout f (horn 2 1).ι).toCommSq.w, ← h.w]
     rfl )

/-- using the above map between pushout products, we get a new `CommSq`. -/
lemma pushoutCommSq_w : (pushoutDescOfCommSq g f h) ≫ (f ◫ (horn 2 1).ι) =
    (g ◫ (horn 2 1).ι) ≫ (Δ[2] ◁ t) := by
  apply Limits.pushout.hom_ext
  · simp [pushoutDescOfCommSq, IsPushout.inl_desc]
    rw [← MonoidalCategory.whiskerLeft_comp, h.w, MonoidalCategory.whiskerLeft_comp]
  · simp [pushoutDescOfCommSq, IsPushout.inr_desc]
    rw [@whisker_exchange]

/-- the `PushoutCocone` determined by the above `CommSq`. -/
noncomputable
def pushoutCommSq_cocone : PushoutCocone (pushoutDescOfCommSq g f h) (g ◫ (horn 2 1).ι) :=
    .mk _ _ (pushoutCommSq_w g f h)

/-- such a `PushoutCocone` gives us a `PushoutCocone` of `Δ[2] ◁ s` and `Δ[2] ◁ g`. -/
noncomputable
def changePushoutCocone (C : PushoutCocone (pushoutDescOfCommSq g f h) (g ◫ (horn 2 1).ι)) :
    PushoutCocone (Δ[2] ◁ s) (Δ[2] ◁ g) := by
  refine PushoutCocone.mk ((pushout.inl ((horn 2 1).ι ▷ A) ((Λ[2, 1] : SSet) ◁ f)) ≫ C.inl) C.inr ?_
  have a := C.condition
  dsimp only [pushoutDescOfCommSq, pushoutProduct] at a
  rw [← (IsPushout.inl_desc _ (Δ[2] ◁ g)), Category.assoc, ← a, ← Category.assoc, ← Category.assoc, IsPushout.inl_desc]
  rfl

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

variable (C : PushoutCocone (pushoutDescOfCommSq g f h'.toCommSq) (g ◫ (horn 2 1).ι))

lemma temp : Δ[2] ◁ s ≫ pushout.inl ((horn 2 1).ι ▷ A) ((Λ[2, 1] : SSet) ◁ f) ≫ C.inl =
    Δ[2] ◁ g ≫ C.inr := by
  have a := C.condition
  dsimp only [pushoutDescOfCommSq, pushoutProduct] at a
  rw [← (IsPushout.inl_desc _ (Δ[2] ◁ g)), Category.assoc, ← a, ← Category.assoc, ← Category.assoc, IsPushout.inl_desc]
  rfl

@[simp]
noncomputable
def pushoutCommSq_IsColimit'_desc : Δ[2] ⊗ B ⟶ C.pt :=
  (whiskerPushout h' Δ[2]).desc
    ((pushout.inl ((horn 2 1).ι ▷ A) ((Λ[2, 1] : SSet) ◁ f)) ≫ C.inl) C.inr (temp h' C)

-- needs to be cleaned up
lemma pushoutCommSq_IsColimit'_fac_left :
    (f ◫ (horn 2 1).ι) ≫ pushoutCommSq_IsColimit'_desc h' C = C.inl := by
  apply (PushoutProduct.IsPushout f (horn 2 1).ι).hom_ext
  · simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, PushoutCocone.ι_app_left,
      PushoutCocone.ι_app_right, IsPushout.inl_desc_assoc, IsPushout.inl_desc, pushoutCommSq_IsColimit'_desc]
  · apply (whiskerPushout h' _).hom_ext
    · change ((Λ[2, 1] : SSet) ◁ f ≫ PushoutProduct.inr f (horn 2 1).ι) ≫
        (f ◫ (horn 2 1).ι) ≫ pushoutCommSq_IsColimit'_desc h' C =
        (Λ[2, 1] : SSet) ◁ f ≫ PushoutProduct.inr f (horn 2 1).ι ≫ C.inl
      rw [← Category.assoc, ← PushoutProduct.w, Category.assoc, Category.assoc,
        ← Category.assoc (PushoutProduct.inl f (horn 2 1).ι)]
      dsimp only [PushoutProduct.inl, pushoutProduct, pushoutCommSq_IsColimit'_desc]
      rw [IsPushout.inl_desc]
      simp only [Fin.isValue, PushoutProduct.pt, PushoutCocone.ι_app_left, pushoutProduct,
        PushoutCocone.ι_app_right, IsPushout.inl_desc, PushoutProduct.inr, IsPushout.cocone_inr]
      exact pushout.condition_assoc C.inl
    · change ((Λ[2, 1] : SSet) ◁ t ≫ PushoutProduct.inr f (horn 2 1).ι) ≫
        (f ◫ (horn 2 1).ι) ≫ pushoutCommSq_IsColimit'_desc h' C =
        (Λ[2, 1] : SSet) ◁ t ≫ PushoutProduct.inr f (horn 2 1).ι ≫ C.inl
      rw [Category.assoc, ← Category.assoc (PushoutProduct.inr f (horn 2 1).ι)]
      dsimp only [PushoutProduct.inl, pushoutProduct, pushoutCommSq_IsColimit'_desc]
      rw [IsPushout.inr_desc, ← Category.assoc, @whisker_exchange, Category.assoc,
        IsPushout.inr_desc, ← Category.assoc]
      have := PushoutProduct.inr g (horn 2 1).ι ≫= C.condition
      dsimp only [PushoutProduct.inr, pushoutDescOfCommSq] at this ⊢
      rw [← Category.assoc, IsPushout.inr_desc] at this
      rw [this]
      aesop

lemma pushoutCommSq_IsColimit'_fac_right : Δ[2] ◁ t ≫ pushoutCommSq_IsColimit'_desc h' C = C.inr := by
  simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, pushoutCommSq_IsColimit'_desc,
    PushoutCocone.ι_app_left, PushoutCocone.ι_app_right, IsPushout.inr_desc]

lemma pushoutCommSq_IsColimit'_uniq (m : Δ[2] ⊗ B ⟶ C.pt)
    (fac_left : (f ◫ (horn 2 1).ι) ≫ m = C.inl)
    (fac_right : Δ[2] ◁ t ≫ m = C.inr) : m = pushoutCommSq_IsColimit'_desc h' C := by
  apply (whiskerPushout h' _).hom_ext
  · have := PushoutProduct.inl f (horn 2 1).ι ≫= fac_left
    simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, PushoutProduct.inl,
      IsPushout.cocone_inl, IsPushout.inl_desc_assoc, PushoutCocone.ι_app_left] at this
    dsimp only [pushoutCommSq_IsColimit'_desc]
    rw [this]
    simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, PushoutCocone.ι_app_left,
      PushoutCocone.ι_app_right, IsPushout.inl_desc]
  · simpa only [Fin.isValue, PushoutProduct.pt, pushoutProduct, pushoutCommSq_IsColimit'_desc,
      PushoutCocone.ι_app_left, PushoutCocone.ι_app_right, IsPushout.inr_desc]

/-- the above is a colimit. -/
noncomputable
def pushoutCommSq_IsColimit' :
    Limits.IsColimit (pushoutCommSq_cocone g f h'.toCommSq) :=
  PushoutCocone.IsColimit.mk _
    (pushoutCommSq_IsColimit'_desc h')
    (pushoutCommSq_IsColimit'_fac_left h')
    (pushoutCommSq_IsColimit'_fac_right h')
    (pushoutCommSq_IsColimit'_uniq h')

def pushoutCommSq_IsPushout :
    CategoryTheory.IsPushout (pushoutDescOfCommSq g f h'.toCommSq) (g ◫ (horn 2 1).ι)
      (f ◫ (horn 2 1).ι) ((Δ[2] ◁ t)) where
  w := pushoutCommSq_w g f h'.toCommSq
  isColimit' := ⟨pushoutCommSq_IsColimit' h'⟩

end CategoryTheory.PushoutProduct
