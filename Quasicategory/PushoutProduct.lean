import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Quasicategory.Retract.Basic
import Quasicategory.TransfiniteComposition

/-!

Defines pushout-products and a little bit of API.

Everything here should be generalized and more API should be added.

-/

open CategoryTheory MonoidalCategory

namespace CategoryTheory.pushoutProduct

variable {A B X Y : SSet} (f : A ⟶ B) (g : X ⟶ Y)

@[simp]
def IsPushout := IsPushout.of_hasPushout (g ▷ A) (X ◁ f)

@[simp]
noncomputable
def pt : SSet := (IsPushout f g).cocone.pt

/-- The pushout-product of `f` and `g`. name should be changed -/
@[simp]
noncomputable
def desc : pt f g ⟶ Y ⊗ B :=
  (IsPushout f g).desc (Y ◁ f) (g ▷ B) rfl

@[simp]
noncomputable
def desc' {W : SSet} (h : Y ⊗ A ⟶ W) (k : X ⊗ B ⟶ W) (w : g ▷ A ≫ h = X ◁ f ≫ k) :
    pt f g ⟶ W := (IsPushout f g).desc h k w

@[simp]
noncomputable
def inl : (Y ⊗ A) ⟶ pt f g := (IsPushout f g).cocone.inl

@[simp]
noncomputable
def inr : (X ⊗ B) ⟶ pt f g := (IsPushout f g).cocone.inr

@[simp]
lemma inl_desc {W : SSet} (h : Y ⊗ A ⟶ W) (k : X ⊗ B ⟶ W) (w : g ▷ A ≫ h = X ◁ f ≫ k) :
    (inl f g) ≫ (desc' f g) h k w = h := (IsPushout f g).inl_desc _ _ _

@[simp]
lemma inr_desc {W : SSet} (h : Y ⊗ A ⟶ W) (k : X ⊗ B ⟶ W) (w : g ▷ A ≫ h = X ◁ f ≫ k) :
    (inr f g) ≫ (desc' f g) h k w = k := (IsPushout f g).inr_desc _ _ _

@[simp]
lemma w : g ▷ A ≫ inl f g = X ◁ f ≫ inr f g  := (IsPushout f g).toCommSq.w

@[simp]
lemma desc_id : (desc' f g) (inl f g) (inr f g) (w f g) = 𝟙 (pt f g) :=
  (IsPushout f g).hom_ext (by aesop) (by aesop)

end CategoryTheory.pushoutProduct

namespace SSet

open Limits Simplicial

/-- pushout in proof `0079` (for retract diagram) -/
def Λ_pushout (m : ℕ) (i : Fin (m + 1)) :=
  pushoutProduct.IsPushout (hornInclusion m i) (hornInclusion 2 1)

noncomputable
def Λ_pushoutProduct (m : ℕ) (i : Fin (m + 1)) : (Λ_pushout m i).cocone.pt ⟶ Δ[2] ⊗ Δ[m] :=
  pushoutProduct.desc (hornInclusion m i) (hornInclusion 2 1)

inductive bdryPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃m : ℕ⦄ : bdryPushout (pushoutProduct.desc (boundaryInclusion m) (hornInclusion 2 1))

/-- the class of pushout products of `∂Δ[n] ↪ Δ[n]` with `Λ[n, i] ↪ Δ[n]`. -/
def bdryPushoutClass : MorphismProperty SSet := fun _ _ p ↦ bdryPushout p

variable {X Y A B : SSet} (g : X ⟶ Y) (f : A ⟶ B)

section Pushout

variable {s : X ⟶ A} {t : Y ⟶ B} (h : CommSq s g f t)

/-- given a `CommSq s g f t`, we get a map between pushout products
  of `f` with `hornInclusion 2 1` and `g` with `hornInclusion 2 1`. -/
noncomputable
def pushoutDescOfCommSq : (pushoutProduct.pt g (hornInclusion 2 1)) ⟶
    (pushoutProduct.pt f (hornInclusion 2 1)) :=
  IsPushout.desc (pushoutProduct.IsPushout g (hornInclusion 2 1))
    ((Δ[2] ◁ s) ≫ (pushoutProduct.IsPushout f (hornInclusion 2 1)).cocone.inl)
    ((Λ[2, 1] ◁ t) ≫ (pushoutProduct.IsPushout f (hornInclusion 2 1)).cocone.inr)
    (by
     change Λ[2, 1] ◁ s ≫ hornInclusion 2 1 ▷ A ≫ pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f) = (Λ[2, 1] ◁ (g ≫ t)) ≫ _
     rw [Λ[2, 1] ◁ s ≫= (pushoutProduct.IsPushout f (hornInclusion 2 1)).toCommSq.w, ← h.w]
     rfl )

/-- using the above map between pushout products, we get a new `CommSq`. -/
lemma pushoutCommSq_w : (pushoutDescOfCommSq g f h) ≫ pushoutProduct.desc f (hornInclusion 2 1) =
    pushoutProduct.desc g (hornInclusion 2 1) ≫ (Δ[2] ◁ t) := by
  apply Limits.pushout.hom_ext
  · simp [pushoutProduct.desc, pushoutDescOfCommSq, IsPushout.inl_desc]
    rw [← MonoidalCategory.whiskerLeft_comp, h.w, MonoidalCategory.whiskerLeft_comp]
  · simp [pushoutProduct.desc, pushoutDescOfCommSq, IsPushout.inr_desc]
    rw [@whisker_exchange]

/-- the `PushoutCocone` determined by the above `CommSq`. -/
noncomputable
def pushoutCommSq_cocone : PushoutCocone (pushoutDescOfCommSq g f h) (pushoutProduct.desc g (hornInclusion 2 1)) :=
    .mk _ _ (pushoutCommSq_w g f h)

/-- such a `PushoutCocone` gives us a `PushoutCocone` of `Δ[2] ◁ s` and `Δ[2] ◁ g`. -/
noncomputable
def changePushoutCocone (C : PushoutCocone (pushoutDescOfCommSq g f h) (pushoutProduct.desc g (hornInclusion 2 1))) :
    PushoutCocone (Δ[2] ◁ s) (Δ[2] ◁ g) := by
  refine PushoutCocone.mk ((pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f)) ≫ C.inl) C.inr ?_
  have a := C.condition
  dsimp only [pushoutDescOfCommSq, pushoutProduct.desc] at a
  rw [← (IsPushout.inl_desc _ (Δ[2] ◁ g)), Category.assoc, ← a, ← Category.assoc, ← Category.assoc, IsPushout.inl_desc]
  rfl

instance {S : SSet} : Functor.IsLeftAdjoint (tensorLeft S) where
  exists_rightAdjoint := ⟨FunctorToTypes.rightAdj S, ⟨FunctorToTypes.adj S⟩⟩

noncomputable
instance {S : SSet} : PreservesColimitsOfSize (tensorLeft S) :=
  Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _

variable {g f} (h' : IsPushout s g f t)

/-- tensoring preserves pushouts. -/
def whiskerPushoutAux (s : X ⟶ A) (g : X ⟶ Y) (S : SSet) :
    IsPushout ((tensorLeft S).map s) ((tensorLeft S).map g)
      ((tensorLeft S).map (pushout.inl s g)) ((tensorLeft S).map (pushout.inr s g)) where
  w := by simp only [← (tensorLeft S).map_comp, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorLeft S) s g⟩

/-- whiskering our original pushout square gives us a pushout square. -/
def whiskerPushout {g f} (h' : IsPushout s g f t) (S : SSet) : IsPushout (S ◁ s) (S ◁ g) (S ◁ f) (S ◁ t) :=
  (whiskerPushoutAux s g S).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((whiskerLeftIso S h'.isoPushout).symm) rfl rfl (by aesop) (by aesop)

variable (C : PushoutCocone (pushoutDescOfCommSq g f h'.toCommSq) (pushoutProduct.desc g (hornInclusion 2 1)))

lemma temp : Δ[2] ◁ s ≫ pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f) ≫ C.inl =
    Δ[2] ◁ g ≫ C.inr := by
  have a := C.condition
  dsimp only [pushoutDescOfCommSq, pushoutProduct.desc] at a
  rw [← (IsPushout.inl_desc _ (Δ[2] ◁ g)), Category.assoc, ← a, ← Category.assoc, ← Category.assoc, IsPushout.inl_desc]
  rfl

@[simp]
noncomputable
def pushoutCommSq_IsColimit'_desc : Δ[2] ⊗ B ⟶ C.pt :=
  (whiskerPushout h' Δ[2]).desc
    ((pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f)) ≫ C.inl) C.inr (temp h' C)

-- needs to be cleaned up
lemma pushoutCommSq_IsColimit'_fac_left :
    pushoutProduct.desc f (hornInclusion 2 1) ≫ pushoutCommSq_IsColimit'_desc h' C = C.inl := by
  apply (pushoutProduct.IsPushout f (hornInclusion 2 1)).hom_ext
  · simp only [Fin.isValue, pushoutProduct.pt, pushoutProduct.desc, PushoutCocone.ι_app_left,
      PushoutCocone.ι_app_right, IsPushout.inl_desc_assoc, IsPushout.inl_desc, pushoutCommSq_IsColimit'_desc]
  · apply (whiskerPushout h' _).hom_ext
    · change (Λ[2, 1] ◁ f ≫ pushoutProduct.inr f (hornInclusion 2 1)) ≫
        pushoutProduct.desc f (hornInclusion 2 1) ≫ pushoutCommSq_IsColimit'_desc h' C =
        Λ[2, 1] ◁ f ≫ pushoutProduct.inr f (hornInclusion 2 1) ≫ C.inl
      rw [← Category.assoc, ← pushoutProduct.w, Category.assoc, Category.assoc,
        ← Category.assoc (pushoutProduct.inl f (hornInclusion 2 1))]
      dsimp only [pushoutProduct.inl, pushoutProduct.desc, pushoutCommSq_IsColimit'_desc]
      rw [IsPushout.inl_desc]
      simp only [Fin.isValue, pushoutProduct.pt, PushoutCocone.ι_app_left, pushoutProduct.desc,
        PushoutCocone.ι_app_right, IsPushout.inl_desc, pushoutProduct.inr, IsPushout.cocone_inr]
      exact pushout.condition_assoc C.inl
    · change (Λ[2, 1] ◁ t ≫ pushoutProduct.inr f (hornInclusion 2 1)) ≫
        pushoutProduct.desc f (hornInclusion 2 1) ≫ pushoutCommSq_IsColimit'_desc h' C =
        Λ[2, 1] ◁ t ≫ pushoutProduct.inr f (hornInclusion 2 1) ≫ C.inl
      rw [Category.assoc, ← Category.assoc (pushoutProduct.inr f (hornInclusion 2 1))]
      dsimp only [pushoutProduct.inl, pushoutProduct.desc, pushoutCommSq_IsColimit'_desc]
      rw [IsPushout.inr_desc, ← Category.assoc, @whisker_exchange, Category.assoc,
        IsPushout.inr_desc, ← Category.assoc]
      have := pushoutProduct.inr g (hornInclusion 2 1) ≫= C.condition
      dsimp only [pushoutProduct.inr, pushoutDescOfCommSq] at this ⊢
      rw [← Category.assoc, IsPushout.inr_desc] at this
      rw [this]
      aesop

lemma pushoutCommSq_IsColimit'_fac_right : Δ[2] ◁ t ≫ pushoutCommSq_IsColimit'_desc h' C = C.inr := by
  simp only [Fin.isValue, pushoutProduct.pt, pushoutProduct.desc, pushoutCommSq_IsColimit'_desc,
    PushoutCocone.ι_app_left, PushoutCocone.ι_app_right, IsPushout.inr_desc]

lemma pushoutCommSq_IsColimit'_uniq (m : Δ[2] ⊗ B ⟶ C.pt)
    (fac_left : pushoutProduct.desc f (hornInclusion 2 1) ≫ m = C.inl)
    (fac_right : Δ[2] ◁ t ≫ m = C.inr) : m = pushoutCommSq_IsColimit'_desc h' C := by
  apply (whiskerPushout h' _).hom_ext
  · have := pushoutProduct.inl f (hornInclusion 2 1) ≫= fac_left
    simp only [Fin.isValue, pushoutProduct.pt, pushoutProduct.desc, pushoutProduct.inl,
      IsPushout.cocone_inl, IsPushout.inl_desc_assoc, PushoutCocone.ι_app_left] at this
    dsimp only [pushoutCommSq_IsColimit'_desc]
    rw [this]
    simp only [Fin.isValue, pushoutProduct.pt, pushoutProduct.desc, PushoutCocone.ι_app_left,
      PushoutCocone.ι_app_right, IsPushout.inl_desc]
  · simpa only [Fin.isValue, pushoutProduct.pt, pushoutProduct.desc, pushoutCommSq_IsColimit'_desc,
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
    IsPushout (pushoutDescOfCommSq g f h'.toCommSq) (pushoutProduct.desc g (hornInclusion 2 1))
      (pushoutProduct.desc f (hornInclusion 2 1)) ((Δ[2] ◁ t)) where
  w := pushoutCommSq_w g f h'.toCommSq
  isColimit' := ⟨pushoutCommSq_IsColimit' h'⟩

end Pushout

section Retract

variable {f g} (h : RetractArrow f g)

noncomputable
def pushoutProduct.i.left :
    pushoutProduct.pt f (hornInclusion 2 1) ⟶ pushoutProduct.pt g (hornInclusion 2 1) :=
  (pushoutProduct.IsPushout f (hornInclusion 2 1)).desc
    (Δ[2] ◁ h.i.left ≫ (pushoutProduct.IsPushout g (hornInclusion 2 1)).cocone.inl)
    (Λ[2, 1] ◁ h.i.right ≫ (pushoutProduct.IsPushout g (hornInclusion 2 1)).cocone.inr)
    (by
      dsimp
      rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ← h.i_w,
        MonoidalCategory.whiskerLeft_comp, ← whisker_exchange, Category.assoc, Category.assoc,
        ← (pushoutProduct.IsPushout g (hornInclusion 2 1)).w])

noncomputable
def pushoutProduct.r.left :
    pushoutProduct.pt g (hornInclusion 2 1) ⟶ pushoutProduct.pt f (hornInclusion 2 1) :=
  (pushoutProduct.IsPushout g (hornInclusion 2 1)).desc
    (Δ[2] ◁ h.r.left ≫ (pushoutProduct.IsPushout f (hornInclusion 2 1)).cocone.inl)
    (Λ[2, 1] ◁ h.r.right ≫ (pushoutProduct.IsPushout f (hornInclusion 2 1)).cocone.inr)
    (by
      dsimp
      rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ← h.r_w,
        MonoidalCategory.whiskerLeft_comp, ← whisker_exchange, Category.assoc, Category.assoc,
        ← (pushoutProduct.IsPushout f (hornInclusion 2 1)).w])

lemma pushoutProduct.retract_left : pushoutProduct.i.left h ≫ pushoutProduct.r.left h = 𝟙 _ := by
  dsimp [i.left, r.left]
  refine (pushoutProduct.IsPushout f (hornInclusion 2 1)).hom_ext ?_ ?_
  · simp only [Fin.isValue, IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h.retract_left]
    rfl
  · simp only [Fin.isValue, IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h.retract_right]
    rfl

lemma pushoutProduct.i_w : pushoutProduct.i.left h ≫ pushoutProduct.desc g (hornInclusion 2 1) =
    pushoutProduct.desc f (hornInclusion 2 1) ≫ Δ[2] ◁ h.i.right := by
  dsimp [i.left]
  apply (pushoutProduct.IsPushout f (hornInclusion 2 1)).hom_ext
  · dsimp [pushoutProduct.desc]
    rw [IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc, ← Category.assoc,
      IsPushout.inl_desc, ← MonoidalCategory.whiskerLeft_comp, h.i_w]
    rfl
  · dsimp [pushoutProduct.desc]
    rw [IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc, ← Category.assoc,
      IsPushout.inr_desc, whisker_exchange]

lemma pushoutProduct.r_w : pushoutProduct.r.left h ≫ pushoutProduct.desc f (hornInclusion 2 1) =
    pushoutProduct.desc g (hornInclusion 2 1) ≫ Δ[2] ◁ h.r.right := by
  dsimp [r.left]
  apply (pushoutProduct.IsPushout g (hornInclusion 2 1)).hom_ext
  · dsimp [pushoutProduct.desc]
    rw [IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc, ← Category.assoc,
      IsPushout.inl_desc, ← MonoidalCategory.whiskerLeft_comp, h.r_w]
    rfl
  · dsimp [pushoutProduct.desc]
    rw [IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc, ← Category.assoc,
      IsPushout.inr_desc, whisker_exchange]

noncomputable
def pushoutProduct.RetractArrow :
    RetractArrow (pushoutProduct.desc f (hornInclusion 2 1)) (pushoutProduct.desc g (hornInclusion 2 1)) where
  i := {
    left := pushoutProduct.i.left h
    right :=  Δ[2] ◁ h.i.right
    w := pushoutProduct.i_w h
  }
  r := {
    left := pushoutProduct.r.left h
    right :=  Δ[2] ◁ h.r.right
    w := pushoutProduct.r_w h
  }
  retract := Arrow.hom_ext _ _ (pushoutProduct.retract_left h) (by
    dsimp
    rw [← MonoidalCategory.whiskerLeft_comp, h.retract_right]
    rfl)

end Retract

section TransfiniteComposition

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet) [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)

noncomputable
def F' : J ⥤ SSet where
  obj j := pushoutProduct.pt (c.ι.app j) (hornInclusion 2 1)
  map {j k} f :=
    (pushoutProduct.desc' (c.ι.app j) (hornInclusion 2 1))
      (Δ[2] ◁ (F.map f) ≫ (pushoutProduct.inl (c.ι.app k) (hornInclusion 2 1)))
      (pushoutProduct.inr (c.ι.app k) (hornInclusion 2 1))
      (by
        have := c.ι.naturality f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        rw [← this, MonoidalCategory.whiskerLeft_comp, Category.assoc, ← pushoutProduct.w,
          ← Category.assoc, ← @whisker_exchange, Category.assoc])
  map_id j := by
    simp only [Functor.const_obj_obj, Fin.isValue, pushoutProduct.pt, pushoutProduct.inl,
      IsPushout.cocone_inl, pushoutProduct.inr, IsPushout.cocone_inr, Functor.const_obj_map,
      eq_mp_eq_cast, cast_eq, id_eq, eq_mpr_eq_cast, pushoutProduct.desc',
      CategoryTheory.Functor.map_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    exact pushoutProduct.desc_id (c.ι.app j) (hornInclusion 2 1)
  map_comp f g := sorry

noncomputable
def c' : Cocone (F' F c) where
  pt := Δ[2] ⊗ c.pt
  ι := {
    app := fun j ↦ pushoutProduct.desc (c.ι.app j) (hornInclusion 2 1)
    naturality := sorry
  }

noncomputable
def Pj_jsucc (j : J) :=
  pushoutProduct.pt (F.map (homOfLE (Order.le_succ j))) (hornInclusion 2 1)

noncomputable
def φ (j : J) : (Pj_jsucc F j) ⟶ (F' F c).obj j := by
  refine pushoutProduct.desc' _ _ ?_ ?_ ?_
  · exact pushoutProduct.inl (c.ι.app j) (hornInclusion 2 1)
  · exact Λ[2, 1] ◁ (c.ι.app (Order.succ j)) ≫ pushoutProduct.inr (c.ι.app j) (hornInclusion 2 1)
  · sorry

lemma newSqComm :
  pushoutProduct.desc (F.map (homOfLE (Order.le_succ j))) (hornInclusion 2 1) ≫ pushoutProduct.inl (c.ι.app (Order.succ j)) (hornInclusion 2 1)
    = (φ F c j) ≫ (F' F c).map (homOfLE (Order.le_succ j)) := by sorry

noncomputable
def newPushoutCocone (j : J) : PushoutCocone (pushoutProduct.desc (F.map (homOfLE (Order.le_succ j))) (hornInclusion 2 1)) (φ F c j) :=
  PushoutCocone.mk _ _ (newSqComm F c)

noncomputable
def newPushoutIsColimit : IsColimit (newPushoutCocone F c j) := by
  apply PushoutCocone.IsColimit.mk
  · sorry
  · sorry
  · sorry
  · sorry

end TransfiniteComposition

end SSet
