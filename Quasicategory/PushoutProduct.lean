import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Quasicategory.Retract.Basic
import Quasicategory.TransfiniteComposition.Basic

/-!

Defines pushout-products and a little bit of API.

Everything here should be generalized and more API should be added.

-/

universe v' v u' u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.PushoutProduct

variable {A B X Y : SSet} (f : A ⟶ B) (g : X ⟶ Y)

@[simp]
def IsPushout := IsPushout.of_hasPushout (g ▷ A) (X ◁ f)

@[simp]
noncomputable
def pt : SSet := (IsPushout f g).cocone.pt

/-- The pushout-product of `f` and `g`. -/
@[simp]
noncomputable
def pushoutProduct : pt f g ⟶ Y ⊗ B :=
  (IsPushout f g).desc (Y ◁ f) (g ▷ B) rfl

/-- Notation for the pushout-product. -/
scoped infixr:80 " ◫ " => PushoutProduct.pushoutProduct

@[simp]
noncomputable
def desc {W : SSet} (h : Y ⊗ A ⟶ W) (k : X ⊗ B ⟶ W) (w : g ▷ A ≫ h = X ◁ f ≫ k) :
    pt f g ⟶ W := (IsPushout f g).desc h k w

@[simp]
noncomputable
def inl : (Y ⊗ A) ⟶ pt f g := (IsPushout f g).cocone.inl

@[simp]
noncomputable
def inr : (X ⊗ B) ⟶ pt f g := (IsPushout f g).cocone.inr

@[simp]
lemma inl_desc {W : SSet} (h : Y ⊗ A ⟶ W) (k : X ⊗ B ⟶ W) (w : g ▷ A ≫ h = X ◁ f ≫ k) :
    (inl f g) ≫ (desc f g) h k w = h := (IsPushout f g).inl_desc _ _ _

@[simp]
lemma inr_desc {W : SSet} (h : Y ⊗ A ⟶ W) (k : X ⊗ B ⟶ W) (w : g ▷ A ≫ h = X ◁ f ≫ k) :
    (inr f g) ≫ (desc f g) h k w = k := (IsPushout f g).inr_desc _ _ _

@[simp]
lemma w : g ▷ A ≫ inl f g = X ◁ f ≫ inr f g  := (IsPushout f g).toCommSq.w

@[simp]
lemma desc_id : (desc f g) (inl f g) (inr f g) (w f g) = 𝟙 (pt f g) :=
  (IsPushout f g).hom_ext (by aesop) (by aesop)


variable {C : Type u} [Category.{v} C] {F G : C ⥤ SSet} (h : F ⟶ G)

variable {X Y : SSet} (g : X ⟶ Y)

@[simp]
noncomputable
def natTransLeftFunctor_map {A B : C} (f : A ⟶ B) : pt (h.app A) g ⟶ pt (h.app B) g := by
  refine (desc (h.app A) g)
    (Y ◁ (F.map f) ≫ inl (h.app B) g) (X ◁ (G.map f) ≫ inr (h.app B) g) ?_
  rw [← Category.assoc (X ◁ _), ← MonoidalCategory.whiskerLeft_comp, ← h.naturality f,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, ← PushoutProduct.w]
  rfl

@[simp]
lemma natTransLeftFunctor_map_id (A : C) :
    natTransLeftFunctor_map h g (𝟙 A) = 𝟙 (pt (h.app A) g) :=
  (IsPushout (h.app A) g).hom_ext (by aesop) (by aesop)

@[simp]
lemma natTransLeftFunctor_map_comp {X Y Z : C} (s : X ⟶ Y) (t : Y ⟶ Z ):
    natTransLeftFunctor_map h g (s ≫ t) = natTransLeftFunctor_map h g s ≫ natTransLeftFunctor_map h g t := by
  apply (IsPushout (h.app X) g).hom_ext (by aesop) (by aesop)

@[simp]
noncomputable
def natTransLeftFunctor : C ⥤ SSet where
  obj A := pt (h.app A) g
  map := natTransLeftFunctor_map h g
  map_id := natTransLeftFunctor_map_id h g
  map_comp := natTransLeftFunctor_map_comp h g

noncomputable
def natTransLeftFunctor_comp {G' : C ⥤ SSet} (h' : G ⟶ G') :
    (natTransLeftFunctor h g) ⟶ (natTransLeftFunctor (h ≫ h') g) where
  app A := by
    refine (IsPushout (h.app A) g).desc
      (inl ((h ≫ h').app A) g) (X ◁ (h'.app A) ≫ inr ((h ≫ h').app A) g) ?_
    · rw [w]; aesop
  naturality {A _} f := by
    apply (IsPushout (h.app A) g).hom_ext (by aesop)
    simp only [natTransLeftFunctor, NatTrans.comp_app, pt, natTransLeftFunctor_map, desc, inl,
      IsPushout.cocone_inl, inr, IsPushout.cocone_inr, IsPushout.inr_desc_assoc, Category.assoc,
      IsPushout.inr_desc, MonoidalCategory.whiskerLeft_comp]
    rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, h'.naturality]

/-- very slow :( -/
noncomputable
def descFunctor : (natTransLeftFunctor h g) ⟶ (G ⋙ tensorLeft Y) where
  app A := (h.app A) ◫ g
  naturality A B f := by
    apply (IsPushout (h.app A) g).hom_ext
    · simp_all only [Functor.comp_obj, tensorLeft_obj, natTransLeftFunctor, pt, natTransLeftFunctor_map, desc, inl,
        IsPushout.cocone_inl, inr, IsPushout.cocone_inr, pushoutProduct, IsPushout.inl_desc_assoc, Category.assoc,
        IsPushout.inl_desc, Functor.comp_map, tensorLeft_map]
      ext : 1
      · ext n a : 2
        simp_all only [Category.assoc, ChosenFiniteProducts.whiskerLeft_fst]
      · ext n a : 2
        simp_all only [Category.assoc, ChosenFiniteProducts.whiskerLeft_snd, ChosenFiniteProducts.whiskerLeft_snd_assoc,
          NatTrans.naturality]
    · simp_all only [Functor.comp_obj, tensorLeft_obj, natTransLeftFunctor, pt, natTransLeftFunctor_map, desc, inl,
        IsPushout.cocone_inl, inr, IsPushout.cocone_inr, pushoutProduct, IsPushout.inr_desc_assoc, Category.assoc,
        IsPushout.inr_desc, Functor.comp_map, tensorLeft_map]
      rfl

end CategoryTheory.PushoutProduct

namespace SSet

open Limits Simplicial PushoutProduct

/-- pushout in proof `0079` (for retract diagram) -/
def Λ_pushout (m : ℕ) (i : Fin (m + 1)) :=
  PushoutProduct.IsPushout (hornInclusion m i) (hornInclusion 2 1)

noncomputable
def Λ_pushoutProduct (m : ℕ) (i : Fin (m + 1)) : (Λ_pushout m i).cocone.pt ⟶ Δ[2] ⊗ Δ[m] :=
  (hornInclusion m i) ◫ (hornInclusion 2 1)

inductive bdryPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃m : ℕ⦄ : bdryPushout ((boundaryInclusion m) ◫ (hornInclusion 2 1))

/-- the class of pushout products of `∂Δ[n] ↪ Δ[n]` with `Λ[n, i] ↪ Δ[n]`. -/
def bdryPushoutClass : MorphismProperty SSet := fun _ _ p ↦ bdryPushout p

variable {X Y A B : SSet} (g : X ⟶ Y) (f : A ⟶ B)
/-
section Pushout

variable {s : X ⟶ A} {t : Y ⟶ B} (h : CommSq s g f t)

/-- given a `CommSq s g f t`, we get a map between pushout products
  of `f` with `hornInclusion 2 1` and `g` with `hornInclusion 2 1`. -/
noncomputable
def pushoutDescOfCommSq : (pt g (hornInclusion 2 1)) ⟶ (pt f (hornInclusion 2 1)) :=
  IsPushout.desc (PushoutProduct.IsPushout g (hornInclusion 2 1))
    ((Δ[2] ◁ s) ≫ (PushoutProduct.inl f (hornInclusion 2 1)))
    ((Λ[2, 1] ◁ t) ≫ (PushoutProduct.inr f (hornInclusion 2 1)))
    (by
     change Λ[2, 1] ◁ s ≫ hornInclusion 2 1 ▷ A ≫ pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f) = (Λ[2, 1] ◁ (g ≫ t)) ≫ _
     rw [Λ[2, 1] ◁ s ≫= (PushoutProduct.IsPushout f (hornInclusion 2 1)).toCommSq.w, ← h.w]
     rfl )

/-- using the above map between pushout products, we get a new `CommSq`. -/
lemma pushoutCommSq_w : (pushoutDescOfCommSq g f h) ≫ f ◫ (hornInclusion 2 1) =
    (g ◫ (hornInclusion 2 1)) ≫ (Δ[2] ◁ t) := by
  apply Limits.pushout.hom_ext
  · simp [pushoutDescOfCommSq, IsPushout.inl_desc]
    rw [← MonoidalCategory.whiskerLeft_comp, h.w, MonoidalCategory.whiskerLeft_comp]
  · simp [pushoutDescOfCommSq, IsPushout.inr_desc]
    rw [@whisker_exchange]

/-- the `PushoutCocone` determined by the above `CommSq`. -/
noncomputable
def pushoutCommSq_cocone : PushoutCocone (pushoutDescOfCommSq g f h) (g ◫ (hornInclusion 2 1)) :=
    .mk _ _ (pushoutCommSq_w g f h)

/-- such a `PushoutCocone` gives us a `PushoutCocone` of `Δ[2] ◁ s` and `Δ[2] ◁ g`. -/
noncomputable
def changePushoutCocone (C : PushoutCocone (pushoutDescOfCommSq g f h) (g ◫ (hornInclusion 2 1))) :
    PushoutCocone (Δ[2] ◁ s) (Δ[2] ◁ g) := by
  refine PushoutCocone.mk ((pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f)) ≫ C.inl) C.inr ?_
  have a := C.condition
  dsimp only [pushoutDescOfCommSq, pushoutProduct] at a
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

variable (C : PushoutCocone (pushoutDescOfCommSq g f h'.toCommSq) (g ◫ (hornInclusion 2 1)))

lemma temp : Δ[2] ◁ s ≫ pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f) ≫ C.inl =
    Δ[2] ◁ g ≫ C.inr := by
  have a := C.condition
  dsimp only [pushoutDescOfCommSq, pushoutProduct] at a
  rw [← (IsPushout.inl_desc _ (Δ[2] ◁ g)), Category.assoc, ← a, ← Category.assoc, ← Category.assoc, IsPushout.inl_desc]
  rfl

@[simp]
noncomputable
def pushoutCommSq_IsColimit'_desc : Δ[2] ⊗ B ⟶ C.pt :=
  (whiskerPushout h' Δ[2]).desc
    ((pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f)) ≫ C.inl) C.inr (temp h' C)

-- needs to be cleaned up
lemma pushoutCommSq_IsColimit'_fac_left :
    (f ◫ (hornInclusion 2 1)) ≫ pushoutCommSq_IsColimit'_desc h' C = C.inl := by
  apply (PushoutProduct.IsPushout f (hornInclusion 2 1)).hom_ext
  · simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, PushoutCocone.ι_app_left,
      PushoutCocone.ι_app_right, IsPushout.inl_desc_assoc, IsPushout.inl_desc, pushoutCommSq_IsColimit'_desc]
  · apply (whiskerPushout h' _).hom_ext
    · change (Λ[2, 1] ◁ f ≫ PushoutProduct.inr f (hornInclusion 2 1)) ≫
        (f ◫ (hornInclusion 2 1)) ≫ pushoutCommSq_IsColimit'_desc h' C =
        Λ[2, 1] ◁ f ≫ PushoutProduct.inr f (hornInclusion 2 1) ≫ C.inl
      rw [← Category.assoc, ← PushoutProduct.w, Category.assoc, Category.assoc,
        ← Category.assoc (PushoutProduct.inl f (hornInclusion 2 1))]
      dsimp only [PushoutProduct.inl, pushoutProduct, pushoutCommSq_IsColimit'_desc]
      rw [IsPushout.inl_desc]
      simp only [Fin.isValue, PushoutProduct.pt, PushoutCocone.ι_app_left, pushoutProduct,
        PushoutCocone.ι_app_right, IsPushout.inl_desc, PushoutProduct.inr, IsPushout.cocone_inr]
      exact pushout.condition_assoc C.inl
    · change (Λ[2, 1] ◁ t ≫ PushoutProduct.inr f (hornInclusion 2 1)) ≫
        (f ◫ (hornInclusion 2 1)) ≫ pushoutCommSq_IsColimit'_desc h' C =
        Λ[2, 1] ◁ t ≫ PushoutProduct.inr f (hornInclusion 2 1) ≫ C.inl
      rw [Category.assoc, ← Category.assoc (PushoutProduct.inr f (hornInclusion 2 1))]
      dsimp only [PushoutProduct.inl, pushoutProduct, pushoutCommSq_IsColimit'_desc]
      rw [IsPushout.inr_desc, ← Category.assoc, @whisker_exchange, Category.assoc,
        IsPushout.inr_desc, ← Category.assoc]
      have := PushoutProduct.inr g (hornInclusion 2 1) ≫= C.condition
      dsimp only [PushoutProduct.inr, pushoutDescOfCommSq] at this ⊢
      rw [← Category.assoc, IsPushout.inr_desc] at this
      rw [this]
      aesop

lemma pushoutCommSq_IsColimit'_fac_right : Δ[2] ◁ t ≫ pushoutCommSq_IsColimit'_desc h' C = C.inr := by
  simp only [Fin.isValue, PushoutProduct.pt, pushoutProduct, pushoutCommSq_IsColimit'_desc,
    PushoutCocone.ι_app_left, PushoutCocone.ι_app_right, IsPushout.inr_desc]

lemma pushoutCommSq_IsColimit'_uniq (m : Δ[2] ⊗ B ⟶ C.pt)
    (fac_left : (f ◫ (hornInclusion 2 1)) ≫ m = C.inl)
    (fac_right : Δ[2] ◁ t ≫ m = C.inr) : m = pushoutCommSq_IsColimit'_desc h' C := by
  apply (whiskerPushout h' _).hom_ext
  · have := PushoutProduct.inl f (hornInclusion 2 1) ≫= fac_left
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
    IsPushout (pushoutDescOfCommSq g f h'.toCommSq) (g ◫ (hornInclusion 2 1))
      (f ◫ (hornInclusion 2 1)) ((Δ[2] ◁ t)) where
  w := pushoutCommSq_w g f h'.toCommSq
  isColimit' := ⟨pushoutCommSq_IsColimit' h'⟩

end Pushout

section Retract

variable {f g} (h : RetractArrow f g)

noncomputable
def pushoutProduct.i.left :
    pt f (hornInclusion 2 1) ⟶ pt g (hornInclusion 2 1) :=
  (PushoutProduct.desc f (hornInclusion 2 1))
    (Δ[2] ◁ h.i.left ≫ (PushoutProduct.inl g (hornInclusion 2 1)))
    (Λ[2, 1] ◁ h.i.right ≫ (PushoutProduct.inr g (hornInclusion 2 1)))
    (by
      dsimp
      rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ← h.i_w,
        MonoidalCategory.whiskerLeft_comp, ← whisker_exchange, Category.assoc, Category.assoc,
        ← (PushoutProduct.IsPushout g (hornInclusion 2 1)).w])

noncomputable
def pushoutProduct.r.left :
    pt g (hornInclusion 2 1) ⟶ pt f (hornInclusion 2 1) :=
  (PushoutProduct.desc g (hornInclusion 2 1))
    (Δ[2] ◁ h.r.left ≫ (PushoutProduct.inl f (hornInclusion 2 1)))
    (Λ[2, 1] ◁ h.r.right ≫ (PushoutProduct.inr f (hornInclusion 2 1)))
    (by
      dsimp
      rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ← h.r_w,
        MonoidalCategory.whiskerLeft_comp, ← whisker_exchange, Category.assoc, Category.assoc,
        ← (PushoutProduct.IsPushout f (hornInclusion 2 1)).w])

lemma pushoutProduct.retract_left : pushoutProduct.i.left h ≫ pushoutProduct.r.left h = 𝟙 _ := by
  dsimp [i.left, r.left]
  refine (PushoutProduct.IsPushout f (hornInclusion 2 1)).hom_ext ?_ ?_
  · simp only [Fin.isValue, IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h.retract_left]
    rfl
  · simp only [Fin.isValue, IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h.retract_right]
    rfl

lemma pushoutProduct.i_w : pushoutProduct.i.left h ≫ g ◫ (hornInclusion 2 1) =
    (f ◫ (hornInclusion 2 1)) ≫ Δ[2] ◁ h.i.right := by
  dsimp [i.left]
  apply (PushoutProduct.IsPushout f (hornInclusion 2 1)).hom_ext
  · dsimp [pushoutProduct]
    rw [IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc, ← Category.assoc,
      IsPushout.inl_desc, ← MonoidalCategory.whiskerLeft_comp, h.i_w]
    rfl
  · dsimp [pushoutProduct]
    rw [IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc, ← Category.assoc,
      IsPushout.inr_desc, whisker_exchange]

lemma pushoutProduct.r_w : pushoutProduct.r.left h ≫ f ◫ (hornInclusion 2 1) =
    (g ◫ (hornInclusion 2 1)) ≫ Δ[2] ◁ h.r.right := by
  dsimp [r.left]
  apply (PushoutProduct.IsPushout g (hornInclusion 2 1)).hom_ext
  · dsimp [pushoutProduct]
    rw [IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc, ← Category.assoc,
      IsPushout.inl_desc, ← MonoidalCategory.whiskerLeft_comp, h.r_w]
    rfl
  · dsimp [pushoutProduct]
    rw [IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc, ← Category.assoc,
      IsPushout.inr_desc, whisker_exchange]

noncomputable
def pushoutProduct.RetractArrow :
    RetractArrow (f ◫ (hornInclusion 2 1)) (g ◫ (hornInclusion 2 1)) where
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

-/

section TransfiniteComposition

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet) [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)

noncomputable
abbrev F' : J ⥤ SSet := PushoutProduct.natTransLeftFunctor c.ι (hornInclusion 2 1)

instance : (F' F c).IsWellOrderContinuous := sorry

noncomputable
def c' : Cocone (F' F c) where
  pt := Δ[2] ⊗ c.pt
  ι := PushoutProduct.descFunctor c.ι (hornInclusion 2 1)

@[simp]
def _root_.CategoryTheory.Functor.succ : J ⥤ SSet where
  obj j := F.obj (Order.succ j)
  map f := F.map (homOfLE (Order.succ_le_succ f.le))
  map_comp _ _ := by rw [← F.map_comp]; rfl

@[simp]
def _root_.CategoryTheory.Functor.succNatTrans : F ⟶ F.succ where
  app j := F.map (homOfLE (Order.le_succ j))
  naturality {j j'} f := by
    simp
    rw [← F.map_comp, ← F.map_comp]
    suffices f ≫ homOfLE (Order.le_succ j') =
      (homOfLE (Order.le_succ j)) ≫ homOfLE (Order.succ_le_succ f.le) by rfl
    rfl

noncomputable
abbrev P := PushoutProduct.natTransLeftFunctor (F.succNatTrans) (hornInclusion 2 1)

@[simp]
def φaux : (F.succ) ⟶ (Functor.const J).obj c.pt where
  app j := c.ι.app (Order.succ j)

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
@[simp]
lemma φaux' : (F.succNatTrans) ≫ (φaux F c) = c.ι := by
  simp_all only [Functor.succ, homOfLE_leOfHom, Functor.succNatTrans, φaux]
  ext x n a : 4
  simp_all only [Functor.const_obj_obj, homOfLE_leOfHom, NatTrans.comp_app, NatTrans.naturality, Functor.const_obj_map,
    Category.comp_id]

noncomputable
def Pj_jsucc (j : J) :=
  PushoutProduct.pt (F.map (homOfLE (Order.le_succ j))) (hornInclusion 2 1)

noncomputable
def φj (j : J) : (Pj_jsucc F j) ⟶ (F' F c).obj j := by
  refine PushoutProduct.desc _ _ ?_ ?_ ?_
  · exact PushoutProduct.inl (c.ι.app j) (hornInclusion 2 1)
  · exact Λ[2, 1] ◁ (c.ι.app (Order.succ j)) ≫ PushoutProduct.inr (c.ι.app j) (hornInclusion 2 1)
  · sorry

-- not defeq but right approach, (P F) ⟶ (F' F c)
set_option maxHeartbeats 400000 in
noncomputable
def φ : P F ⟶ natTransLeftFunctor (F.succNatTrans ≫ φaux F c) (hornInclusion 2 1) :=
  PushoutProduct.natTransLeftFunctor_comp (F.succNatTrans) (hornInclusion 2 1) (φaux F c)

lemma newSqComm :
  ((F.map (homOfLE (Order.le_succ j))) ◫ (hornInclusion 2 1)) ≫ PushoutProduct.inl (c.ι.app (Order.succ j)) (hornInclusion 2 1)
    = (φj F c j) ≫ (F' F c).map (homOfLE (Order.le_succ j)) := by sorry

noncomputable
def newPushoutCocone (j : J) : PushoutCocone ((F.map (homOfLE (Order.le_succ j))) ◫ (hornInclusion 2 1)) (φj F c j) :=
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
