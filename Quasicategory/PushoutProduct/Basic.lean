import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

universe v v' u u'

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.PushoutProduct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasPushouts C]

section Defs

variable {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)

@[simp]
noncomputable
abbrev pt : C := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f g).pt

/-- The pushout-product of `f` and `g`. -/
@[simp]
noncomputable
abbrev pushoutProduct : pushout (f ▷ X) (A ◁ g) ⟶ B ⊗ Y :=
  (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f g).ι

/-- Notation for the pushout-product. -/
scoped infixr:80 " ◫ " => PushoutProduct.pushoutProduct

end Defs

section Functor

variable (h : Arrow C) {f g : Arrow C} (sq : f ⟶ g)

@[simp]
noncomputable
def rightFunctor_map_left  :
    pt f.hom h.hom ⟶ pt g.hom h.hom :=
  pushout.map _ _ _ _
    (sq.right ▷ h.left) (sq.left ▷ h.right) (sq.left ▷ h.left)
    (by simp [← MonoidalCategory.comp_whiskerRight, Arrow.w]) (whisker_exchange sq.left h.hom)

@[simp]
noncomputable
def rightFunctor_map :
    Arrow.mk (f.hom ◫ h.hom) ⟶ Arrow.mk (g.hom ◫ h.hom) where
  left := rightFunctor_map_left h sq
  right := sq.right ▷ h.right
  w := by
    dsimp [Functor.PushoutObjObj.ι]
    apply pushout.hom_ext
    · simp [← whisker_exchange]
    · simp [← MonoidalCategory.comp_whiskerRight, Arrow.w]

@[simp]
noncomputable
def rightFunctor : Arrow C ⥤ Arrow C where
  obj f := f.hom ◫ h.hom
  map := rightFunctor_map h

@[simp]
noncomputable
def rightBifunctor_map_left :
    pt h.hom f.hom ⟶ pt h.hom g.hom :=
  pushout.map _ _ _ _
    (h.right ◁ sq.left) (h.left ◁ sq.right) (h.left ◁ sq.left)
    (whisker_exchange h.hom sq.left).symm (by simp [← MonoidalCategory.whiskerLeft_comp, ← Arrow.w_mk_right])

@[simp]
noncomputable
def rightBifunctor_map :
    rightFunctor f ⟶ rightFunctor g where
  app h := {
    left := rightBifunctor_map_left h sq
    right := h.right ◁ sq.right
    w := by
      dsimp [Functor.PushoutObjObj.ι]
      apply pushout.hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, Arrow.w]
      · simp [whisker_exchange] }
  naturality f' g' sq' := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      all_goals simp [← whisker_exchange_assoc]
    · exact (whisker_exchange _ _).symm

@[simps!]
noncomputable
def rightBifunctor : Arrow C ⥤ Arrow C ⥤ Arrow C where
  obj := rightFunctor
  map := rightBifunctor_map

end Functor

section NatTrans

variable {D : Type u'} [Category.{v'} D]

variable {F G : D ⥤ C} (h : F ⟶ G)

variable {X Y : C} (g : X ⟶ Y)

@[simps!]
def _root_.CategoryTheory.NatTrans.arrowFunctor : D ⥤ Arrow C where
  obj A := Arrow.mk (h.app A)
  map f := Arrow.homMk' _ _ (h.naturality f)

@[simps]
def _root_.CategoryTheory.NatTrans.arrowFunctor_NatTrans {G' : D ⥤ C} (h' : G ⟶ G') :
    NatTrans.arrowFunctor h ⟶ NatTrans.arrowFunctor (h ≫ h') where
  app X := Arrow.homMk' (𝟙 _) (h'.app X)

@[simps!]
noncomputable
def natTransLeftFunctor : D ⥤ C := (NatTrans.arrowFunctor h) ⋙ rightFunctor g ⋙ Arrow.leftFunc

@[simp]
noncomputable
def natTransLeftFunctor_comp {G' : D ⥤ C} (h' : G ⟶ G') :
    (natTransLeftFunctor h g) ⟶ (natTransLeftFunctor (h ≫ h') g) :=
  whiskerRight (NatTrans.arrowFunctor_NatTrans h h') _

@[simps!]
noncomputable
def inrDescFunctor : (F ⋙ tensorRight Y) ⟶ (natTransLeftFunctor h g) where
  app A := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) (h.app A) g).inr

@[simps!]
noncomputable
def inlDescFunctor : (G ⋙ tensorRight X) ⟶ (natTransLeftFunctor h g) where
  app A := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) (h.app A) g).inl

@[simps!]
noncomputable
def descFunctor : (natTransLeftFunctor h g) ⟶ (G ⋙ tensorRight Y) where
  app A := h.app A ◫ g
  naturality _ _ _ := by
    dsimp [Functor.PushoutObjObj.ι]
    apply pushout.hom_ext
    · simp [whisker_exchange]
    · simp [← MonoidalCategory.comp_whiskerRight]

end NatTrans

--variable (hp : IsColimit (PushoutCocone.mk _ _ h.w))

section

variable {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y} {s : X ⟶ A} {t : Y ⟶ B}

variable (S : C) [hS : ∀ S : C, PreservesColimitsOfSize (tensorRight S)]

def whiskerPushoutAux (s : X ⟶ A) (g : X ⟶ Y) :
    IsPushout (s ▷ S) (g ▷ S) ((pushout.inl s g) ▷ S) ((pushout.inr s g) ▷ S) where
  w := by simp only [← comp_whiskerRight, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorRight S) s g⟩

def whiskerPushout (h : IsPushout s g f t) :
    IsPushout (s ▷ S) (g ▷ S) (f ▷ S) (t ▷ S) :=
  (whiskerPushoutAux S s g).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (whiskerRightIso h.isoPushout S).symm (by simp) (by simp)
    (by simp [← comp_whiskerRight, IsPushout.inl_isoPushout_inv]) (by simp [← comp_whiskerRight, IsPushout.inl_isoPushout_inv])

end

section

variable {f g : Arrow C} (ι : Arrow C) (h : f ⟶ g) (hp : IsColimit (PushoutCocone.mk _ _ h.w))

variable [hS : ∀ S : C, PreservesColimitsOfSize (tensorRight S)]

variable (s : PushoutCocone ((rightBifunctor.obj ι).map h).left ((rightBifunctor.obj ι).obj f).hom)

@[simp]
noncomputable
def temp_desc : ((rightBifunctor.obj ι).obj g).right ⟶ s.pt :=
  (whiskerPushout ι.right (IsPushout.of_isColimit hp)).desc
    ((pushout.inr (g.hom ▷ ι.left) (g.left ◁ ι.hom)) ≫ s.inl) s.inr
    (by simpa [pushout.inr_desc_assoc, Functor.PushoutObjObj.ι] using (pushout.inr _ _) ≫= s.condition)

def temp_fac_left : ((rightBifunctor.obj ι).obj g).hom ≫ temp_desc ι h hp s = s.inl := by
  simp [Functor.PushoutObjObj.ι]
  apply pushout.hom_ext
  · apply (whiskerPushout _ (IsPushout.of_isColimit hp)).hom_ext
    · simp [← Category.assoc _ (pushout.inl _ _), pushout.condition, ← whisker_exchange_assoc]
    · simp [← whisker_exchange_assoc]
      have := pushout.inl _ _ ≫= s.condition
      simp [Functor.PushoutObjObj.ι] at this
      rw [this]
  · simp

def temp_uniq (m : ((rightBifunctor.obj ι).obj g).right ⟶ s.pt)
    (fac_left : ((rightBifunctor.obj ι).obj g).hom ≫ m = s.inl)
    (fac_right : ((rightBifunctor.obj ι).map h).right ≫ m = s.inr) : m = temp_desc ι h hp s := by
  apply (whiskerPushout _ (IsPushout.of_isColimit hp)).hom_ext
  · simpa [Functor.PushoutObjObj.ι] using pushout.inr (g.hom ▷ ι.left) (g.left ◁ ι.hom) ≫= fac_left
  · simpa

noncomputable
def rightBifunctor_obj_map_preserves_pushouts
      {f g : Arrow C} (ι : Arrow C) (h : f ⟶ g) (hp : IsColimit (PushoutCocone.mk _ _ h.w)) :
    IsColimit (PushoutCocone.mk _ _ ((rightBifunctor.obj ι).map h).w) :=
  PushoutCocone.IsColimit.mk _ (temp_desc ι h hp) (temp_fac_left ι h hp)
    (by simp) (temp_uniq ι h hp)

def rightBifunctor_obj_map_preserves_pushouts' {A B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y} {s : X ⟶ A} {t : Y ⟶ B}
      (ι : Z ⟶ W) (h : IsPushout s g f t) :
    IsPushout ((rightBifunctor.obj (Arrow.mk ι)).map (Arrow.homMk' s t h.w)).left
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) g ι).ι
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f ι).ι
      (t ▷ W) := by
  apply IsPushout.of_isColimit' ⟨((rightBifunctor.obj (Arrow.mk ι)).map (Arrow.homMk' _ _ h.w)).w⟩
  apply rightBifunctor_obj_map_preserves_pushouts
  exact h.isColimit

end

end CategoryTheory.PushoutProduct

namespace SSet

open Simplicial PushoutProduct

inductive bdryHornPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (m : ℕ) : bdryHornPushout (∂Δ[m].ι ◫ Λ[2, 1].ι)

/-- the class of pushout products of `∂Δ[m] ↪ Δ[m]` with `Λ[2, 1] ↪ Δ[2]`. -/
def bdryHornPushouts : MorphismProperty SSet := fun _ _ p ↦ bdryHornPushout p

end SSet
