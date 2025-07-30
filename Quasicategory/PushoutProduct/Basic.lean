import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

universe w v v' u u'

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
def leftFunctor_map_left  :
    pt h.hom f.hom ⟶ pt h.hom g.hom :=
  pushout.map _ _ _ _
    (h.right ◁ sq.left) (h.left ◁ sq.right) (h.left ◁ sq.left)
    (whisker_exchange _ _).symm (by simp [← MonoidalCategory.whiskerLeft_comp, Arrow.w])

@[simp]
noncomputable
def leftFunctor_map :
    Arrow.mk (h.hom ◫ f.hom) ⟶ Arrow.mk (h.hom ◫ g.hom) where
  left := leftFunctor_map_left h sq
  right := h.right ◁ sq.right
  w := by
    dsimp [Functor.PushoutObjObj.ι]
    apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp, Arrow.w]
    · simp [← whisker_exchange]

@[simp]
noncomputable
def leftFunctor : Arrow C ⥤ Arrow C where
  obj f := h.hom ◫ f.hom
  map := leftFunctor_map h

@[simp]
noncomputable
def leftBifunctor_map_left :
    pt f.hom h.hom ⟶ pt g.hom h.hom :=
  pushout.map _ _ _ _
    (sq.right ▷ h.left) (sq.left ▷ h.right) (sq.left ▷ h.left)
    (by simp [← MonoidalCategory.comp_whiskerRight, Arrow.w]) (whisker_exchange sq.left h.hom)

@[simp]
noncomputable
def leftBifunctor_map :
    leftFunctor f ⟶ leftFunctor g where
  app h := {
    left := leftBifunctor_map_left h sq
    right := sq.right ▷ h.right
    w := by
      dsimp [Functor.PushoutObjObj.ι]
      apply pushout.hom_ext
      · simp [whisker_exchange]
      · simp [← MonoidalCategory.comp_whiskerRight, Arrow.w] }
  naturality f' g' sq' := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      all_goals simp [← whisker_exchange_assoc]
    · exact (whisker_exchange _ _)

@[simps!]
noncomputable
def leftBifunctor : Arrow C ⥤ Arrow C ⥤ Arrow C where
  obj := leftFunctor
  map := leftBifunctor_map

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
def natTransLeftFunctor : D ⥤ C := (NatTrans.arrowFunctor h) ⋙ leftFunctor g ⋙ Arrow.leftFunc

@[simp]
noncomputable
def natTransLeftFunctor_comp {G' : D ⥤ C} (h' : G ⟶ G') :
    (natTransLeftFunctor h g) ⟶ (natTransLeftFunctor (h ≫ h') g) :=
  whiskerRight (NatTrans.arrowFunctor_NatTrans h h') _

@[simps!]
noncomputable
def inlDescFunctor : (F ⋙ tensorLeft Y) ⟶ (natTransLeftFunctor h g) where
  app A := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) g (h.app A)).inl

@[simps!]
noncomputable
def inrDescFunctor : (G ⋙ tensorLeft X) ⟶ (natTransLeftFunctor h g) where
  app A := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) g (h.app A)).inr

@[simps!]
noncomputable
def descFunctor : (natTransLeftFunctor h g) ⟶ (G ⋙ tensorLeft Y) where
  app A := g ◫ h.app A
  naturality _ _ _ := by
    dsimp [Functor.PushoutObjObj.ι]
    apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · simp [whisker_exchange]

end NatTrans

--variable (hp : IsColimit (PushoutCocone.mk _ _ h.w))

section

variable {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y} {s : X ⟶ A} {t : Y ⟶ B}

variable (S : C) [hS : ∀ S : C, PreservesColimitsOfSize (tensorLeft S)]

def whiskerPushoutAux (s : X ⟶ A) (g : X ⟶ Y) :
    IsPushout (S ◁ s) (S ◁ g) (S ◁ (pushout.inl s g)) (S ◁ (pushout.inr s g)) where
  w := by simp only [← MonoidalCategory.whiskerLeft_comp, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorLeft S) s g⟩

def whiskerPushout (h : IsPushout s g f t) :
    IsPushout (S ◁ s) (S ◁ g) (S ◁ f) (S ◁ t) :=
  (whiskerPushoutAux S s g).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (whiskerLeftIso S h.isoPushout).symm (by simp) (by simp)
    (by simp [← MonoidalCategory.whiskerLeft_comp, IsPushout.inl_isoPushout_inv])
    (by simp [← MonoidalCategory.whiskerLeft_comp, IsPushout.inl_isoPushout_inv])

end

section

variable {f g : Arrow C} (ι : Arrow C) (h : f ⟶ g) (hp : IsColimit (PushoutCocone.mk _ _ h.w))

variable [hS : ∀ S : C, PreservesColimitsOfSize (tensorLeft S)]

variable (s : PushoutCocone ((leftBifunctor.obj ι).map h).left ((leftBifunctor.obj ι).obj f).hom)

@[simp]
noncomputable
def temp_desc : ((leftFunctor ι).obj g).right ⟶ s.pt :=
  (whiskerPushout ι.right (IsPushout.of_isColimit hp)).desc
    ((pushout.inl _ _) ≫ s.inl) s.inr
    (by simpa [pushout.inr_desc_assoc, Functor.PushoutObjObj.ι] using (pushout.inl _ _) ≫= s.condition)

def temp_fac_left : ((leftFunctor ι).obj g).hom ≫ temp_desc ι h hp s = s.inl := by
  simp [Functor.PushoutObjObj.ι]
  apply pushout.hom_ext
  · simp
  · apply (whiskerPushout _ (IsPushout.of_isColimit hp)).hom_ext
    · simp [← pushout.condition_assoc, whisker_exchange_assoc]
    · simp [whisker_exchange_assoc]
      have := pushout.inr _ _ ≫= s.condition
      simp [Functor.PushoutObjObj.ι] at this
      rw [this]

def temp_uniq (m : ((leftBifunctor.obj ι).obj g).right ⟶ s.pt)
    (fac_left : ((leftBifunctor.obj ι).obj g).hom ≫ m = s.inl)
    (fac_right : ((leftBifunctor.obj ι).map h).right ≫ m = s.inr) : m = temp_desc ι h hp s := by
  apply (whiskerPushout _ (IsPushout.of_isColimit hp)).hom_ext
  · simpa [Functor.PushoutObjObj.ι] using pushout.inl _ _ ≫= fac_left
  · simpa

noncomputable
def leftBifunctor_obj_map_preserves_pushouts
      {f g : Arrow C} (ι : Arrow C) (h : f ⟶ g) (hp : IsColimit (PushoutCocone.mk _ _ h.w)) :
    IsColimit (PushoutCocone.mk _ _ ((leftBifunctor.obj ι).map h).w) :=
  PushoutCocone.IsColimit.mk _ (temp_desc ι h hp) (temp_fac_left ι h hp)
    (by simp) (temp_uniq ι h hp)

def leftBifunctor_obj_map_preserves_pushouts' {A B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y} {s : X ⟶ A} {t : Y ⟶ B}
      (ι : Z ⟶ W) (h : IsPushout s g f t) :
    IsPushout ((leftBifunctor.obj (Arrow.mk ι)).map (Arrow.homMk' s t h.w)).left
      (ι ◫ g)
      (ι ◫ f)
      (W ◁ t) := by
  apply IsPushout.of_isColimit' ⟨((leftBifunctor.obj (Arrow.mk ι)).map (Arrow.homMk' _ _ h.w)).w⟩
  apply leftBifunctor_obj_map_preserves_pushouts
  exact h.isColimit

end

section

variable (W : MorphismProperty C)

variable (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

variable {A B X Y : C} {f : A ⟶ B} (ι : X ⟶ Y) (h : W.TransfiniteCompositionOfShape J f)

noncomputable
def temp_isoBot : (natTransLeftFunctor h.incl ι).obj ⊥ ≅ pushout (ι ▷ A) (X ◁ f) := by
  have : Arrow.mk (h.incl.app ⊥) ≅ Arrow.mk f :=
    Arrow.isoMk h.isoBot (Iso.refl _) (by simpa using (h.isoBot.inv_comp_eq.1 h.fac).symm)
  exact Comma.leftIso ((leftFunctor (Arrow.mk ι)).mapIso this)

@[simps!]
def _root_.CategoryTheory.NatTrans.whiskerCocone {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (h : F ⟶ G) (s : Cocone G) : Cocone F where
  pt := s.pt
  ι := h ≫ s.ι

noncomputable
def temp_isColimit {m : J} (hm : Order.IsSuccLimit m) :
    (IsColimit ((Set.principalSegIio m).cocone (natTransLeftFunctor h.incl ι))) where
  desc := by
    intro s
    refine pushout.desc ?_ ?_ ?_
    · simp
      have := (h.isWellOrderContinuous.nonempty_isColimit m hm).some.desc
      simp at this


      sorry
    · simp
      have := NatTrans.whiskerCocone (whiskerLeft ((Set.principalSegIio m).monotone.functor) (inrDescFunctor h.incl ι)) s

      sorry
    · sorry

def temp_isWellOrderContinuous : (natTransLeftFunctor h.incl ι).IsWellOrderContinuous where
  nonempty_isColimit _ hm := ⟨temp_isColimit _ _ _ _ hm⟩

noncomputable
def tempppp : TransfiniteCompositionOfShape J (ι ◫ f) where
  F := natTransLeftFunctor h.incl ι
  isoBot := temp_isoBot ..
  isWellOrderContinuous := temp_isWellOrderContinuous ..
  incl := descFunctor h.incl ι ≫ ((tensorLeft Y).constComp J B).hom
  isColimit := sorry
  fac := by
    apply pushout.hom_ext
    · simp [Functor.PushoutObjObj.ι, temp_isoBot, ← MonoidalCategory.whiskerLeft_comp]
    · simp [Functor.PushoutObjObj.ι, temp_isoBot]

end

end CategoryTheory.PushoutProduct

namespace SSet

open Simplicial PushoutProduct

inductive bdryHornPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (m : ℕ) : bdryHornPushout (∂Δ[m].ι ◫ Λ[2, 1].ι)

/-- the class of pushout products of `∂Δ[m] ↪ Δ[m]` with `Λ[2, 1] ↪ Δ[2]`. -/
def bdryHornPushouts : MorphismProperty SSet := fun _ _ p ↦ bdryHornPushout p

end SSet
