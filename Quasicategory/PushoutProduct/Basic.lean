import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

universe v v' u u'

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.PushoutProduct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasPushouts C]

section

variable {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)

@[simp]
noncomputable
abbrev pt : C := pushout (g ▷ A) (X ◁ f)

/-- The pushout-product of `f` and `g`. -/
@[simp]
noncomputable
abbrev pushoutProduct : pushout (g ▷ A) (X ◁ f) ⟶ Y ⊗ B :=
  pushout.desc (Y ◁ f) (g ▷ B) (whisker_exchange _ _).symm

/-- Notation for the pushout-product. -/
scoped infixr:80 " ◫ " => PushoutProduct.pushoutProduct

@[simp]
noncomputable
abbrev desc {W : C} (h : Y ⊗ A ⟶ W) (k : X ⊗ B ⟶ W) (w : g ▷ A ≫ h = X ◁ f ≫ k) :
    pt f g ⟶ W := pushout.desc h k w

@[simp]
noncomputable
abbrev inl : Y ⊗ A ⟶ pt f g := pushout.inl _ _

@[simp]
noncomputable
abbrev inr : X ⊗ B ⟶ pt f g := pushout.inr _ _

@[simp]
lemma desc_id : (desc f g) (inl f g) (inr f g) pushout.condition = 𝟙 (pt f g) :=
  pushout.hom_ext (by aesop) (by aesop)

@[simp]
noncomputable
def id_pushoutProduct_iso (W : C) : pt (𝟙 W) g ≅ Y ⊗ W :=
  IsPushout.isoIsPushout _ _ (IsPushout.of_hasPushout _ _) (by convert IsPushout.id_vert (g ▷ W); exact MonoidalCategory.whiskerLeft_id X W)

noncomputable
def id_pushoutProduct_iso_desc (W : C) :
    (id_pushoutProduct_iso g W).inv ≫ (𝟙 W) ◫ g = 𝟙 (Y ⊗ W) := by
  apply (Iso.inv_comp_eq_id (id_pushoutProduct_iso g W)).2 (by aesop)

@[simp]
noncomputable
def rightFunctor_map_left {X Y : C} (h : X ⟶ Y) (f g : Arrow C) (sq : f ⟶ g) :
    (pt f.hom h) ⟶ (pt g.hom h) := by
  apply pushout.desc (Y ◁ sq.left ≫ (inl g.hom h)) (X ◁ sq.right ≫ (inr g.hom h)) _
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  simp [pushout.condition, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, sq.w]

@[simp]
noncomputable
def rightFunctor_map {X Y : C} (h : X ⟶ Y) (f g : Arrow C) (sq : f ⟶ g):
    Arrow.mk (f.hom ◫ h) ⟶ Arrow.mk (g.hom ◫ h) where
  left := rightFunctor_map_left h f g sq
  right := Y ◁ sq.right
  w := by
    refine pushout.hom_ext ?_ ?_
    · simp [rightFunctor_map_left, ← MonoidalCategory.whiskerLeft_comp, sq.w]
    · simp [rightFunctor_map_left, ← whisker_exchange]

@[simp]
noncomputable
def rightFunctor {X Y : C} (h : X ⟶ Y) : Arrow C ⥤ Arrow C where
  obj f := f.hom ◫ h
  map sq := rightFunctor_map h _ _ sq
  map_id _ := by
    apply Arrow.hom_ext
    all_goals aesop
  map_comp _ _ := by
    apply Arrow.hom_ext
    all_goals aesop

@[simp]
noncomputable
def rightBifunctor_map_left {f g : Arrow C} (sq : f ⟶ g) (f' : Arrow C) :
    pt f'.hom f.hom ⟶ pt f'.hom g.hom := by
  dsimp [rightFunctor, rightFunctor_map, rightFunctor_map_left]
  refine pushout.desc ?_ ?_ ?_
  · exact (sq.right ▷ f'.left) ≫ (inl _ _)
  · exact (sq.left ▷ f'.right) ≫ (inr _ _)
  · have : sq.left ≫ g.hom = f.hom ≫ sq.right := sq.w
    dsimp only [inl, inr]
    rw [← comp_whiskerRight_assoc, ← this, comp_whiskerRight, whisker_exchange_assoc,
      pushout.inl, pushout.inr, Category.assoc, pushout.condition]

@[simp]
noncomputable
def rightBifunctor_map {f g : Arrow C} (sq : f ⟶ g) :
    rightFunctor f.hom ⟶ rightFunctor g.hom where
  app f' := {
    left := rightBifunctor_map_left sq f'
    right := sq.right ▷ f'.right
    w := by
      apply pushout.hom_ext
      · simp [whisker_exchange]
      · simp [← MonoidalCategory.comp_whiskerRight, Arrow.w] }
  naturality f' g' sq' := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      all_goals simp [← whisker_exchange_assoc]
    · exact whisker_exchange _ _

@[simp]
noncomputable
def rightBifunctor : Arrow C ⥤ Arrow C ⥤ Arrow C where
  obj h := rightFunctor h.hom
  map := rightBifunctor_map
  map_comp _ _ := by
    ext : 2
    apply Arrow.hom_ext
    · aesop
    · simp

end

section NatTrans

variable {D : Type u'} [Category.{v'} D]

variable {F G : D ⥤ C} (h : F ⟶ G)

variable {X Y : C} (g : X ⟶ Y)

@[simp]
def _root_.CategoryTheory.NatTrans.arrowFunctor : D ⥤ Arrow C where
  obj A := Arrow.mk (h.app A)
  map f := Arrow.homMk' _ _ (h.naturality f)

@[simp]
def _root_.CategoryTheory.NatTrans.arrowFunctor_NatTrans {G' : D ⥤ C} (h' : G ⟶ G') :
    NatTrans.arrowFunctor h ⟶ NatTrans.arrowFunctor (h ≫ h') where
  app X := Arrow.homMk' (𝟙 _) (h'.app X)

@[simp]
noncomputable
def natTransLeftFunctor : D ⥤ C := (NatTrans.arrowFunctor h) ⋙ rightFunctor g ⋙ Arrow.leftFunc
--  pt (h.app A) g ⟶ pt (h.app B) g

noncomputable
def natTransLeftFunctor_comp {G' : D ⥤ C} (h' : G ⟶ G') :
    (natTransLeftFunctor h g) ⟶ (natTransLeftFunctor (h ≫ h') g) :=
  whiskerRight (NatTrans.arrowFunctor_NatTrans h h') _

noncomputable
def inlDescFunctor : (F ⋙ tensorLeft Y) ⟶ (natTransLeftFunctor h g) where
  app A := inl (h.app A) g

noncomputable
def inrDescFunctor : (G ⋙ tensorLeft X) ⟶ (natTransLeftFunctor h g) where
  app A := inr (h.app A) g

/-- very slow :( -/
noncomputable
def descFunctor : (natTransLeftFunctor h g) ⟶ (G ⋙ tensorLeft Y) where
  app A := (h.app A) ◫ g
  naturality _ _ f := by
    apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · simp [whisker_exchange]

end NatTrans

section Composition

variable {A B B' X Y : C} (f : A ⟶ B) (f' : B ⟶ B') (g : X ⟶ Y)

@[simp]
noncomputable
def desc_comp : pt f g ⟶ pt (f ≫ f') g :=
  desc f g _ _
    (by rw [pushout.condition, MonoidalCategory.whiskerLeft_comp_assoc])

@[simp]
noncomputable
def comp_desc : pt (f ≫ f') g ⟶ pt f' g :=
  desc (f ≫ f') g _ _
  (by rw [MonoidalCategory.whiskerLeft_comp_assoc, ← pushout.condition, ← whisker_exchange_assoc])

-- pt (f ≫ f') g ⟶ pt f' g ⟶ pt (f ≫ f') g
lemma desc_comp_desc_eq :
    (desc_comp f f' g) ≫ (comp_desc f f' g) = (f ◫ g) ≫ (inl f' g) := by
  apply pushout.hom_ext
  · simp
  · simp [pushout.condition]

noncomputable
def compPushoutCocone := Limits.PushoutCocone.mk (comp_desc f f' g) (inl f' g) (desc_comp_desc_eq f f' g)

noncomputable
def compPushoutCoconeIsColimit : Limits.IsColimit (compPushoutCocone f f' g) := by
  refine Limits.PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_
  · intro s
    refine (desc f' g) s.inr (inr (f ≫ f') g ≫ s.inl) ?_
    · have := ((inr f g) ≫= s.condition).symm
      dsimp only [desc_comp] at this
      rw [pushout.inr_desc_assoc] at this
      rw [this, pushout.inr_desc_assoc, Category.assoc]
  · intro s
    apply pushout.hom_ext
    · have := ((inl f g) ≫= s.condition).symm
      dsimp only [desc_comp, comp_desc] at this ⊢
      rw [pushout.inl_desc_assoc] at this
      rw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, this, pushout.inl_desc_assoc]
    · dsimp only [comp_desc]
      rw [pushout.inr_desc_assoc, pushout.inr_desc]
  · intro s
    exact pushout.inl_desc _ _ _
  · intro s m h1 h2
    apply pushout.hom_ext
    · rw [h2, pushout.inl_desc]
    · have := (inr (f ≫ f') g) ≫= h1
      dsimp only [comp_desc] at this
      rw [pushout.inr_desc_assoc] at this
      rw [pushout.inr_desc, this]

def compPushout : CategoryTheory.IsPushout (desc_comp f f' g) (f ◫ g) (comp_desc f f' g) (inl f' g) :=
  IsPushout.of_isColimit (compPushoutCoconeIsColimit f f' g)

@[simp]
lemma pushoutProductCompEq : (comp_desc f f' g) ≫ (f' ◫ g) = (f ≫ f') ◫ g :=
  pushout.hom_ext (by aesop) (by aesop)

end Composition

end CategoryTheory.PushoutProduct

namespace SSet

open Limits Simplicial PushoutProduct

inductive bdryHornPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (m : ℕ) : bdryHornPushout (∂Δ[m].ι ◫ Λ[2, 1].ι)

/-- the class of pushout products of `∂Δ[m] ↪ Δ[m]` with `Λ[2, 1] ↪ Δ[2]`. -/
def bdryHornPushouts : MorphismProperty SSet := fun _ _ p ↦ bdryHornPushout p

end SSet
