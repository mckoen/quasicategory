import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

namespace MonoidalCategory

variable [BraidedCategory C]

@[simps!]
def tensorLeftIsoTensorRight (X : C) :
    tensorLeft X ≅ tensorRight X :=
  NatIso.ofComponents (fun _ ↦ β_ _ _)

end MonoidalCategory

open MonoidalCategory

namespace MonoidalClosed

instance (X : C) [Closed X] : (tensorLeft X).IsLeftAdjoint :=
  (ihom.adjunction X).isLeftAdjoint

instance (X : C) [Closed X] : (ihom X).IsRightAdjoint :=
  (ihom.adjunction X).isRightAdjoint

instance (X : C) [Closed X] [BraidedCategory C]: (tensorRight X).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (tensorLeftIsoTensorRight X)

instance (X : C) [MonoidalClosed C] : (tensorLeft X).IsLeftAdjoint :=
  inferInstance

variable {A B X Y : C} [Closed A] [Closed B]

@[reassoc]
lemma whiskerRight_comp_uncurry (f : A ⟶ B) (g : X ⟶ (ihom B).obj Y) :
    f ▷ X ≫ uncurry g = uncurry (g ≫ (pre f).app Y) := by
  rw [uncurry_natural_left, uncurry_pre, whisker_exchange_assoc]
  rfl

@[reassoc]
lemma curry_whiskerRight_comp (f : A ⟶ B) (g : B ⊗ X ⟶ Y) :
    curry (f ▷ X ≫ g) = curry g ≫ (pre f).app Y := by
  apply uncurry_injective
  rw [uncurry_curry, ← whiskerRight_comp_uncurry, uncurry_curry]

end MonoidalClosed

end CategoryTheory
