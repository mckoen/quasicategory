import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

namespace SSet

open CategoryTheory MonoidalCategory Limits Simplicial

def pushoutProduct_IsPushout {A B X Y : SSet} (f : A ⟶ B) (g : X ⟶ Y) :=
  IsPushout.of_hasPushout (g ▷ A) (X ◁ f)

/-- The pushout product of `f` and `g`. -/
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

end SSet
