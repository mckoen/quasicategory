import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.Closed.Enrichment
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Quasicategory.Main

namespace SSet

open CategoryTheory Simplicial MonoidalCategory MonoidalClosed

def QCat := FullSubcategory Quasicategory

instance : Category QCat := FullSubcategory.category Quasicategory

open Quasicategory ChosenFiniteProducts in
instance : MonoidalPredicate Quasicategory where
  prop_id := { hornFilling' _ _ _ _ _ := ⟨toUnit _, by aesop_cat⟩ }
  prop_tensor _ _ := {
    hornFilling' _ _ σ₀ h0 hn := by
      obtain ⟨σ_X, _⟩ := hornFilling h0 hn (σ₀ ≫ fst ..)
      obtain ⟨σ_Y, _⟩ := hornFilling h0 hn (σ₀ ≫ snd ..)
      use ChosenFiniteProducts.lift σ_X σ_Y
      aesop_cat }

instance ihom_isQuasicategory {X Y : SSet} [Quasicategory Y] :
    Quasicategory ((ihom X).obj Y) :=
  (horn_tkf_iff_quasicat _).2 (aux X Y)

instance : ClosedPredicate Quasicategory where
  prop_ihom _ _ := ihom_isQuasicategory

noncomputable section

instance : MonoidalCategory QCat := fullMonoidalSubcategory Quasicategory

instance : MonoidalClosed QCat := fullMonoidalClosedSubcategory Quasicategory

instance : EnrichedOrdinaryCategory QCat QCat := enrichedOrdinaryCategorySelf QCat

instance : EnrichedCategory QCat QCat := EnrichedOrdinaryCategory.toEnrichedCategory

end
