
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

open CategoryTheory Limits IsTerminal

open Simplicial

def SimplexCategory.isTerminalZero : IsTerminal ⦋0⦌ := by
  refine ofUniqueHom (fun _ ↦ const _ ⦋0⦌ 0) ?_
  · apply eq_const_to_zero

namespace SSet

def isTerminalZero : IsTerminal (Δ[0] : SSet.{u}) where
  lift S := { app := fun X _ => ULift.up <| SimplexCategory.isTerminalZero.from _ }
  uniq := by intros ; ext ; apply ULift.ext ; apply SimplexCategory.isTerminalZero.hom_ext

abbrev proj (S : SSet) : S ⟶ Δ[0] := isTerminalZero.from S

def empty : SSet where
  obj _ := Empty
  map _ := Empty.elim

def emptyIsInitial : IsInitial empty :=
  letI : ∀ (X : SSet), Unique (empty ⟶ X) := fun X => {
    default := {
      app := fun _ ↦ Empty.elim
      naturality := fun _ _ _ => by
        simp only [empty]
        aesop }
    uniq := fun f => by
      ext _ e
      simp only [empty] at e
      aesop }
  IsInitial.ofUnique _

end SSet
