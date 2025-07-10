
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

open CategoryTheory Limits

open Simplicial

def SimplexCategory.isTerminalZero : IsTerminal ⦋0⦌ := by
  refine IsTerminal.ofUniqueHom (fun _ ↦ const _ ⦋0⦌ 0) ?_
  · apply eq_const_to_zero

namespace SSet

def isTerminalZero : IsTerminal (Δ[0] : SSet.{u}) where
  lift S := { app := fun X _ => ULift.up <| SimplexCategory.isTerminalZero.from _ }
  uniq := by intros ; ext ; apply ULift.ext ; apply SimplexCategory.isTerminalZero.hom_ext

abbrev proj (S : SSet) : S ⟶ Δ[0] := isTerminalZero.from S

def SimplexCategory.isInitialEmpty : IsInitial Empty := by
  apply IsInitial.ofUniqueHom (fun _ ↦ Empty.elim) (fun _ _ ↦ by aesop)

def empty : SSet.{u} where
  obj _ := PEmpty.{u + 1}
  map _ := PEmpty.elim

def isInitialEmpty : IsInitial empty.{u} :=
  letI : ∀ (X : SSet), Unique (empty ⟶ X) := fun X => {
    default := {
      app := fun _ ↦ PEmpty.elim
      naturality := fun _ _ _ => by
        simp only [empty]
        aesop }
    uniq := fun f => by
      ext _ e
      simp only [empty] at e
      aesop }
  IsInitial.ofUnique _

end SSet
