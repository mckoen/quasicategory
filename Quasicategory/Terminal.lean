
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

open CategoryTheory Limits

open Simplicial

def SimplexCategory.isTerminalZero : IsTerminal ([0] : SimplexCategory) := by
  refine IsTerminal.ofUniqueHom (fun _ ↦ SimplexCategory.const _ [0] 0) ?_
  · apply SimplexCategory.eq_const_to_zero

def SSet.isTerminal : IsTerminal (Δ[0] : SSet.{u}) where
  lift S := { app := fun X _ => ULift.up <| SimplexCategory.isTerminalZero.from _ }
  uniq := by intros ; ext ; apply ULift.ext ; apply SimplexCategory.isTerminalZero.hom_ext

abbrev SSet.proj (S : SSet) : S ⟶ Δ[0] := Limits.IsTerminal.from isTerminal S

namespace SSet

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
