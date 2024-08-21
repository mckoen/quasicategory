import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.LiftingProperties.Basic

namespace CategoryTheory

variable {C : Type*} [Category C] (W : MorphismProperty C)

open Category

namespace MorphismProperty

structure IsStableUnderRetract : Prop where
  condition (f g : Arrow C) (i : f ⟶ g) (p : g ⟶ f) (hip : i ≫ p = 𝟙 _)
    (hg : W g.hom) : W f.hom

end MorphismProperty

section

variable (f g : Arrow C) (i : f ⟶ g) (p : g ⟶ f) (hip : i ≫ p = 𝟙 _)

lemma hasLeftLiftingProperty_of_retract
    (i : f ⟶ g)  (p : g ⟶ f) (hip : i ≫ p = 𝟙 _) {X Y : C} (π : X ⟶ Y)
    (hg : HasLiftingProperty g.hom π) : HasLiftingProperty f.hom π where
  sq_hasLift {t b} sq := by
    dsimp at t b
    have sq' : CommSq (p.left ≫ t) g.hom π (p.right ≫ b) :=
      ⟨by rw [assoc, sq.w, Arrow.w_assoc p]⟩
    exact ⟨⟨{
      l := i.right ≫ sq'.lift
      fac_left := by
        rw [← Arrow.w_assoc i, sq'.fac_left, ← Arrow.comp_left_assoc,
          hip, Arrow.id_left, id_comp]
      fac_right := by
        rw [assoc, sq'.fac_right, ← Arrow.comp_right_assoc,
        hip, Arrow.id_right, id_comp] }⟩⟩

lemma hasRightLiftingProperty_of_retract
    (i : f ⟶ g) (p : g ⟶ f) (hip : i ≫ p = 𝟙 _) {X Y : C} (ι : X ⟶ Y)
    (hg : HasLiftingProperty ι g.hom) : HasLiftingProperty ι f.hom where
  sq_hasLift {t b} sq := by
    dsimp at t b
    have sq' : CommSq (t ≫ i.left) ι g.hom (b ≫ i.right) :=
      ⟨by rw [assoc, Arrow.w i, sq.w_assoc]⟩
    exact ⟨⟨{
      l := sq'.lift ≫ p.left
      fac_left := by
        rw [sq'.fac_left_assoc, assoc, ← Arrow.comp_left, hip, Arrow.id_left, comp_id]
      fac_right := by
        rw [assoc, Arrow.w p, sq'.fac_right_assoc, assoc, ← Arrow.comp_right,
        hip, Arrow.id_right, comp_id] }⟩⟩

end

end CategoryTheory
