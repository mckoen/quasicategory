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

variable {X Y A B : SSet} {s : X ⟶ A} (g : X ⟶ Y) (f : A ⟶ B) {t : Y ⟶ B}
  (h : CommSq s g f t)

/-- given a CommSq, we want a CommSq with pushout products -/
noncomputable
def pushoutDescOfCommSq : (pushoutProduct_IsPushout g (hornInclusion 2 1)).cocone.pt ⟶
    (pushoutProduct_IsPushout f (hornInclusion 2 1)).cocone.pt :=
  IsPushout.desc (pushoutProduct_IsPushout g (hornInclusion 2 1))
    ((Δ[2] ◁ s) ≫ (pushoutProduct_IsPushout f (hornInclusion 2 1)).cocone.inl)
    ((Λ[2, 1] ◁ t) ≫ (pushoutProduct_IsPushout f (hornInclusion 2 1)).cocone.inr)
    (by
     change Λ[2, 1] ◁ s ≫ hornInclusion 2 1 ▷ A ≫ pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f) = (Λ[2, 1] ◁ (g ≫ t)) ≫ _
     rw [Λ[2, 1] ◁ s ≫= (pushoutProduct_IsPushout f (hornInclusion 2 1)).toCommSq.w, ← h.w]
     rfl )

/-- using the above maps between pushout products, we get a new CommSq. -/
lemma pushoutCommSq_w : (pushoutDescOfCommSq g f h) ≫ pushoutProduct f (hornInclusion 2 1) =
    pushoutProduct g (hornInclusion 2 1) ≫ (Δ[2] ◁ t) := by
  apply Limits.pushout.hom_ext
  · simp [pushoutProduct, pushoutDescOfCommSq, IsPushout.inl_desc]
    rw [← MonoidalCategory.whiskerLeft_comp, h.w, MonoidalCategory.whiskerLeft_comp]
  · simp [pushoutProduct, pushoutDescOfCommSq, IsPushout.inr_desc]
    rw [@whisker_exchange]

variable (h' : IsPushout s g f t)

/-
noncomputable
def changeSpan (C : Cocone (span (pushoutDescOfCommSq g f h'.toCommSq) (pushoutProduct g (hornInclusion 2 1)))) :
    Cocone (span (Δ[2] ◁ s) (Δ[2] ◁ g)) where
  pt := C.pt
  ι := {
    app := fun j ↦ by
      cases j
      · exact (pushout.inl (hornInclusion 2 1 ▷ X) (Λ[2, 1] ◁ g)) ≫ C.ι.app WalkingSpan.zero
      rename_i j; cases j
      · exact (pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f)) ≫ C.ι.app WalkingSpan.left
      · exact C.ι.app WalkingSpan.right
    naturality := by
      intro j j' p
      cases j; cases j'; all_goals cases p
      · rfl
      · rename_i j'; cases j'
        · simp only [span_zero, Fin.isValue, Functor.const_obj_obj, span_left, span_map_fst,
            PushoutCocone.ι_app_left, PushoutCocone.condition_zero, Functor.const_obj_map,
            Category.comp_id]
          rw [pushoutDescOfCommSq, IsPushout.inl_desc]
          --suffices  Δ[2] ◁ s ≫ pushout.inl (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ f) =
          --    pushout.inl (hornInclusion 2 1 ▷ X) (Λ[2, 1] ◁ g) ≫ pushoutDescOfCommSq g f h'.toCommSq by {
          --  rw [← Category.assoc, this]; rfl}
        · simp only [span_zero, Fin.isValue, Functor.const_obj_obj, span_right, span_map_snd,
          PushoutCocone.ι_app_right, PushoutCocone.condition_zero, PushoutCocone.ι_app_left,
          Functor.const_obj_map, Category.comp_id]
          sorry
      · rename_i j; cases j; all_goals rfl
  }
-/

noncomputable
def pushoutCommSq_cocone : PushoutCocone (pushoutDescOfCommSq g f h'.toCommSq) (pushoutProduct g (hornInclusion 2 1)) :=
    .mk _ _ (pushoutCommSq_w g f h'.toCommSq)

def pushoutCommSq_IsColimit'' :
    Limits.IsColimit (CommSq.mk (pushoutCommSq_w g f h'.toCommSq)).cocone where
  desc := by
    intro C
    --have := h'.isColimit.desc
    sorry

def pushoutCommSq_IsColimit' :
    Limits.IsColimit (pushoutCommSq_cocone g f h') where
  desc := by
    intro C
    --have := h'.isColimit.desc
    sorry

def pushoutCommSq_IsPushout :
    IsPushout (pushoutDescOfCommSq g f h) (pushoutProduct g (hornInclusion 2 1))
      (pushoutProduct f (hornInclusion 2 1)) ((Δ[2] ◁ t)) where
  w := pushoutCommSq_w g f h
  isColimit' := ⟨pushoutCommSq_IsColimit' g f h⟩

end SSet
