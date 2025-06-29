import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.SetTheory.Cardinal.Order

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (T : MorphismProperty C)

inductive Morphism {A B : C} (p : A ⟶ B) : {X Y : C} → (X ⟶ Y) → Prop
  | mk : (Morphism p) p

/-- the class of a single morphism `p`. -/
def isMorphism {X Y : C} (p : X ⟶ Y) : MorphismProperty C := fun _ _ i ↦ (Morphism p) i

/-- a morphism `p` has rlp wrt a class `T` of morphisms iff every morphism in `T` has llp wrt `p`. -/
lemma morphism_rlp_iff {X Y : C} (p : X ⟶ Y) : T.rlp p ↔ T ≤ (isMorphism p).llp :=
  ⟨fun hp _ _ _ hi _ _ _ ⟨⟩ ↦ hp _ hi, fun h _ _ i hi ↦ h i hi _ .mk⟩

lemma morphism_llp_iff {X Y : C} (p : X ⟶ Y) : T.llp p ↔ T ≤ (isMorphism p).rlp :=
  ⟨fun hp _ _ _ hi _ _ _ ⟨⟩ ↦ hp _ hi, fun h _ _ i hi ↦ h i hi _ .mk⟩

class WeaklySaturated : Prop where
  IsStableUnderCobaseChange : T.IsStableUnderCobaseChange
  IsStableUnderRetracts : T.IsStableUnderRetracts
  IsStableUnderCoproducts : IsStableUnderCoproducts.{w} T
  IsStableUnderTransfiniteComposition : IsStableUnderTransfiniteComposition.{w} T

instance [h : WeaklySaturated T] : T.IsStableUnderCobaseChange :=
  h.IsStableUnderCobaseChange

instance [h : WeaklySaturated T] : T.IsStableUnderRetracts :=
  h.IsStableUnderRetracts

instance [h : WeaklySaturated.{w} T] : IsStableUnderTransfiniteComposition.{w} T :=
  h.IsStableUnderTransfiniteComposition

instance [h : WeaklySaturated.{w} T] : IsStableUnderCoproducts.{w} T :=
  h.IsStableUnderCoproducts

instance llp_isWeaklySaturated : WeaklySaturated T.llp :=
  ⟨T.llp_isStableUnderCobaseChange, T.llp_isStableUnderRetracts, ⟨T.llp_isStableUnderCoproductsOfShape⟩, ⟨T.isStableUnderTransfiniteCompositionOfShape_llp⟩⟩

/-- weakly saturated classes contain all isomorphisms. -/
lemma WeaklySaturated.isomorphisms_le [WeaklySaturated T] :
    isomorphisms C ≤ T := fun _ _ p hp ↦
  letI : IsIso p := hp
  WeaklySaturated.IsStableUnderCobaseChange.of_isPushout (IsPushout.of_vert_isIso ⟨rfl⟩) (ContainsIdentities.id_mem _)

open Limits in
/-- inductive type defining the weakly saturated class generated by a morphism property -/
inductive WeaklySaturatedClass (T : MorphismProperty C) : {X Y : C} → (X ⟶ Y) → Prop
  | of ⦃X Y : C⦄ (f : X ⟶ Y) (h : T f) : WeaklySaturatedClass T f
  | pushout ⦃X Y Z W : C⦄ ⦃f : X ⟶ Y⦄ ⦃g : X ⟶ Z⦄ ⦃inl : Z ⟶ W⦄ ⦃inr : Y ⟶ W⦄ (_ : IsPushout g f inl inr) : WeaklySaturatedClass T f → WeaklySaturatedClass T inl
  | retract ⦃X Y Z W : C⦄ ⦃f : X ⟶ Y⦄ ⦃g : Z ⟶ W⦄ (_ : RetractArrow f g) : WeaklySaturatedClass T g → WeaklySaturatedClass T f
  | coproduct (J : Type w) (X₁ X₂ : (Discrete J) ⥤ C) (c₁ : Cocone X₁) (c₂ : Cocone X₂) (h₁ : IsColimit c₁) (_ : IsColimit c₂)
      (f : X₁ ⟶ X₂) : (_ : ∀ (j : (Discrete J)), (WeaklySaturatedClass T) (f.app j)) → WeaklySaturatedClass T (h₁.desc (Cocone.mk _ (f ≫ c₂.ι)))
  | transfinite (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
      {X Y : C} (f : X ⟶ Y) (hf : CategoryTheory.TransfiniteCompositionOfShape J f) :
        (∀ (j : J), (hj : ¬IsMax j) → WeaklySaturatedClass T (hf.F.map (homOfLE (Order.le_succ j)))) → WeaklySaturatedClass T f

/-- the weakly saturated class generated by a morphism property. -/
def saturation : MorphismProperty C := fun _ _ f ↦ WeaklySaturatedClass.{w} T f

-- do galois connection, galois insertion

instance saturation_isWeaklySaturated (T : MorphismProperty C) : WeaklySaturated.{w} (saturation.{w} T) where
  IsStableUnderCobaseChange := ⟨fun h hf ↦ .pushout h hf⟩
  IsStableUnderRetracts := ⟨fun h hf ↦ .retract h hf⟩
  IsStableUnderCoproducts := {
    isStableUnderCoproductsOfShape := fun J _ _ _ _ _ h₂ f hf ↦
      .coproduct J _ _ _ _ _ h₂ f hf }
  IsStableUnderTransfiniteComposition := {
    isStableUnderTransfiniteCompositionOfShape := fun J _ _ _ _ ↦
      ⟨fun _ _ f hf ↦ .transfinite J f _ hf.some.map_mem⟩ }

lemma le_saturation : T ≤ T.saturation := .of

lemma WeaklySaturated.le_iff (S : MorphismProperty C) [WeaklySaturated.{w} S] : T ≤ S ↔ (saturation.{w} T) ≤ S := by
  constructor
  · intro h _ _ f hf
    induction hf with
    | of f hf => exact h _ hf
    | pushout h _ hf => exact WeaklySaturated.IsStableUnderCobaseChange.of_isPushout h hf
    | retract h _ hf => exact WeaklySaturated.IsStableUnderRetracts.of_retract h hf
    | coproduct J X₁ X₂ c₁ c₂ h₁ h₂ f hf hs =>
      exact (WeaklySaturated.IsStableUnderCoproducts.isStableUnderCoproductsOfShape J).colimitsOfShape_le _ ⟨X₁, X₂, c₁, c₂, h₁, h₂, f, hs⟩
    | transfinite J f hF h' h'' =>
      exact (WeaklySaturated.IsStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape J).le _ ⟨hF, h''⟩
  · exact T.le_saturation.trans

end MorphismProperty

end CategoryTheory
