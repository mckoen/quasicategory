import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Quasicategory.KInjective.WellOrderContinuous
import Quasicategory.KInjective.Lifting

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- `f : X ⟶ Y` is a retract of `g : Z ⟶ W` if there are morphisms
  `i : f ⟶ g` and `r : g ⟶ f` in the arrow category of `C` such that `i ≫ r = 𝟙 f`. -/
class IsRetract {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) where
  i : Arrow.mk f ⟶ Arrow.mk g
  r : Arrow.mk g ⟶ Arrow.mk f
  retract : i ≫ r = 𝟙 Arrow.mk f

namespace MorphismProperty

def StableUnderRetracts (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z W : C⦄ ⦃f : X ⟶ Y⦄ ⦃g : Z ⟶ W⦄ (_ : IsRetract f g)
    (_ : P g), P f

instance monomorphisms.StableUnderRetracts : StableUnderRetracts (monomorphisms C) := by
  intro X Y Z W f g H p
  refine ⟨fun {A} α β ω ↦ ?_⟩
  have := H.i.w
  dsimp at this
  apply_fun (fun f ↦ f ≫ H.i.right) at ω
  rw [Category.assoc, Category.assoc, ← this, ← Category.assoc, ← Category.assoc] at ω
  have ω' := p.right_cancellation (α ≫ H.i.left) (β ≫ H.i.left) ω
  apply_fun (fun f ↦ f ≫ H.r.left) at ω'
  simp only [Category.assoc] at ω'
  have := Arrow.hom.congr_left H.retract
  aesop

/- llp wrt a class of morphisms -/
def llp (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty f g

/- rlp wrt a class of morphisms -/
def rlp (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ ⦃g : X ⟶ Y⦄ (_ : T g), HasLiftingProperty g f

inductive Morphism {A B : C} (p : A ⟶ B) : {X Y : C} → (X ⟶ Y) → Prop
  | mk : (Morphism p) p

/-- the class of a single morphism `p`. -/
def MorphismClass {X Y : C} (p : X ⟶ Y) : MorphismProperty C := fun _ _ i ↦ (Morphism p) i

/-- a morphism `p` has rlp wrt a class `T` of morphisms iff every morphism in `T` has llp wrt `p`. -/
lemma class_rlp_iff_llp_morphism (T : MorphismProperty C) {X Y : C} (p : X ⟶ Y) : T.rlp p ↔
    ∀ {A B} (i : A ⟶ B) (_ : T i), (MorphismClass p).llp i := by
  refine ⟨fun hp _ _ _ hi _ _ _ h ↦ by induction h; exact hp hi, fun h _ _ i hi ↦ h i hi .mk⟩

/-- a morphism `p` has llp wrt a class `T` of morphisms iff every morphism in `T` has rlp wrt `p`. -/
lemma class_llp_iff_rlp_morphism (T : MorphismProperty C) {X Y : C} (p : X ⟶ Y) : T.llp p ↔
    ∀ {A B} (i : A ⟶ B) (_ : T i), (MorphismClass p).rlp i := by
  refine ⟨fun hp _ _ _ hi _ _ _ h ↦ by induction h; exact hp hi, fun h _ _ i hi ↦ h i hi .mk⟩

-- llp is closed under retract
instance llp_retract {T : MorphismProperty C} : StableUnderRetracts T.llp := by
  intro C D C' D' f f' H L
  intro X Y g h
  refine ⟨?_⟩
  intro u v sq
  have := sq.w
  have : (H.r.left ≫ u) ≫ g = f' ≫ (H.r.right ≫ v) := by simp [sq.w]
  obtain ⟨lift⟩ := ((L h).sq_hasLift (CommSq.mk this)).exists_lift
  refine ⟨H.i.right ≫ lift.l, ?_, ?_⟩
  · rw [← Category.assoc]
    have := H.i.w
    dsimp at this
    rw [← this, Category.assoc, lift.fac_left, ← Category.assoc]
    have := Arrow.hom.congr_left H.retract
    aesop
  · rw [Category.assoc, lift.fac_right, ← Category.assoc]
    have := Arrow.hom.congr_right H.retract
    aesop

-- rlp is closed under retracts
instance rlp_retract {T : MorphismProperty C} : StableUnderRetracts T.rlp := by
  intro C D C' D' f f' H L
  intro X Y g h
  refine ⟨?_⟩
  intro u v sq
  have : (u ≫ H.i.left) ≫ f' = g ≫ (v ≫ H.i.right) := by
    rw [← Category.assoc, ← sq.w]
    simp
  obtain lift := ((L h).sq_hasLift (CommSq.mk this)).exists_lift.some
  refine ⟨lift.l ≫ H.r.left, ?_, ?_⟩
  · rw [← Category.assoc, lift.fac_left, Category.assoc]
    have := Arrow.hom.congr_left H.retract
    aesop
  · rw [Category.assoc]
    have := H.r.w
    dsimp at this
    rw [this, ← Category.assoc, lift.fac_right, Category.assoc]
    have := Arrow.hom.congr_right H.retract
    aesop

-- llp is closed under pushout
open Limits.PushoutCocone in
instance llp_pushout {T : MorphismProperty C} : StableUnderCobaseChange T.llp := by
  intro A B A' B' f s f' t P L
  intro X Y g hg
  refine ⟨?_⟩
  intro u v sq
  have w : (s ≫ u) ≫ g = f ≫ (t ≫ v) := by
    rw [← Category.assoc, ← P.toCommSq.w, Category.assoc, Category.assoc, sq.w]
  obtain ⟨lift⟩ := ((L hg).sq_hasLift (CommSq.mk w)).exists_lift
  let lift' : B' ⟶ X := IsColimit.desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l : f' ≫ lift' = u := IsColimit.inl_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let l' : t ≫ lift' = lift.l := IsColimit.inr_desc P.isColimit u lift.l (by rw [lift.fac_left])
  let newCocone := mk (f' ≫ v) (t ≫ v) (by have := P.w; apply_fun (fun f ↦ f ≫ v) at this; aesop)
  refine ⟨lift', l,
    (P.isColimit.uniq newCocone (lift' ≫ g) ?_).trans (P.isColimit.uniq newCocone v ?_).symm⟩
  all_goals
    dsimp [newCocone]
    intro j
    cases j
    simp only [Limits.span_zero, condition_zero, IsPushout.cocone_inl, Category.assoc]
  · rw [← Category.assoc, ← Category.assoc, Category.assoc s f' lift', l, ← sq.w, Category.assoc]
  · rename_i k; cases k; all_goals dsimp
    · rw [← Category.assoc, l, sq.w]
    · rw [← Category.assoc, l', lift.fac_right]
  · rename_i k; cases k; all_goals dsimp

-- rlp is closed under pullback
open Limits.PullbackCone in
instance rlp_pullback {T : MorphismProperty C} : StableUnderBaseChange T.rlp := by
  intro B' A A' B t f s f' P L
  intro X Y g hg
  refine ⟨?_⟩
  intro u v sq
  have := P.toCommSq.w
  have w : (u ≫ s) ≫ f = g ≫ v ≫ t := by
    rw [Category.assoc, P.toCommSq.w, ← Category.assoc, ← Category.assoc, sq.w]
  obtain lift := ((L hg).sq_hasLift (CommSq.mk w)).exists_lift.some
  let lift' : Y ⟶ A' := IsLimit.lift P.isLimit lift.l v (by rw [lift.fac_right])
  let l : lift' ≫ f' = v := IsLimit.lift_snd P.isLimit lift.l v (by rw [lift.fac_right])
  let l' : lift' ≫ s = lift.l := IsLimit.lift_fst P.isLimit lift.l v (by rw [lift.fac_right])
  have comm : (u ≫ s) ≫ f = (g ≫ v) ≫ t := by aesop
  let newCone := mk _ _ comm
  refine ⟨lift', (P.isLimit.uniq newCone (g ≫ lift') ?_).trans (P.isLimit.uniq newCone u ?_).symm, l⟩
  all_goals dsimp [newCone]; intro j; cases j; simp only [Limits.cospan_one, condition_one, IsPullback.cone_fst, Category.assoc]
  · rw [← Category.assoc u, ← lift.fac_left, ← l', Category.assoc, Category.assoc]
  · rename_i k; cases k; all_goals dsimp
    · rw [← lift.fac_left, ← l', Category.assoc]
    · rw [← sq.w, Category.assoc, l, sq.w]
  · rename_i k; cases k; all_goals dsimp
    exact sq.w

-- rlp is closed under composition
lemma rlp_comp (T : MorphismProperty C) {X Y Z : C}
    (p : X ⟶ Y) (hp : T.rlp p) (q : Y ⟶ Z) (hq : T.rlp q) : T.rlp (p ≫ q) := by
  intro A B i hi
  constructor
  intro f g sq
  have q_sq_comm : (f ≫ p) ≫ q = i ≫ g := by
    rw [Category.assoc, sq.w]
  have q_sq := CommSq.mk q_sq_comm
  obtain ⟨q_lift, q_fac_left, q_fac_right⟩ := ((hq hi).sq_hasLift q_sq).exists_lift.some
  have p_sq := CommSq.mk q_fac_left.symm
  obtain ⟨p_lift, p_fac_left, p_fac_right⟩ := ((hp hi).sq_hasLift p_sq).exists_lift.some
  refine ⟨p_lift, p_fac_left, ?_⟩
  rw [← Category.assoc, p_fac_right, q_fac_right]

instance llp_transfinite_comp {T : MorphismProperty C} :
    T.llp.IsStableUnderTransfiniteComposition := T.llpWith_comp

class WeaklySaturated (P : MorphismProperty C) : Prop :=
  StableUnderCobaseChange : P.StableUnderCobaseChange
  StableUnderRetracts : P.StableUnderRetracts
  IsStableUnderTransfiniteComposition : IsStableUnderTransfiniteComposition.{w} P

instance llp_weakly_saturated (T : MorphismProperty C) : WeaklySaturated T.llp :=
  ⟨llp_pushout, llp_retract, llp_transfinite_comp⟩

/-- weakly saturated classes contain all isomorphisms. -/
lemma WeaklySaturated_contains_iso (T : MorphismProperty C) [hT: WeaklySaturated T] (p : X ⟶ Y) :
    (isomorphisms C) p → T p := fun hp ↦
  letI : IsIso p := hp
  hT.StableUnderCobaseChange (IsPushout.of_vert_isIso ⟨rfl⟩) (hT.IsStableUnderTransfiniteComposition.id_mem X)

-- inductive type defining the weakly saturated class generated by a morphism property
inductive WeaklySaturatedOf (T : MorphismProperty C) : {X Y : C} → (X ⟶ Y) → Prop
  | of ⦃X Y : C⦄ (f : X ⟶ Y) (h : T f) : WeaklySaturatedOf T f
  | pushout ⦃X Y Z W : C⦄ ⦃f : X ⟶ Y⦄ ⦃g : X ⟶ Z⦄ ⦃inl : Z ⟶ W⦄ ⦃inr : Y ⟶ W⦄ (_ : IsPushout g f inl inr) : WeaklySaturatedOf T f → WeaklySaturatedOf T inl
  | retract ⦃X Y Z W : C⦄ ⦃f : X ⟶ Y⦄ ⦃g : Z ⟶ W⦄ (_ : IsRetract f g) : WeaklySaturatedOf T g → WeaklySaturatedOf T f
  | id_mem (X : C) : WeaklySaturatedOf T (𝟙 X)
  | comp_mem {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) : WeaklySaturatedOf T f → WeaklySaturatedOf T g → WeaklySaturatedOf T (f ≫ g)
  | transfinite (β : Type w) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β]
    (F : β ⥤ C) (hF : F.WellOrderContinuous) (c : Limits.Cocone F) (hc : Limits.IsColimit c) :
      (∀ (a : β) (_ : a < wellOrderSucc a), T.WeaklySaturatedOf (F.map (homOfLE (self_le_wellOrderSucc a)))) → T.WeaklySaturatedOf (c.ι.app ⊥)

/-- the weakly saturated class generated by a morphism property. -/
def WeaklySaturatedClassOf (T : MorphismProperty C) : MorphismProperty C := fun _ _ f ↦ WeaklySaturatedOf.{w} T f

-- do galois connection, galois insertion

instance (T : MorphismProperty C) : WeaklySaturated.{w} (WeaklySaturatedClassOf.{w} T) where
  StableUnderCobaseChange := .pushout
  StableUnderRetracts := .retract
  IsStableUnderTransfiniteComposition := {
    id_mem := .id_mem
    comp_mem := .comp_mem
    isStableUnderTransfiniteCompositionOfShape := fun β ↦ {
      condition := fun F hF h c hc ↦ .transfinite β F hF c hc h} }

lemma le_WeaklySaturatedClassOf (T : MorphismProperty C) : T ≤ WeaklySaturatedClassOf T := .of

/-- if S is any other wsc containing T, then it contains the class generated by T. -/
lemma minimalWeaklySaturated (S T : MorphismProperty C) (h : T ≤ S) : WeaklySaturated.{w} S → (WeaklySaturatedClassOf.{w} T) ≤ S := by
  intro hS X Y f hf
  induction hf with
  | of f hf => exact h _ hf
  | pushout h _ hf => exact hS.StableUnderCobaseChange h hf
  | retract h _ hf => exact hS.StableUnderRetracts h hf
  | id_mem => exact hS.IsStableUnderTransfiniteComposition.id_mem _
  | comp_mem f g _ _ hf hg => exact hS.IsStableUnderTransfiniteComposition.comp_mem f g hf hg
  | transfinite β F hF c hc _ h' =>
    exact (hS.IsStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape β).condition F h' c hc

end MorphismProperty

end CategoryTheory
