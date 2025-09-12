import Quasicategory._007F
import Quasicategory.Quasicategory
import Quasicategory.InternalHom
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

universe w

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory MonoidalClosed Limits PushoutProduct

variable {S : SSet} {m : ℕ}

noncomputable
def hornFromPullbackPower (S : SSet) : internalHom.PullbackObjObj Λ[2, 1].ι (isTerminalZero.from S) :=
  Functor.PullbackObjObj.ofHasPullback ..

noncomputable
def pullback_ihom_terminal_iso {S : SSet} :
    pullback ((ihom Λ[2, 1].toSSet).map (isTerminalZero.from S)) ((pre Λ[2, 1].ι).app Δ[0]) ≅
      (ihom Λ[2, 1].toSSet).obj S where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 _) ((isTerminalZeroPow isTerminalZero).from _) rfl

noncomputable
def hornFromPullbackPower_π_arrowIso :
    Arrow.mk (S.hornFromPullbackPower.π) ≅ Arrow.mk ((internalHom.map Λ[2, 1].ι.op).app S) := by
  dsimp [hornFromPullbackPower]
  refine Arrow.isoMk (Iso.refl _) pullback_ihom_terminal_iso ?_
  simp [pullback_ihom_terminal_iso, Functor.PullbackObjObj.π]

-- `0079`
open HasLiftingProperty ParametrizedAdjunction in
/-- `S` is a quasi-category iff `ihom(Δ[2], S) ⟶ ihom(Λ[2, 1], S)` is a trivial fibration. -/
instance quasicategory_iff_internalHom_horn_trivialFibration (S : SSet) :
    Quasicategory S ↔
      trivialFibration ((internalHom.map Λ[2, 1].ι.op).app S) := by
  rw [quasicategory_iff_from_innerAnodyne_rlp, morphism_rlp_iff,
    ← contains_innerAnodyne_iff_contains_pushout_maps, le_llp_iff_le_rlp, morphism_le_iff]
  constructor
  · intro h _ _ _ ⟨m⟩
    rw [← iff_of_arrow_iso_right _ hornFromPullbackPower_π_arrowIso,
      ← hasLiftingProperty_iff internalHomAdjunction₂ _ _]
    exact h _ ⟨m⟩
  · intro h _ _ _ ⟨m⟩
    rw [hasLiftingProperty_iff internalHomAdjunction₂,
      iff_of_arrow_iso_right _ hornFromPullbackPower_π_arrowIso]
    exact h _ ⟨m⟩

/-- `0071` (special case of `0070`) if `p : X ⟶ Y` is a trivial fibration, then `ihom(B, X) ⟶ ihom(B, Y)` is -/
instance trivialFibration_of_ihom_map_trivialFibration {X Y : SSet} (B : SSet) (p : X ⟶ Y) (hp: trivialFibration p) :
    trivialFibration ((ihom B).map p) := by
  intro _ _ i ⟨n⟩
  rw [trivialFibration_eq_rlp_monomorphisms] at hp
  have := hp _ ((tensorLeft_PreservesMonomorphisms B).preserves ∂Δ[n].ι)
  constructor
  intro f g sq
  exact (CommSq.left_adjoint_hasLift_iff sq (FunctorToTypes.adj B)).1
      (this.sq_hasLift (sq.left_adjoint (Closed.adj)))

open MonoidalClosed in
/-- if `D` is a quasi-category, then the restriction map
  `ihom(Δ[2], ihom(S, D)) ⟶ ihom(Λ[2, 1], ihom(S, D))` is a trivial fibration. -/
def aux (S D : SSet) [Quasicategory D] :
    trivialFibration ((internalHom.map Λ[2, 1].ι.op).app ((ihom S).obj D)) := by
  intro _ _ i ⟨n⟩
  have := (quasicategory_iff_internalHom_horn_trivialFibration D).1 (by infer_instance)
  have := (trivialFibration_of_ihom_map_trivialFibration S ((internalHom.map Λ[2, 1].ι.op).app D)) this _ (.mk n)
  dsimp at this
  have H : Arrow.mk ((ihom S).map ((pre Λ[2, 1].ι).app D)) ≅
      Arrow.mk ((internalHom.map Λ[2, 1].ι.op).app ((ihom S).obj D)) :=
    CategoryTheory.Comma.isoMk (ihom_ihom_symm_iso _ _ _) (ihom_ihom_symm_iso _ _ _)
  exact HasLiftingProperty.of_arrow_iso_right ∂Δ[n].ι H

section _00J8

variable {A B X Y : SSet} (f : A ⟶ B) {g : X ⟶ Y} [hf : Mono f]

/-- `T` is the class of all morphisms `i` such that `f □ i` is inner anodyne. -/
def T : MorphismProperty SSet := fun _ _ i ↦
  innerAnodyne (f □ i)

instance : IsStableUnderCobaseChange (T f) where
  of_isPushout h hg := by
    dsimp only [T]
    exact IsStableUnderCobaseChange.of_isPushout (leftFunctor_map_preserves_pushouts' f h) hg

instance : IsStableUnderRetracts (T f) where
  of_retract h hg := by
    dsimp only [T]
    exact IsStableUnderRetracts.of_retract (Retract.map h (leftFunctor f)) hg

set_option maxHeartbeats 400000 in
instance : IsStableUnderCoproducts.{w} (T f) where
  isStableUnderCoproductsOfShape J := by
    refine (isStableUnderColimitsOfShape_iff_colimitsOfShape_le _ (Discrete J)).mpr ?_
    intro X Y _ hf
    cases hf with
    | mk X₁ X₂ c₁ c₂ h₁ h₂ f' hf =>
    dsimp only [T]
    dsimp only [MorphismProperty.functorCategory, T] at hf
    apply (WeaklySaturated.IsStableUnderCoproducts.isStableUnderCoproductsOfShape J).colimitsOfShape_le
    let α := h₁.desc { pt := c₂.pt, ι := f' ≫ c₂.ι }
    let f'' := descFunctor f' f
    let c₁' := c₁' f c₂ h₁ f'
    let h₁' : Limits.IsColimit c₁' := c₁'_isColimit f c₂ h₁ h₂ f'
    let c₂' := (tensorLeft B).mapCocone c₂
    let h₂' : Limits.IsColimit c₂' := Limits.isColimitOfPreserves (tensorLeft B) h₂
    convert colimitsOfShape.mk (natTransLeftFunctor f' f) (X₂ ⋙ tensorLeft B) c₁' c₂' h₁' h₂' f'' hf
    convert h₁'.uniq _ _ _
    · rfl
    · rfl
    · intro j
      dsimp only [c₁', PushoutProduct.c₁', c₂', f'', descFunctor, tensorLeft, curriedTensor,
        Functor.mapCocone]
      simp only [Functor.PushoutObjObj.ι]
      aesop

open Limits in
instance : IsStableUnderTransfiniteComposition.{w} (T f) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    rw [isStableUnderTransfiniteCompositionOfShape_iff]
    intro X Y f' ⟨hf⟩
    apply innerAnodyne.transfiniteCompositions_le
    rw [transfiniteCompositions_iff]
    refine ⟨J, _, _, _, _, ⟨(leftFunctor_preserves_transfiniteComposition J f f' hf.1), ?_⟩⟩

    intro j hj
    dsimp only [leftFunctor_preserves_transfiniteComposition]
    exact IsStableUnderCobaseChange.of_isPushout (newPushoutIsPushout f hf.F (Cocone.mk _ hf.incl) j) (hf.map_mem j hj)

instance : WeaklySaturated.{w} (T f) where
  IsStableUnderCobaseChange := by infer_instance
  IsStableUnderRetracts := by infer_instance
  IsStableUnderCoproducts := by infer_instance
  IsStableUnderTransfiniteComposition := by infer_instance

inductive hornMonoPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (X Y : SSet) (i : X ⟶ Y) (hi : Mono i) : hornMonoPushout (Λ[2, 1].ι □ i)

def hornMonoPushouts : MorphismProperty SSet := fun _ _ p ↦ hornMonoPushout p

lemma saturation_hornMonoPushouts_eq : saturation.{w} hornMonoPushouts = innerAnodyne.{w} := by
  apply le_antisymm
  · rw [← WeaklySaturated.le_iff]
    intro _ _ _ ⟨X, Y, i, hi⟩
    exact hornMonoPushout_innerAnodyne _
  · rw [innerAnodyne_eq_T, ← WeaklySaturated.le_iff]
    intro _ _ _ ⟨m⟩
    exact .of _ (.mk _ _ _ (instMonoι _))

lemma innerAnodyne_le_T : innerAnodyne ≤ T f := by
  rw [← saturation_hornMonoPushouts_eq, ← WeaklySaturated.le_iff]
  intro _ _ _ ⟨X, Y, i, hi⟩
  dsimp only [T]
  have : Arrow.mk (f □ Λ[2, 1].ι □ i) ≅ Arrow.mk (Λ[2, 1].ι □ f □ i) := by
    sorry
  rw [innerAnodyne.arrow_mk_iso_iff this, ← saturation_hornMonoPushouts_eq]
  apply WeaklySaturatedClass.of
  refine .mk _ _ (f □ i) ?_
  sorry

lemma _00J8 (hg : innerAnodyne g) :
    innerAnodyne (f □ g) := innerAnodyne_le_T _ _ hg

end _00J8

open ParametrizedAdjunction in
lemma _01BT {X S A B : SSet} (p : X ⟶ S) (i : A ⟶ B)
    (hp : innerFibration p) [hi : Mono i] :
    innerFibration (Functor.PullbackObjObj.ofHasPullback internalHom i p).π := by
  rw [innerFibration_eq_rlp_innerAnodyne] at hp ⊢
  intro _ _ f hf
  rw [← hasLiftingProperty_iff internalHomAdjunction₂]
  exact hp _ (_00J8 i hf)

end SSet
