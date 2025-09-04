import Quasicategory._007F
import Quasicategory.Quasicategory
import Quasicategory.InternalHom
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

universe w

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory MonoidalClosed Limits PushoutProduct

variable {S : SSet} {m : ℕ}

noncomputable
def bdryHornPushoutProduct (m : ℕ) : (curriedTensor SSet).PushoutObjObj Λ[2, 1].ι ∂Δ[m].ι :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

noncomputable
def hornFromPullbackPower (S : SSet) : internalHom.PullbackObjObj Λ[2, 1].ι (isTerminalZero.from S) :=
  Functor.PullbackObjObj.ofHasPullback internalHom Λ[2, 1].ι (isTerminalZero.from S)

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

noncomputable
def bdryHornPushoutProduct_ι_eq :
    (bdryHornPushoutProduct m).ι = Λ[2, 1].ι □ ∂Δ[m].ι := by
  dsimp [bdryHornPushoutProduct, Functor.PushoutObjObj.ι]
/-

noncomputable
def PushoutObjObj_ι_eq {A B X Y : SSet} {f : A ⟶ B} {g : X ⟶ Y} :
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) f g).ι = g ◫ f := by
  dsimp [Functor.PushoutObjObj.ι]
  exact pushout.hom_ext (by aesop) (by aesop)
-/

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
    exact h _ (.mk m)
  · intro h _ _ _ ⟨m⟩
    rw [← bdryHornPushoutProduct_ι_eq, hasLiftingProperty_iff internalHomAdjunction₂ (bdryHornPushoutProduct m) (hornFromPullbackPower S),
      iff_of_arrow_iso_right _ hornFromPullbackPower_π_arrowIso]
    apply h _ (.mk m)

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

lemma _00J8 {A B X Y : SSet} (f : A ⟶ B) {g : X ⟶ Y} [hf : Mono f] (hg : innerAnodyne g) :
    innerAnodyne (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) f g).ι := by

  sorry

open ParametrizedAdjunction in
lemma _01BT {X S A B : SSet} (p : X ⟶ S) (i : A ⟶ B)
    (hp : innerFibration p) [hi : Mono i] :
    innerFibration (Functor.PullbackObjObj.ofHasPullback internalHom i p).π := by
  rw [innerFibration_eq_rlp_innerAnodyne] at hp ⊢
  intro _ _ f hf
  rw [← hasLiftingProperty_iff internalHomAdjunction₂ (Functor.PushoutObjObj.ofHasPushout _ _ _)]
  exact hp _ (_00J8 i hf)

end SSet
