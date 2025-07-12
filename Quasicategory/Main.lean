import Quasicategory._007F
import Quasicategory.Quasicategory
import Quasicategory.InternalHom
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

universe w

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory MonoidalClosed

open PushoutProduct

variable {S : SSet} {m : ℕ}
  (α : ∂Δ[m].toSSet ⟶ (ihom Δ[2]).obj S)
  (β : Δ[m] ⟶ (ihom Λ[2, 1].toSSet).obj S)

lemma commSq_uncurry (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    CommSq (Λ[2, 1].ι ▷ ∂Δ[m]) (Λ[2, 1].toSSet ◁ ∂Δ[m].ι)
      (MonoidalClosed.uncurry α) (MonoidalClosed.uncurry β) := by
  constructor
  dsimp [MonoidalClosed.uncurry, Adjunction.homEquiv]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← Category.assoc, ← whisker_exchange, ← sq.w]
  rfl

-- induced morphism from pushout to `S` given by `S_cocone`
noncomputable
def to_S
    (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    (PushoutProduct.pt ∂Δ[m].ι Λ[2, 1].ι) ⟶ S :=
  PushoutProduct.desc _ _ (MonoidalClosed.uncurry α) (MonoidalClosed.uncurry β) (commSq_uncurry α β sq).w

-- the new square in `0079`
lemma newSquare
    (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    CommSq (to_S α β sq) (∂Δ[m].ι ◫ Λ[2, 1].ι) (isTerminalZero.from S) (isTerminalZero.from (Δ[2] ⊗ Δ[m])) :=
  CommSq.mk (isTerminalZero.hom_ext
    ((to_S α β sq) ≫ (isTerminalZero.from S)) ((∂Δ[m].ι ◫ Λ[2, 1].ι) ≫ (isTerminalZero.from (Δ[2] ⊗ Δ[m]))))

lemma sqLift_of_newSqLift
    (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    (newSquare α β sq).HasLift → sq.HasLift := by
  intro ⟨lift, fac_left, _⟩
  refine ⟨curry lift, ?_, ?_⟩
  · apply_fun uncurry
    rw [uncurry_natural_left, uncurry_curry]
    apply_fun (fun f ↦ (PushoutProduct.inl ∂Δ[m].ι Λ[2, 1].ι) ≫ f) at fac_left
    simp [to_S] at fac_left
    assumption
  · apply_fun uncurry
    rw [uncurry_natural_left]
    apply_fun (fun f ↦ (PushoutProduct.inr ∂Δ[m].ι Λ[2, 1].ι) ≫ f) at fac_left
    simp [to_S] at fac_left
    simp [← fac_left, whisker_exchange_assoc]

-- given a map from the pushout to S, we can recover a commutative square as in `0079`
def newSq
    (f : (PushoutProduct.pt ∂Δ[m].ι Λ[2, 1].ι) ⟶ S) :
  CommSq (MonoidalClosed.curry ((PushoutProduct.inl ∂Δ[m].ι Λ[2, 1].ι) ≫ f))
    ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S)
    (MonoidalClosed.curry ((PushoutProduct.inr ∂Δ[m].ι Λ[2, 1].ι) ≫ f)) := by
  constructor
  apply_fun uncurry
  simp [uncurry_natural_left, internalHom_map, uncurry_pre, uncurry_natural_left, whisker_exchange_assoc]
  exact Limits.pushout.condition_assoc f

-- iff the pushout diagram has an extension, then the square has a lift
lemma newSqLift_of_sqLift {S : SSet} {m : ℕ}
    (f : PushoutProduct.pt ∂Δ[m].ι Λ[2, 1].ι ⟶ S)
    (g : Δ[2] ⊗ Δ[m] ⟶ Δ[0])
    (sq : CommSq f (∂Δ[m].ι ◫ Λ[2, 1].ι) (isTerminalZero.from S) g) :
    (newSq f).HasLift → sq.HasLift := by
  intro ⟨lift, fac_left, fac_right⟩
  refine ⟨MonoidalClosed.uncurry lift, ?_, isTerminalZero.hom_ext _ _⟩
  apply Limits.pushout.hom_ext
  · apply_fun curry
    simpa [curry_natural_left]
  · apply_fun curry
    dsimp [PushoutProduct.inr] at fac_right
    simp [← fac_right, curry_eq_iff]
    rfl

/-- `0079` `S` is a quasi-category iff `ihom(Δ[2], S) ⟶ ihom(Λ[2, 1], S)` is a trivial fibration. -/
instance quasicategory_iff_internalHom_horn_trivialFibration (S : SSet) :
    Quasicategory S ↔
      trivialFibration ((internalHom.map Λ[2, 1].ι.op).app S) := by
  rw [quasicategory_iff_from_innerAnodyne_rlp, morphism_rlp_iff,
    ← contains_innerAnodyne_iff_contains_pushout_maps, le_llp_iff_le_rlp, morphism_le_iff]
  constructor
  · intro h _ _ _ ⟨m⟩
    constructor
    intro α β sq
    exact sqLift_of_newSqLift α β sq ((h _ (.mk m)).sq_hasLift (newSquare _ _ sq))
  · intro h _ _ _ ⟨m⟩
    constructor
    intro f g sq
    exact newSqLift_of_sqLift f g sq ((h _ (.mk m)).sq_hasLift (newSq f))

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

noncomputable
def bdryHornPushoutProduct (m : ℕ) : Functor.PushoutObjObj (curriedTensor SSet) Λ[2, 1].ι ∂Δ[m].ι :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

noncomputable
def hornFromPullbackPower (S : SSet) : Functor.PullbackObjObj internalHom Λ[2, 1].ι (isTerminalZero.from S) :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

/-
#check ParametrizedAdjunction.liftStructEquiv internalHomAdjunction₂ (bdryHornPushoutProduct m) (hornFromPullbackPower S)

#check ParametrizedAdjunction.hasLiftingProperty_iff internalHomAdjunction₂ (bdryHornPushoutProduct m) (hornFromPullbackPower S)

/-
def : Limits.pullback ((ihom Λ[2, 1].toSSet).map (isTerminalZero.from S)) ((pre Λ[2, 1].ι).app Δ[0]) ≅
  (ihom Λ[2, 1].toSSet).obj S
-/

noncomputable
def hornFromPullbackPower_π_arrowIso :
    Arrow.mk (S.hornFromPullbackPower.π) ≅ Arrow.mk ((internalHom.map Λ[2, 1].ι.op).app S) := by
  apply Arrow.isoMk
  · sorry
  · exact Iso.refl _
  · simp [hornFromPullbackPower]
    have := isProductOfIsTerminalIsPullback
    sorry

-- `0079`
/-- `S` is a quasi-category iff `ihom(Δ[2], S) ⟶ ihom(Λ[2, 1], S)` is a trivial fibration. -/
instance quasicategory_iff_internalHom_horn_trivialFibration' (S : SSet) :
    Quasicategory S ↔
      trivialFibration ((internalHom.map Λ[2, 1].ι.op).app S) := by
  rw [quasicategory_iff_from_innerAnodyne_rlp, morphism_rlp_iff,
    ← contains_innerAnodyne_iff_contains_pushout_maps, le_llp_iff_le_rlp, morphism_le_iff]
  constructor
  · intro h _ _ _ ⟨m⟩
    have := ParametrizedAdjunction.hasLiftingProperty_iff internalHomAdjunction₂ (bdryHornPushoutProduct m) (hornFromPullbackPower S)
    dsimp [rlp] at h
    sorry
  · intro h _ _ _ ⟨m⟩

    sorry
/-
-/
-/

end SSet
