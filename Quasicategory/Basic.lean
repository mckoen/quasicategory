import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.SmallObject.Basic
import Quasicategory.MorphismProperty
import Quasicategory.Terminal
import Quasicategory.TopCatModelCategory.SSet.SmallObject

universe w v u

namespace SSet

attribute [local instance] Cardinal.fact_isRegular_aleph0

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

open CategoryTheory Simplicial MorphismProperty

inductive BoundaryInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk n : BoundaryInclusion (boundary n).ι

/-- The class of all boundary inclusions. -/
def bdryInclusions : MorphismProperty SSet := fun _ _ p ↦ BoundaryInclusion p

inductive InnerHornInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (h0 : 0 < i) (hn : i < Fin.last (n+2)) :
    InnerHornInclusion (horn (n+2) i).ι

/-- The class of all inner horn inclusions. -/
def innerHornInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerHornInclusion p

abbrev trivialFibration := bdryInclusions.rlp

abbrev innerFibration := innerHornInclusions.rlp

-- `01BB` S is a quasicategory iff S ⟶ Δ[0] is an inner fibration
lemma quasicategory_iff_proj_innerFibration {S : SSet} :
    Quasicategory S ↔ innerFibration S.proj := by
  constructor
  · intro h _ _ p hp
    constructor
    intro f _ _
    induction hp with
    | mk h0 hn =>
    obtain ⟨l, hl⟩ := h.hornFilling h0 hn f
    exact ⟨l, hl.symm, isTerminalZero.hom_ext _ _⟩
  · intro h
    constructor
    intro n i σ₀ h0 hn
    have := (CommSq.mk (isTerminalZero.hom_ext
      (σ₀ ≫ S.proj) ((horn (n + 2) i).ι ≫ Δ[n + 2].proj)))
    have lift := ((h _ (.mk h0 hn)).sq_hasLift this).exists_lift.some
    exact ⟨lift.l, lift.fac_left.symm⟩

-- `01BJ` if Y is a quasicategory and X ⟶ Y is an inner fibration, then X is a quasicategory
instance quasicategory_of_innerFibration {X Y : SSet} (p : X ⟶ Y) (hp : innerFibration p) :
    Quasicategory Y → Quasicategory X := fun h ↦ by
  rw [quasicategory_iff_proj_innerFibration] at h ⊢
  apply comp_mem _ p Y.proj hp h

/-- a morphism is inner anodyne if it has llp wrt all inner fibrations. -/
abbrev innerAnodyne := innerFibration.llp

lemma innerHorn_le_innerAnodyne : innerHornInclusions ≤ innerAnodyne :=
  fun _ _ _ ⟨h0, hn⟩ _ _ _ h ↦ h _ (.mk h0 hn)

def J' : MorphismProperty SSet.{u} :=
  ⨆ n, ofHoms (fun (j : { i : Fin (n + 3) // 0 < i ∧ i < Fin.last (n + 2) }) ↦ Λ[n + 2, j.1].ι)

lemma J'_eq : J' = innerHornInclusions.{u} := by
  apply le_antisymm
  · intro _ _ _ ⟨_, h⟩
    simp at h
    obtain ⟨⟨_, h⟩, hw⟩ := h
    obtain ⟨⟨i, ⟨hi₁, hi₂⟩⟩⟩ := h.2 hw
    exact .mk hi₁ hi₂
  · intro _ _ f hf
    induction hf with
    | @mk n i h0 hn =>
    simp [J']
    use n
    rw [ofHoms_iff]
    use ⟨_, ⟨h0, hn⟩⟩

instance isCardinalForSmallObjectArgument_innerHornInclusions :
    innerHornInclusions.{u}.IsCardinalForSmallObjectArgument Cardinal.aleph0.{u} where
  hasIterationOfShape := by infer_instance
  preservesColimit i hi f hf := by
    simp only [innerHornInclusions, iSup_iff] at hi
    cases hi with
    | mk n i =>
    infer_instance
  isSmall := by
    rw [← J'_eq, J']
    infer_instance

instance : HasSmallObjectArgument.{u} innerHornInclusions.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance, inferInstance⟩

lemma llp_rlp_eq_saturation {T : MorphismProperty SSet.{u}} [HasSmallObjectArgument.{u} T] :
    T.rlp.llp = saturation.{u} T := by
  apply le_antisymm
  · rw [llp_rlp_of_hasSmallObjectArgument, retracts_le_iff,
      transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact le_saturation _
  · rw [← WeaklySaturated.le_iff]
    exact T.le_llp_rlp

lemma innerAnodyne_eq : innerAnodyne.{u} = saturation.{u} innerHornInclusions :=
  llp_rlp_eq_saturation

-- extension property wrt every inner anodyne morphism is equivalent to S ⟶ Δ[0] having rlp wrt
-- every inner anodyne morphism
lemma extension_iff_rlp_proj {S : SSet} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    innerAnodyne.rlp S.proj := by
  refine ⟨?_, ?_⟩
  · intro h A B i hi
    constructor
    intro f₀ t sq
    obtain ⟨l, hl⟩ := h i hi f₀
    exact ⟨l, hl.symm, isTerminalZero.hom_ext _ _⟩
  · intro h A B i hi f₀
    obtain ⟨⟨lift⟩⟩ := (h _ hi).sq_hasLift
      (CommSq.mk (isTerminalZero.hom_ext (f₀ ≫ proj S) (i ≫ proj B)))
    exact ⟨lift.l, lift.fac_left.symm⟩

-- `007E`
-- quasicategory iff extension property wrt every inner anodyne morphism
instance quasicat_iff_extension_wrt_innerAnodyne {S : SSet} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    Quasicategory S := by
  refine ⟨fun h ↦
    ⟨fun n i σ₀ h0 hn ↦ h _ (innerHorn_le_innerAnodyne Λ[n + 2, i].ι (.mk h0 hn)) σ₀⟩, ?_⟩
  intro hS
  rw [extension_iff_rlp_proj, morphism_rlp_iff, innerAnodyne_eq, ← WeaklySaturated.le_iff]
  intro _ _ i ⟨h0, hn⟩ _ _ f ⟨⟩
  constructor
  intro σ₀ _ sq
  obtain ⟨l, hl⟩ := hS.hornFilling h0 hn σ₀
  exact ⟨l, hl.symm, isTerminalZero.hom_ext _ _⟩
