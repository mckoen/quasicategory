import Mathlib.AlgebraicTopology.Quasicategory
import Quasicategory.MorphismProperty
import Quasicategory.Terminal
import Mathlib.AlgebraicTopology.KanComplex

namespace SSet

open CategoryTheory Simplicial MorphismProperty

inductive BoundaryInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk n : BoundaryInclusion (boundaryInclusion n)

/-- The class of all boundary inclusions. -/
def BoundaryInclusions : MorphismProperty SSet := fun _ _ p ↦ BoundaryInclusion p

inductive HornInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (h0 : 0 ≤ i) (hn : i ≤ Fin.last (n+2)) :
    HornInclusion (hornInclusion (n+2) i)

/-- The class of all horn inclusions. -/
def HornInclusions : MorphismProperty SSet := fun _ _ p ↦ HornInclusion p

inductive LeftHornInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (h0 : 0 ≤ i) (hn : i < Fin.last (n+2)) :
    LeftHornInclusion (hornInclusion (n+2) i)

/-- The class of all left horn inclusions. -/
def LeftHornInclusions : MorphismProperty SSet := fun _ _ p ↦ LeftHornInclusion p

inductive RightHornInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (h0 : 0 < i) (hn : i ≤ Fin.last (n+2)) :
    RightHornInclusion (hornInclusion (n+2) i)

/-- The class of all right horn inclusions. -/
def RightHornInclusions : MorphismProperty SSet := fun _ _ p ↦ RightHornInclusion p

inductive InnerHornInclusion : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (h0 : 0 < i) (hn : i < Fin.last (n+2)) :
    InnerHornInclusion (hornInclusion (n+2) i)

/-- The class of all inner horn inclusions. -/
def InnerHornInclusions : MorphismProperty SSet := fun _ _ p ↦ InnerHornInclusion p

/- a morphism is a trivial Kan fibration if it has the right lifting property wrt
  every boundary inclusion  `∂Δ[n] ⟶ Δ[n]`. -/
abbrev trivialKanFibration := BoundaryInclusions.rlp

abbrev kanFibration := HornInclusions.rlp

abbrev leftFibration := LeftHornInclusions.rlp

abbrev rightFibration := RightHornInclusions.rlp

/- a morphism is an inner fibration if it has the right lifting property wrt
  every inner horn inclusion  `Λ[n, i] ⟶ Δ[n]`. -/
abbrev innerFibration := InnerHornInclusions.rlp

-- left fibrations are inner fibrations
lemma innerFibration_of_leftFibration {X Y : SSet} (p : X ⟶ Y) (hp : leftFibration p) :
    innerFibration p := fun _ _ _ h ↦ by
  induction h with
  | mk h0 hn => exact hp (.mk (le_of_lt h0) hn)

-- right fibrations are inner fibrations
lemma innerFibration_of_rightFibration {X Y : SSet} (p : X ⟶ Y) (hp : rightFibration p) :
    innerFibration p := fun _ _ _ h ↦ by
  induction h with
  | mk h0 hn => exact hp (.mk h0 (le_of_lt hn))

-- `01BB` S is a quasicategory iff S ⟶ Δ[0] is an inner fibration
lemma quasicategory_iff_proj_innerFibration {S : SSet} :
    Quasicategory S ↔ innerFibration S.proj := by
  refine ⟨fun h _ _ p hp ↦ ⟨?_⟩, fun h ↦ ⟨?_⟩⟩
  · intro f _ _
    induction hp with
    | mk h0 hn =>
    obtain ⟨l, hl⟩ := h.hornFilling h0 hn f
    exact ⟨l, hl.symm, ptIsTerminal.hom_ext _ _⟩
  · intro n i σ₀ h0 hn
    have := (CommSq.mk (Limits.IsTerminal.hom_ext ptIsTerminal
      (σ₀ ≫ S.proj) (hornInclusion (n + 2) i ≫  Δ[n + 2].proj)))
    have lift := ((h (.mk h0 hn)).sq_hasLift this).exists_lift.some
    exact ⟨lift.l, lift.fac_left.symm⟩

-- `01BJ` if Y is a quasicategory and X ⟶ Y is an inner fibration, then X is a quasicategory
instance quasicategory_of_innerFibration {X Y : SSet} (p : X ⟶ Y) (hp : innerFibration p) :
    Quasicategory Y → Quasicategory X := fun h ↦ by
  rw [quasicategory_iff_proj_innerFibration] at h ⊢
  exact rlp_comp _ p hp Y.proj h

/- a morphism is inner anodyne if it has the left lifting property wrt all inner fibrations. -/
abbrev innerAnodyne := innerFibration.llp

lemma innerHorn_le_innerAnodyne : InnerHornInclusions ≤ innerAnodyne := fun _ _ _ hp ↦ by
  induction hp with
  | mk h0 hn => exact fun _ _ _ h ↦ h (.mk h0 hn)

lemma innerAnodyne_eq :
    innerAnodyne = WeaklySaturatedClassOf InnerHornInclusions := by
  ext X Y p
  refine ⟨?_, minimalWeaklySaturated innerAnodyne _ innerHorn_le_innerAnodyne (llp_weakly_saturated _) p⟩
  · sorry -- small object argument?

/-
-- `01C3` aux
def bijection_on_vertices : MorphismProperty SSet.{0} := fun A B _ ↦
  ∃ (f : A _[0] → B _[0]), Function.Bijective f

-- `01C3` aux
instance bijection_on_vertices.WeaklySaturated : WeaklySaturated bijection_on_vertices := by
  sorry

-- `01C3` aux
lemma inner_horn_bij_on_vertices
    ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    bijection_on_vertices (hornInclusion.{0} (n+2) i) := by
  sorry

-- `01C3` inner anodyne morphisms are bijective on vertices
def innerAnodyneVerticesEquiv {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p) :
    bijection_on_vertices p := by
  apply (contains_innerAnodyne_iff_contains_inner_horn.{0,1}
    bijection_on_vertices bijection_on_vertices.WeaklySaturated).1
  exact inner_horn_bij_on_vertices
  exact hp
-/

-- extension property wrt every inner anodyne morphism is equivalent to S ⟶ Δ[0] having RLP wrt
-- every inner anodyne morphism
lemma extension_iff_rlp_proj {S : SSet} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    innerAnodyne.rlp S.proj := by
  refine ⟨?_, ?_⟩
  · intro h A B i hi
    constructor
    intro f₀ t sq
    obtain ⟨l, hl⟩ := h i hi f₀
    exact ⟨l, hl.symm, Limits.IsTerminal.hom_ext ptIsTerminal _ _⟩
  · intro h A B i hi f₀
    obtain ⟨⟨lift⟩⟩ := (h hi).sq_hasLift
      (CommSq.mk (Limits.IsTerminal.hom_ext ptIsTerminal (f₀ ≫ proj S) (i ≫ proj B)))
    exact ⟨lift.l, lift.fac_left.symm⟩

-- since S is a quasicat, every inner horn inclusion has LLP wrt (S ⟶ Δ[0]), and
-- inner horn inclusions generate inner anodyne morphisms,
-- so all inner anodyne must have LLP wrt (S ⟶ Δ[0])

-- `007E`
-- quasicategory iff extension property wrt every inner anodyne morphism
instance quasicat_iff_extension_wrt_innerAnodyne {S : SSet.{0}} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    Quasicategory S := by
  refine ⟨fun h ↦
    ⟨fun n i σ₀ h0 hn ↦ h _ (innerHorn_le_innerAnodyne (hornInclusion (n + 2) i) (.mk h0 hn)) σ₀⟩, ?_⟩
  intro hS
  rw [extension_iff_rlp_proj, class_rlp_iff_llp_morphism, innerAnodyne_eq]
  intro _ _ _
  refine minimalWeaklySaturated.{0} ((MorphismClass S.proj).llp) InnerHornInclusions ?_ (llp_weakly_saturated _) _
  intro _ _ i hi
  induction hi with | mk h0 hn =>
  intro _ _ f hf
  induction hf with | mk =>
  constructor
  intro σ₀ _ sq
  obtain ⟨l, hl⟩ := hS.hornFilling h0 hn σ₀
  exact ⟨l, hl.symm, Limits.IsTerminal.hom_ext ptIsTerminal _ _⟩
