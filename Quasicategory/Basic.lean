import Mathlib.AlgebraicTopology.Quasicategory
import Quasicategory.MorphismProperty
import Quasicategory.Terminal
import Mathlib.AlgebraicTopology.KanComplex

namespace SSet

open CategoryTheory Simplicial MorphismProperty

/- a morphism is a trivial Kan fibration if it has the right lifting property wrt
  every boundary inclusion  `∂Δ[n] ⟶ Δ[n]`. -/
def trivialKanFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ (n : ℕ), HasLiftingProperty (boundaryInclusion n) p

def leftFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 ≤ i) (_hn : i < Fin.last (n+2)),
    HasLiftingProperty (hornInclusion (n+2) i) p

def rightFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i ≤ Fin.last (n+2)),
    HasLiftingProperty (hornInclusion (n+2) i) p

/- a morphism is an inner fibration if it has the right lifting property wrt
  every inner horn inclusion  `Λ[n, i] ⟶ Δ[n]`. -/
def innerFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
    HasLiftingProperty (hornInclusion (n+2) i) p

-- `01BD`
instance innerFibration.StableUnderRetracts : StableUnderRetracts innerFibration := by
  sorry

-- `01BE`
instance innerFibration.StableUnderBaseChange : StableUnderBaseChange innerFibration := by
  sorry

/- a morphism is inner anodyne if it has the left lifting property wrt all inner fibrations. -/
abbrev innerAnodyne := innerFibration.llp

/- inner horn inclusions are inner anodyne. -/
lemma innerAnodyne_of_innerHorn
    ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    innerAnodyne (hornInclusion (n+2) i) := fun _ _ _ h ↦ h _h0 _hn

def innerAnodyneVerticesEquiv' {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p) :
    (Δ[0] ⟶ X) ≃ (Δ[0] ⟶ Y) where
  toFun := by
    intro x
    dsimp [innerAnodyne, innerFibration, llp] at hp
    sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

def innerAnodyneVerticesEquiv {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p) :
    X _[0] ≃ Y _[0] :=
  sorry

-- innerAnodyne = llp(rlp(inner horn inclusions)) is WSC gen. by inner horn inclusions
lemma contains_innerAnodyne_iff_contains_inner_horn
    (S : MorphismProperty SSet) (hS : WeaklySaturated S) :
    (∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)), S (hornInclusion (n+2) i))
      ↔ (∀ {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p), S p) := by
  refine ⟨?_, fun h n i _h0 _hn ↦ h (hornInclusion (n + 2) i) (innerAnodyne_of_innerHorn _h0 _hn)⟩
  sorry

-- extension property wrt every inner anodyne morphism is equivalent to S ⟶ Δ[0] having RLP wrt
-- every inner anodyne morphism
lemma extension_iff_llp_proj {S : SSet} :
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
instance quasicat_iff_extension_wrt_innerAnodyne {S : SSet} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    Quasicategory S := by
  refine ⟨fun h ↦
    ⟨fun n i σ₀ _h0 _hn ↦ h (hornInclusion (n + 2) i) (innerAnodyne_of_innerHorn _h0 _hn) σ₀⟩, ?_⟩
  intro hS
  rw [extension_iff_llp_proj]
  apply (contains_innerAnodyne_iff_contains_inner_horn (llp' S.proj)
    (llp_weakly_saturated' S.proj)).1
  intro n i _h0 _hn
  constructor
  intro σ₀ _ sq
  obtain ⟨l, hl⟩ := hS.hornFilling _h0 _hn σ₀
  exact ⟨l, hl.symm, Limits.IsTerminal.hom_ext ptIsTerminal _ _⟩
