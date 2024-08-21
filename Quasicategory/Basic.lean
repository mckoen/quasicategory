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

def kanFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 ≤ i) (_hn : i ≤ Fin.last (n+2)),
    HasLiftingProperty (hornInclusion (n+2) i) p

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

-- left fibrations are inner fibrations
lemma innerFibration_of_leftFibration {X Y : SSet} (p : X ⟶ Y) (hp : leftFibration p) :
    innerFibration p := fun _ _ _h0 _hn ↦ hp (le_of_lt _h0) _hn

-- right fibrations are inner fibrations
lemma innerFibration_of_rightFibration {X Y : SSet} (p : X ⟶ Y) (hp : rightFibration p) :
    innerFibration p := fun _ _ _h0 _hn ↦ hp _h0 (le_of_lt _hn)

-- `01BB` S is a quasicategory iff S ⟶ Δ[0] is an inner fibration
lemma quasicategory_iff_proj_innerFibration {S : SSet} :
    Quasicategory S ↔ innerFibration S.proj := by
  refine ⟨fun h _ _ _h0 _hn ↦ ⟨?_⟩, fun h ↦ ⟨?_⟩⟩
  · intro f _ _
    obtain ⟨l, hl⟩ := h.hornFilling _h0 _hn f
    exact ⟨l, hl.symm, ptIsTerminal.hom_ext _ _⟩
  · intro n i σ₀ _h0 _hn
    have := (CommSq.mk (Limits.IsTerminal.hom_ext ptIsTerminal
      (σ₀ ≫ S.proj) (hornInclusion (n + 2) i ≫  Δ[n + 2].proj)))
    have lift := ((h _h0 _hn).sq_hasLift this).exists_lift.some
    exact ⟨lift.l, lift.fac_left.symm⟩

-- `014R` composition of left fibrations is a left fibration
lemma leftFibration_comp {X Y Z : SSet} (p : X ⟶ Y) (hp : leftFibration p) (q : Y ⟶ Z)
    (hq : leftFibration q) : leftFibration (p ≫ q) := by
  intro n i _h0 _hn
  constructor
  intro f g sq
  have q_sq_comm : (f ≫ p) ≫ q = (hornInclusion (n + 2) i) ≫ g := by
    rw [Category.assoc, sq.w]
  have q_sq := CommSq.mk q_sq_comm
  obtain ⟨q_lift, q_fac_left, q_fac_right⟩ := ((hq _h0 _hn).sq_hasLift q_sq).exists_lift.some
  have p_sq := CommSq.mk q_fac_left.symm
  obtain ⟨p_lift, p_fac_left, p_fac_right⟩ := ((hp _h0 _hn).sq_hasLift p_sq).exists_lift.some
  refine ⟨p_lift, p_fac_left, ?_⟩
  rw [← Category.assoc, p_fac_right, q_fac_right]

-- `014R` composition of right fibrations is a right fibration
lemma rightFibration_comp {X Y Z : SSet} (p : X ⟶ Y) (hp : rightFibration p) (q : Y ⟶ Z)
    (hq : rightFibration q) : rightFibration (p ≫ q) := by
  intro n i _h0 _hn
  constructor
  intro f g sq
  have q_sq_comm : (f ≫ p) ≫ q = (hornInclusion (n + 2) i) ≫ g := by
    rw [Category.assoc, sq.w]
  have q_sq := CommSq.mk q_sq_comm
  obtain ⟨q_lift, q_fac_left, q_fac_right⟩ := ((hq _h0 _hn).sq_hasLift q_sq).exists_lift.some
  have p_sq := CommSq.mk q_fac_left.symm
  obtain ⟨p_lift, p_fac_left, p_fac_right⟩ := ((hp _h0 _hn).sq_hasLift p_sq).exists_lift.some
  refine ⟨p_lift, p_fac_left, ?_⟩
  rw [← Category.assoc, p_fac_right, q_fac_right]

-- `01BH` composition of inner fibrations is an inner fibration
lemma innerFibration_comp {X Y Z : SSet} (p : X ⟶ Y) (hp : innerFibration p) (q : Y ⟶ Z)
    (hq : innerFibration q) : innerFibration (p ≫ q) := by
  intro n i _h0 _hn
  constructor
  intro f g sq
  have q_sq_comm : (f ≫ p) ≫ q = (hornInclusion (n + 2) i) ≫ g := by
    rw [Category.assoc, sq.w]
  have q_sq := CommSq.mk q_sq_comm
  obtain ⟨q_lift, q_fac_left, q_fac_right⟩ := ((hq _h0 _hn).sq_hasLift q_sq).exists_lift.some
  have p_sq := CommSq.mk q_fac_left.symm
  obtain ⟨p_lift, p_fac_left, p_fac_right⟩ := ((hp _h0 _hn).sq_hasLift p_sq).exists_lift.some
  refine ⟨p_lift, p_fac_left, ?_⟩
  rw [← Category.assoc, p_fac_right, q_fac_right]

-- `01BJ` if Y is a quasicategory and X ⟶ Y is an inner fibration, then X is a quasicategory
instance quasicategory_of_innerFibration {X Y : SSet} (p : X ⟶ Y) (hp : innerFibration p) :
    Quasicategory Y → Quasicategory X := fun h ↦ by
  rw [quasicategory_iff_proj_innerFibration] at h ⊢
  exact innerFibration_comp p hp Y.proj h

/- the retract proofs below are basically the same as `rlp_retract`,
   but we can't use that because fibrations are defined as having rlp wrt
   certain collections of horn inclusions, and I'm not sure how to define
   such a collection as a morphism property. -/

instance leftFibration.StableUnderRetracts : StableUnderRetracts leftFibration := by
  intro C D C' D' f f' H hg
  intro n i _h0 _hn
  refine ⟨?_⟩
  intro u v sq
  have : (u ≫ H.i.left) ≫ f' = ((hornInclusion (n + 2) i)) ≫ (v ≫ H.i.right) := by
    rw [← Category.assoc, ← sq.w]
    simp
  obtain lift := ((hg _h0 _hn).sq_hasLift (CommSq.mk this)).exists_lift.some
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

--
instance leftFibration.StableUnderBaseChange : StableUnderBaseChange leftFibration := by
  sorry

--
instance rightFibration.StableUnderRetracts : StableUnderRetracts rightFibration := by
  intro C D C' D' f f' H hg
  intro n i _h0 _hn
  refine ⟨?_⟩
  intro u v sq
  have : (u ≫ H.i.left) ≫ f' = ((hornInclusion (n + 2) i)) ≫ (v ≫ H.i.right) := by
    rw [← Category.assoc, ← sq.w]
    simp
  obtain lift := ((hg _h0 _hn).sq_hasLift (CommSq.mk this)).exists_lift.some
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

--
instance rightFibration.StableUnderBaseChange : StableUnderBaseChange rightFibration := by
  sorry

-- `01BD`
instance innerFibration.StableUnderRetracts : StableUnderRetracts innerFibration := by
  intro C D C' D' f f' H hg
  intro n i _h0 _hn
  refine ⟨?_⟩
  intro u v sq
  have : (u ≫ H.i.left) ≫ f' = ((hornInclusion (n + 2) i)) ≫ (v ≫ H.i.right) := by
    rw [← Category.assoc, ← sq.w]
    simp
  obtain lift := ((hg _h0 _hn).sq_hasLift (CommSq.mk this)).exists_lift.some
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

-- `01BE`
instance innerFibration.StableUnderBaseChange : StableUnderBaseChange innerFibration := by
  sorry

/- a morphism is inner anodyne if it has the left lifting property wrt all inner fibrations. -/
abbrev innerAnodyne := innerFibration.llp

/- inner horn inclusions are inner anodyne. -/
lemma innerAnodyne_of_innerHorn
    ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    innerAnodyne (hornInclusion (n+2) i) := fun _ _ _ h ↦ h _h0 _hn

-- innerAnodyne = llp(rlp(inner horn inclusions)) is WSC gen. by inner horn inclusions
lemma contains_innerAnodyne_iff_contains_inner_horn
    (S : MorphismProperty SSet) (hS : WeaklySaturated S) :
    (∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)), S (hornInclusion (n+2) i))
      ↔ (∀ {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p), S p) := by
  refine ⟨?_, fun h n i _h0 _hn ↦ h (hornInclusion (n + 2) i) (innerAnodyne_of_innerHorn _h0 _hn)⟩
  sorry

-- `01C3` aux
def bijection_on_vertices : MorphismProperty SSet := fun A B _ ↦
  ∃ (f : A _[0] → B _[0]), Function.Bijective f

-- `01C3` aux
instance bijection_on_vertices.WeaklySaturated : WeaklySaturated bijection_on_vertices := by
  sorry

-- `01C3` aux
lemma inner_horn_bij_on_vertices
    ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    bijection_on_vertices (hornInclusion (n+2) i) := by
  sorry

-- `01C3` inner anodyne morphisms are bijective on vertices
def innerAnodyneVerticesEquiv {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p) :
    bijection_on_vertices p := by
  apply (contains_innerAnodyne_iff_contains_inner_horn
    bijection_on_vertices bijection_on_vertices.WeaklySaturated).1
  exact inner_horn_bij_on_vertices
  exact hp

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
