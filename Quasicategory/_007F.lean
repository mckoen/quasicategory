import Quasicategory._007F_1
import Quasicategory._007F.Tau
import Quasicategory._007F.Sigma

/-!

The second half of the proof of `007F`, which is much more technical.

-/

universe w v u

open CategoryTheory MorphismProperty Simplicial SSet PushoutProduct MonoidalCategory

variable {n : ℕ}

#synth LinearOrder (Σₗ (b : Fin (n + 1)), Fin b.succ)
#synth OrderBot (Σₗ (b : Fin (n + 1)), Fin b.succ)
#synth SuccOrder (Σₗ (b : Fin (n + 1)), Fin b.succ)
#synth WellFoundedLT (Σₗ (b : Fin (n + 1)), Fin b.succ)

#check HomotopicalAlgebra.RelativeCellComplex
#check HomotopicalAlgebra.RelativeCellComplex.transfiniteCompositionOfShape

open Subcomplex.unionProd in
noncomputable
def unionProd_toSSet_iso :
    PushoutProduct.pt ∂Δ[n + 1].ι Λ[2, 1].ι ≅
      (∂Δ[n + 1].unionProd Λ[2, 1]).toSSet :=
  (IsPushout.isoPushout (isPushout Λ[2, 1] ∂Δ[n + 1])).symm ≪≫ symmIso _ _

open Subcomplex in
def σ.filtrationPushout_zero' (n : ℕ) :
    Sq
      (σ.innerHornImage 0 0)
      (σ 0 0)
      (∂Δ[n + 1].unionProd Λ[2, 1])
      (filtration₁' ⊥) := by
  convert filtrationPushout_zero n
  simp [filtration₁', filtration₁, σ.eq_σ]
  rfl

open Subcomplex in
def τ.filtrationPushout_zero' (n : ℕ) :
    Sq
      (τ.innerHornImage 0 0)
      (τ 0 0)
      (filtration₁' (n := n + 1) ⊤)
      (filtration₂' ⊥) := by
  convert filtrationPushout_zero (n + 1)
  · simp [filtration₁', filtration₁, σ.eq_σ]
    apply le_antisymm
    · apply sup_le (le_sup_left) (le_sup_of_le_right _)
      apply iSup_le
      intro ⟨b, a⟩
      apply le_iSup₂_of_le ⟨b, by rw [Nat.mod_eq_of_lt (by omega)]; omega⟩ a
      exact le_rfl
    · apply sup_le (le_sup_left) (le_sup_of_le_right _)
      apply iSup₂_le
      intro ⟨b, hb⟩ ⟨a, ha⟩
      rw [Nat.mod_eq_of_lt (by omega)] at hb
      apply le_iSup_of_le ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      exact le_rfl
  · simp [filtration₂', filtration₁', filtration₃, filtration₁, τ.eq_τ, σ.eq_σ]
    apply le_antisymm
    · apply sup_le (le_sup_of_le_left (sup_le le_sup_left (le_sup_of_le_right _))) (le_sup_right)
      apply iSup_le
      intro ⟨b, a⟩
      apply le_iSup₂_of_le b a
      exact le_rfl
    · apply sup_le (le_sup_of_le_left (sup_le le_sup_left (le_sup_of_le_right _))) (le_sup_right)
      apply iSup₂_le
      intro ⟨b, hb⟩ ⟨a, ha⟩
      apply le_iSup_of_le ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      exact le_rfl

lemma unionProd_ι_innerAnodyne : innerAnodyne.{u} (∂Δ[n].unionProd Λ[2, 1]).ι := by
  rw [innerAnodyne_eq]
  cases n
  · rw [boundary_zero]
    dsimp [Subcomplex.unionProd]
    sorry -- if n=0, case should collapse
  next n =>
  let σsq := (σ.filtrationPushout_zero'.{u} n)
  let τsq := (τ.filtrationPushout_zero'.{u} n)
  change innerHornInclusions.saturation
      ((Subcomplex.homOfLE σsq.le₃₄) ≫ (Subcomplex.homOfLE (filtration₁_monotone.{u} bot_le)) ≫ (Subcomplex.homOfLE τsq.le₃₄) ≫
      (Subcomplex.homOfLE (filtration₂_monotone.{u} bot_le)) ≫ (Subcomplex.isoOfEq (filtration₂_last'.{u})).hom ≫
      (Subcomplex.topIso _).hom)
  refine (innerHornInclusions.saturation).comp_mem _ _ ?_ <|
    (innerHornInclusions.saturation).comp_mem _ _ ?_ <|
    (innerHornInclusions.saturation).comp_mem _ _ ?_ <|
    (innerHornInclusions.saturation).comp_mem _ _ ?_ <|
    (innerHornInclusions.saturation).comp_mem _ _ ?_ <|

  sorry

lemma innerAnodyne_eq_T : innerAnodyne.{u} = (saturation.{u} bdryHornPushouts) := by
  rw [innerAnodyne_eq]
  apply le_antisymm
  all_goals rw [← WeaklySaturated.le_iff]
  · intro _ _ f hf
    cases hf with
    | @mk n i h0 hn =>
      apply WeaklySaturatedClass.retract (hornRetract i h0 hn) -- reduces to showing horn inclusion is a retract of a boundary pushout maps
      exact monomorphisms_le_S _ (monomorphisms.infer_property _)
  · intro _ _ f ⟨n⟩
    sorry

-- `007F` (a)
lemma monoPushout_innerAnodyne {A B : SSet} (i : A ⟶ B) [Mono i] :
    innerAnodyne (i ◫ Λ[2, 1].ι) := by
  rw [innerAnodyne_eq_T]
  exact monomorphisms_le_S i (.infer_property _)

-- `007F` (b)
lemma contains_innerAnodyne_iff_contains_pushout_maps
    (S : MorphismProperty SSet) [WeaklySaturated.{u} S] :
    (bdryHornPushouts ≤ S) ↔ (innerAnodyne.{u} ≤ S) := by
  constructor
  · simp [innerAnodyne_eq_T, ← WeaklySaturated.le_iff]
  · exact fun h _ _ _ ⟨m⟩ ↦ h _ (monoPushout_innerAnodyne ∂Δ[m].ι)
