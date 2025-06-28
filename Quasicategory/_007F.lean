import Quasicategory._007F_1
import Quasicategory._007F.Tau
import Quasicategory._007F.Sigma

/-!

The second half of the proof of `007F`, which is much more technical.

-/

universe w v u

open CategoryTheory MorphismProperty Simplicial SSet PushoutProduct MonoidalCategory

variable {n : ℕ}

open Subcomplex.unionProd in
noncomputable
def unionProd_toSSet_iso (A : Subcomplex Δ[n]):
    PushoutProduct.pt A.ι Λ[2, 1].ι ≅
      (A.unionProd Λ[2, 1]).toSSet :=
  (IsPushout.isoPushout (isPushout Λ[2, 1] A)).symm ≪≫ symmIso _ _

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

open Subcomplex in
noncomputable
def image_arrow_iso_of_mono {X Y : SSet} (f : X ⟶ Y) [Mono f] (A : Subcomplex X) :
    Arrow.mk (Subcomplex.homOfLE (image_le_range A f)) ≅ Arrow.mk A.ι := by
  refine Arrow.isoMk ((isoOfEq (image_eq_range A f)) ≪≫ (asIso (toRangeSubcomplex (A.ι ≫ f))).symm)
    (asIso (toRangeSubcomplex f)).symm ?_
  simp
  have := inv (toRangeSubcomplex (A.ι ≫ f))
  --have := range_comp
  --have := toRangeSubcomplex_ι
  --ext n ⟨x, ⟨y, ⟨hy₁, hy₂⟩⟩⟩
  --simp
  sorry

noncomputable
def σ.innerHornImage_arrowIso (a b : Fin n) (hab : a ≤ b) :
    (Arrow.mk (Subcomplex.homOfLE (σ.innerHornImage_le a b))) ≅ (Arrow.mk Λ[n + 1, a.succ.castSucc].ι) :=
  letI : Mono (f a b) := f_mono hab
  image_arrow_iso_of_mono _ _

noncomputable
def τ.innerHornImage_arrowIso (a b : Fin (n + 1)) (hab : a ≤ b) :
    (Arrow.mk (Subcomplex.homOfLE (τ.innerHornImage_le a b))) ≅ (Arrow.mk Λ[n + 2, a.succ.castSucc].ι) :=
  letI : Mono (g a b) := g_mono hab
  image_arrow_iso_of_mono _ _

noncomputable
def zero_unionProd_arrowIso :
    Arrow.mk ((⊥ : Δ[0].Subcomplex).unionProd Λ[2, 1]).ι ≅
      Arrow.mk Λ[2, 1].ι := by
  refine Arrow.isoMk ?_ (stdSimplex.leftUnitor Δ[2]) ?_
  · dsimp
    refine (unionProd_toSSet_iso (⊥ : Δ[0].Subcomplex)).symm ≪≫ ?_
    simp
    --have := Subcomplex.botIsInitial Δ[0]
    sorry
  · sorry

lemma unionProd_ι_innerAnodyne : innerAnodyne.{u} (∂Δ[n].unionProd Λ[2, 1]).ι := by
  rw [innerAnodyne_eq]
  cases n
  · rw [boundary_zero]
    apply (MorphismProperty.arrow_mk_iso_iff _ zero_unionProd_arrowIso).2
    exact .of _ <| .mk Fin.zero_lt_one Fin.one_lt_last
  next n =>
  let σsq := (σ.filtrationPushout_zero'.{u} n)
  let τsq := (τ.filtrationPushout_zero'.{u} n)
  change innerHornInclusions.saturation
      ((Subcomplex.homOfLE σsq.le₃₄) ≫ (Subcomplex.homOfLE (filtration₁_monotone bot_le)) ≫ (Subcomplex.homOfLE τsq.le₃₄) ≫
      (Subcomplex.homOfLE (filtration₂_monotone bot_le)) ≫ (Subcomplex.isoOfEq filtration₂_last').hom ≫
      (Subcomplex.topIso (Δ[n + 1] ⊗ Δ[2])).hom)
  refine (innerHornInclusions.saturation).comp_mem _ _ ?_ <|
    (innerHornInclusions.saturation).comp_mem _ _ ?_ <|
    (innerHornInclusions.saturation).comp_mem _ _ ?_ <|
    (innerHornInclusions.saturation).comp_mem _ _ ?_ <|
    (innerHornInclusions.saturation).comp_mem _ _ ?_ ?_
  · apply (innerHornInclusions.saturation).of_isPushout (Subcomplex.Sq.isPushout σsq).flip
    apply (MorphismProperty.arrow_mk_iso_iff _ (σ.innerHornImage_arrowIso 0 0 (Fin.zero_le 0))).2
    exact .of _ <| .mk Fin.zero_lt_one Fin.one_lt_last
  · -- (filtration₁' ⊥).toSSet ⟶ (filtration₁' ⊤).toSSet
    sorry
  · apply (innerHornInclusions.saturation).of_isPushout (Subcomplex.Sq.isPushout τsq).flip
    apply (MorphismProperty.arrow_mk_iso_iff _ (τ.innerHornImage_arrowIso 0 0 (Fin.zero_le 0))).2
    exact .of _ <| .mk Fin.zero_lt_one Fin.one_lt_last
  · -- (filtration₂' ⊥).toSSet ⟶ (filtration₂' ⊤).toSSet
    sorry
  · apply of_isIso
  · apply of_isIso

noncomputable
def arrow_unionProd_iso : Arrow.mk (∂Δ[n].ι ◫ Λ[2, 1].ι) ≅ Arrow.mk (∂Δ[n].unionProd Λ[2, 1]).ι := by
  refine Arrow.isoMk (unionProd_toSSet_iso _) (β_ Δ[2] Δ[n]) ?_
  simp [unionProd_toSSet_iso]
  apply Limits.pushout.hom_ext
  all_goals aesop

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
    apply (MorphismProperty.arrow_mk_iso_iff _ arrow_unionProd_iso).2
    rw [← innerAnodyne_eq]
    exact unionProd_ι_innerAnodyne

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
