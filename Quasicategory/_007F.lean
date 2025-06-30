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
def σ.innerHornImage_arrowIso {a b : Fin n} (hab : a ≤ b) :
    (Arrow.mk (Subcomplex.homOfLE (σ.innerHornImage_le a b))) ≅ (Arrow.mk Λ[n + 1, a.succ.castSucc].ι) :=
  letI : Mono (f a b) := f_mono hab
  image_arrow_iso_of_mono _ _

noncomputable
def τ.innerHornImage_arrowIso {a b : Fin (n + 1)} (hab : a ≤ b) :
    (Arrow.mk (Subcomplex.homOfLE (τ.innerHornImage_le a b))) ≅ (Arrow.mk Λ[n + 2, a.succ.castSucc].ι) :=
  letI : Mono (g a b) := g_mono hab
  image_arrow_iso_of_mono _ _

instance {X Y Z : SSet} : Subsingleton ((Y ⊗ (⊥ : X.Subcomplex).toSSet) ⟶ Z) where
  allEq f g := by
    ext _ ⟨_, ⟨x, hx⟩⟩
    simp at hx

instance {X Y Z : SSet} : Inhabited ((Y ⊗ (⊥ : X.Subcomplex).toSSet) ⟶ Z) where
  default :=
    { app _ := fun ⟨_, ⟨_, hx⟩⟩ ↦ by simp at hx
      naturality _ _ _ := by
        ext ⟨_, ⟨_, hx⟩⟩
        simp at hx }

instance {X Y Z : SSet} : Unique ((Y ⊗ (⊥ : X.Subcomplex).toSSet) ⟶ Z)  where
  uniq _ := Subsingleton.elim _ _

noncomputable
def SSet.Subcomplex.tensorBotIsInitial {X Y : SSet} : Limits.IsInitial (Y ⊗ (⊥ : X.Subcomplex).toSSet) :=
  Limits.IsInitial.ofUnique _

noncomputable
def pt_terminal_iso :
    Limits.pushout (Λ[2, 1].ι ▷ (⊥ : Δ[0].Subcomplex).toSSet) (Λ[2, 1].toSSet ◁ ((⊥ : Δ[0].Subcomplex)).ι) ≅
      Λ[2, 1].toSSet ⊗ Δ[0] where
  hom := Limits.pushout.desc (Limits.IsInitial.to Subcomplex.tensorBotIsInitial _) (𝟙 _) (by aesop_cat)
  inv := Limits.pushout.inr _ _
  hom_inv_id := by
    apply Limits.pushout.hom_ext
    all_goals aesop_cat

noncomputable
def zero_unionProd_arrowIso' :
    Arrow.mk (Λ[2, 1].unionProd (⊥ : Δ[0].Subcomplex)).ι ≅
      Arrow.mk (Λ[2, 1].ι ▷ Δ[0]) := by
  refine Arrow.isoMk ((IsPushout.isoPushout (Subcomplex.unionProd.isPushout _ _)) ≪≫ pt_terminal_iso) (Iso.refl _) ?_
  apply IsPushout.hom_ext (Subcomplex.unionProd.isPushout _ _)
  · aesop_cat
  · simp [pt_terminal_iso]

noncomputable
def zero_unionProd_arrowIso :
    Arrow.mk ((⊥ : Δ[0].Subcomplex).unionProd Λ[2, 1]).ι ≅
      Arrow.mk (Λ[2, 1].ι) := by
  refine ?_ ≪≫ zero_unionProd_arrowIso' ≪≫ ?_
  · exact Arrow.isoMk (Subcomplex.unionProd.symmIso _ _) (β_ _ _) rfl
  · exact Arrow.isoMk (stdSimplex.rightUnitor _) (stdSimplex.rightUnitor _) rfl

open Subcomplex in
lemma unionProd_ι_innerAnodyne : innerAnodyne.{u} (∂Δ[n].unionProd Λ[2, 1]).ι := by
  rw [innerAnodyne_eq]
  cases n
  · rw [boundary_zero]
    exact (arrow_mk_iso_iff _ zero_unionProd_arrowIso).2 <| .of _ <| .mk Fin.zero_lt_one Fin.one_lt_last
  next n =>
  let σsq := (σ.filtrationPushout_zero' n)
  let τsq := (τ.filtrationPushout_zero' n)
  change innerHornInclusions.saturation
      ((homOfLE σsq.le₃₄) ≫ (homOfLE (filtration₁_monotone bot_le)) ≫ (homOfLE τsq.le₃₄) ≫
      (homOfLE (filtration₂_monotone bot_le)) ≫ (isoOfEq filtration₂_last').hom ≫
      (topIso (Δ[n + 1] ⊗ Δ[2])).hom)
  refine comp_mem _ _ _ ?_ <| comp_mem _ _ _ ?_ <| comp_mem _ _ _ ?_ <| comp_mem _ _ _ ?_ <| comp_mem _ _ _ (of_isIso _ _) (of_isIso _ _)
  · apply of_isPushout (Sq.isPushout σsq).flip
    apply (arrow_mk_iso_iff _ (σ.innerHornImage_arrowIso (Fin.zero_le 0))).2
    exact .of _ <| .mk Fin.zero_lt_one Fin.one_lt_last
  · -- (filtration₁' ⊥).toSSet ⟶ (filtration₁' ⊤).toSSet
    sorry
  · apply of_isPushout (Sq.isPushout τsq).flip
    apply (arrow_mk_iso_iff _ (τ.innerHornImage_arrowIso (Fin.zero_le 0))).2
    exact .of _ <| .mk Fin.zero_lt_one Fin.one_lt_last
  · -- (filtration₂' ⊥).toSSet ⟶ (filtration₂' ⊤).toSSet
    sorry

noncomputable
def arrow_unionProd_iso : Arrow.mk (∂Δ[n].ι ◫ Λ[2, 1].ι) ≅ Arrow.mk (∂Δ[n].unionProd Λ[2, 1]).ι := by
  refine Arrow.isoMk (unionProd_toSSet_iso _) (β_ Δ[2] Δ[n]) ?_
  simp [unionProd_toSSet_iso]
  apply Limits.pushout.hom_ext
  all_goals aesop

lemma innerAnodyne_eq_T : innerAnodyne.{u} = (saturation.{u} bdryHornPushouts) := by
  apply le_antisymm
  all_goals rw [innerAnodyne_eq, ← WeaklySaturated.le_iff]
  · intro _ _ f ⟨h0, hn⟩
    exact .retract (hornRetract _ h0 hn) (monomorphisms_le_S _ (.infer_property _))
  · intro _ _ f ⟨n⟩
    rw [← innerAnodyne_eq]
    exact (arrow_mk_iso_iff _ arrow_unionProd_iso).2 unionProd_ι_innerAnodyne

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
