import Quasicategory._007F_1
import Quasicategory._007F.Tau
import Quasicategory._007F.Sigma

/-!

The second half of the proof of `007F`, which is much more technical.

-/

universe w v u

open CategoryTheory MorphismProperty Simplicial SSet PushoutProduct MonoidalCategory Subcomplex

variable {n : ℕ}

noncomputable
def image_arrow_iso_of_mono {X Y : SSet} (f : X ⟶ Y) [Mono f] (A : Subcomplex X) :
    Arrow.mk (Subcomplex.homOfLE (image_le_range A f)) ≅ Arrow.mk A.ι := by
  let h := IsIso.out (f := (toRangeSubcomplex (A.ι ≫ f)))
  let ⟨h₁, h₂⟩ := h.choose_spec
  refine Arrow.isoMk ((isoOfEq (image_eq_range A f)) ≪≫ (asIso (toRangeSubcomplex (A.ι ≫ f))).symm)
    (asIso (toRangeSubcomplex f)).symm ?_
  simp
  change _ ≫ h.choose ≫ _ ≫ _ = _
  ext n ⟨y, ⟨x, ⟨hx₁, hx₂⟩⟩⟩
  have := congr_fun (congr_app h₁ n) ⟨x, hx₁⟩
  simp [Subcomplex.homOfLE, Subpresheaf.homOfLe, toRangeSubcomplex,
    Subpresheaf.toRange, Subpresheaf.lift, ← hx₂] at this ⊢
  aesop

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

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C) [W.IsMultiplicative]

-- go from `⟨b, a⟩ --> ⟨b, a'⟩` for `a ≤ a'`
lemma map_mem_of_sigma' {n : ℕ} (F : (Σₗ (b : Fin (n + 1)), Fin b.succ) ⥤ C)
    (hF : ∀ (i : Σₗ (b : Fin (n + 1)), Fin b.succ), W (F.map (homOfLE (Sigma.Lex.le_succ i))))
    {b : Fin (n + 1)} (a a' : Fin b.succ) (h : a ≤ a') :
    W (F.map (homOfLE (show ⟨b, a⟩ ≤ ⟨b, a'⟩ by right; simpa))) := by
  obtain ⟨b, hb⟩ := b
  obtain ⟨a, ha⟩ := a
  obtain ⟨a', ha'⟩ := a'
  induction a' with
  | zero =>
    simp only [Fin.le_iff_val_le_val, le_zero_iff] at h
    subst h
    simp only [homOfLE_refl, Functor.map_id]
    apply id_mem
  | succ a' h' =>
  cases lt_or_eq_of_le h
  · next h'' =>
    have one := h' (by omega) (by simp [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h'' ⊢; omega)
    have two := hF ⟨⟨b, hb⟩, ⟨a', by omega⟩⟩
    have eq := Sigma.Lex.Fin.succ_eq_of_snd_lt_fst ⟨b, hb⟩ ⟨a', by omega⟩ (by simpa [Fin.lt_iff_val_lt_val] using ha')
    change _ = (⟨⟨b, hb⟩, ⟨a' + 1, ha'⟩⟩ : (Σₗ (b : Fin (n + 1)), Fin b.succ)) at eq
    convert W.comp_mem _ _ one two
    exact eq.symm
    rw [← F.map_comp, homOfLE_comp]
    congr!
    exact eq.symm
  · next h'' =>
    simp at h''
    subst h''
    simp only [homOfLE_refl, Functor.map_id]
    apply id_mem

lemma map_mem_of_sigma {n : ℕ} (F : (Σₗ (b : Fin (n + 1)), Fin b.succ) ⥤ C)
    (hF : ∀ (i : Σₗ (b : Fin (n + 1)), Fin b.succ), W (F.map (homOfLE (Sigma.Lex.le_succ i))))
    {i j : Σₗ (b : Fin (n + 1)), Fin b.succ} (f : i ⟶ j) :
    W (F.map f) := by
  have h : i ≤ j := leOfHom f
  obtain ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ := i
  obtain ⟨⟨b', hb'⟩, ⟨a', ha'⟩⟩ := j
  have hbb' : b ≤ b' := by
    cases h
    · next h => exact h.le
    · next => exact le_rfl
  obtain ⟨k, hk⟩ := Nat.le.dest hbb'
  induction k with
  | zero =>
    subst hk
    change W (F.map (homOfLE _))
    apply W.map_mem_of_sigma' F hF
    simpa [Sigma.Lex.le_def] using h
  | succ k hk =>
    cases (lt_or_eq_of_le hbb')
    · next hbb' =>
      have ba_bb : (toLex ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ : Σₗ (b : Fin (n + 1)), Fin b.succ) ≤ toLex ⟨⟨b, hb⟩, ⟨b, Nat.lt_add_one b⟩⟩ := by
        simp at ha ⊢
        right
        simp
        omega
      have b'0_b'a' : (toLex ⟨⟨b', hb'⟩, ⟨0, Nat.zero_lt_succ b'⟩⟩ : Σₗ (b : Fin (n + 1)), Fin b.succ) ≤ toLex ⟨⟨b', hb'⟩, ⟨a', ha'⟩⟩ := by
        right
        simp
      have bb_b'0 : (toLex ⟨⟨b, hb⟩, ⟨b, Nat.lt_add_one b⟩⟩ : Σₗ (b : Fin (n + 1)), Fin b.succ) ≤ toLex ⟨⟨b', hb'⟩, ⟨0, Nat.zero_lt_succ b'⟩⟩ := by
        left
        simpa
      suffices W (F.map (homOfLE bb_b'0)) by
        have := (W.comp_mem (F.map <| homOfLE ba_bb) (F.map (homOfLE bb_b'0)) ?_ this)
        rw [← F.map_comp, homOfLE_comp] at this
        have := W.comp_mem _ (F.map <| homOfLE b'0_b'a') (this) ?_
        rw [← F.map_comp, homOfLE_comp] at this
        exact this
        · apply W.map_mem_of_sigma' F hF
          simp
        · apply W.map_mem_of_sigma' F hF
          simp at ha ⊢
          omega
      subst hk
      let P (k : ℕ) := ∀ (b : ℕ) (hk : 0 < k) (hbk : b + k < n + 1),
        W (F.map (homOfLE (show toLex ⟨⟨b, Nat.lt_of_add_right_lt hbk⟩, ⟨b, Nat.lt_add_one _⟩⟩ ≤ toLex ⟨⟨b + k, hbk⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ by left; simpa)))
      suffices ∀ (k : ℕ), P k by
        exact this (k + 1) b (Nat.zero_lt_succ _) (by omega)
      intro k b hk hbk
      induction k with
      | zero => omega
      | succ k hk =>
        induction k with
        | zero =>
          have goal := hF (toLex ⟨⟨b, Nat.lt_of_add_right_lt hbk⟩, ⟨b, Nat.lt_add_one _⟩⟩)
          convert (config := .unfoldSameFun) goal
          all_goals exact (Sigma.Lex.Fin.succ_eq_of_lt_last ⟨b, Nat.lt_of_add_right_lt hbk⟩ (by simp [Fin.lt_iff_val_lt_val]; omega)).symm
        | succ k hk' =>
          rename_i hk''
          have goal := hk'' (by omega) (by omega)
          have := @homOfLE_comp (Σₗ (b : Fin (n + 1)), Fin ↑b.succ) _ ⟨⟨b, Nat.lt_of_add_right_lt hbk⟩, ⟨b, Nat.lt_add_one _⟩⟩ ⟨⟨b + k + 1, by omega⟩, ⟨0, by simp⟩⟩ ⟨⟨b + (k + 1 + 1), hbk⟩, ⟨0, by simp⟩⟩ (by left; simp; omega) (by left; simp; omega)
          rw [← this, F.map_comp]
          apply comp_mem
          · exact goal
          · have := @homOfLE_comp (Σₗ (b : Fin (n + 1)), Fin ↑b.succ) _ ⟨⟨b + k + 1, by omega⟩, ⟨0, by simp⟩⟩ ⟨⟨b + k + 1, by omega⟩, ⟨b + k + 1, by simp⟩⟩ ⟨⟨b + (k + 1 + 1), hbk⟩, ⟨0, by simp⟩⟩ (by right; simp) (by left; simp; omega)
            rw [← this, F.map_comp]
            apply comp_mem
            · apply W.map_mem_of_sigma' F hF
              simp
            · have goal := hF ⟨⟨b + k + 1, by omega⟩, ⟨b + k + 1, by simp⟩⟩
              convert (config := .unfoldSameFun) goal
              all_goals exact (Sigma.Lex.Fin.succ_eq_of_lt_last ⟨b + k + 1, by omega⟩ (by simp [Fin.lt_iff_val_lt_val]; omega)).symm
    · next hbb' =>
      subst hbb'
      apply W.map_mem_of_sigma' F hF
      omega

end CategoryTheory.MorphismProperty

lemma τ.filtration_last_innerAnodyne : innerHornInclusions.saturation
    (Subcomplex.homOfLE (filtration_monotone (Sigma.Lex.le_succ ⟨Fin.last (n + 1), Fin.last (n + 1)⟩))) := by
  refine (arrow_mk_iso_iff _ ?_).2 <| id_mem innerHornInclusions.saturation (filtration ⟨Fin.last (n + 1), Fin.last (n + 1)⟩).toSSet
  exact Arrow.isoMk (isoOfEq rfl) (isoOfEq (congrArg filtration Sigma.Lex.Fin.succ_last_eq_last))

lemma σ.filtration_last_innerAnodyne : innerHornInclusions.saturation
    (Subcomplex.homOfLE (filtration_monotone (Sigma.Lex.le_succ ⟨Fin.last n, Fin.last n⟩))) := by
  refine (arrow_mk_iso_iff _ ?_).2 <| id_mem innerHornInclusions.saturation (filtration ⟨Fin.last n, Fin.last n⟩).toSSet
  exact Arrow.isoMk (isoOfEq rfl) (isoOfEq (congrArg filtration Sigma.Lex.Fin.succ_last_eq_last))

open Subcomplex in
lemma σ.filtration_innerAnodyne {i j : Σₗ (b : Fin (n + 1)), Fin b.succ} (h : i ≤ j) :
    innerHornInclusions.saturation (homOfLE (filtration_monotone h)) := by
  refine innerHornInclusions.saturation.map_mem_of_sigma
    (filtration_monotone.functor ⋙ Subcomplex.forget _) ?_ (homOfLE h)
  dsimp only [Fin.val_succ, Functor.comp_obj, Monotone.functor_obj, forget_obj,
    Fin.succ_mk, Fin.zero_eta, homOfLE_leOfHom, Functor.comp_map, forget_map]
  intro i
  induction n with
  | zero =>
    have : i = ⊥ := by
      obtain ⟨b, a⟩ := i
      rw [Sigma.Lex.bot_eq_zero]
      have := Fin.eq_zero b
      subst this
      have := Fin.eq_zero a
      subst this
      rfl
    rw [Sigma.Lex.bot_eq_zero] at this
    subst this
    dsimp
    apply id_mem
  | succ n _ =>
    by_cases hn : i < ⊤
    · have σsq := σ.filtrationPushout_intermediate i hn
      rw [σ.innerHornImage, σ.subcomplex, ofSimplex_eq_range, σ.s] at σsq
      refine of_isPushout (Subcomplex.Sq.isPushout σsq).flip
        ((arrow_mk_iso_iff _ (image_arrow_iso_of_mono _ _)).2
          (.of _ (.mk (Nat.lt_of_sub_eq_succ rfl) (?_))))
      · obtain ⟨b, a⟩ := i
        rw [Fin.lt_iff_val_lt_val]
        simp only [Fin.val_succ, Fin.succ_mk, Fin.zero_eta, Fin.castSucc_mk,
          Fin.val_last, add_lt_add_iff_right]
        omega
    · simp at hn
      rw [Sigma.Lex.top_eq_last] at hn
      subst hn
      exact filtration_last_innerAnodyne

open Subcomplex in
lemma τ.filtration_innerAnodyne {i j : Σₗ (b : Fin (n + 2)), Fin b.succ} (h : i ≤ j) :
    innerHornInclusions.saturation (homOfLE (filtration_monotone h)) := by
  refine innerHornInclusions.saturation.map_mem_of_sigma
    (filtration_monotone.functor ⋙ Subcomplex.forget _) ?_ (homOfLE h)
  dsimp only [Fin.val_succ, Functor.comp_obj, Monotone.functor_obj, Subcomplex.forget_obj,
    Fin.succ_mk, Fin.zero_eta, homOfLE_leOfHom, Functor.comp_map, forget_map]
  intro i
  by_cases hn : i < ⊤
  · have τsq := τ.filtrationPushout_intermediate i hn
    rw [τ.innerHornImage, τ.subcomplex, ofSimplex_eq_range, τ.t] at τsq
    refine of_isPushout (Subcomplex.Sq.isPushout τsq).flip
      ((arrow_mk_iso_iff _ (image_arrow_iso_of_mono _ _)).2
        (.of _ (.mk (Nat.lt_of_sub_eq_succ rfl) (?_))))
    · obtain ⟨b, a⟩ := i
      rw [Fin.lt_iff_val_lt_val]
      simp only [Fin.val_succ, Fin.succ_mk, Fin.zero_eta, Fin.castSucc_mk,
        Fin.val_last, add_lt_add_iff_right]
      omega
  · simp at hn
    rw [Sigma.Lex.top_eq_last] at hn
    subst hn
    exact filtration_last_innerAnodyne

open Subcomplex in
lemma unionProd_ι_innerAnodyne : innerAnodyne.{u} (∂Δ[n].unionProd Λ[2, 1]).ι := by
  rw [innerAnodyne_eq_saturation_innerHornInclusions]
  induction n with
  | zero =>
    rw [boundary_zero]
    exact (arrow_mk_iso_iff _ zero_unionProd_arrowIso).2
      (.of _ (.mk Fin.zero_lt_one Fin.one_lt_last))
  | succ n _ =>
    let σsq := (σ.filtrationPushout_zero.{u} (n := n))
    let τsq := (τ.filtrationPushout_zero.{u} (n := n))
    rw [Sigma.Lex.bot_eq_zero, σ.subcomplex, ofSimplex_eq_range] at σsq
    rw [Sigma.Lex.bot_eq_zero, τ.subcomplex, ofSimplex_eq_range] at τsq
    change innerHornInclusions.saturation
        ((homOfLE σ.filtrationPushout_zero.{u}.le₃₄) ≫
        (homOfLE (σ.filtration_monotone bot_le)) ≫
        (homOfLE τ.filtrationPushout_zero.{u}.le₃₄) ≫
        (homOfLE (τ.filtration_monotone bot_le)) ≫
        (isoOfEq τ.filtration_last).hom ≫
        (topIso _).hom)
    refine comp_mem _ _ _ ?_ <|
      comp_mem _ _ _ (σ.filtration_innerAnodyne.{u} bot_le) <|
      comp_mem _ _ _ ?_ <|
      comp_mem _ _ _ (τ.filtration_innerAnodyne.{u} bot_le) <|
      comp_mem _ _ _ (of_isIso _ _) (of_isIso _ _)
    · refine of_isPushout σsq.isPushout.flip
        ((arrow_mk_iso_iff _ (image_arrow_iso_of_mono (σ.s ⊥) Λ[n + 2, 1])).2
          (.of _ (.mk Fin.zero_lt_one Fin.one_lt_last)))
    · exact of_isPushout τsq.isPushout.flip
        ((arrow_mk_iso_iff _ (image_arrow_iso_of_mono _ _)).2
          (.of _ (.mk Fin.zero_lt_one Fin.one_lt_last)))

noncomputable
def arrow_unionProd_iso : Arrow.mk (Λ[2, 1].ι □ ∂Δ[n].ι) ≅ Arrow.mk (∂Δ[n].unionProd Λ[2, 1]).ι := by
  refine Arrow.isoMk
    ((IsPushout.isoPushout (unionProd.isPushout _ _)).symm ≪≫ unionProd.symmIso _ _) (β_ Δ[2] Δ[n]) ?_
  apply Limits.pushout.hom_ext
  all_goals
  · simp [Functor.PushoutObjObj.ι]
    aesop

lemma innerAnodyne_eq_T : innerAnodyne.{u} = (saturation.{u} bdryHornPushouts) := by
  apply le_antisymm
  all_goals rw [innerAnodyne_eq_saturation_innerHornInclusions, ← WeaklySaturated.le_iff]
  · intro _ _ _ ⟨h0, hn⟩
    exact .retract (hornRetract _ h0 hn) (monomorphisms_le_S _ (.infer_property _))
  · intro _ _ _ ⟨_⟩
    rw [← innerAnodyne_eq_saturation_innerHornInclusions]
    exact (arrow_mk_iso_iff _ arrow_unionProd_iso).2 unionProd_ι_innerAnodyne

-- `007F` (a)
lemma monoPushout_innerAnodyne {A B : SSet} (i : A ⟶ B) [Mono i] :
    innerAnodyne (Λ[2, 1].ι □ i) := by
  rw [innerAnodyne_eq_T]
  exact monomorphisms_le_S i (.infer_property _)

-- `007F` (b)
lemma contains_innerAnodyne_iff_contains_pushout_maps
    (S : MorphismProperty SSet) [WeaklySaturated.{u} S] :
    (bdryHornPushouts ≤ S) ↔ (innerAnodyne.{u} ≤ S) := by
  constructor
  · simp [innerAnodyne_eq_T, ← WeaklySaturated.le_iff]
  · exact fun h _ _ _ ⟨m⟩ ↦ h _ (monoPushout_innerAnodyne ∂Δ[m].ι)
