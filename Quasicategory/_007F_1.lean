import Quasicategory.Monomorphism
import Quasicategory.PushoutProduct.Basic
--import Quasicategory.PushoutProduct.TransfiniteComposition

/-!

The first half of the proof of `007F`.

-/

universe w u

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory PushoutProduct

-- T = saturation bdryHornPushouts
-- S is the class of all morphisms `i : A → B` such that the pushout product with `Λ[2, 1] ↪ Δ[2]` is in T
def S : MorphismProperty SSet := fun _ _ i ↦
  (saturation.{u} bdryHornPushouts) (Λ[2, 1].ι ◫ i)

instance S.IsStableUnderCobaseChange : S.IsStableUnderCobaseChange where
  of_isPushout h hg := .pushout (leftBifunctor_obj_map_preserves_pushouts' Λ[2, 1].ι h) hg

instance S.IsStableUnderRetracts : S.IsStableUnderRetracts where
  of_retract h hg := .retract (Retract.map h (leftFunctor Λ[2, 1].ι)) hg

open Limits in
instance S.IsStableUnderTransfiniteComposition : IsStableUnderTransfiniteComposition.{w} S.{w} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    rw [isStableUnderTransfiniteCompositionOfShape_iff]
    intro X Y f ⟨hf⟩
    refine WeaklySaturatedClass.transfinite J _ ?_ ?_
    · sorry
    · sorry

set_option maxHeartbeats 800000 in
open Limits in
noncomputable
def F'_isoBot {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : SSet} {f : X ⟶ Y} (hf : S.TransfiniteCompositionOfShape J f) :
      (F' hf.F (Limits.Cocone.mk _ hf.incl)).obj ⊥ ≅ (PushoutProduct.pt f Λ[2, 1].ι) where
  hom := by
    apply pushout.desc ((Δ[2] ◁ hf.isoBot.hom) ≫ (pushout.inl _ _)) (pushout.inr _ _)
    simp [← whisker_exchange_assoc, pushout.condition]
    have := congr_arg (MonoidalCategory.whiskerLeft Λ[2, 1].toSSet) hf.fac
    simp_rw [← this]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc]
  inv := by
    apply pushout.desc (((Δ[2] ◁ hf.isoBot.inv) ≫ (pushout.inl _ _))) (pushout.inr _ _)
    dsimp
    rw [← whisker_exchange_assoc, pushout.condition, ← MonoidalCategory.whiskerLeft_comp_assoc]
    have := hf.fac.symm
    simp_rw [this]
  inv_hom_id := by
    apply pushout.hom_ext
    · simp
    · simp
  hom_inv_id := by
    apply pushout.hom_ext
    · simp
    · simp

open Limits in
instance Sskj : IsStableUnderTransfiniteComposition.{w} S.{w} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    rw [isStableUnderTransfiniteCompositionOfShape_iff]
    intro X Y f ⟨hf⟩
    refine .transfinite J _ ?_ ?_
    · refine {
      F := F' hf.F (Limits.Cocone.mk _ hf.incl)
      isoBot := F'_isoBot hf
      isWellOrderContinuous := F'_woc hf.F _
      incl := descFunctor hf.incl Λ[2, 1].ι
      isColimit := c'_IsColimit hf.F _ hf.isColimit
      fac := by
        apply pushout.hom_ext
        · simp [descFunctor, ← MonoidalCategory.whiskerLeft_comp, TransfiniteCompositionOfShape.fac, F'_isoBot]
        · simp [descFunctor, F'_isoBot] }
    · intro j hj
      exact .pushout (newPushoutIsPushout hf.F (Limits.Cocone.mk _ hf.incl) j) (hf.map_mem j hj)

noncomputable
def c₁' {J : Type*} {X₁ X₂ : Discrete J ⥤ SSet}
    {c₁ : Limits.Cocone X₁} (c₂ : Limits.Cocone X₂)
    (h₁ : Limits.IsColimit c₁) (f : X₁ ⟶ X₂) :
    Limits.Cocone (natTransLeftFunctor f Λ[2, 1].ι) := {
      pt := PushoutProduct.pt (h₁.desc { pt := c₂.pt, ι := f ≫ c₂.ι }) Λ[2, 1].ι
      ι := {
        app j := by
          apply Limits.pushout.desc
            (Δ[2] ◁ c₁.ι.app j ≫ (Limits.pushout.inl _ _))
            ((Λ[2, 1] : SSet) ◁ c₂.ι.app j ≫ (Limits.pushout.inr _ _))
          have := h₁.fac { pt := c₂.pt, ι := f ≫ c₂.ι } j
          dsimp at this
          simp
          rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← this, MonoidalCategory.whiskerLeft_comp_assoc,
            ← Limits.pushout.condition, whisker_exchange_assoc]
        naturality := by
          intro j k s
          dsimp
          apply Limits.pushout.hom_ext
          · simp
            rw [← MonoidalCategory.whiskerLeft_comp_assoc, c₁.ι.naturality]
            rfl
          · simp
            rw [← MonoidalCategory.whiskerLeft_comp_assoc, c₂.ι.naturality]
            rfl } }

set_option maxHeartbeats 800000 in
open Limits in
noncomputable
def c₁'_isColimit {J : Type*} {X₁ X₂ : Discrete J ⥤ SSet}
    {c₁ : Cocone X₁} (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f : X₁ ⟶ X₂) : IsColimit (c₁' c₂ h₁ f) where
  desc s := by
    dsimp [c₁']
    let s₁ := Cocone.mk s.pt (inlDescFunctor f Λ[2, 1].ι ≫ s.ι)
    let s₂ := Cocone.mk s.pt (inrDescFunctor f Λ[2, 1].ι ≫ s.ι)
    let hs₁ := (isColimitOfPreserves (tensorLeft Δ[2]) h₁)
    let hs₂ := (isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) h₂)
    let hs₁' := (isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) h₁)
    apply pushout.desc (hs₁.desc s₁) (hs₂.desc s₂)
    apply hs₁'.hom_ext
    intro j
    let hs₁_fac := hs₁.fac s₁ j
    let hs₂_fac := hs₂.fac s₂ j
    simp [s₁, s₂, hs₁, hs₂] at hs₁_fac hs₂_fac ⊢
    rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hs₁_fac]
    simp [hs₂_fac, pushout.condition_assoc]
  fac s j := by
    simp [c₁']
    apply pushout.hom_ext
    · simp
      exact (isColimitOfPreserves (tensorLeft Δ[2]) h₁).fac { pt := s.pt, ι := inlDescFunctor f Λ[2, 1].ι ≫ s.ι } j
    · let s₂ := Cocone.mk s.pt (inrDescFunctor f Λ[2, 1].ι ≫ s.ι)
      let hs₂ := (isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) h₂)
      let hs₂_fac := hs₂.fac s₂ j
      simp [s₂] at hs₂_fac ⊢
      rw [hs₂_fac]
  uniq s m hj := by
    simp
    apply pushout.hom_ext
    · let s₁ := Cocone.mk s.pt (inlDescFunctor f Λ[2, 1].ι ≫ s.ι)
      let hs₁ := (isColimitOfPreserves (tensorLeft Δ[2]) h₁)
      apply hs₁.hom_ext
      intro j
      simp
      have := hs₁.fac s₁ j
      dsimp [s₁, c₁'] at this
      rw [this, ← hj j]
      simp [c₁']
    · let s₂ := Cocone.mk s.pt (inrDescFunctor f Λ[2, 1].ι ≫ s.ι)
      let hs₂ := (isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) h₂)
      apply hs₂.hom_ext
      intro j
      simp
      have := hs₂.fac s₂ j
      dsimp [s₂] at this
      rw [this, ← hj j]
      simp [c₁']

set_option maxHeartbeats 400000 in
instance S.IsStableUnderCoproducts : IsStableUnderCoproducts.{w} S.{w} where
  isStableUnderCoproductsOfShape J := by
    refine (isStableUnderColimitsOfShape_iff_colimitsOfShape_le S (Discrete J)).mpr ?_
    intro X Y f hf
    cases hf with
    | mk X₁ X₂ c₁ c₂ h₁ h₂ f hf =>
    dsimp only [S]
    dsimp only [MorphismProperty.functorCategory, S] at hf
    apply (WeaklySaturated.IsStableUnderCoproducts.isStableUnderCoproductsOfShape J).colimitsOfShape_le
    let α := h₁.desc { pt := c₂.pt, ι := f ≫ c₂.ι }
    let f' := descFunctor f Λ[2, 1].ι
    let c₁' := c₁' c₂ h₁ f
    let h₁' : Limits.IsColimit c₁' := c₁'_isColimit c₂ h₁ h₂ f
    let c₂' := (tensorLeft Δ[2]).mapCocone c₂
    let h₂' : Limits.IsColimit c₂' := Limits.isColimitOfPreserves (tensorLeft Δ[2]) h₂
    convert colimitsOfShape.mk (natTransLeftFunctor f Λ[2, 1].ι) (X₂ ⋙ tensorLeft Δ[2]) c₁' c₂' h₁' h₂' f' hf
    convert h₁'.uniq _ _ _
    · rfl
    · rfl
    · intro j
      dsimp only [c₁', SSet.c₁', c₂', f', descFunctor, tensorLeft, curriedTensor,
        Functor.mapCocone]
      aesop

-- S is weakly saturated because T is
instance S.WeaklySaturated : WeaklySaturated.{w} S.{w} where
  IsStableUnderCobaseChange := by infer_instance
  IsStableUnderRetracts := by infer_instance
  IsStableUnderCoproducts := by infer_instance
  IsStableUnderTransfiniteComposition := by infer_instance

lemma bdryInclusions_le_S : bdryInclusions ≤ S := fun _ _ _ ⟨_⟩ ↦ .of _ (.mk _)

lemma monomorphisms_le_S : monomorphisms SSet.{u} ≤ S.{u} := by
  rw [monomorphism_eq_saturation_bdryInclusions, ← WeaklySaturated.le_iff]
  exact bdryInclusions_le_S

variable {n : ℕ} (i : Fin (n + 1))

-- [n] ⟶ [2] by j ↦
-- 0 if j < i
-- 1 if j = i
-- 2 if j > i
def s_aux : Fin (n + 1) →o Fin 3 where
  toFun j :=   if j < i then 0 else if j = i then 1 else 2
  monotone' j k h := by
    simp
    split
    · omega
    · split
      all_goals
      · split
        · omega
        · split
          all_goals omega

def standard_map : Δ[n] ⟶ Δ[2] :=
  stdSimplex.map (SimplexCategory.mkHom (s_aux i))

-- the above map restricted to the horn
def horn_map : (Λ[n, i] : SSet) ⟶ Δ[2] :=
  Λ[n, i].ι ≫ (standard_map i)

-- on vertices j maps to
-- (j, 0) if j < i
-- (j, 1) if j = i
-- (j, 2) if j > i
def s : Δ[n] ⟶ Δ[2] ⊗ Δ[n] :=
  FunctorToTypes.prod.lift (standard_map i) (𝟙 _)

def s_restricted :
    (Λ[n, i] : SSet) ⟶ Δ[2] ⊗ Λ[n, i] :=
  FunctorToTypes.prod.lift (horn_map i) (𝟙 _)

noncomputable
def horn_to_pushout :
    (Λ[n, i] : SSet) ⟶ (PushoutProduct.pt Λ[n, i].ι Λ[2, 1].ι) :=
  s_restricted i ≫ (Limits.pushout.inl (Λ[2, 1].ι ▷ Λ[n, i]) ((Λ[2, 1] : SSet) ◁ Λ[n, i].ι))

lemma leftSqCommAux : s_restricted i ≫ Δ[2] ◁ Λ[n, i].ι = Λ[n, i].ι ≫ s i := rfl

lemma leftSqComm :
    horn_to_pushout i ≫ Λ[n, i].ι ◫ Λ[2, 1].ι = Λ[n, i].ι ≫ s i := by
  rw [← leftSqCommAux]
  dsimp [horn_to_pushout, pushoutProduct]
  rw [Category.assoc, Limits.pushout.inl_desc]

def r_aux : Fin 3 × Fin (n + 1) →o Fin (n + 1) where
  toFun := fun ⟨k, j⟩ ↦ if (j < i ∧ k = 0) ∨ (j > i ∧ k = 2) then j else i
  monotone' := by
    intro ⟨k, j⟩ ⟨k', j'⟩ ⟨(hk : k ≤ k'), (hj : j ≤ j')⟩
    dsimp
    split
    all_goals
    · split
      all_goals omega

open stdSimplex SimplexCategory in
def map_mk_from_prod {n m k : ℕ} (f : Fin (n + 1) × Fin (m + 1) →o Fin (k + 1)) : Δ[n] ⊗ Δ[m] ⟶ Δ[k] := by
  refine ⟨fun x ⟨c, d⟩ ↦ ⟨SimplexCategory.mkHom ⟨fun a ↦ f ((stdSimplex.asOrderHom c) a, (stdSimplex.asOrderHom d) a), ?_⟩⟩, ?_⟩
  · intro j k hjk
    exact f.monotone ⟨(stdSimplex.asOrderHom c).monotone hjk, (stdSimplex.asOrderHom d).monotone hjk⟩
  · aesop

-- on vertices j k map to
-- j if (j < i) ∧ (k = 0)
-- j if (j > i) ∧ (k = 2)
-- i if (j = i) ∨ (k = 1)
def r : Δ[2] ⊗ Δ[n] ⟶ Δ[n] := map_mk_from_prod (r_aux i)

variable (h0 : 0 < i) (hn : i < Fin.last n)

-- r restricted along Λ[2, 1]
noncomputable
def r_restrict_horn_2 : (Λ[2, 1] : SSet) ⊗ Δ[n] ⟶ Λ[n, i] where
  app k := by
    intro ⟨⟨x, hx⟩, y⟩
    refine ⟨(((horn 2 1).ι) ▷ Δ[n] ≫ r i).app k ⟨⟨x, hx⟩, y⟩, ?_⟩
    rw [mem_horn_iff, Set.ne_univ_iff_exists_not_mem] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    fin_cases a
    · simp at ha ⊢
      use 0
      refine ⟨Fin.ne_of_lt h0, fun j h ↦ ?_⟩
      change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at h
      split at h
      all_goals aesop
    · aesop
    · simp at ha ⊢
      use Fin.last n
      refine ⟨Fin.ne_of_gt hn, fun j h ↦ ?_⟩
      change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at h
      split at h
      · next h' =>
        simp_all
        omega
      · omega

-- r restricted along (Λ[n, i] : SSet)
noncomputable
def r_restrict_horn_n : Δ[2] ⊗ Λ[n, i] ⟶ Λ[n, i] where
  app k := by
    intro ⟨x, ⟨y, hy⟩⟩
    refine ⟨(Δ[2] ◁ Λ[n, i].ι ≫ r i).app k ⟨x, ⟨y, hy⟩⟩, ?_⟩
    rw [mem_horn_iff, Set.ne_univ_iff_exists_not_mem] at hy ⊢
    obtain ⟨a, ha⟩ := hy
    use a
    intro h
    simp at h ha
    obtain ⟨ha₁, ha₂⟩ := ha
    cases h
    · omega
    · next h =>
      obtain ⟨j, hj⟩ := h
      apply ha₂ j
      change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at hj
      aesop

open stdSimplex SimplexCategory in
noncomputable
def pushout_to_horn : (PushoutProduct.pt Λ[n, i].ι Λ[2, 1].ι) ⟶ Λ[n, i] :=
  Limits.pushout.desc (r_restrict_horn_n i) (r_restrict_horn_2 i h0 hn) rfl

lemma rightSqComm : pushout_to_horn i h0 hn ≫ (Λ[n, i]).ι = (Λ[n, i].ι ◫ Λ[2, 1].ι) ≫ r i := by
  dsimp [pushout_to_horn, pushoutProduct]
  apply Limits.pushout.hom_ext; all_goals aesop

lemma r_aux_comp_s_aux_prod_id :
    OrderHom.comp (r_aux i) ((s_aux i).prod (OrderHom.id)) = OrderHom.id := by
  ext
  simp [s_aux, r_aux]
  split
  · aesop
  · split
    · aesop
    · split
      · aesop
      · exfalso
        omega

lemma r_comp_s : s i ≫ r i = 𝟙 Δ[n] := by
  change stdSimplex.map (SimplexCategory.mkHom (OrderHom.comp (r_aux i) ((s_aux i).prod (OrderHom.id)))) = _
  rw [r_aux_comp_s_aux_prod_id]
  simp

lemma restricted_r_comp_s : horn_to_pushout i ≫ pushout_to_horn i h0 hn = 𝟙 (Λ[n, i] : SSet) := by
  dsimp [horn_to_pushout, pushout_to_horn]
  rw [Category.assoc, Limits.pushout.inl_desc]
  ext k ⟨x, hx⟩
  change (r_restrict_horn_n i).app k ((horn_map i).app k ⟨x, hx⟩, ⟨x, hx⟩) = ⟨x, hx⟩
  simp [r_restrict_horn_n]
  have := congr_fun (congr_app (r_comp_s i) k) x
  aesop

noncomputable
instance hornRetract : RetractArrow Λ[n, i].ι (Λ[n, i].ι ◫ Λ[2, 1].ι) where
  i := {
    left := horn_to_pushout i
    right := s i
    w := leftSqComm i
  }
  r := {
    left := pushout_to_horn i h0 hn
    right := r i
    w := rightSqComm i h0 hn
  }
  retract := Arrow.hom_ext _ _ (restricted_r_comp_s i h0 hn) (r_comp_s i)
