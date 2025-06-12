import Quasicategory.Monomorphism
import Quasicategory.PushoutProduct.Retract
import Quasicategory.PushoutProduct.Pushout
import Quasicategory.PushoutProduct.TransfiniteComposition

/-!

The first half of the proof of `007F`.

# TODO

Show `S` is stable under transfinite composition.

-/

universe w v u

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory PushoutProduct

-- T = WeaklySaturatedOf bdryPushoutClass
-- S is the class of all morphisms `i : A → B` such that the pushout product with `Λ[2, 1] ↪ Δ[2]` is in T
def S : MorphismProperty SSet := fun _ _ i ↦
    (WeaklySaturatedClassOf.{w} bdryPushoutClass) (i ◫ (horn 2 1).ι)

-- S is weakly saturated because T is
set_option maxHeartbeats 800000 in
open Limits in
instance S.WeaklySaturated : WeaklySaturated.{w} S.{w} where
  IsStableUnderCobaseChange := ⟨by
    intro _ _ _ _ g _ f _ h hg
    exact (bdryPushoutClass).of_is.IsStableUnderCobaseChange.of_isPushout (pushoutCommSq_IsPushout h) hg⟩
  IsStableUnderRetracts := ⟨by
    intro _ _ _ _ f g h hg
    exact (bdryPushoutClass).of_is.IsStableUnderRetracts.of_retract (pushoutProduct.RetractArrow h) hg⟩
  IsStableUnderTransfiniteComposition := {
    isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := {
      le X Y f hf := by
        letI := ((bdryPushoutClass).of_is.IsStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape J)
        obtain hf := hf.some
        dsimp [S]
        have := c'_IsColimit hf.F _ hf.isColimit
        dsimp [c'] at this
        refine WeaklySaturatedOf.transfinite J _ ?_ ?_
        · refine {
          F := F' hf.F (Limits.Cocone.mk _ hf.incl)
          isoBot := by
            simp [F']
            refine {
              hom := by
                refine Limits.pushout.desc ((Δ[2] ◁ hf.isoBot.hom) ≫ (inl _ _)) (inr _ _) ?_
                rw [← Category.assoc, ← @whisker_exchange, Category.assoc]
                dsimp
                rw [pushout.condition]
                simp_rw [← hf.fac]
                rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
              inv := by
                refine Limits.pushout.desc (((Δ[2] ◁ hf.isoBot.inv) ≫ (inl _ _))) (inr _ _) ?_
                rw [← Category.assoc, ← @whisker_exchange, Category.assoc]
                dsimp
                rw [pushout.condition, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
                simp_rw [← hf.fac]
              inv_hom_id := pushout.hom_ext (by simp) (by simp)
              hom_inv_id := pushout.hom_ext (by simp) (by simp)
            }
          isWellOrderContinuous := F'_woc hf.F _
          incl := descFunctor hf.incl Λ[2, 1].ι
          isColimit := this
          fac := by
            apply pushout.hom_ext
            · simp [descFunctor, ← MonoidalCategory.whiskerLeft_comp, hf.fac]
            · simp [descFunctor]
        }
        · intro j hj
          exact WeaklySaturatedOf.pushout (newPushoutIsPushout hf.F (Limits.Cocone.mk _ hf.incl) j) (hf.map_mem j hj)
        }}
        /-
        induction hf with
        | mk F hF c hc =>
        apply bdryPushoutClass.WeaklySaturatedClassOf.mem_of_transfinite_composition ?_ (c'_IsColimit F c hc)
        · intro j hj
          exact WeaklySaturatedOf.pushout (newPushoutIsPushout F c j) (hF j hj) }}
        -/

lemma BoundaryInclusions_le_S : BoundaryInclusions ≤ S := fun _ _ _ h ↦ by
  induction h with | mk =>
  apply WeaklySaturatedOf.of
  apply bdryPushout.mk

lemma monomorphisms_le_S : monomorphisms SSet.{u} ≤ S.{u} := by
  rw [mono_eq_bdryInclusions.{u}]
  apply minimalWeaklySaturated _ _ BoundaryInclusions_le_S S.WeaklySaturated

-- [n] ⟶ [2] by j ↦
-- 0 if j < i
-- 1 if j = i
-- 2 if j > i
def s_aux (i : Fin (n + 1)) : Fin (n + 1) →o Fin 3 where
  toFun j :=   if _ : (j : ℕ) < i then 0 else if _ : (j : ℕ) = i then 1 else 2
  monotone' j k h := by
    dsimp only [dite_eq_ite]
    cases Nat.lt_trichotomy j i with
    | inl h' => simp only [h', ↓reduceIte, Fin.isValue, Fin.zero_le]
    | inr h' => cases h' with
    | inl h' =>
      have : (i : ℕ) ≤ k := le_of_eq_of_le (id (Eq.symm h')) h
      rw [← not_lt] at this
      simp only [h', lt_self_iff_false, ↓reduceIte, Fin.isValue, this, ge_iff_le]
      aesop
    | inr h' =>
      have a : ¬ (j : ℕ) < i := Nat.not_lt_of_gt h'
      have b : ¬ (j : ℕ) = i := Nat.ne_of_lt' h'
      have c : ¬ (k : ℕ) < i := by
        by_contra p
        exact a (lt_of_le_of_lt (h : (j : ℕ) ≤ k) p)
      have d : ¬ (k : ℕ) = i := by
        by_contra p
        apply Nat.not_le_of_lt h'
        have : (j : ℕ) ≤ k := h
        rw [p] at this
        exact this
      simp only [a, ↓reduceIte, b, Fin.isValue, c, d, le_refl]

def standard_map (n : ℕ) (i : Fin (n + 1)) : Δ[n] ⟶ Δ[2] :=
  stdSimplex.map (SimplexCategory.mkHom (s_aux i))

-- the above map restricted to the horn
def horn_map (n : ℕ) (i : Fin (n + 1)) : (Λ[n, i] : SSet) ⟶ Δ[2] :=
  ((horn n i).ι) ≫ (standard_map n i)

-- on vertices j maps to
-- (j, 0) if j < i
-- (j, 1) if j = i
-- (j, 2) if j > i
def s (n : ℕ) (i : Fin (n + 1)) : Δ[n] ⟶ Δ[2] ⊗ Δ[n] :=
  FunctorToTypes.prod.lift (standard_map n i) (𝟙 _)

def s_restricted (n : ℕ) (i : Fin (n + 1)) : (Λ[n, i] : SSet) ⟶ Δ[2] ⊗ (Λ[n, i] : SSet)  :=
  FunctorToTypes.prod.lift (horn_map n i) (𝟙 _)

noncomputable
def horn_to_pushout (n : ℕ) (i : Fin (n + 1)) : (Λ[n, i] : SSet) ⟶ (Λ_pushout n i).cocone.pt :=
  s_restricted n i ≫ (Limits.pushout.inl ((horn 2 1).ι ▷ (Λ[n, i] : SSet)) ((Λ[2, 1] : SSet) ◁ (horn n i).ι))

lemma leftSqCommAux (n : ℕ) (i : Fin (n + 1)) :
    s_restricted n i ≫ Δ[2] ◁ ((horn n i).ι) = ((horn n i).ι) ≫ s n i := rfl

lemma leftSqComm (n : ℕ) (i : Fin (n + 1)) : horn_to_pushout n i ≫ Λ_pushoutProduct n i = ((horn n i).ι) ≫ s n i := by
  rw [← leftSqCommAux]
  dsimp [horn_to_pushout, Λ_pushoutProduct, pushoutProduct]
  rw [Category.assoc, IsPushout.inl_desc]

def r_aux {n} (i : Fin (n + 1)) : Fin 3 × Fin (n + 1) →o Fin (n + 1) where
  toFun := fun ⟨k, j⟩ ↦
    if _ : ((j : ℕ) < i ∧ k = 0) ∨ ((j : ℕ) > i ∧ k = 2) then j else i
  monotone' := by
    intro ⟨k, j⟩ ⟨k', j'⟩ ⟨(hk : k ≤ k'), (hj : j ≤ j')⟩
    cases Nat.lt_trichotomy j i with
    | inl h =>
      have : ¬ i < j := Lean.Omega.Fin.not_lt.mpr (Fin.le_of_lt h)
      fin_cases k; all_goals fin_cases k'
      all_goals simp only [Fin.val_fin_lt, Fin.mk_one, Fin.isValue, one_ne_zero, and_false, gt_iff_lt,
        Fin.reduceEq, or_self, ↓reduceDIte, Fin.reduceFinMk, and_true, false_or, dite_eq_ite,
        ge_iff_le, this]
      pick_goal 6
      · by_cases i < j'; all_goals rename_i h'; simp only [h', ↓reduceIte, le_refl, le_of_lt]
      pick_goal 8
      · by_cases i < j'; all_goals rename_i h'; simp only [h', ↓reduceIte, le_refl, le_of_lt]
      all_goals aesop
    | inr h => cases h with
    | inl h => have := Fin.eq_of_val_eq h; aesop
    | inr h =>
      have : i < j' := lt_of_lt_of_le h hj
      have : i ≤ j' := le_of_lt this
      fin_cases k; all_goals fin_cases k'
      all_goals simp only [Fin.mk_one, one_ne_zero, le_refl,Fin.val_fin_lt,
        Lean.Omega.Fin.not_lt.mpr (Fin.le_of_lt h), Fin.zero_eta, Fin.isValue, and_true, gt_iff_lt, Fin.reduceEq,
        and_false, or_self, ↓reduceDIte, Fin.reduceFinMk, or_false, false_or, dite_eq_ite, ge_iff_le, h]
      pick_goal 3
      · by_cases i < j'; all_goals rename_i h'; aesop
      pick_goal 5
      · by_cases i < j'; all_goals rename_i h'; aesop
      all_goals aesop

open stdSimplex SimplexCategory in
def map_mk_from_prod {n m k} (f : Fin (n + 1) × Fin (m + 1) →o Fin (k + 1)) : Δ[n] ⊗ Δ[m] ⟶ Δ[k] := by
  refine ⟨fun x ⟨c, d⟩ ↦ ⟨mkHom ⟨fun a ↦ f ((stdSimplex.asOrderHom c) a, (stdSimplex.asOrderHom d) a), ?_⟩⟩, ?_⟩
  · intro j k hjk
    exact f.monotone ⟨(stdSimplex.asOrderHom c).monotone hjk, (stdSimplex.asOrderHom d).monotone hjk⟩
  · aesop

-- on vertices j k map to
-- j if (j < i) ∧ (k = 0)
-- j if (j > i) ∧ (k = 2)
-- i if (j = i) ∨ (k = 1)
def r (n : ℕ) (i : Fin (n + 1)) : Δ[2] ⊗ Δ[n] ⟶ Δ[n] := map_mk_from_prod (r_aux i)

variable (n : ℕ) (i : Fin (n + 1)) (h0 : 0 < i) (hn : i < Fin.last n)

-- r restricted along Λ[2, 1]
noncomputable
def r_restrict_horn_2 : (Λ[2, 1] : SSet) ⊗ Δ[n] ⟶ (Λ[n, i] : SSet) where
  app k := by
    intro ⟨⟨x, hx⟩, y⟩
    refine ⟨(((horn 2 1).ι) ▷ Δ[n] ≫ r n i).app k ⟨⟨x, hx⟩, y⟩, ?_⟩
    dsimp [horn, ← ne_eq] at hx ⊢
    rw [Set.ne_univ_iff_exists_not_mem] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    fin_cases a
    · simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Set.union_singleton, Set.mem_insert_iff,
        zero_ne_one, Set.mem_range, false_or, not_exists] at ha
      use 0
      simp only [Fin.isValue, Nat.reduceAdd, ne_eq, Set.union_singleton, Set.mem_insert_iff,
        Set.mem_range, not_or, not_exists]
      refine ⟨Fin.ne_of_lt h0, fun j h ↦ ?_⟩
      change (fun a ↦
                if (stdSimplex.asOrderHom y) a < i ∧ (stdSimplex.asOrderHom x) a = 0 ∨ i < (stdSimplex.asOrderHom y) a ∧ (stdSimplex.asOrderHom x) a = 2 then
                  (stdSimplex.asOrderHom y) a
                else i) j = 0 at h
      by_cases (stdSimplex.asOrderHom y) j < i; all_goals rename_i h'
      · by_cases (stdSimplex.asOrderHom x) j = 0; all_goals rename_i h''
        · apply ha
          right
          exact ⟨j, h''⟩
        · aesop
      · aesop
    · aesop
    · simp only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, Set.union_singleton,
        Set.mem_insert_iff, Fin.reduceEq, Set.mem_range, false_or, not_exists] at ha
      use Fin.last n
      simp only [Fin.isValue, Nat.reduceAdd, ne_eq, Set.union_singleton, Set.mem_insert_iff,
        Set.mem_range, not_or, not_exists]
      refine ⟨Fin.ne_of_gt hn, fun j h ↦ ?_⟩
      change (fun a ↦
                if (stdSimplex.asOrderHom y) a < i ∧ (stdSimplex.asOrderHom x) a = 0 ∨ i < (stdSimplex.asOrderHom y) a ∧ (stdSimplex.asOrderHom x) a = 2 then
                  (stdSimplex.asOrderHom y) a
                else i) j = Fin.last n at h
      by_cases (stdSimplex.asOrderHom y) j < i; all_goals rename_i h'
      · by_cases (stdSimplex.asOrderHom x) j = 0; all_goals rename_i h''
        · simp only [h', Nat.reduceAdd, h'', Fin.isValue, and_self, Fin.reduceEq, and_false,
          or_false, ↓reduceIte, Fin.natCast_eq_last] at h
          rw [h] at h'
          exact absurd (lt_trans h' hn) (Fin.not_lt.mpr (Fin.le_last _))
        · simp_all only [Nat.reduceAdd, Fin.isValue, Set.union_singleton, ne_eq, Fin.natCast_eq_last, and_false,
          or_self, ↓reduceIte, lt_self_iff_false]
      · simp_all only [Nat.reduceAdd, Fin.isValue, Set.union_singleton, ne_eq, Fin.natCast_eq_last, false_and,
        and_false, or_self, ↓reduceIte, not_lt, Fin.last_le_iff, lt_self_iff_false]

-- r restricted along (Λ[n, i] : SSet)
noncomputable
def r_restrict_horn_n : Δ[2] ⊗ (Λ[n, i] : SSet) ⟶ (Λ[n, i] : SSet) where
  app k := by
    intro ⟨x, ⟨y, hy⟩⟩
    refine ⟨(Δ[2] ◁ ((horn n i).ι) ≫ r n i).app k ⟨x, ⟨y, hy⟩⟩, ?_⟩
    dsimp [horn, ← ne_eq] at hy ⊢
    rw [Set.ne_univ_iff_exists_not_mem] at hy ⊢
    obtain ⟨a, this⟩ := hy
    simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_range, not_or, not_exists] at this
    obtain ⟨ha₁, ha₂⟩ := this
    use a
    intro h
    simp only [ne_eq, Set.union_singleton, Set.mem_insert_iff, ha₁, Set.mem_range, false_or] at h
    obtain ⟨j, hj⟩ := h
    apply ha₂ j
    change (stdSimplex.asOrderHom ((r n i).app k (x, y))) j = a at hj
    -- add lemma about (asOrderHom {down := SimplexCategory.Hom.mk {toFun} }) = toFun
    change (fun a ↦
      if (stdSimplex.asOrderHom y) a < i ∧ (stdSimplex.asOrderHom x) a = 0 ∨ i < (stdSimplex.asOrderHom y) a ∧ (stdSimplex.asOrderHom x) a = 2 then
        (stdSimplex.asOrderHom y) a else i) j = a at hj
    aesop

open stdSimplex SimplexCategory in
noncomputable
def pushout_to_horn : (Λ_pushout n i).cocone.pt ⟶ (Λ[n, i] : SSet) :=
  Limits.pushout.desc (r_restrict_horn_n n i) (r_restrict_horn_2 n i h0 hn) rfl

lemma rightSqComm : pushout_to_horn n i h0 hn ≫ (horn n i).ι = Λ_pushoutProduct n i ≫ r n i := by
  dsimp [pushout_to_horn, Λ_pushoutProduct, pushoutProduct]
  apply Limits.pushout.hom_ext; all_goals aesop

lemma r_comp_s (n : ℕ) (i : Fin (n + 1)) : s n i ≫ r n i = 𝟙 Δ[n] := by
  let r' := r_aux i
  let s' : Fin (n + 1) →o Fin 3 × Fin (n + 1) := (s_aux i).prod (OrderHom.id)
  let f : Fin (n + 1) →o Fin (n + 1) := OrderHom.comp r' s'
  have a : f = OrderHom.id := by
    ext x
    simp [f, r', s', s_aux, r_aux]
    cases Nat.lt_trichotomy x i with
    | inl h => aesop
    | inr h => cases h with
    | inl h => aesop
    | inr h =>
      simp_all only [Fin.val_fin_lt, Fin.isValue, true_and]
      split
      next h_1 =>
        simp_all only [Fin.isValue, one_ne_zero, imp_false, not_le, and_self]
        split
        next h_2 => simp_all only [Fin.isValue, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, imp_false, not_le, and_self,
          Fin.reduceEq, or_false, ↓reduceIte]
        next h_2 =>
          simp_all only [not_lt, Fin.isValue, Fin.reduceEq, or_false]
          split
          next h_3 => simp_all only
          next h_3 => simp_all only [not_lt]
      next
        h_1 =>
        simp_all only [Fin.isValue, Fin.reduceEq, imp_false, not_le, and_self, ite_eq_right_iff, not_lt]
        split
        next h_2 => simp_all only
        next h_2 =>
          simp_all only [not_or, not_le]
          obtain ⟨left, right⟩ := h_2
          exfalso
          exact left right
  have : s n i ≫ r n i = stdSimplex.map (SimplexCategory.mkHom f) := rfl
  rw [this, a]
  aesop

lemma restricted_r_comp_s : horn_to_pushout n i ≫ pushout_to_horn n i h0 hn = 𝟙 (Λ[n, i] : SSet) := by
  dsimp [horn_to_pushout, pushout_to_horn]
  rw [Category.assoc, Limits.pushout.inl_desc]
  ext k ⟨x, hx⟩
  change (r_restrict_horn_n n i).app k ((horn_map n i).app k ⟨x, hx⟩, ⟨x, hx⟩) = ⟨x, hx⟩
  simp [r_restrict_horn_n]
  have := congr_fun (congr_app (r_comp_s n i) k) x
  aesop

noncomputable
instance hornRetract : RetractArrow ((horn n i).ι) (Λ_pushoutProduct n i) where
  i := {
    left := horn_to_pushout n i
    right := s n i
    w := leftSqComm n i
  }
  r := {
    left := pushout_to_horn n i h0 hn
    right := r n i
    w := rightSqComm n i h0 hn
  }
  retract := Arrow.hom_ext _ _ (restricted_r_comp_s n i h0 hn) (r_comp_s n i)
