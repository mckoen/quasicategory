import Mathlib.Data.Sigma.Order
import Quasicategory.TopCatModelCategory.SSet.NonDegenerateProdSimplex

open CategoryTheory MonoidalCategory SSet Simplicial SimplexCategory prodStdSimplex

variable {n : ℕ}

/-- defined for `0 ≤ a ≤ b ≤ n`. Can define it for `b = n + 1`,
  but then it lands in `Λ[2, 2] _⦋n + 2⦌`. -/
def τ.objMk₂ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : Δ[2] _⦋n + 2⦌  :=
  stdSimplex.objMk {
    toFun k :=
      if k ≤ (⟨i.2, by omega⟩ : Fin (n + 3)) then 0
      else if k ≤ i.1.castSucc.succ then 1
      else 2
    monotone' := by
      refine Fin.monotone_iff_le_succ.mpr ?_
      rintro (j : Fin (n + 2))
      split
      · next h => simp
      · next h =>
        have : ¬j.succ ≤ ⟨i.2, by omega⟩ := fun h' ↦ h (le_trans (Fin.castSucc_le_succ j) h')
        simp [this]
        split
        · next => aesop
        · next h =>
          have : ¬j ≤ i.1.castSucc := fun h' ↦ h (le_trans (Fin.castSucc_le_castSucc_iff.2 h') (Fin.castSucc_le_succ i.1.castSucc))
          simp [this] }

/-- defined for `0 ≤ a ≤ b < n`. Can define it for `b = n`,
  but then it lands in `Λ[2, 2] _⦋n + 1⦌`. -/
def σ.objMk₂ (i : Σₗ (b : Fin n), Fin b.succ) : Δ[2] _⦋n + 1⦌  :=
  stdSimplex.objMk {
    toFun k :=
      if k ≤ (⟨i.2, by omega⟩ : Fin (n + 1)) then 0
      else if k ≤ i.1.succ then 1
      else 2
    monotone' := by
      refine Fin.monotone_iff_le_succ.mpr ?_
      rintro (j : Fin (n + 1))
      split
      · next h => simp
      · next h =>
        have : ¬j.succ ≤ ⟨i.2, by omega⟩ := by
          intro h'
          rw [Fin.coe_eq_castSucc] at h
          exact h (le_trans (Fin.castSucc_le_succ j) h')
        simp [this]
        split
        · next =>
          simp at h
          simp_all only [Fin.val_succ, not_le, Fin.isValue]
          split
          next
            h_2 =>
            simp_all only [Fin.isValue, Fin.le_zero_iff, len_mk, Nat.reduceAdd, Fin.one_eq_zero_iff,
              OfNat.ofNat_ne_one]
            have := lt_of_le_of_lt h_2 h
            apply this.not_le
            exact Fin.castSucc_le_succ j
          next h_2 =>
            simp_all only [not_le, Fin.isValue]
            split
            next h_3 => simp_all only [Fin.isValue, le_refl]
            next h_3 => simp_all only [not_le, Fin.isValue, Fin.reduceLE]
        · next h =>
          rename_i q
          have : ¬j.succ ≤ i.1.succ := by
            simp_all
            apply lt_trans h ?_
            exact Fin.castSucc_lt_succ j
          dsimp at this
          simp [this]
          simp_all only [len_mk, Fin.val_succ, not_le, Fin.isValue]
          split
          next h_2 =>
            simp_all only [Fin.isValue, Fin.le_zero_iff, len_mk, Nat.reduceAdd, Fin.reduceEq]
            have := lt_of_le_of_lt h_2 q
            apply this.not_le
            exact Fin.castSucc_le_succ j
          next h_2 => simp_all only [not_le, Fin.isValue, le_refl] }

lemma σ.objMk₂_injective : Function.Injective (σ.objMk₂ (n := n)) := by
  intro i j h
  rcases i with ⟨b, a⟩
  rcases j with ⟨b', a'⟩
  dsimp [σ.objMk₂] at h
  wlog hb : b < b' generalizing b b'
  · simp only [not_lt] at hb
    obtain hb | rfl := hb.lt_or_eq
    · exact (this _ _ _ _ h.symm hb).symm
    · clear hb
      wlog ha : a < a' generalizing a a'
      · simp only [not_lt] at ha
        obtain ha | rfl := ha.lt_or_eq
        · exact (this _ _ h.symm ha).symm
        · rfl
      have := stdSimplex.objMk_injective h
      simp at this
      have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨a', by dsimp; omega⟩
      simp [Fin.le_iff_val_le_val] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      simp [ha.not_le] at this
  exfalso
  have := stdSimplex.objMk_injective h
  simp at this
  have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨b'.succ, by dsimp; omega⟩
  simp at this
  have p : ¬ b'.1 + 1 ≤ a.1 := by
    simp only [Fin.val_succ, not_le]
    rw [Fin.lt_iff_val_lt_val] at hb
    omega
  have p' : ¬ b'.1 + 1 ≤ a'.1 := by dsimp; omega
  have p'' : ⟨b'.1 + 1, by omega⟩ ≤ b'.castSucc.succ := by
    rw [Fin.le_iff_val_le_val]
    simp
  simp [Fin.le_iff_val_le_val] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  simp [p, p', p''] at this
  omega

lemma τ.objMk₂_injective : Function.Injective (τ.objMk₂ (n := n)) := by
  intro i j h
  rcases i with ⟨b, a⟩
  rcases j with ⟨b', a'⟩
  dsimp [τ.objMk₂] at h
  wlog hb : b < b' generalizing b b'
  · simp only [not_lt] at hb
    obtain hb | rfl := hb.lt_or_eq
    · exact (this _ _ _ _ h.symm hb).symm
    · clear hb
      wlog ha : a < a' generalizing a a'
      · simp only [not_lt] at ha
        obtain ha | rfl := ha.lt_or_eq
        · exact (this _ _ h.symm ha).symm
        · rfl
      have := stdSimplex.objMk_injective h
      simp at this
      have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨a', by dsimp; omega⟩
      simp [ha] at this
      exfalso
      aesop
  exfalso
  have := stdSimplex.objMk_injective h
  simp at this
  have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨b'.succ, by dsimp; omega⟩
  simp at this
  have p : ¬ b'.1 + 1 ≤ a.1 := by
    simp only [Fin.val_succ, not_le]
    rw [Fin.lt_iff_val_lt_val] at hb
    omega
  have p' : ¬ b'.1 + 1 ≤ a'.1 := by dsimp; omega
  have p'' : ⟨b'.1 + 1, by omega⟩ ≤ b'.castSucc.succ := by
    rw [Fin.le_iff_val_le_val]
    simp
  simp [p, p', p''] at this
  rw [Fin.le_iff_val_le_val] at this
  simp at this
  omega

instance (b : Fin n) : OrderTop (Fin b.succ) where
  top := ⟨b, Nat.lt_add_one b⟩
  le_top a := Nat.le_of_lt_succ a.isLt

def τ' (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : (Δ[n] ⊗ Δ[2] : SSet) _⦋n + 2⦌ :=
  (stdSimplex.objEquiv.symm (σ ⟨i.2, by omega⟩ ≫ σ i.1), τ.objMk₂ i)

def σ' (i : Σₗ (b : Fin n), Fin b.succ) : (Δ[n] ⊗ Δ[2] : SSet) _⦋n + 1⦌ :=
  (stdSimplex.objEquiv.symm (σ ⟨i.2, by omega⟩), σ.objMk₂ i)

/-- for all `0 ≤ a ≤ b < n`, we get a nondegenerate `(n+1)`-simplex. -/
def σ.nonDegenerateEquiv.toFun (i : Σₗ (b : Fin n), Fin b.succ) :
    (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 1) := by
  refine ⟨σ' i, ?_⟩
  rcases i with ⟨b, a⟩
  rw [prodStdSimplex.nonDegenerate_iff']
  simp [σ']
  simp [SSet.yonedaEquiv, yonedaCompUliftFunctorEquiv, stdSimplex.objEquiv, Equiv.ulift]
  intro x y h
  simp at h
  ext i
  fin_cases i
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  rw [stdSimplex.ext'_iff, SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  simp [stdSimplex, σ, objMk₂, SSet.uliftFunctor, stdSimplex.objEquiv, stdSimplex.objMk] at h₁ h₂
  replace h₁ := congr_fun h₁ 0
  replace h₂ := congr_fun h₂ 0
  simp [Hom.toOrderHom, Fin.predAbove] at h₁ h₂
  simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.ext_iff] at h₁ h₂
  simp
  split at h₂
  · next h =>
    simp at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    simp_all only [Fin.isValue, Fin.val_zero, Fin.val_natCast]
    split at h₁
    next h_2 =>
      split at h₂
      next h_3 =>
        split at h₁
        next h_4 =>
          simp_all only [Fin.isValue, Fin.val_zero, Fin.coe_pred]
          change (x 0).1.pred = (y 0).1.pred at h₁
          refine Nat.pred_inj ?_ ?_ h₁
          · change _ < (x 0).1 at h_2
            omega
          · change _ < (y 0).1 at h_4
            omega
        omega
      omega
    next h_2 =>
      split at h₂
      next h_3 =>
        split at h₁
        next h_4 =>
          rw [Nat.mod_eq_of_lt (by omega)] at h_3
          omega
        simpa
      next h_3 =>
        split at h₁
        all_goals
          split at h₂
          all_goals omega
  · next h =>
    simp at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    simp [h] at h₁
    split at h₁
    · next h' =>
      change (x 0).1.pred = (y 0).1.pred at h₁
      refine Nat.pred_inj ?_ ?_ h₁
      · change _ < (x 0).1 at h
        omega
      · change _ < (y 0).1 at h'
        omega
    · next h' =>
      exfalso
      simp at h₁
      simp_all only [Fin.isValue, Fin.val_natCast, not_lt]
      split at h₂
      next h_2 =>
        split at h₂
        next h_3 => simp_all only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero]
        next h_3 =>
          split at h₂
          next h_4 =>
            simp_all only [Fin.isValue, not_le, Fin.val_one]
            rw [Nat.mod_eq_of_lt (by omega)] at h_3
            omega
          omega
      next h_2 =>
        split at h₂
        omega
        next h_3 =>
          split at h₂
          omega
          next h_4 =>
            simp_all only [Fin.isValue, not_le, Fin.val_two]
            rw [Nat.mod_eq_of_lt (by omega)] at h_3
            omega

/-- for all `0 ≤ a ≤ b ≤ n`, we get a nondegenerate `(n+2)`-simplex. -/
def τ.nonDegenerateEquiv.toFun (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 2) := by
  refine ⟨τ' i, ?_⟩
  rcases i with ⟨b, a⟩
  rw [nonDegenerate_iff _ rfl]
  ext x
  change (((Fin.predAbove b) ∘ (Fin.predAbove ⟨a, _⟩)) x).1 + _ = x
  dsimp [Fin.predAbove, τ', objMk₂]
  split
  · next h =>
    simp_rw [Fin.lt_pred_iff]
    simp [h.not_le]
    split
    · next h' =>
      simp [h'.not_le]
      exact Eq.symm (Nat.eq_add_of_sub_eq (le_of_add_le_right h') rfl)
    · next h' =>
      simp [h', not_lt.1 h']
      omega
  · next h =>
    simp_rw [Fin.lt_castPred_iff]
    simp [not_lt.1 h]
    simp at h
    have : ⟨a, by omega⟩ ≤ b.castSucc.castSucc := by
      simp [Fin.le_iff_val_le_val]
      omega
    simp [(h.trans this).not_lt]

/-
-- `σab = ⟨(0, 0),..., (0, a), (1, a),..., (1, b), (2, b + 1),..., (2, n)⟩`
-- `(b + 2)`-th face of `τab` and of `τa(b+1)`
/-- There is a bijection (via `σ`) between pairs `0 ≤ a ≤ b < n` and nondegenerate
  `(n + 1)`-simplices. -/
noncomputable
def σ.nonDegenerateEquiv :
    (Σₗ (b : Fin n), Fin b.succ) ≃ (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 1) := by
  refine Equiv.ofBijective (σ.nonDegenerateEquiv.toFun) ?_
  constructor
  · exact fun _ _ h ↦ σ.objMk₂_injective (congr_arg (Prod.snd ∘ Subtype.val) h)
  · sorry
-/

/-- There is a bijection (via `τ`) between pairs `0 ≤ a ≤ b ≤ n` and nondegenerate
  `(n + 2)`-simplices. -/
noncomputable
def τ.nonDegenerateEquiv :
    (Σₗ (b : Fin (n + 1)), Fin b.succ) ≃ (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 2) := by
  refine Equiv.ofBijective (τ.nonDegenerateEquiv.toFun) ?_
  constructor
  · intro i j h
    simpa using τ.objMk₂_injective (congr_arg (Prod.snd ∘ Subtype.val) h)
  · intro x
    have α := (prodStdSimplex.nonDegenerate_iff _ rfl).1 x.2
    let f := x.1.2
    let g := x.1.1
    let S : Finset (Fin (n + 3)) := { i | f i = 1} -- min will be a+1, max will be b+1
    have thm : ∀ (i : Fin (n + 3)), (g i).1 + (f i).1 = i.1 := fun i ↦
      Fin.eq_mk_iff_val_eq.1 (DFunLike.congr_fun α i)
    by_cases hS : S.Nonempty
    · let asucc := (S.min' hS) -- a+1
      let bsucc := (S.max' hS) -- b+1
      let a := g asucc
      let b := g bsucc

      have ha : asucc ∈ S := S.min'_mem hS
      have hb : bsucc ∈ S := S.max'_mem hS
      have Ha : ⟨a + (f asucc), _⟩ = asucc := DFunLike.congr_fun α asucc
      have Hb : ⟨b + (f bsucc), _⟩ = bsucc := DFunLike.congr_fun α bsucc
      have Ha' : f asucc = 1 := by simpa [S] using (S.min'_mem hS)
      have Hb' : f bsucc = 1 := by simpa [S] using (S.max'_mem hS)
      simp_rw [Ha'] at Ha -- shows that (g asucc) = a
      simp_rw [Hb'] at Hb -- shows that (g bsucc) = b

      have haa : ⟨a, by omega⟩ < asucc := by simp only [← Ha, Nat.reduceAdd, Fin.isValue,
        Fin.val_one, Fin.mk_lt_mk, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, S]
      have hbb : ⟨b, by omega⟩ < bsucc := by simp only [← Hb, Nat.reduceAdd, Fin.isValue,
        Fin.val_one, Fin.mk_lt_mk, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, S]
      have hab : a ≤ b := by
        have : asucc ≤ bsucc := Finset.min'_le S bsucc hb
        rw [← Ha, ← Hb, Fin.le_iff_val_le_val] at this
        simpa only [Nat.reduceAdd, Fin.isValue, Fin.val_one, add_le_add_iff_right, Fin.val_fin_le]

      use ⟨b, ⟨a, Nat.lt_add_one_of_le hab⟩⟩
      apply nonDegenerate_ext rfl
      ext i
      change (((Fin.predAbove b) ∘ (Fin.predAbove ⟨a, _⟩)) i).1 = (g i).1
      simp only [Function.comp_apply, Fin.predAbove, Fin.castSucc_mk, Fin.val_succ, len_mk,
        OrderHom.toFun_eq_coe, stdSimplex.objEquiv_toOrderHom_apply]
      split
      ·
        next h =>
        simp_rw [Fin.lt_pred_iff]
        replace h : asucc ≤ i := by
          rw [← Ha]
          exact Fin.le_iff_val_le_val.1 h
        split
        · next h' =>
          -- f i = 2, so g i = i - 2
          suffices (f i).1 = 2 by
            rw [Fin.coe_pred, Fin.coe_pred, ← thm, this]
            rfl
          have h' : bsucc < i := by rwa [← Hb]
          have ne_one : ¬1 = (f i) := by
            intro h
            apply Finset.not_mem_of_max_lt h' (Finset.coe_max' hS).symm
            simpa [S] using h.symm
          rw [Fin.eq_mk_iff_val_eq] at ne_one
          have : (f bsucc).1 ≤ (f i).1 := (stdSimplex.asOrderHom f).monotone' h'.le
          rw [Hb'] at this
          have := Nat.lt_of_le_of_ne this ne_one
          rw [← Fin.eq_mk_iff_val_eq]
          swap; omega
          apply Fin.eq_last_of_not_lt
          rw [not_lt]
          exact this
        · next h' =>
          -- f i = 1, so g i = i - 1
          suffices (f i).1 = 1 by
            rw [Fin.coe_castPred, Fin.coe_pred, ← thm, this]
            rfl
          have h' : i ≤ bsucc := by
            rw [← Hb]
            rwa [not_lt] at h'
          have ge_one : (f asucc).1 ≤ (f i).1 := (stdSimplex.asOrderHom f).monotone' h
          have le_one : (f i).1 ≤ (f bsucc).1 := (stdSimplex.asOrderHom f).monotone' h'
          rw [Ha'] at ge_one
          rw [Hb'] at le_one
          exact Eq.symm (Nat.le_antisymm ge_one le_one)
      · next h' =>
        -- f i = 0, so g i = i
        simp_rw [Fin.lt_castPred_iff]
        have : ¬ b.castSucc.castSucc < i := fun p ↦ h' (lt_of_le_of_lt hab p)
        simp only [this, ↓reduceDIte, Fin.coe_castPred]
        rw [← thm, Nat.add_right_eq_self, ← Nat.lt_one_iff]
        rw [not_lt] at h'
        have ne_one : ¬(f i) = 1 := by
          intro h
          apply Finset.not_mem_of_lt_min (lt_of_le_of_lt h' haa) (Finset.coe_min' hS).symm
          simpa [S]
        rw [Fin.eq_mk_iff_val_eq] at ne_one
        have : (f i).1 ≤ (f asucc).1 := (stdSimplex.asOrderHom f).monotone' (h'.trans haa.le)
        rw [Ha'] at this
        exact Nat.lt_of_le_of_ne this ne_one
    · --if the set is empty, then 1 is not in the image. contradiction somewhere
      exfalso
      let T : Finset (Fin (n + 3)) := { i | f i = 2}
      by_cases hT : T.Nonempty
      · let a := (T.min' hT)
        have hfa : f a = 2 := by simpa [T] using (T.min'_mem hT)
        cases (Fin.eq_zero_or_eq_succ a)
        · next h =>
          have hfa' := congr_arg f h
          rw [hfa] at hfa'
          have := thm 0
          rw [← hfa'] at this
          simp at this
        · next h =>
          obtain ⟨a1, ha⟩ := h
          cases (Fin.eq_zero_or_eq_succ a1)
          · next h' =>
            subst h'
            have hfa' : f a = f 1 := congr_arg f ha
            rw [hfa] at hfa'
            have := thm 1
            rw [← hfa'] at this
            simp only [Nat.reduceAdd, Fin.isValue, Fin.val_two, Fin.val_one, Nat.reduceEqDiff, T,
              S] at this
          . next h' =>
            obtain ⟨a2, haa⟩ := h'
            have p : (f a1.castSucc).1 = 0 := by
              have p : ¬(f a1.castSucc) = 2 := by
                intro h
                apply Finset.not_mem_of_lt_min (Fin.castSucc_lt_succ a1) (by
                  rw [← ha]
                  exact (Finset.coe_min' hT).symm)
                simpa [T]
              have : (f a1.castSucc).1 ≤ (f a1.succ).1 := (stdSimplex.asOrderHom f).monotone' (Fin.castSucc_le_succ a1)
              rw [← ha, hfa] at this
              cases (lt_or_eq_of_le this)
              · next h'' =>
                cases (lt_or_eq_of_le (Nat.le_of_lt_succ h''))
                · next h''' => exact Nat.lt_one_iff.mp h'''
                · next h''' =>
                  exfalso
                  apply hS
                  refine ⟨a1.castSucc, ?_⟩
                  simp [S]
                  rwa [Fin.eq_mk_iff_val_eq]
              · next h'' => exfalso; omega
            have p' : (f a2.castSucc.castSucc).1 = 0 := by
              have : (f a2.castSucc.castSucc).1 ≤ (f a1.castSucc).1 := by
                rw [haa, ← Fin.succ_castSucc]
                exact (stdSimplex.asOrderHom f).monotone' (Fin.castSucc_le_succ a2.castSucc)
              rw [p] at this
              exact Nat.eq_zero_of_le_zero this
            have p'' : (g a1.castSucc).1 = (a1.castSucc).1 := by
              rw [← thm, p]
              simp
            have p''' : (g a1.succ).1 = (a2.castSucc.castSucc).1 := by
              have := thm a1.succ
              rw [← ha, hfa] at this
              rcases a with ⟨a, pa⟩
              rcases a1 with ⟨a1, pa1⟩
              rcases a2 with ⟨a2, pa2⟩
              simp_all
            have hyp : (g a1.castSucc).1 ≤ (g a1.succ).1 := (stdSimplex.asOrderHom g).monotone' (Fin.castSucc_le_succ a1)
            rw [p'', p'''] at hyp
            simp only [Fin.coe_castSucc, Fin.val_natCast, Fin.cast_val_eq_self, T, S] at hyp
            simp_all
      · -- if the set is empty, then f is constant 0, which is not nondegenerate
        have thm1 : ∀ (i : Fin (n + 3)), ¬(f i) = 1 := by
          intro i hi
          apply hS
          refine ⟨i, ?_⟩
          simpa [S]
        have thm2 : ∀ (i : Fin (n + 3)), ¬(f i) = 2 := by
          intro i hi
          apply hT
          refine ⟨i, ?_⟩
          simpa [T]
        have thm0 : ∀ (i : Fin (n + 3)), (f i) = 0 := by
          intro i
          have thm1 := thm1 i
          have thm2 := thm2 i
          cases Fin.eq_zero_or_eq_succ (f i)
          · next h => exact h
          · next h =>
            obtain ⟨j, hj⟩ := h
            fin_cases j
            · exfalso
              exact thm1 hj
            · exfalso
              exact thm2 hj
        have := thm (Fin.last _)
        rw [thm0] at this
        simp at this
        omega

@[simp]
def Sigma.Lex.succ : (Σₗ (b : Fin (n + 1)), Fin b.succ) → (Σₗ (b : Fin (n + 1)), Fin b.succ) :=
  fun ⟨b, a⟩ ↦
    if h₁ : a.1 < b then ⟨b, ⟨a.succ, by simpa using h₁⟩⟩ -- if a < b, then ⟨b, a + 1⟩
    else if h₂ : b = Fin.last n then ⟨Fin.last n, Fin.last n⟩ -- if a = b = n, then don't change
    else ⟨⟨b.succ, by simp_all [Fin.ext_iff]; omega⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ -- if a = b < n, then ⟨b + 1, 0⟩

lemma Sigma.Lex.le_succ : ∀ (a : Σₗ (b : Fin (n + 1)), Fin b.succ), a ≤ succ a := by
    intro ⟨b, a⟩
    simp
    split
    · simp [le_def, Fin.le_iff_val_le_val]
    · split
      · next h =>
        simp [le_def, Fin.le_iff_val_le_val]
        right
        use h
        omega
      · next h =>
        simp [le_def, Fin.lt_iff_val_lt_val]

lemma Sigma.Lex.max_of_succ_le : ∀ {a : Σₗ (b : Fin (n + 1)), Fin b.succ}, succ a ≤ a → IsMax a := by
    intro ⟨b, a⟩
    simp
    split
    · next h =>
      intro h'
      cases h'
      · omega
      · next h' =>
        simp [Fin.le_iff_val_le_val] at h'
    · next h =>
      split
      · next h' =>
        intro h''
        simp [le_def] at h''
        aesop
      · next h' =>
        intro h''
        exfalso
        simp [le_def, Fin.lt_iff_val_lt_val] at h''
        rw [Fin.eq_mk_iff_val_eq] at h'
        simp at h'
        cases h''
        · next h''' =>
          rename_i h''''
          rw [Fin.eq_mk_iff_val_eq] at h''''
          simp at h''''

lemma Sigma.Lex.succ_le_of_lt : ∀ {a b : Σₗ (b : Fin (n + 1)), Fin b.succ}, a < b → Sigma.Lex.succ a ≤ b := by
    intro ⟨b, a⟩ ⟨b', a'⟩ h
    dsimp
    split
    · next h' =>
      rw [le_def]
      rw [lt_def] at h
      aesop
    · next h'=>
      split
      · next h'' =>
        subst h''
        have : a = Fin.last n := by omega
        subst this
        exact h.le
      · next h'' =>
        rw [lt_def] at h
        cases h
        · next h' =>
          simp at h'
          by_cases hb : b.1 + 1 < b'
          · rw [le_def]
            aesop
          · have hb : (⟨⟨b.1 + 1,  by simp_all [Fin.ext_iff]; omega⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ :  Σₗ (b : Fin (n + 1)), Fin b.succ ) =
                ⟨b', ⟨0, Nat.zero_lt_succ ↑b'⟩⟩ := by
              congr
              omega
              omega
              omega
            dsimp at hb
            rw [hb]
            right
            exact Fin.zero_le a'
        · next h' =>
          obtain ⟨h₁, h₂⟩ := h'
          simp at h₁
          subst h₁
          simp at h₂
          omega

instance Sigma.Lex.succOrder : SuccOrder (Σₗ (b : Fin (n + 1)), Fin b.succ) where
  succ := succ
  le_succ := le_succ
  max_of_succ_le := max_of_succ_le
  succ_le_of_lt := succ_le_of_lt

noncomputable
instance : OrderBot (Σₗ (b : Fin (n + 1)), Fin b.succ) :=
  letI : OrderBot (Fin (⊥ : Fin (n + 1)).succ) := {
    bot := ⟨0, Nat.zero_lt_succ _⟩
    bot_le _ := Fin.zero_le _ }
  Sigma.Lex.orderBot

/-
namespace τ

noncomputable abbrev simplex (j : Σₗ (b : Fin (n + 1)), Fin b.succ) := nonDegenerateEquiv j

noncomputable abbrev ιSimplex (j : Σ (b : Fin (n + 1)), Fin b.succ) :
    (Δ[n + 2] : SSet) ⟶ Δ[n] ⊗ Δ[2] :=
  SSet.yonedaEquiv.symm (simplex j)

instance (j : Σ (b : Fin (n + 1)), Fin b.succ) : Mono (ιSimplex j) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (nonDegenerateEquiv j).2

open Subcomplex in
noncomputable
def filtration₂ (j : Σₗ (b : Fin (n + 1)), Fin b.succ) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (unionProd (boundary n) (horn 2 1)) ⊔
    (⨆ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) (_ : i < j), ofSimplex (simplex i).1)

lemma filtration₂_zero : filtration₂ ⟨0, ⟨0, Nat.zero_lt_succ _⟩⟩ =
    (Subcomplex.unionProd (boundary n) (horn 2 1)) := by
  dsimp [filtration₂]
  refine sup_eq_left.2 (le_of_eq_of_le ?_ bot_le)
  rw [iSup₂_eq_bot]
  intro ⟨b, a⟩ i
  rw [Sigma.Lex.lt_def] at i
  exfalso
  cases i
  · rename_i h
    simp only [Fin.not_lt_zero] at h
  · rename_i h
    simp only [Fin.not_lt_zero] at h
    obtain ⟨_, h⟩ := h
    exact h

lemma monotone_filtration₂ : Monotone (filtration₂ (n := n)) := by
  intro x y hxy
  dsimp [filtration₂]
  apply sup_le (le_sup_left) (le_sup_of_le_right ?_)
  apply iSup₂_le
  intro i hi
  exact le_iSup₂_of_le i (sorry) (le_refl _)

lemma filtration₂_last : (filtration₂ (n := n)) ⊤ = ⊤ := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro x hx
  obtain ⟨i, hi⟩ := nonDegenerateEquiv.surjective ⟨x, hx⟩
  obtain rfl : simplex i = x := by simp_all only [simplex, Fin.val_succ]
  rw [filtration₂, ← Subcomplex.ofSimplex_le_iff]
  refine le_sup_of_le_right (le_iSup₂_of_le i ?_ (le_refl _))
  sorry

end τ
-/
