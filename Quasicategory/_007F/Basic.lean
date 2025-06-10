import Quasicategory._007F.Nondegenerate

open CategoryTheory Simplicial MonoidalCategory SSet

variable {n : ℕ}

@[simp]
def f₂' (a b : Fin n) : Fin (n + 2) → Fin 3 :=
  fun k ↦
    if k ≤ a.castSucc.castSucc then 0
    else if k ≤ b.succ.castSucc then 1
    else 2

/-- `[n + 1] → [2]`. `0 ≤ a ≤ b < n` -/
def f₂ (a b : Fin n) : Fin (n + 2) →o Fin 3 where
  toFun := f₂' a b
  monotone' := by
    refine Fin.monotone_iff_le_succ.mpr ?_
    intro i
    dsimp
    split
    · next => omega
    · next h =>
      have h' : ¬i < a.castSucc := fun h' ↦ h h'.le
      simp [h']
      split
      · next => aesop
      · next h =>
        split
        next h' =>
          exfalso
          apply h
          rw [Fin.le_iff_val_le_val]
          dsimp
          omega
        next => omega

open SimplexCategory stdSimplex in
/-- `0 ≤ a ≤ b < n` -/
noncomputable
def f (a b : Fin n) : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (objEquiv.symm (σ a), objMk (f₂ a b))

open SimplexCategory stdSimplex in
/-- `0 ≤ a ≤ b ≤ n` -/
noncomputable
def g (a b : Fin (n + 1)) : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (objEquiv.symm (σ a.castSucc ≫ σ b), objMk (f₂ a b))

open Subcomplex in
noncomputable
def σ (a b : Fin n) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  range (f a b)

open Subcomplex in
noncomputable
def τ (a b : Fin (n + 1)) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  range (g a b)

noncomputable
abbrev τ.simplex (i : Σₗ (b : Fin (n + 1)), Fin b.succ) := τ.nonDegenerateEquiv i

noncomputable abbrev τ.ιSimplex (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (τ.simplex i)

lemma τ.eq_g (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    τ.ιSimplex i = g ⟨i.2, by omega⟩ i.1 := rfl

lemma τ.eq_τ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    Subcomplex.ofSimplex (τ.simplex i).1 = τ ⟨i.2, by omega⟩ i.1 := by
  simp [τ, simplex, nonDegenerateEquiv, nonDegenerateEquiv.toFun, τ', g,
    Subcomplex.range_eq_ofSimplex]
  rfl

lemma τ.eq_τ' (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    Subcomplex.ofSimplex (τ.simplex i).1 = τ ⟨i.2, by omega⟩ i.1 := by
  simp [τ, simplex, nonDegenerateEquiv, nonDegenerateEquiv.toFun, τ', g,
    Subcomplex.range_eq_ofSimplex]
  rfl

-- g is a mono
instance (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : Mono (τ.ιSimplex i) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (τ.nonDegenerateEquiv i).2

open stdSimplex

open SimplexCategory in
instance (a b : Fin n) : Mono (f a b) := by
  rw [mono_iff]
  intro g g' h
  ext e
  rw [Prod.ext_iff] at h
  obtain ⟨h₁, h₂⟩ := h
  simp [f, f₂, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  replace h₁ := congr_fun h₁ e
  replace h₂ := congr_fun h₂ e
  simp [Fin.predAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
  refine Fin.val_eq_of_eq ?_
  split at h₁
  next h =>
    simp [h.not_le] at h₂
    aesop
  next h =>
    simp [not_lt.1 h] at h₂
    split at h₁
    next h' =>
      simp [h'.not_le] at h₂
      aesop
    next h' => aesop

open SimplexCategory in
/-- only works for `0 ≤ a ≤ b ≤ n` -/
instance g_mono (a b : Fin (n + 1)) (hab : a ≤ b) : Mono (g a b) := by
  change Mono (τ.ιSimplex ⟨b, ⟨a, by simp ;omega⟩⟩)
  infer_instance

  /-
  rw [mono_iff]
  dsimp [g]
  rw [← prodStdSimplex.nonDegenerate_iff', prodStdSimplex.nonDegenerate_iff _ rfl]
  ext i
  simp [f₂, SimplexCategory.σ]
  rw [← stdSimplex.map_objEquiv_symm, map_objEquiv_symm_apply]
  cases i using Fin.lastCases with
  | last =>
    simp
    split
    next h =>
      simp_all only [Fin.isValue, Fin.val_zero, OfNat.zero_ne_ofNat]
      rw [Fin.eq_mk_iff_val_eq] at h
      simp only [Fin.coe_castSucc, Fin.val_last] at h
      omega
    next h =>
      split
      next h_1 =>
        simp_all only [Fin.isValue, Fin.val_one, OfNat.one_ne_ofNat]
        rw [Fin.eq_mk_iff_val_eq] at h_1
        simp only [Fin.coe_castSucc, Fin.val_last] at h_1
        omega
      next h_1 => simp_all only [Fin.isValue, Fin.val_two]
  | cast i =>
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      simp [Fin.predAbove]
      split
      next h =>
        simp_all
        split
        next h_1 =>
          simp_all only [Fin.coe_pred, Fin.coe_castSucc, Fin.isValue]
          split
          next
            h_2 => omega
          next h_2 =>
            simp_all only [not_lt, Fin.isValue]
            split
            next h_2 =>
              simp_all only [Fin.isValue, Fin.val_one, add_left_inj]
              exfalso
              rw [Fin.le_iff_val_le_val] at h_2
              simp only [Fin.coe_castSucc, Fin.val_succ, add_le_add_iff_right,
                Fin.val_fin_le] at h_2
              omega
            next h_2 => omega
        next h_1 =>
          simp_all only [not_lt, Fin.isValue, add_right_inj]
          split
          next h_2 => omega
          next h_2 =>
            simp_all only [not_lt, Fin.isValue]
            split
            next h_2 => simp_all only [Fin.isValue, Fin.val_one]
            next h_2 =>
              simp_all only [not_le, Fin.isValue, Fin.val_two, OfNat.ofNat_ne_one]
              apply h_2.not_le
              rw [Fin.le_iff_val_le_val] at h_1 ⊢
              aesop
      next h =>
        simp_all
        split
        next => omega
        next => aesop
  -/
