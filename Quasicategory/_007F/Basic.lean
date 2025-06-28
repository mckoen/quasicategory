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

abbrev σ.simplex (i : Σₗ (b : Fin n), Fin b.succ) := σ.nonDegenerateEquiv.toFun i

noncomputable
abbrev τ.simplex (i : Σₗ (b : Fin (n + 1)), Fin b.succ) := τ.nonDegenerateEquiv i

noncomputable
abbrev σ.ιSimplex (i : Σₗ (b : Fin n), Fin b.succ) :
    Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (σ.simplex i)

noncomputable abbrev τ.ιSimplex (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (τ.simplex i)

lemma σ.eq_f (i : Σₗ (b : Fin n), Fin b.succ) :
    σ.ιSimplex i = f ⟨i.2, by omega⟩ i.1 := by
  simp [ιSimplex, f, simplex, nonDegenerateEquiv.toFun, σ']
  congr
  exact (Nat.mod_eq_of_lt (by omega)).symm
  ext
  simp [objMk₂, f₂, f₂']
  congr
  all_goals
    simp [Fin.ext_iff]
    omega

lemma τ.eq_g (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    τ.ιSimplex i = g ⟨i.2, by omega⟩ i.1 := rfl

lemma τ.eq_τ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    Subcomplex.ofSimplex (τ.simplex i).1 = τ ⟨i.2, by omega⟩ i.1 := by
  simp [τ, simplex, nonDegenerateEquiv, nonDegenerateEquiv.toFun, τ', g,
    Subcomplex.range_eq_ofSimplex]
  rfl

lemma σ.eq_σ (i : Σₗ (b : Fin n), Fin b.succ) :
    Subcomplex.ofSimplex (σ.simplex i).1 = σ ⟨i.2, by omega⟩ i.1 := by
  simp [σ, Subcomplex.range_eq_ofSimplex, σ]
  congr
  simp [σ, simplex, nonDegenerateEquiv.toFun, σ', f,
    Subcomplex.range_eq_ofSimplex]
  congr
  exact (Nat.mod_eq_of_lt (by omega)).symm
  ext
  simp [objMk₂, f₂, f₂']
  congr
  all_goals
    simp [Fin.ext_iff]
    omega

-- f is a mono
instance (i : Σₗ (b : Fin n), Fin b.succ) : Mono (σ.ιSimplex i) := by
  rw [stdSimplex.mono_iff]
  refine (prodStdSimplex.nonDegenerate_iff' _).1 (σ.nonDegenerateEquiv.toFun i).2

-- g is a mono
instance (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : Mono (τ.ιSimplex i) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (τ.nonDegenerateEquiv i).2

open stdSimplex

open SimplexCategory in
instance f_mono {a b : Fin n} (hab : a ≤ b) : Mono (f a b) := by
  have : Mono (σ.ιSimplex ⟨b, ⟨a, by simp; omega⟩⟩) := by infer_instance
  convert this
  rw [σ.eq_f]

open SimplexCategory in
/-- only works for `0 ≤ a ≤ b ≤ n` -/
instance g_mono {a b : Fin (n + 1)} (hab : a ≤ b) : Mono (g a b) := by
  change Mono (τ.ιSimplex ⟨b, ⟨a, by simp ;omega⟩⟩)
  infer_instance
