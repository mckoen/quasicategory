import Quasicategory._007F.Nondegenerate

open CategoryTheory Simplicial MonoidalCategory SSet

variable {n : ℕ}

abbrev σ.simplex (i : Σₗ (b : Fin n), Fin b.succ) := nonDegenerateEquiv.toFun i

noncomputable
abbrev τ.simplex (i : Σₗ (b : Fin (n + 1)), Fin b.succ) := nonDegenerateEquiv i

noncomputable
abbrev σ.f (i : Σₗ (b : Fin n), Fin b.succ) :
    Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (simplex i)

noncomputable abbrev τ.g (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (simplex i)

noncomputable
def σ (i : Σₗ (b : Fin n), Fin b.succ) := Subcomplex.ofSimplex (σ.simplex i).1

noncomputable
def τ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) := Subcomplex.ofSimplex (τ.simplex i).1

instance (i : Σₗ (b : Fin n), Fin b.succ) : Mono (σ.f i) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (σ.nonDegenerateEquiv.toFun i).2

instance (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : Mono (τ.g i) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (τ.nonDegenerateEquiv i).2
