import Quasicategory._007F.Nondegenerate

namespace SSet

open CategoryTheory Simplicial MonoidalCategory SSet

variable {n : ℕ}

noncomputable
abbrev σ.s (i : Σₗ (b : Fin n), Fin b.succ) :
    Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (σ.simplex i)

noncomputable abbrev τ.t (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  yonedaEquiv.symm (τ.simplex i)

noncomputable
def σ.subcomplex (i : Σₗ (b : Fin n), Fin b.succ) := Subcomplex.ofSimplex (σ.simplex i)

noncomputable
def τ.subcomplex (i : Σₗ (b : Fin (n + 1)), Fin b.succ) := Subcomplex.ofSimplex (τ.simplex i)

instance (i : Σₗ (b : Fin n), Fin b.succ) : Mono (σ.s i) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (σ.nonDegenerateEquiv.toFun i).2

instance (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : Mono (τ.t i) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1 (τ.nonDegenerateEquiv i).2

instance {p q n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet) _⦋n⦌) :
    x ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate n ↔ Mono (yonedaEquiv.symm x) := by
  rw [prodStdSimplex.nonDegenerate_iff', stdSimplex.mono_iff]

example (X : SSet) (n : ℕ) (x : X _⦋n⦌) (A : X.Subcomplex) :
    Subcomplex.range (yonedaEquiv.symm x) ≤ A ↔ (x ∈ A.obj _) := by
  constructor
  · intro h
    apply h
    use (stdSimplex.objEquiv.symm (𝟙 _))
    rw [← stdSimplex.yonedaEquiv_map, CategoryTheory.Functor.map_id, yonedaEquiv_symm_app_id]
  · intro h k y ⟨f, hy⟩
    rw [← hy]
    --have := (A.toSSet.map (stdSimplex.objEquiv f).op ⟨x, h⟩).2
    have : (A.toSSet.map (stdSimplex.objEquiv f).op ⟨x, h⟩) =
      (yonedaEquiv.symm x).app k f := by
      dsimp only [Opposite.op_unop, Subpresheaf.toPresheaf_map_coe]
      rw [SSet.yonedaEquiv_symm_app_apply x f]
    rw [← this]
    exact Subtype.coe_prop (A.toSSet.map (stdSimplex.objEquiv f).op ⟨x, h⟩)

end SSet
