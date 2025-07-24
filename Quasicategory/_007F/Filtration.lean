import Quasicategory._007F.Basic
import Quasicategory.Lex

open CategoryTheory Simplicial MonoidalCategory SSet Subcomplex

variable {n : ℕ}

namespace σ

noncomputable
def filtration (n : ℕ) (i : Σₗ (b : Fin n), Fin b.succ) :
    (Δ[n] ⊗ Δ[2]).Subcomplex :=
  ∂Δ[n].unionProd Λ[2, 1] ⊔
    (⨆ (j) (_ : j ≤ i), ofSimplex (σ.simplex j).1)

lemma filtration_bot :
    filtration (n + 1) ⊥ = ∂Δ[n + 1].unionProd Λ[2, 1] ⊔ ofSimplex (σ.simplex ⊥).1 := by
  simp [σ.filtration]

lemma filtration_succ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    filtration (n + 1) (Sigma.Lex.succ i) =
      filtration (n + 1) i ⊔ ofSimplex (σ.simplex (Sigma.Lex.succ i)).1 := by
  simp only [filtration]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_sup_left)
    apply iSup₂_le
    intro i' hi'
    cases lt_or_eq_of_le hi'
    · next hi' =>
      exact
        le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le i' (Order.le_of_lt_succ hi') le_rfl))
    · next hi' =>
      subst hi'
      exact le_sup_of_le_right le_rfl
  · apply sup_le
    · exact
      sup_le le_sup_left
        (iSup₂_le fun i' hi' ↦
          le_sup_of_le_right (le_iSup₂_of_le i' (hi'.trans (Sigma.Lex.le_succ i)) le_rfl))
    · exact
      le_sup_of_le_right
        (le_iSup₂_of_le (Sigma.Lex.succ i) (le_refl (Sigma.Lex.succ i)) fun i_1 ⦃a⦄ a ↦ a)

lemma filtration_monotone (n : ℕ) : Monotone (filtration n) := fun _ _ h ↦
  sup_le le_sup_left
    (iSup₂_le fun i hi ↦
      le_sup_of_le_right (le_iSup₂_of_le i (hi.trans h) fun _ _ a ↦ a))

end σ

namespace τ

noncomputable
def filtration (n : ℕ) (i : Σₗ (b : Fin (n + 2)), Fin b.succ) :
    (Δ[n + 1] ⊗ Δ[2]).Subcomplex :=
  (σ.filtration (n + 1) ⊤) ⊔ (⨆ (j) (_ : j ≤ i), ofSimplex (τ.simplex j).1)

lemma filtration_bot :
    filtration n ⊥ = σ.filtration (n + 1) ⊤ ⊔ ofSimplex (τ.simplex ⊥).1 := by
  simp [filtration, σ.filtration]

lemma filtration_succ (i : Σₗ (b : Fin (n + 2)), Fin b.succ) :
    filtration n (Sigma.Lex.succ i) =
      filtration n i ⊔ ofSimplex (τ.simplex (Sigma.Lex.succ i)).1 := by
  simp only [filtration]
  apply le_antisymm
  · apply sup_le (le_sup_of_le_left le_sup_left)
    apply iSup₂_le
    intro i' hi'
    cases lt_or_eq_of_le hi'
    · next hi' =>
      exact
        le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le i' (Order.le_of_lt_succ hi') le_rfl))
    · next hi' =>
      subst hi'
      exact le_sup_of_le_right le_rfl
  · apply sup_le
    · exact
      sup_le le_sup_left
        (iSup₂_le fun i' hi' ↦
          le_sup_of_le_right (le_iSup₂_of_le i' (hi'.trans (Sigma.Lex.le_succ i)) le_rfl))
    · exact
      le_sup_of_le_right
        (le_iSup₂_of_le (Sigma.Lex.succ i) (le_refl (Sigma.Lex.succ i)) fun i_1 ⦃a⦄ a ↦ a)

lemma filtration_last :
    filtration n ⊤ = ⊤ := by
  dsimp [filtration]
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro x hx
  obtain ⟨i, hi⟩ := τ.nonDegenerateEquiv.surjective ⟨x, hx⟩
  obtain rfl : τ.simplex i = x := by rw [τ.simplex, hi]
  rw [← Subcomplex.ofSimplex_le_iff]
  exact le_sup_of_le_right (le_iSup₂_of_le i le_top le_rfl)

lemma filtration_monotone (n : ℕ) : Monotone (filtration n) := fun _ _ h ↦
  sup_le le_sup_left
    (iSup₂_le fun i hi ↦
      le_sup_of_le_right (le_iSup₂_of_le i (hi.trans h) fun _ _ a ↦ a))

end τ
