import Quasicategory._007F.Basic

open CategoryTheory Simplicial MonoidalCategory SSet

variable {n : ℕ}

/-- `X(b)` for `0 ≤ b ≤ n`. Goes up to `X(n) = Y(0)`, the first object in the `τ` filtration.
`X(b) = X(0) ⊔ ... ⊔ [σ0(b-1) ⊔ σ1(b-1) ⊔ ... ⊔ σ(b-1)(b-1)]`. -/
noncomputable
def filtration₁ (b : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (boundary n).unionProd (horn 2 1) ⊔
    (⨆ (i : Fin b) (k : Fin i.succ), σ ⟨k, by omega⟩ ⟨i, by omega⟩) -- 0 ≤ k ≤ i < b

/-- `X(0)` is just the `unionProd`. -/
lemma filtration₁_zero :
    filtration₁ 0 = (boundary n).unionProd (horn 2 1) := by simp [filtration₁]

/-- `X(b) ↪ X(b + 1)` for `b < n` is just the union of `X(b.castSucc)` with `[σ0b ⊔ ... ⊔ σbb]`. -/
lemma filtration₁_succ (b : Fin n) :
    filtration₁ b.succ =
      filtration₁ b.castSucc ⊔ (⨆ (i : Fin b.succ), σ ⟨i, by omega⟩ b) := by
  simp [filtration₁]
  apply le_antisymm
  · apply sup_le
    · apply le_sup_of_le_left (le_sup_of_le_left le_rfl)
    · apply iSup₂_le
      intro i k
      cases (lt_or_eq_of_le i.is_le)
      · next h => exact le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le ⟨i, h⟩ k le_rfl))
      · next h =>
        apply le_sup_of_le_right <| le_iSup_of_le ⟨k, by omega⟩ _
        simp [h]
  · apply sup_le
    · apply sup_le le_sup_left
      · exact le_sup_of_le_right
          (iSup₂_le fun i k ↦ le_iSup₂_of_le ⟨i, Nat.lt_add_right 1 i.isLt⟩ k le_rfl)
    · refine le_sup_of_le_right (iSup_le fun i ↦ le_iSup₂_of_le ⟨b, by simp⟩ i le_rfl)

/-- `X(b,a) = X(b) ⊔ ... ⊔ σab` for `0 ≤ a ≤ b < n`. -/
noncomputable
def filtration₂ (b : Fin n) (a : Fin b.succ) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₁ b.castSucc) ⊔ (⨆ (k : Fin a.succ), σ ⟨k, by omega⟩ b)

/-- `X(b,0) = X(b) ∪ (σ 0 b)` for `0 ≤ b < n` -/
lemma filtration₂_zero (hn : n ≠ 0) (b : Fin n) :
    filtration₂ b ⟨0, Nat.zero_lt_succ b⟩ =
      filtration₁ b.castSucc ⊔ (σ ⟨0, by omega⟩ b) := by
  simp [filtration₂]

/-- `X(b,b) = X(b+1)` for `0 ≤ b < n` -/
lemma filtration₂_last (b : Fin n) :
    filtration₂ b ⟨b, Nat.lt_add_one b⟩ = filtration₁ b.succ := by
  rw [filtration₁_succ]
  simp [filtration₂]

/-- `X(b,a) ↪ X(b,a+1)` for `0 ≤ a < b < n` is just the union of `X(b,a)` with `σ(a+1)b`. -/
lemma filtration₂_succ (b : Fin n) (a : Fin b) :
    filtration₂ b a.succ = (filtration₂ b a.castSucc) ⊔
      (σ ⟨a.succ, by omega⟩ b) := by
  dsimp [filtration₂]
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_sup_left) (iSup_le fun ⟨i, hi⟩ ↦ ?_)
    cases lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    · next h => exact le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le ⟨i, h⟩ (le_rfl)))
    · next h =>
      subst h
      exact le_sup_of_le_right le_rfl
  · apply sup_le
    · exact sup_le le_sup_left
        (le_sup_of_le_right (iSup_le (fun i ↦ le_iSup_of_le ⟨i, by omega⟩ le_rfl)))
    · exact le_sup_of_le_right (le_iSup_of_le ⟨a + 1, lt_add_one _⟩ le_rfl)

/-- `Y(b)` for `0 ≤ b ≤ n + 1`. Goes up to `Y(n + 1) = ⊤`.
`Y(b) = X(n) ⊔ ... ⊔ [τ0(b-1) ⊔ τ1(b-1) ⊔ ... ⊔ τ(b-1)(b-1)]`. -/
noncomputable
def filtration₃ (b : Fin (n + 2)) :
    (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₁ (Fin.last n)) ⊔
    (⨆ (i : Fin b) (k : Fin i.succ), τ ⟨k, by omega⟩ ⟨i, by omega⟩)  -- 0 ≤ k ≤ i < b ≤ n + 1

/-- `Y(0) = X(n)`. -/
lemma filtration₃_zero :
    filtration₃ (0 : Fin (n + 2)) = filtration₁ ⟨n, by omega⟩ := by
  simp [filtration₃]
  rfl

/-- `Y(b) ↪ Y(b+1)` for `b < n + 1` is just the union of `Y(b.castSucc)` with `[τ0b ⊔ ... ⊔ τbb]`. -/
lemma filtration₃_succ (b : Fin (n + 1)) :
    filtration₃ b.succ =
      filtration₃ b.castSucc ⊔ -- 0 ≤ i ≤ b, ⨆ τib
        (⨆ (i : Fin b.succ), τ ⟨i, by omega⟩ b) := by
    dsimp [filtration₁]
    apply le_antisymm
    · apply sup_le (le_sup_of_le_left (le_sup_of_le_left le_rfl))
      · apply iSup₂_le (fun i k ↦ ?_)
        cases (lt_or_eq_of_le i.is_le)
        · next h => exact le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le ⟨i, h⟩ k le_rfl))
        · next h =>
          refine le_sup_of_le_right (le_iSup_of_le ⟨k, by simp [← h]⟩ ?_)
          simp [h]
    · apply sup_le
      · apply sup_le (le_sup_of_le_left le_rfl)
        · exact le_sup_of_le_right
            (iSup₂_le fun i k ↦ le_iSup₂_of_le ⟨i, Nat.lt_add_right 1 i.isLt⟩ k le_rfl)
      · exact le_sup_of_le_right (iSup_le fun i ↦ le_iSup₂_of_le ⟨b, Nat.lt_add_one b⟩ i le_rfl)

-- should maybe redefine the filtration in terms of the equivalence between the τ's and the nondegen
-- simplices
lemma filtration₃_last : filtration₃ n.succ = (⊤ : (Δ[n] ⊗ Δ[2]).Subcomplex) := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro x hx
  obtain ⟨i, hi⟩ := τ.nonDegenerateEquiv.surjective ⟨x, hx⟩
  obtain rfl : τ.simplex i = x := by rw [τ.simplex, hi]
  rw [filtration₃, ← Subcomplex.ofSimplex_le_iff]
  apply le_sup_of_le_right
  rw [τ.eq_τ i]
  apply le_iSup₂_of_le ⟨i.1, by simp⟩ ⟨i.2, by simp⟩
  exact le_rfl

/-- `Y(b,a) = Y(b) ⊔ ... ⊔ τab` for `0 ≤ a ≤ b ≤ n`. -/
noncomputable
def filtration₄ (b : Fin (n + 1)) (a : Fin b.succ) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (filtration₃ b.castSucc) ⊔ (⨆ (k : Fin a.succ), τ ⟨k, by omega⟩ b)

/-- `Y(b,0) = Y(b) ∪ (τ0b)` for `0 ≤ b ≤ n`. -/
lemma filtration₄_zero (b : Fin (n + 1)) :
    filtration₄ b ⟨0, Nat.zero_lt_succ b⟩ = filtration₃ b ⊔ (τ 0 b) := by
  simp [filtration₄]

/-- `Y(b,a) ↪ Y(b,a+1)` for `0 ≤ a < b ≤ n` is just the union of `Y(b,a)` with `τ(a+1)b`. -/
lemma filtration₄_succ (b : Fin (n + 1)) (a : Fin b) :
    filtration₄ b a.succ = (filtration₄ b a.castSucc) ⊔
      (τ ⟨a.succ, by omega⟩ b) := by
  simp [filtration₄]
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_sup_left) (iSup_le fun ⟨i, hi⟩ ↦ ?_)
    cases lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    · next h => exact le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le ⟨i, h⟩ le_rfl))
    · next h =>
      subst h
      exact le_sup_of_le_right le_rfl
  · apply sup_le
    · exact sup_le le_sup_left
        (le_sup_of_le_right (iSup_le fun i ↦ le_iSup_of_le ⟨i, Nat.lt_add_right 1 i.2⟩ le_rfl))
    · exact le_sup_of_le_right (le_iSup_of_le ⟨a + 1, lt_add_one _⟩ le_rfl)

/-- `Y(b,b) = X(b + 1)` for `0 ≤ b ≤ n`. -/
lemma filtration₄_last (b : Fin (n + 1)) :
    filtration₄ b ⟨b, Nat.lt_add_one b⟩ = filtration₃ b.succ := by
  rw [filtration₃_succ]
  simp [filtration₄]

lemma filtration₄_last' : filtration₄ (Fin.last n) ⟨n, by simp⟩ = (⊤ : (Δ[n] ⊗ Δ[2]).Subcomplex) := by
  dsimp [Fin.last]
  rw [← filtration₃_last, filtration₄_last]
  aesop

open Subcomplex

-- need n ≠ 0, so take n + 1

noncomputable
def filtration₁' (i : Σₗ (b : Fin n), Fin b.succ) :
    (Δ[n] ⊗ Δ[2]).Subcomplex :=
  ∂Δ[n].unionProd Λ[2, 1] ⊔
    (⨆ (j) (_ : j ≤ i), ofSimplex (σ.simplex j).1)

lemma filtration₁_zero' :
    filtration₁' ⊥ = ∂Δ[n + 1].unionProd Λ[2, 1] ⊔ ofSimplex (σ.simplex ⊥).1 := by
  simp [filtration₁']

lemma filtration₁_succ' (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    filtration₁' (Sigma.Lex.succ i) =
      filtration₁' i ⊔ ofSimplex (σ.simplex (Sigma.Lex.succ i)).1 := by
  simp only [filtration₁']
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

noncomputable
def filtration₂' (i : Σₗ (b : Fin (n + 2)), Fin b.succ) : (Δ[n + 1] ⊗ Δ[2]).Subcomplex :=
  (filtration₁' ⊤) ⊔ (⨆ (j) (_ : j ≤ i), ofSimplex (τ.simplex j).1)

lemma filtration₂_zero' :
    filtration₂' (n := n) ⊥ = filtration₁' ⊤ ⊔ ofSimplex (τ.simplex ⊥).1 := by
  simp [filtration₂', filtration₁']

lemma filtration₂_succ' (i : Σₗ (b : Fin (n + 2)), Fin b.succ) :
    filtration₂' (Sigma.Lex.succ i) =
      filtration₂' i ⊔ ofSimplex (τ.simplex (Sigma.Lex.succ i)).1 := by
  simp only [filtration₂']
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

lemma filtration₂_last' :
    filtration₂' (n := n) ⊤ = ⊤ := by
  dsimp [filtration₂']
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro x hx
  obtain ⟨i, hi⟩ := τ.nonDegenerateEquiv.surjective ⟨x, hx⟩
  obtain rfl : τ.simplex i = x := by rw [τ.simplex, hi]
  rw [← Subcomplex.ofSimplex_le_iff]
  exact le_sup_of_le_right (le_iSup₂_of_le i le_top le_rfl)

lemma filtration₁_monotone : Monotone (filtration₁' (n := n)) := fun _ _ h ↦
  sup_le le_sup_left
    (iSup₂_le fun i hi ↦
      le_sup_of_le_right (le_iSup₂_of_le i (hi.trans h) fun _ _ a ↦ a))

lemma filtration₂_monotone : Monotone (filtration₂' (n := n)) := fun _ _ h ↦
  sup_le le_sup_left
    (iSup₂_le fun i hi ↦
      le_sup_of_le_right (le_iSup₂_of_le i (hi.trans h) fun _ _ a ↦ a))
