import Quasicategory._007F_1

/-!

The second half of the proof of `007F`, which is much more technical.

-/

universe w


open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

-- `0 ≤ i ≤ j ≤ n`
variable (n : ℕ)

/-- `[n + 1] → [n]`, defined for each `0 ≤ a ≤ b < n`. -/
def f₁ (a b : Fin n) (hab : a ≤ b) : Fin (n + 2) →o Fin (n + 1) where
  toFun k :=
    if (k : ℕ) ≤ a then k
    else k - 1
  monotone' := sorry

/-- `[n + 2] → [n]`, defined for each `0 ≤ a ≤ b ≤ n`. -/
def g₁ (a b : Fin (m + 1)) (hab : a ≤ b) : Fin (n + 3) →o Fin (n + 1) where
  toFun k :=
    if (k : ℕ) ≤ a then k
    else if (k : ℕ) ≤ b + 1 then k - 1
    else k - 2
  monotone' := sorry

/-- `[n + 1] → [2]`. -/
def f₂ (a b : Fin n) : Fin (n + 2) →o Fin 3 where
  toFun k :=
    if (k : ℕ) ≤ a then 0
    else if (k : ℕ) ≤ b + 1 then 1
    else 2
  monotone' := sorry

/-- `[n + 2] → [2]`. -/
abbrev g₂ (a b : Fin (n + 1)) : Fin (n + 3) →o Fin 3 := f₂ (n + 1) a b

open SimplexCategory FunctorToTypes in
def f (a b : Fin n) (hab : a ≤ b) : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2] :=
  prod.lift (standardSimplex.map <| mkHom (f₁ n a b hab))
    (standardSimplex.map <| mkHom (f₂ n a b))

open SimplexCategory in
instance (a b : Fin n) (hab : a ≤ b) : Mono (f n a b hab) := by
  have : ∀ k, Mono ((f n a b hab).app k) := by
    sorry
  apply NatTrans.mono_of_mono_app

open SimplexCategory FunctorToTypes in
def g (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2] :=
  prod.lift (standardSimplex.map <| mkHom (g₁ n a b hab))
    (standardSimplex.map <| mkHom (g₂ n a b))

open SimplexCategory in
instance : Mono (g n a b hab) := by
  have : ∀ k, Mono ((g n a b hab).app k) := by
    intro k
    simp only [g, FunctorToTypes.prod.lift]
    rw [CategoryTheory.mono_iff_injective]
    intro x y h
    rw [Prod.ext_iff] at h
    obtain ⟨h₁, h₂⟩ := h
    dsimp at h₁ h₂
    simp [standardSimplex] at h₁
    sorry
  apply NatTrans.mono_of_mono_app

open GrothendieckTopology in
/-- `fᵢⱼ` as a simplicial subset of `Δ[n] ⊗ Δ[2]`. -/
noncomputable
def σ (a b : Fin n) (hab : a ≤ b) : SimplicialSubset (Δ[n] ⊗ Δ[2]) :=
  imagePresheaf (f n a b hab)

open GrothendieckTopology in
/-- `gᵢⱼ` as a simplicial subset of `Δ[n] ⊗ Δ[2]`. -/
noncomputable
def τ (a b : Fin (n + 1)) (hab : a ≤ b) : SimplicialSubset (Δ[n] ⊗ Δ[2]) :=
  imagePresheaf (g n a b hab)

/-- `Δ[n + 1] ≅ σᵢⱼ ⊆ Δ[n] ⊗ Δ[2]`. -/
noncomputable
def m_succ_simplex_iso_σ (a b : Fin n) (hab : a ≤ b) : Δ[n + 1] ≅ (σ n a b hab).toPresheaf :=
  SimplicialSubset.mono_iso (f n a b hab)

/-- `Δ[n + 2] ≅ τᵢⱼ ⊆ Δ[n] ⊗ Δ[2]`. -/
noncomputable
def m_succ_simplex_iso_τ (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n + 2] ≅ (τ n a b hab).toPresheaf :=
  SimplicialSubset.mono_iso (g n a b hab)

open GrothendieckTopology in
/-- each pair `0 ≤ a ≤ b < n` determines a map `Λ[n + 1, i + 1] ⟶ (σ n a b)`. -/
noncomputable
def horn_to_σ (a b : Fin n) (hab : a ≤ b) :
    Λ[n + 1, a + 1] ⟶ (σ n a b hab).toPresheaf :=
  Subpresheaf.lift _ (hornInclusion (n + 1) (a + 1) ≫ f n a b hab) (fun _ ⟨x, _⟩ ↦ ⟨x, rfl⟩)

lemma horn_to_σ_eq (i j : Fin m) (hij : i ≤ j) : (horn_to_σ m i j hij) =
    (hornInclusion (m + 1) (i + 1)) ≫ (m_succ_simplex_iso_σ m i j hij).hom := rfl

-- since `0 ≤ b < n` (so `1 ≤ n`), we shift up by 1 so inner horn stuff works
-- when `n = 0`, get `Λ[2, 1] ⟶ σ 1 0 0`
-- `0 ≤ a ≤ b ≤ m`
/-- the map `Λ[n + 1 + 1, a + 1] ⟶ (σ (n + 1) a b)` is inner anodyne. This should just follow
from closure under composition with isomorphisms. -/
lemma horn_to_σ_innerAnodyne (a b : Fin (n + 1)) (hab : a ≤ b) :
    innerAnodyne (horn_to_σ (n + 1) a b hab) := sorry

open GrothendieckTopology in
/-- each pair `0 ≤ a ≤ b ≤ n` determines a map `Λ[n + 2, a + 1] ⟶ (τ n a b)`. -/
noncomputable
def horn_to_τ (a b : Fin (n + 1)) (hab : a ≤ b) : Λ[n + 2, a + 1] ⟶ (τ n a b hab).toPresheaf :=
  Subpresheaf.lift _ (hornInclusion (n + 2) (a + 1) ≫ g n a b hab) (fun _ ⟨x, _⟩ ↦ ⟨x, rfl⟩)

lemma horn_to_τ_eq (a b : Fin (n + 1)) (hab : a ≤ b) : (horn_to_τ n a b hab) =
    (hornInclusion (n + 2) (a + 1)) ≫ (m_succ_simplex_iso_τ n a b hab).hom := rfl

lemma horn_to_τ_innerAnodyne (a b : Fin (n + 1)) (hab : a ≤ b) :
    innerAnodyne (horn_to_τ n a b hab) := sorry


open GrothendieckTopology in
noncomputable
def X_0 : SimplicialSubset (Δ[n] ⊗ Δ[2]) :=
  imagePresheaf (PushoutProduct.pushoutProduct (hornInclusion 2 1) (boundaryInclusion n))

instance : Mono (PushoutProduct.pushoutProduct (hornInclusion 2 1) (boundaryInclusion n) ) := sorry

noncomputable
def X_0_iso : (PushoutProduct.pt (hornInclusion 2 1) (boundaryInclusion n)) ≅ (X_0 n).toPresheaf :=
  SimplicialSubset.mono_iso (PushoutProduct.pushoutProduct _ _)

example (j : Fin m) (i : ℕ) (hi : i ∈ Finset.range (j + 1)) : Fin m :=
  ⟨i, Nat.lt_of_le_of_lt (Finset.mem_range_succ_iff.mp hi) j.isLt⟩

/-
-- fix 0 ≤ j < m, let k ≤ i ≤ j. This gives σ m k i
noncomputable
def σ'' {m : ℕ} {j : Fin m} (i : ℕ) (hi : i ∈ Finset.range (j + 1)) (k : ℕ) (hk : k ∈ Finset.range (i + 1)) :
    SimplicialSubset (Δ[m] ⊗ Δ[2]) := by
  refine σ m ⟨k, ?_⟩ ⟨i, ?_⟩ (Finset.mem_range_succ_iff.mp hk)
  · exact Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (List.mem_range.mp hk)) (Nat.lt_of_lt_of_le (List.mem_range.mp hi) (j.isLt))
  · exact Nat.lt_of_lt_of_le (List.mem_range.mp hi) (j.isLt)
-/

-- fix 0 ≤ j < m, let k ≤ i < j. This gives σ m k i
noncomputable
def σ' {m : ℕ} {j : Fin m} (i : ℕ) (hi : i < j) (k : ℕ) (hk : k ≤ i) :
    SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  σ m ⟨k, (lt_of_le_of_lt hk hi).trans j.isLt⟩ ⟨i, hi.trans j.isLt⟩ hk

/-!

X(j+1) = X(j) ∪ σ_{0j} ∪ ... ∪ σ_{jj}

X0 = X0 ∪ nothing
X1 = X0 ∪ σ_{00}
X2 = X1 ∪ σ_{01} ∪ σ_{11} = X0 ∪ σ_{00} ∪ σ_{01} ∪ σ_{11}

X(j) = X0 ∪ (σ_{00}) ∪ (σ_{01} ∪ σ_{11}) ∪ (σ_{02} ∪ σ_{12} ∪ σ_{22}) ∪ ... ∪ (σ_{0{j-1}} ∪ ... ∪ σ_{{j-1}{j-1}})

X(j + 1) = X(j) ∪ (σ_{0j} ∪ ... ∪ σ_{jj})

-/

/-- `Xⱼ` for `0 ≤ j < m` -/
noncomputable
def X (b : Fin n) : SimplicialSubset (Δ[n] ⊗ Δ[2]) :=
  (X_0 n) ⊔ (⨆ (i : Fin n) (_ : i < b) (k : Fin n) (hk : k ≤ i), σ n k i hk)

--right map
noncomputable
def X_succ_map (b : Fin n) (hb : b + 1 < n) : (X n b) ⟶ (X n ⟨b + 1, hb⟩) := by
  apply homOfLE
  dsimp [X]
  apply sup_le_sup
  rfl
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  have : i < ⟨b + 1, hb⟩ := by
    refine lt_of_lt_of_le hi ?_
    refine (Fin.le_of_lt ?_)
    exact Set.Ici_subset_Ioi.mp fun ⦃a⦄ a ↦ a
  apply le_iSup_of_le i
  apply le_iSup_of_le this
  apply le_iSup_of_le k
  apply le_iSup_of_le hk
  rfl

--bottom map
noncomputable
def σ_X_map (a b : Fin n) (hab : a ≤ b) (hb : b + 1 < n) : (σ n a b hab) ⟶ (X n ⟨b + 1, hb⟩) := by
  apply homOfLE
  dsimp [X]
  apply le_sup_of_le_right
  apply le_iSup_of_le b
  apply le_iSup_of_le _
  apply le_iSup_of_le a
  apply le_iSup_of_le hab
  rfl
  exact Set.Ici_subset_Ioi.mp fun ⦃a⦄ a ↦ a

/-
noncomputable
def Xi (m : ℕ) (j : Fin m) (i : Fin m) (_ : i < j) : SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  (X_0 m) ⊔ (⨆ (k : Fin m) (hk : k ≤ i), σ m k i hk)

open GrothendieckTopology in
def X_succ_map (m : ℕ) (j : Fin m) (hj : j + 1 < m) :
    (X m j).toPresheaf ⟶ (X m ⟨j + 1, hj⟩).toPresheaf where
  app a := fun ⟨x, hx⟩ ↦ by
    refine ⟨x, ?_⟩
    cases hx with
    | inl h => exact .inl h
    | inr h =>
    right
    cases h with
    | intro w h =>
      refine ⟨w, ⟨?_, h.2⟩⟩
      obtain ⟨⟨i, ⟨p, hp⟩⟩, h⟩ := h.1
      sorry
-/


/-
/-- `Xⱼ₊₁` for `0 ≤ j < m` -/
noncomputable
def X (m : ℕ) (j : Fin m) : SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  (X_0 m) ⊔ (⨆ (i : ℕ) (hi : i ∈ Finset.range (j + 1)) (k : ℕ) (hk : k ∈ Finset.range (i + 1)), σ' i hi k hk)
-/

lemma innerAnodyne_eq_T : innerAnodyne = (WeaklySaturatedClassOf.{w} bdryPushoutClass) := by
  rw [innerAnodyne_eq]
  ext X Y f
  refine ⟨?_, ?_⟩ -- other direction is more technical
  intro h
  refine minimalWeaklySaturated bdryPushoutClass.WeaklySaturatedClassOf InnerHornInclusions ?_ (by infer_instance) _ h
  intro A B g hg
  induction hg with
  | @mk n i h0 hn =>
    apply WeaklySaturatedOf.retract -- reduces to showing horn inclusion is a retract of a boundary pushout maps
    · exact hornRetract (n + 2) i h0 hn
    · exact monomorphisms_le_S.{w} (hornInclusion (n + 2) i) (hornInclusion_mono _ _)
  refine minimalWeaklySaturated InnerHornInclusions.WeaklySaturatedClassOf bdryPushoutClass ?_ (by infer_instance) f
  intro _ _ f hf
  induction hf with | @mk m =>
  rw [← innerAnodyne_eq]
  -- show that the pushout product of ∂Δ[m] ⟶ Δ[m] and Λ[2, 1] ⟶ Δ[2] is generated by inner anodyne maps
  sorry

-- `007F` (a)
lemma monoPushout_innerAnodyne {A B : SSet} (i : A ⟶ B) [hi : Mono i] :
    innerAnodyne (PushoutProduct.pushoutProduct i (hornInclusion 2 1)) := by
  rw [innerAnodyne_eq_T.{w}]
  exact monomorphisms_le_S.{w} i hi

-- `007F` (b)
lemma contains_innerAnodyne_iff_contains_pushout_maps
    (S : MorphismProperty SSet) (hS : WeaklySaturated S) :
    (∀ m, S (PushoutProduct.pushoutProduct (boundaryInclusion m) (hornInclusion 2 1))) ↔ (∀ {X Y : SSet} (p : X ⟶ Y) (_ : innerAnodyne p), S p) := by
  refine ⟨?_, fun h m ↦ h _ (monoPushout_innerAnodyne.{w} (boundaryInclusion m))⟩
  intro h X Y p hp
  rw [innerAnodyne_eq_T] at hp
  refine minimalWeaklySaturated S bdryPushoutClass ?_ hS _ hp
  intro _ _ _ hf
  induction hf with
  | @mk m => exact h m
