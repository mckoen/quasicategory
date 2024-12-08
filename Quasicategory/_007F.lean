import Quasicategory._007F_1

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory

-- `0 ≤ i ≤ j ≤ m`
variable (m : ℕ)

/-- `[m + 1] → [m]`, defined for each `0 ≤ i ≤ j < m`. -/
def f_aux₁ (i j : Fin m) (hij : i ≤ j) : Fin (m + 2) →o Fin (m + 1) where
  toFun k :=
    if (k : ℕ) ≤ i then k
    else k - 1
  monotone' := by
    intro k k' (hk : (k : ℕ) ≤ k')
    by_cases (k : ℕ) ≤ i; all_goals by_cases (k' : ℕ) ≤ i; all_goals rename_i h h'; simp only [h, ↓reduceIte, h']
    · exact (Fin.natCast_le_natCast (le_trans h i.prop.le) (le_trans h' i.prop.le)).mpr hk
    · rw [not_le] at h'
      have : (k : ℕ) ≤ k' - 1 := Nat.le_sub_one_of_lt (Nat.lt_of_le_of_lt h h')
      sorry
    · exfalso; exact h (le_trans hk h')
    · sorry

/-- `[m + 2] → [m]`, defined for each `0 ≤ i ≤ j ≤ m`. -/
def g_aux₁ (i j : Fin (m + 1)) (hij : i ≤ j) : Fin (m + 3) →o Fin (m + 1) where
  toFun k :=
    if (k : ℕ) ≤ i then k
    else if (k : ℕ) ≤ j + 1 then k - 1
    else k - 2
  monotone' := sorry
    /-
    by
    intro k k' (hk : (k : ℕ) ≤ k')
    by_cases (k : ℕ) ≤ i; all_goals rename_i h
    · simp [h]
      by_cases (k' : ℕ) ≤ i; all_goals rename_i h'
      · simp [h']
        have := (Fin.natCast_le_natCast (le_trans h i.prop.le) (le_trans h' i.prop.le)).mpr hk
        sorry
      · simp [h']
        sorry
    · simp [h]
      have a : ¬ (k' : ℕ) ≤ i := by
        rw [not_le] at h ⊢
        exact Nat.lt_of_lt_of_le h hk
      by_cases (k : ℕ) ≤ j + 1; all_goals rename_i h'
      · simp [h, h', a]
        sorry
      · have b : ¬ (k' : ℕ) ≤ j + 1 := by
          rw [not_le] at h' ⊢
          exact Nat.lt_of_lt_of_le h' hk
        simp [h, h', a, b]
        have := Nat.sub_le_sub_right hk 2
        sorry
    -/

/-- `[m + 1] → [2]`. -/
def f_aux₂ (i j : Fin m) : Fin (m + 2) →o Fin 3 where
  toFun k :=
    if (k : ℕ) ≤ i then 0
    else if (k : ℕ) ≤ j + 1 then 1
    else 2
  monotone' := sorry
    /-
    by
    intro k k' (hk : (k : ℕ) ≤ k')
    by_cases (k : ℕ) ≤ i; all_goals rename_i h
    · simp only [h, ↓reduceIte, Fin.isValue, Fin.zero_le]
    · have a : ¬ (k' : ℕ) ≤ i := by
        rw [not_le] at h ⊢
        exact Nat.lt_of_lt_of_le h hk
      by_cases (k : ℕ) ≤ j + 1; all_goals rename_i h'
      · simp only [h, ↓reduceIte, h', Fin.isValue, a, ge_iff_le]
        aesop
      · have b : ¬ (k' : ℕ) ≤ j + 1 := by
          rw [not_le] at h' ⊢
          exact Nat.lt_of_lt_of_le h' hk
        simp only [h, ↓reduceIte, h', Fin.isValue, a, b, le_refl]
    -/

/-- `[m + 2] → [2]`. -/
abbrev g_aux₂ (i j : Fin (m + 1)) : Fin (m + 3) →o Fin 3 := f_aux₂ (m + 1) i j

open SimplexCategory FunctorToTypes in
def f (i j : Fin m) (hij : i ≤ j) : Δ[m + 1] ⟶ Δ[m] ⊗ Δ[2] :=
  prod.lift (standardSimplex.map <| mkHom (f_aux₁ m i j hij)) (standardSimplex.map <| mkHom (f_aux₂ m i j))

open SimplexCategory in
instance (i j : Fin m) (hij : i ≤ j) : Mono (f m i j hij) := by
  have : ∀ k, Mono ((f m i j hij).app k) := by
    sorry
  apply NatTrans.mono_of_mono_app

open SimplexCategory FunctorToTypes in
def g (i j : Fin (m + 1)) (hij : i ≤ j) : Δ[m + 2] ⟶ Δ[m] ⊗ Δ[2] :=
  prod.lift (standardSimplex.map <| mkHom (g_aux₁ m i j hij)) (standardSimplex.map <| mkHom (g_aux₂ m i j))

open SimplexCategory in
instance : Mono (g m i j hij) := by
  have : ∀ k, Mono ((g m i j hij).app k) := by
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
/-- `fᵢⱼ` as a simplicial subset of `Δ[m] ⊗ Δ[2]`. -/
noncomputable
def σ (i j : Fin m) (hij : i ≤ j) : SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  imagePresheaf (f m i j hij)

open GrothendieckTopology in
/-- `gᵢⱼ` as a simplicial subset of `Δ[m] ⊗ Δ[2]`. -/
noncomputable
def τ (i j : Fin (m + 1)) (hij : i ≤ j) : SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  imagePresheaf (g m i j hij)

/-- `Δ[m + 1] ≅ σᵢⱼ ⊆ Δ[m] ⊗ Δ[2]`. -/
noncomputable
def m_succ_simplex_iso_σ (i j : Fin m) (hij : i ≤ j) : Δ[m + 1] ≅ (σ m i j hij).toPresheaf :=
  SimplicialSubset.mono_iso (f m i j hij)

/-- `Δ[m + 2] ≅ τᵢⱼ ⊆ Δ[m] ⊗ Δ[2]`. -/
noncomputable
def m_succ_simplex_iso_τ (i j : Fin (m + 1)) (hij : i ≤ j) : Δ[m + 2] ≅ (τ m i j hij).toPresheaf :=
  SimplicialSubset.mono_iso (g m i j hij)

open GrothendieckTopology in
/-- each pair `0 ≤ i ≤ j < m` determines a map `Λ[m + 1, i + 1] ⟶ (σ m i j)`. -/
noncomputable
def horn_to_σ (i j : Fin m) (hij : i ≤ j) : Λ[m + 1, i + 1] ⟶ (σ m i j hij).toPresheaf :=
  Subpresheaf.lift _ (hornInclusion (m + 1) (i + 1) ≫ f m i j hij) (fun _ ⟨x, _⟩ ↦ ⟨x, rfl⟩)

lemma horn_to_σ_eq (i j : Fin m) (hij : i ≤ j) : (horn_to_σ m i j hij) =
    (hornInclusion (m + 1) (i + 1)) ≫ (m_succ_simplex_iso_σ m i j hij).hom := rfl

-- since `0 ≤ j < m` (so `1 ≤ m`), we shift up by 1 so inner horn stuff works
-- when `m = 0`, get `Λ[2, 1] ⟶ σ 1 0 0`
-- `0 ≤ i ≤ j ≤ m`
/-- the map `Λ[m + 1 + 1, i + 1] ⟶ (σ (m + 1) i j)` is inner anodyne. This should just follow
from closure under composition with isomorphisms. -/
lemma horn_to_σ_innerAnodyne (m : ℕ) (i j : Fin (m + 1)) (hij : i ≤ j) :
    innerAnodyne (horn_to_σ (m + 1) i j hij) := sorry /-by
  intro X Y g hg
  refine ⟨?_⟩
  intro α β sq
  rw [horn_to_σ_eq] at sq
  let w' : α ≫ g = (hornInclusion (m + 1 + 1) (i + 1)) ≫ ((m_succ_simplex_iso_σ (m + 1) i j hij).hom ≫ β) := sq.w
  have h0 : 0 < (i + 1 : Fin (m + 2 + 1)) := by
    rw [← Fin.sub_one_lt_iff]
    simp_all only [add_sub_cancel_right, Fin.lt_add_one_iff]
    sorry
  have hn : (i + 1 : Fin (m + 2 + 1)) < Fin.last (m + 2) := sorry
  let L := ((hg (@InnerHornInclusion.mk m (i + 1) h0 hn)).sq_hasLift (CommSq.mk w')).exists_lift.some
  refine ⟨⟨⟨(m_succ_simplex_iso_σ (m + 1) i j hij).inv ≫ L.l, ?_, ?_⟩⟩⟩
  · have := L.fac_left
    rw [horn_to_σ_eq]
    aesop
  · rw [Category.assoc, L.fac_right, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]-/

open GrothendieckTopology in
/-- each pair `0 ≤ i ≤ j < m` determines a map `Λ[m + 2, i + 1] ⟶ (τ m i j)`. -/
noncomputable
def horn_to_τ (i j : Fin (m + 1)) (hij : i ≤ j) : Λ[m + 2, i + 1] ⟶ (τ m i j hij).toPresheaf :=
  Subpresheaf.lift _ (hornInclusion (m + 2) (i + 1) ≫ g m i j hij) (fun _ ⟨x, _⟩ ↦ ⟨x, rfl⟩)

lemma horn_to_τ_eq (i j : Fin (m + 1)) (hij : i ≤ j) : (horn_to_τ m i j hij) =
    (hornInclusion (m + 2) (i + 1)) ≫ (m_succ_simplex_iso_τ m i j hij).hom := rfl

lemma horn_to_τ_innerAnodyne (m : ℕ) (i j : Fin (m + 1)) (hij : i ≤ j) :
    innerAnodyne (horn_to_τ m i j hij) := sorry /-by
  intro X Y g hg
  refine ⟨?_⟩
  intro α β sq
  rw [horn_to_τ_eq] at sq
  let w' : α ≫ g = (hornInclusion (m + 2) (i + 1)) ≫ ((m_succ_simplex_iso_τ m i j hij).hom ≫ β) := sq.w
  have h0 : 0 < (i + 1 : Fin (m + 2 + 1)) := sorry
  have hn : (i + 1 : Fin (m + 2 + 1)) < Fin.last (m + 2) := sorry
  let L := ((hg (@InnerHornInclusion.mk (m ) (i + 1) h0 hn)).sq_hasLift (CommSq.mk w')).exists_lift.some
  refine ⟨⟨⟨(m_succ_simplex_iso_τ (m ) i j hij).inv ≫ L.l, ?_, ?_⟩⟩⟩
  · have := L.fac_left
    rw [horn_to_τ_eq]
    aesop
  · rw [Category.assoc, L.fac_right, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]-/

/-
noncomputable
def X_0 := (pushoutProduct_IsPushout (boundaryInclusion m) (hornInclusion 2 1)).cocone.pt

instance : Mono (pushoutProduct (boundaryInclusion m) (hornInclusion 2 1)) := sorry
-/

open GrothendieckTopology in
noncomputable
def X_0 : SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  imagePresheaf (pushoutProduct (hornInclusion 2 1) (boundaryInclusion m))

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
def X (m : ℕ) (j : Fin m) : SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  (X_0 m) ⊔ (⨆ (i : Fin m) (_ : i < j) (k : Fin m) (hk : k ≤ i), σ m k i hk)

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


/-
/-- `Xⱼ₊₁` for `0 ≤ j < m` -/
noncomputable
def X (m : ℕ) (j : Fin m) : SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  (X_0 m) ⊔ (⨆ (i : ℕ) (hi : i ∈ Finset.range (j + 1)) (k : ℕ) (hk : k ∈ Finset.range (i + 1)), σ' i hi k hk)
-/

-- need to show inner anodyne = wsc generated by inner horn inclusions
-- the class inner anodyne morphisms is the weakly saturated class generated by the pushout maps given in `to_Δ`
lemma innerAnodyne_eq_T : innerAnodyne.{0} = (WeaklySaturatedClassOf.{0} bdryPushoutClass) := by
  rw [innerAnodyne_eq]
  ext X Y f
  refine ⟨?_, ?_⟩ -- other direction is more technical
  intro h
  refine minimalWeaklySaturated.{0} (WeaklySaturatedClassOf bdryPushoutClass) InnerHornInclusions ?_ (by infer_instance) _ h
  intro A B g hg
  induction hg with
  | @mk n i h0 hn =>
    apply WeaklySaturatedOf.retract -- reduces to showing horn inclusion is a retract of a boundary pushout maps
    · exact hornRetract (n + 2) i h0 hn
    · exact monomorphisms_le_S (hornInclusion (n + 2) i) (hornInclusion_mono _ _)
  refine minimalWeaklySaturated InnerHornInclusions.WeaklySaturatedClassOf bdryPushoutClass ?_ (by infer_instance) f
  intro _ _ f hf
  induction hf with | @mk m =>
  rw [← innerAnodyne_eq]
  -- show that the pushout product of ∂Δ[m] ⟶ Δ[m] and Λ[2, 1] ⟶ Δ[2] is generated by inner anodyne maps
  sorry

-- `007F` (a)
lemma monoPushout_innerAnodyne {A B : SSet} (i : A ⟶ B) [hi : Mono i] :
    innerAnodyne.{0} (pushoutProduct i (hornInclusion 2 1)) := by
  rw [innerAnodyne_eq_T]
  exact monomorphisms_le_S i hi

-- `007F` (b)
-- inner Anodyne morphisms are generated by the pushout maps given in `to_Δ`
lemma contains_innerAnodyne_iff_contains_pushout_maps
    (S : MorphismProperty SSet.{0}) (hS : WeaklySaturated.{0} S) :
    (∀ m, S (pushoutProduct (boundaryInclusion m) (hornInclusion 2 1))) ↔ (∀ {X Y : SSet} (p : X ⟶ Y) (_ : innerAnodyne p), S p) := by
  refine ⟨?_, fun h m ↦ h _ (monoPushout_innerAnodyne (boundaryInclusion m))⟩
  intro h X Y p hp
  rw [innerAnodyne_eq_T] at hp
  refine minimalWeaklySaturated.{0} S bdryPushoutClass ?_ hS _ hp
  intro _ _ _ hf
  induction hf with
  | @mk m => exact h m

end SSet
