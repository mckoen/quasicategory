import Quasicategory.Basic
import Quasicategory.PushoutProduct
import Quasicategory.MorphismProperty
import Quasicategory.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Quasicategory.Monomorphism

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory

/-
-- T = WeaklySaturatedOf bdryPushoutClass
-- S is the class of all morphism `i : A → B` such that the pushout product with `Λ[n, i] ↪ Δ[n]` is in T
def S : MorphismProperty SSet := fun _ _ i ↦ (WeaklySaturatedClassOf.{0} bdryPushoutClass) (pushoutProduct i (hornInclusion 2 1))

-- S is weakly saturated because T is
instance S_WeaklySaturated : WeaklySaturated S := sorry

lemma BoundaryInclusions_le_S : BoundaryInclusions ≤ S := fun _ _ _ h ↦ by
  induction h with | mk =>
  apply WeaklySaturatedOf.of
  apply bdryPushout.mk

lemma monomorphisms_le_S : monomorphisms SSet ≤ S := by
  rw [mono_eq_bdryInclusions]
  apply minimalWeaklySaturated _ _ BoundaryInclusions_le_S S_WeaklySaturated

section _007F_1

-- [n] ⟶ [2] by j ↦
-- 0 if j < i
-- 1 if j = i
-- 2 if j > i
def s_aux (i : Fin (n + 1)) : Fin (n + 1) →o Fin 3 where
  toFun j :=   if _ : (j : ℕ) < i then 0 else if _ : (j : ℕ) = i then 1 else 2
  monotone' j k h := by
    dsimp only [dite_eq_ite]
    cases Nat.lt.isWellOrder.trichotomous j i with
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
  standardSimplex.map (SimplexCategory.mkHom (s_aux i))

-- the above map restricted to the horn
def horn_map (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[2] :=
  (hornInclusion n i) ≫ (standard_map n i)

-- on vertices j maps to
-- (j, 0) if j < i
-- (j, 1) if j = i
-- (j, 2) if j > i
def s (n : ℕ) (i : Fin (n + 1)) : Δ[n] ⟶ Δ[2] ⊗ Δ[n] :=
  FunctorToTypes.prod.lift (standard_map n i) (𝟙 _)

def s_restricted (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[2] ⊗ Λ[n, i]  :=
  FunctorToTypes.prod.lift (horn_map n i) (𝟙 _)

noncomputable
def horn_to_pushout (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ (Λ_pushout n i).cocone.pt :=
  s_restricted n i ≫ (Limits.pushout.inl (hornInclusion 2 1 ▷ Λ[n, i]) (Λ[2, 1] ◁ hornInclusion n i))

lemma leftSqCommAux (n : ℕ) (i : Fin (n + 1)) :
    s_restricted n i ≫ Δ[2] ◁ (hornInclusion n i) = (hornInclusion n i) ≫ s n i := rfl

lemma leftSqComm (n : ℕ) (i : Fin (n + 1)) : horn_to_pushout n i ≫ Λ_pushoutProduct n i = (hornInclusion n i) ≫ s n i := by
  rw [← leftSqCommAux]
  dsimp [horn_to_pushout, Λ_pushoutProduct, pushoutProduct]
  rw [Category.assoc, IsPushout.inl_desc]

def r_aux (i : Fin (n + 1)) : Fin 3 × Fin (n + 1) →o Fin (n + 1) where
  toFun := fun ⟨k, j⟩ ↦
    if _ : ((j : ℕ) < i ∧ k = 0) ∨ ((j : ℕ) > i ∧ k = 2) then j else i
  monotone' := by
    intro ⟨k, j⟩ ⟨k', j'⟩ ⟨(hk : k ≤ k'), (hj : j ≤ j')⟩
    cases Nat.lt.isWellOrder.trichotomous j i with
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

open standardSimplex SimplexCategory in
def map_mk_from_prod (f : Fin (n + 1) × Fin (m + 1) →o Fin (k + 1)) : Δ[n] ⊗ Δ[m] ⟶ Δ[k] := by
  refine ⟨fun x ⟨c, d⟩ ↦ ⟨mkHom ⟨fun a ↦ f ((asOrderHom c) a, (asOrderHom d) a), ?_⟩⟩, ?_⟩
  · intro j k hjk
    exact f.monotone ⟨(asOrderHom c).monotone hjk, (asOrderHom d).monotone hjk⟩
  · aesop

-- on vertices j k map to
-- j if (j < i) ∧ (k = 0)
-- j if (j > i) ∧ (k = 2)
-- i if (j = i) ∨ (k = 1)
def r (n : ℕ) (i : Fin (n + 1)) : Δ[2] ⊗ Δ[n] ⟶ Δ[n] := map_mk_from_prod (r_aux i)

variable (n : ℕ) (i : Fin (n + 1)) (h0 : 0 < i) (hn : i < Fin.last n)

-- r restricted along Λ[2, 1]
noncomputable
def r_restrict_horn_2 : Λ[2, 1] ⊗ Δ[n] ⟶ Λ[n, i] where
  app k := by
    intro ⟨⟨x, hx⟩, y⟩
    refine ⟨((hornInclusion 2 1) ▷ Δ[n] ≫ r n i).app k ⟨⟨x, hx⟩, y⟩, ?_⟩
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
                if (asOrderHom y) a < i ∧ (asOrderHom x) a = 0 ∨ i < (asOrderHom y) a ∧ (asOrderHom x) a = 2 then
                  (asOrderHom y) a
                else i) j = 0 at h
      by_cases (asOrderHom y) j < i; all_goals rename_i h'
      · by_cases (asOrderHom x) j = 0; all_goals rename_i h''
        · exact ha j h''
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
                if (asOrderHom y) a < i ∧ (asOrderHom x) a = 0 ∨ i < (asOrderHom y) a ∧ (asOrderHom x) a = 2 then
                  (asOrderHom y) a
                else i) j = Fin.last n at h
      by_cases (asOrderHom y) j < i; all_goals rename_i h'
      · by_cases (asOrderHom x) j = 0; all_goals rename_i h''
        · simp only [h', Nat.reduceAdd, h'', Fin.isValue, and_self, Fin.reduceEq, and_false,
          or_false, ↓reduceIte, Fin.natCast_eq_last] at h
          rw [h] at h'
          exact absurd (lt_trans h' hn) (Fin.not_lt.mpr (Fin.le_last _))
        · simp_all only [Nat.reduceAdd, Fin.isValue, Set.union_singleton, ne_eq, Fin.natCast_eq_last, and_false,
          or_self, ↓reduceIte, lt_self_iff_false]
      · simp_all only [Nat.reduceAdd, Fin.isValue, Set.union_singleton, ne_eq, Fin.natCast_eq_last, false_and,
        and_false, or_self, ↓reduceIte, not_lt, Fin.last_le_iff, lt_self_iff_false]

-- r restricted along Λ[n, i]
noncomputable
def r_restrict_horn_n : Δ[2] ⊗ Λ[n, i] ⟶ Λ[n, i] where
  app k := by
    intro ⟨x, ⟨y, hy⟩⟩
    refine ⟨(Δ[2] ◁ (hornInclusion n i) ≫ r n i).app k ⟨x, ⟨y, hy⟩⟩, ?_⟩
    rw [Set.ne_univ_iff_exists_not_mem] at hy ⊢
    obtain ⟨a, this⟩ := hy
    simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_range, not_or, not_exists] at this
    obtain ⟨ha₁, ha₂⟩ := this
    use a
    intro h
    simp only [ne_eq, Set.union_singleton, Set.mem_insert_iff, ha₁, Set.mem_range, false_or] at h
    obtain ⟨j, hj⟩ := h
    apply ha₂ j
    change (asOrderHom ((r n i).app k (x, y))) j = a at hj
    -- add lemma about (asOrderHom {down := SimplexCategory.Hom.mk {toFun} }) = toFun
    change (fun a ↦
      if (asOrderHom y) a < i ∧ (asOrderHom x) a = 0 ∨ i < (asOrderHom y) a ∧ (asOrderHom x) a = 2 then
        (asOrderHom y) a else i) j = a at hj
    aesop

open standardSimplex SimplexCategory in
noncomputable
def pushout_to_horn : (Λ_pushout n i).cocone.pt ⟶ Λ[n, i] :=
  Limits.pushout.desc (r_restrict_horn_n n i) (r_restrict_horn_2 n i h0 hn) rfl

lemma rightSqComm : pushout_to_horn n i h0 hn ≫ hornInclusion n i = Λ_pushoutProduct n i ≫ r n i := by
  dsimp [pushout_to_horn, Λ_pushoutProduct, pushoutProduct]
  apply Limits.pushout.hom_ext; all_goals aesop

lemma r_comp_s (n : ℕ) (i : Fin (n + 1)) : s n i ≫ r n i = 𝟙 Δ[n] := by
  let r' := r_aux i
  let s' : Fin (n + 1) →o Fin 3 × Fin (n + 1) := (s_aux i).prod (OrderHom.id)
  let f : Fin (n + 1) →o Fin (n + 1) := OrderHom.comp r' s'
  have a : f = OrderHom.id := by
    ext x
    simp [f, r', s', s_aux, r_aux]
    cases Nat.lt.isWellOrder.trichotomous x i with
    | inl h => aesop
    | inr h => cases h with
    | inl h => aesop
    | inr h =>
      simp_all only [Fin.val_fin_lt, Fin.isValue, true_and]
      split
      next h_1 =>
        simp_all only [Fin.isValue, one_ne_zero, imp_false, not_le, and_self]
        split
        next h_2 => simp_all only [Fin.isValue, Fin.reduceEq, or_false, ↓reduceIte]
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
  have : s n i ≫ r n i = standardSimplex.map (SimplexCategory.mkHom f) := rfl
  rw [this, a]
  aesop

lemma restricted_r_comp_s : horn_to_pushout n i ≫ pushout_to_horn n i h0 hn = 𝟙 Λ[n, i] := by
  dsimp [horn_to_pushout, pushout_to_horn]
  rw [Category.assoc, Limits.pushout.inl_desc]
  ext k ⟨x, hx⟩
  change (r_restrict_horn_n n i).app k ((horn_map n i).app k ⟨x, hx⟩, ⟨x, hx⟩) = ⟨x, hx⟩
  simp [r_restrict_horn_n]
  congr
  have := congr_fun (congr_app (r_comp_s n i) k) x
  aesop

noncomputable
instance hornRetract : IsRetract (hornInclusion n i) (Λ_pushoutProduct n i) where
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

end _007F_1

-/

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
/-- the map `Λ[m + 1 + 1, i + 1] ⟶ (σ (m + 1) i j)` is inner anodyne. -/
lemma horn_to_σ_innerAnodyne (m : ℕ) (i j : Fin (m + 1)) (hij : i ≤ j) :
    innerAnodyne (horn_to_σ (m + 1) i j hij) := by
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
  · rw [Category.assoc, L.fac_right, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

open GrothendieckTopology in
/-- each pair `0 ≤ i ≤ j < m` determines a map `Λ[m + 2, i + 1] ⟶ (τ m i j)`. -/
noncomputable
def horn_to_τ (i j : Fin (m + 1)) (hij : i ≤ j) : Λ[m + 2, i + 1] ⟶ (τ m i j hij).toPresheaf :=
  Subpresheaf.lift _ (hornInclusion (m + 2) (i + 1) ≫ g m i j hij) (fun _ ⟨x, _⟩ ↦ ⟨x, rfl⟩)

lemma horn_to_τ_eq (i j : Fin (m + 1)) (hij : i ≤ j) : (horn_to_τ m i j hij) =
    (hornInclusion (m + 2) (i + 1)) ≫ (m_succ_simplex_iso_τ m i j hij).hom := rfl

lemma horn_to_τ_innerAnodyne (m : ℕ) (i j : Fin (m + 1)) (hij : i ≤ j) :
    innerAnodyne (horn_to_τ m i j hij) := by
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
  · rw [Category.assoc, L.fac_right, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

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

end SSet

/-
/-- `Xⱼ₊₁` for `0 ≤ j < m` -/
noncomputable
def X (m : ℕ) (j : Fin m) : SimplicialSubset (Δ[m] ⊗ Δ[2]) :=
  (X_0 m) ⊔ (⨆ (i : ℕ) (hi : i ∈ Finset.range (j + 1)) (k : ℕ) (hk : k ∈ Finset.range (i + 1)), σ' i hi k hk)
-/

/-
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
