import Quasicategory._007F.Filtration
import Quasicategory._007F.Order

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

universe u

variable {n : ℕ}

namespace σ

variable (b : Fin n) (i : Σₗ (b : Fin n), Fin b.succ)

/-- the image of `Λ[n + 1, i.snd + 1]` under `f i`. -/
@[simp]
noncomputable
abbrev innerHornImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  Λ[n + 1, ⟨i.snd.succ, by omega⟩].image (f i)

lemma innerHornImage_eq_iSup : innerHornImage i =
    ⨆ (j : ({⟨i.snd.succ, by omega⟩}ᶜ : Set (Fin (n + 2)))), (face {j.1}ᶜ).image (f i) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup]

/-- each face of `σ b a` except the `a`-th and `a + 1`-th is contained in `∂Δ[n] ⊗ Δ[2]`. -/
lemma face_ne_snd_succ_image_le_boundary_prod_top (a : Fin b.succ) (j : Fin (n + 2))
    (hj : ¬j = ⟨a, by omega⟩) (hj' : ¬j = ⟨a.succ, by omega⟩) :
    (face {j}ᶜ).image (f ⟨b, a⟩) ≤ ∂Δ[n].prod ⊤ := by
  simp [face_singleton_compl]
  refine ⟨?_, Set.mem_univ _⟩
  change ¬Function.Surjective (Fin.predAbove _ ∘ j.succAbove)
  intro h
  have : j < ⟨a, by omega⟩ ∨ ⟨a.succ, by omega⟩ < j := by
    cases Fin.lt_or_lt_of_ne hj'
    all_goals cases Fin.lt_or_lt_of_ne hj; try omega
    any_goals omega
    · next q q' =>
      exfalso
      apply not_lt.2 q' q
  cases this
  · next hj =>
    obtain ⟨i, hi⟩ := h ⟨j, lt_trans hj (by simp; omega)⟩
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj
    split at hi
    · next h' =>
      simp [show ¬a.1 < i.1 by omega, Fin.eq_mk_iff_val_eq] at hi
      omega
    · next h' =>
      split at hi
      all_goals simp [Fin.eq_mk_iff_val_eq] at hi
      · next h'' =>
        simp at h''
        omega
      · next h'' => omega
  · next hj =>
    obtain ⟨i, hi⟩ := h (j.pred (Fin.ne_zero_of_lt hj))
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj
    split at hi
    · next h' =>
      split at hi
      · next => aesop
      · next h'' =>
        simp at h''
        simp_all
        omega
    · next h'' =>
      simp [show a.1 < i + 1 by omega] at hi
      aesop

/-- the `0`-th face of `σ b 0` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma face_zero_image_le_top_prod_horn :
    (face {0}ᶜ).image (f ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩) ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (objMk₂.{u} ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩ ∘ Fin.succ) ∪ {1} ≠ Set.univ
  intro h
  rw [Set.eq_univ_iff_forall] at h
  have h := h 0
  simp at h
  obtain ⟨e, h⟩ := h
  simp [objMk₂] at h
  have := h (Nat.zero_lt_succ _)
  split at this
  all_goals omega

/-- for `0 ≤ a < b < n` the `(a + 1)`-th face of `σ b (a + 1)` is the `(a + 1)`-th face of
  `σ b a`. -/
lemma face_snd_succ_image_eq (a : Fin b) :
    (face {⟨a.succ, by omega⟩}ᶜ).image (f ⟨b, a.succ⟩) =
      (face {⟨a.succ, by omega⟩}ᶜ).image (f ⟨b, a.castSucc⟩) := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk, f,
      simplex, nonDegenerateEquiv.toFun, σ', objMk₂]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Nat.mod_eq_of_lt]
  · split
    · next h => simp [h.le.not_lt, show (¬ a.1 < e) by omega]
    · next => simp [show (a.1 < e) by omega, show (a.1 < e + 1) by omega]
  · split
    · next h =>
      simp [show e.1 ≤ (a.1) % (n + 1 + 1) by rw [Nat.mod_eq_of_lt (by omega)]; omega,
        show ¬(a.1 + 1) % (n + 1 + 1) < e.1 by rw [Nat.mod_eq_of_lt (by omega)]; omega]
    · next h =>
      rw [not_lt] at h
      have : a.1 + 1 < e.succ := Nat.add_lt_of_lt_sub h
      have := this.not_le
      simp [show ¬e.1.succ ≤ (a.1 + 1) % (n + 1 + 1) by rw [Nat.mod_eq_of_lt (by omega)]; omega,
        show ¬e.1.succ ≤ (a.1) % (n + 1 + 1) by rw [Nat.mod_eq_of_lt (by omega)]; omega]

/-- for `0 ≤ a < b < n`, the `(a + 1)`-th face of `σ b (a + 1)` is contained in `σ b a`. -/
lemma face_snd_succ_image_le (a : Fin b) :
    (face {⟨a.succ, by omega⟩}ᶜ).image (f ⟨b, a.succ⟩) ≤ σ ⟨b, a.castSucc⟩ := by
  rw [face_snd_succ_image_eq, σ, ofSimplex_eq_range]
  exact image_le_range _ _

/-- for `0 ≤ a < b < n`, the image of `Λ[n + 1, a + 2]` under `f b (a + 1)` is contained
  in `X(b, a)`. -/
lemma innerHornImage_intermediate_le_filtration (a : Fin b) :
    innerHornImage ⟨b, a.succ⟩ ≤ filtration n ⟨b, a.castSucc⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a.succ, by omega⟩ -- check whether the face is the (a + 1)-th
  · subst h
    refine le_sup_of_le_right (le_iSup_of_le ⟨b, a.castSucc⟩ ?_)
    simp only [Fin.val_succ, le_refl, iSup_pos]
    exact face_snd_succ_image_le b a
  · exact le_sup_of_le_left
      (le_sup_of_le_right (face_ne_snd_succ_image_le_boundary_prod_top b a.succ j h hj))

/-- for `0 ≤ b < n`, the image of `Λ[n + 1, 1]` under `f b 0` is contained in `X(b, b)`. -/
lemma innerHornImage_join_le_filtration :
    innerHornImage ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩ ≤
      filtration (n + 1) ⟨b.castSucc, ⟨b, Nat.lt_add_one _⟩⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  by_cases h : j = 0
  · subst h
    exact le_sup_of_le_left
      ((face_zero_image_le_top_prod_horn.{u} b.succ).trans (top_prod_le_unionProd _ _))
  · exact le_sup_of_le_left
      ((face_ne_snd_succ_image_le_boundary_prod_top _ _ j h hj).trans (prod_top_le_unionProd _ _))

open Sigma.Lex in
lemma innerHornImage_succ_le_filtration (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    innerHornImage (succ i) ≤ filtration (n + 1) i := by
  obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
  · rw [Fin.succ_last_eq_last]
    apply le_sup_of_le_right (le_iSup_of_le ⟨Fin.last n, Fin.last n⟩ _)
    simp [ofSimplex_eq_range, image_le_range]
  · rw [Fin.succ_eq₁]
    exact innerHornImage_intermediate_le_filtration b a
  · rw [Fin.succ_eq₂]
    exact innerHornImage_join_le_filtration.{u} b

lemma innerHornImage_bot_le_unionProd : innerHornImage ⊥ ≤ ∂Δ[n + 1].unionProd Λ[2, 1] := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  obtain rfl | ⟨j, rfl⟩ := (Fin.eq_zero_or_eq_succ j)
  · exact le_sup_of_le_left
      (face_zero_image_le_top_prod_horn.{u} 0)
  · exact le_sup_of_le_right
      (face_ne_snd_succ_image_le_boundary_prod_top _ _ j.succ (Fin.succ_ne_zero _) hj)

/-- for `0 ≤ a < b < n`, the `a + 2`-th face of `σ b (a + 1)` is not contained in
  `Δ[n] ⊗ Λ[2, 1]`. -/
lemma face_snd_succ_succ_image_not_le_top_prod_horn (a : Fin b) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (f ⟨b, a.succ⟩)
      ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  rw [mem_horn_iff]
  simp
  change insert 1 (Set.range (objMk₂.{u} _ ∘ Fin.succAbove _)) = Set.univ
  ext i
  fin_cases i
  all_goals simp [Fin.succAbove, objMk₂]
  · use a.succ
    simp [Fin.lt_iff_val_lt_val]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Fin.lt_iff_val_lt_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp
  · use b.succ
    simp [Fin.lt_iff_val_lt_val, show ¬b.1 < a.1 + 1 by omega]
    split
    · next h =>
      simp [Fin.le_iff_val_le_val] at h
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    · simp [Fin.le_iff_val_le_val]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

lemma face_one_image_not_le_top_prod_horn :
    ¬ (face {1}ᶜ).image (f ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl, filtration, unionProd]
  refine Set.nmem_setOf_iff.2 ?_
  simp [mem_horn_iff]
  change insert 1 (Set.range ((objMk₂.{u} ⟨b.succ, _⟩).down.toOrderHom ∘ Fin.succAbove _)) = Set.univ
  ext i
  fin_cases i
  all_goals simp [Fin.succAbove, objMk₂, objMk]
  · use 0
    aesop
  · use b.succ.succ
    simp [Fin.lt_iff_val_lt_val]
    simp [SimplexCategory.Hom.mk, SimplexCategory.Hom.toOrderHom, objEquiv, Equiv.ulift]
    simp [Fin.le_iff_val_le_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- for `0 ≤ a < b < n`, the `((a + 1) + 1)`-th face of `σ (a + 1) b` is not contained in
  `∂Δ[n] ⊗ Δ[2]`. -/
lemma face_snd_succ_succ_image_not_le_boundary_prod_top (a : Fin b) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (f ⟨b, a.succ⟩)
      ≤ ∂Δ[n].prod ⊤ := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary]
  change Function.Surjective (Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
  intro i
  use i
  dsimp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp [Fin.lt_iff_val_lt_val]
  split
  all_goals
    simp
    omega

lemma face_one_image_not_le_boundary_prod_top :
    ¬ (face {1}ᶜ).image (f ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ ∂Δ[n + 1].prod ⊤ := by
  simp [face_singleton_compl, filtration, unionProd]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary, f]
  change Function.Surjective (Fin.predAbove 0 ∘ (Fin.succ 0).succAboveOrderEmb)
  intro i
  use i
  simp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp_rw [Fin.lt_iff_val_lt_val]
  aesop

/-- for `0 ≤ a < b < n`, the `((a + 1) + 1)`-th face of `σ (a + 1) b` is not contained in
  `σ i j` for any `0 ≤ i ≤ j < b`. -/
lemma face_snd_succ_succ_image_not_le_σ (a j : Fin b) (i : Fin j.succ) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (f ⟨b, a.succ⟩)
      ≤ σ ⟨⟨j, by omega⟩, ⟨i, by simp⟩⟩ := by
  dsimp [σ]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [f, simplex, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ', objMk, objMk₂] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  simp  at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  cases lt_or_eq_of_le (show a.1 + 1 ≤ b.1 from a.2)
  all_goals
    replace h₁ := congr_fun h₁ b.castSucc
    replace h₂ := congr_fun h₂ b.castSucc
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
  · next h =>
    simp [show ¬b.1 < a.1 + 1 + 1 by omega, show ¬b.1 ≤ a.1 by omega] at h₁ h₂
    split at h₂
    · next h' =>
      rw [Nat.mod_eq_of_lt (by omega)] at h'
      simp [h'.not_lt, Fin.ext_iff] at h₁
      omega
    · next h' =>
      rw [Nat.mod_eq_of_lt (by omega), not_le] at h'
      simp [h', Fin.ext_iff] at h₁
      split at h₂
      · next h'' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h''
        omega
      · next h'' =>
        split at h₂
        · omega
        · next h'' =>
          split at h₂
          · omega
          · next h'' =>
            rw [Nat.mod_eq_of_lt (by omega)] at h''
            omega
  · next h =>
    simp_rw [← h] at h₁ h₂
    have p : ¬(a.1 + 1) % (n + 1) < b.1 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [show a.1 + 1 < a.1 + 1 + 1 by omega, h.symm.le, p] at h₁ h₂
    split at h₁
    · next h' =>
      simp [Fin.ext_iff, h.not_lt] at h₁
      split at h₂
      · next h'' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h''
        omega
      · split at h₂
        · next h'' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h''
          omega
        · split at h₂
          · omega
          · next h'' =>
            rw [Nat.mod_eq_of_lt (by omega)] at h''
            omega
    · next h' =>
      simp [Fin.ext_iff] at h₁
      rw [Nat.mod_eq_of_lt (by omega)] at p
      simp [p] at h₁
      omega

/-- for `0 ≤ a < b < n`, the `a + 2`-th face of `σ b (a + 1)` is not contained in
  `σ b i` for any `0 ≤ i ≤ a`. -/
lemma face_snd_succ_succ_image_not_le_σ' (a : Fin b) (i : Fin a.succ) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (f ⟨b, a.succ⟩)
      ≤ σ ⟨b, ⟨i, by simp; omega⟩⟩ := by
  dsimp [σ]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [f, simplex, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ', objMk, objMk₂] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  dsimp at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  replace h₁ := congr_fun h₁ ⟨a.succ, by omega⟩
  replace h₂ := congr_fun h₂ ⟨a.succ, by omega⟩
  simp [Fin.succAbove, Fin.predAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
  split at h₁
  · next h =>
    simp [Fin.ext_iff] at h₁
    split at h₂
    · next h =>
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    · split at h₂
      · simp [show a.1 + 1 ≤ (a + 1) % (n + 1 + 1) by rw [Nat.mod_eq_of_lt (by omega)]] at h₂
      · next h =>
        rw [Nat.mod_eq_of_lt (by omega)] at h
        omega
  · next h =>
    simp [Fin.ext_iff] at h₁
    omega

open Sigma.Lex in
lemma face_snd_succ_succ_image_not_le_σ_le (i j : Σₗ (b : Fin (n + 1)), Fin b.succ) (h : j ≤ i) (hn : i < ⊤) :
    ¬ (face {⟨(succ i).2.succ, by omega⟩}ᶜ).image (f (succ i)) ≤ σ j := by
  obtain ⟨b', a'⟩ := j
  obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := (Sigma.Lex.Fin.cases i)
  · exfalso
    rwa [top_eq_last, lt_self_iff_false] at hn
  · rw [Fin.succ_eq₁]
    cases h
    · next h =>
      exact face_snd_succ_succ_image_not_le_σ b a ⟨b', h⟩ ⟨a', by simp⟩
    · next h =>
      simp [Fin.le_iff_val_le_val] at h
      exact face_snd_succ_succ_image_not_le_σ' b' a ⟨a', by simp; omega⟩
  · rw [Fin.succ_eq₂]
    simp
    dsimp [σ]
    rw [ofSimplex_eq_range]
    simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
      Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
    intro x h'
    simp [f, simplex, nonDegenerateEquiv.toFun] at h'
    have h₁ := congr_arg Prod.fst h'
    have h₂ := congr_arg Prod.snd h'
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ', objMk, objMk₂] at h₁ h₂
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
    dsimp at h₁ h₂
    change _ ∘ x = _ at h₁ h₂
    replace h₁ := congr_fun h₁ ⟨b.succ, by omega⟩
    replace h₂ := congr_fun h₂ ⟨b.succ, by omega⟩
    simp [Fin.succAbove, Fin.predAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
    split at h₂
    · aesop
    · next h'' =>
      rw [Nat.mod_eq_of_lt (by omega), not_le] at h''
      simp [h'', Fin.ext_iff] at h₁
      rw [h₁, Nat.mod_eq_of_lt (by omega)] at h₂
      split at h₂
      · simp [Fin.le_iff_val_le_val] at h
        cases h
        · next h =>
          simp [Fin.lt_iff_val_lt_val] at h
          omega
        · aesop
      · rw [Nat.mod_eq_of_lt (by omega)] at h₂
        simp at h₂

open Sigma.Lex in
lemma face_snd_succ_succ_image_succ_not_le_filtration (i : Σₗ (b : Fin (n + 1)), Fin b.succ) (hn : i < ⊤) :
    ¬ (face {⟨(succ i).snd.succ, by omega⟩}ᶜ).image (f (succ i))
      ≤ filtration (n + 1) i := by
  simp only [Fin.val_succ, face_singleton_compl, Subpresheaf.ofSection_image,
    filtration, unionProd, Fin.isValue, Subpresheaf.ofSection_le_iff, Subpresheaf.max_obj,
    prod_obj, Subpresheaf.top_obj, Set.top_eq_univ, Subpresheaf.iSup_obj, iSup_obj, Set.mem_union,
    Set.mem_iUnion, exists_prop, not_or, not_exists, not_and]
  constructor
  · obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
    · exfalso
      rwa [top_eq_last, lt_self_iff_false] at hn
    · rw [Fin.succ_eq₁]
      refine ⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩
      · have := face_snd_succ_succ_image_not_le_top_prod_horn.{u} b a
        simp [face_singleton_compl] at this
        exact this
      · have := face_snd_succ_succ_image_not_le_boundary_prod_top b a
        simp [face_singleton_compl] at this
        exact this
    · rw [Fin.succ_eq₂]
      refine ⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩
      · have := face_one_image_not_le_top_prod_horn.{u} b
        simp [face_singleton_compl] at this
        exact this
      · have := face_one_image_not_le_boundary_prod_top b
        simp [face_singleton_compl] at this
        exact this
  · intro j hj
    simpa only [face_singleton_compl, Subpresheaf.ofSection_image,
      Subpresheaf.ofSection_le_iff] using face_snd_succ_succ_image_not_le_σ_le i j hj hn

open Sigma.Lex in
lemma face_one_image_not_le_unionProd :
    ¬ (face {1}ᶜ).image (f ⊥) ≤ ∂Δ[n + 1].unionProd Λ[2, 1] := by
  simp [face_singleton_compl, filtration, unionProd, bot_eq_zero]
  refine ⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩
  · simp [mem_horn_iff]
    change insert 1 (Set.range ((objMk₂.{u} _).down.toOrderHom ∘ Fin.succAbove _)) = Set.univ
    ext i
    fin_cases i
    · simp
      use 0
      rfl
    · simp
    · simp
      use 1
      rfl
  · simp [boundary]
    change Function.Surjective (Fin.predAbove 0 ∘ (Fin.succ 0).succAboveOrderEmb)
    intro i
    use i
    simp [Fin.predAbove, Fin.succAbove]
    simp_rw [Fin.lt_iff_val_lt_val]
    aesop

open Sigma.Lex in
lemma innerHornImage_succ_le_inf (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    innerHornImage (succ i) ≤
      σ (succ i) ⊓ filtration (n + 1) i := by
  apply le_inf
  · rw [σ, ofSimplex_eq_range]
    exact image_le_range _ _
  · exact innerHornImage_succ_le_filtration.{u} i

open Sigma.Lex in
lemma inf_le_innerHornImage_succ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) (hn : i < ⊤) :
    σ (succ i) ⊓ filtration (n + 1) i ≤
      innerHornImage (succ i) := by
  rw [σ, ofSimplex_eq_range, subcomplex_le_horn_image_iff _ _ inf_le_left, le_inf_iff, not_and]
  exact fun _ ↦ face_snd_succ_succ_image_succ_not_le_filtration.{u} i hn

open Sigma.Lex in
def filtrationPushout_intermediate (n : ℕ) (i : Σₗ (b : Fin (n + 1)), Fin b.succ) (hn : i < ⊤) :
    Sq
      (innerHornImage (succ i))
      (σ (succ i))
      (filtration (n + 1) i)
      (filtration (n + 1) (succ i))
      where
  max_eq := by rw [σ, filtration_succ, sup_comm]
  min_eq := le_antisymm (inf_le_innerHornImage_succ.{u} i hn) (innerHornImage_succ_le_inf.{u} i)

open Sigma.Lex in
def filtrationPushout_zero (n : ℕ) :
    Sq
      (innerHornImage ⊥)
      (σ ⊥)
      (∂Δ[n + 1].unionProd Λ[2, 1])
      (filtration (n + 1) ⊥) where
  max_eq := by simp [σ, filtration, sup_comm]
  min_eq := by
    rw [σ, ofSimplex_eq_range]
    apply le_antisymm
    · rw [subcomplex_le_horn_image_iff, le_inf_iff, not_and]
      · exact fun _ ↦ face_one_image_not_le_unionProd.{u}
      · exact inf_le_left
    · exact le_inf (image_le_range _ _) (innerHornImage_bot_le_unionProd.{u})

end σ
