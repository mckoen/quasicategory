import Quasicategory._007F.Filtration
import Quasicategory._007F.Order

universe u

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ}

namespace τ

variable (b : Fin (n + 1)) (i : Σₗ (b : Fin (n + 1)), Fin b.succ)

/-- the image of `Λ[n + 2, i.snd + 1]` under `g i`. -/
@[simp]
noncomputable
abbrev innerHornImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  Λ[n + 2, ⟨i.snd.succ, by omega⟩].image (ιSimplex i)

lemma innerHornImage_eq_iSup : innerHornImage i =
    ⨆ (j : ({⟨i.snd.succ, by omega⟩}ᶜ : Set (Fin (n + 3)))), (face {j.1}ᶜ).image (ιSimplex i) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup]

/-- for `0 ≤ a ≤ b ≤ n`, each face of `τ b a` except the `a`-th, `a + 1`-th, `b + 1`-th, and
  `b + 2`-th is contained in `∂Δ[n] ⊗ Δ[2]`. -/
lemma face_ne_fst_snd_succ_image_le_boundary_prod_top (a : Fin b.succ) (j : Fin (n + 3))
    (ha : ¬j = ⟨a, by omega⟩) (ha' : ¬j = ⟨a + 1, by omega⟩)
    (hb : ¬j = b.succ.castSucc) (hb' : ¬j = b.succ.succ) :
      (face {j}ᶜ).image (ιSimplex ⟨b, a⟩) ≤ ∂Δ[n].prod ⊤ := by
  simp [face_singleton_compl]
  refine ⟨?_, Set.mem_univ _⟩
  change ¬ Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAbove _)
  intro h
  have : j < ⟨a, by omega⟩ ∨ ⟨a + 1, by omega⟩ < j := by
    cases Fin.lt_or_lt_of_ne ha
    all_goals cases Fin.lt_or_lt_of_ne ha'; try omega
    any_goals omega
    · next q q' =>
      exfalso
      exact not_le.2 q' q
  cases this
  · next hj =>
    obtain ⟨i, hi⟩ := h ⟨j, by simp [Fin.lt_iff_val_lt_val] at hj ⊢; omega⟩
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj
    split at hi
    · next h' =>
      simp [show ¬a.1 < i.1 by omega, show ¬b.1 < i by omega, Fin.eq_mk_iff_val_eq] at hi
      omega
    · next h' =>
      split at hi
      all_goals
        simp [Fin.eq_mk_iff_val_eq] at hi
        · next h'' =>
          split at hi
          all_goals
            simp at hi h''
            omega
  · next hj =>
    have : j < b.succ.castSucc ∨ b.succ.succ < j := by
      cases Fin.lt_or_lt_of_ne hb'
      all_goals cases Fin.lt_or_lt_of_ne hb; try omega
      any_goals omega
      · next q q' =>
        exfalso
        exact not_lt.2 q' q
    cases this
    . next hj' =>
      simp [Fin.lt_iff_val_lt_val] at hj hj'
      obtain ⟨i, hi⟩ := h ⟨j - 1, by dsimp; omega⟩
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj hj'
      split at hi
      · next h' =>
        split at hi
        · next =>
          simp [show ¬b.1 < i - 1 by omega, Fin.eq_mk_iff_val_eq] at hi
          omega
        · next h'' =>
          simp [show ¬b.1 < i by omega, Fin.eq_mk_iff_val_eq] at hi
          simp_all
          omega
      · next h'' =>
        simp [show a.1 < i + 1 by omega] at hi
        split at hi
        all_goals
          simp [Fin.eq_mk_iff_val_eq] at hi
          omega
    · next hj' =>
      simp [Fin.lt_iff_val_lt_val] at hj hj'
      obtain ⟨i, hi⟩ := h ⟨j - 2, by dsimp; omega⟩
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj hj'
      split at hi
      · next h' =>
        split at hi
        · next h'' =>
          split at hi
          all_goals
            simp [Fin.eq_mk_iff_val_eq] at hi
            simp_all
            omega
        · next h'' =>
          split at hi
          all_goals
            simp [Fin.eq_mk_iff_val_eq] at hi
            simp_all
          simp_all
          omega
          omega
      · next h'' =>
        simp [show a.1 < i + 1 by omega] at hi
        split at hi
        all_goals
          simp [Fin.eq_mk_iff_val_eq] at hi
          omega

/-- for `0 ≤ b ≤ n`, the `0`-th face of `τ b 0` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma face_zero_image_le_top_prod_horn :
    (face {0}ᶜ).image (ιSimplex ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩) ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (objMk₂.{u} ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩ ∘ Fin.succ) ∪ {1} ≠ Set.univ
  rw [ne_eq, Set.union_singleton, Set.eq_univ_iff_forall, not_forall]
  use 0
  simp [objMk₂]
  intro ⟨e, he⟩
  aesop

/-- for `0 ≤ a ≤ n` the `n + 2`-th face of `τ n a` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma face_last_image_le_top_prod_horn (a : Fin (n + 1)) :
    (face {Fin.last (n + 2)}ᶜ).image (ιSimplex ⟨Fin.last n, a⟩) ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl, SimplexCategory.δ, Fin.succAboveOrderEmb]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (objMk₂.{u} _ ∘ Fin.castSucc) ∪ {1} ≠ Set.univ
  rw [ne_eq, Set.eq_univ_iff_forall, not_forall]
  use 2
  simp [objMk₂]
  intro e he
  split at he
  · omega
  · simp [Fin.lt_iff_val_lt_val] at he
    omega

/-- for `0 ≤ a ≤ b < n` the `b + 2`-th face of `τ b a` is `σ b a`. -/
lemma face_fst_succ_succ_image_eq (b : Fin n) (a : Fin b.succ) :
    (face {⟨b + 2, by omega⟩}ᶜ).image (ιSimplex ⟨b.castSucc, a⟩) = σ_ ⟨b, a⟩ := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk, ιSimplex,
      simplex, nonDegenerateEquiv.toFun, σ', objMk₂, nonDegenerateEquiv, τ', σ.simplex,
      σ.nonDegenerateEquiv.toFun, σ.objMk₂, Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split
    · next h' =>
      simp
      split
      · next h'' => simp [show ¬b.1 < e - 1 by omega, h'']
      · next h'' => simp [h'', ((not_lt.1 h'').trans a.is_le).not_lt]
    · next h' =>
      have := a.is_le
      simp [show a.1 < e + 1 by omega, show b.1 < e by omega, show a.1 < e by omega]
  · simp
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
      rfl
    · have := a.is_le
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp [show ¬e.1 + 1 ≤ a by omega, show ¬e.1 ≤ b by omega, show ¬e.1 ≤ a by omega,
        show ¬e.1 ≤ b + 1 by omega]

/-- for `0 ≤ a ≤ b < n` the `b + 2`-th face of `τ (b + 1) a` is `σ b a`. -/
lemma face_fst_succ_succ_image_succ_eq (b : Fin n) (a : Fin b.succ) :
    (face {⟨b + 2, by omega⟩}ᶜ).image (ιSimplex ⟨b.succ, a.castSucc⟩) = σ_ ⟨b, a⟩ := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk, ιSimplex,
      simplex, nonDegenerateEquiv.toFun, σ', objMk₂, nonDegenerateEquiv, τ', σ.simplex,
      σ.nonDegenerateEquiv.toFun, σ.objMk₂, Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split
    · next h =>
      simp
      split
      · simp [show ¬b.1 + 1 < e - 1 by omega]
      · simp [show ¬b.1 + 1 < e by omega]
    · next h =>
      simp [show a.1 < e + 1 by dsimp; omega, show a.1 < e by dsimp; omega]
      split
      · simp
      · omega
  · ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · next h =>
      simp [h.le, show e.1 ≤ b + 1 by omega]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      split
      · rfl
      · simp [show e.1 ≤ b + 1 by omega]
    · next h =>
      rw [not_lt] at h
      simp [show ¬e.1 + 1 ≤ a by dsimp; omega, show ¬e.1 ≤ a by dsimp; omega]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp [show ¬e.1 ≤ b + 1 by omega, show ¬ e.1 ≤ a by simp; omega]

/-- for `0 ≤ a < b ≤ n` the `a + 1`-th face of `τ b (a + 1)` is the `a + 1`-th face of
  `τ b a`. -/
lemma face_snd_succ_image_eq (a : Fin b) :
    (face {⟨a + 1, by omega⟩}ᶜ).image (ιSimplex ⟨b, a.succ⟩) =
      (face {⟨a + 1, by omega⟩}ᶜ).image (ιSimplex ⟨b, a.castSucc⟩) := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk, ιSimplex,
      simplex, nonDegenerateEquiv.toFun, σ', objMk₂, nonDegenerateEquiv, τ', σ.simplex,
      σ.nonDegenerateEquiv.toFun, σ.objMk₂, Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Nat.mod_eq_of_lt]
  · split
    · next h => simp [h.le.not_lt, show (¬ a.1 < e) by omega]
    · next => simp [show (a.1 < e) by omega, show (a.1 < e + 1) by omega]
  · split
    · next h => simp [h.le, show e.1 ≤ a by omega]
    · next =>
      simp [show ¬e.1 ≤ a by omega]
      split
      all_goals simp [show ¬e.1 + 1 ≤ a by omega]

/-- for `0 ≤ a < b ≤ n`, the image of `Λ[n + 2, a + 2]` under `g b (a + 1)` is contained
  in `Y(b, a)`. -/
lemma innerHornImage_intermediate_le_filtration₂ (b : Fin (n + 2)) (a : Fin b) :
    innerHornImage ⟨b, a.succ⟩ ≤ filtration₂' n ⟨b, a.castSucc⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a + 1, by omega⟩
  · subst h
    apply le_sup_of_le_right (le_iSup_of_le ⟨b, a.castSucc⟩ _)
    simp only [Fin.val_succ, face_snd_succ_image_eq, le_refl, ofSimplex_eq_range, iSup_pos]
    exact image_le_range _ _
  · by_cases h' : j = b.succ.castSucc
    · subst h'
      cases b using Fin.cases with
    | zero =>
      apply le_sup_of_le_right
      apply le_iSup_of_le ⟨0, ⟨0, Nat.zero_lt_succ _⟩⟩
      simp only [Fin.succ_zero_eq_one, Fin.castSucc_one, Fin.val_succ, Fin.val_zero, Fin.eq_zero,
        Fin.isValue, Fin.val_one, le_refl, ofSimplex_eq_range, iSup_pos]
      exact image_le_range _ _
    | succ b =>
      have : a.1 < b := by
        apply Nat.lt_of_le_of_ne a.is_le
        simp only [Fin.val_succ, Sigma.Lex.Fin.fst_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
          Fin.ext_iff, Fin.coe_castSucc, add_left_inj] at hj
        omega
      apply le_sup_of_le_left (le_sup_of_le_right _)
      have := face_fst_succ_succ_image_succ_eq b ⟨a.succ, by dsimp; omega⟩
      simp [Fin.succ] at this ⊢
      rw [this]
      exact le_iSup_of_le ⟨b, ⟨a.succ, by dsimp; omega⟩⟩ le_rfl
    by_cases h'' : j = b.succ.succ
    · subst h''
      obtain rfl | ⟨b , rfl⟩ := Fin.eq_last_or_eq_castSucc b
      · exact
        le_sup_of_le_left
          (le_sup_of_le_left (le_sup_of_le_left (face_last_image_le_top_prod_horn.{u} a.succ)))
      · have := face_fst_succ_succ_image_eq b a.succ
        simp [Fin.succ] at this ⊢
        rw [this]
        apply le_sup_of_le_left (le_sup_of_le_right _)
        simp only [σ_, Fin.val_succ, Fin.coe_castSucc, le_top, iSup_pos, ofSimplex_eq_range]
        exact le_iSup_of_le ⟨b, a.succ⟩ le_rfl
    exact
      le_sup_of_le_left
        (le_sup_of_le_left
          (le_sup_of_le_right
            (face_ne_fst_snd_succ_image_le_boundary_prod_top b a.succ j h hj h' h'')))

/-- for `0 ≤ b < n`, the image of `Λ[n + 2, 1]` under `g (b + 1) 0` is contained in `Y(b, b)`. -/
lemma innerHornImage_join_le_filtration₂ :
    innerHornImage ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩ ≤
      filtration₂' n ⟨b.castSucc, ⟨b, Nat.lt_add_one _⟩⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  apply le_sup_of_le_left
  by_cases h : j = 0 -- case for the `0`-th face
  · subst h
    exact (le_sup_of_le_left (le_sup_of_le_left (face_zero_image_le_top_prod_horn.{u} b.succ)))
  · by_cases h' : j = b.succ.succ.castSucc -- case for the `(b + 1)`-th face
    subst h'
    apply le_sup_of_le_right (le_iSup_of_le ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩ _)
    have := face_fst_succ_succ_image_succ_eq b ⟨0, Nat.zero_lt_succ _⟩
    simp [Fin.succ] at this ⊢
    rw [this]
    simp only [Fin.val_succ, Fin.zero_eta, le_top, iSup_pos, σ_]
    exact le_rfl
    by_cases h'' : j = b.succ.succ.succ
    · subst h''
      obtain rfl | ⟨b , rfl⟩ := Fin.eq_last_or_eq_castSucc b
      · exact (le_sup_of_le_left (le_sup_of_le_left (face_last_image_le_top_prod_horn.{u} 0)))
      · have := face_fst_succ_succ_image_eq b.succ ⟨0, Nat.zero_lt_succ _⟩
        simp [Fin.succ] at this ⊢
        rw [this]
        apply (le_sup_of_le_right _)
        simp only [σ_, Fin.val_succ, Fin.coe_castSucc, le_top, iSup_pos, ofSimplex_eq_range]
        exact le_iSup_of_le ⟨b.succ, 0⟩ le_rfl
    exact
      le_sup_of_le_left
        (le_sup_of_le_right
          (face_ne_fst_snd_succ_image_le_boundary_prod_top b.succ ⟨0, Nat.zero_lt_succ _⟩ j h hj h' h''))

open Sigma.Lex in
lemma innerHornImage_succ_le_filtration₂ (i : Σₗ (b : Fin (n + 2)), Fin b.succ) :
    innerHornImage (succ i) ≤ filtration₂' n i := by
  obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
  · rw [Fin.succ_last_eq_last]
    apply le_sup_of_le_right (le_iSup_of_le ⟨Fin.last _, Fin.last _⟩ _)
    simp [ofSimplex_eq_range, image_le_range]
  · rw [Fin.succ_eq₁]
    exact innerHornImage_intermediate_le_filtration₂.{u} b a
  · rw [Fin.succ_eq₂]
    exact innerHornImage_join_le_filtration₂.{u} b

lemma innerHornImage_bot_le_filtration₁ : innerHornImage ⊥ ≤ filtration₁' (n + 1) ⊤ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · exact le_sup_of_le_left (le_sup_of_le_left (face_zero_image_le_top_prod_horn.{u} 0))
  · by_cases h : j = 1
    · subst h
      have := face_fst_succ_succ_image_eq (n := n + 1) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩
      change (face {2}ᶜ).image (ιSimplex ⊥) = _ at this
      dsimp
      rw [this]
      apply le_sup_of_le_right
      apply le_iSup_of_le ⟨0, ⟨0, Nat.zero_lt_succ _⟩⟩
      simp
      exact le_rfl
    · exact le_sup_of_le_left (le_sup_of_le_right
        (face_ne_fst_snd_succ_image_le_boundary_prod_top _ _ j.succ (ne_of_beq_false rfl) hj hj (by simpa [Fin.succ, Fin.ext_iff] using h)))

/-- for `0 ≤ a < b ≤ n`, the `a + 2`-th face of `τ b (a + 1)` is not contained in
  `Δ[n] ⊗ Λ[2, 1]`. -/
lemma face_snd_succ_succ_image_not_le_top_prod_horn (a : Fin b) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (ιSimplex ⟨b, a.succ⟩)
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
    rw [Nat.mod_eq_of_lt (by omega)]
    simp [Fin.lt_iff_val_lt_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp
  · use b.succ
    simp [Fin.lt_iff_val_lt_val, show ¬b.1 < a.1 + 1 by omega]
    omega

lemma face_one_image_not_le_top_prod_horn (b : Fin n) :
    ¬ (face {1}ᶜ).image (ιSimplex ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl, filtration₁', unionProd]
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
    simp [SimplexCategory.Hom.mk, SimplexCategory.Hom.toOrderHom, objEquiv, Equiv.ulift, Fin.succ]

/-- for `0 ≤ a < b ≤ n`, the `a + 2`-th face of `τ b (a + 1)` is not contained in
  `∂Δ[n] ⊗ Δ[2]`. -/
lemma face_snd_succ_succ_image_not_le_boundary_prod_top (a : Fin b) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (ιSimplex ⟨b, a.succ⟩)
      ≤ ∂Δ[n].prod ⊤ := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary]
  change Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
  intro i
  dsimp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp [Fin.lt_iff_val_lt_val]
  by_cases h : b.1 < i
  · use i.succ
    rw [Fin.eq_mk_iff_val_eq]
    simp [show ¬i.1 < a + 1 by omega, show a.1 < i + 1 by omega, show b.1 < i + 1 by omega]
  · use i.castSucc
    simp
    split
    · simp [show ¬ a.1 + 1 < i by omega]
      omega
    · simp [show a.1 < i by omega]
      omega

lemma face_one_image_not_le_boundary_prod_top (b : Fin n) :
    ¬ (face {1}ᶜ).image (ιSimplex ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ ∂Δ[n].prod ⊤ := by
  simp [face_singleton_compl, filtration₂, filtration₁, unionProd]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary, f]
  change Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
  intro i
  dsimp
  simp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp_rw [Fin.lt_iff_val_lt_val]
  by_cases h : b.succ.1 < i
  · use i.succ
    simp
    intro h'
    exfalso
    exact h'.not_lt (Nat.lt_of_succ_lt h)
  · use i.castSucc
    split
    next h_1 =>
      simp at h_1
      subst h_1
      simp [Fin.ext_iff]
    next h_1 =>
      simp
      intro h'
      exfalso
      exact h h'

/-- for `0 ≤ a < b ≤ n`, the `a + 2`-th face of `τ b (a + 1)` is not contained in
  `σ j i` for any `0 ≤ i ≤ j < n`. -/
lemma face_snd_succ_succ_image_not_le_σ (a : Fin b) (j : Fin n) (i : Fin j.succ) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (ιSimplex ⟨b, a.succ⟩)
      ≤ σ_ ⟨j, i⟩ := by
  dsimp [τ_, σ_]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [ιSimplex, simplex, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ', objMk,
    σ.objMk₂, σ.nonDegenerateEquiv.toFun, τ.nonDegenerateEquiv,
    τ.nonDegenerateEquiv.toFun, τ', τ.objMk₂] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  dsimp at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  by_cases hb : a.1 + 1 = b
  · simp_rw [hb] at h₁ h₂ -- check vertices (0, b) & (2, b)
    simp_all
    cases Fin.eq_last_or_eq_castSucc b
    · next h =>
      subst h
      let h₁' := congr_fun h₁ (Fin.last n).castSucc
      let h₂' := congr_fun h₂ (Fin.last n).castSucc
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.eq_mk_iff_val_eq] at h₁' h₂'
      split at h₁'
      · next h' =>
        rw [Fin.ext_iff] at h₁'
        simp [Fin.le_iff_val_le_val] at h₂'
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        aesop
      · next h' =>
        rw [not_lt] at h'
        rw [Fin.ext_iff] at h₁'
        simp at h₁'
        omega
    · next hb =>
      obtain ⟨b', hb⟩ := hb
      subst hb
      let h₁' := congr_fun h₁ b'.castSucc.castSucc
      let h₂' := congr_fun h₂ b'.castSucc.castSucc
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.eq_mk_iff_val_eq] at h₁' h₂'
      split at h₁'
      · next h =>
        rw [Fin.ext_iff] at h₁'
        simp [Fin.le_iff_val_le_val] at h₂'
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        aesop
      · next h => -- b ≤ i
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        dsimp at h₁'
        rw [not_lt, h₁'] at h
        replace h₁' := congr_fun h₁ b'.succ.castSucc
        replace h₂' := congr_fun h₂ b'.succ.castSucc
        simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
          Fin.eq_mk_iff_val_eq, show b'.1 < b' + 1 + 1 + 1 by omega, show b'.1 < b' + 1 + 1 by omega,
          show ¬b'.1 + 1 + 1 < b' by omega, show ¬b'.1 + 1 + 1 + 1 ≤ b' by omega,
          show ¬b'.1 + 1 + 1≤ b' by omega] at h₁' h₂'
        split at h₁'
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h₂'
          simp [h'.not_le] at h₂'
          rw [Nat.mod_eq_of_lt (by omega)] at h₂'
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          dsimp at h₁'
          omega -- get j < b
        · next h' =>
          rw [not_lt] at h'
          rw [Nat.mod_eq_of_lt (by omega)] at h₂'
          simp [h'] at h₂'
  · have a_lt_b : a.1 + 1 < b := by omega
    cases Fin.eq_last_or_eq_castSucc b
    · next h =>
      subst h
      let h₁' := congr_fun h₁ (Fin.last n).castSucc
      let h₂' := congr_fun h₂ (Fin.last n).castSucc
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
        Fin.eq_mk_iff_val_eq, show ¬n < a + 1 + 1 by omega, show ¬n ≤ a by omega] at h₁' h₂'
      split at h₁'
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        simp [h'.not_le] at h₂'
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        simp at h₁'
        omega
      · next h' =>
        rw [not_lt] at h'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        simp at h₁'
        omega
    . next hb =>
      obtain ⟨b', hb⟩ := hb
      subst hb
      dsimp at a_lt_b
      replace h₁' := congr_fun h₁ b'.succ.castSucc
      replace h₂' := congr_fun h₂ b'.succ.castSucc
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
        Fin.eq_mk_iff_val_eq, show ¬b'.1 < a + 1 by omega, show a.1 < b' + 1 by omega,
        show ¬b'.1 + 1 ≤ a by omega] at h₁' h₂'
      split at h₁'
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        simp [h'.not_le] at h₂'
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        dsimp at h₁'
        have : j.1 < b' := by omega -- get j < b
        let h₁' := congr_fun h₁ b'.castSucc.castSucc
        let h₂' := congr_fun h₂ b'.castSucc.castSucc
        simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
          Fin.eq_mk_iff_val_eq, show ¬b'.1 < a + 1 + 1 by omega, show ¬b'.1 ≤ a by omega] at h₁' h₂'
        split at h₁'
        · next h =>
          rw [Nat.mod_eq_of_lt (by omega)] at h₂'
          simp [h.not_le] at h₂'
          rw [Nat.mod_eq_of_lt (by omega)] at h₂'
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          simp at h₁'
          omega
        · next h => -- b ≤ i
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          dsimp at h₁'
          rw [not_lt, h₁'] at h
          omega
      · next h' =>
        rw [not_lt] at h'
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        simp [h'] at h₂'

lemma face_one_image_not_le_σ (b : Fin n) (j : Fin n) (i : Fin j.succ) :
    ¬ (face {1}ᶜ).image (ιSimplex ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ σ_ ⟨j, i⟩ := by
  dsimp [τ_, σ_]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [ιSimplex, simplex, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ', objMk,
    σ.objMk₂, σ.nonDegenerateEquiv.toFun, τ.nonDegenerateEquiv,
    τ.nonDegenerateEquiv.toFun, τ', τ.objMk₂] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  dsimp at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  cases n with
  | zero =>
    fin_cases j
  | succ n =>
  cases Fin.eq_last_or_eq_castSucc b.succ
  · next hb =>
    rw [hb] at h₁ h₂
    let h₁' := congr_fun h₁ (Fin.last (n + 1)).castSucc
    let h₂' := congr_fun h₂ (Fin.last (n + 1)).castSucc
    simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
    simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
    simp at h₁' h₂'
    split at h₁'
    · next h' =>
      rw [Nat.mod_eq_of_lt (by omega)] at h₂'
      rw [Fin.ext_iff] at h₁'
      simp [h'.not_le] at h₂'
      simp [Fin.last] at h₂' h₁'
      rw [Nat.mod_eq_of_lt (by omega)] at h₂'
      omega
    · next h' =>
      rw [Nat.mod_eq_of_lt (by omega)] at h₂'
      rw [Fin.eq_mk_iff_val_eq] at h₁'
      simp at h₁'
      omega
  · next hb =>
    obtain ⟨b, hb⟩ := hb
    rw [hb] at h₁ h₂
    by_cases hb : b.1 = 0
    · let h₁' := congr_fun h₁ 1
      let h₂' := congr_fun h₂ 1
      simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
      simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
      simp [hb] at h₁' h₂'
      split at h₁'
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        simp [h'.not_le, Fin.succ] at h₂'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        dsimp at h₁'
        simp [show (j.1 + 1) % (n + 1 + 1 + 1) = j + 1 by rw [Nat.mod_eq_of_lt (by omega)],
          show (x 1).1 ≤ j + 1 by omega, show ¬ (2 : Fin (n + 4)) = 0 by exact ne_of_beq_false rfl] at h₂'
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        simp [not_lt.1 h', show ¬ (2 : Fin (n + 4)) = 0 by exact ne_of_beq_false rfl] at h₂'
    · let h₁' := congr_fun h₁ b.succ.castSucc
      let h₂' := congr_fun h₂ b.succ.castSucc
      simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
      simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.ext_iff] at h₁' h₂'
      simp at h₁' h₂'
      split at h₁'
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        simp [h'.not_le, show (j.1 + 1) % (n + 1 + 1 + 1) = j + 1 by rw [Nat.mod_eq_of_lt (by omega)]] at h₂'
        dsimp at h₁'
        split at h₂'
        · omega
        have : j.1 < b := by omega -- get j < b
        let h₁' := congr_fun h₁ b.castSucc.castSucc
        let h₂' := congr_fun h₂ b.castSucc.castSucc
        dsimp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
        simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
        simp [Fin.succ, hb] at h₁' h₂'
        split at h₁'
        · next h =>
          rw [Nat.mod_eq_of_lt (by omega)] at h₂'
          simp [h.not_le, show (j.1 + 1) % (n + 1 + 1 + 1) = j + 1 by rw [Nat.mod_eq_of_lt (by omega)]] at h₂'
          rw [Fin.ext_iff] at h₁'
          simp at h₁'
          omega
        · next h => -- b ≤ i
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          dsimp at h₁'
          rw [not_lt, h₁'] at h
          omega
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h₂'
        simp [show (j.1 + 1) % (n + 1 + 1 + 1) = j + 1 by rw [Nat.mod_eq_of_lt (by omega)]] at h₂'
        simp [not_lt.1 h'] at h₂'

open Sigma.Lex in
lemma face_snd_succ_succ_image_succ_not_le_filtration₂ (i : Σₗ (b : Fin (n + 2)), Fin b.succ) (hn : i < ⊤) :
    ¬ (face {⟨(succ i).snd.succ, by omega⟩}ᶜ).image (ιSimplex (succ i))
      ≤ filtration₂' n i := by
  simp only [Fin.val_succ, face_singleton_compl, Subpresheaf.ofSection_image,
    filtration₂', filtration₁', unionProd, Fin.isValue, Subpresheaf.ofSection_le_iff, Subpresheaf.max_obj,
    prod_obj, Subpresheaf.top_obj, Set.top_eq_univ, Subpresheaf.iSup_obj, iSup_obj, Set.mem_union,
    Set.mem_iUnion, exists_prop, not_or, not_exists, not_and]
  constructor
  · obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
    · exfalso
      rwa [top_eq_last, lt_self_iff_false] at hn
    · rw [Fin.succ_eq₁]
      refine ⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩
      · have := face_snd_succ_succ_image_not_le_top_prod_horn.{u} b a
        simp [face_singleton_compl] at this
        exact this
      · have := face_snd_succ_succ_image_not_le_boundary_prod_top b a
        simp [face_singleton_compl] at this
        exact this
      · intro ⟨j, i⟩ _
        have := face_snd_succ_succ_image_not_le_σ b a j i
        simp [face_singleton_compl] at this
        exact this
    · rw [Fin.succ_eq₂]
      refine ⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩
      · have := face_one_image_not_le_top_prod_horn.{u} b
        simp [face_singleton_compl] at this
        exact this
      · have := face_one_image_not_le_boundary_prod_top b
        simp [face_singleton_compl] at this
        exact this
      · intro ⟨j, i⟩ hij
        have := face_one_image_not_le_σ b j i
        simp [face_singleton_compl] at this
        exact this
  · obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
    · exfalso
      rwa [top_eq_last, lt_self_iff_false] at hn
    · rw [Fin.succ_eq₁]
      intro ⟨j, i⟩ hij
      sorry
    · rw [Fin.succ_eq₂]
      intro ⟨j, i⟩ hij
      sorry

/-- for `0 ≤ b ≤ n`, the `1`-th face of `τ 0 b` is not contained in `Y(b)`. -/
lemma faceImage_one_not_le_filtration₁_top :
  ¬ (face {1}ᶜ).image (ιSimplex ⊥) ≤ filtration₁' (n + 1) ⊤ := by
  simp [face_singleton_compl, filtration₁', unionProd]
  refine ⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩
  · simp [mem_horn_iff]
    change insert 1 (Set.range (objMk₂.{u} _ ∘ Fin.succAbove _)) = Set.univ
    ext i
    fin_cases i
    all_goals simp [Fin.succAbove, objMk₂, Sigma.Lex.bot_eq_zero, SimplexCategory.Hom.toOrderHom,
        SimplexCategory.Hom.mk, objMk, objEquiv, Equiv.ulift]
    · use 0
      aesop
    · use 1
      aesop
  · simp [boundary]
    change Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
    intro i
    dsimp
    simp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove, Sigma.Lex.bot_eq_zero]
    simp_rw [Fin.lt_iff_val_lt_val]
    by_cases h : 0 < i.1
    · use i.succ
      simp
    · use i.castSucc
      aesop
  · intro j i
    rw [ofSimplex_eq_range, Sigma.Lex.bot_eq_zero]
    simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
      Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
    intro x h
    simp [ιSimplex, simplex, nonDegenerateEquiv.toFun] at h
    have h₁ := congr_arg Prod.fst h
    have h₂ := congr_arg Prod.snd h
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ', objMk,
      σ.objMk₂, σ.nonDegenerateEquiv.toFun, τ.nonDegenerateEquiv,
      τ.nonDegenerateEquiv.toFun, τ', τ.objMk₂] at h₁ h₂
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
    dsimp at h₁ h₂
    change _ ∘ x = _ at h₁ h₂
    let h₁' := congr_fun h₁ 1
    let h₂' := congr_fun h₂ 1
    simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
    simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
    have fst : (toLex (⟨j, i⟩ : (a : Fin (n + 1)) × Fin (↑a + 1))).fst = j := rfl
    have snd : (toLex (⟨j, i⟩ : (a : Fin (n + 1)) × Fin (↑a + 1))).snd = i := rfl
    simp_rw [fst, snd] at h₁' h₂'
    split at h₁'
    · next h' =>
      dsimp [Fin.succ] at h₂'
      rw [Nat.mod_eq_of_lt (by omega)] at h₂'
      simp [h'.not_le] at h₂'
      rw [Nat.mod_eq_of_lt (by omega)] at h₂'
      rw [Fin.eq_mk_iff_val_eq] at h₁'
      dsimp at h₁'
      split at h₂'
      · aesop
      · omega
    · next h' =>
      rw [Fin.ext_iff] at h₁'
      dsimp at h₁'
      rw [h₁'] at h₂'
      simp [show ¬ (2 : Fin (n + 4)) = 0 by simp [Fin.ext_iff]] at h₂'

open Sigma.Lex in
lemma innerHornImage_succ_le_inf (i : Σₗ (b : Fin (n + 2)), Fin b.succ) :
    innerHornImage (succ i) ≤
      τ_ (succ i) ⊓ filtration₂' n i := by
  apply le_inf
  · rw [τ_, ofSimplex_eq_range]
    exact image_le_range _ _
  · exact innerHornImage_succ_le_filtration₂.{u} i

open Sigma.Lex in
lemma inf_le_innerHornImage_succ (i : Σₗ (b : Fin (n + 2)), Fin b.succ) (hn : i < ⊤) :
    τ_ (succ i) ⊓ filtration₂' n i ≤
      innerHornImage (succ i) := by
  rw [τ_, ofSimplex_eq_range, subcomplex_le_horn_image_iff _ _ inf_le_left, le_inf_iff, not_and]
  exact fun _ ↦ face_snd_succ_succ_image_succ_not_le_filtration₂.{u} i hn

open Sigma.Lex in
def filtrationPushout_intermediate (n : ℕ) (i : Σₗ (b : Fin (n + 2)), Fin b.succ) (hn : i < ⊤) :
    Sq
      (innerHornImage (succ i))
      (τ_ (succ i))
      (filtration₂' n i)
      (filtration₂' n (succ i))
      where
  max_eq := by rw [τ_, filtration₂_succ', sup_comm]
  min_eq := le_antisymm (inf_le_innerHornImage_succ.{u} i hn) (innerHornImage_succ_le_inf.{u} i)

open Sigma.Lex in
def filtrationPushout_zero (n : ℕ) :
    Sq
      (innerHornImage ⊥)
      (τ_ ⊥)
      (filtration₁' (n + 1) ⊤)
      (filtration₂' n ⊥) where
  max_eq := by rw [τ_, filtration₂_zero', sup_comm]
  min_eq := by
    rw [τ_, ofSimplex_eq_range]
    apply le_antisymm
    · rw [subcomplex_le_horn_image_iff, le_inf_iff, not_and]
      · exact fun _ ↦ faceImage_one_not_le_filtration₁_top.{u}
      · exact inf_le_left
    · exact le_inf (image_le_range _ _) (innerHornImage_bot_le_filtration₁.{u})

end τ
