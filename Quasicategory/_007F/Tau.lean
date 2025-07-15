import Quasicategory._007F.Filtration
import Quasicategory._007F.Order

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ} (a b : Fin (n + 1))

namespace τ

/-- for `0 ≤ a ≤ b ≤ n`, the image of `Λ[n + 2, a + 1]` under `g a b : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
abbrev innerHornImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (horn (n + 2) a.succ.castSucc).image (g a b)

/-- the image of the `i`-th face of `Δ[n + 2]` under some map `Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
abbrev faceImage (i : Fin (n + 3)) (f : Δ[n + 2] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (face {i}ᶜ).image f

lemma innerHornImage_eq_iSup : innerHornImage a b =
    ⨆ (j : ({a.succ.castSucc}ᶜ : Set (Fin (n + 3)))), faceImage j.1 (g a b) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup, faceImage]

lemma innerHornImage_le : innerHornImage a b ≤ τ a b := by
  rw [innerHornImage_eq_iSup]
  exact iSup_le fun _ ↦ image_le_range _ (g a b)

lemma faceImage_le (j : Fin (n + 3)) :
    faceImage j (g a b) ≤ τ a b := image_le_range _ _

/-- for `0 ≤ a ≤ b ≤ n`, each face of `τ a b` except the `a`-th, `(a+1)`-th, `(b+1)`-th, and
  `(b+2)`-th is contained in `∂Δ[n] ⊗ Δ[2]`. -/
lemma faceImage_le_boundary_prod_top (hab : a ≤ b) (j : Fin (n + 3))
    (ha : ¬j = a.castSucc.castSucc) (ha' : ¬j = a.succ.castSucc)
    (hb : ¬j = b.succ.castSucc) (hb' : ¬j = b.succ.succ) :
      faceImage j (g a b) ≤ (boundary n).prod ⊤ := by
  simp [face_singleton_compl]
  refine ⟨?_, Set.mem_univ _⟩
  change ¬Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAbove _)
  intro h
  have : j < a.castSucc.castSucc ∨ a.succ.castSucc < j := by
    cases Fin.lt_or_lt_of_ne ha
    all_goals cases Fin.lt_or_lt_of_ne ha'; try omega
    any_goals omega
    · next q q' =>
      exfalso
      exact not_le.2 q' q
  cases this
  · next hj =>
    obtain ⟨i, hi⟩ := h ⟨j, lt_trans hj (by simp)⟩
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

/-- for `0 ≤ a ≤ b < n` the `(b + 2)`-th face of `τ a b` is `σ a b`. -/
lemma faceImage_b_succ_succ_eq (n : ℕ) (b : Fin n) (a : Fin b.succ) :
    faceImage b.castSucc.succ.succ (g ⟨a, by omega⟩ b.castSucc) = σ ⟨a, by omega⟩ b := by
  simp [face_singleton_compl, σ, f, g, f₂, range, Subpresheaf.range_eq_ofSection', SSet.yonedaEquiv,
    SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex, objEquiv, SimplexCategory.σ,
    SimplexCategory.δ, objMk]
  congr
  apply Prod.ext
  all_goals
    simp [Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · change (Fin.predAbove _ ∘ Fin.predAbove _) ∘ Fin.succAbove _ = Fin.predAbove _
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    have amod : a.1 % (n + 1) = a.1 := Nat.mod_eq_of_lt (by omega)
    split
    · next h' =>
      simp
      split
      · next h'' => simp [show ¬b.1 < e - 1 by omega, amod, h'']
      · next h'' =>
        simp [amod, h'']
        simp [((not_lt.1 h'').trans a.is_le).not_lt]
    · next h' =>
      have := a.is_le
      simp [amod, show a.1 < e + 1 by omega, show b.1 < e by omega, show a.1 < e by omega]
  · change f₂' ⟨a, by omega⟩ b.castSucc ∘ b.succ.succ.castSucc.succAbove = f₂' ⟨a, by omega⟩ b
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · aesop
    · have := a.is_le
      simp [show ¬e.1 + 1 ≤ a by omega, show ¬e.1 ≤ b by omega, show ¬e.1 ≤ a by omega,
        show ¬e.1 ≤ b + 1 by omega]

/-- for `0 ≤ a ≤ n` the `(n + 2)`-th face of `τ a n` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma faceImage_last_le_top_prod_horn :
    faceImage (Fin.last (n + 2)) (g a (Fin.last n)) ≤ (⊤ : Subcomplex Δ[n]).prod (horn 2 1) := by
  simp [face_singleton_compl, SimplexCategory.δ, Fin.succAboveOrderEmb]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (f₂' a (Fin.last n) ∘ Fin.castSucc) ∪ {1} ≠ Set.univ
  rw [ne_eq, Set.eq_univ_iff_forall, not_forall]
  use 2
  simp
  intro e he
  split at he
  · omega
  · simp [Fin.lt_iff_val_lt_val] at he
    omega

/-- for `0 ≤ a ≤ b < n` the `((b + 1) + 1)`-th face of `τ a (b + 1)` is `σ a b`. -/
lemma faceImage_b_succ_eq (n : ℕ) (b : Fin n) (a : Fin b.succ) :
    faceImage b.succ.succ.castSucc (g ⟨a, by omega⟩ b.succ) = σ ⟨a, by omega⟩ b := by
  simp [face_singleton_compl, σ, f, g, f₂, range, Subpresheaf.range_eq_ofSection', SSet.yonedaEquiv,
    SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex, objEquiv, SimplexCategory.σ,
    SimplexCategory.δ, objMk]
  congr
  apply Prod.ext
  all_goals
    simp [Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · simp
    change (Fin.predAbove _ ∘ Fin.predAbove _) ∘ Fin.succAbove _ = Fin.predAbove _
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split
    · next h =>
      simp
      split
      · simp [show ¬b.1 + 1 < e - 1 by omega]
        split
        · aesop
        · next h'' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h''
          omega
      · simp [show ¬b.1 + 1 < e by omega]
        split
        · next h'' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h''
          omega
        · aesop
    · next h =>
      simp [show a.1 < e + 1 by dsimp; omega, show a.1 < e by dsimp; omega]
      split
      · split
        · aesop
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h'
          omega
      · omega
  · change f₂' ⟨a, _⟩ b.succ ∘ Fin.succAbove _ = f₂' ⟨a, by omega⟩ b
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · next h => simp [h.le, show e.1 ≤ b + 1 by omega]
    · simp [show ¬e.1 + 1 ≤ a by dsimp; omega, show ¬e.1 ≤ a by dsimp; omega]

/-- for `0 ≤ b ≤ n`, the `0`-th face of `τ 0 b` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma faceImage_zero_le_top_prod_horn :
    faceImage 0 (g 0 b) ≤ (⊤ : Subcomplex Δ[n]).prod (horn 2 1) := by
  simp [face_singleton_compl]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (f₂' ⟨0, by omega⟩ b ∘ Fin.succ) ∪ {1} ≠ Set.univ
  rw [ne_eq, Set.union_singleton, Set.eq_univ_iff_forall, not_forall]
  use 0
  simp
  intro ⟨e, he⟩
  aesop

/-- for `0 ≤ a < b ≤ n` the `(a + 1)`-th face of `τ (a + 1) b` is the `(a + 1)`-th face of
  `τ a b`. -/
lemma faceImage_succ_eq (hab : a < b) :
    faceImage a.succ.castSucc (g ⟨a.succ, by dsimp; omega⟩ b) =
      faceImage a.succ.castSucc (g a b) := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [g, f₂, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk]
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

/-- for `0 ≤ a < b ≤ n`, the `(a + 1)`-th face of `τ (a + 1) b` is contained in `τ a b`. -/
lemma faceImage_succ_le (hab : a < b) :
    faceImage a.succ.castSucc (g ⟨a.succ, by simp; omega⟩ b) ≤ τ a b := by
  rw [faceImage_succ_eq a b hab]
  exact faceImage_le _ _ _

/-- for `0 ≤ a < b ≤ n`, the image of `Λ[n + 2, (a + 1) + 1]` under `g (a + 1) b` is contained
  in `Y(b, a)`. -/
lemma innerHornImage_a_succ_le_filtration₄ (a : Fin b) :
    innerHornImage ⟨a.succ, by omega⟩ b
      ≤ filtration₄ b ⟨a, by simp; omega⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a.succ, by omega⟩ -- case for the `(a + 1)`-th face
  · subst h
    refine le_sup_of_le_right (le_iSup_of_le ⟨a, Nat.lt_add_one a⟩ ?_)
    exact faceImage_succ_le ⟨a, by omega⟩ b (by simp [Fin.lt_iff_val_lt_val])
  · apply le_sup_of_le_left (le_sup_of_le_left ?_)
    by_cases h' : j = b.succ.castSucc -- case for the `(b + 1)`-th face
    · have := Fin.ne_zero_of_lt (a := ⟨a, by omega⟩) (b := b) a.2
      obtain ⟨b', hb'⟩ := Fin.eq_succ_of_ne_zero (this) -- `b ≠ 0` so `b = b'.succ`
      subst hb' h'
      have : ¬a.1 = b' := by
        intro h
        simp [Fin.eq_mk_iff_val_eq, h] at hj
      have : a.1 < b' := by
        simp_all
        omega
      rw [faceImage_b_succ_eq n b' ⟨a.succ, by simp [this]⟩]
      apply le_sup_of_le_right
      exact le_iSup₂_of_le ⟨b', by simp⟩ ⟨a.succ, by simp [this]⟩ (le_refl _)
    by_cases h'' : j = b.succ.succ -- case for the `(b + 2)`-th face
    · cases Fin.eq_last_or_eq_castSucc b -- check if `b = n` or not
      · next hb =>
        subst hb
        subst h''
        exact le_sup_of_le_left
          (le_sup_of_le_left (faceImage_last_le_top_prod_horn ⟨a.succ, by omega⟩))
      · next hb =>
        obtain ⟨b', hb'⟩ := hb
        subst hb' h''
        rw [faceImage_b_succ_succ_eq n b' a.succ]
        exact le_sup_of_le_right (le_iSup₂_of_le ⟨b', by simp⟩ ⟨a.succ, by simp⟩ (le_refl _))
    -- the case where `j` is not any of the special faces
    exact le_sup_of_le_left (le_sup_of_le_right
      (faceImage_le_boundary_prod_top ⟨a.succ, by omega⟩ _ (by simp [Fin.le_iff_val_le_val]; omega) j h hj h' h''))

/-- for `0 ≤ b ≤ n`, the image of `Λ[n + 2, 1]` under `g 0 b` is contained in `Y(b)`. -/
lemma innerHornImage_zero_le_filtration₃ :
    innerHornImage ⟨0, by omega⟩ b ≤ filtration₃ b.castSucc := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  by_cases h : j = 0 -- case for the `0`-th face
  · subst h
    apply le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left _))
    exact faceImage_zero_le_top_prod_horn b
  · apply le_sup_of_le_left
    by_cases h' : j = b.succ.castSucc -- case for the `(b + 1)`-th face
    · cases Fin.eq_zero_or_eq_succ b
      · aesop
      · next h'' =>
        obtain ⟨b', hb'⟩ := h'' -- `b ≠ 0` so `b = b'.succ`
        subst hb' h'
        rw [faceImage_b_succ_eq n b' ⟨0, Nat.zero_lt_succ _⟩]
        exact le_sup_of_le_right (le_iSup₂_of_le ⟨b', by simp⟩ ⟨0, _⟩ (le_refl _))
    by_cases h'' : j = b.succ.succ -- case for the `(b + 2)`-th face
    · cases Fin.eq_last_or_eq_castSucc b -- check if `b = n` or not
      · next hb =>
        subst hb
        subst h''
        apply (le_sup_of_le_left (le_sup_of_le_left (faceImage_last_le_top_prod_horn 0)))
      · next hb =>
        obtain ⟨b', hb'⟩ := hb
        subst hb' h''
        rw [faceImage_b_succ_succ_eq n b' ⟨0, _⟩]
        exact le_sup_of_le_right (le_iSup₂_of_le ⟨b', by simp⟩ ⟨0, by simp⟩ (le_refl _))
    -- the case where `j` is not any of the special faces
    exact le_sup_of_le_left (le_sup_of_le_right
      (faceImage_le_boundary_prod_top 0 _ (Fin.zero_le _) j h hj h' h''))

/-- for `0 ≤ a < b ≤ n`, the `((a + 1) + 1)`-th face of `τ (a + 1) b` is not contained in
  `Δ[n] ⊗ Λ[2, 1]`. -/
lemma faceImage_succ_not_le_unionProd₁ (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (g ⟨a.succ, by omega⟩ b)
      ≤ Subcomplex.prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  rw [mem_horn_iff]
  simp
  change insert 1 (Set.range (f₂' _ b ∘ Fin.succAbove _)) = Set.univ
  ext i
  fin_cases i
  all_goals simp [Fin.succAbove]
  · use a.succ
    simp [Fin.lt_iff_val_lt_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp [Fin.lt_iff_val_lt_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp
  · use b.succ
    simp [Fin.lt_iff_val_lt_val, show ¬b.1 < a.1 + 1 by omega]
    omega

/-- for `0 ≤ a < b ≤ n`, the `((a + 1) + 1)`-th face of `τ (a + 1) b` is not contained in
  `∂Δ[n] ⊗ Δ[2]`. -/
lemma faceImage_succ_not_le_unionProd₂ (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (g ⟨a.succ, by omega⟩ b)
      ≤ ∂Δ[n].prod ⊤ := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary, f]
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

/-- for `0 ≤ a < b ≤ n`, the `((a + 1) + 1)`-th face of `τ (a + 1) b` is not contained in
  `τ i j` for any `0 ≤ i ≤ j < b`. -/
lemma faceImage_succ_not_le_τij (a j : Fin b) (i : Fin j.succ) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (g ⟨a.succ, by omega⟩ b)
      ≤ τ ⟨i, by omega⟩ ⟨j, by omega⟩ := by
  simp [τ, face_singleton_compl]
  intro x h
  simp [g] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [f, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, f₂, objMk] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  simp  at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  cases lt_or_eq_of_le (show a.1 + 1 ≤ b.1 from a.2)
  all_goals
    replace h₁ := congr_fun h₁ b.castSucc
    replace h₂ := congr_fun h₂ b.castSucc
    simp [Fin.predAbove, Fin.succAbove, f₂', Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
  · next h =>
    simp [show ¬b.1 < a.1 + 1 + 1 by omega, show ¬b.1 ≤ a.1 by omega] at h₁ h₂
    split at h₂
    · next h' => omega
    · next h' =>
      split at h₂
      · next h'' =>
        rw [Fin.eq_mk_iff_val_eq] at h₁
        split at h₁
        · split at h₁
          all_goals
            simp at h₁
            omega
        · omega
      · next h'' => omega
  · next h =>
    simp_rw [← h] at h₁ h₂
    simp [show a.1 + 1 < a.1 + 1 + 1 by omega, h.symm.le, h.symm.not_gt] at h₁ h₂
    split at h₁
    · next h' =>
      have := h₂ h'
      split at this
      all_goals omega
    · rw [Fin.eq_mk_iff_val_eq] at h₁
      split at h₁
      all_goals
        simp at h₁
        omega

/-- for `0 ≤ a < b ≤ n`, the `((a + 1) + 1)`-th face of `τ (a + 1) b` is not contained in
  `τ i b` for any `0 ≤ i ≤ a`. -/
lemma faceImage_succ_not_le_τib (a : Fin b) (i : Fin a.succ) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (g ⟨a.succ, by omega⟩ b)
      ≤ τ ⟨i, by omega⟩ b := by
  simp [τ, face_singleton_compl]
  intro x h
  simp [g] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [f, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, f₂, objMk] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  dsimp at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  replace h₁ := congr_fun h₁ ⟨a.succ, by omega⟩
  replace h₂ := congr_fun h₂ ⟨a.succ, by omega⟩
  simp [Fin.succAbove, Fin.predAbove, f₂', Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
  split at h₁
  · next h =>
    aesop
  · next h =>
    rw [Fin.eq_mk_iff_val_eq] at h₁
    simp [show ¬b.1 < a.1 + 1 by omega] at h₁
    split at h₁
    · omega
    · aesop
/-
τab = ⟨(0, 0),...,(0, a), (1, a),..., (1, b), (2, b),..., (2, n)⟩.

For 0 ≤ a < b ≤ n,
(a+2)-th face of τ(a+1)b is
  ⟨(0, 0),...,(0, a+1), (1, a+2),..., (1, b), (2, b),..., (2, n)⟩.

If b = n
  ⟨(0, 0),...,(0, a+1), (1, a+2),..., (1, n), (2, n)⟩.

If a+1 = b,
  ⟨(0, 0),...,(0, b), (2, b),..., (2, n)⟩.
  vertex (0, b), (2, b) prevent this from being in any σij:

σij = ⟨(0, 0),..., (0, i), (1, i),..., (1, j), (2, j + 1),..., (2, n)⟩.

For a+1 = b:
  (0, b) in σij means b ≤ i, and (2, b) in σij means j < b, but i ≤ j.

Else if a+1 < b, vertex (1, b), (2, b) prevent this from being in any σij
  (1, b) in σij means b ≤ j, and (2, b) in σij means j < b

-/

/-- for `0 ≤ a < b ≤ n`, the `((a + 1) + 1)`-th face of `τ (a + 1) b` is not contained in
  `σ i j` for any `0 ≤ i ≤ j < n`. -/
lemma faceImage_succ_not_le_σij (a : Fin b) (j : Fin n) (i : Fin j.succ) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (g ⟨a.succ, by omega⟩ b)
      ≤ σ ⟨i, by omega⟩ j := by
  simp [τ, σ, face_singleton_compl]
  intro x h
  simp [g] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [f, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, f₂, objMk] at h₁ h₂
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
        rw [Nat.mod_eq_of_lt (by omega)] at h'
        aesop
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega), not_lt] at h'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
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
        rw [Nat.mod_eq_of_lt (by omega)] at h
        aesop
      · next h => -- b ≤ i
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        dsimp at h₁'
        rw [Nat.mod_eq_of_lt (by omega), not_lt, h₁'] at h
        replace h₁' := congr_fun h₁ b'.succ.castSucc
        replace h₂' := congr_fun h₂ b'.succ.castSucc
        simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
          Fin.eq_mk_iff_val_eq, show b'.1 < b' + 1 + 1 + 1 by omega, show b'.1 < b' + 1 + 1 by omega,
          show ¬b'.1 + 1 + 1 < b' by omega, show ¬b'.1 + 1 + 1 + 1 ≤ b' by omega,
          show ¬b'.1 + 1 + 1≤ b' by omega] at h₁' h₂'
        split at h₁'
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h'
          simp [h'.not_le] at h₂'
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          dsimp at h₁'
          omega -- get j < b
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega), not_lt] at h'
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
        rw [Nat.mod_eq_of_lt (by omega)] at h'
        simp [h'.not_le] at h₂'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        simp at h₁'
        omega
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega), not_lt] at h'
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
        rw [Nat.mod_eq_of_lt (by omega)] at h'
        simp [h'.not_le] at h₂'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        dsimp at h₁'
        have : j.1 < b' := by omega -- get j < b
        let h₁' := congr_fun h₁ b'.castSucc.castSucc
        let h₂' := congr_fun h₂ b'.castSucc.castSucc
        simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
          Fin.eq_mk_iff_val_eq, show ¬b'.1 < a + 1 + 1 by omega, show ¬b'.1 ≤ a by omega] at h₁' h₂'
        split at h₁'
        · next h =>
          rw [Nat.mod_eq_of_lt (by omega)] at h
          simp [h.not_le] at h₂'
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          simp at h₁'
          omega
        · next h => -- b ≤ i
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          dsimp at h₁'
          rw [Nat.mod_eq_of_lt (by omega), not_lt, h₁'] at h
          omega
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega), not_lt] at h'
        simp [h'] at h₂'

/-- for `0 ≤ a < b < n`, the `((a + 1) + 1)`-th face of `τ (a + 1) b` is not contained in
  `Y(b, a)`. -/
lemma faceImage_succ_not_le_filtration₄ (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (g ⟨a.succ, by omega⟩ b)
      ≤ filtration₄ b a.castSucc := by
  simp [face_singleton_compl, filtration₄, filtration₁, filtration₃, unionProd]
  refine ⟨⟨⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, fun j i ↦ ?_⟩, fun j i ↦ ?_⟩, fun i ↦ ?_⟩
  · -- not in `Δ[n] ⨯ Λ[2, 1]`
    simpa [face_singleton_compl, Set.prod] using faceImage_succ_not_le_unionProd₁ b a
  · -- not in `∂Δ[n] ⨯ Δ[2]`
    simpa [face_singleton_compl, Set.prod] using faceImage_succ_not_le_unionProd₂ b a
  · -- not in any `σ i j` for any `0 ≤ a ≤ b < n`
    simpa [face_singleton_compl] using faceImage_succ_not_le_σij b a j i
  · -- not in any `τ i j` for any `0 ≤ i ≤ j < b`
    simpa [face_singleton_compl] using faceImage_succ_not_le_τij b a j i
  · -- not in `τ i b` for any `0 ≤ i < a + 1`
    simpa [face_singleton_compl] using faceImage_succ_not_le_τib b a i

/-
τ0b = ⟨(0, 0), (1, 0),..., (1, b), (2, b),..., (2, n)⟩.

1st face of τ0b is
  ⟨(0, 0), (1, 1),..., (1, b), (2, b),..., (2, n)⟩.

If b = n
  ⟨(0, 0), (1, 1),..., (1, n), (2, n)⟩.

If b = 0,
  ⟨(0, 0), (2, 0),..., (2, n)⟩.

σij = ⟨(0, 0),..., (0, i), (1, i),..., (1, j), (2, j + 1),..., (2, n)⟩.

If b = 0, (2, 0) cant be in σij

If b ≠ 0, (1, b) says b ≤ j, (2, b) says j < b

-/

-- really bad
/-- for `0 ≤ b ≤ n`, the `1`-th face of `τ 0 b` is not contained in `Y(b)`. -/
lemma faceImage_one_not_le_filtration₃ :
  ¬ faceImage 1 (g 0 b) ≤ filtration₃ b.castSucc := by
  simp [face_singleton_compl, filtration₃, filtration₁, unionProd]
  refine ⟨⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩, ?_⟩
  · simp [mem_horn_iff]
    change insert 1 (Set.range (f₂' _ b ∘ (Fin.succ 0).succAbove)) = Set.univ
    ext i
    fin_cases i
    all_goals simp [Fin.succAbove]
    · exact ⟨0, by simp⟩
    · exact ⟨b.succ, by simp [Fin.lt_iff_val_lt_val, Fin.succ_ne_zero]⟩
  · simp [boundary, f, g]
    change Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove 0 ∘ (Fin.succ 0).succAboveOrderEmb)
    intro i
    dsimp
    simp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
    simp_rw [Fin.lt_iff_val_lt_val]
    by_cases h : b.1 < i
    · use i.succ
      simp
      omega
    · use i.castSucc
      split
      next h_1 =>
        simp at h_1
        simp [show ¬0 < i by omega]
        omega
      next h_1 =>
        simp only [Fin.succ_pos, ↓reduceDIte, Fin.pred_succ, Fin.coe_castSucc, Fin.val_fin_lt,
          Fin.castPred_castSucc, dite_eq_right_iff]
        omega
  · intro j i
    by_cases hn : n = 0
    · subst hn
      fin_cases j
    simp [σ, face_singleton_compl]
    intro x h
    have h₁ := congr_arg Prod.fst h
    have h₂ := congr_arg Prod.snd h
    simp [g, f, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, f₂, objMk] at h₁ h₂
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
    dsimp at h₁ h₂
    change _ ∘ x = _ at h₁ h₂
    cases Fin.eq_last_or_eq_castSucc b
    · next hb =>
      subst hb
      let h₁' := congr_fun h₁ (Fin.last n).castSucc
      let h₂' := congr_fun h₂ (Fin.last n).castSucc
      simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
      simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
      simp [hn] at h₁' h₂'
      split at h₁'
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega)] at h'
        simp [h'.not_le] at h₂'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        simp [Fin.last] at h₂' h₁'
        omega
      · next h' =>
        rw [Nat.mod_eq_of_lt (by omega), not_lt] at h'
        rw [Fin.eq_mk_iff_val_eq] at h₁'
        simp at h₁'
        omega
    · next hb =>
      obtain ⟨b, hb⟩ := hb
      subst hb
      by_cases hb : b.1 = 0
      · obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn
        subst hn'
        let h₁' := congr_fun h₁ 1
        let h₂' := congr_fun h₂ 1
        simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
        simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
        simp [hb] at h₁' h₂'
        split at h₁'
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h'
          simp [h'.not_le, Fin.succ] at h₂'
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          dsimp at h₁'
          simp [show (x 1).1 ≤ j + 1 by omega] at h₂'
          split at h₂'
          all_goals omega
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega), not_lt] at h'
          simp [h'] at h₂'
          split at h₂'
          · next h'' =>
            rw [Fin.eq_mk_iff_val_eq] at h''
            simp_all only [Nat.succ_eq_add_one, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
              not_false_eq_true, Fin.val_two, Fin.val_zero, OfNat.ofNat_ne_zero]
          · omega
      · let h₁' := congr_fun h₁ b.succ.castSucc
        let h₂' := congr_fun h₂ b.succ.castSucc
        simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
          Fin.eq_mk_iff_val_eq] at h₁' h₂'
        split at h₁'
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega)] at h'
          simp [h'.not_le] at h₂'
          rw [Fin.eq_mk_iff_val_eq] at h₁'
          dsimp at h₁'
          have : j.1 < b := by omega -- get j < b
          let h₁' := congr_fun h₁ b.castSucc.castSucc
          let h₂' := congr_fun h₂ b.castSucc.castSucc
          dsimp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
          simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
          simp [Fin.succ, hb] at h₁' h₂'
          split at h₁'
          · next h =>
            rw [Nat.mod_eq_of_lt (by omega)] at h
            simp [h.not_le] at h₂'
            rw [Fin.eq_mk_iff_val_eq] at h₁'
            simp at h₁'
            omega
          · next h => -- b ≤ i
            rw [Fin.eq_mk_iff_val_eq] at h₁'
            dsimp at h₁'
            rw [Nat.mod_eq_of_lt (by omega), not_lt, h₁'] at h
            omega
        · next h' =>
          rw [Nat.mod_eq_of_lt (by omega), not_lt] at h'
          simp [h'] at h₂'
  · intro j i
    simp [τ]
    intro x h
    have h₁ := congr_arg Prod.fst h
    have h₂ := congr_arg Prod.snd h
    simp [g, f, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, f₂, objMk] at h₁ h₂
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
    dsimp at h₁ h₂
    change _ ∘ x = _ at h₁ h₂
    replace h₁ := congr_fun h₁ b
    replace h₂ := congr_fun h₂ b
    simp [Fin.predAbove, Fin.succAbove] at h₁ h₂
    simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
    by_cases h : b.1 = 0
    · simp [h, show b.castSucc = 0 from Fin.eq_of_val_eq h] at h₁ h₂
      split at h₂
      all_goals omega
    · simp [h, Fin.succ_ne_zero] at h₁ h₂
      split at h₂
      · next => omega
      · next h' =>
        rw [not_le] at h'
        simp [h'] at h₁
        split at h₂
        · rw [Fin.eq_mk_iff_val_eq] at h₁
          split at h₁
          omega
          aesop
        · omega

/-- a subcomplex `A` of `Δ[n] ⊗ Δ[2]` which is contained in `τ a b` is contained in the image of
  `Λ[n + 2, a + 1]` under `g a b` iff the `(a + 1)`-th face of `τ a b` is not contained in `A`. -/
lemma subcomplex_le_innerHornImage_iff {a b : Fin (n + 1)} (ha : a ≤ b)
    (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ τ a b) :
    A ≤ τ.innerHornImage a b ↔ ¬ τ.faceImage a.succ.castSucc (g a b) ≤ A :=
  letI := g_mono ha
  subcomplex_le_horn_image_iff (g a b) A hA a.succ.castSucc

/-
for `0 ≤ a < b ≤ n`, (so for `n ≥ 1`) the following square

`Λ[n+2,(a+1)+1]` -------> `Y(b) ∪ τ0b ∪ ... ∪ τab`
        |                             |
        |                             |
        v                             V
    `τ(a+1)b` ------> `Y(b) ∪ τ0b ∪ ... ∪ τab ∪ τ(a+1)b`

so this says `Y(b,a) ↪ Y(b,a+1)` is inner anodyne

need `b ≤ n` because `Y(n + 1)` is the last term. `Y(n, n) = X(n + 1)`.
need `a < b` because we need `a + 1 ≤ b`
-/
def filtrationPushout_intermediate (a : Fin b) :
    Sq
      (τ.innerHornImage ⟨a.succ, by omega⟩ b)
      (τ ⟨a.succ, by omega⟩ b)
      (filtration₄ b a.castSucc)
      (filtration₄ b a.succ)
      where
  max_eq := by rw [filtration₄_succ b a, sup_comm]
  min_eq := by
    apply le_antisymm
    · rw [subcomplex_le_innerHornImage_iff (by simp [Fin.le_iff_val_le_val]; omega) _ inf_le_left,
        le_inf_iff, not_and]
      exact fun _ ↦ τ.faceImage_succ_not_le_filtration₄ b a
    · exact le_inf (τ.innerHornImage_le _ _) (τ.innerHornImage_a_succ_le_filtration₄ _ _)

open Sigma.Lex in
def filtrationPushout_intermediate' (i : Σₗ (b : Fin (n + 2)), Fin b.succ) (h0 : ⊥ < i) (hn : i < ⊤) :
    Sq
      (τ.innerHornImage (⟨(succ i).2, by omega⟩ : Fin (n + 2)) ⟨(succ i).1, by simp⟩)
      (ofSimplex (τ.simplex (succ i)).1)
      (filtration₂' n i)
      (filtration₂' n (succ i))
      where
  max_eq := by rw [filtration₂_succ', sup_comm]
  min_eq := by
    clear a b
    apply le_antisymm
    · rw [eq_τ]
      rcases i with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      induction b with
      | zero =>
        dsimp
        simp at ha
        subst ha
        rw [Sigma.Lex.Fin.succ_bot_eq]
        dsimp
        change _ ≤ innerHornImage 0 1
        rw [subcomplex_le_innerHornImage_iff (Fin.zero_le 1) _ inf_le_left, le_inf_iff, not_and]
        intro
        change ¬(face {1}ᶜ).image (g 0 1) ≤ filtration₂' n ⊥
        rw [filtration₂_zero', Sigma.Lex.bot_eq_zero, eq_τ, Sigma.Lex.top_eq_last, filtration₁'_eq']
        have := filtration₂_last (Fin.last n)
        change filtration₂ (Fin.last n) (Fin.last n) = _ at this
        rw [this]
        simp
        convert τ.faceImage_one_not_le_filtration₃ (n := n + 1) 1
        simp [filtration₃]
      | succ b _ =>
        induction a with
        | zero =>
          have h := (Sigma.Lex.Fin.succ_eq_of_snd_lt_fst ⟨b + 1, hb⟩ ⟨0, ha⟩ (by simp))
          have h' : (succ ⟨⟨b + 1, hb⟩, ⟨0, ha⟩⟩).snd.1 = (⟨⟨b + 1, hb⟩, ⟨1, by simp⟩⟩ :  Σₗ (b : Fin (n + 1 + 1)), Fin ↑b.succ).snd := by
            dsimp only [Fin.val_succ, Fin.succ_mk, Fin.zero_eta, Fin.val_zero,
              lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true,
              Fin.succ_zero_eq_one, Fin.val_one, Fin.mk_one, dite_eq_ite, Nat.add_zero,
              eq_mpr_eq_cast] at h ⊢
            rw [h]
            simp
          simp_rw [h, h']
          rw [subcomplex_le_innerHornImage_iff (by simp [Fin.le_iff_val_le_val]) _ inf_le_left, le_inf_iff, not_and]
          intro
          dsimp
          have := faceImage_succ_not_le_filtration₄ ⟨b + 1, hb⟩ 0
          dsimp at this
          convert this
          exact filtration₂_eq' _ _
        | succ a _ =>
          have hab : a ≤ b := by
            simp at ha
            omega
          cases (lt_or_eq_of_le hab)
          · next hab =>
            have h := (Sigma.Lex.Fin.succ_eq_of_snd_lt_fst ⟨b + 1, hb⟩ ⟨a + 1, ha⟩ (by simpa))
            have h' : (succ ⟨⟨b + 1, hb⟩, ⟨a + 1, ha⟩⟩).snd.1 = (⟨⟨b + 1, hb⟩, ⟨a + 2, by simpa⟩⟩ :  Σₗ (b : Fin (n + 1 + 1)), Fin ↑b.succ).snd := by
              dsimp only [Fin.val_succ, Fin.succ_mk, Fin.zero_eta, Fin.val_zero,
                lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true,
                Fin.succ_zero_eq_one, Fin.val_one, Fin.mk_one, dite_eq_ite, Nat.add_zero,
                eq_mpr_eq_cast] at h ⊢
              rw [h]
            simp_rw [h, h']
            rw [subcomplex_le_innerHornImage_iff (by simpa [Fin.le_iff_val_le_val]) _ inf_le_left, le_inf_iff, not_and]
            intro
            dsimp
            have := faceImage_succ_not_le_filtration₄ ⟨b + 1, hb⟩ ⟨a + 1, by simpa⟩
            dsimp at this
            convert this
            exact filtration₂_eq' _ _
          · next hab =>
            subst hab
            have goal : a + 2 < n + 1 + 1 := by
              rw [Sigma.Lex.lt_def] at hn
              cases hn
              · next hn =>
                simp [Fin.lt_iff_val_lt_val, Sigma.Lex.top_eq_last] at hn
                omega
              · next hn =>
                obtain ⟨hn, hn'⟩ := hn
                simp [Fin.ext_iff, Fin.lt_iff_val_lt_val, Sigma.Lex.top_eq_last] at hn
                subst hn
                simp [Fin.ext_iff, Fin.lt_iff_val_lt_val, Sigma.Lex.top_eq_last] at hn'
            have h := Sigma.Lex.Fin.succ_eq_of_lt_last ⟨a + 1, hb⟩ (by simpa [Fin.lt_iff_val_lt_val] using goal)
            have h' : (succ ⟨⟨a + 1, hb⟩, ⟨a + 1, ha⟩⟩).snd.1 = (⟨⟨a + 2, goal⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ :  Σₗ (b : Fin (n + 1 + 1)), Fin b.succ).snd := by
              dsimp only [Fin.val_succ, Fin.succ_mk, lt_self_iff_false, Fin.zero_eta,
                Fin.val_zero] at h ⊢
              rw [h]
              rfl
            simp_rw [h, h']
            rw [subcomplex_le_innerHornImage_iff (by simp [Fin.le_iff_val_le_val]) _ inf_le_left, le_inf_iff, not_and]
            intro
            dsimp
            rw [filtration₂_eq', filtration₄_last]
            exact faceImage_one_not_le_filtration₃ (n := n + 1) ⟨a + 1 + 1, goal⟩
    · rw [eq_τ]
      apply le_inf (innerHornImage_le _ _)
      · rcases i with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
        induction b with
        | zero =>
          dsimp only [Fin.val_succ, Fin.zero_eta, Fin.succ_zero_eq_one, Fin.val_one,
            succ.eq_1, Fin.val_zero, not_lt_zero', ↓dreduceDIte, Fin.zero_eq_last_iff,
            AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, Fin.val_last, Fin.mk_one,
            Fin.succ_one_eq_two, Fin.val_two, Fin.isValue, Fin.castSucc_one, succ, ↓reduceDIte]
          simp at ha
          subst ha
          convert innerHornImage_zero_le_filtration₃ (n := n + 1) 1
          rw [filtration₂_eq']
          exact filtration₄_last 0
        | succ b _ =>
          induction a with
          | zero =>
            have h := (Sigma.Lex.Fin.succ_eq_of_snd_lt_fst ⟨b + 1, hb⟩ ⟨0, ha⟩ (by simp))
            have h' : (succ ⟨⟨b + 1, hb⟩, ⟨0, ha⟩⟩).snd.1 = (⟨⟨b + 1, hb⟩, ⟨1, by simp⟩⟩ :  Σₗ (b : Fin (n + 1 + 1)), Fin ↑b.succ).snd := by
              dsimp only [Fin.val_succ, Fin.succ_mk, Fin.zero_eta, Fin.val_zero,
                lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true,
                Fin.succ_zero_eq_one, Fin.val_one, Fin.mk_one, dite_eq_ite, Nat.add_zero,
                eq_mpr_eq_cast] at h ⊢
              rw [h]
              simp
            simp_rw [h, h']
            rw [filtration₂_eq']
            dsimp only [Fin.val_succ, Fin.succ_mk, Fin.zero_eta, succ.eq_1, Fin.val_zero,
              lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true,
              Fin.succ_zero_eq_one, Fin.val_one, Fin.mk_one, dite_eq_ite, Int.reduceNeg, id_eq,
              Nat.cast_ofNat, Int.Nat.cast_ofNat_Int, Nat.reduceAdd, Nat.add_zero, eq_mpr_eq_cast, Fin.succ_one_eq_two]
            exact innerHornImage_a_succ_le_filtration₄ ⟨b + 1, hb⟩ ⟨0, Nat.zero_lt_succ _⟩
          | succ a _ =>
            have hab : a ≤ b := by
              simp at ha
              omega
            cases (lt_or_eq_of_le hab)
            · next hab =>
              have h := (Sigma.Lex.Fin.succ_eq_of_snd_lt_fst ⟨b + 1, hb⟩ ⟨a + 1, ha⟩ (by simpa))
              have h' : (succ ⟨⟨b + 1, hb⟩, ⟨a + 1, ha⟩⟩).snd.1 = (⟨⟨b + 1, hb⟩, ⟨a + 2, by simpa⟩⟩ :  Σₗ (b : Fin (n + 1 + 1)), Fin ↑b.succ).snd := by
                dsimp only [Fin.val_succ, Fin.succ_mk, Fin.zero_eta, Fin.val_zero,
                  lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true,
                  Fin.succ_zero_eq_one, Fin.val_one, Fin.mk_one, dite_eq_ite, Nat.add_zero,
                  eq_mpr_eq_cast] at h ⊢
                rw [h]
              simp_rw [h, h']
              rw [filtration₂_eq']
              convert innerHornImage_a_succ_le_filtration₄ ⟨b + 1, hb⟩ ⟨a + 1, by simp; omega⟩
            · next hab =>
              subst hab
              have goal : a + 2 < n + 1 + 1 := by
                rw [Sigma.Lex.lt_def] at hn
                cases hn
                · next hn =>
                  simp [Fin.lt_iff_val_lt_val, Sigma.Lex.top_eq_last] at hn
                  omega
                · next hn =>
                  obtain ⟨hn, hn'⟩ := hn
                  simp [Fin.ext_iff, Fin.lt_iff_val_lt_val, Sigma.Lex.top_eq_last] at hn
                  subst hn
                  simp [Fin.ext_iff, Fin.lt_iff_val_lt_val, Sigma.Lex.top_eq_last] at hn'
              have h := Sigma.Lex.Fin.succ_eq_of_lt_last ⟨a + 1, hb⟩ (by simpa [Fin.lt_iff_val_lt_val] using goal)
              have h' : (succ ⟨⟨a + 1, hb⟩, ⟨a + 1, ha⟩⟩).snd.1 = (⟨⟨a + 2, goal⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ :  Σₗ (b : Fin (n + 1 + 1)), Fin b.succ).snd := by
                dsimp only [Fin.val_succ, Fin.succ_mk, lt_self_iff_false, Fin.zero_eta,
                  Fin.val_zero] at h ⊢
                rw [h]
                rfl
              simp_rw [h, h']
              rw [filtration₂_eq', filtration₄_last]
              simp
              exact innerHornImage_zero_le_filtration₃ ⟨a + 2, goal⟩

/--
`0 ≤ b ≤ (n + 1)`
`Y(b) ↪ Y(b, 0)`
`filtration₃ b ↪ filtration₄ b 0`

so this says `Y(b-1,b-1) = Y(b) ↪ Y(b,0)` is inner anodyne

-/
def filtrationPushout_join :
    Sq
      (τ.innerHornImage 0 b)
      (τ 0 b)
      (filtration₃ b.castSucc)
      (filtration₄ b ⟨0, Nat.zero_lt_succ _⟩)
      where
  max_eq := by
    cases b using Fin.cases with
    | zero => simp [filtration₃, filtration₄, sup_comm]
    | succ b' => rw [filtration₄_zero, Fin.coe_eq_castSucc, ← Fin.succ_castSucc, filtration₃_succ, sup_comm]
  min_eq := by
    apply le_antisymm
    · rw [subcomplex_le_innerHornImage_iff (Fin.zero_le b) _ inf_le_left, le_inf_iff, not_and]
      exact fun _ ↦ τ.faceImage_one_not_le_filtration₃ b
    · apply le_inf (τ.innerHornImage_le 0 _) (τ.innerHornImage_zero_le_filtration₃ b)

/--
`Λ[n+3,n+2]` ----> `Y(n+1) ∪ τ0(n+1) ∪ ... ∪ τn(n+1)`
      |                            |
      |                            |
      v                            V
`τ(n+1)(n+1)` ------------> `Δ[2] ⊗ Δ[2]`

`Y(n + 1, n) ↪ Y(n + 1, n + 1) = ⊤` is inner anodyne
-/
def filtrationPushout_last (n : ℕ) :
    Sq
      (τ.innerHornImage (Fin.last (n + 1)) (Fin.last (n + 1)))
      (τ (Fin.last (n + 1)) (Fin.last (n + 1)))
      (filtration₄ (Fin.last (n + 1)) (Fin.last n).castSucc)
      ⊤ := by
  rw [← filtration₄_last']
  exact filtrationPushout_intermediate (Fin.last (n + 1)) (Fin.last n)

/-
`Λ[n+2,1]` ---> `X(n) = Y(0)`
    |                |
    |                |
    v                V
  `τ00` ---------> `Y(1)`

`Y(0) ↪ Y(1)`
-/
def filtrationPushout_zero (n : ℕ) :
    Sq
      (τ.innerHornImage 0 0)
      (τ 0 0)
      (filtration₁ n)
      (filtration₃ (1 : Fin (n + 2))) := by
  have h := filtration₃_succ (0 : Fin (n + 1))
  have h' := filtration₄_zero (0 : Fin (n + 1))
  dsimp at h h'
  rw [h]
  change _ = filtration₃ 0 ⊔ τ 0 0 at h'
  simp [Fin.last]
  rw [← h', ← filtration₃_zero]
  exact filtrationPushout_join 0

end τ
