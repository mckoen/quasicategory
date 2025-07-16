import Quasicategory._007F.Filtration
import Quasicategory._007F.Order

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ}

namespace σ

section

variable (a b : Fin n)

/-- for `0 ≤ a ≤ b < n`, the image of `Λ[n + 1, a + 1]` under `f a b : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
abbrev innerHornImage : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (horn (n + 1) a.succ.castSucc).image (f a b)

/-- the image of the `i`-th face of `Δ[n + 1]` under some map `Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]`. -/
@[simp]
noncomputable
abbrev faceImage (i : Fin (n + 2)) (h : Δ[n + 1] ⟶ Δ[n] ⊗ Δ[2]) : (Δ[n] ⊗ Δ[2]).Subcomplex :=
  (face {i}ᶜ).image h

lemma innerHornImage_eq_iSup : innerHornImage a b =
    ⨆ (j : ({a.succ.castSucc}ᶜ : Set (Fin (n + 2)))), faceImage j.1 (f a b) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup, faceImage]

/-- the image of `Λ[n + 1, a + 1]` under `fab` is contained in `σ a b`. -/
lemma innerHornImage_le : innerHornImage a b ≤ σ a b := by
  rw [innerHornImage_eq_iSup]
  exact iSup_le fun _ ↦ image_le_range _ (f a b)

/-- the image of every face of `Δ[n + 1]` under `f a b` is contained in `σ a b`. -/
lemma faceImage_le (j : Fin (n + 2)) :
    faceImage j (f a b) ≤ σ a b := image_le_range _ (f a b)

/-- each face of `σ a b` except the `a`-th and `(a + 1)`-th is contained in `∂Δ[n] ⊗ Δ[2]`. -/
lemma faceImage_le_boundary_prod_top (j : Fin (n + 2))
    (hj : ¬j = a.succ.castSucc) (hj' : ¬j = a.castSucc.castSucc) :
    faceImage j (f a b) ≤ ∂Δ[n].prod ⊤ := by
  simp [face_singleton_compl]
  refine ⟨?_, Set.mem_univ _⟩
  change ¬Function.Surjective (Fin.predAbove _ ∘ j.succAbove)
  intro h
  have : j < a.castSucc.castSucc ∨ a.succ.castSucc < j := by
    cases Fin.lt_or_lt_of_ne hj
    all_goals cases Fin.lt_or_lt_of_ne hj'; try omega
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

/-- the `0`-th face of `σ 0 b` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma faceImage_zero_le_top_prod_horn (n : ℕ) (b : Fin (n + 1)) :
    faceImage 0 (f 0 b) ≤ (⊤ : Subcomplex Δ[n + 1]).prod (horn 2 1) := by
  simp [face_singleton_compl]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (f₂' ⟨0, by omega⟩ b ∘ Fin.succ) ∪ {1} ≠ Set.univ
  intro h'
  rw [Set.eq_univ_iff_forall] at h'
  have h'' := h' 0
  simp at h''
  obtain ⟨e, he⟩ := h''
  have := he e.succ_ne_zero
  aesop

/-- for `0 ≤ a < b < n` the `(a + 1)`-th face of `σ (a + 1) b` is the `(a + 1)`-th face of
  `σ a b`. -/
lemma faceImage_succ_eq (hab : a < b) :
    faceImage a.succ.castSucc (f ⟨a.succ, by dsimp; omega⟩ b) =
      faceImage a.succ.castSucc (f a b) := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [f, f₂, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
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

/-- for `0 ≤ a < b < n`, the `(a + 1)`-th face of `σ (a + 1) b` is contained in `σ a b`. -/
lemma faceImage_succ_le (hab : a < b) :
    faceImage a.succ.castSucc (f ⟨a.succ, by simp; omega⟩ b) ≤ σ a b := by
  rw [faceImage_succ_eq a b hab]
  exact faceImage_le _ _ _

/-- for `0 ≤ a < b < n`, the image of `Λ[n + 1, (a + 1) + 1]` under `f a b` is contained
  in `X(b, a)`. -/
lemma innerHornImage_succ_le_filtration₂ (a : Fin b) :
    innerHornImage ⟨a.succ, by omega⟩ b
      ≤ filtration₂ b a.castSucc := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a.succ, by omega⟩ -- check whether the face is the (a + 1)-th
  · subst h
    refine le_sup_of_le_right (le_iSup_of_le ⟨a, Nat.lt_add_one a⟩ ?_)
    exact faceImage_succ_le ⟨a, by omega⟩ b ((Fin.mk_lt_of_lt_val a.2))
  · apply le_sup_of_le_left
      (le_sup_of_le_left
        ((faceImage_le_boundary_prod_top _ _ _ hj h).trans (prod_top_le_unionProd _ _)))

/-- for `0 ≤ b < n`, the image of `Λ[n + 1, 1]` under `f 0 b` is contained in `X(b)`. -/
lemma innerHornImage_zero_le_filtration₁ (n : ℕ) (b : Fin (n + 1)) :
    innerHornImage ⟨0, by omega⟩ b ≤ filtration₁ b.castSucc := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  by_cases h : j = 0
  · subst h
    exact le_sup_of_le_left
      ((faceImage_zero_le_top_prod_horn n b).trans (top_prod_le_unionProd _ _))
  · exact le_sup_of_le_left
      ((faceImage_le_boundary_prod_top _ _ _ hj h).trans (prod_top_le_unionProd _ _))

/-- a subcomplex `A` of `Δ[n] ⊗ Δ[2]` which is contained in `σ a b` is contained in the image of
  `Λ[n + 1, a + 1]` under `f a b` iff the `(a + 1)`-th face of `σ a b` is not contained in `A`. -/
lemma subcomplex_le_innerHornImage_iff {a b : Fin n} (hab : a ≤ b) (A : (Δ[n] ⊗ Δ[2]).Subcomplex) (hA : A ≤ σ a b) :
    A ≤ innerHornImage a b ↔ ¬ faceImage a.succ.castSucc (f a b) ≤ A :=
  letI := f_mono hab
  subcomplex_le_horn_image_iff (f a b) A hA a.succ.castSucc

/-- for `0 ≤ a < b < n`, the `((a + 1) + 1)`-th face of `σ (a + 1) b` is not contained in
  `Δ[n] ⊗ Λ[2, 1]`. -/
lemma faceImage_succ_not_le_unionProd₁ (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b)
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

/-- for `0 ≤ a < b < n`, the `((a + 1) + 1)`-th face of `σ (a + 1) b` is not contained in
  `∂Δ[n] ⊗ Δ[2]`. -/
lemma faceImage_succ_not_le_unionProd₂ (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b)
      ≤ ∂Δ[n].prod ⊤ := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary, f]
  change Function.Surjective (Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
  intro i
  use i
  dsimp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp [Fin.lt_iff_val_lt_val]
  split
  all_goals simp; intro h'; rw [Nat.mod_eq_of_lt (by omega)] at h'; omega

/-- for `0 ≤ a < b < n`, the `((a + 1) + 1)`-th face of `σ (a + 1) b` is not contained in
  `σ i j` for any `0 ≤ i ≤ j < b`. -/
lemma faceImage_succ_not_le_σij (a j : Fin b) (i : Fin j.succ) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b)
      ≤ σ ⟨i, by omega⟩ ⟨j, by omega⟩ := by
  simp [σ, face_singleton_compl]
  intro x h
  simp [f] at h
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
        have p : i.1 % (n + 1) < (x b.castSucc).1 := by rwa [Nat.mod_eq_of_lt (by omega), ← not_le]
        have p' : (a.1 + 1) % (n + 1) < b.1 + 1 := by
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        simp [p, p'] at h₁
        rw [Fin.eq_mk_iff_val_eq] at h₁
        simp at h₁
        omega
      · next h'' => omega
  · next h =>
    simp_rw [← h] at h₁ h₂
    have p : ¬(a.1 + 1) % (n + 1) < b.1 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [show a.1 + 1 < a.1 + 1 + 1 by omega, h.symm.le, p] at h₁ h₂
    split at h₁
    · next h' =>
      rw [Nat.mod_eq_of_lt (by omega)] at h'
      aesop
    · next h' =>
      rw [Nat.mod_eq_of_lt (by omega)] at h'
      rw [Fin.eq_mk_iff_val_eq] at h₁
      simp at h₁
      omega

/-- for `0 ≤ a < b < n`, the `((a + 1) + 1)`-th face of `σ (a + 1) b` is not contained in
  `σ i b` for any `0 ≤ i ≤ a`. -/
lemma faceImage_succ_not_le_σib (a : Fin b) (i : Fin a.succ) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b)
      ≤ σ ⟨i, by omega⟩ b := by
  simp [σ, face_singleton_compl]
  intro x h
  simp [f] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [f, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, f₂, objMk] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  dsimp at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  replace h₁ := congr_fun h₁ ⟨a.succ, by omega⟩
  replace h₂ := congr_fun h₂ ⟨a.succ, by omega⟩
  simp [Fin.succAbove, Fin.predAbove, f₂', Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
    show ¬(a.1 + 1) % (n + 1) < a.1 + 1 by rw [Nat.mod_eq_of_lt (by omega)]; omega] at h₁ h₂
  split at h₁
  · next h =>
    rw [Nat.mod_eq_of_lt (by omega)] at h
    aesop
  · next h =>
    rw [Nat.mod_eq_of_lt (by omega)] at h
    rw [Fin.eq_mk_iff_val_eq] at h₁
    simp_all
    omega

/-- for `0 ≤ a < b < n`, the `((a + 1) + 1)`-th face of `σ (a + 1) b` is not contained in
  `X(b, a)`. -/
lemma faceImage_succ_not_le_filtration₂ (a : Fin b) :
    ¬ faceImage ⟨a.succ.succ, by omega⟩ (f ⟨a.succ, by omega⟩ b)
      ≤ filtration₂ b a.castSucc := by
  simp [face_singleton_compl, filtration₂, filtration₁, unionProd]
  refine ⟨⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, fun j i ↦ ?_⟩, fun i ↦ ?_⟩
  · -- not in `Δ[n] ⨯ Λ[2, 1]`
    have := faceImage_succ_not_le_unionProd₁ b a
    simp [face_singleton_compl] at this
    exact this
  · -- not in `∂Δ[n] ⨯ Δ[2]`
    have := faceImage_succ_not_le_unionProd₂ b a
    simp [face_singleton_compl] at this
    exact this
  · -- not in any `σij` for `i ≤ j < b`
    have := faceImage_succ_not_le_σij b a j i
    simp [face_singleton_compl] at this
    exact this
  · -- not in any `σib` for any `i < a + 1`
    have := faceImage_succ_not_le_σib b a i
    simp [face_singleton_compl] at this
    exact this

/-- for `0 ≤ b < n`, the `1`-th face of `σ 0 b` is not contained in `X(b)`. -/
lemma faceImage_one_not_le_filtration₁ (n : ℕ) (b : Fin (n + 1)) :
  ¬ faceImage 1 (f 0 b) ≤ filtration₁ b.castSucc := by
  simp [face_singleton_compl, filtration₂, filtration₁, unionProd]
  refine ⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩
  · simp [mem_horn_iff]
    change insert 1 (Set.range (f₂' _ b ∘ (Fin.succ 0).succAbove)) = Set.univ
    ext i
    fin_cases i
    all_goals simp [Fin.succAbove]
    · exact ⟨0, by simp⟩
    · exact ⟨b.succ, by simp [Fin.lt_iff_val_lt_val, Fin.succ_ne_zero]⟩
  · simp [boundary, f]
    change Function.Surjective (Fin.predAbove 0 ∘ (Fin.succ 0).succAboveOrderEmb)
    intro i
    use i
    simp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
    simp_rw [Fin.lt_iff_val_lt_val]
    aesop
  · intro j i
    simp [σ, face_singleton_compl]
    intro x h
    have h₁ := congr_arg Prod.fst h
    have h₂ := congr_arg Prod.snd h
    simp [f, SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
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
        have p : i.1 % (n + 1 + 1) < (x b.castSucc).1 := by rwa [Nat.mod_eq_of_lt (by omega), ← not_le]
        simp [p] at h₁
        split at h₂
        · rw [Fin.eq_mk_iff_val_eq] at h₁
          simp at h₁
          omega
        · omega

end

open Sigma.Lex in
lemma subcomplex_le_innerHornImage_iff' (i : Σₗ (b : Fin n), Fin b.succ) (j : Fin (n + 2))
    {A : (Δ[n] ⊗ Δ[2]).Subcomplex} (hA : A ≤ σ_ i) :
    A ≤ (Λ[n + 1, j].image (ιSimplex i)) ↔ ¬ faceImage j (ιSimplex i) ≤ A := by
  dsimp [σ_] at hA
  rw [ofSimplex_eq_range] at hA
  exact subcomplex_le_horn_image_iff (ιSimplex i) A hA j

open Sigma.Lex in
lemma temp₂ (b : Fin (n + 1)) (a : Fin b) :
    σ_ ⟨b, a.succ⟩ ⊓
      filtration₁' (n + 1) ⟨b, a.castSucc⟩ =
        Λ[n + 2, ⟨a + 2, by omega⟩].image (ιSimplex ⟨b, a.succ⟩) := by
  apply le_antisymm
  · rw [subcomplex_le_innerHornImage_iff' _ _ inf_le_left, le_inf_iff, not_and]
    intro
    simp
    convert faceImage_succ_not_le_filtration₂ b a
    · exact eq_f _
    · exact filtration₁'_eq' _ _
  · apply le_inf
    · rw [σ_, ofSimplex_eq_range]
      exact image_le_range _ _
    · convert innerHornImage_succ_le_filtration₂ b a
      · exact eq_f _
      · exact filtration₁'_eq' _ _

open Sigma.Lex in
lemma temp₃ (b : Fin n) :
    σ_ ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩ ⊓
      filtration₁' (n + 1) ⟨b.castSucc, ⟨b, Nat.lt_add_one _⟩⟩ =
        Λ[n + 2, 1].image (ιSimplex ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩) := by
  apply le_antisymm
  · rw [subcomplex_le_innerHornImage_iff' _ _ inf_le_left, le_inf_iff, not_and]
    intro
    convert faceImage_one_not_le_filtration₁ _ b.succ
    · exact eq_f _
    · rw [filtration₁'_eq', ← Fin.succ_castSucc, ← filtration₂_last]
      rfl
  · apply le_inf
    · rw [σ_, ofSimplex_eq_range]
      exact image_le_range _ _
    · rw [eq_f, filtration₁'_eq']
      convert innerHornImage_zero_le_filtration₁ _ b.succ
      exact filtration₂_last b.castSucc

open Sigma.Lex in
def filtrationPushout_intermediate (n : ℕ) (i : Σₗ (b : Fin (n + 1)), Fin b.succ) (hn : i < ⊤) :
    Sq
      (Λ[n + 2, ⟨(succ i).2.succ, by omega⟩].image (ιSimplex (succ i)))
      (σ_ (succ i))
      (filtration₁' (n + 1) i)
      (filtration₁' (n + 1) (succ i))
      where
  max_eq := by rw [σ_, filtration₁_succ', sup_comm]
  min_eq := by
    obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
    · exfalso
      rwa [top_eq_last, lt_self_iff_false] at hn
    · rw [Fin.succ_eq₁]
      exact temp₂ b a
    · rw [Fin.succ_eq₂]
      exact temp₃ b

open Sigma.Lex in
def filtrationPushout_zero (n : ℕ) :
    Sq
      (Λ[n + 2, 1].image (ιSimplex ⊥))
      (σ_ ⊥)
      (∂Δ[n + 1].unionProd Λ[2, 1])
      (filtration₁' (n + 1) ⊥) where
  max_eq := by simp [σ_, filtration₁', sup_comm]
  min_eq := by
    rw [σ_, ofSimplex_eq_range]
    apply le_antisymm
    · rw [subcomplex_le_horn_image_iff, le_inf_iff, not_and]
      · exact fun _ h ↦ faceImage_one_not_le_filtration₁ n 0 (le_sup_of_le_left h)
      · exact inf_le_left
    · apply le_inf
      · exact image_le_range _ _
      · convert (innerHornImage_zero_le_filtration₁ n 0)
        rw [Fin.castSucc_zero, filtration₁_zero]

end σ
