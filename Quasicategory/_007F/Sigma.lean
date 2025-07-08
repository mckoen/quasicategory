import Quasicategory._007F.Filtration
import Quasicategory._007F.Order

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ} (a b : Fin n)

namespace σ

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

/-
for `0 ≤ a < b < n`, (so for `n ≥ 2`) the following square

`Λ[n+1,(a+1)+1]` -------> `X(b) ∪ σ0b ∪ ... ∪ σab`
        |                             |
        |                             |
        v                             V
    `σ(a+1)b` ------> `X(b) ∪ σ0b ∪ ... ∪ σab ∪ σ(a+1)b`

so this says `X(b,a) ↪ X(b,a+1)` is inner anodyne

need `b < n` because `X(n)` is the last term. `X(n-1, n-1) = X(n)`.
need `a < b` because we need `a + 1 ≤ b`
-/
def filtrationPushout_intermediate (a : Fin b) :
    Sq
      (σ.innerHornImage ⟨a.succ, by omega⟩ b)
      (σ ⟨a.succ, by omega⟩ b)
      (filtration₂ b a.castSucc)
      (filtration₂ b a.succ)
      where
  max_eq := by rw [filtration₂_succ b a, sup_comm]
  min_eq := by
    apply le_antisymm
    · rw [σ.subcomplex_le_innerHornImage_iff (by simp [Fin.le_iff_val_le_val]; omega) _ inf_le_left, le_inf_iff, not_and]
      exact fun _ ↦ (σ.faceImage_succ_not_le_filtration₂ b a)
    · exact le_inf (σ.innerHornImage_le _ _) (σ.innerHornImage_succ_le_filtration₂ _ _)

set_option maxHeartbeats 800000 in
open Sigma.Lex in
def filtrationPushout_intermediate' (i : Σₗ (b : Fin (n + 1)), Fin b.succ) (h0 : ⊥ < i) (hn : i < ⊤) :
    Sq
      (σ.innerHornImage (⟨(succ i).2, by omega⟩ : Fin (n + 1)) ⟨(succ i).1, by simp⟩)
      (ofSimplex (σ.simplex (succ i)).1)
      (filtration₁' (n + 1) i)
      (filtration₁' (n + 1) (succ i))
      where
  max_eq := by rw [filtration₁_succ', sup_comm]
  min_eq := by
    clear a b
    induction n with
    | zero =>
      have : i = ⊥ := by
        rw [Sigma.Lex.bot_eq_zero]
        rcases i with ⟨b, a⟩
        have := Fin.eq_zero b
        subst this
        have := Fin.eq_zero a
        subst this
        rfl
      exfalso
      exact hn.not_le this.symm.le
    | succ n _ =>
      apply le_antisymm
      · rw [σ.eq_σ]
        rcases i with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
        induction b with
        | zero =>
          dsimp
          simp at ha
          subst ha
          change _ ≤ innerHornImage 0 1
          rw [σ.subcomplex_le_innerHornImage_iff (Fin.zero_le _) _ inf_le_left, le_inf_iff, not_and]
          intro
          change ¬(face {1}ᶜ).image (f 0 1) ≤ filtration₁' (n + 2) ⊥
          rw [filtration₁_zero', Sigma.Lex.bot_eq_zero, σ.eq_σ]
          convert σ.faceImage_one_not_le_filtration₁ (n + 1) 1
          simp [filtration₁]
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
            rw [σ.subcomplex_le_innerHornImage_iff (by simp [Fin.le_iff_val_le_val]) _ inf_le_left, le_inf_iff, not_and]
            intro
            dsimp
            have := σ.faceImage_succ_not_le_filtration₂ ⟨b + 1, hb⟩ 0
            dsimp at this
            convert this
            exact filtration₁'_eq' _ _
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
              rw [σ.subcomplex_le_innerHornImage_iff (by simpa [Fin.le_iff_val_le_val]) _ inf_le_left, le_inf_iff, not_and]
              intro
              dsimp
              have := σ.faceImage_succ_not_le_filtration₂ ⟨b + 1, hb⟩ ⟨a + 1, by simpa⟩
              dsimp at this
              convert this
              exact filtration₁'_eq' _ _
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
                  simp [Fin.ext_iff, Fin.lt_iff_val_lt_val, Sigma.Lex.top_eq_last] at hn hn'
                  subst hn
                  simp_all
              have h := Sigma.Lex.Fin.succ_eq_of_lt_last ⟨a + 1, hb⟩ (by simpa [Fin.lt_iff_val_lt_val] using goal)
              have h' : (succ ⟨⟨a + 1, hb⟩, ⟨a + 1, ha⟩⟩).snd.1 = (⟨⟨a + 2, goal⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ :  Σₗ (b : Fin (n + 1 + 1)), Fin b.succ).snd := by
                dsimp only [Fin.val_succ, Fin.succ_mk, lt_self_iff_false, Fin.zero_eta,
                  Fin.val_zero] at h ⊢
                rw [h]
                rfl
              simp_rw [h, h']
              rw [σ.subcomplex_le_innerHornImage_iff (by simp [Fin.le_iff_val_le_val]) _ inf_le_left, le_inf_iff, not_and]
              intro
              dsimp
              rw [filtration₁'_eq', filtration₂_last]
              exact σ.faceImage_one_not_le_filtration₁ (n + 1) ⟨a + 1 + 1, goal⟩
      · rw [σ.eq_σ]
        apply le_inf (σ.innerHornImage_le _ _)
        · rcases i with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
          induction b with
          | zero =>
            dsimp only [Fin.val_succ, Fin.zero_eta, Fin.succ_zero_eq_one, Fin.val_one,
              succ.eq_1, Fin.val_zero, not_lt_zero', ↓dreduceDIte, Fin.zero_eq_last_iff,
              AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, Fin.val_last, Fin.mk_one,
              Fin.succ_one_eq_two, Fin.val_two, Fin.isValue, Fin.castSucc_one, succ, ↓reduceDIte]
            simp at ha
            subst ha
            convert innerHornImage_zero_le_filtration₁ (n + 1) 1
            rw [filtration₁'_eq']
            dsimp [filtration₂]
            have := filtration₁_succ (0 : Fin (n + 2))
            dsimp at this
            rw [this]
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
              rw [filtration₁'_eq']
              dsimp only [Fin.val_succ, Fin.succ_mk, Fin.zero_eta, succ.eq_1, Fin.val_zero,
                lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true,
                Fin.succ_zero_eq_one, Fin.val_one, Fin.mk_one, dite_eq_ite, Int.reduceNeg, id_eq,
                Nat.cast_ofNat, Int.Nat.cast_ofNat_Int, Nat.reduceAdd, Nat.add_zero, eq_mpr_eq_cast, Fin.succ_one_eq_two]
              exact σ.innerHornImage_succ_le_filtration₂ ⟨b + 1, hb⟩ ⟨0, Nat.zero_lt_succ _⟩
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
                rw [filtration₁'_eq']
                convert σ.innerHornImage_succ_le_filtration₂ ⟨b + 1, hb⟩ ⟨a + 1, by simp; omega⟩
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
                    simp [Fin.ext_iff, Fin.lt_iff_val_lt_val, Sigma.Lex.top_eq_last] at hn hn'
                    subst hn
                    simp_all
                have h := Sigma.Lex.Fin.succ_eq_of_lt_last ⟨a + 1, hb⟩ (by simpa [Fin.lt_iff_val_lt_val] using goal)
                have h' : (succ ⟨⟨a + 1, hb⟩, ⟨a + 1, ha⟩⟩).snd.1 = (⟨⟨a + 2, goal⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ :  Σₗ (b : Fin (n + 1 + 1)), Fin b.succ).snd := by
                  dsimp only [Fin.val_succ, Fin.succ_mk, lt_self_iff_false, Fin.zero_eta,
                    Fin.val_zero] at h ⊢
                  rw [h]
                  rfl
                simp_rw [h, h']
                rw [filtration₁'_eq', filtration₂_last]
                simp
                exact innerHornImage_zero_le_filtration₁ _ ⟨a + 2, goal⟩

/--
`0 ≤ b < (n + 1)`
`X(b) ↪ X(b, 0)`
`filtration₁ b ↪ filtration₂ b 0`

so this says `X(b-1,b-1) = X(b) ↪ X(b,0)` is inner anodyne
-/
def filtrationPushout_join (n : ℕ) (b : Fin (n + 1)) :
    Sq
      (σ.innerHornImage 0 b)
      (σ 0 b)
      (filtration₁ b.castSucc)
      (filtration₂ b ⟨0, Nat.zero_lt_succ _⟩)
      where
  max_eq := by
    cases b using Fin.cases with
    | zero => simp [filtration₁, filtration₂, sup_comm]
    | succ =>
      rw [filtration₂_zero (Nat.zero_ne_add_one _).symm, ← Fin.succ_castSucc, filtration₁_succ, sup_comm]
      rfl
  min_eq := by
    apply le_antisymm
    · rw [σ.subcomplex_le_innerHornImage_iff (by simp [Fin.le_iff_val_le_val]) _ inf_le_left, le_inf_iff, not_and]
      exact fun _ ↦ σ.faceImage_one_not_le_filtration₁ n b
    · apply le_inf (σ.innerHornImage_le 0 _) (σ.innerHornImage_zero_le_filtration₁ n b)

/--
`Λ[n+3,n+2]` -------> `X(n+1) ∪ σ0(n+1) ∪ ... ∪ σn(n+1)`
      |                               |
      |                               |
      v                               V
`σ(n+1)(n+1)` ------> `X(n+1) ∪ σ0(n+1) ∪ ... ∪ σn(n+1) ∪ σ(n+1)(n+1) = X(n+2)` -/
def filtrationPushout_last (n : ℕ) :
    Sq
      (σ.innerHornImage (Fin.last (n + 1)) (Fin.last (n + 1)))
      (σ (Fin.last (n + 1)) (Fin.last (n + 1)))
      (filtration₂ (Fin.last (n + 1)) ⟨n, by dsimp; omega⟩)
      (filtration₃ 0) := by
  rw [filtration₃_zero]
  have := filtration₂_last (n := n + 2) ⟨n + 1, by omega⟩
  simp at this
  rw [← this]
  exact filtrationPushout_intermediate (Fin.last (n + 1)) ⟨n, by simp⟩

/-
`Λ[n+2,1]` ---> `X(0)`
    |             |
    |             |
    v             V
  `σ00` ------> `X(1)`
-/
def filtrationPushout_zero (n : ℕ) :
    Sq
      (σ.innerHornImage 0 0)
      (σ 0 0)
      (∂Δ[n + 1].unionProd Λ[2, 1])
      (filtration₁ (1 : Fin (n + 2))) := by
  have h := filtration₁_succ (0 : Fin (n + 1))
  have h' := filtration₂_zero (Nat.zero_ne_add_one n).symm 0
  dsimp at h h'
  rw [← filtration₁_zero, h]
  simp
  rw [← h']
  exact filtrationPushout_join n 0

section examples

/-
`Λ[2,1]` --------> `X(0)`
    |                 |
    |                 |
    v                 V
  `σ00` ------> `X(0) ∪ σ00`
-/
def filtrationPushout_zero1 :
    Sq
      (σ.innerHornImage (n := 1) 0 0)
      (σ 0 0)
      (∂Δ[1].unionProd Λ[2, 1])
      (filtration₁ 1) :=
  filtrationPushout_zero 0

/-
`Λ[3,1]` --------> `X(0)`
    |                 |
    |                 |
    v                 V
  `σ00` ------> `X(0) ∪ σ00`
-/
def filtrationPushout_zero2 :
    Sq
      (σ.innerHornImage (n := 2) 0 0)
      (σ 0 0)
      (∂Δ[2].unionProd Λ[2, 1])
      (filtration₁ 1) :=
  filtrationPushout_zero 1

/-
`Λ[3,1]` ------> `X(0) ∪ σ00`
    |                  |
    |                  |
    v                  V
  `σ01` ------> `X(0) ∪ σ00 ∪ σ01`
-/
def filtrationPushout_join2 :
    Sq
      (σ.innerHornImage (n := 2) 0 1)
      (σ 0 1)
      (filtration₁ 1)
      (filtration₂ 1 ⟨0, Nat.zero_lt_succ 1⟩) :=
  filtrationPushout_join 1 1

/--
`Λ[3,2]` -------> `X(0) ∪ σ00 ∪ σ01`
    |                     |
    |                     |
    v                     V
  `σ11` ----> ``X(0) ∪ σ00 ∪ σ01 ∪ σ11` -/
def filtrationPushout_two2 :
    Sq
      (σ.innerHornImage (n := 2) 1 1)
      (σ 1 1)
      (filtration₂ 1 ⟨0, Nat.zero_lt_succ 1⟩)
      (filtration₃ 0) :=
  filtrationPushout_last 0

end examples

/-
variable (b : Fin n) (a : Fin b.1)

#check Subcomplex.isColimitPushoutCoconeOfPullback (f (n := n) ⟨a.succ, by omega⟩ b)
  (filtration₂ b a.castSucc) (filtration₂ b a.succ) (Λ[n + 1, a + 2]) ⊤
-/
end σ

/-
if `n = 2`, `0 < 1 < 2`

get `X(0,0) ≤ X(1, 0) ≤ X(1, 1) = X(2)`

have for `0 ≤ b < n`, `X(b) ↪ X(b, 0)`
have for `0 ≤ a < b < n`, `X(b, a) ↪ X(b, a + 1)`

so we have `X(0) ≤ X(0, 0) = X(1) ≤ X(1, 0) ≤ X(1, 1) = X(2) ≤ ...`
  `... ≤ X(n-1) ≤ X(n-1, 0) ≤ X(n-1, n-2) ≤ X(n-1, n-1) = X(n)`

`X(0, 0) ≤ X(1, 0) ≤ X(1, 1) ≤ X(2, 0) ≤ ... ≤ X(n-2, n-2) ≤ X(n-1, 0) ≤ X(n-1, n-2) ≤ X(n-1, n-1)`

-/
