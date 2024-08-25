import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Sites.Subsheaf
import Quasicategory.Terminal

open CategoryTheory GrothendieckTopology SimplicialObject Simplicial

namespace SSet

variable {S T : SSet} {n : ℕ}

structure IsDegenerate (s : S _[n + 1]) : Prop where
  exists_simplex : ∃ (x : S _[n]), s = (S.σ n) x

abbrev Nondegenerate (s : S _[n + 1]) : Prop := ¬ IsDegenerate s

lemma image_degen_of_degen (f : S ⟶ T) (s : S _[n + 1]) (h : IsDegenerate s) :
    IsDegenerate (f.app _ s) where
  exists_simplex := by
    obtain ⟨x, hx⟩ := h.exists_simplex
    use f.app _ x
    rw [hx]
    exact congr_fun (f.naturality (SimplexCategory.σ n).op) x

lemma degen_of_image_degen_mono (f : S ⟶ T) [Mono f]
    (s : S _[n + 1]) (h : IsDegenerate (f.app _ s)) :
    IsDegenerate s where
  exists_simplex := sorry

abbrev SimplicialSubset (S : SSet) := Subpresheaf S

namespace SimplicialSubset

variable (A B : SimplicialSubset S)

--#synth (Mono (Subpresheaf.ι A))

def union : SimplicialSubset S where
  obj n := A.obj n ⊔ B.obj n
  map i _ h := by
    cases h with
    | inl h =>
      left
      apply A.map i h
    | inr h =>
      right
      apply B.map i h

def inter : SimplicialSubset S where
  obj n := A.obj n ⊓ B.obj n
  map i _ h := ⟨(A.map i) h.1, (B.map i) h.2⟩

instance : Lattice (SimplicialSubset S) where
  sup := union
  le A B := ∀ n, A.obj n ≤ B.obj n
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h₁ h₂ n _ h := by
    cases h with
    | inl h => exact h₁ n h
    | inr h => exact h₂ n h
  inf := inter
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _:= inf_le_right
  le_inf _ _ _ h₁ h₂ n := le_inf (h₁ n) (h₂ n)

noncomputable
def mono_iso (f : S ⟶ T) [h : Mono f] : S ≅ (imagePresheaf f).toPresheaf where
  hom := {
    app := fun n x ↦ ⟨f.app n x, by simp⟩
    naturality := by
      intros n m g
      ext x
      simp only [imagePresheaf, Subpresheaf.toPresheaf, types_comp_apply, Subtype.mk.injEq]
      exact FunctorToTypes.naturality S T f g x
  }
  inv := {
    app := fun n x ↦ Exists.choose x.2
    naturality := by
      intro n m g
      ext x
      rw [NatTrans.mono_iff_mono_app] at h
      have := (mono_iff_injective _).1 (h n)
      simp
      sorry
  }

variable (S : SSet) (k : ℕ)

open SimplexCategory

def hom_of_le (m k : ℕ) (h : m ≤ k) :
    ([m] : SimplexCategory) ⟶ [k] :=
  Hom.mk ⟨fun x ↦ Fin.castLE (Nat.add_le_add_right h 1) x, fun _ _ h ↦ h⟩

def HasFactorization (n : ℕ) (s : S _[n]) : Prop :=
  ∃ (m : ℕ) (_ : m ≤ k) (τ : S _[m]) (f : Δ[n] ⟶ Δ[m]),
    (S.yonedaEquiv _).symm s = f ≫ ((yonedaEquiv S _).symm τ)

-- skₖ(S)ₙ
def skeleton_subset (k n : ℕ) : Set (S _[n]) :=
  { s : S _[n] | HasFactorization S k n s }

lemma _0016 (h : n ≤ k) : ⊤ ⊆ skeleton_subset S k n :=
    fun s _ ↦ ⟨n, h, s, 𝟙 _, by aesop⟩

lemma _0500 (h : l ≤ k) : skeleton_subset S l n ⊆ skeleton_subset S k n :=
    fun _ ⟨m, hm, τ, f, hf⟩ ↦ ⟨m, le_trans hm h, τ, f, hf⟩

def skeleton : SimplicialSubset S where
  obj n := skeleton_subset S k (len n.unop)
  map := by
    intro n n' g s ⟨m, hm, τ, f, hf⟩
    simp
    sorry

abbrev Sk (k : ℕ) (S : SSet) : SSet := (skeleton S k).toPresheaf

lemma _0018 (h : k < 0) : Sk k S = SSet.empty := by aesop

end SimplicialSubset

end SSet
