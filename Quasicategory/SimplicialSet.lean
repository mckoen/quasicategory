import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Sites.Subsheaf
import Quasicategory.Terminal

open CategoryTheory GrothendieckTopology SimplicialObject Simplicial

namespace SSet

variable {S T : SSet} {n : ℕ}

structure IsDegenerate (s : S _[n + 1]) : Prop where
  exists_simplex : ∃ (x : S _[n]), s = (S.σ n) x

abbrev Nondegenerate (s : S _[n + 1]) : Prop := ¬ IsDegenerate s

-- `0013`
lemma image_degen_of_degen (f : S ⟶ T) (s : S _[n + 1]) (h : IsDegenerate s) :
    IsDegenerate (f.app _ s) where
  exists_simplex := by
    obtain ⟨x, hx⟩ := h.exists_simplex
    use f.app _ x
    rw [hx]
    exact congr_fun (f.naturality (SimplexCategory.σ n).op) x

-- `0013`
lemma degen_of_image_degen_mono (f : S ⟶ T) [hf : Mono f]
    (s : S _[n + 1]) (h : IsDegenerate (f.app (.op [n + 1]) s)) :
    IsDegenerate s where
  exists_simplex := by
    obtain ⟨a, ha⟩ := h.exists_simplex
    have := (mono_iff_injective _).1 (((NatTrans.mono_iff_mono_app _ _).1 hf) (Opposite.op [n + 1]))
    dsimp [σ] at ha ⊢
    sorry

lemma _04ZN (f : S ⟶ T) :
    (∀ (n : ℕ) (t : T _[n + 1]) (ht : Nondegenerate t), t ∈ Set.range (f.app _)) → Epi f := by
  intro h
  rw [NatTrans.epi_iff_epi_app]
  intro m
  rw [epi_iff_surjective]
  intro Tm
  sorry

abbrev SimplicialSubset (S : SSet) := Subpresheaf S

namespace SimplicialSubset

variable (A B : SimplicialSubset S)

--#synth Mono A.ι

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
      exact FunctorToTypes.naturality S T f g x }
  inv := {
    app := fun n ⟨x, hx⟩ ↦ Exists.choose hx
    naturality := fun n m g ↦ by
      ext x
      apply (mono_iff_injective _).1 (((NatTrans.mono_iff_mono_app _ _).1 h) m)
      dsimp only [types_comp_apply, Subpresheaf.toPresheaf_obj, imagePresheaf_obj,
        Subpresheaf.toPresheaf_map_coe]
      let a := ((imagePresheaf f).toPresheaf.map g x).property
      rw [a.choose_spec, ← types_comp_apply (S.map g) (f.app m),
        congr_fun (f.naturality g) x.property.choose, types_comp_apply, x.property.choose_spec]
      dsimp only [imagePresheaf_obj, Subpresheaf.toPresheaf_map_coe] }
  hom_inv_id := by
    ext n x
    apply (mono_iff_injective _).1 (((NatTrans.mono_iff_mono_app _ _).1 h) n)
    exact Exists.choose_spec (Set.mem_range_self x)
  inv_hom_id := by
    ext n x
    dsimp at x
    change
        ⟨f.app n (Exists.choose x.2), Set.mem_range_self (Exists.choose x.property)⟩ = x
    congr
    exact Exists.choose_spec x.2

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
    refine ⟨m, hm, τ, standardSimplex.map g.unop ≫ f, ?_⟩
    rw [Category.assoc, ← hf]
    ext l x
    change S.map x.down.op (S.map g s) =
      S.map ((standardSimplex.map g.unop).app l x).down.op s
    simp [standardSimplex, uliftFunctor]

abbrev Sk (k : ℕ) (S : SSet) : SSet := (skeleton S k).toPresheaf

lemma _0018 (h : k < 0) : Sk k S = SSet.empty := by aesop

end SimplicialSubset

end SSet
