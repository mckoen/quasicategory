import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Sites.Subsheaf
import Quasicategory.Terminal
import Quasicategory.KInjective.WellOrderContinuous

open CategoryTheory GrothendieckTopology SimplicialObject Simplicial

namespace SSet

abbrev SimplicialSubset (S : SSet) := Subpresheaf S

namespace SimplicialSubset

variable (A B : SimplicialSubset S)

def empty (S : SSet) : SimplicialSubset S where
  obj _ := ∅
  map _ _ x := x

def top (S : SSet) : SimplicialSubset S where
  obj _ := Set.univ
  map _ _ x := x

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

end SimplicialSubset

variable {S : SSet}

open SimplexCategory

-- how to prove things are degenerate?
inductive IsDegenerate : {n : ℕ} → (s : S _[n]) → Prop
  | mk (n : ℕ) (x : S _[n]) (i : Fin (n + 1)) : IsDegenerate (S.σ i x)

abbrev Nondegenerate {S : SSet} (s : S _[n]) : Prop := ¬ IsDegenerate s

-- `0013`
lemma image_degen_of_degen (f : S ⟶ T) (s : S _[n]) (h : IsDegenerate s) :
    IsDegenerate (f.app _ s) := by
  induction h with
  | mk m s i =>
  sorry
  /-
  exists_simplex := by
    obtain ⟨x, hx⟩ := h.exists_simplex
    use f.app _ x
    rw [hx]
    exact congr_fun (f.naturality (SimplexCategory.σ n).op) x
  -/

-- `0013`
lemma degen_of_image_degen_mono (f : S ⟶ T) [hf : Mono f]
    (s : S _[n]) (h : IsDegenerate (f.app (.op [n]) s)) :
    IsDegenerate s := sorry
  /-
  exists_simplex := by
    obtain ⟨a, ha⟩ := h.exists_simplex
    have := (mono_iff_injective _).1 (((NatTrans.mono_iff_mono_app _ _).1 hf) (Opposite.op [n + 1]))
    dsimp [σ] at ha ⊢
    sorry
  -/

lemma _04ZN (f : S ⟶ T) :
    (∀ (n : ℕ) (t : T _[n]) (ht : Nondegenerate t), t ∈ Set.range (f.app _)) → Epi f := sorry
  /-
  intro h
  rw [NatTrans.epi_iff_epi_app]
  intro m
  rw [epi_iff_surjective]
  intro Tm
  sorry
  -/

variable (S : SSet)

class dim_le (k : ℕ) : Prop where
  condition : ∀ (n : ℕ) (s : S _[n]), k < n → IsDegenerate s

/-
def hom_of_le (m k : ℕ) (h : m ≤ k) :
    ([m] : SimplexCategory) ⟶ [k] :=
  Hom.mk ⟨fun x ↦ Fin.castLE (Nat.add_le_add_right h 1) x, fun _ _ h ↦ h⟩
-/

-- want to somehow say the skeleton is empty for k < 0
def HasFactorization (k n : ℕ) (s : S _[n]) : Prop :=
  ∃ (m : ℕ) (_ : m ≤ k) (τ : S _[m]) (f : Δ[n] ⟶ Δ[m]),
    (S.yonedaEquiv [n]).symm s = f ≫ (S.yonedaEquiv [m]).symm τ

-- skₖ(S)ₙ
def skeleton_subset (k n : ℕ) : Set (S _[n]) :=
  { s : S _[n] | HasFactorization S k n s }

lemma _0016 (h : n ≤ k) : ⊤ ≤ skeleton_subset S k n :=
  fun s _ ↦ ⟨n, h, s, 𝟙 _, by aesop⟩

lemma _0500 (n : ℕ) (h : l ≤ k) : skeleton_subset S l n ≤ skeleton_subset S k n :=
  fun _ ⟨m, hm, τ, f, hf⟩ ↦ ⟨m, le_trans hm h, τ, f, hf⟩

def skeleton (k : ℕ) : SimplicialSubset S where
  obj n := skeleton_subset S k (len n.unop)
  map := by
    intro n n' g s ⟨m, hm, τ, f, hf⟩
    refine ⟨m, hm, τ, standardSimplex.map g.unop ≫ f, ?_⟩
    rw [Category.assoc, ← hf]
    ext l x
    change S.map x.down.op (S.map g s) =
      S.map ((standardSimplex.map g.unop).app l x).down.op s
    simp [standardSimplex, uliftFunctor]

-- want to have Sk(-1, S) = ∅ as bottom element
def Sk (k : ℕ) : SSet := (S.skeleton k).toPresheaf

def Sk.ι (k : ℕ) : S.Sk k ⟶ S := (S.skeleton k).ι

/-- an n-simplex is degenerate iff it is in skₖ(S)ₙ for some k < n. -/
lemma _0011 (s : S _[n]) : IsDegenerate s ↔ (∃ (k : ℕ) (_ : k < n), s ∈ (S.skeleton k).obj (.op [n])) := by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | mk m x i =>
    refine ⟨m, Nat.lt.base m, m, le_rfl, x, standardSimplex.map (SimplexCategory.σ i), (Equiv.symm_apply_eq (S.yonedaEquiv [m + 1])).mpr rfl⟩
  · sorry

/-- a nondegenerate n-simplex is in skₖ(S)ₙ iff n ≤ K (i.e., iff skₖ(S)ₙ = Sₙ) -/
lemma _0017 (s : S _[n]) (hs : Nondegenerate s) : s ∈ (S.skeleton k).obj (.op [n]) ↔ n ≤ k := by
  refine ⟨?_, fun h ↦ _0016 S h (Set.mem_univ s)⟩
  intro h
  by_contra h'
  apply hs
  rw [not_le] at h'
  rw [_0011]
  use k

-- the k-skeleton has dimension ≤ k
instance (k : ℕ) : (S.Sk k).dim_le k where
  condition := by
    intro n ⟨s, hs⟩ hk
    by_contra h
    have : Nondegenerate s := by
      sorry
    rw [_0017 S s this] at hs
    rw [← not_le] at hk
    exact hk hs

def skeletonIso (k : ℕ) (hS : S.dim_le k) : SimplicialSubset.top S ≅ (S.skeleton k) where
  hom := by
    refine ⟨⟨?_⟩⟩
    intro ⟨n⟩ (s : S _[n.len]) _
    by_cases (IsDegenerate s)
    · rename_i h
      sorry
    · rename_i h
      apply (@_0017 S n.len k s h).2
      have := hS.condition n.len s
      rw [← not_imp_not] at this
      by_contra h'
      rw [not_le] at h'
      exact this h h'
  inv := LE.le.hom (fun _ _ _ ↦ _root_.trivial)

def boundaryIsoSkeleton (n : ℕ) : ∂Δ[n] ≅ (Δ[n].Sk (n - 1)) where
  hom := sorry
  inv := sorry

instance boundary_dim (k : ℕ) : ∂Δ[k].dim_le (k - 1) := sorry

def skeleton_hom_equiv {S T : SSet} (h : T.dim_le k) : (T ⟶ S.Sk k) ≃ (T ⟶ S) where
  toFun f := f ≫ (S.skeleton k).ι
  invFun f := {
    app := fun n t ↦ by
      sorry
  }
  left_inv := sorry
  right_inv := sorry

-- can also be shown using skeleton_hom_equiv
/-- every k simplex determines a map Δ[k] ⟶ (S.Sk k) -/
def simplex_map {S : SSet} (s : S _[k]) : Δ[k] ⟶ (S.Sk k) :=
  (yonedaEquiv _ _).symm (⟨s, _0016 S le_rfl (Set.mem_univ s)⟩)

/-- simplex_map induces ∂Δ[k] ⟶ (S.Sk (k - 1)) -/
def simplex_boundary_map  (s : S _[k]) : ∂Δ[k] ⟶ (S.Sk (k - 1)) :=
  (skeleton_hom_equiv (boundary_dim k)).symm ((boundaryInclusion k) ≫ (simplex_map s) ≫ (S.skeleton k).ι)

lemma _0014 (s : Δ[n] ⟶ S) : ∃ (α : ([n] : SimplexCategory) ⟶ [m]) (τ : Δ[m] ⟶ S),
    Function.Surjective α.toOrderHom ∧ Nondegenerate (yonedaEquiv _ _ τ) ∧ s = standardSimplex.map α ≫ τ := sorry

/-
/-- every nondegenerate k simplex determines a map Δ[k] ⟶ (S.Sk k) -/
def nd_simplex_map (s : S _[k]) (hs : Nondegenerate s) :
    Δ[k] ⟶ (S.Sk k) := sorry
-/

/-
lemma _0018 : S.skeleton 0 = SimplicialSubset.empty S := by
  ext
  refine ⟨fun ⟨l, ⟨hl, _⟩⟩ ↦ by aesop, fun h ↦ by exfalso; exact Set.not_mem_empty _ h⟩
-/

-- functor sending simplicial subsets to simplicial sets
@[simps]
def sset_functor : SimplicialSubset S ⥤ SSet where
  obj := Subpresheaf.toPresheaf
  map f := Subpresheaf.homOfLe f.le

-- functor sending k to k-th skeleton (as subset)
@[simps]
def skeleton_functor : ℕ ⥤ SimplicialSubset S where
  obj k := S.skeleton k
  map f := ⟨⟨fun n ↦ _0500 S n.unop.len f.le⟩⟩

-- functor sending k to k-th skeleton as a simplicial set
@[simps!]
def skeleton_functor' : ℕ ⥤ SSet := skeleton_functor S ⋙ sset_functor S

-- the cone with pt S given by the skeletons of S
def skeleton_cocone : Limits.Cocone (skeleton_functor' S) where
  pt := S
  ι := { app := fun k ↦ (S.skeleton k).ι }

-- functor sending k to union of B with k-th skeleton
def skeleton_union_functor (B : SimplicialSubset S) : ℕ ⥤ SimplicialSubset S where
  obj k := (S.skeleton k) ⊔ B
  map f := by
    refine ⟨⟨fun k Sk h ↦ ?_⟩⟩
    cases h with
    | inl h => left; exact _0500 S k.unop.len f.le h
    | inr h => right; exact h

-- functor sending k to union of B with k-th skeleton as a simplicial set
def skeleton_union_functor' (B : SimplicialSubset S) : ℕ ⥤ SSet :=
  skeleton_union_functor S B ⋙ sset_functor S

-- the cone with point S given by the unions of B with all the skeletons
def skeleton_union_cocone (B : SimplicialSubset S) : Limits.Cocone (skeleton_union_functor' S B) where
  pt := S
  ι := { app := fun k ↦ (S.skeleton k ⊔ B).ι }

-- Subpresheaf.ι (empty S)
-- lemma test : (sset_cocone S).ι.app ⊥ = Subpresheaf.ι (empty S)
-- Subpresheaf.ext

@[ext]
lemma dumbext (n : SimplexCategoryᵒᵖ) (x y : ((skeleton_functor S).obj (n.unop.len + 1)).obj n) : x.1 = y.1 → x = y := by
  dsimp [skeleton_functor, sset_functor] at x y
  aesop

@[simps!]
def aux1 (n : SimplexCategoryᵒᵖ) (s : S.obj n) :
    (S.skeleton (n.unop.len + 1)).obj n := .mk _ (_0016 S (Nat.le_succ _) (Set.mem_univ s))

-- the skeleton cocone is a colimit
def skeleton_cocone_iscolimit : Limits.IsColimit (skeleton_cocone S) where
  desc c := {
    app := fun n s ↦ (c.ι.app (n.unop.len + 1)).app n (aux1 S n s)
    naturality := by
      intro k m f
      ext (x : S.obj k)
      simp [skeleton_cocone]
      sorry }
  fac := by
    intro c j
    ext k x
    dsimp
    change ((c.ι.app ((Opposite.unop k).len + 1)).app k (aux1 S k ((((skeleton_cocone S).ι.app j).app k x) ))) = _
    simp [skeleton_cocone]
    sorry
  uniq := sorry

-- the skeleton union cocone is a colimit
def skeleton_union_cocone_iscolimit (B : SimplicialSubset S) : Limits.IsColimit (skeleton_union_cocone S B) where
  desc c := {
    app := fun n s ↦ (c.ι.app (n.unop.len + 1)).app n ⟨s, by left; exact ⟨n.unop.len, Nat.le_succ _, s, 𝟙 _, rfl⟩⟩
    naturality := by
      intro k m f
      ext (x : S.obj k)
      dsimp [skeleton_union_cocone]
      sorry }
  fac := sorry
  uniq := sorry

/-
class IsStableUnderTransfiniteCompositionOfShape (β : Type*) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β] : Prop where
  condition (F : β ⥤ C) [F.WellOrderContinuous] (hF : ∀ (a : β) (_ : a < wellOrderSucc a), W (F.map (homOfLE (self_le_wellOrderSucc a))))
    (c : Cocone F) (hc : IsColimit c) : W (c.ι.app ⊥)

def temp {S : SSet} {n : SimplexCategoryᵒᵖ} (s : (cocone S).pt.obj n) :
    ((sset_functor S).obj (Opposite.unop n).len).obj n := ⟨s, ⟨_, le_rfl, s, 𝟙 _, rfl⟩⟩
-/

-- if X ⊆ S, then we should have S = ∪ X(k), where X(k) = X ∪ Skₖ(S)
-- so if i : A → B is a monomorphism, then A ≅ im(i) ⊆ B, so B = ∪ im(i)(k)

end SSet
