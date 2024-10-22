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

inductive IsDegenerate : {n : ℕ} → (s : S _[n]) → Prop
  | mk (n : ℕ) (x : S _[n]) (i : Fin (n + 1)) : IsDegenerate (S.σ i x)

abbrev Nondegenerate {S : SSet} (s : S _[n]) : Prop := ¬ IsDegenerate s

-- `0013`, image of degenerate simplex is degenerate
lemma image_degen_of_degen (f : S ⟶ T) (s : S _[n]) (h : IsDegenerate s) :
    IsDegenerate (f.app (.op [n]) s) := by
  induction h with
  | mk m s i =>
  have := congr_fun (f.naturality (SimplexCategory.σ i).op) s
  dsimp [SimplicialObject.σ] at this ⊢
  rw [this]
  apply IsDegenerate.mk

-- `0013`
lemma degen_of_image_degen_mono (f : S ⟶ T) [hf : Mono f]
    (s : S _[n]) (h : IsDegenerate (f.app (.op [n]) s)) :
    IsDegenerate s := sorry

lemma _04ZN (f : S ⟶ T) :
    (∀ (n : ℕ) (t : T _[n]) (ht : Nondegenerate t), t ∈ Set.range (f.app _)) → Epi f := sorry

variable (S : SSet)

class dim_le (k : ℕ) : Prop where
  condition : ∀ (n : ℕ) (s : S _[n]), k < n → IsDegenerate s

/-
def hom_of_le (m k : ℕ) (h : m ≤ k) :
    ([m] : SimplexCategory) ⟶ [k] :=
  Hom.mk ⟨fun x ↦ Fin.castLE (Nat.add_le_add_right h 1) x, fun _ _ h ↦ h⟩
-/

-- want to say the skeleton is empty for k < 0
-- we shift everything by 1 so that skel is empty for k = 0
def HasFactorization (k n : ℕ) (s : S _[n]) : Prop :=
  ∃ (m : ℕ) (_ : m < k) (τ : S _[m]) (f : Δ[n] ⟶ Δ[m]),
    (S.yonedaEquiv [n]).symm s = f ≫ (S.yonedaEquiv [m]).symm τ

-- skₖ₋₁(S)ₙ
def skeleton_subset (k n : ℕ) : Set (S _[n]) :=
  { s : S _[n] | HasFactorization S k n s }

-- skₖ₋₁(S)ₙ = S _[n] for n < k (since n ≤ k - 1)
lemma _0016 (h : n < k) : ⊤ ≤ skeleton_subset S k n :=
  fun s _ ↦ ⟨n, h, s, 𝟙 _, by aesop⟩

-- skₗ₋₁(S)ₙ ⊆ skₖ₋₁(S)ₙ for l ≤ k
lemma _0500 (n : ℕ) (h : l ≤ k) : skeleton_subset S l n ≤ skeleton_subset S k n :=
  fun _ ⟨m, hm, τ, f, hf⟩ ↦ ⟨m, le_trans hm h, τ, f, hf⟩

-- the skeleton as a simplicial subset
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

-- the 0-skeleton is empty
lemma _0018 : S.skeleton 0 = SimplicialSubset.empty S := by
  ext
  refine ⟨fun ⟨l, ⟨hl, _⟩⟩ ↦ by aesop, fun h ↦ by exfalso; exact Set.not_mem_empty _ h⟩

-- the skeleton as a simplicial set
def Sk (k : ℕ) : SSet := (S.skeleton k).toPresheaf

def Sk.ι (k : ℕ) : S.Sk k ⟶ S := (S.skeleton k).ι

def SkSucc : S.Sk k ⟶ S.Sk (k + 1) :=
  Subpresheaf.homOfLe <| fun n ↦ S._0500 n.unop.len (Nat.le_succ k)

lemma lt_then_not_surj (n m : ℕ) (τ : Fin n →o Fin m) (h : m < n) :
    ¬ Function.Injective τ := by
  sorry

lemma lt_then_factor_through_σ (n m : ℕ) (h : m < n) (τ : ([n + 1] : SimplexCategory) ⟶ [m]) :
    ∃ i α, τ = (SimplexCategory.σ i) ≫ α := by
  sorry

/-- an n-simplex is degenerate iff it is in skₖ₋₁(S)ₙ for some k ≤ n. -/
lemma _0011 (s : S _[n]) : IsDegenerate s ↔ (∃ (k : ℕ) (_ : k ≤ n), s ∈ (S.skeleton k).obj (.op [n])) := by
  refine ⟨?_, ?_⟩
  · intro h
    induction h with
    | mk m x i =>
    refine ⟨m + 1, le_rfl, m, Nat.lt.base m, x, standardSimplex.map (SimplexCategory.σ i), (Equiv.symm_apply_eq (S.yonedaEquiv [m + 1])).mpr rfl⟩
  · intro ⟨k, hk, m, hm, σ', (τ : Δ[n] ⟶ Δ[m]), (hf : (S.yonedaEquiv [n]).symm s = τ ≫ (S.yonedaEquiv [m]).symm σ')⟩
    -- m < n, so τ cannot be injective on vertices, so τ factors through some σ map.

    /-
    have equ' : ([n - 1 + 1] : SimplexCategory) = ([n] : SimplexCategory) := sorry
    have equ : (([n] : SimplexCategory) ⟶ [m]) = (([n - 1 + 1] : SimplexCategory) ⟶ [m]) := congrFun (congrArg Quiver.Hom (id (Eq.symm equ'))) [m]
    --have equ'' : Δ[n] = Δ[n - 1 + 1] := congrArg standardSimplex.obj (id (Eq.symm equ'))
    let τ' := standardSimplex.objEquiv _ _ (yonedaEquiv _ _ τ)
    rw [equ] at τ'
    obtain ⟨i, α, hiα⟩ := lt_then_factor_through_σ _ _ sorry τ'
    --rw [equ''] at τ
    rw [← equ] at τ'
    have : (yonedaEquiv _ _).symm ((standardSimplex.objEquiv _ _).symm τ') = τ := sorry
    rw [← this] at hf
    apply_fun (fun f ↦ (S.yonedaEquiv [n]) f) at hf
    simp at hf
    rw [hf]
    -/

    sorry

/-- a nondegenerate n-simplex is in skₖ₋₁(S)ₙ iff n < k (i.e., iff skₖ₋₁(S)ₙ = Sₙ) -/
lemma _0017 (s : S _[n]) (hs : Nondegenerate s) : s ∈ (S.skeleton k).obj (.op [n]) ↔ n < k := by
  refine ⟨?_, fun h ↦ _0016 S h (Set.mem_univ s)⟩
  intro h
  by_contra h'
  apply hs
  rw [not_lt] at h'
  rw [_0011]
  use k

-- the (k - 1)-skeleton has dimension ≤ (k - 1)
instance (k : ℕ) : (S.Sk k).dim_le (k - 1) where
  condition := by
    intro n ⟨s, hs⟩ hk
    by_contra h
    have : Nondegenerate s := by
      --obtain ⟨m, t, i, hi⟩ := h'
      sorry
    rw [_0017 S s this] at hs
    have : k ≤ n := Nat.le_of_pred_lt hk
    rw [← not_lt] at this
    exact this hs

-- if S has dim ≤ k then S = skₖ(S)
def skeletonEq (k : ℕ) (hS : S.dim_le k) : SimplicialSubset.top S = (S.skeleton (k + 1)) := by
  ext n (s : S _[n.unop.len])
  refine ⟨fun _ ↦ ?_, fun _ ↦ _root_.trivial⟩
  by_cases (IsDegenerate s)
  · rename_i h
    have := hS.condition
    sorry
  · rename_i h
    apply (_0017 S s h).2
    have := hS.condition n.unop.len s
    rw [← not_imp_not] at this
    by_contra h'
    rw [not_lt] at h'
    exact this h h'

/--  ∂Δ[n] ≅ skₙ₋₁(Δ[n]) -/
def boundaryIsoSkeleton (n : ℕ) : ∂Δ[n] ≅ (Δ[n].Sk n) where
  hom := sorry
  inv := sorry

instance boundary_dim (k : ℕ) : ∂Δ[k].dim_le (k - 1) := sorry

/-
inductive ndFac : {n : ℕ} → (s : Δ[n] ⟶ S) → Prop
  | mk (m : ℕ) (α : ([n] : SimplexCategory) ⟶ [m]) (τ : Δ[m] ⟶ S) : ndFac (standardSimplex.map α ≫ τ)
-/

def fac_nat_subset {S : SSet} (s : Δ[n] ⟶ S) : Set ℕ :=
  { m | ∃ (α : ([n] : SimplexCategory) ⟶ [m]) (τ : Δ[m] ⟶ S), s = standardSimplex.map α ≫ τ}

instance (s : Δ[n] ⟶ S) : Nonempty (fac_nat_subset s) := ⟨⟨n, 𝟙 _, s, by aesop⟩⟩

noncomputable
instance : DecidablePred fun x ↦ x ∈ (fac_nat_subset s) := Classical.decPred fun x ↦ x ∈ fac_nat_subset s

--#check Nat.Subtype.orderBot (fac_nat_subset s)

--#check (⊥ : (fac_nat_subset s))

--#check  (⊥ : fac_nat_subset s).property.2

-- `0014`
noncomputable
def min_nat {S : SSet} (s : Δ[n] ⟶ S) : ℕ := (⊥ : (fac_nat_subset s)).val

noncomputable
def facα {S : SSet} (s : Δ[n] ⟶ S) : ([n] : SimplexCategory) ⟶ [min_nat s] := Exists.choose (⊥ : (fac_nat_subset s)).property

noncomputable
def facτ {S : SSet} (s : Δ[n] ⟶ S) : Δ[min_nat s] ⟶ S := Exists.choose (Exists.choose_spec (⊥ : fac_nat_subset s).property)

lemma fac_eq {S : SSet} (s : Δ[n] ⟶ S) : s = standardSimplex.map (facα s) ≫ facτ s := Exists.choose_spec (Exists.choose_spec (⊥ : fac_nat_subset s).property)

-- if α were not surjective, then we could find a smaller m by taking the image of α
lemma α_surj {S : SSet} (s : Δ[n] ⟶ S) : Function.Surjective (facα s).toOrderHom := sorry

-- τ is nondegenerate otherwise we could find a smaller m
lemma τ_nondegen {S : SSet} (s : Δ[n] ⟶ S) : Nondegenerate (yonedaEquiv _ _ (facτ s)) := sorry

-- `001A`
noncomputable
def skeleton_hom_equiv {S T : SSet} (h : T.dim_le k) : (T ⟶ S.Sk (k + 1)) ≃ (T ⟶ S) where
  toFun f := f ≫ (S.skeleton (k + 1)).ι
  invFun f := {
    app := fun n (t : T _[n.unop.len]) ↦ by
      by_cases (Nondegenerate t)
      · rename_i h'
        have := h.condition n.unop.len t
        rw [← not_imp_not] at this
        exact ⟨f.app n t, S._0016 (Nat.gt_of_not_le (this h')) (Set.mem_univ _)⟩
      · rename_i h'
        simp only [not_not] at h'
        let t' : Δ[n.unop.len] ⟶ T := (yonedaEquiv _ _).symm t
        have := h.condition (min_nat t') (yonedaEquiv _ _ (facτ t'))
        rw [← not_imp_not] at this
        --have := this (τ_nondegen t')
        --rw [not_lt] at this
        have : min_nat t' < k + 1 := Nat.gt_of_not_le (this (τ_nondegen t'))
        have := (S._0016 this (Set.mem_univ (f.app _ (yonedaEquiv _ _ (facτ t')))))
        --have := _0017 T (yonedaEquiv _ _ t') (τ_nondegen t')
        sorry
      /-
      -/
  }
  left_inv := sorry
  right_inv := sorry

-- can also be shown using skeleton_hom_equiv
/-- every k simplex determines a map Δ[k] ⟶ skₖ(S) -/
def simplex_map {S : SSet} (s : S _[k]) : Δ[k] ⟶ (S.Sk (k + 1)) :=
  (yonedaEquiv _ _).symm (⟨s, _0016 S le_rfl (Set.mem_univ s)⟩)

/-- simplex_map induces ∂Δ[k] ⟶ skₖ₋₁(S) (assuming 1 ≤ k) -/
noncomputable
def simplex_boundary_map {S : SSet} (h1 : 1 ≤ k) (s : S _[k]) : ∂Δ[k] ⟶ (S.Sk k) := by
  have := (skeleton_hom_equiv (boundary_dim k)).symm ((boundaryInclusion k) ≫ (simplex_map s) ≫ (S.skeleton (k + 1)).ι)
  convert this
  exact (Nat.sub_eq_iff_eq_add h1).mp rfl

variable (k : ℕ) (hk : 1 ≤ k)

def nd : Set (S _[k]) := { s | Nondegenerate s }

def nd_map1 : ((S.nd k) : Type*) → SSet := fun _ ↦ Δ[k]

def nd_map2 : ((S.nd k) : Type*) → SSet := fun _ ↦ ∂Δ[k]

noncomputable
-- coproduct of Δ[k] indexed by nondegenerate k-simplices
def smplx_coprod : SSet := ∐ (S.nd_map1 k)

noncomputable
-- coproduct of ∂Δ[k] indexed by nondegenerate k-simplices
def bndry_coprod : SSet := ∐ (S.nd_map2 k)

noncomputable
-- map between the above coproducts induced by the boundary inclusion
def coprod_map : (S.bndry_coprod k) ⟶ (S.smplx_coprod k) :=
  Limits.Sigma.desc <| fun b ↦ boundaryInclusion k ≫ (Limits.Sigma.ι (S.nd_map1 k) b)

noncomputable
-- map from simplex coproduct to the k-skeleton induced by each nondegenerate simplex
def coprod_to_smplx : (S.smplx_coprod k) ⟶ (S.Sk (k + 1)) :=
  Limits.Sigma.desc <| fun b ↦ simplex_map b

noncomputable
-- map from boundary coproduct to the (k-1)-skeleton induced by each nondegenerate simplex
def coprod_to_bndry : (S.bndry_coprod k) ⟶ (S.Sk k) :=
  Limits.Sigma.desc <| fun b ↦ simplex_boundary_map hk b

lemma coprod_square_commutes :
    (S.coprod_to_bndry k hk) ≫ S.SkSucc = (S.coprod_map k) ≫ (S.coprod_to_smplx k) := by
  apply Limits.Sigma.hom_ext
  intro b
  ext n x
  simp [coprod_map, coprod_to_smplx, coprod_to_bndry]
  sorry

noncomputable
-- the pushout cocone of the above square
def skPushoutCocone : Limits.PushoutCocone (S.coprod_to_bndry k hk) (S.coprod_map k) :=
  .mk (S.SkSucc) (S.coprod_to_smplx k) (coprod_square_commutes S k hk)

noncomputable
-- the pushout cocone on the level of objects
def skPushoutCoconeObj (n : SimplexCategoryᵒᵖ) : Limits.PushoutCocone ((S.coprod_to_bndry k hk).app n) ((S.coprod_map k).app n) :=
  .mk (S.SkSucc.app n) ((S.coprod_to_smplx k).app n) (congr_app (coprod_square_commutes S k hk) n)

def skIsoPushout : (S.Sk (k + 1)).obj n ≅ (Limits.Types.Pushout ((S.coprod_to_bndry k hk).app n) ((S.coprod_map k).app n)) := sorry

#check Limits.Types.Pushout.isColimitCocone

def skPushoutObj : Limits.IsColimit (skPushoutCoconeObj S k hk n) where
  desc := sorry

def skPushout : Limits.IsColimit (skPushoutCocone S k hk) := by
  refine ⟨?_, sorry, sorry⟩
  intro s

  sorry

-- should be generalized
lemma empty_union_image (i : A ⟶ B) : skeleton B 0 ⊔ imagePresheaf i = imagePresheaf i := by
  rw [_0018]
  dsimp [SimplicialSubset.empty]
  ext n Bn
  change Bn ∈ (∅ ⊔ (imagePresheaf i).obj n) ↔ _
  simp only [imagePresheaf_obj, Set.le_eq_subset, Set.empty_subset, sup_of_le_right,
    Set.mem_range]

-- functor sending simplicial subsets to simplicial sets
@[simps]
def sset_functor : SimplicialSubset S ⥤ SSet where
  obj := Subpresheaf.toPresheaf
  map f := Subpresheaf.homOfLe f.le

-- functor sending k to (k - 1)-th skeleton (as subset)
@[simps]
def skeleton_functor : ℕ ⥤ SimplicialSubset S where
  obj k := S.skeleton k
  map f := ⟨⟨fun n ↦ _0500 S n.unop.len f.le⟩⟩

-- functor sending k to (k - 1)-th skeleton as a simplicial set
@[simps!]
def skeleton_functor' : ℕ ⥤ SSet := skeleton_functor S ⋙ sset_functor S

-- the cone with pt S given by the skeletons of S
def skeleton_cocone : Limits.Cocone (skeleton_functor' S) where
  pt := S
  ι := { app := fun k ↦ (S.skeleton k).ι }

-- functor sending k to union of B with (k - 1)-th skeleton
def skeleton_union_functor (B : SimplicialSubset S) : ℕ ⥤ SimplicialSubset S where
  obj k := (S.skeleton k) ⊔ B
  map f := by
    refine ⟨⟨fun k Sk h ↦ ?_⟩⟩
    cases h with
    | inl h => left; exact _0500 S k.unop.len f.le h
    | inr h => right; exact h

-- functor sending k to union of B with (k - 1)-th skeleton as a simplicial set
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
def skltonaux1 (n : SimplexCategoryᵒᵖ) (s : S.obj n) :
    (S.skeleton (n.unop.len + 1)).obj n := .mk _ (_0016 S (Nat.lt.base _) (Set.mem_univ s))

-- the skeleton cocone is a colimit
def skeleton_cocone_iscolimit : Limits.IsColimit (skeleton_cocone S) where
  desc c := {
    app := fun n s ↦ (c.ι.app (n.unop.len + 1)).app n (skltonaux1 S n s)
    naturality := by
      intro k m f
      ext (x : S.obj k)
      simp [skeleton_cocone]
      sorry }
  fac := by
    intro c j
    ext k x
    dsimp
    change ((c.ι.app ((Opposite.unop k).len + 1)).app k (skltonaux1 S k ((((skeleton_cocone S).ι.app j).app k x) ))) = _
    simp [skeleton_cocone]
    sorry
  uniq := sorry

-- the skeleton union cocone is a colimit
def skeleton_union_cocone_iscolimit (B : SimplicialSubset S) : Limits.IsColimit (skeleton_union_cocone S B) where
  desc c := {
    app := fun n s ↦ (c.ι.app (n.unop.len + 1)).app n ⟨s, by left; exact ⟨n.unop.len, Nat.lt.base _, s, 𝟙 _, rfl⟩⟩
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
