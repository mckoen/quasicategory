import Quasicategory.Basic
import Mathlib.CategoryTheory.Adhesive
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Quasicategory.InternalHom
import Quasicategory.Terminal
import Quasicategory.SimplicialSet

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory

-- boundary inclusions are monomorphisms
instance boundaryInclusion_mono (n : ℕ) : Mono (boundaryInclusion n) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((boundaryInclusion n).app k) := fun _ ↦ by
    rw [mono_iff_injective]
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  apply NatTrans.mono_of_mono_app

-- B ⊗ ∂Δ[n] ⟶ B ⊗ Δ[n] is a monomorphism
open MonoidalCategory in
instance boundaryInclusion_whisker_mono (B : SSet) (n : ℕ) : Mono (B ◁ (boundaryInclusion n)) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((B ◁ boundaryInclusion n).app k) := by
    intro k
    rw [mono_iff_injective]
    rintro ⟨b, x⟩ ⟨b', x'⟩ h
    apply Prod.ext_iff.1 at h
    apply Prod.ext
    · exact h.1
    · simp only [boundaryInclusion, whiskerLeft_app_apply] at h ⊢
      apply (Set.injective_codRestrict Subtype.property).mp
      exact fun ⦃a₁ a₂⦄ a ↦ a
      exact h.2
  apply NatTrans.mono_of_mono_app

-- inner horn inclusions are monomorphisms
instance inner_horn_mono ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    monomorphisms SSet (hornInclusion (n+2) i) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((hornInclusion (n + 2) i).app k) := fun _ ↦ by
    rw [mono_iff_injective]
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  apply NatTrans.mono_of_mono_app

instance monomorphisms.StableUnderCobaseChange : StableUnderCobaseChange (monomorphisms SSet) := by
  intro A B A' B' f s f' t P hf
  letI _ : Mono f := hf
  letI _ : Adhesive SSet := adhesive_functor
  exact Adhesive.mono_of_isPushout_of_mono_right P

/-
def transfinite_monos_aux (α : Ordinal) (F : {β | β ≤ α} ⥤ SSet) : Ordinal → Prop := fun γ ↦
  (hγ : γ ≤ α) → monomorphisms SSet (F.map (zero_to γ hγ))

instance transfinite_monos
    (X Y : SSet) (f : X ⟶ Y)
    (α : Ordinal)
    (F : {β | β ≤ α} ⥤ SSet) (hF : Limits.PreservesColimits F)
    (hS : ∀ (β : Ordinal) (hβ : β < α), monomorphisms SSet (F.map (to_succ hβ))) :
    ∀ {γ} (hγ : γ ≤ α), monomorphisms SSet (F.map (zero_to γ hγ)) := by
  intro γ hγ
  refine @Ordinal.limitRecOn (transfinite_monos_aux α F) γ ?_ ?_ ?_ hγ
  all_goals dsimp [transfinite_monos_aux]
  · intro; simp [zero_to]; exact instMonoId _
  · intro o IH (succ_le : o + 1 ≤ α)
    have o_lt : o < α := Order.succ_le_iff.mp succ_le
    have : (F.map (zero_to (Order.succ o) succ_le)) = (F.map (zero_to o (le_of_lt o_lt))) ≫
        (F.map (to_succ o_lt)) := by
      suffices (zero_to (Order.succ o) succ_le) = (zero_to o (le_of_lt o_lt)) ≫ (to_succ o_lt) by
        aesop
      simp only [Set.coe_setOf, Set.mem_setOf_eq, zero_to, to_succ, homOfLE_comp]
    rw [this]
    have a := IH (le_of_lt o_lt)
    have b := hS o o_lt
    exact @CategoryTheory.mono_comp SSet _ _ _ _
      (F.map (zero_to o (le_of_lt o_lt))) a (F.map (to_succ o_lt)) b
  · simp only [monomorphisms.iff]
    intro o ho IH o_le
    sorry -- because monomorphisms are closed under filtered colimits?
-- o is colimit of o' < o, and ∀ o' < o we have f_o'_0 : F(0) ⟶ F(o') is a Mono.
-- {o' | o' < o} is a filtered category (as a directed set), so o is a filtered colimit
-- F preserves colimits, so F(o) is a filtered colimit of F(o') for o' < o
-- since each F(0) ⟶ F(o') is a Mono, also F(0) ⟶ F(o) is a Mono

  intro X Y f hf
  induction hf with
  | mk α F hF hS => exact transfinite_monos X Y f α F hF hS (le_refl α)
-/

instance monomorphisms.isStableUnderTransfiniteCompositionOfShape (β : Type u_1)
    (h1 : LinearOrder β) (h2 : IsWellOrder β fun x y ↦ x < y) (h3 : OrderBot β) :
    (monomorphisms SSet).IsStableUnderTransfiniteCompositionOfShape β where
  condition := by
    intro F hf h c hc
    sorry

instance monomorphisms.IsStableUnderTransfiniteComposition :
    IsStableUnderTransfiniteComposition (monomorphisms SSet) where
  id_mem _ := instMonoId _
  comp_mem f g hf hg := @mono_comp _ _ _ _ _ f hf g hg
  isStableUnderTransfiniteCompositionOfShape :=
    monomorphisms.isStableUnderTransfiniteCompositionOfShape

-- `0077` (a) monomorphisms are weakly saturated
instance monomorphisms.WeaklySaturated : WeaklySaturated (monomorphisms SSet) :=
  ⟨ monomorphisms.StableUnderCobaseChange,
    monomorphisms.StableUnderRetracts,
    monomorphisms.IsStableUnderTransfiniteComposition⟩

-- should be moved to other file and made more general
open SimplicialSubset GrothendieckTopology in
lemma empty_union_image (i : A ⟶ B) : skeleton B 0 ⊔ imagePresheaf i = imagePresheaf i := by
  rw [_0018 _ zero_lt_one]
  dsimp [SimplicialSubset.empty]
  ext n Bn
  change Bn ∈ (∅ ⊔ (imagePresheaf i).obj n) ↔ _
  simp only [imagePresheaf_obj, Set.le_eq_subset, Set.empty_subset, sup_of_le_right,
    Set.mem_range]

-- need pushout construction for this
open SimplicialSubset GrothendieckTopology in
lemma succ_mem_thing (S : MorphismProperty SSet) (hS : S.WeaklySaturated) (h : ∀ (n : ℕ), S (boundaryInclusion n))
    {A B : SSet} (i : A ⟶ B) [hi : Mono i] :
    ∀ a < wellOrderSucc a, S ((sset_union_functor B (imagePresheaf i)).map (homOfLE (self_le_wellOrderSucc a))) := by
  intro a ha
  dsimp [sset_union_functor, subset_union_functor, sset_functor]
  sorry

def zerofunctor (X : SSet) : Fin 1 ⥤ SSet where
  obj _ := X
  map _ := 𝟙 X

instance (X : SSet) : X.zerofunctor.WellOrderContinuous := sorry

example  (S : MorphismProperty SSet) (hS : S.WeaklySaturated) (X : SSet) : sorry := by
  have := (hS.IsStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape (Fin 1)).condition (zerofunctor X)
  sorry

open SimplicialSubset GrothendieckTopology in
-- `0077` (b) monomorphisms are generated by boundary inclusions
lemma contains_mono_iff_contains_boundaryInclusion
    (S : MorphismProperty SSet.{0}) (hS : WeaklySaturated.{0, 1, 0} S) :
    (∀ (n : ℕ), S (boundaryInclusion n))
      ↔ ∀ {A B : SSet} (i : A ⟶ B) [Mono i], S i := by
  refine ⟨?_, fun h n ↦ h (boundaryInclusion n)⟩
  intro h A B i hi
  have := (hS.IsStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape ℕ).condition
    (sset_union_functor B (imagePresheaf i)) (succ_mem_thing S hS h i) (skeleton_union_cocone B (imagePresheaf i)) (skeleton_union_cocone_iscolimit B (imagePresheaf i))
  dsimp [SimplicialSubset.skeleton_union_cocone] at this
  have H : S (Subpresheaf.ι (imagePresheaf i)) := by
    convert this
    swap
    rw [empty_union_image i]
    dsimp [sset_union_functor, sset_functor, subset_union_functor]
    congr
    rw [empty_union_image i]
  change S ((mono_iso i).hom ≫ (imagePresheaf i).ι)
  -- need that weakly saturated contain all isomorphisms. then composition with isomorphism gives i
  sorry

/- `006Y` trivial Kan fibration iff rlp wrt all monomorphisms -/
lemma trivialKanFibration_eq_rlp_monomorphisms :
    trivialKanFibration.{0} = (monomorphisms SSet).rlp:= by
  ext X Y p
  refine ⟨?_, ?_⟩
  · intro h
    rw [class_rlp_iff_llp_morphism]
    apply (contains_mono_iff_contains_boundaryInclusion
      (MorphismClass p).llp (llp_weakly_saturated _)).1
    intro n _ _ p hp
    induction hp
    exact h (.mk n)
  · intro h _ _ p hp
    induction hp
    exact h (boundaryInclusion_mono _)

-- `006Z`(a), trivial Kan fibrations admit sections
noncomputable
def trivialKanFibration_section {X Y : SSet} (p : X ⟶ Y)
    (hp : trivialKanFibration p) : Y ⟶ X := by
  rw [trivialKanFibration_eq_rlp_monomorphisms] at hp
  have : (emptyIsInitial.to X) ≫ p = (emptyIsInitial.to Y) ≫ (𝟙 Y) :=
    Limits.IsInitial.hom_ext emptyIsInitial _ _
  exact ((hp (initial_mono Y emptyIsInitial)).sq_hasLift (CommSq.mk (this))).exists_lift.some.l

-- the above map is a section
lemma trivialKanFibration_section_comp {X Y : SSet} (p : X ⟶ Y) (hp : trivialKanFibration p) :
    trivialKanFibration_section p hp ≫ p = 𝟙 Y := by
  rw [trivialKanFibration_eq_rlp_monomorphisms] at hp
  have : (emptyIsInitial.to X) ≫ p = (emptyIsInitial.to Y) ≫ (𝟙 Y) :=
    Limits.IsInitial.hom_ext emptyIsInitial _ _
  exact ((hp (initial_mono Y emptyIsInitial)).sq_hasLift (CommSq.mk (this))).exists_lift.some.fac_right

-- `050J` (1)
instance kanComplex_of_trivialKanFibration {X Y : SSet.{0}}
    (p : X ⟶ Y) (hp : trivialKanFibration p) :
    KanComplex X → KanComplex Y := by
  intro h
  constructor
  intro n i σ₀
  rw [trivialKanFibration_eq_rlp_monomorphisms] at hp
  dsimp [rlp] at hp
  have : (emptyIsInitial.to X) ≫ p = (emptyIsInitial.to Λ[n, i]) ≫ σ₀ :=
    Limits.IsInitial.hom_ext emptyIsInitial _ _
  have τ₀ := ((hp (initial_mono Λ[n, i] emptyIsInitial)).sq_hasLift (CommSq.mk (this))).exists_lift.some
  obtain ⟨τ, hτ⟩ := h.hornFilling τ₀.l
  use τ ≫ p
  rw [← Category.assoc, ← hτ, τ₀.fac_right]

-- `050J` (3)
instance quasicategory_of_trivialKanFibration {X Y : SSet.{0}}
    (p : X ⟶ Y) (hp : trivialKanFibration p) :
    Quasicategory X → Quasicategory Y := by
  intro h
  constructor
  intro n i σ₀ h0 hn
  rw [trivialKanFibration_eq_rlp_monomorphisms] at hp
  dsimp [rlp] at hp
  have : (emptyIsInitial.to X) ≫ p = (emptyIsInitial.to Λ[n + 2, i]) ≫ σ₀ :=
    Limits.IsInitial.hom_ext emptyIsInitial _ _
  have τ₀ := ((hp (initial_mono Λ[n + 2, i] emptyIsInitial)).sq_hasLift (CommSq.mk (this))).exists_lift.some
  obtain ⟨τ, hτ⟩ := h.hornFilling h0 hn τ₀.l
  use τ ≫ p
  rw [← Category.assoc, ← hτ, τ₀.fac_right]

-- innerAnodyne is generated by inner horn inclusions, which are monos and monos are saturated,
-- thus innerAnodynes are monos
lemma innerAnodyne_mono {X Y : SSet.{0}} (p : X ⟶ Y) (hp : innerAnodyne p) :
    monomorphisms SSet p :=
  (contains_innerAnodyne_iff_contains_inner_horn.{0,1}
    (monomorphisms SSet) monomorphisms.WeaklySaturated).1 inner_horn_mono p hp

-- the pushout in `007F` (a)
def monoPushout {A B : SSet} (i : A ⟶ B) [Mono i] :=
  IsPushout.of_hasPushout (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ i)

-- cocone with pt. `Δ[2] ⊗ B` given by `i`
noncomputable
def B_cocone {A B : SSet} (i : A ⟶ B) [Mono i] :
    Limits.PushoutCocone (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ i) :=
  Limits.PushoutCocone.mk (Δ[2] ◁ i) (hornInclusion 2 1 ▷ B) rfl

-- induced morphism from the pushout to `Δ[2] ⊗ B` given by `B_cocone`
noncomputable
def to_B {A B : SSet} (i : A ⟶ B) [Mono i] : (monoPushout i).cocone.pt ⟶ Δ[2] ⊗ B :=
  (monoPushout i).isColimit.desc (B_cocone i)

-- `007F` (a)
lemma monoPushout_innerAnodyne {A B : SSet} (i : A ⟶ B) [Mono i] :
    innerAnodyne (to_B i) := by sorry

-- `007F` (b)
-- inner Anodyne morphisms are generated by the pushout maps given in `to_Δ`
lemma contains_innerAnodyne_iff_contains_pushout_maps
    (S : MorphismProperty SSet) (hS : WeaklySaturated S) :
    (∀ m, S (to_B (boundaryInclusion m))) ↔ (∀ {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p), S p) := by
  refine ⟨sorry, fun h m ↦ h _ (monoPushout_innerAnodyne (boundaryInclusion m))⟩
