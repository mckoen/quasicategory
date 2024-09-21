import Quasicategory.Basic
import Mathlib.CategoryTheory.Adhesive
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Quasicategory.InternalHom
import Quasicategory.Terminal
import Quasicategory.SimplicialSet
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

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

section mono_proof

variable {β : Type*} [h1 : LinearOrder β] [h2 : IsWellOrder β (· < ·)] [h3 : OrderBot β]

variable {F : β ⥤ SSet} [h : F.WellOrderContinuous]
  (hF : ∀ (a : β) (_ : a < wellOrderSucc a), (monomorphisms SSet) (F.toPrefunctor.map (homOfLE (self_le_wellOrderSucc a))))
  {c : Limits.Cocone F} (hc : Limits.IsColimit c)

variable (γ : β)

instance has_bot (not_bot : γ ≠ ⊥) : OrderBot {b | b < γ} where
  bot := ⟨⊥, Ne.bot_lt' (id (Ne.symm not_bot))⟩ -- only if γ is not ⊥
  bot_le _ := OrderBot.bot_le _

instance has_bot' [IsWellOrderLimitElement γ] : OrderBot {b | b < γ} :=
  has_bot γ (IsWellOrderLimitElement.neq_bot γ)

example [IsWellOrderLimitElement γ] :
    (F.map (homOfLE bot_le)) = ((F.coconeOfFunctorToOver (PrincipalSeg.ofElement (· < ·) γ).functorToOver).ι.app ⊥) := rfl

-- obviously can be golfed
instance isfilt [hγ : IsWellOrderLimitElement γ] : IsFiltered {b | b < γ} where
  cocone_objs := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    cases h2.trichotomous x y with
    | inl h =>
      obtain ⟨z, hz⟩ := hγ.not_succ y hy
      use ⟨z, hz.2⟩
      refine ⟨homOfLE ?_, homOfLE ?_, trivial⟩
      have := (le_of_lt (lt_trans h hz.1))
      exact this
      exact le_of_lt hz.1
    | inr h =>
      cases h with
      | inl h =>
        obtain ⟨z, hz⟩ := hγ.not_succ y hy
        use ⟨z, hz.2⟩
        refine ⟨homOfLE ?_, homOfLE ?_, trivial⟩
        have := le_of_lt hz.1
        rw [← h] at this
        exact this
        exact le_of_lt hz.1
      | inr h =>
        obtain ⟨z, hz⟩ := hγ.not_succ x hx
        use ⟨z, hz.2⟩
        refine ⟨homOfLE ?_, homOfLE ?_, trivial⟩
        exact le_of_lt hz.1
        have := (le_of_lt (lt_trans h hz.1))
        exact this
  cocone_maps := fun ⟨x, hx⟩ ⟨y, hy⟩ _ _ ↦ by
    obtain ⟨z, hz⟩ := hγ.not_succ y hy
    refine ⟨⟨z, hz.2⟩, ⟨homOfLE (le_of_lt hz.1), rfl⟩⟩
  nonempty := by simp [IsWellOrderLimitElement.not_bot]

/-
def filteredfunctor [hγ : IsWellOrderLimitElement γ] : {b | b < γ} ⥤ SSet where
  obj x := (F.map (homOfLE (@bot_le _ _ _ x)))
  map := _
-/

-- this is functor {b | b < x} ⥤ SSet, for which we have a cocone which is a filtered colimit
--((PrincipalSeg.ofElement (fun x x_1 ↦ x < x_1) x).functorToOver ⋙
--    Over.forget (PrincipalSeg.ofElement (fun x x_1 ↦ x < x_1) x).top ⋙ F)

-- show that F(⊥) ⟶ F(γ) is a monomorphism for all (γ : β)
instance aux1 : monomorphisms SSet (F.map (homOfLE (@bot_le _ _ _ γ))) := by
  apply WellFounded.induction h2.wf γ
  intro x ih
  cases eq_bot_or_eq_succ_or_isWellOrderLimitElement x with
  | inl h0 =>
    have : monomorphisms SSet (F.map (homOfLE (@bot_le _ _ _ ⊥))) := by
      simp only [homOfLE_refl, CategoryTheory.Functor.map_id, monomorphisms.iff]
      exact instMonoId (F.obj ⊥)
    convert this
  | inr h =>
    cases h with
    | inl hsucc =>
      obtain ⟨b, ⟨hb1, hb2⟩⟩ := hsucc
      rw [hb1] at hb2 ih
      have := @mono_comp SSet _ _ _ _ _ (ih b hb2) _ (hF b hb2)
      rw [← Functor.map_comp, homOfLE_comp] at this
      convert this
    | inr hlim =>
      let filt := ((PrincipalSeg.ofElement (· < ·) x).functorToOver ⋙ Over.forget (PrincipalSeg.ofElement (· < ·) x).top ⋙ F) --functor
      let cocone : Limits.Cocone filt := (F.coconeOfFunctorToOver (PrincipalSeg.ofElement (· < ·) x).functorToOver) --cocone over functor
      obtain ⟨hd : Limits.IsColimit cocone⟩ := h.nonempty_isColimit (PrincipalSeg.ofElement (· < ·) x) --filtered colimit
      change monomorphisms SSet ((cocone).ι.app ⊥) -- filt(⊥) ⟶ filt(x)
      have : ∀ y : {b | b < x}, monomorphisms SSet (filt.map (homOfLE (OrderBot.bot_le y))) := fun ⟨y, hy⟩ ↦ ih y hy
      refine @preserves_mono_of_preservesLimit _ _ _ _ _ _ _ _ ?_ sorry
      refine @Limits.PreservesLimitsOfShape.preservesLimit _ _ _ _ _ _ _ ?_ _
      --refine @Limits.filteredColimPreservesFiniteLimits Limits.WalkingCospan
      /-
      refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ ?_
      intro k
      rw [mono_iff_injective]
      intro a b h
      dsimp [cocone] at a b h
      -/
      sorry

#check Limits.filteredColimPreservesFiniteLimits
--(J := Limits.WalkingCospan)
-- we have a functor `{b | b < x} ⥤ SSet`, given by `b ↦ F(b)` and a colimit cocone for this
-- this is a filtered colimit. Each `F(⊥) ⟶ F(b)` is a mono, and filtered colimits preserve monos
-- so `F(⊥) ⟶ F(x)` is a mono

instance monomorphisms.isStableUnderTransfiniteCompositionOfShape :
    (monomorphisms SSet).IsStableUnderTransfiniteCompositionOfShape β where
  condition F h hF c hc := by
    sorry

end mono_proof
/-
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
  exact hS.IsStableUnderTransfiniteComposition.comp_mem (mono_iso i).hom (imagePresheaf i).ι
    (WeaklySaturated_contains_iso S (mono_iso i).hom (isomorphisms.infer_property (mono_iso i).hom)) H

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
-/
