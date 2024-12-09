import Quasicategory.Basic
import Quasicategory.InternalHom
import Quasicategory.SimplicialSet

/-!

Some results about monomorphisms, and the proof of `0077`.

-/

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory

/-- boundary inclusions are monomorphisms. -/
instance boundaryInclusion_mono (n : ℕ) : Mono (boundaryInclusion n) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((boundaryInclusion n).app k) := fun _ ↦ by
    rw [mono_iff_injective]
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  apply NatTrans.mono_of_mono_app

/-- horn inclusions are monomorphisms. -/
instance hornInclusion_mono (n : ℕ) (i : Fin (n + 1)) : Mono (hornInclusion n i) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((hornInclusion n i).app k) := fun _ ↦ by
    rw [mono_iff_injective]
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  apply NatTrans.mono_of_mono_app

-- inner horn inclusions are monomorphisms
instance innerHornInclusion_mono ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    monomorphisms SSet (hornInclusion (n + 2) i) := hornInclusion_mono _ _

open MonoidalCategory in
/-- B ⊗ ∂Δ[n] ⟶ B ⊗ Δ[n] is a monomorphism. Should be generalized. -/
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

instance monomorphisms.StableUnderCobaseChange : IsStableUnderCobaseChange (monomorphisms SSet) := by
  refine ⟨?_⟩
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
  bot := ⟨⊥, Ne.bot_lt' (id (Ne.symm not_bot))⟩
  bot_le _ := OrderBot.bot_le _

instance has_bot' [IsWellOrderLimitElement γ] : OrderBot {b | b < γ} :=
  has_bot γ (IsWellOrderLimitElement.neq_bot γ)

example [IsWellOrderLimitElement γ] :
    (F.map (homOfLE bot_le)) = ((F.coconeOfFunctorToOver (PrincipalSeg.ofElement (· < ·) γ).functorToOver).ι.app ((has_bot' γ).bot)) := rfl

instance [hγ : IsWellOrderLimitElement γ] : IsDirected {b | b < γ} (· ≤ ·) where
  directed a b := by
    cases h2.trichotomous a b with
    | inl h =>
      obtain ⟨c, hc⟩ := hγ.not_succ _ b.property
      exact ⟨⟨c, hc.2⟩, ⟨(le_of_lt h).trans (le_of_lt hc.1), le_of_lt hc.1⟩⟩
    | inr h =>
      cases h with
      | inl h =>
        obtain ⟨c, hc⟩ := hγ.not_succ _ b.property
        refine ⟨⟨c, hc.2⟩, ⟨(by rw [h]; exact le_of_lt hc.1 : a ≤ c), le_of_lt hc.1⟩⟩
      | inr h =>
        obtain ⟨c, hc⟩ := hγ.not_succ _ a.property
        exact ⟨⟨c, hc.2⟩, ⟨le_of_lt hc.1, (le_of_lt h).trans (le_of_lt hc.1)⟩⟩

instance isfilt [IsWellOrderLimitElement γ] : IsFiltered {b | b < γ} := isFiltered_of_directed_le_nonempty _

-- when `γ : β` is a limit element, `Over.forgetCocone γ` is a colimit
def forgetCoconeColimit (h : IsWellOrderLimitElement γ) : Limits.IsColimit (Over.forgetCocone γ) where
  desc c := ⟨⟨ by
    by_contra h'
    rw [not_le] at h'
    obtain ⟨y, hy1, hy2⟩ := h.not_succ _ h'
    have := (c.ι.app (Over.mk (le_of_lt hy2).hom)).le
    dsimp at this
    rw [← not_le] at hy1
    exact hy1 this ⟩⟩

-- show that F(⊥) ⟶ F(γ) is a monomorphism for all (γ : β)
-- prove for ordinals by lurie
-- genl using
-- Ordinal.limitRecOn
/-
instance monoaux1 : monomorphisms SSet (F.map (bot_le (a := γ).hom)) := by
  apply WellFounded.induction h2.wf γ
  intro x ih
  cases eq_bot_or_eq_succ_or_isWellOrderLimitElement x with
  | inl h0 =>
    have : monomorphisms SSet (F.map (bot_le (a := ⊥)).hom) := by
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
      let filt := ((PrincipalSeg.ofElement (· < ·) x).functorToOver ⋙ Over.forget x ⋙ F) --functor
      let cocone : Limits.Cocone filt := (F.coconeOfFunctorToOver (PrincipalSeg.ofElement (· < ·) x).functorToOver) --cocone over functor
      obtain ⟨hd : Limits.IsColimit cocone⟩ := h.nonempty_isColimit (PrincipalSeg.ofElement (· < ·) x) --filtered colimit
      --change Mono ((cocone).ι.app ⊥)
      --change Mono ((F.mapCocone (Over.forgetCocone x)).ι.app (Over.mk bot_le.hom))
      sorry
-/

-- show for all γ satisfying same thing as γ, whisker by γ ⥤ β, then bot γ ↦ bot β from << (ordinal equivalence), conclude with special case β = γ
instance monomorphisms.isStableUnderTransfiniteCompositionOfShape :
    (monomorphisms SSet).IsStableUnderTransfiniteCompositionOfShape β where
  condition F h hF c hc := by
    sorry

end mono_proof

instance monomorphisms.IsStableUnderTransfiniteComposition :
    IsStableUnderTransfiniteComposition (monomorphisms SSet) where
  id_mem _ := instMonoId _
  comp_mem f g hf hg := @mono_comp _ _ _ _ _ f hf g hg
  isStableUnderTransfiniteCompositionOfShape _ :=
    monomorphisms.isStableUnderTransfiniteCompositionOfShape

-- `0077` (a) monomorphisms are weakly saturated
instance monomorphisms.WeaklySaturated : WeaklySaturated (monomorphisms SSet) :=
  ⟨ monomorphisms.StableUnderCobaseChange,
    monomorphisms.StableUnderRetracts,
    monomorphisms.IsStableUnderTransfiniteComposition⟩

-- need skeleta pushout construction for this, this is showing B(k - 1) ↪ B(k) is contained in S
open SimplicialSubset GrothendieckTopology in
lemma succ_mem_thing (S : MorphismProperty SSet) (hS : S.WeaklySaturated) (h : ∀ (n : ℕ), S (boundaryInclusion n))
    {A B : SSet} (i : A ⟶ B) [hi : Mono i] :
    ∀ a < wellOrderSucc a, S ((skeleton_union_functor' B (imagePresheaf i)).map (homOfLE (self_le_wellOrderSucc a))) := by
  intro a ha
  dsimp [skeleton_union_functor, skeleton_union_functor', sset_functor]
  sorry

open SimplicialSubset GrothendieckTopology in
/-- `0077` (b) monomorphisms are generated by boundary inclusions. -/
lemma mono_eq_bdryInclusions : monomorphisms SSet = WeaklySaturatedClassOf.{0} BoundaryInclusions := by
  ext A B i
  refine ⟨?_, fun h ↦ minimalWeaklySaturated _ _ (fun _ _ _ h ↦ by induction h with | mk => exact boundaryInclusion_mono _) monomorphisms.WeaklySaturated i h⟩
  intro h
  letI hS : WeaklySaturated (WeaklySaturatedClassOf BoundaryInclusions) := by infer_instance
  letI : Mono i := h
  have := (hS.IsStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape ℕ).condition
    (skeleton_union_functor' B (imagePresheaf i)) (succ_mem_thing _ hS (fun n ↦ .of _ (.mk n)) i) (skeleton_union_cocone B (imagePresheaf i)) (skeleton_union_cocone_iscolimit B (imagePresheaf i))
  dsimp [SSet.skeleton_union_cocone] at this
  have H : BoundaryInclusions.WeaklySaturatedClassOf (Subpresheaf.ι (imagePresheaf i)) := by
    convert this
    swap
    rw [empty_union_image i]
    dsimp [skeleton_union_functor, sset_functor, skeleton_union_functor']
    congr
    rw [empty_union_image i]
  change BoundaryInclusions.WeaklySaturatedClassOf ((mono_iso i).hom ≫ (imagePresheaf i).ι)
  exact hS.IsStableUnderTransfiniteComposition.comp_mem (mono_iso i).hom (imagePresheaf i).ι
    (WeaklySaturated_contains_iso _ (mono_iso i).hom (isomorphisms.infer_property (mono_iso i).hom)) H

/-- `006Y` trivial Kan fibration iff rlp wrt all monomorphisms -/
lemma trivialKanFibration_eq_rlp_monomorphisms :
    trivialKanFibration.{0} = (monomorphisms SSet).rlp:= by
  ext X Y p
  refine ⟨?_, ?_⟩
  · intro h
    rw [class_rlp_iff_llp_morphism, mono_eq_bdryInclusions]
    intro _ _ i hi
    refine minimalWeaklySaturated (MorphismClass p).llp BoundaryInclusions ?_ (llp_weakly_saturated _) i hi
    intro _ _ _ hf _ _ _ hg
    induction hg with | mk => exact h hf
  · intro h _ _ p hp
    induction hp
    exact h (boundaryInclusion_mono _)

/-- `006Z`(a), trivial Kan fibrations admit sections -/
noncomputable
def trivialKanFibration_section {X Y : SSet} (p : X ⟶ Y)
    (hp : trivialKanFibration p) : Y ⟶ X := by
  rw [trivialKanFibration_eq_rlp_monomorphisms] at hp
  have : (emptyIsInitial.to X) ≫ p = (emptyIsInitial.to Y) ≫ (𝟙 Y) :=
    Limits.IsInitial.hom_ext emptyIsInitial _ _
  exact ((hp (initial_mono Y emptyIsInitial)).sq_hasLift (CommSq.mk (this))).exists_lift.some.l

/-- the above map is a section -/
lemma trivialKanFibration_section_comp {X Y : SSet} (p : X ⟶ Y) (hp : trivialKanFibration p) :
    trivialKanFibration_section p hp ≫ p = 𝟙 Y := by
  rw [trivialKanFibration_eq_rlp_monomorphisms] at hp
  have : (emptyIsInitial.to X) ≫ p = (emptyIsInitial.to Y) ≫ (𝟙 Y) :=
    Limits.IsInitial.hom_ext emptyIsInitial _ _
  exact ((hp (initial_mono Y emptyIsInitial)).sq_hasLift (CommSq.mk (this))).exists_lift.some.fac_right

/-- `050J` (1) -/
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

/-- `050J` (3) --/
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

/-- inner anodyne morphisms are monomorphisms -/
lemma innerAnodyne_mono : innerAnodyne ≤ monomorphisms SSet := by
  rw [innerAnodyne_eq]
  refine minimalWeaklySaturated.{0} (monomorphisms SSet) InnerHornInclusions ?_ monomorphisms.WeaklySaturated
  intro _ _ _ h
  induction h with | mk => exact hornInclusion_mono _ _

end SSet
