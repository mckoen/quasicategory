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

instance hornInclusion_mono (n : ℕ) (i : Fin (n + 1)) : Mono (hornInclusion n i) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((hornInclusion n i).app k) := fun _ ↦ by
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
-- `0077` (b) monomorphisms are generated by boundary inclusions
lemma contains_mono_iff_contains_boundaryInclusion
    (S : MorphismProperty SSet.{0}) (hS : WeaklySaturated.{0} S) :
    (∀ (n : ℕ), S (boundaryInclusion n))
      ↔ ∀ {A B : SSet} (i : A ⟶ B) [Mono i], S i := by
  refine ⟨?_, fun h n ↦ h (boundaryInclusion n)⟩
  intro h A B i hi
  have := (hS.IsStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape ℕ).condition
    (skeleton_union_functor' B (imagePresheaf i)) (succ_mem_thing S hS h i) (skeleton_union_cocone B (imagePresheaf i)) (skeleton_union_cocone_iscolimit B (imagePresheaf i))
  dsimp [SSet.skeleton_union_cocone] at this
  have H : S (Subpresheaf.ι (imagePresheaf i)) := by
    convert this
    swap
    rw [empty_union_image i]
    dsimp [skeleton_union_functor, sset_functor, skeleton_union_functor']
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
  (contains_innerAnodyne_iff_contains_inner_horn.{0, 1}
    (monomorphisms SSet) monomorphisms.WeaklySaturated).1 inner_horn_mono p hp

-- the pushout in `007F` (a) given by a morphism `A ⟶ B`
def generalPushout {A B : SSet} (i : A ⟶ B) :=
  IsPushout.of_hasPushout (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ i)

-- cocone with pt. `Δ[2] ⊗ B` given by `i`
noncomputable
def B_cocone {A B : SSet} (i : A ⟶ B) :
    Limits.PushoutCocone (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ i) :=
  Limits.PushoutCocone.mk (Δ[2] ◁ i) (hornInclusion 2 1 ▷ B) rfl

-- induced morphism from the pushout to `Δ[2] ⊗ B`
noncomputable
def to_B {A B : SSet} (i : A ⟶ B) : (generalPushout i).cocone.pt ⟶ Δ[2] ⊗ B :=
  (generalPushout i).desc (Δ[2] ◁ i) (hornInclusion 2 1 ▷ B) rfl

----------------
-- pushout in `0079`,
-- inclusions of this into `Δ[2] ⊗ Δ[m]` generate the WSC of inner anodyne morphisms (`007F` (b))
def Δ_pushout (m : ℕ) :=
  generalPushout (boundaryInclusion m)

-- the cocone with point `Δ[2] ⊗ Δ[m]` given by boundary inclusions
noncomputable
def Δ_cocone (m : ℕ) := B_cocone (boundaryInclusion m)

-- induced morphism from pushout to `Δ[2] ⊗ Δ[m]` given by `Δ_cocone`
noncomputable
def to_Δ (m : ℕ) : (Δ_pushout m).cocone.pt ⟶ Δ[2] ⊗ Δ[m] :=
  (Δ_pushout m).isColimit.desc (Δ_cocone m)
----------------


-- pushout in proof `0079` (for retract diagram)
def Λ_pushout (m : ℕ) (i : Fin (m + 1)) :=
  generalPushout (hornInclusion m i)


-- induced morphism from pushout to `Δ[2] ⊗ Δ[m]` given by `Λ_cocone`
noncomputable
def to_Λ (m : ℕ) (i : Fin (m + 1)) : (Λ_pushout m i).cocone.pt ⟶ Δ[2] ⊗ Δ[m] :=
  to_B (hornInclusion m i)

inductive bdryPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk ⦃m : ℕ⦄ : bdryPushout (to_Δ m)

/-- the class inclusions from pushouts to `Δ[2] ⊗ Δ[m]` -/
def bdryPushoutClass : MorphismProperty SSet := fun _ _ p ↦ bdryPushout p

section _007F

namespace _007F

-- T = WeaklySaturatedOf bdryPushoutClass
-- S is the class of all morphism `i : A → B` such that the induced pushout is in T
def S : MorphismProperty SSet := fun _ _ i ↦ (WeaklySaturatedClassOf.{0} bdryPushoutClass) (to_B i)

lemma S_contains_bdry_incl : ∀ (n : ℕ), S (boundaryInclusion n) := fun _ ↦ by
  apply WeaklySaturatedOf.of
  apply bdryPushout.mk

-- S is weakly saturated because T is. closure under retracts and pushouts can be shown,
-- not sure about composition
instance S_WeaklySaturated : WeaklySaturated S := sorry

lemma S_contains_monos : ∀ {A B : SSet.{0}} (i : A ⟶ B) [Mono i], S i := by
  have := S_contains_bdry_incl
  rw [contains_mono_iff_contains_boundaryInclusion S S_WeaklySaturated] at this
  intro _ _ i _
  exact this i

lemma innerAnodyne_eq_innerHorn : innerAnodyne.{0} = (WeaklySaturatedClassOf.{0} InnerHornInclusions) := sorry

-- [n] ⟶ [2] by j ↦
-- 0 if j < i
-- 1 if j = i
-- 2 if j > i
def s_aux (i : Fin (n + 1)) : Fin (n + 1) →o Fin 3 where
  toFun j :=   if _ : (j : ℕ) < i then 0 else if _ : (j : ℕ) = i then 1 else 2
  monotone' j k h := by
    dsimp only [dite_eq_ite]
    cases Nat.lt.isWellOrder.trichotomous j i with
    | inl h' => simp only [h', ↓reduceIte, Fin.isValue, Fin.zero_le]
    | inr h' => cases h' with
    | inl h' =>
      have : (i : ℕ) ≤ k := le_of_eq_of_le (id (Eq.symm h')) h
      rw [← not_lt] at this
      simp only [h', lt_self_iff_false, ↓reduceIte, Fin.isValue, this, ge_iff_le]
      aesop
    | inr h' =>
      have a : ¬ (j : ℕ) < i := Nat.not_lt_of_gt h'
      have b : ¬ (j : ℕ) = i := Nat.ne_of_lt' h'
      have c : ¬ (k : ℕ) < i := by
        by_contra p
        exact a (lt_of_le_of_lt (h : (j : ℕ) ≤ k) p)
      have d : ¬ (k : ℕ) = i := by
        by_contra p
        apply Nat.not_le_of_lt h'
        have : (j : ℕ) ≤ k := h
        rw [p] at this
        exact this
      simp only [a, ↓reduceIte, b, Fin.isValue, c, d, le_refl]

def standard_map (n : ℕ) (i : Fin (n + 1)) : Δ[n] ⟶ Δ[2] :=
  standardSimplex.map (SimplexCategory.mkHom (s_aux i))

-- the above map restricted to the horn
def horn_map (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[2] :=
  (hornInclusion n i) ≫ (standard_map n i)

-- on vertices j maps to
-- (j, 0) if j < i
-- (j, 1) if j = i
-- (j, 2) if j > i
def s (n : ℕ) (i : Fin (n + 1)) : Δ[n] ⟶ Δ[2] ⊗ Δ[n] :=
  FunctorToTypes.prod.lift (standard_map n i) (𝟙 _)

def s_restricted (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[2] ⊗ Λ[n, i]  :=
  FunctorToTypes.prod.lift (horn_map n i) (𝟙 _)

noncomputable
def horn_to_pushout (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ (Λ_pushout n i).cocone.pt :=
  s_restricted n i ≫ (Limits.pushout.inl (hornInclusion 2 1 ▷ Λ[n, i]) (Λ[2, 1] ◁ hornInclusion n i))

lemma leftSqCommAux (n : ℕ) (i : Fin (n + 1)) :
    s_restricted n i ≫ Δ[2] ◁ (hornInclusion n i) = (hornInclusion n i) ≫ s n i := rfl

lemma leftSqComm (n : ℕ) (i : Fin (n + 1)) : horn_to_pushout n i ≫ to_Λ n i = (hornInclusion n i) ≫ s n i := by
  rw [← leftSqCommAux]
  dsimp [horn_to_pushout, to_Λ, to_B]
  rw [Category.assoc, IsPushout.inl_desc]

def r_aux (i : Fin (n + 1)) : Fin 3 × Fin (n + 1) →o Fin (n + 1) where
  toFun := fun ⟨k, j⟩ ↦
    if _ : ((j : ℕ) < i ∧ k = 0) ∨ ((j : ℕ) > i ∧ k = 2) then j else i
  monotone' := by
    intro ⟨k, j⟩ ⟨k', j'⟩ ⟨(hk : k ≤ k'), (hj : j ≤ j')⟩
    cases Nat.lt.isWellOrder.trichotomous j i with
    | inl h =>
      have : ¬ i < j := Lean.Omega.Fin.not_lt.mpr (Fin.le_of_lt h)
      fin_cases k; all_goals fin_cases k'
      all_goals simp only [Fin.val_fin_lt, Fin.mk_one, Fin.isValue, one_ne_zero, and_false, gt_iff_lt,
        Fin.reduceEq, or_self, ↓reduceDIte, Fin.reduceFinMk, and_true, false_or, dite_eq_ite,
        ge_iff_le, this]
      pick_goal 6
      · by_cases i < j'; all_goals rename_i h'; simp only [h', ↓reduceIte, le_refl, le_of_lt]
      pick_goal 8
      · by_cases i < j'; all_goals rename_i h'; simp only [h', ↓reduceIte, le_refl, le_of_lt]
      all_goals aesop
    | inr h => cases h with
    | inl h => have := Fin.eq_of_val_eq h; aesop
    | inr h =>
      have : i < j' := lt_of_lt_of_le h hj
      have : i ≤ j' := le_of_lt this
      fin_cases k; all_goals fin_cases k'
      all_goals simp only [Fin.mk_one, one_ne_zero, le_refl,Fin.val_fin_lt,
        Lean.Omega.Fin.not_lt.mpr (Fin.le_of_lt h), Fin.zero_eta, Fin.isValue, and_true, gt_iff_lt, Fin.reduceEq,
        and_false, or_self, ↓reduceDIte, Fin.reduceFinMk, or_false, false_or, dite_eq_ite, ge_iff_le, h]
      pick_goal 3
      · by_cases i < j'; all_goals rename_i h'; aesop
      pick_goal 5
      · by_cases i < j'; all_goals rename_i h'; aesop
      all_goals aesop

open standardSimplex SimplexCategory in
def map_mk_from_prod (f : Fin (n + 1) × Fin (m + 1) →o Fin (k + 1)) : Δ[n] ⊗ Δ[m] ⟶ Δ[k] := by
  refine ⟨fun x ⟨c, d⟩ ↦ ⟨mkHom ⟨fun a ↦ f ((asOrderHom c) a, (asOrderHom d) a), ?_⟩⟩, ?_⟩
  · intro j k hjk
    exact f.monotone ⟨(asOrderHom c).monotone hjk, (asOrderHom d).monotone hjk⟩
  · aesop

-- on vertices j k map to
-- j if (j < i) ∧ (k = 0)
-- j if (j > i) ∧ (k = 2)
-- i if (j = i) ∨ (k = 1)
def r (n : ℕ) (i : Fin (n + 1)) : Δ[2] ⊗ Δ[n] ⟶ Δ[n] := map_mk_from_prod (r_aux i)

variable (n : ℕ) (i : Fin (n + 1)) (h0 : 0 < i) (hn : i < Fin.last n)

-- r restricted along Λ[2, 1]
noncomputable
def r_restrict_horn_2 : Λ[2, 1] ⊗ Δ[n] ⟶ Λ[n, i] where
  app k := by
    intro ⟨⟨x, hx⟩, y⟩
    refine ⟨((hornInclusion 2 1) ▷ Δ[n] ≫ r n i).app k ⟨⟨x, hx⟩, y⟩, ?_⟩
    rw [Set.ne_univ_iff_exists_not_mem] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    fin_cases a
    · simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Set.union_singleton, Set.mem_insert_iff,
        zero_ne_one, Set.mem_range, false_or, not_exists] at ha
      use 0
      simp only [Fin.isValue, Nat.reduceAdd, ne_eq, Set.union_singleton, Set.mem_insert_iff,
        Set.mem_range, not_or, not_exists]
      refine ⟨Fin.ne_of_lt h0, fun j h ↦ ?_⟩
      change (fun a ↦
                if (asOrderHom y) a < i ∧ (asOrderHom x) a = 0 ∨ i < (asOrderHom y) a ∧ (asOrderHom x) a = 2 then
                  (asOrderHom y) a
                else i) j = 0 at h
      by_cases (asOrderHom y) j < i; all_goals rename_i h'
      · by_cases (asOrderHom x) j = 0; all_goals rename_i h''
        · exact ha j h''
        · aesop
      · aesop
    · aesop
    · simp only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, Set.union_singleton,
        Set.mem_insert_iff, Fin.reduceEq, Set.mem_range, false_or, not_exists] at ha
      use Fin.last n
      simp only [Fin.isValue, Nat.reduceAdd, ne_eq, Set.union_singleton, Set.mem_insert_iff,
        Set.mem_range, not_or, not_exists]
      refine ⟨Fin.ne_of_gt hn, fun j h ↦ ?_⟩
      change (fun a ↦
                if (asOrderHom y) a < i ∧ (asOrderHom x) a = 0 ∨ i < (asOrderHom y) a ∧ (asOrderHom x) a = 2 then
                  (asOrderHom y) a
                else i) j = Fin.last n at h
      by_cases (asOrderHom y) j < i; all_goals rename_i h'
      · by_cases (asOrderHom x) j = 0; all_goals rename_i h''
        · simp only [h', Nat.reduceAdd, h'', Fin.isValue, and_self, Fin.reduceEq, and_false,
          or_false, ↓reduceIte, Fin.natCast_eq_last] at h
          rw [h] at h'
          exact absurd (lt_trans h' hn) (Fin.not_lt.mpr (Fin.le_last _))
        · simp_all only [Nat.reduceAdd, Fin.isValue, Set.union_singleton, ne_eq, Fin.natCast_eq_last, and_false,
          or_self, ↓reduceIte, lt_self_iff_false]
      · simp_all only [Nat.reduceAdd, Fin.isValue, Set.union_singleton, ne_eq, Fin.natCast_eq_last, false_and,
        and_false, or_self, ↓reduceIte, not_lt, Fin.last_le_iff, lt_self_iff_false]

-- r restricted along Λ[n, i]
noncomputable
def r_restrict_horn_n : Δ[2] ⊗ Λ[n, i] ⟶ Λ[n, i] where
  app k := by
    intro ⟨x, ⟨y, hy⟩⟩
    refine ⟨(Δ[2] ◁ (hornInclusion n i) ≫ r n i).app k ⟨x, ⟨y, hy⟩⟩, ?_⟩
    sorry

open standardSimplex SimplexCategory in
noncomputable
def pushout_to_horn : (Λ_pushout n i).cocone.pt ⟶ Λ[n, i] :=
  Limits.pushout.desc (r_restrict_horn_n n i) (r_restrict_horn_2 n i h0 hn) rfl

lemma rightSqComm : pushout_to_horn n i h0 hn ≫ hornInclusion n i = to_Λ n i ≫ r n i := by
  dsimp [pushout_to_horn, to_Λ, to_B]
  apply Limits.pushout.hom_ext; all_goals aesop

lemma r_comp_s (n : ℕ) (i : Fin (n + 1)) : s n i ≫ r n i = 𝟙 Δ[n] := by
  let r' := r_aux i
  let s' : Fin (n + 1) →o Fin 3 × Fin (n + 1) := (s_aux i).prod (OrderHom.id)
  let f : Fin (n + 1) →o Fin (n + 1) := OrderHom.comp r' s'
  have a : f = OrderHom.id := by
    ext x
    simp [f, r', s', s_aux, r_aux]
    cases Nat.lt.isWellOrder.trichotomous x i with
    | inl h => aesop
    | inr h => cases h with
    | inl h => aesop
    | inr h =>
      simp_all only [Fin.val_fin_lt, Fin.isValue, true_and]
      split
      next h_1 =>
        simp_all only [Fin.isValue, one_ne_zero, imp_false, not_le, and_self]
        split
        next h_2 => simp_all only [Fin.isValue, Fin.reduceEq, or_false, ↓reduceIte]
        next h_2 =>
          simp_all only [not_lt, Fin.isValue, Fin.reduceEq, or_false]
          split
          next h_3 => simp_all only
          next h_3 => simp_all only [not_lt]
      next
        h_1 =>
        simp_all only [Fin.isValue, Fin.reduceEq, imp_false, not_le, and_self, ite_eq_right_iff, not_lt]
        split
        next h_2 => simp_all only
        next h_2 =>
          simp_all only [not_or, not_le]
          obtain ⟨left, right⟩ := h_2
          exfalso
          exact left right
  have : s n i ≫ r n i = standardSimplex.map (SimplexCategory.mkHom f) := rfl
  rw [this, a]
  aesop

lemma restricted_r_comp_s : horn_to_pushout n i ≫ pushout_to_horn n i h0 hn = 𝟙 Λ[n, i] := by
  dsimp [horn_to_pushout, pushout_to_horn]
  rw [Category.assoc, Limits.pushout.inl_desc]
  ext k ⟨x, hx⟩
  change (r_restrict_horn_n n i).app k ((horn_map n i).app k ⟨x, hx⟩, ⟨x, hx⟩) = ⟨x, hx⟩
  simp [r_restrict_horn_n]
  congr
  have := congr_fun (congr_app (r_comp_s n i) k) x
  aesop

noncomputable
instance hornRetract : IsRetract (hornInclusion n i) (to_Λ n i) where
  i := {
    left := horn_to_pushout n i
    right := s n i
    w := leftSqComm n i
  }
  r := {
    left := pushout_to_horn n i h0 hn
    right := r n i
    w := rightSqComm n i h0 hn
  }
  retract := Arrow.hom_ext _ _ (restricted_r_comp_s n i h0 hn) (r_comp_s n i)

-- need to show inner anodyne = wsc generated by inner horn inclusions
-- the class inner anodyne morphisms is the weakly saturated class generated by the pushout maps given in `to_Δ`
lemma innerAnodyne_eq_T : innerAnodyne.{0} = (WeaklySaturatedClassOf.{0} bdryPushoutClass) := by
  rw [innerAnodyne_eq_innerHorn]
  ext X Y f
  refine ⟨?_, sorry⟩ -- other direction is more technical
  intro h
  refine minimalWeaklySaturated.{0} (WeaklySaturatedClassOf bdryPushoutClass) InnerHornInclusions ?_ (by infer_instance) _ h
  intro A B g hg
  induction hg with
  | @mk n i h0 hn =>
    apply WeaklySaturatedOf.retract -- reduces to showing horn inclusion is a retract of a boundary pushout maps
    · exact hornRetract (n + 2) i h0 hn
    · exact S_contains_monos (hornInclusion (n + 2) i)

-- `007F` (a)
lemma monoPushout_innerAnodyne {A B : SSet} (i : A ⟶ B) [hi : Mono i] :
    innerAnodyne.{0} (to_B i) := by
  rw [innerAnodyne_eq_T]
  apply S_contains_monos

-- `007F` (b)
-- inner Anodyne morphisms are generated by the pushout maps given in `to_Δ`
lemma contains_innerAnodyne_iff_contains_pushout_maps
    (S : MorphismProperty SSet.{0}) (hS : WeaklySaturated.{0} S) :
    (∀ m, S (to_B (boundaryInclusion m))) ↔ (∀ {X Y : SSet} (p : X ⟶ Y) (_ : innerAnodyne p), S p) := by
  refine ⟨?_, fun h m ↦ h _ (monoPushout_innerAnodyne (boundaryInclusion m))⟩
  intro h X Y p hp
  rw [innerAnodyne_eq_T] at hp
  refine minimalWeaklySaturated.{0} S bdryPushoutClass ?_ hS _ hp
  intro _ _ _ hf
  induction hf with
  | @mk m => exact h m

end _007F
