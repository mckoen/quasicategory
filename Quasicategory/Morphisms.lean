import Mathlib.AlgebraicTopology.Quasicategory
import Mathlib.AlgebraicTopology.KanComplex
import Mathlib.CategoryTheory.Adhesive
import Quasicategory.InternalHom
import Quasicategory.MorphismProperty
import Quasicategory.Terminal

namespace SSet

open CategoryTheory Simplicial MorphismProperty

/- a morphism is a trivial Kan fibration if it has the right lifting property wrt
  every boundary inclusion  `∂Δ[n] ⟶ Δ[n]`. -/
def trivialKanFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ (n : ℕ), HasLiftingProperty (boundaryInclusion n) p

/- a morphism is an inner fibration if it has the right lifting property wrt
  every inner horn inclusion  `Λ[n, i] ⟶ Δ[n]`. -/
def innerFibration : MorphismProperty SSet := fun _ _ p ↦
  ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
    HasLiftingProperty (hornInclusion (n+2) i) p

/- a morphism is inner anodyne if it has the left lifting property wrt all inner fibrations. -/
abbrev innerAnodyne := llp_wrt innerFibration

/- inner horn inclusions are inner anodyne. -/
lemma innerAnodyne_of_innerHorn
    ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)) :
    innerAnodyne (hornInclusion (n+2) i) := fun _ _ _ h ↦ h _h0 _hn

-- innerAnodyne is WSC gen. by inner horn inclusions
lemma contains_innerAnodyne_iff_contains_inner_horn
    (S : MorphismProperty SSet) (hS : WeaklySaturated S) :
    (∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (_h0 : 0 < i) (_hn : i < Fin.last (n+2)), S (hornInclusion (n+2) i))
      ↔ (∀ {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p), S p) := by
  refine ⟨?_, fun h n i _h0 _hn ↦ h (hornInclusion (n + 2) i) (innerAnodyne_of_innerHorn _h0 _hn)⟩
  sorry

section Monomorphism

-- boundary inclusions are monomorphisms
instance boundaryInclusion_mono (n : ℕ) : Mono (boundaryInclusion n) := by
  have : ∀ (k : SimplexCategoryᵒᵖ), Mono ((boundaryInclusion n).app k) := fun _ ↦ by
    rw [mono_iff_injective]
    exact (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  apply NatTrans.mono_of_mono_app

open MonoidalCategory in
-- need that B ⊗ ∂Δ[n] ⟶ B ⊗ Δ[n] is a monomorphism for next lemma
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

instance monomorphisms.StableUnderTransfiniteComposition :
    StableUnderTransfiniteComposition (monomorphisms SSet) := by
  intro X Y f hf
  induction hf with
  | mk α F hF hS => exact transfinite_monos X Y f α F hF hS (le_refl α)

-- `0077` (a) monomorphisms are weakly saturated
instance monomorphisms.WeaklySaturated : WeaklySaturated (monomorphisms SSet) :=
  ⟨ monomorphisms.StableUnderCobaseChange,
    monomorphisms.StableUnderRetracts,
    monomorphisms.StableUnderTransfiniteComposition⟩

-- `0077` (b) monomorphisms are generated by boundary inclusions
lemma contains_mono_iff_contains_boundaryInclusion
    (S : MorphismProperty SSet) (hS : WeaklySaturated S) :
    (∀ (n : ℕ), S (boundaryInclusion n))
      ↔ ∀ {A B : SSet} (i : A ⟶ B) [Mono i], S i := by
  sorry

/- `006Y` trivial Kan fibration iff rlp wrt all monomorphisms -/
lemma trivialKanFibration_iff_rlp_monomorphisms {X Y : SSet} (p : X ⟶ Y) :
    trivialKanFibration p ↔ rlp_wrt (monomorphisms SSet) p :=
  ⟨ (contains_mono_iff_contains_boundaryInclusion (llp_wrt' p) (llp_weakly_saturated' p)).1,
    fun h n ↦ h (boundaryInclusion_mono n)⟩

-- innerAnodyne is generated by inner horn inclusions, which are monos and monos are saturated,
-- thus innerAnodynes are monos
lemma innerAnodyne_mono {X Y : SSet} (p : X ⟶ Y) (hp : innerAnodyne p) :
    monomorphisms SSet p :=
  (contains_innerAnodyne_iff_contains_inner_horn
    (monomorphisms SSet) monomorphisms.WeaklySaturated).1 inner_horn_mono p hp

end Monomorphism

section _007E

-- `007E` (1), if extension property wrt every inner anodyne, then quasicat
-- to prove converse, need that class of inner anodyne morphisms is generated by inner horn inclusions
instance _007Ea {S : SSet}
    (h : ∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) :
    Quasicategory S where
  hornFilling' n i σ₀ _h0 _hn := h (hornInclusion (n + 2) i) (innerAnodyne_of_innerHorn _h0 _hn) σ₀

abbrev proj (S : SSet) : S ⟶ Δ[0] := Limits.IsTerminal.from ptIsTerminal S

-- extension property wrt every inner anodyne morphism is equivalent to (S ⟶ Δ[0]) having RLP wrt
-- every inner anodyne morphism
lemma extension_iff_llp_proj {S : SSet} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    (rlp_wrt (innerAnodyne)) (proj S) := by
  refine ⟨?_, ?_⟩
  · intro h A B i hi
    refine ⟨?_⟩
    intro f₀ t sq
    obtain ⟨l, hl⟩ := h i hi f₀
    exact ⟨l, hl.symm, Limits.IsTerminal.hom_ext ptIsTerminal _ _⟩
  · intro h A B i hi f₀
    have : f₀ ≫ proj S = (i ≫ proj B) := Limits.IsTerminal.hom_ext ptIsTerminal _ _
    obtain ⟨⟨lift⟩⟩ := (h hi).sq_hasLift (CommSq.mk this)
    exact ⟨lift.l, lift.fac_left.symm⟩

-- since S is a quasicat, every inner horn inclusion has LLP wrt (S ⟶ Δ[0]), and
-- inner horn inclusions generate inner anodyne morphisms,
-- so all inner anodyne must have LLP wrt (S ⟶ Δ[0])

-- `007E`
-- quasicategory iff extension property wrt every inner anodyne morphism
instance quasicat_iff_extension_wrt_innerAnodyne {S : SSet} :
    (∀ {A B} (i : A ⟶ B) (_ : innerAnodyne i) (f₀ : A ⟶ S), ∃ (f : B ⟶ S), f₀ = i ≫ f) ↔
    Quasicategory S := by
  refine ⟨_007Ea, ?_⟩
  intro hS
  rw [extension_iff_llp_proj]
  apply (contains_innerAnodyne_iff_contains_inner_horn (llp_wrt' S.proj)
    (llp_weakly_saturated' S.proj)).1
  intro n i _h0 _hn
  constructor
  intro σ₀ _ sq
  obtain ⟨l, hl⟩ := hS.hornFilling _h0 _hn σ₀
  use l
  exact hl.symm
  apply Limits.IsTerminal.hom_ext ptIsTerminal

end _007E

open MonoidalCategory MonoidalClosed

noncomputable
abbrev Fun : SSetᵒᵖ ⥤ SSet ⥤ SSet := internalHom

-- the pushout in `007F` (a)
def monoPushout {A B : SSet} (i : A ⟶ B) [Mono i] :=
  IsPushout.of_hasPushout (hornInclusion 2 1 ▷ A) (Λ[2, 1] ◁ i)

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

section _0079

-- pushout in `0079`,
-- inclusions of this into `Δ[2] ⊗ Δ[m]` generate the WSC of inner anodyne morphisms (`007F` (b))
def Δ_pushout (m : ℕ) :=
  monoPushout (boundaryInclusion m)

-- the cocone with point `Δ[2] ⊗ Δ[m]` given by the 4 natural maps
noncomputable
def Δ_cocone (m : ℕ) := B_cocone (boundaryInclusion m)

-- induced morphism from pushout to `Δ[2] ⊗ Δ[m]` given by `Δ_cocone`
noncomputable
def to_Δ (m : ℕ) : (Δ_pushout m).cocone.pt ⟶ Δ[2] ⊗ Δ[m] :=
  (Δ_pushout m).isColimit.desc (Δ_cocone m)

lemma S_cocone_aux (S : SSet) (m : ℕ)
    (α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S)
    (β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S)
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    hornInclusion 2 1 ▷ ∂Δ[m] ≫ MonoidalClosed.uncurry α =
    Λ[2, 1] ◁ boundaryInclusion m ≫ MonoidalClosed.uncurry β := by
  let α' := MonoidalClosed.uncurry α
  let β' := MonoidalClosed.uncurry β
  ext n ⟨x, y⟩
  have := congr_fun (congr_app sq.w n) y
  change ((MonoidalClosed.pre (hornInclusion 2 1)).app S).app n (α.app n y) =
    β.app n ((boundaryInclusion m).app n y) at this
  change α'.app n ((hornInclusion 2 1 ▷ ∂Δ[m]).app n (x, y)) =
    β'.app n ((Λ[2, 1] ◁ boundaryInclusion m).app n (x, y))
  simp only [MonoidalClosed.uncurry, tensorLeft_obj, ihom.adjunction, Closed.adj,
    FunctorToTypes.adj, Functor.id_obj, FunctorToTypes.homEquiv_invFun, Monoidal.tensorObj_obj,
    Functor.rightOp_obj, NatTrans.id_app, types_id_apply, FunctorToTypes.homEquiv,
    Equiv.coe_fn_symm_mk, Fin.isValue, whiskerRight_app_apply, whiskerLeft_app_apply, α', β']
  rw [← this]
  simp only [Fin.isValue, MonoidalClosed.pre, internalHom_obj]
  aesop

-- the cocone with point `S` given by uncurrying the maps `α` and `β`
noncomputable
def S_cocone (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    Limits.PushoutCocone (hornInclusion 2 1 ▷ ∂Δ[m]) (Λ[2, 1] ◁ boundaryInclusion m) := by
  refine Limits.PushoutCocone.mk
    (MonoidalClosed.uncurry α) (MonoidalClosed.uncurry β) (S_cocone_aux S m α β sq)

-- induced morphism from pushout to `S` given by `S_cocone`
noncomputable
def to_S (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    (Δ_pushout m).cocone.pt ⟶ S :=
  (Δ_pushout m).isColimit.desc (S_cocone S m sq)

open IsPushout in
-- the new square in `0079`
lemma newSquare (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    CommSq (to_S S m sq) (to_Δ m) S.proj (Δ[2] ⊗ Δ[m]).proj :=
  CommSq.mk (Limits.IsTerminal.hom_ext ptIsTerminal
    ((to_S S m sq) ≫ S.proj) ((to_Δ m) ≫ (Δ[2] ⊗ Δ[m]).proj))

lemma aux1 (S : SSet) (m : ℕ)
    (α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S)
    (β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S)
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β)
    (lift : Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S)
    (fac_left : boundaryInclusion m ≫ lift = α)
    (fac_right : lift ≫ (Fun.map (hornInclusion 2 1).op).app S = β) :
    ∀ (j : Limits.WalkingSpan), (Δ_pushout m).cocone.ι.app j ≫ to_Δ m ≫ MonoidalClosed.uncurry lift =
      (S.S_cocone m sq).ι.app j := by
  intro j
  simp only [Fin.isValue, Functor.const_obj_obj, to_Δ, Δ_cocone, Limits.IsColimit.fac_assoc,
    Limits.PushoutCocone.mk_pt, Limits.PushoutCocone.mk_ι_app, Limits.span_zero, S_cocone]
  rw [← congrArg MonoidalClosed.uncurry fac_left]
  cases j
  · aesop
  · rename_i j
    cases j
    · aesop
    · aesop

lemma aux2 (S : SSet) (m : ℕ)
    (α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S)
    (β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S)
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    ∀ (j : Limits.WalkingSpan), (Δ_pushout m).cocone.ι.app j ≫ S.to_S m sq = (S.S_cocone m sq).ι.app j := by
  intro j
  cases j
  · simp only [Fin.isValue, Limits.span_zero, Functor.const_obj_obj,
    Limits.PushoutCocone.condition_zero, IsPushout.cocone_inl, to_S, S_cocone, Category.assoc,
    Limits.PushoutCocone.mk_pt, Limits.PushoutCocone.mk_ι_app]
    congr 1
    apply Limits.PushoutCocone.IsColimit.inl_desc (Δ_pushout m).isColimit
  · rename_i j
    cases j
    · apply Limits.PushoutCocone.IsColimit.inl_desc (Δ_pushout m).isColimit
    · apply Limits.PushoutCocone.IsColimit.inr_desc (Δ_pushout m).isColimit

/-
lemma newSqLift_of_sqLift (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    sq.HasLift → (newSquare S m sq).HasLift := by
  · intro ⟨lift, fac_left, fac_right⟩
    refine ⟨MonoidalClosed.uncurry lift, ?_, ?_⟩
    · refine ((Δ_pushout m).isColimit.uniq
        (S_cocone S m sq) (to_Δ m ≫ MonoidalClosed.uncurry lift) ?_).trans
        ((Δ_pushout m).isColimit.uniq (S_cocone S m sq) (S.to_S m sq) ?_).symm
      · exact aux1 S m α β sq lift fac_left fac_right
      · exact aux2 S m α β sq
    · exact Limits.IsTerminal.comp_from ptIsTerminal (MonoidalClosed.uncurry lift)
-/

-- awful proof
lemma sqLift_of_newSqLift (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    (newSquare S m sq).HasLift → sq.HasLift := by
  · intro ⟨lift, fac_left, _⟩
    have S' := (Δ_pushout m).isColimit.uniq (S_cocone S m sq) (to_S S m sq) (aux2 S m α β sq)
    have Δ' := (Δ_pushout m).isColimit.uniq (Δ_cocone m) (to_Δ m) (by simp only [Fin.isValue,
      Δ_cocone, Limits.PushoutCocone.mk_pt, Functor.const_obj_obj, to_Δ, Limits.IsColimit.fac,
      Limits.PushoutCocone.mk_ι_app, Limits.span_zero, implies_true])
    refine ⟨MonoidalClosed.curry lift, ?_, ?_⟩
    all_goals apply_fun MonoidalClosed.uncurry
    · simp only [uncurry_natural_left, uncurry_curry]
      have := Limits.PushoutCocone.IsColimit.inl_desc (Δ_pushout m).isColimit _ _
        (S_cocone_aux S m α β sq)
      change (Δ_pushout m).cocone.inl ≫ (Δ_pushout m).isColimit.desc (S.S_cocone m sq) = _ at this
      have L := Limits.PushoutCocone.IsColimit.inl_desc (Δ_pushout m).isColimit
        (Δ[2] ◁ boundaryInclusion m) (hornInclusion 2 1 ▷ Δ[m]) rfl
      change (Δ_pushout m).cocone.inl ≫ (Δ_pushout m).isColimit.desc (Δ_cocone m) = _ at L
      rw [← this, ← S', ← fac_left, Δ', ← Category.assoc, L]
    · have := Limits.PushoutCocone.IsColimit.inr_desc (Δ_pushout m).isColimit _ _
        (S_cocone_aux S m α β sq)
      change (Δ_pushout m).cocone.inr ≫ (Δ_pushout m).isColimit.desc (S.S_cocone m sq) = _ at this
      have L := Limits.PushoutCocone.IsColimit.inr_desc (Δ_pushout m).isColimit
        (Δ[2] ◁ boundaryInclusion m) (hornInclusion 2 1 ▷ Δ[m]) rfl
      change (Δ_pushout m).cocone.inr ≫ (Δ_pushout m).isColimit.desc (Δ_cocone m) = _ at L
      dsimp only [Fin.isValue, internalHom_obj, internalHom_map, Quiver.Hom.unop_op]
      rw [← this, ← S', ← fac_left, Δ', ← Category.assoc, L]
      apply_fun MonoidalClosed.curry
      rfl

-- given a map from the pushout to S, we can recover a commutative square as in `0079`
def newSq (S : SSet) (m : ℕ)
    (f : (Δ_pushout m).cocone.pt ⟶ S) :
  CommSq (MonoidalClosed.curry ((Δ_pushout m).cocone.inl ≫ f))
    (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S)
    (MonoidalClosed.curry ((Δ_pushout m).cocone.inr ≫ f)) := by
  constructor
  apply_fun MonoidalClosed.uncurry
  simp only [Fin.isValue, internalHom_obj, IsPushout.cocone_inl, internalHom_map,
    Quiver.Hom.unop_op, uncurry_natural_left, MonoidalClosed.uncurry_pre, Functor.id_obj,
    IsPushout.cocone_inr, uncurry_curry]
  let inl := Limits.pushout.inl (hornInclusion 2 1 ▷ ∂Δ[m]) (Λ[2, 1] ◁ boundaryInclusion m)
  let inr := Limits.pushout.inr (hornInclusion 2 1 ▷ ∂Δ[m]) (Λ[2, 1] ◁ boundaryInclusion m)
  change Λ[2, 1] ◁ MonoidalClosed.curry (inl ≫ f) ≫
    hornInclusion 2 1 ▷ (ihom Δ[2]).obj S ≫ (ihom.ev Δ[2]).app S =
    Λ[2, 1] ◁ boundaryInclusion m ≫ inr ≫ f
  rw [← Category.assoc, ← Category.assoc, ← (Δ_pushout m).w]
  ext n ⟨x, y⟩
  change (FunctorToTypes.rightAdj_map f n (FunctorToTypes.homEquiv_toFun_app inl n y)).app n (𝟙 n)
    ((hornInclusion 2 1).app n x) =
  f.app n (inl.app n ((hornInclusion 2 1).app n x, y))
  dsimp [FunctorToTypes.rightAdj_map, FunctorToTypes.homEquiv_toFun_app]
  simp only [Fin.isValue, FunctorToTypes.map_id_apply]

-- iff the pushout diagram has an extension, then the square has a lift
lemma newSqLift_of_sqLift (S : SSet) (m : ℕ)
    (f : (Δ_pushout m).cocone.pt ⟶ S)
    (g : Δ[2] ⊗ Δ[m] ⟶ Δ[0])
    (sq : CommSq f (to_Δ m) S.proj g) :
    (newSq S m f).HasLift → sq.HasLift := by
  intro ⟨lift, fac_left, fac_right⟩
  use MonoidalClosed.uncurry lift
  · refine ((Δ_pushout m).isColimit.uniq
      (S_cocone S m ((newSq S m f))) (to_Δ m ≫ MonoidalClosed.uncurry lift) ?_).trans
      ((Δ_pushout m).isColimit.uniq (S_cocone S m (newSq S m f)) f ?_).symm
    · exact aux1 S m (MonoidalClosed.curry ((Δ_pushout m).cocone.inl ≫ f))
        (MonoidalClosed.curry ((Δ_pushout m).cocone.inr ≫ f)) (newSq S m f) lift fac_left fac_right
    · have := aux2 S m (MonoidalClosed.curry ((Δ_pushout m).cocone.inl ≫ f))
        (MonoidalClosed.curry ((Δ_pushout m).cocone.inr ≫ f)) (newSq S m f)
      convert this
      apply (Δ_pushout m).isColimit.uniq (S_cocone S m (newSq S m f)) f
      intro j
      cases j
      all_goals simp only [Fin.isValue, Limits.span_zero, IsPushout.cocone_inl, IsPushout.cocone_inr,
        S_cocone, Limits.PushoutCocone.mk_pt, Functor.const_obj_obj,
        Limits.PushoutCocone.condition_zero, Category.assoc, Limits.PushoutCocone.mk_ι_app,
        uncurry_curry]
      · rename_i j
        cases j
        all_goals simp
  · exact Limits.IsTerminal.hom_ext ptIsTerminal _ _

end _0079

-- `0079`
/- S is a quasicat iff Fun(Δ[2], S) ⟶ Fun(Λ[2, 1], S) is a trivial Kan fib -/
instance horn_tkf_iff_quasicat (S : SSet) : Quasicategory S ↔
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app S) := by
  rw [← quasicat_iff_extension_wrt_innerAnodyne, extension_iff_llp_proj, rlp_wrt]
  have := contains_innerAnodyne_iff_contains_pushout_maps _ (llp_weakly_saturated' S.proj)
  dsimp [llp_wrt'] at this
  rw [← this]
  refine ⟨?_, ?_⟩
  · intro h m
    constructor
    intro α β sq
    exact sqLift_of_newSqLift _ _ _ ((h m).sq_hasLift (newSquare S m sq))
  · intro h m
    constructor
    intro f g sq
    exact (newSqLift_of_sqLift S m f g sq) ((h m).sq_hasLift (newSq S m f))


/- changing the square to apply the lifting property of p
   on the monomorphism `(B ◁ boundaryInclusion n)` -/
lemma induced_tkf_aux (B X Y : SSet) (p : X ⟶ Y)
    (n : ℕ) [h : HasLiftingProperty (B ◁ boundaryInclusion n) p] :
    HasLiftingProperty (boundaryInclusion n) ((Fun.obj (Opposite.op B)).map p) where
  sq_hasLift sq :=
    (CommSq.left_adjoint_hasLift_iff sq (FunctorToTypes.adj B)).1
      (h.sq_hasLift (sq.left_adjoint (Closed.adj)))

-- `0071` (special case of `0070`)
/- if p : X ⟶ Y is a trivial Kan fib, then Fun(B,X) ⟶ Fun(B,Y) is -/
noncomputable
instance induced_tkf (B X Y : SSet) (p : X ⟶ Y) (hp: trivialKanFibration p) :
    trivialKanFibration ((Fun.obj (.op B)).map p) := by
  intro n
  have := (trivialKanFibration_iff_rlp_monomorphisms p).1 hp (boundaryInclusion_whisker_mono B n)
  apply induced_tkf_aux

-- uses `0071` and `0079`
/- the map Fun(Δ[2], Fun(S, D)) ⟶ Fun(Λ[2,1], Fun(S, D)) is a trivial Kan fib -/
-- apply `ihom_equiv` and `0079`
open MonoidalClosed in
noncomputable
def fun_quasicat_aux (S D : SSet) [Quasicategory D] :
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (.op S)).obj D)) := by
  intro n
  -- since Fun[Δ[n], D] ⟶ Fun[Λ[2,1], D] is a TKF by `0079`,
  -- get Fun(S, Fun(Δ[n], D)) ⟶ Fun(S, Fun(Λ[2,1], D)) is a TKF by `0071`
  have := (horn_tkf_iff_quasicat D).1 (by infer_instance)
  have := (induced_tkf S _ _ ((Fun.map (hornInclusion 2 1).op).app D)) this n
  dsimp at this
  have H : Arrow.mk ((ihom S).map ((MonoidalClosed.pre (hornInclusion 2 1)).app D)) ≅
      Arrow.mk ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (Opposite.op S)).obj D)) :=
    CategoryTheory.Comma.isoMk (ihom_iso' _ _ _) (ihom_iso' _ _ _)
  exact HasLiftingProperty.of_arrow_iso_right (boundaryInclusion n) H


-- what can be said for more general filling conditions?
-- `0066`
/- if D is a quasicat, then Fun(S, D) is -/
instance fun_quasicat (S D : SSet) [Quasicategory D] : Quasicategory ((Fun.obj (.op S)).obj D) :=
  -- instance inferred by `fun_quasicat_aux`
  (horn_tkf_iff_quasicat ((Fun.obj (.op S)).obj D)).2 (fun_quasicat_aux S D)

end SSet
