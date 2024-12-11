import Quasicategory._007F

/-!

The main result, `0066`. Every proof here should be redone.

-/

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory MonoidalClosed

section _0079

def Δ_pushout (m : ℕ) :=
  pushoutProduct.IsPushout (boundaryInclusion m) (hornInclusion 2 1)

noncomputable
def Δ_cocone (m : ℕ) :
    Limits.PushoutCocone (hornInclusion 2 1 ▷ ∂Δ[m]) (Λ[2, 1] ◁ (boundaryInclusion m)) :=
  Limits.PushoutCocone.mk (Δ[2] ◁ (boundaryInclusion m)) (hornInclusion 2 1 ▷ Δ[m]) rfl

noncomputable
def Δ_pushoutProduct (m : ℕ) : (Δ_pushout m).cocone.pt ⟶ Δ[2] ⊗ Δ[m] :=
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
  simp only [MonoidalClosed.uncurry, tensorLeft_obj, Adjunction.homEquiv, Functor.comp_obj,
    ihom.adjunction, Closed.adj, FunctorToTypes.adj, FunctorToTypes.rightAdj,
    FunctorToTypes.functorHomEquiv, Functor.homObjEquiv, Monoidal.tensorObj_obj,
    Equiv.invFun_as_coe, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, NatTrans.id_app,
    types_id_apply, Equiv.trans_apply, Equiv.coe_fn_mk, Functor.functorHomEquiv_apply_app,
    Functor.rightOp_obj, tensorLeft_map, Fin.isValue, whiskerRight_app_apply, whiskerLeft_app_apply,
    α', β']
  change _ = (β.app n ((boundaryInclusion m).app n y)).app n (𝟙 n) x
  rw [← this]
  rfl

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
    CommSq (to_S S m sq) (Δ_pushoutProduct m) S.proj (Δ[2] ⊗ Δ[m]).proj :=
  CommSq.mk (Limits.IsTerminal.hom_ext isTerminal
    ((to_S S m sq) ≫ S.proj) ((Δ_pushoutProduct m) ≫ (Δ[2] ⊗ Δ[m]).proj))

lemma aux1 (S : SSet) (m : ℕ)
    (α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S)
    (β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S)
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β)
    (lift : Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S)
    (fac_left : boundaryInclusion m ≫ lift = α)
    (fac_right : lift ≫ (Fun.map (hornInclusion 2 1).op).app S = β) :
    ∀ (j : Limits.WalkingSpan), (Δ_pushout m).cocone.ι.app j ≫ Δ_pushoutProduct m ≫ MonoidalClosed.uncurry lift =
      (S.S_cocone m sq).ι.app j := by
  intro j
  simp only [Fin.isValue, Functor.const_obj_obj, Δ_pushoutProduct, Δ_cocone, Limits.IsColimit.fac_assoc,
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
        (S_cocone S m sq) (Δ_pushoutProduct m ≫ MonoidalClosed.uncurry lift) ?_).trans
        ((Δ_pushout m).isColimit.uniq (S_cocone S m sq) (S.to_S m sq) ?_).symm
      · exact aux1 S m α β sq lift fac_left fac_right
      · exact aux2 S m α β sq
    · exact Limits.IsTerminal.comp_from isTerminal (MonoidalClosed.uncurry lift)
-/

-- awful proof
lemma sqLift_of_newSqLift (S : SSet) (m : ℕ)
    {α : ∂Δ[m] ⟶ (Fun.obj (Opposite.op Δ[2])).obj S}
    {β : Δ[m] ⟶ (Fun.obj (Opposite.op Λ[2, 1])).obj S}
    (sq : CommSq α (boundaryInclusion m) ((Fun.map (hornInclusion 2 1).op).app S) β) :
    (newSquare S m sq).HasLift → sq.HasLift := by
  · intro ⟨lift, fac_left, _⟩
    have S' := (Δ_pushout m).isColimit.uniq (S_cocone S m sq) (to_S S m sq) (aux2 S m α β sq)
    have Δ' := (Δ_pushout m).isColimit.uniq (Δ_cocone m) (Δ_pushoutProduct m) (by simp only [Fin.isValue,
      Δ_cocone, Limits.PushoutCocone.mk_pt, Functor.const_obj_obj, Δ_pushoutProduct, Limits.IsColimit.fac,
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
  change _ = f.app n (inl.app n ((hornInclusion 2 1).app n x, y))
  simp [MonoidalClosed.curry, Adjunction.homEquiv, ihom]
  change (((ihom.adjunction Δ[2]).counit).app S).app
    n ((((hornInclusion 2 1).app n x, ((Closed.rightAdj Δ[2]).map f).app n (((Closed.rightAdj Δ[2]).map inl).app n (((ihom.adjunction Δ[2]).unit.app ∂Δ[m]).app n y) )))) = _
  simp only [Functor.id_obj, Functor.comp_obj, tensorLeft_obj, ihom.adjunction, Closed.adj,
    FunctorToTypes.adj, Equiv.invFun_as_coe, Fin.isValue, Closed.rightAdj,
    FunctorToTypes.functorHomEquiv_apply_app, NatTrans.id_app, FunctorToTypes.rightAdj_obj_obj,
    types_id_apply, FunctorToTypes.rightAdj_map_app_app,
    FunctorToTypes.functorHomEquiv_symm_apply_app_app, FunctorToTypes.map_id_apply,
    Monoidal.tensorObj_obj]

-- iff the pushout diagram has an extension, then the square has a lift
lemma newSqLift_of_sqLift (S : SSet) (m : ℕ)
    (f : (Δ_pushout m).cocone.pt ⟶ S)
    (g : Δ[2] ⊗ Δ[m] ⟶ Δ[0])
    (sq : CommSq f (Δ_pushoutProduct m) S.proj g) :
    (newSq S m f).HasLift → sq.HasLift := by
  intro ⟨lift, fac_left, fac_right⟩
  use MonoidalClosed.uncurry lift
  · refine ((Δ_pushout m).isColimit.uniq
      (S_cocone S m ((newSq S m f))) (Δ_pushoutProduct m ≫ MonoidalClosed.uncurry lift) ?_).trans
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
  · exact Limits.IsTerminal.hom_ext isTerminal _ _

end _0079

-- `0079`
/- S is a quasicat iff Fun(Δ[2], S) ⟶ Fun(Λ[2, 1], S) is a trivial Kan fib -/
instance horn_tkf_iff_quasicat (S : SSet.{0}) : Quasicategory S ↔
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app S) := by
  rw [← quasicat_iff_extension_wrt_innerAnodyne, extension_iff_rlp_proj, class_rlp_iff_llp_morphism]
  have := contains_innerAnodyne_iff_contains_pushout_maps _ (llp.WeaklySaturated (MorphismClass S.proj))
  rw [← this]
  refine ⟨?_, ?_⟩
  · intro h _ _ p hp
    induction hp with | mk m =>
    constructor
    intro α β sq
    exact sqLift_of_newSqLift _ _ _ ((h m .mk).sq_hasLift (newSquare S m sq))
  · intro h m _ _ p hp
    induction hp
    constructor
    intro f g sq
    exact (newSqLift_of_sqLift S m f g sq) ((h (.mk m)).sq_hasLift (newSq S m f))

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
instance induced_tkf (B X Y : SSet.{0}) (p : X ⟶ Y) (hp: trivialKanFibration p) :
    trivialKanFibration ((Fun.obj (.op B)).map p) := by
  intro _ _ i hi
  induction hi with | mk n =>
  rw [trivialKanFibration_eq_rlp_monomorphisms] at hp
  have := hp (boundaryInclusion_whisker_mono B n)
  apply induced_tkf_aux

-- uses `0071` and `0079`
/- the map Fun(Δ[2], Fun(S, D)) ⟶ Fun(Λ[2,1], Fun(S, D)) is a trivial Kan fib -/
-- apply `ihom_equiv` and `0079`
open MonoidalClosed in
noncomputable
def fun_quasicat_aux (S D : SSet.{0}) [Quasicategory D] :
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (.op S)).obj D)) := by
  intro _ _ i hi
  induction hi with | mk n =>
  -- since Fun[Δ[n], D] ⟶ Fun[Λ[2,1], D] is a TKF by `0079`,
  -- get Fun(S, Fun(Δ[n], D)) ⟶ Fun(S, Fun(Λ[2,1], D)) is a TKF by `0071`
  have := (horn_tkf_iff_quasicat D).1 (by infer_instance)
  have := (induced_tkf S _ _ ((Fun.map (hornInclusion 2 1).op).app D)) this (.mk n)
  dsimp at this
  have H : Arrow.mk ((ihom S).map ((MonoidalClosed.pre (hornInclusion 2 1)).app D)) ≅
      Arrow.mk ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (Opposite.op S)).obj D)) :=
    CategoryTheory.Comma.isoMk (ihom_iso' _ _ _) (ihom_iso' _ _ _)
  exact HasLiftingProperty.of_arrow_iso_right (boundaryInclusion n) H

-- what can be said for more general filling conditions?
-- `0066`
/- if D is a quasicat, then Fun(S, D) is -/
instance fun_quasicat (S D : SSet.{0}) [Quasicategory D] : Quasicategory ((Fun.obj (.op S)).obj D) :=
  -- instance inferred by `fun_quasicat_aux`
  (horn_tkf_iff_quasicat ((Fun.obj (.op S)).obj D)).2 (fun_quasicat_aux S D)

end SSet
