import Quasicategory._007F

/-!

The main result, `0066`.

Every proof here should be redone (and everything should be seriously reworked).

-/

universe w

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory MonoidalClosed

open PushoutProduct

section _0079

variable {S : SSet} {m : ℕ}
  (α : (∂Δ[m] : SSet) ⟶ (ihom Δ[2]).obj S) (β : Δ[m] ⟶ (ihom (Λ[2, 1] : SSet)).obj S)

lemma commSq_uncurry (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    CommSq (Λ[2, 1].ι ▷ ∂Δ[m]) ((Λ[2, 1] : SSet) ◁ ∂Δ[m].ι)
      (MonoidalClosed.uncurry α) (MonoidalClosed.uncurry β) := by
  constructor
  dsimp [MonoidalClosed.uncurry, Adjunction.homEquiv]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← Category.assoc, ← whisker_exchange, ← sq.w]
  rfl

-- induced morphism from pushout to `S` given by `S_cocone`
noncomputable
def to_S
    (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    (PushoutProduct.pt ∂Δ[m].ι Λ[2, 1].ι) ⟶ S :=
  PushoutProduct.desc _ _ (MonoidalClosed.uncurry α) (MonoidalClosed.uncurry β) (commSq_uncurry α β sq).w

-- the new square in `0079`
lemma newSquare
    (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    CommSq (to_S α β sq) (∂Δ[m].ι ◫ Λ[2, 1].ι) S.proj (Δ[2] ⊗ Δ[m]).proj :=
  CommSq.mk (Limits.IsTerminal.hom_ext isTerminal
    ((to_S α β sq) ≫ S.proj) ((∂Δ[m].ι ◫ Λ[2, 1].ι) ≫ (Δ[2] ⊗ Δ[m]).proj))

lemma sqLift_of_newSqLift
    (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    (newSquare α β sq).HasLift → sq.HasLift := by
  intro ⟨lift, fac_left, _⟩
  refine ⟨curry lift, ?_, ?_⟩
  · apply_fun uncurry
    rw [uncurry_natural_left, uncurry_curry]
    apply_fun (fun f ↦ (PushoutProduct.inl ∂Δ[m].ι Λ[2, 1].ι) ≫ f) at fac_left
    simp [to_S] at fac_left
    assumption
  · apply_fun uncurry
    rw [uncurry_natural_left]
    apply_fun (fun f ↦ (PushoutProduct.inr ∂Δ[m].ι Λ[2, 1].ι) ≫ f) at fac_left
    simp [to_S] at fac_left
    simp [← fac_left, whisker_exchange_assoc]

-- given a map from the pushout to S, we can recover a commutative square as in `0079`
def newSq
    (f : (PushoutProduct.pt ∂Δ[m].ι Λ[2, 1].ι) ⟶ S) :
  CommSq (MonoidalClosed.curry ((PushoutProduct.inl ∂Δ[m].ι Λ[2, 1].ι) ≫ f))
    ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S)
    (MonoidalClosed.curry ((PushoutProduct.inr ∂Δ[m].ι Λ[2, 1].ι) ≫ f)) := by
  constructor
  apply_fun uncurry
  simp [uncurry_natural_left, internalHom_map, uncurry_pre, uncurry_natural_left, whisker_exchange_assoc]
  exact Limits.pushout.condition_assoc f

-- iff the pushout diagram has an extension, then the square has a lift
lemma newSqLift_of_sqLift (S : SSet) (m : ℕ)
    (f : PushoutProduct.pt ∂Δ[m].ι Λ[2, 1].ι ⟶ S)
    (g : Δ[2] ⊗ Δ[m] ⟶ Δ[0])
    (sq : CommSq f (∂Δ[m].ι ◫ Λ[2, 1].ι) S.proj g) :
    (newSq f).HasLift → sq.HasLift := by
  intro ⟨lift, fac_left, fac_right⟩
  refine ⟨MonoidalClosed.uncurry lift, ?_, Limits.IsTerminal.hom_ext isTerminal _ _⟩
  apply (IsPushout ∂Δ[m].ι Λ[2, 1].ι).hom_ext
  · apply_fun curry
    simpa [curry_natural_left]
  · apply_fun curry
    dsimp [PushoutProduct.inr] at fac_right
    simp [← fac_right, curry_eq_iff]
    rfl

end _0079

-- `0079`
/- S is a quasicat iff Fun(Δ[2], S) ⟶ Fun((Λ[2, 1] : SSet), S) is a trivial Kan fib -/
instance horn_tkf_iff_quasicat (S : SSet) : Quasicategory S ↔
    trivialKanFibration ((internalHom.map Λ[2, 1].ι.op).app S) := by
  rw [← quasicat_iff_extension_wrt_innerAnodyne, extension_iff_rlp_proj, class_rlp_iff_llp_morphism]
  have := contains_innerAnodyne_iff_contains_pushout_maps _ (llp.WeaklySaturated (MorphismClass S.proj))
  rw [← this]
  refine ⟨?_, ?_⟩
  · intro h _ _ p hp
    induction hp with | mk m =>
    constructor
    intro α β sq
    exact sqLift_of_newSqLift _ _ _ ((h m _ .mk).sq_hasLift (newSquare _ _ sq))
  · intro h m _ _ p hp
    induction hp
    constructor
    intro f g sq
    exact (newSqLift_of_sqLift S m f g sq) ((h _ (.mk m)).sq_hasLift (newSq f))

/- changing the square to apply the lifting property of p
   on the monomorphism `(B ◁ boundaryInclusion n)` -/
lemma induced_tkf_aux (B X Y : SSet) (p : X ⟶ Y)
    (n : ℕ) [h : HasLiftingProperty (B ◁ ∂Δ[n].ι) p] :
    HasLiftingProperty ∂Δ[n].ι ((internalHom.obj (.op B)).map p) where
  sq_hasLift sq :=
    (CommSq.left_adjoint_hasLift_iff sq (FunctorToTypes.adj B)).1
      (h.sq_hasLift (sq.left_adjoint (Closed.adj)))

-- `0071` (special case of `0070`)
/- if p : X ⟶ Y is a trivial Kan fib, then Fun(B,X) ⟶ Fun(B,Y) is -/
noncomputable
instance induced_tkf (B X Y : SSet) (p : X ⟶ Y) (hp: trivialKanFibration p) :
    trivialKanFibration ((internalHom.obj (.op B)).map p) := by
  intro _ _ i hi
  induction hi with | mk n =>
  rw [trivialKanFibration_eq_rlp_monomorphisms] at hp
  have := hp _ (boundaryInclusion_whisker_mono B n)
  apply induced_tkf_aux

-- uses `0071` and `0079`
/- the map Fun(Δ[2], Fun(S, D)) ⟶ Fun(Λ[2,1], Fun(S, D)) is a trivial Kan fib -/
-- apply `ihom_equiv` and `0079`
open MonoidalClosed in
noncomputable
def fun_quasicat_aux (S D : SSet) [Quasicategory D] :
    trivialKanFibration ((internalHom.map Λ[2, 1].ι.op).app ((internalHom.obj (.op S)).obj D)) := by
  intro _ _ i hi
  induction hi with | mk n =>
  -- since Fun[Δ[n], D] ⟶ Fun[Λ[2,1], D] is a TKF by `0079`,
  -- get Fun(S, Fun(Δ[n], D)) ⟶ Fun(S, Fun(Λ[2,1], D)) is a TKF by `0071`
  have := (horn_tkf_iff_quasicat D).1 (by infer_instance)
  have := (induced_tkf S _ _ ((internalHom.map Λ[2, 1].ι.op).app D)) this _ (.mk n)
  dsimp at this
  have H : Arrow.mk ((ihom S).map ((MonoidalClosed.pre Λ[2, 1].ι).app D)) ≅
      Arrow.mk ((internalHom.map Λ[2, 1].ι.op).app ((internalHom.obj (.op S)).obj D)) :=
    CategoryTheory.Comma.isoMk (ihom_iso' _ _ _) (ihom_iso' _ _ _)
  exact HasLiftingProperty.of_arrow_iso_right ((boundary n).ι) H

-- `0066`
/- if D is a quasicat, then Fun(S, D) is -/
instance fun_quasicat (S D : SSet) [Quasicategory D] : Quasicategory ((Fun.obj (.op S)).obj D) :=
  -- instance inferred by `fun_quasicat_aux`
  (horn_tkf_iff_quasicat ((internalHom.obj (.op S)).obj D)).2 (fun_quasicat_aux S D)

end SSet
