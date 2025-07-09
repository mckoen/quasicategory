import Quasicategory._007F

universe w

namespace SSet

open CategoryTheory Simplicial MorphismProperty MonoidalCategory MonoidalClosed

open PushoutProduct

variable {S : SSet} {m : ℕ}
  (α : ∂Δ[m].toSSet ⟶ (ihom Δ[2]).obj S) (β : Δ[m] ⟶ (ihom Λ[2, 1].toSSet).obj S)

lemma commSq_uncurry (sq : CommSq α ∂Δ[m].ι ((internalHom.map Λ[2, 1].ι.op).app S) β) :
    CommSq (Λ[2, 1].ι ▷ ∂Δ[m]) (Λ[2, 1].toSSet ◁ ∂Δ[m].ι)
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
  CommSq.mk (isTerminalZero.hom_ext
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
  refine ⟨MonoidalClosed.uncurry lift, ?_, isTerminalZero.hom_ext _ _⟩
  apply Limits.pushout.hom_ext
  · apply_fun curry
    simpa [curry_natural_left]
  · apply_fun curry
    dsimp [PushoutProduct.inr] at fac_right
    simp [← fac_right, curry_eq_iff]
    rfl

-- `0079`
/- S is a quasicat iff Fun(Δ[2], S) ⟶ Fun((Λ[2, 1] : SSet), S) is a trivial Kan fib -/
instance horn_tkf_iff_quasicat (S : SSet) : Quasicategory S ↔
    trivialFibration ((internalHom.map Λ[2, 1].ι.op).app S) := by
  rw [← quasicat_iff_extension_wrt_innerAnodyne, extension_iff_rlp_proj, morphism_rlp_iff,
    ← contains_innerAnodyne_iff_contains_pushout_maps]
  constructor
  · intro h _ _ _ ⟨m⟩
    constructor
    intro α β sq
    exact sqLift_of_newSqLift α β sq ((h _ (.mk m) _ ⟨⟩).sq_hasLift (newSquare _ _ sq))
  · intro h _ _ _ ⟨m⟩ _ _ _ ⟨⟩
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
instance induced_tkf (B X Y : SSet) (p : X ⟶ Y) (hp: trivialFibration p) :
    trivialFibration ((internalHom.obj (.op B)).map p) := by
  intro _ _ i ⟨n⟩
  rw [trivialFibration_eq_rlp_monomorphisms] at hp
  have := hp _ (boundaryInclusion_whisker_mono B n)
  apply induced_tkf_aux

/- the map Fun(Δ[2], Fun(S, D)) ⟶ Fun(Λ[2,1], Fun(S, D)) is a trivial Kan fib -/
open MonoidalClosed in
def aux (S D : SSet) [Quasicategory D] :
    trivialFibration ((internalHom.map Λ[2, 1].ι.op).app ((internalHom.obj (.op S)).obj D)) := by
  intro _ _ i ⟨n⟩
  have := (horn_tkf_iff_quasicat D).1 (by infer_instance)
  have := (induced_tkf S _ _ ((internalHom.map Λ[2, 1].ι.op).app D)) this _ (.mk n)
  dsimp at this
  have H : Arrow.mk ((ihom S).map ((MonoidalClosed.pre Λ[2, 1].ι).app D)) ≅
      Arrow.mk ((internalHom.map Λ[2, 1].ι.op).app ((internalHom.obj (.op S)).obj D)) :=
    CategoryTheory.Comma.isoMk (ihom_iso' _ _ _) (ihom_iso' _ _ _)
  exact HasLiftingProperty.of_arrow_iso_right ∂Δ[n].ι H

instance internalHom_isQuasicategory (S D : SSet) [Quasicategory D] :
    Quasicategory ((internalHom.obj (.op S)).obj D) :=
  (horn_tkf_iff_quasicat _).2 (aux S D)

end SSet
