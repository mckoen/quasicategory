import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Quasicategory.TopCatModelCategory.SSet.Monoidal

open CategoryTheory Limits Simplicial

universe u

def SimplexCategory.isTerminalZero : IsTerminal ⦋0⦌ := by
  refine IsTerminal.ofUniqueHom (fun _ ↦ const _ ⦋0⦌ 0) ?_
  · apply eq_const_to_zero

def SimplexCategory.isInitialEmpty : IsInitial PEmpty := by
  apply IsInitial.ofUniqueHom (fun _ ↦ PEmpty.elim) (fun _ _ ↦ by ext ⟨⟩)

namespace SSet

def isTerminalZero : IsTerminal (Δ[0] : SSet.{u}) where
  lift S := { app := fun _ _ => ULift.up <| SimplexCategory.isTerminalZero.from _ }
  uniq := by intros ; ext ; apply ULift.ext ; apply SimplexCategory.isTerminalZero.hom_ext

@[simp]
def empty : SSet.{u} where
  obj _ := PEmpty.{u + 1}
  map _ := PEmpty.elim

def isInitialEmpty : IsInitial empty.{u} :=
  letI : ∀ (X : SSet), Unique (empty ⟶ X) := fun X ↦ {
    default := { app := fun _ ↦ PEmpty.elim }
    uniq := fun _ ↦ by ext _ ⟨⟩}
  IsInitial.ofUnique _

open MonoidalCategory MonoidalClosed FunctorToTypes

/- everything below is taken from Mathlib.CategoryTheory.Closed.Cartesian -/

/-- `A ⨯ I ≅ I`. -/
@[simps]
noncomputable
def zeroMul {A I : SSet} (t : IsInitial I) : A ⊗ I ≅ I where
  hom := prod.snd
  inv := t.to _
  hom_inv_id := by
    have : (prod.snd : A ⊗ I ⟶ I) = MonoidalClosed.uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _

noncomputable
def mulZero {I A : SSet} (t : IsInitial I) : I ⊗ A ≅ I :=
  β_ _ _ ≪≫ zeroMul t

noncomputable
def powZero {I B : SSet} (t : IsInitial I) : (ihom I).obj B ≅ Δ[0] where
  hom := isTerminalZero.from _
  inv := curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi (mulZero t).inv]
    apply t.hom_ext

instance prod.mono_lift_of_mono_left {W X Y : SSet} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (FunctorToTypes.prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _

instance prod.mono_lift_of_mono_right {W X Y : SSet} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (FunctorToTypes.prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _

theorem strict_initial {A I : SSet} (t : Limits.IsInitial I) (f : A ⟶ I) : IsIso f := by
  haveI : Mono (FunctorToTypes.prod.lift (𝟙 A) f ≫ (zeroMul t).hom) := mono_comp _ _
  rw [zeroMul_hom, FunctorToTypes.prod.lift_snd] at this
  haveI : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi

theorem initial_mono {I : SSet} (B : SSet) (t : Limits.IsInitial I) : Mono (t.to B) :=
  ⟨fun g h _ => by
    haveI := strict_initial t g
    haveI := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

instance to_initial_isIso  (f : A ⟶ ⊥_ SSet) : IsIso f :=
  strict_initial initialIsInitial _

instance Initial.mono_to (B : SSet) : Mono (initial.to B) :=
  initial_mono B initialIsInitial

instance : InitialMonoClass SSet where
  isInitial_mono_from := initial_mono

end SSet
