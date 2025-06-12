import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Quasicategory.TopCatModelCategory.SSet.Monoidal

/-!

Some isomorphisms of internal homs, used in `0066`.

-/

open CategoryTheory Simplicial MonoidalCategory MonoidalClosed

namespace SSet

instance : MonoidalClosed SSet := by infer_instance

noncomputable
abbrev Fun : SSetᵒᵖ ⥤ SSet ⥤ SSet := internalHom

open FunctorToTypes

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simps]
noncomputable
def zeroMul {I : SSet} (t : Limits.IsInitial I) : A ⊗ I ≅ I where
  hom := prod.snd
  inv := t.to _
  hom_inv_id := by
    have : (prod.snd : A ⊗ I ⟶ I) = MonoidalClosed.uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _

instance prod.mono_lift_of_mono_left {W X Y : SSet} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _

instance prod.mono_lift_of_mono_right {W X Y : SSet} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _

theorem strict_initial {A I : SSet} (t : Limits.IsInitial I) (f : A ⟶ I) : IsIso f := by
  haveI : Mono (prod.lift (𝟙 A) f ≫ (zeroMul t).hom) := mono_comp _ _
  rw [zeroMul_hom, prod.lift_snd] at this
  haveI : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi

theorem initial_mono {I : SSet} (B : SSet) (t : Limits.IsInitial I) : Mono (t.to B) :=
  ⟨fun g h _ => by
    haveI := strict_initial t g
    haveI := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

noncomputable section

@[ext]
lemma ihom_ext (Y Z : SSet) (n : SimplexCategoryᵒᵖ)
    (a b : (((ihom Y).obj Z)).obj n) : a.app = b.app → a = b := fun h ↦ by
  apply Functor.functorHom_ext
  intro m f; exact congr_fun (congr_fun h m) f

@[ext]
lemma ihom_ihom_ext (X Y Z : SSet) (n : SimplexCategoryᵒᵖ)
    (a b : ((ihom X).obj ((ihom Y).obj Z)).obj n) : a.app = b.app → a = b := fun h ↦ by
  apply Functor.functorHom_ext
  intro m f; exact congr_fun (congr_fun h m) f

def ihom_iso_hom (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ⟶ (ihom (X ⊗ Y)).obj Z where
  app := fun n x ↦ by
    refine ⟨fun m f ⟨Xm, Ym⟩ ↦ (x.app m f Xm).app m (𝟙 m) Ym, ?_⟩
    · intro m l f g
      ext ⟨Xm, Ym⟩
      change
        (x.app l (g ≫ f) (X.map f Xm)).app l (𝟙 l) (Y.map f Ym) =
          Z.map f ((x.app m g Xm).app m (𝟙 m) Ym)
      have := (congr_fun (x.naturality f g) Xm)
      simp at this
      rw [this]
      exact congr_fun ((x.app m g Xm).naturality f (𝟙 m)) Ym

def ihom_iso_inv (X Y Z : SSet) : (ihom (X ⊗ Y)).obj Z ⟶ (ihom X).obj ((ihom Y).obj Z) where
  app := fun n x ↦ by
    refine ⟨?_, ?_⟩
    · intro m f Xm
      refine ⟨fun l g Yl ↦ x.app l (f ≫ g) (X.map g Xm, Yl), ?_⟩
      · intro l k g h
        ext Yl
        have := congr_fun (x.naturality g (f ≫ h)) (X.map h Xm, Yl)
        simp at this ⊢
        exact this
    · intro m l f g
      ext
      simp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.functorHom, Functor.homObjFunctor]

/- [X, [Y, Z]] ≅ [X ⊗ Y, Z] -/
def ihom_iso (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom (X ⊗ Y)).obj Z where
  hom := ihom_iso_hom X Y Z
  inv := ihom_iso_inv X Y Z
  hom_inv_id := by
    ext n x m f Xm l g Yl
    change (x.app l (f ≫ g) (X.map g Xm)).app l (𝟙 l) Yl = (x.app m f Xm).app l g Yl
    have := congr_fun (x.naturality g f) Xm
    dsimp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.functorHom,
      Functor.homObjFunctor] at this
    rw [this]
    aesop
  inv_hom_id := by
    ext n x m f ⟨Xm, Ym⟩
    change ((X.ihom_iso_hom Y Z).app n ((X.ihom_iso_inv Y Z).app n x)).app m f (Xm, Ym) =
      x.app m f (Xm, Ym)
    simp [ihom_iso_hom, ihom_iso_inv]

@[simp]
lemma ihom_braid_hom_eq {X Y Z : SSet} {n m : SimplexCategoryᵒᵖ} {f : n ⟶ m}
    (a : ((ihom (Y ⊗ X)).obj Z).obj n) :
    (((MonoidalClosed.pre (β_ X Y).hom).app Z).app n a).app m f =
      (β_ X Y).hom.app m ≫ a.app m f := by
  ext ⟨Xm, Ym⟩
  change (((Y ⊗ X).functorHom Z).map f a).app m (𝟙 m) (Ym, Xm) = a.app m f (Ym, Xm)
  simp [Functor.functorHom]

@[simp]
lemma ihom_braid_inv_eq {X Y Z : SSet} {n m : SimplexCategoryᵒᵖ} {f : n ⟶ m}
    (a : ((ihom (X ⊗ Y)).obj Z).obj n) :
    (((MonoidalClosed.pre (β_ X Y).inv).app Z).app n a).app m f = (β_ X Y).inv.app m ≫ a.app m f := by
  ext ⟨Ym, Xm⟩
  change (((X ⊗ Y).functorHom Z).map f a).app m (𝟙 m) (Xm, Ym) = a.app m f (Xm, Ym)
  simp [Functor.functorHom]

/- [X ⊗ Y, Z] ≅ [Y ⊗ X, Z] -/
def ihom_braid_iso (X Y Z : SSet) : (ihom (X ⊗ Y)).obj Z ≅ (ihom (Y ⊗ X)).obj Z where
  hom := (MonoidalClosed.pre (β_ X Y).inv).app Z
  inv := (MonoidalClosed.pre (β_ X Y).hom).app Z
  hom_inv_id := by
    ext n x m f ⟨Xm, Ym⟩
    change ((
      (MonoidalClosed.pre (β_ X Y).hom).app Z).app n
      (((MonoidalClosed.pre (β_ X Y).inv).app Z).app n x)).app m f (Xm, Ym) = _
    rw [ihom_braid_hom_eq, ihom_braid_inv_eq]
    rfl
  inv_hom_id := by
    ext n x m f ⟨Ym, Xm⟩
    change ((
      (MonoidalClosed.pre (β_ X Y).inv).app Z).app n
      (((MonoidalClosed.pre (β_ X Y).hom).app Z).app n x)).app m f (Ym, Xm) = _
    rw [ihom_braid_inv_eq, ihom_braid_hom_eq]
    rfl

/- [X, [Y, Z]] ≅ [X ⊗ Y, Z] ≅ [Y ⊗ X, Z] ≅ [Y, [X, Z]] -/
def ihom_iso' (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom Y).obj ((ihom X).obj Z) :=
  (ihom_iso X Y Z) ≪≫ (ihom_braid_iso X Y Z) ≪≫ (ihom_iso Y X Z).symm

end

end SSet
