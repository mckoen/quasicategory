import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.PushoutProduct

section

variable {A B X Y : SSet} (f : A ⟶ B) (g : X ⟶ Y)

@[simp]
def IsPushout := IsPushout.of_hasPushout (g ▷ A) (X ◁ f)

@[simp]
noncomputable
def pt : SSet := pushout (g ▷ A) (X ◁ f)

/-- The pushout-product of `f` and `g`. -/
@[simp]
noncomputable
def pushoutProduct : pushout (g ▷ A) (X ◁ f) ⟶ Y ⊗ B :=
  (IsPushout f g).desc (Y ◁ f) (g ▷ B) rfl

/-- Notation for the pushout-product. -/
scoped infixr:80 " ◫ " => PushoutProduct.pushoutProduct

@[simp]
noncomputable
abbrev desc {W : SSet} (h : Y ⊗ A ⟶ W) (k : X ⊗ B ⟶ W) (w : g ▷ A ≫ h = X ◁ f ≫ k) :
    pt f g ⟶ W := (IsPushout f g).desc h k w

@[simp]
noncomputable
abbrev inl : Y ⊗ A ⟶ pt f g := (IsPushout f g).cocone.inl

@[simp]
noncomputable
abbrev inr : X ⊗ B ⟶ pt f g := (IsPushout f g).cocone.inr

lemma w : g ▷ A ≫ inl f g = X ◁ f ≫ inr f g  := (IsPushout f g).toCommSq.w

lemma desc_id : (desc f g) (inl f g) (inr f g) (w f g) = 𝟙 (pt f g) :=
  (IsPushout f g).hom_ext (by aesop) (by aesop)

noncomputable
def id_pushoutProduct_iso (W : SSet) : pt (𝟙 W) g ≅ Y ⊗ W :=
  IsPushout.isoIsPushout _ _ (IsPushout (𝟙 W) g) (IsPushout.id_vert (g ▷ W))

noncomputable
def id_pushoutProduct_iso_desc (W : SSet) :
    (id_pushoutProduct_iso g W).inv ≫ (𝟙 W) ◫ g = 𝟙 (Y ⊗ W) := by
  exact (Iso.inv_comp_eq_id (id_pushoutProduct_iso g W)).mpr rfl

end

noncomputable
def pushoutProductRight_map_left {X Y : SSet} (h : X ⟶ Y)
    {A B K L : SSet} (f : A ⟶ B) (g : K ⟶ L)
    {s : A ⟶ K} {t : B ⟶ L} (w : s ≫ g = f ≫ t) :
    (PushoutProduct.pt f h) ⟶ (PushoutProduct.pt g h) := by
  apply pushout.desc (Y ◁ s ≫ (inl g h)) (X ◁ t ≫ (inr g h)) _
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  simp [pushout.condition, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, w]

noncomputable
def pushoutProductRight_map {X Y : SSet} (h : X ⟶ Y)
    {A B K L : SSet} (f : A ⟶ B) (g : K ⟶ L)
    {s : A ⟶ K} {t : B ⟶ L} (w : s ≫ g = f ≫ t) :
    Arrow.mk (f ◫ h) ⟶ Arrow.mk (g ◫ h) where
  left := pushoutProductRight_map_left h f g w
  right := Y ◁ t
  w := by
    refine pushout.hom_ext ?_ ?_
    · simp [pushoutProductRight_map_left, ← MonoidalCategory.whiskerLeft_comp, w]
    · simp [pushoutProductRight_map_left, ← whisker_exchange]

noncomputable
def pushoutProductRight {X Y : SSet} (h : X ⟶ Y) : Arrow SSet.{u} ⥤ Arrow SSet.{u} where
  obj f := f.hom ◫ h
  map {f g} sq := pushoutProductRight_map h f.hom g.hom sq.w
  map_id _ := by
    simp [pushoutProductRight_map, pushoutProductRight_map_left]
    apply Arrow.hom_ext
    · aesop
    · aesop
  map_comp f g := by
    simp [pushoutProductRight_map, pushoutProductRight_map_left]
    apply Arrow.hom_ext
    · aesop
    · aesop

noncomputable
def pushoutProductFunctor : Arrow SSet.{u} ⥤ Arrow SSet.{u} ⥤ Arrow SSet.{u} where
  obj h := pushoutProductRight h.hom
  map {f g} sq := {
    app f' := by
      --simp [pushoutProductRight, pushoutProductRight_map, pushoutProductRight_map_left]
      refine ⟨?_, ?_, ?_⟩
      · dsimp [pushoutProductRight, pushoutProductRight_map, pushoutProductRight_map_left]
        refine pushout.desc ?_ ?_ ?_
        · exact (sq.right ▷ f'.left) ≫ (inl _ _)
        · exact (sq.left ▷ f'.right) ≫ (inr _ _)
        · have := sq.w
          dsimp at this
          rw [← Category.assoc, ← comp_whiskerRight, ← this, comp_whiskerRight, Category.assoc]
          rw [← Category.assoc, ← Category.assoc, whisker_exchange, Category.assoc]
          simp [pushout.condition]
      · exact sq.right ▷ f'.right
      · dsimp only [pushoutProductRight, pushoutProductRight_map, pushoutProductRight_map_left]
        apply pushout.hom_ext
        · sorry
        · sorry
    naturality := by
      intro f' g' sq'
      dsimp only [pushoutProductRight, pushoutProductRight_map, pushoutProductRight_map_left]
      apply Arrow.hom_ext
      · sorry
      · sorry --aesop
  }

section NatTrans

variable {C : Type u} [Category.{v} C] {F G : C ⥤ SSet} (h : F ⟶ G)

variable {X Y : SSet} (g : X ⟶ Y)

@[simp]
noncomputable
def natTransLeftFunctor_map {A B : C} (f : A ⟶ B) : pt (h.app A) g ⟶ pt (h.app B) g := by
  refine (desc (h.app A) g)
    (Y ◁ (F.map f) ≫ inl (h.app B) g) (X ◁ (G.map f) ≫ inr (h.app B) g) ?_
  rw [← Category.assoc (X ◁ _), ← MonoidalCategory.whiskerLeft_comp, ← h.naturality f,
    MonoidalCategory.whiskerLeft_comp, Category.assoc, ← w]
  rfl

@[simp]
lemma natTransLeftFunctor_map_id (A : C) :
    natTransLeftFunctor_map h g (𝟙 A) = 𝟙 (pt (h.app A) g) :=
  (IsPushout (h.app A) g).hom_ext (by aesop) (by aesop)

@[simp]
lemma natTransLeftFunctor_map_comp {X Y Z : C} (s : X ⟶ Y) (t : Y ⟶ Z) :
    natTransLeftFunctor_map h g (s ≫ t) = natTransLeftFunctor_map h g s ≫ natTransLeftFunctor_map h g t := by
  apply (IsPushout (h.app X) g).hom_ext (by aesop) (by aesop)

@[simp]
noncomputable
def natTransLeftFunctor : C ⥤ SSet where
  obj A := pt (h.app A) g
  map := natTransLeftFunctor_map h g
  map_id := natTransLeftFunctor_map_id h g
  map_comp := natTransLeftFunctor_map_comp h g

noncomputable
def natTransLeftFunctor_comp {G' : C ⥤ SSet} (h' : G ⟶ G') :
    (natTransLeftFunctor h g) ⟶ (natTransLeftFunctor (h ≫ h') g) where
  app A := by
    refine (IsPushout (h.app A) g).desc
      (inl ((h ≫ h').app A) g) (X ◁ (h'.app A) ≫ inr ((h ≫ h').app A) g) ?_
    · rw [w]; aesop
  naturality {A _} f := by
    apply (IsPushout (h.app A) g).hom_ext (by aesop)
    simp only [natTransLeftFunctor, NatTrans.comp_app, pt, natTransLeftFunctor_map, desc, inl,
      IsPushout.cocone_inl, inr, IsPushout.cocone_inr, IsPushout.inr_desc_assoc, Category.assoc,
      IsPushout.inr_desc, MonoidalCategory.whiskerLeft_comp]
    rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, h'.naturality]

noncomputable
def inlDescFunctor : (F ⋙ tensorLeft Y) ⟶ (natTransLeftFunctor h g) where
  app A := inl (h.app A) g

noncomputable
def inrDescFunctor : (G ⋙ tensorLeft X) ⟶ (natTransLeftFunctor h g) where
  app A := inr (h.app A) g

/-- very slow :( -/
noncomputable
def descFunctor : (natTransLeftFunctor h g) ⟶ (G ⋙ tensorLeft Y) where
  app A := (h.app A) ◫ g
  naturality A B f := by
    apply (IsPushout (h.app A) g).hom_ext
    · simp_all only [Functor.comp_obj, tensorLeft_obj, natTransLeftFunctor, pt, natTransLeftFunctor_map, desc, inl,
        IsPushout.cocone_inl, inr, IsPushout.cocone_inr, pushoutProduct, IsPushout.inl_desc_assoc, Category.assoc,
        IsPushout.inl_desc, Functor.comp_map, tensorLeft_map]
      ext : 1
      · ext n a : 2
        simp_all only [Category.assoc, ChosenFiniteProducts.whiskerLeft_fst]
      · ext n a : 2
        simp_all only [Category.assoc, ChosenFiniteProducts.whiskerLeft_snd, ChosenFiniteProducts.whiskerLeft_snd_assoc,
          NatTrans.naturality]
    · simp_all only [Functor.comp_obj, tensorLeft_obj, natTransLeftFunctor, pt, natTransLeftFunctor_map, desc, inl,
        IsPushout.cocone_inl, inr, IsPushout.cocone_inr, pushoutProduct, IsPushout.inr_desc_assoc, Category.assoc,
        IsPushout.inr_desc, Functor.comp_map, tensorLeft_map]
      rfl

end NatTrans

section Composition

variable {A B C X Y : SSet} (f : A ⟶ B) (f' : B ⟶ C) (g : X ⟶ Y)

@[simp]
noncomputable
def descComp : pt f g ⟶ pt (f ≫ f') g := desc f g (inl (f ≫ f') g) (X ◁ f' ≫ inr (f ≫ f') g)
  (by rw [w, MonoidalCategory.whiskerLeft_comp, Category.assoc])

@[simp]
noncomputable
def compDesc : pt (f ≫ f') g ⟶ pt f' g := desc (f ≫ f') g (Y ◁ f ≫ inl f' g) (inr f' g)
  (by rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, ← w, ← Category.assoc,
    ← @whisker_exchange, Category.assoc])

lemma compDesc_comp_descComp_eq :
    (descComp f f' g) ≫ (compDesc f f' g) = (f ◫ g) ≫ (inl f' g) := by
  apply (IsPushout f g).hom_ext (by aesop)
  simp only [descComp, compDesc, MonoidalCategory.whiskerLeft_comp, IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc,
    pushoutProduct, w]

noncomputable
def compPushoutCocone := Limits.PushoutCocone.mk (compDesc f f' g) (inl f' g) (compDesc_comp_descComp_eq f f' g)

set_option maxHeartbeats 400000 in
noncomputable
def compPushoutCoconeIsColimit : Limits.IsColimit (compPushoutCocone f f' g) := by
  refine Limits.PushoutCocone.IsColimit.mk _ ?_ ?_ ?_ ?_
  · intro s
    refine (desc f' g) s.inr (inr (f ≫ f') g ≫ s.inl) ?_
    · have := ((inr f g) ≫= s.condition).symm
      simp only [pt, descComp, Limits.PushoutCocone.ι_app_left, IsPushout.cocone_inl,
        Limits.PushoutCocone.ι_app_right, IsPushout.cocone_inr, desc, pushoutProduct, inr,
        IsPushout.inr_desc_assoc, inl, Category.assoc] at this
      exact this
  · intro s
    apply (IsPushout (f ≫ f') g).hom_ext
    · have := ((inl f g) ≫= s.condition).symm
      simp_all only [pt, descComp, Limits.PushoutCocone.ι_app_left, IsPushout.cocone_inl,
        Limits.PushoutCocone.ι_app_right, IsPushout.cocone_inr, desc, pushoutProduct, inl, IsPushout.inl_desc_assoc,
        inr, compDesc, MonoidalCategory.whiskerLeft_comp, Category.assoc, IsPushout.inl_desc]
    · simp_all only [pt, descComp, Limits.PushoutCocone.ι_app_left, IsPushout.cocone_inl,
      Limits.PushoutCocone.ι_app_right, IsPushout.cocone_inr, desc, pushoutProduct, compDesc,
      MonoidalCategory.whiskerLeft_comp, inl, inr, IsPushout.inr_desc_assoc, IsPushout.inr_desc]
  · intro s
    simp only [pt, descComp, Limits.PushoutCocone.ι_app_left, IsPushout.cocone_inl,
      Limits.PushoutCocone.ι_app_right, IsPushout.cocone_inr, desc, pushoutProduct, inl, inr, IsPushout.inl_desc]
  · intro s m h1 h2
    apply (IsPushout f' g).hom_ext (by aesop)
    have := (inr (f ≫ f') g) ≫= h1
    dsimp only [compDesc] at this
    simp only [pt, descComp, Limits.PushoutCocone.ι_app_left, IsPushout.cocone_inl,
      Limits.PushoutCocone.ι_app_right, IsPushout.cocone_inr, desc, pushoutProduct, inr,
      IsPushout.inr_desc]
    change inr f' g ≫ m = inr (f ≫ f') g ≫ s.inl
    rw [← this, ← Category.assoc]
    simp

def compPushout : CategoryTheory.IsPushout (descComp f f' g) (f ◫ g) (compDesc f f' g) (inl f' g) :=
  IsPushout.of_isColimit (compPushoutCoconeIsColimit f f' g)

@[simp]
lemma pushoutProductCompEq : (compDesc f f' g) ≫ (f' ◫ g) = (f ≫ f') ◫ g :=
  (IsPushout (f ≫ f') g).hom_ext (by aesop) (by aesop)

end Composition

end CategoryTheory.PushoutProduct

namespace SSet

open Limits Simplicial PushoutProduct

inductive bdryPushout : {X Y : SSet} → (X ⟶ Y) → Prop
  | mk (m : ℕ) : bdryPushout (∂Δ[m].ι ◫ Λ[2, 1].ι)

/-- the class of pushout products of `∂Δ[m] ↪ Δ[m]` with `Λ[2, 1] ↪ Δ[2]`. -/
def bdryPushoutClass : MorphismProperty SSet := fun _ _ p ↦ bdryPushout p

end SSet
