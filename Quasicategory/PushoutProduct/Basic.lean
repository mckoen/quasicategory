import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Quasicategory.MorphismProperty

universe w v v' u u'

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.PushoutProduct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasPushouts C]

section Defs

variable {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)

@[simp]
noncomputable
abbrev pt : C := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f g).pt

/-- The pushout-product of `f` and `g`. -/
@[simp]
noncomputable
abbrev pushoutProduct : pushout (f ▷ X) (A ◁ g) ⟶ B ⊗ Y :=
  (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f g).ι

/-- Notation for the pushout-product. -/
scoped infixr:80 " □ " => PushoutProduct.pushoutProduct

end Defs

section Functor

variable (h : Arrow C) {f g : Arrow C} (sq : f ⟶ g)

@[simp]
noncomputable
def leftFunctor_map_left  :
    pt h.hom f.hom ⟶ pt h.hom g.hom :=
  pushout.map _ _ _ _
    (h.right ◁ sq.left) (h.left ◁ sq.right) (h.left ◁ sq.left)
    (whisker_exchange _ _).symm (by simp [← MonoidalCategory.whiskerLeft_comp, Arrow.w])

@[simp]
noncomputable
def leftFunctor_map :
    Arrow.mk (h.hom □ f.hom) ⟶ Arrow.mk (h.hom □ g.hom) where
  left := leftFunctor_map_left h sq
  right := h.right ◁ sq.right
  w := by
    dsimp [Functor.PushoutObjObj.ι]
    apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp, Arrow.w]
    · simp [← whisker_exchange]

@[simp]
noncomputable
def leftFunctor : Arrow C ⥤ Arrow C where
  obj f := h.hom □ f.hom
  map := leftFunctor_map h

@[simp]
noncomputable
def leftBifunctor_map_left :
    pt f.hom h.hom ⟶ pt g.hom h.hom :=
  pushout.map _ _ _ _
    (sq.right ▷ h.left) (sq.left ▷ h.right) (sq.left ▷ h.left)
    (by simp [← MonoidalCategory.comp_whiskerRight, Arrow.w]) (whisker_exchange sq.left h.hom)

@[simp]
noncomputable
def leftBifunctor_map :
    leftFunctor f ⟶ leftFunctor g where
  app h := {
    left := leftBifunctor_map_left h sq
    right := sq.right ▷ h.right
    w := by
      dsimp [Functor.PushoutObjObj.ι]
      apply pushout.hom_ext
      · simp [whisker_exchange]
      · simp [← MonoidalCategory.comp_whiskerRight, Arrow.w] }
  naturality f' g' sq' := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext
      all_goals simp [← whisker_exchange_assoc]
    · exact (whisker_exchange _ _)

@[simps!]
noncomputable
def leftBifunctor : Arrow C ⥤ Arrow C ⥤ Arrow C where
  obj := leftFunctor
  map := leftBifunctor_map

end Functor

section NatTrans

variable {D : Type u'} [Category.{v'} D]

variable {F G : D ⥤ C} (h : F ⟶ G)

variable {X Y : C} (g : X ⟶ Y)

@[simps!]
def _root_.CategoryTheory.NatTrans.arrowFunctor : D ⥤ Arrow C where
  obj A := Arrow.mk (h.app A)
  map f := Arrow.homMk' _ _ (h.naturality f)

@[simps]
def _root_.CategoryTheory.NatTrans.arrowFunctor_NatTrans {G' : D ⥤ C} (h' : G ⟶ G') :
    NatTrans.arrowFunctor h ⟶ NatTrans.arrowFunctor (h ≫ h') where
  app X := Arrow.homMk' (𝟙 _) (h'.app X)

@[simps!]
noncomputable
def natTransLeftFunctor : D ⥤ C := NatTrans.arrowFunctor h ⋙ leftFunctor g ⋙ Arrow.leftFunc

@[simp]
noncomputable
def natTransLeftFunctor_comp {G' : D ⥤ C} (h' : G ⟶ G') :
    (natTransLeftFunctor h g) ⟶ (natTransLeftFunctor (h ≫ h') g) :=
  whiskerRight (NatTrans.arrowFunctor_NatTrans h h') _

@[simps!]
noncomputable
def inlDescFunctor : (F ⋙ tensorLeft Y) ⟶ (natTransLeftFunctor h g) where
  app A := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) g (h.app A)).inl

@[simps!]
noncomputable
def inrDescFunctor : (G ⋙ tensorLeft X) ⟶ (natTransLeftFunctor h g) where
  app A := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) g (h.app A)).inr

@[simps!]
noncomputable
def descFunctor : (natTransLeftFunctor h g) ⟶ (G ⋙ tensorLeft Y) where
  app A := g □ h.app A
  naturality _ _ _ := by
    dsimp [Functor.PushoutObjObj.ι]
    apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · simp [whisker_exchange]

end NatTrans

--variable (hp : IsColimit (PushoutCocone.mk _ _ h.w))

section

variable {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y} {s : X ⟶ A} {t : Y ⟶ B}

variable (S : C) [hS : PreservesColimitsOfSize (tensorLeft S)]

def whiskerPushoutAux (s : X ⟶ A) (g : X ⟶ Y) :
    IsPushout (S ◁ s) (S ◁ g) (S ◁ (pushout.inl s g)) (S ◁ (pushout.inr s g)) where
  w := by simp only [← MonoidalCategory.whiskerLeft_comp, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorLeft S) s g⟩

def whiskerPushout (h : IsPushout s g f t) :
    IsPushout (S ◁ s) (S ◁ g) (S ◁ f) (S ◁ t) :=
  (whiskerPushoutAux S s g).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (whiskerLeftIso S h.isoPushout).symm (by simp) (by simp)
    (by simp [← MonoidalCategory.whiskerLeft_comp, IsPushout.inl_isoPushout_inv])
    (by simp [← MonoidalCategory.whiskerLeft_comp, IsPushout.inl_isoPushout_inv])

end

section Pushout

variable {f g : Arrow C} (ι : Arrow C) (h : f ⟶ g) (hp : IsColimit (PushoutCocone.mk _ _ h.w))

variable [hS : ∀ S : C, PreservesColimitsOfSize (tensorLeft S)]

variable (s : PushoutCocone ((leftBifunctor.obj ι).map h).left ((leftBifunctor.obj ι).obj f).hom)

@[simp]
noncomputable
def temp_desc : ((leftFunctor ι).obj g).right ⟶ s.pt :=
  (whiskerPushout ι.right (IsPushout.of_isColimit hp)).desc
    ((pushout.inl _ _) ≫ s.inl) s.inr
    (by simpa [pushout.inr_desc_assoc, Functor.PushoutObjObj.ι] using (pushout.inl _ _) ≫= s.condition)

def temp_fac_left : ((leftFunctor ι).obj g).hom ≫ temp_desc ι h hp s = s.inl := by
  simp [Functor.PushoutObjObj.ι]
  apply pushout.hom_ext
  · simp
  · apply (whiskerPushout _ (IsPushout.of_isColimit hp)).hom_ext
    · simp [← pushout.condition_assoc, whisker_exchange_assoc]
    · simp [whisker_exchange_assoc]
      have := pushout.inr _ _ ≫= s.condition
      simp [Functor.PushoutObjObj.ι] at this
      rw [this]

def temp_uniq (m : ((leftBifunctor.obj ι).obj g).right ⟶ s.pt)
    (fac_left : ((leftBifunctor.obj ι).obj g).hom ≫ m = s.inl)
    (fac_right : ((leftBifunctor.obj ι).map h).right ≫ m = s.inr) : m = temp_desc ι h hp s := by
  apply (whiskerPushout _ (IsPushout.of_isColimit hp)).hom_ext
  · simpa [Functor.PushoutObjObj.ι] using pushout.inl _ _ ≫= fac_left
  · simpa

noncomputable
def leftFunctor_map_preserves_pushouts
      {f g : Arrow C} (ι : Arrow C) (h : f ⟶ g) (hp : IsColimit (PushoutCocone.mk _ _ h.w)) :
    IsColimit (PushoutCocone.mk _ _ ((leftBifunctor.obj ι).map h).w) :=
  PushoutCocone.IsColimit.mk _ (temp_desc ι h hp) (temp_fac_left ι h hp)
    (by simp) (temp_uniq ι h hp)

def leftFunctor_map_preserves_pushouts' {A B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y} {s : X ⟶ A} {t : Y ⟶ B}
      (ι : Z ⟶ W) (h : IsPushout s g f t) :
    IsPushout ((leftBifunctor.obj (Arrow.mk ι)).map (Arrow.homMk' s t h.w)).left
      (ι □ g)
      (ι □ f)
      (W ◁ t) := by
  apply IsPushout.of_isColimit' ⟨((leftBifunctor.obj (Arrow.mk ι)).map (Arrow.homMk' _ _ h.w)).w⟩
  apply leftFunctor_map_preserves_pushouts
  exact h.isColimit

end Pushout

section Transfinite

variable (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

variable {A B X Y : C} {f : A ⟶ B} (ι : X ⟶ Y) (h : TransfiniteCompositionOfShape J f)

variable [hX : PreservesColimitsOfSize (tensorLeft X)] [hY : PreservesColimitsOfSize (tensorLeft Y)]

noncomputable
def temp_isoBot : (natTransLeftFunctor h.incl ι).obj ⊥ ≅ pushout (ι ▷ A) (X ◁ f) := by
  have : Arrow.mk (h.incl.app ⊥) ≅ Arrow.mk f :=
    Arrow.isoMk h.isoBot (Iso.refl _) (by simpa using (h.isoBot.inv_comp_eq.1 h.fac).symm)
  exact Comma.leftIso ((leftFunctor (Arrow.mk ι)).mapIso this)

noncomputable
def temp_isColimit {m : J} (hm : Order.IsSuccLimit m) :
    (IsColimit ((Set.principalSegIio m).cocone (natTransLeftFunctor h.incl ι))) where
  desc := by
    intro s
    refine pushout.desc
      ((isColimitOfPreserves (tensorLeft Y) (h.isWellOrderContinuous.nonempty_isColimit m hm).some).desc <|
        Cocone.mk s.pt ((whiskerLeft ((Set.principalSegIio m).monotone.functor) (inlDescFunctor h.incl ι)) ≫ s.ι))
      (pushout.inr _ _ ≫ s.ι.app ⟨⊥, hm.bot_lt⟩) ?_
    · apply (isColimitOfPreserves (tensorLeft X) (h.isWellOrderContinuous.nonempty_isColimit m hm).some).hom_ext
      intro j
      have h₁ := (s.ι.naturality (homOfLE <| (Subtype.coe_le_coe.mp bot_le : ⟨⊥, hm.bot_lt⟩ ≤ j)))
      have h₂ := ((isColimitOfPreserves (tensorLeft Y) (h.isWellOrderContinuous.nonempty_isColimit m hm).some).fac <|
        Cocone.mk s.pt ((whiskerLeft ((Set.principalSegIio m).monotone.functor) (inlDescFunctor h.incl ι)) ≫ s.ι)) j
      simp only [Functor.comp_obj, Monotone.functor_obj, Set.principalSegIio_toRelEmbedding,
        natTransLeftFunctor_obj, Functor.const_obj_obj, homOfLE_leOfHom, Functor.comp_map,
        natTransLeftFunctor_map, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id,
        Category.comp_id, tensorLeft_obj, Functor.mapCocone_pt, PrincipalSeg.cocone_pt,
        Set.principalSegIio_top, Functor.mapCocone_ι_app, PrincipalSeg.cocone_ι_app, tensorLeft_map,
        NatTrans.comp_app, whiskerLeft_app, inlDescFunctor_app] at h₁ h₂
      simp only [Functor.comp_obj, Monotone.functor_obj, Set.principalSegIio_toRelEmbedding,
        tensorLeft_obj, Functor.mapCocone_pt, PrincipalSeg.cocone_pt, Set.principalSegIio_top,
        Functor.const_obj_obj, Functor.mapCocone_ι_app, PrincipalSeg.cocone_ι_app, homOfLE_leOfHom,
        tensorLeft_map, Arrow.mk_left, Functor.id_obj, NatTrans.arrowFunctor_obj_left,
        Arrow.mk_right, Arrow.mk_hom, whisker_exchange_assoc, h₂, NatTrans.arrowFunctor_obj_right,
        NatTrans.arrowFunctor_obj_hom, ← h₁, colimit.ι_desc_assoc, span_right,
        Functor.const_obj_map, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.id_comp, ←
        MonoidalCategory.whiskerLeft_comp_assoc, NatTrans.naturality, Category.comp_id, ←
        pushout.condition_assoc]
  fac s j := by
    apply pushout.hom_ext
    · simp
      apply (isColimitOfPreserves (tensorLeft Y) (h.isWellOrderContinuous.nonempty_isColimit m hm).some).fac
    · have := s.ι.naturality (homOfLE <| (Subtype.coe_le_coe.mp bot_le : ⟨⊥, hm.bot_lt⟩ ≤ j))
      simp only [Functor.comp_obj, Monotone.functor_obj, Set.principalSegIio_toRelEmbedding,
        natTransLeftFunctor_obj, Functor.const_obj_obj, homOfLE_leOfHom, Functor.comp_map,
        natTransLeftFunctor_map, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id,
        Category.comp_id] at this
      simp only [Arrow.mk_left, Functor.id_obj, Monotone.functor_obj,
        Set.principalSegIio_toRelEmbedding, NatTrans.arrowFunctor_obj_right, Functor.const_obj_obj,
        NatTrans.arrowFunctor_obj_left, Arrow.mk_right, Arrow.mk_hom, NatTrans.arrowFunctor_obj_hom,
        Functor.comp_obj, natTransLeftFunctor_obj, PrincipalSeg.cocone_pt, Set.principalSegIio_top,
        PrincipalSeg.cocone_ι_app, homOfLE_leOfHom, natTransLeftFunctor_map, Functor.const_obj_map,
        MonoidalCategory.whiskerLeft_id, ← this, colimit.ι_desc_assoc, span_right,
        PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.id_comp, colimit.ι_desc, span_zero]
  uniq s m' h' := by
    apply pushout.hom_ext
    · apply (isColimitOfPreserves (tensorLeft Y) (h.isWellOrderContinuous.nonempty_isColimit m hm).some).hom_ext
      intro j
      have h₁ := h' j
      have h₂ := (isColimitOfPreserves (tensorLeft Y) (h.isWellOrderContinuous.nonempty_isColimit m hm).some).fac
      simp only [Functor.comp_obj, Monotone.functor_obj, Set.principalSegIio_toRelEmbedding,
        natTransLeftFunctor_obj, Functor.const_obj_obj, PrincipalSeg.cocone_pt,
        Set.principalSegIio_top, PrincipalSeg.cocone_ι_app, homOfLE_leOfHom,
        natTransLeftFunctor_map, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id,
        tensorLeft_obj, Functor.mapCocone_pt, Functor.mapCocone_ι_app, tensorLeft_map,
        Subtype.forall, Set.mem_Iio] at h₁ h₂
      simp [h₂ _ j.1 j.2, ← h₁]
    · simp [← h' ⟨⊥, hm.bot_lt⟩]

instance temp_isWellOrderContinuous : (natTransLeftFunctor h.incl ι).IsWellOrderContinuous where
  nonempty_isColimit _ hm := ⟨temp_isColimit _ _ _ hm⟩

noncomputable
def temp_isColimit' : IsColimit ({ pt := Y ⊗ B, ι := descFunctor h.incl ι ≫ (Functor.constComp J B (tensorLeft Y)).hom } : Cocone (natTransLeftFunctor h.incl ι)) where
  desc s :=
    (Limits.isColimitOfPreserves (tensorLeft Y) h.isColimit).desc <| Cocone.mk s.pt ((inlDescFunctor h.incl ι) ≫ s.ι)
  fac s j := by
    simp [Functor.PushoutObjObj.ι]
    apply pushout.hom_ext
    · simpa using (Limits.isColimitOfPreserves (tensorLeft Y) h.isColimit).fac (Cocone.mk s.pt ((inlDescFunctor h.incl ι) ≫ s.ι)) j
    · apply (Limits.isColimitOfPreserves (tensorLeft X) h.isColimit).hom_ext
      intro k
      simp [whisker_exchange_assoc]
      have := (isColimitOfPreserves (tensorLeft Y) h.isColimit).fac (Cocone.mk s.pt ((inlDescFunctor h.incl ι) ≫ s.ι)) k
      simp at this
      rw [this, pushout.condition_assoc]
      by_cases hjk : j ≤ k
      · have := (s.ι.naturality (homOfLE hjk))
        simp only [Functor.const_obj_obj, Category.comp_id, Functor.const_obj_map] at this
        simp [← this]
      · have := (s.ι.naturality (homOfLE (not_le.1 hjk).le))
        simp only [Functor.const_obj_obj, Category.comp_id, Functor.const_obj_map] at this
        simp [← this]
  uniq s m hj := by
    apply (Limits.isColimitOfPreserves (tensorLeft Y) h.isColimit).hom_ext
    intro j
    have := (pushout.inl _ _) ≫= hj j
    simp [Functor.PushoutObjObj.ι] at this ⊢
    rw [this]
    have := (Limits.isColimitOfPreserves (tensorLeft Y) h.isColimit).fac (Cocone.mk s.pt ((inlDescFunctor h.incl ι) ≫ s.ι)) j
    simp at this
    rw [this]

noncomputable
def leftFunctor_preserves_transfiniteComposition
      (ι : X ⟶ Y) (f : A ⟶ B) (h : TransfiniteCompositionOfShape J f) :
    TransfiniteCompositionOfShape J (ι □ f) where
  F := natTransLeftFunctor h.incl ι
  isoBot := temp_isoBot ..
  incl := descFunctor h.incl ι ≫ ((tensorLeft Y).constComp J B).hom
  isColimit := temp_isColimit' ..
  fac := by
    apply pushout.hom_ext
    · simp [Functor.PushoutObjObj.ι, temp_isoBot, ← MonoidalCategory.whiskerLeft_comp]
    · simp [Functor.PushoutObjObj.ι, temp_isoBot]

variable (W : MorphismProperty C) (hf : W.TransfiniteCompositionOfShape J f)

lemma mflakdw (j : J) (hj : ¬IsMax j)
      (hW : ∀ (j : J), ¬IsMax j → W (ι □ hf.F.map (homOfLE (Order.le_succ j)))) :
    W.saturation ((natTransLeftFunctor hf.incl ι).map (homOfLE (Order.le_succ j))) := by
  sorry

end Transfinite

end CategoryTheory.PushoutProduct
