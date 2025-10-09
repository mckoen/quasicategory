import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Adhesive

universe w v v' u u'

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.PushoutProduct

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasPushouts C]

section Defs

variable {A B X Y Z W : C} (f : A ⟶ B) (g : X ⟶ Y) (h : Z ⟶ W)

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

noncomputable
def iso_of_arrow_iso (iso : (Arrow.mk g) ≅ (Arrow.mk h)) : Arrow.mk (f □ g) ≅ Arrow.mk (f □ h) := by
  refine Arrow.isoMk ?_ (whiskerLeftIso B (Comma.rightIso iso)) ?_
  · refine HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
    · exact whiskerLeftIso A (Comma.leftIso iso)
    · exact whiskerLeftIso B (Comma.leftIso iso)
    · exact whiskerLeftIso A (Comma.rightIso iso)
    · exact whisker_exchange f iso.hom.left
    · simp [← MonoidalCategory.whiskerLeft_comp]
  · apply pushout.hom_ext
    · simp [Functor.PushoutObjObj.ι, ← MonoidalCategory.whiskerLeft_comp]
    · simp [Functor.PushoutObjObj.ι, ← whisker_exchange]

def pt_tensorLeft_iso' [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorLeft W)] :
    IsPushout (W ◁ (f ▷ X)) (W ◁ (A ◁ g))
      (W ◁ (pushout.inl (f ▷ X) (A ◁ g))) (W ◁ (pushout.inr (f ▷ X) (A ◁ g))) where
  w := by simp only [← MonoidalCategory.whiskerLeft_comp, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorLeft W) _ _⟩

@[simp]
noncomputable
def pt_tensorLeft_iso [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorLeft W)]  : W ⊗ (pt f g) ≅ pt (W ◁ f) g := by
    refine (pt_tensorLeft_iso' _ _).isoPushout ≪≫ HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
    · exact (α_ W A X).symm
    · exact (α_ W B X).symm
    · exact (α_ W A Y).symm
    · exact (associator_inv_naturality_middle W f X).symm
    · simp only [curriedTensor_obj_obj, Iso.symm_hom, curriedTensor_obj_map, tensor_whiskerLeft,
        Iso.inv_hom_id_assoc]

def pt_tensorRight_iso' [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    IsPushout ((f ▷ X) ▷ W) ((A ◁ g) ▷ W)
      ((pushout.inl (f ▷ X) (A ◁ g)) ▷ W) ((pushout.inr (f ▷ X) (A ◁ g)) ▷ W) where
  w := by simp only [← MonoidalCategory.comp_whiskerRight, pushout.condition]
  isColimit' := ⟨Limits.isColimitOfHasPushoutOfPreservesColimit (tensorRight W) _ _⟩

@[simp]
noncomputable
def pt_tensorRight_iso [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] : (pt f g) ⊗ W ≅ pt f (g ▷ W) := by
  refine (pt_tensorRight_iso' _ _).isoPushout ≪≫ HasColimit.isoOfNatIso (spanExt ?_ ?_ ?_ ?_ ?_)
  · exact α_ A X W
  · exact α_ B X W
  · exact α_ A Y W
  · exact (associator_naturality_left f X W).symm
  · exact (associator_naturality_middle A g W).symm

noncomputable
def whiskerRight_iso [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    Arrow.mk ((f □ g) ▷ W) ≅ Arrow.mk (f □ (g ▷ W)) := by
  refine Arrow.isoMk (pt_tensorRight_iso f g) (α_ B Y W) ?_
  · apply (pt_tensorRight_iso' _ _).hom_ext
    all_goals simp [Functor.PushoutObjObj.ι, ← MonoidalCategory.comp_whiskerRight_assoc]

noncomputable
def whiskerLeft_iso [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorLeft W)] :
    Arrow.mk (W ◁ (f □ g)) ≅ Arrow.mk ((W ◁ f) □ g) := by
  refine Arrow.isoMk (pt_tensorLeft_iso _ _) (α_ W B Y).symm ?_
  · apply (pt_tensorLeft_iso' _ _).hom_ext
    all_goals simp [Functor.PushoutObjObj.ι, ← MonoidalCategory.whiskerLeft_comp_assoc]

@[simp]
noncomputable
def pt_associator_iso_hom
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight Z)]
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] : pt (f □ g) h ⟶ pt f (g □ h) := by
  apply pushout.desc ?_ ?_ ?_
  · exact (α_ _ _ _).hom ≫ (B ◁ pushout.inl _ _) ≫ pushout.inl _ _
  · refine (pt_tensorRight_iso _ _).hom ≫ pushout.desc ?_ ?_ ?_
    · exact (B ◁ pushout.inr _ _) ≫ pushout.inl _ _
    · exact pushout.inr _ _
    · dsimp [Functor.PushoutObjObj.ι]
      rw [← whisker_exchange_assoc, pushout.condition,
        ← MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inr_desc]
  · dsimp [Functor.PushoutObjObj.ι]
    apply (pt_tensorRight_iso' _ _).hom_ext
    · simp only [← MonoidalCategory.comp_whiskerRight_assoc, IsPushout.inl_desc, whisker_assoc,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, pushout.condition, ← whisker_exchange_assoc]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, tensor_whiskerLeft,
        HasColimit.isoOfNatIso_hom_desc, IsPushout.inl_isoPushout_hom_assoc, colimit.ι_desc,
        Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι,
        NatTrans.comp_app, span_left, Functor.const_obj_obj, spanExt_hom_app_left,
        PushoutCocone.mk_ι_app, Iso.inv_hom_id_assoc]
    · simp only [← comp_whiskerRight_assoc, IsPushout.inr_desc, Category.assoc,
        HasColimit.isoOfNatIso_hom_desc, ← whisker_exchange_assoc, tensor_whiskerLeft,
        IsPushout.inr_isoPushout_hom_assoc, colimit.ι_desc, Cocones.precompose_obj_pt,
        PushoutCocone.mk_pt, Cocones.precompose_obj_ι, NatTrans.comp_app, span_right,
        Functor.const_obj_obj, spanExt_hom_app_right, PushoutCocone.mk_ι_app, Iso.inv_hom_id_assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, pushout.condition,
        ← MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inl_desc]

@[simp]
noncomputable
def pt_associator_iso_inv
    [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft A)]
    [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft B)] : pt f (g □ h) ⟶ pt (f □ g) h := by
  apply pushout.desc ?_ ?_ ?_
  · refine (pt_tensorLeft_iso _ _).hom ≫ pushout.desc ?_ ?_ ?_
    · exact 𝟙 _ ≫ pushout.inl _ _
    · exact (pushout.inl _ _ ▷ W) ≫ pushout.inr _ _
    · dsimp [Functor.PushoutObjObj.ι]
      rw [Category.id_comp, whisker_exchange_assoc, ← pushout.condition,
        ← MonoidalCategory.comp_whiskerRight_assoc, IsPushout.inl_desc]
  · exact (α_ _ _ _).inv ≫ (pushout.inr _ _) ▷ _ ≫ pushout.inr _ _
  · dsimp [Functor.PushoutObjObj.ι]
    apply (pt_tensorLeft_iso' _ _).hom_ext
    · rw [whisker_exchange_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      simp only [whiskerRight_tensor, Category.id_comp, Category.assoc,
        HasColimit.isoOfNatIso_hom_desc, IsPushout.inl_isoPushout_hom_assoc, colimit.ι_desc,
        Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι,
        NatTrans.comp_app, span_left, Functor.const_obj_obj, spanExt_hom_app_left, Iso.symm_hom,
        PushoutCocone.mk_ι_app, Iso.hom_inv_id_assoc, IsPushout.inl_desc]
      rw [← congrFun (congrArg MonoidalCategoryStruct.whiskerRight ((IsPushout.of_hasPushout (f ▷ X) (A ◁ g)).inr_desc (B ◁ g) (f ▷ Y) (whisker_exchange f g).symm)) Z,
        MonoidalCategory.comp_whiskerRight, Category.assoc, pushout.condition, ← whisker_exchange_assoc]
      simp only [tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
    · simp only [Category.id_comp, Category.assoc, HasColimit.isoOfNatIso_hom_desc,
        whisker_exchange_assoc, whiskerRight_tensor, IsPushout.inr_isoPushout_hom_assoc,
        colimit.ι_desc, Cocones.precompose_obj_pt, PushoutCocone.mk_pt, Cocones.precompose_obj_ι,
        NatTrans.comp_app, span_right, Functor.const_obj_obj, spanExt_hom_app_right, Iso.symm_hom,
        PushoutCocone.mk_ι_app, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, pushout.condition,
        comp_whiskerRight, whisker_assoc, Iso.inv_hom_id_assoc, ←
        MonoidalCategory.whiskerLeft_comp_assoc, IsPushout.inr_desc]

@[simp]
noncomputable
def pt_associator_iso
      [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft A)]
      [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft B)]
      [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight Z)]
      [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    pt (f □ g) h ≅ pt f (g □ h) where
  hom := pt_associator_iso_hom f g h
  inv := pt_associator_iso_inv f g h
  hom_inv_id := by
    apply pushout.hom_ext
    · simp [Functor.PushoutObjObj.ι]
    · apply (pt_tensorRight_iso' _ _).hom_ext
      all_goals simp [Functor.PushoutObjObj.ι]
  inv_hom_id := by
    apply pushout.hom_ext
    · apply (pt_tensorLeft_iso' _ _).hom_ext
      all_goals simp [Functor.PushoutObjObj.ι]
    · simp [Functor.PushoutObjObj.ι]

@[simp]
noncomputable
def pt_comm_iso [BraidedCategory C] : pt f g ≅ pt g f :=
  pushoutSymmetry (f ▷ X) (A ◁ g) ≪≫
    (HasColimit.isoOfNatIso (spanExt (β_ _ _) (β_ _ _) (β_ _ _)
    (BraidedCategory.braiding_naturality_right A g).symm
    (BraidedCategory.braiding_naturality_left f X).symm))

noncomputable
def comm_iso [BraidedCategory C] : Arrow.mk (f □ g) ≅ Arrow.mk (g □ f) := by
  refine Arrow.isoMk (pt_comm_iso f g) (β_ _ _) ?_
  · simp [Functor.PushoutObjObj.ι]
    aesop

noncomputable
def associator
    [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft A)]
    [PreservesColimit (span (g ▷ Z) (X ◁ h)) (tensorLeft B)]
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight Z)]
    [PreservesColimit (span (f ▷ X) (A ◁ g)) (tensorRight W)] :
    Arrow.mk ((f □ g) □ h) ≅ Arrow.mk (f □ g □ h) := by
  refine Arrow.isoMk (pt_associator_iso _ _ _) (α_ _ _ _) ?_
  · dsimp [Functor.PushoutObjObj.ι]
    apply pushout.hom_ext
    · simp [← MonoidalCategory.whiskerLeft_comp]
    · apply (pt_tensorRight_iso' _ _).hom_ext
      · simp [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.comp_whiskerRight_assoc]
      · simp [← MonoidalCategory.comp_whiskerRight_assoc]

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

noncomputable
instance [HasInitial C] [HasTerminal C]
    [∀ W : C, PreservesColimitsOfSize (tensorRight W)]
    [∀ W : C, PreservesColimitsOfSize (tensorLeft W)] :
    MonoidalCategory (Arrow C) where
  tensorObj X Y := (leftBifunctor.obj X).obj Y
  whiskerLeft X _ _ f := (leftBifunctor.obj X).map f
  whiskerRight f X := (leftBifunctor.map f).app X
  tensorUnit := Arrow.mk (initial.to (𝟙_ C))
  associator X Y Z := associator X.hom Y.hom Z.hom
  leftUnitor X := by
    simp [Functor.PushoutObjObj.ι]
    refine Arrow.isoMk ?_ ?_ ?_
    · simp
      refine {
        hom := by
          apply pushout.desc (leftUnitor X.left).hom ?_ ?_
          · have : (⊥_ C) ⊗ X.right ≅ (⊥_ C) := by
              sorry
            sorry
          · sorry
        inv := sorry
      }
    · exact leftUnitor X.right
    · sorry
  rightUnitor := sorry

end Functor

section NatTrans

variable {D : Type u'} [Category.{v'} D]

variable {F G : D ⥤ C} (h : F ⟶ G)

variable {X Y : C} (g : X ⟶ Y)

/-- `(A : D) ↦ (h.app A : F.obj A ⟶ G.obj A)` -/
@[simps!]
def _root_.CategoryTheory.NatTrans.arrowFunctor : D ⥤ Arrow C where
  obj A := Arrow.mk (h.app A)
  map f := Arrow.homMk' _ _ (h.naturality f)

@[simps]
def _root_.CategoryTheory.NatTrans.arrowFunctor_NatTrans {G' : D ⥤ C} (h' : G ⟶ G') :
    NatTrans.arrowFunctor h ⟶ NatTrans.arrowFunctor (h ≫ h') where
  app X := Arrow.homMk' (𝟙 _) (h'.app X)

/-- `(A : D) ↦ pushout (g ▷ F.obj A) (X ◁ h.app A)` -/
@[simps!]
noncomputable
def natTransLeftFunctor : D ⥤ C := NatTrans.arrowFunctor h ⋙ leftFunctor g ⋙ Arrow.leftFunc

-- include interactions with whiskering

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

variable [hS : ∀ S : C, PreservesColimitsOfSize (tensorLeft S)]

def leftFunctor_map_preserves_pushouts {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {s : K ⟶ A} {t : L ⟶ B}
      (ι : X ⟶ Y) (h : IsPushout s g f t) :
    IsPushout ((leftFunctor (Arrow.mk ι)).map (Arrow.homMk' s t h.w)).left
      (ι □ g)
      (ι □ f)
      (Y ◁ t) := by
  have P₁ := whiskerPushout Y h
  have a : pushout.inl _ _ ≫ ι □ g = Y ◁ g := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) ι g).inl_ι
  have b : pushout.inl _ _ ≫ ι □ f = Y ◁ f := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) ι f).inl_ι
  rw [← a, ← b] at P₁
  apply IsPushout.of_top P₁
  · apply pushout.hom_ext
    · simp [Functor.PushoutObjObj.ι, ← MonoidalCategory.whiskerLeft_comp, h.w]
    · simp [Functor.PushoutObjObj.ι, whisker_exchange]
  · have P₂ := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) ι g).isPushout
    refine IsPushout.of_left ?_ ?_ P₂
    · have P₃ := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) ι f).isPushout
      have := IsPushout.paste_horiz (whiskerPushout X h) P₃
      dsimp at this
      rw [whisker_exchange] at this
      simpa
    · aesop

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

end Transfinite

section Transfinite'

variable {X Y : C} (ι : X ⟶ Y)

variable {J : Type w} [LinearOrder J] [SuccOrder J]
  (F : J ⥤ C) (c : Cocone F) (hc : IsColimit c)

variable {j : J}

/-
@[simp]
def id_to_succ : (.id J) ⟶ Order.succ_mono.functor where
  app j := homOfLE (Order.le_succ j)

lemma cocone_ι_facs : (id_to_succ ◫ 𝟙 F) ≫ (whiskerLeft Order.succ_mono.functor c.ι) = c.ι := by
  ext : 2
  simp [NatTrans.hcomp, whiskerLeft]
-/

@[simp]
noncomputable
def φ_j (j : J) : (pushout (ι ▷ F.obj j) (X ◁ F.map (homOfLE (Order.le_succ j)))) ⟶ (natTransLeftFunctor c.ι ι).obj j :=
  pushout.desc
    (pushout.inl _ _)
    (_ ◁ c.ι.app (Order.succ j) ≫ pushout.inr _ _)
    (by simp [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality, pushout.condition])

lemma newSqComm :
    (φ_j ι F c j) ≫
      ((natTransLeftFunctor c.ι ι).map (homOfLE (Order.le_succ j))) =
    (ι □ (F.map (homOfLE (Order.le_succ j)))) ≫
      ((inlDescFunctor c.ι ι).app (Order.succ j)) := by
  simp [Functor.PushoutObjObj.ι]
  apply pushout.hom_ext
  · simp
  · simp [pushout.condition]

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    (φ_j ι F c j) (ι □ (F.map (homOfLE (Order.le_succ j)))) :=
  PushoutCocone.mk _ _ (newSqComm ι F c)

@[simp]
noncomputable
def newPushoutIsColimit_desc (s : PushoutCocone (φ_j ι F c j) (ι □ (F.map (homOfLE (Order.le_succ j))))) :
    (natTransLeftFunctor c.ι ι).obj (Order.succ j) ⟶ s.pt :=
  pushout.desc s.inr ((pushout.inr _ _) ≫ s.inl)
    (by simpa [Functor.PushoutObjObj.ι] using ((pushout.inr _ _) ≫= s.condition).symm)

lemma newPushoutIsColimit_fac_left (s : PushoutCocone (φ_j ι F c j) (ι □ F.map (homOfLE (Order.le_succ j)))) :
    (natTransLeftFunctor c.ι ι).map (homOfLE (Order.le_succ j)) ≫ newPushoutIsColimit_desc ι F c s = s.inl := by
  simp only [Fin.isValue, natTransLeftFunctor_obj, Functor.const_obj_obj,
    Functor.id_obj, Monotone.functor_obj, homOfLE_leOfHom, Functor.comp_obj,
    NatTrans.hcomp_app, NatTrans.id_app, φ_j, Arrow.mk_left, NatTrans.arrowFunctor_obj_left,
    Arrow.mk_right, NatTrans.arrowFunctor_obj_right, Arrow.mk_hom, NatTrans.arrowFunctor_obj_hom,
    Functor.PushoutObjObj.ι, curriedTensor_obj_obj, Functor.PushoutObjObj.ofHasPushout_pt,
    curriedTensor_map_app, curriedTensor_obj_map, Functor.PushoutObjObj.ofHasPushout_inl,
    Functor.PushoutObjObj.ofHasPushout_inr, natTransLeftFunctor_map, Functor.const_obj_map,
    MonoidalCategory.whiskerLeft_id, newPushoutIsColimit_desc, PushoutCocone.ι_app_right,
    PushoutCocone.ι_app_left]
  apply pushout.hom_ext
  · have := (pushout.inl _ _) ≫= s.condition
    simp [Functor.PushoutObjObj.ι] at this
    rw [this]
    rw [pushout.inl_desc_assoc]
    have := (_ ◁ F.map (homOfLE (Order.le_succ j))) ≫=
      pushout.inl_desc s.inr (pushout.inr (ι ▷ F.obj j) (_ ◁ c.ι.app j) ≫ s.inl) (newPushoutIsColimit_desc.proof_5 ι F c s)
    rw [← this]
    dsimp only [NatTrans.arrowFunctor, Arrow.mk, Functor.id_obj]
    rw [pushout.inl_desc, Category.assoc, pushout.inl_desc]
  · simp only [pushout.inr_desc_assoc, Category.id_comp, pushout.inr_desc]

noncomputable
def newPushoutIsColimit : IsColimit (newPushoutCocone ι F c j) := by
  refine PushoutCocone.IsColimit.mk _ (newPushoutIsColimit_desc ι F c) ?_ ?_ ?_
  · exact newPushoutIsColimit_fac_left _ _ _
  · intro
    simp only [newPushoutIsColimit_desc, pushout.inl_desc, Arrow.mk, NatTrans.arrowFunctor, inlDescFunctor,
      Functor.id_obj, Functor.PushoutObjObj.ofHasPushout]
  · intro _ _ h h'
    apply pushout.hom_ext
    · dsimp only [inlDescFunctor, Functor.id_obj, Arrow.mk, NatTrans.arrowFunctor, newPushoutIsColimit_desc]
      rw [pushout.inl_desc, ← h']
      simp [inlDescFunctor]
    · dsimp only [Functor.id_obj, Arrow.mk, NatTrans.arrowFunctor, newPushoutIsColimit_desc]
      rw [pushout.inr_desc, ← h]
      simp

def newPushoutIsPushout (j : J) : IsPushout
    (φ_j ι F c j)
    (ι □ F.map (homOfLE (Order.le_succ j)))
    ((natTransLeftFunctor c.ι ι).map (homOfLE (Order.le_succ j)))
    (pushout.inl _ _) :=
  .of_isColimit (newPushoutIsColimit ι F c)

end Transfinite'

section Coproduct

variable {A B : C} (f : A ⟶ B)

open Limits in
noncomputable
def c₁' {J : Type*} {X₁ X₂ : Discrete J ⥤ C}
    {c₁ : Cocone X₁} (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (f' : X₁ ⟶ X₂) :
    Cocone (natTransLeftFunctor f' f) := {
      pt := PushoutProduct.pt f (h₁.desc { pt := c₂.pt, ι := f' ≫ c₂.ι })
      ι :=
        {
        app j := by
          apply Limits.pushout.desc
            (_ ◁ c₁.ι.app j ≫ (Limits.pushout.inl _ _))
            (_ ◁ c₂.ι.app j ≫ (Limits.pushout.inr _ _))
          have := h₁.fac { pt := c₂.pt, ι := f' ≫ c₂.ι } j
          dsimp at this
          simp
          rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← this, MonoidalCategory.whiskerLeft_comp_assoc,
            ← Limits.pushout.condition, whisker_exchange_assoc]
        naturality := by
          intro j k s
          dsimp
          apply Limits.pushout.hom_ext
          · simp
            rw [← MonoidalCategory.whiskerLeft_comp_assoc, c₁.ι.naturality]
            simp
          · simp
            rw [← MonoidalCategory.whiskerLeft_comp_assoc, c₂.ι.naturality]
            simp } }

variable  {J : Type*} {X₁ : Discrete J ⥤ C}  {X₂ : Discrete J ⥤ C}
    [PreservesColimit X₁ (tensorLeft A)] [PreservesColimit X₁ (tensorLeft B)]
    [PreservesColimit X₂ (tensorLeft A)]

set_option maxHeartbeats 800000 in
open Limits in
noncomputable
def c₁'_isColimit
    {c₁ : Cocone X₁} (c₂ : Cocone X₂)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (f' : X₁ ⟶ X₂) : IsColimit (c₁' f c₂ h₁ f') where
  desc s := by
    dsimp [c₁']
    let s₁ := Cocone.mk s.pt (inlDescFunctor f' f ≫ s.ι)
    let s₂ := Cocone.mk s.pt (inrDescFunctor f' f ≫ s.ι)
    let hs₁ := (isColimitOfPreserves (tensorLeft B) h₁)
    let hs₂ := (isColimitOfPreserves (tensorLeft A) h₂)
    let hs₁' := (isColimitOfPreserves (tensorLeft A) h₁)
    apply pushout.desc (hs₁.desc s₁) (hs₂.desc s₂)
    apply hs₁'.hom_ext
    intro j
    let hs₁_fac := hs₁.fac s₁ j
    let hs₂_fac := hs₂.fac s₂ j
    simp [s₁, s₂, hs₁, hs₂] at hs₁_fac hs₂_fac ⊢
    rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hs₁_fac]
    simp [hs₂_fac, pushout.condition_assoc]
  fac s j := by
    simp [c₁']
    apply pushout.hom_ext
    · simp
      exact (isColimitOfPreserves (tensorLeft _) h₁).fac { pt := s.pt, ι := inlDescFunctor f' f ≫ s.ι } j
    · let s₂ := Cocone.mk s.pt (inrDescFunctor f' f ≫ s.ι)
      let hs₂ := (isColimitOfPreserves (tensorLeft A) h₂)
      let hs₂_fac := hs₂.fac s₂ j
      simp [s₂] at hs₂_fac ⊢
      rw [hs₂_fac]
  uniq s m hj := by
    simp
    apply pushout.hom_ext
    · let s₁ := Cocone.mk s.pt (inlDescFunctor f' f ≫ s.ι)
      let hs₁ := (isColimitOfPreserves (tensorLeft B) h₁)
      apply hs₁.hom_ext
      intro j
      simp
      have := hs₁.fac s₁ j
      dsimp [s₁, c₁'] at this
      rw [this, ← hj j]
      simp [c₁']
    · let s₂ := Cocone.mk s.pt (inrDescFunctor f' f ≫ s.ι)
      let hs₂ := (isColimitOfPreserves (tensorLeft A) h₂)
      apply hs₂.hom_ext
      intro j
      simp
      have := hs₂.fac s₂ j
      dsimp [s₂] at this
      rw [this, ← hj j]
      simp [c₁']

end Coproduct

end CategoryTheory.PushoutProduct
