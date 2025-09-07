import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Enriched.FunctorCategory

universe w v v' u u'

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (f : A ⟶ B) (g : X ⟶ Y)

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet) [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)

instance : MonoidalCategory (J ⥤ J) := endofunctorMonoidalCategory J

noncomputable
instance : MonoidalCategory (J ⥤ SSet) := by infer_instance

variable {m : J}

@[simp]
def _root_.CategoryTheory.Functor.succ : J ⥤ SSet :=
  Order.succ_mono.functor ⋙ F

@[simp]
def id_to_succ : (.id J) ⟶ Order.succ_mono.functor where
  app j := homOfLE (Order.le_succ j)

@[simp]
def _root_.CategoryTheory.Functor.succNatTrans : F ⟶ Order.succ_mono.functor ⋙ F :=
  id_to_succ ◫ 𝟙 F

variable {G} (h : F ⟶ G)

@[simp]
def natTransSucc : Order.succ_mono.functor ⋙ F ⟶ Order.succ_mono.functor ⋙ G :=
  whiskerLeft Order.succ_mono.functor h

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
@[simp]
lemma cocone_ι_facs_app {j : J} : ((id_to_succ ◫ 𝟙 F) ≫ (whiskerLeft Order.succ_mono.functor c.ι)).app j = c.ι.app j := by simp

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma cocone_ι_facs : (id_to_succ ◫ 𝟙 F) ≫ (whiskerLeft Order.succ_mono.functor c.ι) = c.ι := by
  ext : 2
  apply cocone_ι_facs_app


/-
@[simp]
noncomputable
def intermediateeqhom : (natTransLeftFunctor ((id_to_succ ◫ 𝟙 F) ≫ (whiskerLeft Order.succ_mono.functor c.ι)) Λ[2, 1].ι) ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι) :=
  eqToHom (by rw [cocone_ι_facs])
-/

@[simp]
noncomputable
def φ_j (j) : (natTransLeftFunctor F.succNatTrans Λ[2, 1].ι).obj j ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι).obj j :=
  pushout.desc
    (pushout.inl _ _)
    (Λ[2, 1].toSSet ◁ c.ι.app (Order.succ j) ≫ pushout.inr _ _)
    (by simp [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality, pushout.condition])

set_option maxHeartbeats 300000 in
@[simp]
noncomputable
def φ : (natTransLeftFunctor (id_to_succ ◫ 𝟙 F) Λ[2, 1].ι) ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι) where
  app := φ_j F c
  naturality k j f := by
    apply pushout.hom_ext
    · simp only [Fin.isValue, Arrow.mk_right, Functor.id_obj, id_to_succ, Monotone.functor_obj,
      homOfLE_leOfHom, NatTrans.arrowFunctor_obj_left, Functor.comp_obj, natTransLeftFunctor_obj,
      Functor.const_obj_obj, Arrow.mk_left, NatTrans.arrowFunctor_obj_right, Arrow.mk_hom,
      NatTrans.arrowFunctor_obj_hom, NatTrans.hcomp_app, NatTrans.id_app, natTransLeftFunctor_map,
      Functor.comp_map, Functor.id_map, φ_j, Functor.succNatTrans, colimit.ι_desc_assoc, span_left,
      id_eq, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.assoc, colimit.ι_desc,
      Functor.const_obj_map, MonoidalCategory.whiskerLeft_id]
    · simp [← MonoidalCategory.whiskerLeft_comp_assoc]

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma newSqComm {j} :
    (φ F c).app j ≫
      ((natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j))) =
    (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j)))) ≫
      pushout.inl _ _ := by
  simp [Functor.PushoutObjObj.ι]
  apply pushout.hom_ext
  · simp
  · simp [pushout.condition]

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    ((φ F c).app j) (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j)))) :=
  PushoutCocone.mk _ _ (newSqComm F c)

@[simp]
noncomputable
def newPushoutIsColimit_desc {j} (s : PushoutCocone ((φ F c).app j) (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j))))) :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).obj (Order.succ j) ⟶ s.pt :=
  pushout.desc s.inr ((pushout.inr _ _) ≫ s.inl)
    (by simpa [Functor.PushoutObjObj.ι] using ((pushout.inr _ _) ≫= s.condition).symm)

lemma auxxxxxxxx {j} (s : PushoutCocone ((φ F c).app j) (Λ[2, 1].ι □ F.map (homOfLE (Order.le_succ j))))
   (h2 : j ≤ Order.succ j) (h11 : Λ[2, 1].ι ▷ F.obj j ≫ Δ[2] ◁ F.map (homOfLE h2) = Λ[2, 1].toSSet ◁ F.map (homOfLE h2) ≫ Λ[2, 1].ι ▷ F.obj (Order.succ j))
    (h13 : Λ[2, 1].toSSet ◁ c.ι.app j ≫ 𝟙 (Λ[2, 1].toSSet ⊗ c.pt) =
      Λ[2, 1].toSSet ◁ F.map (homOfLE h2) ≫ Λ[2, 1].toSSet ◁ c.ι.app (Order.succ j))
    (h21 : Λ[2, 1].ι ▷ F.obj (Order.succ j) ≫ s.inr =
  Λ[2, 1].toSSet ◁ c.ι.app (Order.succ j) ≫ pushout.inr (Λ[2, 1].ι ▷ F.obj j) (Λ[2, 1].toSSet ◁ c.ι.app j) ≫ s.inl)
     : pushout.inl (Λ[2, 1].ι ▷ F.obj j) (Λ[2, 1].toSSet ◁ c.ι.app j) ≫
    pushout.map (Λ[2, 1].ι ▷ F.obj j) (Λ[2, 1].toSSet ◁ c.ι.app j) (Λ[2, 1].ι ▷ F.obj (Order.succ j))
        (Λ[2, 1].toSSet ◁ c.ι.app (Order.succ j)) (Δ[2] ◁ F.map (homOfLE h2)) (𝟙 (Λ[2, 1].toSSet ⊗ c.pt))
        (Λ[2, 1].toSSet ◁ F.map (homOfLE h2)) h11 h13 ≫
      pushout.desc s.inr (pushout.inr (Λ[2, 1].ι ▷ F.obj j) (Λ[2, 1].toSSet ◁ c.ι.app j) ≫ s.inl) h21 =
    pushout.inl (Λ[2, 1].ι ▷ F.obj j) (Λ[2, 1].toSSet ◁ c.ι.app j) ≫ s.inl := by
  rw [pushout.inl_desc_assoc]
  have := (pushout.inl _ _) ≫= s.condition
  simp [Functor.PushoutObjObj.ι] at this
  rw [this]
  have := s.condition
  have H := pushout.condition (f := (Λ[2, 1].ι ▷ F.obj (Order.succ j))) (g := (Λ[2, 1].toSSet ◁ c.ι.app (Order.succ j)))
  have H' := cocone_ι_facs_app F c (j := j)
  dsimp at H'
  rw [Category.id_comp] at H'
  sorry

/-
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 200000 in
-/
omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma newPushoutIsColimit_fac_left {j} (s : PushoutCocone ((φ F c).app j) (Λ[2, 1].ι □ F.map (homOfLE (Order.le_succ j)))) :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j)) ≫ newPushoutIsColimit_desc F c s = s.inl := by
  /-
  simp only [Fin.isValue, natTransLeftFunctor_obj, Functor.const_obj_obj, Functor.succNatTrans,
    id_to_succ, Functor.id_obj, Monotone.functor_obj, homOfLE_leOfHom, Functor.comp_obj,
    NatTrans.hcomp_app, NatTrans.id_app, φ_j, Arrow.mk_left, NatTrans.arrowFunctor_obj_left,
    Arrow.mk_right, NatTrans.arrowFunctor_obj_right, Arrow.mk_hom, NatTrans.arrowFunctor_obj_hom,
    Functor.PushoutObjObj.ι, curriedTensor_obj_obj, Functor.PushoutObjObj.ofHasPushout_pt,
    curriedTensor_map_app, curriedTensor_obj_map, Functor.PushoutObjObj.ofHasPushout_inl,
    Functor.PushoutObjObj.ofHasPushout_inr, natTransLeftFunctor_map, Functor.const_obj_map,
    MonoidalCategory.whiskerLeft_id, newPushoutIsColimit_desc, PushoutCocone.ι_app_right,
    PushoutCocone.ι_app_left]
  -/
  apply pushout.hom_ext
  · simp only [Fin.isValue, natTransLeftFunctor_obj, Functor.const_obj_obj, Functor.succNatTrans,
      id_to_succ, Functor.id_obj, Monotone.functor_obj, homOfLE_leOfHom, Functor.comp_obj,
      NatTrans.hcomp_app, NatTrans.id_app, φ_j, Arrow.mk_left, NatTrans.arrowFunctor_obj_left,
      Arrow.mk_right, NatTrans.arrowFunctor_obj_right, Arrow.mk_hom, NatTrans.arrowFunctor_obj_hom,
      Functor.PushoutObjObj.ι, curriedTensor_obj_obj, Functor.PushoutObjObj.ofHasPushout_pt,
      curriedTensor_map_app, curriedTensor_obj_map, Functor.PushoutObjObj.ofHasPushout_inl,
      Functor.PushoutObjObj.ofHasPushout_inr, natTransLeftFunctor_map, Functor.const_obj_map,
      MonoidalCategory.whiskerLeft_id, newPushoutIsColimit_desc, PushoutCocone.ι_app_right,
      PushoutCocone.ι_app_left]
    have := (pushout.inl _ _) ≫= s.condition
    simp [Functor.PushoutObjObj.ι] at this
    rw [this]
    rw [pushout.inl_desc_assoc]

    /-
    -/

    sorry
  · sorry--simp only [pushout.inr_desc_assoc, Category.id_comp, pushout.inr_desc]

noncomputable
def newPushoutIsColimit {j} : IsColimit (newPushoutCocone F c j) := by
  refine PushoutCocone.IsColimit.mk _ (newPushoutIsColimit_desc F c) ?_ ?_ ?_
  · exact newPushoutIsColimit_fac_left _ _
  · intro
    simp only [newPushoutIsColimit_desc, pushout.inl_desc]
  · intro _ _ h h'
    apply pushout.hom_ext
    · dsimp only [Functor.id_obj, Arrow.mk, NatTrans.arrowFunctor, newPushoutIsColimit_desc]
      rw [pushout.inl_desc, ← h']
      dsimp only [NatTrans.arrowFunctor, Arrow.mk, Functor.id_obj]
    · dsimp only [Functor.id_obj, Arrow.mk, NatTrans.arrowFunctor, newPushoutIsColimit_desc]
      rw [pushout.inr_desc, ← h]
      simp only [Fin.isValue, Functor.const_obj_obj, Functor.succ, homOfLE_leOfHom,
        Functor.succNatTrans, natTransLeftFunctor_obj, pushoutProduct, pt,
        natTransLeftFunctor_map, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id,
        Category.id_comp, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
        PushoutCocone.mk_ι_app]

def newPushoutIsPushout (j : J) : CategoryTheory.IsPushout
    (φ_j F c j)
    (Λ[2, 1].ι □ F.map (homOfLE (Order.le_succ j)))
    ((natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j)))
    (pushout.inl _ _) :=
  .of_isColimit (newPushoutIsColimit F c (j := j))

end CategoryTheory.PushoutProduct
