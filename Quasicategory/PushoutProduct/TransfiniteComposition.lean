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

/-
--set_option maxHeartbeats 300000 in
@[simp]
noncomputable
def φ : (natTransLeftFunctor F.succNatTrans Λ[2, 1].ι) ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι) :=
  natTransLeftFunctor_comp F.succNatTrans Λ[2, 1].ι (whiskerLeft Order.succ_mono.functor c.ι) ≫ intermediateeqhom _ _

where
  app := φ_j F c
  naturality k j f := by
    apply pushout.hom_ext
    · simp only [Fin.isValue, Arrow.mk_right, Functor.id_obj, Functor.succ, homOfLE_leOfHom,
      Functor.succNatTrans, NatTrans.arrowFunctor_obj_left, natTransLeftFunctor_obj,
      Functor.const_obj_obj, Arrow.mk_left, NatTrans.arrowFunctor_obj_right, Arrow.mk_hom,
      NatTrans.arrowFunctor_obj_hom, natTransLeftFunctor_map, φ_j, pt,
      colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.assoc,
      colimit.ι_desc, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    · simp [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality, pushout.condition]
-/

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma newSqComm {j} :
    φ_j F c j ≫
      ((natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j))) =
    (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j)))) ≫
      pushout.inl _ _ := by
  simp [Functor.PushoutObjObj.ofHasPushout]
  apply pushout.hom_ext
  ·
    sorry
  ·
    sorry

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    (φ_j F c j) (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j)))) :=
  PushoutCocone.mk _ _ (newSqComm F c)

@[simp]
noncomputable
def newPushoutIsColimit_desc {j} (s : PushoutCocone (φ_j F c j) (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j))))) :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).obj (Order.succ j) ⟶ s.pt :=
  pushout.desc s.inr ((pushout.inr _ _) ≫ s.inl) (by
    have := ((pushout.inr _ _) ≫= s.condition)
    simp only [Fin.isValue, Arrow.mk_left, Functor.id_obj, Functor.succNatTrans, id_to_succ,
      Monotone.functor_obj, homOfLE_leOfHom, NatTrans.arrowFunctor_obj_right, Functor.comp_obj,
      natTransLeftFunctor_obj, NatTrans.hcomp_app, NatTrans.id_app, Functor.const_obj_obj, φ_j,
      NatTrans.arrowFunctor_obj_left, Arrow.mk_right, Arrow.mk_hom, NatTrans.arrowFunctor_obj_hom,
      pushoutProduct, Functor.PushoutObjObj.ofHasPushout, curriedTensor_obj_obj,
      curriedTensor_map_app, curriedTensor_obj_map, PushoutCocone.ι_app_left, colimit.ι_desc_assoc,
      span_right, id_eq, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.assoc,
      PushoutCocone.ι_app_right] at this
    simp only [Fin.isValue, Arrow.mk_left, Functor.id_obj, NatTrans.arrowFunctor_obj_left,
      Functor.succNatTrans, id_to_succ, Monotone.functor_obj, homOfLE_leOfHom,
      natTransLeftFunctor_obj, Functor.comp_obj, NatTrans.hcomp_app, NatTrans.id_app,
      Functor.const_obj_obj, φ_j, Arrow.mk_right, NatTrans.arrowFunctor_obj_right, Arrow.mk_hom,
      NatTrans.arrowFunctor_obj_hom, pushoutProduct, PushoutCocone.ι_app_right,
      PushoutCocone.ι_app_left, this]
    sorry)-- simpa using ((pushout.inr _ _) ≫= s.condition).symm)

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma newPushoutIsColimit_fac_left {j} (s : PushoutCocone (φ_j F c j) (Λ[2, 1].ι □ F.map (homOfLE (Order.le_succ j)))) :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j)) ≫ newPushoutIsColimit_desc F c s = s.inl := by
  dsimp only [newPushoutIsColimit_desc, NatTrans.arrowFunctor, Arrow.mk, natTransLeftFunctor,
    Functor.comp_map, Arrow.homMk', leftFunctor, leftFunctor_map, Arrow.leftFunc_map,
    leftFunctor_map_left, Functor.id_obj, Functor.const, pushout.map]
  simp_rw [MonoidalCategory.whiskerLeft_id]
  apply pushout.hom_ext
  ·
    sorry
    /-
    simpa only [Functor.succ, homOfLE_leOfHom, Functor.succNatTrans, Fin.isValue, pt,
    pushoutProduct, φ, natTransLeftFunctor, NatTrans.arrowFunctor, Arrow.mk, Functor.const_obj_obj,
    Functor.const_obj_map, φ_j, Functor.id_obj, pushout.inl, pushout.inr,
    PushoutCocone.ι_app_right, PushoutCocone.ι_app_left, pushout.inl_desc_assoc, Category.assoc,
    pushout.inl_desc] using ((pushout.inl _ _) ≫= s.condition).symm
    -/
  ·
    sorry --rw [pushout.inr_desc_assoc, pushout.inr_desc]
  --sorry
  /-
  -/

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
