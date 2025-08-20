import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

universe w v v' u u'

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (f : A ⟶ B) (g : X ⟶ Y)

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet) [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)


-- def natTransLeftFunctor : D ⥤ C := (NatTrans.arrowFunctor h) ⋙ leftFunctor g ⋙ Arrow.leftFunc
@[simps!]
noncomputable
abbrev F' : J ⥤ SSet := natTransLeftFunctor c.ι Λ[2, 1].ι

instance ll {S : SSet} : Functor.IsLeftAdjoint (tensorLeft S) where
  exists_rightAdjoint := ⟨FunctorToTypes.rightAdj S, ⟨FunctorToTypes.adj S⟩⟩

instance rr {S : SSet} : PreservesColimitsOfSize (tensorLeft S) :=
  Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _

noncomputable
instance {S : SSet} : PreservesColimitsOfSize (tensorRight S) := by
  apply preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight S)

variable {m : J}

@[simp]
def _root_.CategoryTheory.Functor.succ : J ⥤ SSet :=
  Order.succ_mono.functor ⋙ F

@[simp]
def temp_id_to_succ : (Functor.id J) ⟶ Order.succ_mono.functor where
  app j := homOfLE (Order.le_succ j)

@[simp]
def _root_.CategoryTheory.Functor.succNatTrans : F ⟶ Order.succ_mono.functor ⋙ F :=
  temp_id_to_succ ◫ (𝟙 F)

@[simp]
noncomputable
abbrev P := natTransLeftFunctor F.succNatTrans Λ[2, 1].ι

variable {G} (h : F ⟶ G)

@[simp]
def natTransSucc : Order.succ_mono.functor ⋙ F ⟶ Order.succ_mono.functor ⋙ G :=
  whiskerLeft Order.succ_mono.functor h

/-
@[simp]
def φaux : (F.succ) ⟶ (Functor.const J).obj c.pt := natTransSucc F c.ι

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
@[simp]
lemma φaux' : (F.succNatTrans) ≫ (natTransSucc F c.ι) = c.ι := by
  ext
  simp

@[simp]
noncomputable
def φ_1 : P F ⟶ natTransLeftFunctor (F.succNatTrans ≫ (natTransSucc F c.ι)) ((horn 2 1).ι) :=
  PushoutProduct.natTransLeftFunctor_comp (F.succNatTrans) ((horn 2 1).ι) (natTransSucc F c.ι)

@[simp]
noncomputable
def φ_2 : natTransLeftFunctor (F.succNatTrans ≫ (natTransSucc F c.ι)) ((horn 2 1).ι) ⟶ (F' F c) :=
  eqToHom (by rw [φaux'])

@[simp]
noncomputable
def φ : (P F) ⟶ (F' F c) :=
  PushoutProduct.natTransLeftFunctor_comp (F.succNatTrans) ((horn 2 1).ι) (natTransSucc F c.ι) ≫
    eqToHom (by rw [φaux'])
-/

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma cocone_ι_facs : F.succNatTrans ≫ (whiskerLeft Order.succ_mono.functor c.ι) = c.ι := by
  ext : 2
  simp

@[simp]
noncomputable
def intermediateeqhom : (natTransLeftFunctor (F.succNatTrans ≫ (whiskerLeft Order.succ_mono.functor c.ι)) Λ[2, 1].ι) ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι) :=
  eqToHom (by rw [cocone_ι_facs])

@[simp]
noncomputable
def φ_j (j) : (natTransLeftFunctor F.succNatTrans Λ[2, 1].ι).obj j ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι).obj j := by
  apply pushout.desc
    (pushout.inl _ _)
    ((Λ[2, 1] : SSet) ◁ c.ι.app (Order.succ j) ≫ pushout.inr _ _)
  simp [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality, pushout.condition]
  /-
  natTransLeftFunctor_comp F.succNatTrans Λ[2, 1].ι (natTransSucc F c.ι) ≫ (intermediateeqhom _ _)
  -/

--natTransLeftFunctor_comp

--set_option maxHeartbeats 300000 in
@[simp]
noncomputable
def φ : (natTransLeftFunctor F.succNatTrans Λ[2, 1].ι) ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι) :=
  natTransLeftFunctor_comp F.succNatTrans Λ[2, 1].ι (whiskerLeft Order.succ_mono.functor c.ι) ≫ intermediateeqhom _ _

/-
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
    (φ F c).app j ≫ ((natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j))) =
    (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j)))) ≫
      pushout.inl _ _ := by
  apply pushout.hom_ext
  · sorry
  · sorry

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    ((φ F c).app j) (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j)))) :=
  PushoutCocone.mk _ _ (newSqComm F c)

@[simp]
noncomputable
def newPushoutIsColimit_desc {j} (s : PushoutCocone ((φ F c).app j) (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j))))) :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).obj (Order.succ j) ⟶ s.pt :=
  pushout.desc s.inr ((pushout.inr _ _) ≫ s.inl) (by sorry)-- simpa using ((pushout.inr _ _) ≫= s.condition).symm)

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma newPushoutIsColimit_fac_left {j} (s : PushoutCocone ((φ F c).app j) (Λ[2, 1].ι □ F.map (homOfLE (Order.le_succ j)))) :
    (F' F c).map (homOfLE (Order.le_succ j)) ≫ newPushoutIsColimit_desc F c s = s.inl := by
  dsimp only [F', newPushoutIsColimit_desc, NatTrans.arrowFunctor, Arrow.mk, natTransLeftFunctor,
    Functor.comp_map, Arrow.homMk', leftFunctor, leftFunctor_map, Arrow.leftFunc_map,
    leftFunctor_map_left, Functor.id_obj, Functor.const, pushout.map]
  simp_rw [MonoidalCategory.whiskerLeft_id]
  sorry
  apply pushout.hom_ext
  · sorry
    /-
    simpa only [Functor.succ, homOfLE_leOfHom, Functor.succNatTrans, Fin.isValue, pt,
    pushoutProduct, φ, natTransLeftFunctor, NatTrans.arrowFunctor, Arrow.mk, Functor.const_obj_obj,
    Functor.const_obj_map, φ_j, Functor.id_obj, pushout.inl, pushout.inr,
    PushoutCocone.ι_app_right, PushoutCocone.ι_app_left, pushout.inl_desc_assoc, Category.assoc,
    pushout.inl_desc] using ((pushout.inl _ _) ≫= s.condition).symm
    -/
  · sorry --rw [pushout.inr_desc_assoc, pushout.inr_desc]

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
  ((φ F c).app j)
  (Λ[2, 1].ι □ F.map (homOfLE (Order.le_succ j)))
  ((natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j)))
  (pushout.inl _ _)
  := IsPushout.of_isColimit (newPushoutIsColimit F c (j := j))

end CategoryTheory.PushoutProduct
