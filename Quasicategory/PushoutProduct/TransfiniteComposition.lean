import Quasicategory.PushoutProduct.Basic

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {J : Type w} [LinearOrder J] [SuccOrder J]
  (F : J ⥤ SSet) (c : Cocone F) (hc : IsColimit c)

variable {j : J}

@[simp]
def id_to_succ : (.id J) ⟶ Order.succ_mono.functor where
  app j := homOfLE (Order.le_succ j)

lemma cocone_ι_facs : (id_to_succ ◫ 𝟙 F) ≫ (whiskerLeft Order.succ_mono.functor c.ι) = c.ι := by
  ext : 2
  simp [NatTrans.hcomp, whiskerLeft]

@[simp]
noncomputable
def φ_j (j : J) : (natTransLeftFunctor (id_to_succ ◫ 𝟙 F) Λ[2, 1].ι).obj j ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι).obj j :=
  pushout.desc
    (pushout.inl _ _)
    (Λ[2, 1].toSSet ◁ c.ι.app (Order.succ j) ≫ pushout.inr _ _)
    (by simp [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality, pushout.condition])

lemma newSqComm :
    (φ_j F c j) ≫
      ((natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j))) =
    (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j)))) ≫
      pushout.inl _ _ := by
  simp [Functor.PushoutObjObj.ι]
  apply pushout.hom_ext
  · simp
  · simp [pushout.condition]

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    (φ_j F c j) (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j)))) :=
  PushoutCocone.mk _ _ (newSqComm F c)

@[simp]
noncomputable
def newPushoutIsColimit_desc (s : PushoutCocone (φ_j F c j) (Λ[2, 1].ι □ (F.map (homOfLE (Order.le_succ j))))) :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).obj (Order.succ j) ⟶ s.pt :=
  pushout.desc s.inr ((pushout.inr _ _) ≫ s.inl)
    (by simpa [Functor.PushoutObjObj.ι] using ((pushout.inr _ _) ≫= s.condition).symm)

lemma newPushoutIsColimit_fac_left (s : PushoutCocone (φ_j F c j) (Λ[2, 1].ι □ F.map (homOfLE (Order.le_succ j)))) :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j)) ≫ newPushoutIsColimit_desc F c s = s.inl := by
  simp only [Fin.isValue, natTransLeftFunctor_obj, Functor.const_obj_obj,
    id_to_succ, Functor.id_obj, Monotone.functor_obj, homOfLE_leOfHom, Functor.comp_obj,
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
    have := (Δ[2] ◁ F.map (homOfLE (Order.le_succ j))) ≫=
      pushout.inl_desc s.inr (pushout.inr (Λ[2, 1].ι ▷ F.obj j) (Λ[2, 1].toSSet ◁ c.ι.app j) ≫ s.inl) (newPushoutIsColimit_desc.proof_7 F c s)
    rw [← this]
    dsimp only [NatTrans.arrowFunctor, Arrow.mk, Functor.id_obj]
    rfl
  · simp only [pushout.inr_desc_assoc, Category.id_comp, pushout.inr_desc]

noncomputable
def newPushoutIsColimit : IsColimit (newPushoutCocone F c j) := by
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
      simp

def newPushoutIsPushout (j : J) : IsPushout
    (φ_j F c j)
    (Λ[2, 1].ι □ F.map (homOfLE (Order.le_succ j)))
    ((natTransLeftFunctor c.ι Λ[2, 1].ι).map (homOfLE (Order.le_succ j)))
    (pushout.inl _ _) :=
  .of_isColimit (newPushoutIsColimit F c)

end CategoryTheory.PushoutProduct
