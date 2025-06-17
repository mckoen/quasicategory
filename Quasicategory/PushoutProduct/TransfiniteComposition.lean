import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

universe w v u

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (f : A ⟶ B) (g : X ⟶ Y)

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet) [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)

@[simp]
noncomputable
abbrev F' : J ⥤ SSet := PushoutProduct.natTransLeftFunctor c.ι (horn 2 1).ι

instance ll {S : SSet} : Functor.IsLeftAdjoint (tensorLeft S) where
  exists_rightAdjoint := ⟨FunctorToTypes.rightAdj S, ⟨FunctorToTypes.adj S⟩⟩

noncomputable
instance rr {S : SSet} : PreservesColimitsOfSize (tensorLeft S) :=
  Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _

variable {m : J}

noncomputable
def tempCocone (s : Cocone ((Set.principalSegIio m).monotone.functor ⋙ (F' F c))) :
    Cocone (((Set.principalSegIio m).monotone.functor ⋙ F) ⋙ tensorLeft Δ[2]) where
  pt := s.pt
  ι := (whiskerLeft ((Set.principalSegIio m).monotone.functor) (inlDescFunctor c.ι ((horn 2 1).ι))) ≫ s.ι

noncomputable
def tempCocone' (s : Cocone (F' F c)) :
    (Cocone (F ⋙ tensorLeft Δ[2])) where
  pt := s.pt
  ι := (inlDescFunctor c.ι ((horn 2 1).ι)) ≫ s.ι

/-
noncomputable
def tempCocone' (s : Cocone ((F' F c).restrictionLT m)) :
    Cocone (((Functor.const J).obj c.pt).restrictionLT m ⋙ tensorLeft Λ[2, 1]) where
  pt := s.pt
  ι := (whiskerLeft (Monotone.functor _) (inrDescFunctor c.ι ((horn 2 1).ι))) ≫ s.ι
-/

instance {m : J} {hm : Order.IsSuccLimit m} : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt

instance constIsWellOrderContinuous (X : SSet) : ((Functor.const J).obj X).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨{
    desc s := s.ι.app ⟨⊥, hm.bot_lt⟩
    fac s j := by
      letI : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt
      simpa using (s.ι.naturality (homOfLE <| bot_le)).symm
    uniq s f hf := by simpa using hf ⟨⊥, hm.bot_lt⟩
  }⟩

set_option maxHeartbeats 1000000 in
noncomputable
def auxWellOrderCont_desc [hF: F.IsWellOrderContinuous]
    {m : J} (hm : Order.IsSuccLimit m) (s : Cocone ((Set.principalSegIio m).monotone.functor ⋙ (F' F c))) :
    ((Set.principalSegIio m).cocone (F' F c)).pt ⟶ s.pt := by
  letI : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt
  let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) (hF.nonempty_isColimit m hm).some)
  let H'' := (Limits.isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) (hF.nonempty_isColimit m hm).some)
  refine pushout.desc (H.desc (tempCocone F c s)) ((inr _ _) ≫ s.ι.app ⊥) ?_
  apply H''.hom_ext
  intro j
  have Hfac := H.fac (tempCocone F c s) j
  dsimp only [Functor.comp_obj, Monotone.functor_obj, Set.principalSegIio_toRelEmbedding,
    tensorLeft_obj, Functor.mapCocone_pt, PrincipalSeg.cocone_pt, Set.principalSegIio_top,
    Functor.const_obj_obj, Functor.mapCocone_ι_app, PrincipalSeg.cocone_ι_app, homOfLE_leOfHom,
    tensorLeft_map] at Hfac
  dsimp
  rw [whisker_exchange_assoc, Hfac]
  dsimp only [tempCocone, inlDescFunctor]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality]
  have := (s.ι.naturality (homOfLE <| bot_le (a := j)))
  simp only [natTransLeftFunctor.eq_1, NatTrans.arrowFunctor.eq_1, Functor.const_obj_obj,
    Functor.const_obj_map, Fin.isValue, rightFunctor.eq_1, Arrow.mk_left, Functor.id_obj,
    Arrow.mk_right, Arrow.mk_hom, pushoutProduct, rightFunctor_map.eq_1, rightFunctor_map_left.eq_1,
    pt, inl, inr, Functor.comp_obj, Monotone.functor_obj, Set.principalSegIio_toRelEmbedding,
    Arrow.leftFunc_obj, homOfLE_leOfHom, Functor.comp_map, Arrow.homMk'_left, Arrow.homMk'_right,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Arrow.leftFunc_map, Category.comp_id] at this
  simp [← this]
  rw [pushout.condition_assoc]

instance F'_woc [hF: F.IsWellOrderContinuous] : (F' F c).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨{
    desc := auxWellOrderCont_desc _ _ hm
    fac s j := by
      dsimp only [auxWellOrderCont_desc]
      apply pushout.hom_ext
      · simp
        let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) (hF.nonempty_isColimit m hm).some)
        exact H.fac (tempCocone F c s) j
      · simp
        letI : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt
        change inr (c.ι.app ⊥) ((horn 2 1).ι) ≫ s.ι.app ⊥ =
         inr (c.ι.app j) ((horn 2 1).ι) ≫ s.ι.app j
        have := s.ι.naturality (homOfLE <| bot_le (a := j))
        simp at this
        rw [← this]
        simp only [Fin.isValue, Functor.const_obj_obj, natTransLeftFunctor.eq_1, pt.eq_1, inr,
          pushout.inr, homOfLE_leOfHom, pushout.inr_desc_assoc]
    uniq s h hj := by
      apply pushout.hom_ext
      · dsimp [auxWellOrderCont_desc]
        let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) (hF.nonempty_isColimit m hm).some)
        apply H.hom_ext
        intro j
        simp
        have := H.fac (tempCocone F c s) j
        simp at this
        rw [this]
        dsimp [tempCocone, inlDescFunctor]
        rw [← hj j]
        simp
      · dsimp [auxWellOrderCont_desc]
        simp
        letI : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt
        rw [← hj ⊥]
        simp
  }⟩

noncomputable
def c' : Cocone (F' F c) where
  pt := Δ[2] ⊗ c.pt
  ι := PushoutProduct.descFunctor c.ι ((horn 2 1).ι)

omit [SuccOrder J] [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma c'_icColimit_fac (s : Cocone (F' F c)) (j : J) :
    (c' F c).ι.app j ≫ (isColimitOfPreserves (tensorLeft Δ[2]) hc).desc (tempCocone' F c s) = s.ι.app j := by
  apply pushout.hom_ext
  · have := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) j
    simp [tempCocone', inlDescFunctor] at this
    simp [c', descFunctor, tempCocone']
    rw [← this]
    rfl
  · let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc)
    apply (Limits.isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) hc).hom_ext
    intro k
    simp [c', descFunctor]
    rw [whisker_exchange_assoc]
    have := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) k
    simp at this
    rw [this]
    simp [tempCocone', inlDescFunctor, pushout.condition_assoc]
    by_cases hj : j ≤ k
    · have := s.ι.naturality (homOfLE <| hj)
      simp at this
      rw [← this]
      simp
    · rw [not_le] at hj
      have := s.ι.naturality (homOfLE <| le_of_lt hj)
      simp at this
      rw [← this]
      simp

omit [SuccOrder J] [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma c'_isColimit_uniq (s : Cocone (F' F c)) (h : (c' F c).pt ⟶ s.pt)
    (hj : ∀ (j : J), (c' F c).ι.app j ≫ h = s.ι.app j) :
    h = (isColimitOfPreserves (tensorLeft Δ[2]) hc).desc (tempCocone' F c s) := by
  apply (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).hom_ext
  intro j
  have := (inl _ _) ≫= hj j
  simp [c', descFunctor] at this ⊢
  rw [this]
  have := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) j
  simp at this
  rw [this]
  rfl

noncomputable
def c'_IsColimit : IsColimit (c' F c) where
  desc s := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).desc (tempCocone' F c s)
  fac := c'_icColimit_fac _ _ _
  uniq := c'_isColimit_uniq _ _ _

@[simp]
def _root_.CategoryTheory.Functor.succ : J ⥤ SSet where
  obj j := F.obj (Order.succ j)
  map f := F.map (homOfLE (Order.succ_le_succ f.le))
  map_comp _ _ := by rw [← F.map_comp]; rfl

@[simp]
def _root_.CategoryTheory.Functor.succNatTrans : F ⟶ F.succ where
  app j := F.map (homOfLE (Order.le_succ j))
  naturality {j j'} f := by
    simp only [Functor.succ, homOfLE_leOfHom]
    rw [← F.map_comp, ← F.map_comp]
    rfl

@[simp]
noncomputable
abbrev P := PushoutProduct.natTransLeftFunctor (F.succNatTrans) ((horn 2 1).ι)

variable {G} (h : F ⟶ G)

@[simp]
def natTransSucc : F.succ ⟶ G.succ where
  app j := h.app (Order.succ j)

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

@[simp]
noncomputable
def φ_j : (P F).obj j ⟶ (F' F c).obj j := by
  refine pushout.desc
    (inl (c.ι.app j) ((horn 2 1).ι))
    ((Λ[2, 1] : SSet) ◁ c.ι.app (Order.succ j) ≫ inr (c.ι.app j) ((horn 2 1).ι)) ?_
  simp
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  have : (F.map (homOfLE (Order.le_succ j)) ≫ c.ι.app (Order.succ j)) = c.ι.app j := by simp
  rw [this]
  simpa using pushout.condition

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma newSqComm {j} :
    (φ_j F c) ≫ (F' F c).map (homOfLE (Order.le_succ j)) =
    ((F.map (homOfLE (Order.le_succ j))) ◫ ((horn 2 1).ι)) ≫
      PushoutProduct.inl (c.ι.app (Order.succ j)) ((horn 2 1).ι) := by
  apply pushout.hom_ext (by aesop)
  simp [pushout.condition]

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    (φ_j F c) ((F.map (homOfLE (Order.le_succ j))) ◫ ((horn 2 1).ι)) :=
  PushoutCocone.mk _ _ (newSqComm F c)

@[simp]
noncomputable
def newPushoutIsColimit_desc {j} (s : PushoutCocone (φ_j F c) (F.map (homOfLE (Order.le_succ j)) ◫ (horn 2 1).ι)) :
    (F' F c).obj (Order.succ j) ⟶ s.pt :=
  pushout.desc s.inr ((inr _ _) ≫ s.inl) (by simpa using ((inr _ _) ≫= s.condition).symm)

lemma newPushoutIsColimit_fac_left {j} (s : PushoutCocone (φ_j F c) (F.map (homOfLE (Order.le_succ j)) ◫ Λ[2, 1].ι)) :
    (F' F c).map (homOfLE (Order.le_succ j)) ≫ newPushoutIsColimit_desc F c s = s.inl := by
  apply pushout.hom_ext
  · have := ((inl _ _) ≫= s.condition).symm
    dsimp only [Arrow.mk, NatTrans.arrowFunctor, newPushoutIsColimit_desc,
      Functor.succNatTrans, φ_j, Functor.id_obj, inl] at this ⊢
    rw [pushout.inl_desc_assoc, pushout.inl_desc_assoc] at this
    --rw [← this]
    dsimp only [F', natTransLeftFunctor, Functor.comp_map, NatTrans.arrowFunctor,
      Functor.const, rightFunctor, rightFunctor_map, rightFunctor_map_left, Arrow.leftFunc_map,
      Arrow.mk, Arrow.homMk', Functor.id_obj, inl, inr]
    rw [pushout.inl_desc_assoc, ← this]
    sorry
  · sorry
  -- (by simpa using ((inl _ _) ≫= s.condition).symm) (by aesop)

noncomputable
def newPushoutIsColimit {j} : IsColimit (newPushoutCocone F c j) := by
  refine PushoutCocone.IsColimit.mk _ (newPushoutIsColimit_desc F c) ?_ ?_ ?_
  · exact newPushoutIsColimit_fac_left _ _
  · sorry
  · sorry
    /-
    intro _ _ h _
    exact pushout.hom_ext (by aesop) (by simp [← h])
    -/

def newPushoutIsPushout (j : J) : CategoryTheory.IsPushout
  (φ_j F c)
  (F.map (homOfLE (Order.le_succ j)) ◫ (horn 2 1).ι)
  ((F' F c).map (homOfLE (Order.le_succ j)))
  (PushoutProduct.inl (c.ι.app (Order.succ j)) ((horn 2 1).ι))
  := IsPushout.of_isColimit (newPushoutIsColimit F c (j := j))

end CategoryTheory.PushoutProduct
