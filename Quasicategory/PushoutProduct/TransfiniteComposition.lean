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

noncomputable
def auxWellOrderCont_desc [hF: F.IsWellOrderContinuous]
    {m : J} (hm : Order.IsSuccLimit m) (s : Cocone ((Set.principalSegIio m).monotone.functor ⋙ (F' F c))) :
    ((Set.principalSegIio m).cocone (F' F c)).pt ⟶ s.pt := by
  let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) (hF.nonempty_isColimit m hm).some)
  let H'' := (Limits.isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) (hF.nonempty_isColimit m hm).some)
  refine PushoutProduct.desc _ _ (H.desc (tempCocone F c s)) ((inr _ _) ≫ s.ι.app ⟨⊥, hm.bot_lt⟩) ?_
  apply H''.hom_ext
  intro j
  have Hfac := H.fac (tempCocone F c s) j
  dsimp at Hfac
  simp only [Fin.isValue, Functor.comp_obj, Monotone.functor_obj,
    Set.principalSegIio_toRelEmbedding, tensorLeft_obj, natTransLeftFunctor.eq_1,
    Functor.const_obj_obj, pt.eq_1, Functor.mapCocone_pt, PrincipalSeg.cocone_pt,
    Set.principalSegIio_top, Functor.mapCocone_ι_app, PrincipalSeg.cocone_ι_app, homOfLE_leOfHom,
    tensorLeft_map, inr, IsPushout.cocone_inr]
  rw [← Category.assoc, @whisker_exchange, Category.assoc, Hfac]
  dsimp [tempCocone, inlDescFunctor]
  letI : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality]
  have := (s.ι.naturality (homOfLE <| bot_le (a := j)))
  simp only [natTransLeftFunctor.eq_1, Functor.const_obj_obj, Fin.isValue, pt.eq_1,
    homOfLE_leOfHom,
    natTransLeftFunctor_map, desc, inl, IsPushout.cocone_inl, Functor.const_obj_map,
    MonoidalCategory.whiskerLeft_id, inr, IsPushout.cocone_inr, Category.id_comp,
    Category.comp_id] at this
  change _ = _ ≫ _ ≫ s.ι.app ⊥
  rw [← this]
  simp only [Fin.isValue, natTransLeftFunctor.eq_1, Functor.const_obj_obj, pt.eq_1, homOfLE_leOfHom,
    Functor.const_obj_map, Category.comp_id, Functor.comp_obj, Monotone.functor_obj,
    Set.principalSegIio_toRelEmbedding, Functor.comp_map, natTransLeftFunctor_map, desc, inl,
    IsPushout.cocone_inl, MonoidalCategory.whiskerLeft_id, inr, IsPushout.cocone_inr,
    Category.id_comp, IsPushout.inr_desc_assoc]
  change (horn 2 1).ι ▷ F.obj ↑j ≫ inl (c.ι.app ↑j) ((horn 2 1).ι) ≫ s.ι.app j =
    (Λ[2, 1] : SSet) ◁ c.ι.app ↑j ≫ inr (c.ι.app ↑j) ((horn 2 1).ι) ≫ s.ι.app j
  rw [← Category.assoc, w, Category.assoc]

-- inefficient and messy but it works
instance F'_woc [hF: F.IsWellOrderContinuous] : (F' F c).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨{
    desc := auxWellOrderCont_desc _ _ hm
    fac s j := by
      dsimp only [auxWellOrderCont_desc]
      apply (IsPushout _ _).hom_ext
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
          IsPushout.cocone_inr, homOfLE_leOfHom, IsPushout.inr_desc_assoc]
    uniq s h hj := by
      apply (IsPushout _ _).hom_ext
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
        simp only [Fin.isValue, homOfLE_leOfHom, natTransLeftFunctor.eq_1, Functor.const_obj_obj,
          pt.eq_1, Functor.comp_obj, Monotone.functor_obj, Set.principalSegIio_toRelEmbedding,
          PrincipalSeg.cocone_pt, Set.principalSegIio_top, PrincipalSeg.cocone_ι_app,
          natTransLeftFunctor_map, desc, inl, IsPushout.cocone_inl, Functor.const_obj_map,
          MonoidalCategory.whiskerLeft_id, inr, IsPushout.cocone_inr, Category.id_comp,
          IsPushout.inl_desc_assoc, Category.assoc]
      · dsimp [auxWellOrderCont_desc]
        simp
        rw [← hj ⟨⊥, hm.bot_lt⟩]
        simp
  }⟩

noncomputable
def c' : Cocone (F' F c) where
  pt := Δ[2] ⊗ c.pt
  ι := PushoutProduct.descFunctor c.ι ((horn 2 1).ι)

set_option maxHeartbeats 400000 in
/-- also really really bad -/
noncomputable
def c'_IsColimit : IsColimit (c' F c) where
  desc s := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).desc (tempCocone' F c s)
  fac s j := by
    apply (IsPushout _ _).hom_ext
    · have := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) j
      simp [tempCocone', inlDescFunctor] at this
      rw [← this]
      simp [c', descFunctor, tempCocone']
      rfl
    · let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc)
      apply (Limits.isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) hc).hom_ext
      intro k
      simp [c', descFunctor]
      rw [← Category.assoc, @whisker_exchange, Category.assoc]
      have := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) k
      simp at this
      rw [this]
      simp [tempCocone', inlDescFunctor]
      have a := (w (c.ι.app k) ((horn 2 1).ι)) --=≫ s.ι.app j
      simp at a
      rw [← Category.assoc, a]
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
  uniq s h hj := by
    apply (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).hom_ext
    intro j
    have := (inl _ _) ≫= hj j
    simp [c', descFunctor] at this ⊢
    rw [this]
    have := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) j
    simp at this
    rw [this]
    rfl

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
  refine (IsPushout _ _).desc
    (inl (c.ι.app j) ((horn 2 1).ι))
    ((Λ[2, 1] : SSet) ◁ c.ι.app (Order.succ j) ≫ inr (c.ι.app j) ((horn 2 1).ι)) ?_
  simp
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  have : (F.map (homOfLE (Order.le_succ j)) ≫ c.ι.app (Order.succ j)) = c.ι.app j := by simp
  rw [this]
  simpa using w (c.ι.app j) ((horn 2 1).ι)

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma newSqComm {j} :
    (φ_j F c) ≫ (F' F c).map (homOfLE (Order.le_succ j)) =
    ((F.map (homOfLE (Order.le_succ j))) ◫ ((horn 2 1).ι)) ≫
      PushoutProduct.inl (c.ι.app (Order.succ j)) ((horn 2 1).ι) := by
  apply (IsPushout _ _).hom_ext (by aesop)
  simp
  have := w (c.ι.app (Order.succ j)) ((horn 2 1).ι)
  dsimp at this
  rw [this]

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    (φ_j F c) ((F.map (homOfLE (Order.le_succ j))) ◫ ((horn 2 1).ι)) :=
  PushoutCocone.mk _ _ (newSqComm F c)

@[simp]
noncomputable
def newPushoutIsColimit_desc {j} (s : PushoutCocone (φ_j F c) (F.map (homOfLE (Order.le_succ j)) ◫ (horn 2 1).ι)) :
    (F' F c).obj (Order.succ j) ⟶ s.pt :=
  (IsPushout _ _).desc s.inr ((inr _ _) ≫ s.inl) (by simpa using ((inr _ _) ≫= s.condition).symm)

set_option maxHeartbeats 800000 in
noncomputable
def newPushoutIsColimit {j} : IsColimit (newPushoutCocone F c j) := by
  refine PushoutCocone.IsColimit.mk _ (newPushoutIsColimit_desc F c) ?_ ?_ ?_
  · intro s
    exact (IsPushout _ _).hom_ext (by simpa using ((inl _ _) ≫= s.condition).symm) (by aesop)
  · aesop
  · intro _ _ h _
    exact (IsPushout _ _).hom_ext (by aesop) (by simp [← h])

def newPushoutIsPushout (j : J) : CategoryTheory.IsPushout
  (φ_j F c)
  (F.map (homOfLE (Order.le_succ j)) ◫ (horn 2 1).ι)
  ((F' F c).map (homOfLE (Order.le_succ j)))
  (PushoutProduct.inl (c.ι.app (Order.succ j)) ((horn 2 1).ι))
  := IsPushout.of_isColimit (newPushoutIsColimit F c (j := j))

end CategoryTheory.PushoutProduct
