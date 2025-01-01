import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Closed.FunctorToTypes

universe w v u

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (f : A ⟶ B) (g : X ⟶ Y)

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet) [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)

@[simp]
noncomputable
abbrev F' : J ⥤ SSet := PushoutProduct.natTransLeftFunctor c.ι (hornInclusion 2 1)

instance ll {S : SSet} : Functor.IsLeftAdjoint (tensorLeft S) where
  exists_rightAdjoint := ⟨FunctorToTypes.rightAdj S, ⟨FunctorToTypes.adj S⟩⟩

noncomputable
instance rr {S : SSet} : PreservesColimitsOfSize (tensorLeft S) :=
  Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _

noncomputable
def tempCocone (s : Cocone ((F' F c).restrictionLT m)) :
    Cocone (F.restrictionLT m ⋙ tensorLeft Δ[2]) where
  pt := s.pt
  ι := (whiskerLeft (Monotone.functor _) (inlDescFunctor c.ι (hornInclusion 2 1))) ≫ s.ι

noncomputable
def tempCocone' (s : Cocone ((F' F c).restrictionLT m)) :
    Cocone (((Functor.const J).obj c.pt).restrictionLT m ⋙ tensorLeft Λ[2, 1]) where
  pt := s.pt
  ι := (whiskerLeft (Monotone.functor _) (inrDescFunctor c.ι (hornInclusion 2 1))) ≫ s.ι

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
    {m : J} (hm : Order.IsSuccLimit m) (s : Cocone ((F' F c).restrictionLT m)) :
    ((F' F c).coconeLT m).pt ⟶ s.pt := by
  let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) (hF.nonempty_isColimit m hm).some)
  let H'' := (Limits.isColimitOfPreserves (tensorLeft Λ[2, 1]) (hF.nonempty_isColimit m hm).some)
  refine PushoutProduct.desc _ _ (H.desc (tempCocone F c s)) ((inr _ _) ≫ s.ι.app ⟨⊥, hm.bot_lt⟩) ?_
  apply H''.hom_ext
  intro j
  have Hfac := H.fac (tempCocone F c s) j
  dsimp at Hfac
  simp only [Fin.isValue, Functor.comp_obj, Functor.restrictionLT_obj, tensorLeft_obj,
    natTransLeftFunctor.eq_1, Functor.const_obj_obj, pt.eq_1, Functor.mapCocone_pt,
    Functor.coconeLT_pt, Functor.mapCocone_ι_app, Functor.coconeLT_ι_app,
    Monotone.functor_obj, subset_refl, Set.coe_inclusion, homOfLE_leOfHom, tensorLeft_map,
    inr, IsPushout.cocone_inr]
  rw [← Category.assoc, @whisker_exchange, Category.assoc, Hfac]
  dsimp [tempCocone, inlDescFunctor]
  letI : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality]
  have := (s.ι.naturality (homOfLE <| bot_le (a := j)))
  simp only [natTransLeftFunctor.eq_1, Functor.const_obj_obj, Fin.isValue, pt.eq_1,
    Functor.restrictionLT_obj, homOfLE_leOfHom, Functor.restrictionLT_map,
    natTransLeftFunctor_map, desc, inl, IsPushout.cocone_inl, Functor.const_obj_map,
    MonoidalCategory.whiskerLeft_id, inr, IsPushout.cocone_inr, Category.id_comp,
    Category.comp_id] at this
  change _ = _ ≫ _ ≫ s.ι.app ⊥
  rw [← this]
  simp only [Fin.isValue, natTransLeftFunctor.eq_1, Functor.const_obj_obj, pt.eq_1,
    homOfLE_leOfHom, Functor.const_obj_map, Category.comp_id, Functor.restrictionLT_obj,
    IsPushout.inr_desc_assoc]
  change hornInclusion 2 1 ▷ F.obj ↑j ≫ inl (c.ι.app ↑j) (hornInclusion 2 1) ≫ s.ι.app j =
    Λ[2, 1] ◁ c.ι.app ↑j ≫ inr (c.ι.app ↑j) (hornInclusion 2 1) ≫ s.ι.app j
  rw [← Category.assoc, w, Category.assoc]

-- inefficient and messy but it works
instance [hF: F.IsWellOrderContinuous] : (F' F c).IsWellOrderContinuous where
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
        change inr (c.ι.app ⊥) (hornInclusion 2 1) ≫ s.ι.app ⊥ =
         inr (c.ι.app j) (hornInclusion 2 1) ≫ s.ι.app j
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
          pt.eq_1, Functor.restrictionLT_obj, Functor.coconeLT_pt, Functor.coconeLT_ι_app,
          natTransLeftFunctor_map, desc, Monotone.functor_obj, subset_refl, Set.coe_inclusion, inl,
          IsPushout.cocone_inl, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id, inr,
          IsPushout.cocone_inr, Category.id_comp, IsPushout.inl_desc_assoc, Category.assoc]
      · dsimp [auxWellOrderCont_desc]
        simp
        rw [← hj ⟨⊥, hm.bot_lt⟩]
        simp
  }⟩

noncomputable
def c' : Cocone (F' F c) where
  pt := Δ[2] ⊗ c.pt
  ι := PushoutProduct.descFunctor c.ι (hornInclusion 2 1)

def c'_IsColimit : IsColimit (c' F c) := sorry

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
abbrev P := PushoutProduct.natTransLeftFunctor (F.succNatTrans) (hornInclusion 2 1)

variable {G} (h : F ⟶ G)

@[simp]
def natTransSucc : F.succ ⟶ G.succ where
  app j := h.app (Order.succ j)

@[simp]
def φaux : (F.succ) ⟶ (Functor.const J).obj c.pt := natTransSucc F c.ι

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
@[simp]
lemma φaux' : (F.succNatTrans) ≫ (natTransSucc F c.ι) = c.ι := by
  ext
  simp

/-
noncomputable
def Pj_jsucc (j : J) :=
  PushoutProduct.pt (F.map (homOfLE (Order.le_succ j))) (hornInclusion 2 1)
-/

-- not defeq but right approach, (P F) ⟶ (F' F c)
noncomputable
def φ : P F ⟶ natTransLeftFunctor (F.succNatTrans ≫ (natTransSucc F c.ι)) (hornInclusion 2 1) :=
  PushoutProduct.natTransLeftFunctor_comp (F.succNatTrans) (hornInclusion 2 1) (natTransSucc F c.ι)

def φ' : (P F) ⟶ (F' F c) where
  app j := by
    have := (φ F c).app j
    rw [φaux'] at this
    dsimp only [F']
    sorry

noncomputable
def φj (j : J) : (P F).obj j ⟶ (F' F c).obj j := sorry

lemma newSqComm :
    (φj F c j) ≫ (F' F c).map (homOfLE (Order.le_succ j)) =
    ((F.map (homOfLE (Order.le_succ j))) ◫ (hornInclusion 2 1)) ≫
      PushoutProduct.inl (c.ι.app (Order.succ j)) (hornInclusion 2 1) := by
  sorry

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    (φj F c j) ((F.map (homOfLE (Order.le_succ j))) ◫ (hornInclusion 2 1)) :=
  PushoutCocone.mk _ _ (newSqComm F c)

noncomputable
def newPushoutIsColimit : IsColimit (newPushoutCocone F c j) := by
  apply PushoutCocone.IsColimit.mk
  · sorry
  · sorry
  · sorry
  · sorry

def newPushoutIsPushout (j : J) : CategoryTheory.IsPushout
  (φj F c j)
  (F.map (homOfLE (Order.le_succ j)) ◫ hornInclusion 2 1)
  ((F' F c).map (homOfLE (Order.le_succ j)))
  (PushoutProduct.inl (c.ι.app (Order.succ j)) (hornInclusion 2 1))
  := IsPushout.of_isColimit (newPushoutIsColimit F c (j := j))

end CategoryTheory.PushoutProduct
