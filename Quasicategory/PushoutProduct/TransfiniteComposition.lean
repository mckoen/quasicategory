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

instance [hF: F.IsWellOrderContinuous] : (F' F c).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨{
    desc s := by
      let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) (hF.nonempty_isColimit m hm).some)
      refine PushoutProduct.desc _ _ ?_ ?_ ?_
      · exact H.desc (tempCocone F c s)
      ·
        exact (PushoutProduct.inr _ _) ≫ s.ι.app ⟨⊥, hm.bot_lt⟩
      ·
        --simp_all only [Fin.isValue, natTransLeftFunctor.eq_1, Functor.const_obj_obj, pt.eq_1, Monotone.functor_obj, inr,
        --  IsPushout.cocone_inr]
        change hornInclusion 2 1 ▷ F.obj m ≫ H.desc (tempCocone F c s) = _
        dsimp
        --apply H.hom_ext
        --intro j
        sorry
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
