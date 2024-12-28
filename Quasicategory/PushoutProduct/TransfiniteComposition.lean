import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

universe v' v u' u

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (g : X ⟶ Y) (f : A ⟶ B)


variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet) [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)

noncomputable
abbrev F' : J ⥤ SSet := PushoutProduct.natTransLeftFunctor c.ι (hornInclusion 2 1)

instance : (F' F c).IsWellOrderContinuous := sorry

noncomputable
def c' : Cocone (F' F c) where
  pt := Δ[2] ⊗ c.pt
  ι := PushoutProduct.descFunctor c.ι (hornInclusion 2 1)

@[simp]
def _root_.CategoryTheory.Functor.succ : J ⥤ SSet where
  obj j := F.obj (Order.succ j)
  map f := F.map (homOfLE (Order.succ_le_succ f.le))
  map_comp _ _ := by rw [← F.map_comp]; rfl

@[simp]
def _root_.CategoryTheory.Functor.succNatTrans : F ⟶ F.succ where
  app j := F.map (homOfLE (Order.le_succ j))
  naturality {j j'} f := by
    simp
    rw [← F.map_comp, ← F.map_comp]
    suffices f ≫ homOfLE (Order.le_succ j') =
      (homOfLE (Order.le_succ j)) ≫ homOfLE (Order.succ_le_succ f.le) by rfl
    rfl

noncomputable
abbrev P := PushoutProduct.natTransLeftFunctor (F.succNatTrans) (hornInclusion 2 1)

@[simp]
def φaux : (F.succ) ⟶ (Functor.const J).obj c.pt where
  app j := c.ι.app (Order.succ j)

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
@[simp]
lemma φaux' : (F.succNatTrans) ≫ (φaux F c) = c.ι := by
  simp_all only [Functor.succ, homOfLE_leOfHom, Functor.succNatTrans, φaux]
  ext x n a : 4
  simp_all only [Functor.const_obj_obj, homOfLE_leOfHom, NatTrans.comp_app, NatTrans.naturality, Functor.const_obj_map,
    Category.comp_id]

noncomputable
def Pj_jsucc (j : J) :=
  PushoutProduct.pt (F.map (homOfLE (Order.le_succ j))) (hornInclusion 2 1)

noncomputable
def φj (j : J) : (Pj_jsucc F j) ⟶ (F' F c).obj j := by
  refine PushoutProduct.desc _ _ ?_ ?_ ?_
  · exact PushoutProduct.inl (c.ι.app j) (hornInclusion 2 1)
  · exact Λ[2, 1] ◁ (c.ι.app (Order.succ j)) ≫ PushoutProduct.inr (c.ι.app j) (hornInclusion 2 1)
  · sorry

-- not defeq but right approach, (P F) ⟶ (F' F c)
set_option maxHeartbeats 400000 in
noncomputable
def φ : P F ⟶ natTransLeftFunctor (F.succNatTrans ≫ φaux F c) (hornInclusion 2 1) :=
  PushoutProduct.natTransLeftFunctor_comp (F.succNatTrans) (hornInclusion 2 1) (φaux F c)

lemma newSqComm :
  ((F.map (homOfLE (Order.le_succ j))) ◫ (hornInclusion 2 1)) ≫ PushoutProduct.inl (c.ι.app (Order.succ j)) (hornInclusion 2 1)
    = (φj F c j) ≫ (F' F c).map (homOfLE (Order.le_succ j)) := by sorry

noncomputable
def newPushoutCocone (j : J) : PushoutCocone ((F.map (homOfLE (Order.le_succ j))) ◫ (hornInclusion 2 1)) (φj F c j) :=
  PushoutCocone.mk _ _ (newSqComm F c)

noncomputable
def newPushoutIsColimit : IsColimit (newPushoutCocone F c j) := by
  apply PushoutCocone.IsColimit.mk
  · sorry
  · sorry
  · sorry
  · sorry

end CategoryTheory.PushoutProduct
