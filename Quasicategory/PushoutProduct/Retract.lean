import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.Retract

universe v' v u' u

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (g : X ⟶ Y) (f : A ⟶ B)

variable {f g} (h : RetractArrow f g)

noncomputable
def pushoutProduct.i.left :
    pt f ((horn 2 1).ι) ⟶ pt g ((horn 2 1).ι) :=
  (PushoutProduct.desc f ((horn 2 1).ι))
    (Δ[2] ◁ h.i.left ≫ (PushoutProduct.inl g ((horn 2 1).ι)))
    ((Λ[2, 1] : SSet) ◁ h.i.right ≫ (PushoutProduct.inr g ((horn 2 1).ι)))
    (by
      dsimp
      rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ← h.i_w,
        MonoidalCategory.whiskerLeft_comp, ← whisker_exchange, Category.assoc, Category.assoc,
        ← (PushoutProduct.IsPushout g ((horn 2 1).ι)).w])

noncomputable
def pushoutProduct.r.left :
    pt g ((horn 2 1).ι) ⟶ pt f ((horn 2 1).ι) :=
  (PushoutProduct.desc g ((horn 2 1).ι))
    (Δ[2] ◁ h.r.left ≫ (PushoutProduct.inl f ((horn 2 1).ι)))
    ((Λ[2, 1] : SSet) ◁ h.r.right ≫ (PushoutProduct.inr f ((horn 2 1).ι)))
    (by
      dsimp
      rw [← Category.assoc, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, ← h.r_w,
        MonoidalCategory.whiskerLeft_comp, ← whisker_exchange, Category.assoc, Category.assoc,
        ← (PushoutProduct.IsPushout f ((horn 2 1).ι)).w])

lemma pushoutProduct.retract_left : pushoutProduct.i.left h ≫ pushoutProduct.r.left h = 𝟙 _ := by
  dsimp [i.left, r.left]
  refine (PushoutProduct.IsPushout f ((horn 2 1).ι)).hom_ext ?_ ?_
  · simp only [Fin.isValue, IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h.retract_left]
    rfl
  · simp only [Fin.isValue, IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, h.retract_right]
    rfl

lemma pushoutProduct.i_w : pushoutProduct.i.left h ≫ g ◫ ((horn 2 1).ι) =
    (f ◫ ((horn 2 1).ι)) ≫ Δ[2] ◁ h.i.right := by
  dsimp [i.left]
  apply (PushoutProduct.IsPushout f ((horn 2 1).ι)).hom_ext
  · dsimp [pushoutProduct]
    rw [IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc, ← Category.assoc,
      IsPushout.inl_desc, ← MonoidalCategory.whiskerLeft_comp, h.i_w]
    rfl
  · dsimp [pushoutProduct]
    rw [IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc, ← Category.assoc,
      IsPushout.inr_desc, whisker_exchange]

lemma pushoutProduct.r_w : pushoutProduct.r.left h ≫ f ◫ ((horn 2 1).ι) =
    (g ◫ ((horn 2 1).ι)) ≫ Δ[2] ◁ h.r.right := by
  dsimp [r.left]
  apply (PushoutProduct.IsPushout g ((horn 2 1).ι)).hom_ext
  · dsimp [pushoutProduct]
    rw [IsPushout.inl_desc_assoc, Category.assoc, IsPushout.inl_desc, ← Category.assoc,
      IsPushout.inl_desc, ← MonoidalCategory.whiskerLeft_comp, h.r_w]
    rfl
  · dsimp [pushoutProduct]
    rw [IsPushout.inr_desc_assoc, Category.assoc, IsPushout.inr_desc, ← Category.assoc,
      IsPushout.inr_desc, whisker_exchange]

noncomputable
def pushoutProduct.RetractArrow :
    RetractArrow (f ◫ ((horn 2 1).ι)) (g ◫ ((horn 2 1).ι)) where
  i := {
    left := pushoutProduct.i.left h
    right :=  Δ[2] ◁ h.i.right
    w := pushoutProduct.i_w h
  }
  r := {
    left := pushoutProduct.r.left h
    right :=  Δ[2] ◁ h.r.right
    w := pushoutProduct.r_w h
  }
  retract := Arrow.hom_ext _ _ (pushoutProduct.retract_left h) (by
    dsimp
    rw [← MonoidalCategory.whiskerLeft_comp, h.retract_right]
    rfl)

end CategoryTheory.PushoutProduct
