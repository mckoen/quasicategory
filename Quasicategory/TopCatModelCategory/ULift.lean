import Mathlib.Order.Shrink

universe v u

variable (α : Type u)

def orderIsoULift [Preorder α] : α ≃o ULift.{v} α where
  toEquiv := Equiv.ulift.symm
  map_rel_iff' := by rfl

instance [Preorder α] [SuccOrder α] : SuccOrder (ULift.{v} α) :=
  SuccOrder.ofOrderIso (orderIsoULift α)

instance [Preorder α] [WellFoundedLT α] : WellFoundedLT (ULift.{v} α) where
  wf := (orderIsoULift.{v} α).symm.toRelIsoLT.toRelEmbedding.isWellFounded.wf
