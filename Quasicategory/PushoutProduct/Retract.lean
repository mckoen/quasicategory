import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.Retract

universe v' v u' u

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (g : X ⟶ Y) (f : A ⟶ B)

variable {f g} (h : RetractArrow f g)

noncomputable
def pushoutProduct.RetractArrow :
    RetractArrow (f ◫ Λ[2, 1].ι) (g ◫ Λ[2, 1].ι) :=
  Retract.map h (rightBifunctor.obj (.mk Λ[2, 1].ι))

end CategoryTheory.PushoutProduct
