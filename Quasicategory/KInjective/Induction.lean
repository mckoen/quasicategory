import Quasicategory.KInjective.WellOrderContinuous

universe v u

namespace CategoryTheory

open Opposite

namespace Functor

variable {J : Type u} [LinearOrder J] [IsWellOrder J (· < ·)] (F : Jᵒᵖ ⥤ Type v)

@[simps]
def _root_.PrincipalSeg.ofElementSectionsMk {j : J} (x : F.obj (op j)):
    (((PrincipalSeg.ofElement (· < ·) j).functorToOver ⋙
      Over.forget _).op ⋙ F).sections where
  val a := F.map (homOfLE a.unop.2.le).op x
  property _ := by
    dsimp
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp]

structure WellOrderInductionData where
  succ (j : J) (hj : j < wellOrderSucc j) : F.obj (op j) → F.obj (op (wellOrderSucc j))
  map_succ (j : J) (hj : j < wellOrderSucc j) (x : F.obj (op j)) : F.map (homOfLE (self_le_wellOrderSucc j)).op (succ j hj x) = x
  desc (j : J) [IsWellOrderLimitElement j] (x : (((PrincipalSeg.ofElement (· < ·) j).functorToOver ⋙
      Over.forget _).op ⋙ F).sections) : F.obj (op j)
  fac (j : J) [IsWellOrderLimitElement j] (i : J) (hi : i < j)
    (x : (((PrincipalSeg.ofElement (· < ·) j).functorToOver ⋙
      Over.forget _).op ⋙ F).sections) :
        F.map (homOfLE (le_of_lt hi)).op (desc j x) = x.val (op ⟨i, hi⟩)

namespace WellOrderInductionData

variable {F} [OrderBot J]
variable (d : F.WellOrderInductionData)

structure Extension (val₀ : F.obj (op ⊥)) (j : J) where
  val : F.obj (op j)
  map_zero : F.map (homOfLE bot_le).op val = val₀
  map_succ (i : J) (hi : i < j) :
    F.map (homOfLE (wellOrderSucc_le hi)).op val =
      d.succ i (self_lt_wellOrderSucc hi) (F.map (homOfLE hi.le).op val)
  map_limit (i : J) [IsWellOrderLimitElement i] (hi : i ≤ j) :
    F.map (homOfLE hi).op val = d.desc i (PrincipalSeg.ofElementSectionsMk F (F.map (homOfLE hi).op val))

namespace Extension

variable {d}
variable {val₀ : F.obj (op ⊥)}

def ofLE {j : J} (e : d.Extension val₀ j) {i : J} (h : i ≤ j) :
    d.Extension val₀ i where
  val := F.map (homOfLE h).op e.val
  map_zero := by rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp, e.map_zero]
  map_succ k hk := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
      homOfLE_comp, homOfLE_comp, e.map_succ k (lt_of_lt_of_le hk h)]
  map_limit k _ hk := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp]
    exact e.map_limit k (hk.trans h)

lemma ext' {e e' : d.Extension val₀ j} (h : e.val = e'.val) : e = e' := by
  cases e
  cases e'
  subst h
  rfl

instance (j : J) : Subsingleton (d.Extension val₀ j) := by
  apply @WellFoundedLT.induction J _ _ (fun j => Subsingleton (d.Extension val₀ j))
  intro j hj
  obtain rfl|⟨i, rfl, hi⟩|_ := eq_bot_or_eq_succ_or_isWellOrderLimitElement j
  · refine Subsingleton.intro (fun e₁ e₂ => ext' ?_)
    have h₁ := e₁.map_zero
    have h₂ := e₂.map_zero
    erw [Functor.map_id] at h₁ h₂
    dsimp at h₁ h₂
    rw [h₁, h₂]
  · refine Subsingleton.intro (fun e₁ e₂ => ext' ?_)
    have h₁ := e₁.map_succ i hi
    have h₂ := e₂.map_succ i hi
    erw [Functor.map_id] at h₁ h₂
    dsimp at h₁ h₂
    rw [h₁, h₂]
    congr 1
    have := hj i hi
    exact congr_arg Extension.val (Subsingleton.elim (e₁.ofLE hi.le) (e₂.ofLE hi.le))
  · refine Subsingleton.intro (fun e₁ e₂ => ext' ?_)
    have h₁ := e₁.map_limit j (by rfl)
    have h₂ := e₂.map_limit j (by rfl)
    erw [Functor.map_id] at h₁ h₂
    dsimp at h₁ h₂
    rw [h₁, h₂]
    congr 1
    ext ⟨a, ha : a < j⟩
    dsimp
    have := hj a ha
    exact congr_arg Extension.val (Subsingleton.elim (e₁.ofLE ha.le) (e₂.ofLE ha.le))

lemma compatibility {j : J} (e : d.Extension val₀ j) {i : J}
    (e' : d.Extension val₀ i) (h : i ≤ j) :
    F.map (homOfLE h).op e.val = e'.val := by
  obtain rfl : e' = e.ofLE h := Subsingleton.elim _ _
  rfl

end Extension

variable (val₀)

def extensionZero : d.Extension val₀ ⊥ where
  val := val₀
  map_zero := by
    erw [Functor.map_id]
    rfl
  map_succ i hi := by simp at hi
  map_limit i _ hi := by
    exfalso
    exact IsWellOrderLimitElement.neq_bot i (by simpa using hi)

variable {val₀}

def extensionSucc {j : J} (e : d.Extension val₀ j) (hj : j < wellOrderSucc j) :
    d.Extension val₀ (wellOrderSucc j) where
  val := d.succ j hj e.val
  map_zero := by
    have h := congr_arg (F.map (homOfLE (bot_le : ⊥ ≤ j)).op) (d.map_succ j hj e.val)
    rw [e.map_zero, ← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp] at h
    exact h
  map_succ i hi := by
    obtain rfl|hi' := eq_or_lt_of_le (le_of_lt_wellOrderSucc hi)
    · rw [d.map_succ _ hi]
      erw [Functor.map_id]
      rfl
    · rw [← homOfLE_comp (le_of_lt_wellOrderSucc hi) hj.le, op_comp,
        FunctorToTypes.map_comp_apply, d.map_succ _ hj, ← e.map_succ i hi',
        ← homOfLE_comp (wellOrderSucc_le hi') hj.le, op_comp,
        FunctorToTypes.map_comp_apply, d.map_succ _ hj]
  map_limit i _ hi := by
    obtain rfl|hi' := eq_or_lt_of_le hi
    · simpa using IsWellOrderLimitElement.neq_succ _ hj
    · have h := congr_arg (F.map (homOfLE (le_of_lt_wellOrderSucc hi')).op) (d.map_succ j hj e.val)
      rw [e.map_limit i (le_of_lt_wellOrderSucc hi'), ← FunctorToTypes.map_comp_apply,
        ← op_comp, homOfLE_comp] at h
      rw [h]
      congr 1
      ext ⟨a, ha⟩
      dsimp
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp, d.fac i a ha]
      dsimp
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp]

variable (val₀) in
def extensionLimit (j : J) [IsWellOrderLimitElement j]
    (e : ∀ (i : J) (_ : i < j), d.Extension val₀ i) :
    d.Extension val₀ j where
  val := d.desc j
    { val := fun ⟨i, (hi : i < j)⟩ => (e i hi).val
      property := fun _ => Extension.compatibility _ _ _ }
  map_zero := by
    have h := (e ⊥ (IsWellOrderLimitElement.bot_lt j)).map_zero
    erw [Functor.map_id] at h
    dsimp at h ⊢
    rw [d.fac j ⊥ (IsWellOrderLimitElement.bot_lt j)]
    exact h
  map_succ := fun i hi => by
    have hi' := IsWellOrderLimitElement.wellOrderSucc_lt hi
    convert (e (wellOrderSucc i) hi').map_succ i
      (self_lt_wellOrderSucc hi) using 1
    · erw [Functor.map_id]
      rw [d.fac j _ hi']
      rfl
    · rw [← homOfLE_comp (self_lt_wellOrderSucc hi).le hi'.le, op_comp,
        FunctorToTypes.map_comp_apply, d.fac j _ hi']
  map_limit := fun i _ hi => by
    obtain rfl|h := eq_or_lt_of_le hi
    · erw [Functor.map_id]
      dsimp
      congr 1
      ext ⟨k, hk⟩
      dsimp
      rw [d.fac i _ hk]
    · have eq := (e i h).map_limit i (by rfl)
      erw [Functor.map_id] at eq
      rw [d.fac j _ h]
      exact eq

instance (j : J) : Nonempty (d.Extension val₀ j) := by
  apply @WellFoundedLT.induction J _ _ (fun j => Nonempty (d.Extension val₀ j))
  intro j hj
  obtain rfl|⟨i, rfl, hi⟩|_ := eq_bot_or_eq_succ_or_isWellOrderLimitElement j
  · exact ⟨d.extensionZero val₀⟩
  · exact ⟨d.extensionSucc (hj i hi).some hi⟩
  · exact ⟨d.extensionLimit val₀ j (fun i hi => (hj i hi).some)⟩

noncomputable instance (j : J) : Unique (d.Extension val₀ j) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

variable (val₀ : F.obj (op ⊥))

noncomputable def sectionsMk : F.sections where
  val j := (default : d.Extension val₀ j.unop).val
  property _ := Extension.compatibility _ _ _

end WellOrderInductionData

end Functor

end CategoryTheory
