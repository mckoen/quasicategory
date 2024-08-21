import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Order.InitialSeg

universe u

open CategoryTheory Category Limits

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C)

def over (S : C) : MorphismProperty (Over S) := fun _ _ f => W f.left

@[simp]
lemma mem_over_iff {S : C} {X Y : Over S} (f : X ⟶ Y) : W.over S f ↔ W f.left := by rfl

end MorphismProperty

end CategoryTheory


namespace PrincipalSeg

variable {α β : Type*} [PartialOrder α] [PartialOrder β] (h : PrincipalSeg (· < · : α → _) (· < · : β → _))

noncomputable def orderIso : α ≃o { x | x < h.top } where
  toEquiv := Equiv.ofBijective (fun a => ⟨h a, h.down.2 ⟨a, rfl⟩⟩) ⟨fun _ _ => by simp, fun ⟨y, hy⟩ => by
    obtain ⟨x, rfl⟩ := h.down.1 hy
    exact ⟨x, rfl⟩⟩
  map_rel_iff' {x₁ x₂} := by
    have : h x₁ < h x₂ ↔ x₁ < x₂ := h.toRelEmbedding.map_rel_iff'
    dsimp
    simp only [Subtype.mk_le_mk]
    constructor
    · intro h'
      obtain h''|h'' := h'.lt_or_eq
      · exact (this.1 h'').le
      · simp only [EmbeddingLike.apply_eq_iff_eq] at h''
        rw [h'']
    · intro h'
      obtain h''|rfl := h'.lt_or_eq
      · exact (this.2 h'').le
      · rfl

lemma orderIso_apply (a : α) : h.orderIso a = ⟨h a, h.down.2 ⟨a, rfl⟩⟩ := rfl

end PrincipalSeg
/-
namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
@[simps]
def equivalence : α ≌ β where
  functor := e.monotone.functor
  inverse := e.symm.monotone.functor
  unitIso := NatIso.ofComponents (fun x => eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun x => eqToIso (by simp))

end OrderIso
-/

section

variable {α : Type*} [LinearOrder α] [IsWellOrder α (· < ·)]

noncomputable def wellOrderSucc (a : α) : α :=
  (@IsWellFounded.wf α (· < ·)).succ a

lemma self_le_wellOrderSucc (a : α) : a ≤ wellOrderSucc a := by
  by_cases h : ∃ b, a < b
  · exact (IsWellFounded.wf.lt_succ h).le
  · dsimp [wellOrderSucc, WellFounded.succ]
    rw [dif_neg h]

lemma wellOrderSucc_le {a b : α} (ha : a < b) : wellOrderSucc a ≤ b := by
  dsimp [wellOrderSucc, WellFounded.succ]
  rw [dif_pos ⟨_, ha⟩]
  exact WellFounded.min_le _ ha

lemma self_lt_wellOrderSucc {a b : α} (h : a < b) : a < wellOrderSucc a := by
  dsimp [wellOrderSucc, WellFounded.succ]
  rw [dif_pos ⟨b, h⟩]
  apply WellFounded.min_mem

lemma le_of_lt_wellOrderSucc {a b : α} (h : a < wellOrderSucc b) : a ≤ b := by
  by_contra!
  simpa using lt_of_lt_of_le h (wellOrderSucc_le this)

class IsWellOrderLimitElement (a : α) : Prop where
  not_bot : ∃ (b : α), b < a
  not_succ (b : α) (hb : b < a) : ∃ (c : α), b < c ∧ c < a

variable (a : α) [ha : IsWellOrderLimitElement a]

lemma IsWellOrderLimitElement.neq_bot [OrderBot α] : a ≠ ⊥ := by
  rintro rfl
  obtain ⟨b, hb⟩ := ha.not_bot
  simp at hb

lemma IsWellOrderLimitElement.bot_lt [OrderBot α] : ⊥ < a := by
  obtain h|h := eq_or_lt_of_le (@bot_le _ _ _ a)
  · exfalso
    exact IsWellOrderLimitElement.neq_bot a h.symm
  · exact h

variable {a b}

lemma IsWellOrderLimitElement.wellOrderSucc_lt {b : α} (hb : b < a) :
    wellOrderSucc b < a := by
  obtain ⟨c, hc₁, hc₂⟩ := ha.not_succ b hb
  exact lt_of_le_of_lt (wellOrderSucc_le hc₁) hc₂

lemma eq_bot_or_eq_succ_or_isWellOrderLimitElement [OrderBot α] (a : α) :
    a = ⊥ ∨ (∃ b, a = wellOrderSucc b ∧ b < a) ∨ IsWellOrderLimitElement a := by
  by_cases h₁ : a = ⊥
  · exact Or.inl (by rw [h₁])
  · by_cases h₂ : ∃ b, a = wellOrderSucc b ∧ b < a
    · exact Or.inr (Or.inl h₂)
    · refine Or.inr (Or.inr (IsWellOrderLimitElement.mk ?_ ?_))
      · refine ⟨⊥, ?_⟩
        obtain h₃|h₃ := eq_or_lt_of_le (bot_le : ⊥ ≤ a)
        · exfalso
          exact h₁ h₃.symm
        · exact h₃
      · intro b hb
        obtain h₃|h₃ := eq_or_lt_of_le (wellOrderSucc_le hb)
        · exfalso
          exact h₂ ⟨b, h₃.symm, hb⟩
        · exact ⟨wellOrderSucc b, self_lt_wellOrderSucc hb, h₃⟩

lemma IsWellOrderLimitElement.neq_succ (a : α) (ha : a < wellOrderSucc a)
    [IsWellOrderLimitElement (wellOrderSucc a)] : False := by
  simpa using IsWellOrderLimitElement.wellOrderSucc_lt ha

end

@[simp]
lemma Nat.wellOrderSucc_eq (a : ℕ) : wellOrderSucc a = succ a :=
  le_antisymm (wellOrderSucc_le (Nat.lt_succ_self a))
    (Nat.succ_le.1 (self_lt_wellOrderSucc (Nat.lt_succ_self a)))

instance needed_this : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le

lemma Nat.not_isWellOrderLimitElement (a : ℕ) [IsWellOrderLimitElement a] : False := by
  obtain _|a := a
  · have := IsWellOrderLimitElement.neq_bot (0 : ℕ)
    simp only [needed_this, ne_eq, not_true_eq_false] at this
  · simpa using IsWellOrderLimitElement.wellOrderSucc_lt (Nat.lt_succ_self a)

section

variable (α : Type*) (β : Type*) [LinearOrder α] [LinearOrder β]

namespace PrincipalSeg

variable {α β}
variable (h : PrincipalSeg (· < · : α → _) (· < · : β → _))

lemma lt (a : α) : h.toRelEmbedding a < h.top := by
  rw [h.down]
  exact ⟨a, rfl⟩

lemma le (a : α) : h.toRelEmbedding a ≤ h.top := le_of_lt (h.lt a)

@[simps]
def functorToOver : α ⥤ Over h.top where
  obj a := Over.mk (homOfLE (h.le a))
  map {a a'} φ := Over.homMk (homOfLE (by
    dsimp
    obtain hφ|rfl := (leOfHom φ).lt_or_eq
    · exact (h.map_rel_iff.2 hφ).le
    · exact le_refl _))

end PrincipalSeg

end

namespace CategoryTheory


namespace Functor

variable {J : Type u} {C' C D E : Type*} [LinearOrder J] [IsWellOrder J (· < ·)]
  [Category C'] [Category C] [Category D] [Category E]

section

variable (F : C ⥤ D) {X : C} (ι : C' ⥤ Over X)

@[simps]
def coconeOfFunctorToOver : Cocone (ι ⋙ Over.forget X ⋙ F) where
  pt := F.obj X
  ι :=
    { app := fun Y => F.map ((ι.obj Y).hom)
      naturality := fun Y Y' f => by
        dsimp
        rw [← F.map_comp, Over.w, comp_id] }

end

class WellOrderContinuous (F : J ⥤ D) : Prop where
  nonempty_isColimit {α : Type u} [LinearOrder α] (h : PrincipalSeg (· < · : α → α → Prop) (· < · : J → J → Prop))
      [IsWellOrderLimitElement h.top] :
    Nonempty (IsColimit (F.coconeOfFunctorToOver h.functorToOver))

lemma WellOrderContinuous.mk' (F : J ⥤ D)
    (hF : ∀ (j : J) [IsWellOrderLimitElement j],
      IsColimit (F.coconeOfFunctorToOver (PrincipalSeg.ofElement (· < ·) j).functorToOver)) :
    F.WellOrderContinuous where
  nonempty_isColimit h _ := ⟨(hF h.top).whiskerEquivalence (h.orderIso.equivalence)⟩

instance (F : ℕ ⥤ D) : F.WellOrderContinuous where
  nonempty_isColimit h := False.elim (Nat.not_isWellOrderLimitElement h.top)

noncomputable def isColimitOfWellOrderContinuous (F : J ⥤ D) [WellOrderContinuous F] {α : Type u} [LinearOrder α]
    (h : PrincipalSeg (· < · : α → α → Prop) (· < · : J → J → Prop)) [IsWellOrderLimitElement h.top] :
  (IsColimit (F.coconeOfFunctorToOver h.functorToOver)) :=
    Nonempty.some (WellOrderContinuous.nonempty_isColimit h)

variable (J) in
class PreservesWellOrderContinuousOfShape (G : D ⥤ E) where
  condition (j : J) [IsWellOrderLimitElement j] : PreservesColimitsOfShape { i | i < j} G

instance (F : J ⥤ D) [WellOrderContinuous F] (G : D ⥤ E)
    [h : PreservesWellOrderContinuousOfShape J G] :
    WellOrderContinuous (F ⋙ G) := WellOrderContinuous.mk' _ (fun j _ => by
  have : IsWellOrderLimitElement (PrincipalSeg.ofElement (· < · ) j).top := by
    dsimp
    infer_instance
  have := h.condition j
  exact isColimitOfPreserves G (F.isColimitOfWellOrderContinuous (PrincipalSeg.ofElement (· < ·) j)))

end Functor

namespace MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C)

class IsStableUnderTransfiniteCompositionOfShape (β : Type*) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β] : Prop where
  condition (F : β ⥤ C) [F.WellOrderContinuous] (hF : ∀ (a : β) (_ : a < wellOrderSucc a), W (F.map (homOfLE (self_le_wellOrderSucc a))))
    (c : Cocone F) (hc : IsColimit c) : W (c.ι.app ⊥)

abbrev IsStableUnderInfiniteComposition := W.IsStableUnderTransfiniteCompositionOfShape ℕ

lemma mem_of_transfinite_composition (β : Type*) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β]
    (F : β ⥤ C) [F.WellOrderContinuous] (hF : ∀ (a : β) (_ : a < wellOrderSucc a), W (F.map (homOfLE (self_le_wellOrderSucc a))))
    (c : Cocone F) (hc : IsColimit c) [W.IsStableUnderTransfiniteCompositionOfShape β] : W (c.ι.app ⊥) :=
  IsStableUnderTransfiniteCompositionOfShape.condition F hF c hc

class IsStableUnderTransfiniteComposition extends W.IsMultiplicative : Prop where
  isStableUnderTransfiniteCompositionOfShape (β : Type u) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β] :
    W.IsStableUnderTransfiniteCompositionOfShape β := by infer_instance

section

variable (D : Type*) [Category D]

def functor : MorphismProperty (D ⥤ C) := fun _ _ τ => ∀ X, W (τ.app X)

variable {D}

@[simp]
lemma mem_functor_iff {F₁ F₂ : D ⥤ C} (τ : F₁ ⟶ F₂) : W.functor D τ ↔ ∀ X, W (τ.app X) := by rfl

variable (β : Type*) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β]

instance [W.IsStableUnderTransfiniteCompositionOfShape β] [HasColimitsOfShape β C]
    [∀ X, Functor.PreservesWellOrderContinuousOfShape β ((evaluation D C).obj X)] :
    (W.functor D).IsStableUnderTransfiniteCompositionOfShape β where
  condition F _ hF _ hc X := W.mem_of_transfinite_composition β (F ⋙ (evaluation D C).obj X)
    (fun j hj => hF j hj X) _ (isColimitOfPreserves ((evaluation D C).obj X) hc)

instance isStableUnderTransfiniteCompositionOfShape_over [W.IsStableUnderTransfiniteCompositionOfShape β] (S : C)
    [Functor.PreservesWellOrderContinuousOfShape β (Over.forget S)]
    [PreservesColimitsOfShape β (Over.forget S)] :
    (W.over S).IsStableUnderTransfiniteCompositionOfShape β where
  condition F _ hF _ hc := W.mem_of_transfinite_composition β (F ⋙ Over.forget _) hF _
    (isColimitOfPreserves (Over.forget _) hc)

end

end MorphismProperty

end CategoryTheory
