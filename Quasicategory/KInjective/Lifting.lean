import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Quasicategory.KInjective.Induction
import Quasicategory.KInjective.StableUnderRetract

universe w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace IsPushout

variable {X Y Z T : C} (t : X ⟶ Y) (l : X ⟶ Z) (r : Y ⟶ T) (b : Z ⟶ T)
  (h : IsPushout t l r b)

lemma hasLiftingProperty (t : X ⟶ Y) (l : X ⟶ Z) (r : Y ⟶ T) (b : Z ⟶ T)
    (h : IsPushout t l r b)
    {A B : C} (p : A ⟶ B) [HasLiftingProperty l p] :
    HasLiftingProperty r p where
  sq_hasLift {f g} sq := by
    have sq' : CommSq (t ≫ f) l p (b ≫ g) :=
      ⟨by rw [assoc, sq.w, h.w_assoc]⟩
    exact ⟨⟨{
      l := PushoutCocone.IsColimit.desc h.isColimit f sq'.lift (by simp)
      fac_left := PushoutCocone.IsColimit.inl_desc h.isColimit _ _ _
      fac_right := by
        apply PushoutCocone.IsColimit.hom_ext h.isColimit
        · rw [PushoutCocone.IsColimit.inl_desc_assoc, cocone_inl, sq.w]
        · rw [PushoutCocone.IsColimit.inr_desc_assoc, cocone_inr, sq'.fac_right] }⟩⟩

end IsPushout

/-
instance hasLiftingProperty_pushout_inl {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] {A B : C} (p : A ⟶ B)
    [HasLiftingProperty g p] : HasLiftingProperty (pushout.inl f g : Y ⟶ pushout f g) p :=
  (IsPushout.of_hasPushout f g).hasLiftingProperty p

instance hasLiftingProperty_pushout_inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] {A B : C} (p : A ⟶ B)
    [HasLiftingProperty f p] : HasLiftingProperty (pushout.inr f g: Z ⟶ pushout f g) p :=
  (IsPushout.of_hasPushout f g).flip.hasLiftingProperty p
-/

instance hasLiftingProperty_limits_map {I : Type*} {A B : I → C} (f : ∀ i, A i ⟶ B i)
    [HasCoproduct A] [HasCoproduct B] {X Y : C} (p : X ⟶ Y) [∀ i, HasLiftingProperty (f i) p] :
    HasLiftingProperty (Limits.Sigma.map f) p where
  sq_hasLift {t b} sq := by
    have sq' : ∀ i, CommSq (Sigma.ι A i ≫ t) (f i) p (Sigma.ι B i ≫ b) := fun i => ⟨by simp [sq.w]⟩
    exact ⟨⟨{
        l := Sigma.desc (fun i => (sq' i).lift)
        fac_left := by aesop_cat
        fac_right := by aesop_cat }⟩⟩

namespace MorphismProperty

section

variable {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)

inductive ofHoms : MorphismProperty C
  | mk (i : I) : ofHoms (f i)

lemma ofHoms.mk_mem (i : I) : (ofHoms f) (f i) := ofHoms.mk i

end

variable (W : MorphismProperty C)

def llpWith : MorphismProperty C := fun _ _ i =>
  ∀ ⦃X Y : C⦄ (p : X ⟶ Y) (_ : W p), HasLiftingProperty i p

def rlpWith : MorphismProperty C := fun _ _ p =>
  ∀ ⦃A B : C⦄ (i : A ⟶ B) (_ : W i), HasLiftingProperty i p

instance : W.llpWith.ContainsIdentities where
  id_mem _ _ _ _ _ := inferInstance

instance : W.llpWith.IsMultiplicative where
  comp_mem := by
    intro _ _ _ i j hi hj _ _ p hp
    have := hi p hp
    have := hj p hp
    infer_instance

instance : W.rlpWith.ContainsIdentities where
  id_mem _ _ _ _ _ := inferInstance

instance : W.rlpWith.IsMultiplicative where
  comp_mem := by
    intro _ _ _ p q hp hq _ _ i hi
    have := hp i hi
    have := hq i hi
    infer_instance

lemma le_llpWith_rlpWith : W ≤ W.llpWith.rlpWith := by
  intro X Y p hp A B i hi
  have := hi p hp
  infer_instance

lemma le_rlpWith_llpWith : W ≤ W.rlpWith.llpWith := by
  intro A B i hi X Y p hp
  have := hp i hi
  infer_instance

lemma llpWith_isStableUnderRetract : W.llpWith.IsStableUnderRetract where
  condition f g i p hip hg _ _ π hπ := hasLeftLiftingProperty_of_retract f g i p hip π (hg π hπ)

lemma rlpWith_isStableUnderRetract : W.rlpWith.IsStableUnderRetract where
  condition f g i p hip hg _ _ ι hι := hasRightLiftingProperty_of_retract f g i p hip ι (hg ι hι)

/-
lemma llpWith_respectsIso : W.llpWith.RespectsIso where
  precomp e f hf X Y p hp := by
    have := hf p hp
    infer_instance
  postcomp e f hf X Y p hp := by
    have := hf p hp
    infer_instance

lemma rlpWith_respectsIso : W.rlpWith.RespectsIso where
  precomp e f hf A B i hi := by
    have := hf i hi
    infer_instance
  postcomp e f hf A B i hi := by
    have := hf i hi
    infer_instance
-/

namespace IsStableUnderTransfiniteCompositionOfShapeLlpWith

variable {W}
variable {β : Type*} [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β]
  {F : β ⥤ C} [F.WellOrderContinuous]
  (hF : ∀ (a : β) (_ : a < wellOrderSucc a), W.llpWith (F.toPrefunctor.map (homOfLE (self_le_wellOrderSucc a))))
  {c : Cocone F} (hc : IsColimit c)

section

variable {X Y : C} {p : X ⟶ Y} (hp : W p)
  {f : F.obj ⊥ ⟶ X} {g : c.pt ⟶ Y} (sq : CommSq f (c.ι.app ⊥) p g)

lemma commSq (sq : CommSq f (c.ι.app ⊥) p g)
    (i : β) : CommSq f (F.map (homOfLE bot_le)) p (c.ι.app i ≫ g) where
  w := by rw [sq.w, Cocone.w_assoc]

variable (F) in
@[simps]
def system : βᵒᵖ ⥤ Type _ where
  obj i := (commSq sq i.unop).LiftStruct
  map {i j} φ := fun s =>
    { l := F.map φ.unop ≫ s.l
      fac_left := by simpa only [← Functor.map_comp_assoc] using s.fac_left
      fac_right := by
        dsimp
        rw [assoc, s.fac_right, Cocone.w_assoc] }

section

variable {sq}
variable (j : β) (hj : j < wellOrderSucc j) (s : (system F sq).obj (Opposite.op j))

variable {j} in
lemma wellOrderInductionDataSucc_sq :
    CommSq s.l (F.map (homOfLE (self_le_wellOrderSucc j))) p
    (c.ι.app (wellOrderSucc j) ≫ g) where
  w := by simp [s.fac_right]

noncomputable def wellOrderInductionDataSucc :
    (system F sq).obj (Opposite.op (wellOrderSucc j)) :=
  letI := hF j hj p hp
  { l := (wellOrderInductionDataSucc_sq s).lift
    fac_left := by
      conv_rhs => rw [← s.fac_left, ← (wellOrderInductionDataSucc_sq s).fac_left]
      rw [← F.map_comp_assoc, homOfLE_comp]
    fac_right := by simp }

lemma wellOrderInductionData_map_succ :
    (system F sq).toPrefunctor.map (homOfLE (self_le_wellOrderSucc j)).op
      (wellOrderInductionDataSucc hF hp j hj s) = s := by
  letI := hF j hj p hp
  exact CommSq.LiftStruct.ext (wellOrderInductionDataSucc_sq s).fac_left

end

section

variable {sq}
variable {j : β} [IsWellOrderLimitElement j]
  (x : (((PrincipalSeg.ofElement (· < ·) j).functorToOver ⋙ Over.forget _).op ⋙ system F sq).sections)

instance (β : Type*) [LinearOrder β] (j : β) [IsWellOrderLimitElement j] :
    IsWellOrderLimitElement (PrincipalSeg.ofElement (· < ·) j).top := by
  dsimp
  infer_instance

noncomputable def wellOrderInductionDataDesc : (system F sq).obj (Opposite.op j) where
  l := (F.isColimitOfWellOrderContinuous (PrincipalSeg.ofElement (· < ·) j)).desc
    (Cocone.mk _
      { app := fun i => (x.1 (Opposite.op i)).l
        naturality := fun i i' φ => by
          dsimp
          rw [comp_id, ← x.2 φ.op]
          rfl })
  fac_left := by
    have hj := IsWellOrderLimitElement.bot_lt j
    have h : F.map (𝟙 _) ≫ _ = _ := (x.1 (Opposite.op ⟨⊥, hj⟩)).fac_left
    rw [F.map_id, id_comp] at h
    erw [(F.isColimitOfWellOrderContinuous (PrincipalSeg.ofElement (· < ·) j)).fac _ ⟨⊥, hj⟩]
    exact h
  fac_right := (F.isColimitOfWellOrderContinuous (PrincipalSeg.ofElement (· < ·) j)).hom_ext (fun i => by
    rw [IsColimit.fac_assoc]
    dsimp
    rw [Cocone.w_assoc, (x.1 (Opposite.op i)).fac_right]
    rfl)

lemma wellOrderInductionData_fac {i : β} (hi : i < j) :
    (system F sq).map (homOfLE hi.le).op (wellOrderInductionDataDesc x) = x.val ⟨i, hi⟩ :=
  CommSq.LiftStruct.ext
    ((F.isColimitOfWellOrderContinuous (PrincipalSeg.ofElement (· < ·) j)).fac _ ⟨i, hi⟩)

end

noncomputable def wellOrderInductionData : (system F sq).WellOrderInductionData where
  succ j hj s := wellOrderInductionDataSucc hF hp j hj s
  map_succ j hj s := wellOrderInductionData_map_succ hF hp j hj s
  desc _ _ x := wellOrderInductionDataDesc x
  fac _ _ _ hi x := wellOrderInductionData_fac x hi

variable (c) in
noncomputable def systemSection : (system F sq).sections :=
  (wellOrderInductionData hF hp sq).sectionsMk
    { l := f
      fac_left := by
        change F.map (𝟙 _) ≫ f = f
        simp
      fac_right := sq.w }

noncomputable def liftStruct : sq.LiftStruct where
  l := hc.desc (Cocone.mk _
    { app := fun i => ((systemSection hF c hp sq).1 (Opposite.op i)).l
      naturality := fun i j φ => by
        dsimp
        rw [comp_id, ← (systemSection hF c hp sq).2 φ.op]
        rfl })
  fac_left := by
    have h := ((systemSection hF c hp sq).1 (Opposite.op ⊥)).fac_left
    simp only [IsColimit.fac, ← h]
    convert (id_comp _).symm
    apply F.map_id
  fac_right := hc.hom_ext (fun i => by
    dsimp
    simpa only [IsColimit.fac_assoc] using ((systemSection hF c hp sq).1 (Opposite.op i)).fac_right)

end

lemma hasLiftingProperty
    (hF : ∀ (a : β) (_ : a < wellOrderSucc a), W.llpWith (F.toPrefunctor.map (homOfLE (self_le_wellOrderSucc a))))
    (hc : IsColimit c)
    {X Y : C} {p : X ⟶ Y} (hp : W p) : HasLiftingProperty (c.ι.app ⊥) p where
  sq_hasLift sq := ⟨⟨liftStruct hF hc hp sq⟩⟩

lemma llpWith_ι_app
    (hF : ∀ (a : β) (_ : a < wellOrderSucc a), W.llpWith (F.toPrefunctor.map (homOfLE (self_le_wellOrderSucc a))))
    (hc : IsColimit c) :
    W.llpWith (c.ι.app ⊥) :=
  fun _ _ _ hp => hasLiftingProperty hF hc hp

end IsStableUnderTransfiniteCompositionOfShapeLlpWith

instance (β : Type*) [LinearOrder β] [IsWellOrder β (· < ·)] [OrderBot β] :
  W.llpWith.IsStableUnderTransfiniteCompositionOfShape β where
    condition _ _ hF _ hc :=
      IsStableUnderTransfiniteCompositionOfShapeLlpWith.llpWith_ι_app hF hc

instance llpWith_comp : W.llpWith.IsStableUnderTransfiniteComposition where

end MorphismProperty

end CategoryTheory
