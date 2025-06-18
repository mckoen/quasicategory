import Quasicategory.PushoutProduct.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

universe w v v' u u'

open CategoryTheory MonoidalCategory Simplicial SSet Limits

namespace CategoryTheory.PushoutProduct

variable {X Y A B : SSet} (f : A ⟶ B) (g : X ⟶ Y)

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (F : J ⥤ SSet) [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)


-- def natTransLeftFunctor : D ⥤ C := (NatTrans.arrowFunctor h) ⋙ rightFunctor g ⋙ Arrow.leftFunc
@[simps!]
noncomputable
abbrev F' : J ⥤ SSet := natTransLeftFunctor c.ι Λ[2, 1].ι

instance ll {S : SSet} : Functor.IsLeftAdjoint (tensorLeft S) where
  exists_rightAdjoint := ⟨FunctorToTypes.rightAdj S, ⟨FunctorToTypes.adj S⟩⟩

instance rr {S : SSet} : PreservesColimitsOfSize (tensorLeft S) :=
  Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint _

variable {m : J}

@[simps!]
def _root_.CategoryTheory.NatTrans.whiskerCocone {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (h : F ⟶ G) (s : Cocone G) : Cocone F where
  pt := s.pt
  ι := h ≫ s.ι

@[simp]
noncomputable
def tempCocone (s : Cocone ((Set.principalSegIio m).monotone.functor ⋙ natTransLeftFunctor c.ι Λ[2, 1].ι)) :
    Cocone ((Set.principalSegIio m).monotone.functor ⋙ F ⋙ tensorLeft Δ[2]) :=
  NatTrans.whiskerCocone (whiskerLeft ((Set.principalSegIio m).monotone.functor) (inlDescFunctor c.ι Λ[2, 1].ι)) s

@[simp]
noncomputable
def tempCocone' (s : Cocone (natTransLeftFunctor c.ι Λ[2, 1].ι)) :
    (Cocone (F ⋙ tensorLeft Δ[2])) :=
  NatTrans.whiskerCocone (inlDescFunctor c.ι Λ[2, 1].ι) s

instance (m : J) (hm : Order.IsSuccLimit m) : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt

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
  letI : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt
  let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) (hF.nonempty_isColimit m hm).some)
  let H'' := (Limits.isColimitOfPreserves (tensorLeft (Λ[2, 1] : SSet)) (hF.nonempty_isColimit m hm).some)
  apply pushout.desc (H.desc (tempCocone F c s)) ((inr _ _) ≫ s.ι.app ⊥)
  apply H''.hom_ext
  intro j
  have := H.fac (tempCocone F c s) j
  dsimp [tempCocone, inlDescFunctor] at this ⊢
  rw [whisker_exchange_assoc, this, ← MonoidalCategory.whiskerLeft_comp_assoc, NatTrans.naturality]
  have : _ = s.ι.app ⊥ := (s.ι.naturality (homOfLE <| bot_le (a := j)))
  rw [← this]
  simp [pushout.condition_assoc]

instance F'_woc [hF: F.IsWellOrderContinuous] :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨{
    desc := auxWellOrderCont_desc _ _ hm
    fac s j := by
      dsimp only [auxWellOrderCont_desc]
      apply pushout.hom_ext
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
        simp [pushout.map, pushout.inr_desc_assoc]
    uniq s h hj := by
      apply pushout.hom_ext
      · dsimp [auxWellOrderCont_desc]
        let H := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) (hF.nonempty_isColimit m hm).some)
        apply H.hom_ext
        intro j
        simp
        have := H.fac (tempCocone F c s) j
        simp at this
        rw [this, ← hj j]
        simp
      · dsimp [auxWellOrderCont_desc]
        simp
        letI : OrderBot (Set.Iio m) := Subtype.orderBot hm.bot_lt
        rw [← hj ⊥]
        simp
  }⟩

@[simps!]
noncomputable
def c' : Cocone (natTransLeftFunctor c.ι Λ[2, 1].ι) where
  pt := Δ[2] ⊗ c.pt
  ι := descFunctor c.ι Λ[2, 1].ι

omit [SuccOrder J] [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma c'_icColimit_fac (s : Cocone (F' F c)) (j : J) :
    (c' F c).ι.app j ≫ (isColimitOfPreserves (tensorLeft Δ[2]) hc).desc (tempCocone' F c s) = s.ι.app j := by
  apply pushout.hom_ext
  · simpa using (isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) j
  · apply (isColimitOfPreserves (tensorLeft Λ[2, 1].toSSet) hc).hom_ext
    intro k
    have := (isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) k
    simp at this ⊢
    rw [whisker_exchange_assoc, this, pushout.condition_assoc]
    by_cases hj : j ≤ k
    · have := s.ι.naturality (homOfLE hj)
      simp at this
      rw [← this]
      simp
    · rw [not_le] at hj
      have := s.ι.naturality (homOfLE (le_of_lt hj))
      simp at this
      rw [← this]
      simp

omit [SuccOrder J] [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma c'_isColimit_uniq (s : Cocone (F' F c)) (h : (c' F c).pt ⟶ s.pt)
    (hj : ∀ (j : J), (c' F c).ι.app j ≫ h = s.ι.app j) :
    h = (isColimitOfPreserves (tensorLeft Δ[2]) hc).desc (tempCocone' F c s) := by
  apply (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).hom_ext
  intro j
  have := (inl _ _) ≫= hj j
  simp [c', descFunctor] at this ⊢
  rw [this]
  have := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).fac (tempCocone' F c s) j
  simp at this
  rw [this]

noncomputable
def c'_IsColimit : IsColimit (c' F c) where
  desc s := (Limits.isColimitOfPreserves (tensorLeft Δ[2]) hc).desc (tempCocone' F c s)
  fac := c'_icColimit_fac _ _ _
  uniq := c'_isColimit_uniq _ _ _

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
abbrev P := natTransLeftFunctor F.succNatTrans Λ[2, 1].ι

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

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma cocone_ι_facs : F.succNatTrans ≫ natTransSucc F c.ι = c.ι := by
  ext : 2
  simp

@[simp]
noncomputable
def intermediateeqhom : (natTransLeftFunctor (F.succNatTrans ≫ natTransSucc F c.ι) Λ[2, 1].ι) ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι) :=
  eqToHom (by rw [cocone_ι_facs])

@[simp]
noncomputable
def φ_j (j) : (natTransLeftFunctor F.succNatTrans Λ[2, 1].ι).obj j ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι).obj j := by
  apply pushout.desc
    (inl (c.ι.app j) ((horn 2 1).ι))
    ((Λ[2, 1] : SSet) ◁ c.ι.app (Order.succ j) ≫ inr (c.ι.app j) ((horn 2 1).ι))
  simp [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality, pushout.condition]
  /-
  natTransLeftFunctor_comp F.succNatTrans Λ[2, 1].ι (natTransSucc F c.ι) ≫ (intermediateeqhom _ _)
  -/

set_option maxHeartbeats 300000 in
@[simps!]
noncomputable
def φ : (natTransLeftFunctor F.succNatTrans Λ[2, 1].ι) ⟶ (natTransLeftFunctor c.ι Λ[2, 1].ι) where
  app := φ_j F c
  naturality k j f := by
    apply pushout.hom_ext
    · simp only [Fin.isValue, Arrow.mk_right, Functor.id_obj, Functor.succ, homOfLE_leOfHom,
      Functor.succNatTrans, NatTrans.arrowFunctor_obj_left, natTransLeftFunctor_obj,
      Functor.const_obj_obj, Arrow.mk_left, NatTrans.arrowFunctor_obj_right, Arrow.mk_hom,
      NatTrans.arrowFunctor_obj_hom, natTransLeftFunctor_map, φ_j, pt, inl, inr,
      colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.assoc,
      colimit.ι_desc, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    · simp [← MonoidalCategory.whiskerLeft_comp_assoc, c.ι.naturality, pushout.condition]

omit [OrderBot J] [WellFoundedLT J] [F.IsWellOrderContinuous] in
lemma newSqComm {j} :
    (φ F c).app j ≫ (F' F c).map (homOfLE (Order.le_succ j)) =
    ((F.map (homOfLE (Order.le_succ j))) ◫ ((horn 2 1).ι)) ≫
      PushoutProduct.inl (c.ι.app (Order.succ j)) ((horn 2 1).ι) := by
  apply pushout.hom_ext
  · simp
  · simp [pushout.condition]

noncomputable
def newPushoutCocone (j : J) : PushoutCocone
    ((φ F c).app j) ((F.map (homOfLE (Order.le_succ j))) ◫ ((horn 2 1).ι)) :=
  PushoutCocone.mk _ _ (newSqComm F c)

@[simp]
noncomputable
def newPushoutIsColimit_desc {j} (s : PushoutCocone ((φ F c).app j) (F.map (homOfLE (Order.le_succ j)) ◫ (horn 2 1).ι)) :
    (natTransLeftFunctor c.ι Λ[2, 1].ι).obj (Order.succ j) ⟶ s.pt :=
  pushout.desc s.inr ((inr _ _) ≫ s.inl) (by simpa using ((inr _ _) ≫= s.condition).symm)

lemma newPushoutIsColimit_fac_left_aux {j} (s : PushoutCocone ((φ F c).app j) (F.map (homOfLE (Order.le_succ j)) ◫ Λ[2, 1].ι)) :
    pushout.inl ((Arrow.mk Λ[2, 1].ι).hom ▷ (𝟭 SSet).obj ((NatTrans.arrowFunctor c.ι).obj j).left)
        ((𝟭 SSet).obj (Arrow.mk Λ[2, 1].ι).left ◁ ((NatTrans.arrowFunctor c.ι).obj j).hom) ≫
      (F' F c).map (homOfLE (Order.le_succ j)) ≫ newPushoutIsColimit_desc F c s =
    pushout.inl ((Arrow.mk Λ[2, 1].ι).hom ▷ (𝟭 SSet).obj ((NatTrans.arrowFunctor c.ι).obj j).left)
        ((𝟭 SSet).obj (Arrow.mk Λ[2, 1].ι).left ◁ ((NatTrans.arrowFunctor c.ι).obj j).hom) ≫
      s.inl := by
  have := ((pushout.inl _ _) ≫= s.condition).symm
  dsimp only [F', newPushoutIsColimit_desc, NatTrans.arrowFunctor, Arrow.mk, natTransLeftFunctor,
    Functor.comp_map, Arrow.homMk', rightFunctor, rightFunctor_map, Arrow.leftFunc_map,
    rightFunctor_map_left, Functor.id_obj, Functor.const, inl, inr]
  dsimp only [Arrow.mk, Functor.id_obj, Functor.succNatTrans, NatTrans.arrowFunctor, φ, φ_j,
    inl] at this
  rw [pushout.inl_desc_assoc, pushout.inl_desc_assoc] at this
  rw [pushout.inl_desc_assoc, ← this]
  have := congr_app (cocone_ι_facs F c) j
  dsimp only [Functor.succNatTrans, natTransSucc, NatTrans.comp_app] at this
  have := c.ι.naturality (homOfLE (Order.le_succ j))
  simp only [Functor.const, Category.comp_id] at this
  /-
  have : (Λ[2, 1].toSSet ◁ c.ι.app j) = (Λ[2, 1].toSSet ◁ (F.map (homOfLE (Order.le_succ j)) ≫ c.ι.app (Order.succ j) )) := by
    rw [this]
  have := pushout.congrHom (show (Λ[2, 1].ι ▷ F.obj j) = (Λ[2, 1].ι ▷ F.obj j) by rfl) this.symm
  -/
  sorry

lemma newPushoutIsColimit_fac_left {j} (s : PushoutCocone ((φ F c).app j) (F.map (homOfLE (Order.le_succ j)) ◫ Λ[2, 1].ι)) :
    (F' F c).map (homOfLE (Order.le_succ j)) ≫ newPushoutIsColimit_desc F c s = s.inl := by
  dsimp only [F', newPushoutIsColimit_desc, NatTrans.arrowFunctor, Arrow.mk, natTransLeftFunctor,
    Functor.comp_map, Arrow.homMk', rightFunctor, rightFunctor_map, Arrow.leftFunc_map,
    rightFunctor_map_left, Functor.id_obj, Functor.const, inl, inr, pushout.map]
  simp_rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  apply pushout.hom_ext
  · --simpa using ((pushout.inl _ _) ≫= s.condition).symm
    exact newPushoutIsColimit_fac_left_aux _ _ _
  · rw [pushout.inr_desc_assoc, pushout.inr_desc]

/--/
set_option maxHeartbeats 300000 in
noncomputable
def newPushoutIsColimit {j} : IsColimit (newPushoutCocone F c j) := by
  refine PushoutCocone.IsColimit.mk _ (newPushoutIsColimit_desc F c) ?_ ?_ ?_
  · exact newPushoutIsColimit_fac_left _ _
  · intro
    simp only [newPushoutIsColimit_desc, pushout.inl_desc]
  · intro _ _ h h'
    apply pushout.hom_ext
    · dsimp only [Functor.id_obj, Arrow.mk, NatTrans.arrowFunctor, newPushoutIsColimit_desc]
      rw [pushout.inl_desc, ← h']
    · dsimp only [Functor.id_obj, Arrow.mk, NatTrans.arrowFunctor, newPushoutIsColimit_desc]
      rw [pushout.inr_desc, ← h]
      simp only [Fin.isValue, Functor.const_obj_obj, Functor.succ, homOfLE_leOfHom,
        Functor.succNatTrans, natTransLeftFunctor_obj, φ_app, pushoutProduct, pt, inr,
        natTransLeftFunctor_map, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id,
        Category.id_comp, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
        PushoutCocone.mk_ι_app]

def newPushoutIsPushout (j : J) : CategoryTheory.IsPushout
  ((φ F c).app j)
  (F.map (homOfLE (Order.le_succ j)) ◫ (horn 2 1).ι)
  ((F' F c).map (homOfLE (Order.le_succ j)))
  (PushoutProduct.inl (c.ι.app (Order.succ j)) ((horn 2 1).ι))
  := IsPushout.of_isColimit (newPushoutIsColimit F c (j := j))

end CategoryTheory.PushoutProduct
