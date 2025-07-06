import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Sigma.Order

variable {n : ℕ}

namespace Sigma.Lex

@[simp]
def succ : (Σₗ (b : Fin (n + 1)), Fin b.succ) → (Σₗ (b : Fin (n + 1)), Fin b.succ) :=
  fun ⟨b, a⟩ ↦
    if h₁ : a.1 < b then ⟨b, ⟨a.succ, by simpa using h₁⟩⟩ -- if a < b, then ⟨b, a + 1⟩
    else if h₂ : b = Fin.last n then ⟨Fin.last n, Fin.last n⟩ -- if a = b = n, then don't change
    else ⟨⟨b.succ, by simp_all [Fin.ext_iff]; omega⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ -- if a = b < n, then ⟨b + 1, 0⟩

variable (i : Σₗ (b : Fin (n + 1)), Fin b.succ)

@[simp]
lemma Fin.succ_eq_of_snd_lt_fst (b : Fin (n + 1)) (a : Fin b.succ) (h : a.1 < b) : succ ⟨b, a⟩ = ⟨b, ⟨a.succ, Nat.succ_lt_succ h⟩⟩ := by
  simp [h]

@[simp]
lemma Fin.succ_eq_of_snd_lt_fst' (b : Fin (n + 1)) (a : Fin b) : succ ⟨b, a.castSucc⟩ = ⟨b, a.succ⟩ := by
  simp
  congr

@[simp]
lemma Fin.succ_eq_of_lt_last (b : Fin (n + 1)) (h : b < Fin.last n) :
    succ ⟨b, ⟨b, Nat.lt_add_one _⟩⟩ = ⟨⟨b.succ, Nat.succ_lt_succ h⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ := by
  simp [Fin.ne_of_lt h]

@[simp]
lemma Fin.succ_eq_of_eq_last (b : Fin (n + 1)) (h : b = Fin.last n) :
    succ ⟨b, ⟨b, Nat.lt_add_one _⟩⟩ = ⟨Fin.last n, Fin.last n⟩ := by
  subst h
  simp

@[simp]
lemma Fin.lt_of_snd_lt {b : Fin (n + 1)} {a a' : Fin b.succ} :
    a ≤ a' → (⟨b, a⟩ :  Σₗ (b : Fin (n + 1)), Fin b.succ) ≤ (⟨b, a'⟩ : Σₗ (b : Fin (n + 1)), Fin b.succ) := by
  intro h
  simpa

theorem succ_eq_of_lt_fst (h : i.2.1 < i.1.1) :
    succ i = ⟨i.1, ⟨i.2.1.succ, by simpa using h⟩⟩ := by
  obtain ⟨b, a⟩ := i
  simp [succ, h]

theorem le_succ : i ≤ succ i := by
    obtain ⟨b, a⟩ := i
    simp
    split
    · simp [le_def, Fin.le_iff_val_le_val]
    · split
      · next h =>
        simp [le_def, Fin.le_iff_val_le_val]
        right
        use h
        omega
      · next h =>
        simp [le_def, Fin.lt_iff_val_lt_val]

variable {i : Σₗ (b : Fin (n + 1)), Fin b.succ}

theorem max_of_succ_le : succ i ≤ i → IsMax i := by
    obtain ⟨b, a⟩ := i
    simp
    split
    · next h =>
      intro h'
      cases h'
      · omega
      · next h' =>
        simp [Fin.le_iff_val_le_val] at h'
    · next h =>
      split
      · next h' =>
        intro h''
        simp [le_def] at h''
        aesop
      · next h' =>
        intro h''
        exfalso
        simp [le_def, Fin.lt_iff_val_lt_val] at h''
        rw [Fin.eq_mk_iff_val_eq] at h'
        simp at h'
        cases h''
        · next h''' =>
          rename_i h''''
          rw [Fin.eq_mk_iff_val_eq] at h''''
          simp at h''''

theorem succ_le_of_lt {j : Σₗ (b : Fin (n + 1)), Fin b.succ} : i < j → Sigma.Lex.succ i ≤ j := by
    obtain ⟨b, a⟩ := i
    obtain ⟨b', a'⟩ := j
    intro h
    dsimp
    split
    · next h' =>
      rw [le_def]
      rw [lt_def] at h
      aesop
    · next h'=>
      split
      · next h'' =>
        subst h''
        have : a = Fin.last n := by omega
        subst this
        exact h.le
      · next h'' =>
        rw [lt_def] at h
        cases h
        · next h' =>
          simp at h'
          by_cases hb : b.1 + 1 < b'
          · rw [le_def]
            aesop
          · have hb : (⟨⟨b.1 + 1,  by simp_all [Fin.ext_iff]; omega⟩, ⟨0, Nat.zero_lt_succ _⟩⟩ :  Σₗ (b : Fin (n + 1)), Fin b.succ ) =
                ⟨b', ⟨0, Nat.zero_lt_succ ↑b'⟩⟩ := by
              congr
              omega
              omega
              omega
            dsimp at hb
            rw [hb]
            right
            exact Fin.zero_le a'
        · next h' =>
          obtain ⟨h₁, h₂⟩ := h'
          simp at h₁
          subst h₁
          simp at h₂
          omega

instance succOrder : SuccOrder (Σₗ (b : Fin (n + 1)), Fin b.succ) where
  succ := succ
  le_succ := le_succ
  max_of_succ_le := max_of_succ_le
  succ_le_of_lt := succ_le_of_lt

noncomputable
instance : OrderBot (Σₗ (b : Fin (n + 1)), Fin b.succ) :=
  letI : OrderBot (Fin (⊥ : Fin (n + 1)).succ) := {
    bot := ⟨0, Nat.zero_lt_succ _⟩
    bot_le _ := Fin.zero_le _ }
  Sigma.Lex.orderBot

noncomputable
instance : OrderTop (Σₗ (b : Fin (n + 1)), Fin b.succ) :=
  letI : OrderTop (Fin (⊤ : Fin (n + 1)).succ) := {
    top := Fin.last _
    le_top _ := Fin.le_last _ }
  Sigma.Lex.orderTop


lemma bot_eq_zero : (⊥ : Σₗ (b : Fin (n + 1)), Fin b.succ) = ⟨0, ⟨0, Nat.zero_lt_succ _⟩⟩ := by
  rfl

lemma top_eq_last : (⊤ : Σₗ (b : Fin (n + 1)), Fin b.succ) = ⟨Fin.last n, Fin.last n⟩ := by
  rfl

lemma Fin.succ_last_eq_last : succ ⟨Fin.last n, Fin.last n⟩ = ⟨Fin.last n, Fin.last n⟩ := by
  simp

lemma Fin.eq_zero_or_eq_succ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    i = ⊥ ∨ ∃ j, i = succ j := by
  obtain ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ := i
  induction b with
  | zero =>
    left
    have : a = 0 := Nat.lt_one_iff.mp ha
    subst this
    rfl
  | succ b _ =>
    right
    induction a with
    | zero =>
      use ⟨⟨b, by omega⟩, ⟨b, by simp⟩⟩
      symm
      apply succ_eq_of_lt_last
      simp [Fin.lt_iff_val_lt_val]
      omega
    | succ a _ =>
      simp [Fin.lt_iff_val_lt_val] at ha
      use ⟨⟨b + 1, hb⟩, ⟨a, by omega⟩⟩
      symm
      apply succ_eq_of_snd_lt_fst
      simp
      omega

end Sigma.Lex
