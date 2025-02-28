import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  -- search_proof
  -- simp [abs]

  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]

    -- suggest_tactics
    -- linarith

    linarith

  -- aesop

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  -- search_proof
  -- simp [abs]

  -- suggest_tactics
  -- simp [abs]

  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

  -- aesop

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  -- search_proof
  -- exact abs_add x y

  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

  -- suggest_tactics

  -- aesop

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by

  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      left
      exact h'
    · intro h'
      rcases h' with h' | h'
      · exact h'
      · linarith
  rw [abs_of_neg h]

  -- search_proof
  -- simp_all only [gt_iff_lt, iff_or_self]
  -- intro a
  -- linarith

  constructor
  · -- suggest_tactics
    -- tauto

    -- aesop
    intro h'
    right
    exact h'
  · intro h'
    rcases h' with h' | h'
    · linarith

    -- suggest_tactics
    -- exact h'

    -- aesop

    · exact h'

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by

  rcases le_or_gt 0 x with h | h

  -- search_proof
  -- apply Iff.intro
  -- · intro a
  --   apply And.intro
  --   · rw [abs] at a
  --     simp_all only [neg_le_self_iff, sup_of_le_left]
  --     linarith
  --   · rw [abs] at a
  --     simp_all only [neg_le_self_iff, sup_of_le_left]
  -- · intro a
  --   obtain ⟨left, right⟩ := a
  --   exact abs_lt.2 ⟨left, right⟩

  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      constructor

      -- suggest_tactics
      -- all_goals linarith

      · linarith
      exact h'
    · -- suggest_tactics
      -- simp [h]

      -- aesop

      intro h'
      rcases h' with ⟨h1, h2⟩
      exact h2
  · rw [abs_of_neg h]
    constructor
    · intro h'
      constructor

      -- suggest_tactics
      -- all_goals linarith

      · linarith
      · linarith
    · intro h'

      -- suggest_tactics
      -- linarith

      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  -- search_proof
  -- simp_all only [ge_iff_le]
  -- obtain ⟨w, h⟩ := h
  -- obtain ⟨w_1, h⟩ := h
  -- cases h with
  -- | inl h_1 =>
  --   subst h_1
  --   positivity
  -- | inr h_2 =>
  --   subst h_2
  --   positivity

  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

  -- suggest_tactics

  -- aesop

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  -- search_proof
  -- simp_all only [sq_eq_one_iff]

  -- suggest_tactics
  -- simpa using h

  -- aesop
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by

  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring

  -- search_proof
  -- simp_all only [sub_self, mul_eq_zero]
  -- cases h'' with
  -- | inl h_1 => exact Or.inr (eq_neg_of_add_eq_zero_left h_1)
  -- | inr h_2 =>
  --   apply Or.inl
  --   linarith

  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right

    -- suggest_tactics
    -- linarith

    exact eq_neg_iff_add_eq_zero.mpr h1
  · left

    -- suggest_tactics
    -- linarith

    exact eq_of_sub_eq_zero h1

  -- aesop

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  -- search_proof
  -- simp_all only [sq_eq_one_iff]

  -- suggest_tactics
  -- simpa using h

  -- aesop

  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by

  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring

  -- search_proof
  -- simp_all only [sub_self, mul_eq_zero]
  -- cases h'' with
  -- | inl h_1 =>
  --   apply Or.inr
  --   exact add_eq_zero_iff_eq_neg.1 h_1
  -- | inr h_2 =>
  --   apply Or.inl
  --   rwa [sub_eq_zero] at h_2

  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1

  · right

    -- suggest_tactics
    -- exact eq_neg_of_add_eq_zero_left h1

    exact eq_neg_iff_add_eq_zero.mpr h1
  · left

    -- suggest_tactics
    -- rwa [sub_eq_zero] at h1

    exact eq_of_sub_eq_zero h1

  -- aesop

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  -- search_proof
  -- apply Iff.intro
  -- · intro a
  --   tauto
  -- · intro a a_1
  --   simp_all only [not_true_eq_false, false_or]

  -- suggest_tactics
  -- tauto

  constructor
  · intro h
    by_cases h' : P
    · -- aesop
      right
      exact h h'
    · -- aesop
      left
      exact h'

  -- aesop

  rintro (h | h)
  · intro h'
    exact absurd h' h
  · intro
    exact h
