import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  -- suggest_tactics
  -- rw [max_comm]

  -- search_proof
  -- rw [max_comm]

  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left
  -- aesop


example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min

    -- suggest_tactics
    -- all_goals simp
  -- suggest_tactics
  -- simp

    · apply le_trans
      apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left

  --     aesop
  --   aesop
  -- aesop

      -- search_proof
      -- simp_all only [min_le_iff, le_refl, or_true]
    -- search_proof
    -- simp_all only [min_le_iff, le_refl, or_true]
  -- search_proof
  -- simp_all only [le_min_iff, min_le_iff, le_refl, true_or, or_true, and_self]

      apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
  apply le_trans
  apply min_le_right
  apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  -- suggest_tactics
  -- simp

  -- search_proof
  -- simp_all only [le_min_iff, add_le_add_iff_right, min_le_iff, le_refl, true_or, or_true, and_self]

  -- aesop

  apply le_min
  · apply add_le_add_right
    apply min_le_left
  apply add_le_add_right
  apply min_le_right


example : min a b + c = min (a + c) (b + c) := by
  -- suggest_tactics
  -- simp only [add_comm, min_add_add_right]

  -- search_proof
  -- simp only [add_comm, min_add_add_right]

  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right

  -- aesop

  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]


#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| :=
  sorry -- Proof by term rather than by tactic.
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right

    -- search_proof
    -- exact dvd_pow_self x two_ne_zero
  -- search_proof
  -- rw [pow_two]
  -- exact h.mul_left w

    apply dvd_mul_left
  rw [pow_two]

  -- suggest_tactics
  -- exact h.mul_left w

  apply dvd_mul_of_dvd_right

  -- aesop

  exact h

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  -- suggest_tactics
  -- rw [Nat.gcd_comm]

  -- search_proof
  -- rw [Nat.gcd_comm]

  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left

  -- aesop

end
