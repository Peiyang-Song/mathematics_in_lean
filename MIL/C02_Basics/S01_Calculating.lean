-- 6 examples in this file, evaluated 6.

import MIL.Common
import Mathlib.Data.Real.Basic

import Aesop

-- structure neuralConfig where
--   neuralProver : String

-- @[aesop unsafe 50% neural]
-- def conf : neuralConfig := { neuralProver := "onnx-leandojo-lean4-tacgen-byt5-small" }

-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  -- sorry
  -- ring_nf -- suggest_tactics -- Yes.
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]
  -- aesop
  -- [1/6] 3/0

-- theorem my_thm (a b c : ℝ) : c * b * a = b * (a * c) := by
--   aesop

-- #print axioms my_thm

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  -- sorry
  -- ring_nf -- suggest_tactics -- Yes.
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]
  -- aesop
  -- [2/6] 3/0

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  -- sorry
  -- ring_nf -- suggest_tactics -- Yes.
  rw [mul_comm]
  rw [mul_assoc]
  -- aesop
  -- [3/6] 2/0

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  -- sorry
  -- rw [mul_left_comm, ← mul_assoc] -- suggest_tactics -- Yes.
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]
  -- aesop
  -- [4/6] 3/0

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  -- sorry
  -- simp [h, mul_assoc] -- suggest_tactics -- Yes.
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]
  -- aesop
  -- [5/6] 3/0

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  -- sorry
  -- rw [hyp] -- suggest_tactics -- No.
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  -- aesop
  rw [sub_self]
  -- [6/6] 3/0

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
