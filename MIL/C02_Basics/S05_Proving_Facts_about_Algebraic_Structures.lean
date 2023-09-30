-- 12 examples in this file, evaluated 5.
import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

import Aesop

structure neuralConfig where
  neuralProver : String

@[aesop unsafe 50% neural]
def conf : neuralConfig := { neuralProver := "onnx-leandojo-lean4-tacgen-byt5-small" }

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  sorry

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  -- rw [← inf_assoc, inf_right_comm] -- suggest_tactics
  -- sorry
  apply le_antisymm
  · apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    apply le_trans
    apply inf_le_right
    apply inf_le_left
  apply le_trans
  apply inf_le_right
  -- aesop
  apply inf_le_right
  -- [1/5] 18/0

example : x ⊔ y = y ⊔ x := by
  sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  -- simp only [sup_assoc, sup_assoc] -- suggest_tactics
  -- sorry
  -- aesop
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      apply le_sup_left
      · apply le_trans
        apply @le_sup_left _ _ y z
        apply le_sup_right
    apply le_trans
    apply @le_sup_right _ _ y z
    apply le_sup_right
  apply sup_le
  · apply le_trans
    apply @le_sup_left _ _ x y
    apply le_sup_left
  apply sup_le
  · apply le_trans
    apply @le_sup_right _ _ x y
    apply le_sup_left
  apply le_sup_right
  -- [2/5] 0/0

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  -- rwa [sub_nonneg] -- suggest_tactics
  -- sorry
  aesop
  -- [3/5] 0/0

theorem aux2 (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  -- exact mul_le_mul_of_nonneg_right h h' -- suggest_tactics
  -- sorry
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  -- aesop
  exact aux2 _ _ h1
  -- [4/5] 2/0

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  -- simp [dist_nonneg] -- suggest_tactics
  -- sorry
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]
  -- aesop
  -- [5/5] 4/0

end
