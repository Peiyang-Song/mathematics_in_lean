import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  -- search_proof
  -- simp_all only [subset_inter_iff, union_subset_iff, inter_subset_left, and_self, true_and]
  -- apply And.intro
  -- · intro x hx
  --   simp_all only [mem_inter_iff, mem_union, true_or]
  -- · intro x hx
  --   simp_all only [mem_inter_iff, mem_union, or_true]

  -- suggest_tactics
  -- rw [inter_union_distrib_left]

  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)

  · -- aesop
    use xs; left; exact xt
  · -- aesop
    use xs; right; exact xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  -- search_proof
  -- intro x hx
  -- simp_all only [mem_diff, mem_union, not_or, not_false_eq_true, and_self]

  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)

  -- suggest_tactics
  -- simp_all

  -- aesop

  intro xu
  apply xntu (Or.inr xu)

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm sorry sorry

example : s ∩ (s ∪ t) = s := by
  -- search_proof
  -- simp_all only [inter_eq_left, subset_union_left]

  -- suggest_tactics
  -- simp

  -- aesop

  ext x; constructor
  · rintro ⟨xs, _⟩
    exact xs
  · intro xs
    use xs; left; exact xs

example : s ∪ s ∩ t = s := by
  -- search_proof
  -- simp_all only [union_eq_left, inter_subset_left]

  -- suggest_tactics
  -- simp

  -- aesop

  ext x; constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  · intro xs; left; exact xs

example : s \ t ∪ t = s ∪ t := by
  -- search_proof
  -- simp_all only [diff_union_self]

  -- suggest_tactics
  -- simp

  -- aesop

  ext x; constructor
  · rintro (⟨xs, nxt⟩ | xt)
    · left
      exact xs
    · right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  -- search_proof
  -- ext1 x
  -- simp_all only [mem_union, mem_diff, mem_inter_iff, not_and]
  -- apply Iff.intro
  -- · intro a
  --   cases a with
  --   | inl h => simp_all only [or_false, not_false_eq_true, imp_self, and_self]
  --   | inr h_1 => simp_all only [or_true, not_true_eq_false, false_implies, and_self]
  -- · intro a
  --   obtain ⟨left, right⟩ := a
  --   cases left with
  --   | inl h => simp_all only [true_implies, not_false_eq_true, and_self, not_true_eq_false, or_false]
  --   | inr h_1 => simp_all only [not_true_eq_false, imp_false, and_self, not_false_eq_true, or_true]

  -- aesop

  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      left
      exact xs
      rintro ⟨_, xt⟩
      contradiction
    · constructor
      right
      exact xt
      rintro ⟨xs, _⟩
      contradiction
  rintro ⟨xs | xt, nxst⟩
  · left
    use xs
    intro xt
    -- suggest_tactics
    -- exact nxst ⟨xs, xt⟩
    apply nxst
    constructor <;> assumption
  · right; use xt; intro xs
    apply nxst
    -- suggest_tactics
    -- exact ⟨xs, xt⟩
    constructor <;> assumption

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by

  intro n
  simp
  intro nprime n_gt
  rcases Nat.Prime.eq_two_or_odd nprime with h | h

  · -- search_proof
    -- subst h
    -- simp_all only [lt_self_iff_false]

    -- aesop

    -- suggest_tactics
    -- simp_all

    rw [h]
    linarith
  · rw [Nat.odd_iff, h]

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  -- search_proof
  -- intro x a
  -- simp_all only [Nat.not_even_iff_odd]
  -- apply And.intro
  -- · exact h₀ x (ssubt a)
  -- · exact h₁ x (ssubt a)

  -- suggest_tactics
  -- tauto

  -- aesop

  intro x xs
  constructor
  · apply h₀ x (ssubt xs)
  apply h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  -- search_proof
  -- simp_all only [Nat.not_even_iff_odd]
  -- obtain ⟨w, h⟩ := h
  -- obtain ⟨left, right⟩ := h
  -- obtain ⟨left_1, right⟩ := right
  -- exact ⟨w, ssubt left, right⟩

  -- suggest_tactics
  -- tauto

  -- aesop

  rcases h with ⟨x, xs, _, px⟩
  use x, ssubt xs

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  -- search_proof
  -- rw [union_comm]
  -- simp [iInter_union]

  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (xs | xI)
    · intro i
      right
      exact xs
    intro i
    left
    exact xI i

  intro h

  by_cases xs : x ∈ s

  · -- aesop

    -- suggest_tactics
    -- exact Or.inl xs
    left
    exact xs

  -- aesop

  right

  intro i
  cases h i
  · -- suggest_tactics
    -- assumption

    assumption

  contradiction

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by

  apply eq_univ_of_forall
  intro x
  simp
  rcases Nat.exists_infinite_primes x with ⟨p, pge, primep⟩
  -- search_proof
  -- exact ⟨p, primep, pge⟩

  -- suggest_tactics
  -- exact ⟨p, primep, pge⟩

  -- aesop

  use p, primep

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
