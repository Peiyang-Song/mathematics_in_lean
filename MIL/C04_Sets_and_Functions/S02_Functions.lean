import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  -- search_proof
  -- simp_all only [image_subset_iff]

  -- suggest_tactics
  -- simp

  -- aesop

  constructor
  · intro h x xs
    have : f x ∈ f '' s := mem_image_of_mem _ xs
    exact h this
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw [← fxeq]
  apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  -- search_proof
  -- simp_all only [preimage_image_eq, subset_refl]

  -- suggest_tactics
  -- rw [preimage_image_eq _ h]

  -- aesop

  rintro x ⟨y, ys, fxeq⟩
  rw [← h fxeq]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  -- search_proof
  -- simp_all only [image_subset_iff, subset_refl]

  -- suggest_tactics
  -- simp

  -- aesop

  rintro y ⟨x, xmem, rfl⟩
  exact xmem

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  -- search_proof
  -- simp_all only [image_preimage_eq, subset_refl]

  -- suggest_tactics
  -- simp [h]

  -- aesop

  intro y yu
  rcases h y with ⟨x, fxeq⟩
  use x
  constructor
  · show f x ∈ u
    rw [fxeq]
    exact yu
  exact fxeq

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  -- search_proof
  -- simp_all only [image_subset_iff]
  -- intro x hx
  -- simp_all only [mem_preimage, mem_image]
  -- exact ⟨x, h hx, rfl⟩

  -- suggest_tactics
  -- exact image_subset f h

  rintro y ⟨x, xs, fxeq⟩

  -- aesop

  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  -- search_proof
  -- exact preimage_mono h

  -- suggest_tactics
  -- exact preimage_mono h

  intro x; apply h

  -- aesop

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  -- search_proof
  -- simp_all only [preimage_union]

  -- suggest_tactics
  -- simp

  -- aesop

  ext x; rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  -- search_proof
  -- simp_all only [subset_inter_iff, image_subset_iff]
  -- apply And.intro
  -- · intro x hx
  --   simp_all only [mem_inter_iff, mem_preimage, mem_image]
  --   obtain ⟨left, right⟩ := hx
  --   exact ⟨x, left, rfl⟩
  -- · intro u hu
  --   simp_all only [mem_inter_iff, mem_preimage, mem_image]
  --   obtain ⟨left, right⟩ := hu
  --   exact ⟨u, right, rfl⟩

  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor

  -- suggest_tactics
  -- exacts [mem_image_of_mem _ xs, mem_image_of_mem _ xt]

  · -- aesop
    use x, xs
  · -- aesop
    use x, xt

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  -- search_proof
  -- intro u hu
  -- simp_all only [mem_inter_iff, mem_image]
  -- obtain ⟨left, right⟩ := hu
  -- obtain ⟨w, h_1⟩ := left
  -- obtain ⟨w_1, h_2⟩ := right
  -- obtain ⟨left, right⟩ := h_1
  -- obtain ⟨left_1, right_1⟩ := h_2
  -- subst right
  -- apply Exists.intro
  -- · apply And.intro
  --   · apply And.intro
  --     on_goal 2 => {exact left_1
  --     }
  --     · rwa [h right_1]
  --   · simp_all only


  rintro y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, fx₂eq⟩⟩
  use x₁
  constructor
  · use x₁s
    rw [← h fx₂eq]

    -- suggest_tactics
    -- exact x₂t

    -- aesop

    exact x₂t

  · -- suggest_tactics
    -- rfl

    -- aesop

    rfl

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  -- search_proof
  -- intro u hu
  -- simp_all only [mem_diff, mem_image, not_exists, not_and]
  -- obtain ⟨left, right⟩ := hu
  -- obtain ⟨w, h⟩ := left
  -- obtain ⟨left, right_1⟩ := h
  -- subst right_1
  -- apply Exists.intro
  -- · apply And.intro
  --   · apply And.intro
  --     · exact left
  --     · apply Aesop.BuiltinRules.not_intro
  --       intro a
  --       apply right
  --       on_goal 2 => {rfl
  --       }
  --       · simp_all only
  --   · simp_all only

  rintro y ⟨⟨x₁, x₁s, rfl⟩, h⟩

  -- aesop

  use x₁
  constructor
  · constructor
    · exact x₁s
    · intro h'
      apply h
      -- suggest_tactics
      -- exact mem_image_of_mem f h'
      use x₁, h'
  · -- suggest_tactics
    -- rw [mem_image] at h
    rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  -- search_proof
  -- simp [image_inter_preimage]

  -- suggest_tactics
  -- simp [image_inter_preimage]

  -- aesop

  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
  exact ⟨⟨x, xs, rfl⟩, fxv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by

  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩

  -- search_proof
  -- simp_all only [mem_preimage, mem_inter_iff, mem_image, and_true]
  -- exact ⟨x, xs, rfl⟩

  -- aesop

  exact ⟨⟨x, xs, rfl⟩, fxu⟩

  -- suggest_tactics

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by

  rintro x ⟨xs, fxu⟩

  -- search_proof
  -- simp_all only [mem_preimage, preimage_inter, mem_inter_iff, mem_image, and_true]
  -- exact ⟨x, xs, rfl⟩

  -- aesop

  exact ⟨⟨x, xs, rfl⟩, fxu⟩

  -- suggest_tactics

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  -- search_proof
  -- simp_all only [preimage_union, union_subset_iff, subset_union_right, and_true]
  -- simp [subset_def]
  -- intro x a
  -- exact Or.inl ⟨x, a, rfl⟩

  rintro x (xs | fxu)

  · -- aesop

    left

    -- suggest_tactics
    -- exact mem_image_of_mem _ xs

    exact ⟨x, xs, rfl⟩

  -- aesop

  -- suggest_tactics
  -- exact Or.inr fxu

  right; exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  -- search_proof
  -- simp [image_iUnion]

  -- suggest_tactics
  -- simp [image_iUnion]

  -- aesop

  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  -- search_proof
  -- simp_all only [subset_iInter_iff, image_subset_iff]
  -- intro i
  -- intro x hx
  -- simp_all only [mem_iInter, mem_preimage, mem_image]
  -- exact ⟨x, hx i, rfl⟩

  intro y; simp

  -- suggest_tactics
  -- tauto

  -- aesop

  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by

  intro y; simp
  intro h
  rcases h i with ⟨x, xAi, fxeq⟩

  use x; constructor
  ·
    intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩

    -- search_proof
    -- subst fxeq
    -- convert x'Ai
    -- apply injf
    -- simp_all only

    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this

    -- suggest_tactics
    -- rwa [this]

    -- Aesop

    rw [this]
    exact x'Ai


  -- search_proof
  -- subst fxeq
  -- simp_all only

  -- suggest_tactics
  -- exact fxeq

  -- aesop

  exact fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  -- search_proof
  -- simp_all only [preimage_iUnion]

  -- suggest_tactics
  -- simp

  -- aesop

  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  -- aesop

  ext x

  -- search_proof
  -- simp_all only [mem_preimage, mem_iInter]

  -- suggest_tactics
  -- simp

  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  -- search_proof
  -- simp_all only [ge_iff_le]
  -- intro x hx
  -- intro x₂ a a_1
  -- simp_all only [mem_setOf_eq, sqrt_inj]

  intro x xnonneg y ynonneg

  -- aesop

  intro e
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt xnonneg]
    _ = sqrt y ^ 2 := by rw [e]
    _ = y := by rw [sq_sqrt ynonneg]

  -- suggest_tactics

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  -- search_proof
  -- simp_all only [ge_iff_le]
  -- intro x hx
  -- intro x₂ a a_1
  -- simp_all only [mem_setOf_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj]

  intro x xnonneg y ynonneg

  -- aesop

  intro e

  -- suggest_tactics
  -- simp_all

  dsimp at *
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq xnonneg]
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq ynonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by

  ext y; constructor
  · rintro ⟨x, ⟨xnonneg, rfl⟩⟩
    apply sqrt_nonneg
  intro ynonneg
  use y ^ 2

  -- search_proof
  -- simp_all only [ge_iff_le, mem_setOf_eq, pow_nonneg, sqrt_sq, and_self]

  -- aesop

  dsimp at *

  -- suggest_tactics
  -- simp [ynonneg]

  constructor
  apply pow_nonneg ynonneg
  apply sqrt_sq
  assumption


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  -- search_proof
  -- simp_all only [ge_iff_le]
  -- ext
  -- simp_all only [mem_range, mem_setOf_eq]
  -- apply Iff.intro
  -- · intro a
  --   obtain ⟨w, h⟩ := a
  --   subst h
  --   positivity
  -- · intro a
  --   apply Exists.intro
  --   · rw [← Real.sq_sqrt a]

  ext y
  constructor
  · rintro ⟨x, rfl⟩
    dsimp at *
    apply pow_two_nonneg
  intro ynonneg
  use sqrt y

  -- aesop

  exact sq_sqrt ynonneg

  -- suggest_tactics

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by

  constructor
  · intro h y

    -- search_proof
    -- rename_i h_1
    -- obtain ⟨w, h_1⟩ := h_1
    -- simp only [inverse, h.eq_iff]
    -- simp_all only [exists_eq, ↓reduceDIte, choose_eq]

    apply h
    apply inverse_spec

    -- suggest_tactics
    -- use y

    -- aesop

    use y

  -- search_proof
  -- intro a
  -- obtain ⟨w, h⟩ := h
  -- exact a.injective

  intro h x1 x2 e
  rw [← h x1, ← h x2, e]

  -- suggest_tactics

  -- aesop

example : Surjective f ↔ RightInverse (inverse f) f := by

  constructor
  · intro h y
    apply inverse_spec

    -- search_proof
    -- rename_i h_1
    -- obtain ⟨w, h_1⟩ := h_1
    -- apply h

    -- suggest_tactics
    -- exact h y

    -- aesop

    apply h


  -- search_proof
  -- intro a
  -- obtain ⟨w, h⟩ := h
  -- exact a.rightInverse.surjective

  -- suggest_tactics
  -- tauto

  intro h y

  -- aesop

  use inverse f y
  apply h

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by

  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁

  -- search_proof
  -- simp_all only [not_true_eq_false, S]

  -- aesop

  have h₃ : j ∉ S := by rwa [h] at h₁

  -- suggest_tactics
  -- exact h₃ h₁

  contradiction

end
