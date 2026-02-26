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
  fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

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
  show (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
  rintro x h
  rcases h with ⟨xs, xt⟩ | ⟨xs, xu⟩
  . constructor
    . exact xs
    . left
      exact xt
  . constructor
    . exact xs
    . right
      exact xu

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
  rintro x ⟨xs, xntu⟩
  simp
  constructor
  . constructor
    . show x ∈ s
      exact xs
    . show x ∉ t
      intro xt
      have : x ∈ t ∪ u := by exact mem_union_left u xt
      exact xntu this
  . show x ∉ u
    intro xu
    have : x ∈ t ∪ u := by exact mem_union_right t xu
    exact xntu this

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _ ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  -- TODO
  Subset.antisymm sorry sorry

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  . rintro ⟨xs, _⟩
    exact xs
  . intro xs
    have : x ∈ s ∪ t := by
      left
      exact xs
    simp
    constructor
    . exact xs
    . left
      exact xs


example : s ∪ s ∩ t = s := by
  show s ∪ (s ∩ t) = s
  ext x
  constructor
  . rintro (xs | ⟨xs, _⟩)
    . exact xs
    . exact xs
  . intro xs
    left
    exact xs

example : s \ t ∪ t = s ∪ t := by
  show (s \ t) ∪ t = s ∪ t
  ext x
  constructor
  . rintro (⟨xs, xnt⟩ | xt)
    . left
      exact xs
    . right
      exact xt
  . rintro (xs | xt)
    . simp
      left
      exact xs
    . right
      exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  show (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)
  ext x
  constructor
  . rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . simp
      constructor
      . left
        exact xs
      . intro _
        exact xnt
    . simp
      constructor
      . right
        exact xt
      . intro _
        contradiction
  . rintro ⟨xs | xt, xnst⟩
    . simp
      left
      have xnt: x ∉ t := by
        intro xt
        have : x ∈ s ∩ t := by exact mem_inter xs xt
        exact xnst this
      constructor
      . exact xs
      . exact xnt
    . simp
      right
      have xns : x ∉ s := by
        intro xs
        have : x ∈ s ∩ t := by exact mem_inter xs xt
        exact xnst this
      constructor
      . exact xt
      . exact xns

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  -- rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

-- As an exercise, prove the following inclusion. Use intro n to unfold the
-- definition of subset, and use the simplifier to reduce the set-theoretic
-- constructions to logic. We also recommend using the theorems
-- Nat.Prime.eq_two_or_odd and Nat.odd_iff.
#check Nat.Prime.eq_two_or_odd
#check Nat.odd_iff

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  rintro nprime n_gt_two
  rcases Nat.Prime.eq_two_or_odd nprime with n_two | n_odd
  . have : 2 < 2 := by
      calc
        2 < n := by exact n_gt_two
        _ = 2 := by exact n_two
    contradiction
  . exact Nat.odd_iff.mpr n_odd

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
  intro x xs
  constructor
  . exact h₀ x (ssubt xs)
  . exact h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, ⟨xs, xodd, xprime⟩⟩
  have xt : x ∈ t := by exact ssubt xs
  use x

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
  show s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s)
  ext x
  simp
  constructor
  . intro h
    rcases h with xs | xA
    . intro i
      right
      exact xs
    . intro i
      left
      exact xA i
  . intro h
    -- have : ∀ (i : I), (x ∈ A i ∨ x ∈ s) := h -- sanity
    show (x ∈ s) ∨ (∀ (i : I), x ∈ A i)
    by_cases xs : x ∈ s
    . left
      exact xs
    . right
      intro i
      have : x ∈ A i ∨ x ∈ s := by exact h i
      rcases (h i) with xA | xs
      . exact xA
      . contradiction

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

-- Try solving the following example, which is similar. If you start typing
-- eq_univ, tab completion will tell you that apply eq_univ_of_forall is a
-- good way to start the proof. We also recommend using the theorem
-- Nat.exists_infinite_primes.

#check Nat.exists_infinite_primes

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  simp
  intro x
  rcases (Nat.exists_infinite_primes x) with h
  rcases h with ⟨p, ⟨x_le_p, p_prime⟩⟩
  use p
  constructor
  . exact p_prime
  . exact x_le_p

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
