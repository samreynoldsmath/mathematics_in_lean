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

#check le_max_left
#check le_max_right
#check max_le

-- goofy
lemma lem₁ : max a b ≤ max b a := by
  apply max_le
  apply le_max_right
  apply le_max_left

example : max a b = max b a := by
  apply le_antisymm
  apply lem₁
  apply lem₁

-- recommended, clean
example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

-- definitely the most complicated way to prove this
example : min (min a b) c = min a (min b c) := by
  -- show both sides are bounded by a,b,c
  have left_bound_a : min (min a b) c ≤ a:= by
    apply le_trans
    apply min_le_left
    apply min_le_left
  have left_bound_b : min (min a b) c ≤ b:= by
    apply le_trans
    apply min_le_left
    apply min_le_right
  have left_bound_c : min (min a b) c ≤ c:= by
    apply min_le_right
  have right_bound_a : min a (min b c) ≤ a:= by
    apply min_le_left
  have right_bound_b : min a (min b c) ≤ b:= by
    apply le_trans
    apply min_le_right
    apply min_le_left
  have right_bound_c : min a (min b c) ≤ c:= by
    apply le_trans
    apply min_le_right
    apply min_le_right
  -- use the inequalities above to prove equality
  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    apply le_min
    . apply left_bound_a
    . apply le_min
      . apply left_bound_b
      apply left_bound_c
  . show min a (min b c) ≤ min (min a b) c
    apply le_min
    . apply le_min
      . apply right_bound_a
      apply right_bound_b
    . apply right_bound_c

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . show min a b + c ≤ a + c
    have h₁ : min a b ≤ a := by apply min_le_left
    linarith
  . show min a b + c ≤ b + c
    have h₂ : min a b ≤ b := by apply min_le_right
    linarith

theorem aux2 : min (a + c) (b + c) - c ≤ a := by
  have h : min (a + c) (b + c) ≤ a + c := by
    apply min_le_left
  linarith

theorem aux3 : min (a + c) (b + c) - c ≤ b := by
  have h : min (a + c) (b + c) ≤ b + c := by
    apply min_le_right
  linarith

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply aux
  . show min (a + c) (b + c) ≤ min a b + c
    have h : min (a + c) (b + c) - c ≤ min a b := by
      apply le_min
      . apply aux2 -- super hacky
      . apply aux3
    linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  -- not in three lines or less... but neither is the official solution!
  have h : |a| ≤ |a - b| + |b| := by
    calc
      |a| = |(a - b) + b| := by ring
      _ ≤ |a - b| + |b| := by apply abs_add
  linarith
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

#check dvd_add
#check dvd_add_left
#check dvd_add_right
#check dvd_pow
#check dvd_mul_of_dvd_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  . show x ∣ y * (x * z) + x ^ 2
    apply dvd_add
    . show x ∣ y * (x * z)
      have h₁ : y * (x * z) = (y * z) * x := by ring
      rw [h₁]
      apply dvd_mul_left
    . show x ∣ x ^ 2
      apply dvd_mul_left
  . show x ∣ w ^ 2
    apply dvd_pow h
    exact Ne.symm (Nat.zero_ne_add_one 1) -- wild way to state 2 ≠ 0
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

#check Nat.gcd_def
#check Nat.gcd_comm

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.gcd_comm -- cheating?
end
