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
  rcases le_or_gt 0 x with h₁ | h₂
  . have : x ≤ |x| := by
      calc
        x = |x| := by rw [abs_of_nonneg h₁]
        _ ≤ |x| := by apply le_refl
    exact this
  . have h : 0 ≤ -x := by linarith
    have : x ≤ |x| := by
      calc
        x ≤ 0 := by apply le_of_lt h₂
        _ ≤ -x := by exact h
        _ = |x| := by rw [abs_of_neg h₂]
    exact this


theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h₁ | h₂
  . have : -x ≤ |x| := by
      calc
        -x ≤ x := by linarith
        _ = |x| := by rw [abs_of_nonneg h₁]
    exact this
  . have : -x ≤ |x| := by
      calc
        -x = |x| := by rw [abs_of_neg h₂]
        _ ≤ |x| := by apply le_refl
    exact this

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h₁ | h₂
  . have : |x + y| ≤ |x| + |y| := by
      calc
        |x + y| = x + y := by rw [abs_of_nonneg h₁]
        _ ≤ |x| + y := by apply add_le_add_right (le_abs_self x)
        _ ≤ |x| + |y| := by apply add_le_add_left (le_abs_self y)
    exact this
  . have : |x + y| ≤ |x| + |y| := by
      calc
        |x + y| = -(x + y) := by rw [abs_of_neg h₂]
        _ = -x + (-y) := by linarith
        _ ≤ |x| + (-y) := by apply add_le_add_right (neg_le_abs_self x)
        _ ≤ |x| + |y| := by apply add_le_add_left (neg_le_abs_self y)
    exact this

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . intro h
    rcases le_or_gt 0 y with h₁ | h₂
    . left
      have : x < y := by
        calc
          x < |y| := by exact h
          _ = y := by rw [abs_of_nonneg h₁]
      exact this
    . right
      have : x < -y := by
        calc
          x < |y| := by exact h
          _ = -y := by rw [abs_of_neg h₂]
      exact this
  . intro h
    rcases h with h₁ | h₂
    . have : x < |y| := by
        calc
          x < y := by exact h₁
          _ ≤ |y| := by apply (le_abs_self y)
      exact this
    . have : x < |y| := by
        calc
          x < -y := by exact h₂
          _ ≤ |y| := by apply (neg_le_abs_self y)
      exact this

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  . intro h
    have y_pos : 0 < y := by
      calc
        0 ≤ |x| := by apply abs_nonneg x
        _ < y := by exact h
    have neg_y_neg : -y < 0 := by linarith
    rcases le_or_gt 0 x with h₁ | h₂
    . constructor
      . have : -y < x := by
          calc
            -y < 0 := by exact neg_y_neg
            _ ≤ x := by exact h₁
        exact this
      . have : x < y := by
          calc
            x = |x| := by rw [abs_of_nonneg h₁]
            _ < y := by exact h
        exact this
    . constructor
      . have : -x < y := by
          calc
            -x ≤ |x| := by rw [abs_of_neg h₂]
            _ < y := by exact h
        linarith
      . have : x < y := by
          calc
            x < 0 := by exact h₂
            _ < y := by exact y_pos
        exact this
  . rintro ⟨h₁, h₂⟩
    rcases le_or_gt 0 x with x_nonneg | x_neg
    . have : |x| < y := by
        calc
          |x| = x := by rw [abs_of_nonneg x_nonneg]
          _ < y := by exact h₂
      exact this
    . have neg_x_lt_y : -x < y := by linarith
      have : |x| < y := by
        calc
          |x| = -x := by rw [abs_of_neg x_neg]
          _ < y := by exact neg_x_lt_y
      exact this

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
  rcases h with ⟨x, y, h₁ | h₂⟩
  . calc
      z = x ^ 2 + y ^ 2 := by exact h₁
      _ ≥ 0 := by apply add_nonneg (sq_nonneg x) (sq_nonneg y)
  . calc
      z = x ^ 2 + y ^ 2 + 1 := by exact h₂
      _ ≥ x ^ 2 + y ^ 2 := by linarith
      _ ≥ 0 := by apply add_nonneg (sq_nonneg x) (sq_nonneg y)

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have poly_root : x ^ 2 - 1 = 0 := by linarith
  have factored : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = 0 := by exact poly_root
  rcases eq_zero_or_eq_zero_of_mul_eq_zero factored with h₁ | h₂
  . left
    linarith
  . right
    linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  -- copy and paste bb
  have poly_root : x ^ 2 - y ^ 2 = 0 := by linarith
  have factored : (x - y) * (x + y) = 0 := by
    calc
      (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      _ = 0 := by exact poly_root
  rcases eq_zero_or_eq_zero_of_mul_eq_zero factored with h₁ | h₂
  . left
    linarith
  . right
    linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have poly_root : x ^ 2 - 1 = 0 := by --linarith
    calc
      x ^ 2 - 1 = 1 - 1 := by rw [h]
      _ = 0 := by apply sub_self
  have factored : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      _ = 0 := by exact poly_root
  rcases eq_zero_or_eq_zero_of_mul_eq_zero factored with h₁ | h₂
  . left
    -- linarith
    calc
      x = x + 0 := by rw [add_zero]
      _ = x + (1 + -1) := by rw [add_neg_cancel]
      _ = x + (-1 + 1) := by rw [add_comm 1]
      _ = (x + -1) + 1 := by rw [add_assoc]
      _ = (x - 1) + 1 := by ring -- somehow this works??
      _ = 0 + 1 := by rw [h₁]
      _ = 1 := by rw [zero_add]
  . right
    -- linarith
    calc
      x = x + 0 := by rw [add_zero]
      _ = x + (1 + -1) := by rw [add_neg_cancel]
      _ = (x + 1) + -1 := by rw [add_assoc]
      _ = 0 + -1 := by rw [h₂]
      _ = -1 := by rw [zero_add]

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have poly_root : x ^ 2 - y ^ 2 = 0 := by --linarith
    calc
      x ^ 2 - y ^ 2 = y ^ 2 - y ^ 2 := by rw [h]
      _ = 0 := by apply sub_self
  have factored : (x - y) * (x + y) = 0 := by
    calc
      (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      _ = 0 := by exact poly_root
  rcases eq_zero_or_eq_zero_of_mul_eq_zero factored with h₁ | h₂
  . left
    -- linarith
    calc
      x = x + 0 := by rw [add_zero]
      _ = x + (y + -y) := by rw [add_neg_cancel]
      _ = x + (-y + y) := by rw [add_comm y]
      _ = (x + -y) + y := by rw [add_assoc]
      _ = (x - y) + y := by ring -- somehow this works??
      _ = 0 + y := by rw [h₁]
      _ = y := by rw [zero_add]
  . right
    -- linarith
    calc
      x = x + 0 := by rw [add_zero]
      _ = x + (y + -y) := by rw [add_neg_cancel]
      _ = (x + y) + -y := by rw [add_assoc]
      _ = 0 + -y := by rw [h₂]
      _ = -y := by rw [zero_add]

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
  constructor
  -- (P → Q) → ¬P ∨ Q
  . intro h
    by_cases h' : P
    -- sps P is true
    -- P → Q, so Q is true
    -- then ¬ P ∨ Q is true
    . right
      have : Q := by exact h h'
      exact this
    -- sps ¬P is true
    -- then ¬P ∨ Q is true for any Q
    . left
      exact h'
  -- ¬P ∨ Q → (P → Q)
  . intro h
    rcases h with h₁ | h₂
    -- sps ¬P is true
    -- then P is false
    -- False → True/False is true, so P → Q
    -- can show this by contrapositive: ¬Q → ¬P
    . contrapose
      intro h'
      exact h₁
    -- sps Q
    -- True/False → True is true, so P → Q
    . intro h'
      exact h₂
