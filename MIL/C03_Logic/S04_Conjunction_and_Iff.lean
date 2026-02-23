import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

-- the official solution is *much* more elegant
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  -- write n = m * k
  have ⟨m_div_n, m_neq_n⟩ := h
  constructor
  -- m ∣ n is given
  . exact m_div_n
  -- bwoc sps n ∣ m
  . intro n_div_m
    -- since m ∣ n, write n = m * k
    rcases m_div_n with ⟨k, n_eq_mk⟩
    -- must have m > 0
    have m_pos : 0 < m := by
      apply Nat.zero_lt_of_ne_zero
      intro m_eq_zero
      have m_eq_n : m = n := by
        calc
          m = 0 := by rw [m_eq_zero]
          _ = 0 * k := by ring
          _ = m * k := by rw [m_eq_zero]
          _ = n := by rw [n_eq_mk]
      exact m_neq_n m_eq_n
    -- write m = n * l
    rcases n_div_m with ⟨l, m_eq_nl⟩
    -- must have n > 0
    have n_pos : 0 < n := by
      apply Nat.zero_lt_of_ne_zero
      intro n_eq_zero
      have m_eq_n : m = n := by
        calc
          m = n * l := by rw [m_eq_nl]
          _ = 0 * l := by rw [n_eq_zero]
          _ = 0 := by ring
          _ = n := by rw [n_eq_zero]
      exact m_neq_n m_eq_n
    -- must have l ≥ 1
    have one_le_l : 1 ≤ l := by
      apply Nat.zero_lt_of_ne_zero
      intro l_eq_zero
      have m_lt_m : m < m := by
        calc
          m = n * l := by rw [m_eq_nl]
          _ = n * 0 := by rw [l_eq_zero]
          _ = 0 := by ring
          _ < m := by exact m_pos
      apply lt_irrefl m m_lt_m
    -- must have k ≥ 2
    have two_le_k : 2 ≤ k := by
      apply (Nat.two_le_iff k).mpr
      constructor
      -- k ≠ 0
      . intro k_eq_zero
        have n_lt_n : n < n := by
          calc
            n = m * k := by exact n_eq_mk
            _ = m * 0 := by rw [k_eq_zero]
            _ = 0 := by ring
            _ < n := by exact n_pos
        apply lt_irrefl n n_lt_n
      -- k ≠ 1
      . intro k_eq_one
        have m_eq_n : m = n := by
          calc
            m = m * 1 := by ring
            _ = m * k := by rw [k_eq_one]
            _ = n := by rw [n_eq_mk]
        exact m_neq_n m_eq_n
    -- it holds that 2 * m ≤ m
    have two_m_le_m : 2 * m ≤ m := by
      calc
        2 * m = 1 * (2 * m) := by rw [one_mul]
        _ ≤ l * (2 * m) := by exact Nat.mul_le_mul_right (2 * m) one_le_l
        _ = 2 * (l * m) := by ring
        _ ≤ k * (l * m) := by exact Nat.mul_le_mul_right (l * m) two_le_k
        _ = (m * k) * l:= by ring
        _ = n * l := by rw [n_eq_mk]
        _ = m := by rw [m_eq_nl]
    -- thus m ≤ 0 < m
    have m_le_zero : m ≤ 0 := by
      linarith
    have m_lt_m : m < m := by
      calc
        m ≤ 0 := by exact m_le_zero
        _ < m := by exact m_pos
    -- m < m is impossible
    apply lt_irrefl m m_lt_m

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  -- sps: x ≤ y ∧ ¬y ≤ x → x ≤ y ∧ x ≠ y
  . rintro ⟨x_le_y, not_y_le_x⟩
    constructor
    . exact x_le_y -- nothing to show
    . intro x_eq_y -- bwoc: sps x = y
      have y_eq_x : y = x := by rw [x_eq_y]
      have y_le_x : y ≤ x := by exact le_of_eq y_eq_x
      exact not_y_le_x y_le_x
  -- sps: x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x
  . rintro ⟨x_le_y, x_neq_y⟩
    constructor
    . exact x_le_y -- nothing to show
    . intro y_le_x -- bwoc: sps y ≤ x
      have x_eq_y : x = y := by
        -- x ≤ y and y ≤ x → x = y
        exact le_antisymm x_le_y y_le_x
      exact x_neq_y x_eq_y

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    have neg_y_sq_nonpos : - y ^ 2 ≤ 0 := by
      have : 0 ≤ y ^ 2 := by exact sq_nonneg y
      linarith
    apply le_antisymm
    -- x ^ 2 ≤ 0
    . calc
        x ^ 2 = - (y ^ 2) := by linarith
        _ ≤ 0 := by exact neg_y_sq_nonpos
    -- x ^ 2 ≥ 0
    . exact sq_nonneg x
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  -- x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
  . rintro h
    constructor
    -- x = 0
    . apply aux h
    -- y = 0
    . have h' : y ^ 2 + x ^ 2 = 0 := by linarith
      apply aux h'
  -- x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
  . rintro ⟨x_eq_zero, y_eq_zero⟩
    calc
      x ^ 2 + y ^ 2 = 0 ^ 2 + y ^ 2 := by rw [x_eq_zero]
      _ = 0 ^ 2 + 0 ^ 2 := by rw [y_eq_zero]
      _ = 0 := by ring

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  apply not_monotone_iff.mpr
  use 0, 1
  norm_num

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  -- pretty much exacly the same as the proof for over ℝ
  constructor
  -- sps: x ≤ y ∧ ¬y ≤ x → x ≤ y ∧ x ≠ y
  . rintro ⟨x_le_y, not_y_le_x⟩
    constructor
    . exact x_le_y -- nothing to show
    . intro x_eq_y -- bwoc: sps x = y
      have y_eq_x : b = a := by rw [x_eq_y]
      have y_le_x : b ≤ a := by exact le_of_eq y_eq_x
      exact not_y_le_x y_le_x
  -- sps: x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x
  . rintro ⟨x_le_y, x_neq_y⟩
    constructor
    . exact x_le_y -- nothing to show
    . intro y_le_x -- bwoc: sps y ≤ x
      have x_eq_y : a = b := by
        -- x ≤ y and y ≤ x → x = y
        exact le_antisymm x_le_y y_le_x
      exact x_neq_y x_eq_y

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  rintro ⟨a_le_a, not_a_le_a⟩
  exact not_a_le_a a_le_a

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  rintro ⟨a_le_b, no_b_le_a⟩
  rintro ⟨b_le_c, not_c_le_b⟩
  constructor
  -- a ≤ c
  . apply le_trans a_le_b b_le_c
  -- ¬ c ≤ a
  . intro c_le_a
    -- this would imply that c ≤ a ≤ b, a contradiction
    have c_le_b : c ≤ b := by
      calc
        c ≤ a := by exact c_le_a
        _ ≤ b := by exact a_le_b
    exact not_c_le_b c_le_b

end
