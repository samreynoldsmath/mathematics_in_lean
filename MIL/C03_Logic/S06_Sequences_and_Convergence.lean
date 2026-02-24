import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have nge_Ns : n ≥ Ns := by exact le_of_max_le_left nge
  have nge_Nt : n ≥ Nt := by exact le_of_max_le_right nge
  have sn_a_lt_eps2 : |s n - a| < ε / 2 := by exact hs n nge_Ns
  have tn_b_lt_eps2 : |t n - b| < ε / 2 := by exact ht n nge_Nt
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; ring
    _ ≤ |s n - a| + |t n - b| := by exact abs_add_le (s n - a) (t n - b)
    _ < (ε / 2) + (ε / 2) := by apply add_lt_add sn_a_lt_eps2 tn_b_lt_eps2
    _ ≤ ε := by linarith

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  have ac_nonzero : |c| ≠ 0 := by exact abs_ne_zero.mpr h
  intro ε εpos
  dsimp
  have ε_c_pos : ε / |c| > 0 := by exact div_pos εpos acpos
  rcases cs (ε / |c|) ε_c_pos with ⟨N, h⟩
  use N
  intro n nge
  have sn_a_lt_eps : |s n - a| < ε / |c| := by exact h n nge
  calc
    |c * s n - c * a| = |c * (s n - a)| := by congr; ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ < |c| * (ε / |c|) := by exact (mul_lt_mul_left acpos).mpr (h n nge)
    _ = ε := by exact mul_div_cancel₀ ε ac_nonzero

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngeN
  calc
    |s n| = |s n - a + a| := by congr; linarith
    _ ≤ |s n - a| + |a| := by exact abs_add_le (s n - a) a
    _ < 1 + |a| := by exact (add_lt_add_iff_right |a|).mpr (h n ngeN)
    _ = |a| + 1 := by linarith

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have B_nonzero : B ≠ 0 := by exact Ne.symm (ne_of_lt Bpos)
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngeN
  have ngeN₀ : n ≥ N₀ := by exact le_of_max_le_left ngeN
  have ngeN₁ : n ≥ N₁ := by exact le_of_max_le_right ngeN
  have sn_lt_B : |s n| < B := by exact h₀ n ngeN₀
  have tn_lt_epsB : |t n - 0| < ε / B := by exact h₁ n ngeN₁
  have sn_nonneg : 0 ≤ |s n| := by exact abs_nonneg (s n)
  have tn_nonneg : 0 ≤ |t n - 0| := by exact abs_nonneg (t n - 0)
  calc
    |s n * t n - 0| = |s n * t n| := by congr; linarith
    _ = |s n| * |t n| := by exact abs_mul (s n) (t n)
    _ = |s n| * |t n - 0| := by congr; linarith
    _ < B * (ε / B) := by
      apply mul_lt_mul'' sn_lt_B tn_lt_epsB sn_nonneg tn_nonneg
    _ = ε := by exact mul_div_cancel₀ ε B_nonzero

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    exact abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have N_ge_Na : N ≥ Na := by exact Nat.le_max_left Na Nb
  have N_ge_Nb : N ≥ Nb := by exact Nat.le_max_right Na Nb
  have absa : |s N - a| < ε := by
    exact hNa N N_ge_Na
  have absb : |s N - b| < ε := by
    exact hNb N N_ge_Nb
  have : |a - s N| = |s N - a| := by exact abs_sub_comm a (s N)
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |(a - s N) + (s N - b)| := by congr; linarith
      _ ≤ |a - s N| + |s N - b| := by exact abs_add_le (a - s N) (s N - b)
      _ = |s N - a| + |s N - b| := by rw [this]
      _ < ε + ε := by exact add_lt_add (hNa N N_ge_Na) (hNb N N_ge_Nb)
      _ = |a - b| / 2 + |a - b| / 2 := by exact rfl
      _ = |a - b| := by linarith
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
