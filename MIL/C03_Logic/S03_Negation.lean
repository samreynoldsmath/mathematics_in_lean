import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h' -- BWOC
  have : a < a := lt_trans h h' -- we would have: a < b < a, so a < a
  apply lt_irrefl a this -- but a < a is a contradiction

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub -- BWOC, assume f has an upper bound
  rcases fnub with ⟨a, fnuba⟩ -- f(x) ≤ a for all x
  rcases h a with ⟨x, hx⟩ -- for this a, we have ∃ x with f(x) > a by hypth.
  have : f x ≤ a := fnuba x -- and yet f(x) ≤ a
  linarith -- obtain a contradiction by arithmetic

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : a ≤ f x := fnlba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  -- f(x) = x is not bounded from above
  rintro ⟨a, f_bdd_a⟩ -- bwoc assume f(x) ≤ a for all x
  have h : (fun x ↦ x) (a + 1) ≤ a := by
    apply f_bdd_a (a + 1)
  have h': (fun x ↦ x) (a + 1) > a := by
    dsimp
    linarith
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge -- get the negation statement
  intro b_le_a -- proceed to BWOC
  have  : f b < f b := by
    calc
      f b ≤ f a := by apply h b_le_a -- b ≤ a → f(b) ≤ f(a)
      _ < f b := by apply h' -- so f(b) ≤ f(a) < f(b)
  apply lt_irrefl (f b) this -- f(b) < f(b) is a contradiction

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro f_is_mono -- bwoc
  have : f a < f a := by
    calc
      f a ≤ f b := by apply f_is_mono h
      _ < f a := by apply h'
  apply lt_irrefl (f a) this

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  -- counterexample: a constant function
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ) -- the constant function zero
  have monof : Monotone f := by -- this function is monotone
    rintro a b a_le_b
    calc
      f a = 0 := rfl
      _ ≤ 0 := by apply le_refl
      _ = f b := rfl
  have h' : f 1 ≤ f 0 := le_refl _
  -- have : 1 ≤ 0 := h monof h' -- so annoying this doesn't work
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

-- Use le_of_not_gt to prove the following
#check le_of_not_gt

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro x_pos -- sps x > 0
  let ε := x / 2
  have eps_pos : 0 < ε := by
    calc
      0 < x / 2 := half_pos x_pos
      _ = ε := rfl
  have x_lt_eps : x < ε := h ε eps_pos
  have : ε < ε := by
    calc
      ε = x / 2 := rfl
      _ < x := div_two_lt_of_pos x_pos
      _ < ε := x_lt_eps
  apply lt_irrefl ε this

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro exists_x_st_Px
  rcases exists_x_st_Px with ⟨x, Px⟩
  apply h x Px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  -- DON'T DO THIS
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro forall_x_Px
  rcases h with ⟨x, not_P_x⟩
  exact not_P_x (forall_x_Px x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  apply by_contra h -- easy?

example (h : Q) : ¬¬Q := by
  intro not_Q
  exact not_Q h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra not_exist_x_st_fx_gt_a
  apply h
  use a
  change ∀ x, f x ≤ a
  intro x
  apply le_of_not_gt
  intro a_lt_fx
  apply not_exist_x_st_fx_gt_a
  use x

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  by_contra h'
  apply h
  push_neg at h'
  exact h'

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith -- will learn next section

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
