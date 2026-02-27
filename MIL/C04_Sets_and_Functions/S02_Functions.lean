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

#check mem_image_of_mem

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . rintro h x xs
    simp
    have : f x ∈ f '' s := by
      simp
      use x
    exact h this
  . rintro h y yfs
    have : ∃ x ∈ s, f x = y := by exact yfs
    rcases this with ⟨x, xs, fxy⟩
    have yfx : y = f x := by rw[fxy]
    have : f x ∈ v := by exact h xs
    exact mem_of_eq_of_mem yfx this

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x₁ x₁_ffs
  have fx₁_fs: f x₁ ∈ f '' s := by exact x₁_ffs
  rcases fx₁_fs with ⟨x₂, x₂s, fx₁_fx₂⟩
  have : x₁ = x₂ := by rw [h fx₁_fx₂]
  exact mem_of_eq_of_mem this x₂s

example : f '' (f ⁻¹' u) ⊆ u := by
  let s := f⁻¹' u
  simp
  -- wow I can't belive this works! feels like cheating

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xfu, fxy⟩
  have fxu : f x ∈ u := by exact xfu
  have yfx : y = f x := by rw [fxy]
  exact mem_of_eq_of_mem yfx xfu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y yu
  simp
  have : ∃ x : α, f x = y := by exact h y
  rcases this with ⟨x, fxy⟩
  use x
  constructor
  . exact mem_of_eq_of_mem fxy yu
  . exact fxy

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y yfs
  simp
  have : ∃ x ∈ s, f x = y := by exact yfs
  rcases this with ⟨x, xs, fxy⟩
  use x
  constructor
  . exact h xs
  . exact fxy

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x xfu
  simp
  have : f x ∈ u := by exact xfu
  exact h xfu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  simp -- wow

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  . intro h
    have : f x ∈ u ∪ v := by exact h
    rcases this with xu | xv
    . left
      exact xu
    . right
      exact xv
  . intro h
    rcases h with h₁ | h₂
    . have : f x ∈ u ∪ v:= by
        left
        exact h₁
      exact this
    . have : f x ∈ u ∪ v:= by
        right
        exact h₂
      exact this

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y yfst
  rcases yfst with ⟨x, ⟨xs, xt⟩, fxy⟩
  constructor
  . simp
    use x
  . simp
    use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨yfs, yft⟩
  simp
  rcases yfs with ⟨x₁, x₁s, fx₁y⟩
  rcases yft with ⟨x₂, x₂t, fx₂y⟩
  have fx₁_eq_fx₂ : f x₁ = f x₂ := by
    calc
      f x₁ = y := by rw [fx₁y]
      _ = f x₂ := by rw [fx₂y]
  have x₁x₂: x₁ = x₂ := by
    apply h fx₁_eq_fx₂
  use x₁
  constructor
  . constructor
    . exact x₁s
    . exact mem_of_eq_of_mem x₁x₂ x₂t
  . exact fx₁y

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨yfs, ynft⟩
  simp
  rcases yfs with ⟨x, xs, fxy⟩
  have yfx : y = f x := by rw [fxy]
  use x
  constructor
  . constructor
    . exact xs
    . by_contra
      have : f x ∈ f '' t := by
        simp
        use x
      have : y ∈ f '' t := by
        exact mem_of_eq_of_mem yfx this
      exact ynft this
  . exact fxy

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨xfu, xnfv⟩
  simp
  constructor
  . exact xfu
  . exact xnfv

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  . rintro h
    have : y ∈ (f '' s) ∩ v := by exact h -- sanity check
    rcases h with ⟨⟨x, xs, fxy⟩, yv⟩
    simp
    use x
    constructor
    . constructor
      . exact xs
      . exact mem_of_eq_of_mem fxy yv
    . exact fxy
  . rintro ⟨x, ⟨xs, xfv⟩, fxy⟩
    simp
    constructor
    . use x
    . have yfx : y = f x := by rw [fxy]
      have : f x ∈ v := by exact xfv
      exact mem_of_eq_of_mem yfx this

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, xfu⟩, fxy⟩
  have yfx : y = f x := by rw [fxy]
  simp
  constructor
  . use x
  . have : f x ∈ u := by exact xfu
    exact mem_of_eq_of_mem yfx this

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, xfu⟩
  simp
  constructor
  . use x
  . exact xfu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x h
  simp
  rcases h with h' | h'
  . left
    use x
  . right
    exact h'

variable {I : Type*} (A : I → Set α) (B : I → Set β)

-- To prove any of these, we recommend using ext or intro to unfold the meaning
-- of an equation or inclusion between sets, and then calling simp to unpack
-- the conditions for membership.

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  . rintro ⟨x, ⟨i, xAi⟩, fxy⟩
    use i
    use x
  . rintro ⟨i, x ,⟨xAi, fxy⟩⟩
    use x
    constructor
    . use i
    . exact fxy

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y ⟨x, x_cap_Ai, fxy⟩
  simp
  rintro i
  use x
  constructor
  . apply x_cap_Ai
    exact mem_range_self i
  . exact fxy

-- In the third exercise, the argument i : I is needed to guarantee that the
-- index set is nonempty.
example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  have : ∀ i : I, ∃ xi ∈ A i, f xi = y := by exact h
  rcases h i with ⟨xi, xiAi, fxiy⟩
  use xi
  constructor
  . intro j
    have h' : ∃ xj ∈ A j, f xj = y := by exact h j
    rcases h' with ⟨xj, xjAj, fxjy⟩
    have fxi_eq_fxj : f xi = f xj := by
      calc
        f xi = y := by rw [fxiy]
        _ = f xj := by rw [fxjy]
    have xi_eq_xj : xi = xj := by exact injf fxi_eq_fxj
    exact mem_of_eq_of_mem (injf fxi_eq_fxj) xjAj
  . exact fxiy

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp -- nice

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  -- long way
  ext x
  constructor
  . intro h
    have : f x ∈ ⋃ i, B i := by exact h
    have : ∃ i : I, f x ∈ B i := by exact mem_iUnion.mp h
    rcases this with ⟨i, fx_Bi⟩
    simp
    use i
  . intro h
    have : ∃ i : I, x ∈ f⁻¹' B i := by exact mem_iUnion.mp h
    rcases this with ⟨i, xf_cup_Bi⟩
    have : f x ∈ ⋃ i, B i := by exact mem_iUnion_of_mem i xf_cup_Bi
    exact this

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp -- too easy

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
  intro x hx y hy h
  calc
    x = (√x)^2 := by rw [sq_sqrt hx]
    _ = (√y)^2 := by rw [h]
    _ = y := by rw [sq_sqrt hy]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy h
  calc
    x = √(x ^ 2) := by rw [sqrt_sq hx]
    _ = √(y ^ 2) := by congr
    _ = y := by rw [sqrt_sq hy]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  simp
  constructor
  . intro ⟨x, xge, sqrtx_eq_y⟩
    calc
      0 ≤ √x := by exact sqrt_nonneg x
      _ = y := by exact sqrtx_eq_y
  . intro yge
    use y ^ 2
    constructor
    . exact sq_nonneg y
    . exact sqrt_sq yge

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  simp
  constructor
  . intro h
    rcases h with ⟨x, xsq_eq_y⟩
    calc
      0 ≤ x ^ 2 := by exact sq_nonneg x
      _ = y := by rw [xsq_eq_y]
  . intro yge
    use √y
    exact sq_sqrt yge
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

#print LeftInverse
#print RightInverse
#print inverse
#print inverse_spec

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro finj x
    apply finj
    apply inverse_spec
    use x
  . intro h x y fxfy
    calc
      x = inverse f (f x) := by rw [h x]
      _ = inverse f (f y) := by rw [fxfy]
      _ = y := by rw [h y]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro fsurj y
    apply inverse_spec
    apply fsurj y
  . intro h y
    have : f (inverse f y) = y := by apply h y
    use inverse f y
end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, fj_eq_S⟩
  by_cases h : j ∈ S
  -- if j ∈ S, then j ∈ S = f j, but by def S we have j ∈ S → j ∉ f j
  . have j_in_S_eq_fj : j ∈ f j := by
      simp [fj_eq_S]
      exact h
    contradiction
  -- if j ∉ S, then j ∈ S = f j, but by def S we have j ∉ S → j ∈ f j
  . have j_notin_S_eq_fj : j ∉ f j := by
      simp [fj_eq_S]
      exact h
    contradiction
end
