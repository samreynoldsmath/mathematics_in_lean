import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
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
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z)
    . apply le_inf
      . show (x ⊓ y) ⊓ z ≤ x
        apply le_trans
        apply inf_le_left
        apply inf_le_left
      . show (x ⊓ y) ⊓ z ≤ y ⊓ z
        apply le_inf
        . show (x ⊓ y) ⊓ z ≤ y
          apply le_trans
          apply inf_le_left
          apply inf_le_right
        . show (x ⊓ y) ⊓ z ≤ z
          apply inf_le_right
  . show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z
    . apply le_inf
      . show x ⊓ (y ⊓ z) ≤ x ⊓ y
        apply le_inf
        . show x ⊓ (y ⊓ z) ≤ x
          apply inf_le_left
        . show x ⊓ (y ⊓ z) ≤ y
          apply le_trans
          apply inf_le_right
          apply inf_le_left
      . show x ⊓ (y ⊓ z) ≤ z
        apply le_trans
        apply inf_le_right
        apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  . show x ⊔ y ≤ y ⊔ x
    apply sup_le
    apply le_sup_right
    apply le_sup_left
  . show y ⊔ x ≤ x ⊔ y
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  . show (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    . show x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      . show x ≤ x ⊔ (y ⊔ z)
        apply le_sup_left
      . show y ≤ x ⊔ (y ⊔ z)
        apply le_sup_of_le_right
        apply le_sup_left
    . show z ≤ x ⊔ (y ⊔ z)
      apply le_sup_of_le_right
      apply le_sup_right
  . show x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
    apply sup_le
    . show x ≤ (x ⊔ y) ⊔ z
      apply le_sup_of_le_left
      apply le_sup_left
    . show y ⊔ z ≤ (x ⊔ y) ⊔ z
      apply sup_le
      . show y ≤ (x ⊔ y) ⊔ z
        apply le_sup_of_le_left
        apply le_sup_right
      . show z ≤ (x ⊔ y) ⊔ z
        apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  . show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    . show x ≤ x
      apply le_refl
    . show x ≤ x ⊔ y
      apply le_sup_left

#check x ⊔ x ⊓ y -- very confusing implied parentheses
#check x ⊔ (x ⊓ y)

-- double check notation
example : x ⊔ x ⊓ y = x ⊔ (x ⊓ y) := by
  exact rfl

theorem absorb2 : x ⊔ x ⊓ y = x := by
  -- sanity: x ⊔ (x ⊓ y) = x
  apply le_antisymm
  . show x ⊔ (x ⊓ y) ≤ x
    apply sup_le
    . show x ≤ x
      apply le_refl
    . show x ⊓ y ≤ x
      apply inf_le_left
  . show x ≤ x ⊔ (x ⊓ y)
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  -- we have: x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)
  calc
    a ⊔ b ⊓ c = a ⊔ (b ⊓ c) := by rfl -- sanity
    _ = (a ⊔ (a ⊓ b)) ⊔ (b ⊓ c) := by rw [absorb2]
    _ = a ⊔ ((a ⊓ b) ⊔ (b ⊓ c)) := by apply sup_assoc
    _ = a ⊔ ((b ⊓ a) ⊔ (b ⊓ c)) := by rw [inf_comm a b]
    _ = a ⊔ (b ⊓ (a ⊔ c)) := by rw [h]
    _ = (a ⊓ (a ⊔ c)) ⊔ (b ⊓ (a ⊔ c)) := by rw [absorb1]
    _ = ((a ⊔ c) ⊓ a) ⊔ ((a ⊔ c) ⊓ b) := by rw [inf_comm a, inf_comm b]
    _ = (a ⊔ c) ⊓ (a ⊔ b) := by rw [h]
    _ = (a ⊔ b) ⊓ (a ⊔ c) := by apply inf_comm

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  calc
    a ⊓ (b ⊔ c) = (a ⊓ (a ⊔ c)) ⊓ (b ⊔ c) := by rw [absorb1]
    _ = a ⊓ ((a ⊔ c) ⊓ (b ⊔ c)) := by apply inf_assoc
    _ = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) := by rw [sup_comm a, sup_comm b]
    _ = a ⊓ (c ⊔ (a ⊓ b)) := by rw [h]
    _ = (a ⊔ (a ⊓ b)) ⊓ (c ⊔ (a ⊓ b)) := by rw [absorb2]
    _ = ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c) := by rw [sup_comm a, sup_comm c]
    _ = (a ⊓ b) ⊔ (a ⊓ c) := by rw [h]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

#check sub_self

example (h : a ≤ b) : 0 ≤ b - a := by
  calc
    0 = a + -a := by rw [add_neg_cancel]
    _ ≤ b + -a := by apply add_le_add_right h
    _ = b - a := by rw [sub_eq_add_neg]


example (h: 0 ≤ b - a) : a ≤ b := by
  calc
    a = 0 + a := by rw [zero_add]
    _ ≤ (b - a) + a := by apply add_le_add_right h
    _ = (b + -a) + a := by rw [sub_eq_add_neg]
    _ = b + (-a + a) := by rw [add_assoc]
    _ = b + 0 := by rw [neg_add_cancel]
    _ = b := by rw [add_zero]

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  exact mul_le_mul_of_nonneg_right h h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ 2 * dist x y := by
    calc
      0 ≤ dist x x := by rw [dist_self]
      _ ≤ dist x y + dist y x := by exact dist_triangle x y x
      _ = dist x y + dist x y := by rw [dist_comm y x]
      _ = 2 * dist x y := by rw [two_mul]
  linarith
end
