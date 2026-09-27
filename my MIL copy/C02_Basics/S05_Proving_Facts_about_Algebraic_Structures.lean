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
  · apply le_inf
    · apply inf_le_right
    · apply inf_le_left
  · apply le_inf
    · apply inf_le_right
    · apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · trans (x ⊓ y)
      · exact inf_le_left
      · exact inf_le_left
    apply le_inf
    · trans (x ⊓ y)
      · exact inf_le_left
      · exact inf_le_right
    · exact inf_le_right
  · apply le_inf
    · apply le_inf
      · exact inf_le_left
      · trans (y ⊓ z)
        exact inf_le_right
        exact inf_le_left
    · trans (y ⊓ z)
      · exact inf_le_right
      · exact inf_le_right


example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    · exact le_sup_right
    · exact le_sup_left
  · apply sup_le
    · exact le_sup_right
    · exact le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact le_sup_left
      · exact le_trans le_sup_left le_sup_right
    · exact le_trans le_sup_right le_sup_right
  · apply sup_le
    · exact le_trans le_sup_left le_sup_left
    · apply sup_le
      · exact le_trans le_sup_right le_sup_left
      · exact le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · exact inf_le_left
  · apply le_inf
    · apply le_refl
    · exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    · exact inf_le_left
  · exact le_sup_left

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
  apply sup_inf_assoc

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [sub_eq_add_neg]
  rw [← add_neg_cancel a]
  apply add_le_add_left
  exact h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero b]
  rw [← neg_add_cancel a, ← add_assoc]
  nth_rewrite 1 [← zero_add a]
  apply add_le_add_left
  rw [← sub_eq_add_neg]
  exact h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ 2 * dist x y := by
    trans (dist x x)
    · rw [dist_self]
    · rw [two_mul]
      nth_rewrite 3 [dist_comm]
      apply dist_triangle
  linarith


end
