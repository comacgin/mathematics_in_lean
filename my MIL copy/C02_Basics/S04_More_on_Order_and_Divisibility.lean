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

example : max a b = max b a := by
  -- have h : ∀ x y : ℝ, max x y ≤ max y x := by
  --   intro x y
  --   apply max_le
  --   apply le_max_right
  --   apply le_max_left
  -- apply le_antisymm
  -- repeat apply h
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  have h1 : ∀ x y z : ℝ, min (min x y) z ≤ x := by
    intro x y z
    apply le_trans
    apply min_le_left
    apply min_le_left
  have h2 : ∀ x y z : ℝ, min (min x y) z ≤ y := by
    sorry
  have h3 : ∀ x y z : ℝ, min (min x y) z ≤ z := by
    sorry
  have h4 : ∀ x y z : ℝ, min x (min y z) ≤ x := by
    sorry
  have h5 : ∀ x y z : ℝ, min x (min y z) ≤ y := by
    sorry
  have h6 : ∀ x y z : ℝ, min x (min y z) ≤ z := by
    sorry
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    · apply le_min
      · apply h2
      · apply h3
  · apply le_min
    · apply le_min
      · apply h4
      · apply h5
    · apply h6


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · refine add_le_add_left ?_ c
    exact min_le_left a b
  · refine add_le_add_left ?_ c
    exact min_le_right a b

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_left
  rw [sub_eq_add_neg]
  nth_rewrite 2 [← add_neg_cancel_right a c, ← add_neg_cancel_right b c]
  apply aux

#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check (sub_add_cancel : ∀ a b : ℝ, a - b + b = a)

example : |a| - |b| ≤ |a - b| := by
  have h : |a| ≤ |a - b| + |b| := by
    nth_rewrite 1 [← sub_add_cancel a b]
    apply abs_add_le
  linarith

example : |a| - |b| ≤ |a - b| := by
  rw [sub_le_iff_le_add]
  nth_rewrite 1 [ ← sub_add_cancel a b]
  apply abs_add_le

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

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · rw [← mul_assoc]
      apply dvd_mul_of_dvd_left
      apply dvd_mul_left
    · apply dvd_mul_left
  · apply dvd_mul_of_dvd_right
    exact h

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply gcd_comm


example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  · apply dvd_gcd
    · apply gcd_dvd_right
    · apply gcd_dvd_left
  · apply dvd_gcd
    · apply gcd_dvd_right
    · apply gcd_dvd_left

end
