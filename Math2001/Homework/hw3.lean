/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

/-! # Homework 3 

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-3
for clearer statements and any special instructions. -/

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

namespace Int


/- 4 points -/
theorem problem1 : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by


/- 5 points -/
theorem problem2 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
 use x + 1
 extra

/- 5 points -/
theorem problem3 {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
dsimp [Odd] at *
obtain ⟨k, hk⟩ := hx
use 2 * k + 1
calc
x ^ 3 = (2 * k + 1) ^ 3 := by rw [hk]
_ = 2 * (4 * k ^ 3 + 6 k ^ 2 + 3 * k) + 1 := by ring

/- 6 points -/
theorem problem4 (n : ℤ) : Odd (5 * n ^ 2 + 3 * n + 7) := by
obtain hn | hn := Int.even_or_odd n
obtain ⟨x, hx⟩ := hn
use 10 * x ^ 2 + 3 * x + 3
 calc
5 * n ^ 2 + 3 * n + 7 = 5 * (2 * x) ^ 2 + 3 * (2 * x) + 7 by rw [hx]
_ = 2 * (10 * x ^ 2 + 3 * x + 3) + 1 := by ring
obtain ⟨x, hx⟩ := hn
use 10 * x ^ 2 + 13 * x + 7
calc
5 * n ^ 2 + 3 * n + 7 = 5 * (2 * x + 1) ^ 2 + 3 * (2 * x + 1) + 7 by rw [hx]
_ = 2 * (10 * x ^ 2 + 13 * x + 7) + 1 := by ring

/- 2 points -/
theorem problem5 : (3 : ℤ) ∣ -9 := by
dsimp [(· ∣ ·)] 
use -3
numbers

/- 3 points -/
theorem problem6 : ¬(3 : ℤ) ∣ -10 := by
apply Int.not_dvd_of_exists_lt_and_lt
use -4
constructor
numbers -- show '3 * -4 < -10'
numbers -- show '-10 < 3 * (-4 + 1)'
