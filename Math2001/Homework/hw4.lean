/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Tactic.Addarith
import Library.Tactic.Extra
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Use

/-! # Homework 4 

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-4
for clearer statements and any special instructions. -/

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
open Int


/- 4 points -/
theorem problem1 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
obtain ⟨k, hk⟩ := hab
  use b ^ 3 * k ^ 3
  calc
   a ^ 6 = (b * k) ^ 3 := by rw [hk]
    _ = b ^ 3 * k ^ 3 := by ring

/- 4 points -/
theorem problem2 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a - b + (b - c) = a - b + b - c := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

/- 4 points -/
theorem problem3 {x : ℤ} (h : x ≡ 2 [ZMOD 5]) :
    (2 * x + 3) ^ 2 ≡ (2 * 2 + 3) ^ 2 [ZMOD 5] := by
  obtain ⟨y, hy⟩ := hx
  use y * ( x + 5) * 4
  calc
    (2 * x + 3) ^ 2 - (2 * 2 + 3) ^ 2) =
        (x - 2) * ( x + 5) * 4 :=
      by ring
    _ = 2 * y * ( x + 5) * 4 := by rw [hx]
    _ = 2 * (y * ( x + 5) * 4) := by ring

/- 4 points -/
theorem problem4 {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] :=
 calc
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 3 ^ 3 + 4 * 3 ^ 2 + 2 [ZMOD 4] := by rel [ha]
    _ ≡ 27 + 4 * 9 [ZMOD 4]
    _ = 3 + 15 * 4 := by numbers
    _ ≡ 3 [ZMOD 4] := by extra


/- 4 points -/
theorem problem5 : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
 use 6
  calc
    (5:ℤ) * 6 = 6 + 3 * 8 := by numbers
    _ ≡ 6 [ZMOD 8] := by extra

/- 5 points -/
theorem problem6 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
calc
    x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 5] := by rel [hx]    
  calc
    x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 2 + 5 * 6 := by numbers
    _ ≡ 2 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 3 + 5 * 48 := by numbers
    _ ≡ 3 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 4 + 5 * 184 := by numbers
    _ ≡ 4 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel [hx]
