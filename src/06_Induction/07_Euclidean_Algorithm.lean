/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Math2001.Library.Prime
import Math2001.Tactic.Addarith
import Math2001.Tactic.Induction
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option linter.unusedVariables false

namespace Euclid
open Int


@[decreasing] theorem lower_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : -b < fmod a b := by
  have H : 0 ≤ fmod a b 
  · apply fmod_nonneg_of_pos
    apply h1
  calc -b < 0 := by addarith [h1]
    _ ≤ _ := H

@[decreasing] theorem lower_bound_fmod2 (a b : ℤ) (h1 : b < 0) : b < fmod a (-b) := by
  have H : 0 ≤ fmod a (-b) 
  · apply fmod_nonneg_of_pos
    addarith [h1]
  have h2 : 0 < -b := by addarith [h1]
  calc b < 0 := h1
    _ ≤ fmod a (-b) := H

@[decreasing] theorem upper_bound_fmod2 (a b : ℤ) (h1 : b < 0) : fmod a (-b) < -b := by
  apply fmod_lt_of_pos
  addarith [h1]

@[decreasing] theorem upper_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : fmod a b < b := by
  apply fmod_lt_of_pos
  apply h1

def gcd (a b : ℤ) : ℤ :=
  if 0 < b then
    gcd b (fmod a b)
  else if b < 0 then
    gcd b (fmod a (-b))
  else if 0 ≤ a then
    a
  else
    -a
termination_by _ a b => b


#eval gcd (-21) 15 -- infoview displays `3`


theorem gcd_nonneg (a b : ℤ) : 0 ≤ gcd a b := by
  rw [gcd]
  split_ifs with h1 h2 ha <;> push_neg at *
  · -- case `0 < b`
    apply gcd_nonneg
  · -- case `b < 0`
    apply gcd_nonneg
  · -- case `b = 0`, `0 ≤ a`
    apply ha
  · -- case `b = 0`, `a < 0`
    addarith [ha]
termination_by _ a b => b


mutual
theorem gcd_dvd_right (a b : ℤ) : gcd a b ∣ b := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    exact gcd_dvd_left b (fmod a b)
  · -- case `b < 0`
    exact gcd_dvd_left b (fmod a (-b))
  · -- case `b = 0`, `0 ≤ a`
    have hb : b = 0 := le_antisymm h1 h2
    take 0
    calc b = 0 := hb
      _ = a * 0 := by ring
  · -- case `b = 0`, `a < 0`
    have hb : b = 0 := le_antisymm h1 h2
    take 0
    calc b = 0 := hb
      _ = -a * 0 := by ring

theorem gcd_dvd_left (a b : ℤ) : gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH1 := gcd_dvd_left b (fmod a b)
    have IH2 := gcd_dvd_right b (fmod a b)
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    take k * q + l
    calc a = r + b * q := by rw [H]
      _ = gcd b r * l + (gcd b r * k) * q := by rw [← hk, ← hl]
      _ = gcd b r * (k * q + l) := by ring
  · -- case `b < 0`
    have IH1 := gcd_dvd_left b (fmod a (-b))
    have IH2 := gcd_dvd_right b (fmod a (-b))
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H := fmod_add_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    take -k * q + l
    calc a = r + (-b) * q := by rw [H]
      _ = gcd b r * l + (- (gcd b r * k)) * q := by rw [← hk, ← hl]
      _ = gcd b r * (-k * q + l) := by ring
  · -- case `b = 0`, `0 ≤ a`
    take 1
    ring
  · -- case `b = 0`, `a < 0`
    take -1
    ring
end
termination_by gcd_dvd_right a b => b ; gcd_dvd_left a b => b

namespace bezout

mutual

def L (a b : ℤ) : ℤ :=
  if 0 < b then
    R b (fmod a b)
  else if b < 0 then
    R b (fmod a (-b)) 
  else if 0 ≤ a then 
    1
  else
    -1

def R (a b : ℤ) : ℤ :=
  if 0 < b then
    L b (fmod a b) - (fdiv a b) * R b (fmod a b)
  else if b < 0 then
    L b (fmod a (-b)) + (fdiv a (-b)) * R b (fmod a (-b))
  else
    0

end
termination_by L a b => b ; R a b => b

#eval L 24 15
#eval R 24 15

theorem L_mul_add_R_mul (a b : ℤ) : L a b * a + R a b * b = gcd a b := by
  rw [R, L, gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · have := L_mul_add_R_mul b (fmod a b)
    have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    calc R b r * a + (L b r - q * R b r) * b
        = R b r * (r + b * q) + (L b r - q * R b r) * b:= by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := this
  · have := L_mul_add_R_mul b (fmod a (-b))
    have H : fmod a (-b) + (-b) * fdiv a (-b) = a := fmod_add_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    calc  R b r * a + (L b r + q * R b r) * b 
        =  R b r * (r + -b * q) + (L b r + q * R b r) * b := by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := this
  · ring
  · ring
termination_by L_mul_add_R_mul a b => b

end bezout

open bezout

theorem bezout (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = gcd a b := by
  take L a b, R a b
  apply L_mul_add_R_mul


/-! # Exercises -/


@[decreasing] theorem Q_bound {n : ℕ} (h0 : n ≠ 0) (h2 : Nat.mod n 2 = 0) :
    Nat.div n 2 < n := by
  have H : 2 * (Nat.div n 2) + Nat.mod n 2 = n := Nat.div_add_mod n 2
  apply lt_of_mul_lt_mul_left (a := 2)
  calc 2 * Nat.div n 2 = 2 * Nat.div n 2 + 0 := by ring
    _ = 2 * Nat.div n 2 + Nat.mod n 2 := by rw [h2]
    _ = n := H
    _ < n + n := by extra
    _ = 2 * n := by ring
  numbers

def Q (n : ℕ) : ℕ :=
  if n = 0 then
    0
  else if Nat.mod n 2 = 0 then
    Q (Nat.div n 2)
  else
    n

theorem Q_div (n : ℕ) : Q n ∣ n := by
  sorry

theorem gcd_maximal {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b := by
  sorry