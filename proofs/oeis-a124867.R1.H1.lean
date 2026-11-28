import OMAReductions.R_oeis_a124867_R1

import Mathlib

namespace DistinctPrimeTriples

private def witnesses : ℕ → List (ℕ × ℕ)
  | 0 => [(2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3)]
  | 1 => [(3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 19), (2, 3), (3, 5)]
  | 2 => [(2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7)]
  | 3 => [(3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5)]
  | 4 => [(2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 11), (3, 11), (2, 13), (3, 13), (2, 19), (3, 19), (2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3)]
  | 5 => [(3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7)]
  | 6 => [(2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 19), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 11)]
  | 7 => [(3, 11), (2, 11), (3, 11), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 13), (3, 13), (2, 3), (3, 17)]
  | 8 => [(2, 5), (3, 5), (2, 7), (3, 7), (2, 23), (3, 23), (2, 11), (3, 11), (2, 13), (3, 13), (2, 3), (3, 29), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7)]
  | 9 => [(3, 7), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 19), (2, 5), (3, 5), (2, 7), (3, 7)]
  | 10 => [(2, 3), (3, 37), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 31), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7)]
  | 11 => [(3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 11), (3, 11), (2, 13), (3, 13), (2, 31), (3, 31), (2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7)]
  | 12 => [(2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 11), (3, 11), (2, 13), (3, 13), (2, 19), (3, 19), (2, 3), (3, 17), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3)]
  | 13 => [(3, 23), (2, 5), (3, 5), (2, 7), (3, 7), (2, 29), (3, 29), (2, 11), (3, 11), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5)]
  | 14 => [(2, 7), (3, 7), (2, 19), (3, 19), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 17), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 23), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7)]
  | 15 => [(3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 3), (3, 11), (2, 5), (3, 5)]
  | 16 => [(2, 7), (3, 7), (2, 17), (3, 17), (2, 11), (3, 11), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7)]
  | 17 => [(3, 7), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7)]
  | 18 => [(2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 11), (3, 11), (2, 13), (3, 13), (2, 3), (3, 19), (2, 5), (3, 5), (2, 7), (3, 7), (2, 31), (3, 31), (2, 3)]
  | 19 => [(3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5)]
  | 20 => [(2, 7), (3, 7), (2, 19), (3, 19), (2, 11), (3, 11), (2, 13), (3, 13), (2, 3), (3, 37), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 13), (3, 13), (2, 17), (3, 17), (2, 17)]
  | 21 => [(3, 17), (2, 19), (3, 19), (2, 3), (3, 23), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 29), (2, 5), (3, 5), (2, 7), (3, 7), (2, 47), (3, 47), (2, 11), (3, 11), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7)]
  | 22 => [(2, 3), (3, 19), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 31), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7), (2, 17), (3, 17), (2, 11), (3, 11), (2, 3)]
  | 23 => [(3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 19), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 31), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7)]
  | 24 => [(2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 13), (3, 13), (2, 3), (3, 17), (2, 5), (3, 5), (2, 7), (3, 7), (2, 23)]
  | 25 => [(3, 23), (2, 11), (3, 11), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 19), (2, 3), (3, 5)]
  | 26 => [(2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 13), (3, 13), (2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7)]
  | 27 => [(3, 7), (2, 19), (3, 19), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7), (2, 17), (3, 17), (2, 11), (3, 11), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 3), (3, 11), (2, 5), (3, 5)]
  | 28 => [(2, 7), (3, 7), (2, 17), (3, 17), (2, 11), (3, 11), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 17), (2, 5), (3, 5), (2, 7)]
  | 29 => [(3, 7), (2, 3), (3, 23), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7)]
  | 30 => [(2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 3), (3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 11), (3, 11), (2, 13), (3, 13), (2, 19), (3, 19), (2, 3)]
  | 31 => [(3, 17), (2, 5), (3, 5), (2, 7), (3, 7), (2, 23), (3, 23), (2, 11), (3, 11), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 11), (3, 11), (2, 13), (3, 13), (2, 3), (3, 43), (2, 3), (3, 5)]
  | 32 => [(2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11), (3, 11), (2, 3), (3, 13), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 7), (3, 7), (2, 11), (3, 11), (2, 11)]
  | 33 => [(3, 11), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 11), (3, 11), (2, 13), (3, 13), (2, 31), (3, 31), (2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5)]
  | 34 => [(2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 11), (3, 11), (2, 13), (3, 13), (2, 19), (3, 19), (2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7), (2, 3), (3, 5), (2, 5), (3, 5), (2, 3)]
  | 35 => [(3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 11), (3, 11), (2, 13), (3, 13), (2, 19), (3, 19), (2, 17), (3, 17), (2, 19), (3, 19), (2, 31), (3, 31), (2, 3), (3, 23), (2, 5), (3, 5), (2, 3), (3, 7)]
  | 36 => [(2, 5), (3, 5), (2, 7), (3, 7), (2, 13), (3, 13), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7), (2, 17), (3, 17), (2, 11), (3, 11), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 19), (3, 19), (2, 3)]
  | 37 => [(3, 11), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 19), (2, 5), (3, 5), (2, 7), (3, 7), (2, 43), (3, 43), (2, 11), (3, 11)]
  | 38 => [(2, 13), (3, 13), (2, 31), (3, 31), (2, 3), (3, 17), (2, 5), (3, 5), (2, 3), (3, 7), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 13), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 19), (2, 5), (3, 5), (2, 7)]
  | 39 => [(3, 7), (2, 73), (3, 73), (2, 3), (3, 11), (2, 5), (3, 5), (2, 7), (3, 7), (2, 3), (3, 17), (2, 5), (3, 5), (2, 7), (3, 7), (2, 23), (3, 23), (2, 11), (3, 11), (2, 13), (3, 13), (2, 3), (3, 29), (2, 5), (3, 5)]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ × ℕ := (witnesses i).getD j.val (0, 0)

private def smallPrimeProduct : ℕ := 31610054640417607788145206291543662493274686990

private theorem product_eq : primorial 113 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 113 then n.Prime else n ≤ 12012 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 113
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 12012 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 113 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 114 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ fac.dvd_primorial_iff.mpr small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let p := (witness i j).1
  let q := (witness i j).2
  let n := 25 * i + j.val + 18
  let r := n - p - q
  Certified p ∧ Certified q ∧ Certified r ∧ p < q ∧ q < r ∧ p + q + r = n

private instance (i : ℕ) (j : Fin 25) : Decidable (Valid i j) := by
  unfold Valid
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked0 : ∀ j : Fin 25, Valid 0 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked1 : ∀ j : Fin 25, Valid 1 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked2 : ∀ j : Fin 25, Valid 2 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked3 : ∀ j : Fin 25, Valid 3 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked4 : ∀ j : Fin 25, Valid 4 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked5 : ∀ j : Fin 25, Valid 5 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked6 : ∀ j : Fin 25, Valid 6 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked7 : ∀ j : Fin 25, Valid 7 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked8 : ∀ j : Fin 25, Valid 8 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked9 : ∀ j : Fin 25, Valid 9 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked10 : ∀ j : Fin 25, Valid 10 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked11 : ∀ j : Fin 25, Valid 11 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked12 : ∀ j : Fin 25, Valid 12 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked13 : ∀ j : Fin 25, Valid 13 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked14 : ∀ j : Fin 25, Valid 14 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked15 : ∀ j : Fin 25, Valid 15 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked16 : ∀ j : Fin 25, Valid 16 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked17 : ∀ j : Fin 25, Valid 17 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked18 : ∀ j : Fin 25, Valid 18 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked19 : ∀ j : Fin 25, Valid 19 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked20 : ∀ j : Fin 25, Valid 20 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked21 : ∀ j : Fin 25, Valid 21 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked22 : ∀ j : Fin 25, Valid 22 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked23 : ∀ j : Fin 25, Valid 23 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked24 : ∀ j : Fin 25, Valid 24 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked25 : ∀ j : Fin 25, Valid 25 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked26 : ∀ j : Fin 25, Valid 26 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked27 : ∀ j : Fin 25, Valid 27 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked28 : ∀ j : Fin 25, Valid 28 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked29 : ∀ j : Fin 25, Valid 29 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked30 : ∀ j : Fin 25, Valid 30 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked31 : ∀ j : Fin 25, Valid 31 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked32 : ∀ j : Fin 25, Valid 32 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked33 : ∀ j : Fin 25, Valid 33 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked34 : ∀ j : Fin 25, Valid 34 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked35 : ∀ j : Fin 25, Valid 35 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked36 : ∀ j : Fin 25, Valid 36 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked37 : ∀ j : Fin 25, Valid 37 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked38 : ∀ j : Fin 25, Valid 38 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked39 : ∀ j : Fin 25, Valid 39 j := by decide +kernel

private theorem checked (i : ℕ) (hi : i < 40) (j : Fin 25) : Valid i j := by
  interval_cases i
  · exact checked0 j
  · exact checked1 j
  · exact checked2 j
  · exact checked3 j
  · exact checked4 j
  · exact checked5 j
  · exact checked6 j
  · exact checked7 j
  · exact checked8 j
  · exact checked9 j
  · exact checked10 j
  · exact checked11 j
  · exact checked12 j
  · exact checked13 j
  · exact checked14 j
  · exact checked15 j
  · exact checked16 j
  · exact checked17 j
  · exact checked18 j
  · exact checked19 j
  · exact checked20 j
  · exact checked21 j
  · exact checked22 j
  · exact checked23 j
  · exact checked24 j
  · exact checked25 j
  · exact checked26 j
  · exact checked27 j
  · exact checked28 j
  · exact checked29 j
  · exact checked30 j
  · exact checked31 j
  · exact checked32 j
  · exact checked33 j
  · exact checked34 j
  · exact checked35 j
  · exact checked36 j
  · exact checked37 j
  · exact checked38 j
  · exact checked39 j

theorem result : OMA.R_oeis_a124867_R1.H1 := by
  intro n hlo hhi
  let i := (n - 18) / 25
  let j : Fin 25 := ⟨(n - 18) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 18 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hp, hq, hr, hpq, hqr, hsum⟩ := h
  exact ⟨(witness i j).1, (witness i j).2, n - (witness i j).1 - (witness i j).2,
    primeOfCertified hp, primeOfCertified hq, primeOfCertified hr, hpq, hqr, hsum⟩

end DistinctPrimeTriples

theorem OMA.solution : OMA.R_oeis_a124867_R1.H1 :=
  DistinctPrimeTriples.result