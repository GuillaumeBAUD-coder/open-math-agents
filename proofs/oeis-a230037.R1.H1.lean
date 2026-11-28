import OMAReductions.R_oeis_a230037_R1
import Mathlib

namespace TwinPrimeTriples

private def witnesses : ℕ → List (ℕ × ℕ)
  | 0 => [(1,1), (1,1), (1,1), (1,2), (1,1), (1,2), (1,1), (1,2), (1,3), (1,1), (1,2), (1,1), (1,2), (1,3), (2,5), (1,5), (1,1), (1,1), (1,2), (1,3), (1,5), (1,5), (1,1), (1,2), (1,1)]
  | 1 => [(1,2), (1,3), (1,12), (1,5), (1,1), (1,2), (1,1), (1,1), (1,2), (1,3), (1,5), (1,5), (1,1), (1,2), (1,1), (1,2), (1,3), (1,12), (1,5), (1,1), (1,2), (1,1), (1,2), (1,3), (1,18)]
  | 2 => [(1,5), (1,1), (1,2), (1,3), (1,18), (1,5), (1,18), (1,1), (1,2), (1,3), (1,10), (1,5), (1,12), (1,7), (1,33), (5,5), (1,10), (1,17), (1,12), (1,1), (1,2), (1,1), (1,2), (1,3), (1,18)]
  | 3 => [(1,5), (1,1), (1,2), (1,3), (1,23), (1,5), (1,25), (1,7), (1,33), (5,5), (1,10), (1,1), (1,2), (1,3), (1,33), (1,5), (1,23), (1,7), (1,18), (1,1), (1,2), (1,3), (1,12), (1,5), (1,1)]
  | 4 => [(1,2), (1,3), (1,1), (1,2), (1,3), (1,7), (1,1), (1,2), (1,3), (1,1), (1,2), (1,3), (1,7), (1,5), (1,58), (1,7), (1,18), (1,12), (1,10), (1,18), (1,12), (1,23), (1,17), (1,18), (1,23)]
  | 5 => [(1,17), (1,18), (1,52), (1,23), (7,25), (1,25), (1,23), (1,47), (1,25), (1,1), (1,2), (1,1), (1,1), (1,2), (1,3), (1,5), (1,5), (1,1), (1,2), (1,3), (1,10), (1,1), (1,2), (1,3), (7,10)]
  | 6 => [(1,5), (1,10), (1,7), (1,12), (1,18), (1,10), (1,23), (1,12), (1,17), (1,18), (1,25), (1,25), (1,17), (1,18), (1,23), (1,30), (1,25), (1,32), (1,23), (1,1), (1,2), (1,1), (1,2), (1,3), (1,1)]
  | 7 => [(1,2), (1,1), (1,2), (1,3), (1,38), (1,5), (1,1), (1,2), (1,3), (5,5), (1,5), (1,18), (1,7), (1,18), (5,5), (1,10), (1,1), (1,2), (1,3), (1,58), (1,5), (1,23), (1,7), (1,18), (1,58)]
  | 8 => [(1,10), (1,33), (1,12), (1,23), (1,1), (1,2), (1,3), (1,17), (1,5), (2,5), (1,7), (1,38), (1,1), (1,2), (1,1), (1,2), (1,1), (1,2), (1,3), (1,1), (1,2), (1,3), (1,7), (1,5), (2,5)]
  | 9 => [(1,7), (1,23), (1,12), (1,10), (1,18), (1,12), (1,18), (1,17), (1,18), (1,23), (1,17), (1,18), (1,1), (1,2), (1,3), (1,25), (1,1), (1,2), (1,3), (1,33), (1,5), (1,1), (1,1), (1,2), (1,3)]
  | 10 => [(1,5), (1,5), (1,7), (1,7), (1,18), (1,10), (1,10), (1,12), (1,12), (1,23), (1,45), (1,25), (1,17), (1,17), (1,18), (1,25), (1,30), (1,1), (1,2), (1,1), (1,2), (1,3), (1,32), (1,5), (1,38)]
  | 11 => [(1,7), (1,10), (1,1), (1,2), (1,3), (1,12), (1,5), (1,1), (1,2), (1,3), (1,17), (1,1), (1,2), (1,3), (1,23), (1,5), (1,10), (1,7), (1,12), (1,18), (1,10), (1,30), (1,1), (1,2), (1,3)]
  | 12 => [(1,32), (1,5), (1,17), (1,7), (1,23), (1,87), (1,10), (1,137), (1,12), (1,33), (1,25), (1,1), (1,1), (1,2), (1,3), (1,5), (1,5), (1,7), (1,7), (1,23), (1,10), (1,1), (1,2), (1,3), (1,1)]
  | 13 => [(1,2), (1,3), (1,7), (1,5), (1,18), (1,7), (1,95), (1,1), (1,2), (1,3), (1,12), (1,5), (1,1), (1,2), (1,3), (1,17), (1,5), (1,32), (1,7), (1,33), (1,25), (1,1), (1,1), (1,2), (1,3)]
  | 14 => [(1,5), (1,1), (1,2), (1,3), (1,1), (1,2), (1,1), (1,2), (1,3), (1,23), (1,5), (1,25), (1,7), (1,10), (1,18), (1,10), (1,30), (1,12), (1,18), (1,23), (1,17), (1,18), (1,1), (1,2), (1,3)]
  | 15 => [(1,25), (1,5), (1,1), (1,2), (1,3), (1,25), (1,5), (1,32), (1,7), (1,1), (1,2), (1,3), (1,32), (1,5), (1,1), (1,2), (1,3), (1,47), (1,5), (1,18), (1,7), (1,1), (1,2), (1,3), (1,23)]
  | 16 => [(1,5), (1,18), (1,7), (1,32), (1,33), (1,10), (1,18), (1,12), (1,25), (1,33), (1,87), (1,23), (1,17), (1,18), (1,38), (1,32), (1,33), (1,72), (1,23), (1,138), (1,25), (1,33), (1,72), (1,40), (1,1)]
  | 17 => [(1,2), (1,3), (1,32), (1,5), (1,58), (1,7), (1,1), (1,2), (1,3), (1,58), (1,5), (1,100), (1,7), (1,107), (1,103), (1,10), (1,18), (1,1), (1,2), (1,3), (1,95), (1,5), (1,1), (1,2), (1,3)]
  | 18 => [(1,95), (1,1), (1,2), (1,3), (1,1), (1,2), (1,3), (1,7), (1,5), (1,18), (1,7), (1,38), (1,12), (1,10), (1,1), (1,2), (1,1), (1,2), (1,3), (1,23), (1,5), (1,18), (1,7), (1,10), (1,33)]
  | 19 => [(1,10), (1,23), (1,12), (1,25), (1,33), (1,17), (1,18), (1,17), (1,18), (1,38), (1,32), (1,23), (1,137), (1,23), (1,143), (1,25), (1,38), (1,137), (1,30), (1,1), (1,2), (1,3), (1,32), (1,5), (1,1)]
  | 20 => [(1,2), (1,3), (1,52), (1,5), (1,58), (1,7), (1,135), (1,77), (1,10), (1,138), (1,12), (1,18), (1,47), (1,72), (1,138), (1,17), (1,18), (1,52), (1,25), (1,1), (1,2), (1,3), (1,72), (1,5), (1,213)]
  | 21 => [(1,7), (1,33), (1,1), (1,2), (1,3), (1,12), (1,5), (1,137), (1,7), (1,238), (1,17), (1,10), (1,72), (1,12), (5,215), (1,47), (1,1), (1,1), (1,2), (1,3), (1,5), (1,5), (1,7), (1,7), (1,1)]
  | 22 => [(1,2), (1,3), (1,12), (1,5), (1,1), (1,2), (1,3), (1,17), (1,5), (1,1), (1,2), (1,1), (1,2), (1,3), (1,1), (1,2), (1,3), (1,7), (1,5), (1,238), (1,7), (1,18), (1,12), (1,10), (1,33)]
  | 23 => [(1,12), (1,1), (1,1), (1,2), (1,3), (1,5), (1,5), (1,7), (1,7), (1,58), (1,10), (1,10), (1,1), (1,2), (1,1), (1,2), (1,3), (1,1), (1,2), (1,3), (1,7), (1,1), (1,2), (1,3), (1,23)]
  | 24 => [(1,5), (1,10), (1,7), (1,12), (1,18), (1,10), (1,18), (1,12), (1,17), (1,18), (1,47), (1,1), (1,2), (1,3), (1,23), (1,5), (1,25), (1,7), (1,23), (1,33), (1,10), (1,30), (1,12), (1,32), (1,33)]
  | 25 => [(1,30), (1,38), (1,1), (1,2), (1,3), (1,70), (1,5), (1,72), (1,7), (1,58), (1,25), (1,1), (1,2), (1,3), (1,268), (1,5), (1,1), (1,2), (1,3), (1,18), (1,5), (1,58), (1,7), (1,38), (1,23)]
  | 26 => [(1,10), (1,25), (1,1), (1,2), (1,1), (1,2), (1,3), (1,17), (1,5), (1,33), (1,7), (1,10), (1,52), (1,10), (1,38), (1,12), (1,1), (1,2), (1,3), (1,1), (1,2), (1,3), (1,7), (1,5), (1,1)]
  | 27 => [(1,2), (1,3), (1,12), (1,5), (1,103), (1,7), (1,1), (1,2), (1,3), (1,33), (1,5), (1,18), (1,1), (1,2), (1,3), (1,10), (1,5), (1,1), (1,2), (1,3), (1,30), (1,5), (1,17), (1,7), (2,110)]
  | 28 => [(1,32), (1,10), (1,1), (1,2), (1,1), (1,2), (1,1), (1,2), (1,3), (1,1), (1,2), (1,1), (1,2), (1,3), (1,23), (1,5), (1,25), (1,7), (1,10), (1,18), (1,10), (1,18), (1,1), (1,2), (1,3)]
  | 29 => [(1,17), (1,5), (1,17), (1,7), (1,38), (1,25), (1,10), (1,52), (1,12), (1,33), (1,25), (1,1), (1,2), (1,3), (1,18), (1,5), (1,33), (1,7), (1,33), (1,23), (1,10), (1,1), (1,2), (1,3), (1,58)]
  | 30 => [(1,5), (1,30), (1,1), (1,2), (1,3), (1,10), (1,5), (1,1), (1,2), (1,3), (1,25), (1,5), (1,17), (1,7), (1,138), (1,30), (1,10), (1,32), (1,12), (1,18), (1,25), (1,70), (1,1), (1,2), (1,1)]
  | 31 => [(1,2), (1,3), (1,32), (1,5), (1,23), (1,7), (1,10), (1,47), (1,10), (1,33), (1,12), (1,1), (1,2), (1,3), (1,18), (1,5), (1,18), (1,7), (1,58), (1,23), (1,10), (1,23), (1,1), (1,2), (1,1)]
  | 32 => [(1,2), (1,3), (1,17), (1,5), (1,33), (1,7), (1,10), (1,72), (1,10), (1,38), (1,12), (1,38), (1,77), (1,17), (1,18), (1,17), (1,18), (1,32), (1,33), (1,23), (1,47), (1,1), (1,2), (1,3), (1,103)]
  | 33 => [(1,5), (1,30), (1,1), (1,2), (1,3), (1,10), (1,5), (1,12), (1,7), (1,1), (1,2), (1,1), (1,2), (1,3), (1,138), (1,5), (1,45), (1,7), (1,10), (1,18), (1,10), (1,95), (1,12), (1,52), (1,1)]
  | 34 => [(1,2), (1,3), (1,17), (1,5), (1,58), (1,7), (1,23), (1,72), (1,10), (1,33), (1,12), (1,110), (1,77), (1,30), (1,38), (1,17), (1,18), (1,32), (1,33), (1,278), (1,72), (1,1), (1,2), (1,3), (1,103)]
  | 35 => [(1,5), (1,103), (1,7), (1,30), (1,1), (1,2), (1,3), (1,12), (1,5), (1,58), (1,7), (1,38), (1,17), (1,10), (1,138), (1,12), (1,58), (1,72), (1,23), (1,138), (1,17), (1,18), (1,77), (1,72), (1,103)]
  | 36 => [(1,30), (1,23), (1,1), (1,2), (1,3), (1,70), (1,1), (1,2), (1,3), (1,138), (1,5), (1,10), (1,1), (1,2), (1,3), (1,10), (1,1), (1,2), (1,3), (1,1), (1,2), (1,3), (1,7), (1,5), (1,23)]
  | 37 => [(1,7), (1,25), (1,12), (1,10), (1,18), (1,12), (1,30), (1,17), (1,18), (1,23), (1,17), (1,18), (1,32), (1,23), (1,1), (1,2), (1,1), (1,1), (1,2), (1,3), (1,5), (1,5), (1,7), (1,7), (1,38)]
  | 38 => [(1,10), (1,10), (1,12), (1,12), (1,268), (1,17), (1,1), (1,2), (1,3), (1,18), (1,5), (1,23), (1,7), (1,23), (1,23), (1,10), (1,25), (1,12), (1,30), (1,58), (1,30), (1,30), (1,17), (1,18), (1,1)]
  | 39 => [(1,2), (1,3), (1,1), (1,2), (1,1), (1,2), (1,3), (1,77), (1,5), (1,213), (1,7), (1,10), (1,32), (1,10), (1,238), (1,12), (1,18), (1,52), (1,17), (1,18), (1,17), (1,18), (1,177), (1,25), (1,23)]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ × ℕ := (witnesses i).getD j.val (0,0)

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
  let n := 25 * i + j.val + 3
  let x := (witness i j).1
  let y := (witness i j).2
  let z := n - x - y
  0 < x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
    Certified (6*x-1) ∧ Certified (6*x+1) ∧ Certified (6*y-1) ∧ Certified (6*y+1) ∧
    Certified (6*z-1) ∧ Certified (6*z+1) ∧ Certified (6*x*y-1) ∧ Certified (6*x*y+1)

private instance (i : ℕ) (j : Fin 25) : Decidable (Valid i j) := by
  unfold Valid
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked0 : ∀ j : Fin 25, Valid 0 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked1 : ∀ j : Fin 25, Valid 1 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked2 : ∀ j : Fin 25, Valid 2 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked3 : ∀ j : Fin 25, Valid 3 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked4 : ∀ j : Fin 25, Valid 4 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked5 : ∀ j : Fin 25, Valid 5 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked6 : ∀ j : Fin 25, Valid 6 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked7 : ∀ j : Fin 25, Valid 7 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked8 : ∀ j : Fin 25, Valid 8 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked9 : ∀ j : Fin 25, Valid 9 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked10 : ∀ j : Fin 25, Valid 10 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked11 : ∀ j : Fin 25, Valid 11 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked12 : ∀ j : Fin 25, Valid 12 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked13 : ∀ j : Fin 25, Valid 13 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked14 : ∀ j : Fin 25, Valid 14 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked15 : ∀ j : Fin 25, Valid 15 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked16 : ∀ j : Fin 25, Valid 16 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked17 : ∀ j : Fin 25, Valid 17 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked18 : ∀ j : Fin 25, Valid 18 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked19 : ∀ j : Fin 25, Valid 19 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked20 : ∀ j : Fin 25, Valid 20 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked21 : ∀ j : Fin 25, Valid 21 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked22 : ∀ j : Fin 25, Valid 22 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked23 : ∀ j : Fin 25, Valid 23 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked24 : ∀ j : Fin 25, Valid 24 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked25 : ∀ j : Fin 25, Valid 25 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked26 : ∀ j : Fin 25, Valid 26 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked27 : ∀ j : Fin 25, Valid 27 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked28 : ∀ j : Fin 25, Valid 28 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked29 : ∀ j : Fin 25, Valid 29 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked30 : ∀ j : Fin 25, Valid 30 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked31 : ∀ j : Fin 25, Valid 31 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked32 : ∀ j : Fin 25, Valid 32 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked33 : ∀ j : Fin 25, Valid 33 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked34 : ∀ j : Fin 25, Valid 34 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked35 : ∀ j : Fin 25, Valid 35 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked36 : ∀ j : Fin 25, Valid 36 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked37 : ∀ j : Fin 25, Valid 37 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem checked38 : ∀ j : Fin 25, Valid 38 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
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

end TwinPrimeTriples

open TwinPrimeTriples

theorem OMA.solution : OMA.R_oeis_a230037_R1.H1 := by
  intro n hlo hhi
  let i := (n - 3) / 25
  let j : Fin 25 := ⟨(n - 3) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 3 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hx, hxy, hyz, hsum, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨(witness i j).1, (witness i j).2, n - (witness i j).1 - (witness i j).2,
    hx, hxy, hyz, hsum, primeOfCertified h1, primeOfCertified h2,
    primeOfCertified h3, primeOfCertified h4, primeOfCertified h5, primeOfCertified h6,
    primeOfCertified h7, primeOfCertified h8⟩