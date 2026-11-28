import OMAReductions.R_oeis_a020483_R1

import Mathlib

namespace EvenPrimeDifferences

private def witnesses : ℕ → List ℕ
  | 0 => [2, 3, 3, 5, 3, 3, 5, 3, 3, 5, 3, 7, 5, 3, 3, 7, 5, 3, 5, 3, 3, 5, 3, 7, 5]
  | 1 => [3, 7, 5, 3, 3, 7, 5, 3, 5, 3, 3, 7, 5, 3, 5, 3, 7, 5, 3, 13, 7, 5, 3, 5, 3]
  | 2 => [3, 5, 3, 3, 5, 3, 19, 13, 11, 13, 7, 5, 3, 5, 3, 7, 5, 3, 3, 11, 11, 7, 5, 3, 3]
  | 3 => [7, 5, 3, 7, 5, 3, 5, 3, 7, 5, 3, 7, 5, 3, 3, 11, 11, 7, 5, 3, 3, 5, 3, 3, 13]
  | 4 => [11, 31, 7, 5, 3, 13, 11, 13, 7, 5, 3, 5, 3, 3, 5, 3, 7, 5, 3, 3, 11, 29, 7, 5, 3]
  | 5 => [7, 5, 3, 7, 5, 3, 7, 5, 3, 3, 7, 5, 3, 5, 3, 3, 11, 23, 7, 5, 3, 19, 13, 11, 13]
  | 6 => [7, 5, 3, 5, 3, 3, 5, 3, 31, 13, 11, 31, 7, 5, 3, 7, 5, 3, 11, 11, 7, 5, 3, 3, 5]
  | 7 => [3, 7, 5, 3, 31, 7, 5, 3, 7, 5, 3, 7, 5, 3, 5, 3, 7, 5, 3, 13, 7, 5, 3, 5, 3]
  | 8 => [19, 7, 5, 3, 11, 11, 7, 5, 3, 3, 11, 11, 7, 5, 3, 3, 7, 5, 3, 5, 3, 7, 5, 3, 13]
  | 9 => [7, 5, 3, 5, 3, 3, 5, 3, 13, 11, 17, 7, 5, 3, 13, 7, 5, 3, 5, 3, 13, 7, 5, 3, 5]
  | 10 => [3, 7, 5, 3, 13, 11, 11, 7, 5, 3, 3, 19, 17, 31, 13, 11, 31, 7, 5, 3, 7, 5, 3, 11, 23]
  | 11 => [7, 5, 3, 7, 5, 3, 7, 5, 3, 3, 7, 5, 3, 11, 23, 7, 5, 3, 7, 5, 3, 7, 5, 3, 3]
  | 12 => [7, 5, 3, 7, 5, 3, 5, 3, 3, 13, 11, 19, 7, 5, 3, 11, 11, 7, 5, 3, 3, 5, 3, 7, 5]
  | 13 => [3, 7, 5, 3, 3, 13, 11, 13, 7, 5, 3, 5, 3, 7, 5, 3, 19, 7, 5, 3, 11, 17, 7, 5, 3]
  | 14 => [19, 7, 5, 3, 11, 17, 7, 5, 3, 43, 7, 5, 3, 7, 5, 3, 7, 5, 3, 5, 3, 19, 7, 5, 3]
  | 15 => [7, 5, 3, 5, 3, 13, 7, 5, 3, 5, 3, 37, 13, 11, 19, 7, 5, 3, 11, 23, 7, 5, 3, 13, 11]
  | 16 => [11, 7, 5, 3, 3, 11, 11, 7, 5, 3, 3, 5, 3, 3, 11, 23, 7, 5, 3, 19, 13, 11, 13, 7, 5]
  | 17 => [3, 5, 3, 3, 5, 3, 19, 13, 11, 13, 7, 5, 3, 5, 3, 3, 5, 3, 43, 19, 17, 19, 13, 11, 13]
  | 18 => [7, 5, 3, 5, 3, 19, 7, 5, 3, 11, 17, 7, 5, 3, 13, 7, 5, 3, 5, 3, 7, 5, 3, 7, 5]
  | 19 => [3, 19, 13, 11, 13, 7, 5, 3, 5, 3, 7, 5, 3, 7, 5, 3, 31, 7, 5, 3, 7, 5, 3, 13, 11]
  | 20 => [13, 7, 5, 3, 5, 3, 7, 5, 3, 3, 11, 11, 7, 5, 3, 3, 7, 5, 3, 11, 11, 7, 5, 3, 3]
  | 21 => [11, 11, 7, 5, 3, 3, 7, 5, 3, 19, 17, 19, 13, 11, 13, 7, 5, 3, 5, 3, 3, 5, 3, 7, 5]
  | 22 => [3, 7, 5, 3, 43, 7, 5, 3, 7, 5, 3, 7, 5, 3, 23, 23, 19, 17, 17, 13, 11, 11, 7, 5, 3]
  | 23 => [3, 11, 17, 7, 5, 3, 19, 7, 5, 3, 11, 29, 7, 5, 3, 7, 5, 3, 7, 5, 3, 31, 7, 5, 3]
  | 24 => [13, 11, 13, 7, 5, 3, 5, 3, 7, 5, 3, 7, 5, 3, 3, 7, 5, 3, 13, 11, 19, 7, 5, 3, 11]
  | 25 => [29, 7, 5, 3, 19, 17, 17, 13, 11, 11, 7, 5, 3, 3, 5, 3, 7, 5, 3, 3, 7, 5, 3, 5, 3]
  | 26 => [3, 5, 3, 13, 11, 11, 7, 5, 3, 3, 7, 5, 3, 41, 53, 31, 29, 47, 31, 23, 41, 19, 17, 53, 13]
  | 27 => [11, 29, 7, 5, 3, 7, 5, 3, 7, 5, 3, 37, 7, 5, 3, 19, 17, 43, 13, 11, 19, 7, 5, 3, 11]
  | 28 => [23, 7, 5, 3, 19, 13, 11, 13, 7, 5, 3, 5, 3, 3, 5, 3, 7, 5, 3, 13, 7, 5, 3, 5, 3]
  | 29 => [3, 7, 5, 3, 13, 11, 19, 7, 5, 3, 11, 11, 7, 5, 3, 3, 5, 3, 3, 5, 3, 7, 5, 3, 13]
  | 30 => [11, 29, 7, 5, 3, 13, 11, 17, 7, 5, 3, 31, 7, 5, 3, 13, 11, 19, 7, 5, 3, 7, 5, 3, 5]
  | 31 => [3, 7, 5, 3, 13, 7, 5, 3, 5, 3, 13, 7, 5, 3, 5, 3, 19, 13, 11, 13, 7, 5, 3, 5, 3]
  | 32 => [7, 5, 3, 3, 5, 3, 7, 5, 3, 3, 7, 5, 3, 11, 29, 7, 5, 3, 31, 19, 17, 67, 13, 11, 19]
  | 33 => [7, 5, 3, 7, 5, 3, 5, 3, 3, 29, 23, 37, 19, 17, 19, 13, 11, 13, 7, 5, 3, 5, 3, 3, 11]
  | 34 => [23, 7, 5, 3, 13, 11, 11, 7, 5, 3, 3, 11, 17, 7, 5, 3, 79, 7, 5, 3, 7, 5, 3, 7, 5]
  | 35 => [3, 7, 5, 3, 19, 17, 61, 13, 11, 19, 7, 5, 3, 7, 5, 3, 5, 3, 3, 13, 11, 19, 7, 5, 3]
  | 36 => [11, 29, 7, 5, 3, 13, 11, 17, 7, 5, 3, 67, 7, 5, 3, 17, 29, 13, 11, 23, 7, 5, 3, 31, 13]
  | 37 => [11, 19, 7, 5, 3, 7, 5, 3, 5, 3, 3, 5, 3, 3, 11, 53, 7, 5, 3, 13, 11, 41, 7, 5, 3]
  | 38 => [7, 5, 3, 7, 5, 3, 19, 17, 17, 13, 11, 11, 7, 5, 3, 3, 17, 17, 13, 11, 11, 7, 5, 3, 3]
  | 39 => [23, 41, 19, 17, 29, 13, 11, 23, 7, 5, 3, 7, 5, 3, 19, 7, 5, 3, 7, 5, 3, 5, 3, 3, 5]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

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
  let p := witness i j
  let n := 25 * i + j.val + 0
  Certified p ∧ Certified (p + 2 * n)

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

theorem result : OMA.R_oeis_a020483_R1.H1 := by
  intro n hhi
  let i := (n - 0) / 25
  let j : Fin 25 := ⟨(n - 0) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 0 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hp, hq⟩ := h
  exact ⟨witness i j, primeOfCertified hp, primeOfCertified hq⟩

end EvenPrimeDifferences

theorem OMA.solution : OMA.R_oeis_a020483_R1.H1 :=
  EvenPrimeDifferences.result