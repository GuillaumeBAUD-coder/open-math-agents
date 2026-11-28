import OMAReductions.R_oeis_a232109_R1
import Mathlib

namespace PrimeOffsetWitness

private def witnesses : ℕ → List ℕ
  | 0 => [5, 3, 3, 5, 3, 5, 3, 7, 11, 5, 3, 5, 3, 7, 17, 5, 3, 5, 3, 7, 11, 5, 3, 23, 17]
  | 1 => [7, 11, 5, 3, 5, 3, 13, 11, 7, 19, 5, 3, 7, 17, 5, 3, 5, 3, 7, 17, 5, 3, 23, 11, 7]
  | 2 => [11, 5, 3, 23, 17, 7, 11, 5, 3, 5, 3, 31, 11, 7, 19, 5, 3, 7, 11, 5, 3, 5, 3, 13, 17]
  | 3 => [7, 19, 5, 3, 7, 17, 5, 3, 23, 17, 7, 11, 5, 3, 29, 11, 13, 11, 7, 19, 5, 3, 7, 11, 5]
  | 4 => [3, 5, 3, 7, 89, 5, 3, 5, 3, 7, 17, 5, 3, 47, 19, 13, 11, 23, 67, 29, 11, 13, 17, 7, 67]
  | 5 => [5, 3, 7, 11, 5, 3, 29, 67, 7, 17, 5, 3, 5, 3, 37, 11, 13, 19, 23, 17, 7, 11, 5, 3, 5]
  | 6 => [3, 13, 11, 7, 19, 5, 3, 13, 41, 7, 19, 5, 3, 7, 17, 5, 3, 23, 11, 7, 11, 5, 3, 23, 19]
  | 7 => [7, 41, 5, 3, 5, 3, 13, 11, 13, 139, 23, 11, 7, 11, 5, 3, 5, 3, 7, 17, 5, 3, 5, 3, 37]
  | 8 => [11, 23, 19, 47, 17, 31, 41, 7, 43, 5, 3, 13, 11, 13, 19, 23, 11, 13, 11, 7, 19, 5, 3, 7, 59]
  | 9 => [5, 3, 5, 3, 7, 11, 5, 3, 47, 17, 7, 59, 5, 3, 5, 3, 13, 17, 31, 19, 29, 11, 7, 17, 5]
  | 10 => [3, 23, 11, 7, 17, 5, 3, 23, 11, 7, 11, 5, 3, 71, 17, 7, 11, 5, 3, 5, 3, 79, 11, 7, 19]
  | 11 => [5, 3, 7, 17, 5, 3, 5, 3, 31, 17, 37, 139, 29, 17, 7, 89, 5, 3, 23, 19, 13, 11, 13, 43, 149]
  | 12 => [11, 13, 11, 7, 97, 5, 3, 7, 17, 5, 3, 5, 3, 7, 107, 5, 3, 23, 17, 79, 11, 13, 19, 23, 17]
  | 13 => [31, 11, 7, 67, 5, 3, 13, 41, 7, 67, 5, 3, 13, 11, 29, 73, 23, 11, 7, 17, 5, 3, 5, 3, 7]
  | 14 => [17, 5, 3, 23, 17, 7, 11, 5, 3, 47, 17, 31, 11, 7, 19, 5, 3, 13, 11, 7, 97, 5, 3, 13, 89]
  | 15 => [7, 43, 5, 3, 7, 17, 5, 3, 23, 19, 7, 11, 5, 3, 47, 11, 61, 17, 7, 19, 5, 3, 7, 11, 5]
  | 16 => [3, 23, 17, 13, 17, 7, 19, 5, 3, 37, 11, 23, 19, 53, 17, 7, 41, 5, 3, 5, 3, 61, 11, 13, 19]
  | 17 => [53, 19, 7, 11, 5, 3, 5, 3, 13, 17, 7, 43, 5, 3, 7, 41, 5, 3, 23, 107, 7, 11, 5, 3, 29]
  | 18 => [11, 13, 11, 7, 19, 5, 3, 7, 17, 5, 3, 5, 3, 7, 227, 5, 3, 23, 11, 109, 17, 13, 19, 47, 17]
  | 19 => [7, 11, 5, 3, 29, 11, 31, 41, 7, 19, 5, 3, 7, 11, 5, 3, 23, 11, 13, 17, 7, 139, 5, 3, 7]
  | 20 => [41, 5, 3, 47, 19, 7, 83, 5, 3, 29, 11, 31, 11, 23, 139, 23, 43, 7, 17, 5, 3, 5, 3, 37, 89]
  | 21 => [13, 19, 29, 17, 37, 11, 13, 19, 47, 17, 31, 11, 7, 97, 5, 3, 13, 17, 7, 379, 5, 3, 13, 17, 29]
  | 22 => [19, 23, 11, 7, 107, 5, 3, 23, 11, 7, 11, 5, 3, 23, 17, 7, 11, 5, 3, 5, 3, 13, 17, 7, 67]
  | 23 => [5, 3, 13, 17, 37, 19, 29, 11, 7, 17, 5, 3, 23, 11, 7, 11, 5, 3, 53, 19, 7, 11, 5, 3, 5]
  | 24 => [3, 13, 11, 7, 19, 5, 3, 37, 11, 7, 19, 5, 3, 7, 17, 5, 3, 5, 3, 37, 11, 23, 19, 47, 17]
  | 25 => [13, 59, 7, 43, 5, 3, 13, 11, 31, 67, 23, 11, 7, 41, 5, 3, 5, 3, 7, 17, 5, 3, 29, 11, 7]
  | 26 => [11, 5, 3, 23, 17, 7, 59, 5, 3, 5, 3, 13, 11, 23, 19, 29, 11, 13, 41, 7, 43, 5, 3, 7, 89]
  | 27 => [5, 3, 23, 83, 7, 11, 5, 3, 23, 59, 13, 41, 7, 67, 5, 3, 31, 41, 13, 67, 23, 19, 7, 11, 5]
  | 28 => [3, 23, 19, 13, 17, 7, 19, 5, 3, 37, 17, 13, 193, 23, 17, 7, 11, 5, 3, 29, 19, 31, 11, 7, 19]
  | 29 => [5, 3, 13, 11, 7, 43, 5, 3, 31, 107, 7, 19, 5, 3, 7, 11, 5, 3, 47, 17, 13, 11, 7, 67, 5]
  | 30 => [3, 31, 89, 7, 67, 5, 3, 7, 11, 5, 3, 29, 11, 103, 59, 7, 43, 5, 3, 7, 113, 5, 3, 23, 19]
  | 31 => [31, 11, 31, 67, 47, 17, 13, 17, 7, 19, 5, 3, 37, 83, 29, 19, 29, 17, 7, 17, 5, 3, 23, 11, 37]
  | 32 => [11, 23, 19, 23, 97, 7, 41, 5, 3, 5, 3, 13, 11, 13, 337, 29, 11, 7, 11, 5, 3, 5, 3, 7, 17]
  | 33 => [5, 3, 5, 3, 37, 17, 23, 67, 47, 17, 7, 83, 5, 3, 47, 19, 13, 11, 13, 19, 29, 11, 13, 11, 7]
  | 34 => [19, 5, 3, 7, 17, 5, 3, 5, 3, 7, 41, 5, 3, 23, 89, 13, 11, 13, 73, 47, 11, 13, 11, 7, 19]
  | 35 => [5, 3, 7, 17, 5, 3, 5, 3, 7, 59, 5, 3, 53, 83, 127, 17, 13, 19, 71, 59, 13, 11, 23, 43, 29]
  | 36 => [11, 109, 41, 7, 19, 5, 3, 7, 11, 5, 3, 23, 17, 13, 59, 7, 19, 5, 3, 109, 59, 13, 67, 53, 17]
  | 37 => [7, 11, 5, 3, 29, 11, 13, 41, 7, 19, 5, 3, 7, 17, 5, 3, 23, 11, 7, 179, 5, 3, 29, 17, 7]
  | 38 => [137, 5, 3, 23, 17, 13, 11, 23, 67, 29, 11, 13, 17, 7, 67, 5, 3, 7, 17, 5, 3, 29, 11, 7, 59]
  | 39 => [5, 3, 23, 73, 7, 11, 5, 3, 23, 17, 31, 11, 7, 73, 5, 3, 31, 17, 7, 19, 5, 3, 13, 11, 29]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def smallPrimeProduct : ℕ := 72047817630210000485677936198920432067383702541010310

private theorem product_eq : primorial 137 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 137 then n.Prime else n ≤ 18311 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 137
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 18311 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 137 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 138 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ fac.dvd_primorial_iff.mpr small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let n := 25 * i + j.val + 1
  let p := witness i j
  Certified p ∧ p ≠ 2 ∧ p < n + 5 ∧ Certified (n + (p-1)*(p-3)/8)

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

end PrimeOffsetWitness

open PrimeOffsetWitness

theorem OMA.solution : OMA.R_oeis_a232109_R1.H1 := by
  intro n hlo hhi
  let i := (n - 1) / 25
  let j : Fin 25 := ⟨(n - 1) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 1 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨witness i j, primeOfCertified h1, h2, h3, primeOfCertified h4⟩