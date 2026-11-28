import OMAReductions.R_oeis_a219025_R1

import Mathlib

namespace PrimeSymmetricSums

private def witnesses : ℕ → List ℕ
  | 0 => [5, 5, 5, 7, 7, 5, 11, 5, 5, 7, 7, 5, 5, 13, 7, 13, 5, 11, 5, 13, 7, 5, 5, 7, 13]
  | 1 => [5, 19, 31, 7, 13, 17, 11, 5, 5, 11, 5, 11, 19, 7, 7, 5, 11, 5, 13, 7, 43, 5, 41, 7, 17]
  | 2 => [23, 5, 11, 5, 7, 7, 59, 5, 5, 7, 13, 19, 11, 5, 11, 5, 11, 5, 5, 7, 7, 5, 11, 13, 19]
  | 3 => [23, 29, 11, 5, 11, 7, 19, 19, 13, 17, 23, 5, 11, 7, 7, 67, 5, 11, 7, 7, 7, 5, 41, 7, 11]
  | 4 => [5, 11, 5, 7, 13, 7, 11, 5, 7, 29, 5, 41, 31, 5, 19, 7, 41, 5, 17, 7, 5, 11, 29, 13, 7]
  | 5 => [43, 5, 11, 7, 13, 5, 61, 31, 5, 13, 7, 29, 5, 43, 7, 53, 5, 31, 13, 19, 23, 29, 11, 5, 11]
  | 6 => [17, 5, 19, 13, 7, 47, 5, 31, 7, 7, 13, 11, 11, 5, 11, 5, 19, 71, 5, 11, 5, 29, 19, 13, 11]
  | 7 => [17, 5, 5, 13, 7, 7, 29, 59, 17, 11, 17, 29, 5, 67, 17, 5, 11, 71, 7, 13, 43, 11, 5, 7, 7]
  | 8 => [13, 41, 11, 5, 23, 17, 101, 19, 5, 7, 5, 5, 11, 7, 41, 47, 29, 61, 17, 23, 53, 61, 41, 7, 19]
  | 9 => [13, 31, 31, 5, 29, 7, 61, 5, 5, 7, 7, 19, 29, 17, 11, 5, 11, 5, 5, 11, 17, 19, 31, 43, 19]
  | 10 => [13, 11, 5, 5, 7, 13, 29, 19, 13, 7, 13, 5, 11, 5, 7, 43, 5, 19, 23, 13, 37, 5, 31, 47, 13]
  | 11 => [23, 29, 61, 5, 11, 7, 101, 5, 13, 7, 13, 31, 89, 23, 17, 113, 5, 79, 7, 11, 5, 11, 29, 23, 41]
  | 12 => [53, 19, 59, 7, 13, 5, 5, 11, 5, 11, 17, 29, 41, 37, 13, 47, 19, 59, 43, 37, 23, 11, 19, 23, 7]
  | 13 => [7, 5, 5, 7, 7, 13, 5, 11, 5, 13, 7, 59, 5, 47, 17, 7, 29, 181, 5, 11, 7, 29, 19, 13, 31]
  | 14 => [5, 11, 5, 67, 19, 13, 31, 89, 23, 47, 17, 41, 5, 7, 17, 13, 11, 31, 7, 37, 13, 11, 29, 7, 7]
  | 15 => [47, 5, 11, 7, 23, 23, 11, 19, 23, 7, 5, 5, 19, 7, 13, 5, 11, 5, 5, 11, 17, 29, 19, 13, 7]
  | 16 => [37, 5, 11, 13, 13, 7, 5, 61, 37, 13, 97, 29, 31, 37, 73, 5, 11, 71, 5, 7, 53, 31, 11, 17, 29]
  | 17 => [7, 41, 19, 13, 53, 67, 71, 19, 13, 7, 13, 5, 41, 7, 7, 13, 5, 5, 5, 7, 7, 19, 11, 5, 11]
  | 18 => [5, 11, 19, 13, 7, 37, 5, 11, 7, 13, 5, 281, 11, 23, 17, 7, 29, 5, 7, 7, 5, 109, 11, 13, 23]
  | 19 => [53, 5, 11, 53, 7, 37, 5, 11, 37, 13, 7, 109, 5, 7, 31, 23, 19, 31, 67, 37, 5, 11, 19, 13, 7]
  | 20 => [13, 19, 139, 13, 19, 17, 11, 11, 5, 29, 13, 19, 29, 5, 71, 37, 71, 29, 23, 13, 47, 41, 89, 7, 11]
  | 21 => [5, 11, 11, 13, 7, 13, 31, 179, 17, 11, 83, 61, 41, 7, 53, 23, 31, 31, 37, 29, 7, 11, 5, 5, 17]
  | 22 => [7, 19, 41, 7, 13, 5, 41, 71, 23, 17, 37, 11, 61, 43, 13, 37, 59, 31, 73, 17, 7, 5, 61, 17, 11]
  | 23 => [53, 79, 29, 13, 19, 17, 5, 11, 5, 7, 13, 5, 59, 7, 11, 5, 11, 5, 13, 7, 67, 5, 5, 7, 7]
  | 24 => [23, 29, 11, 17, 17, 7, 29, 19, 7, 19, 5, 31, 11, 5, 19, 7, 61, 29, 17, 11, 23, 61, 29, 5, 13]
  | 25 => [7, 31, 5, 43, 13, 37, 29, 5, 13, 7, 43, 29, 5, 13, 7, 13, 29, 41, 13, 11, 17, 5, 11, 5, 13]
  | 26 => [7, 61, 19, 47, 29, 23, 29, 11, 17, 23, 7, 71, 5, 7, 7, 23, 19, 11, 113, 23, 37, 11, 11, 17, 31]
  | 27 => [7, 19, 41, 53, 17, 17, 11, 29, 5, 13, 7, 59, 19, 37, 31, 43, 29, 29, 17, 41, 5, 59, 41, 5, 11]
  | 28 => [5, 11, 5, 43, 29, 5, 11, 5, 13, 7, 43, 61, 19, 43, 37, 37, 5, 11, 5, 13, 7, 79, 5, 17, 17]
  | 29 => [23, 29, 59, 47, 13, 7, 59, 19, 13, 17, 5, 5, 61, 17, 13, 127, 31, 5, 13, 7, 13, 5, 5, 43, 17]
  | 30 => [13, 19, 101, 7, 37, 17, 11, 59, 37, 7, 47, 19, 41, 23, 17, 23, 11, 41, 5, 7, 7, 11, 5, 17, 23]
  | 31 => [37, 29, 61, 47, 19, 13, 71, 5, 83, 11, 13, 31, 29, 107, 19, 17, 31, 5, 5, 13, 7, 19, 59, 7, 31]
  | 32 => [53, 29, 61, 23, 29, 5, 59, 79, 53, 13, 7, 31, 179, 5, 11, 7, 61, 5, 7, 7, 13, 5, 31, 37, 7]
  | 33 => [13, 19, 5, 5, 11, 5, 29, 59, 47, 19, 53, 29, 19, 13, 11, 37, 5, 11, 7, 13, 7, 281, 79, 23, 17]
  | 34 => [17, 29, 41, 73, 7, 13, 59, 11, 5, 19, 83, 31, 19, 17, 11, 47, 5, 41, 17, 23, 23, 181, 41, 107, 43]
  | 35 => [107, 11, 89, 43, 13, 7, 241, 5, 53, 7, 67, 29, 61, 17, 23, 43, 31, 269, 13, 7, 7, 5, 19, 7, 11]
  | 36 => [5, 29, 29, 17, 11, 17, 29, 29, 43, 11, 163, 19, 229, 7, 37, 5, 31, 19, 13, 19, 113, 61, 5, 17, 11]
  | 37 => [5, 61, 41, 47, 29, 43, 31, 109, 103, 17, 5, 5, 11, 5, 13, 7, 29, 5, 43, 11, 5, 29, 61, 13, 13]
  | 38 => [43, 41, 31, 37, 19, 17, 29, 29, 43, 11, 5, 11, 59, 7, 7, 13, 11, 11, 5, 7, 5, 5, 11, 5, 23]
  | 39 => [17, 11, 29, 23, 13, 37, 131, 59, 53, 13, 7, 29, 79, 83, 17, 53, 29, 349, 13, 47, 67, 31, 11, 13, 23]
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
  let n := 25 * i + j.val + 6
  p < n ∧ Certified p ∧ Certified (6 * n - p) ∧ Certified (6 * n + p)

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

theorem result : OMA.R_oeis_a219025_R1.H1 := by
  intro n hlo hhi
  let i := (n - 6) / 25
  let j : Fin 25 := ⟨(n - 6) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 6 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hle, hp, hleft, hright⟩ := h
  exact ⟨witness i j, hle, primeOfCertified hp, primeOfCertified hleft, primeOfCertified hright⟩

end PrimeSymmetricSums

theorem OMA.solution : OMA.R_oeis_a219025_R1.H1 :=
  PrimeSymmetricSums.result