import OMAReductions.R_oeis_a230230_R1

import Mathlib

namespace PairedPrimeSums

private def witnesses : ℕ → List ℕ
  | 0 => [5, 7, 5, 7, 5, 7, 13, 5, 5, 7, 5, 7, 13, 5, 5, 7, 11, 11, 13, 17, 5, 7, 5, 7, 13]
  | 1 => [11, 13, 19, 17, 5, 7, 23, 5, 7, 5, 5, 7, 11, 11, 13, 17, 17, 19, 5, 7, 31, 11, 13, 31, 5]
  | 2 => [7, 37, 5, 5, 7, 5, 7, 13, 11, 13, 19, 17, 19, 61, 23, 31, 31, 5, 7, 37, 11, 13, 79, 5, 5]
  | 3 => [7, 11, 11, 13, 17, 5, 7, 23, 11, 13, 41, 17, 19, 5, 7, 37, 11, 13, 31, 17, 19, 37, 5, 5, 7]
  | 4 => [11, 11, 13, 17, 5, 7, 23, 11, 13, 47, 17, 19, 5, 7, 37, 5, 7, 31, 5, 5, 7, 11, 11, 13, 17]
  | 5 => [17, 19, 23, 23, 67, 41, 31, 31, 41, 5, 7, 41, 11, 13, 5, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23]
  | 6 => [37, 83, 31, 31, 83, 37, 37, 41, 41, 163, 47, 47, 61, 53, 53, 67, 59, 5, 7, 107, 11, 13, 5, 7, 19]
  | 7 => [5, 7, 79, 5, 7, 31, 11, 13, 37, 17, 5, 7, 23, 11, 13, 41, 17, 19, 41, 23, 61, 41, 5, 7, 5]
  | 8 => [7, 13, 11, 5, 7, 17, 11, 13, 23, 17, 19, 83, 23, 37, 5, 7, 31, 11, 5, 7, 17, 11, 13, 23, 17]
  | 9 => [19, 59, 5, 7, 107, 5, 7, 41, 11, 13, 47, 17, 19, 5, 7, 31, 11, 5, 7, 5, 7, 13, 11, 13, 19]
  | 10 => [17, 19, 229, 23, 37, 31, 41, 31, 37, 47, 5, 7, 41, 11, 13, 47, 17, 19, 53, 23, 61, 59, 61, 31, 317]
  | 11 => [67, 37, 83, 41, 79, 5, 7, 109, 11, 5, 7, 17, 5, 7, 23, 11, 13, 101, 17, 19, 5, 7, 31, 11, 13]
  | 12 => [31, 17, 5, 7, 23, 11, 13, 5, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 37, 5, 7, 31, 5, 7, 37]
  | 13 => [11, 13, 199, 5, 5, 7, 11, 11, 13, 17, 5, 7, 23, 11, 13, 41, 17, 19, 47, 5, 7, 41, 11, 13, 5]
  | 14 => [7, 19, 11, 5, 7, 17, 11, 13, 23, 17, 19, 83, 23, 61, 89, 37, 31, 41, 53, 37, 5, 7, 61, 11, 13]
  | 15 => [67, 17, 5, 7, 5, 7, 13, 11, 13, 19, 17, 19, 109, 23, 167, 31, 47, 5, 7, 53, 11, 13, 41, 17, 19]
  | 16 => [47, 23, 151, 5, 7, 31, 11, 13, 37, 5, 7, 157, 11, 13, 79, 17, 19, 151, 23, 37, 61, 41, 31, 67, 47]
  | 17 => [37, 151, 41, 107, 79, 47, 61, 163, 53, 67, 307, 59, 61, 97, 269, 5, 7, 5, 7, 13, 11, 13, 19, 17, 19]
  | 18 => [151, 23, 5, 7, 107, 11, 13, 101, 5, 7, 41, 11, 13, 5, 7, 19, 11, 13, 37, 5, 7, 31, 5, 7, 37]
  | 19 => [11, 13, 79, 17, 19, 61, 23, 31, 67, 47, 31, 61, 41, 37, 67, 41, 61, 109, 47, 67, 79, 53, 5, 7, 59]
  | 20 => [11, 13, 83, 5, 7, 5, 7, 13, 5, 7, 19, 11, 13, 37, 17, 5, 7, 23, 11, 13, 101, 17, 19, 41, 5]
  | 21 => [7, 41, 11, 13, 47, 17, 19, 53, 5, 7, 59, 11, 13, 137, 17, 19, 269, 5, 7, 83, 11, 13, 5, 7, 19]
  | 22 => [5, 7, 61, 11, 13, 31, 17, 5, 7, 23, 11, 13, 191, 17, 19, 41, 23, 109, 41, 59, 31, 47, 83, 37, 5]
  | 23 => [5, 7, 11, 11, 13, 5, 7, 19, 11, 13, 61, 17, 19, 31, 23, 37, 37, 5, 7, 79, 11, 13, 151, 17, 5]
  | 24 => [7, 23, 11, 13, 53, 17, 19, 59, 23, 109, 41, 67, 31, 5, 7, 37, 11, 13, 157, 17, 19, 97, 23, 53, 223]
  | 25 => [107, 31, 61, 101, 37, 67, 41, 109, 157, 47, 191, 79, 53, 5, 7, 59, 11, 13, 5, 7, 19, 11, 13, 151, 17]
  | 26 => [5, 7, 5, 7, 13, 11, 13, 19, 5, 7, 277, 11, 13, 31, 17, 19, 37, 23, 37, 67, 41, 31, 151, 47, 37]
  | 27 => [79, 41, 59, 61, 5, 7, 67, 5, 7, 97, 5, 7, 79, 11, 5, 7, 17, 11, 13, 23, 17, 19, 41, 23, 373]
  | 28 => [41, 37, 31, 41, 97, 37, 47, 41, 223, 53, 47, 151, 59, 5, 7, 131, 11, 13, 5, 7, 19, 11, 13, 151, 5]
  | 29 => [7, 31, 11, 13, 37, 17, 19, 193, 23, 5, 7, 41, 11, 13, 47, 17, 19, 41, 23, 67, 47, 61, 31, 5, 7]
  | 30 => [37, 11, 13, 313, 17, 19, 367, 23, 53, 97, 89, 31, 61, 83, 5, 7, 41, 11, 13, 47, 5, 7, 53, 5, 7]
  | 31 => [59, 11, 13, 191, 17, 19, 131, 23, 31, 5, 7, 31, 11, 13, 37, 5, 7, 61, 11, 13, 67, 17, 5, 7, 5]
  | 32 => [7, 13, 5, 7, 19, 11, 13, 79, 17, 19, 31, 23, 31, 37, 53, 31, 97, 41, 37, 97, 41, 53, 109, 47, 59]
  | 33 => [61, 53, 61, 67, 59, 5, 7, 5, 7, 13, 11, 13, 19, 17, 19, 157, 23, 109, 31, 89, 31, 37, 5, 5, 7]
  | 34 => [11, 11, 13, 17, 17, 19, 23, 23, 61, 59, 5, 7, 131, 11, 13, 5, 7, 19, 11, 5, 7, 17, 11, 13, 23]
  | 35 => [17, 19, 191, 23, 67, 101, 37, 31, 41, 53, 37, 47, 41, 61, 53, 47, 67, 59, 53, 97, 101, 59, 61, 107, 5]
  | 36 => [7, 443, 11, 13, 5, 7, 19, 11, 13, 163, 5, 7, 31, 11, 5, 7, 17, 11, 13, 23, 17, 19, 41, 23, 157]
  | 37 => [47, 37, 31, 41, 167, 37, 47, 41, 151, 5, 7, 79, 5, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 163, 83]
  | 38 => [31, 31, 41, 37, 37, 5, 7, 199, 11, 13, 97, 17, 19, 193, 23, 59, 61, 131, 31, 67, 137, 37, 151, 5, 7]
  | 39 => [79, 11, 13, 163, 17, 19, 229, 23, 61, 97, 101, 31, 151, 107, 37, 109, 41, 79, 163, 47, 167, 199, 53, 5, 7]
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
  let n := 25 * i + j.val + 4
  let q := 2 * n - p
  p + q = 2 * n ∧ Certified p ∧ Certified q ∧
    Certified (3 * p - 10) ∧ Certified (3 * q + 10)

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

theorem result : OMA.R_oeis_a230230_R1.H1 := by
  intro n hlo hhi
  let i := (n - 4) / 25
  let j : Fin 25 := ⟨(n - 4) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 4 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hsum, hp, hq, hleft, hright⟩ := h
  exact ⟨witness i j, 2 * n - witness i j, hsum, primeOfCertified hp,
    primeOfCertified hq, primeOfCertified hleft, primeOfCertified hright⟩

end PairedPrimeSums

theorem OMA.solution : OMA.R_oeis_a230230_R1.H1 :=
  PairedPrimeSums.result