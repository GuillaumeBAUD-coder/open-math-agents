import OMAReductions.R_oeis_a085053_R1

import Mathlib

namespace AffinePrimeWitnesses

private def witnesses : ℕ → List ℕ
  | 0 => [1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 2, 2, 1, 6, 1, 10, 2, 2, 1, 2, 3, 4]
  | 1 => [2, 4, 1, 2, 1, 10, 3, 2, 3, 2, 1, 4, 5, 2, 1, 2, 1, 4, 2, 4, 1, 6, 2, 4, 2]
  | 2 => [2, 1, 2, 2, 6, 2, 4, 1, 12, 1, 6, 5, 2, 3, 2, 1, 4, 2, 2, 1, 8, 1, 4, 2, 2]
  | 3 => [3, 6, 1, 4, 3, 2, 1, 2, 4, 12, 2, 4, 1, 2, 2, 6, 3, 4, 3, 2, 1, 4, 2, 2, 1]
  | 4 => [6, 1, 6, 3, 2, 1, 6, 1, 10, 3, 2, 1, 2, 2, 4, 2, 8, 6, 2, 2, 6, 3, 6, 3, 2]
  | 5 => [1, 4, 2, 8, 1, 2, 3, 12, 2, 2, 1, 6, 1, 4, 2, 2, 4, 6, 3, 10, 2, 6, 1, 8, 1]
  | 6 => [6, 3, 2, 3, 2, 1, 10, 2, 20, 4, 6, 1, 4, 5, 2, 1, 14, 2, 4, 6, 12, 1, 2, 2, 4]
  | 7 => [2, 4, 1, 2, 1, 6, 3, 2, 7, 8, 2, 6, 5, 2, 1, 2, 1, 4, 2, 6, 1, 18, 1, 4, 2]
  | 8 => [8, 3, 12, 2, 4, 3, 4, 6, 2, 1, 10, 5, 4, 3, 2, 2, 6, 5, 2, 3, 2, 1, 12, 2, 8]
  | 9 => [1, 24, 1, 12, 2, 2, 1, 2, 4, 4, 3, 6, 1, 2, 1, 6, 3, 2, 3, 2, 3, 6, 6, 2, 1]
  | 10 => [2, 3, 4, 2, 4, 1, 6, 4, 10, 2, 2, 1, 6, 5, 4, 6, 4, 1, 8, 1, 6, 5, 2, 3, 12]
  | 11 => [1, 4, 2, 4, 1, 2, 1, 6, 2, 2, 3, 6, 2, 12, 5, 6, 1, 2, 3, 4, 2, 6, 4, 2, 2]
  | 12 => [10, 3, 2, 4, 6, 1, 4, 2, 2, 1, 6, 1, 6, 5, 2, 1, 26, 10, 4, 2, 2, 3, 2, 4, 4]
  | 13 => [2, 8, 7, 2, 1, 6, 3, 6, 7, 6, 1, 10, 2, 8, 3, 2, 6, 4, 3, 2, 1, 6, 1, 10, 2]
  | 14 => [10, 1, 14, 2, 6, 3, 4, 1, 2, 5, 30, 3, 2, 3, 18, 1, 6, 9, 2, 4, 2, 1, 4, 3, 2]
  | 15 => [3, 14, 1, 12, 2, 6, 1, 12, 2, 6, 2, 4, 1, 24, 3, 6, 8, 2, 9, 6, 1, 6, 2, 4, 1]
  | 16 => [8, 4, 4, 2, 2, 6, 8, 1, 4, 2, 2, 3, 2, 2, 28, 3, 4, 1, 2, 1, 10, 5, 4, 4, 6]
  | 17 => [2, 4, 2, 2, 1, 2, 1, 4, 3, 4, 6, 18, 1, 10, 2, 2, 1, 2, 4, 6, 6, 4, 1, 8, 4]
  | 18 => [6, 6, 2, 12, 2, 1, 30, 6, 2, 1, 6, 1, 12, 2, 4, 1, 6, 2, 4, 2, 8, 4, 2, 3, 4]
  | 19 => [2, 14, 1, 8, 7, 6, 3, 2, 3, 2, 1, 4, 2, 12, 1, 2, 6, 4, 3, 2, 3, 14, 1, 4, 6]
  | 20 => [10, 1, 6, 2, 10, 2, 4, 1, 2, 2, 6, 15, 4, 3, 2, 2, 4, 5, 2, 1, 32, 1, 10, 2, 2]
  | 21 => [3, 6, 4, 24, 2, 2, 3, 12, 2, 4, 3, 8, 4, 12, 1, 18, 3, 2, 10, 2, 1, 10, 2, 14, 6]
  | 22 => [2, 3, 4, 2, 4, 1, 6, 2, 4, 5, 2, 1, 14, 2, 6, 3, 4, 1, 12, 1, 10, 5, 4, 3, 2]
  | 23 => [1, 4, 6, 10, 3, 2, 3, 4, 3, 2, 1, 14, 6, 4, 2, 6, 1, 2, 3, 4, 2, 4, 1, 8, 1]
  | 24 => [6, 5, 12, 4, 6, 1, 6, 2, 4, 3, 2, 1, 10, 2, 2, 1, 8, 1, 4, 3, 6, 3, 6, 2, 18]
  | 25 => [3, 10, 6, 2, 1, 10, 6, 14, 13, 8, 5, 4, 2, 2, 1, 2, 1, 12, 2, 2, 1, 14, 2, 10, 2]
  | 26 => [2, 1, 2, 4, 4, 12, 6, 1, 2, 1, 6, 3, 2, 3, 14, 3, 6, 11, 4, 3, 6, 1, 4, 5, 6]
  | 27 => [1, 8, 4, 10, 2, 8, 1, 2, 3, 4, 2, 4, 4, 12, 1, 10, 5, 6, 3, 18, 3, 4, 5, 2, 1]
  | 28 => [18, 5, 6, 2, 6, 7, 6, 1, 4, 3, 2, 3, 2, 2, 4, 2, 8, 1, 2, 3, 6, 15, 2, 4, 2]
  | 29 => [1, 4, 9, 2, 9, 8, 1, 10, 3, 2, 7, 6, 1, 4, 2, 2, 1, 2, 2, 10, 2, 6, 7, 2, 1]
  | 30 => [6, 5, 6, 7, 2, 1, 16, 6, 4, 1, 2, 3, 12, 3, 2, 6, 6, 1, 10, 3, 2, 1, 6, 2, 6]
  | 31 => [2, 4, 12, 2, 3, 16, 3, 2, 4, 2, 1, 6, 6, 2, 3, 2, 3, 6, 3, 4, 1, 6, 2, 22, 2]
  | 32 => [10, 4, 2, 2, 4, 2, 4, 1, 2, 1, 10, 3, 2, 4, 8, 8, 6, 2, 8, 1, 8, 1, 10, 3, 4]
  | 33 => [1, 14, 1, 10, 14, 2, 4, 2, 2, 6, 8, 6, 1, 12, 3, 12, 5, 4, 13, 8, 2, 4, 2, 2, 3]
  | 34 => [6, 1, 4, 2, 8, 1, 8, 1, 22, 2, 2, 1, 6, 3, 4, 2, 4, 6, 12, 2, 6, 3, 2, 9, 8]
  | 35 => [1, 16, 5, 2, 1, 18, 1, 4, 5, 4, 1, 6, 2, 4, 3, 2, 3, 2, 2, 4, 3, 8, 4, 8, 2]
  | 36 => [6, 3, 4, 3, 2, 1, 6, 6, 4, 1, 2, 5, 6, 15, 2, 3, 6, 1, 4, 6, 6, 3, 2, 4, 4]
  | 37 => [6, 4, 1, 8, 2, 10, 3, 2, 3, 2, 1, 6, 2, 2, 1, 6, 4, 6, 2, 8, 1, 6, 4, 4, 2]
  | 38 => [10, 1, 2, 7, 4, 2, 6, 4, 8, 5, 16, 3, 4, 9, 2, 1, 16, 9, 4, 1, 6, 3, 6, 2, 2]
  | 39 => [1, 8, 6, 4, 6, 10, 1, 14, 3, 10, 2, 6, 7, 2, 1, 18, 6, 2, 7, 12, 1, 4, 2, 2, 3]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def smallPrimeProduct : ℕ := 10014646650599190067509233131649940057366334653200433090

private theorem product_eq : primorial 139 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 139 then n.Prime else n ≤ 19000 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 139
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 19000 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 139 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 140 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ fac.dvd_primorial_iff.mpr small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let k := witness i j
  let n := 25 * i + j.val + 1
  1 ≤ k ∧ k ≤ n ∧ Certified (n * k + 1)

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

theorem result : OMA.R_oeis_a085053_R1.H1 := by
  intro n hlo hhi
  let i := (n - 1) / 25
  let j : Fin 25 := ⟨(n - 1) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 1 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hpos, hle, hprime⟩ := h
  exact ⟨witness i j, hpos, hle, primeOfCertified hprime⟩

end AffinePrimeWitnesses

theorem OMA.solution : OMA.R_oeis_a085053_R1.H1 :=
  AffinePrimeWitnesses.result