import OMAReductions.R_oeis_a219864_R1
import Mathlib

namespace PrimeWitnesses

private def witnesses : ℕ → List ℕ
  | 0 => [3, 2, 3, 2, 2, 3, 3, 2, 3, 2, 5, 3, 2, 3, 7, 5, 2, 13, 2, 2, 3, 2, 2, 7, 5]
  | 1 => [3, 7, 3, 2, 7, 3, 2, 3, 2, 7, 3, 11, 2, 7, 2, 3, 3, 2, 2, 7, 23, 3, 3, 11, 5]
  | 2 => [3, 2, 2, 3, 2, 13, 3, 3, 2, 37, 5, 2, 7, 2, 2, 3, 5, 2, 3, 11, 19, 3, 2, 2, 7]
  | 3 => [53, 3, 7, 2, 5, 13, 2, 2, 13, 11, 3, 3, 2, 5, 31, 3, 2, 7, 2, 2, 3, 2, 3, 3, 2]
  | 4 => [3, 7, 2, 5, 7, 3, 2, 3, 2, 2, 3, 11, 5, 3, 5, 5, 3, 3, 3, 31, 3, 2, 7, 3, 2]
  | 5 => [13, 3, 5, 19, 2, 3, 19, 3, 2, 31, 5, 2, 3, 2, 17, 13, 3, 2, 7, 2, 5, 3, 2, 2, 127]
  | 6 => [5, 3, 7, 11, 2, 43, 3, 2, 37, 2, 3, 3, 2, 2, 7, 3, 7, 3, 3, 2, 3, 2, 3, 3, 101]
  | 7 => [13, 3, 2, 5, 7, 5, 3, 3, 2, 2, 79, 2, 2, 7, 11, 3, 7, 5, 2, 7, 3, 2, 3, 5, 2]
  | 8 => [3, 2, 7, 3, 11, 5, 13, 2, 2, 67, 3, 3, 3, 2, 2, 3, 3, 19, 7, 5, 13, 7, 5, 7, 37]
  | 9 => [3, 2, 19, 2, 2, 13, 5, 2, 3, 5, 5, 3, 3, 2, 7, 3, 5, 3, 2, 11, 19, 2, 2, 19, 2]
  | 10 => [3, 7, 2, 3, 7, 83, 2, 7, 3, 2, 19, 2, 19, 3, 5, 3, 3, 2, 2, 37, 5, 2, 3, 2, 7]
  | 11 => [43, 2, 3, 3, 11, 13, 13, 2, 5, 31, 3, 3, 3, 3, 2, 13, 3, 2, 3, 2, 3, 7, 2, 2, 7]
  | 12 => [3, 2, 7, 2, 7, 3, 2, 3, 3, 5, 29, 61, 17, 2, 31, 5, 2, 3, 2, 2, 3, 11, 5, 13, 2]
  | 13 => [19, 3, 3, 3, 7, 3, 3, 7, 3, 2, 13, 5, 2, 31, 2, 19, 7, 3, 3, 7, 29, 2, 3, 5, 41]
  | 14 => [3, 2, 2, 7, 5, 3, 7, 2, 3, 37, 5, 11, 3, 17, 2, 3, 2, 2, 3, 11, 3, 7, 17, 3, 61]
  | 15 => [3, 3, 3, 17, 5, 3, 2, 2, 13, 197, 3, 3, 17, 5, 37, 3, 3, 3, 2, 2, 13, 2, 2, 31, 2]
  | 16 => [13, 3, 5, 2, 31, 29, 3, 3, 2, 7, 13, 2, 3, 19, 11, 3, 7, 2, 2, 7, 3, 2, 7, 5, 2]
  | 17 => [19, 53, 2, 7, 2, 19, 3, 2, 11, 7, 53, 3, 7, 2, 5, 3, 2, 3, 3, 2, 5, 3, 3, 3, 7]
  | 18 => [3, 7, 7, 3, 11, 13, 3, 17, 7, 2, 3, 3, 2, 2, 37, 149, 2, 3, 17, 2, 3, 3, 2, 7, 71]
  | 19 => [59, 3, 2, 19, 37, 5, 2, 7, 5, 5, 19, 11, 2, 19, 71, 3, 13, 2, 2, 97, 3, 7, 31, 2, 5]
  | 20 => [19, 2, 5, 3, 17, 3, 3, 2, 3, 31, 59, 2, 13, 3, 2, 3, 2, 7, 13, 11, 5, 7, 2, 3, 7]
  | 21 => [3, 2, 7, 2, 2, 43, 3, 2, 3, 2, 5, 13, 3, 3, 7, 3, 5, 7, 59, 5, 3, 3, 2, 3, 2]
  | 22 => [3, 13, 3, 2, 37, 3, 5, 3, 11, 7, 3, 2, 2, 67, 2, 13, 43, 2, 2, 331, 83, 2, 3, 3, 17]
  | 23 => [13, 5, 2, 3, 2, 3, 3, 5, 2, 7, 3, 3, 7, 2, 2, 3, 2, 2, 7, 11, 5, 3, 3, 2, 37]
  | 24 => [3, 3, 3, 2, 2, 13, 5, 3, 7, 5, 3, 3, 2, 2, 31, 59, 3, 3, 3, 5, 13, 11, 11, 3, 2]
  | 25 => [19, 7, 3, 5, 7, 29, 2, 3, 2, 11, 13, 3, 3, 19, 5, 23, 3, 2, 3, 61, 5, 2, 13, 2, 2]
  | 26 => [3, 29, 2, 7, 5, 5, 3, 11, 2, 7, 23, 23, 3, 2, 7, 3, 2, 2, 13, 11, 3, 3, 2, 5, 331]
  | 27 => [5, 2, 3, 3, 2, 3, 2, 2, 3, 5, 13, 7, 3, 2, 7, 23, 2, 13, 2, 2, 3, 5, 5, 3, 11]
  | 28 => [3, 7, 2, 2, 7, 3, 11, 3, 2, 2, 103, 3, 5, 43, 11, 13, 3, 53, 2, 37, 29, 2, 3, 2, 7]
  | 29 => [43, 11, 7, 31, 5, 5, 19, 2, 2, 97, 3, 2, 7, 5, 11, 43, 17, 3, 19, 2, 5, 3, 3, 3, 7]
  | 30 => [23, 5, 13, 2, 2, 3, 2, 7, 7, 2, 3, 3, 3, 13, 7, 3, 2, 7, 3, 7, 3, 2, 3, 7, 2]
  | 31 => [13, 13, 11, 2, 37, 173, 5, 3, 3, 11, 109, 2, 5, 3, 2, 13, 19, 3, 3, 7, 3, 2, 3, 2, 2]
  | 32 => [3, 2, 7, 7, 11, 3, 7, 2, 2, 31, 23, 7, 3, 3, 5, 13, 5, 3, 7, 2, 3, 3, 2, 3, 7]
  | 33 => [29, 2, 3, 3, 7, 3, 11, 3, 7, 2, 79, 7, 2, 3, 31, 5, 2, 43, 5, 7, 3, 3, 2, 3, 5]
  | 34 => [19, 13, 2, 11, 7, 5, 2, 13, 2, 2, 43, 2, 11, 3, 47, 5, 3, 3, 11, 31, 5, 5, 13, 2, 7]
  | 35 => [3, 2, 2, 13, 2, 5, 13, 3, 2, 7, 53, 3, 7, 11, 2, 13, 5, 2, 7, 5, 43, 3, 2, 2, 7]
  | 36 => [3, 3, 3, 2, 7, 43, 5, 7, 3, 137, 13, 13, 2, 2, 31, 3, 3, 7, 2, 2, 19, 2, 3, 3, 41]
  | 37 => [3, 7, 2, 5, 37, 53, 5, 3, 101, 2, 3, 2, 3, 3, 5, 5, 13, 2, 2, 151, 3, 5, 19, 5, 2]
  | 38 => [13, 3, 2, 3, 47, 53, 7, 2, 3, 7, 3, 7, 61, 2, 2, 3, 2, 7, 3, 5, 3, 3, 11, 2, 31]
  | 39 => [3, 2, 7, 5, 7, 193, 11, 3, 67, 5, 19, 31, 3, 17, 61, 5, 2, 7, 17, 2, 13, 3, 2, 13, 2]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def smallPrimeProduct : ℕ := 1435626364184616525344593631006921385120806701387686527815553074299489808109929181482606325443788648158680773797406646719784966780615352007682001766090079288486500932652961265112128822061531207476892899033822509910792951470110

private theorem product_eq : primorial 560 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 560 then n.Prime else n ≤ 314720 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 560
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 314720 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 560 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 561 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ fac.dvd_primorial_iff.mpr small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let n := 25 * i + j.val + 8
  let p := witness i j
  p ≤ n ∧ Certified p ∧ Certified (2 * p * (n - p) + 1)

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

theorem result : OMA.R_oeis_a219864_R1.H1 := by
  intro n hlo hhi
  let i := (n - 8) / 25
  let j : Fin 25 := ⟨(n - 8) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 8 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hp, h₁, h₂⟩ := h
  exact ⟨witness i j, n - witness i j, by omega, primeOfCertified h₁, primeOfCertified h₂⟩

end PrimeWitnesses

theorem OMA.solution : OMA.R_oeis_a219864_R1.H1 :=
  PrimeWitnesses.result