import OMAReductions.R_oeis_a047949_R1

import Mathlib

namespace PrimePairsAroundMidpoints

private def witnesses : ℕ → List ℕ
  | 0 => [0, 0, 1, 0, 1, 0, 3, 2, 3, 0, 1, 0, 3, 2, 3, 0, 1, 0, 3, 2, 9, 0, 5, 6, 3]
  | 1 => [4, 9, 0, 1, 0, 9, 4, 3, 6, 5, 0, 9, 2, 3, 0, 1, 0, 3, 2, 15, 0, 5, 12, 3, 8]
  | 2 => [9, 0, 7, 12, 3, 4, 15, 0, 1, 0, 9, 4, 3, 6, 5, 0, 15, 2, 3, 0, 1, 0, 15, 4, 3]
  | 3 => [6, 5, 0, 9, 2, 15, 0, 5, 12, 3, 14, 9, 0, 7, 12, 9, 4, 15, 6, 7, 0, 9, 2, 3, 0]
  | 4 => [1, 0, 3, 2, 3, 0, 1, 0, 3, 2, 15, 0, 13, 12, 15, 10, 9, 12, 7, 18, 9, 14, 15, 12, 13]
  | 5 => [0, 21, 2, 21, 0, 5, 6, 3, 4, 27, 0, 1, 0, 9, 10, 15, 6, 5, 6, 33, 10, 9, 0, 1, 0]
  | 6 => [15, 4, 3, 18, 7, 0, 9, 8, 3, 12, 5, 0, 15, 2, 15, 0, 5, 12, 3, 8, 9, 0, 7, 18, 3]
  | 7 => [4, 15, 0, 1, 0, 9, 10, 27, 6, 5, 6, 9, 8, 9, 0, 1, 0, 3, 2, 3, 0, 1, 0, 27, 10]
  | 8 => [9, 24, 7, 6, 27, 16, 15, 18, 13, 0, 15, 14, 15, 18, 17, 6, 21, 8, 9, 30, 11, 0, 27, 2, 3]
  | 9 => [0, 1, 0, 3, 2, 9, 0, 5, 6, 3, 4, 39, 0, 1, 0, 9, 14, 33, 6, 5, 24, 9, 8, 21, 0]
  | 10 => [11, 24, 3, 14, 15, 0, 19, 18, 3, 10, 21, 0, 7, 42, 3, 4, 39, 0, 1, 0, 9, 4, 3, 6, 5]
  | 11 => [0, 15, 2, 3, 0, 1, 0, 27, 8, 45, 6, 5, 18, 21, 20, 15, 0, 13, 12, 15, 14, 15, 18, 7, 30]
  | 12 => [9, 10, 27, 12, 25, 0, 39, 2, 3, 0, 1, 0, 3, 2, 33, 0, 35, 12, 27, 10, 9, 30, 7, 12, 33]
  | 13 => [10, 21, 18, 17, 0, 15, 16, 3, 18, 23, 0, 21, 8, 9, 48, 5, 6, 75, 8, 33, 0, 1, 0, 3, 2]
  | 14 => [15, 0, 5, 18, 3, 10, 9, 0, 7, 12, 69, 4, 15, 18, 7, 0, 15, 10, 3, 12, 25, 0, 15, 8, 3]
  | 15 => [24, 5, 0, 21, 2, 15, 0, 5, 12, 3, 14, 9, 0, 7, 18, 9, 4, 15, 6, 13, 0, 45, 2, 21, 0]
  | 16 => [19, 6, 15, 4, 27, 24, 11, 0, 9, 10, 45, 30, 5, 6, 15, 16, 21, 0, 1, 0, 21, 26, 15, 6, 5]
  | 17 => [6, 39, 10, 9, 0, 1, 0, 15, 4, 3, 6, 5, 0, 9, 2, 21, 0, 5, 12, 3, 14, 9, 0, 7, 12]
  | 18 => [9, 4, 33, 6, 7, 0, 9, 2, 3, 0, 1, 0, 3, 2, 33, 0, 11, 30, 9, 8, 15, 6, 13, 12, 15]
  | 19 => [10, 21, 0, 19, 18, 21, 4, 63, 6, 23, 0, 21, 2, 33, 0, 29, 6, 15, 4, 75, 6, 11, 0, 9, 2]
  | 20 => [39, 0, 5, 18, 3, 16, 69, 0, 11, 12, 9, 10, 27, 6, 7, 30, 39, 28, 21, 0, 1, 0, 33, 16, 87]
  | 21 => [36, 19, 42, 27, 10, 9, 24, 13, 12, 27, 34, 39, 18, 17, 0, 21, 20, 3, 24, 23, 0, 39, 8, 27, 42]
  | 22 => [5, 54, 33, 8, 15, 0, 11, 12, 3, 38, 15, 0, 7, 42, 3, 4, 45, 0, 1, 0, 15, 4, 3, 12, 55]
  | 23 => [0, 9, 8, 33, 12, 5, 36, 15, 8, 15, 0, 11, 12, 3, 22, 15, 0, 7, 18, 3, 4, 21, 0, 1, 0]
  | 24 => [15, 4, 3, 12, 7, 0, 9, 8, 3, 42, 5, 0, 27, 2, 3, 0, 1, 0, 21, 20, 9, 24, 7, 6, 27]
  | 25 => [14, 15, 12, 11, 0, 15, 14, 27, 18, 5, 6, 21, 8, 21, 0, 1, 0, 3, 2, 15, 0, 5, 42, 3, 8]
  | 26 => [9, 0, 7, 36, 3, 4, 15, 0, 1, 0, 15, 10, 45, 12, 7, 6, 9, 8, 39, 12, 11, 0, 27, 2, 15]
  | 27 => [0, 5, 48, 3, 20, 9, 0, 7, 24, 33, 4, 45, 12, 29, 0, 9, 16, 33, 48, 5, 36, 21, 40, 9, 0]
  | 28 => [25, 30, 57, 4, 33, 54, 25, 0, 9, 28, 21, 30, 5, 24, 57, 16, 9, 0, 19, 12, 21, 4, 15, 48, 7]
  | 29 => [0, 45, 10, 3, 12, 41, 0, 75, 8, 3, 36, 5, 0, 21, 2, 9, 0, 17, 6, 27, 4, 9, 48, 7, 0]
  | 30 => [9, 20, 3, 54, 5, 0, 15, 2, 9, 0, 11, 6, 45, 4, 57, 6, 29, 0, 27, 2, 15, 0, 13, 36, 33]
  | 31 => [20, 9, 18, 7, 30, 39, 14, 27, 12, 25, 0, 69, 20, 21, 18, 5, 36, 33, 26, 27, 0, 11, 12, 27, 28]
  | 32 => [51, 6, 7, 18, 33, 20, 21, 0, 1, 0, 15, 16, 45, 6, 5, 6, 9, 8, 9, 0, 1, 0, 3, 2, 3]
  | 33 => [0, 1, 0, 9, 8, 21, 6, 5, 24, 27, 16, 15, 0, 13, 12, 15, 14, 15, 18, 7, 36, 9, 10, 27, 12]
  | 34 => [25, 0, 27, 2, 3, 0, 1, 0, 3, 2, 75, 0, 43, 12, 45, 10, 9, 12, 7, 12, 9, 10, 45, 12, 53]
  | 35 => [0, 51, 2, 3, 0, 1, 0, 3, 2, 33, 0, 31, 30, 51, 28, 15, 36, 13, 12, 15, 10, 21, 12, 19, 18]
  | 36 => [39, 16, 93, 24, 23, 0, 21, 2, 27, 0, 25, 6, 27, 4, 93, 30, 11, 0, 9, 62, 15, 60, 5, 42, 15]
  | 37 => [20, 9, 0, 11, 78, 21, 4, 57, 6, 17, 0, 9, 2, 57, 0, 5, 24, 3, 8, 63, 0, 19, 42, 3, 32]
  | 38 => [15, 0, 13, 36, 15, 10, 39, 12, 7, 78, 9, 34, 27, 12, 25, 0, 15, 2, 51, 0, 5, 36, 3, 8, 57]
  | 39 => [0, 31, 12, 3, 10, 15, 0, 7, 48, 33, 4, 21, 42, 7, 0, 21, 16, 3, 18, 13, 0, 15, 22, 9, 18]
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
  let n := 25 * i + j.val + 2
  p ≤ n ∧ Certified (n - p) ∧ Certified (n + p)

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

theorem result : OMA.R_oeis_a047949_R1.H1 := by
  intro n hlo hhi
  let i := (n - 2) / 25
  let j : Fin 25 := ⟨(n - 2) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 2 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hm, hleft, hright⟩ := h
  exact ⟨witness i j, hm, primeOfCertified hleft, primeOfCertified hright⟩

end PrimePairsAroundMidpoints

theorem OMA.solution : OMA.R_oeis_a047949_R1.H1 :=
  PrimePairsAroundMidpoints.result