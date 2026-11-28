import OMAReductions.R_OeisA227923_conjecture_4_R1

import Mathlib

namespace PrimeDecompositions

private def witnesses : ℕ → List ℕ
  | 0 => [1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4, 5, 1, 2, 9, 1, 1, 2, 4, 4, 1, 2, 7, 4]
  | 1 => [5, 14, 1, 1, 2, 4, 1, 2, 7, 4, 5, 9, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4, 5, 7, 7]
  | 2 => [9, 1, 2, 47, 4, 5, 14, 1, 1, 2, 4, 4, 5, 1, 2, 9, 4, 5, 32, 7, 14, 9, 15, 1, 2]
  | 3 => [19, 1, 2, 22, 4, 5, 9, 7, 1, 2, 29, 4, 5, 32, 7, 15, 9, 1, 1, 2, 4, 4, 1, 1, 2]
  | 4 => [4, 4, 5, 7, 7, 9, 1, 1, 1, 2, 4, 4, 1, 2, 7, 4, 5, 42, 7, 14, 9, 14, 15, 32, 19]
  | 5 => [14, 15, 22, 22, 22, 19, 39, 40, 22, 29, 29, 1, 2, 32, 4, 5, 30, 1, 2, 9, 4, 1, 2, 7, 4]
  | 6 => [5, 40, 7, 42, 9, 14, 1, 1, 2, 4, 4, 1, 1, 2, 4, 4, 5, 7, 1, 2, 9, 4, 5, 32, 7]
  | 7 => [14, 9, 22, 22, 19, 19, 1, 1, 1, 2, 4, 4, 5, 7, 7, 9, 9, 32, 32, 14, 14, 1, 1, 2, 4]
  | 8 => [4, 5, 1, 1, 2, 4, 4, 5, 7, 7, 9, 9, 1, 1, 2, 4, 1, 2, 7, 4, 5, 9, 7, 22, 9]
  | 9 => [14, 1, 1, 2, 4, 4, 5, 7, 7, 9, 9, 40, 1, 1, 2, 4, 4, 5, 7, 7, 9, 1, 1, 1, 2]
  | 10 => [4, 4, 5, 7, 7, 9, 9, 32, 1, 2, 14, 4, 5, 82, 7, 19, 1, 1, 1, 2, 4, 4, 5, 7, 7]
  | 11 => [9, 9, 30, 32, 14, 14, 14, 15, 47, 19, 19, 19, 22, 22, 22, 109, 109, 47, 47, 29, 29, 29, 30, 32, 32]
  | 12 => [74, 99, 107, 107, 39, 39, 39, 40, 42, 42, 74, 1, 2, 47, 4, 5, 1, 1, 2, 4, 4, 5, 7, 7, 9]
  | 13 => [9, 60, 60, 1, 2, 14, 4, 1, 2, 7, 4, 5, 22, 7, 29, 9, 14, 15, 1, 2, 14, 1, 2, 32, 4]
  | 14 => [5, 9, 7, 22, 9, 39, 14, 15, 42, 14, 15, 19, 47, 32, 19, 49, 39, 1, 2, 42, 4, 5, 1, 2, 29]
  | 15 => [4, 5, 1, 2, 114, 4, 5, 40, 7, 39, 9, 15, 42, 1, 2, 14, 1, 2, 22, 4, 5, 9, 7, 1, 2]
  | 16 => [29, 1, 1, 2, 4, 4, 1, 2, 7, 4, 5, 14, 7, 42, 9, 14, 15, 30, 42, 14, 15, 175, 22, 1, 2]
  | 17 => [49, 4, 5, 247, 7, 29, 9, 32, 32, 29, 30, 14, 15, 72, 39, 39, 19, 1, 2, 22, 4, 5, 1, 1, 2]
  | 18 => [4, 4, 5, 7, 7, 9, 9, 60, 82, 72, 14, 14, 15, 22, 42, 19, 19, 70, 22, 22, 29, 30, 1, 2, 74]
  | 19 => [4, 5, 30, 7, 32, 9, 40, 1, 1, 2, 4, 4, 5, 7, 7, 9, 9, 1, 1, 2, 4, 4, 5, 7, 7]
  | 20 => [9, 9, 175, 22, 22, 14, 14, 15, 107, 109, 19, 19, 30, 1, 2, 74, 4, 5, 47, 7, 29, 9, 30, 32, 32]
  | 21 => [120, 14, 15, 47, 47, 39, 19, 40, 1, 2, 135, 4, 5, 47, 7, 49, 1, 2, 72, 4, 5, 14, 7, 107, 9]
  | 22 => [109, 19, 40, 1, 2, 15, 4, 5, 242, 7, 114, 9, 22, 72, 32, 74, 14, 1, 2, 29, 4, 5, 32, 7, 22]
  | 23 => [9, 1, 2, 107, 4, 5, 15, 7, 252, 9, 19, 74, 1, 1, 2, 4, 4, 5, 7, 7, 9, 9, 22, 32, 47]
  | 24 => [14, 14, 1, 2, 29, 4, 5, 32, 7, 22, 9, 1, 2, 47, 4, 5, 15, 7, 32, 9, 19, 109, 47, 22, 14]
  | 25 => [15, 1, 2, 42, 4, 5, 30, 1, 2, 9, 4, 5, 85, 7, 14, 9, 40, 32, 42, 19, 14, 15, 22, 47, 39]
  | 26 => [19, 1, 1, 1, 2, 4, 4, 5, 7, 7, 9, 9, 110, 32, 14, 14, 1, 1, 1, 2, 4, 4, 5, 7, 7]
  | 27 => [9, 9, 410, 1, 2, 14, 4, 5, 32, 7, 19, 9, 1, 1, 2, 4, 4, 5, 7, 7, 9, 9, 30, 32, 22]
  | 28 => [14, 1, 2, 72, 4, 5, 19, 7, 1, 2, 60, 4, 5, 1, 2, 15, 4, 5, 32, 7, 70, 9, 15, 72, 47]
  | 29 => [39, 14, 15, 42, 22, 30, 1, 2, 47, 4, 5, 29, 7, 72, 9, 40, 1, 1, 2, 4, 4, 5, 7, 7, 9]
  | 30 => [9, 39, 1, 2, 14, 4, 5, 70, 7, 19, 9, 49, 22, 22, 99, 14, 15, 60, 82, 29, 19, 30, 1, 1, 2]
  | 31 => [4, 4, 5, 1, 2, 9, 4, 5, 32, 7, 14, 9, 15, 47, 49, 19, 14, 15, 22, 22, 109, 19, 1, 1, 2]
  | 32 => [4, 4, 5, 7, 7, 9, 9, 30, 242, 32, 14, 1, 2, 42, 4, 5, 19, 7, 22, 9, 49, 1, 1, 2, 4]
  | 33 => [4, 5, 1, 2, 9, 4, 5, 22, 1, 2, 9, 4, 5, 42, 7, 14, 9, 22, 22, 47, 19, 1, 2, 22, 4]
  | 34 => [5, 19, 7, 32, 9, 29, 30, 1, 2, 14, 4, 5, 30, 7, 19, 9, 40, 22, 42, 49, 14, 1, 2, 47, 4]
  | 35 => [5, 99, 7, 1, 2, 60, 4, 1, 1, 2, 4, 4, 5, 7, 7, 9, 9, 15, 72, 49, 14, 1, 1, 1, 2]
  | 36 => [4, 4, 5, 7, 7, 9, 9, 30, 82, 14, 14, 1, 1, 2, 4, 4, 1, 2, 7, 4, 5, 39, 7, 42, 9]
  | 37 => [14, 15, 30, 32, 14, 15, 49, 22, 22, 19, 39, 39, 22, 42, 29, 29, 1, 2, 32, 4, 5, 49, 7, 127, 9]
  | 38 => [39, 1, 2, 42, 4, 5, 60, 7, 47, 9, 49, 135, 22, 82, 14, 15, 1, 1, 2, 4, 4, 5, 7, 1, 2]
  | 39 => [9, 1, 2, 82, 4, 5, 9, 1, 2, 9, 4, 5, 15, 7, 14, 9, 19, 42, 82, 19, 14, 1, 2, 32, 4]
  | _ => []

private def pair (i : ℕ) (j : Fin 25) : ℕ × ℕ :=
  let x := (witnesses i).getD j.val 0
  (x, 25 * i + j.val + 2 - x)

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
  let x := (pair i j).1
  let y := (pair i j).2
  0 < x ∧ 0 < y ∧ x + y = 25 * i + j.val + 2 ∧
    Certified (6 * x - 1) ∧ Certified (12 * x - 1) ∧
    Certified (6 * y - 1) ∧ Certified (6 * y + 5)

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

theorem result : OMA.R_OeisA227923_conjecture_4_R1.H1 := by
  intro n hlo hhi
  let i := (n - 2) / 25
  let j : Fin 25 := ⟨(n - 2) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 2 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hx, hy, hsum, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨(pair i j).1, (pair i j).2, hx, hy, hsum, primeOfCertified h₁,
    primeOfCertified h₂, primeOfCertified h₃, primeOfCertified h₄⟩

end PrimeDecompositions

theorem OMA.solution : OMA.R_OeisA227923_conjecture_4_R1.H1 :=
  PrimeDecompositions.result