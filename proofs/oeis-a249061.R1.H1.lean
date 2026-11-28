import OMAReductions.R_oeis_a249061_R1
import Mathlib

namespace PrimeWitnesses

private def witnesses : ℕ → List ℕ
  | 0 => [2, 1, 1, 4, 1, 3, 1, 3, 2, 4, 1, 3, 1, 3, 2, 7, 1, 3, 1, 4, 2, 4, 1, 3, 10]
  | 1 => [3, 2, 4, 1, 12, 1, 3, 5, 4, 2, 3, 1, 3, 2, 7, 1, 3, 1, 4, 2, 7, 1, 3, 10, 4]
  | 2 => [2, 4, 1, 3, 10, 3, 2, 4, 1, 12, 1, 3, 6, 4, 2, 3, 1, 3, 2, 4, 1, 8, 1, 3, 5]
  | 3 => [7, 2, 3, 1, 4, 2, 7, 1, 3, 10, 7, 2, 4, 1, 12, 13, 3, 5, 4, 2, 3, 1, 3, 2, 4]
  | 4 => [1, 3, 1, 3, 2, 16, 1, 3, 1, 7, 2, 7, 1, 8, 22, 8, 5, 4, 6, 12, 13, 3, 5, 7, 2]
  | 5 => [3, 1, 4, 2, 4, 1, 3, 13, 3, 2, 7, 1, 8, 1, 4, 17, 4, 5, 3, 10, 3, 2, 4, 1, 12]
  | 6 => [1, 3, 5, 4, 2, 8, 1, 3, 5, 19, 2, 3, 1, 4, 2, 7, 1, 3, 10, 4, 2, 4, 1, 3, 10]
  | 7 => [3, 2, 16, 1, 12, 1, 4, 5, 4, 5, 3, 10, 3, 2, 4, 1, 3, 1, 3, 2, 7, 1, 8, 1, 7]
  | 8 => [17, 4, 6, 8, 22, 3, 6, 19, 2, 20, 1, 7, 5, 4, 5, 8, 10, 3, 5, 4, 2, 3, 1, 3, 2]
  | 9 => [28, 1, 3, 1, 4, 2, 4, 1, 3, 22, 3, 2, 16, 1, 12, 1, 4, 5, 7, 14, 3, 13, 4, 2, 7]
  | 10 => [1, 3, 10, 4, 2, 7, 1, 3, 10, 4, 2, 4, 1, 3, 34, 3, 2, 4, 1, 12, 1, 3, 6, 4, 2]
  | 11 => [3, 1, 3, 2, 7, 1, 8, 1, 4, 14, 7, 6, 3, 13, 7, 2, 31, 1, 11, 10, 8, 5, 4, 5, 15]
  | 12 => [46, 3, 5, 4, 2, 3, 1, 3, 2, 7, 1, 3, 1, 8, 2, 31, 1, 8, 10, 7, 18, 4, 5, 8, 10]
  | 13 => [3, 6, 4, 2, 15, 1, 3, 5, 19, 2, 11, 1, 4, 5, 4, 13, 3, 10, 3, 2, 7, 1, 3, 1, 4]
  | 14 => [2, 7, 1, 3, 10, 7, 2, 4, 1, 15, 22, 3, 6, 4, 2, 8, 1, 3, 5, 4, 2, 12, 1, 3, 5]
  | 15 => [43, 2, 3, 1, 4, 2, 7, 1, 3, 10, 8, 2, 4, 1, 12, 22, 3, 18, 7, 2, 3, 1, 8, 2, 4]
  | 16 => [1, 11, 10, 3, 5, 7, 2, 8, 1, 4, 6, 4, 6, 3, 25, 3, 2, 19, 1, 24, 1, 4, 6, 4, 5]
  | 17 => [3, 25, 3, 2, 4, 1, 8, 1, 3, 5, 7, 2, 3, 1, 4, 2, 16, 1, 3, 10, 12, 2, 4, 1, 15]
  | 18 => [13, 3, 5, 4, 2, 3, 1, 3, 2, 7, 1, 3, 1, 7, 2, 16, 1, 8, 10, 4, 6, 7, 5, 3, 22]
  | 19 => [7, 2, 4, 1, 12, 13, 3, 6, 16, 2, 3, 1, 8, 2, 4, 1, 11, 10, 3, 5, 7, 2, 3, 1, 4]
  | 20 => [2, 19, 1, 3, 22, 8, 2, 16, 1, 12, 13, 4, 9, 4, 10, 3, 10, 3, 2, 7, 1, 8, 1, 12, 9]
  | 21 => [16, 5, 8, 13, 7, 17, 4, 5, 8, 22, 3, 6, 4, 2, 12, 1, 3, 5, 7, 2, 23, 1, 4, 5, 7]
  | 22 => [6, 3, 10, 4, 2, 16, 1, 3, 10, 4, 2, 4, 1, 3, 10, 3, 2, 4, 1, 12, 1, 3, 5, 7, 2]
  | 23 => [11, 1, 4, 5, 7, 6, 3, 13, 4, 2, 7, 1, 3, 10, 4, 2, 4, 1, 3, 25, 3, 2, 4, 1, 12]
  | 24 => [1, 3, 5, 4, 2, 8, 1, 3, 9, 4, 2, 3, 1, 3, 2, 7, 1, 8, 1, 7, 6, 4, 6, 8, 22]
  | 25 => [3, 5, 28, 2, 20, 1, 4, 5, 4, 14, 3, 10, 3, 2, 19, 1, 3, 1, 4, 2, 7, 1, 3, 13, 4]
  | 26 => [2, 4, 1, 3, 10, 3, 2, 28, 1, 32, 1, 11, 5, 4, 9, 8, 13, 3, 5, 19, 2, 3, 1, 4, 2]
  | 27 => [16, 1, 3, 10, 12, 2, 4, 1, 8, 10, 3, 5, 16, 2, 15, 1, 4, 14, 16, 5, 3, 10, 8, 2, 4]
  | 28 => [1, 15, 10, 3, 5, 7, 2, 8, 1, 4, 17, 7, 5, 3, 10, 7, 2, 4, 1, 12, 13, 3, 6, 4, 2]
  | 29 => [8, 1, 3, 5, 4, 2, 11, 1, 3, 14, 31, 2, 3, 1, 15, 2, 4, 1, 11, 22, 3, 5, 4, 2, 12]
  | 30 => [1, 3, 6, 31, 2, 3, 1, 11, 2, 4, 1, 8, 13, 3, 9, 28, 2, 3, 1, 7, 2, 16, 1, 8, 10]
  | 31 => [8, 6, 4, 9, 12, 22, 3, 5, 7, 2, 8, 1, 4, 6, 40, 6, 3, 13, 7, 2, 7, 1, 11, 10, 4]
  | 32 => [6, 4, 6, 3, 10, 3, 2, 19, 1, 12, 1, 4, 5, 4, 5, 3, 13, 3, 2, 4, 1, 3, 1, 3, 2]
  | 33 => [7, 1, 8, 1, 4, 17, 7, 6, 3, 22, 7, 2, 40, 1, 20, 22, 8, 5, 4, 5, 8, 13, 3, 5, 4]
  | 34 => [2, 3, 1, 3, 2, 7, 1, 3, 1, 7, 2, 16, 1, 11, 10, 31, 5, 4, 5, 12, 22, 3, 5, 4, 2]
  | 35 => [3, 1, 3, 2, 7, 1, 3, 1, 7, 2, 16, 1, 11, 25, 12, 6, 7, 5, 8, 34, 16, 5, 4, 6, 12]
  | 36 => [13, 3, 9, 16, 2, 3, 1, 19, 2, 4, 1, 8, 10, 3, 5, 16, 2, 8, 1, 4, 6, 28, 5, 3, 25]
  | 37 => [7, 2, 4, 1, 15, 13, 3, 5, 16, 2, 3, 1, 4, 2, 7, 1, 3, 10, 4, 2, 88, 1, 3, 13, 7]
  | 38 => [2, 16, 1, 11, 10, 7, 5, 4, 10, 24, 13, 3, 5, 7, 2, 3, 1, 4, 2, 7, 1, 3, 13, 4, 2]
  | 39 => [28, 1, 3, 10, 24, 2, 4, 1, 8, 10, 3, 9, 4, 2, 15, 1, 3, 6, 7, 2, 8, 1, 8, 5, 4]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def smallPrimeProduct : ℕ := 11978571669969891796072783721689098736458938142546425857555362864628009582789845319680000000000000000

private theorem product_eq : Nat.factorial 70 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 70 then n.Prime else n ≤ 5040 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 70
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 5040 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 70 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 71 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ Nat.dvd_factorial fac.pos small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let n := 25 * i + j.val
  let k := witness i j
  0 < k ∧ Certified (n + k * (k + 1) / 2)

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

theorem result : OMA.R_oeis_a249061_R1.H1 := by
  intro n hn
  let i := n / 25
  let j : Fin 25 := ⟨n % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn2 : 25 * i + j.val = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn2] at h
  exact ⟨witness i j, h.1, primeOfCertified h.2⟩

end PrimeWitnesses

theorem OMA.solution : OMA.R_oeis_a249061_R1.H1 :=
  PrimeWitnesses.result