import OMAReductions.R_oeis_a219966_R1
import Mathlib

namespace PrimeWitnesses

private def witnesses : ℕ → List ℕ
  | 0 => [5, 5, 7, 5, 5, 5, 5, 7, 7, 5, 5, 5, 5, 7, 7, 5, 5, 5, 7, 7, 13, 5, 5, 11, 5]
  | 1 => [7, 7, 5, 11, 5, 5, 7, 7, 7, 5, 5, 5, 13, 7, 5, 5, 5, 7, 7, 13, 5, 5, 11, 7, 7]
  | 2 => [31, 5, 5, 11, 5, 7, 7, 5, 11, 5, 5, 7, 7, 7, 5, 5, 5, 13, 7, 5, 11, 5, 5, 7, 7]
  | 3 => [7, 5, 5, 7, 31, 13, 5, 5, 11, 7, 7, 31, 5, 11, 11, 5, 7, 7, 11, 5, 5, 5, 13, 7, 5]
  | 4 => [5, 5, 5, 7, 7, 5, 5, 5, 7, 7, 13, 5, 11, 11, 13, 7, 31, 11, 17, 11, 5, 13, 7, 11, 5]
  | 5 => [5, 7, 13, 13, 5, 5, 17, 5, 7, 7, 5, 11, 5, 11, 7, 13, 7, 5, 23, 5, 13, 7, 5, 11, 5]
  | 6 => [5, 7, 7, 7, 17, 5, 5, 31, 7, 7, 5, 5, 7, 13, 13, 5, 5, 11, 7, 7, 31, 5, 5, 11, 5]
  | 7 => [7, 7, 5, 11, 5, 11, 7, 13, 7, 5, 17, 5, 13, 7, 5, 5, 5, 5, 7, 7, 5, 11, 5, 11, 7]
  | 8 => [13, 7, 17, 11, 5, 13, 7, 11, 23, 5, 11, 13, 13, 7, 47, 17, 5, 31, 7, 17, 5, 5, 5, 31, 7]
  | 9 => [5, 5, 5, 7, 7, 13, 5, 5, 11, 5, 7, 7, 5, 11, 5, 11, 7, 13, 7, 5, 17, 7, 13, 31, 5]
  | 10 => [5, 11, 7, 7, 37, 5, 5, 23, 7, 7, 31, 5, 5, 17, 5, 7, 7, 5, 11, 5, 5, 7, 7, 7, 5]
  | 11 => [5, 5, 13, 7, 5, 11, 5, 11, 7, 13, 7, 5, 11, 7, 31, 31, 5, 11, 11, 13, 7, 31, 13, 17, 17]
  | 12 => [5, 31, 7, 11, 5, 5, 5, 13, 7, 5, 5, 5, 7, 7, 13, 5, 11, 11, 13, 7, 61, 11, 17, 11, 5]
  | 13 => [13, 7, 11, 23, 5, 5, 13, 7, 7, 53, 5, 11, 61, 13, 7, 5, 11, 5, 31, 7, 5, 5, 5, 7, 7]
  | 14 => [13, 5, 5, 17, 7, 7, 31, 5, 11, 11, 5, 7, 7, 11, 17, 5, 5, 13, 7, 7, 23, 5, 5, 13, 7]
  | 15 => [7, 5, 5, 7, 37, 13, 5, 5, 11, 7, 7, 31, 5, 11, 11, 5, 7, 7, 11, 5, 5, 7, 13, 13, 5]
  | 16 => [11, 17, 5, 7, 7, 17, 17, 5, 11, 31, 13, 7, 5, 23, 5, 13, 7, 5, 11, 5, 11, 7, 13, 7, 5]
  | 17 => [53, 5, 61, 7, 5, 11, 5, 5, 7, 7, 7, 5, 5, 7, 31, 13, 5, 5, 11, 7, 7, 37, 5, 11, 11]
  | 18 => [5, 7, 7, 11, 5, 5, 5, 13, 7, 5, 5, 5, 7, 7, 13, 5, 11, 11, 13, 7, 61, 11, 5, 11, 7]
  | 19 => [13, 31, 5, 11, 17, 5, 7, 7, 17, 5, 5, 7, 73, 13, 5, 11, 23, 5, 7, 7, 23, 5, 5, 7, 31]
  | 20 => [13, 5, 5, 41, 7, 7, 31, 5, 11, 11, 13, 7, 37, 11, 5, 47, 5, 13, 7, 5, 11, 5, 11, 7, 13]
  | 21 => [7, 17, 41, 17, 31, 103, 11, 23, 11, 5, 13, 7, 13, 41, 5, 5, 31, 7, 7, 47, 5, 11, 103, 13, 7]
  | 22 => [5, 11, 7, 31, 67, 5, 5, 11, 7, 7, 31, 5, 5, 17, 5, 7, 7, 5, 11, 5, 5, 7, 7, 7, 17]
  | 23 => [5, 11, 13, 13, 7, 5, 11, 7, 13, 73, 5, 5, 11, 7, 7, 31, 5, 5, 17, 5, 7, 7, 5, 11, 5]
  | 24 => [5, 7, 7, 7, 17, 5, 5, 13, 7, 7, 5, 5, 5, 13, 7, 5, 11, 5, 11, 7, 13, 7, 17, 11, 5]
  | 25 => [37, 7, 11, 23, 5, 11, 13, 13, 7, 5, 17, 5, 31, 7, 5, 5, 5, 7, 7, 13, 5, 5, 23, 7, 7]
  | 26 => [31, 5, 5, 11, 5, 7, 7, 5, 11, 5, 11, 7, 13, 7, 17, 17, 5, 13, 7, 11, 5, 5, 7, 13, 13]
  | 27 => [5, 5, 23, 7, 7, 31, 5, 11, 11, 5, 7, 7, 11, 17, 5, 11, 13, 13, 7, 5, 17, 7, 13, 37, 5]
  | 28 => [11, 11, 5, 7, 7, 13, 17, 5, 11, 31, 13, 7, 5, 17, 7, 13, 37, 5, 11, 11, 5, 7, 7, 13, 17]
  | 29 => [5, 5, 31, 7, 7, 23, 5, 5, 13, 7, 7, 5, 5, 7, 37, 13, 5, 11, 11, 5, 7, 7, 13, 17, 5]
  | 30 => [5, 31, 7, 7, 5, 5, 7, 13, 13, 5, 11, 11, 5, 7, 7, 13, 5, 5, 7, 31, 13, 5, 11, 17, 13]
  | 31 => [7, 31, 23, 17, 11, 5, 37, 7, 11, 23, 5, 11, 13, 13, 7, 5, 17, 7, 31, 37, 5, 11, 11, 13, 7]
  | 32 => [61, 13, 5, 23, 5, 37, 7, 5, 11, 5, 11, 7, 13, 7, 5, 47, 5, 73, 7, 5, 5, 5, 5, 7, 7]
  | 33 => [5, 11, 5, 11, 7, 13, 7, 5, 11, 7, 13, 37, 5, 11, 11, 13, 7, 31, 13, 17, 17, 5, 31, 7, 11]
  | 34 => [5, 5, 5, 13, 7, 5, 5, 5, 7, 7, 13, 5, 11, 11, 13, 7, 67, 11, 17, 11, 5, 13, 7, 11, 5]
  | 35 => [5, 5, 13, 7, 5, 5, 5, 7, 7, 13, 5, 11, 11, 13, 7, 73, 11, 17, 11, 23, 13, 31, 11, 23, 17]
  | 36 => [5, 13, 7, 17, 5, 5, 7, 31, 13, 5, 11, 23, 5, 7, 7, 23, 17, 5, 11, 37, 13, 7, 5, 41, 7]
  | 37 => [13, 31, 5, 11, 11, 5, 7, 7, 13, 5, 5, 7, 31, 13, 5, 5, 17, 7, 7, 37, 5, 5, 11, 7, 7]
  | 38 => [103, 5, 11, 23, 13, 7, 31, 11, 17, 17, 5, 13, 7, 11, 5, 5, 7, 13, 13, 5, 5, 23, 7, 7, 67]
  | 39 => [5, 5, 11, 7, 7, 73, 5, 11, 83, 5, 7, 7, 11, 17, 5, 5, 13, 7, 7, 23, 5, 11, 13, 13, 7]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def smallPrimeProduct : ℕ := 263130836933693530167218012160000000

private theorem product_eq : Nat.factorial 32 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 32 then n.Prime else n ≤ 1088 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 32
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 1088 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 32 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 33 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ Nat.dvd_factorial fac.pos small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let n := 25 * i + j.val + 12
  let q := witness i j
  (1 + n % 2) * q ≤ n ∧ 2 * q ≤ n ∧
    Certified (n - (1 + n % 2) * q) ∧ Certified q ∧ Certified (q + 6)

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

theorem result : OMA.R_oeis_a219966_R1.H1 := by
  intro n hlo hhi
  let i := (n - 12) / 25
  let j : Fin 25 := ⟨(n - 12) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 12 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hb, hq, h₁, h₂, h₃⟩ := h
  refine ⟨n - (1 + n % 2) * witness i j, witness i j, ?_, hq, primeOfCertified h₁, primeOfCertified h₂, primeOfCertified h₃⟩
  rw [Nat.add_mul, one_mul] at hb ⊢
  omega

end PrimeWitnesses

theorem OMA.solution : OMA.R_oeis_a219966_R1.H1 :=
  PrimeWitnesses.result