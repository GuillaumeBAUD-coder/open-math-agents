import OMAReductions.R_oeis_a187758_R1
import Mathlib

namespace PrimePairWitness

private def witnesses : ℕ → List ℕ
  | 0 => [4, 4, 4, 5, 7, 4, 4, 5, 7, 7, 4, 5, 4, 5, 8, 4, 4, 4, 5, 7, 4, 5, 10, 7, 8]
  | 1 => [13, 4, 5, 17, 7, 8, 4, 5, 17, 7, 8, 4, 4, 5, 7, 7, 8, 10, 10, 17, 4, 5, 20, 7, 8]
  | 2 => [4, 4, 5, 7, 7, 8, 10, 4, 5, 13, 7, 8, 4, 5, 17, 4, 5, 20, 7, 8, 17, 10, 4, 5, 13]
  | 3 => [4, 4, 5, 7, 7, 4, 5, 4, 5, 8, 7, 8, 55, 10, 13, 22, 13, 20, 17, 22, 17, 20, 25, 20, 28]
  | 4 => [22, 4, 5, 25, 7, 8, 4, 5, 32, 7, 8, 4, 5, 35, 7, 8, 38, 10, 50, 17, 13, 43, 4, 5, 17]
  | 5 => [4, 5, 4, 5, 8, 7, 8, 25, 10, 13, 17, 4, 5, 17, 7, 8, 4, 4, 5, 7, 4, 4, 5, 7, 7]
  | 6 => [4, 5, 10, 7, 8, 4, 5, 20, 7, 8, 4, 5, 20, 7, 8, 28, 10, 4, 5, 13, 7, 8, 35, 10, 28]
  | 7 => [38, 13, 35, 22, 28, 4, 4, 5, 7, 7, 8, 10, 10, 25, 13, 13, 28, 50, 17, 17, 32, 20, 20, 22, 22]
  | 8 => [77, 4, 5, 52, 7, 8, 43, 10, 32, 32, 13, 35, 4, 5, 17, 4, 4, 5, 7, 7, 8, 10, 10, 67, 13]
  | 9 => [13, 50, 50, 17, 17, 22, 20, 20, 22, 22, 38, 4, 4, 5, 7, 4, 5, 10, 7, 8, 13, 4, 4, 5, 7]
  | 10 => [7, 8, 10, 10, 22, 13, 13, 4, 5, 17, 4, 5, 4, 5, 8, 4, 5, 4, 5, 8, 7, 8, 130, 10, 13]
  | 11 => [17, 4, 5, 17, 7, 8, 4, 5, 20, 7, 8, 25, 10, 25, 17, 13, 28, 20, 32, 17, 32, 4, 5, 35, 7]
  | 12 => [8, 38, 10, 50, 32, 13, 43, 35, 50, 17, 4, 4, 5, 7, 7, 8, 10, 10, 55, 13, 13, 85, 50, 17, 17]
  | 13 => [53, 20, 20, 22, 22, 38, 4, 4, 5, 7, 7, 8, 10, 10, 32, 13, 13, 35, 80, 17, 17, 4, 5, 20, 7]
  | 14 => [8, 88, 10, 25, 77, 4, 5, 50, 7, 8, 32, 10, 20, 35, 13, 38, 4, 5, 17, 7, 8, 20, 4, 5, 32]
  | 15 => [7, 8, 4, 5, 17, 7, 4, 5, 10, 7, 8, 13, 10, 20, 38, 4, 5, 50, 7, 8, 4, 5, 4, 5, 8]
  | 16 => [7, 8, 25, 10, 13, 4, 5, 80, 7, 8, 17, 4, 5, 20, 7, 8, 25, 10, 17, 28, 13, 20, 4, 5, 17]
  | 17 => [7, 8, 20, 10, 22, 53, 13, 25, 32, 43, 4, 5, 130, 7, 8, 22, 10, 4, 5, 13, 7, 4, 4, 5, 7]
  | 18 => [4, 5, 10, 7, 8, 13, 10, 4, 5, 13, 7, 8, 20, 10, 22, 4, 5, 25, 7, 8, 17, 4, 5, 20, 7]
  | 19 => [4, 5, 10, 7, 8, 13, 10, 140, 22, 13, 32, 25, 20, 17, 22, 52, 4, 5, 22, 7, 8, 25, 10, 52, 28]
  | 20 => [13, 55, 4, 5, 17, 4, 5, 20, 7, 8, 43, 10, 4, 5, 13, 7, 8, 50, 10, 32, 22, 13, 35, 22, 53]
  | 21 => [17, 4, 5, 20, 7, 4, 5, 10, 7, 8, 4, 5, 50, 7, 8, 32, 4, 5, 17, 7, 8, 20, 10, 17, 88]
  | 22 => [13, 20, 4, 5, 17, 7, 4, 5, 10, 7, 8, 13, 10, 32, 38, 13, 35, 80, 20, 17, 22, 118, 20, 25, 22]
  | 23 => [4, 4, 5, 7, 7, 8, 10, 10, 35, 13, 13, 38, 4, 5, 17, 7, 8, 20, 10, 22, 43, 13, 25, 50, 28]
  | 24 => [17, 4, 5, 20, 7, 8, 35, 10, 25, 38, 13, 4, 5, 115, 7, 4, 5, 10, 7, 8, 13, 10, 25, 52, 13]
  | 25 => [28, 43, 20, 17, 22, 188, 4, 5, 22, 7, 8, 25, 10, 55, 28, 4, 5, 35, 7, 8, 4, 5, 20, 7, 8]
  | 26 => [4, 5, 4, 5, 8, 7, 4, 5, 10, 7, 8, 13, 10, 17, 28, 13, 4, 5, 20, 7, 8, 25, 10, 25, 22]
  | 27 => [13, 28, 25, 32, 17, 28, 35, 20, 35, 22, 88, 38, 4, 5, 43, 7, 4, 5, 10, 7, 8, 13, 10, 50, 53]
  | 28 => [13, 53, 50, 20, 17, 22, 175, 20, 25, 22, 113, 28, 25, 67, 52, 28, 80, 55, 35, 32, 113, 38, 35, 77, 88]
  | 29 => [38, 43, 130, 80, 67, 43, 85, 80, 50, 88, 52, 53, 50, 55, 52, 4, 5, 55, 7, 8, 97, 10, 85, 137, 13]
  | 30 => [67, 4, 4, 5, 7, 7, 8, 10, 10, 97, 13, 13, 155, 80, 17, 17, 118, 20, 20, 22, 22, 35, 4, 5, 38]
  | 31 => [7, 8, 115, 10, 32, 32, 13, 35, 35, 97, 17, 38, 4, 5, 53, 7, 8, 130, 10, 167, 133, 4, 4, 5, 7]
  | 32 => [7, 4, 5, 10, 7, 8, 13, 10, 25, 17, 13, 28, 20, 20, 17, 22, 80, 20, 25, 22, 28, 4, 5, 55, 7]
  | 33 => [8, 43, 4, 5, 32, 7, 8, 4, 5, 17, 7, 8, 20, 10, 22, 17, 13, 25, 20, 52, 4, 5, 50, 7, 8]
  | 34 => [22, 10, 35, 25, 13, 32, 28, 230, 17, 67, 4, 5, 115, 7, 8, 97, 10, 50, 85, 13, 4, 4, 5, 7, 7]
  | 35 => [8, 10, 10, 22, 13, 13, 25, 85, 17, 17, 88, 20, 20, 22, 22, 4, 5, 25, 7, 8, 28, 10, 80, 32, 13]
  | 36 => [77, 4, 5, 17, 7, 4, 5, 10, 7, 8, 13, 10, 4, 5, 13, 7, 4, 5, 10, 7, 4, 5, 10, 7, 8]
  | 37 => [13, 10, 4, 5, 13, 7, 8, 20, 10, 22, 38, 13, 25, 22, 38, 4, 4, 5, 7, 7, 8, 10, 4, 5, 13]
  | 38 => [7, 8, 55, 10, 17, 4, 5, 20, 7, 8, 17, 10, 4, 5, 13, 7, 8, 55, 10, 32, 178, 13, 4, 5, 38]
  | 39 => [4, 5, 80, 7, 8, 22, 10, 85, 25, 13, 17, 4, 5, 17, 7, 8, 20, 10, 22, 43, 13, 25, 85, 55, 17]
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
  let n := 25 * i + j.val + 5
  let x := witness i j
  let y := n - x
  0 < x ∧ 0 < y ∧ x + y = n ∧ Certified (2*x-3) ∧ Certified (2*x+3) ∧
    Certified (6*y+1) ∧ Certified (6*y+5)

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

end PrimePairWitness

open PrimePairWitness

theorem OMA.solution : OMA.R_oeis_a187758_R1.H1 := by
  intro n hlo hhi
  let i := (n - 5) / 25
  let j : Fin 25 := ⟨(n - 5) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 5 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hx, hy, hsum, h1, h2, h3, h4⟩ := h
  exact ⟨witness i j, n - witness i j, hx, hy, hsum,
    primeOfCertified h1, primeOfCertified h2, primeOfCertified h3, primeOfCertified h4⟩