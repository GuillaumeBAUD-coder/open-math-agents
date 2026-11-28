import OMAReductions.R_oeis_a220431_R1
import Mathlib

namespace PrimeProductWitness

private def witnesses : ℕ → List ℕ
  | 0 => [2, 2, 2, 4, 2, 2, 4, 2, 2, 6, 2, 4, 4, 2, 2, 4, 6, 2, 4, 2, 2, 4, 2, 14, 6]
  | 1 => [2, 4, 4, 2, 2, 6, 6, 2, 4, 2, 2, 24, 20, 2, 36, 2, 4, 4, 2, 6, 4, 6, 2, 4, 2]
  | 2 => [2, 6, 2, 2, 6, 2, 4, 4, 20, 20, 4, 6, 2, 4, 2, 14, 4, 2, 2, 6, 14, 4, 6, 2, 2]
  | 3 => [24, 6, 2, 4, 6, 2, 34, 2, 4, 6, 2, 6, 4, 2, 2, 4, 20, 4, 34, 2, 2, 4, 2, 2, 10]
  | 4 => [6, 6, 6, 14, 2, 4, 24, 10, 4, 6, 2, 4, 2, 2, 76, 2, 4, 4, 2, 2, 4, 14, 4, 4, 2]
  | 5 => [4, 4, 2, 20, 6, 2, 4, 10, 2, 2, 6, 20, 2, 10, 2, 2, 4, 6, 4, 46, 2, 6, 4, 14, 6]
  | 6 => [4, 14, 2, 24, 2, 2, 10, 2, 4, 6, 6, 4, 4, 14, 2, 4, 6, 2, 10, 36, 14, 4, 2, 2, 6]
  | 7 => [2, 10, 6, 2, 6, 4, 14, 2, 24, 6, 2, 4, 6, 2, 36, 2, 20, 24, 2, 6, 10, 6, 2, 24, 2]
  | 8 => [6, 6, 14, 2, 10, 6, 4, 4, 2, 2, 4, 24, 6, 10, 2, 2, 4, 6, 2, 6, 2, 4, 4, 2, 10]
  | 9 => [24, 14, 2, 4, 2, 2, 6, 2, 10, 46, 36, 14, 4, 2, 36, 6, 6, 2, 4, 2, 10, 4, 80, 2, 6]
  | 10 => [2, 6, 6, 2, 6, 4, 6, 14, 4, 2, 2, 6, 6, 4, 6, 24, 4, 10, 20, 2, 6, 6, 2, 4, 50]
  | 11 => [6, 4, 2, 10, 10, 2, 4, 24, 2, 2, 6, 14, 2, 4, 6, 14, 4, 2, 4, 10, 2, 14, 4, 2, 2]
  | 12 => [6, 14, 2, 10, 6, 2, 4, 2, 2, 46, 6, 10, 34, 14, 2, 4, 14, 6, 10, 2, 2, 4, 2, 4, 6]
  | 13 => [2, 4, 4, 2, 2, 4, 6, 4, 34, 20, 2, 6, 2, 10, 10, 2, 24, 4, 140, 2, 10, 6, 6, 60, 2]
  | 14 => [4, 10, 6, 2, 6, 20, 4, 4, 2, 6, 4, 6, 2, 4, 20, 2, 34, 20, 2, 66, 2, 4, 4, 14, 2]
  | 15 => [4, 6, 2, 4, 2, 6, 4, 60, 2, 10, 2, 4, 6, 24, 20, 4, 6, 2, 4, 6, 4, 4, 2, 10, 6]
  | 16 => [60, 6, 4, 2, 2, 4, 6, 4, 10, 2, 2, 10, 2, 2, 10, 6, 4, 4, 2, 10, 10, 24, 10, 144, 6]
  | 17 => [2, 6, 2, 2, 10, 2, 4, 6, 60, 6, 10, 36, 2, 154, 2, 2, 6, 2, 20, 36, 6, 4, 4, 14, 50]
  | 18 => [6, 6, 2, 4, 2, 14, 4, 6, 2, 6, 14, 6, 4, 2, 36, 6, 20, 2, 4, 2, 4, 10, 2, 14, 10]
  | 19 => [2, 6, 4, 14, 6, 34, 66, 2, 4, 2, 6, 6, 2, 4, 36, 2, 14, 6, 14, 2, 4, 6, 2, 10, 36]
  | 20 => [4, 4, 6, 2, 6, 2, 6, 4, 2, 2, 4, 14, 10, 24, 2, 2, 4, 6, 2, 60, 20, 4, 4, 2, 2]
  | 21 => [4, 24, 10, 4, 2, 2, 24, 14, 2, 6, 14, 4, 6, 200, 6, 24, 14, 2, 64, 2, 2, 10, 2, 10, 46]
  | 22 => [2, 4, 4, 2, 10, 66, 6, 2, 10, 20, 2, 4, 6, 2, 6, 20, 24, 4, 24, 20, 6, 6, 4, 10, 2]
  | 23 => [2, 36, 6, 4, 6, 2, 10, 24, 50, 2, 4, 20, 4, 4, 2, 6, 6, 2, 4, 10, 2, 4, 64, 14, 2]
  | 24 => [4, 6, 14, 4, 66, 2, 4, 2, 20, 10, 2, 34, 4, 2, 2, 4, 24, 2, 34, 6, 14, 24, 6, 2, 190]
  | 25 => [14, 4, 34, 2, 6, 6, 14, 6, 4, 50, 4, 4, 2, 2, 6, 2, 6, 10, 2, 2, 4, 6, 2, 4, 2]
  | 26 => [2, 10, 2, 10, 6, 6, 6, 6, 2, 2, 6, 20, 2, 10, 20, 4, 4, 6, 4, 6, 6, 4, 4, 14, 10]
  | 27 => [4, 14, 4, 4, 2, 4, 6, 2, 4, 6, 2, 14, 24, 14, 2, 6, 6, 4, 10, 36, 6, 10, 20, 2, 276]
  | 28 => [20, 4, 10, 2, 6, 4, 14, 6, 10, 6, 2, 4, 2, 2, 6, 2, 6, 6, 2, 10, 4, 24, 2, 24, 2]
  | 29 => [2, 4, 6, 2, 10, 14, 6, 4, 90, 2, 4, 14, 6, 24, 2, 2, 4, 2, 2, 6, 2, 6, 46, 2, 6]
  | 30 => [4, 6, 10, 4, 2, 4, 4, 14, 80, 10, 2, 10, 10, 20, 2, 10, 6, 4, 60, 80, 2, 4, 14, 2, 36]
  | 31 => [2, 6, 6, 2, 20, 4, 6, 2, 24, 2, 10, 6, 36, 2, 6, 2, 4, 4, 90, 6, 90, 14, 2, 4, 2]
  | 32 => [6, 4, 2, 2, 36, 2, 64, 10, 2, 2, 10, 14, 2, 4, 6, 4, 34, 2, 4, 60, 50, 14, 6, 20, 6]
  | 33 => [4, 6, 2, 10, 350, 2, 4, 2, 2, 36, 14, 4, 4, 60, 6, 4, 14, 6, 4, 6, 2, 34, 2, 2, 6]
  | 34 => [6, 20, 4, 2, 20, 46, 24, 46, 34, 2, 2, 6, 14, 14, 6, 2, 4, 4, 14, 2, 24, 20, 2, 4, 6]
  | 35 => [2, 10, 50, 2, 6, 24, 6, 4, 50, 10, 4, 6, 2, 10, 36, 2, 6, 2, 2, 6, 20, 4, 36, 90, 2]
  | 36 => [6, 6, 4, 10, 2, 6, 4, 50, 4, 6, 2, 4, 10, 14, 2, 4, 6, 10, 4, 6, 6, 34, 2, 4, 6]
  | 37 => [14, 10, 10, 104, 2, 4, 6, 2, 24, 2, 2, 34, 2, 2, 66, 24, 10, 4, 2, 6, 4, 14, 6, 10, 2]
  | 38 => [10, 4, 2, 24, 6, 2, 4, 34, 20, 6, 10, 14, 4, 4, 2, 2, 4, 14, 10, 6, 6, 6, 34, 2, 2]
  | 39 => [10, 6, 4, 4, 6, 4, 4, 6, 4, 46, 2, 4, 4, 2, 10, 6, 60, 2, 90, 20, 2, 34, 2, 2, 6]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def smallPrimeProduct : ℕ := 2577426147548683169379880845613862450845254401055092509543183257270179188707233718999293223417932941038924189941484105421516996015467418326179536384362799440729804187886824533414953001905801090622787969540076319408964006230

private theorem product_eq : primorial 547 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 547 then n.Prime else n ≤ 300000 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 547
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 300000 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 547 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 548 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ fac.dvd_primorial_iff.mpr small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let n := 25 * i + j.val + 4
  let x := witness i j
  let y := n - x
  0 < x ∧ 0 < y ∧ x + y = n ∧ Certified (3*x-1) ∧ Certified (3*x+1) ∧ Certified (x*y-1)

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

end PrimeProductWitness

open PrimeProductWitness

theorem OMA.solution : OMA.R_oeis_a220431_R1.H1 := by
  intro n hlo hhi
  let i := (n - 4) / 25
  let j : Fin 25 := ⟨(n - 4) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 40 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 4 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hx, hy, hsum, h1, h2, h3⟩ := h
  exact ⟨witness i j, n - witness i j, hx, hy, hsum,
    primeOfCertified h1, primeOfCertified h2, primeOfCertified h3⟩