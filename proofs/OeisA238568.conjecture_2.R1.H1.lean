import OMAReductions.R_OeisA238568_conjecture_2_R1

namespace H1BoundedDivisors

def primeTest (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ d ∈ Finset.Icc 2 (Nat.sqrt n), ¬ d ∣ n

instance (n : ℕ) : Decidable (primeTest n) := by
  unfold primeTest
  infer_instance

theorem primeTest_iff (n : ℕ) : primeTest n ↔ Nat.Prime n := by
  simp only [primeTest, Nat.prime_def_le_sqrt, Finset.mem_Icc]
  aesop

def countPrimes (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter primeTest).card

theorem countPrimes_eq (n : ℕ) : countPrimes n = Nat.primeCounting n := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  unfold countPrimes
  congr 1
  exact Finset.filter_congr fun _ _ => primeTest_iff _

def countCandidates (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k => primeTest (n ^ 2 - countPrimes (k * n))).card

theorem countCandidates_eq (n : ℕ) : countCandidates n = OeisA238568.a n := by
  unfold countCandidates OeisA238568.a
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [countPrimes_eq]
  exact primeTest_iff _

end H1BoundedDivisors

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem OMA.solution : OMA.R_OeisA238568_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rw [← H1BoundedDivisors.countCandidates_eq]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
