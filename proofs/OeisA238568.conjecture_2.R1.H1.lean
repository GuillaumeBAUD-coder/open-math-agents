import OMAReductions.R_OeisA238568_conjecture_2_R1

-- Step OeisA238568.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA238568.conjecture_2.R1
-- Credit: @ishaanzee
-- Proof: a verified trial-division primality test (divisors below 42, correct below 42^2) replaces
-- Nat.Prime and Nat.primeCounting in the definition of a(n) for n <= 41; the seven values are then
-- checked by kernel reduction.

namespace A238568Aux

/-- Trial division by `2, …, 41`; decides primality below `42 ^ 2 = 1764`. -/
def isPrimeB (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range 42).all (fun m => decide (m < 2) || decide (n < m * m) || n % m != 0)

lemma isPrimeB_iff (n : ℕ) (h : n < 1764) : isPrimeB n = true ↔ n.Prime := by
  unfold isPrimeB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, hall⟩
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hnp : ¬ n.Prime := fun hp => hne hp.minFac_eq
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hm2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
    have hm42 : n.minFac < 42 := by nlinarith
    have hdvd := Nat.minFac_dvd n
    rcases hall n.minFac hm42 with (h' | h') | h'
    · omega
    · nlinarith
    · exact h' (Nat.mod_eq_zero_of_dvd hdvd)
  · intro hp
    refine ⟨hp.two_le, fun m _ => ?_⟩
    by_cases hm2 : m < 2
    · exact Or.inl (Or.inl hm2)
    by_cases hmn : n < m * m
    · exact Or.inl (Or.inr hmn)
    refine Or.inr (fun hmod => ?_)
    rcases hp.eq_one_or_self_of_dvd m (Nat.dvd_of_mod_eq_zero hmod) with h' | h'
    · omega
    · subst h'
      nlinarith

/-- Prime counting below `1764` through `isPrimeB`. -/
def fastPi (x : ℕ) : ℕ := ((Finset.range (x + 1)).filter (fun m => isPrimeB m = true)).card

lemma pi_eq (x : ℕ) (hx : x < 1764) : Nat.primeCounting x = fastPi x := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range, fastPi]
  congr 1
  apply Finset.filter_congr
  intro m hm
  rw [Finset.mem_range] at hm
  exact (isPrimeB_iff m (by omega)).symm

/-- `OeisA238568.a` computed through `isPrimeB`. -/
def fastA (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter (fun k => isPrimeB (n ^ 2 - fastPi (k * n)) = true)).card

lemma a_eq (n : ℕ) (hn : n ≤ 41) : OeisA238568.a n = fastA n := by
  unfold OeisA238568.a fastA
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hkn : k * n < 1764 := by nlinarith
  rw [pi_eq (k * n) hkn]
  have : n ^ 2 - fastPi (k * n) < 1764 := by
    have : n ^ 2 ≤ 41 ^ 2 := Nat.pow_le_pow_left hn 2
    omega
  exact (isPrimeB_iff _ this).symm

end A238568Aux

open A238568Aux

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA238568_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rw [a_eq _ (by norm_num)]; decide +kernel)
