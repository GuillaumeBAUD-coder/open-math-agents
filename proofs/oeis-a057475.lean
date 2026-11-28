import OMAStatements.S_oeis_a057475

-- Problem: A057475: Number of k, 1 <= k <= n, such that gcd(n,k) = gcd(n+1,k) = 1.
-- Upstream: formal-conjectures statements/oeis-a057475.lean:0 (declaration OMA.S_oeis_a057475.main)
-- Credit: @pyaf (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a057475

open OMA.S_oeis_a057475

-- Primes p ≤ n not dividing n(n+1) are counted by a n.
lemma a_ge (n : ℕ) (hn : 0 < n) :
    (Nat.primesLE n).card - (n * (n + 1)).primeFactors.card ≤ a n := by
  refine le_trans (Finset.le_card_sdiff _ _) (Finset.card_le_card ?_)
  intro p hp
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primeFactors] at hp
  obtain ⟨⟨hpn, hpp⟩, hnd⟩ := hp
  have hnd' : ¬ p ∣ n * (n + 1) := fun h => hnd ⟨hpp, h, by positivity⟩
  simp only [a, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hpp.one_le, hpn⟩, ?_, ?_⟩
  · exact ((Nat.Prime.coprime_iff_not_dvd hpp).2 fun h => hnd' (dvd_mul_of_dvd_left h _)).symm
  · exact ((Nat.Prime.coprime_iff_not_dvd hpp).2 fun h => hnd' (dvd_mul_of_dvd_right h _)).symm

lemma two_pow_card_le (m : ℕ) (hm : m ≠ 0) : 2 ^ m.primeFactors.card ≤ m :=
  calc 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p :=
        Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

lemma pi_pow (j : ℕ) (hj : 1 ≤ j) : 2 ^ j - (j + 1) ≤ Nat.primeCounting (2 ^ j) * j := by
  have h := Chebyshev.pi_ge (2 ^ j)
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlog : Real.log ((2 ^ j : ℕ) : ℝ) = j * Real.log 2 := by push_cast; rw [Real.log_pow]
  have hlog1 : Real.log (((2 ^ j : ℕ) : ℝ) + 1) ≤ (j + 1) * Real.log 2 := by
    have : ((2 ^ j : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by
      push_cast; rw [pow_succ]; have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num); linarith
    calc Real.log (((2 ^ j : ℕ) : ℝ) + 1) ≤ Real.log ((2 : ℝ) ^ (j + 1)) :=
          Real.log_le_log (by positivity) this
      _ = (j + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  rw [hlog, div_le_iff₀ (by positivity)] at h
  have hle : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
  have key : ((2 ^ j : ℕ) : ℝ) - (j + 1) ≤ (Nat.primeCounting (2 ^ j) : ℝ) * j := by
    have := h.trans' (by nlinarith : (((2 ^ j : ℕ) : ℝ) - (j + 1)) * Real.log 2 ≤
      ((2 ^ j : ℕ) : ℝ) * Real.log 2 - Real.log (((2 ^ j : ℕ) : ℝ) + 1))
    nlinarith
  have : ((2 ^ j - (j + 1) : ℕ) : ℝ) ≤ ((Nat.primeCounting (2 ^ j) * j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]; push_cast at key ⊢; linarith
  exact_mod_cast this

lemma pow_big (j : ℕ) (hj : 10 ≤ j) : j * (2 * j + 51) + (j + 1) ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; nlinarith

lemma pi_big (j : ℕ) (hj : 10 ≤ j) : 2 * j + 51 ≤ Nat.primeCounting (2 ^ j) := by
  have h1 := pi_pow j (by omega)
  have h2 := pow_big j hj
  have : j * (2 * j + 51) ≤ Nat.primeCounting (2 ^ j) * j := by omega
  rw [mul_comm] at this
  exact Nat.le_of_mul_le_mul_right this (by omega)

set_option maxRecDepth 10000 in
lemma pi_512 : 69 ≤ Nat.primeCounting 512 := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  refine le_trans (le_of_eq ?_) (Finset.card_le_card (s := ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
    31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
    239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347} :
    Finset ℕ)) ?_)
  · rfl
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rw [Nat.mem_primesLE]
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma tail (n : ℕ) (hn : 512 ≤ n) : 50 ≤ a n := by
  set j := Nat.log 2 n
  have hj : 9 ≤ j := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hlo : 2 ^ j ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hpi : 2 * j + 51 ≤ (Nat.primesLE n).card := by
    rw [Nat.primesLE_card_eq_primeCounting]
    rcases hj.eq_or_lt with h9 | h10
    · rw [← h9] at hlo; have := pi_512.trans (Nat.monotone_primeCounting hlo); omega
    · exact (pi_big j h10).trans (Nat.monotone_primeCounting hlo)
  have hm : n * (n + 1) ≠ 0 := by positivity
  have hw : (n * (n + 1)).primeFactors.card ≤ 2 * j + 1 := by
    have h2 := two_pow_card_le _ hm
    have : n * (n + 1) < 2 ^ (2 * j + 2) := by
      rw [show 2 * j + 2 = (j + 1) + (j + 1) by ring, pow_add]
      nlinarith
    have := lt_of_le_of_lt h2 this
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
    omega
  have := a_ge n (by omega)
  omega

set_option maxRecDepth 100000 in
lemma small : ∀ n < 512, a n ≠ 49 := by decide +kernel

end OMA.P_oeis_a057475

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a057475.main) := by
  intro h
  obtain ⟨n, -, hn⟩ := h 49 (by norm_num)
  by_cases hs : n < 512
  · exact OMA.P_oeis_a057475.small n hs hn
  · have := OMA.P_oeis_a057475.tail n (by omega)
    omega
