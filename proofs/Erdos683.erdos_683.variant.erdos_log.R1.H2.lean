import OMAReductions.R_Erdos683_erdos_683_variant_erdos_log_R1
import Mathlib

-- Step Erdos683.erdos_683.variant.erdos_log.R1.H2: hypothesis H2 of reduction Erdos683.erdos_683.variant.erdos_log.R1
-- Credit: @ivillar (original proof), following Erdos [Er55d]; uses the lemma le_P of the reduction file.
-- Strategy. If every prime factor of C(n,k) were below y = k log k / 20, then with m the number of
-- prime factors: (n/(2k))^k <= C(n,k) <= n^m (prime powers dividing C(n,k) are at most n), and
-- m! <= prod of those primes <= primorial(y) <= 4^y. With k^3 < n^2 the first gives m > k/4, and then
-- m log m <= m + y log 4 forces log k < 4, contradicting log k >= 20.

namespace OMA.Erdos683H2

open Finset

lemma card_factorial_le_prod : ∀ S : Finset ℕ, (∀ a ∈ S, 0 < a) → S.card.factorial ≤ ∏ a ∈ S, a := by
  intro S
  refine Finset.induction_on_max S (by simp) ?_
  intro a s hlt ih hS
  have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
  rw [card_insert_of_notMem ha, prod_insert ha, Nat.factorial_succ]
  have hs : ∀ x ∈ s, 0 < x := fun x hx => hS x (mem_insert_of_mem hx)
  have hcard : s.card + 1 ≤ a := by
    have hsub : s ⊆ Icc 1 (a - 1) := by
      intro x hx
      rw [mem_Icc]
      have h1 := hs x hx
      have h2 := hlt x hx
      omega
    have h3 := card_le_card hsub
    rw [Nat.card_Icc] at h3
    have h4 := hS a (mem_insert_self a s)
    omega
  exact Nat.mul_le_mul hcard (ih hs)

end OMA.Erdos683H2

open Finset in
theorem OMA.solution : OMA.R_Erdos683_erdos_683_variant_erdos_log_R1.H2 := by
  intro n k hk hkn hk3
  by_contra hcon
  push Not at hcon
  set y : ℝ := (k : ℝ) * Real.log k / 20 with hy
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 20) hk
  have hk1 : 0 < k := by exact_mod_cast hkpos
  have hlogk : 20 ≤ Real.log k := by
    rw [← Real.log_exp 20]
    exact Real.log_le_log (Real.exp_pos 20) hk
  have h2k : 2 * k ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hC0 : n.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  -- the binomial coefficient is at most n ^ m
  have hCle : n.choose k ≤ n ^ (n.choose k).primeFactors.card := by
    have h := Nat.prod_factorization_pow_eq_self hC0
    conv_lhs => rw [← h]
    rw [Finsupp.prod, Nat.support_factorization]
    exact Finset.prod_le_pow_card _ _ _ (fun p _ => Nat.pow_factorization_choose_le hn0)
  set m := (n.choose k).primeFactors.card with hm
  -- m! is at most the primorial of y
  have hsub : (n.choose k).primeFactors ⊆ (range (⌊y⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    have hpP := OMA.R_Erdos683_erdos_683_variant_erdos_log_R1.le_P hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    rw [mem_filter, mem_range]
    refine ⟨?_, hpr⟩
    have h1 : (p : ℝ) ≤ y := le_trans (by exact_mod_cast hpP) hcon.le
    have h2 := Nat.le_floor h1
    omega
  have hfact : m.factorial ≤ 4 ^ ⌊y⌋₊ := by
    calc m.factorial ≤ ∏ p ∈ (n.choose k).primeFactors, p :=
          OMA.Erdos683H2.card_factorial_le_prod _
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
      _ ≤ ∏ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, p :=
          Finset.prod_le_prod_of_subset_of_one_le' hsub
            (fun p hp _ => (mem_filter.mp hp).2.one_lt.le)
      _ = primorial ⌊y⌋₊ := rfl
      _ ≤ 4 ^ ⌊y⌋₊ := primorial_le_four_pow _
  -- the binomial coefficient is at least (n/(2k))^k
  have hlow : ((n : ℝ) / (2 * k)) ^ k ≤ (n.choose k : ℝ) := by
    have h1 := Nat.pow_le_choose (α := ℝ) k n
    have h2 : ((k.factorial : ℕ) : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    have h2k' : (2 : ℝ) * k ≤ n := by exact_mod_cast h2k
    have h3 : (n : ℝ) / 2 ≤ ((n + 1 - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    calc ((n : ℝ) / (2 * k)) ^ k = ((n : ℝ) / 2) ^ k / (k : ℝ) ^ k := by
          rw [show (n : ℝ) / (2 * k) = ((n : ℝ) / 2) / k by ring, div_pow]
      _ ≤ ((n + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) :=
          div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 k)
            (by exact_mod_cast Nat.factorial_pos k) h2
      _ ≤ (n.choose k : ℝ) := h1
  -- logarithmic form of the three estimates
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  have hA : (k : ℝ) * Real.log ((n : ℝ) / (2 * k)) ≤ (m : ℝ) * Real.log n := by
    have h1 : ((n : ℝ) / (2 * k)) ^ k ≤ (n : ℝ) ^ m := hlow.trans (by exact_mod_cast hCle)
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow, Real.log_pow] at h2
  have hdiv : Real.log ((n : ℝ) / (2 * k)) = Real.log n - Real.log 2 - Real.log k := by
    rw [Real.log_div hN.ne' (by positivity), Real.log_mul (by norm_num) hkpos.ne']
    ring
  have hB : 3 * Real.log k < 2 * Real.log n := by
    have h1 : (k : ℝ) ^ 3 < (n : ℝ) ^ 2 := by exact_mod_cast hk3
    have h2 := Real.log_lt_log (by positivity) h1
    rwa [Real.log_pow, Real.log_pow] at h2
  have hl2 := Real.log_two_lt_d9
  have hl2p := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set a := Real.log n
  set b := Real.log k
  have ha30 : 30 < a := by linarith
  -- m > k / 4
  have hMK : (k : ℝ) < 4 * m := by
    have h1 : (k : ℝ) * (a / 3 - Real.log 2) ≤ (m : ℝ) * a := by
      rw [hdiv] at hA
      have : (k : ℝ) * (a / 3 - Real.log 2) ≤ (k : ℝ) * (a - Real.log 2 - b) :=
        mul_le_mul_of_nonneg_left (by linarith) hkpos.le
      linarith
    have h2 : (k : ℝ) * (a / 4) < (k : ℝ) * (a / 3 - Real.log 2) :=
      mul_lt_mul_of_pos_left (by linarith) hkpos
    have h3 : (k : ℝ) * a < (4 * m) * a := by linarith
    exact lt_of_mul_lt_mul_right h3 (by linarith)
  have hM : (0 : ℝ) < m := by linarith
  -- the factorial bound in logarithmic form
  have hfl : (m : ℝ) * Real.log m ≤ m + y * Real.log 4 := by
    have h1 := Real.pow_div_factorial_le_exp (m : ℝ) hM.le m
    have h2 : (m : ℝ) ^ m ≤ Real.exp m * (m.factorial : ℝ) := by
      rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos m : (0 : ℝ) < (m.factorial : ℝ))] at h1
      exact h1
    have h3 : ((m.factorial : ℕ) : ℝ) ≤ (4 : ℝ) ^ ⌊y⌋₊ := by exact_mod_cast hfact
    have h4 := Real.log_le_log (by positivity) (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h4
    have hy0 : 0 ≤ y := by positivity
    have h5 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
    have h6 : (⌊y⌋₊ : ℝ) * Real.log 4 ≤ y * Real.log 4 :=
      mul_le_mul_of_nonneg_right h5 (Real.log_nonneg (by norm_num))
    linarith
  -- log m > log k - log 4
  have hc : b - Real.log 4 < Real.log m := by
    have h1 : (k : ℝ) / 4 < m := by linarith
    have h2 := Real.log_lt_log (by positivity) h1
    rwa [Real.log_div hkpos.ne' (by norm_num)] at h2
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  -- conclude
  have hb0 : 0 < b := by linarith
  have hyb : y * Real.log 4 = (k : ℝ) * b * Real.log 4 / 20 := by rw [hy]; ring
  have h1 : (m : ℝ) * Real.log m < (m : ℝ) * (1 + b * Real.log 4 / 5) := by
    have : (k : ℝ) * b * Real.log 4 / 20 < (4 * m) * b * Real.log 4 / 20 := by
      have hL : 0 < b * Real.log 4 := mul_pos hb0 (by rw [hl4]; linarith)
      nlinarith
    nlinarith
  have h2 : Real.log m < 1 + b * Real.log 4 / 5 := lt_of_mul_lt_mul_left h1 hM.le
  have h3 : (20 : ℝ) * (5 - Real.log 4) ≤ b * (5 - Real.log 4) :=
    mul_le_mul_of_nonneg_right hlogk (by rw [hl4]; linarith)
  rw [hl4] at h2 hc h3
  nlinarith
