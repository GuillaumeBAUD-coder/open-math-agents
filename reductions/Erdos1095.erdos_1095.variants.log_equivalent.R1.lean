import FormalConjectures.ErdosProblems.«1095»
import Mathlib.NumberTheory.Chebyshev

/-!
# A short-period reduction for the Erdős–Selfridge first hit

The lower sieve uses prime powers only up to the row index. On the upper
side a small LCM progression settles all primes up to twice k/log k.
The remaining primes have only two digit tests.
-/

namespace OMA.R_Erdos1095_erdos_1095_variants_log_equivalent_R1

open Filter Real
open scoped Asymptotics

/-- The prime powers up to k cover the initial interval above k+1 by
their forbidden residue intervals after two forced divisibility tests. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
    ∀ n : ℕ, k + 1 < n →
      Nat.gcd k.factorial (k + 1) ∣ n + 1 →
      Nat.gcd k.factorial ((k + 2).choose 2) ∣ (n + 2).choose 2 →
      log n < c * (k / log k) →
      ∃ p i : ℕ, p.Prime ∧ p ^ i ≤ k ∧ n % (p ^ i) < k % (p ^ i)

/-- On a fixed progression, find a short multiplier satisfying just the
two residue tests for primes above the cutoff. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
    let z := ⌈2 * ((k : ℝ) / log k)⌉₊
    ∃ t : ℕ, 2 ≤ t ∧ log t ≤ C * (k / log k) ∧
      ∀ p : ℕ, p.Prime → z < p → p ≤ k →
        let n := k + t * Nat.lcmUpto z ^ 4
        k % p ≤ n % p ∧ k ≤ n % (p ^ 2)

/-- Consecutive shifts give forced divisors of binomial polynomials in n.
This tests a sparse set of candidates before any prime-power search. -/
lemma shifted_divisor {n k : ℕ} (hk : 0 < k) (hn : k < n)
    (hgood : k < (n.choose k).minFac) (j : ℕ) :
    Nat.gcd k.factorial ((k+j).choose j) ∣ (n+j).choose j := by
  let d := Nat.gcd k.factorial ((k+j).choose j)
  have hn1 : n.choose k ≠ 1 := by
    intro h
    have := Nat.choose_eq_one_iff.mp h
    omega
  have hcop := (Nat.coprime_factorial_iff hn1).2 hgood
  have hd : d.Coprime (n.choose k) :=
    hcop.symm.coprime_dvd_left (Nat.gcd_dvd_left ..)
  apply hd.dvd_mul_right.mp
  have heq := Nat.choose_mul (n := n+j) (k := k+j) (s := j) (by omega)
  simp only [Nat.add_sub_cancel] at heq
  rw [← heq]
  exact (Nat.gcd_dvd_right ..).trans (dvd_mul_left _ _)

lemma no_carry_iff {n k q : ℕ} (hkn : k ≤ n) (hq : 0 < q) :
    k % q + (n - k) % q < q ↔ k % q ≤ n % q := by
  have hn : n % q = (k % q + (n-k) % q) % q := by
    rw [← Nat.add_mod, Nat.add_sub_of_le hkn]
  have ha := Nat.mod_lt k hq
  have hb := Nat.mod_lt (n-k) hq
  rw [hn]
  by_cases h : k % q + (n-k) % q < q
  · simp [h, Nat.mod_eq_of_lt h]
  · have hs : (k % q + (n-k) % q) % q = k % q + (n-k) % q - q := by
      exact (Nat.mod_eq_sub_mod (by omega)).trans (Nat.mod_eq_of_lt (by omega))
    rw [hs]
    omega

lemma prime_avoids_iff {n k p : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    ¬ p ∣ n.choose k ↔ ∀ i : ℕ, k % (p^i) ≤ n % (p^i) := by
  have hpos := Nat.choose_pos hkn
  have hf : ¬ p ∣ n.choose k ↔ (n.choose k).factorization p = 0 := by
    simp [Nat.factorization_eq_zero_iff, hp, hpos.ne']
  rw [hf]
  constructor
  · intro h i
    let b := max (Nat.log p n) i + 1
    rw [Nat.factorization_choose hp hkn (show Nat.log p n < b by dsimp [b]; omega),
      Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    by_cases hi : i = 0
    · simp [hi, Nat.mod_one]
    apply (no_carry_iff hkn (pow_pos hp.pos i)).1
    exact lt_of_not_ge (@h i (Finset.mem_Ico.mpr ⟨by omega, by dsimp [b]; omega⟩))
  · intro h
    rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _), Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro i _
    exact not_le.mpr ((no_carry_iff hkn (pow_pos hp.pos i)).2 (h i))

lemma residue_mono_of_dvd (n : ℕ) {a b : ℕ} (hab : a ∣ b) : n % a ≤ n % b := by
  rw [← Nat.mod_mod_of_dvd n hab]
  exact Nat.mod_le _ _

/-- Once a power exceeds k, passing its residue test implies every
higher-power test. -/
lemma first_power_suffices {n k p j : ℕ} (hkj : k < p^j)
    (htests : ∀ i ≤ j, k % (p^i) ≤ n % (p^i)) :
    ∀ i : ℕ, k % (p^i) ≤ n % (p^i) := by
  intro i
  by_cases h : i ≤ j
  · exact htests i h
  · have htop := htests j le_rfl
    rw [Nat.mod_eq_of_lt hkj] at htop
    exact (Nat.mod_le _ _).trans (htop.trans (residue_mono_of_dvd n (Nat.pow_dvd_pow p (by omega))))

lemma power_dvd_wheel {z p : ℕ} (hp : p.Prime) :
    p ^ (4 * Nat.log p z) ∣ Nat.lcmUpto z ^ 4 := by
  have hpow := Nat.ordProj_dvd (Nat.lcmUpto z) p
  rw [Nat.factorization_lcmUpto z hp] at hpow
  rw [mul_comm, pow_mul]
  exact pow_dvd_pow_of_dvd hpow 4

lemma wheel_clears_small {k z p t : ℕ} (hkz : k ≤ z^2) (hp : p.Prime)
    (hpz : p ≤ z) : ¬ p ∣ (k + t * Nat.lcmUpto z ^ 4).choose k := by
  have hlog : 1 ≤ Nat.log p z := by
    apply Nat.le_log_of_pow_le hp.one_lt
    simpa using hpz
  have hz := Nat.lt_pow_succ_log_self hp.one_lt z
  have hlarge : k < p ^ (4 * Nat.log p z) := calc
    k ≤ z^2 := hkz
    _ < (p ^ (Nat.log p z + 1)) ^ 2 := by gcongr
    _ ≤ _ := by rw [← pow_mul]; exact Nat.pow_le_pow_right hp.pos (by omega)
  apply (prime_avoids_iff hp (by omega)).2
  apply first_power_suffices hlarge
  intro i hi
  have hd := (Nat.pow_dvd_pow p hi).trans (power_dvd_wheel hp)
  have hd' : p^i ∣ t * Nat.lcmUpto z ^ 4 := hd.trans (dvd_mul_left _ _)
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd', Nat.add_zero, Nat.mod_mod]

lemma wheel_witness {k z t : ℕ} (hk : 0 < k) (ht : 2 ≤ t) (hkz : k ≤ z^2)
    (hbig : ∀ p : ℕ, p.Prime → z < p → p ≤ k →
      let n := k + t * Nat.lcmUpto z ^ 4
      k % p ≤ n % p ∧ k ≤ n % (p ^ 2)) :
    let n := k + t * Nat.lcmUpto z ^ 4
    k + 1 < n ∧ k < (n.choose k).minFac := by
  let n := k + t * Nat.lcmUpto z ^ 4
  have hw := Nat.lcmUpto_pos z
  have hoff : 2 ≤ t * Nat.lcmUpto z ^ 4 :=
    ht.trans (Nat.le_mul_of_pos_right _ (pow_pos hw _))
  have hn : k+1 < n := by dsimp [n]; omega
  refine ⟨hn, ?_⟩
  have hn1 : n.choose k ≠ 1 := by
    intro h
    have := Nat.choose_eq_one_iff.mp h
    omega
  let p := (n.choose k).minFac
  have hp : p.Prime := Nat.minFac_prime hn1
  change k < p
  by_contra! hpk
  have hd := Nat.minFac_dvd (n.choose k)
  change p ∣ n.choose k at hd
  by_cases hz : p ≤ z
  · exact wheel_clears_small hkz hp hz hd
  have hsq : k < p^2 := hkz.trans_lt (by gcongr; omega)
  obtain ⟨h₁, h₂⟩ := hbig p hp (by omega) hpk
  apply ((prime_avoids_iff hp (show k ≤ n by omega)).2 ?_) hd
  apply first_power_suffices hsq
  intro i hi
  interval_cases i
  · simp [Nat.mod_one]
  · simpa using h₁
  · simpa [Nat.mod_eq_of_lt hsq] using h₂

/-- The LCM progression costs only a constant times the target scale in the log. -/
lemma cutoff_estimates {k : ℕ} (hk : 2 ≤ k) :
    let s := (k : ℝ) / log k
    let z := ⌈2 * s⌉₊
    1 ≤ s ∧ k ≤ z ^ 2 ∧ log (Nat.lcmUpto z) ≤ (log 4 + 4) * (3 * s) := by
  let s := (k : ℝ) / log k
  let z := ⌈2 * s⌉₊
  have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hl := log_pos hk'
  have hs : 1 ≤ s := by
    dsimp [s]
    apply (le_div_iff₀ hl).2
    linarith [log_le_sub_one_of_pos (zero_lt_one.trans hk')]
  have hz₁ : 2*s ≤ z := Nat.le_ceil _
  have hz₂ : (z : ℝ) ≤ 3*s := by
    have : (z : ℝ) < 2*s + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ k by positivity)
  have hl' : log k ≤ 2 * √(k : ℝ) := by
    have bound := log_le_rpow_div (x := (k : ℝ)) (by positivity) (show 0 < (1:ℝ)/2 by norm_num)
    rw [← sqrt_eq_rpow] at bound
    linarith
  have hroot_z : √(k : ℝ) ≤ z := by
    apply le_trans _ hz₁
    dsimp [s]
    rw [← mul_div_assoc, le_div_iff₀ hl]
    nlinarith [mul_le_mul_of_nonneg_left hl' (Real.sqrt_nonneg k)]
  refine ⟨hs, ?_, ?_⟩
  · exact_mod_cast (show (k : ℝ) ≤ (z : ℝ)^2 by rw [← hroot]; gcongr)
  · change log (Nat.lcmUpto z) ≤ (log 4 + 4) * (3*s)
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    exact (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg z)).trans
      (mul_le_mul_of_nonneg_left hz₂ (by positivity))

lemma witness_log_bound {k z t : ℕ} (hkz : k ≤ z^2) (ht : 2 ≤ t) :
    log ((k + t * Nat.lcmUpto z ^ 4 : ℕ) : ℝ) ≤
      log 2 + log t + 4 * log (Nat.lcmUpto z) := by
  let L := Nat.lcmUpto z
  have hL : 0 < L := Nat.lcmUpto_pos z
  have hzL : z ≤ L := by
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · omega
    apply Nat.le_of_dvd hL
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hz, le_rfl⟩)
  have hkL : k ≤ L^4 := calc
    k ≤ z^2 := hkz
    _ ≤ L^2 := by gcongr
    _ ≤ L^4 := Nat.pow_le_pow_right hL (by decide)
  have hkT : k ≤ t * L^4 := hkL.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hn : k + t * L^4 ≤ 2 * t * L^4 := by nlinarith
  calc
    _ ≤ log (((2 * t * L^4 : ℕ) : ℝ)) :=
      log_le_log (by exact_mod_cast (show 0 < k + t * L^4 by positivity)) (by exact_mod_cast hn)
    _ = _ := by
      push_cast
      rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity), log_pow]
      norm_num [L]

theorem main : H1 → H2 → type_of% @Erdos1095.erdos_1095.variants.log_equivalent := by
  rintro ⟨c, hc, hlow⟩ ⟨C, hC, hhigh⟩
  let B := log 2 + C + 12 * (log 4 + 4)
  have bounds : ∀ᶠ k : ℕ in atTop,
      let s := (k : ℝ) / log k
      c * s ≤ log (Erdos1095.g k) ∧ log (Erdos1095.g k) ≤ B * s := by
    filter_upwards [eventually_ge_atTop 2, hlow, hhigh] with k hk hlo hup
    let s := (k : ℝ) / log k
    let z := ⌈2 * s⌉₊
    obtain ⟨hs, hkz, hbudget⟩ := cutoff_estimates hk
    obtain ⟨t, ht, htlog, htests⟩ := hup
    let n := k + t * Nat.lcmUpto z ^ 4
    let S : Set ℕ := {m | k+1 < m ∧ k < (m.choose k).minFac}
    have hnS : n ∈ S := wheel_witness (by omega) ht hkz htests
    have hgS : Erdos1095.g k ∈ S := Nat.sInf_mem ⟨n, hnS⟩
    obtain ⟨hgk, hgf⟩ := hgS
    have hgn : Erdos1095.g k ≤ n := Nat.sInf_le (s := S) hnS
    constructor
    · by_contra! h
      have shifts := shifted_divisor (by omega : 0 < k) (by omega : k < Erdos1095.g k) hgf
      have h₁ : Nat.gcd k.factorial (k+1) ∣ Erdos1095.g k + 1 := by
        simpa only [Nat.choose_one_right] using shifts 1
      obtain ⟨p, i, hp, hi, hbad⟩ := hlo _ hgk h₁ (shifts 2) h
      have hi0 : i ≠ 0 := by rintro rfl; simp [Nat.mod_one] at hbad
      have hpk : p ≤ k := (Nat.le_self_pow hi0 _).trans hi
      have havoid : ¬ p ∣ (Erdos1095.g k).choose k :=
        fun hd ↦ (not_le.mpr hgf) ((Nat.minFac_le_of_dvd hp.two_le hd).trans hpk)
      exact (not_lt_of_ge ((prime_avoids_iff hp (by omega)).1 havoid i)) hbad
    · have hgpos : (0 : ℝ) < Erdos1095.g k := by exact_mod_cast (show 0 < Erdos1095.g k by omega)
      have lgn : log (Erdos1095.g k) ≤ log n := log_le_log hgpos (by exact_mod_cast hgn)
      have lnt := witness_log_bound hkz ht
      change log n ≤ log 2 + log t + 4 * log (Nat.lcmUpto z) at lnt
      change log (Nat.lcmUpto z) ≤ (log 4 + 4) * (3 * s) at hbudget
      change log t ≤ C * s at htlog
      change 1 ≤ s at hs
      change log (Erdos1095.g k) ≤ B * s
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ log 2 by positivity)]
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨B, ?_⟩
    filter_upwards [bounds, eventually_ge_atTop 2] with k h hk
    have hnon := (cutoff_estimates hk).1
    simpa only [Real.norm_eq_abs, abs_of_nonneg (log_natCast_nonneg _),
      abs_of_nonneg (show 0 ≤ (k : ℝ) / log k by linarith)] using h.2
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨c⁻¹, ?_⟩
    filter_upwards [bounds, eventually_ge_atTop 2] with k h hk
    have hnon := (cutoff_estimates hk).1
    simp only [Real.norm_eq_abs, abs_of_nonneg (log_natCast_nonneg _),
      abs_of_nonneg (show 0 ≤ (k : ℝ) / log k by linarith)]
    change (k : ℝ) / log k ≤ c⁻¹ * log (Erdos1095.g k)
    rw [← div_eq_inv_mul, le_div_iff₀ hc, mul_comm]
    exact h.1

end OMA.R_Erdos1095_erdos_1095_variants_log_equivalent_R1
