import FormalConjectures.ErdosProblems.«1095»
import Mathlib

/-!
# Reduction of the Erdős–Lacampagne–Selfridge lower conjecture

The target asks for `g k ≥ exp (c * k / log k)` eventually, where `g k` is the least `n > k+1`
such that every prime factor of `n.choose k` exceeds `k`.

The literature route (ELS93, and Konyagin's proof in the other direction) is a sieve on the
*residue classes of `n` modulo the prime powers up to `k`*: `p ∤ n.choose k` exactly when, in base
`p`, adding `k` and `n - k` produces no carry, i.e. `k % p^i ≤ n % p^i` for every `i`. So a lower
bound for `g` is a statement that every `n` below the threshold fails one of these tests for some
prime power `p^i ≤ k`.

`H1` below is that statement, restricted to the `n` that the two forced-divisibility identities
(proved here as `shifted_divisor`) allow the sieve to see; the restriction is what makes it strictly
weaker than the target. `H2` is the nonemptiness half of the *known* result EES74
(`g k ≤ exp ((1+o(1)) k)`), i.e. that such an `n` exists at all: without it `g k` is `sInf ∅ = 0`.
The `main` proof below is the combinatorial bridge: it is `shifted_divisor` (a `n.choose k`-good `n`
satisfies the two congruences) plus the no-carry criterion `prime_avoids_iff` plus the `sInf`
bookkeeping.
-/

namespace OMA.R_Erdos1095_erdos_1095_variants_lower_conjecture_R1

open Nat hiding log
open Real Filter
open scoped Topology

/-- The lower sieve, restricted to the class of `n` that carry the two forced divisors of
`n.choose k` coming from consecutive shifts: below the threshold `exp (c * k / log k)` some prime
power `p^i ≤ k` has a smaller residue than `k` does, so `p` divides `n.choose k`. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
    ∀ n : ℕ, k + 1 < n →
      Nat.gcd k.factorial (k + 1) ∣ n + 1 →
      Nat.gcd k.factorial ((k + 2).choose 2) ∣ (n + 2).choose 2 →
      log n < c * ((k : ℝ) / log k) →
      ∃ p i : ℕ, p.Prime ∧ p ^ i ≤ k ∧ n % (p ^ i) < k % (p ^ i)

/-- Nonemptiness of the defining set of `g`, eventually: some `n > k+1` has all prime factors of
`n.choose k` above `k`. This is the existence half of EES74 (`g k ≤ exp ((1+o(1)) k)`), a known
result whose formalization is the sibling target `upper_conjecture`. -/
def H2 : Prop :=
  ∀ᶠ k : ℕ in atTop, ∃ n : ℕ, k + 1 < n ∧ k < (n.choose k).minFac

/-- Adding `k` and `n - k` in base `q` produces no carry exactly when `k % q ≤ n % q`. -/
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

/-- `n.choose k` is not divisible by `p` exactly when no carry occurs in base `p`
(Kummer/Legendre: the exponent of `p` is the number of carries). -/
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

/-- Consecutive shifts give forced divisors of the binomial polynomials in `n`: if `n.choose k` is
`k`-rough then `gcd k! (k+j).choose j` divides `(n+j).choose j`. -/
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

/-- A `k`-rough binomial coefficient forces `k % p^i ≤ n % p^i` for every prime `p ≤ k` and every
power `i`: the elements of the defining set of `g` pass all the prime-power tests up to `k`. -/
lemma no_carry_of_good {n k p : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hgood : k < (n.choose k).minFac) (hpk : p ≤ k) : ∀ i : ℕ, k % (p^i) ≤ n % (p^i) := by
  refine (prime_avoids_iff hp hkn).1 fun hd ↦ ?_
  have := Nat.minFac_le_of_dvd hp.two_le hd
  omega

/-- A nonempty defining set is attained by its infimum, so `g k` itself is a witness. -/
lemma g_mem {k : ℕ} (h : ∃ n : ℕ, k + 1 < n ∧ k < (n.choose k).minFac) :
    Erdos1095.g k ∈ {m : ℕ | k + 1 < m ∧ k < (m.choose k).minFac} := by
  exact Nat.sInf_mem ⟨h.choose, h.choose_spec⟩

theorem main : H1 → H2 →
    type_of% @Erdos1095.erdos_1095.variants.lower_conjecture := by
  rintro ⟨c, hc, hlow⟩ hne
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlow, hne, eventually_ge_atTop 2] with k hlowk hnek hk
  have hmemset := g_mem (k := k) hnek
  obtain ⟨hgk, hgf⟩ := hmemset
  show (Erdos1095.g k : ℝ) ≥ exp (c * (k : ℝ) / log k)
  by_contra hcon
  have hlt : (Erdos1095.g k : ℝ) < exp (c * (k : ℝ) / log k) := lt_of_not_ge hcon
  have hpos : (0 : ℝ) < (Erdos1095.g k : ℝ) := by exact_mod_cast (show 0 < Erdos1095.g k by omega)
  have hloglt : log (Erdos1095.g k) < c * ((k : ℝ) / log k) := by
    have h := log_lt_log hpos hlt
    rw [log_exp, mul_div_assoc] at h
    exact h
  have hd1 : Nat.gcd k.factorial (k + 1) ∣ Erdos1095.g k + 1 := by
    simpa only [Nat.choose_one_right] using
      shifted_divisor (k := k) (n := Erdos1095.g k) (by omega) (by omega : k < Erdos1095.g k) hgf 1
  have hd2 : Nat.gcd k.factorial ((k + 2).choose 2) ∣ (Erdos1095.g k + 2).choose 2 :=
    shifted_divisor (k := k) (n := Erdos1095.g k) (by omega) (by omega : k < Erdos1095.g k) hgf 2
  obtain ⟨p, i, hp, hpi, hbad⟩ := hlowk _ hgk hd1 hd2 hloglt
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp only [pow_zero, Nat.mod_one] at hbad
    omega
  have hpk : p ≤ k := (Nat.le_self_pow hi0 p).trans hpi
  have hdvd : p ∣ (Erdos1095.g k).choose k := by
    by_contra hnd
    exact absurd hbad (not_lt.mpr ((prime_avoids_iff hp (by omega)).1 hnd i))
  have := (Nat.minFac_le_of_dvd hp.two_le hdvd).trans hpk
  omega

end OMA.R_Erdos1095_erdos_1095_variants_lower_conjecture_R1
