import FormalConjectures.OEIS.«193279»

/-!
# Even perfect numbers: every number up to `n` is a sum of distinct proper divisors

By the Euclid-Euler theorem, an even perfect number is `n = 2 ^ k * p` with `p = 2 ^ (k + 1) - 1`
prime. Its proper divisors include `1, 2, ..., 2 ^ k` and `p, 2 * p, ..., 2 ^ (k - 1) * p`.
For `m < n`, write `m = q * p + r` with `r < p < 2 ^ (k + 1)` and `q < 2 ^ k`; the binary digits
of `r` and `q` pick out disjoint sets of these divisors with sums `r` and `q * p`. The whole set
of proper divisors sums to `n`, and no subset sum exceeds `n`. So the subset sums are exactly
`0, 1, ..., n`, and `a n = n`.

The Euclid-Euler part follows `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`
from Mathlib's `Archive/Wiedijk100Theorems/PerfectNumbers.lean`, which proofs here cannot import.
-/

namespace OMA.A193279

open ArithmeticFunction Finset

open scoped sigma

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n)
    (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

lemma lt_of_two_pow_le_lt {i r k : ℕ} (h1 : 2 ^ i ≤ r) (h2 : r < 2 ^ k) : i < k := by
  by_contra h
  have : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Every `m ≤ 2 ^ k * p` is a sum of distinct proper divisors of `2 ^ k * p`, where
`p = 2 ^ (k + 1) - 1` is an odd prime. -/
lemma exists_subset_sum {k p : ℕ} (hp : p.Prime) (hp1 : p + 1 = 2 ^ (k + 1)) (hk : k ≠ 0)
    {m : ℕ} (hm : m < 2 ^ k * p) :
    ∃ u ⊆ (2 ^ k * p).properDivisors, ∑ x ∈ u, x = m := by
  have hk4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp3 : 3 ≤ p := by omega
  have hppos : 0 < p := by omega
  set q := m / p with hq
  set r := m % p with hr
  have hqlt : q < 2 ^ k := by
    rw [hq, Nat.div_lt_iff_lt_mul hppos]
    exact hm
  have hrlt : r < 2 ^ (k + 1) := by
    have := Nat.mod_lt m hppos
    omega
  let U1 : Finset ℕ := r.bitIndices.toFinset.image (fun i => 2 ^ i)
  let U2 : Finset ℕ := q.bitIndices.toFinset.image (fun i => 2 ^ i * p)
  have hinj1 : Set.InjOn (fun i : ℕ => 2 ^ i) (r.bitIndices.toFinset : Set ℕ) :=
    fun i _ j _ h => Nat.pow_right_injective le_rfl h
  have hinj2 : Set.InjOn (fun i : ℕ => 2 ^ i * p) (q.bitIndices.toFinset : Set ℕ) := by
    intro i _ j _ h
    exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hppos h)
  have hs1 : ∑ x ∈ U1, x = r := by
    rw [Finset.sum_image hinj1]
    exact Finset.sum_toFinset_bitIndices_two_pow r
  have hs2 : ∑ x ∈ U2, x = q * p := by
    rw [Finset.sum_image hinj2, ← Finset.sum_mul, Finset.sum_toFinset_bitIndices_two_pow q]
  have hsub1 : U1 ⊆ (2 ^ k * p).properDivisors := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.1 hi)
    have hik : i ≤ k := by have := lt_of_two_pow_le_lt hi' hrlt; omega
    rw [Nat.mem_properDivisors]
    refine ⟨Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 hik) p, ?_⟩
    calc 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hik
      _ < 2 ^ k * p := by
        have : 0 < 2 ^ k := by positivity
        nlinarith
  have hsub2 : U2 ⊆ (2 ^ k * p).properDivisors := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.1 hi)
    have hik : i < k := lt_of_two_pow_le_lt hi' hqlt
    rw [Nat.mem_properDivisors]
    refine ⟨Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 hik.le) p, ?_⟩
    have : 2 ^ i < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hik
    exact Nat.mul_lt_mul_of_pos_right this hppos
  have hdisj : Disjoint U1 U2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx1
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx2
    have hdvd : p ∣ 2 ^ i := ⟨2 ^ j, by rw [← hj, mul_comm]⟩
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hdvd)
    omega
  refine ⟨U1 ∪ U2, Finset.union_subset hsub1 hsub2, ?_⟩
  rw [Finset.sum_union hdisj, hs1, hs2, hr, hq, mul_comm]
  exact Nat.mod_add_div m p

end OMA.A193279

theorem OMA.solution : type_of% @OeisA193279.a_eq_self_of_perfect_of_even := by
  intro n hperf heven
  obtain ⟨k, hpr, rfl⟩ := OMA.A193279.eq_two_pow_mul_prime_mersenne_of_even_perfect heven hperf
  have hk := OMA.A193279.ne_zero_of_prime_mersenne k hpr
  have hp1 : mersenne (k + 1) + 1 = 2 ^ (k + 1) := succ_mersenne (k + 1)
  set p := mersenne (k + 1)
  have hsum : ∑ i ∈ (2 ^ k * p).properDivisors, i = 2 ^ k * p :=
    (Nat.perfect_iff_sum_properDivisors hperf.2).1 hperf
  have himage : (2 ^ k * p).properDivisors.powerset.image (fun s : Finset ℕ => ∑ x ∈ s, x) =
      Finset.range (2 ^ k * p + 1) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hu
      rw [hsum] at this
      omega
    · intro hm
      rcases Nat.lt_or_ge m (2 ^ k * p) with hlt | hge
      · exact OMA.A193279.exists_subset_sum hpr hp1 hk hlt
      · exact ⟨_, Finset.Subset.refl _, by rw [hsum]; omega⟩
  rw [OeisA193279.a, himage, Finset.card_range]
  omega
