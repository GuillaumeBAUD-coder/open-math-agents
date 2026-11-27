import OMAReductions.R_Erdos470_erdos_470_parts_ii_R3

/-!
# Proof of `Erdos470.erdos_470.parts.ii.R3.H1`

Let `M = 2^(k+1)` and let `p ≠ q` be primes larger than `M`. If `N = 2^k p q` is abundant
(`M p q < (M - 1)(p + 1)(q + 1)`) and its excess `E = σ(N) - 2 N` does not lie in any block
`[b p + c q, b p + c q + M)` for `b, c < M`, then `N` is primitive weird:
1. `N` is abundant by the multiplicativity of the divisor sum `σ`.
2. `E < p q`, so no subset of proper divisors of `N` summing to `E` can contain any multiple
   of `p q`, forcing `E = a + b p + c q` with `a, b, c < M`, contradicting the hypothesis.
3. Every proper divisor of `N` divides `2^k q`, `2^k p`, or (when `k ≥ 1`) `2^(k-1) p q`,
   each of which is non-abundant since `p, q > M`; hence no proper divisor is weird.
-/

namespace Erdos470R3H1Proof

private lemma sum_divisors_two_pow (k : ℕ) :
    ∑ d ∈ (2 ^ k).divisors, d = 2 ^ (k + 1) - 1 := by
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (m + 1 + 1) = 2 ^ (m + 1) + 2 ^ (m + 1) := by ring
    omega

private lemma sum_divisors_prime {p : ℕ} (hp : p.Prime) :
    ∑ d ∈ p.divisors, d = p + 1 := by
  rw [hp.divisors, Finset.sum_pair hp.ne_one.symm]
  ring

private lemma sum_divisors_mul_coprime {a b : ℕ} (h : a.Coprime b) :
    ∑ d ∈ (a * b).divisors, d = (∑ d ∈ a.divisors, d) * (∑ d ∈ b.divisors, d) := by
  have h1 := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have h2 := h1.map_mul_of_coprime h
  simpa [ArithmeticFunction.sigma_apply] using h2

private lemma coprime_two_pow_prime {k p : ℕ} (hp : p.Prime) (hgt : 2 ^ (k + 1) < p) :
    (2 ^ k).Coprime p := by
  apply Nat.Coprime.pow_left
  refine (hp.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hpow : 2 ≤ 2 ^ (k + 1) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]; omega
  omega

private lemma sum_divisors_2pow_p_q {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpM : 2 ^ (k + 1) < p) (hqM : 2 ^ (k + 1) < q) (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ k * p * q).divisors, d = (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) := by
  have hcp : (2 ^ k).Coprime p := coprime_two_pow_prime hp hpM
  have hcq : (2 ^ k).Coprime q := coprime_two_pow_prime hq hqM
  have hpqc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have h2pq : (2 ^ k * p).Coprime q := hcq.mul_left hpqc
  rw [sum_divisors_mul_coprime h2pq, sum_divisors_mul_coprime hcp,
    sum_divisors_two_pow, sum_divisors_prime hp, sum_divisors_prime hq]

private lemma sum_subset_divisors_two_pow_lt {k : ℕ} {S : Finset ℕ}
    (hS : ∀ d ∈ S, d ∣ 2 ^ k) : ∑ d ∈ S, d < 2 ^ (k + 1) := by
  have hsub : S ⊆ (2 ^ k).divisors := fun d hd =>
    Nat.mem_divisors.mpr ⟨hS d hd, by positivity⟩
  have hle : ∑ d ∈ S, d ≤ ∑ d ∈ (2 ^ k).divisors, d :=
    Finset.sum_le_sum_of_subset hsub
  rw [sum_divisors_two_pow] at hle
  have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  omega

private lemma dvd_two_pow_of_dvd_mul_coprime {k p q d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hd : d ∣ 2 ^ k * p * q)
    (hnp : ¬ p ∣ d) (hnq : ¬ q ∣ d) : d ∣ 2 ^ k := by
  have hcp : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hnp).symm
  have hcq : d.Coprime q := (hq.coprime_iff_not_dvd.mpr hnq).symm
  have h1 : d ∣ 2 ^ k * p := hcq.dvd_of_dvd_mul_right hd
  exact hcp.dvd_of_dvd_mul_right h1

private lemma not_abundant_2pow_prime {k p : ℕ} (hp : p.Prime) (hpM : 2 ^ (k + 1) < p) :
    ¬ (2 ^ k * p).Abundant := by
  rw [Nat.abundant_iff_sum_divisors]
  have hcp : (2 ^ k).Coprime p := coprime_two_pow_prime hp hpM
  rw [sum_divisors_mul_coprime hcp, sum_divisors_two_pow, sum_divisors_prime hp]
  have hM : 2 ≤ 2 ^ (k + 1) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]; omega
  have h2k : 2 * (2 ^ k * p) = 2 ^ (k + 1) * p := by rw [pow_succ]; ring
  rw [h2k]
  zify [show 1 ≤ 2 ^ (k + 1) by omega]
  nlinarith

private lemma not_abundant_half {k p q : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime)
    (hpM : 2 ^ (k + 1) < p) (hqM : 2 ^ (k + 1) < q) (hpq : p ≠ q) :
    ¬ (2 ^ (k - 1) * p * q).Abundant := by
  rw [Nat.abundant_iff_sum_divisors]
  have hpow_eq : k - 1 + 1 = k := by omega
  have hpM' : 2 ^ (k - 1 + 1) < p := by
    rw [hpow_eq]
    have : 2 ^ k < 2 ^ (k + 1) := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]; omega
    omega
  have hqM' : 2 ^ (k - 1 + 1) < q := by
    rw [hpow_eq]
    have : 2 ^ k < 2 ^ (k + 1) := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]; omega
    omega
  rw [sum_divisors_2pow_p_q hp hq hpM' hqM' hpq, hpow_eq]
  have h2k : 2 * (2 ^ (k - 1) * p * q) = 2 ^ k * p * q := by
    have hpow2 : 2 * 2 ^ (k - 1) = 2 ^ k := by
      conv_rhs => rw [← hpow_eq, pow_succ]
      ring
    calc 2 * (2 ^ (k - 1) * p * q) = (2 * 2 ^ (k - 1)) * p * q := by ring
      _ = 2 ^ k * p * q := by rw [hpow2]
  rw [h2k]
  have h2k_pos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hp2 : 2 * 2 ^ k < p := by rw [pow_succ] at hpM; omega
  have hq2 : 2 * 2 ^ k < q := by rw [pow_succ] at hqM; omega
  zify [h2k_pos]
  nlinarith

private lemma dvd_two_pow_pred_of_lt {k m : ℕ} (hdvd : m ∣ 2 ^ k) (hlt : m < 2 ^ k) :
    1 ≤ k ∧ m ∣ 2 ^ (k - 1) := by
  obtain ⟨j, hjle, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hjlt : j < k := by
    by_contra hge
    have hjeq : j = k := by omega
    subst hjeq
    omega
  refine ⟨by omega, ?_⟩
  exact Nat.pow_dvd_pow 2 (by omega)

end Erdos470R3H1Proof

open Erdos470R3H1Proof in
theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R3.H1 := by
  intro k p q hp hq hpM hqM hpq habund hblock
  set N := 2 ^ k * p * q with hN_def
  have hN_pos : 0 < N := by
    have : 0 < 2 ^ k := by positivity
    have : 0 < p := hp.pos
    have : 0 < q := hq.pos
    positivity
  have hN_ne : N ≠ 0 := by omega
  have h2N : 2 * N = 2 ^ (k + 1) * p * q := by
    rw [hN_def, pow_succ]; ring
  have hsigma : ∑ d ∈ N.divisors, d = (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) :=
    sum_divisors_2pow_p_q hp hq hpM hqM hpq
  have hAbund : N.Abundant := by
    rw [Nat.abundant_iff_sum_divisors, h2N, hsigma]
    exact habund
  have hNotPseudo : ¬ N.Pseudoperfect := by
    rintro ⟨_, s, hs, hssum⟩
    set t := N.properDivisors \ s
    have hsum_prop : ∑ d ∈ N.properDivisors, d + N = ∑ d ∈ N.divisors, d := by
      have hdiv : insert N N.properDivisors = N.divisors := Nat.insert_self_properDivisors hN_ne
      have hnot : N ∉ N.properDivisors := fun h => lt_irrefl N (Nat.mem_properDivisors.mp h).2
      rw [← hdiv, Finset.sum_insert hnot]
      ring
    have hst : ∑ d ∈ t, d + ∑ d ∈ s, d = ∑ d ∈ N.properDivisors, d :=
      Finset.sum_sdiff hs
    set E := (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q
    have htsum : ∑ d ∈ t, d = E := by
      have : ∑ d ∈ t, d + 2 * N = ∑ d ∈ N.divisors, d := by omega
      rw [h2N, hsigma] at this
      omega
    have hE_lt_pq : E < p * q := by
      dsimp only [E]
      have hM1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      have hle : 2 ^ (k + 1) * p * q ≤ (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) := le_of_lt habund
      zify [hM1, hle]
      nlinarith
    have hno_pq : ∀ d ∈ t, ¬ (p ∣ d ∧ q ∣ d) := by
      intro d hd ⟨hpd, hqd⟩
      have hpqc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
      have hpqd : p * q ∣ d := hpqc.mul_dvd_of_dvd_of_dvd hpd hqd
      have hd_mem : d ∈ N.properDivisors := (Finset.mem_sdiff.mp hd).1
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd_mem).1 hN_pos
      have hpq_le_d : p * q ≤ d := Nat.le_of_dvd hd_pos hpqd
      have hd_le_sum : d ≤ ∑ x ∈ t, x := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
      omega
    let t0 := t.filter fun d => ¬ p ∣ d ∧ ¬ q ∣ d
    let tp := t.filter fun d => p ∣ d ∧ ¬ q ∣ d
    let tq := t.filter fun d => ¬ p ∣ d ∧ q ∣ d
    have hdisj0p : Disjoint t0 tp := by
      rw [Finset.disjoint_left]
      intro d hd0 hdp
      exact (Finset.mem_filter.mp hd0).2.1 (Finset.mem_filter.mp hdp).2.1
    have hdisj0pq : Disjoint (t0 ∪ tp) tq := by
      rw [Finset.disjoint_left]
      intro d hd0p hdq
      rcases Finset.mem_union.mp hd0p with hd0 | hdp
      · exact (Finset.mem_filter.mp hd0).2.2 (Finset.mem_filter.mp hdq).2.2
      · exact (Finset.mem_filter.mp hdp).2.2 (Finset.mem_filter.mp hdq).2.2
    have hunion : t = (t0 ∪ tp) ∪ tq := by
      ext d
      simp only [t0, tp, tq, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hd
        have hnpq := hno_pq d hd
        by_cases hpd : p ∣ d <;> by_cases hqd : q ∣ d
        · exact absurd ⟨hpd, hqd⟩ hnpq
        · exact Or.inl (Or.inr ⟨hd, hpd, hqd⟩)
        · exact Or.inr ⟨hd, hpd, hqd⟩
        · exact Or.inl (Or.inl ⟨hd, hpd, hqd⟩)
      · rintro ((⟨hd, _⟩ | ⟨hd, _⟩) | ⟨hd, _⟩) <;> exact hd
    have hsplit : E = (∑ d ∈ t0, d) + (∑ d ∈ tp, d) + (∑ d ∈ tq, d) := by
      rw [← htsum, hunion, Finset.sum_union hdisj0pq, Finset.sum_union hdisj0p]
    have ha_lt : ∑ d ∈ t0, d < 2 ^ (k + 1) := by
      apply sum_subset_divisors_two_pow_lt
      intro d hd
      have hdt := (Finset.mem_filter.mp hd).1
      have hdvd : d ∣ N := (Nat.mem_properDivisors.mp (Finset.mem_sdiff.mp hdt).1).1
      exact dvd_two_pow_of_dvd_mul_coprime hp hq hdvd
        (Finset.mem_filter.mp hd).2.1 (Finset.mem_filter.mp hd).2.2
    have htp_sum : ∑ d ∈ tp, d = (∑ d ∈ tp.image (· / p), d) * p := by
      rw [Finset.sum_mul, Finset.sum_image]
      · refine Finset.sum_congr rfl fun d hd => ?_
        exact (Nat.div_mul_cancel (Finset.mem_filter.mp hd).2.1).symm
      · intro d1 hd1 d2 hd2 heq
        dsimp only at heq
        have h1 := Nat.div_mul_cancel (Finset.mem_filter.mp hd1).2.1
        have h2 := Nat.div_mul_cancel (Finset.mem_filter.mp hd2).2.1
        rw [← h1, ← h2, heq]
    have hb_lt : ∑ d ∈ tp.image (· / p), d < 2 ^ (k + 1) := by
      apply sum_subset_divisors_two_pow_lt
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨d, hd, rfl⟩
      have hdt := (Finset.mem_filter.mp hd).1
      have hdvd : d ∣ N := (Nat.mem_properDivisors.mp (Finset.mem_sdiff.mp hdt).1).1
      have hpd : p ∣ d := (Finset.mem_filter.mp hd).2.1
      have hnqd : ¬ q ∣ d := (Finset.mem_filter.mp hd).2.2
      have hmul : (d / p) * p ∣ (2 ^ k * q) * p := by
        rw [Nat.div_mul_cancel hpd]
        convert hdvd using 1; rw [hN_def]; ring
      have hdq : d / p ∣ 2 ^ k * q := (mul_dvd_mul_iff_right hp.ne_zero).mp hmul
      have hnqm : ¬ q ∣ d / p := fun hqdiv =>
        hnqd (dvd_trans hqdiv (Nat.div_dvd_of_dvd hpd))
      have hcq : (d / p).Coprime q := (hq.coprime_iff_not_dvd.mpr hnqm).symm
      exact hcq.dvd_of_dvd_mul_right hdq
    have htq_sum : ∑ d ∈ tq, d = (∑ d ∈ tq.image (· / q), d) * q := by
      rw [Finset.sum_mul, Finset.sum_image]
      · refine Finset.sum_congr rfl fun d hd => ?_
        exact (Nat.div_mul_cancel (Finset.mem_filter.mp hd).2.2).symm
      · intro d1 hd1 d2 hd2 heq
        dsimp only at heq
        have h1 := Nat.div_mul_cancel (Finset.mem_filter.mp hd1).2.2
        have h2 := Nat.div_mul_cancel (Finset.mem_filter.mp hd2).2.2
        rw [← h1, ← h2, heq]
    have hc_lt : ∑ d ∈ tq.image (· / q), d < 2 ^ (k + 1) := by
      apply sum_subset_divisors_two_pow_lt
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨d, hd, rfl⟩
      have hdt := (Finset.mem_filter.mp hd).1
      have hdvd : d ∣ N := (Nat.mem_properDivisors.mp (Finset.mem_sdiff.mp hdt).1).1
      have hnpd : ¬ p ∣ d := (Finset.mem_filter.mp hd).2.1
      have hqd : q ∣ d := (Finset.mem_filter.mp hd).2.2
      have hmul : (d / q) * q ∣ (2 ^ k * p) * q := by
        rw [Nat.div_mul_cancel hqd]
        exact hdvd
      have hdp : d / q ∣ 2 ^ k * p := (mul_dvd_mul_iff_right hq.ne_zero).mp hmul
      have hnpm : ¬ p ∣ d / q := fun hpdiv =>
        hnpd (dvd_trans hpdiv (Nat.div_dvd_of_dvd hqd))
      have hcp : (d / q).Coprime p := (hp.coprime_iff_not_dvd.mpr hnpm).symm
      exact hcp.dvd_of_dvd_mul_right hdp
    apply hblock (∑ d ∈ tp.image (· / p), d) (∑ d ∈ tq.image (· / q), d) hb_lt hc_lt
    rw [htp_sum, htq_sum] at hsplit
    omega
  refine ⟨⟨hAbund, hNotPseudo⟩, fun d hd hweird => ?_⟩
  have hda : d.Abundant := hweird.1
  obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
  by_cases hpd : p ∣ d
  · by_cases hqd : q ∣ d
    · have hpqc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
      have hpqd : p * q ∣ d := hpqc.mul_dvd_of_dvd_of_dvd hpd hqd
      obtain ⟨m, rfl⟩ := hpqd
      have hm_dvd : m ∣ 2 ^ k := by
        have h1 : m * (p * q) ∣ 2 ^ k * (p * q) := by
          convert hdvd using 1 <;> ring
        exact (mul_dvd_mul_iff_right (mul_ne_zero hp.ne_zero hq.ne_zero)).mp h1
      have hm_lt : m < 2 ^ k := by
        have h1 : m * (p * q) < 2 ^ k * (p * q) := by
          convert hdlt using 1 <;> ring
        exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
      obtain ⟨hk1, hmpred⟩ := dvd_two_pow_pred_of_lt hm_dvd hm_lt
      have hd_half : p * q * m ∣ 2 ^ (k - 1) * p * q := by
        obtain ⟨c, hc⟩ := hmpred
        exact ⟨c, by rw [hc]; ring⟩
      have hne_half : 2 ^ (k - 1) * p * q ≠ 0 := by
        have : 0 < 2 ^ (k - 1) := by positivity
        have : 0 < p := hp.pos
        have : 0 < q := hq.pos
        positivity
      exact not_abundant_half hk1 hp hq hpM hqM hpq (hda.of_dvd hd_half hne_half)
    · have hcq : d.Coprime q := (hq.coprime_iff_not_dvd.mpr hqd).symm
      have hd_2kp : d ∣ 2 ^ k * p := hcq.dvd_of_dvd_mul_right hdvd
      have hne_2kp : 2 ^ k * p ≠ 0 := mul_ne_zero (by positivity) hp.ne_zero
      exact not_abundant_2pow_prime hp hpM (hda.of_dvd hd_2kp hne_2kp)
  · have hcp : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
    have hd_2kq : d ∣ 2 ^ k * q := by
      have h1 : d ∣ (2 ^ k * q) * p := by convert hdvd using 1; ring
      exact hcp.dvd_of_dvd_mul_right h1
    have hne_2kq : 2 ^ k * q ≠ 0 := mul_ne_zero (by positivity) hq.ne_zero
    exact not_abundant_2pow_prime hq hqM (hda.of_dvd hd_2kq hne_2kq)
