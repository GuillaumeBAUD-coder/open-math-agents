import OMAReductions.R_Erdos470_erdos_470_parts_ii_R2

-- Step Erdos470.erdos_470.parts.ii.R2.H1: hypothesis H1 of reduction Erdos470.erdos_470.parts.ii.R2
-- Credit: @OrangeHeadz
-- For primes p, q above N = 2^(k+1), p different from q, let D = (N - 1) * (p + 1) * (q + 1) - N * p * q
-- be the abundance of n = 2^k * p * q. If 0 < D < q and D mod p >= N then n is primitive weird.
--
-- Proof. A set of proper divisors of n sums to n exactly when its complement sums to D. As D < q the
-- complement consists of divisors of 2^k * p; the ones divisible by p sum to a multiple of p and the
-- others are distinct divisors of 2^k, with sum below N < p. So the complement sum has residue
-- below N mod p, which D does not. Every proper divisor of n divides n / 2, n / p or n / q, none of
-- which is abundant since p, q > N.

namespace OMA470

open Finset

lemma geom_two (j : ℕ) : (∑ i ∈ range (j + 1), 2 ^ i) + 1 = 2 ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (j + 1)]
    omega

lemma sigma_two_pow (j : ℕ) : (∑ d ∈ (2 ^ j).divisors, d) + 1 = 2 ^ (j + 1) := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  exact geom_two j

lemma sigma_prime {p : ℕ} (hp : p.Prime) : ∑ d ∈ p.divisors, d = p + 1 := by
  rw [Nat.Prime.sum_divisors hp]

lemma abundant_iff (n : ℕ) : n.Abundant ↔ 2 * n < ∑ d ∈ n.divisors, d := by
  rw [Nat.Abundant, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

lemma sigma_mul_le (d e : ℕ) (he : 0 < e) :
    (∑ x ∈ d.divisors, x) * e ≤ ∑ x ∈ (d * e).divisors, x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  rw [Finset.sum_mul]
  calc ∑ x ∈ d.divisors, x * e = ∑ y ∈ d.divisors.image (fun x => x * e), y := by
        rw [Finset.sum_image]
        intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_right he h
    _ ≤ ∑ x ∈ (d * e).divisors, x := by
        apply Finset.sum_le_sum_of_subset
        intro y hy
        simp only [Finset.mem_image, Nat.mem_divisors] at hy ⊢
        obtain ⟨x, ⟨hx, _⟩, rfl⟩ := hy
        exact ⟨Nat.mul_dvd_mul_right hx e, by positivity⟩

lemma not_abundant_of_mul {d e m : ℕ} (hm : 0 < m) (hde : d * e = m)
    (h : ∑ x ∈ m.divisors, x ≤ 2 * m) : ¬ d.Abundant := by
  rw [abundant_iff]
  subst hde
  have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have h1 := sigma_mul_le d e he
  intro hab
  have h2 : (2 * d + 1) * e ≤ (∑ x ∈ d.divisors, x) * e := Nat.mul_le_mul_right e hab
  nlinarith

/-- sum of divisors of `2 ^ j * p` -/
lemma sigma_two_pow_mul_prime (j : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ d ∈ (2 ^ j * p).divisors, d = (2 ^ (j + 1) - 1) * (p + 1) := by
  have hc : Nat.Coprime (2 ^ j) p :=
    Nat.Coprime.pow_left j ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  rw [Nat.Coprime.sum_divisors_mul hc, sigma_prime hp]
  have := sigma_two_pow j
  congr 1
  omega

lemma sigma_two_pow_mul_prime_mul_prime (j : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    ∑ d ∈ (2 ^ j * p * q).divisors, d = (2 ^ (j + 1) - 1) * (p + 1) * (q + 1) := by
  have hc1 : Nat.Coprime (2 ^ j) q :=
    Nat.Coprime.pow_left j ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have hc2 : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hc : Nat.Coprime (2 ^ j * p) q := Nat.Coprime.mul_left hc1 hc2
  rw [Nat.Coprime.sum_divisors_mul hc, sigma_prime hq, sigma_two_pow_mul_prime j hp hp2]

/-- `2 ^ j * p` is not abundant when `2 ^ (j + 1) < p`. -/
lemma sigma_two_pow_mul_prime_le (j : ℕ) {p : ℕ} (hp : p.Prime) (h : 2 ^ (j + 1) < p) :
    ∑ d ∈ (2 ^ j * p).divisors, d ≤ 2 * (2 ^ j * p) := by
  have hpos : 0 < 2 ^ (j + 1) := by positivity
  have hp2 : p ≠ 2 := by
    intro h2
    have : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [sigma_two_pow_mul_prime j hp hp2]
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ (j + 1) = M + 1 := ⟨2 ^ (j + 1) - 1, by omega⟩
  have e : 2 * (2 ^ j * p) = 2 ^ (j + 1) * p := by rw [pow_succ]; ring
  rw [e, hM]
  rw [hM] at h
  simp only [Nat.add_sub_cancel]
  nlinarith

lemma two_le_two_pow_succ (k : ℕ) : 2 ≤ 2 ^ (k + 1) := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `2 ^ j * p * q` is not abundant when `2 ^ (j + 2) < p, q`. -/
lemma sigma_half_le (j : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : 2 ^ (j + 2) < p) (h2 : 2 ^ (j + 2) < q) :
    ∑ d ∈ (2 ^ j * p * q).divisors, d ≤ 2 * (2 ^ j * p * q) := by
  have h4 : 2 ≤ 2 ^ (j + 1) := two_le_two_pow_succ j
  have h5 : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  rw [sigma_two_pow_mul_prime_mul_prime j hp hq (by omega) (by omega) hpq]
  obtain ⟨L, hL⟩ : ∃ L, 2 ^ (j + 1) = L + 1 := ⟨2 ^ (j + 1) - 1, by omega⟩
  have e : 2 * (2 ^ j * p * q) = 2 ^ (j + 1) * p * q := by rw [pow_succ]; ring
  rw [e, hL]
  simp only [Nat.add_sub_cancel]
  obtain ⟨a, rfl⟩ : ∃ a, p = 2 * L + 3 + a := ⟨p - (2 * L + 3), by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = 2 * L + 3 + b := ⟨q - (2 * L + 3), by omega⟩
  nlinarith [Nat.zero_le (a * b), Nat.zero_le (L * a), Nat.zero_le (L * b), Nat.zero_le (L * L)]

/-- residues of subset sums of divisors of `2 ^ k * p` -/
lemma subset_sum_mod (k : ℕ) {p : ℕ} (hp : p.Prime) (h : 2 ^ (k + 1) < p) (t : Finset ℕ)
    (ht : ∀ x ∈ t, x ∣ 2 ^ k * p) : (∑ x ∈ t, x) % p < 2 ^ (k + 1) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not t (fun x => p ∣ x) (fun x => x)
  have h1 : p ∣ ∑ x ∈ t.filter (fun x => p ∣ x), x :=
    Finset.dvd_sum (fun x hx => (Finset.mem_filter.1 hx).2)
  have h2 : ∑ x ∈ t.filter (fun x => ¬ p ∣ x), x ≤ ∑ x ∈ (2 ^ k).divisors, x := by
    apply Finset.sum_le_sum_of_subset
    intro x hx
    obtain ⟨hxt, hxp⟩ := Finset.mem_filter.1 hx
    have hcop : Nat.Coprime x p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hxp).symm
    exact Nat.mem_divisors.2 ⟨hcop.dvd_of_dvd_mul_right (ht x hxt), by positivity⟩
  have h3 := sigma_two_pow k
  obtain ⟨c, hc⟩ := h1
  rw [← hsplit, hc, Nat.mul_add_mod]
  have hlt : ∑ x ∈ t.filter (fun x => ¬ p ∣ x), x < p := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

theorem criterion (k p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hNp : 2 ^ (k + 1) < p)
    (hNq : 2 ^ (k + 1) < q) (hpq : p ≠ q)
    (hpos : 2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1))
    (hlt : (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) < 2 ^ (k + 1) * p * q + q)
    (hmod : 2 ^ (k + 1) ≤ ((2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q) % p) :
    Erdos470.PrimitiveWeird (2 ^ k * p * q) := by
  have hN2 : 2 ≤ 2 ^ (k + 1) := two_le_two_pow_succ k
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hsig := sigma_two_pow_mul_prime_mul_prime k hp hq hp2 hq2 hpq
  have h2n : 2 * (2 ^ k * p * q) = 2 ^ (k + 1) * p * q := by rw [pow_succ]; ring
  have hnpos : 0 < 2 ^ k * p * q := by
    have := hp.pos; have := hq.pos; positivity
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- abundant
    rw [abundant_iff, hsig, h2n]
    exact hpos
  · -- not pseudoperfect
    rintro ⟨-, s, hs, hsum⟩
    set n := 2 ^ k * p * q with hn
    set t := n.properDivisors \ s with ht
    have hP : ∑ x ∈ n.divisors, x = (∑ x ∈ n.properDivisors, x) + n :=
      Nat.sum_divisors_eq_sum_properDivisors_add_self
    have hts : (∑ x ∈ t, x) + ∑ x ∈ s, x = ∑ x ∈ n.properDivisors, x := Finset.sum_sdiff hs
    have htsum : ∑ x ∈ t, x =
        (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q := by omega
    have htq : ∀ x ∈ t, x ∣ 2 ^ k * p := by
      intro x hx
      have hxle : x ≤ ∑ y ∈ t, y := Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx
      have hxP : x ∈ n.properDivisors := (Finset.mem_sdiff.1 hx).1
      have hxn : x ∣ n := (Nat.mem_properDivisors.1 hxP).1
      have hx0 : 0 < x := Nat.pos_of_dvd_of_pos hxn hnpos
      have hnq : ¬ q ∣ x := fun hqx => by
        have := Nat.le_of_dvd hx0 hqx
        omega
      have hcop : Nat.Coprime x q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hnq).symm
      exact hcop.dvd_of_dvd_mul_right hxn
    have := subset_sum_mod k hp hNp t htq
    rw [htsum] at this
    omega
  · -- primitive
    intro d hd hw
    obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.1 hd
    obtain ⟨e, he⟩ := hdn
    have he1 : e ≠ 1 := by rintro rfl; omega
    obtain ⟨e', he'⟩ := Nat.minFac_dvd e
    have hr : (e.minFac).Prime := Nat.minFac_prime he1
    set r := e.minFac with hrdef
    have hfac : 2 ^ k * p * q = d * e' * r := by rw [he, he']; ring
    have hrn : r ∣ 2 ^ k * p * q := ⟨d * e', by rw [hfac]; ring⟩
    rcases (Nat.Prime.dvd_mul hr).1 hrn with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · -- r = 2
        have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
          rcases k with _ | j
          · rw [hr2] at h; norm_num at h
          · exact ⟨j, rfl⟩
        have hm : d * e' = 2 ^ j * p * q := by
          have : d * e' * 2 = (2 ^ j * p * q) * 2 := by
            have h' := hfac
            rw [hr2] at h'
            rw [← h', pow_succ]; ring
          exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
        have hmpos : 0 < 2 ^ j * p * q := by
          have := hp.pos; have := hq.pos; positivity
        exact not_abundant_of_mul hmpos hm (sigma_half_le j hp hq hpq hNp hNq) hw.1
      · -- r = p
        have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 h
        have hm : d * e' = 2 ^ k * q := by
          have : d * e' * p = (2 ^ k * q) * p := by
            have h' := hfac
            rw [hrp] at h'
            rw [← h']; ring
          exact Nat.eq_of_mul_eq_mul_right hp.pos this
        have hmpos : 0 < 2 ^ k * q := by
          have := hq.pos; positivity
        exact not_abundant_of_mul hmpos hm (sigma_two_pow_mul_prime_le k hq hNq) hw.1
    · -- r = q
      have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).1 h
      have hm : d * e' = 2 ^ k * p := by
        have : d * e' * q = (2 ^ k * p) * q := by
          have h' := hfac
          rw [hrq] at h'
          rw [← h']
        exact Nat.eq_of_mul_eq_mul_right hq.pos this
      have hmpos : 0 < 2 ^ k * p := by
        have := hp.pos; positivity
      exact not_abundant_of_mul hmpos hm (sigma_two_pow_mul_prime_le k hp hNp) hw.1

end OMA470

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R2.H1 := by
  intro k p q hp hq hNp hNq hpq hpos hlt hmod
  exact OMA470.criterion k p q hp hq hNp hNq hpq hpos hlt hmod
