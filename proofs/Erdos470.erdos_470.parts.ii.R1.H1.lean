import OMAReductions.R_Erdos470_erdos_470_parts_ii_R1

-- Step Erdos470.erdos_470.parts.ii.R1.H1: hypothesis H1 of reduction Erdos470.erdos_470.parts.ii.R1
-- Credit: @OrangeHeadz
-- Melfi 2015, Theorem 1 (sharpened size condition): two primes p = 2^(k+2) - a and q = 2^(k+2) + b
-- with b + 3 < a and a * (a + b) < 2^(k+2) give the primitive weird number 2^k * p * q.
--
-- Proof. Put N = 2^(k+1). Both primes are odd, so a = b + 4 + 2 * h. The sum of divisors of
-- n = 2^k * p * q is (N - 1) * (p + 1) * (q + 1), which gives the abundance
--   D = sigma(n) - 2 * n = N * (2 * h + 1) + (a - 1) * (b + 1) > 0.
-- A set of proper divisors of n sums to n exactly when its complement sums to D. Any sum of distinct
-- divisors of n has the form A0 + p * B + q * C with A0 < N (the part coprime to p * q consists of
-- distinct divisors of 2^k). With m = B + C such a sum lies in [m * p, m * q + N), and
-- h * q + N <= D < (h + 1) * p, so D is not of this form and n is not pseudoperfect.
-- Every proper divisor of n divides n / 2, n / p or n / q, none of which is abundant since p, q > N.

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

/-- No proper divisor of `2 ^ k * p * q` is abundant when `2 ^ (k + 1) < p, q`. -/
lemma no_abundant_proper_divisor (k p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hNp : 2 ^ (k + 1) < p) (hNq : 2 ^ (k + 1) < q) (hpq : p ≠ q) :
    ∀ d ∈ (2 ^ k * p * q).properDivisors, ¬ d.Abundant := by
  intro d hd hw
  obtain ⟨hdn, hdlt⟩ := Nat.mem_properDivisors.1 hd
  obtain ⟨e, he⟩ := hdn
  have he1 : e ≠ 1 := by rintro rfl; omega
  obtain ⟨f, hf⟩ := Nat.minFac_dvd e
  have hr : (e.minFac).Prime := Nat.minFac_prime he1
  set r := e.minFac with hrdef
  have hfac : 2 ^ k * p * q = d * f * r := by rw [he, hf]; ring
  have hrn : r ∣ 2 ^ k * p * q := ⟨d * f, by rw [hfac]; ring⟩
  rcases (Nat.Prime.dvd_mul hr).1 hrn with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · have hr2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
        rcases k with _ | j
        · rw [hr2] at h; norm_num at h
        · exact ⟨j, rfl⟩
      have hm : d * f = 2 ^ j * p * q := by
        have : d * f * 2 = (2 ^ j * p * q) * 2 := by
          have hfac2 := hfac
          rw [hr2] at hfac2
          rw [← hfac2, pow_succ]; ring
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
      have hmpos : 0 < 2 ^ j * p * q := by
        have := hp.pos; have := hq.pos; positivity
      exact not_abundant_of_mul hmpos hm (sigma_half_le j hp hq hpq hNp hNq) hw
    · have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 h
      have hm : d * f = 2 ^ k * q := by
        have : d * f * p = (2 ^ k * q) * p := by
          have hfac2 := hfac
          rw [hrp] at hfac2
          rw [← hfac2]; ring
        exact Nat.eq_of_mul_eq_mul_right hp.pos this
      have hmpos : 0 < 2 ^ k * q := by
        have := hq.pos; positivity
      exact not_abundant_of_mul hmpos hm (sigma_two_pow_mul_prime_le k hq hNq) hw
  · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).1 h
    have hm : d * f = 2 ^ k * p := by
      have : d * f * q = (2 ^ k * p) * q := by
        have hfac2 := hfac
        rw [hrq] at hfac2
        rw [← hfac2]
      exact Nat.eq_of_mul_eq_mul_right hq.pos this
    have hmpos : 0 < 2 ^ k * p := by
      have := hp.pos; positivity
    exact not_abundant_of_mul hmpos hm (sigma_two_pow_mul_prime_le k hp hNp) hw

/-- A sum of distinct divisors of `2 ^ k * p * q` is `A0 + p * B + q * C` with `A0 < 2 ^ (k + 1)`. -/
lemma three_split (k : ℕ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (t : Finset ℕ)
    (ht : ∀ x ∈ t, x ∣ 2 ^ k * p * q) :
    ∃ A0 B C : ℕ, ∑ x ∈ t, x = A0 + p * B + q * C ∧ A0 < 2 ^ (k + 1) := by
  have hs1 := Finset.sum_filter_add_sum_filter_not t (fun x => p ∣ x) (fun x => x)
  have hs2 := Finset.sum_filter_add_sum_filter_not (t.filter (fun x => ¬ p ∣ x))
    (fun x => q ∣ x) (fun x => x)
  have h1 : p ∣ ∑ x ∈ t.filter (fun x => p ∣ x), x :=
    Finset.dvd_sum (fun x hx => (Finset.mem_filter.1 hx).2)
  have h2 : q ∣ ∑ x ∈ (t.filter (fun x => ¬ p ∣ x)).filter (fun x => q ∣ x), x :=
    Finset.dvd_sum (fun x hx => (Finset.mem_filter.1 hx).2)
  have h3 : ∑ x ∈ (t.filter (fun x => ¬ p ∣ x)).filter (fun x => ¬ q ∣ x), x
      ≤ ∑ x ∈ (2 ^ k).divisors, x := by
    apply Finset.sum_le_sum_of_subset
    intro x hx
    obtain ⟨hx1, hxq⟩ := Finset.mem_filter.1 hx
    obtain ⟨hxt, hxp⟩ := Finset.mem_filter.1 hx1
    have hcq : Nat.Coprime x q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hxq).symm
    have hcp : Nat.Coprime x p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hxp).symm
    have hd1 : x ∣ 2 ^ k * p := hcq.dvd_of_dvd_mul_right (ht x hxt)
    exact Nat.mem_divisors.2 ⟨hcp.dvd_of_dvd_mul_right hd1, by positivity⟩
  have h4 := sigma_two_pow k
  obtain ⟨B, hB⟩ := h1
  obtain ⟨C, hC⟩ := h2
  refine ⟨∑ x ∈ (t.filter (fun x => ¬ p ∣ x)).filter (fun x => ¬ q ∣ x), x, B, C, ?_, by omega⟩
  rw [← hs1, ← hs2, hB, hC]
  ring

/-- The abundance is not of the form `A0 + P * B + Q * C`. -/
lemma melfi_arith (N a b h P Q A0 B C D : ℤ) (ha : a = b + 4 + 2 * h) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hP : P = 2 * N - a) (hQ : Q = 2 * N + b) (hsz : a * (a + b) < 2 * N)
    (hD : D = N * (2 * h + 1) + (a - 1) * (b + 1))
    (hA0n : 0 ≤ A0) (hA0 : A0 < N) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hrep : D = A0 + P * B + Q * C) : False := by
  have ha4 : 4 ≤ a := by linarith
  have haN : a < 2 * N := by nlinarith
  have hPpos : 0 < P := by linarith
  have hPQ : P ≤ Q := by linarith
  have hQpos : 0 < Q := by linarith
  have hbh : 0 ≤ b * h := mul_nonneg hb hh
  have hbb : 0 ≤ b * b := mul_nonneg hb hb
  have hhh : 0 ≤ h * h := mul_nonneg hh hh
  rcases le_or_gt (B + C) h with hm | hm
  · have h1 : P * B ≤ Q * B := mul_le_mul_of_nonneg_right hPQ hB
    have h2 : Q * (B + C) ≤ Q * h := mul_le_mul_of_nonneg_left hm hQpos.le
    have h3 : D ≤ A0 + Q * h := by rw [hrep]; nlinarith
    rw [hD, hQ, ha] at h3
    nlinarith
  · have h1 : P * C ≤ Q * C := mul_le_mul_of_nonneg_right hPQ hC
    have h2 : P * (h + 1) ≤ P * (B + C) := mul_le_mul_of_nonneg_left (by linarith) hPpos.le
    have h3 : P * (h + 1) ≤ D := by rw [hrep]; nlinarith
    have key : 2 * ((a - 1) * (b + 1) + a * (h + 1)) = a * (a + b) - 2 * b - 2 := by
      rw [ha]; ring
    rw [hD, hP] at h3
    nlinarith

theorem melfi (k a b p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpX : p + a = 2 ^ (k + 2))
    (hqX : q = 2 ^ (k + 2) + b) (hab : b + 3 < a) (hsize : a * (a + b) < 2 ^ (k + 2)) :
    Erdos470.PrimitiveWeird (2 ^ k * p * q) := by
  have hN2 : 2 ≤ 2 ^ (k + 1) := two_le_two_pow_succ k
  have hX : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ 2 (k + 1)]; ring
  have h4a : 4 * a ≤ a * (a + b) := by nlinarith
  have hNp : 2 ^ (k + 1) < p := by omega
  have hNq : 2 ^ (k + 1) < q := by omega
  have hpq : p ≠ q := by omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  obtain ⟨u, hu⟩ := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨v, hv⟩ := hq.eq_two_or_odd'.resolve_left hq2
  obtain ⟨h, hh⟩ : ∃ h, a = b + 4 + 2 * h := ⟨(a - b - 4) / 2, by omega⟩
  have hsig := sigma_two_pow_mul_prime_mul_prime k hp hq hp2 hq2 hpq
  have h2n : 2 * (2 ^ k * p * q) = 2 ^ (k + 1) * p * q := by rw [pow_succ]; ring
  have hnpos : 0 < 2 ^ k * p * q := by
    have := hp.pos; have := hq.pos; positivity
  have hprim := no_abundant_proper_divisor k p q hp hq hNp hNq hpq
  have hsplit := three_split k hp hq
  -- from here on only `N = 2 ^ (k + 1)` matters
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ (k + 1) = N := ⟨_, rfl⟩
  rw [hN] at hN2 hX hsig h2n hsplit
  rw [hX] at hpX hqX hsize
  have hsigZ : ((∑ d ∈ (2 ^ k * p * q).divisors, d : ℕ) : ℤ)
      = ((N : ℤ) - 1) * ((p : ℤ) + 1) * ((q : ℤ) + 1) := by
    rw [hsig]; push_cast [Nat.cast_sub (show 1 ≤ N by omega)]; ring
  have hPZ : (p : ℤ) = 2 * (N : ℤ) - (a : ℤ) := by
    have : (p : ℤ) + (a : ℤ) = 2 * (N : ℤ) := by exact_mod_cast hpX
    linarith
  have hQZ : (q : ℤ) = 2 * (N : ℤ) + (b : ℤ) := by exact_mod_cast hqX
  have haZ : (a : ℤ) = (b : ℤ) + 4 + 2 * (h : ℤ) := by exact_mod_cast hh
  have hszZ : (a : ℤ) * ((a : ℤ) + (b : ℤ)) < 2 * (N : ℤ) := by exact_mod_cast hsize
  have h2nZ : ((2 * (2 ^ k * p * q) : ℕ) : ℤ) = (N : ℤ) * (p : ℤ) * (q : ℤ) := by
    rw [h2n]; push_cast; ring
  have hDZ : ((∑ d ∈ (2 ^ k * p * q).divisors, d : ℕ) : ℤ) - ((2 * (2 ^ k * p * q) : ℕ) : ℤ)
      = (N : ℤ) * (2 * (h : ℤ) + 1) + ((a : ℤ) - 1) * ((b : ℤ) + 1) := by
    rw [hsigZ, h2nZ, hPZ, hQZ, haZ]; ring
  have hbZ : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
  have hhZ : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  have hNZ : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- abundant
    rw [abundant_iff]
    have hpos : (0 : ℤ) < (N : ℤ) * (2 * (h : ℤ) + 1) + ((a : ℤ) - 1) * ((b : ℤ) + 1) := by
      have h1 : (0 : ℤ) < (N : ℤ) * (2 * (h : ℤ) + 1) := by positivity
      have h2 : (0 : ℤ) ≤ ((a : ℤ) - 1) * ((b : ℤ) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    rw [← hDZ] at hpos
    have : ((2 * (2 ^ k * p * q) : ℕ) : ℤ) < ((∑ d ∈ (2 ^ k * p * q).divisors, d : ℕ) : ℤ) := by
      linarith
    exact_mod_cast this
  · -- not pseudoperfect
    rintro ⟨-, s, hs, hsum⟩
    have hP : ∑ x ∈ (2 ^ k * p * q).divisors, x
        = (∑ x ∈ (2 ^ k * p * q).properDivisors, x) + 2 ^ k * p * q :=
      Nat.sum_divisors_eq_sum_properDivisors_add_self
    have hts : (∑ x ∈ (2 ^ k * p * q).properDivisors \ s, x) + ∑ x ∈ s, x
        = ∑ x ∈ (2 ^ k * p * q).properDivisors, x := Finset.sum_sdiff hs
    have htsum : (∑ x ∈ (2 ^ k * p * q).properDivisors \ s, x) + 2 * (2 ^ k * p * q)
        = ∑ x ∈ (2 ^ k * p * q).divisors, x := by omega
    have htd : ∀ x ∈ (2 ^ k * p * q).properDivisors \ s, x ∣ 2 ^ k * p * q := fun x hx =>
      (Nat.mem_properDivisors.1 (Finset.mem_sdiff.1 hx).1).1
    obtain ⟨A0, B, C, hrep, hA0⟩ := hsplit _ htd
    have hrepZ : ((∑ x ∈ (2 ^ k * p * q).divisors, x : ℕ) : ℤ) - ((2 * (2 ^ k * p * q) : ℕ) : ℤ)
        = (A0 : ℤ) + (p : ℤ) * (B : ℤ) + (q : ℤ) * (C : ℤ) := by
      rw [← htsum, hrep]; push_cast; ring
    exact melfi_arith (N : ℤ) (a : ℤ) (b : ℤ) (h : ℤ) (p : ℤ) (q : ℤ) (A0 : ℤ) (B : ℤ) (C : ℤ) _
      haZ hbZ hhZ hPZ hQZ hszZ hDZ (Int.natCast_nonneg A0) (by exact_mod_cast hA0)
      (Int.natCast_nonneg B)
      (Int.natCast_nonneg C) hrepZ
  · -- primitive
    intro d hd hw
    exact hprim d hd hw.1

end OMA470

theorem OMA.solution : OMA.R_Erdos470_erdos_470_parts_ii_R1.H1 := by
  intro k a b hab hsize hp hq
  have ha : a < 2 ^ (k + 2) := by nlinarith
  exact OMA470.melfi k a b (2 ^ (k + 2) - a) (2 ^ (k + 2) + b) hp hq (by omega) rfl hab hsize
