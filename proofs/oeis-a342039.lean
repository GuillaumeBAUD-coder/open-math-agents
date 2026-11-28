import OMAStatements.S_oeis_a342039

/-!
# Disproof of OEIS A342039 conjecture

We refute `OMA.S_oeis_a342039.main` with the explicit counterexample
`p = 2203`, `m = 734`, `k = 11015 = 5 * 2203`.

Here `2 * m = 1468 = 4 * 367`, and `λ(11015) = lcm(λ(5), λ(2203)) = lcm(4, 2202) = 4404 = 3 * 1468`.
For any `0 < j < 11015` with `1468 ∣ λ(j)`, the prime `367` must divide `λ(r^e)` for some
prime power `r^e ‖ j`. Since `367^2 = 134689 > 11015`, we must have `r ≠ 367` and `367 ∣ r - 1`,
so `r = 734 * t + 1` with `1 ≤ t ≤ 15`. The only prime values in this range are
`r ∈ {2203, 3671, 6607}`, all of which satisfy `r ≡ 3 (mod 4)`. Any multiple `j = r * s < 11015`
has `s ≤ 4`, hence `λ(s) ∣ 2` and `λ(j) = r - 1 ≡ 2 (mod 4)`, contradicting `4 ∣ 1468 ∣ λ(j)`.
Thus `A307437(734) = 11015`, which is divisible by `p = 2203` and strictly greater than `2203`,
yet `m = 734 < 2202 = p - 1`.
-/

namespace OMA.S_oeis_a342039

open ArithmeticFunction

private lemma prime_dvd_finset_lcm {α : Type*} {q : ℕ} (hq : q.Prime) (s : Finset α)
    (f : α → ℕ) (h : q ∣ s.lcm f) : ∃ a ∈ s, q ∣ f a := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.lcm_empty] at h
    exact absurd h hq.not_dvd_one
  | @insert a s has ih =>
    rw [Finset.lcm_insert] at h
    have hmul : q ∣ f a * s.lcm f :=
      h.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
    rcases hq.dvd_mul.mp hmul with hfa | hs
    · exact ⟨a, Finset.mem_insert_self a s, hfa⟩
    · obtain ⟨b, hbs, hfb⟩ := ih hs
      exact ⟨b, Finset.mem_insert_of_mem hbs, hfb⟩

private lemma carmichael_prime_val {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    carmichael r = r - 1 := by
  have h := carmichael_pow_of_prime_ne_two 1 hr hr2
  rw [pow_one, Nat.totient_prime hr] at h
  exact h

private lemma carmichael_small_dvd_two {s : ℕ} (hs1 : 1 ≤ s) (hs4 : s ≤ 4) :
    carmichael s ∣ 2 := by
  interval_cases s
  · rw [show (1 : ℕ) = 2 ^ 0 by norm_num, carmichael_two_pow_of_le_two (by omega)]
    norm_num
  · rw [show (2 : ℕ) = 2 ^ 1 by norm_num, carmichael_two_pow_of_le_two (by omega)]
    norm_num
  · rw [carmichael_prime_val (by norm_num) (by norm_num)]
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, carmichael_two_pow_of_le_two (by omega)]
    norm_num

private lemma not_four_dvd_carmichael_mul_small {r s : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrmod : r % 4 = 3) (hs1 : 1 ≤ s) (hs4 : s ≤ 4) (hcop : r.Coprime s) :
    ¬ (4 ∣ carmichael (r * s)) := by
  rw [carmichael_mul hcop, carmichael_prime_val hr hr2]
  have hs2 : carmichael s ∣ 2 := carmichael_small_dvd_two hs1 hs4
  have h2r : 2 ∣ r - 1 := by omega
  have hlcm : Nat.lcm (r - 1) (carmichael s) = r - 1 :=
    Nat.lcm_eq_left (hs2.trans h2r)
  rw [hlcm]
  omega

private lemma isA307437_734_11015 : IsA307437 734 11015 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · have h5 : carmichael 5 = 4 := carmichael_prime_val (by norm_num) (by norm_num)
    have h2203 : carmichael 2203 = 2202 := carmichael_prime_val (by norm_num) (by norm_num)
    have hmul : carmichael (5 * 2203) = Nat.lcm (carmichael 5) (carmichael 2203) :=
      carmichael_mul (by norm_num)
    rw [show (11015 : ℕ) = 5 * 2203 by norm_num, hmul, h5, h2203]
    norm_num
  · intro j hj0 hjl hdvd
    have h367 : 367 ∣ carmichael j := dvd_trans (by norm_num) hdvd
    have h4 : 4 ∣ carmichael j := dvd_trans (by norm_num) hdvd
    have : NeZero j := ⟨hj0.ne'⟩
    rw [carmichael_factorization j] at h367
    have hq : Nat.Prime 367 := by norm_num
    obtain ⟨r, hr_mem, hr_dvd⟩ := prime_dvd_finset_lcm hq j.primeFactors
      (fun r => carmichael (r ^ j.factorization r)) h367
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
    have hrj : r ∣ j := Nat.dvd_of_mem_primeFactors hr_mem
    set e := j.factorization r
    have he1 : 1 ≤ e := by
      have := (hrp.dvd_iff_one_le_factorization hj0.ne').mp hrj
      omega
    have hr2 : r ≠ 2 := by
      intro h2
      subst h2
      have hd2 : carmichael (2 ^ e) ∣ 2 ^ e := by
        by_cases he2 : e ≤ 2
        · rw [carmichael_two_pow_of_le_two he2]
          exact Nat.pow_dvd_pow 2 (by omega)
        · rw [carmichael_two_pow_of_ne_two (by omega)]
          exact Nat.pow_dvd_pow 2 (by omega)
      have h367_2 : 367 ∣ 2 := hq.dvd_of_dvd_pow (hr_dvd.trans hd2)
      norm_num at h367_2
    rw [carmichael_pow_of_prime_ne_two e hrp hr2, Nat.totient_prime_pow hrp he1] at hr_dvd
    rcases hq.dvd_mul.mp hr_dvd with hpow | hsub
    · have h367_r : 367 ∣ r := hq.dvd_of_dvd_pow hpow
      have hr_eq : r = 367 := by
        rcases (Nat.dvd_prime hrp).mp h367_r with h1 | h2
        · norm_num at h1
        · exact h2.symm
      have he2 : 2 ≤ e := by
        by_contra hlt
        have heq1 : e = 1 := by omega
        rw [heq1] at hpow
        norm_num at hpow
      have hsq_dvd : 367 ^ 2 ∣ j := by
        have hre : r ^ e ∣ j := Nat.ordProj_dvd j r
        rw [hr_eq] at hre
        exact (Nat.pow_dvd_pow 367 he2).trans hre
      have hsq_le : 367 ^ 2 ≤ j := Nat.le_of_dvd hj0 hsq_dvd
      omega
    · have hr_le : r ≤ j := Nat.le_of_dvd hj0 hrj
      have hr_odd : r % 2 = 1 := by
        rcases hrp.eq_two_or_odd with h2 | hodd
        · exact absurd h2 hr2
        · exact hodd
      have h2_dvd : 2 ∣ r - 1 := by omega
      have h734_dvd : 734 ∣ r - 1 := by
        have hcop : Nat.Coprime 2 367 := by norm_num
        simpa [show 2 * 367 = 734 by norm_num] using hcop.mul_dvd_of_dvd_of_dvd h2_dvd hsub
      obtain ⟨t, ht⟩ := h734_dvd
      have hr_val : r = 734 * t + 1 := by
        have := hrp.two_le
        omega
      have ht1 : 1 ≤ t := by
        by_contra h0
        have ht0 : t = 0 := by omega
        rw [ht0] at hr_val
        have := hrp.two_le
        omega
      have ht15 : t ≤ 15 := by omega
      have hr_cases : r = 2203 ∨ r = 3671 ∨ r = 6607 := by
        interval_cases t <;> rw [hr_val] at hrp <;> norm_num at hrp
        · left; omega
        · right; left; omega
        · right; right; omega
      obtain ⟨s, rfl⟩ := hrj
      have hs1 : 1 ≤ s := by
        by_contra hs0
        have : s = 0 := by omega
        subst this
        omega
      rcases hr_cases with rfl | rfl | rfl
      · have hs4 : s ≤ 4 := by omega
        have hcop : Nat.Coprime 2203 s := by interval_cases s <;> norm_num
        exact not_four_dvd_carmichael_mul_small (by norm_num) (by norm_num) (by norm_num)
          hs1 hs4 hcop h4
      · have hs3 : s ≤ 3 := by omega
        have hcop : Nat.Coprime 3671 s := by interval_cases s <;> norm_num
        exact not_four_dvd_carmichael_mul_small (by norm_num) (by norm_num) (by norm_num)
          hs1 (by omega) hcop h4
      · have hs1' : s = 1 := by omega
        subst hs1'
        exact not_four_dvd_carmichael_mul_small (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) (by norm_num) h4

end OMA.S_oeis_a342039

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a342039.main) := by
  intro h
  have hle := h 2203 734 11015 (by norm_num) (by norm_num)
    OMA.S_oeis_a342039.isA307437_734_11015 ⟨5, by norm_num⟩ (by norm_num)
  omega
