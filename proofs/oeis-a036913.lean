import OMAStatements.S_oeis_a036913

/-!
We prove two facts about a sparsely totient number. Its divisor subset sums
fill the interval from zero to the divisor sum, and the divisor sum is even
except at 2 and 18. In both arguments, replacing a factor by a slightly larger
multiple of the first missing prime preserves the required totient inequality.
-/
namespace SparseZumkeller
open Finset
open OMA.S_oeis_a036913

private theorem totient_mul_le (x y : ℕ) : (x*y).totient ≤ x*y.totient := by
  induction x using induction_on_primes generalizing y with
  | zero => simp
  | one => simp
  | prime_mul p x hp ih =>
    rw [mul_assoc]
    have h : (p*(x*y)).totient ≤ p*(x*y).totient := by
      by_cases hd : p ∣ x*y
      · rw [Nat.totient_mul_of_prime_of_dvd hp hd]
      · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd]
        exact Nat.mul_le_mul_right _ (by omega)
    simpa only [mul_assoc] using h.trans (Nat.mul_le_mul_left p (ih y))

private theorem totient_mul_of_dvd {x y : ℕ} (hx : 0 < x) (h : x ∣ y) :
    (x*y).totient = x*y.totient := by
  have h1 := Nat.totient_gcd_mul_totient_mul x y
  rw [Nat.gcd_eq_left h, mul_assoc, mul_comm y.totient] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hx) h1

private theorem sparse_even {n : ℕ} (hn : IsSparselyTotient n) : Even n := by
  by_contra h
  have ho := Nat.not_even_iff_odd.mp h
  have hn1 := hn.1
  have hlt := hn.2 (2*n) (by omega)
  rw [Nat.totient_two_mul_of_odd ho] at hlt
  omega

private theorem replacement {q s t c : ℕ} (h : IsSparselyTotient (s*t))
    (hq : q.Prime) (hnq : ¬ q ∣ s*t) (ht : 0 < t)
    (hs : c*t.totient ≤ (s*t).totient)
    (hlarge : (q-1)*(s/q+1) ≤ c) : False := by
  let k := s/q + 1
  have hk : s < q*k := by
    have hrem := Nat.mod_lt s hq.pos
    have hdiv := Nat.div_add_mod s q
    dsimp [k]
    rw [mul_add, mul_one]
    omega
  have hgreater : s*t < (q*k)*t := Nat.mul_lt_mul_of_pos_right hk ht
  have hnt : ¬ q ∣ t := fun hd => hnq (dvd_mul_of_dvd_right hd _)
  have hphi : ((q*k)*t).totient ≤ (q-1)*k*t.totient := by
    calc
      _ = (k*(q*t)).totient := congrArg Nat.totient (by ring)
      _ ≤ k*(q*t).totient := totient_mul_le _ _
      _ = _ := by rw [Nat.totient_mul_of_prime_of_not_dvd hq hnt]; ac_rfl
  have hl := h.2 _ hgreater
  exact (not_lt_of_ge (hphi.trans ((Nat.mul_le_mul_right _ hlarge).trans hs))) hl

private theorem replacement_prime {q p t : ℕ} (h : IsSparselyTotient (p*t))
    (hq : q.Prime) (hp : p.Prime) (hnq : ¬ q ∣ p*t) (ht : 0 < t)
    (hlarge : (q-1)*(p/q+1) ≤ p-1) : False := by
  apply replacement h hq hnq ht _ hlarge
  by_cases hd : p ∣ t
  · rw [Nat.totient_mul_of_prime_of_dvd hp hd]
    exact Nat.mul_le_mul_right _ (by omega)
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp hd]

private theorem replacement_square {n q s : ℕ} (h : IsSparselyTotient n)
    (hq : q.Prime) (hnq : ¬ q ∣ n) (hs : 0 < s) (hd : s^2 ∣ n)
    (hlarge : (q-1)*(s/q+1) ≤ s) : False := by
  obtain ⟨t, ht⟩ := hd
  rw [pow_two, mul_assoc] at ht
  have hpos : 0 < s*t := by
    have hn : 0 < n := h.1
    rw [ht] at hn
    exact Nat.pos_of_ne_zero (right_ne_zero_of_mul hn.ne')
  rw [ht] at h hnq
  exact replacement h hq hnq hpos (totient_mul_of_dvd hs (dvd_mul_right s t)).ge hlarge

private theorem smallest_missing {n : ℕ} (hn : 0 < n) :
    ∃ q, q.Prime ∧ ¬ q ∣ n ∧ ∀ p < q, p.Prime → p ∣ n := by
  have he : ∃ q, q.Prime ∧ ¬ q ∣ n := by
    obtain ⟨q,hq,hp⟩ := Nat.exists_infinite_primes (n+1)
    exact ⟨q,hp,fun hd => by have := Nat.le_of_dvd hn hd; omega⟩
  exact ⟨Nat.find he, (Nat.find_spec he).1, (Nat.find_spec he).2,
    fun p hlt hp => by
      by_contra h
      exact Nat.find_min he hlt ⟨hp,h⟩⟩

private theorem rounding_bound {q s : ℕ} (hq : 1 ≤ q) (hs : q*(q-1) ≤ s) :
    (q-1)*(s/q+1) ≤ s := by
  have hdiv : q-1 ≤ s/q := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [mul_comm] using hs)
  calc
    _ = (q-1)*(s/q)+(q-1) := by ring
    _ ≤ (q-1)*(s/q)+s/q := Nat.add_le_add_left hdiv _
    _ = q * (s/q) := by
      have he : q-1+1=q := by omega
      calc
        _ = (q-1+1)*(s/q) := by rw [Nat.add_mul, one_mul]
        _ = _ := congrArg (fun x => x*(s/q)) he
    _ ≤ s := Nat.mul_div_le _ _

private theorem rounding_bound_strict {q s : ℕ} (hq : 1 ≤ q) (hs : q*q ≤ s) :
    (q-1)*(s/q+1) ≤ s-1 := by
  have hdiv : q ≤ s/q := (Nat.le_div_iff_mul_le (by omega)).mpr hs
  have heq : q*(s/q) = (q-1)*(s/q)+s/q := by
    have hq' : q-1+1=q := by omega
    calc
      _ = (q-1+1)*(s/q) := congrArg (fun x => x*(s/q)) hq'.symm
      _ = _ := by rw [Nat.add_mul, one_mul]
  rw [Nat.mul_add, mul_one]
  have := Nat.mul_div_le s q
  omega

private def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

private theorem sigma_le_of_dvd {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    sigma d ≤ sigma n :=
  Finset.sum_le_sum_of_subset (fun _ hi =>
    Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hi).1.trans hd, hn⟩)

private theorem le_sigma {d : ℕ} (hd : d ≠ 0) : d ≤ sigma d :=
  Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self d hd)


private theorem prime_pow_prod_dvd {n e : ℕ} (S : Finset ℕ)
    (h : ∀ p ∈ S, p.Prime ∧ p^e ∣ n) : (∏ p ∈ S, p)^e ∣ n := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hps ih =>
    have hp := h p (mem_insert_self _ _)
    have hS : ∀ r ∈ S, r.Prime ∧ r^e ∣ n :=
      fun r hr => h r (mem_insert_of_mem hr)
    rw [prod_insert hps, mul_pow]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ hp.2 (ih hS)
    apply Nat.Coprime.pow _ _ (Nat.coprime_prod_right_iff.mpr _)
    intro r hr
    exact Nat.coprime_primes hp.1 (hS r hr).1 |>.2 (fun h => hps (h ▸ hr))

private theorem two_prime_pow_dvd {n e a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a ≠ b) (han : a^e ∣ n) (hbn : b^e ∣ n) : (a*b)^e ∣ n := by
  rw [mul_pow]
  exact (((Nat.coprime_primes ha hb).2 hab).pow e e).mul_dvd_of_dvd_of_dvd han hbn

private theorem prime_in_half {q : ℕ} (hq : q.Prime) (h2 : 2 < q) :
    ∃ p : ℕ, p.Prime ∧ p < q ∧ q < 2*p := by
  have ho := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  obtain ⟨p, hp, hl, hu⟩ := Nat.exists_prime_lt_and_le_two_mul (q/2) (by omega)
  exact ⟨p, hp, by omega, by omega⟩

private theorem large_prefix {q n e : ℕ} (hq : q.Prime) (hq13 : 13 ≤ q)
    (hdiv : ∀ p < q, p.Prime → p ≠ 2 → p^e ∣ n) : ∃ s ≥ q*q, s^e ∣ n := by
  by_cases hq21 : q < 21
  · have hS : ∀ p ∈ ({3,5,7,11} : Finset ℕ), p.Prime ∧ p^e ∣ n := by
      intro p hp
      simp at hp
      rcases hp with (rfl | rfl | rfl | rfl) <;>
        exact ⟨by decide, hdiv _ (by omega) (by decide) (by decide)⟩
    have hs := prime_pow_prod_dvd _ hS
    have hs' : (1155:ℕ)^e ∣ n := by simpa using hs
    exact ⟨1155, by nlinarith, hs'⟩
  · obtain ⟨p, hp, hpq, hqp⟩ := prime_in_half hq (by omega)
    obtain ⟨r, hr, hrp, hpr⟩ := prime_in_half hp (by omega)
    have hr7 : 7 ≤ r := by
      have hh : 5 < r := by omega
      by_contra h
      have he : r = 6 := by omega
      subst r
      exact (by decide : ¬ Nat.Prime 6) hr
    have hS : ∀ a ∈ ({3,5,r,p} : Finset ℕ), a.Prime ∧ a^e ∣ n := by
      intro a ha
      simp at ha
      rcases ha with (rfl | rfl | rfl | rfl)
      · exact ⟨by decide, hdiv _ (by omega) (by decide) (by decide)⟩
      · exact ⟨by decide, hdiv _ (by omega) (by decide) (by decide)⟩
      · exact ⟨hr, hdiv _ (by omega) hr (by omega)⟩
      · exact ⟨hp, hdiv _ hpq hp (by omega)⟩
    have hs := prime_pow_prod_dvd _ hS
    have hs' : (15*r*p)^e ∣ n := by
      have hh : (∏ k ∈ ({3,5,r,p} : Finset ℕ), k) = 15*r*p := by
        simp [show 3 ≠ 5 by decide, show (3:ℕ) ≠ r by omega, show (3:ℕ) ≠ p by omega,
          show (5:ℕ) ≠ r by omega, show (5:ℕ) ≠ p by omega, hrp.ne]
        ring
      rwa [hh] at hs
    refine ⟨15*r*p, ?_, hs'⟩
    have h1 := Nat.mul_le_mul hqp.le (show q ≤ 4*r by omega)
    have h2 : 2*p * (4*r) ≤ 15*r*p := by
      calc
        _ = 8 * (r*p) := by ring
        _ ≤ 15 * (r*p) := Nat.mul_le_mul_right _ (by decide)
        _ = _ := by ring
    exact h1.trans h2

private theorem small_prefix_dvd {q n e : ℕ}
    (hdiv : ∀ p < q, p.Prime → p^e ∣ n) :
    (3 < q → 3^e ∣ n) ∧ (5 < q → 15^e ∣ n) ∧ (7 < q → 105^e ∣ n) := by
  have h3 : 3 < q → 3^e ∣ n := fun h => hdiv _ h (by decide)
  have h15 : 5 < q → 15^e ∣ n := fun h =>
    two_prime_pow_dvd (a := 3) (b := 5) (by decide) (by decide) (by decide)
      (h3 (by omega)) (hdiv _ h (by decide))
  refine ⟨h3, h15, fun h => ?_⟩
  rw [show (105:ℕ)=15*7 by decide, mul_pow]
  exact ((by decide : Nat.Coprime 15 7).pow e e).mul_dvd_of_dvd_of_dvd
    (h15 (by omega)) (hdiv _ h (by decide))

private theorem prime_rounding {n p q : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q < p) (hlarge : sigma n + 1 < p)
    (h2 : 2 ∣ n) (hdiv : ∀ r < q, r.Prime → r ∣ n) :
    (q-1)*(p/q+1) ≤ p-1 := by
  have hpref : ∀ r < q, r.Prime → r^1 ∣ n := fun r hr hprime => by
    simpa using hdiv r hr hprime
  obtain ⟨h3, h15, h105⟩ := small_prefix_dvd hpref
  simp only [pow_one] at h3 h15 h105
  have hqg := hq.two_le
  by_cases hq13 : 13 ≤ q
  · obtain ⟨s, hs, hd⟩ := large_prefix hq hq13 (fun r hr hp _ => hpref r hr hp)
    have hd' : s ∣ n := by simpa using hd
    have hs0 : s ≠ 0 := fun H => hn (Nat.zero_dvd.mp (H ▸ hd'))
    have hh := (le_sigma hs0).trans (sigma_le_of_dvd hn hd')
    exact rounding_bound_strict (by omega) (by omega)
  · have hcases : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 := by
      interval_cases q <;> simp_all +decide
    rcases hcases with (rfl | rfl | rfl | rfl)
    · by_cases hpp : 9 ≤ p
      · exact rounding_bound_strict (by decide) hpp
      · interval_cases p <;> simp_all +decide
    · have hd : 6 ∣ n := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 (h3 (by decide))
      have hh : 12 ≤ sigma n := (show 12 ≤ sigma 6 by decide).trans (sigma_le_of_dvd hn hd)
      by_cases hpp : 25 ≤ p
      · exact rounding_bound_strict (by decide) hpp
      · interval_cases p <;> simp_all +decide <;> omega
    · have hd : 30 ∣ n := (by decide : Nat.Coprime 2 15).mul_dvd_of_dvd_of_dvd h2 (h15 (by decide))
      have hh : 72 ≤ sigma n := (show 72 ≤ sigma 30 by decide).trans (sigma_le_of_dvd hn hd)
      exact rounding_bound_strict (by decide) (by omega)
    · have hd : 210 ∣ n := (by decide : Nat.Coprime 2 105).mul_dvd_of_dvd_of_dvd h2 (h105 (by decide))
      have hh : 210 ≤ sigma n := (le_sigma (by decide : (210:ℕ) ≠ 0)).trans (sigma_le_of_dvd hn hd)
      exact rounding_bound_strict (by decide) (by omega)


private def Complete (d : ℕ) : Prop :=
  ∀ x ≤ sigma d, ∃ S ⊆ d.divisors, ∑ s ∈ S, s = x

private theorem complete_one : Complete 1 := by
  intro x hx
  have h : sigma 1 = 1 := by decide
  rw [h] at hx
  interval_cases x
  · exact ⟨∅, by simp⟩
  · exact ⟨{1}, by decide, by simp⟩

private theorem divisors_prime_step {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0) (hpd : ¬ p ∣ d)
    (e : ℕ) :
    let f : ℕ ↪ ℕ := ⟨fun z => p^(e+1)*z, fun _ _ h =>
      Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h⟩
    Disjoint (p^e*d).divisors (d.divisors.map f) ∧
      (p^(e+1)*d).divisors = (p^e*d).divisors ∪ (d.divisors.map f) := by
  let f : ℕ ↪ ℕ := ⟨fun z => p^(e+1)*z, fun _ _ h =>
    Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h⟩
  have h0 : p^e*d ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hd
  have h1 : p^(e+1)*d ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hd
  constructor
  · apply disjoint_left.mpr
    intro z hz hzm
    obtain ⟨s, _, rfl⟩ := mem_map.mp hzm
    have hf : f s = p^(e+1)*s := rfl
    rw [hf] at hz
    have hbad : p^(e+1) ∣ p^e*d := (dvd_mul_right _ _).trans (Nat.dvd_of_mem_divisors hz)
    rw [pow_succ] at hbad
    exact hpd ((Nat.mul_dvd_mul_iff_left (pow_pos hp.pos _)).mp hbad)
  · ext z
    simp only [mem_union, mem_map, Nat.mem_divisors]
    constructor
    · intro hz
      obtain ⟨u,v,hu,hv,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hz.1
      obtain ⟨j,hj,rfl⟩ := (Nat.dvd_prime_pow hp).mp hu
      rcases eq_or_lt_of_le hj with rfl | hj
      · exact Or.inr ⟨v, ⟨hv,hd⟩, rfl⟩
      · exact Or.inl ⟨mul_dvd_mul (pow_dvd_pow p (by omega)) hv,h0⟩
    · rintro (hz | ⟨v,hv,rfl⟩)
      · exact ⟨hz.1.trans (mul_dvd_mul (pow_dvd_pow p (by omega)) dvd_rfl),h1⟩
      · exact ⟨mul_dvd_mul dvd_rfl hv.1,h1⟩

private theorem complete_prime_pow {p d : ℕ} (hp : p.Prime) (hd : d ≠ 0)
    (hpd : ¬ p ∣ d) (hC : Complete d) (hsize : p ≤ sigma d + 1) (e : ℕ) :
    Complete (p^e*d) ∧ p^(e+1) ≤ sigma (p^e*d)+1 := by
  induction e with
  | zero => simpa using And.intro hC hsize
  | succ e ih =>
    let f : ℕ ↪ ℕ := ⟨fun z => p^(e+1)*z, fun _ _ h =>
      Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h⟩
    obtain ⟨hdis, hsplit⟩ := divisors_prime_step hp hd hpd e
    change Disjoint (p^e*d).divisors (d.divisors.map f) at hdis
    change (p^(e+1)*d).divisors = (p^e*d).divisors ∪ (d.divisors.map f) at hsplit
    have hsigma : sigma (p^(e+1)*d) = sigma (p^e*d) + p^(e+1)*sigma d := by
      unfold sigma
      rw [hsplit, sum_union hdis, sum_map, mul_sum]
      rfl
    constructor
    · intro x hx
      let q := min (x/(p^(e+1))) (sigma d)
      have hq : q ≤ sigma d := min_le_right _ _
      have hqt : p^(e+1)*q ≤ x :=
        (Nat.mul_le_mul_left _ (min_le_left _ _)).trans (Nat.mul_div_le _ _)
      have hr : x - p^(e+1)*q ≤ sigma (p^e*d) := by
        by_cases hq' : x/(p^(e+1)) ≤ sigma d
        · change x - p^(e+1)*min (x/(p^(e+1))) (sigma d) ≤ _
          rw [min_eq_left hq']
          have hdiv := Nat.div_add_mod x (p^(e+1))
          have hmod := Nat.mod_lt x (pow_pos hp.pos (e+1))
          have := ih.2
          omega
        · change x - p^(e+1)*min (x/(p^(e+1))) (sigma d) ≤ _
          rw [min_eq_right (by omega)]
          rw [hsigma] at hx
          omega
      obtain ⟨A,hA,hAv⟩ := ih.1 _ hr
      obtain ⟨B,hB,hBv⟩ := hC _ hq
      have hB' : B.map f ⊆ d.divisors.map f := by
        intro s hs
        obtain ⟨z,hz,rfl⟩ := mem_map.mp hs
        exact mem_map.mpr ⟨z,hB hz,rfl⟩
      have hab := hdis.mono hA hB'
      have htot : ∑ s ∈ B.map f, s = p^(e+1)*q := by
        rw [sum_map, ← hBv, mul_sum]
        rfl
      refine ⟨A ∪ B.map f, ?_, ?_⟩
      · rw [hsplit]
        exact union_subset_union hA hB'
      · rw [sum_union hab, htot, hAv, Nat.sub_add_cancel hqt]
    · rw [hsigma, pow_succ]
      have hA := ih.2
      have hB := Nat.mul_le_mul_left (p^(e+1)) hsize
      rw [Nat.mul_add, mul_one] at hB
      omega

private theorem sparse_complete {n : ℕ} (hn : IsSparselyTotient n) : Complete n := by
  have hn0 : n ≠ 0 := by have := hn.1; omega
  have hn2 := (sparse_even hn).two_dvd
  obtain ⟨q, hq, hnq, hsmall⟩ := smallest_missing (Nat.pos_of_ne_zero hn0)
  have hq2 : q ≠ 2 := fun he => hnq (he ▸ hn2)
  have build (b a : ℕ) (he : n = a*b)
      (hsep : ∀ p, p.Prime → p ∣ a → ∀ r, r.Prime → r ∣ b → p < r)
      (hca : Complete a) : Complete n := by
    induction b using Nat.strong_induction_on generalizing a with
    | h b ih =>
      have hb0 : b ≠ 0 := fun hz => hn0 (by simp [he,hz])
      have ha0 : a ≠ 0 := fun hz => hn0 (by simp [he,hz])
      by_cases hb : b = 1
      · simpa [he, hb] using hca
      let p := b.minFac
      have hp : p.Prime := Nat.minFac_prime hb
      have hpb : p ∣ b := Nat.minFac_dvd b
      have hleast : ∀ r, r.Prime → r ∣ b → p ≤ r :=
        fun r hr hd => Nat.minFac_le_of_dvd hr.two_le hd
      have hpa : ¬ p ∣ a := fun h => (hsep p hp h p hp hpb).false
      have hsize : p ≤ sigma a + 1 := by
        by_contra! hbad
        have hq' : q < p := by
          have h1 : a+1 ≠ 1 := by omega
          obtain ⟨r,hr,hrd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp h1
          have hrp : r < p := by
            have h := Nat.le_of_dvd (show 0 < a+1 by omega) hrd
            have := le_sigma ha0
            omega
          by_contra! hpq
          have hrn := hsmall r (hrp.trans_le hpq) hr
          rw [he, hr.dvd_mul] at hrn
          rcases hrn with hra | hrb
          · exact hr.not_dvd_one ((Nat.dvd_add_iff_right hra).mpr hrd)
          · exact (not_le_of_gt hrp) (hleast r hr hrb)
        have h2 : 2 ∣ a := by
          rw [he, Nat.prime_two.dvd_mul] at hn2
          rcases hn2 with h2 | h2
          · exact h2
          · have hh := hleast 2 Nat.prime_two h2
            have hh' := le_sigma ha0
            omega
        have hbelow : ∀ r < q, r.Prime → r ∣ a := by
          intro r hr hprime
          have H := hsmall r hr hprime
          rw [he, hprime.dvd_mul] at H
          exact H.resolve_right (fun h => (not_le_of_gt (hr.trans hq')) (hleast r hprime h))
        have hround := prime_rounding ha0 hp hq hq2 hq' hbad h2 hbelow
        have hpd : p ∣ n := he ▸ dvd_mul_of_dvd_right hpb a
        obtain ⟨t,ht⟩ := hpd
        have ht0 : 0 < t := by
          by_contra! H
          have hz : t = 0 := by omega
          exact hn0 (by simp [ht,hz])
        rw [ht] at hn hnq
        exact replacement_prime hn hq hp hnq ht0 hround
      obtain ⟨e,c,hpc,hec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb0 p hp.one_lt.ne'
      have hpos : 0 < e := by
        by_contra! hh
        have hzero : e = 0 := by omega
        exact hpc (by simpa [hec,hzero] using hpb)
      have hc0 : c ≠ 0 := fun hz => hb0 (by simp [hec,hz])
      have hcb : c < b := by
        rw [hec]
        have hh := hp.one_lt.trans_le (Nat.le_self_pow hpos.ne' p)
        simpa using Nat.mul_lt_mul_of_pos_right hh (Nat.pos_of_ne_zero hc0)
      have hen : n = (p^e*a)*c := by rw [he,hec]; ring
      apply ih c hcb (p^e*a) hen _ (complete_prime_pow hp ha0 hpa hca hsize e).1
      intro r hr hra s hs hsc
      have hsb : s ∣ b := by rw [hec]; exact dvd_mul_of_dvd_right hsc _
      rcases hr.dvd_mul.mp hra with hrp | hra
      · have hrp' : r ∣ p := hr.dvd_of_dvd_pow hrp
        have hre : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp'
        have hle := hleast s hs hsb
        exact lt_of_le_of_ne (hre ▸ hle) (fun h => hpc ((hre ▸ h) ▸ hsc))
      · exact hsep r hr hra s hs hsb
  apply build n 1 (by simp) _ complete_one
  intro p hp h
  exact (hp.not_dvd_one h).elim


private theorem dvd_of_prime_factorization_le {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (h : ∀ p, p.Prime → n.factorization p ≤ m.factorization p) : n ∣ m := by
  apply (Nat.factorization_le_iff_dvd hn hm).mp
  intro p
  by_cases hp : p.Prime
  · exact h p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem factorization_value {n p e : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hl : p^e ∣ n) (hu : ¬ p^(e+1) ∣ n) : n.factorization p = e := by
  have hle := (hp.pow_dvd_iff_le_factorization hn).mp hl
  have hgt := mt (hp.pow_dvd_iff_le_factorization hn).mpr hu
  omega

private theorem not_sparse_36 : ¬ IsSparselyTotient 36 := by
  intro H
  exact (by decide : ¬ (36:ℕ).totient < (42:ℕ).totient) (H.2 42 (by decide))

private theorem not_sparse_72 : ¬ IsSparselyTotient 72 := by
  intro H
  exact (by decide : ¬ (72:ℕ).totient < (90:ℕ).totient) (H.2 90 (by decide))

set_option maxRecDepth 10000 in
private theorem not_sparse_450 : ¬ IsSparselyTotient 450 := by
  intro H
  exact (by decide : ¬ (450:ℕ).totient < (462:ℕ).totient) (H.2 462 (by decide))

private theorem odd_valuation {n : ℕ} (hn : IsSparselyTotient n) (hn2 : n ≠ 2) (hn18 : n ≠ 18) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ Odd (n.factorization p) := by
  by_contra hex
  have hn0 : n ≠ 0 := by have := hn.1; omega
  have h2 := (sparse_even hn).two_dvd
  have hev (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : Even (n.factorization p) :=
    Nat.not_odd_iff_even.mp (fun h => hex ⟨p,hp,hp2,h⟩)
  have hsq (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ n) : p^2 ∣ n := by
    have h1 := hp.factorization_pos_of_dvd hn0 hd
    have hh := Nat.even_iff.mp (hev p hp hp2)
    apply (hp.pow_dvd_iff_le_factorization hn0).mpr
    omega
  obtain ⟨q,hq,hqn,hbelow⟩ := smallest_missing (Nat.pos_of_ne_zero hn0)
  have hq2 : q ≠ 2 := fun H => hqn (H ▸ h2)
  have hsmall (p : ℕ) (hpq : p < q) (hp : p.Prime) (hp2 : p ≠ 2) : p^2 ∣ n :=
    hsq p hp hp2 (hbelow p hpq hp)
  by_cases hq13 : 13 ≤ q
  · have hdiv : ∀ p < q, p.Prime → (p ≠ 2 → p^2 ∣ n) := hsmall
    -- The large-prefix witness uses odd primes only.
    obtain ⟨s,hs,hsd⟩ := large_prefix hq hq13 hdiv
    exact replacement_square hn hq hqn ((Nat.mul_pos hq.pos hq.pos).trans_le hs) hsd
      (rounding_bound (by have := hq.two_le; omega) (by
        exact (Nat.mul_le_mul_left q (Nat.sub_le _ _)).trans hs))
  have hqmin := hq.two_le
  have hcases : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 := by
    interval_cases q <;> simp_all +decide
  rcases hcases with (rfl | rfl | rfl | rfl)
  · have h22 : ¬ 2^2 ∣ n := fun H =>
      replacement_square hn hq hqn (s := 2) (by decide) H (by decide)
    have hone : n ∣ 2 := by
      refine dvd_of_prime_factorization_le hn0 (by decide) ?_
      intro p hp
      by_cases hp2 : p = 2
      · subst p
        have H := mt ((Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr) h22
        have hval : (2:ℕ).factorization 2 = 1 := 
          factorization_value (by decide) (by decide) (by decide) (by decide)
        omega
      · have hnp : ¬ p ∣ n := by
          intro hpdiv
          have hpg := hp.two_le
          have h5 : 5 ≤ p := by
            by_contra! hh
            interval_cases p <;> simp_all +decide
          have hround : (3-1)*(p/3+1) ≤ p := by
            by_cases h6 : 6 ≤ p
            · exact rounding_bound (by decide) h6
            · have h5' : p = 5 := by omega
              subst p
              decide
          exact replacement_square hn hq hqn hp.pos (hsq p hp hp2 hpdiv) hround
        rw [Nat.factorization_eq_zero_of_not_dvd hnp]
        exact Nat.zero_le _
    exact hn2 (Nat.dvd_antisymm hone h2)
  · have h3 := hsmall 3 (by decide) (by decide) (by decide)
    have h24 : ¬ 2^4 ∣ n := by
      intro H
      have hh : (12:ℕ)^2 ∣ n := by
        rw [show (12:ℕ)^2 = (2:ℕ)^4*3^2 by decide]
        exact (by decide : Nat.Coprime (2^4) (3^2)).mul_dvd_of_dvd_of_dvd H h3
      exact replacement_square hn hq hqn (by decide) hh (by decide)
    have h34 : ¬ 3^4 ∣ n := by
      intro H
      have hh : (9:ℕ)^2 ∣ n := by simpa using H
      exact replacement_square hn hq hqn (by decide) hh (by decide)
    have h72 : n ∣ 72 := by
      refine dvd_of_prime_factorization_le hn0 (by decide) ?_
      intro p hp
      by_cases hp2 : p = 2
      · subst p
        have H := mt ((Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr) h24
        have hval : (72:ℕ).factorization 2 = 3 := 
          factorization_value (by decide) (by decide) (by decide) (by decide)
        omega
      by_cases hp3 : p = 3
      · subst p
        have H := mt (((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization hn0).mpr) h34
        have he := Nat.even_iff.mp (hev 3 hp hp2)
        have hval : (72:ℕ).factorization 3 = 2 := 
          factorization_value (by decide) (by decide) (by decide) (by decide)
        omega
      have hnp : ¬ p ∣ n := by
        intro hpd
        have hpg := hp.two_le
        have h7 : 7 ≤ p := by
          by_contra! hh
          interval_cases p <;> simp_all +decide
        have hpd' := hsq p hp hp2 hpd
        have hsD : (3*p)^2 ∣ n :=
          two_prime_pow_dvd (by decide) hp (Ne.symm hp3) h3 hpd'
        have hlarge : 5*(5-1) ≤ 3*p := by omega
        exact replacement_square hn hq hqn (by omega) hsD (rounding_bound (by decide) hlarge)
      rw [Nat.factorization_eq_zero_of_not_dvd hnp]
      exact Nat.zero_le _
    have h18 : 18 ∣ n := (by decide : Nat.Coprime 2 (3^2)).mul_dvd_of_dvd_of_dvd h2 h3
    obtain ⟨k,hk⟩ := h18
    have hk1 := Nat.le_of_dvd (by decide : 0 < 72) h72
    rw [hk] at hk1
    have hk4 : k ≤ 4 := by omega
    interval_cases k
    · exact hn0 (by simpa using hk)
    · exact hn18 (by simpa using hk)
    · apply not_sparse_36
      simpa [hk] using hn
    · have hh : ¬ (54:ℕ) ∣ 72 := by decide
      rw [hk] at h72
      exact hh h72
    · apply not_sparse_72
      simpa [hk] using hn
  · have h3 := hsmall 3 (by decide) (by decide) (by decide)
    have h5 := hsmall 5 (by decide) (by decide) (by decide)
    have h15 : (15:ℕ)^2 ∣ n := two_prime_pow_dvd (by decide) (by decide) (by decide) h3 h5
    have h22 : ¬ 2^2 ∣ n := by
      intro H
      have hh : (30:ℕ)^2 ∣ n := by
        rw [show (30:ℕ)^2 = (2:ℕ)^2*15^2 by decide]
        exact (by decide : Nat.Coprime (2^2) (15^2)).mul_dvd_of_dvd_of_dvd H h15
      exact replacement_square hn hq hqn (by decide) hh (by decide)
    have h34 : ¬ 3^4 ∣ n := by
      intro H
      have hh : (45:ℕ)^2 ∣ n := by
        rw [show (45:ℕ)^2 = (3:ℕ)^4*5^2 by decide]
        exact (by decide : Nat.Coprime (3^4) (5^2)).mul_dvd_of_dvd_of_dvd H h5
      exact replacement_square hn hq hqn (by decide) hh (by decide)
    have h54 : ¬ 5^4 ∣ n := by
      intro H
      have hh : (75:ℕ)^2 ∣ n := by
        rw [show (75:ℕ)^2 = (5:ℕ)^4*3^2 by decide]
        exact (by decide : Nat.Coprime (5^4) (3^2)).mul_dvd_of_dvd_of_dvd H h3
      exact replacement_square hn hq hqn (by decide) hh (by decide)
    have h450 : n ∣ 450 := by
      refine dvd_of_prime_factorization_le hn0 (by decide) ?_
      intro p hp
      by_cases hp2 : p = 2
      · subst p
        have H := mt ((Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr) h22
        have hval : (450:ℕ).factorization 2 = 1 := 
          factorization_value (by decide) (by decide) (by decide) (by decide)
        omega
      by_cases hp3 : p = 3
      · subst p
        have H := mt (((by decide : Nat.Prime 3).pow_dvd_iff_le_factorization hn0).mpr) h34
        have he := Nat.even_iff.mp (hev 3 hp hp2)
        have hval : (450:ℕ).factorization 3 = 2 := 
          factorization_value (by decide) (by decide) (by decide) (by decide)
        omega
      by_cases hp5 : p = 5
      · subst p
        have H := mt (((by decide : Nat.Prime 5).pow_dvd_iff_le_factorization hn0).mpr) h54
        have he := Nat.even_iff.mp (hev 5 hp hp2)
        have hval : (450:ℕ).factorization 5 = 2 := 
          factorization_value (by decide) (by decide) (by decide) (by decide)
        omega
      have hnp : ¬ p ∣ n := by
        intro hpd
        have hpg := hp.two_le
        have h11 : 11 ≤ p := by
          by_contra! hh
          interval_cases p <;> simp_all +decide
        have hpd' := hsq p hp hp2 hpd
        have hcop : Nat.Coprime 15 p := by
          rw [show 15 = 3*5 by decide, Nat.coprime_mul_iff_left]
          exact ⟨(Nat.coprime_primes (by decide) hp).mpr (Ne.symm hp3),
            (Nat.coprime_primes (by decide) hp).mpr (Ne.symm hp5)⟩
        have hsD : (15*p)^2 ∣ n := by
          rw [mul_pow]
          exact (hcop.pow _ _).mul_dvd_of_dvd_of_dvd h15 hpd'
        have hlarge : 7*(7-1) ≤ 15*p := by omega
        exact replacement_square hn hq hqn (by omega) hsD (rounding_bound (by decide) hlarge)
      rw [Nat.factorization_eq_zero_of_not_dvd hnp]
      exact Nat.zero_le _
    have h450' : 450 ∣ n := (by decide : Nat.Coprime 2 (15^2)).mul_dvd_of_dvd_of_dvd h2 h15
    exact not_sparse_450 ((Nat.dvd_antisymm h450 h450') ▸ hn)
  · have hS : ∀ p ∈ ({3,5,7} : Finset ℕ), p.Prime ∧ p^2 ∣ n := by
      intro p hp
      simp at hp
      rcases hp with (rfl | rfl | rfl) <;>
        exact ⟨by decide, hsmall _ (by decide) (by decide) (by decide)⟩
    have h := prime_pow_prod_dvd _ hS
    have hh : (105:ℕ)^2 ∣ n := by simpa using h
    exact replacement_square hn hq hqn (by decide) hh (by decide)


private theorem paired_power_sum_even {p : ℕ} (hp : Odd p) (k : ℕ) :
    Even (∑ i ∈ range (2*k), p^i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1)=(2*k+1)+1 by omega, sum_range_succ, sum_range_succ, add_assoc]
    exact ih.add (hp.pow.add_odd hp.pow)

private theorem sigma_even_of_odd_valuation {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (he : Odd (n.factorization p)) : Even (sigma n) := by
  obtain ⟨e,d,hd,hnd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  have hd0 : d ≠ 0 := fun h => hn (by simp [hnd,h])
  have hh : n.factorization p = e := by
    rw [hnd, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hd0, hp.factorization_pow,
      Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hd, add_zero]
  have he' : Odd e := hh ▸ he
  have hcop : (p^e).Coprime d := ((hp.coprime_iff_not_dvd).mpr hd).pow_left e
  have hs : sigma n = sigma (p^e) * sigma d := by
    rw [hnd]
    exact hcop.sum_divisors_mul
  have hs' : Even (sigma (p^e)) := by
    unfold sigma
    rw [Nat.sum_divisors_prime_pow hp]
    obtain ⟨u,hu⟩ := he'
    have heq : e+1=2*(u+1) := by omega
    rw [heq]
    exact paired_power_sum_even (hp.odd_of_ne_two hp2) (u+1)
  rw [hs]
  exact hs'.mul_right _

theorem main : type_of% @OMA.S_oeis_a036913.main := by
  intro n hn hn2 hn18
  obtain ⟨p,hp,hp2,hodd⟩ := odd_valuation hn hn2 hn18
  have hn0 : n ≠ 0 := by have := hn.1; omega
  obtain ⟨k,hk⟩ := sigma_even_of_odd_valuation hn0 hp hp2 hodd
  obtain ⟨S,hS,hv⟩ := sparse_complete hn k (by omega)
  refine ⟨S,hS,?_⟩
  have hsplit := sum_sdiff (f := fun a : ℕ => a) hS
  change (∑ d ∈ n.divisors \ S, d) + (∑ d ∈ S, d) = sigma n at hsplit
  omega

end SparseZumkeller

theorem OMA.solution : type_of% @OMA.S_oeis_a036913.main := SparseZumkeller.main
