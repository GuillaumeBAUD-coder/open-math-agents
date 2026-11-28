import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1

/-! Erdős 1052, the 607 branch. A single repeated odd prime forces either exactly 65537
in the fourth Fermat layer or a Fermat divisor in layer eight or higher. Two independent
forced powers exclude singleton kernels in layers six and seven. Finite subsets of
forced repeated primes also exclude three infinite exponent classes by the parent product bound. -/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R2

open OMA.R_Erdos1052_erdos_1052_R1 (sum_udiv_of_isUnitaryPerfect sum_udiv_eq_prod)

lemma odd_multiple_factor {b d m : ℕ} (hd : m % (2 * d) = d) :
    b ^ d + 1 ∣ b ^ m + 1 := by
  have he : m = d * (2 * (m / (2 * d)) + 1) := by
    have hr := Nat.div_add_mod m (2 * d)
    rw [hd] at hr
    linarith
  have hf := Odd.nat_add_dvd_pow_add_pow (b ^ d) 1 (show Odd (2 * (m / (2*d)) + 1) from ⟨_, rfl⟩)
  rwa [one_pow, ← pow_mul, ← he] at hf

/-- Every odd divisor of the unitary sum of one prime power divides the perfect number. -/
lemma component_divisor {n p d : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hd : d.Coprime 2)
    (h : d ∣ p ^ n.factorization p + 1) : d ∣ n := by
  obtain ⟨hpos, hs⟩ := sum_udiv_of_isUnitaryPerfect hn
  rw [sum_udiv_eq_prod hpos.ne'] at hs
  apply hd.dvd_of_dvd_mul_left
  rw [← hs]
  exact (show d ∣ 1 + p ^ n.factorization p by simpa [add_comm] using h).trans
    (Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hpn, hpos.ne'⟩))

lemma required_divisor {n p d q : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hq : q.Coprime 2)
    (hqd : q ∣ p ^ d + 1) (he : n.factorization p % (2*d) = d) : q ∣ n :=
  component_divisor hn hp hpn hq (hqd.trans (odd_multiple_factor he))

lemma excluded_residue {n p q d : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hq : q.Coprime 2)
    (hqd : q ∣ p ^ d + 1) (hqn : ¬ q ∣ n) : n.factorization p % (2*d) ≠ d :=
  fun he => hqn (required_divisor hn hp hpn hq hqd he)

lemma power_divides {n p k : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hk : k ∣ n.factorization p) : p ^ k ∣ n := by
  exact Nat.pow_dvd_of_le_of_pow_dvd
    (Nat.le_of_dvd (hp.factorization_pos_of_dvd (sum_udiv_of_isUnitaryPerfect hn).1.ne' hpn) hk)
    (Nat.ordProj_dvd n p)
lemma lift_power_of_two {e d : ℕ} (hd : 0 < d) (h : d ∣ e) (hhalf : e % (2*d) ≠ d) :
    2*d ∣ e := by
  obtain ⟨u, hu⟩ := h
  rcases Nat.even_or_odd u with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨v, by rw [hu, hv]; ring⟩
  · exfalso
    apply hhalf
    have he : e = d + 2*d*v := by rw [hu, hv]; ring
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]


/-- A finite Lucas certificate, with repeated factors grouped into prime powers. -/
lemma lucas_certificate {p a : ℕ} (factors : List (ℕ × ℕ))
    (hf : (factors.map (fun f => f.1 ^ f.2)).prod = p-1)
    (hprime : ∀ f ∈ factors, Nat.Prime f.1)
    (hfull : (a : ZMod p) ^ (p-1) = 1)
    (hpart : ∀ f ∈ factors, (a : ZMod p) ^ ((p-1)/f.1) ≠ 1) : p.Prime := by
  apply lucas_primality p (a : ZMod p) hfull
  intro q hq hqd
  rw [← hf] at hqd
  obtain ⟨x,hx,hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hqd
  obtain ⟨f,hf',rfl⟩ := List.mem_map.mp hx
  have heq := (Nat.prime_dvd_prime_iff_eq hq (hprime f hf')).mp (hq.dvd_of_dvd_pow hqx)
  rw [heq]
  exact hpart f hf'

lemma prime_166571 : Nat.Prime 166571 := by
  apply lucas_certificate (a := 2) [(2,1), (5,1), (16657,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_933019 : Nat.Prime 933019 := by
  apply lucas_certificate (a := 3) [(2,1), (3,1), (23,1), (6761,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_1677019 : Nat.Prime 1677019 := by
  apply lucas_certificate (a := 2) [(2,1), (3,1), (7,1), (39929,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_1896229 : Nat.Prime 1896229 := by
  apply lucas_certificate (a := 2) [(2,2), (3,2), (52673,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_2998279 : Nat.Prime 2998279 := by
  apply lucas_certificate (a := 3) [(2,1), (3,2), (166571,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_166571
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_6939437 : Nat.Prime 6939437 := by
  apply lucas_certificate (a := 2) [(2,2), (7,1), (139,1), (1783,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_55515497 : Nat.Prime 55515497 := by
  apply lucas_certificate (a := 3) [(2,3), (6939437,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · norm_num
    · exact prime_6939437
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_18533742247 : Nat.Prime 18533742247 := by
  apply lucas_certificate (a := 6) [(2,1), (3,3), (181,1), (1896229,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1896229
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_733803839347 : Nat.Prime 733803839347 := by
  apply lucas_certificate (a := 2) [(2,1), (3,1), (2203,1), (55515497,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_55515497
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_67280421310721 : Nat.Prime 67280421310721 := by
  apply lucas_certificate (a := 3) [(2,8), (5,1), (47,1), (373,1), (2998279,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_2998279
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_116503103764643 : Nat.Prime 116503103764643 := by
  apply lucas_certificate (a := 2) [(2,1), (7,1), (449,1), (18533742247,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_18533742247
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_59649589127497217 : Nat.Prime 59649589127497217 := by
  apply lucas_certificate (a := 3) [(2,9), (116503103764643,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · norm_num
    · exact prime_116503103764643
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_324942424281449593 : Nat.Prime 324942424281449593 := by
  apply lucas_certificate (a := 5) [(2,3), (3,1), (17,1), (509,1), (1677019,1), (933019,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_1677019
    · exact prime_933019
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_407477800048937789623 : Nat.Prime 407477800048937789623 := by
  apply lucas_certificate (a := 3) [(2,1), (3,1), (11,1), (19,1), (324942424281449593,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_324942424281449593
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

lemma prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 := by
  apply lucas_certificate (a := 21) [(2,9), (3,5), (5,1), (12497,1), (733803839347,1)] (by decide)
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_733803839347
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Prod.fst, Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

/-- A prime with exponent one forces each odd divisor of its successor. -/
lemma next_prime {n p q : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hs : ¬ p^2 ∣ n)
    (hq : q.Coprime 2) (hdiv : q ∣ p+1) : q ∣ n := by
  have hn0 := (sum_udiv_of_isUnitaryPerfect hn).1.ne'
  have hpos := hp.factorization_pos_of_dvd hn0 hpn
  have hlt := mt (hp.pow_dvd_iff_le_factorization hn0).mpr hs
  have he : n.factorization p = 1 := by omega
  exact component_divisor hn hp hpn hq (by simpa only [he, pow_one] using hdiv)

/-- For the exact 128 layer, each side of the factorization of F₇ forces a
different repeated odd prime. The second one can come from a successor. -/
theorem fermat_seven_forces_two_powers {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n % 256 = 128)
    (hgap : ∀ q : ℕ, q.Prime → q ∣ n → q < 152 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (hs : ∀ p ∈ ([277,367,733] : List ℕ), ¬ p^2 ∣ n) :
    59649589127497217 ^ 16 ∣ n ∧
      (5704689200685129054721 ^ 8 ∣ n ∨ 407477800048937789623 ^ 4 ∣ n) := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega : 1 ≤ padicValNat 2 n)
  have he : n.factorization 2 % (2*128) = 128 := by rwa [Nat.factorization_def _ Nat.prime_two]
  have hp : 59649589127497217 ∣ n :=
    required_divisor hn Nat.prime_two h2 (d := 128) (by decide) (by decide) he
  have hq : 5704689200685129054721 ∣ n :=
    required_divisor hn Nat.prime_two h2 (d := 128) (by decide) (by decide) he
  have small : ∀ p ∈ ([17,23,29,59,97,113,139] : List ℕ), ¬ p ∣ n := by
    intro p hp' hpn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      have hh := hgap _ (by norm_num) hpn (by decide)
      norm_num at hh
  have n277 : ¬ 277 ∣ n := fun h => small 139 (by decide)
    (next_prime hn (by norm_num : Nat.Prime 277) h (hs _ (by decide)) (by decide) (by decide))
  have n367 : ¬ 367 ∣ n := fun h => small 23 (by decide)
    (next_prime hn (by norm_num : Nat.Prime 367) h (hs _ (by decide)) (by decide) (by decide))
  have n733 : ¬ 733 ∣ n := fun h => n367
    (next_prime hn (by norm_num : Nat.Prime 733) h (hs _ (by decide)) (by decide) (by decide))
  constructor
  · have h1 := excluded_residue hn prime_59649589127497217 hp (d := 1) (by decide) (by decide) n733
    have h2' := excluded_residue hn prime_59649589127497217 hp (d := 2) (by decide) (by decide) (small 17 (by decide))
    have h4 := excluded_residue hn prime_59649589127497217 hp (d := 4) (by decide) (by decide) (small 97 (by decide))
    have h8 := excluded_residue hn prime_59649589127497217 hp (d := 8) (by decide) (by decide) (small 113 (by decide))
    have hx2 := lift_power_of_two (by decide) (one_dvd _) h1
    have hx4 := lift_power_of_two (by decide) hx2 h2'
    have hx8 := lift_power_of_two (by decide) hx4 h4
    exact power_divides hn prime_59649589127497217 hp (lift_power_of_two (by decide) hx8 h8)
  · by_cases hodd : n.factorization 5704689200685129054721 % 2 = 1
    · right
      have hr : 407477800048937789623 ∣ n :=
        required_divisor hn prime_5704689200685129054721 hq (d := 1) (by decide) (by decide) hodd
      have h1 := excluded_residue hn prime_407477800048937789623 hr (d := 1) (by decide) (by decide)
        (small 59 (by decide))
      have h2' := excluded_residue hn prime_407477800048937789623 hr (d := 2) (by decide) (by decide)
        (small 29 (by decide))
      have hx2 := lift_power_of_two (by decide) (one_dvd _) h1
      exact power_divides hn prime_407477800048937789623 hr (lift_power_of_two (by decide) hx2 h2')
    · left
      have h2' := excluded_residue hn prime_5704689200685129054721 hq (d := 2) (by decide) (by decide) n277
      have h4 := excluded_residue hn prime_5704689200685129054721 hq (d := 4) (by decide) (by decide)
        (small 17 (by decide))
      have hx2 := lift_power_of_two (by decide) (one_dvd _) hodd
      have hx4 := lift_power_of_two (by decide) hx2 h2'
      exact power_divides hn prime_5704689200685129054721 hq (lift_power_of_two (by decide) hx4 h4)

lemma no_second_source {n p d r s : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hpr : p ≠ r) (hr : r.Prime) (hrn : r ∣ n)
    (hrsq : ¬ r^2 ∣ n) (hc : (s^2).Coprime 2) (hsr : s ∣ 1+r)
    (hssq : ¬ s^2 ∣ n) (hdiv : s ∣ p^d + 1) :
    n.factorization p % (2*d) ≠ d := by
  intro he
  obtain ⟨hpos,hprod⟩ := sum_udiv_of_isUnitaryPerfect hn
  rw [sum_udiv_eq_prod hpos.ne'] at hprod
  have her : n.factorization r = 1 := by
    have hle := mt (hr.pow_dvd_iff_le_factorization hpos.ne').mpr hrsq
    have hge := hr.factorization_pos_of_dvd hpos.ne' hrn
    omega
  have hds : s ∣ 1 + p ^ n.factorization p := by
    rw [add_comm]
    exact hdiv.trans (odd_multiple_factor he)
  have hs : ({p,r} : Finset ℕ) ⊆ n.primeFactors := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Nat.mem_primeFactors.mpr ⟨hp,hpn,hpos.ne'⟩, Nat.mem_primeFactors.mpr ⟨hr,hrn,hpos.ne'⟩⟩
  have hsub := Finset.prod_dvd_prod_of_subset _ _ (fun x : ℕ => 1+x^n.factorization x) hs
  rw [Finset.prod_insert (by simpa using hpr), Finset.prod_singleton, her, pow_one, hprod] at hsub
  apply hssq
  apply hc.dvd_of_dvd_mul_left
  simpa only [pow_two] using (Nat.mul_dvd_mul hds hsr).trans hsub

lemma no_second_five {n p d : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hp19 : p ≠ 19) (h19 : 19 ∣ n)
    (h19sq : ¬ 19^2 ∣ n) (h5sq : ¬ 5^2 ∣ n) (hdiv : 5 ∣ p^d + 1) :
    n.factorization p % (2*d) ≠ d :=
  no_second_source hn hp hpn hp19 (by decide) h19 h19sq (by decide) (by decide) h5sq hdiv

lemma broad_fermat_four {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n % 32 = 16) (h19 : 19 ∣ n)
    (hsq : ∀ p ∈ ([5,19,257,641,1409] : List ℕ), ¬ p^2 ∣ n)
    (hsmall : ∀ p ∈ ([11,17,43,47,107] : List ℕ), ¬ p ∣ n) :
    65537 ^ 16 ∣ n ∧ (n.factorization 65537 % 32 = 16 ∨ 128 ∣ n.factorization 65537) := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega : 1 ≤ padicValNat 2 n)
  have hp : Nat.Prime 65537 := by norm_num
  have hF : 65537 ∣ n := required_divisor hn Nat.prime_two h2 (by decide) (d:=16) (by decide)
    (by rwa [Nat.factorization_def _ Nat.prime_two])
  have no257 : ¬ 257 ∣ n := fun h => hsmall _ (by decide : 43 ∈ ([11,17,43,47,107] : List ℕ))
    (next_prime hn (by norm_num : Nat.Prime 257) h (hsq _ (by decide)) (by decide) (by decide))
  have no641 : ¬ 641 ∣ n := fun h => hsmall 107 (by decide)
    (next_prime hn (by norm_num : Nat.Prime 641) h (hsq _ (by decide)) (by decide) (by decide))
  have no1409 : ¬ 1409 ∣ n := fun h => hsmall 47 (by decide)
    (next_prime hn (by norm_num : Nat.Prime 1409) h (hsq _ (by decide)) (by decide) (by decide))
  have b1 := excluded_residue hn hp hF (d:=1) (by decide) (by decide) (hsmall 11 (by decide))
  have b2 := no_second_five hn hp hF (by decide) h19 (hsq _ (by decide)) (hsq _ (by decide))
    (d:=2) (by decide)
  have b4 := excluded_residue hn hp hF (d:=4) (by decide) (by decide) (hsmall 17 (by decide))
  have b8 := excluded_residue hn hp hF (d:=8) (by decide) (by decide) no257
  have x2 := lift_power_of_two (by decide) (one_dvd _) b1
  have x4 := lift_power_of_two (by decide) x2 b2
  have x8 := lift_power_of_two (by decide) x4 b4
  have x16 := lift_power_of_two (by decide) x8 b8
  refine ⟨power_divides hn hp hF x16, ?_⟩
  by_cases h : n.factorization 65537 % 32 = 16
  · exact Or.inl h
  · have b32 := excluded_residue hn hp hF (d:=32) (by decide) (by decide) no1409
    have b64 := excluded_residue hn hp hF (d:=64) (by decide) (by decide) no641
    have x32 := lift_power_of_two (by decide) x16 h
    have x64 := lift_power_of_two (by decide) x32 b32
    exact Or.inr (lift_power_of_two (by decide) x64 b64)

lemma broad_fermat_six {n : ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n % 128 = 64) (h19 : 19 ∣ n)
    (hsq : ∀ p ∈ ([5,19,157,313] : List ℕ), ¬ p^2 ∣ n)
    (hsmall : ∀ p ∈ ([13,17,79,109] : List ℕ), ¬ p ∣ n) :
    67280421310721 ^ 8 ∣ n ∧ (274177 ^ 4 ∣ n ∨ 137089 ^ 8 ∣ n) := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega : 1 ≤ padicValNat 2 n)
  have he : n.factorization 2 % (2*64) = 64 := by rwa [Nat.factorization_def _ Nat.prime_two]
  have hL : 67280421310721 ∣ n := required_divisor hn Nat.prime_two h2 (by decide) (by decide) he
  have hM : 274177 ∣ n := required_divisor hn Nat.prime_two h2 (by decide) (by decide) he
  have largeP := prime_67280421310721
  have mp : Nat.Prime 274177 := by norm_num
  have sp : Nat.Prime 137089 := by norm_num
  constructor
  · have b1 := excluded_residue hn largeP hL (d:=1) (by decide) (by decide) (hsmall 109 (by decide))
    have b2 := excluded_residue hn largeP hL (d:=2) (by decide) (by decide) (hsmall 13 (by decide))
    have b4 := excluded_residue hn largeP hL (d:=4) (by decide) (by decide) (hsmall 17 (by decide))
    have x2 := lift_power_of_two (by decide) (one_dvd _) b1
    have x4 := lift_power_of_two (by decide) x2 b2
    exact power_divides hn largeP hL (lift_power_of_two (by decide) x4 b4)
  · by_cases hodd : n.factorization 274177 % 2 = 1
    · right
      have hS : 137089 ∣ n := required_divisor hn mp hM (d:=1) (by decide) (by decide) hodd
      have no157 : ¬ 157 ∣ n := fun h => hsmall 79 (by decide)
        (next_prime hn (by norm_num : Nat.Prime 157) h (hsq _ (by decide)) (by decide) (by decide))
      have no313 : ¬ 313 ∣ n := fun h => no157
        (next_prime hn (by norm_num : Nat.Prime 313) h (hsq _ (by decide)) (by decide) (by decide))
      have b1 := no_second_five hn sp hS (by decide) h19 (hsq _ (by decide)) (hsq _ (by decide))
        (d:=1) (by decide)
      have b2 := excluded_residue hn sp hS (d:=2) (by decide) (by decide) (hsmall 109 (by decide))
      have b4 := excluded_residue hn sp hS (d:=4) (by decide) (by decide) no313
      have x2 := lift_power_of_two (by decide) (one_dvd _) b1
      have x4 := lift_power_of_two (by decide) x2 b2
      exact power_divides hn sp hS (lift_power_of_two (by decide) x4 b4)
    · left
      have b2 := no_second_five hn mp hM (by decide) h19 (hsq _ (by decide)) (hsq _ (by decide))
        (d:=2) (by decide)
      have x2 := lift_power_of_two (by decide) (one_dvd _) hodd
      exact power_divides hn mp hM (lift_power_of_two (by decide) x2 b2)

/-- The exact power of two in the exponent selects a Fermat number before the odd cofactor enters.
A prime divisor congruent to 2 modulo 3 must occur among the repeated primes. -/
lemma high_singleton_factor {n : ℕ} {S : Finset ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hge : ∀ z ∈ S, 2100 ≤ z) (h2 : 2 ∣ n) (h5 : 5 ∣ n)
    (ha : 256 ∣ padicValNat 2 n) (ha0 : padicValNat 2 n ≠ 0) :
    ∃ k t z : ℕ, 8 ≤ k ∧ Odd t ∧ padicValNat 2 n = 2 ^ k * t ∧ z ∈ S ∧
      z % 3 = 2 ∧ z ∣ Nat.fermatNumber k ∧ 2 ^ (k + 2) ∣ z - 1 := by
  obtain ⟨k,t,ht,he⟩ := Nat.exists_eq_two_pow_mul_odd ha0
  have hk : 8 ≤ k := by
    by_contra! hsmall
    obtain ⟨u,hu⟩ := ht
    rw [he, hu] at ha
    interval_cases k <;> norm_num at ha <;> omega
  have hF3 : Nat.fermatNumber k % 3 = 2 := by
    obtain ⟨i,hi⟩ : ∃ i, k = i + 1 := ⟨k-1, by omega⟩
    have hpow : (2 : ℕ) ^ 2 ^ k % 3 = 1 := by
      rw [hi, pow_succ', pow_mul, Nat.pow_mod]
      norm_num
    unfold Nat.fermatNumber
    omega
  obtain ⟨z,hzp,hzF,hz3⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1.exists_prime_mod3 _ hF3
  obtain ⟨b,hb⟩ := Nat.fermat_primeFactors_one_lt k z (by omega) hzp hzF
  have hpow : 8 ≤ (2:ℕ) ^ (k+2) := le_trans (by decide : 8 ≤ (2:ℕ)^3)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hzbig : 5 < z := by
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb; exact hzp.ne_one hb
    have hbpos : 1 ≤ b := by omega
    have := Nat.mul_le_mul_right (2^(k+2)) hbpos
    simp only [one_mul] at this
    omega
  have hroot : z ∣ 2 ^ padicValNat 2 n + 1 := by
    have hmul := ht.nat_add_dvd_pow_add_pow ((2:ℕ) ^ 2 ^ k) 1
    rw [one_pow, ← pow_mul, ← he] at hmul
    exact hzF.trans hmul
  have hz2 : ¬ 2 ∣ z := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hzp).mp h
    omega
  have hzn := component_divisor hn Nat.prime_two h2
    (Nat.prime_two.coprime_iff_not_dvd.mpr hz2).symm (by rwa [Nat.factorization_def _ Nat.prime_two])
  have hs (p : ℕ) (h : p.Prime) (h₂ : p ≠ 2) (hl : p < 2100) : ¬ p^2 ∣ n :=
    fun hd => (hge p ((hS p).mpr ⟨h,h₂,hd⟩)).not_gt hl
  have h1 : n.factorization z % 2 ≠ 1 := no_second_source hn hzp hzn (by omega : z ≠ 5)
    (by decide) h5 (hs 5 (by decide) (by decide) (by decide)) (by decide : (3^2 : ℕ).Coprime 2)
    (by decide) (hs 3 (by decide) (by decide) (by decide)) (d:=1) (by simp; omega)
  have hsq : z^2 ∣ n := power_divides hn hzp hzn (lift_power_of_two (by decide) (one_dvd _) h1)
  exact ⟨k,t,z,hk,ht,he,(hS z).mpr ⟨hzp,by omega,hsq⟩,hz3,hzF,⟨b, by rw [hb, Nat.add_sub_cancel, mul_comm]⟩⟩

lemma divisor_from_residue {p b d : ℕ} (h : (b : ZMod p) ^ d = -1) :
    p ∣ b ^ d + 1 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  rw [h, neg_add_cancel]


/-- Any explicitly forced subset supplies a lower bound for the admissibility product.
The actual cardinality of the kernel is at least that of the subset. -/
lemma obstruction {S T : Finset ℕ} (hT : T ⊆ S) (hs : ∀ z ∈ S, S.card + 3 ≤ z)
    (hlim : ∏ z ∈ S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    (hbad : (2101:ℚ)/2097 < ∏ z ∈ T, (((z:ℚ)+1)/((z:ℚ)-2-(T.card:ℚ)))) : False := by
  have hc : (T.card : ℚ) ≤ S.card := by exact_mod_cast Finset.card_le_card hT
  have hpos (z : ℕ) (hz : z ∈ S) : (S.card:ℚ)+3 ≤ z := by exact_mod_cast hs z hz
  have hmono : ∏ z ∈ T, (((z:ℚ)+1)/((z:ℚ)-2-(T.card:ℚ))) ≤
      ∏ z ∈ T, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) := by
    apply Finset.prod_le_prod
    · intro z hz
      have h := hpos z (hT hz)
      exact div_nonneg (by positivity) (by linarith)
    · intro z hz
      have h := hpos z (hT hz)
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hone (z : ℕ) (hz : z ∈ S) : (1:ℚ) ≤ ((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ)) := by
    have h := hpos z hz
    have hc0 : (0:ℚ) ≤ S.card := by positivity
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hsub := Finset.prod_le_prod_of_subset_of_one_le (f := fun z : ℕ => ((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ)))
    hT (fun z hz => (hone z (hT hz)).trans' (by norm_num)) (fun z hz _ => hone z hz)
  exact hbad.not_ge (hmono.trans (hsub.trans hlim))

lemma forced_repeat {n r p d : ℕ} {S : Finset ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ q, q ∈ S ↔ q.Prime ∧ q ≠ 2 ∧ q^2 ∣ n)
    (ha : padicValNat 2 n % (2*d) = d) (hd : d ≠ 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p.Coprime 2) (hseed : p ∣ 2^d + 1)
    (hr : r.Coprime 2) (hrs : r ∣ p+1) (hrn : ¬ r ∣ n) : p ∈ S := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by
    by_contra! h
    have : padicValNat 2 n = 0 := by omega
    simp [this] at ha
    exact hd ha.symm)
  have he : n.factorization 2 % (2*d) = d := by rwa [Nat.factorization_def _ Nat.prime_two]
  have hpn := required_divisor hn Nat.prime_two h2 hpc hseed he
  refine (hS p).mpr ⟨hp,hp2,?_⟩
  by_contra hs
  exact hrn (next_prime hn hp hpn hs hr hrs)


lemma exclude_21328 {n : ℕ} {S : Finset ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ q, q ∈ S ↔ q.Prime ∧ q ≠ 2 ∧ q^2 ∣ n) (hadm : ∀ z ∈ S, S.card + 3 ≤ z)
    (hlim : ∏ z ∈ S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    (hno : ∀ q ∈ ([17,13] : List ℕ), ¬ q ∣ n) :
    padicValNat 2 n % 42656 ≠ 21328 := by
  intro ha
  have m2753 : 2753 ∈ S := forced_repeat hn hS (d:=21328) ha (by decide)
    (by norm_num) (by decide) (by decide) (divisor_from_residue (by reduce_mod_char))
    (by decide) (by decide) (hno 17 (by decide))
  have m5953 : 5953 ∈ S := forced_repeat hn hS (d:=21328) ha (by decide)
    (by norm_num) (by decide) (by decide) (divisor_from_residue (by reduce_mod_char))
    (by decide) (by decide) (hno 13 (by decide))
  apply obstruction (T := {2753,5953}) _ hadm hlim
  · norm_num [Finset.prod_insert, Finset.card_insert_of_notMem, Finset.prod_singleton]
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact m2753
    · exact m5953

lemma exclude_19136 {n : ℕ} {S : Finset ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ q, q ∈ S ↔ q.Prime ∧ q ≠ 2 ∧ q^2 ∣ n) (hadm : ∀ z ∈ S, S.card + 3 ≤ z)
    (hlim : ∏ z ∈ S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    (hno : ∀ q ∈ ([37,13] : List ℕ), ¬ q ∣ n) :
    padicValNat 2 n % 38272 ≠ 19136 := by
  intro ha
  have m3329 : 3329 ∈ S := forced_repeat hn hS (d:=19136) ha (by decide)
    (by norm_num) (by decide) (by decide) (divisor_from_residue (by reduce_mod_char))
    (by decide) (by decide) (hno 37 (by decide))
  have m11777 : 11777 ∈ S := forced_repeat hn hS (d:=19136) ha (by decide)
    (by norm_num) (by decide) (by decide) (divisor_from_residue (by reduce_mod_char))
    (by decide) (by decide) (hno 13 (by decide))
  apply obstruction (T := {3329,11777}) _ hadm hlim
  · norm_num [Finset.prod_insert, Finset.card_insert_of_notMem, Finset.prod_singleton]
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact m3329
    · exact m11777

lemma exclude_13440 {n : ℕ} {S : Finset ℕ} (hn : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ q, q ∈ S ↔ q.Prime ∧ q ≠ 2 ∧ q^2 ∣ n) (hadm : ∀ z ∈ S, S.card + 3 ≤ z)
    (hlim : ∏ z ∈ S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    (hno : ∀ q ∈ ([23,283,29,11] : List ℕ), ¬ q ∣ n) :
    padicValNat 2 n % 26880 ≠ 13440 := by
  intro ha
  have m7681 : 7681 ∈ S := forced_repeat hn hS (d:=13440) ha (by decide)
    (by norm_num) (by decide) (by decide) (divisor_from_residue (by reduce_mod_char))
    (by decide) (by decide) (hno 23 (by decide))
  have m10753 : 10753 ∈ S := forced_repeat hn hS (d:=13440) ha (by decide)
    (by norm_num) (by decide) (by decide) (divisor_from_residue (by reduce_mod_char))
    (by decide) (by decide) (hno 283 (by decide))
  have m17921 : 17921 ∈ S := forced_repeat hn hS (d:=13440) ha (by decide)
    (by norm_num) (by decide) (by decide) (divisor_from_residue (by reduce_mod_char))
    (by decide) (by decide) (hno 29 (by decide))
  have m161281 : 161281 ∈ S := forced_repeat hn hS (d:=13440) ha (by decide)
    (by norm_num) (by decide) (by decide) (divisor_from_residue (by reduce_mod_char))
    (by decide) (by decide) (hno 11 (by decide))
  apply obstruction (T := {7681,10753,17921,161281}) _ hadm hlim
  · norm_num [Finset.prod_insert, Finset.card_insert_of_notMem, Finset.prod_singleton]
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact m7681
    · exact m10753
    · exact m17921
    · exact m161281

lemma two_repeats {n p q e f : ℕ} {S : Finset ℕ}
    (hS : ∀ r, r ∈ S ↔ r.Prime ∧ r ≠ 2 ∧ r ^ 2 ∣ n)
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hneq : p ≠ q)
    (he : 2 ≤ e) (hf : 2 ≤ f) (hpn : p^e ∣ n) (hqn : q^f ∣ n) : 2 ≤ S.card :=
  Finset.one_lt_card.mpr ⟨p,(hS p).mpr ⟨hp,hp2,Nat.pow_dvd_of_le_of_pow_dvd he hpn⟩,
    q,(hS q).mpr ⟨hq,hq2,Nat.pow_dvd_of_le_of_pow_dvd hf hqn⟩,hneq⟩

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    607 ∣ n →
    S = {65537} → padicValNat 2 n % 32 = 16 → 65537 ^ 16 ∣ n →
    (n.factorization 65537 % 32 = 16 ∨ 128 ∣ n.factorization 65537) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    607 ∣ n →
    S.card = 1 → 256 ∣ padicValNat 2 n →
    (∃ k t z : ℕ, 8 ≤ k ∧ Odd t ∧ padicValNat 2 n = 2 ^ k * t ∧ z ∈ S ∧
      z % 3 = 2 ∧ z ∣ Nat.fermatNumber k ∧ 2 ^ (k+2) ∣ z-1) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    607 ∣ n →
    2 ≤ S.card →
    (padicValNat 2 n % 128 = 64 → 67280421310721 ^ 8 ∣ n ∧ (274177 ^ 4 ∣ n ∨ 137089 ^ 8 ∣ n)) →
    (padicValNat 2 n % 256 = 128 → 59649589127497217 ^ 16 ∣ n ∧
      (5704689200685129054721 ^ 8 ∣ n ∨ 407477800048937789623 ^ 4 ∣ n)) →
    padicValNat 2 n % 42656 ≠ 21328 → padicValNat 2 n % 38272 ≠ 19136 →
    padicValNat 2 n % 26880 ≠ 13440 →
    padicValNat 2 n ≤ A
theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1.H3 := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩ ⟨C,hC⟩
  refine ⟨max A (max B C), ?_⟩
  intro n hn hns S hS hadm hlim h4 h3 h5 h7 h19 hres h16 hn32 h31 hgap h607
  specialize hA n hn hns S hS hadm hlim h4 h3 h5 h7 h19 hres h16 hn32 h31 hgap h607
  specialize hB n hn hns S hS hadm hlim h4 h3 h5 h7 h19 hres h16 hn32 h31 hgap h607
  specialize hC n hn hns S hS hadm hlim h4 h3 h5 h7 h19 hres h16 hn32 h31 hgap h607
  have hN : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z :=
    fun z hz => ⟨((hS z).mp hz).1, hadm z hz⟩
  have hge := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1.adm_ge_2100 hN hlim
  have sqgap {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hlt : p < 2100) : ¬ p^2 ∣ n :=
    fun hd => (hge p ((hS p).mpr ⟨hp,hp2,hd⟩)).not_gt hlt
  have small : ∀ p ∈ ([11,13,17,23,29,37,43,47,59,71,79,97,107,109,113,139] : List ℕ), ¬ p ∣ n := by
    intro p hp hpn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      have h := hgap _ (by norm_num) hpn (by decide)
      norm_num at h
  have nosq : ∀ p ∈ ([5,19,157,257,277,283,313,367,641,733,1409] : List ℕ), ¬ p^2 ∣ n := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact sqgap (by norm_num) (by decide) (by decide)
  have smalls (l : List ℕ) (hl : l ⊆ ([11,13,17,23,29,37,43,47,59,71,79,97,107,109,113,139] : List ℕ)) :
      ∀ p ∈ l, ¬ p ∣ n := fun _ h => small _ (hl h)
  have squares (l : List ℕ) (hl : l ⊆ ([5,19,157,257,277,283,313,367,641,733,1409] : List ℕ)) :
      ∀ p ∈ l, ¬ p^2 ∣ n := fun _ h => nosq _ (hl h)
  have six := fun h => broad_fermat_six hn h h19 (squares _ (by decide)) (smalls _ (by decide))
  have seven := fun h => fermat_seven_forces_two_powers hn h hgap (squares _ (by decide))
  by_cases multi : 2 ≤ S.card
  · have n283 : ¬ 283 ∣ n := fun h => small 71 (by decide)
      (next_prime hn (by norm_num : Nat.Prime 283) h (nosq _ (by decide)) (by decide) (by decide))
    have obs := fun z hz => (hadm z hz).2
    have hblock : ∀ p ∈ ([23,283,29,11] : List ℕ), ¬ p ∣ n := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact small 23 (by decide)
      · exact n283
      · exact small 29 (by decide)
      · exact small 11 (by decide)
    exact (hC multi six seven (exclude_21328 hn hS obs hlim (smalls _ (by decide)))
      (exclude_19136 hn hS obs hlim (smalls _ (by decide))) (exclude_13440 hn hS obs hlim hblock)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨z,hz,-,-⟩ := (hres S (Finset.Subset.refl _) hN hlim).1
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨z,hz⟩
  have hone : S.card = 1 := by omega
  by_cases hm : padicValNat 2 n % 32 = 16
  · obtain ⟨hpow,he⟩ := broad_fermat_four hn hm h19 (squares _ (by decide)) (smalls _ (by decide))
    have hz0 : 65537 ∈ S := (hS _).mpr ⟨by norm_num,by decide,Nat.pow_dvd_of_le_of_pow_dvd (by decide : 2 ≤ 16) hpow⟩
    have hset : S = {65537} := (Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr hz0) (by simpa using hone.le)).symm
    exact (hA hset hm hpow he).trans (le_max_left _ _)
  have h32 := lift_power_of_two (by decide) h16 hm
  have h64 := lift_power_of_two (by decide) h32 hn32
  have hn64 : padicValNat 2 n % 128 ≠ 64 := by
    intro h
    obtain ⟨hL,hM | hM⟩ := six h
    · exact multi (two_repeats hS prime_67280421310721 (by norm_num) (by decide) (by decide) (by decide)
        (by decide) (by decide) hL hM)
    · exact multi (two_repeats hS prime_67280421310721 (by norm_num) (by decide) (by decide) (by decide)
        (by decide) (by decide) hL hM)
  have h128 := lift_power_of_two (by decide) h64 hn64
  have hn128 : padicValNat 2 n % 256 ≠ 128 := by
    intro h
    obtain ⟨hL,hM | hM⟩ := seven h
    · exact multi (two_repeats hS prime_59649589127497217 prime_5704689200685129054721
        (by decide) (by decide) (by decide) (by decide) (by decide) hL hM)
    · exact multi (two_repeats hS prime_59649589127497217 prime_407477800048937789623
        (by decide) (by decide) (by decide) (by decide) (by decide) hL hM)
  have h256 := lift_power_of_two (by decide) h128 hn128
  by_cases ha0 : padicValNat 2 n = 0
  · rw [ha0]; exact Nat.zero_le _
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr ha0)
  exact (hB hone h256 (high_singleton_factor hn hS hge h2 h5 h256 ha0)).trans
    ((le_max_left _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R2
