import OMAStatements.S_oeis_a051179
import Mathlib.NumberTheory.Fermat
import Mathlib.Tactic.ReduceModChar

namespace OMA.R_oeis_a051179_R1

open OMA.S_oeis_a051179 (a)

/-- Compare adjacent Fermat numbers when the incoming number has three or four prime
    factors counted with multiplicity and the size of the previous prime makes the product bound inconclusive. -/
def H1 : Prop :=
  ∀ n p : ℕ, 8 ≤ n → p.Prime → p ∣ Nat.fermatNumber (n - 1) →
    2 ^ (n + 2) + 1 < p →
    let f := Nat.fermatNumber n
    let k := f.primeFactorsList.length
    3 ≤ k → k ≤ 4 → f ≤ (p - 1) ^ k →
    ∃ q ∈ f.primeFactorsList, p < q

/-- Make the same adjacent comparison for incoming numbers with at least five prime factors. -/
def H2 : Prop :=
  ∀ n p : ℕ, 8 ≤ n → p.Prime → p ∣ Nat.fermatNumber (n - 1) →
    2 ^ (n + 2) + 1 < p →
    let f := Nat.fermatNumber n
    let k := f.primeFactorsList.length
    5 ≤ k → f ≤ (p - 1) ^ k →
    ∃ q ∈ f.primeFactorsList, p < q

section

private theorem prefix_product (n : ℕ) :
    a n = ∏ j ∈ Finset.range n, Nat.fermatNumber j := by
  rw [Nat.prod_fermatNumber, Nat.fermatNumber, a]
  omega

private theorem factor_from_prefix {n p : ℕ} (hp : p ∈ (a n).primeFactors) :
    ∃ j < n, p ∣ Nat.fermatNumber j := by
  have h := Nat.mem_primeFactors.mp hp
  have hd : p ∣ ∏ j ∈ Finset.range n, Nat.fermatNumber j := by
    rw [← prefix_product]
    exact h.2.1
  obtain ⟨j, hj, hd⟩ := (h.1.prime.dvd_finsetProd_iff Nat.fermatNumber).mp hd
  exact ⟨j, Finset.mem_range.mp hj, hd⟩

private theorem next_factor_mem {m q : ℕ} (hq : q.Prime)
    (hd : q ∣ Nat.fermatNumber m) : q ∈ (a (m + 1)).primeFactors := by
  apply Nat.mem_primeFactors.mpr
  refine ⟨hq, ?_, ?_⟩
  · rw [prefix_product, Finset.prod_range_succ]
    exact dvd_mul_of_dvd_right hd _
  · rw [prefix_product, Nat.prod_fermatNumber]
    have := Nat.three_le_fermatNumber (m + 1)
    omega

private theorem lucas_from_prime_factors {p : ℕ} (base : ZMod p) (factors : List ℕ)
    (hp : 1 < p) (hprod : factors.prod = p - 1) (hprime : ∀ q ∈ factors, q.Prime)
    (hfull : base ^ (p - 1) = 1)
    (hproper : ∀ q ∈ factors, base ^ ((p - 1) / q) ≠ 1) : p.Prime := by
  have hperm := Nat.primeFactorsList_unique hprod hprime
  apply lucas_primality p base hfull
  intro q hq hd
  exact hproper q (hperm.mem_iff.mpr (Nat.mem_primeFactorsList'.mpr ⟨hq, hd, by omega⟩))

private theorem prime_6700417 : Nat.Prime 6700417 := by
  refine lucas_from_prime_factors 5 (List.replicate 7 2 ++ [3, 17449]) (by decide) (by decide) ?_ ?_ ?_
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    all_goals
      norm_num only [Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

private theorem prime_166571 : Nat.Prime 166571 := by
  refine lucas_from_prime_factors 2 [2, 5, 16657] (by decide) (by decide) ?_ ?_ ?_
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    all_goals
      norm_num only [Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

private theorem prime_2998279 : Nat.Prime 2998279 := by
  refine lucas_from_prime_factors 3 (List.replicate 2 3 ++ [2, 166571]) (by decide) (by decide) ?_ ?_ ?_
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl <;> first | exact prime_166571 | norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    all_goals
      norm_num only [Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

private theorem prime_67280421310721 : Nat.Prime 67280421310721 := by
  refine lucas_from_prime_factors 3 (List.replicate 8 2 ++ [5, 47, 373, 2998279]) (by decide) (by decide) ?_ ?_ ?_
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> first | exact prime_2998279 | norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

private theorem prime_6939437 : Nat.Prime 6939437 := by
  refine lucas_from_prime_factors 2 (List.replicate 2 2 ++ [7, 139, 1783]) (by decide) (by decide) ?_ ?_ ?_
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

private theorem prime_55515497 : Nat.Prime 55515497 := by
  refine lucas_from_prime_factors 3 (List.replicate 3 2 ++ [6939437]) (by decide) (by decide) ?_ ?_ ?_
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl <;> first | exact prime_6939437 | norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    all_goals
      norm_num only [Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

private theorem prime_733803839347 : Nat.Prime 733803839347 := by
  refine lucas_from_prime_factors 2 [2, 3, 2203, 55515497] (by decide) (by decide) ?_ ?_ ?_
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl <;> first | exact prime_55515497 | norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

private theorem prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 := by
  refine lucas_from_prime_factors 21 (List.replicate 9 2 ++ List.replicate 5 3 ++ [5, 12497, 733803839347]) (by decide) (by decide) ?_ ?_ ?_
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> first | exact prime_733803839347 | norm_num
  · norm_num only [Nat.reduceSub]
    reduce_mod_char
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num only [Nat.reduceSub, Nat.reduceDiv]
      reduce_mod_char
      decide

private theorem initial_large_factor (n : ℕ) (hn : 1 ≤ n) (hn7 : n ≤ 7) :
    ∃ q, q.Prime ∧ q ∣ Nat.fermatNumber n ∧ Nat.fermatNumber (n - 1) ≤ q := by
  have h : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨5, by norm_num, by decide, by decide⟩
  · exact ⟨17, by norm_num, by decide, by decide⟩
  · exact ⟨257, by norm_num, by decide, by decide⟩
  · exact ⟨65537, by norm_num, by decide, by decide⟩
  · exact ⟨6700417, prime_6700417, by decide, by decide⟩
  · exact ⟨67280421310721, prime_67280421310721, by decide, by decide⟩
  · exact ⟨5704689200685129054721, prime_5704689200685129054721, by decide, by decide⟩

private theorem list_prod_le_pow (xs : List ℕ) (b : ℕ) (h : ∀ p ∈ xs, p ≤ b) :
    xs.prod ≤ b ^ xs.length := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    simpa only [List.prod_cons, List.length_cons, pow_succ'] using
      Nat.mul_le_mul (h p (by simp)) (ih fun q hq => h q (by simp [hq]))

private theorem fermat_pos (n : ℕ) : 0 < Nat.fermatNumber n :=
  lt_of_lt_of_le (by decide) (Nat.three_le_fermatNumber n)

private theorem adjacent_factor_ne {n p q : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hpd : p ∣ Nat.fermatNumber (n - 1)) (hqd : q ∣ Nat.fermatNumber n) : p ≠ q := by
  intro heq
  subst q
  have h := Nat.dvd_gcd hpd hqd
  rw [show (Nat.fermatNumber (n - 1)).gcd (Nat.fermatNumber n) = 1 from
    Nat.coprime_fermatNumber_fermatNumber (by omega : n - 1 ≠ n)] at h
  exact hp.ne_one (Nat.dvd_one.mp h)

private theorem adjacent_comparison (h1 : H1) (h2 : H2) {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hpd : p ∣ Nat.fermatNumber (n - 1)) :
    ∃ q, q.Prime ∧ q ∣ Nat.fermatNumber n ∧ p < q := by
  have hp_le : p ≤ Nat.fermatNumber (n - 1) := Nat.le_of_dvd (fermat_pos _) hpd
  by_cases hn7 : n ≤ 7
  · obtain ⟨q, hq, hqd, hbound⟩ := initial_large_factor n hn hn7
    exact ⟨q, hq, hqd, lt_of_le_of_ne (hp_le.trans hbound) (adjacent_factor_ne hn hp hpd hqd)⟩
  have hn8 : 8 ≤ n := by omega
  by_cases hp_large : 2 ^ (n + 2) + 1 < p
  swap
  · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (Nat.fermatNumber_ne_one n)
    obtain ⟨c, hc⟩ := Nat.fermat_primeFactors_one_lt n q (by omega) hq hqd
    have hcpos : 1 ≤ c := by
      by_contra h
      have hc0 : c = 0 := by omega
      simp [hc0] at hc
      exact hq.ne_one hc
    have hbound : 2 ^ (n + 2) + 1 ≤ q := by
      rw [hc]
      simpa using Nat.add_le_add_right (Nat.mul_le_mul_right (2 ^ (n + 2)) hcpos) 1
    exact ⟨q, hq, hqd, lt_of_le_of_ne ((le_of_not_gt hp_large).trans hbound)
      (adjacent_factor_ne hn hp hpd hqd)⟩
  let f := Nat.fermatNumber n
  let k := f.primeFactorsList.length
  by_cases hsize : f ≤ (p - 1) ^ k
  swap
  · have hlarge : ∃ q ∈ f.primeFactorsList, p - 1 < q := by
      by_contra h
      have hall : ∀ q ∈ f.primeFactorsList, q ≤ p - 1 :=
        fun q hq => le_of_not_gt (fun hgt => h ⟨q, hq, hgt⟩)
      exact hsize (by
        simpa only [f, k, Nat.prod_primeFactorsList (fermat_pos n).ne'] using
          list_prod_le_pow f.primeFactorsList (p - 1) hall)
    obtain ⟨q, hq, hgt⟩ := hlarge
    obtain ⟨hqprime, hqd, _⟩ := Nat.mem_primeFactorsList'.mp hq
    exact ⟨q, hqprime, hqd, lt_of_le_of_ne (by omega) (adjacent_factor_ne hn hp hpd hqd)⟩
  have hk : 3 ≤ k := by
    by_contra h
    have hk2 : k ≤ 2 := by omega
    have hprev : 0 < Nat.fermatNumber (n - 1) - 1 := by
      have := Nat.three_le_fermatNumber (n - 1)
      omega
    have hpow : (p - 1) ^ k ≤ (Nat.fermatNumber (n - 1) - 1) ^ 2 :=
      (Nat.pow_le_pow_left (Nat.sub_le_sub_right hp_le 1) k).trans (Nat.pow_le_pow_right hprev hk2)
    have hn' : n - 1 + 1 = n := by omega
    have hsucc : f = (Nat.fermatNumber (n - 1) - 1) ^ 2 + 1 := by
      simpa only [f, hn'] using Nat.fermatNumber_succ (n - 1)
    omega
  have hnext : ∃ q ∈ f.primeFactorsList, p < q := by
    by_cases hk4 : k ≤ 4
    · exact h1 n p hn8 hp hpd hp_large hk hk4 hsize
    · exact h2 n p hn8 hp hpd hp_large (show 5 ≤ k by omega) hsize
  obtain ⟨q, hq, hgt⟩ := hnext
  obtain ⟨hqprime, hqd, _⟩ := Nat.mem_primeFactorsList'.mp hq
  exact ⟨q, hqprime, hqd, hgt⟩

private theorem factor_dominated (h1 : H1) (h2 : H2) (m : ℕ) :
    ∀ j ≤ m, ∀ p, p.Prime → p ∣ Nat.fermatNumber j →
      ∃ q, q.Prime ∧ q ∣ Nat.fermatNumber m ∧ p ≤ q := by
  induction m with
  | zero =>
    intro j hj p hp hd
    have h : j = 0 := by omega
    subst j
    exact ⟨p, hp, hd, le_rfl⟩
  | succ m ih =>
    intro j hj p hp hd
    rcases eq_or_lt_of_le hj with heq | hlt
    · subst j
      exact ⟨p, hp, hd, le_rfl⟩
    · obtain ⟨r, hr, hrd, hpr⟩ := ih j (by omega) p hp hd
      obtain ⟨q, hq, hqd, hrq⟩ :=
        adjacent_comparison h1 h2 (n := m + 1) (by omega) hr hrd
      exact ⟨q, hq, hqd, hpr.trans hrq.le⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a051179.main := by
  intro h1 h2 n hn
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (Nat.fermatNumber_ne_one n)
  let s := (Nat.fermatNumber n).primeFactors
  have hs : s.Nonempty := ⟨r, Nat.mem_primeFactors.mpr ⟨hr, hrd, (fermat_pos n).ne'⟩⟩
  let q := s.max' hs
  have hqmem : q ∈ s := Finset.max'_mem s hs
  obtain ⟨hq, hqd, _⟩ := Nat.mem_primeFactors.mp hqmem
  refine ⟨q, next_factor_mem hq hqd, ?_⟩
  intro p hp
  obtain ⟨j, hj, hpd⟩ := factor_from_prefix hp
  obtain ⟨t, ht, htd, hpt⟩ := factor_dominated h1 h2 (n - 1) j (by omega) p
    (Nat.mem_primeFactors.mp hp).1 hpd
  obtain ⟨u, hu, hud, htu⟩ := adjacent_comparison h1 h2 hn ht htd
  have humem : u ∈ s := Nat.mem_primeFactors.mpr ⟨hu, hud, (fermat_pos n).ne'⟩
  have huq : u ≤ q := s.le_max' u humem
  exact (hpt.trans_lt htu).trans_le huq

end

end OMA.R_oeis_a051179_R1
