import OMAStatements.S_oeis_a365498
import Mathlib

namespace A365498Aux

lemma pf_mul (f : ℕ → ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) :
    ∏ p ∈ (m * n).primeFactors, f ((m * n).factorization p) =
      (∏ p ∈ m.primeFactors, f (m.factorization p)) *
        (∏ p ∈ n.primeFactors, f (n.factorization p)) := by
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    have hnd : ¬ p ∣ n := fun hd =>
      hp'.1.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h hp'.2.1 hd)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
  · apply Finset.prod_congr rfl
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    have hnd : ¬ p ∣ m := fun hd =>
      hp'.1.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h hd hp'.2.1)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, zero_add]

lemma pf_pp (f : ℕ → ℤ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ∏ q ∈ (p ^ k).primeFactors, f ((p ^ k).factorization q) = f k := by
  rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton, Nat.factorization_pow_self hp]

open OMA.S_oeis_a365498 in
lemma g_pp {p : ℕ} (hp : p.Prime) (i : ℕ) : g (p ^ i) = c i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [g, c]
  · exact pf_pp c hp hi.ne'

open OMA.S_oeis_a365498 in
lemma csum3 (k : ℕ) (hk : 3 ≤ k) : ∑ i ∈ Finset.range (k + 1), c i = 1 := by
  induction k, hk using Nat.le_induction with
  | base => simp [Finset.sum_range_succ, c]
  | succ j hj ih =>
    rw [Finset.sum_range_succ, ih]
    have h0 : c (j + 1) = 0 := by
      unfold c
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [h0, add_zero]

open OMA.S_oeis_a365498 in
lemma csum (k : ℕ) (hk : 0 < k) : ∑ i ∈ Finset.range (k + 1), c i =
    (if k = 1 then 2 else 1) * (if k = 2 then 2 else 1) := by
  obtain h | h | h : k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  · subst h
    simp [Finset.sum_range_succ, c]
  · subst h
    simp [Finset.sum_range_succ, c]
  · rw [csum3 k h, if_neg (by omega), if_neg (by omega)]
    norm_num

open OMA.S_oeis_a365498 in
lemma a_pp {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    a (p ^ k) = a056671 (p ^ k) * a368885 (p ^ k) := by
  have h1 : a (p ^ k) = ∑ i ∈ Finset.range (k + 1), c i := by
    unfold a
    rw [Nat.sum_divisors_prime_pow hp]
    exact Finset.sum_congr rfl (fun i _ => g_pp hp i)
  have h2 : a056671 (p ^ k) = if k = 1 then 2 else 1 :=
    pf_pp (fun e => if e = 1 then 2 else 1) hp hk.ne'
  have h3 : a368885 (p ^ k) = if k = 2 then 2 else 1 :=
    pf_pp (fun e => if e = 2 then 2 else 1) hp hk.ne'
  rw [h1, h2, h3, csum k hk]

open OMA.S_oeis_a365498 in
noncomputable def G : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else g n, by simp⟩

open OMA.S_oeis_a365498 in
lemma G_apply (n : ℕ) (hn : n ≠ 0) : G n = g n := by
  show (if n = 0 then 0 else g n) = g n
  rw [if_neg hn]

open OMA.S_oeis_a365498 in
lemma G_mult : G.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [G_apply 1 one_ne_zero]
    simp [g]
  · intro m n hm hn h
    rw [G_apply _ (mul_ne_zero hm hn), G_apply m hm, G_apply n hn]
    exact pf_mul c hm hn h

open OMA.S_oeis_a365498 in
lemma a_eq (n : ℕ) :
    a n = (G * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)) n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  unfold a
  apply Finset.sum_congr rfl
  intro d hd
  rw [G_apply d (Nat.pos_of_mem_divisors hd).ne']

open OMA.S_oeis_a365498 in
lemma a_mul {x y : ℕ} (h : x.Coprime y) : a (x * y) = a x * a y := by
  rw [a_eq (x * y), a_eq x, a_eq y]
  exact (G_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast).map_mul_of_coprime h

end A365498Aux

open OMA.S_oeis_a365498 in
theorem OMA.solution : type_of% @OMA.S_oeis_a365498.main := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    exact A365498Aux.a_pp hp k hk
  | zero =>
    intro h
    omega
  | one =>
    intro _
    simp [a, g, a056671, a368885]
  | coprime x y hx hy hxy ihx ihy =>
    intro _
    have hx0 : x ≠ 0 := by omega
    have hy0 : y ≠ 0 := by omega
    have e1 : a056671 (x * y) = a056671 x * a056671 y :=
      A365498Aux.pf_mul (fun e => if e = 1 then 2 else 1) hx0 hy0 hxy
    have e2 : a368885 (x * y) = a368885 x * a368885 y :=
      A365498Aux.pf_mul (fun e => if e = 2 then 2 else 1) hx0 hy0 hxy
    rw [A365498Aux.a_mul hxy, ihx (by omega), ihy (by omega), e1, e2]
    ring
