import OMAStatements.S_oeis_a193679
import Mathlib

namespace A193679Aux

def B (n : ℕ) : ℕ := ∏ d ∈ n.divisors, OMA.S_oeis_a193679.expMangoldt d ^ Nat.totient (n / d)

lemma B_filter (n : ℕ) :
    B n = ∏ d ∈ n.divisors.filter IsPrimePow, d.minFac ^ Nat.totient (n / d) := by
  unfold B
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro d _
  unfold OMA.S_oeis_a193679.expMangoldt
  by_cases h : IsPrimePow d
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, one_pow]

lemma sum_tot (p : ℕ) (hp : p.Prime) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), Nat.totient (p ^ i) = p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm : 0 < m + 1 := by omega
    rw [Finset.sum_range_succ, ih, Nat.totient_prime_pow hp hm]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    simp only [Nat.add_sub_cancel]
    ring

lemma B_pp (p m : ℕ) (hp : p.Prime) : B (p ^ (m + 1)) = p ^ p ^ m := by
  have h0 : OMA.S_oeis_a193679.expMangoldt (p ^ 0) = 1 := by
    unfold OMA.S_oeis_a193679.expMangoldt
    rw [pow_zero, if_neg not_isPrimePow_one]
  have hj : ∀ j ∈ Finset.range (m + 1),
      OMA.S_oeis_a193679.expMangoldt (p ^ (j + 1)) ^ Nat.totient (p ^ (m + 1) / p ^ (j + 1))
        = p ^ Nat.totient (p ^ (m + 1 - 1 - j)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj1 : j + 1 ≠ 0 := by omega
    have hle : j + 1 ≤ m + 1 := by omega
    have hpp : IsPrimePow (p ^ (j + 1)) := hp.isPrimePow.pow hj1
    have e : m + 1 - (j + 1) = m + 1 - 1 - j := by omega
    unfold OMA.S_oeis_a193679.expMangoldt
    rw [if_pos hpp, hp.pow_minFac hj1, Nat.pow_div hle hp.pos, e]
  have hs : ∑ j ∈ Finset.range (m + 1), Nat.totient (p ^ (m + 1 - 1 - j)) = p ^ m :=
    (Finset.sum_range_reflect (fun i => Nat.totient (p ^ i)) (m + 1)).trans (sum_tot p hp m)
  have key : ∏ x ∈ Finset.range (m + 1 + 1),
      OMA.S_oeis_a193679.expMangoldt (p ^ x) ^ Nat.totient (p ^ (m + 1) / p ^ x) = p ^ p ^ m := by
    rw [Finset.prod_range_succ', h0, one_pow, mul_one, Finset.prod_congr rfl hj,
      Finset.prod_pow_eq_pow_sum, hs]
  unfold B
  rw [Nat.divisors_prime_pow hp, Finset.prod_map]
  exact key

lemma a_pp (p m : ℕ) (hp : p.Prime) : OMA.S_oeis_a193679.a (p ^ (m + 1)) = p ^ p ^ m := by
  have hm0 : m + 1 ≠ 0 := by omega
  have hm : 0 < m + 1 := by omega
  have h1 : m + 1 - 1 = m := by omega
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  unfold OMA.S_oeis_a193679.a
  rw [Nat.primeFactors_prime_pow hm0 hp, Finset.prod_singleton, Nat.totient_prime_pow hp hm,
    h1, Nat.mul_div_cancel _ hp1]

lemma expo (p x y : ℕ) (hp : p.Prime) (hpx : p ∣ x) (hxy : Nat.Coprime x y) :
    Nat.totient (x * y) / (p - 1) = Nat.totient x / (p - 1) * Nat.totient y := by
  have hd : (p - 1) ∣ Nat.totient x := by
    have h := Nat.totient_dvd_of_dvd hpx
    rw [Nat.totient_prime hp] at h
    exact h
  obtain ⟨c, hc⟩ := hd
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  rw [Nat.totient_mul hxy, hc, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp1,
    Nat.mul_div_cancel_left _ hp1]

lemma a_mul (x y : ℕ) (hxy : Nat.Coprime x y) :
    OMA.S_oeis_a193679.a (x * y)
      = OMA.S_oeis_a193679.a x ^ Nat.totient y * OMA.S_oeis_a193679.a y ^ Nat.totient x := by
  unfold OMA.S_oeis_a193679.a
  rw [hxy.primeFactors_mul, Finset.prod_union hxy.disjoint_primeFactors, ← Finset.prod_pow,
    ← Finset.prod_pow]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [expo p x y hp.1 hp.2.1 hxy, pow_mul]
  · apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mul_comm x y, expo p y x hp.1 hp.2.1 hxy.symm, pow_mul]

lemma B_mul (x y : ℕ) (hxy : Nat.Coprime x y) :
    B (x * y) = B x ^ Nat.totient y * B y ^ Nat.totient x := by
  have hset : (x * y).divisors.filter IsPrimePow
      = x.divisors.filter IsPrimePow ∪ y.divisors.filter IsPrimePow := by
    have h := Nat.mul_divisors_filter_prime_pow hxy
    rw [Finset.filter_union] at h
    exact h
  rw [B_filter (x * y), B_filter x, B_filter y, hset,
    Finset.prod_union (Nat.disjoint_divisors_filter_isPrimePow hxy), ← Finset.prod_pow,
    ← Finset.prod_pow]
  congr 1
  · apply Finset.prod_congr rfl
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨c, hc⟩ := hd.1.1
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hd.1.2)
    have e1 : x * y / d = c * y := by
      rw [hc, Nat.mul_assoc, Nat.mul_div_cancel_left _ hd0]
    have e2 : x / d = c := by
      rw [hc, Nat.mul_div_cancel_left _ hd0]
    have hcy : Nat.Coprime c y := Nat.Coprime.coprime_dvd_left (Dvd.intro_left d hc.symm) hxy
    rw [e1, e2, Nat.totient_mul hcy, pow_mul]
  · apply Finset.prod_congr rfl
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨c, hc⟩ := hd.1.1
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hd.1.2)
    have e1 : x * y / d = c * x := by
      rw [hc, Nat.mul_comm x (d * c), Nat.mul_assoc, Nat.mul_div_cancel_left _ hd0]
    have e2 : y / d = c := by
      rw [hc, Nat.mul_div_cancel_left _ hd0]
    have hcx : Nat.Coprime c x :=
      Nat.Coprime.coprime_dvd_left (Dvd.intro_left d hc.symm) hxy.symm
    rw [e1, e2, Nat.totient_mul hcx, pow_mul]

lemma key (n : ℕ) : OMA.S_oeis_a193679.a n = B n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [a_pp p m hp, B_pp p m hp]
  | zero => simp [OMA.S_oeis_a193679.a, B]
  | one => simp [OMA.S_oeis_a193679.a, B, OMA.S_oeis_a193679.expMangoldt, not_isPrimePow_one]
  | coprime x y hx hy hxy ihx ihy =>
    rw [a_mul x y hxy, B_mul x y hxy, ihx, ihy]

end A193679Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a193679.main := by
  intro n _
  exact A193679Aux.key n
