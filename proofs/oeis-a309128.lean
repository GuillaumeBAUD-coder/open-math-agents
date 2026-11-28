import OMAStatements.S_oeis_a309128
import Mathlib

/-!
Proof of the A309128 formula. Notation: `σ S = ∑ i ∈ S, i`, `U = Icc 1 n`, `N` = number of `S ⊆ U` with
`n ∣ σ S`, `T` = the sum of `σ S` over these `S`. Steps:
- complement `S ↦ U \ S` (odd `n`: class `0` to class `0`; even `n = 2m`: class `0` to class `m`);
- roots of unity filter with `w` a primitive `n`-th root of unity in `ℂ`:
  `n * N = ∑ j, ∏ i ∈ U, (1 + w^(j*i))`, evaluated through the order of `w^j` (gives A053636);
  for `n = 2m`: `n * (T_m - T_0) = n * 2 * m * φ n` from `H(z) = ∑ S, σ S * z^(σ S)` at odd `j`,
  where `H(w^j) = 0` unless `j` is coprime to `n`, and then `H(w^j) = -m * n`.
-/

namespace OMA.A309128Proof

open Finset

/-! ### Subset generating functions -/

theorem prod_one_add_pow {R : Type*} [CommSemiring R] (z : R) (U : Finset ℕ) :
    ∏ i ∈ U, (1 + z ^ i) = ∑ S ∈ U.powerset, z ^ (∑ i ∈ S, i) := by
  rw [Finset.prod_one_add]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  exact Finset.prod_pow_eq_pow_sum S (fun i => i) z

theorem sumH_insert {R : Type*} [CommSemiring R] (z : R) {a : ℕ} {s : Finset ℕ} (h : a ∉ s) :
    ∑ S ∈ (insert a s).powerset, ((∑ i ∈ S, i : ℕ) : R) * z ^ (∑ i ∈ S, i) =
      (1 + z ^ a) * ∑ S ∈ s.powerset, ((∑ i ∈ S, i : ℕ) : R) * z ^ (∑ i ∈ S, i) +
        (a : R) * z ^ a * ∏ i ∈ s, (1 + z ^ i) := by
  rw [Finset.sum_powerset_insert h]
  have key : ∀ t ∈ s.powerset,
      ((∑ i ∈ insert a t, i : ℕ) : R) * z ^ (∑ i ∈ insert a t, i) =
        z ^ a * (((∑ i ∈ t, i : ℕ) : R) * z ^ (∑ i ∈ t, i)) +
          (a : R) * z ^ a * z ^ (∑ i ∈ t, i) := by
    intro t ht
    have hat : a ∉ t := fun hh => h (Finset.mem_powerset.mp ht hh)
    rw [Finset.sum_insert hat, pow_add, Nat.cast_add]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, prod_one_add_pow, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

theorem sumH_eq_zero {R : Type*} [CommRing R] (z : R) {U : Finset ℕ} {i₁ i₂ : ℕ}
    (h₁ : i₁ ∈ U) (h₂ : i₂ ∈ U) (hne : i₁ ≠ i₂) (hz₁ : 1 + z ^ i₁ = 0) (hz₂ : 1 + z ^ i₂ = 0) :
    ∑ S ∈ U.powerset, ((∑ i ∈ S, i : ℕ) : R) * z ^ (∑ i ∈ S, i) = 0 := by
  have hp : ∏ i ∈ U.erase i₁, (1 + z ^ i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, h₂⟩) hz₂
  rw [← Finset.insert_erase h₁, sumH_insert z (Finset.notMem_erase i₁ U), hz₁, zero_mul, zero_add,
    hp, mul_zero]

theorem sumH_single {R : Type*} [CommRing R] (z : R) {U : Finset ℕ} {k : ℕ}
    (hk : k ∈ U) (hz : z ^ k = -1) :
    ∑ S ∈ U.powerset, ((∑ i ∈ S, i : ℕ) : R) * z ^ (∑ i ∈ S, i) =
      -(k : R) * ∏ i ∈ U.erase k, (1 + z ^ i) := by
  conv_lhs => rw [← Finset.insert_erase hk]
  rw [sumH_insert z (Finset.notMem_erase k U), hz]
  ring

/-! ### Products over intervals -/

theorem prod_Icc_eq_prod_range_succ {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∏ i ∈ Icc 1 k, f i = ∏ i ∈ range k, f (i + 1) := by
  induction k with
  | zero => rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by norm_num)]; simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (show 1 ≤ k + 1 by omega), Finset.prod_range_succ, ih]

theorem prod_Icc_eq_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) (h : f n = f 0) :
    ∏ i ∈ Icc 1 n, f i = ∏ i ∈ range n, f i := by
  cases n with
  | zero => rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by norm_num)]; simp
  | succ k =>
    rw [prod_Icc_eq_prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ', h]

theorem prod_range_mul_of_periodic {M : Type*} [CommMonoid M] (f : ℕ → M) (d : ℕ)
    (hf : ∀ k i, f (d * k + i) = f i) (g : ℕ) :
    ∏ i ∈ range (d * g), f i = (∏ i ∈ range d, f i) ^ g := by
  induction g with
  | zero => simp
  | succ k ih =>
    rw [mul_add_one, Finset.prod_range_add, ih, pow_succ]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => hf k i)

theorem sum_Icc_mul_two (n : ℕ) : (∑ i ∈ Icc 1 n, i) * 2 = n * (n + 1) := by
  induction n with
  | zero => rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by norm_num)]; simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega), add_mul, ih]
    ring

theorem dvd_iff_of_add {n A B c : ℕ} (h : A + B = n * c) : n ∣ A ↔ n ∣ B := by
  have hd : n ∣ A + B := by rw [h]; exact dvd_mul_right n c
  exact ⟨fun hA => (Nat.dvd_add_right hA).mp hd, fun hB => (Nat.dvd_add_left hB).mp hd⟩

/-! ### Roots of unity -/

theorem filter_sum {w : ℂ} {n : ℕ} (hw : IsPrimitiveRoot w n) (s : ℕ) :
    ∑ j ∈ range n, (w ^ j) ^ s = if n ∣ s then (n : ℂ) else 0 := by
  have e : ∀ j ∈ range n, (w ^ j) ^ s = (w ^ s) ^ j := fun j _ => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [Finset.sum_congr rfl e]
  split_ifs with h
  · rw [(hw.pow_eq_one_iff_dvd s).mpr h]
    simp
  · have h1 : w ^ s ≠ 1 := fun h' => h ((hw.pow_eq_one_iff_dvd s).mp h')
    have h2 : (w ^ s) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

theorem filter_card {w : ℂ} {n : ℕ} (hw : IsPrimitiveRoot w n) (U : Finset ℕ) :
    ∑ j ∈ range n, ∏ i ∈ U, (1 + (w ^ j) ^ i) =
      (n : ℂ) * ((U.powerset.filter (fun S => n ∣ ∑ i ∈ S, i)).card : ℂ) := by
  have e1 : ∀ j ∈ range n, ∏ i ∈ U, (1 + (w ^ j) ^ i) =
      ∑ S ∈ U.powerset, (w ^ j) ^ (∑ i ∈ S, i) := fun j _ => prod_one_add_pow (w ^ j) U
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ S ∈ U.powerset, ∑ j ∈ range n, (w ^ j) ^ (∑ i ∈ S, i) =
      if n ∣ ∑ i ∈ S, i then (n : ℂ) else 0 := fun S _ => filter_sum hw _
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem filter_H0 {w : ℂ} {n : ℕ} (hw : IsPrimitiveRoot w n) (U : Finset ℕ) :
    ∑ j ∈ range n, ∑ S ∈ U.powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i) =
      (n : ℂ) * ((∑ S ∈ U.powerset.filter (fun S => n ∣ ∑ i ∈ S, i), ∑ i ∈ S, i : ℕ) : ℂ) := by
  rw [Finset.sum_comm]
  have e2 : ∀ S ∈ U.powerset, ∑ j ∈ range n, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i) =
      if n ∣ ∑ i ∈ S, i then (n : ℂ) * ((∑ i ∈ S, i : ℕ) : ℂ) else 0 := by
    intro S _
    rw [← Finset.mul_sum, filter_sum hw]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter, Nat.cast_sum, Finset.mul_sum]

theorem filter_H {w : ℂ} {n : ℕ} (hw : IsPrimitiveRoot w n) (U : Finset ℕ) (r : ℕ) :
    ∑ j ∈ range n, (w ^ j) ^ r *
        ∑ S ∈ U.powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i) =
      (n : ℂ) *
        ((∑ S ∈ U.powerset.filter (fun S => n ∣ (∑ i ∈ S, i) + r), ∑ i ∈ S, i : ℕ) : ℂ) := by
  have e : ∀ j ∈ range n, (w ^ j) ^ r *
        ∑ S ∈ U.powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i) =
      ∑ S ∈ U.powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ ((∑ i ∈ S, i) + r) := by
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [pow_add]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  have e2 : ∀ S ∈ U.powerset,
      ∑ j ∈ range n, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ ((∑ i ∈ S, i) + r) =
        if n ∣ (∑ i ∈ S, i) + r then (n : ℂ) * ((∑ i ∈ S, i : ℕ) : ℂ) else 0 := by
    intro S _
    rw [← Finset.mul_sum, filter_sum hw]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter, Nat.cast_sum, Finset.mul_sum]

/-- `∏ (1 ≤ i ≤ 2m, i ≠ m) (1 + z^i) = 2m` for a primitive `2m`-th root of unity `z`. -/
theorem prod_erase_half {z : ℂ} {m : ℕ} (hz : IsPrimitiveRoot z (2 * m)) (hm : 0 < m)
    (hzm : z ^ m = -1) :
    ∏ i ∈ (Icc 1 (2 * m)).erase m, (1 + z ^ i) = ((2 * m : ℕ) : ℂ) := by
  have hmem : m ∈ Icc 1 (2 * m) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h1 : (Polynomial.X : Polynomial ℂ) ^ (2 * m) - Polynomial.C 1 =
      ∏ i ∈ range (2 * m), (Polynomial.X + Polynomial.C (z ^ i)) := by
    rw [X_pow_sub_C_eq_prod hz (by omega) (show ((-1 : ℂ)) ^ (2 * m) = 1 by
      rw [pow_mul]; norm_num)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [mul_neg_one, Polynomial.C_neg, sub_neg_eq_add]
  have h2 : ∏ i ∈ Icc 1 (2 * m), (Polynomial.X + Polynomial.C (z ^ i)) =
      ∏ i ∈ range (2 * m), (Polynomial.X + Polynomial.C (z ^ i)) :=
    prod_Icc_eq_prod_range (fun i => Polynomial.X + Polynomial.C (z ^ i)) (2 * m)
      (by simp only [hz.pow_eq_one, pow_zero])
  have h3 : ∏ i ∈ Icc 1 (2 * m), (Polynomial.X + Polynomial.C (z ^ i)) =
      (Polynomial.X - Polynomial.C 1) *
        ∏ i ∈ (Icc 1 (2 * m)).erase m, (Polynomial.X + Polynomial.C (z ^ i)) := by
    rw [← Finset.mul_prod_erase _ _ hmem, hzm, Polynomial.C_neg, ← sub_eq_add_neg]
  have h4 : (Polynomial.X : Polynomial ℂ) ^ (2 * m) - Polynomial.C 1 =
      (Polynomial.X - Polynomial.C 1) * ∑ i ∈ range (2 * m), Polynomial.X ^ i := by
    rw [Polynomial.C_1, mul_geom_sum]
  have h5 : ∏ i ∈ (Icc 1 (2 * m)).erase m, (Polynomial.X + Polynomial.C (z ^ i)) =
      ∑ i ∈ range (2 * m), (Polynomial.X : Polynomial ℂ) ^ i := by
    apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (1 : ℂ))
    rw [← h3, h2, ← h1, h4]
  have h6 := congrArg (Polynomial.eval (1 : ℂ)) h5
  rw [Polynomial.eval_prod, Polynomial.eval_finsetSum] at h6
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h6
  exact h6

/-- `∏ (1 ≤ i ≤ d*g) (1 + z^i)` for a primitive `d`-th root of unity `z`. -/
theorem F_eval {z : ℂ} {d : ℕ} (hz : IsPrimitiveRoot z d) (hd : 0 < d) (g : ℕ) (hg : 0 < g) :
    ∏ i ∈ Icc 1 (d * g), (1 + z ^ i) = if Odd d then (2 : ℂ) ^ g else 0 := by
  have h1 : ∏ i ∈ Icc 1 (d * g), (1 + z ^ i) = ∏ i ∈ range (d * g), (1 + z ^ i) :=
    prod_Icc_eq_prod_range (fun i => 1 + z ^ i) (d * g)
      (by simp only [pow_mul, hz.pow_eq_one, one_pow, pow_zero])
  have h2 : ∏ i ∈ range (d * g), (1 + z ^ i) = (∏ i ∈ range d, (1 + z ^ i)) ^ g :=
    prod_range_mul_of_periodic (fun i => 1 + z ^ i) d
      (fun k i => by simp only [pow_add, pow_mul, hz.pow_eq_one, one_pow, one_mul]) g
  rw [h1, h2]
  split_ifs with hodd
  · have h3 : (Polynomial.X : Polynomial ℂ) ^ d - Polynomial.C (-1) =
        ∏ i ∈ range d, (Polynomial.X + Polynomial.C (z ^ i)) := by
      rw [X_pow_sub_C_eq_prod hz hd hodd.neg_one_pow]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [mul_neg_one, Polynomial.C_neg, sub_neg_eq_add]
    have h4 := congrArg (Polynomial.eval (1 : ℂ)) h3
    rw [Polynomial.eval_prod] at h4
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, one_pow] at h4
    rw [← h4]
    norm_num
  · have hev : Even d := Nat.not_odd_iff_even.mp hodd
    obtain ⟨e, he⟩ := hev
    have hz2 : IsPrimitiveRoot (z ^ e) 2 := hz.pow hd (by omega)
    have hze : z ^ e = -1 := hz2.eq_neg_one_of_two_right
    have hmem : e ∈ range d := Finset.mem_range.mpr (by omega)
    have h0 : ∏ i ∈ range d, (1 + z ^ i) = 0 :=
      Finset.prod_eq_zero hmem (by show 1 + z ^ e = 0; rw [hze]; ring)
    rw [h0, zero_pow (show g ≠ 0 by omega)]

theorem F_at {w : ℂ} {n : ℕ} (hw : IsPrimitiveRoot w n) (hn : 0 < n) (j : ℕ) :
    ∏ i ∈ Icc 1 n, (1 + (w ^ j) ^ i) =
      if Odd (n / Nat.gcd n j) then (2 : ℂ) ^ (Nat.gcd n j) else 0 := by
  have hgpos : 0 < Nat.gcd n j := Nat.gcd_pos_of_pos_left j hn
  obtain ⟨d, hd⟩ := Nat.gcd_dvd_left n j
  obtain ⟨j', hj'⟩ := Nat.gcd_dvd_right n j
  have hdpos : 0 < d := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hd; omega)
  have hnd : n / Nat.gcd n j = d :=
    Nat.div_eq_of_eq_mul_left hgpos (by rw [mul_comm]; exact hd)
  have hjd : j / Nat.gcd n j = j' :=
    Nat.div_eq_of_eq_mul_left hgpos (by rw [mul_comm]; exact hj')
  have hcop : Nat.Coprime (n / Nat.gcd n j) (j / Nat.gcd n j) := Nat.coprime_div_gcd_div_gcd hgpos
  rw [hnd, hjd] at hcop
  have h1 : IsPrimitiveRoot (w ^ Nat.gcd n j) d := hw.pow hn hd
  have h2 : IsPrimitiveRoot ((w ^ Nat.gcd n j) ^ j') d := h1.pow_of_coprime j' hcop.symm
  rw [← pow_mul, ← hj'] at h2
  have h3 := F_eval h2 hdpos (Nat.gcd n j) hgpos
  have hn' : d * Nat.gcd n j = n := by rw [mul_comm]; exact hd.symm
  rw [hn'] at h3
  rw [hnd]
  exact h3

theorem sum_gcd (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ range n, (if Odd (n / Nat.gcd n j) then 2 ^ (Nat.gcd n j) else 0) =
      ∑ d ∈ n.divisors.filter Odd, Nat.totient d * 2 ^ (n / d) := by
  have hmaps : ∀ j ∈ range n, Nat.gcd n j ∈ n.divisors :=
    fun j _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n j, by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have inner : ∀ g ∈ n.divisors,
      ∑ j ∈ (range n).filter (fun j => Nat.gcd n j = g),
        (if Odd (n / Nat.gcd n j) then 2 ^ (Nat.gcd n j) else 0) =
      Nat.totient (n / g) * (if Odd (n / g) then 2 ^ (n / (n / g)) else 0) := by
    intro g hg
    have hgn : g ∣ n := Nat.dvd_of_mem_divisors hg
    have e : ∀ j ∈ (range n).filter (fun j => Nat.gcd n j = g),
        (if Odd (n / Nat.gcd n j) then 2 ^ (Nat.gcd n j) else 0) =
          (if Odd (n / g) then 2 ^ g else 0) := by
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    rw [Finset.sum_congr rfl e, Finset.sum_const, smul_eq_mul, ← Nat.totient_div_of_dvd hgn,
      Nat.div_div_self hgn (by omega)]
  rw [Finset.sum_congr rfl inner,
    Nat.sum_div_divisors n (fun d => Nat.totient d * (if Odd d then 2 ^ (n / d) else 0)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  split_ifs <;> simp

/-- `n * A063776(n) = A053636(n)`. -/
theorem nN_eq {w : ℂ} {n : ℕ} (hw : IsPrimitiveRoot w n) (hn : 0 < n) :
    n * ((Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i)).card =
      ∑ d ∈ n.divisors.filter Odd, Nat.totient d * 2 ^ (n / d) := by
  have h1 := filter_card hw (Icc 1 n)
  have e : ∀ j ∈ range n, ∏ i ∈ Icc 1 n, (1 + (w ^ j) ^ i) =
      if Odd (n / Nat.gcd n j) then (2 : ℂ) ^ (Nat.gcd n j) else 0 := fun j _ => F_at hw hn j
  rw [Finset.sum_congr rfl e] at h1
  rw [← sum_gcd n hn]
  have h2 : ((∑ j ∈ range n, (if Odd (n / Nat.gcd n j) then 2 ^ (Nat.gcd n j) else 0) : ℕ) : ℂ) =
      ∑ j ∈ range n, (if Odd (n / Nat.gcd n j) then (2 : ℂ) ^ (Nat.gcd n j) else 0) := by
    norm_cast
  exact_mod_cast h1.symm.trans h2.symm

/-- `H(w^j)` at odd `j` for `n = 2m`. -/
theorem H_odd {w : ℂ} {m : ℕ} (hw : IsPrimitiveRoot w (2 * m)) (hm : 0 < m) {j : ℕ} (hj : Odd j) :
    ∑ S ∈ (Icc 1 (2 * m)).powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i) =
      if Nat.Coprime (2 * m) j then -((m : ℂ) * ((2 * m : ℕ) : ℂ)) else 0 := by
  have hw2 : IsPrimitiveRoot (w ^ m) 2 := hw.pow (by omega) (by ring)
  have hwm : w ^ m = -1 := hw2.eq_neg_one_of_two_right
  split_ifs with hc
  · have hz : IsPrimitiveRoot (w ^ j) (2 * m) := hw.pow_of_coprime j hc.symm
    have hzm : (w ^ j) ^ m = -1 := by
      rw [← pow_mul, mul_comm, pow_mul, hwm, hj.neg_one_pow]
    have hmem : m ∈ Icc 1 (2 * m) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [sumH_single (w ^ j) hmem hzm, prod_erase_half hz hm hzm]
    ring
  · have hg1 : Nat.gcd (2 * m) j ≠ 1 := hc
    have hgpos : 0 < Nat.gcd (2 * m) j := Nat.gcd_pos_of_pos_left j (by omega)
    obtain ⟨j', hj'⟩ := Nat.gcd_dvd_right (2 * m) j
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_left (2 * m) j
    have hgodd : Odd (Nat.gcd (2 * m) j) := Odd.of_dvd_nat hj (Nat.gcd_dvd_right _ _)
    have hj'odd : Odd j' := by
      have h : Odd (Nat.gcd (2 * m) j * j') := by rw [← hj']; exact hj
      exact (Nat.odd_mul.mp h).2
    have htev : Even t := by
      have h : Even (Nat.gcd (2 * m) j * t) := by rw [← ht]; exact even_two_mul m
      rcases Nat.even_mul.mp h with h' | h'
      · exact absurd h' (Nat.not_even_iff_odd.mpr hgodd)
      · exact h'
    obtain ⟨e, he⟩ := htev
    have hme : m = Nat.gcd (2 * m) j * e := by
      rw [he] at ht
      nlinarith [ht]
    have hg2 : 2 ≤ Nat.gcd (2 * m) j := by omega
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h, mul_zero] at hme
        omega
      · exact h
    have hge : 2 * e ≤ Nat.gcd (2 * m) j * e := Nat.mul_le_mul_right e hg2
    have hje : j * e = m * j' := by
      calc j * e = Nat.gcd (2 * m) j * j' * e := by rw [← hj']
        _ = (Nat.gcd (2 * m) j * e) * j' := by ring
        _ = m * j' := by rw [← hme]
    have hze : (w ^ j) ^ e = -1 := by
      rw [← pow_mul, hje, pow_mul, hwm, hj'odd.neg_one_pow]
    have hz3 : (w ^ j) ^ (3 * e) = -1 := by
      rw [mul_comm, pow_mul, hze]
      norm_num
    have h1 : e ∈ Icc 1 (2 * m) := Finset.mem_Icc.mpr ⟨by omega, by linarith⟩
    have h2 : 3 * e ∈ Icc 1 (2 * m) := Finset.mem_Icc.mpr ⟨by omega, by linarith⟩
    exact sumH_eq_zero (w ^ j) h1 h2 (by omega) (by rw [hze]; ring) (by rw [hz3]; ring)

theorem diff_sum {w : ℂ} {m : ℕ} (hw : IsPrimitiveRoot w (2 * m)) (hm : 0 < m) :
    ∑ j ∈ range (2 * m), (1 - (w ^ j) ^ m) *
        ∑ S ∈ (Icc 1 (2 * m)).powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i) =
      -(2 * (m : ℂ) * ((2 * m : ℕ) : ℂ)) * (Nat.totient (2 * m) : ℂ) := by
  have hw2 : IsPrimitiveRoot (w ^ m) 2 := hw.pow (by omega) (by ring)
  have hwm : w ^ m = -1 := hw2.eq_neg_one_of_two_right
  have key : ∀ j ∈ range (2 * m), (1 - (w ^ j) ^ m) *
        ∑ S ∈ (Icc 1 (2 * m)).powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i) =
      if Nat.Coprime (2 * m) j then -(2 * (m : ℂ) * ((2 * m : ℕ) : ℂ)) else 0 := by
    intro j _
    have hpow : (w ^ j) ^ m = (-1) ^ j := by rw [← pow_mul, mul_comm, pow_mul, hwm]
    rcases Nat.even_or_odd j with hj | hj
    · have hnc : ¬ Nat.Coprime (2 * m) j :=
        Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_mul_right 2 m) (even_iff_two_dvd.mp hj)
      rw [hpow, hj.neg_one_pow, sub_self, zero_mul, if_neg hnc]
    · rw [hpow, hj.neg_one_pow, H_odd hw hm hj]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    ← Nat.totient_eq_card_coprime]
  ring

/-- For `n = 2m`: `T_m = T_0 + 2 m φ(n)` (sums of `σ S` over the classes `m` and `0`). -/
theorem T_sub {w : ℂ} {m : ℕ} (hw : IsPrimitiveRoot w (2 * m)) (hm : 0 < m) :
    ∑ S ∈ (Icc 1 (2 * m)).powerset.filter (fun S => 2 * m ∣ (∑ i ∈ S, i) + m), ∑ i ∈ S, i =
      (∑ S ∈ (Icc 1 (2 * m)).powerset.filter (fun S => 2 * m ∣ ∑ i ∈ S, i), ∑ i ∈ S, i) +
        2 * m * Nat.totient (2 * m) := by
  have hn : 0 < 2 * m := by omega
  have hT0 := filter_H0 hw (Icc 1 (2 * m))
  have hTm := filter_H hw (Icc 1 (2 * m)) m
  have hD := diff_sum hw hm
  have hsplit : (∑ j ∈ range (2 * m), (1 - (w ^ j) ^ m) *
        ∑ S ∈ (Icc 1 (2 * m)).powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i)) =
      (∑ j ∈ range (2 * m),
        ∑ S ∈ (Icc 1 (2 * m)).powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i)) -
      ∑ j ∈ range (2 * m), (w ^ j) ^ m *
        ∑ S ∈ (Icc 1 (2 * m)).powerset, ((∑ i ∈ S, i : ℕ) : ℂ) * (w ^ j) ^ (∑ i ∈ S, i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hn0 : ((2 * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : ((2 * m : ℕ) : ℂ) *
      (((∑ S ∈ (Icc 1 (2 * m)).powerset.filter (fun S => 2 * m ∣ (∑ i ∈ S, i) + m),
          ∑ i ∈ S, i : ℕ) : ℂ) -
        (((∑ S ∈ (Icc 1 (2 * m)).powerset.filter (fun S => 2 * m ∣ ∑ i ∈ S, i),
          ∑ i ∈ S, i : ℕ) : ℂ) + 2 * (m : ℂ) * (Nat.totient (2 * m) : ℂ))) = 0 := by
    linear_combination hsplit - hD + hT0 - hTm
  have key2 := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hn0)
  exact_mod_cast key2

/-! ### Complement -/

theorem compl_sum (U : Finset ℕ) (p q : Finset ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ S ⊆ U, p (U \ S) ↔ q S) :
    (∑ S ∈ U.powerset.filter p, ∑ i ∈ S, i) + (∑ S ∈ U.powerset.filter q, ∑ i ∈ S, i) =
      (U.powerset.filter q).card * ∑ i ∈ U, i := by
  have h1 : ∑ S ∈ U.powerset.filter p, (∑ i ∈ S, i) =
      ∑ S ∈ U.powerset.filter q, (∑ i ∈ U \ S, i) := by
    refine Finset.sum_nbij' (fun S => U \ S) (fun S => U \ S) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      refine ⟨Finset.sdiff_subset, ?_⟩
      have h := hpq (U \ S) Finset.sdiff_subset
      rw [Finset.sdiff_sdiff_eq_self hS.1] at h
      exact h.mp hS.2
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      exact ⟨Finset.sdiff_subset, (hpq S hS.1).mpr hS.2⟩
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      exact Finset.sdiff_sdiff_eq_self hS.1
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      exact Finset.sdiff_sdiff_eq_self hS.1
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      show ∑ i ∈ S, i = ∑ i ∈ U \ (U \ S), i
      rw [Finset.sdiff_sdiff_eq_self hS.1]
  rw [h1, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  exact Finset.sum_sdiff hS.1

theorem compl_even (m : ℕ) :
    (∑ S ∈ (Icc 1 (2 * m)).powerset.filter (fun S => 2 * m ∣ (∑ i ∈ S, i) + m), ∑ i ∈ S, i) +
      (∑ S ∈ (Icc 1 (2 * m)).powerset.filter (fun S => 2 * m ∣ ∑ i ∈ S, i), ∑ i ∈ S, i) =
      ((Icc 1 (2 * m)).powerset.filter (fun S => 2 * m ∣ ∑ i ∈ S, i)).card *
        ∑ i ∈ Icc 1 (2 * m), i :=
  compl_sum (Icc 1 (2 * m)) _ _ (fun S hS => by
    show 2 * m ∣ (∑ i ∈ Icc 1 (2 * m) \ S, i) + m ↔ 2 * m ∣ ∑ i ∈ S, i
    have h1 : (∑ i ∈ Icc 1 (2 * m) \ S, i) + (∑ i ∈ S, i) = ∑ i ∈ Icc 1 (2 * m), i :=
      Finset.sum_sdiff hS
    have h2 := sum_Icc_mul_two (2 * m)
    exact dvd_iff_of_add (c := m + 1) (by nlinarith [h1, h2]))

theorem compl_odd (n : ℕ) (hn : Odd n) :
    (∑ S ∈ (Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i), ∑ i ∈ S, i) +
      (∑ S ∈ (Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i), ∑ i ∈ S, i) =
      ((Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i)).card * ∑ i ∈ Icc 1 n, i := by
  obtain ⟨k, hk⟩ := hn
  exact compl_sum (Icc 1 n) _ _ (fun S hS => by
    show n ∣ (∑ i ∈ Icc 1 n \ S, i) ↔ n ∣ ∑ i ∈ S, i
    have h1 : (∑ i ∈ Icc 1 n \ S, i) + (∑ i ∈ S, i) = ∑ i ∈ Icc 1 n, i := Finset.sum_sdiff hS
    have h2 := sum_Icc_mul_two n
    exact dvd_iff_of_add (c := k + 1) (by subst hk; nlinarith [h1, h2]))

end OMA.A309128Proof

open OMA.A309128Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a309128.main := by
  intro n hn
  have hn0 : 0 < n := hn
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hw := Complex.isPrimitiveRoot_exp n (by omega)
  have hN : OMA.S_oeis_a309128.A063776 n =
      ((Finset.Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i)).card := by
    unfold OMA.S_oeis_a309128.A063776
    congr 1
    exact Finset.filter_congr (fun S _ => ⟨Nat.dvd_of_mod_eq_zero, Nat.mod_eq_zero_of_dvd⟩)
  have hA : OMA.S_oeis_a309128.A053636 n =
      n * ((Finset.Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i)).card := by
    unfold OMA.S_oeis_a309128.A053636
    exact (nN_eq hw hn0).symm
  have ha : OMA.S_oeis_a309128.a n = 1 / (n : ℚ) *
      ((∑ S ∈ (Finset.Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i), ∑ i ∈ S, i : ℕ) : ℚ) :=
    rfl
  have main1 : OMA.S_oeis_a309128.a n =
      ((n : ℚ) + 1) * (OMA.S_oeis_a309128.A063776 n : ℚ) / 4 -
        ((Nat.totient n : ℚ) / 2) * (1 + (-1 : ℚ) ^ n) / 2 := by
    rw [ha, hN, one_div, inv_mul_eq_iff_eq_mul₀ hnq]
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, hm⟩ := he
      have hm2 : n = 2 * m := by omega
      subst hm2
      have hmpos : 0 < m := by omega
      have R1 := T_sub hw hmpos
      have R2 := compl_even m
      have R3 := sum_Icc_mul_two (2 * m)
      rw [(even_two_mul m).neg_one_pow]
      have R1q := congrArg (Nat.cast : ℕ → ℚ) R1
      have R2q := congrArg (Nat.cast : ℕ → ℚ) R2
      have R3q := congrArg (Nat.cast : ℕ → ℚ) R3
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at R1q R2q R3q ⊢
      linear_combination (-(1 : ℚ) / 2) * R1q + (1 / 2 : ℚ) * R2q +
        ((((Finset.Icc 1 (2 * m)).powerset.filter (fun S => 2 * m ∣ ∑ i ∈ S, i)).card : ℚ) / 4) *
          R3q
    · have R2 := compl_odd n ho
      have R3 := sum_Icc_mul_two n
      rw [ho.neg_one_pow]
      have R2q := congrArg (Nat.cast : ℕ → ℚ) R2
      have R3q := congrArg (Nat.cast : ℕ → ℚ) R3
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at R2q R3q
      linear_combination (1 / 2 : ℚ) * R2q +
        ((((Finset.Icc 1 n).powerset.filter (fun S => n ∣ ∑ i ∈ S, i)).card : ℚ) / 4) * R3q
  refine ⟨main1, ?_⟩
  rw [main1, hA, hN, sub_left_inj, Nat.cast_mul, div_mul_eq_mul_div,
    eq_div_iff (mul_ne_zero (show (4 : ℚ) ≠ 0 by norm_num) hnq)]
  ring
