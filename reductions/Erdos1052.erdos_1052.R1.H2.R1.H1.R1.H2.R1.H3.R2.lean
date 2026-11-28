import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H3.R2 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H3
-- Credit: @yuka30240

/-!
# Forced prime divisors for the single repeated odd prime 5

Write `a = v₂(n)` and `e = v₅(n)`. For `a ≥ 10` and `e ≥ 4`, every candidate
has the simple primes 3 and 7 and at least one of 13, 19, and 31. When 3
divides none of the simple factors `p + 1`, all five primes occur.
The proof bounds the product along chains of simple primes by endpoint
weights. The endpoints with `p + 1 = 2^k 5^j` and `j > 0` have total
weight at most 75/64. The remaining endpoints are Mersenne primes.

H1 asks for a valuation bound when an odd exponent supplies the factor 3.
H2 asks for the bound when simple primes supply 3 and 7.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R2

-- An odd exponent gives the factor 3 in one of the two prime-power components.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → 41 ≤ n.factorization 5 →
    (Odd (n.factorization 5) → n.factorization 5 % 6 = 1) →
    (∀ d ∈ ({5, 6, 7, 8, 10, 12, 13, 14, 16, 19, 20, 22, 26, 28, 29, 31, 32, 34, 37, 38} : Finset ℕ),
      n.factorization 5 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → padicValNat 2 n % 6 ≠ 5 →
    padicValNat 2 n % 10 ≠ 5 → padicValNat 2 n % 14 ≠ 7 →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    (Odd (padicValNat 2 n) ∨ Odd (n.factorization 5)) →
    ({3, 7, 13, 19, 31} : Finset ℕ) ⊆ n.primeFactors →
    (∀ q ∈ n.primeFactors, q ≠ 2 → q ≠ 5 → ¬ 3 ∣ q + 1) →
    padicValNat 2 n ≤ A

-- With both exponents even, 3 and 7 each have a unique simple prime supplier.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → 41 ≤ n.factorization 5 →
    (∀ d ∈ ({5, 6, 7, 8, 10, 12, 13, 14, 16, 19, 20, 22, 26, 28, 29, 31, 32, 34, 37, 38} : Finset ℕ),
      n.factorization 5 % (2 * d) ≠ d) →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    Even (padicValNat 2 n) → Even (n.factorization 5) →
    3 ∈ n.primeFactors → 7 ∈ n.primeFactors →
    (13 ∈ n.primeFactors ∨ 19 ∈ n.primeFactors ∨ 31 ∈ n.primeFactors) →
    (∀ r ∈ ({3, 7} : Finset ℕ), ∃! q, q ∈ n.primeFactors ∧ q ≠ 2 ∧ q ≠ 5 ∧ r ∣ q + 1) →
    padicValNat 2 n ≤ A

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
  (B_nonneg one_add_le_B B_anti master_gen mersenne_bound zleaf_form zleaf_bound fiber_bound facts)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (setup hK5 step_ge)

-- In the rectangle 1 ≤ k ≤ 6, 1 ≤ j ≤ 3 there are just five primes 2^k 5^j - 1.
theorem small_leaf_primes {q k j : ℕ} (hp : q.Prime) (hk : 1 ≤ k) (hk' : k ≤ 6)
    (hj : 1 ≤ j) (hj' : j ≤ 3) (he : q + 1 = 2 ^ k * 5 ^ j) :
    q ∈ ({19, 79, 199, 499, 1999} : Finset ℕ) := by
  interval_cases j <;> interval_cases k <;> norm_num at he <;>
    obtain rfl : q = _ := Nat.eq_sub_of_add_eq he <;> first | decide | norm_num at hp

-- Separate the finite rectangle, the three horizontal tails, and the part j ≥ 4.
theorem weighted_five_leaves {L : Finset ℕ} (hprime : ∀ q ∈ L, q.Prime)
    (hform : ∀ q ∈ L, ∃ k j : ℕ, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 5 ^ j) :
    ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 75 / 64 := by
  classical
  let w (q : ℕ) : ℚ := ((q : ℚ) + 1) / ((q : ℚ) - 1)
  let S : Finset ℕ := {19, 79, 199, 499, 1999}
  choose! K J hKJ using hform
  have nonneg (Q : Finset ℕ) (hQ : Q ⊆ L) : 0 ≤ ∏ q ∈ Q, w q :=
    Finset.prod_nonneg fun q hq => B_nonneg (hprime q (hQ hq)).one_lt.le
  have hsmall : ∏ q ∈ L.filter (· ∈ S), w q ≤ ∏ q ∈ S, w q := by
    apply Finset.prod_le_prod_of_subset_of_one_le (fun q hq => (Finset.mem_filter.mp hq).2)
    · exact fun q hq => B_nonneg (hprime q (Finset.mem_filter.mp hq).1).one_lt.le
    · intro q hq _
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num [w]
  let T := L.filter (· ∉ S)
  have hT : T ⊆ L := Finset.filter_subset _ _
  let U := T.filter (fun q => J q ≤ 3)
  have hU : U ⊆ T := Finset.filter_subset _ _
  have hlarge : ∏ q ∈ T.filter (fun q => ¬ J q ≤ 3), w q ≤ (625 : ℚ) / 622 := by
    have h := zleaf_bound (z := 5) (by decide) 4 (by decide)
      (T.filter (fun q => ¬ J q ≤ 3)) (fun q hq => by
        obtain ⟨hqT, hj⟩ := Finset.mem_filter.mp hq
        exact ⟨K q, J q, (hKJ q (hT hqT)).1, by omega, (hKJ q (hT hqT)).2.2⟩)
    exact h.trans (by norm_num)
  let F : Finset ℕ := {1, 2, 3}
  have hmap : ∀ q ∈ U, J q ∈ F := by
    intro q hq
    have hj := (hKJ q (hT (hU hq))).2.1
    have hj' := (Finset.mem_filter.mp hq).2
    simp only [F, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hfiber (j : ℕ) (hj : j ∈ F) :
      ∏ q ∈ U.filter (fun q => J q = j), w q ≤
        ((64 * 5 ^ j : ℕ) : ℚ) / (((64 * 5 ^ j : ℕ) : ℚ) - 2) := by
    apply fiber_bound (by have := Nat.one_le_pow j 5 (by decide); omega)
    intro q hq
    obtain ⟨hqU, hJ⟩ := Finset.mem_filter.mp hq
    have hqT := hU hqU
    obtain ⟨hk, hjpos, he⟩ := hKJ q (hT hqT)
    have hkh : 6 < K q := by
      by_contra! hkle
      exact (Finset.mem_filter.mp hqT).2
        (small_leaf_primes (hprime q (hT hqT)) hk hkle hjpos (Finset.mem_filter.mp hqU).2 he)
    refine ⟨K q - 6, by omega, ?_⟩
    have hsplit : K q = (K q - 6) + 6 := by omega
    calc q + 1 = 2 ^ (K q) * 5 ^ j := hJ ▸ he
      _ = 2 ^ (K q - 6) * (64 * 5 ^ j) := by
        conv_lhs => rw [hsplit, pow_add]
        ring
  have hmiddle : ∏ q ∈ U, w q ≤
      ∏ j ∈ F, ((64 * 5 ^ j : ℕ) : ℚ) / (((64 * 5 ^ j : ℕ) : ℚ) - 2) := by
    rw [← Finset.prod_fiberwise_of_maps_to hmap]
    exact Finset.prod_le_prod
      (fun j _ => nonneg _ ((Finset.filter_subset _ _).trans (hU.trans hT))) hfiber
  have hTprod := mul_le_mul hmiddle hlarge
    (nonneg _ ((Finset.filter_subset _ _).trans hT)) (by
      norm_num [F, Finset.prod_insert])
  rw [show (∏ q ∈ U, w q) * ∏ q ∈ T.filter (fun q => ¬ J q ≤ 3), w q = ∏ q ∈ T, w q from
    Finset.prod_filter_mul_prod_filter_not T _ w] at hTprod
  have h := mul_le_mul hsmall hTprod (nonneg T hT) (by norm_num [S, w, Finset.prod_insert])
  rw [show (∏ q ∈ L.filter (· ∈ S), w q) * ∏ q ∈ T, w q = ∏ q ∈ L, w q from
    Finset.prod_filter_mul_prod_filter_not L _ w] at h
  exact h.trans (by norm_num [S, F, w, Finset.prod_insert])


-- The cost of a chain ending at 3 or 7 depends on the smallest possible
-- predecessor. With no simple prime sending a factor to 3, the weight at 3
-- is exactly 4/3. If 13 is absent as well, a predecessor of 7 is at least 97.
theorem forced_small_primes {a e : ℕ} {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (balance : (2 ^ a + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 5 ^ e * ∏ p ∈ P, p)
    (ha : 10 ≤ a) (he : 4 ≤ e) :
    3 ∈ P ∧ 7 ∈ P ∧ (13 ∈ P ∨ 19 ∈ P ∨ 31 ∈ P) ∧
      ((∀ p ∈ P, ¬ 3 ∣ p + 1) → 13 ∈ P ∧ 19 ∈ P ∧ 31 ∈ P) := by
  classical
  let clean := ∀ p ∈ P, ¬ 3 ∣ p + 1
  let x : ℚ := if 3 ∈ P then (if clean then 4 / 3 else 32 / 21) else 1
  let y : ℚ := if 7 ∈ P then
    (if 13 ∈ P then 64 / 51 else if clean then 7 / 6 else 6 / 5) else 1
  let z : ℚ := if 31 ∈ P then 16 / 15 else 1
  let t : ℚ := if 19 ∈ P then 75 / 64 else (75 / 64) * (9 / 10)
  let β (q : ℕ) : ℚ := if q = 3 then x else if q = 7 then y else if q = 11 then 8 / 7
    else if q = 13 then 56 / 51 else if q = 31 then z else ((q : ℚ) + 1) / ((q : ℚ) - 1)
  have hweights : ∀ q ∈ P, 1 + 1 / (q : ℚ) ≤ β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := by
    intro q hq
    by_cases q3 : q = 3
    · subst q
      by_cases h : clean <;> norm_num [β, x, hq, h]
    by_cases q7 : q = 7
    · subst q
      simp only [β, y, hq, if_pos, Nat.reduceEqDiff, if_false]
      split_ifs <;> norm_num
    by_cases q11 : q = 11
    · subst q
      norm_num [β]
    by_cases q13 : q = 13
    · subst q
      norm_num [β]
    by_cases q31 : q = 31
    · subst q
      norm_num [β, z, hq]
    simp only [β, if_neg q3, if_neg q7, if_neg q11, if_neg q13, if_neg q31, le_refl, and_true]
    exact one_add_le_B (hp q hq).1.two_le
  have hstep : ∀ p ∈ P, ∀ q ∈ P, q ∣ p + 1 →
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∉ ({5} : Finset ℕ) → c ∣ p + 1 → q ≤ c) →
      β q ≠ ((q : ℚ) + 1) / ((q : ℚ) - 1) → (1 + 1 / (q : ℚ)) * β p ≤ β q := by
    intro p hmem q hq hd _ hdiff
    by_cases q3 : q = 3
    · subst q
      by_cases h : clean
      · exact (h p hmem hd).elim
      have hval : β 3 = 32 / 21 := by simp [β, x, hq, h]
      rw [hval]
      by_cases h11 : p = 11
      · subst p
        norm_num [β]
      have h17 : 17 ≤ p := by
        by_contra! hlt
        have trial : ∀ t : Fin 17, (t : ℕ).Prime → 3 ∣ (t : ℕ) + 1 →
            (t : ℕ) = 2 ∨ (t : ℕ) = 5 ∨ (t : ℕ) = 11 := by decide
        rcases trial ⟨p, hlt⟩ (hp p hmem).1 hd with h2 | h5' | h11'
        · exact (hp p hmem).2 h2
        · exact h5 (h5' ▸ hmem)
        · exact h11 h11'
      exact step_ge (by decide) h17 (hweights p hmem).2 (by norm_num)
    by_cases q7 : q = 7
    · subst q
      have after13 (hn : p ≠ 13) : 41 ≤ p := by
        by_contra! hlt
        have trial : ∀ i : Fin 41, (i : ℕ).Prime → 7 ∣ (i : ℕ) + 1 → (i : ℕ) = 13 := by decide
        exact hn (trial ⟨p, hlt⟩ (hp p hmem).1 hd)
      by_cases h13 : 13 ∈ P
      · by_cases h13' : p = 13
        · subst p
          norm_num [β, y, hq, h13]
        · apply step_ge (by decide) (after13 h13') (hweights p hmem).2
          norm_num [β, y, hq, h13]
      by_cases h : clean
      · have h97 : 97 ≤ p := by
          by_contra! hlt
          have trial : ∀ i : Fin 97, (i : ℕ).Prime → 7 ∣ (i : ℕ) + 1 →
              (i : ℕ) = 13 ∨ 3 ∣ (i : ℕ) + 1 := by decide
          rcases trial ⟨p, hlt⟩ (hp p hmem).1 hd with heq | hd3
          · exact h13 (heq ▸ hmem)
          · exact h p hmem hd3
        apply step_ge (by decide) h97 (hweights p hmem).2
        norm_num [β, y, hq, h13, h]
      · apply step_ge (by decide) (after13 (fun heq => h13 (heq ▸ hmem))) (hweights p hmem).2
        norm_num [β, y, hq, h13, h]
    by_cases q11 : q = 11
    · subst q
      have h43 : 43 ≤ p := by
        by_contra! hlt
        have trial : ∀ t : Fin 43, (t : ℕ).Prime → ¬ 11 ∣ (t : ℕ) + 1 := by decide
        exact trial ⟨p, hlt⟩ (hp p hmem).1 hd
      apply step_ge (by decide) h43 (hweights p hmem).2
      norm_num [β]
    by_cases q13 : q = 13
    · subst q
      have h103 : 103 ≤ p := by
        by_contra! hlt
        have trial : ∀ i : Fin 103, (i : ℕ).Prime → ¬ 13 ∣ (i : ℕ) + 1 := by decide
        exact trial ⟨p, hlt⟩ (hp p hmem).1 hd
      apply step_ge (by decide) h103 (hweights p hmem).2
      norm_num [β]
    by_cases q31 : q = 31
    · subst q
      exact (hdiff (by norm_num [β, z, hq])).elim
    exact (hdiff (by simp [β, q3, q7, q11, q13, q31])).elim
  obtain ⟨L, hLP, hleaf, hbalance⟩ := master_gen hp (hK5 e) (by positivity) balance β hweights hstep
  have hpos (q : ℕ) (hq : q ∈ L) : 0 < β q := by
    exact lt_of_lt_of_le (by positivity) (hweights q (hLP hq)).1
  let M := L.filter (fun q => ∃ k, q + 1 = 2 ^ k)
  let Z := L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k)
  have hx : 1 ≤ x := by dsimp [x]; split_ifs <;> norm_num
  have hy : 1 ≤ y := by dsimp [y]; split_ifs <;> norm_num
  have hz1 : 1 ≤ z := by dsimp [z]; split_ifs <;> norm_num
  have hz0 := le_trans (by norm_num : (0 : ℚ) ≤ 1) hz1
  have hx0 := le_trans (by norm_num : (0 : ℚ) ≤ 1) hx
  have hy0 := le_trans (by norm_num : (0 : ℚ) ≤ 1) hy
  have hm := mersenne_bound β M
    (fun q hq => (hp q (hLP (Finset.mem_filter.mp hq).1)).1)
    (fun q hq => (Finset.mem_filter.mp hq).2)
    (fun q hq => ⟨hpos q (Finset.mem_filter.mp hq).1, (hweights q (hLP (Finset.mem_filter.mp hq).1)).2⟩)
    ⟨by simpa [β] using hx, by simpa [β] using hy, by simpa [β] using hz1, by norm_num [β]⟩
  have hz : ∏ q ∈ Z, β q ≤ t := by
    refine (Finset.prod_le_prod (fun q hq => (hpos q (Finset.mem_filter.mp hq).1).le)
      (fun q hq => (hweights q (hLP (Finset.mem_filter.mp hq).1)).2)).trans ?_
    have hpZ : ∀ q ∈ Z, q.Prime := fun q hq => (hp q (hLP (Finset.mem_filter.mp hq).1)).1
    have form : ∀ q ∈ Z, ∃ k j : ℕ, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 5 ^ j := by
      intro q hq
      obtain ⟨hqL, hn⟩ := Finset.mem_filter.mp hq
      exact zleaf_form Nat.prime_five (by decide) (hp q (hLP hqL)).1 (hp q (hLP hqL)).2 (hleaf q hqL) hn
    by_cases h19 : 19 ∈ P
    · simpa only [t, if_pos h19] using weighted_five_leaves hpZ form
    · have h19Z : 19 ∉ Z := fun hq => h19 (hLP (Finset.mem_filter.mp hq).1)
      have h := weighted_five_leaves (L := insert 19 Z) (fun q hq => by
        rcases Finset.mem_insert.mp hq with rfl | hq
        · decide
        · exact hpZ q hq) (fun q hq => by
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact ⟨2, 1, by decide, by decide, by decide⟩
        · exact form q hq)
      rw [Finset.prod_insert h19Z] at h
      simp only [t, if_neg h19]
      norm_num only [Nat.cast_ofNat, show ((19 : ℚ) + 1) / (19 - 1) = 10 / 9 by norm_num] at h
      linarith
  have hm' : ∏ q ∈ M, β q ≤ (x * y * z * (64/63)) * (2048/2047) := by
    convert hm using 1
    norm_num [β]
  have hleaves := mul_le_mul hm' hz
    (Finset.prod_nonneg (s := Z) fun q hq => (hpos q (Finset.mem_filter.mp hq).1).le)
    (by positivity)
  rw [show (∏ q ∈ M, β q) * ∏ q ∈ Z, β q = ∏ q ∈ L, β q from
    Finset.prod_filter_mul_prod_filter_not L _ β] at hleaves
  have htwo : 1 + 1 / (2 : ℚ) ^ a ≤ 1025 / 1024 := by
    have hpow : (2 : ℚ) ^ 10 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
    have hi : 1 / (2 : ℚ) ^ a ≤ 1 / 1024 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      norm_num at hpow ⊢
      linarith
    linarith
  have hfiv : ((1 + 5 ^ e : ℕ) : ℚ) / ((5 ^ e : ℕ) : ℚ) ≤ 626 / 625 := by
    have hpow : (5 : ℚ) ^ 4 ≤ 5 ^ e := pow_le_pow_right₀ (by norm_num) he
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num at hpow
    linarith
  have coeff := mul_le_mul htwo hfiv (by positivity) (by norm_num)
  have total := hbalance.trans (mul_le_mul coeff hleaves
    (Finset.prod_nonneg fun q hq => (hpos q hq).le) (by norm_num))
  have h3 : 3 ∈ P := by
    by_contra hn
    simp only [x, if_neg hn, y, z, t] at total
    split_ifs at total <;> norm_num at total
  have h7 : 7 ∈ P := by
    by_contra hn
    simp only [x, if_pos h3, y, if_neg hn, z, t] at total
    split_ifs at total <;> norm_num at total
  refine ⟨h3, h7, ?_, ?_⟩
  · by_contra! hn
    simp only [x, y, z, t, if_pos h3, if_pos h7, if_neg hn.1, if_neg hn.2.1, if_neg hn.2.2] at total
    split_ifs at total <;> norm_num at total
  · intro hc
    change clean at hc
    simp only [x, y, z, t, if_pos h3, if_pos h7, if_pos hc] at total
    split_ifs at total <;> first | (norm_num at total; done) | (exact ⟨by assumption, by assumption, by assumption⟩)

theorem no_even_power_source {r e : ℕ} (hr : r = 3 ∨ r = 7) (b : ℕ) (he : Even e) :
    ¬ r ∣ b ^ e + 1 := by
  obtain ⟨k, rfl⟩ := he
  rw [pow_add]
  have hrpos : 0 < r := by rcases hr with rfl | rfl <;> decide
  have trial : ∀ i : Fin r, ¬ r ∣ (i : ℕ) * (i : ℕ) + 1 := by
    rcases hr with rfl | rfl <;> decide
  let x := b ^ k
  have congr := Nat.mod_modEq x r
  exact fun h => trial ⟨x % r, Nat.mod_lt _ hrpos⟩
    ((((congr.mul congr).add_right 1).dvd_iff (dvd_refl r)).mpr h)

theorem unique_simple_source {a e r : ℕ} {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (balance : (2 ^ a + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hr : r = 3 ∨ r = 7) (hrP : r ∈ P) (ha : Even a) (he : Even e) :
    ∃! q, q ∈ P ∧ r ∣ q + 1 := by
  have hdiv : r ∣ (2 ^ a + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) := by
    rw [balance]
    exact (Finset.dvd_prod_of_mem (fun p => p) hrP).mul_left _
  have pr := (hp r hrP).1
  have hprod := (pr.dvd_mul.mp hdiv).resolve_left (fun h => by
    rcases pr.dvd_mul.mp h with h | h
    · exact no_even_power_source hr 2 ha h
    · exact no_even_power_source hr 5 he (by rwa [add_comm] at h))
  obtain ⟨q, hq, hd⟩ := (Prime.dvd_finsetProd_iff pr.prime _).mp hprod
  obtain ⟨_, _, unique, _, _, _, _, _⟩ := facts hp (hK5 e) balance
  have hr5 : r ∉ ({5} : Finset ℕ) := by rcases hr with rfl | rfl <;> decide
  exact ⟨q, ⟨hq, hd⟩, fun p h => unique r pr (hp r hrP).2 hr5 p h.1 q hq h.2 hd⟩

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.H3 := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  refine ⟨max 9 (max A B), ?_⟩
  intro n hn hrepeat he hodd hfilter h6 h6' h10 h14 hfermat
  by_cases hsmall : padicValNat 2 n < 10
  · omega
  let P := (n.primeFactors.erase 2).filter (fun q => q ∉ ({5} : Finset ℕ))
  have memP (q : ℕ) : q ∈ P ↔ q ∈ n.primeFactors ∧ q ≠ 2 ∧ q ≠ 5 := by
    simp [P, and_assoc, and_left_comm, and_comm]
  obtain ⟨hp, h5, balance⟩ := setup hn hrepeat
  obtain ⟨h3, h7, hmore, hclean⟩ := forced_small_primes hp h5 balance (by omega) (by omega)
  by_cases ho : Odd (padicValNat 2 n) ∨ Odd (n.factorization 5)
  · obtain ⟨_, _, _, sourceTwo, _, _, _, sourceFive⟩ := facts hp (hK5 _) balance
    have clean : ∀ q ∈ P, ¬ 3 ∣ q + 1 := by
      rcases ho with ha | he'
      · exact sourceTwo 3 Nat.prime_three (by decide) (by decide)
          (OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.three_dvd_two_pow_add_one (Nat.odd_iff.mp ha))
      · have h6div : 6 ∣ 5 ^ n.factorization 5 + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 5 1 he'
        apply sourceFive 3 Nat.prime_three (by decide) (by decide)
        rw [add_comm]
        exact (show 3 ∣ 6 by decide).trans h6div
    obtain ⟨h13, h19, h31⟩ := hclean clean
    have core : ({3, 7, 13, 19, 31} : Finset ℕ) ⊆ n.primeFactors := by
      intro q hq
      apply ((memP q).mp _).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> assumption
    have bound := hA n hn hrepeat he hodd hfilter h6 h6' h10 h14 hfermat ho core
      (fun q hmem h2 h5' => clean q ((memP q).mpr ⟨hmem, h2, h5'⟩))
    omega
  · have haEven := Nat.not_odd_iff_even.mp (fun h => ho (Or.inl h))
    have heEven := Nat.not_odd_iff_even.mp (fun h => ho (Or.inr h))
    have hmore' : 13 ∈ n.primeFactors ∨ 19 ∈ n.primeFactors ∨ 31 ∈ n.primeFactors :=
      hmore.imp (fun h => ((memP _).mp h).1)
        (Or.imp (fun h => ((memP _).mp h).1) (fun h => ((memP _).mp h).1))
    have bound := hB n hn hrepeat he hfilter hfermat haEven heEven
      ((memP _).mp h3).1 ((memP _).mp h7).1 hmore' (fun r hr => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        have hrP : r ∈ P := hr.elim (fun eq => eq ▸ h3) (fun eq => eq ▸ h7)
        have source : ∃! q, q ∈ P ∧ r ∣ q + 1 := unique_simple_source hp balance hr hrP haEven heEven
        simpa only [memP, and_assoc] using source)
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H3_R2
