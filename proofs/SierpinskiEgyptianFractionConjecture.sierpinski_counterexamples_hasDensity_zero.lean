import FormalConjectures.Wikipedia.SierpinskiEgyptianFractionConjecture

/-!
# Exceptional denominators of Sierpinski's 5/n problem have density zero

If a prime `p = 5k - 1` divides `n = p m`, then `5/n = 1/(2km) + 1/(2km) + 1/(kpm)`. So every
exceptional `n > 0` has no prime factor congruent to 4 mod 5. The sum of `1/p` over such primes
diverges (from Mathlib's lower bound for the residue-class L-series of the von Mangoldt function),
so products of `1 - 1/p` over finitely many of them get arbitrarily small, and a periodic count of
integers coprime to their product bounds the density. This is a Lean formalisation of the
density-zero consequence of the Webb (1970) and Vaughan (1970) results, by a weaker elementary route.
-/

namespace SierpinskiDensitySolution

open SierpinskiEgyptianFractionConjecture
open ArithmeticFunction.vonMangoldt Filter Topology Finset

theorem decompB {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (h4 : p % 5 = 4) (hd : p ∣ n) :
    HasSierpinskiDecomposition n := by
  obtain ⟨m, rfl⟩ := hd
  have hm : 0 < m := Nat.pos_of_mul_pos_left hn
  obtain ⟨k, hk⟩ : ∃ k, p + 1 = 5 * k := ⟨(p + 1) / 5, by omega⟩
  have hk0 : 0 < k := by omega
  refine ⟨2 * k * m, 2 * k * m, k * (p * m), ?_, ?_, ?_, ?_⟩
  · have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 2) hk0) hm; omega
  · have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 2) hk0) hm; omega
  · have := Nat.mul_pos hk0 (Nat.mul_pos hp.pos hm); omega
  · have hkq : (p : ℚ) + 1 = 5 * k := by exact_mod_cast hk
    have : (0:ℚ) < p := by exact_mod_cast hp.pos
    have : (0:ℚ) < m := by exact_mod_cast hm
    have : (0:ℚ) < k := by exact_mod_cast hk0
    push_cast
    field_simp
    linear_combination (-2:ℚ) * hkq

theorem totient_prodB (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((Nat.totient (∏ p ∈ P, p) : ℕ) : ℝ) / ((∏ p ∈ P, p : ℕ) : ℝ) = ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have ha : a.Prime := hP a (mem_insert_self _ _)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes ha (hs q hq)).mpr (fun h => has (h ▸ hq))
    rw [prod_insert has, prod_insert has, Nat.totient_mul hcop, Nat.totient_prime ha, ← ih hs]
    have hpos : (0:ℝ) < ((∏ p ∈ s, p : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun p hp => (hs p hp).pos)
    have ha0 : (0:ℝ) < a := by exact_mod_cast ha.pos
    have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha.one_lt.le
    push_cast [Nat.cast_sub ha.one_lt.le]
    field_simp

theorem count_coprimeB (Q N : ℕ) (hQ : 0 < Q) :
    #{n ∈ range N | Q.Coprime n} ≤ (N / Q + 1) * Nat.totient Q := by
  have hblock : ∀ k, #{n ∈ range (k * Q) | Q.Coprime n} ≤ k * Nat.totient Q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsplit : range ((k + 1) * Q) = range (k * Q) ∪ Ico (k * Q) (k * Q + Q) := by
        rw [range_eq_Ico, range_eq_Ico, Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)]
        congr 1; ring
      rw [hsplit, filter_union]
      calc _ ≤ #{n ∈ range (k * Q) | Q.Coprime n} + #{n ∈ Ico (k * Q) (k * Q + Q) | Q.Coprime n} :=
            card_union_le _ _
        _ ≤ k * Nat.totient Q + Nat.totient Q := by
            rw [Nat.filter_coprime_Ico_eq_totient]; omega
        _ = (k + 1) * Nat.totient Q := by ring
  refine le_trans (card_le_card ?_) (hblock (N / Q + 1))
  apply filter_subset_filter
  intro n hn
  simp only [mem_range] at hn ⊢
  have := Nat.lt_div_mul_add (a := N) hQ
  nlinarith [this]

theorem prod_smallC (f : ℕ → ℝ)
    (hfdef : ∀ n, f n = if n.Prime ∧ n % 5 = 4 then (1:ℝ) / n else 0)
    (hf : ¬ Summable f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p % 5 = 4) ∧ ∏ p ∈ P, (1 - 1 / (p : ℝ)) < δ := by
  have f0 : ∀ n, 0 ≤ f n := fun n => by rw [hfdef]; split_ifs <;> positivity
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg f0).mp hf
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 ht (-Real.log δ + 1)).exists
  refine ⟨(range N).filter (fun n => n.Prime ∧ n % 5 = 4), fun p hp => (mem_filter.1 hp).2, ?_⟩
  have hsum : ∑ i ∈ range N, f i = ∑ p ∈ (range N).filter (fun n => n.Prime ∧ n % 5 = 4), (1 / (p:ℝ)) := by
    rw [sum_filter]; exact sum_congr rfl (fun i _ => hfdef i)
  calc ∏ p ∈ (range N).filter (fun n => n.Prime ∧ n % 5 = 4), (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ (range N).filter (fun n => n.Prime ∧ n % 5 = 4), Real.exp (-(1 / (p:ℝ))) := by
        apply Finset.prod_le_prod
        · intro p hp
          have := (mem_filter.1 hp).2.1.one_lt
          have h1 : (1:ℝ) ≤ p := by exact_mod_cast this.le
          have : 1 / (p:ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
          linarith
        · intro p _
          have := Real.add_one_le_exp (-(1 / (p:ℝ)))
          linarith
    _ = Real.exp (-∑ i ∈ range N, f i) := by
        rw [hsum, ← Real.exp_sum, ← sum_neg_distrib]
    _ < δ := by
        rw [← Real.exp_log hδ, Real.exp_lt_exp]
        linarith

theorem divA : ¬ Summable (fun n : ℕ => if n.Prime ∧ n % 5 = 4 then (1:ℝ) / n else 0) := by
  intro hf
  set f : ℕ → ℝ := fun n => if n.Prime ∧ n % 5 = 4 then (1:ℝ) / n else 0 with hfdef
  have ha : IsUnit (4 : ZMod 5) := by decide
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound (q := 5) ha
  have ht5 : ((Nat.totient 5 : ℕ) : ℝ) = 4 := by rw [Nat.totient_prime (by norm_num)]; norm_num
  have f0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [hfdef]; split_ifs <;> positivity
  have htail := tendsto_sum_nat_add f
  obtain ⟨M, hM⟩ := ((tendsto_order.1 htail).2 (1/8) (by norm_num)).exists
  set r : ℕ → ℝ := fun n => (if n.Prime then 0 else residueClass (4 : ZMod 5) n) / n with hrdef
  have hr : Summable r := summable_residueClass_non_primes_div _
  have hrM : Summable (fun k => r (k + M)) := (summable_nat_add_iff M).mpr hr
  have hfM : Summable (fun k => f (k + M)) := (summable_nat_add_iff M).mpr hf
  set K := ∑' k, r (k + M)
  have key : ∀ x : ℝ, x ∈ Set.Ioc 1 2 →
      ∑' n, residueClass (4 : ZMod 5) n / (n : ℝ) ^ x ≤ M + (1/8) / (x - 1) + K := by
    intro x hx
    have hx1 : 0 < x - 1 := sub_pos.mpr hx.1
    set h : ℕ → ℝ := fun n => residueClass (4 : ZMod 5) n / (n : ℝ) ^ x with hhdef
    have hs : Summable h := LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one _).trans_lt <| mod_cast hx.1
    rw [← hs.sum_add_tsum_nat_add M]
    have hhead : ∑ i ∈ range M, h i ≤ M := by
      have : ∀ i ∈ range M, h i ≤ 1 := by
        intro i _
        simp only [hhdef]
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · simp
        have hi1 : (1:ℝ) ≤ i := by exact_mod_cast hi
        have hpos : (0:ℝ) < (i:ℝ) ^ x := Real.rpow_pos_of_pos (by linarith) x
        rw [div_le_one hpos]
        calc residueClass (4 : ZMod 5) i ≤ Λ i := residueClass_le _ _
          _ ≤ Real.log i := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ (i:ℝ) := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
          _ = (i:ℝ) ^ (1:ℝ) := (Real.rpow_one _).symm
          _ ≤ (i:ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le hi1 hx.1.le
      calc ∑ i ∈ range M, h i ≤ ∑ i ∈ range M, (1:ℝ) := sum_le_sum this
        _ = M := by simp
    have hpt : ∀ n, h n ≤ f n / (x - 1) + r n := by
      intro n
      simp only [hhdef, hfdef, hrdef]
      by_cases hp : n.Prime
      · have hn1 : (1:ℝ) < n := by exact_mod_cast hp.one_lt
        have hpos : (0:ℝ) < (n:ℝ) ^ x := Real.rpow_pos_of_pos (by linarith) x
        simp only [hp, true_and, if_true, zero_div, add_zero]
        by_cases hm : n % 5 = 4
        · have hz : ((n : ZMod 5)) = 4 := by
            have : ((n : ZMod 5)).val = 4 := by rw [ZMod.val_natCast]; exact hm
            rw [← ZMod.natCast_zmod_val (n : ZMod 5), this]; rfl
          simp only [hm, if_true, residueClass, Set.indicator_apply, Set.mem_ofPred_eq, hz,
            ArithmeticFunction.vonMangoldt_apply_prime hp]
          have hl := Real.log_le_rpow_div (x := (n:ℝ)) (by linarith) hx1
          have hsplit : (n:ℝ) ^ x = n * (n:ℝ) ^ (x - 1) := by
            rw [Real.rpow_sub (by linarith), Real.rpow_one]; field_simp
          have hq : (0:ℝ) < (n:ℝ) ^ (x - 1) := Real.rpow_pos_of_pos (by linarith) _
          rw [hsplit, div_le_div_iff₀ (by positivity) hx1]
          calc Real.log n * (x - 1) ≤ (n:ℝ) ^ (x - 1) / (x - 1) * (x - 1) := by
                exact mul_le_mul_of_nonneg_right hl hx1.le
            _ = 1 / n * (n * (n:ℝ) ^ (x - 1)) := by field_simp
        · have hz : ¬ ((n : ZMod 5)) = 4 := by
            intro hz; apply hm
            have := congrArg ZMod.val hz
            rw [ZMod.val_natCast] at this; exact this
          simp only [hm, if_false, residueClass, Set.indicator_apply, Set.mem_ofPred_eq, hz,
            zero_div, le_refl]
      · simp only [hp, false_and, if_false, zero_div, if_false, zero_add]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
        apply div_le_div_of_nonneg_left (residueClass_nonneg _ _) (by linarith)
        calc (n:ℝ) = (n:ℝ) ^ (1:ℝ) := (Real.rpow_one _).symm
          _ ≤ (n:ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le hn1 hx.1.le
    have htl : ∑' k, h (k + M) ≤ (1/8) / (x - 1) + K := by
      have hfMx : Summable (fun k => f (k + M) / (x - 1)) := hfM.div_const _
      calc ∑' k, h (k + M) ≤ ∑' k, (f (k + M) / (x - 1) + r (k + M)) :=
            Summable.tsum_le_tsum (fun k => hpt _) ((summable_nat_add_iff M).mpr hs)
              (hfMx.add hrM)
        _ = (∑' k, f (k + M)) / (x - 1) + K := by
            rw [hfMx.tsum_add hrM, tsum_div_const]
        _ ≤ (1/8) / (x - 1) + K := by
            gcongr
    linarith
  set B := |C| + M + |K| + 1 with hB
  have hBpos : 0 < B := by positivity
  have hx : 1 + 1 / (8 * B) ∈ Set.Ioc (1:ℝ) 2 := by
    constructor
    · have : 0 < 1 / (8 * B) := by positivity
      linarith
    · have : 1 / (8 * B) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (1:ℝ) ≤ B := by
          have := abs_nonneg C; have := abs_nonneg K; have : (0:ℝ) ≤ M := by positivity
          linarith
        linarith
      linarith
  have h1 := hC hx
  have h2 := key _ hx
  rw [ht5] at h1
  have e : (1 + 1 / (8 * B)) - 1 = 1 / (8 * B) := by ring
  rw [e] at h1 h2
  have e1 : (4:ℝ)⁻¹ / (1 / (8 * B)) = 2 * B := by field_simp; ring
  have e2 : (1/8:ℝ) / (1 / (8 * B)) = B := by field_simp
  rw [e1] at h1; rw [e2] at h2
  have := le_abs_self C; have := le_abs_self K
  linarith

theorem mainD : {n : ℕ | ¬ HasSierpinskiDecomposition n}.HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP, hprod⟩ := prod_smallC
    (fun n : ℕ => if n.Prime ∧ n % 5 = 4 then (1:ℝ) / n else 0) (fun n => rfl) divA (ε/2)
    (by positivity)
  set Q := ∏ p ∈ P, p with hQdef
  have hQ : 0 < Q := prod_pos (fun p hp => (hP p hp).1.pos)
  have hrat := totient_prodB P (fun p hp => (hP p hp).1)
  rw [← hQdef] at hrat
  set T : ℝ := ((Nat.totient Q : ℕ) : ℝ) with hT
  have hq : (0:ℝ) < Q := by exact_mod_cast hQ
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((1 + T) / (ε / 2))
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNgt : (N0:ℝ) < N := by exact_mod_cast (show N0 < N by omega)
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (Nat.cast_nonneg _) hNgt
  have hsub : {n : ℕ | ¬ HasSierpinskiDecomposition n} ∩ Set.univ ∩ Set.Iio N ⊆
      ↑(insert 0 ((range N).filter (fun n => Q.Coprime n))) := by
    rintro n ⟨⟨hn, -⟩, hlt⟩
    simp only [coe_insert, coe_filter, mem_range, Set.mem_insert_iff, Set.mem_ofPred_eq]
    rcases Nat.eq_zero_or_pos n with h0 | hn0
    · left; exact h0
    · right
      refine ⟨hlt, ?_⟩
      apply Nat.Coprime.prod_left
      intro p hp
      exact (Nat.Prime.coprime_iff_not_dvd (hP p hp).1).2
        (fun hd => hn (decompB hn0 (hP p hp).1 (hP p hp).2 hd))
  have hcard : (({n : ℕ | ¬ HasSierpinskiDecomposition n} ∩ Set.univ ∩ Set.Iio N).ncard : ℝ)
      ≤ 1 + ((N / Q : ℕ) + 1) * T := by
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 := card_insert_le 0 ((range N).filter (fun n => Q.Coprime n))
    have h3 := count_coprimeB Q N hQ
    have h4 : ({n : ℕ | ¬ HasSierpinskiDecomposition n} ∩ Set.univ ∩ Set.Iio N).ncard ≤
        1 + (N / Q + 1) * Nat.totient Q := by omega
    have h5 : ((({n : ℕ | ¬ HasSierpinskiDecomposition n} ∩ Set.univ ∩ Set.Iio N).ncard : ℕ) : ℝ)
        ≤ ((1 + (N / Q + 1) * Nat.totient Q : ℕ) : ℝ) := by exact_mod_cast h4
    rw [hT]; push_cast at h5 ⊢; linarith
  have hden : ((Set.univ ∩ Set.Iio N : Set ℕ).ncard : ℝ) = N := by
    rw [Set.univ_inter, ← Finset.coe_range, Set.ncard_coe_finset, card_range]
  have hd : ((N / Q : ℕ) : ℝ) ≤ (N : ℝ) / Q := Nat.cast_div_le
  have hpd0 : 0 ≤ ({n : ℕ | ¬ HasSierpinskiDecomposition n}.partialDensity Set.univ N) := by
    unfold Set.partialDensity; positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpd0]
  unfold Set.partialDensity
  rw [hden, div_lt_iff₀ hNpos]
  have hA : (1 + T) < ε / 2 * N := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < ε / 2)).1 (hN0.trans hNgt)
    linarith
  have hB : ((N / Q : ℕ) : ℝ) * T ≤ T / Q * N := by
    calc ((N / Q : ℕ) : ℝ) * T ≤ (N : ℝ) / Q * T := mul_le_mul_of_nonneg_right hd hT0
      _ = T / Q * N := by ring
  have hC : T / Q * N < ε / 2 * N := by
    rw [hrat]; exact mul_lt_mul_of_pos_right hprod hNpos
  nlinarith

end SierpinskiDensitySolution

theorem OMA.solution : type_of% @SierpinskiEgyptianFractionConjecture.sierpinski_counterexamples_hasDensity_zero :=
  SierpinskiDensitySolution.mainD
