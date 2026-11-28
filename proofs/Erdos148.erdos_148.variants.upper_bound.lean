import FormalConjectures.ErdosProblems.«148»
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Counting ordered Egyptian-fraction decompositions with a bounded residual. -/

open Finset Filter Real
open scoped BigOperators Topology Asymptotics

namespace EgyptianCounting

open Erdos148 (u c₀)

private noncomputable def recip (a : ℕ → ℕ) (i : ℕ) : ℝ := 1 / a i

private noncomputable def gap (a : ℕ → ℕ) (i : ℕ) : ℝ :=
  1 - ∑ j ∈ range i, recip a j

private def denominator (a : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∏ j ∈ range i, a j

private lemma denominator_pos {a : ℕ → ℕ} (ha : ∀ j, 0 < a j) (i : ℕ) :
    0 < denominator a i :=
  Finset.prod_pos fun j _ => ha j

private lemma numerator_exists {a : ℕ → ℕ} (ha : ∀ j, 0 < a j) (i : ℕ) :
    ∃ m : ℤ, gap a i * (denominator a i : ℝ) = (m : ℝ) := by
  induction i with
  | zero => exact ⟨1, by norm_num [gap, denominator]⟩
  | succ i ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m * a i - denominator a i, ?_⟩
    have hg : gap a (i + 1) = gap a i - recip a i := by
      simp only [gap, sum_range_succ]
      ring
    rw [hg, denominator, prod_range_succ, ← denominator]
    push_cast
    have hzero : (a i : ℝ) ≠ 0 := by exact_mod_cast (ha i).ne'
    have hrec : recip a i * (a i : ℝ) = 1 := by simp [recip, hzero]
    calc
      (gap a i - recip a i) * ((denominator a i : ℝ) * a i) =
          (gap a i * denominator a i) * a i -
          (denominator a i : ℝ) * (recip a i * a i) := by ring
      _ = _ := by rw [hm, hrec, mul_one]

private lemma numerator_pos {a : ℕ → ℕ} (ha : ∀ j, 0 < a j) {i : ℕ}
    (hi : 0 < gap a i) :
    ∃ m : ℤ, 0 < m ∧ gap a i * (denominator a i : ℝ) = (m : ℝ) := by
  obtain ⟨m, hm⟩ := numerator_exists ha i
  have hd : (0 : ℝ) < denominator a i := by exact_mod_cast denominator_pos ha i
  have h : (0 : ℝ) < (m : ℝ) := by rw [← hm]; positivity
  exact ⟨m, by exact_mod_cast h, hm⟩

/-- The log-product comparison used in Soundararajan's proof of Curtiss's bound. -/
private lemma sum_le_of_prefix_products {x y : ℕ → ℝ} (n : ℕ)
    (hx : ∀ i < n, 0 < x i) (hy : ∀ i < n, 0 < y i)
    (hd : ∀ i, i + 1 < n → y (i + 1) ≤ y i)
    (hp : ∀ j ≤ n, (∏ i ∈ range j, y i) ≤ ∏ i ∈ range j, x i) :
    (∑ i ∈ range n, y i) ≤ ∑ i ∈ range n, x i := by
  let g : ℕ → ℝ := fun i => log (x i) - log (y i)
  have hG : ∀ j ≤ n, 0 ≤ ∑ i ∈ range j, g i := by
    intro j hj
    have hx0 : ∀ i ∈ range j, x i ≠ 0 :=
      fun i hi => (hx i ((mem_range.mp hi).trans_le hj)).ne'
    have hy0 : ∀ i ∈ range j, y i ≠ 0 :=
      fun i hi => (hy i ((mem_range.mp hi).trans_le hj)).ne'
    have hypos : 0 < ∏ i ∈ range j, y i :=
      Finset.prod_pos fun i hi => hy i ((mem_range.mp hi).trans_le hj)
    have hl := Real.log_le_log hypos (hp j hj)
    rw [Real.log_prod hx0, Real.log_prod hy0] at hl
    simpa only [g, sum_sub_distrib, sub_nonneg] using hl
  have hsum : 0 ≤ ∑ i ∈ range n, y i * g i := by
    by_cases hn : n = 0
    · simp [hn]
    have h := Finset.sum_range_by_parts y g n
    simp only [smul_eq_mul] at h
    rw [h]
    have hfirst : 0 ≤ y (n - 1) * (∑ i ∈ range n, g i) :=
      mul_nonneg (hy (n - 1) (by omega)).le (hG n le_rfl)
    have hsecond : (∑ i ∈ range (n - 1),
        (y (i + 1) - y i) * (∑ j ∈ range (i + 1), g j)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      have hi' := mem_range.mp hi
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hd i (by omega))) (hG _ (by omega))
    linarith
  have htangent : ∀ i ∈ range n, y i * g i ≤ x i - y i := by
    intro i hi
    have hxi := hx i (mem_range.mp hi)
    have hyi := hy i (mem_range.mp hi)
    have he := Real.add_one_le_exp (g i)
    rw [show g i = log (x i) - log (y i) from rfl,
      Real.exp_sub, Real.exp_log hxi, Real.exp_log hyi] at he
    have hh := (le_div_iff₀ hyi).mp he
    change y i * (log (x i) - log (y i)) ≤ x i - y i
    nlinarith only [hh]
  have hh := Finset.sum_le_sum htangent
  rw [Finset.sum_sub_distrib] at hh
  linarith

private lemma u_pos (i : ℕ) : 0 < u i := by
  induction i with
  | zero => decide
  | succ i ih => rw [u]; positivity

private def greedy (i : ℕ) : ℕ := u i + 1

private lemma greedy_pos (i : ℕ) : 0 < greedy i := by simp [greedy]

private lemma greedy_prod (i : ℕ) : denominator greedy i = u i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [denominator, prod_range_succ, greedy, u]; rw [← ih]; rfl

private lemma greedy_gap (i : ℕ) : gap greedy i = (1 : ℝ) / u i := by
  induction i with
  | zero => norm_num [gap, u]
  | succ i ih =>
    have hg : gap greedy (i + 1) = gap greedy i - recip greedy i := by
      simp only [gap, sum_range_succ]
      ring
    rw [hg, ih]
    simp only [recip, greedy, u, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hp : (0 : ℝ) < u i := by exact_mod_cast u_pos i
    field_simp
    ring

private lemma recip_prod (a : ℕ → ℕ) (n : ℕ) :
    (∏ i ∈ range n, recip a i) = (1 : ℝ) / denominator a n := by
  simp only [recip, one_div, Finset.prod_inv_distrib, denominator, Nat.cast_prod]

/-- Curtiss's sharp lower bound on the positive residual of a finite unit-fraction sum. -/
private lemma curtiss {a : ℕ → ℕ} (ha : ∀ i, 0 < a i) (hm : Monotone a) (n : ℕ)
    (hgap : 0 < gap a n) : (1 : ℝ) / u n ≤ gap a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hprod : denominator a n ≤ u n
    · obtain ⟨m, hm, heq⟩ := numerator_pos ha hgap
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
      have hd : (0 : ℝ) < denominator a n := by exact_mod_cast denominator_pos ha n
      have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos n
      have hh : (denominator a n : ℝ) ≤ u n := by exact_mod_cast hprod
      refine ((one_div_le_one_div_of_le hd hh)).trans ?_
      exact (div_le_iff₀ hd).mpr (heq ▸ hm1)
    · let Good : ℕ → Prop := fun j =>
        j < n ∧ (∏ i ∈ range (n - j), greedy (j + i)) ≤
          ∏ i ∈ range (n - j), a (j + i)
      have hex : ∃ j, Good j := by
        refine ⟨0, ?_, ?_⟩
        · by_contra hz
          have hn : n = 0 := by omega
          subst n
          simp [denominator, u] at hprod
        · simp only [Nat.sub_zero, zero_add]
          change denominator greedy n ≤ denominator a n
          rw [greedy_prod]
          omega
      classical
      let s := (Finset.range n).filter Good
      have hs : s.Nonempty := by
        obtain ⟨j, hj⟩ := hex
        exact ⟨j, Finset.mem_filter.mpr ⟨mem_range.mpr hj.1, hj⟩⟩
      let l := s.max' hs
      have hl : Good l := (Finset.mem_filter.mp (Finset.max'_mem _ _)).2
      -- The maximal suffix with the larger product gives product comparisons
      -- on every initial segment of that suffix.
      have hprefix : ∀ r ≤ n - l,
          (∏ i ∈ range r, recip a (l + i)) ≤ ∏ i ∈ range r, recip greedy (l + i) := by
        intro r hr
        by_cases hr0 : r = 0
        · simp [hr0]
        have hsuff : (∏ i ∈ range (n - l - r), a (l + r + i)) ≤
            ∏ i ∈ range (n - l - r), greedy (l + r + i) := by
          by_cases he : r = n - l
          · simp [he]
          · have hlt : l + r < n := by omega
            have hnGood : ¬ Good (l + r) := by
              intro hh
              have := Finset.le_max' s (l + r)
                (Finset.mem_filter.mpr ⟨mem_range.mpr hlt, hh⟩)
              change l + r ≤ l at this
              omega
            have hne := not_le.mp (fun h : (∏ i ∈ range (n - (l + r)), greedy (l + r + i)) ≤
                ∏ i ∈ range (n - (l + r)), a (l + r + i) => hnGood ⟨hlt, h⟩)
            simpa only [show n - (l + r) = n - l - r by omega] using hne.le
        have ham : 0 < ∏ i ∈ range (n - l - r), a (l + r + i) :=
          Finset.prod_pos fun i _ => ha _
        have hgm : 0 < ∏ i ∈ range r, greedy (l + i) :=
          Finset.prod_pos fun i _ => greedy_pos _
        have hall := hl.2
        rw [show n - l = r + (n - l - r) by omega, Finset.prod_range_add,
          Finset.prod_range_add] at hall
        simp only [Nat.add_assoc] at hsuff
        have hnat : (∏ i ∈ range r, greedy (l + i)) ≤ ∏ i ∈ range r, a (l + i) := by
          by_contra! hbad
          have hmul := Nat.mul_lt_mul_of_pos_right hbad ham
          have hw := Nat.mul_le_mul_left (∏ i ∈ range r, greedy (l + i)) hsuff
          simp only [Nat.add_assoc] at hmul hw hall
          exact (not_lt_of_ge hall) (hmul.trans_le hw)
        have has : (∏ i ∈ range r, recip a (l + i)) =
            (1 : ℝ) / (∏ i ∈ range r, a (l + i) : ℕ) := recip_prod (fun i => a (l + i)) r
        have hgs : (∏ i ∈ range r, recip greedy (l + i)) =
            (1 : ℝ) / (∏ i ∈ range r, greedy (l + i) : ℕ) := recip_prod (fun i => greedy (l + i)) r
        rw [has, hgs]
        exact one_div_le_one_div_of_le (by exact_mod_cast hgm) (by exact_mod_cast hnat)
      have htail := sum_le_of_prefix_products (n - l) (x := fun i => recip greedy (l + i))
        (y := fun i => recip a (l + i))
        (fun i _ => one_div_pos.mpr (by exact_mod_cast greedy_pos (l + i)))
        (fun i _ => one_div_pos.mpr (by exact_mod_cast ha (l + i)))
        (fun i _ => one_div_le_one_div_of_le (by exact_mod_cast ha (l + i))
          (by exact_mod_cast hm (show l + i ≤ l + (i + 1) by omega))) hprefix
      have hlt : l < n := hl.1
      have hpos : 0 < gap a l := by
        have hg := Finset.sum_range_add (recip a) l (n - l)
        rw [Nat.add_sub_of_le hlt.le] at hg
        have hnt : 0 ≤ ∑ i ∈ range (n - l), recip a (l + i) := by
          apply Finset.sum_nonneg
          intro i _
          unfold recip
          positivity
        dsimp [gap] at hgap ⊢
        linarith
      have hfirst := ih l hlt hpos
      have hsa := Finset.sum_range_add (recip a) l (n - l)
      have hsg := Finset.sum_range_add (recip greedy) l (n - l)
      rw [Nat.add_sub_of_le hlt.le] at hsa hsg
      rw [← greedy_gap l] at hfirst
      rw [← greedy_gap n]
      simp only [gap] at hfirst ⊢
      simp only [Nat.add_comm] at hsa hsg htail
      linarith

/-- A small-power divisor bound, with a uniform constant for the finitely many
smaller primes and a factor of one for every prime with p^δ at least two. -/
private lemma divisor_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  let B := (2 : ℝ) ^ δ
  have hB : 1 < B := Real.one_lt_rpow (by norm_num) hδ
  let K := max 1 (B - 1)⁻¹
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := by linarith
  have hKmul : 1 ≤ K * (B - 1) := by
    have h := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (B - 1)⁻¹) (show 0 ≤ B - 1 by linarith)
    simpa [K, inv_mul_cancel₀ (show B - 1 ≠ 0 by linarith)] using h
  have hsmall (e : ℕ) : (e : ℝ) + 1 ≤ K * B ^ e := by
    have h := one_add_mul_le_pow (a := B - 1) (by linarith) e
    rw [show 1 + (B - 1) = B by ring] at h
    have hj := mul_le_mul_of_nonneg_left h hKpos.le
    have hj' := mul_le_mul_of_nonneg_left hKmul (Nat.cast_nonneg (α := ℝ) e)
    nlinarith only [hj, hj', hK]
  let T : ℕ := ⌈(2 : ℝ) ^ (1 / δ)⌉₊
  have hlargeBase (p : ℕ) (hp : T ≤ p) : 2 ≤ (p : ℝ) ^ δ := by
    have hT : (2 : ℝ) ^ (1 / δ) ≤ p :=
      (Nat.le_ceil _).trans (by exact_mod_cast hp)
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ (1 / δ)) hT hδ.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      div_mul_cancel₀ _ hδ.ne', Real.rpow_one] at h
    exact h
  refine ⟨K ^ T, one_le_pow₀ hK, ?_⟩
  intro n hn
  rw [Nat.card_divisors hn.ne', Nat.cast_prod]
  let W : ℕ → ℝ := fun p => if p < T then K else 1
  have hpoint (p : ℕ) (hp : p ∈ n.primeFactors) :
      ((n.factorization p + 1 : ℕ) : ℝ) ≤
        W p * ((p : ℝ) ^ n.factorization p) ^ δ := by
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    rw [Nat.cast_add, Nat.cast_one, ← Real.rpow_natCast_mul (Nat.cast_nonneg p),
      mul_comm (n.factorization p : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    by_cases hpt : p < T
    · rw [show W p = K from if_pos hpt]
      refine (hsmall _).trans ?_
      gcongr
      exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp2) hδ.le
    · rw [show W p = 1 from if_neg hpt, one_mul]
      have hnat (e : ℕ) : e + 1 ≤ 2 ^ e := by
        induction e with
        | zero => decide
        | succ e ih =>
          rw [pow_succ]
          omega
      calc
        _ ≤ (2 : ℝ) ^ n.factorization p := by
          exact_mod_cast hnat (n.factorization p)
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) (hlargeBase p (by omega)) _
  have hprod := Finset.prod_le_prod
    (s := n.primeFactors) (f := fun p => ((n.factorization p + 1 : ℕ) : ℝ))
    (g := fun p => W p * ((p : ℝ) ^ n.factorization p) ^ δ)
    (fun p hp => Nat.cast_nonneg _) hpoint
  refine hprod.trans ?_
  rw [Finset.prod_mul_distrib, Real.finsetProd_rpow n.primeFactors
    (fun p => (p : ℝ) ^ n.factorization p) (fun p hp => by positivity) δ]
  have hnprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = n := by
    exact_mod_cast (show (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n from
      n.prod_factorization_pow_eq_self hn.ne')
  rw [hnprod]
  gcongr
  have hw : (∏ p ∈ n.primeFactors, W p) =
      K ^ (n.primeFactors.filter (· < T)).card := by
    rw [← Finset.prod_filter]
    exact Finset.prod_const K
  rw [hw]
  apply pow_le_pow_right₀ hK
  calc
    _ ≤ (Finset.range T).card :=
      Finset.card_le_card (fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
    _ = T := Finset.card_range _

private lemma two_mul_u_le (i : ℕ) : 2 * u i ≤ 2 ^ (2 ^ i : ℕ) := by
  induction i with
  | zero => decide
  | succ i ih =>
    have hu := u_pos i
    calc
      2 * u (i + 1) ≤ (2 * u i) ^ 2 := by rw [u]; nlinarith
      _ ≤ (2 ^ (2 ^ i : ℕ)) ^ 2 := Nat.pow_le_pow_left ih 2
      _ = _ := by rw [← pow_mul, pow_succ (2 : ℕ) i]

private lemma c₀_bounded : BddAbove (Set.range fun j : ℕ => (u j : ℝ) ^ ((1 : ℝ) / 2 ^ j)) := by
  refine ⟨2, ?_⟩
  intro z hz
  obtain ⟨j, rfl⟩ := hz
  have hnat : u j ≤ (2 : ℕ) ^ (2 ^ j : ℕ) := by
    have := two_mul_u_le j
    omega
  have hreal : (u j : ℝ) ≤ (2 : ℝ) ^ (2 ^ j : ℕ) := by exact_mod_cast hnat
  have h := Real.rpow_le_rpow (Nat.cast_nonneg _) hreal
    (show (0 : ℝ) ≤ 1 / 2 ^ j by positivity)
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hex : (↑(2 ^ j : ℕ) : ℝ) * (1 / 2 ^ j) = 1 := by
    push_cast
    field_simp
  rwa [hex, Real.rpow_one] at h

private lemma u_le_c₀ (i : ℕ) : (u i : ℝ) ≤ c₀ ^ (2 ^ i : ℕ) := by
  have hsup : (u i : ℝ) ^ ((1 : ℝ) / 2 ^ i) ≤ c₀ := le_ciSup c₀_bounded i
  have hu0 : (0 : ℝ) ≤ u i := Nat.cast_nonneg _
  have hm := pow_le_pow_left₀ (Real.rpow_nonneg hu0 _) hsup (2 ^ i : ℕ)
  rw [← Real.rpow_mul_natCast hu0] at hm
  have hex : (1 : ℝ) / 2 ^ i * ↑(2 ^ i : ℕ) = 1 := by
    push_cast
    field_simp
  rwa [hex, Real.rpow_one] at hm

private lemma one_lt_c₀ : 1 < c₀ := by
  have h := u_le_c₀ 1
  norm_num [u] at h
  have h0 : 0 ≤ c₀ := le_ciSup_of_le c₀_bounded 0 (by norm_num [u])
  by_contra! hc
  have hc2 := pow_le_pow_left₀ h0 hc 2
  rw [one_pow] at hc2
  linarith

private lemma gap_succ (a : ℕ → ℕ) (i : ℕ) : gap a (i + 1) = gap a i - recip a i := by
  simp only [gap, sum_range_succ]
  ring

private lemma denominator_succ (a : ℕ → ℕ) (i : ℕ) :
    denominator a (i + 1) = denominator a i * a i :=
  Finset.prod_range_succ a i

private structure Sol (k : ℕ) (a : ℕ → ℕ) : Prop where
  pos : ∀ i, 0 < a i
  mono : Monotone a
  sum_eq : (∑ i ∈ range k, recip a i) = 1

private lemma Sol.tail {k : ℕ} {a : ℕ → ℕ} (h : Sol k a) {i : ℕ} (hi : i ≤ k) :
    gap a i = ∑ j ∈ range (k - i), recip a (i + j) := by
  have hh := Finset.sum_range_add (recip a) i (k - i)
  rw [Nat.add_sub_of_le hi, h.sum_eq] at hh
  simp only [gap]
  linarith

private lemma Sol.gap_pos {k : ℕ} {a : ℕ → ℕ} (h : Sol k a) {i : ℕ} (hi : i < k) :
    0 < gap a i := by
  rw [h.tail hi.le]
  apply Finset.sum_pos
  · intro j hj
    exact one_div_pos.mpr (by exact_mod_cast h.pos (i + j))
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

private lemma Sol.rank_gap {k : ℕ} {a : ℕ → ℕ} (h : Sol k a) {i : ℕ} (hi : i < k) :
    (a i : ℝ) * gap a i ≤ (k - i : ℕ) := by
  have hp : (0 : ℝ) < a i := by exact_mod_cast h.pos i
  have hs : gap a i ≤ ((k - i : ℕ) : ℝ) / a i := by
    rw [h.tail hi.le, show ((↑(k - i : ℕ) : ℝ) / a i) =
        ∑ j ∈ range (k - i), (1 : ℝ) / a i by simp [div_eq_mul_inv, nsmul_eq_mul]]
    apply Finset.sum_le_sum
    intro j hj
    exact one_div_le_one_div_of_le hp (by exact_mod_cast h.mono (Nat.le_add_right i j))
  rw [mul_comm]
  exact (le_div_iff₀ hp).mp hs

private lemma Sol.rank_bound {k : ℕ} {a : ℕ → ℕ} (h : Sol k a) {i : ℕ} (hi : i < k) :
    a i ≤ (k - i) * u i := by
  have hu : (0 : ℝ) < u i := by exact_mod_cast u_pos i
  have ha : (0 : ℝ) ≤ a i := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left (curtiss h.pos h.mono i (h.gap_pos hi)) ha
  have hmain : (a i : ℝ) / u i ≤ (k - i : ℕ) := by
    simpa only [mul_one_div] using hh.trans (h.rank_gap hi)
  exact_mod_cast (div_le_iff₀ hu).mp hmain

private lemma prefix_box_product (k p : ℕ) :
    (∏ i ∈ range p, k * u i) ≤ k ^ p * u p := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range]
  apply Nat.mul_le_mul_left
  rw [← greedy_prod p]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => Nat.le_succ _

private lemma Sol.prefix_prod {k : ℕ} {a : ℕ → ℕ} (h : Sol k a) {p : ℕ} (hp : p ≤ k) :
    denominator a p ≤ k ^ p * u p := by
  refine le_trans (Finset.prod_le_prod (s := range p) (f := a)
    (g := fun i => k * u i) (fun _ _ => Nat.zero_le _) ?_) (prefix_box_product k p)
  intro i hi
  exact (h.rank_bound ((Finset.mem_range.mp hi).trans_le hp)).trans
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

private noncomputable def middleCut (a : ℕ → ℕ) (p : ℕ) : ℕ := ⌊1 / gap a p⌋₊ + 1

private noncomputable def middleDifference (a : ℕ → ℕ) (p : ℕ) : ℕ := a p - middleCut a p

/-- Away from the first possible next denominator, the difference from the
cut and the following denominator have bounded product. At the cut, the
following denominator is retained directly. -/
private noncomputable def middleProduct (a : ℕ → ℕ) (p : ℕ) : ℕ :=
  if middleDifference a p = 0 then a (p + 1) else middleDifference a p * a (p + 1)

private lemma Sol.middle_cut_le {p : ℕ} {a : ℕ → ℕ} (h : Sol (p + 4) a) :
    middleCut a p ≤ a p := by
  have hg := h.gap_pos (i := p) (by omega)
  have hn := h.gap_pos (i := p + 1) (by omega)
  rw [gap_succ] at hn
  have ha : (0 : ℝ) < a p := by exact_mod_cast h.pos p
  have hp : (1 : ℝ) / (a p : ℝ) < gap a p := sub_pos.mp hn
  have ht : (1 : ℝ) / gap a p < a p := by
    apply (div_lt_iff₀ hg).mpr
    have hh := (div_lt_iff₀ ha).mp hp
    linarith
  exact Nat.succ_le_of_lt ((Nat.floor_lt (by positivity)).mpr ht)

private lemma Sol.middle_spec {p : ℕ} {a : ℕ → ℕ} (h : Sol (p + 4) a) :
    0 < middleProduct a p ∧ middleProduct a p ≤ 12 * (u p) ^ 2 ∧
      (middleDifference a p = 0 ∨ middleDifference a p ∈ (middleProduct a p).divisors) ∧
      a (p + 1) ≤ 12 * (u p) ^ 2 := by
  let d := middleDifference a p
  let b := a (p + 1)
  have hb : 0 < b := h.pos _
  have hu := u_pos p
  by_cases hd : d = 0
  · have hb' : b ≤ 3 * u (p + 1) := by
      simpa [show p + 4 - (p + 1) = 3 by omega] using
        h.rank_bound (i := p + 1) (by omega)
    have hbig : 3 * u (p + 1) ≤ 12 * u p ^ 2 := by
      rw [u]
      have hh := Nat.mul_le_mul_left (u p) (show u p + 1 ≤ 2 * u p by omega)
      nlinarith only [hh]
    have heq : middleProduct a p = b := if_pos hd
    exact ⟨heq ▸ hb, heq ▸ hb'.trans hbig, Or.inl hd, hb'.trans hbig⟩
  · let t : ℝ := 1 / gap a p
    have hg := h.gap_pos (i := p) (by omega)
    have ht : 0 < t := one_div_pos.mpr hg
    have ht_le : t ≤ u p := by
      have hu' : (0 : ℝ) < u p := by exact_mod_cast hu
      have hh := one_div_le_one_div_of_le (one_div_pos.mpr hu')
        (curtiss h.pos h.mono p hg)
      simpa [t, one_div_div] using hh
    have ha : (0 : ℝ) < a p := by exact_mod_cast h.pos p
    have ha_le : (a p : ℝ) ≤ 4 * u p := by
      exact_mod_cast (show a p ≤ 4 * u p from by simpa using h.rank_bound (i := p) (by omega))
    have hcut : t ≤ middleCut a p := by
      simpa only [middleCut, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one t).le
    have hdiff : (d : ℝ) ≤ (a p : ℝ) - t := by
      change ((a p - middleCut a p : ℕ) : ℝ) ≤ (a p : ℝ) - t
      rw [Nat.cast_sub h.middle_cut_le]
      linarith
    have hidentity : (a p : ℝ) - t = t * a p * gap a (p + 1) := by
      rw [gap_succ, recip]
      dsimp [t]
      field_simp
    have hbg : (b : ℝ) * gap a (p + 1) ≤ 3 := by
      simpa [b, show p + 4 - (p + 1) = 3 by omega] using h.rank_gap (i := p + 1) (by omega)
    have hbg0 : 0 ≤ (b : ℝ) * gap a (p + 1) :=
      mul_nonneg (Nat.cast_nonneg b) (h.gap_pos (by omega)).le
    have hmul : d * b ≤ 12 * u p ^ 2 := by
      apply (Nat.cast_le (α := ℝ)).mp
      push_cast
      calc
        (d : ℝ) * b ≤ ((a p : ℝ) - t) * b := mul_le_mul_of_nonneg_right hdiff (Nat.cast_nonneg _)
        _ = (t * a p) * ((b : ℝ) * gap a (p + 1)) := by rw [hidentity]; ring
        _ ≤ ((u p : ℝ) * (4 * u p)) * 3 := by gcongr
        _ = 12 * (u p : ℝ) ^ 2 := by ring
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdb : 0 < d * b := Nat.mul_pos hdpos hb
    have heq : middleProduct a p = d * b := if_neg hd
    have hdd : d ∣ d * b := dvd_mul_right _ _
    have hb_le : b ≤ d * b := by
      simpa using Nat.mul_le_mul_right b (show 1 ≤ d by omega)
    rw [heq]
    exact ⟨hdb, hmul, Or.inr (Nat.mem_divisors.mpr ⟨hdd, hdb.ne'⟩), hb_le.trans hmul⟩

private lemma Sol.final_den_bound {p : ℕ} {a : ℕ → ℕ} (h : Sol (p + 4) a) :
    denominator a (p + 2) ≤ 48 * (p + 4) ^ p * (u p) ^ 4 := by
  have ha : a p ≤ 4 * u p := by simpa using h.rank_bound (i := p) (by omega)
  have hb := h.middle_spec.2.2.2
  rw [denominator_succ, denominator_succ]
  calc
    _ ≤ ((p + 4) ^ p * u p) * (4 * u p) * (12 * u p ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (h.prefix_prod (by omega)) ha) hb
    _ = _ := by ring

private noncomputable def residualNumerator (a : ℕ → ℕ) (i : ℕ) : ℤ :=
  ⌊gap a i * (denominator a i : ℝ)⌋

private lemma residual_numerator_cast {a : ℕ → ℕ} (ha : ∀ j, 0 < a j) (i : ℕ) :
    ((residualNumerator a i : ℤ) : ℝ) = gap a i * (denominator a i : ℝ) := by
  obtain ⟨m, hm⟩ := numerator_exists ha i
  rw [residualNumerator, hm, Int.floor_intCast]

private noncomputable def finalFactor (a : ℕ → ℕ) (i : ℕ) : ℤ :=
  residualNumerator a i * (a i : ℤ) - (denominator a i : ℤ)

private lemma Sol.final_factor_pos {k : ℕ} {a : ℕ → ℕ} (h : Sol k a) {i : ℕ}
    (hi : i + 1 < k) : 0 < finalFactor a i := by
  have hg := h.gap_pos hi
  rw [gap_succ] at hg
  have ha : (0 : ℝ) < a i := by exact_mod_cast h.pos i
  have hn : (0 : ℝ) < denominator a i := by exact_mod_cast denominator_pos h.pos i
  have hg' : (1 : ℝ) / (a i : ℝ) < gap a i := sub_pos.mp hg
  have ht := (div_lt_iff₀ ha).mp hg'
  have ht' := mul_lt_mul_of_pos_right ht hn
  have hreal : (0 : ℝ) < ((finalFactor a i : ℤ) : ℝ) := by
    rw [finalFactor]
    push_cast
    rw [residual_numerator_cast h.pos]
    nlinarith only [ht']
  exact_mod_cast hreal

/-- For a two-term residual m/N, the two factors mA-N and mB-N multiply to N². -/
private lemma Sol.final_code_mem {p : ℕ} {a : ℕ → ℕ} (h : Sol (p + 4) a) :
    (finalFactor a (p + 2)).toNat ∈ ((denominator a (p + 2)) ^ 2).divisors := by
  let i := p + 2
  let m := residualNumerator a i
  let N := denominator a i
  let A := a i
  let B := a (i + 1)
  let z : ℤ := m * (A : ℤ) - N
  let w : ℤ := m * (B : ℤ) - N
  have ha : (0 : ℝ) < A := by exact_mod_cast h.pos i
  have hb : (0 : ℝ) < B := by exact_mod_cast h.pos (i + 1)
  have hn : (0 : ℝ) < N := by exact_mod_cast denominator_pos h.pos i
  have hg := h.tail (i := i) (by omega)
  have hd : p + 4 - i = 2 := by omega
  rw [hd] at hg
  have hg' : gap a i = (1 : ℝ) / A + (1 : ℝ) / B := by
    simpa [Finset.sum_range_succ, recip, A, B] using hg
  have hm : (m : ℝ) = gap a i * N := residual_numerator_cast h.pos i
  have hm' : (m : ℝ) * A * B = (N : ℝ) * ((A : ℝ) + B) := by
    rw [hm, hg']
    field_simp
    ring
  have hz : 0 < z := h.final_factor_pos (i := i) (by omega)
  have hw : 0 < w := by
    have hlt : (1 : ℝ) / (B : ℝ) < gap a i := by rw [hg']; linarith [one_div_pos.mpr ha]
    have hh := (div_lt_iff₀ hb).mp hlt
    have hh' := mul_lt_mul_of_pos_right hh hn
    have hreal : (0 : ℝ) < (w : ℝ) := by
      simp only [w, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      rw [hm]
      nlinarith only [hh']
    exact_mod_cast hreal
  have heq : z * w = (N : ℤ) ^ 2 := by
    apply Int.cast_injective (α := ℝ)
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, z, w, Int.cast_sub]
    change ((m : ℝ) * A - N) * ((m : ℝ) * B - N) = (N : ℝ) ^ 2
    linear_combination (m : ℝ) * hm'
  have hnat : z.toNat * w.toNat = N ^ 2 := by
    apply Int.ofNat.inj
    change (((z.toNat * w.toNat : ℕ) : ℤ)) = (↑(N ^ 2 : ℕ) : ℤ)
    simp only [Nat.cast_mul, Nat.cast_pow]
    rwa [Int.toNat_of_nonneg hz.le, Int.toNat_of_nonneg hw.le]
  exact Nat.mem_divisors.mpr ⟨⟨w.toNat, hnat.symm⟩, pow_ne_zero 2 (denominator_pos h.pos i).ne'⟩

private def solutionSet (p : ℕ) : Set (Finset ℕ) :=
  {S | S.card = p + 4 ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℚ) / n = 1}

private noncomputable def ordered {p : ℕ} (S : solutionSet p) (i : ℕ) : ℕ :=
  S.val.orderEmbOfFin S.property.1 ⟨min i (p + 3), by omega⟩

private lemma ordered_at {p : ℕ} (S : solutionSet p) (i : Fin (p + 4)) :
    ordered S i = S.val.orderEmbOfFin S.property.1 i := by
  unfold ordered
  congr 1
  exact Fin.ext (Nat.min_eq_left (by have := i.isLt; omega))

private lemma ordered_sol {p : ℕ} (S : solutionSet p) : Sol (p + 4) (ordered S) := by
  have hpos : ∀ i, 0 < ordered S i := by
    intro i
    have hi : ordered S i ∈ S.val := Finset.orderEmbOfFin_mem S.val S.property.1 _
    exact Nat.pos_of_ne_zero (fun h => S.property.2.1 (h ▸ hi))
  have hmono : Monotone (ordered S) := by
    intro i j hij
    exact (S.val.orderEmbOfFin S.property.1).monotone (min_le_min_right (p + 3) hij)
  refine ⟨hpos, hmono, ?_⟩
  have hrange := Fin.sum_univ_eq_sum_range (recip (ordered S)) (p + 4)
  rw [← hrange]
  simp only [recip, ordered_at]
  have himage := Finset.image_orderEmbOfFin_univ S.val S.property.1
  have hcast : (∑ n ∈ S.val, (1 : ℝ) / n) = 1 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) S.property.2.2
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using h
  rw [← himage, Finset.sum_image] at hcast
  · exact hcast
  · exact (S.val.orderEmbOfFin S.property.1).injective.injOn

private lemma ordered_ext {p : ℕ} {S T : solutionSet p}
    (h : ∀ i < p + 4, ordered S i = ordered T i) : S = T := by
  apply Subtype.ext
  rw [← Finset.image_orderEmbOfFin_univ S.val S.property.1,
    ← Finset.image_orderEmbOfFin_univ T.val T.property.1]
  congr 1
  funext i
  rw [← ordered_at S i, ← ordered_at T i]
  exact h i i.isLt

private lemma gap_congr {a b : ℕ → ℕ} {i : ℕ} (h : ∀ j < i, a j = b j) :
    gap a i = gap b i := by
  unfold gap
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [recip, h j (mem_range.mp hj)]

private lemma denominator_congr {a b : ℕ → ℕ} {i : ℕ} (h : ∀ j < i, a j = b j) :
    denominator a i = denominator b i :=
  Finset.prod_congr rfl (fun j hj => h j (mem_range.mp hj))

private noncomputable def rankCode (G : Finset ℕ) (J : ℕ) (hG : G.card ≤ J)
    (x : G) : Fin J :=
  Fin.castLE hG ((G.orderIsoOfFin rfl).symm x)

private lemma rankCode_cancel {G H : Finset ℕ} {J : ℕ} (hG : G.card ≤ J) (hH : H.card ≤ J)
    {x : G} {y : H} (he : G = H) (hc : rankCode G J hG x = rankCode H J hH y) :
    (x : ℕ) = y := by
  subst H
  have hv := congrArg Fin.val hc
  have ht : (G.orderIsoOfFin rfl).symm x = (G.orderIsoOfFin rfl).symm y :=
    Fin.ext hv
  exact congrArg Subtype.val ((G.orderIsoOfFin rfl).symm.injective ht)

private noncomputable def optionRank (G : Finset ℕ) (J : ℕ) (hG : G.card ≤ J)
    (x : ℕ) (hx : x = 0 ∨ x ∈ G) : Fin (J + 1) :=
  if hz : x = 0 then 0
  else (rankCode G J hG ⟨x, hx.resolve_left hz⟩).succ

private lemma optionRank_cancel {G H : Finset ℕ} {J : ℕ}
    (hG : G.card ≤ J) (hH : H.card ≤ J) {x y : ℕ}
    (hx : x = 0 ∨ x ∈ G) (hy : y = 0 ∨ y ∈ H) (he : G = H)
    (hc : optionRank G J hG x hx = optionRank H J hH y hy) :
    x = y := by
  by_cases hx0 : x = 0 <;> by_cases hy0 : y = 0
  · exact hx0.trans hy0.symm
  · simp [optionRank, hx0, hy0] at hc
    exact (Fin.succ_ne_zero _ hc.symm).elim
  · simp [optionRank, hx0, hy0] at hc
  · have hf : rankCode G J hG ⟨x, hx.resolve_left hx0⟩ =
        rankCode H J hH ⟨y, hy.resolve_left hy0⟩ := by
      apply Fin.succ_injective _
      simpa only [optionRank, dif_neg hx0, dif_neg hy0] using hc
    exact rankCode_cancel hG hH he hf

private lemma middle_cancel {p : ℕ} {a b : ℕ → ℕ}
    (ha : Sol (p + 4) a) (hb : Sol (p + 4) b)
    (hpre : ∀ i < p, a i = b i) (hx : middleProduct a p = middleProduct b p)
    (hy : middleDifference a p = middleDifference b p) :
    a p = b p ∧ a (p + 1) = b (p + 1) := by
  have hca := ha.middle_cut_le
  have hcb := hb.middle_cut_le
  have hc : middleCut a p = middleCut b p := by
    simp only [middleCut, gap_congr hpre]
  have he : a p = b p := by
    unfold middleDifference at hy
    omega
  refine ⟨he, ?_⟩
  by_cases hn : middleDifference a p = 0
  · simpa only [middleProduct, if_pos hn, if_pos (hy ▸ hn)] using hx
  · simp only [middleProduct, if_neg hn, ← hy] at hx
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) hx

private lemma final_cancel {p : ℕ} {a b : ℕ → ℕ} (ha : Sol (p + 4) a)
    (hb : Sol (p + 4) b) (hpre : ∀ i < p + 2, a i = b i)
    (hx : (finalFactor a (p + 2)).toNat = (finalFactor b (p + 2)).toNat) :
    ∀ i < p + 4, a i = b i := by
  have hgap := gap_congr hpre
  have hden := denominator_congr hpre
  have hm : residualNumerator a (p + 2) = residualNumerator b (p + 2) := by
    simp only [residualNumerator, hgap, hden]
  have hma : 0 < residualNumerator a (p + 2) := by
    apply (Int.cast_pos (R := ℝ)).mp
    rw [residual_numerator_cast ha.pos]
    exact mul_pos (ha.gap_pos (by omega)) (by exact_mod_cast denominator_pos ha.pos _)
  have hf : finalFactor a (p + 2) = finalFactor b (p + 2) := by
    have ht := congrArg Int.ofNat hx
    change ((finalFactor a (p + 2)).toNat : ℤ) =
      ((finalFactor b (p + 2)).toNat : ℤ) at ht
    rwa [Int.toNat_of_nonneg (ha.final_factor_pos (i := p + 2) (by omega)).le,
      Int.toNat_of_nonneg (hb.final_factor_pos (i := p + 2) (by omega)).le] at ht
  have hc : a (p + 2) = b (p + 2) := by
    simp only [finalFactor, ← hm, ← hden] at hf
    have ht : residualNumerator a (p + 2) * (a (p + 2) : ℤ) =
        residualNumerator a (p + 2) * (b (p + 2) : ℤ) := by linarith
    exact_mod_cast (mul_left_cancel₀ hma.ne' ht)
  have hta := ha.tail (i := p + 2) (by omega)
  have htb := hb.tail (i := p + 2) (by omega)
  simp [show p + 4 - (p + 2) = 2 by omega, sum_range_succ] at hta
  simp [show p + 4 - (p + 2) = 2 by omega, sum_range_succ] at htb
  have hd' : recip a (p + 2 + 1) = recip b (p + 2 + 1) := by
    simp only [recip, hc] at hta ⊢
    unfold recip at htb
    linarith
  have hd : a (p + 3) = b (p + 3) := by
    have hd'' : ((a (p + 3) : ℕ) : ℝ)⁻¹ = ((b (p + 3) : ℕ) : ℝ)⁻¹ := by
      simpa only [recip, one_div, show p + 2 + 1 = p + 3 by omega] using hd'
    exact_mod_cast inv_injective hd''
  intro i hi
  by_cases hh : i < p + 2
  · exact hpre i hh
  · rcases (show i = p + 2 ∨ i = p + 3 by omega) with rfl | rfl
    · exact hc
    · exact hd

private lemma count_bound (p : ℕ) (δ C : ℝ) (hδ : 0 < δ)
    (hdiv : ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ)
    (hC : 1 ≤ C) :
    Erdos148.F (p + 4) ≤ ((p + 4) ^ p * u p) * (12 * u p ^ 2) *
      (⌊C * ((12 * u p ^ 2 : ℕ) : ℝ) ^ δ⌋₊ + 1) *
      ⌊C * (((48 * (p + 4) ^ p * u p ^ 4) ^ 2 : ℕ) : ℝ) ^ δ⌋₊ := by
  classical
  let k := p + 4
  let U := u p
  let B := 12 * U ^ 2
  let D := 48 * k ^ p * U ^ 4
  let J := ⌊C * (B : ℝ) ^ δ⌋₊
  let L := ⌊C * (D ^ 2 : ℕ) ^ δ⌋₊
  have hc0 : 0 ≤ C := by linarith
  have div_le_floor {n bound : ℕ} (hn : 0 < n) (hle : n ≤ bound) :
      n.divisors.card ≤ ⌊C * (bound : ℝ) ^ δ⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    refine (hdiv n hn).trans (mul_le_mul_of_nonneg_left ?_ hc0)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) hδ.le
  have hmiddle (S : solutionSet p) :
      (middleProduct (ordered S) p).divisors.card ≤ J := by
    have hm := (ordered_sol S).middle_spec
    exact div_le_floor hm.1 hm.2.1
  have hfinal (S : solutionSet p) :
      (denominator (ordered S) (p + 2) ^ 2).divisors.card ≤ L := by
    exact div_le_floor (pow_pos (denominator_pos (ordered_sol S).pos _) _)
      (Nat.pow_le_pow_left (ordered_sol S).final_den_bound _)
  let Code := (∀ i : Fin p, Fin (k * u i)) × Fin B × Fin (J + 1) × Fin L
  let code (S : solutionSet p) : Code :=
    ⟨fun i => ⟨ordered S i - 1, by
        have hi := (ordered_sol S).rank_bound (i := i) (by have := i.isLt; omega)
        have hs := hi.trans (Nat.mul_le_mul_right _ (Nat.sub_le k i))
        have hp := (ordered_sol S).pos i
        omega⟩,
      ⟨middleProduct (ordered S) p - 1, by
        have hs := (ordered_sol S).middle_spec
        change middleProduct (ordered S) p - 1 < 12 * u p ^ 2
        omega⟩,
      optionRank _ J (hmiddle S) _ (ordered_sol S).middle_spec.2.2.1,
      rankCode _ L (hfinal S) ⟨_, (ordered_sol S).final_code_mem⟩⟩
  have hinj : Function.Injective code := by
    intro S T he
    let a := ordered S
    let b := ordered T
    have ha : Sol (p + 4) a := ordered_sol S
    have hb : Sol (p + 4) b := ordered_sol T
    have hp : ∀ i < p, a i = b i := by
      intro i hi
      have ht := congrArg (fun x : Code => (x.1 ⟨i, hi⟩).val) he
      change a i - 1 = b i - 1 at ht
      have hpa := ha.pos i
      have hpb := hb.pos i
      omega
    have hx : middleProduct a p = middleProduct b p := by
      have ht := congrArg (fun x : Code => x.2.1.val) he
      change middleProduct a p - 1 = middleProduct b p - 1 at ht
      have hpa := ha.middle_spec.1
      have hpb := hb.middle_spec.1
      omega
    have hy : middleDifference a p = middleDifference b p := by
      refine optionRank_cancel (hmiddle S) (hmiddle T) ha.middle_spec.2.2.1
        hb.middle_spec.2.2.1 (congrArg Nat.divisors hx) ?_
      exact congrArg (fun x : Code => x.2.2.1) he
    obtain ⟨hmp, hmp1⟩ := middle_cancel ha hb hp hx hy
    have hp' : ∀ i < p + 2, a i = b i := by
      intro i hi
      by_cases hlt : i < p
      · exact hp i hlt
      · rcases (show i = p ∨ i = p + 1 by omega) with rfl | rfl
        · exact hmp
        · exact hmp1
    have hz : (finalFactor a (p + 2)).toNat = (finalFactor b (p + 2)).toNat := by
      exact rankCode_cancel (hfinal S) (hfinal T)
        (x := ⟨_, ha.final_code_mem⟩) (y := ⟨_, hb.final_code_mem⟩)
        (congrArg (fun n : ℕ => (n ^ 2).divisors) (denominator_congr hp'))
        (congrArg (fun x : Code => x.2.2.2) he)
    exact ordered_ext (final_cancel ha hb hp' hz)
  have hcard := Nat.card_le_card_of_injective code hinj
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hcard
  change Erdos148.F (p + 4) ≤ _ at hcard
  dsimp [Code] at hcard
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin] at hcard
  rw [Fin.prod_univ_eq_prod_range (fun i => k * u i) p] at hcard
  have hpre := prefix_box_product k p
  calc
    Erdos148.F (p + 4) ≤ (∏ i ∈ range p, k * u i) * (B * ((J + 1) * L)) := hcard
    _ ≤ (k ^ p * U) * (B * ((J + 1) * L)) := Nat.mul_le_mul_right _ hpre
    _ = _ := by dsimp [k, U, B, J, L, D]; ring

private noncomputable def countConstant (C : ℝ) : ℝ :=
  log 2 + (101 / 100) * log 12 + 2 * log C + (1 / 50) * log 48

private lemma log_count_bound (p : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hdiv : ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 100 : ℝ))
    (hf : 0 < Erdos148.F (p + 4)) :
    log (Erdos148.F (p + 4)) ≤
      countConstant C + (51 / 50) * p * log ((p + 4 : ℕ) : ℝ) + (31 / 10) * log (u p) := by
  let k : ℝ := (p + 4 : ℕ)
  let U : ℝ := u p
  have hk : 0 < k := by dsimp [k]; positivity
  have hu : 0 < U := by dsimp [U]; exact_mod_cast u_pos p
  have hu1 : 1 ≤ U := by dsimp [U]; exact_mod_cast (show 1 ≤ u p from u_pos p)
  have hc : 0 < C := by linarith
  have hb : 0 < 12 * U ^ 2 := by positivity
  have hd : 0 < 48 * k ^ p * U ^ 4 := by positivity
  have hb1 : 1 ≤ 12 * U ^ 2 := by
    have h := one_le_pow₀ hu1 (n := 2)
    linarith
  let B := 12 * U ^ 2
  let D := 48 * k ^ p * U ^ 4
  have hpow : 1 ≤ B ^ (1 / 100 : ℝ) := Real.one_le_rpow hb1 (by norm_num)
  have hm : 1 ≤ C * B ^ (1 / 100 : ℝ) := one_le_mul_of_one_le_of_one_le hC hpow
  have hfloor1 : (↑(⌊C * B ^ (1 / 100 : ℝ)⌋₊ + 1) : ℝ) ≤
      2 * C * B ^ (1 / 100 : ℝ) := by
    push_cast
    have hflo := Nat.floor_le (show 0 ≤ C * B ^ (1 / 100 : ℝ) by
      exact mul_nonneg hc.le (Real.rpow_nonneg hb.le _))
    linarith
  have hfloor2 : (↑⌊C * (D ^ (2 : ℕ)) ^ (1 / 100 : ℝ)⌋₊ : ℝ) ≤
      C * (D ^ (2 : ℕ)) ^ (1 / 100 : ℝ) := by
    exact Nat.floor_le (mul_nonneg hc.le (Real.rpow_nonneg (pow_nonneg hd.le _) _))
  have hn := count_bound p (1 / 100 : ℝ) C (by norm_num) hdiv hC
  have hcst : (Erdos148.F (p + 4) : ℝ) ≤
      (k ^ p * U) * B * (↑(⌊C * B ^ (1 / 100 : ℝ)⌋₊ + 1) : ℝ) *
        (↑⌊C * (D ^ (2 : ℕ)) ^ (1 / 100 : ℝ)⌋₊ : ℝ) := by
    have hh := (Nat.cast_le (α := ℝ)).mpr hn
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, k, U, B, D] using hh
  have hreal : (Erdos148.F (p + 4) : ℝ) ≤
      (k ^ p * U) * B * (2 * C * B ^ (1 / 100 : ℝ)) *
        (C * (D ^ (2 : ℕ)) ^ (1 / 100 : ℝ)) := by
    refine hcst.trans ?_
    gcongr
  have hlog := Real.log_le_log (by exact_mod_cast hf) hreal
  have hcalc :
      log ((k ^ p * U) * B * (2 * C * B ^ (1 / 100 : ℝ)) *
        (C * (D ^ (2 : ℕ)) ^ (1 / 100 : ℝ))) =
        countConstant C + (51 / 50) * p * log k + (31 / 10) * log U := by
    unfold countConstant B D
    simp (disch := positivity) only [Real.log_mul, Real.log_pow, Real.log_rpow]
    ring
  rwa [hcalc] at hlog

private lemma log_prefactor_eventually (A t : ℝ) (ht : 0 < t) :
    ∀ᶠ p : ℕ in atTop,
      A + (51 / 50) * p * log ((p + 4 : ℕ) : ℝ) ≤ t * (2 : ℝ) ^ p := by
  have ho : (fun p : ℕ => (p : ℝ) ^ (2 : ℕ)) =o[atTop] (fun p : ℕ => (2 : ℝ) ^ p) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2
      (b := log 2) (Real.log_pos (by norm_num))).comp_tendsto tendsto_natCast_atTop_atTop
    change (fun p : ℕ => (p : ℝ) ^ (2 : ℕ)) =o[atTop]
      (fun p : ℕ => exp (log 2 * (p : ℝ))) at h
    simpa only [mul_comm (log 2), Real.exp_nat_mul, Real.exp_log
      (by norm_num : (0 : ℝ) < 2)] using h
  let S := |A| + 10
  have hS : 0 < S := by dsimp [S]; positivity
  filter_upwards [ho.bound (div_pos ht hS), eventually_ge_atTop (1 : ℕ)] with p hp hp1
  have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hp2 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := one_le_pow₀ hp1'
  have hlog : log ((p + 4 : ℕ) : ℝ) ≤ 4 * p := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ((p + 4 : ℕ) : ℝ) by positivity)
    push_cast at h ⊢
    linarith
  have hA : A ≤ |A| * (p : ℝ) ^ 2 :=
    (le_abs_self A).trans (le_mul_of_one_le_right (abs_nonneg _) hp2)
  have hl := mul_le_mul_of_nonneg_left hlog hp0
  have hp' : (p : ℝ) ^ 2 ≤ (t / S) * (2 : ℝ) ^ p := by
    simpa only [Real.norm_of_nonneg (pow_nonneg hp0 _),
      Real.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)] using hp
  calc
    _ ≤ S * (p : ℝ) ^ 2 := by dsimp [S]; nlinarith only [hA, hl, sq_nonneg (p : ℝ)]
    _ ≤ S * ((t / S) * (2 : ℝ) ^ p) := mul_le_mul_of_nonneg_left hp' hS.le
    _ = _ := by field_simp

private lemma eventual_exact_upper :
    ∀ᶠ k : ℕ in atTop, (Erdos148.F k : ℝ) ≤ c₀ ^ ((1 / 5 : ℝ) * 2 ^ k) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_bound (1 / 100 : ℝ) (by norm_num)
  have hln : 0 < log c₀ := Real.log_pos one_lt_c₀
  have hc : 0 < c₀ := by linarith only [one_lt_c₀]
  have hlarge := log_prefactor_eventually (countConstant C) (log c₀ / 10) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  refine eventually_atTop.mpr ⟨N + 4, ?_⟩
  intro k hk
  let p := k - 4
  have hpk : p + 4 = k := by dsimp [p]; omega
  have hNp : N ≤ p := by dsimp [p]; omega
  rw [← hpk]
  by_cases hz : Erdos148.F (p + 4) = 0
  · rw [hz]
    simpa only [Nat.cast_zero] using
      (Real.rpow_nonneg hc.le ((1 / 5 : ℝ) * 2 ^ (p + 4)))
  have hf := Nat.pos_of_ne_zero hz
  have hlog := log_count_bound p C hC hdiv hf
  have hU : log (u p : ℝ) ≤ (2 : ℝ) ^ p * log c₀ := by
    have h := Real.log_le_log (by exact_mod_cast u_pos p) (u_le_c₀ p)
    simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] using h
  apply (Real.log_le_log_iff (by exact_mod_cast hf) (Real.rpow_pos_of_pos hc _)).mp
  rw [Real.log_rpow hc, pow_add]
  norm_num only [show (2 : ℝ) ^ (4 : ℕ) = 16 by norm_num]
  have htail := hN p hNp
  calc
    _ ≤ countConstant C + (51 / 50) * p * log ((p + 4 : ℕ) : ℝ)
       + (31 / 10) * log (u p) := hlog
    _ ≤ (log c₀ / 10) * (2 : ℝ) ^ p + (31 / 10) * ((2 : ℝ) ^ p * log c₀) :=
      add_le_add htail (mul_le_mul_of_nonneg_left hU (by norm_num))
    _ = _ := by ring

end EgyptianCounting

theorem OMA.solution : type_of% @Erdos148.erdos_148.variants.upper_bound := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact Asymptotics.isLittleO_zero _ _
  · simpa only [add_zero] using EgyptianCounting.eventual_exact_upper
