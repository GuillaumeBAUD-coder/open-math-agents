import OMAReductions.R_Erdos239_erdos_239_R1

-- Step Erdos239.erdos_239.R1.H1: hypothesis H1 of reduction Erdos239.erdos_239.R1
-- Credit: @anmolspace
-- Proof: g = mu * f (Moebius inversion); |g|/n is multiplicative, and its Euler factors are
-- bounded by 1 + (1 - f p)/p + 16/p^2, so the partial sums are bounded by exp of a convergent series.

namespace OMA.S239

open Finset

noncomputable def FF (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

noncomputable def GG (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * FF f

noncomputable def hh (f : ℕ → ℝ) (n : ℕ) : ℝ := |GG f n| / n

lemma FF_apply (f : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) : FF f n = f n := if_neg hn

lemma FF_mult (f : ℕ → ℝ) (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1) :
    (FF f).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [FF_apply f 1 one_ne_zero, h1], ?_⟩
  intro m n hm hn hmn
  rw [FF_apply f _ (mul_ne_zero hm hn), FF_apply f m hm, FF_apply f n hn, hmul m n hmn]

lemma GG_mult (f : ℕ → ℝ) (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1) :
    (GG f).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.mul (FF_mult f hmul h1)

lemma GG_sum (f : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) : ∑ i ∈ n.divisors, GG f i = f n := by
  have hGz : GG f * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
      = FF f := by
    unfold GG
    rw [mul_comm ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
      (FF f), mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  rw [← ArithmeticFunction.coe_mul_zeta_apply, hGz, FF_apply f n hn]

lemma GG_pp (f : ℕ → ℝ) (p : ℕ) (hp : p.Prime) (k : ℕ) :
    GG f (p ^ (k+1)) = f (p ^ (k+1)) - f (p ^ k) := by
  have e1 := GG_sum f (p ^ (k+1)) (pow_ne_zero _ hp.ne_zero)
  have e0 := GG_sum f (p ^ k) (pow_ne_zero _ hp.ne_zero)
  rw [Nat.sum_divisors_prime_pow hp] at e1 e0
  rw [Finset.sum_range_succ] at e1
  linarith

lemma hh_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ hh f n := by
  unfold hh; positivity

lemma hh_zero (f : ℕ → ℝ) : hh f 0 = 0 := by
  unfold hh; simp

lemma hh_one (f : ℕ → ℝ) (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1) :
    hh f 1 = 1 := by
  unfold hh; rw [(GG_mult f hmul h1).map_one]; simp

lemma hh_mul (f : ℕ → ℝ) (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1)
    {m n : ℕ} (hmn : m.Coprime n) : hh f (m * n) = hh f m * hh f n := by
  unfold hh
  rw [(GG_mult f hmul h1).map_mul_of_coprime hmn, abs_mul, Nat.cast_mul, mul_div_mul_comm]

lemma GG_pp_le (f : ℕ → ℝ) (hf : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1)
    (p : ℕ) (hp : p.Prime) (k : ℕ) : |GG f (p ^ k)| ≤ 2 := by
  rcases k with _ | k
  · rw [pow_zero, (GG_mult f hmul h1).map_one]; norm_num
  · rw [GG_pp f p hp k]
    have ha := hf (p ^ (k+1)) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero))
    have hb := hf (p ^ k) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero))
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> norm_num

lemma hh_pp_le (f : ℕ → ℝ) (hf : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1)
    (p : ℕ) (hp : p.Prime) (k : ℕ) : hh f (p ^ k) ≤ 2 / (p : ℝ) ^ k := by
  unfold hh
  rw [Nat.cast_pow]
  have hpos : (0 : ℝ) < (p : ℝ) ^ k := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  exact div_le_div_of_nonneg_right (GG_pp_le f hf hmul h1 p hp k) hpos.le

lemma hh_pp_geom (f : ℕ → ℝ) (hf : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1)
    (p : ℕ) (hp : p.Prime) (k : ℕ) : hh f (p ^ k) ≤ 2 * (1 / 2 : ℝ) ^ k := by
  refine le_trans (hh_pp_le f hf hmul h1 p hp k) ?_
  rw [one_div_pow, mul_one_div]
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  gcongr

lemma hh_summable_pp (f : ℕ → ℝ) (hf : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1)
    (p : ℕ) (hp : p.Prime) : Summable (fun k : ℕ => hh f (p ^ k)) :=
  Summable.of_nonneg_of_le (fun k => hh_nonneg f _) (hh_pp_geom f hf hmul h1 p hp)
    (summable_geometric_two.mul_left 2)

lemma hh_tsum_pp (f : ℕ → ℝ) (hf : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1)
    (p : ℕ) (hp : p.Prime) :
    ∑' k : ℕ, hh f (p ^ k) ≤ 1 + ((1 - f p) / p + 16 / (p : ℝ) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hfp : f p = 1 ∨ f p = -1 := hf p hp.one_lt.le
  let b : ℕ → ℝ := fun k => (if k = 0 then 1 else 0) + (if k = 1 then (1 - f p) / p else 0)
    + 8 / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k
  have hb : HasSum b (1 + (1 - f p) / p + 8 / (p : ℝ) ^ 2 * 2) :=
    ((hasSum_ite_eq 0 (1 : ℝ)).add (hasSum_ite_eq 1 ((1 - f p) / p))).add
      (hasSum_geometric_two.mul_left _)
  have hle : ∀ k, hh f (p ^ k) ≤ b k := by
    intro k
    have hc : 0 ≤ 8 / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k := by positivity
    rcases k with _ | _ | k
    · show hh f (p ^ 0) ≤ (if 0 = 0 then 1 else 0) + (if 0 = 1 then (1 - f p) / p else 0)
        + 8 / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 0
      rw [if_pos rfl, if_neg (by norm_num), pow_zero, hh_one f hmul h1]
      rw [pow_zero] at hc
      linarith
    · show hh f (p ^ (0+1)) ≤ (if 0 + 1 = 0 then 1 else 0)
        + (if 0 + 1 = 1 then (1 - f p) / p else 0) + 8 / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (0+1)
      rw [if_neg (by norm_num), if_pos rfl]
      have e : hh f (p ^ (0+1)) = (1 - f p) / p := by
        unfold hh
        rw [GG_pp f p hp 0]
        simp only [zero_add, pow_one, pow_zero, h1, Nat.cast_pow]
        congr 1
        rcases hfp with h | h <;> rw [h] <;> norm_num
      rw [e]
      linarith
    · show hh f (p ^ (k+1+1)) ≤ (if k + 1 + 1 = 0 then 1 else 0)
        + (if k + 1 + 1 = 1 then (1 - f p) / p else 0) + 8 / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k+1+1)
      rw [if_neg (by omega), if_neg (by omega), zero_add, zero_add]
      calc hh f (p ^ (k+1+1)) ≤ 2 / (p : ℝ) ^ (k+1+1) := hh_pp_le f hf hmul h1 p hp _
        _ = 2 / ((p : ℝ) ^ 2 * (p : ℝ) ^ k) := by ring
        _ ≤ 2 / ((p : ℝ) ^ 2 * 2 ^ k) := by gcongr
        _ = 8 / (p : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (k+1+1) := by
          rw [one_div_pow, pow_succ, pow_succ]
          field_simp
          ring
  have := hasSum_le hle (hh_summable_pp f hf hmul h1 p hp).hasSum hb
  have e16 : 8 / (p : ℝ) ^ 2 * 2 = 16 / (p : ℝ) ^ 2 := by ring
  linarith

lemma hh_partial (f : ℕ → ℝ) (hf : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1) (N : ℕ) :
    ∑ m ∈ range N, hh f m ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, hh f (p ^ k) := by
  classical
  have HS := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := hh f) (hh_one f hmul h1) (fun {m n} hmn => hh_mul f hmul h1 hmn)
    (fun {p} hp => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hh_nonneg f _)]
        using hh_summable_pp f hf hmul h1 p hp) N).2
  have key := sum_le_hasSum ((range N).subtype (· ∈ N.smoothNumbers))
    (fun i _ => hh_nonneg f i) HS
  have e : ∑ m ∈ range N, hh f m
      = ∑ i ∈ (range N).subtype (· ∈ N.smoothNumbers), hh f i := by
    rw [Finset.sum_subtype_eq_sum_filter, Finset.sum_filter_of_ne]
    intro x hx hne
    apply Nat.mem_smoothNumbers_of_lt _ (Finset.mem_range.mp hx)
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · exact absurd (by rw [h0]; exact hh_zero f) hne
    · exact h0
  rw [e]
  exact key

theorem main (f : ℕ → ℝ) (hf : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1)
    (hsum : Summable (fun p : Nat.Primes => (1 - f p) / (p.val : ℝ))) :
    ∃ g : ℕ → ℝ, Summable (fun d : ℕ => |g d| / d) ∧
      ∀ n ≥ 1, f n = ∑ d ∈ n.divisors, g d := by
  classical
  let A1 : ℕ → ℝ := fun n => if n.Prime then (1 - f n) / n else 0
  let A2 : ℕ → ℝ := fun n => if n.Prime then 16 / (n : ℝ) ^ 2 else 0
  have hA1 : Summable A1 := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
    refine (hinj.summable_iff ?_).mp ?_
    · intro x hx
      show (if x.Prime then (1 - f x) / x else 0) = 0
      rw [if_neg]
      intro hp
      exact hx ⟨⟨x, hp⟩, rfl⟩
    · refine hsum.congr (fun p => ?_)
      show (1 - f p) / (p.val : ℝ) = (if (p : ℕ).Prime then (1 - f p) / ((p : ℕ) : ℝ) else 0)
      exact (if_pos p.2).symm
  have hA2 : Summable A2 := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((Real.summable_nat_pow_inv.mpr one_lt_two).mul_left 16)
    · show 0 ≤ (if n.Prime then 16 / (n : ℝ) ^ 2 else 0)
      split_ifs <;> positivity
    · show (if n.Prime then 16 / (n : ℝ) ^ 2 else 0) ≤ 16 * ((n : ℝ) ^ 2)⁻¹
      split_ifs
      · rw [div_eq_mul_inv]
      · positivity
  have hA1n : ∀ n, 0 ≤ A1 n := by
    intro n
    show 0 ≤ (if n.Prime then (1 - f n) / n else 0)
    split_ifs with hn
    · have : f n ≤ 1 := by rcases hf n hn.one_lt.le with h | h <;> rw [h] <;> norm_num
      have : (0 : ℝ) ≤ 1 - f n := by linarith
      positivity
    · exact le_refl 0
  have hA2n : ∀ n, 0 ≤ A2 n := by
    intro n
    show 0 ≤ (if n.Prime then 16 / (n : ℝ) ^ 2 else 0)
    split_ifs <;> positivity
  let C : ℝ := Real.exp (∑' n, (A1 n + A2 n))
  have hS : Summable (hh f) := by
    refine summable_of_sum_range_le (c := C) (hh_nonneg f) (fun N => ?_)
    refine le_trans (hh_partial f hf hmul h1 N) ?_
    have pt : ∀ p ∈ N.primesBelow, ∑' k : ℕ, hh f (p ^ k) ≤ Real.exp (A1 p + A2 p) := by
        intro p hp
        have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
        have e1 : A1 p = (1 - f p) / p := if_pos hpp
        have e2 : A2 p = 16 / (p : ℝ) ^ 2 := if_pos hpp
        rw [e1, e2]
        refine le_trans (hh_tsum_pp f hf hmul h1 p hpp) ?_
        have := Real.add_one_le_exp ((1 - f p) / p + 16 / (p : ℝ) ^ 2)
        linarith
    have step1 : ∏ p ∈ N.primesBelow, ∑' k : ℕ, hh f (p ^ k)
        ≤ ∏ p ∈ N.primesBelow, Real.exp (A1 p + A2 p) := by
      gcongr with p hp
      all_goals first
        | exact tsum_nonneg (fun k => hh_nonneg f _)
        | (apply pt; assumption)
        | (intro i _; exact tsum_nonneg (fun k => hh_nonneg f _))
    refine le_trans step1 ?_
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    exact sum_le_hasSum _ (fun i _ => add_nonneg (hA1n i) (hA2n i)) (hA1.add hA2).hasSum
  refine ⟨GG f, hS, ?_⟩
  intro n hn
  exact (GG_sum f n (Nat.one_le_iff_ne_zero.mp hn)).symm

end OMA.S239

theorem OMA.solution : OMA.R_Erdos239_erdos_239_R1.H1 := by
  intro f hf hmul h1 hsum
  exact OMA.S239.main f hf hmul h1 hsum
