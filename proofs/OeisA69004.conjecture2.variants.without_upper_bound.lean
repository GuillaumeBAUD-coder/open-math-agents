import FormalConjectures.OEIS.«69004»
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

-- Credit: @Burntgogi

/-!
# Small products over primes congruent to three modulo four

The finite product of the surviving proportions can be made arbitrarily small.
We first prove divergence of the prime reciprocal sum in any invertible residue class,
using the pole bound for the von Mangoldt L-series in Mathlib.
-/

namespace A069004

open ArithmeticFunction Filter
open ArithmeticFunction.vonMangoldt
open scoped Topology

private lemma scaled_log_div_le {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 1 < x) :
    (x - 1) * (Real.log n / (n : ℝ) ^ x) ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
    rw [← Real.rpow_add_one hn'.ne', sub_add_cancel]
  have hlog := (le_div_iff₀' (sub_pos.mpr hx)).mp
    (Real.log_natCast_le_rpow_div n (sub_pos.mpr hx))
  rw [← mul_div_assoc, div_le_div_iff₀ (Real.rpow_pos_of_pos hn' _) hn', one_mul, hpow]
  exact mul_le_mul_of_nonneg_right hlog hn'.le

/-- The sum of reciprocal primes in any invertible residue class diverges. -/
theorem not_summable_prime_reciprocal {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ¬ Summable (fun n : ℕ ↦ if n.Prime ∧ (n : ZMod q) = a then 1 / (n : ℝ) else 0) := by
  classical
  intro h
  let f (x : ℝ) (n : ℕ) := (x - 1) * (residueClass a n / (n : ℝ) ^ x)
  have hpoint (n : ℕ) : Tendsto (fun x ↦ f x n) (𝓝[>] 1) (𝓝 0) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [f]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hcont : ContinuousAt (fun x ↦ f x n) 1 :=
      (continuousAt_id.sub continuousAt_const).mul
        (continuousAt_const.div (Real.continuousAt_const_rpow hn'.ne')
          (Real.rpow_pos_of_pos hn' _).ne')
    simpa [f] using hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  -- A summable majorant consists of the prime reciprocals and the higher prime powers.
  have hsum := h.add (summable_residueClass_non_primes_div a)
  have hdom : ∀ᶠ x in 𝓝[>] (1 : ℝ), ∀ n : ℕ, ‖f x n‖ ≤
      (if n.Prime ∧ (n : ZMod q) = a then 1 / (n : ℝ) else 0) +
        (if n.Prime then 0 else residueClass a n) / n := by
    filter_upwards [Ioc_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with x hx n
    have hpos := sub_pos.mpr hx.1
    have hf : 0 ≤ f x n := mul_nonneg hpos.le
      (div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg n.cast_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hf]
    by_cases hp : n.Prime
    · by_cases ha' : (n : ZMod q) = a
      · simpa [f, residueClass, hp, ha', vonMangoldt_apply_prime hp] using
          scaled_log_div_le hp.pos hx.1
      · simp [f, residueClass, hp, ha']
    · simp only [hp, false_and, if_false, zero_add]
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [f]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hpow : (n : ℝ) ≤ (n : ℝ) ^ x := by
        simpa using Real.rpow_le_rpow_of_exponent_le (x := (n : ℝ))
          (by exact_mod_cast hn) hx.1.le
      calc
        f x n ≤ 1 * (residueClass a n / (n : ℝ) ^ x) := by
          exact mul_le_mul_of_nonneg_right (by linarith [hx.2])
            (div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg n.cast_nonneg _))
        _ ≤ _ := by
          rw [one_mul]
          exact div_le_div_of_nonneg_left (residueClass_nonneg a n) hn' hpow
  have hzero : Tendsto (fun x ↦ ∑' n, f x n) (𝓝[>] 1) (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hsum hpoint hdom
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound ha
  have hlin : Tendsto (fun x : ℝ ↦ (x - 1) * C) (𝓝[>] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ (x - 1) * C) 1 := by fun_prop
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hpole : (q.totient : ℝ)⁻¹ ≤ 0 + 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (hzero.add hlin)
    filter_upwards [Ioc_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with x hx
    have hineq := (div_le_iff₀ (sub_pos.mpr hx.1)).mp (sub_le_iff_le_add.mp (hC hx))
    change (q.totient : ℝ)⁻¹ ≤ (∑' n, (x - 1) * (residueClass a n / (n : ℝ) ^ x)) + (x - 1) * C
    rw [tsum_mul_left]
    linarith only [hineq]
  have hq : 0 < (q.totient : ℝ)⁻¹ := inv_pos.mpr (mod_cast q.totient.pos_of_neZero)
  linarith

/-- The products over all primes below a cutoff in an invertible residue class tend to zero. -/
theorem tendsto_prime_product {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ (Finset.range N).filter (fun p : ℕ ↦ p.Prime ∧ (p : ZMod q) = a),
      (1 - 1 / (p : ℝ))) atTop (𝓝 0) := by
  classical
  let S (N : ℕ) := (Finset.range N).filter (fun p : ℕ ↦ p.Prime ∧ (p : ZMod q) = a)
  have hsum : Tendsto (fun N ↦ ∑ p ∈ S N, 1 / (p : ℝ)) atTop atTop := by
    simp only [S, Finset.sum_filter]
    apply (not_summable_iff_tendsto_nat_atTop_of_nonneg _).mp (not_summable_prime_reciprocal ha)
    intro n
    split <;> positivity
  have hfactor {N p : ℕ} (hp : p ∈ S N) : 0 ≤ 1 - 1 / (p : ℝ) := by
    have hprime := (Finset.mem_filter.mp hp).2.1
    exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast hprime.pos)).mpr
      (by exact_mod_cast hprime.one_lt.le))
  apply squeeze_zero (fun N ↦ Finset.prod_nonneg fun p hp ↦ hfactor hp)
    (fun N ↦ ?_) (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsum))
  change (∏ p ∈ S N, (1 - 1 / (p : ℝ))) ≤ Real.exp (-(∑ p ∈ S N, 1 / (p : ℝ)))
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod (fun p hp ↦ hfactor hp)
  intro p _
  linarith [Real.add_one_le_exp (-(1 / (p : ℝ)))]

/-- For each positive ε some finite set of distinct primes congruent to three modulo four
has product of the factors `1 - 1 / p` less than ε. -/
theorem exists_inert_prime_product_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 4 = 3) ∧
      (∏ p ∈ S, (1 - 1 / (p : ℝ))) < ε := by
  have ha : IsUnit ((3 : ℕ) : ZMod 4) := (ZMod.isUnit_iff_coprime 3 4).2 (by decide)
  obtain ⟨N, hN⟩ := ((tendsto_prime_product ha).eventually_lt_const hε).exists
  refine ⟨_, ?_, hN⟩
  intro p hp
  obtain ⟨_, hprime, heq⟩ := Finset.mem_filter.mp hp
  exact ⟨hprime, (ZMod.natCast_eq_natCast_iff' p 3 4).mp heq⟩

end A069004

/- Explicit bounds that turn a finite sieve certificate into the required refutation. -/

open Real

namespace A069004Certificate

theorem primeCounting_mul_log_lower {n : ℕ} (hn : 512 ≤ n) :
    (3 / 8 : ℝ) * n ≤ (n.primeCounting : ℝ) * log n := by
  have hn' : (512 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / 32 by positivity)
  rw [Real.log_div hpos.ne' (by norm_num)] at hlog
  have hc := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 32 by norm_num)
  have herr : log ((n : ℝ) + 1) ≤ n / 8 := by linarith
  have htwo : (1 / 2 : ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
  have h := (Chebyshev.psi_ge n).trans (Chebyshev.psi_le_primeCounting_mul_log n)
  nlinarith [mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α := ℝ) n)]

theorem violates_of_log_bound {n : ℕ} (hn : 512 ≤ n)
    (h : 20 * (OeisA69004.a n : ℝ) * log n ≤ n) :
    5 * OeisA69004.a n < n.primeCounting := by
  have hn' : (512 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < log (n : ℝ) := Real.log_pos (by linarith)
  have hπ := primeCounting_mul_log_lower hn
  by_contra! hrev
  have hrev' : (n.primeCounting : ℝ) ≤ 5 * (OeisA69004.a n : ℝ) := by exact_mod_cast hrev
  have := mul_le_mul_of_nonneg_right hrev' hlog.le
  linarith

theorem disproof_of_sieve_estimates {n : ℕ} {G E : ℝ} (hn : 512 ≤ n)
    (hsieve : (OeisA69004.a n : ℝ) ≤ n / G + E)
    (hmass : 100 * log n ≤ G) (hrem : E * log n ≤ n / 100) :
    ¬ (type_of% @OeisA69004.conjecture2.variants.without_upper_bound) := by
  have hn' : (512 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < log (n : ℝ) := Real.log_pos (by linarith)
  have hG : 0 < G := by linarith
  have hscale : (n : ℝ) / G * log n ≤ n / 100 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hG (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (α := ℝ) n)]
  have hcount := mul_le_mul_of_nonneg_right hsieve hlog.le
  have hbad := violates_of_log_bound hn (by nlinarith)
  intro h
  exact (Nat.not_le_of_lt hbad) (h.1 n (by omega))

theorem disproof_of_scaled_mass {M Y : ℕ} {G : ℝ} (hM : 1 ≤ M) (hMY : M ≤ Y)
    (hY : 1700 ≤ Y) (hmass : 1700 * log Y ≤ G)
    (hsieve : (OeisA69004.a (M*Y^16) : ℝ) ≤
      (M*Y^16 : ℕ) / G + ((M*Y : ℕ) : ℝ)^6) :
    ¬ (type_of% @OeisA69004.conjecture2.variants.without_upper_bound) := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hYr : (1700 : ℝ) ≤ Y := by exact_mod_cast hY
  have hMYr : (M : ℝ) ≤ Y := by exact_mod_cast hMY
  have hypos : (0 : ℝ) < Y := by linarith
  have hmpos : (0 : ℝ) < M := by linarith
  have hlog : log (M*Y^16 : ℕ) ≤ 17 * log Y := by
    push_cast
    rw [Real.log_mul hmpos.ne' (pow_pos hypos _).ne', Real.log_pow]
    norm_num
    linarith [Real.log_le_log hmpos hMYr]
  have hy1 : 1 ≤ Y := by omega
  have hN : 512 ≤ M*Y^16 := calc
    512 ≤ Y := by omega
    _ ≤ Y^16 := by simpa using (Nat.pow_le_pow_right hy1 (show 1 ≤ 16 by decide))
    _ ≤ M*Y^16 := Nat.le_mul_of_pos_left _ hM
  apply disproof_of_sieve_estimates hN hsieve (by linarith)
  push_cast at hlog ⊢
  have hE : ((M:ℝ)*Y)^6 ≤ (Y:ℝ)^12 := by
    calc
      _ ≤ ((Y:ℝ)*Y)^6 := by gcongr
      _ = _ := by ring
  have hlog' : log ((M:ℝ)*Y^16) ≤ 17 * Y := by
    linarith [Real.log_le_sub_one_of_pos hypos]
  have hp13 : 0 ≤ (Y:ℝ)^13 := by positivity
  have hp : 1700 * (Y:ℝ)^13 ≤ (Y:ℝ)^14 := by
    nlinarith [mul_le_mul_of_nonneg_right hYr hp13]
  have hp' : (Y:ℝ)^14 ≤ (Y:ℝ)^16 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hn' : (Y:ℝ)^16 ≤ M*(Y:ℝ)^16 := by
    simpa using mul_le_mul_of_nonneg_right hMr (show 0 ≤ (Y:ℝ)^16 by positivity)
  have hcombined := mul_le_mul hE hlog' (Real.log_nonneg (by exact_mod_cast (show 1 ≤ M*Y^16 by omega)))
    (show 0 ≤ (Y:ℝ)^12 by positivity)
  nlinarith

end A069004Certificate

/-
# A finite upper-bound sieve for OEIS A069004

The polynomial is `n ^ 2 + s ^ 2`. The bounds use `OeisA69004.a` from the problem module.
The sieve bounds the number of prime values in the interval.
-/

namespace A069004Sieve

open Finset
open OeisA69004 (a)
open scoped Count

/-- Number of roots in a complete residue system modulo `d`. -/
def rootCount (n d : ℕ) : ℕ :=
  Nat.count (fun s => d ∣ n ^ 2 + s ^ 2) d

theorem rootCount_eq_card (n d : ℕ) [NeZero d] :
    rootCount n d = Fintype.card {x : ZMod d // (n : ZMod d) ^ 2 + x ^ 2 = 0} := by
  rw [rootCount, Nat.count_eq_card_fintype]
  apply Fintype.card_congr
  exact
    { toFun := fun ⟨s, hs, h⟩ => ⟨s, by
        simpa using (ZMod.natCast_eq_zero_iff _ _).mpr h⟩
      invFun := fun ⟨x, hx⟩ => ⟨x.val, x.val_lt, (ZMod.natCast_eq_zero_iff _ _).mp (by
        simpa using hx)⟩
      left_inv := fun ⟨s, hs, _⟩ => Subtype.ext (ZMod.val_natCast_of_lt hs)
      right_inv := fun ⟨x, _⟩ => Subtype.ext (ZMod.natCast_zmod_val x) }

/-- Chinese remaindering makes the root count multiplicative. -/
theorem rootCount_mul (n : ℕ) {d e : ℕ} (hc : d.Coprime e) :
    rootCount n (d * e) = rootCount n d * rootCount n e := by
  by_cases hd : d = 0
  · simp [hd, rootCount]
  by_cases he : e = 0
  · simp [he, rootCount]
  let : NeZero d := ⟨hd⟩
  let : NeZero e := ⟨he⟩
  rw [rootCount_eq_card, rootCount_eq_card, rootCount_eq_card, ← Fintype.card_prod]
  let E := ZMod.chineseRemainder hc
  apply Fintype.card_congr
  refine (E.toEquiv.subtypeEquiv (q := fun x =>
    ((n : ZMod d) ^ 2 + x.1 ^ 2 = 0) ∧ ((n : ZMod e) ^ 2 + x.2 ^ 2 = 0)) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun x : ZMod d => (n : ZMod d)^2 + x^2 = 0)
      (q := fun y : ZMod e => (n : ZMod e)^2 + y^2 = 0))
  intro x
  rw [← E.injective.eq_iff]
  simp [Prod.ext_iff]

@[simp] theorem rootCount_one (n : ℕ) : rootCount n 1 = 1 := by
  simp [rootCount, Nat.count_one]

theorem rootCount_le (n d : ℕ) : rootCount n d ≤ d := Nat.count_le _

theorem rootCount_two (n : ℕ) : rootCount n 2 = 1 := by
  rw [rootCount_eq_card]
  change Fintype.card {x : ZMod 2 // (n : ZMod 2) ^ 2 + x ^ 2 = 0} = 1
  generalize (n : ZMod 2) = t
  fin_cases t <;> decide

/-- At an odd prime there is one root if the prime divides `n`. Otherwise
there are two roots in the class `1 mod 4` and none in the class `3 mod 4`. -/
theorem rootCount_prime (n : ℕ) {p : ℕ} (hp : p.Prime) :
    rootCount n p = if p = 2 ∨ p ∣ n then 1 else if p % 4 = 1 then 2 else 0 := by
  by_cases h₂ : p = 2
  · subst p
    simp [rootCount_two]
  let : Fact p.Prime := ⟨hp⟩
  have hs := legendreSym.card_sqrts p h₂ (-((n : ℤ) ^ 2))
  have hcard : rootCount n p =
      {x : ZMod p | x ^ 2 = ((-((n : ℤ)^2) : ℤ) : ZMod p)}.toFinset.card := by
    rw [rootCount_eq_card]
    apply Fintype.card_of_subtype
    intro x
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq, Int.cast_neg, Int.cast_pow, Int.cast_natCast]
    constructor <;> intro h <;> linear_combination h
  rw [← hcard, legendreSym.at_neg h₂] at hs
  by_cases hdiv : p ∣ n
  · have hn0 : (((n : ℤ) ^ 2 : ℤ) : ZMod p) = 0 := by
      simp [(ZMod.natCast_eq_zero_iff _ _).mpr hdiv]
    rw [(legendreSym.eq_zero_iff p _).mpr hn0, mul_zero, zero_add] at hs
    simp [h₂, hdiv]
    exact_mod_cast hs
  · have hn : ((n : ℤ) : ZMod p) ≠ 0 := by simpa [ZMod.natCast_eq_zero_iff] using hdiv
    rw [legendreSym.sq_one' p hn, mul_one, ZMod.χ₄_nat_eq_if_mod_four] at hs
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h₂
    by_cases h4 : p % 4 = 1 <;> simp [h₂, hdiv, h4, hodd] at hs ⊢ <;> omega

/-- At least one residue class survives each prime modulus. -/
theorem rootCount_lt_prime (n : ℕ) {p : ℕ} (hp : p.Prime) : rootCount n p < p := by
  refine lt_of_le_of_ne (rootCount_le n p) ?_
  intro heq
  have hall := (Nat.count_iff_forall.mp heq)
  have h₀ := hall 0 hp.pos
  have h₁ := hall 1 hp.one_lt
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero, one_pow] at h₀ h₁
  exact hp.not_dvd_one ((Nat.dvd_add_right h₀).mp h₁)

/-- The local density of roots as a multiplicative arithmetic function. -/
noncomputable def density (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => (rootCount n d : ℝ) / d, by simp⟩

@[simp] theorem density_apply (n d : ℕ) : density n d = (rootCount n d : ℝ) / d := rfl

theorem density_mult (n : ℕ) : (density n).IsMultiplicative := by
  constructor
  · simp
  · intro d e h
    simp [rootCount_mul n h, mul_div_mul_comm]

/-- Number of polynomial values divisible by `d` on `[b,b+N)`. -/
def hits (n d b N : ℕ) : ℕ :=
  ((Ico b (b + N)).filter fun s => d ∣ n ^ 2 + s ^ 2).card

private theorem root_periodic (n d : ℕ) :
    Function.Periodic (fun s => d ∣ n ^ 2 + s ^ 2) d := by
  intro s
  apply propext
  simp only [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, ZMod.natCast_self, add_zero]

theorem hits_period (n d b : ℕ) : hits n d b d = rootCount n d :=
  Nat.filter_Ico_card_eq_of_periodic b d _ (root_periodic n d)

private theorem hits_mono (n d b : ℕ) : Monotone (hits n d b) := by
  intro u v h
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.Ico_subset_Ico le_rfl (by omega)

theorem hits_blocks (n d b q : ℕ) : hits n d b (q * d) = q * rootCount n d := by
  induction q with
  | zero => simp [hits]
  | succ q ih =>
    rw [Nat.succ_mul, Nat.succ_mul, ← ih, ← hits_period n d (b + q * d)]
    unfold hits
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext s
      simp only [mem_filter, mem_union, mem_Ico]
      omega
    · apply Finset.disjoint_left.mpr
      intro s hs ht
      have h₁ := (mem_Ico.mp (mem_filter.mp hs).1).2
      have h₂ := (mem_Ico.mp (mem_filter.mp ht).1).1
      omega

/-- An incomplete final period contributes an absolute error at most one root count.
Taking `b = 1` and `N = n` gives the interval of §3.1. -/
theorem hits_error (n d b N : ℕ) (hd : 0 < d) :
    |(hits n d b N : ℝ) - (rootCount n d : ℝ) / d * N| ≤ rootCount n d := by
  let q := N / d
  have hlo : q * d ≤ N := Nat.div_mul_le_self N d
  have hhi : N ≤ (q + 1) * d := by
    have := Nat.mod_lt N hd
    have := Nat.mod_add_div N d
    dsimp [q]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (N / d) d]
    omega
  have hl := hits_mono n d b hlo
  have hu := hits_mono n d b hhi
  rw [hits_blocks] at hl hu
  have hL : (q : ℝ) * rootCount n d ≤ hits n d b N := by exact_mod_cast hl
  have hU : (hits n d b N : ℝ) ≤ ((q : ℝ) + 1) * rootCount n d := by exact_mod_cast hu
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : (0 : ℝ) ≤ rootCount n d := Nat.cast_nonneg _
  have hq : (q : ℝ) ≤ (N : ℝ) / d := (le_div_iff₀ hd').mpr (by exact_mod_cast hlo)
  have hq' : (N : ℝ) / d ≤ (q : ℝ) + 1 := (div_le_iff₀ hd').mpr (by exact_mod_cast hhi)
  rw [show (rootCount n d : ℝ) / d * N = (N / (d : ℝ)) * rootCount n d by ring]
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hq hr, mul_le_mul_of_nonneg_right hq' hr]

/-- The quadratic form for the main term, using the actual root densities. -/
noncomputable def quadraticMain (n : ℕ) (D : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, w d * w e * ((rootCount n (d.lcm e) : ℝ) / d.lcm e)

/-- The error attached to a finite system of sieve weights. -/
noncomputable def quadraticError (n : ℕ) (D : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, |w d * w e| * rootCount n (d.lcm e)

private theorem square_expansion (n s : ℕ) (D : Finset ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ D, if d ∣ n ^ 2 + s ^ 2 then w d else 0) ^ 2 =
      ∑ d ∈ D, ∑ e ∈ D, if d.lcm e ∣ n ^ 2 + s ^ 2 then w d * w e else 0 := by
  rw [sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : d ∣ n ^ 2 + s ^ 2 <;> by_cases k : e ∣ n ^ 2 + s ^ 2 <;>
    simp [Nat.lcm_dvd_iff, h, k]

/-- Selberg's quadratic upper bound, valid for any real weights normalized at 1.
The error uses only root counts, and has no dependence on the length of the interval. -/
theorem a_le_quadratic (n : ℕ) (D : Finset ℕ) (w : ℕ → ℝ)
    (h1 : 1 ∈ D) (hw : w 1 = 1) (hD : ∀ d ∈ D, 0 < d ∧ d ≤ n) :
    (a n : ℝ) ≤ n * quadraticMain n D w + quadraticError n D w := by
  let T := Ico 1 (1 + n)
  have hsubset : Ico 1 n ⊆ T := Finset.Ico_subset_Ico le_rfl (by omega)
  have hprime (s : ℕ) (hs : s ∈ T) (hp : (n ^ 2 + s ^ 2).Prime) :
      (∑ d ∈ D, if d ∣ n ^ 2 + s ^ 2 then w d else 0) = 1 := by
    rw [Finset.sum_eq_single_of_mem 1 h1, if_pos (one_dvd _), hw]
    intro d hd hne
    apply if_neg
    intro hdiv
    have he := (Nat.dvd_prime hp).mp hdiv
    have hs' := (mem_Ico.mp hs).1
    have hd' := (hD d hd).2
    rcases he with he | he
    · exact hne he
    · nlinarith [Nat.le_mul_self n, Nat.le_mul_self s]
  let F := fun s => (∑ d ∈ D, if d ∣ n ^ 2 + s ^ 2 then w d else 0) ^ 2
  have hsum : (a n : ℝ) ≤ ∑ s ∈ T, F s := by
    unfold a
    push_cast
    calc
      _ ≤ ∑ s ∈ Ico 1 n, F s := by
        apply Finset.sum_le_sum
        intro s hs
        by_cases hp : (n ^ 2 + s ^ 2).Prime
        · simp [hp, F, hprime s (hsubset hs) hp]
        · simpa [hp, F] using sq_nonneg (∑ d ∈ D, if d ∣ n ^ 2 + s ^ 2 then w d else 0)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun s _ _ => sq_nonneg _)
  have hexpand : (∑ s ∈ T, F s) =
      ∑ d ∈ D, ∑ e ∈ D, w d * w e * (hits n (d.lcm e) 1 n : ℝ) := by
    simp only [F, square_expansion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.sum_filter]
    simp [T, hits, mul_comm]
  refine hsum.trans (hexpand.le.trans ?_)
  unfold quadraticMain quadraticError
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro e he
  have h := hits_error n (d.lcm e) 1 n (Nat.lcm_pos (hD d hd).1 (hD e he).1)
  have hh := mul_le_mul_of_nonneg_left h (abs_nonneg (w d * w e))
  rw [← abs_mul] at hh
  have hb := (le_abs_self _).trans hh
  linarith

/-- The mathlib sieve for the distinct polynomial values with `1 ≤ s ≤ n`. -/
noncomputable def sieve (n P : ℕ) (hP : Squarefree P)
    (hp : ∀ p : ℕ, p.Prime → p ∣ P → 0 < rootCount n p) : BoundingSieve where
  support := (Ico 1 (1 + n)).image fun s => n ^ 2 + s ^ 2
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := n
  prodPrimes := P
  prodPrimes_squarefree := hP
  nu := density n
  nu_mult := density_mult n
  nu_pos_of_prime := fun p hprime hdiv => div_pos (by exact_mod_cast hp p hprime hdiv)
    (by exact_mod_cast hprime.pos)
  nu_lt_one_of_prime := fun p hprime _ => by
    change (rootCount n p : ℝ) / p < 1
    rw [div_lt_one (by exact_mod_cast hprime.pos)]
    exact_mod_cast rootCount_lt_prime n hprime

/-- The mass on multiples of `d` is exactly the root count in the sieved interval. -/
theorem sieve_multSum (n P d : ℕ) (hP : Squarefree P)
    (hp : ∀ p : ℕ, p.Prime → p ∣ P → 0 < rootCount n p) :
    (sieve n P hP hp).multSum d = hits n d 1 n := by
  unfold BoundingSieve.multSum sieve hits
  rw [Finset.sum_image]
  · exact Finset.sum_boole _ _
  · intro x _ y _ h
    have he : x ^ 2 = y ^ 2 := Nat.add_left_cancel h
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) he

theorem sieve_rem_le (n P d : ℕ) (hP : Squarefree P)
    (hp : ∀ p : ℕ, p.Prime → p ∣ P → 0 < rootCount n p) (hd : 0 < d) :
    |(sieve n P hP hp).rem d| ≤ rootCount n d := by
  rw [BoundingSieve.rem, sieve_multSum]
  exact hits_error n d 1 n hd

open scoped ArithmeticFunction.Moebius

private theorem sum_moebius_interval {P m l : ℕ} (hP : P ≠ 0) (hm : m ∣ P) (hl : l ≠ 0) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ (m / d) : ℝ) else 0) =
      if l = m then 1 else 0 := by
  by_cases h : l ∣ m
  · obtain ⟨k, rfl⟩ := h
    have hk : k ≠ 0 := by intro h; simp [h, hP] at hm
    have hl' := Nat.pos_of_ne_zero hl
    rw [← Finset.sum_filter]
    have ha : (∑ d ∈ P.divisors.filter (fun d => l ∣ d ∧ d ∣ l * k),
        (μ (l * k / d) : ℝ)) = ∑ i ∈ k.divisors, (μ (k / i) : ℝ) := by
      symm
      apply Finset.sum_bij' (fun i _ => l * i) (fun d _ => d / l)
      · intro i hi
        have hdiv := Nat.mul_dvd_mul_left l (Nat.dvd_of_mem_divisors hi)
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv.trans hm, hP⟩,
          dvd_mul_right _ _, hdiv⟩
      · intro d hd
        obtain ⟨_, hld, hdm⟩ := mem_filter.mp hd
        obtain ⟨i, rfl⟩ := hld
        exact Nat.mem_divisors.mpr ⟨by simpa [hl', Nat.mul_dvd_mul_iff_left hl'] using hdm, hk⟩
      · intro i _
        simp [Nat.mul_div_cancel_left _ hl']
      · intro d hd
        exact Nat.mul_div_cancel' (mem_filter.mp hd).2.1
      · intro i _
        rw [Nat.mul_div_mul_left _ _ hl']
    rw [ha, Nat.sum_div_divisors k (fun i => (μ i : ℝ))]
    have hs : (∑ i ∈ k.divisors, (μ i : ℤ)) = if k = 1 then 1 else 0 := by
      rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta]
      rfl
    have heq : l = l * k ↔ k = 1 := by
      constructor
      · intro h
        exact (Nat.eq_of_mul_eq_mul_left hl' ((Nat.mul_one l).trans h)).symm
      · rintro rfl
        simp
    by_cases hk1 : k = 1 <;> simp [heq, hk1] at hs ⊢
    exact_mod_cast hs
  · have h' : l ≠ m := by rintro rfl; exact h dvd_rfl
    have hf (d : ℕ) : ¬ (l ∣ d ∧ d ∣ m) := fun hh => h (hh.1.trans hh.2)
    simp [hf, h']

/-- The truncated Selberg denominator. The admissible primes are encoded in `S.prodPrimes`. -/
noncomputable def denominator (S : BoundingSieve) (z : ℕ) : ℝ :=
  ∑ m ∈ S.prodPrimes.divisors.filter (· ≤ z), S.selbergTerms m

private theorem denominator_pos (S : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < denominator S z := by
  apply Finset.sum_pos
  · intro m hm
    exact BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hm).1)
  · exact ⟨1, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _, S.prodPrimes_ne_zero⟩, hz⟩⟩

/-- Möbius inversion of the diagonal coordinates of the Selberg quadratic form. -/
noncomputable def selbergWeight (S : BoundingSieve) (z d : ℕ) : ℝ :=
  (∑ m ∈ S.prodPrimes.divisors.filter (· ≤ z),
    if d ∣ m then (μ (m / d) : ℝ) * (μ m : ℝ) * S.selbergTerms m else 0) /
    (S.nu d * denominator S z)

theorem selbergWeight_one (S : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    selbergWeight S z 1 = 1 := by
  unfold selbergWeight
  simp only [one_dvd, if_true, Nat.div_one, S.nu_mult.map_one, one_mul]
  rw [div_eq_one_iff_eq (denominator_pos S hz).ne']
  apply Finset.sum_congr rfl
  intro m hm
  have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree
    (S.squarefree_of_mem_divisors_prodPrimes (mem_filter.mp hm).1)
  have h' : (μ m : ℝ) ^ 2 = 1 := by exact_mod_cast h
  rw [← sq, h', one_mul]

theorem selbergWeight_eq_zero (S : BoundingSieve) {z d : ℕ} (h : z < d) :
    selbergWeight S z d = 0 := by
  unfold selbergWeight
  convert zero_div (S.nu d * denominator S z) using 2
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm, hmz⟩ := mem_filter.mp hm
  exact if_neg fun hdm => (not_le_of_gt h) ((Nat.le_of_dvd (Nat.pos_of_mem_divisors hm) hdm).trans hmz)

private theorem selberg_transform (S : BoundingSieve) {z l : ℕ} (hl : l ∈ S.prodPrimes.divisors) :
    (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * selbergWeight S z d else 0) =
      (if l ≤ z then (μ l : ℝ) * S.selbergTerms l else 0) / denominator S z := by
  let D := S.prodPrimes.divisors.filter (· ≤ z)
  have hexpand (d : ℕ) (hd : d ∈ S.prodPrimes.divisors) :
      (if l ∣ d then S.nu d * selbergWeight S z d else 0) =
        (∑ m ∈ D, if l ∣ d ∧ d ∣ m then (μ (m / d) : ℝ) * (μ m : ℝ) *
          S.selbergTerms m else 0) / denominator S z := by
    by_cases hld : l ∣ d
    · simp only [selbergWeight, hld, true_and, if_true, D]
      rw [← div_div, mul_div_assoc', mul_div_cancel₀ _ (S.nu_ne_zero (Nat.dvd_of_mem_divisors hd))]
    · simp [hld]
  rw [Finset.sum_congr rfl hexpand, ← Finset.sum_div, Finset.sum_comm]
  congr 1
  calc
    _ = ∑ m ∈ D, ((if l = m then 1 else 0 : ℝ) * (μ m : ℝ) * S.selbergTerms m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← sum_moebius_interval S.prodPrimes_ne_zero (Nat.dvd_of_mem_divisors (mem_filter.mp hm).1)
        (Nat.pos_of_mem_divisors hl).ne', Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp_all
    _ = _ := by simp [D, hl, ite_mul]

/-- The chosen weights attain the reciprocal Selberg denominator exactly. -/
theorem mainSum_optimal (S : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    S.mainSum (BoundingSieve.lambdaSquared (selbergWeight S z)) = (denominator S z)⁻¹ := by
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    _ = ∑ l ∈ S.prodPrimes.divisors,
        (if l ≤ z then S.selbergTerms l else 0) / (denominator S z) ^ 2 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [selberg_transform S hl]
      by_cases h : l ≤ z
      · have hm : (μ l : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
            (S.squarefree_of_mem_divisors_prodPrimes hl)
        have hg := (S.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).ne'
        simp only [h, if_true, div_pow, mul_pow, hm, one_mul]
        field_simp
      · simp [h]
    _ = _ := by
      rw [← Finset.sum_div, ← Finset.sum_filter]
      change denominator S z / denominator S z ^ 2 = _
      field_simp [(denominator_pos S hz).ne']

/-- The root-density quadratic form agrees with the diagonalized mathlib main sum. -/
private theorem quadraticMain_eq (n P : ℕ) (hP : Squarefree P)
    (hp : ∀ p : ℕ, p.Prime → p ∣ P → 0 < rootCount n p) (z : ℕ) :
    let S := sieve n P hP hp
    let w := selbergWeight S z
    quadraticMain n (P.divisors.filter (· ≤ z)) w = S.mainSum (BoundingSieve.lambdaSquared w) := by
  let S := sieve n P hP hp
  let w := selbergWeight S z
  change quadraticMain n (P.divisors.filter (· ≤ z)) w = S.mainSum (BoundingSieve.lambdaSquared w)
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul]
  change _ = ∑ d ∈ P.divisors, ∑ e ∈ P.divisors, _
  simp only [quadraticMain, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdz : d ≤ z
  · rw [if_pos hdz]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hez : e ≤ z
    · rw [if_pos hez]
      change w d * w e * S.nu (d.lcm e) = _
      rw [S.nu_mult.map_lcm (S.nu_ne_zero ((Nat.gcd_dvd_left d e).trans (Nat.dvd_of_mem_divisors hd)))]
      ring
    · simp [hez, w, selbergWeight_eq_zero S (lt_of_not_ge hez)]
  · simp [hdz, w, selbergWeight_eq_zero S (lt_of_not_ge hdz)]

/-- The optimized finite Selberg inequality for the concrete sequence and its root-count error. -/
theorem a_le_selberg (n P z : ℕ) (hP : Squarefree P)
    (hp : ∀ p : ℕ, p.Prime → p ∣ P → 0 < rootCount n p) (hz : 1 ≤ z) (hzn : z ≤ n) :
    let S := sieve n P hP hp
    (a n : ℝ) ≤ n / denominator S z +
      quadraticError n (P.divisors.filter (· ≤ z)) (selbergWeight S z) := by
  let S := sieve n P hP hp
  have hone : 1 ∈ P.divisors.filter (· ≤ z) :=
    mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _, hP.ne_zero⟩, hz⟩
  have h := a_le_quadratic n _ _ hone (selbergWeight_one S hz) (fun d hd =>
    ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1, (mem_filter.mp hd).2.trans hzn⟩)
  rw [quadraticMain_eq n P hP hp z, mainSum_optimal _ hz, ← div_eq_mul_inv] at h
  exact h

private theorem lcm_div_of_squarefree {d m x : ℕ} (hm : Squarefree m) (hd : d ∣ m)
    (hx : x ∣ d) : d.lcm (m / x) = m := by
  have hxm := hx.trans hd
  have hprod := Nat.div_mul_cancel hxm
  have hc := Nat.coprime_of_squarefree_mul (hprod.symm ▸ hm)
  apply Nat.dvd_antisymm (Nat.lcm_dvd hd (Nat.div_dvd_of_dvd hxm))
  have hdiv := hc.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_right d (m / x))
    (hx.trans (Nat.dvd_lcm_left d (m / x)))
  rwa [hprod] at hdiv

private theorem selberg_mass_multiples (S : BoundingSieve) {d z : ℕ} (hd : d ∣ S.prodPrimes) :
    let D := S.prodPrimes.divisors.filter (· ≤ z)
    (∑ m ∈ D.filter (d ∣ ·), S.selbergTerms m) / S.nu d ≤ denominator S z := by
  let D := S.prodPrimes.divisors.filter (· ≤ z)
  let T := D.filter (d ∣ ·)
  let f := fun t : ℕ × ℕ => t.1 / t.2
  have hpair {m x : ℕ} (h : (m,x) ∈ T ×ˢ d.divisors) :
      m ∈ D ∧ d ∣ m ∧ x ∣ d :=
    ⟨(mem_filter.mp (mem_product.mp h).1).1, (mem_filter.mp (mem_product.mp h).1).2,
      Nat.dvd_of_mem_divisors (mem_product.mp h).2⟩
  have hs {m : ℕ} (hm : m ∈ D) := S.squarefree_of_mem_divisors_prodPrimes (mem_filter.mp hm).1
  have hinj : Set.InjOn f (↑(T ×ˢ d.divisors)) := by
    rintro ⟨m,x⟩ hmx ⟨k,y⟩ hky he
    obtain ⟨hm, hdm, hxd⟩ := hpair hmx
    obtain ⟨hk, hdk, hyd⟩ := hpair hky
    change m / x = k / y at he
    have hmk := congrArg (Nat.lcm d) he
    rw [lcm_div_of_squarefree (hs hm) hdm hxd, lcm_div_of_squarefree (hs hk) hdk hyd] at hmk
    subst k
    exact Prod.ext rfl ((Nat.div_eq_iff_eq_of_dvd_dvd (hs hm).ne_zero
      (hxd.trans hdm) (hyd.trans hdk)).mp he)
  have hsub : (T ×ˢ d.divisors).image f ⊆ D := by
    intro v hv
    obtain ⟨⟨m,x⟩, hmx, rfl⟩ := mem_image.mp hv
    obtain ⟨hm, hdm, hxd⟩ := hpair hmx
    obtain ⟨hmp, hmz⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(Nat.div_dvd_of_dvd (hxd.trans hdm)).trans (Nat.dvd_of_mem_divisors hmp), S.prodPrimes_ne_zero⟩,
      (Nat.div_le_self m x).trans hmz⟩
  have hinv := S.nu_inv_eq_sum_divisors_inv_selbergTerms hd
  rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero hd] at hinv
  change (∑ m ∈ T, S.selbergTerms m) / S.nu d ≤ ∑ m ∈ D, S.selbergTerms m
  rw [div_eq_mul_inv, hinv, Finset.sum_mul]
  calc
    _ = ∑ t ∈ T ×ˢ d.divisors, S.selbergTerms (f t) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨hm, hdm⟩ := mem_filter.mp hm
      have hxd := Nat.dvd_of_mem_divisors hx
      have hxm := hxd.trans hdm
      have hc := Nat.coprime_of_squarefree_mul ((Nat.div_mul_cancel hxm).symm ▸ hs hm)
      exact (S.selbergTerms_isMultiplicative.map_div_of_coprime hxm hc
        (S.selbergTerms_pos (hxd.trans hd)).ne').symm
    _ = ∑ v ∈ (T ×ˢ d.divisors).image f, S.selbergTerms v := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ =>
      (S.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hm).1)).le)

/-- The normalized Selberg weights have magnitude at most one. -/
theorem abs_selbergWeight_le_one (S : BoundingSieve) {d z : ℕ} (hd : d ∣ S.prodPrimes)
    (hz : 1 ≤ z) : |selbergWeight S z d| ≤ 1 := by
  have hn := S.nu_pos_of_dvd_prodPrimes hd
  have hg := denominator_pos S hz
  have hμ (m : ℕ) : |(μ m : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  unfold selbergWeight
  rw [abs_div, abs_of_pos (mul_pos hn hg), div_le_one (mul_pos hn hg), mul_comm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_
    ((div_le_iff₀ hn).mp (selberg_mass_multiples S (z := z) hd)))
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro m hm
  have hgm := S.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hm).1)
  by_cases h : d ∣ m
  · rw [if_pos h, if_pos h, abs_mul, abs_mul, abs_of_pos hgm]
    calc
      _ ≤ (1 * 1 : ℝ) * S.selbergTerms m := by gcongr <;> apply hμ
      _ = _ := by ring
  · simp [h]

/-- Uniform all-modulus bound sufficient for a power-saving remainder when the
sieve level is a sufficiently small power of `n`. -/
theorem a_le_selberg_pow (n P z : ℕ) (hP : Squarefree P)
    (hp : ∀ p : ℕ, p.Prime → p ∣ P → 0 < rootCount n p) (hz : 1 ≤ z) (hzn : z ≤ n) :
    (a n : ℝ) ≤ n / denominator (sieve n P hP hp) z + (z : ℝ) ^ 6 := by
  let S := sieve n P hP hp
  let D := P.divisors.filter (· ≤ z)
  let w := selbergWeight S z
  refine (a_le_selberg n P z hP hp hz hzn).trans (add_le_add_right ?_ _)
  have hw (d : ℕ) (hd : d ∈ D) : |w d| ≤ z :=
    (abs_selbergWeight_le_one S (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1) hz).trans
      (by exact_mod_cast hz)
  have hcard : D.card ≤ z := by
    calc
      D.card ≤ (Icc 1 z).card := card_le_card (fun d hd =>
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1, (mem_filter.mp hd).2⟩)
      _ = z := by simp
  change (∑ d ∈ D, ∑ e ∈ D, |w d * w e| * rootCount n (d.lcm e)) ≤ _
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D, (z : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hde : rootCount n (d.lcm e) ≤ z * z :=
        (rootCount_le _ _).trans ((Nat.lcm_le_mul (Nat.pos_of_mem_divisors (mem_filter.mp hd).1)
          (Nat.pos_of_mem_divisors (mem_filter.mp he).1)).trans
          (Nat.mul_le_mul (mem_filter.mp hd).2 (mem_filter.mp he).2))
      rw [abs_mul, show (z : ℝ)^4 = ((z : ℝ) * z) * ((z : ℝ) * z) by ring]
      gcongr
      · exact hw d hd
      · exact hw e he
      · exact_mod_cast hde
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : (D.card : ℝ) ≤ z := by exact_mod_cast hcard
      calc
        _ ≤ (z : ℝ) * (z * z ^ 4) := by gcongr
        _ = _ := by ring

/-- All the primes up to the cutoff at which the polynomial has a root. -/
def sievingPrimes (n z : ℕ) : Finset ℕ :=
  (Icc 2 z).filter fun p => p.Prime ∧ 0 < rootCount n p

def sieveProduct (n z : ℕ) : ℕ := ∏ p ∈ sievingPrimes n z, p

private theorem sieveProduct_squarefree (n z : ℕ) : Squarefree (sieveProduct n z) := by
  have hp (p : ℕ) (h : p ∈ sievingPrimes n z) := (mem_filter.mp h).2.1
  exact Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hne =>
    Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp a ha) (hp b hb)).mpr hne))
    (fun p h => (hp p h).squarefree)

private theorem rootCount_pos_of_dvd_sieveProduct (n z p : ℕ) (hp : p.Prime)
    (hd : p ∣ sieveProduct n z) : 0 < rootCount n p := by
  have hmem := (Nat.mem_primeFactors_of_ne_zero (sieveProduct_squarefree n z).ne_zero).mpr ⟨hp, hd⟩
  change p ∈ (∏ q ∈ sievingPrimes n z, q).primeFactors at hmem
  rw [Nat.primeFactors_prod (fun q h => (mem_filter.mp h).2.1)] at hmem
  exact (mem_filter.mp hmem).2.2

/-- The denominators selected by the prime product are exactly the squarefree
integers up to the cutoff with a nonempty set of roots. -/
theorem mem_sieveDivisors_iff (n z d : ℕ) :
    d ∈ (sieveProduct n z).divisors.filter (· ≤ z) ↔
      d ≤ z ∧ Squarefree d ∧ 0 < rootCount n d := by
  have hP := sieveProduct_squarefree n z
  let S := sieve n (sieveProduct n z) hP (rootCount_pos_of_dvd_sieveProduct n z)
  constructor
  · intro hd
    obtain ⟨h, hz⟩ := mem_filter.mp hd
    have hdiv := Nat.dvd_of_mem_divisors h
    refine ⟨hz, hP.squarefree_of_dvd hdiv, ?_⟩
    have hpos := S.nu_pos_of_dvd_prodPrimes hdiv
    by_contra! h0
    change 0 < (rootCount n d : ℝ) / d at hpos
    simp [Nat.eq_zero_of_le_zero h0] at hpos
  · rintro ⟨hdz, hsq, hroot⟩
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hP.ne_zero⟩, hdz⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq, Nat.prod_primeFactors_dvd_iff hP.ne_zero]
    change d.primeFactors ⊆ (∏ q ∈ sievingPrimes n z, q).primeFactors
    rw [Nat.primeFactors_prod (fun q h => (mem_filter.mp h).2.1)]
    intro p hpd
    have hp := Nat.prime_of_mem_primeFactors hpd
    have hdiv := Nat.dvd_of_mem_primeFactors hpd
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le, (Nat.le_of_dvd hsq.ne_zero.bot_lt hdiv).trans hdz⟩,
      hp, ?_⟩
    obtain ⟨k, rfl⟩ := hdiv
    rw [rootCount_mul n (Nat.coprime_of_squarefree_mul hsq)] at hroot
    exact Nat.pos_of_mul_pos_right hroot

/-- The Selberg denominator in terms of local congruence counts. -/
noncomputable def G (n z : ℕ) : ℝ :=
  ∑ d ∈ (sieveProduct n z).divisors.filter (· ≤ z),
    ∏ p ∈ d.primeFactors, (rootCount n p : ℝ) / (p - (rootCount n p : ℝ))

theorem G_eq_sum (n z : ℕ) :
    G n z = ∑ d ∈ (Icc 1 z).filter (fun d => Squarefree d ∧ 0 < rootCount n d),
      ∏ p ∈ d.primeFactors, (rootCount n p : ℝ) / (p - (rootCount n p : ℝ)) := by
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext d
  rw [mem_sieveDivisors_iff, mem_filter, mem_Icc]
  exact ⟨fun ⟨hd, hs, hω⟩ => ⟨⟨hs.ne_zero.bot_lt, hd⟩, hs, hω⟩,
    fun ⟨⟨_, hd⟩, hs, hω⟩ => ⟨hd, hs, hω⟩⟩

private theorem denominator_eq_G (n z : ℕ) :
    denominator (sieve n (sieveProduct n z) (sieveProduct_squarefree n z)
      (rootCount_pos_of_dvd_sieveProduct n z)) z = G n z := by
  let S := sieve n (sieveProduct n z) (sieveProduct_squarefree n z)
    (rootCount_pos_of_dvd_sieveProduct n z)
  change (∑ d ∈ (sieveProduct n z).divisors.filter (· ≤ z), S.selbergTerms d) = _
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv : d ∣ S.prodPrimes := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
  rw [BoundingSieve.selbergTerms_apply, ← S.prod_primeFactors_nu hdiv, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpd
  have hp := Nat.prime_of_mem_primeFactors hpd
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change (rootCount n p : ℝ) / p * (1 - (rootCount n p : ℝ) / p)⁻¹ = _
  have hl : (rootCount n p : ℝ) < p := by exact_mod_cast rootCount_lt_prime n hp
  field_simp

theorem one_le_G (n z : ℕ) (hz : 1 ≤ z) : 1 ≤ G n z := by
  rw [← denominator_eq_G]
  let S := sieve n (sieveProduct n z) (sieveProduct_squarefree n z)
    (rootCount_pos_of_dvd_sieveProduct n z)
  change 1 ≤ ∑ d ∈ S.prodPrimes.divisors.filter (· ≤ z), S.selbergTerms d
  rw [← S.selbergTerms_isMultiplicative.map_one]
  exact Finset.single_le_sum (fun d hd => (S.selbergTerms_pos
    (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)).le)
    (mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _, S.prodPrimes_ne_zero⟩, hz⟩)

/-- A finite upper sieve with no local hypotheses. -/
theorem a_le_G (n z : ℕ) (hz : 1 ≤ z) (hzn : z ≤ n) :
    (a n : ℝ) ≤ n / G n z + (z : ℝ)^6 := by
  rw [← denominator_eq_G]
  exact a_le_selberg_pow n _ z _ _ hz hzn

private def rootArithmetic (n : ℕ) : ArithmeticFunction ℕ :=
  ⟨rootCount n, by simp [rootCount]⟩

private theorem rootArithmetic_mult (n : ℕ) : (rootArithmetic n).IsMultiplicative :=
  ⟨rootCount_one n, rootCount_mul n⟩

theorem rootCount_le_card_divisors (n : ℕ) {d : ℕ} (hd : Squarefree d) :
    rootCount n d ≤ d.divisors.card := by
  have hprod := (rootArithmetic_mult n).map_prod_of_subset_primeFactors d d.primeFactors Subset.rfl
  rw [Nat.prod_primeFactors_of_squarefree hd] at hprod
  change rootArithmetic n d ≤ _
  rw [hprod, Nat.card_divisors hd.ne_zero]
  apply Finset.prod_le_prod'
  intro p hp
  have h := Nat.prime_of_mem_primeFactors hp
  have hfac := h.factorization_pos_of_dvd hd.ne_zero (Nat.dvd_of_mem_primeFactors hp)
  change rootCount n p ≤ _
  rw [rootCount_prime n h]
  split_ifs <;> omega

theorem sum_card_divisors_le (z : ℕ) :
    (∑ d ∈ Ioc 0 z, (d.divisors.card : ℝ)) ≤ z * (1 + Real.log z) := by
  have hnat := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div z
  simp only [ArithmeticFunction.sigma_zero_apply] at hnat
  have hreal : (∑ d ∈ Ioc 0 z, (d.divisors.card : ℝ)) =
      ∑ d ∈ Ioc 0 z, ((z / d : ℕ) : ℝ) := by exact_mod_cast hnat
  rw [hreal]
  calc
    _ ≤ ∑ d ∈ Ioc 0 z, (z : ℝ) * (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← div_eq_mul_inv, le_div_iff₀ (by exact_mod_cast (mem_Ioc.mp hd).1)]
      exact_mod_cast Nat.div_mul_le_self z d
    _ = (z : ℝ) * harmonic z := by
      rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
      push_cast
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (Nat.cast_nonneg _)

/-- Section 3.2 with an arbitrary squarefree product of admissible primes. -/
theorem a_le_selberg_log (n P z : ℕ) (hP : Squarefree P)
    (hp : ∀ p : ℕ, p.Prime → p ∣ P → 0 < rootCount n p) (hz : 1 ≤ z) (hzn : z ≤ n) :
    (a n : ℝ) ≤ n / denominator (sieve n P hP hp) z + (z : ℝ)^2 * (1 + Real.log z)^2 := by
  let S := sieve n P hP hp
  let D := P.divisors.filter (· ≤ z)
  let w := selbergWeight S z
  refine (a_le_selberg n P z hP hp hz hzn).trans (add_le_add_right ?_ _)
  have hω (d e : ℕ) (hd : d ∈ D) (he : e ∈ D) :
      rootCount n (d.lcm e) ≤ d.divisors.card * e.divisors.card := by
    have hdP := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
    have heP := Nat.dvd_of_mem_divisors (mem_filter.mp he).1
    have hg := S.nu_pos_of_dvd_prodPrimes ((Nat.gcd_dvd_left d e).trans hdP)
    change 0 < (rootCount n (d.gcd e) : ℝ) / (d.gcd e) at hg
    have hpos : 0 < rootCount n (d.gcd e) := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hg
    have hmul := (rootArithmetic_mult n).lcm_apply_mul_gcd_apply (x := d) (y := e)
    calc
      _ ≤ rootCount n (d.lcm e) * rootCount n (d.gcd e) := Nat.le_mul_of_pos_right _ hpos
      _ = _ := hmul
      _ ≤ _ := Nat.mul_le_mul (rootCount_le_card_divisors n (hP.squarefree_of_dvd hdP))
        (rootCount_le_card_divisors n (hP.squarefree_of_dvd heP))
  have hsum : (∑ d ∈ D, (d.divisors.card : ℝ)) ≤ z * (1 + Real.log z) := by
    apply le_trans _ (sum_card_divisors_le z)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1, (mem_filter.mp hd).2⟩
    · intros
      positivity
  calc
    quadraticError n D w ≤ ∑ d ∈ D, ∑ e ∈ D, (d.divisors.card : ℝ) * e.divisors.card := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have h1 := abs_selbergWeight_le_one S (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1) hz
      have h2 := abs_selbergWeight_le_one S (Nat.dvd_of_mem_divisors (mem_filter.mp he).1) hz
      rw [abs_mul]
      calc
        _ ≤ (1 * 1 : ℝ) * rootCount n (d.lcm e) := by gcongr
        _ ≤ _ := by simpa using (show (rootCount n (d.lcm e) : ℝ) ≤ _ by exact_mod_cast hω d e hd he)
    _ = (∑ d ∈ D, (d.divisors.card : ℝ)) ^ 2 := by
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ ≤ ((z : ℝ) * (1 + Real.log z))^2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun d _ => Nat.cast_nonneg _) hsum 2
    _ = _ := mul_pow _ _ _

/-- The explicit upper bound of §3.2 for the original OEIS sequence. -/
theorem a_le_G_log (n z : ℕ) (hz : 1 ≤ z) (hzn : z ≤ n) :
    (a n : ℝ) ≤ n / G n z + (z : ℝ)^2 * (1 + Real.log z)^2 := by
  rw [← denominator_eq_G]
  exact a_le_selberg_log n _ z _ _ hz hzn

/-- The real-cutoff version. The denominator changes only at integer cutoffs. -/
theorem a_le_G_real (n : ℕ) (z : ℝ) (hz : 1 ≤ z) (hzn : z ≤ n) :
    (a n : ℝ) ≤ n / G n ⌊z⌋₊ + z ^ 2 * (1 + Real.log z) ^ 2 := by
  have hf : 1 ≤ ⌊z⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hz)
  have hfz := Nat.floor_le (by linarith : 0 ≤ z)
  have hfn : ⌊z⌋₊ ≤ n := by exact_mod_cast hfz.trans hzn
  have hf' : (1 : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast hf
  have hlog := Real.log_le_log (by linarith : 0 < (⌊z⌋₊ : ℝ)) hfz
  have hnon := Real.log_nonneg hf'
  refine (a_le_G_log n _ hf hfn).trans (add_le_add_right ?_ _)
  exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hfz 2)
    (pow_le_pow_left₀ (by linarith) (add_le_add_right hlog 1) 2)
    (sq_nonneg _) (sq_nonneg _)

end A069004Sieve

/-
# Local factors for the A069004 sieve

For a finite set of primes `Q`, the squarefree root counts and the Selberg
denominator for `2 ^ t * ∏ q ∈ Q, q` are independent of `t`. When all primes
in `Q` are inert, every split prime contributes two roots.
These local factors determine the Selberg denominator.
-/

namespace A069004Root

open Finset A069004Sieve

/-- The prime root count for the family with prime factors in `{2} ∪ Q`. -/
def primeRoots (Q : Finset ℕ) (p : ℕ) : ℕ :=
  if p = 2 ∨ p ∈ Q then 1 else if p % 4 = 1 then 2 else 0

/-- The formula holds at every prime and also for exponent zero. -/
theorem rootCount_prime_family (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (t : ℕ) {p : ℕ} (hp : p.Prime) :
    rootCount (2 ^ t * ∏ q ∈ Q, q) p = primeRoots Q p := by
  have hprod : p ∣ ∏ q ∈ Q, q ↔ p ∈ Q := by
    have hne := Finset.prod_ne_zero_iff.mpr fun q hq => (hQ q hq).ne_zero
    calc
      p ∣ ∏ q ∈ Q, q ↔ p ∈ (∏ q ∈ Q, q).primeFactors := by
        simp [Nat.mem_primeFactors, hp, hne]
      _ ↔ p ∈ Q := by rw [Nat.primeFactors_prod hQ]
  have hcond : (p = 2 ∨ p ∣ 2 ^ t * ∏ q ∈ Q, q) ↔ p = 2 ∨ p ∈ Q := by
    rw [hp.dvd_mul, hprod]
    have htwo (h : p ∣ 2 ^ t) : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    tauto
  simp only [rootCount_prime _ hp, hcond, primeRoots]

/-- A split prime cannot occur in the chosen set of inert primes. -/
theorem rootCount_split (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q ∧ q % 4 = 3)
    (t : ℕ) {p : ℕ} (hp : p.Prime) (hs : p % 4 = 1) :
    rootCount (2 ^ t * ∏ q ∈ Q, q) p = 2 := by
  have hnot : p ∉ Q := fun h => by
    have := (hQ p h).2
    omega
  have htwo : p ≠ 2 := by omega
  simp [rootCount_prime_family Q (fun q h => (hQ q h).1) t hp, primeRoots, htwo, hnot, hs]

/-- The multiplicative root count as a Mathlib arithmetic function. -/
def rootCountAF (n : ℕ) : ArithmeticFunction ℕ := ⟨rootCount n, by simp [rootCount]⟩

theorem rootCountAF_mult (n : ℕ) : (rootCountAF n).IsMultiplicative :=
  ⟨rootCount_one n, fun h => rootCount_mul n h⟩

/-- For a squarefree modulus, all dependence on the exponent of 2 disappears. -/
theorem rootCount_squarefree (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (t : ℕ) {d : ℕ} (hd : Squarefree d) :
    rootCount (2 ^ t * ∏ q ∈ Q, q) d = ∏ p ∈ d.primeFactors, primeRoots Q p := by
  change rootCountAF _ d = _
  rw [← (rootCountAF_mult _).prod_primeFactors hd]
  exact prod_congr rfl fun p hp => rootCount_prime_family Q hQ t (Nat.prime_of_mem_primeFactors hp)

/-- The nonzero prime values of the inverse density `f` are `p` and `p / 2`. -/
theorem inv_density_prime_family (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (t : ℕ) {p : ℕ} (hp : p.Prime) :
    (density (2 ^ t * ∏ q ∈ Q, q) p)⁻¹ =
      if p = 2 ∨ p ∈ Q then (p : ℝ) else if p % 4 = 1 then (p : ℝ) / 2 else 0 := by
  rw [density_apply, rootCount_prime_family Q hQ t hp, primeRoots]
  split_ifs <;> simp

/-- Prime factors of the Selberg denominator. In particular `primeG Q 2 = 1`. -/
noncomputable def primeG (Q : Finset ℕ) (p : ℕ) : ℝ :=
  if p = 2 ∨ p ∈ Q then 1 / ((p : ℝ) - 1)
  else if p % 4 = 1 then 2 / ((p : ℝ) - 2) else 0

theorem rootCount_div_sub_eq_primeG (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (t : ℕ) {p : ℕ} (hp : p.Prime) :
    let r := (rootCount (2 ^ t * ∏ q ∈ Q, q) p : ℝ)
    r / ((p : ℝ) - r) = primeG Q p := by
  dsimp only
  rw [rootCount_prime_family Q hQ t hp, primeRoots, primeG]
  split_ifs <;> simp

@[simp] theorem primeG_two (Q : Finset ℕ) : primeG Q 2 = 1 := by norm_num [primeG]

/-- The local density lower-bounds the Selberg factor, also when both vanish. -/
theorem density_le_primeG (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (t : ℕ) {p : ℕ} (hp : p.Prime) :
    density (2 ^ t * ∏ q ∈ Q, q) p ≤ primeG Q p := by
  let n := 2 ^ t * ∏ q ∈ Q, q
  rw [← rootCount_div_sub_eq_primeG Q hQ t hp]
  change (rootCount n p : ℝ) / p ≤ rootCount n p / ((p : ℝ) - rootCount n p)
  have hlt : (rootCount n p : ℝ) < p := by exact_mod_cast rootCount_lt_prime n hp
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sub_pos.mpr hlt)
    (sub_le_self _ (Nat.cast_nonneg _))

/-- Adjoining a chosen prime contributes the reciprocal of its surviving fraction. -/
theorem one_add_primeG_of_mem {Q : Finset ℕ} {p : ℕ} (hmem : p ∈ Q) (hp : p.Prime) :
    1 + primeG Q p = (1 - 1 / (p : ℝ))⁻¹ := by
  have hgt : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  simp only [primeG, hmem, or_true, if_true]
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rw [one_sub_div hp0, inv_div]
  field_simp [(sub_pos.mpr hgt).ne']
  exact sub_add_cancel _ _

/-- The denominator can be summed over all positive squarefree moduli up to
`z`. Each added modulus has a prime factor with zero local weight. -/
theorem G_eq_sum_squarefree (n z : ℕ) :
    G n z = ∑ d ∈ (Icc 1 z).filter Squarefree,
      ∏ p ∈ d.primeFactors, (rootCount n p : ℝ) / ((p : ℝ) - rootCount n p) := by
  unfold G
  apply sum_subset
  · intro d hd
    obtain ⟨hdz, hsq, _⟩ := (mem_sieveDivisors_iff n z d).mp hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hsq.ne_zero, hdz⟩, hsq⟩
  · intro d hd hnot
    obtain ⟨hrange, hsq⟩ := mem_filter.mp hd
    have hzero : rootCountAF n d = 0 := by
      by_contra h
      exact hnot ((mem_sieveDivisors_iff n z d).mpr
        ⟨(mem_Icc.mp hrange).2, hsq, Nat.pos_of_ne_zero h⟩)
    rw [← (rootCountAF_mult n).prod_primeFactors hsq, Finset.prod_eq_zero_iff] at hzero
    obtain ⟨p, hp, hroot⟩ := hzero
    change rootCount n p = 0 at hroot
    exact Finset.prod_eq_zero hp (by simp [hroot])

/-- The denominator in the sieve upper bound depends only on `Q` and the cutoff. -/
theorem G_family (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q) (t z : ℕ) :
    G (2 ^ t * ∏ q ∈ Q, q) z =
      ∑ d ∈ (Icc 1 z).filter Squarefree, ∏ p ∈ d.primeFactors, primeG Q p := by
  rw [G_eq_sum_squarefree]
  refine sum_congr rfl fun d _ => prod_congr rfl fun p hp => ?_
  exact rootCount_div_sub_eq_primeG Q hQ t (Nat.prime_of_mem_primeFactors hp)

end A069004Root

/-
# Lower bound on the Selberg bounding sum for OEIS A069004

This file formalizes the lower bound on the Selberg denominator (corresponding to §3.3 of
`A069004-gemini.md`), via the Dirichlet convolution `b = ζ * χ₄`:
1. Pointwise prime-power evaluation of `b = ζ * χ₄` and `∑_{m=1}^N b(m)/m ≥ (2/3) log(N+1)`.
2. Squarefree decomposition `m = d * r^2`, giving `b(d * r^2) ≤ w₀(d) * τ(r)^2` and vanishing
   whenever `d` has a prime factor `p ≡ 3 (mod 4)`.
3. Elementary finite-sum bound `∑_{r=1}^N τ(r)^2 / r^2 ≤ 16` via the injection
   `(r, u, v) ↦ (gcd(u, v), u / gcd(u, v), v / gcd(u, v), r / lcm(u, v))` and `∑ 1/k^2 ≤ 2`.
4. Lower bounds `(1/24) log(N+1) ≤ W₀(N) ≤ G₀(N)`.
5. Factoring out a squarefree product `M = ∏_{p ∈ S} p` of primes `p ≡ 3 (mod 4)` and applying the
   result directly to `BoundingSieve.selbergTerms` from `Mathlib.NumberTheory.SelbergSieve`.
-/

namespace A069004Density

open Finset ArithmeticFunction

section CharacterAndB

/-- The non-principal Dirichlet character modulo 4 as an arithmetic function into `ℤ`. -/
def chi4AF : ArithmeticFunction ℤ where
  toFun n := ZMod.χ₄ (n : ZMod 4)
  map_zero' := by simp

@[simp]
theorem chi4AF_apply (n : ℕ) : chi4AF n = ZMod.χ₄ (n : ZMod 4) := rfl

theorem chi4AF_mul (m n : ℕ) : chi4AF (m * n) = chi4AF m * chi4AF n := by
  rw [chi4AF_apply, chi4AF_apply, chi4AF_apply, Nat.cast_mul, map_mul]

theorem chi4AF_pow (p k : ℕ) : chi4AF (p ^ k) = (chi4AF p) ^ k := by
  rw [chi4AF_apply, chi4AF_apply, Nat.cast_pow, map_pow]

theorem chi4AF_isMultiplicative : chi4AF.IsMultiplicative :=
  ⟨by simp [chi4AF], fun _ => chi4AF_mul _ _⟩

theorem chi4AF_two : chi4AF 2 = 0 := by decide

theorem chi4AF_of_mod_four_eq_one {n : ℕ} (hn : n % 4 = 1) : chi4AF n = 1 :=
  ZMod.χ₄_nat_one_mod_four hn

theorem chi4AF_of_mod_four_eq_three {n : ℕ} (hn : n % 4 = 3) : chi4AF n = -1 :=
  ZMod.χ₄_nat_three_mod_four hn

theorem prime_cases_mod_four {p : ℕ} (hp : p.Prime) : p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · exact Or.inl rfl
  · omega

/-- The twisted divisor sum `b(m) = ∑_{d ∣ m} χ₄(d)` as an arithmetic function into `ℤ`. -/
def bAF : ArithmeticFunction ℤ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * chi4AF

theorem bAF_isMultiplicative : bAF.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul chi4AF_isMultiplicative

theorem bAF_apply (n : ℕ) : bAF n = ∑ d ∈ n.divisors, chi4AF d := by
  rw [bAF, ArithmeticFunction.coe_zeta_mul_apply]

theorem bAF_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    bAF (p ^ a) = ∑ j ∈ Finset.range (a + 1), (chi4AF p) ^ j := by
  rw [bAF_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa using chi4AF_pow p j

theorem bAF_two_pow (a : ℕ) : bAF (2 ^ a) = 1 := by
  rw [bAF_prime_pow Nat.prime_two, chi4AF_two, Finset.sum_range_succ']
  simp

theorem bAF_prime_pow_one_mod_four {p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) (a : ℕ) :
    bAF (p ^ a) = (a + 1 : ℤ) := by
  rw [bAF_prime_pow hp, chi4AF_of_mod_four_eq_one h1]
  simp

theorem bAF_prime_pow_three_mod_four {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (a : ℕ) :
    bAF (p ^ a) = if Even a then 1 else 0 := by
  rw [bAF_prime_pow hp, chi4AF_of_mod_four_eq_three h3]
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hn : Even n
    · have hodd : ¬ Even (n + 1) := by rwa [Nat.even_add_one, not_not]
      rw [if_pos hn, if_neg hodd, pow_succ, hn.neg_one_pow]
      ring
    · have hev : Even (n + 1) := by rwa [Nat.even_add_one]
      have hodd : Odd n := Nat.not_even_iff_odd.mp hn
      rw [if_neg hn, if_pos hev, pow_succ, hodd.neg_one_pow]
      ring

theorem bAF_prime_pow_nonneg {p : ℕ} (hp : p.Prime) (a : ℕ) : 0 ≤ bAF (p ^ a) := by
  rcases prime_cases_mod_four hp with rfl | h1 | h3
  · rw [bAF_two_pow]; norm_num
  · rw [bAF_prime_pow_one_mod_four hp h1]; positivity
  · rw [bAF_prime_pow_three_mod_four hp h3]; split_ifs <;> norm_num

theorem bAF_nonneg (n : ℕ) : 0 ≤ bAF n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [bAF_isMultiplicative.multiplicative_factorization _ hn]
    refine Finset.prod_nonneg fun p hp => ?_
    exact bAF_prime_pow_nonneg (Nat.prime_of_mem_primeFactors (by simpa using hp)) _

end CharacterAndB

section TwistedDivisorLower

/-- Reciprocal arithmetic function `n ↦ 1 / n` into `ℝ`. -/
noncomputable def recipAF : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ)⁻¹, by simp⟩

/-- Twisted reciprocal arithmetic function `n ↦ χ₄(n) / n` into `ℝ`. -/
noncomputable def chiRecipAF : ArithmeticFunction ℝ :=
  ⟨fun n => (chi4AF n : ℝ) / (n : ℝ), by simp⟩

@[simp]
theorem recipAF_apply (n : ℕ) : recipAF n = (n : ℝ)⁻¹ := rfl

@[simp]
theorem chiRecipAF_apply (n : ℕ) : chiRecipAF n = (chi4AF n : ℝ) / (n : ℝ) := rfl

theorem recipAF_mul_chiRecipAF_apply (m : ℕ) :
    (recipAF * chiRecipAF) m = (bAF m : ℝ) / (m : ℝ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [ArithmeticFunction.mul_apply, bAF_apply, Int.cast_sum, Finset.sum_div]
    rw [← Nat.sum_divisorsAntidiagonal' (f := fun _ d => (chi4AF d : ℝ) / (m : ℝ))]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx1 : x.1 ≠ 0 := left_ne_zero_of_mul (hprod.symm ▸ hm)
    have hx2 : x.2 ≠ 0 := right_ne_zero_of_mul (hprod.symm ▸ hm)
    have hmul : ((x.1 : ℝ) * (x.2 : ℝ)) = (m : ℝ) := by exact_mod_cast hprod
    simp only [recipAF_apply, chiRecipAF_apply]
    rw [← hmul]
    field_simp [Nat.cast_ne_zero.mpr hx1, Nat.cast_ne_zero.mpr hx2]

private theorem chiRecipAF_four (k : ℕ) : chiRecipAF (4 * k) = 0 := by
  rw [chiRecipAF_apply, chi4AF_apply, ZMod.χ₄_nat_eq_if_mod_four]
  norm_num [Nat.mul_mod]

private theorem chiRecipAF_four_one (k : ℕ) :
    chiRecipAF (4 * k + 1) = 1 / (4 * (k : ℝ) + 1) := by
  rw [chiRecipAF_apply, chi4AF_of_mod_four_eq_one (by omega)]
  push_cast
  ring

private theorem chiRecipAF_four_two (k : ℕ) : chiRecipAF (4 * k + 2) = 0 := by
  rw [chiRecipAF_apply, chi4AF_apply, ZMod.χ₄_nat_eq_if_mod_four]
  norm_num [Nat.add_mod, Nat.mul_mod]

private theorem chiRecipAF_four_three (k : ℕ) :
    chiRecipAF (4 * k + 3) = -(1 / (4 * (k : ℝ) + 3)) := by
  rw [chiRecipAF_apply, chi4AF_of_mod_four_eq_three (by omega)]
  push_cast
  ring

private theorem sum_chiRecipAF_blocks (k : ℕ) :
    (2 / 3 : ℝ) ≤ ∑ d ∈ Finset.Ioc 0 (4 * (k + 1)), chiRecipAF d := by
  induction k with
  | zero =>
    have hset : Finset.Ioc 0 4 = {1, 2, 3, 4} := by decide
    rw [show 4 * (0 + 1) = 4 by omega, hset]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
      OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
    have h1 := chiRecipAF_four_one 0
    have h2 := chiRecipAF_four_two 0
    have h3 := chiRecipAF_four_three 0
    have h4 := chiRecipAF_four 1
    norm_num at h1 h2 h3 h4 ⊢
  | succ k ih =>
    let b := k + 1
    have hstep : 4 * (b + 1) = 4 * b + 4 := by omega
    change (2 / 3 : ℝ) ≤ ∑ d ∈ Finset.Ioc 0 (4 * (b + 1)), chiRecipAF d
    rw [hstep, Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega),
      Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]
    have h4 : chiRecipAF (4 * b + 4) = 0 := by
      simpa [Nat.mul_add] using chiRecipAF_four (b + 1)
    rw [chiRecipAF_four_one b, chiRecipAF_four_two b, chiRecipAF_four_three b, h4]
    have hle := one_div_le_one_div_of_le (show (0 : ℝ) < 4 * (b : ℝ) + 1 by positivity)
      (show (4 * (b : ℝ) + 1) ≤ 4 * (b : ℝ) + 3 by linarith)
    change (2 / 3 : ℝ) ≤ ∑ d ∈ Finset.Ioc 0 (4 * b), chiRecipAF d at ih
    linarith

/-- Every nonempty partial sum `∑_{d=1}^M χ₄(d)/d` is at least `2/3`. -/
theorem sum_chiRecipAF_ge_two_thirds {M : ℕ} (hM : 1 ≤ M) :
    (2 / 3 : ℝ) ≤ ∑ d ∈ Finset.Ioc 0 M, chiRecipAF d := by
  by_cases hlt : M < 4
  · interval_cases M
    · have hset : Finset.Ioc 0 1 = {1} := by decide
      rw [hset, Finset.sum_singleton]
      have h1 := chiRecipAF_four_one 0
      norm_num at h1 ⊢
    · have hset : Finset.Ioc 0 2 = {1, 2} := by decide
      rw [hset, Finset.sum_pair (by decide)]
      have h1 := chiRecipAF_four_one 0
      have h2 := chiRecipAF_four_two 0
      norm_num at h1 h2 ⊢
    · have hset : Finset.Ioc 0 3 = {1, 2, 3} := by decide
      rw [hset]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
        OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
      have h1 := chiRecipAF_four_one 0
      have h2 := chiRecipAF_four_two 0
      have h3 := chiRecipAF_four_three 0
      norm_num at h1 h2 h3 ⊢
  · let q := M / 4
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hblock : (2 / 3 : ℝ) ≤ ∑ d ∈ Finset.Ioc 0 (4 * q), chiRecipAF d := by
      have h := sum_chiRecipAF_blocks (q - 1)
      rwa [Nat.sub_add_cancel hq] at h
    have hmod : M = 4 * q ∨ M = 4 * q + 1 ∨ M = 4 * q + 2 ∨ M = 4 * q + 3 := by
      dsimp [q]; omega
    rcases hmod with h0 | h1 | h2 | h3
    · rw [h0]; exact hblock
    · rw [h1, Finset.sum_Ioc_succ_top (by omega), chiRecipAF_four_one q]
      have : (0 : ℝ) ≤ 1 / (4 * (q : ℝ) + 1) := by positivity
      linarith
    · rw [h2, Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega),
        chiRecipAF_four_one q, chiRecipAF_four_two q]
      have : (0 : ℝ) ≤ 1 / (4 * (q : ℝ) + 1) := by positivity
      linarith
    · have hnext := sum_chiRecipAF_blocks q
      have hstep : 4 * (q + 1) = (4 * q + 3) + 1 := by omega
      rw [hstep, Finset.sum_Ioc_succ_top (by omega)] at hnext
      have h4 : chiRecipAF ((4 * q + 3) + 1) = 0 := by
        simpa [hstep] using chiRecipAF_four (q + 1)
      rw [h3]
      linarith

/-- Lower bound `∑_{m=1}^N b(m)/m ≥ (2/3) H_N`. -/
theorem sum_bAF_div_ge_harmonic (N : ℕ) :
    (2 / 3 : ℝ) * (harmonic N : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ) := by
  have hconv : ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ) =
      ∑ e ∈ Finset.Ioc 0 N, recipAF e * ∑ d ∈ Finset.Ioc 0 (N / e), chiRecipAF d := by
    rw [← ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    refine Finset.sum_congr rfl fun m _ => (recipAF_mul_chiRecipAF_apply m).symm
  rw [hconv, harmonic_eq_sum_Icc]
  push_cast
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  obtain ⟨he0, heN⟩ := Finset.mem_Ioc.mp he
  rw [recipAF_apply, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (sum_chiRecipAF_ge_two_thirds (Nat.div_pos heN he0)) (by positivity)

/-- Lower bound `∑_{m=1}^N b(m)/m ≥ (2/3) log(N + 1)`. -/
theorem sum_bAF_div_ge_log (N : ℕ) :
    (2 / 3 : ℝ) * Real.log (N + 1 : ℕ) ≤ ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ) := by
  refine le_trans ?_ (sum_bAF_div_ge_harmonic N)
  exact mul_le_mul_of_nonneg_left (log_add_one_le_harmonic N) (by norm_num)

end TwistedDivisorLower

section SquarefreeComparison

/-- Admissible squarefree integers with no prime factor `p ≡ 3 (mod 4)`. -/
def IsGood (d : ℕ) : Prop :=
  Squarefree d ∧ ∀ p ∈ d.primeFactors, p % 4 ≠ 3

theorem isGood_iff_two_or_one_mod_four {d : ℕ} :
    IsGood d ↔ Squarefree d ∧ ∀ p ∈ d.primeFactors, p = 2 ∨ p % 4 = 1 := by
  constructor
  · rintro ⟨hsq, h⟩
    refine ⟨hsq, fun p hp => ?_⟩
    rcases prime_cases_mod_four (Nat.prime_of_mem_primeFactors hp) with rfl | h1 | h3
    · exact Or.inl rfl
    · exact Or.inr h1
    · exact absurd h3 (h p hp)
  · rintro ⟨hsq, h⟩
    refine ⟨hsq, fun p hp h3 => ?_⟩
    rcases h p hp with rfl | h1 <;> omega

open scoped Classical in
/-- The finite set `𝒟₀(N)` of squarefree `1 ≤ d ≤ N` with no prime factor `≡ 3 (mod 4)`. -/
noncomputable def D0 (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter IsGood

theorem mem_D0 {N d : ℕ} : d ∈ D0 N ↔ (0 < d ∧ d ≤ N) ∧ IsGood d := by
  classical
  simp [D0]

/-- Simple multiplicative weight `w₀(d) = 2^{#\{p ∣ d : p ≡ 1 (mod 4)\}}`. -/
def w0 (d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, if p % 4 = 1 then 2 else 1

/-- Lower-bound sum `W₀(N) = ∑_{d ∈ 𝒟₀(N)} w₀(d) / d`. -/
noncomputable def W0 (N : ℕ) : ℝ :=
  ∑ d ∈ D0 N, (w0 d : ℝ) / (d : ℝ)

theorem bAF_mul_sq_eq_zero_of_not_isGood {d r : ℕ} (hd : Squarefree d) (hr : r ≠ 0)
    (hng : ¬ IsGood d) : bAF (d * r ^ 2) = 0 := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hm0 : d * r ^ 2 ≠ 0 := mul_ne_zero hd0 (pow_ne_zero 2 hr)
  have hex : ∃ p ∈ d.primeFactors, p % 4 = 3 := by
    by_contra! hall
    exact hng ⟨hd, hall⟩
  obtain ⟨p, hp_mem, hp3⟩ := hex
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp_mem
  have hfac_d : d.factorization p = 1 := Nat.factorization_eq_one_of_squarefree hd hp hpd
  have hfac_m : (d * r ^ 2).factorization p = 1 + 2 * r.factorization p := by
    rw [Nat.factorization_mul hd0 (pow_ne_zero 2 hr), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hfac_d]
  have hodd : ¬ Even ((d * r ^ 2).factorization p) := by
    rw [hfac_m, Nat.even_iff]; omega
  rw [bAF_isMultiplicative.multiplicative_factorization _ hm0]
  refine Finset.prod_eq_zero (i := p) ?_ ?_
  · rw [Nat.support_factorization, Nat.primeFactors_mul hd0 (pow_ne_zero 2 hr)]
    exact Finset.mem_union_left _ hp_mem
  · dsimp only
    rw [bAF_prime_pow_three_mod_four hp hp3, if_neg hodd]

/-- Prime-power comparison `b(d * r^2) ≤ w₀(d) * τ(r)^2` for squarefree `d` and `r ≠ 0`. -/
theorem bAF_mul_sq_le {d r : ℕ} (hd : Squarefree d) (hr : r ≠ 0) :
    bAF (d * r ^ 2) ≤ (w0 d : ℤ) * (r.divisors.card : ℤ) ^ 2 := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hm0 : d * r ^ 2 ≠ 0 := mul_ne_zero hd0 hr2
  let S := (d * r ^ 2).primeFactors
  have hd_sub : d.primeFactors ⊆ S := by
    intro p hp
    dsimp [S]
    rw [Nat.primeFactors_mul hd0 hr2]
    exact Finset.mem_union_left _ hp
  have hr_sub : r.primeFactors ⊆ S := by
    intro p hp
    dsimp [S]
    rw [Nat.primeFactors_mul hd0 hr2, Nat.primeFactors_pow r two_ne_zero]
    exact Finset.mem_union_right _ hp
  have hb_eq : bAF (d * r ^ 2) = ∏ p ∈ S, bAF (p ^ (d.factorization p + 2 * r.factorization p)) := by
    rw [bAF_isMultiplicative.multiplicative_factorization _ hm0]
    refine Finset.prod_congr (Nat.support_factorization _) fun p _ => ?_
    rw [Nat.factorization_mul hd0 hr2, Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul]
  have hw_eq : (w0 d : ℤ) =
      ∏ p ∈ S, if p ∈ d.primeFactors ∧ p % 4 = 1 then (2 : ℤ) else 1 := by
    rw [w0, Nat.cast_prod, ← Finset.prod_subset hd_sub]
    · refine Finset.prod_congr rfl fun p hp => ?_
      by_cases h1 : p % 4 = 1 <;> simp [hp, h1]
    · intro p _ hp
      simp [hp]
  have htau_eq : (r.divisors.card : ℤ) ^ 2 =
      ∏ p ∈ S, ((r.factorization p + 1 : ℤ) ^ 2) := by
    rw [Nat.card_divisors hr, Nat.cast_prod, ← Finset.prod_pow, ← Finset.prod_subset hr_sub]
    · refine Finset.prod_congr rfl fun p _ => by push_cast; rfl
    · intro p _ hp
      have hzero : r.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hp
      simp [hzero]
  rw [hb_eq, hw_eq, htau_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p hp => bAF_prime_pow_nonneg (Nat.prime_of_mem_primeFactors hp) _) ?_
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  set k : ℕ := r.factorization p
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg k
  have hk1 : (1 : ℤ) ≤ ((k : ℤ) + 1) ^ 2 := by nlinarith
  have he_le : d.factorization p ≤ 1 := hd.natFactorization_le_one p
  have hmem_iff : p ∈ d.primeFactors ↔ d.factorization p = 1 := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  rcases prime_cases_mod_four hp_prime with rfl | h1 | h3
  · rw [bAF_two_pow]
    simp [hk1]
  · by_cases hpd : p ∈ d.primeFactors
    · have he : d.factorization p = 1 := hmem_iff.mp hpd
      rw [he, bAF_prime_pow_one_mod_four hp_prime h1, if_pos ⟨hpd, h1⟩]
      push_cast
      nlinarith
    · have he : d.factorization p = 0 := by
        have := hmem_iff.not.mp hpd; omega
      rw [he, zero_add, bAF_prime_pow_one_mod_four hp_prime h1, if_neg (by simp [hpd])]
      push_cast
      nlinarith
  · have hnot1 : ¬ (p ∈ d.primeFactors ∧ p % 4 = 1) := fun h => by have := h.2; omega
    rw [bAF_prime_pow_three_mod_four hp_prime h3, if_neg hnot1]
    split_ifs <;> linarith

private theorem sum_inv_sq_le_two_sub (n : ℕ) :
    ∑ k ∈ Finset.Ioc 0 (n + 1), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / ((n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero =>
    have hset : Finset.Ioc 0 1 = {1} := by decide
    rw [hset, Finset.sum_singleton]
    norm_num
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have h1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have h2 : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have hdiff : (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 ≤
        1 / ((n + 1 : ℕ) : ℝ) - 1 / ((n + 2 : ℕ) : ℝ) := by
      have hcast : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [div_sub_div _ _ h1.ne' h2.ne', hcast]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- Elementary finite bound `∑_{k=1}^N 1 / k^2 ≤ 2`. -/
theorem sum_inv_sq_le_two (N : ℕ) :
    ∑ k ∈ Finset.Ioc 0 N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  cases N with
  | zero => simp
  | succ n =>
    have h := sum_inv_sq_le_two_sub n
    have hpos : (0 : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    linarith

private theorem sum_product_mul_eq {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → ℝ) (g : β → ℝ) :
    ∑ x ∈ s ×ˢ t, f x.1 * g x.2 = (∑ a ∈ s, f a) * (∑ b ∈ t, g b) := by
  rw [Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [← Finset.mul_sum]

/-- Elementary finite bound `∑_{r=1}^N τ(r)^2 / r^2 ≤ 16`. -/
theorem sum_card_divisors_sq_div_sq_le (N : ℕ) :
    ∑ r ∈ Finset.Ioc 0 N, (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2 ≤ 16 := by
  let I := Finset.Ioc 0 N
  let T := I.sigma fun r => r.divisors ×ˢ r.divisors
  let Q := I ×ˢ (I ×ˢ (I ×ˢ I))
  let φ : (Σ _ : ℕ, ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ := fun x =>
    let r := x.1
    let u := x.2.1
    let v := x.2.2
    let g := u.gcd v
    (g, u / g, v / g, r / u.lcm v)
  have hprod : ∀ x ∈ T, (φ x).1 * (φ x).2.1 * (φ x).2.2.1 * (φ x).2.2.2 = x.1 := by
    intro x hx
    rcases x with ⟨r, u, v⟩
    simp only [T, Finset.mem_sigma, Finset.mem_product, Nat.mem_divisors] at hx
    rcases hx with ⟨hrI, ⟨hu, hr0⟩, ⟨hv, _⟩⟩
    have hu0 : 0 < u := Nat.pos_of_dvd_of_pos hu (Finset.mem_Ioc.mp hrI).1
    have hv0 : 0 < v := Nat.pos_of_dvd_of_pos hv (Finset.mem_Ioc.mp hrI).1
    have hg0 : 0 < u.gcd v := Nat.gcd_pos_of_pos_left v hu0
    have hga : u.gcd v * (u / u.gcd v) = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
    have hgb : u.gcd v * (v / u.gcd v) = v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
    have hlcm : u.gcd v * (u / u.gcd v) * (v / u.gcd v) = u.lcm v := by
      apply Nat.eq_of_mul_eq_mul_left hg0
      calc
        u.gcd v * (u.gcd v * (u / u.gcd v) * (v / u.gcd v))
            = (u.gcd v * (u / u.gcd v)) * (u.gcd v * (v / u.gcd v)) := by ring
        _ = u * v := by rw [hga, hgb]
        _ = u.gcd v * u.lcm v := (Nat.gcd_mul_lcm u v).symm
    dsimp [φ]
    rw [hlcm, Nat.mul_div_cancel' (Nat.lcm_dvd hu hv)]
  have hmaps : ∀ x ∈ T, φ x ∈ Q := by
    intro x hx
    have hp := hprod x hx
    have hrI : x.1 ∈ I := (Finset.mem_sigma.mp hx).1
    obtain ⟨hr0, hrN⟩ := Finset.mem_Ioc.mp hrI
    rcases hφ : φ x with ⟨a, b, c, d⟩
    rw [hφ] at hp
    have habcd_pos : 0 < a * b * c * d := hp.symm ▸ hr0
    have ha0 : 0 < a := by
      by_contra h; push Not at h; simp [Nat.le_zero.mp h] at habcd_pos
    have hb0 : 0 < b := by
      by_contra h; push Not at h; simp [Nat.le_zero.mp h] at habcd_pos
    have hc0 : 0 < c := by
      by_contra h; push Not at h; simp [Nat.le_zero.mp h] at habcd_pos
    have hd0 : 0 < d := by
      by_contra h; push Not at h; simp [Nat.le_zero.mp h] at habcd_pos
    have haN : a ≤ N := (Nat.le_of_dvd hr0 ⟨b * c * d, by linarith⟩).trans hrN
    have hbN : b ≤ N := (Nat.le_of_dvd hr0 ⟨a * c * d, by linarith⟩).trans hrN
    have hcN : c ≤ N := (Nat.le_of_dvd hr0 ⟨a * b * d, by linarith⟩).trans hrN
    have hdN : d ≤ N := (Nat.le_of_dvd hr0 ⟨a * b * c, by linarith⟩).trans hrN
    simp only [Q, I, Finset.mem_product, Finset.mem_Ioc]
    exact ⟨⟨ha0, haN⟩, ⟨hb0, hbN⟩, ⟨hc0, hcN⟩, ⟨hd0, hdN⟩⟩
  have hinj : ∀ x ∈ T, ∀ y ∈ T, φ x = φ y → x = y := by
    intro x hx y hy hxy
    have hpx := hprod x hx
    have hpy := hprod y hy
    have hrx : x.1 = y.1 := by rw [← hpx, hxy, hpy]
    have hux : x.2.1 = y.2.1 := by
      have h1 : (φ x).1 * (φ x).2.1 = x.2.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have h2 : (φ y).1 * (φ y).2.1 = y.2.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      rw [← h1, hxy, h2]
    have hvx : x.2.2 = y.2.2 := by
      have h1 : (φ x).1 * (φ x).2.2.1 = x.2.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have h2 : (φ y).1 * (φ y).2.2.1 = y.2.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      rw [← h1, hxy, h2]
    rcases x with ⟨rx, ux, vx⟩
    rcases y with ⟨ry, uy, vy⟩
    dsimp at hrx hux hvx
    subst hrx; subst hux; subst hvx; rfl
  let f1 : ℕ → ℝ := fun k => (1 : ℝ) / (k : ℝ) ^ 2
  let f2 : ℕ × ℕ → ℝ := fun q => f1 q.1 * f1 q.2
  let f3 : ℕ × ℕ × ℕ → ℝ := fun q => f1 q.1 * f2 q.2
  let F : ℕ × ℕ × ℕ × ℕ → ℝ := fun q => f1 q.1 * f3 q.2
  have hsum_lhs :
      ∑ r ∈ I, (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2 = ∑ x ∈ T, F (φ x) := by
    calc
      ∑ r ∈ I, (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2
          = ∑ r ∈ I, ∑ _ ∈ r.divisors ×ˢ r.divisors, (1 : ℝ) / (r : ℝ) ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul, Nat.cast_mul, ← sq,
          mul_one_div]
      _ = ∑ x ∈ T, (1 : ℝ) / (x.1 : ℝ) ^ 2 := by
        symm
        exact Finset.sum_sigma I (fun r => r.divisors ×ˢ r.divisors) (fun x => (1 : ℝ) / (x.1 : ℝ) ^ 2)
      _ = ∑ x ∈ T, F (φ x) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hcast : ((x.1 : ℝ)) =
            ((φ x).1 : ℝ) * ((φ x).2.1 : ℝ) * ((φ x).2.2.1 : ℝ) * ((φ x).2.2.2 : ℝ) := by
          exact_mod_cast (hprod x hx).symm
        dsimp [F, f3, f2, f1]
        rw [hcast]
        ring
  have hsum_img : ∑ x ∈ T, F (φ x) ≤ ∑ q ∈ Q, F q := by
    rw [← Finset.sum_image (f := F) (g := φ) (by intro x hx y hy h; exact hinj x hx y hy h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => by dsimp [F, f3, f2, f1]; positivity)
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
    exact hmaps x hx
  have hsum_rhs : ∑ q ∈ Q, F q = (∑ k ∈ I, f1 k) ^ 4 := by
    have h2 : ∑ q ∈ I ×ˢ I, f2 q = (∑ k ∈ I, f1 k) * (∑ k ∈ I, f1 k) :=
      sum_product_mul_eq I I f1 f1
    have h3 : ∑ q ∈ I ×ˢ (I ×ˢ I), f3 q = (∑ k ∈ I, f1 k) * ∑ q ∈ I ×ˢ I, f2 q :=
      sum_product_mul_eq I (I ×ˢ I) f1 f2
    have h4 : ∑ q ∈ Q, F q = (∑ k ∈ I, f1 k) * ∑ q ∈ I ×ˢ (I ×ˢ I), f3 q :=
      sum_product_mul_eq I (I ×ˢ (I ×ˢ I)) f1 f3
    rw [h4, h3, h2]
    ring
  calc
    ∑ r ∈ I, (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2
        = ∑ x ∈ T, F (φ x) := hsum_lhs
    _ ≤ ∑ q ∈ Q, F q := hsum_img
    _ = (∑ k ∈ I, f1 k) ^ 4 := hsum_rhs
    _ ≤ (2 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => by positivity)
        (sum_inv_sq_le_two N) 4
    _ = 16 := by norm_num

/-- Upper bound `∑_{m=1}^N b(m)/m ≤ W₀(N) * ∑_{r=1}^N τ(r)^2 / r^2`. -/
theorem sum_bAF_div_le_W0_mul (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ) ≤
      W0 N * ∑ r ∈ Finset.Ioc 0 N, (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
  classical
  let sqPart : ℕ → ℕ × ℕ := fun m =>
    if hm : 0 < m then
      let d := Classical.choose (Nat.sq_mul_squarefree_of_pos hm)
      let r := Classical.choose (Classical.choose_spec (Nat.sq_mul_squarefree_of_pos hm))
      (d, r)
    else (0, 0)
  have hsqPart : ∀ m, 0 < m →
      0 < (sqPart m).1 ∧ 0 < (sqPart m).2 ∧
      (sqPart m).1 * (sqPart m).2 ^ 2 = m ∧ Squarefree (sqPart m).1 := by
    intro m hm
    dsimp only [sqPart]
    rw [dif_pos hm]
    have hspec := Classical.choose_spec (Classical.choose_spec (Nat.sq_mul_squarefree_of_pos hm))
    exact ⟨hspec.1, hspec.2.1, by rw [mul_comm]; exact hspec.2.2.1, hspec.2.2.2⟩
  let A := (Finset.Ioc 0 N).filter fun m => IsGood (sqPart m).1
  let H : ℕ × ℕ → ℝ := fun p =>
    ((w0 p.1 : ℝ) / (p.1 : ℝ)) * ((p.2.divisors.card : ℝ) ^ 2 / (p.2 : ℝ) ^ 2)
  have hfilter : ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ) =
      ∑ m ∈ A, (bAF m : ℝ) / (m : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : 0 < m := (Finset.mem_Ioc.mp hm).1
    obtain ⟨_, hr0, hprod, hsq⟩ := hsqPart m hm0
    by_cases hg : IsGood (sqPart m).1
    · rw [if_pos hg]
    · rw [if_neg hg, ← hprod, bAF_mul_sq_eq_zero_of_not_isGood hsq hr0.ne' hg]
      simp
  have hpoint : ∑ m ∈ A, (bAF m : ℝ) / (m : ℝ) ≤ ∑ m ∈ A, H (sqPart m) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm0 : 0 < m := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
    set d := (sqPart m).1
    set r := (sqPart m).2
    obtain ⟨_, hr0, hprod, hsq⟩ := hsqPart m hm0
    have hprod' : d * r ^ 2 = m := hprod
    have hle : (bAF m : ℝ) ≤ (w0 d : ℝ) * (r.divisors.card : ℝ) ^ 2 := by
      rw [← hprod']
      exact_mod_cast bAF_mul_sq_le hsq hr0.ne'
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    have hcast : (m : ℝ) = (d : ℝ) * (r : ℝ) ^ 2 := by
      exact_mod_cast hprod'.symm
    change (bAF m : ℝ) / (m : ℝ) ≤ ((w0 d : ℝ) / (d : ℝ)) * ((r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2)
    rw [div_mul_div_comm, ← hcast]
    exact div_le_div_of_nonneg_right hle hm_pos.le
  have hinj : ∀ m₁ ∈ A, ∀ m₂ ∈ A, sqPart m₁ = sqPart m₂ → m₁ = m₂ := by
    intro m₁ hm₁ m₂ hm₂ heq
    have h1 := (hsqPart m₁ (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm₁).1).1).2.2.1
    have h2 := (hsqPart m₂ (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm₂).1).1).2.2.1
    rw [← h1, heq, h2]
  have hmaps : ∀ m ∈ A, sqPart m ∈ D0 N ×ˢ Finset.Ioc 0 N := by
    intro m hm
    obtain ⟨hmI, hgood⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hmI
    obtain ⟨hd0, hr0, hprod, _⟩ := hsqPart m hm0
    have hdN : (sqPart m).1 ≤ N :=
      (Nat.le_of_dvd hm0 ⟨(sqPart m).2 ^ 2, hprod.symm⟩).trans hmN
    have hrN : (sqPart m).2 ≤ N := by
      have hr2_dvd : (sqPart m).2 ^ 2 ∣ m := ⟨(sqPart m).1, by rw [mul_comm]; exact hprod.symm⟩
      have hr_dvd : (sqPart m).2 ∣ m := (dvd_pow_self _ two_ne_zero).trans hr2_dvd
      exact (Nat.le_of_dvd hm0 hr_dvd).trans hmN
    rw [Finset.mem_product, mem_D0, Finset.mem_Ioc]
    exact ⟨⟨⟨hd0, hdN⟩, hgood⟩, ⟨hr0, hrN⟩⟩
  have himg : ∑ m ∈ A, H (sqPart m) ≤ ∑ p ∈ D0 N ×ˢ Finset.Ioc 0 N, H p := by
    rw [← Finset.sum_image (f := H) (g := sqPart) (by intro x hx y hy h; exact hinj x hx y hy h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by dsimp [H]; positivity)
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨m, hm, rfl⟩
    exact hmaps m hm
  have hprod_sum : ∑ p ∈ D0 N ×ˢ Finset.Ioc 0 N, H p =
      W0 N * ∑ r ∈ Finset.Ioc 0 N, (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
    rw [W0]
    exact sum_product_mul_eq (D0 N) (Finset.Ioc 0 N)
      (fun d => (w0 d : ℝ) / (d : ℝ))
      (fun r => (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2)
  calc
    ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ)
        = ∑ m ∈ A, (bAF m : ℝ) / (m : ℝ) := hfilter
    _ ≤ ∑ m ∈ A, H (sqPart m) := hpoint
    _ ≤ ∑ p ∈ D0 N ×ˢ Finset.Ioc 0 N, H p := himg
    _ = W0 N * ∑ r ∈ Finset.Ioc 0 N, (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2 := hprod_sum

/-- Key density comparison `∑_{m=1}^N b(m)/m ≤ 16 * W₀(N)`. -/
theorem sum_bAF_div_le_sixteen_mul_W0 (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ) ≤ 16 * W0 N := by
  have hW0 : 0 ≤ W0 N := Finset.sum_nonneg fun d _ => by positivity
  calc
    ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ)
        ≤ W0 N * ∑ r ∈ Finset.Ioc 0 N, (r.divisors.card : ℝ) ^ 2 / (r : ℝ) ^ 2 :=
      sum_bAF_div_le_W0_mul N
    _ ≤ W0 N * 16 := mul_le_mul_of_nonneg_left (sum_card_divisors_sq_div_sq_le N) hW0
    _ = 16 * W0 N := mul_comm _ _

/-- Equivalent form in terms of `recipAF * chiRecipAF` for direct integration. -/
theorem sum_recip_mul_chi_le_sixteen_mul_W0 (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, (recipAF * chiRecipAF) m ≤ 16 * W0 N := by
  have h : ∑ m ∈ Finset.Ioc 0 N, (recipAF * chiRecipAF) m =
      ∑ m ∈ Finset.Ioc 0 N, (bAF m : ℝ) / (m : ℝ) :=
    Finset.sum_congr rfl fun m _ => recipAF_mul_chiRecipAF_apply m
  rw [h]
  exact sum_bAF_div_le_sixteen_mul_W0 N

theorem W0_ge_harmonic (N : ℕ) :
    (1 / 24 : ℝ) * (harmonic N : ℝ) ≤ W0 N := by
  have h1 := sum_bAF_div_ge_harmonic N
  have h2 := sum_bAF_div_le_sixteen_mul_W0 N
  linarith

theorem W0_ge_log (N : ℕ) :
    (1 / 24 : ℝ) * Real.log (N + 1 : ℕ) ≤ W0 N := by
  have h1 := sum_bAF_div_ge_log N
  have h2 := sum_bAF_div_le_sixteen_mul_W0 N
  linarith

end SquarefreeComparison

section G0LowerBound

/-- Prime values of the model Selberg weight `g₀` from §3.3. -/
noncomputable def g0Prime (p : ℕ) : ℝ :=
  if p = 2 then 1 else if p % 4 = 1 then 2 / ((p : ℝ) - 2) else 0

/-- The multiplicative model weight `g₀(d) = ∏_{p ∣ d, p=2} 1 · ∏_{p ∣ d, p≡1(4)} 2/(p-2)`. -/
noncomputable def g0 : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors g0Prime

/-- The model Selberg bounding sum `G₀(N) = ∑_{d ∈ 𝒟₀(N)} g₀(d)`. -/
noncomputable def G0 (N : ℕ) : ℝ :=
  ∑ d ∈ D0 N, g0 d

theorem g0_isMultiplicative : g0.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors g0Prime

theorem w0_div_le_g0 {d : ℕ} (hd : IsGood d) : (w0 d : ℝ) / (d : ℝ) ≤ g0 d := by
  obtain ⟨hsq, hgood⟩ := isGood_iff_two_or_one_mod_four.mp hd
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hd_prod : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  rw [g0, ArithmeticFunction.prodPrimeFactors_apply hd0, w0, Nat.cast_prod, hd_prod,
    ← Finset.prod_div_distrib]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  rcases hgood p hp with rfl | h1
  · simp [g0Prime]
    norm_num
  · have hp5 : 5 ≤ p := by
      have := hp_prime.two_le
      omega
    have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by
      have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
      linarith
    have hp_ne2 : p ≠ 2 := by omega
    simp only [h1, ite_true, g0Prime, hp_ne2, ite_false]
    norm_num
    exact div_le_div_of_nonneg_left (by norm_num) hp2_pos (by linarith)

theorem W0_le_G0 (N : ℕ) : W0 N ≤ G0 N := by
  refine Finset.sum_le_sum fun d hd => ?_
  exact w0_div_le_g0 (mem_D0.mp hd).2

/-- Lemma 3.4 (improved, without additive constant): `G₀(N) ≥ (1/24) H_N`. -/
theorem G0_ge_harmonic (N : ℕ) :
    (1 / 24 : ℝ) * (harmonic N : ℝ) ≤ G0 N :=
  (W0_ge_harmonic N).trans (W0_le_G0 N)

/-- Lemma 3.4 (improved, without additive constant): `G₀(N) ≥ (1/24) log(N + 1)`. -/
theorem G0_ge_log (N : ℕ) :
    (1 / 24 : ℝ) * Real.log (N + 1 : ℕ) ≤ G0 N :=
  (W0_ge_log N).trans (W0_le_G0 N)

/-- Real-cutoff version of Lemma 3.4: for every `y ≥ 1`, `G₀(⌊y⌋) ≥ (1/24) log y`. -/
theorem G0_floor_ge_log {y : ℝ} (hy : 1 ≤ y) :
    (1 / 24 : ℝ) * Real.log y ≤ G0 ⌊y⌋₊ := by
  refine le_trans ?_ (G0_ge_log ⌊y⌋₊)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Real.log_le_log (by linarith)
  exact_mod_cast (Nat.lt_floor_add_one y).le

end G0LowerBound

section FactoringAndSelbergSieve

private theorem coprime_of_disjoint_primeFactors {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hdisj : Disjoint a.primeFactors b.primeFactors) : a.Coprime b :=
  Nat.coprime_of_dvd fun _ hp hpa hpb =>
    Finset.disjoint_left.mp hdisj
      (Nat.mem_primeFactors.mpr ⟨hp, hpa, ha⟩)
      (Nat.mem_primeFactors.mpr ⟨hp, hpb, hb⟩)

private theorem squarefree_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : p ≠ q := fun h => hps (h ▸ hq)
      exact (Nat.coprime_primes hp (hs q hq)).mpr hne
    exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ih hs⟩

private theorem prod_primes_dvd_of_dvd {S : Finset ℕ} {P : ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ P) : (∏ p ∈ S, p) ∣ P := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hp (hs q hq)).mpr (fun h => hps (h ▸ hq))
    exact hcop.mul_dvd_of_dvd_of_dvd
      (hdvd p (Finset.mem_insert_self p s))
      (ih hs (fun q hq => hdvd q (Finset.mem_insert_of_mem hq)))

/-- Sum of a multiplicative function over divisors of `M = ∏_{p ∈ S} p` exceeds
`(∏_{p ∈ S} (1 - 1/p))⁻¹` when `f(p) ≥ 1 / (p - 1)` for every `p ∈ S`. -/
theorem sum_divisors_prod_primes_ge {S : Finset ℕ} {f : ArithmeticFunction ℝ}
    (hS : ∀ p ∈ S, p.Prime) (hf_mult : f.IsMultiplicative)
    (hf_inert : ∀ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ≤ f p) :
    (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ ≤ ∑ d ∈ (∏ p ∈ S, p).divisors, f d := by
  let M := ∏ p ∈ S, p
  have hM_sq : Squarefree M := squarefree_prod_primes hS
  have hM_pf : M.primeFactors = S := Nat.primeFactors_prod hS
  have hsum : ∑ d ∈ M.divisors, f d = ∏ p ∈ S, (1 + f p) := by
    have hmul : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * f) M =
        ∑ d ∈ M.divisors, f d := ArithmeticFunction.coe_zeta_mul_apply
    rw [← hmul,
      ← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree
        ArithmeticFunction.isMultiplicative_zeta.natCast hf_mult hM_sq,
      ArithmeticFunction.prodPrimeFactors_apply hM_sq.ne_zero, hM_pf]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : p ≠ 0 := (hS p hp).ne_zero
    simp [hp0]
  rw [hsum, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod ?_ fun p hp => ?_
  · intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
    have h1 : 0 < 1 - 1 / (p : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
    positivity
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have heq : (1 - 1 / (p : ℝ))⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
      field_simp [hp0, hp1]
      ring
    rw [heq]
    linarith [hf_inert p hp]

/-- Generic Lemma 3.3: factoring out `M = ∏_{p ∈ S} p` for any multiplicative weight `f`
dominating `1/(p-1)` on `S` and `w₀(d)/d` on `𝒟₀(z / M)`. -/
theorem sum_multiplicative_ge_factor_W0 {S F : Finset ℕ} {f : ArithmeticFunction ℝ} {z : ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p % 4 = 3)
    (hf_mult : f.IsMultiplicative)
    (hf_nonneg : ∀ d ∈ F, 0 ≤ f d)
    (hf_inert : ∀ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ≤ f p)
    (hf_good : ∀ d ∈ D0 (z / (∏ p ∈ S, p)), (w0 d : ℝ) / (d : ℝ) ≤ f d)
    (hmem : ∀ d₁ ∈ (∏ p ∈ S, p).divisors, ∀ d₂ ∈ D0 (z / (∏ p ∈ S, p)), d₁ * d₂ ∈ F) :
    (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ * W0 (z / (∏ p ∈ S, p)) ≤ ∑ d ∈ F, f d := by
  let M := ∏ p ∈ S, p
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hM_sq : Squarefree M := squarefree_prod_primes hS_prime
  have hM_pf : M.primeFactors = S := Nat.primeFactors_prod hS_prime
  have hcop_M : ∀ d₂ ∈ D0 (z / M), M.Coprime d₂ := by
    intro d₂ hd₂
    have hgood := (mem_D0.mp hd₂).2
    have hdisj : Disjoint M.primeFactors d₂.primeFactors := by
      rw [Finset.disjoint_left]
      intro p hpM hpd2
      rw [hM_pf] at hpM
      exact hgood.2 p hpd2 (hS p hpM).2
    exact coprime_of_disjoint_primeFactors hM_sq.ne_zero hgood.1.ne_zero hdisj
  have hcop : ∀ d₁ ∈ M.divisors, ∀ d₂ ∈ D0 (z / M), d₁.Coprime d₂ := by
    intro d₁ hd₁ d₂ hd₂
    exact (hcop_M d₂ hd₂).coprime_dvd_left (Nat.dvd_of_mem_divisors hd₁)
  have hinj : ∀ x ∈ M.divisors ×ˢ D0 (z / M), ∀ y ∈ M.divisors ×ˢ D0 (z / M),
      x.1 * x.2 = y.1 * y.2 → x = y := by
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    have hdx : Nat.gcd (x.1 * x.2) M = x.1 := by
      rw [(hcop_M x.2 hx2).symm.gcd_mul_right_cancel x.1,
        Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hx1)]
    have hdy : Nat.gcd (y.1 * y.2) M = y.1 := by
      rw [(hcop_M y.2 hy2).symm.gcd_mul_right_cancel y.1,
        Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hy1)]
    have h1 : x.1 = y.1 := by rw [← hdx, hxy, hdy]
    have hx1_pos : 0 < x.1 := Nat.pos_of_mem_divisors hx1
    have h2 : x.2 = y.2 := Nat.eq_of_mul_eq_mul_left hx1_pos (by simpa [h1] using hxy)
    exact Prod.ext h1 h2
  have hfactor1 := sum_divisors_prod_primes_ge hS_prime hf_mult hf_inert
  have hfactor2 : W0 (z / M) ≤ ∑ d₂ ∈ D0 (z / M), f d₂ := Finset.sum_le_sum hf_good
  have hprod_nonneg : 0 ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [inv_nonneg]
    refine Finset.prod_nonneg fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS_prime p hp).two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hW0_nonneg : 0 ≤ W0 (z / M) := Finset.sum_nonneg fun d _ => by positivity
  calc
    (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ * W0 (z / M)
        ≤ (∑ d₁ ∈ M.divisors, f d₁) * (∑ d₂ ∈ D0 (z / M), f d₂) :=
      mul_le_mul hfactor1 hfactor2 hW0_nonneg (hprod_nonneg.trans hfactor1)
    _ = ∑ x ∈ M.divisors ×ˢ D0 (z / M), f x.1 * f x.2 :=
      (sum_product_mul_eq M.divisors (D0 (z / M)) f f).symm
    _ = ∑ x ∈ M.divisors ×ˢ D0 (z / M), f (x.1 * x.2) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
      exact (hf_mult.map_mul_of_coprime (hcop x.1 hx1 x.2 hx2)).symm
    _ = ∑ d ∈ (M.divisors ×ˢ D0 (z / M)).image (fun x => x.1 * x.2), f d := by
      rw [Finset.sum_image (by intro x hx y hy h; exact hinj x hx y hy h)]
    _ ≤ ∑ d ∈ F, f d := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d hd _ => hf_nonneg d hd)
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨⟨d₁, d₂⟩, hx, rfl⟩
      obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
      exact hmem d₁ hx1 d₂ hx2

/-- Pointwise comparison `a / (1 - a) ≤ B.selbergTerms p` when `a ≤ B.nu p < 1`. -/
theorem selbergTerms_prime_ge_of_nu_ge (B : BoundingSieve) {p : ℕ} {a : ℝ}
    (hp : p.Prime) (hpP : p ∣ B.prodPrimes) (ha : a ≤ B.nu p) (ha1 : a < 1) :
    a / (1 - a) ≤ B.selbergTerms p := by
  have hlt : B.nu p < 1 := B.nu_lt_one_of_prime p hp hpP
  rw [BoundingSieve.selbergTerms_apply, hp.primeFactors, Finset.prod_singleton,
    ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- On `𝒟₀`, if `B.nu 2 ≥ 1/2` and `B.nu p ≥ 2/p` for split primes `p ∣ B.prodPrimes`,
then `g₀(d) ≤ B.selbergTerms d`. -/
theorem g0_le_selbergTerms (B : BoundingSieve) {d : ℕ}
    (hd : IsGood d) (hdP : d ∣ B.prodPrimes)
    (hnu_two : 2 ∣ B.prodPrimes → (1 : ℝ) / 2 ≤ B.nu 2)
    (hnu_split : ∀ p, p.Prime → p % 4 = 1 → p ∣ B.prodPrimes → (2 : ℝ) / (p : ℝ) ≤ B.nu p) :
    g0 d ≤ B.selbergTerms d := by
  obtain ⟨hsq, hgood⟩ := isGood_iff_two_or_one_mod_four.mp hd
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hselb : B.selbergTerms d = ∏ p ∈ d.primeFactors, B.selbergTerms p := by
    rw [← B.selbergTerms_isMultiplicative.map_prod_of_subset_primeFactors d d.primeFactors subset_rfl,
      Nat.prod_primeFactors_of_squarefree hsq]
  rw [g0, ArithmeticFunction.prodPrimeFactors_apply hd0, hselb]
  refine Finset.prod_le_prod ?_ fun p hp => ?_
  · intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    rcases hgood p hp with rfl | h1
    · simp [g0Prime]
    · have hp5 : 5 ≤ p := by have := hp_prime.two_le; omega
      have : (0 : ℝ) < (p : ℝ) - 2 := by
        have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
        linarith
      simp only [g0Prime, show p ≠ 2 by omega, ite_false, h1, ite_true]
      positivity
  · have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpP : p ∣ B.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hdP
    rcases hgood p hp with rfl | h1
    · simp only [g0Prime, ite_true]
      have h := selbergTerms_prime_ge_of_nu_ge B Nat.prime_two hpP (hnu_two hpP) (by norm_num)
      norm_num at h
      exact h
    · have hp5 : 5 ≤ p := by have := hp_prime.two_le; omega
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
      have ha1 : (2 : ℝ) / (p : ℝ) < 1 := by
        rw [div_lt_one hp_pos]
        exact_mod_cast (by omega : 2 < p)
      have h := selbergTerms_prime_ge_of_nu_ge B hp_prime hpP (hnu_split p hp_prime h1 hpP) ha1
      have hsimp : ((2 : ℝ) / (p : ℝ)) / (1 - (2 : ℝ) / (p : ℝ)) = 2 / ((p : ℝ) - 2) := by
        have hp2 : (p : ℝ) - 2 ≠ 0 := by
          have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
          linarith
        field_simp [hp_pos.ne', hp2]
      rw [hsimp] at h
      simpa [g0Prime, show p ≠ 2 by omega, h1] using h

/-- Direct lower bound on the truncated Selberg denominator
`∑ m ∈ B.prodPrimes.divisors.filter (· ≤ z), B.selbergTerms m`
in terms of the inert-prime product over `S` and `log (z / M + 1)`.
This matches `A069004Sieve.denominator B z` definitionally. -/
theorem sum_selbergTerms_ge_log (B : BoundingSieve) (S : Finset ℕ) (z : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p % 4 = 3)
    (hP_inert : ∀ p ∈ S, p ∣ B.prodPrimes)
    (hP_two : 2 ≤ z / (∏ p ∈ S, p) → 2 ∣ B.prodPrimes)
    (hP_split : ∀ p, p.Prime → p % 4 = 1 → p ≤ z / (∏ p ∈ S, p) → p ∣ B.prodPrimes)
    (hnu_inert : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ B.nu p)
    (hnu_two : 2 ∣ B.prodPrimes → (1 : ℝ) / 2 ≤ B.nu 2)
    (hnu_split : ∀ p, p.Prime → p % 4 = 1 → p ∣ B.prodPrimes → (2 : ℝ) / (p : ℝ) ≤ B.nu p) :
    (1 / 24 : ℝ) * (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ *
        Real.log ((z / (∏ p ∈ S, p) + 1 : ℕ) : ℝ) ≤
      ∑ m ∈ B.prodPrimes.divisors.filter (· ≤ z), B.selbergTerms m := by
  let M := ∏ p ∈ S, p
  have hS_prime : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hM_sq : Squarefree M := squarefree_prod_primes hS_prime
  have hM_pos : 0 < M := Nat.pos_of_ne_zero hM_sq.ne_zero
  have hM_dvd : M ∣ B.prodPrimes := prod_primes_dvd_of_dvd hS_prime hP_inert
  have hd2_dvd : ∀ d₂ ∈ D0 (z / M), d₂ ∣ B.prodPrimes := by
    intro d₂ hd₂
    obtain ⟨⟨hd₂_pos, hd₂_le⟩, hd₂_good⟩ := mem_D0.mp hd₂
    obtain ⟨hsq, hgood⟩ := isGood_iff_two_or_one_mod_four.mp hd₂_good
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    refine prod_primes_dvd_of_dvd (fun p hp => Nat.prime_of_mem_primeFactors hp) fun p hp => ?_
    have hp_le : p ≤ z / M :=
      (Nat.le_of_dvd hd₂_pos (Nat.dvd_of_mem_primeFactors hp)).trans hd₂_le
    rcases hgood p hp with rfl | h1
    · exact hP_two hp_le
    · exact hP_split p (Nat.prime_of_mem_primeFactors hp) h1 hp_le
  have hselb_inert : ∀ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ≤ B.selbergTerms p := by
    intro p hp
    have hp_prime : p.Prime := (hS p hp).1
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
      linarith
    have ha1 : (1 : ℝ) / (p : ℝ) < 1 := by
      rw [div_lt_one hp_pos]
      exact_mod_cast hp_prime.one_lt
    have h := selbergTerms_prime_ge_of_nu_ge B hp_prime (hP_inert p hp) (hnu_inert p hp) ha1
    have hsimp : ((1 : ℝ) / (p : ℝ)) / (1 - (1 : ℝ) / (p : ℝ)) = 1 / ((p : ℝ) - 1) := by
      field_simp [hp_pos.ne', hp1]
    rwa [hsimp] at h
  have hstep := sum_multiplicative_ge_factor_W0
    (S := S) (F := B.prodPrimes.divisors.filter (· ≤ z)) (f := B.selbergTerms) (z := z)
    hS B.selbergTerms_isMultiplicative
    (fun d hd => (B.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)).le)
    hselb_inert
    (fun d₂ hd₂ => (w0_div_le_g0 (mem_D0.mp hd₂).2).trans
      (g0_le_selbergTerms B (mem_D0.mp hd₂).2 (hd2_dvd d₂ hd₂) hnu_two hnu_split))
    (fun d₁ hd₁ d₂ hd₂ => by
      have hd₁_dvd_M : d₁ ∣ M := Nat.dvd_of_mem_divisors hd₁
      have hd₁_dvd_P : d₁ ∣ B.prodPrimes := hd₁_dvd_M.trans hM_dvd
      have hd₂_dvd_P : d₂ ∣ B.prodPrimes := hd2_dvd d₂ hd₂
      have hdisj : Disjoint d₁.primeFactors d₂.primeFactors := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        have hpM : p ∈ M.primeFactors :=
          Nat.primeFactors_mono hd₁_dvd_M hM_sq.ne_zero hp1
        rw [Nat.primeFactors_prod hS_prime] at hpM
        exact (mem_D0.mp hd₂).2.2 p hp2 (hS p hpM).2
      have hcop : d₁.Coprime d₂ :=
        coprime_of_disjoint_primeFactors (Nat.pos_of_mem_divisors hd₁).ne'
          (mem_D0.mp hd₂).2.1.ne_zero hdisj
      have hmul_dvd : d₁ * d₂ ∣ B.prodPrimes := hcop.mul_dvd_of_dvd_of_dvd hd₁_dvd_P hd₂_dvd_P
      have hmul_le : d₁ * d₂ ≤ z := by
        have hd₁_le : d₁ ≤ M := Nat.le_of_dvd hM_pos hd₁_dvd_M
        have hd₂_le : d₂ ≤ z / M := (mem_D0.mp hd₂).1.2
        exact (Nat.mul_le_mul hd₁_le hd₂_le).trans (Nat.mul_div_le z M)
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hmul_dvd, B.prodPrimes_ne_zero⟩, hmul_le⟩)
  have hprod_nonneg : 0 ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [inv_nonneg]
    refine Finset.prod_nonneg fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS_prime p hp).two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  calc
    (1 / 24 : ℝ) * (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ * Real.log ((z / M + 1 : ℕ) : ℝ)
        = (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ * ((1 / 24 : ℝ) * Real.log ((z / M + 1 : ℕ) : ℝ)) := by
      ring
    _ ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ * W0 (z / M) :=
      mul_le_mul_of_nonneg_left (W0_ge_log (z / M)) hprod_nonneg
    _ ≤ ∑ m ∈ B.prodPrimes.divisors.filter (· ≤ z), B.selbergTerms m := hstep

end FactoringAndSelbergSieve

end A069004Density

/- Combine the finite sieve and its lower bound for a single choice of cutoff. -/

namespace A069004Certificate

open Finset A069004Sieve

theorem prime_dvd_sieving_product {p n z : ℕ} (hp : p.Prime) (hpz : p ≤ z)
    (hr : 0 < rootCount n p) : p ∣ sieveProduct n z := by
  have hm : p ∈ sievingPrimes n z := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpz⟩, hp, hr⟩
  exact Finset.dvd_prod_of_mem id hm

theorem concrete_sieve_product (n P : ℕ) (hsq : Squarefree P)
    (hr : ∀ p : ℕ, p.Prime → p ∣ P → 0 < rootCount n p) :
    (sieve n P hsq hr).prodPrimes = P := rfl

set_option maxRecDepth 2500 in
theorem disproof :
    ¬ (type_of% @OeisA69004.conjecture2.variants.without_upper_bound) := by
  obtain ⟨S, hS, hsmall⟩ := A069004.exists_inert_prime_product_lt
    (ε := (1/40800 : ℝ)) (by norm_num)
  let M := ∏ p ∈ S, p
  let t := M + 1700
  let Y := 2 ^ t
  let n := M * Y^16
  let z := M * Y
  have hprime : ∀ p ∈ S, Nat.Prime p := fun p hp => (hS p hp).1
  have hM : 0 < M := Finset.prod_pos fun p hp => (hprime p hp).pos
  have hlarge : t < Y := Nat.lt_two_pow_self
  have hMY : M ≤ Y := by dsimp [t] at hlarge; omega
  have hY : 1700 ≤ Y := by dsimp [t] at hlarge; omega
  have hy1 : 1 ≤ Y := by omega
  have hzpos : 1 ≤ z := Nat.mul_pos hM hy1
  have hzn : z ≤ n := Nat.mul_le_mul_left M (by simpa using
    (Nat.pow_le_pow_right hy1 (show 1 ≤ 16 by decide)))
  have hnEq : n = 2 ^ (t*16) * ∏ q ∈ S, q := by
    dsimp [n,M,Y]
    rw [pow_mul, Nat.mul_comm]
  have hzdiv : z / M = Y := Nat.mul_div_cancel_left Y hM
  let P := sieveProduct n z
  have hpP (p : ℕ) (hp : p ∈ sievingPrimes n z) : p.Prime := (mem_filter.mp hp).2.1
  have hPsq : Squarefree P := Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hpP p hp) (hpP q hq)).mpr hpq)) (fun p hp => (hpP p hp).squarefree)
  have hroots (p : ℕ) (hp : p.Prime) (hd : p ∣ P) : 0 < rootCount n p := by
    have hmem := (Nat.mem_primeFactors_of_ne_zero hPsq.ne_zero).mpr ⟨hp,hd⟩
    change p ∈ (∏ q ∈ sievingPrimes n z, q).primeFactors at hmem
    rw [Nat.primeFactors_prod hpP] at hmem
    exact (mem_filter.mp hmem).2.2
  let B := sieve n P hPsq hroots
  have hinclude {p : ℕ} (hp : p.Prime) (hpz : p ≤ z) (hr : 0 < rootCount n p) :
      p ∣ B.prodPrimes := by
    rw [show B.prodPrimes = P from concrete_sieve_product n P hPsq hroots]
    exact prime_dvd_sieving_product (n := n) (z := z) hp hpz hr
  have hinert {p : ℕ} (hp : p ∈ S) : rootCount n p = 1 := by
    rw [hnEq, A069004Root.rootCount_prime_family S hprime _ (hprime p hp)]
    simp [A069004Root.primeRoots, hp]
  have hsplit {p : ℕ} (hp : p.Prime) (hs : p % 4 = 1) : rootCount n p = 2 := by
    rw [hnEq]
    exact A069004Root.rootCount_split S hS _ hp hs
  have hG := A069004Density.sum_selbergTerms_ge_log B S z hS
    (fun p hp => hinclude (hprime p hp)
      ((Nat.le_of_dvd hM (Finset.dvd_prod_of_mem id hp)).trans (Nat.le_mul_of_pos_right M hy1))
      (by rw [hinert hp]; decide))
    (fun h => hinclude Nat.prime_two (h.trans (Nat.div_le_self _ _)) (by simp [rootCount_two]))
    (fun p hp hs hpz => hinclude hp (hpz.trans (Nat.div_le_self _ _))
      (by rw [hsplit hp hs]; decide))
    (fun p hp => by change 1 / (p:ℝ) ≤ (rootCount n p : ℝ) / p; simp [hinert hp])
    (fun _ => by change 1 / (2:ℝ) ≤ (rootCount n 2 : ℝ) / 2; simp [rootCount_two])
    (fun p hp hs _ => by change 2 / (p:ℝ) ≤ (rootCount n p : ℝ) / p; simp [hsplit hp hs])
  let L := ∏ p ∈ S, (1-1/(p:ℝ))
  have hL : 0 < L := Finset.prod_pos fun p hp => by
    have hp' : (1:ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp')
  change L < 1/40800 at hsmall
  have hInv : (40800:ℝ) ≤ L⁻¹ := by
    rw [← one_div, le_div_iff₀ hL]; linarith
  change 1/24 * L⁻¹ * Real.log ((z/M+1:ℕ):ℝ) ≤ denominator B z at hG
  rw [hzdiv] at hG
  have hylog : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast hy1)
  have hmon : Real.log (Y:ℝ) ≤ Real.log ((Y+1:ℕ):ℝ) := Real.log_le_log
    (by exact_mod_cast (show 0 < Y from hy1)) (by exact_mod_cast Nat.le_succ Y)
  have hmain : 1700 * Real.log Y ≤ denominator B z :=
    (mul_le_mul (by linarith : (1700:ℝ) ≤ 1/24 * L⁻¹) hmon hylog (mul_nonneg (by norm_num) (inv_nonneg.mpr hL.le))).trans hG
  exact disproof_of_scaled_mass hM hMY hY hmain
    (a_le_selberg_pow n P z hPsq hroots hzpos hzn)

end A069004Certificate

theorem OMA.disproof : ¬ (type_of% @OeisA69004.conjecture2.variants.without_upper_bound) :=
  A069004Certificate.disproof
