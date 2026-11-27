import FormalConjectures.ErdosProblems.«687»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SmoothNumbers

-- Reduction Erdos687.erdos_687.variants.fgkmt.R1 of Erdős Problem 687 — fgkmt
-- Credit: @ItsNotTheGabs
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Section-3 reduction of the Ford–Green–Konyagin–Maynard–Tao bound for Erdős Problem 687

Following Section 3 of Ford, Green, Konyagin, Maynard, and Tao (J. Amer. Math. Soc. 31, 2018,
arXiv:1412.5029), we reduce `Erdos687.erdos_687.variants.fgkmt` to two independent results:

1. `H1`: Rankin's smooth-number upper bound at the FGKMT18 cutoff
   `z = ⌊x ^ (log (log (log x)) / (4 * log (log x)))⌋₊`, bounding the number of `z`-smooth
   integers in `[1, y]` by `O(x / log x)`.
2. `H2`: Theorem 2 of FGKMT18, asserting the existence of residue classes for primes in
   `(⌊(log x)^20⌋₊, z]` and `(x / 2, x]` that leave at most `O(x / log x)` primes in `(x, y]`
   uncovered.

Unconditionally in Lean, this file proves:
- Rankin's exact survivor classification after zero-sifting primes `p ≤ w` and `p ∈ (z, x / 2]`,
- Chebyshev's lower bound `≥ x / (5 * log x)` for primes in `(x / 3, x]` and upper bound
  `≤ 2 * x / log x` for primes in `(x / 2, x]` via `Mathlib.NumberTheory.Chebyshev`,
- Stage-3 greedy covering of all remaining survivors by reserved primes in `(x / 3, x]` after
  rescaling `x' = x / K`,
- The `sSup` and `Asymptotics.IsBigO` deduction of `Erdos687.erdos_687.variants.fgkmt`.
-/

namespace OMA.R_Erdos687_erdos_687_variants_fgkmt_R1

open Asymptotics Erdos687 Filter Finset Real
open scoped Topology

/-- Rankin's smooth-number bound at the FGKMT18 cutoff: for every `c > 0`, letting
`y = ⌊c * x * log x * log (log (log x)) / log (log x)⌋₊` and
`z = ⌊x ^ (log (log (log x)) / (4 * log (log x)))⌋₊`, the number of `z`-smooth integers
in `[1, y]` is `O(x / log x)`. -/
def H1 : Prop :=
  ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      let y := ⌊c * (x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) /
        Real.log (Real.log x)⌋₊
      let z := ⌊(x : ℝ) ^ (Real.log (Real.log (Real.log x)) /
        (4 * Real.log (Real.log x)))⌋₊
      ((y.smoothNumbersUpTo (z + 1)).card : ℝ) ≤ C * (x : ℝ) / Real.log x

/-- Theorem 2 of Ford–Green–Konyagin–Maynard–Tao (2018): there exist constants `c > 0` and
`C > 0` such that for all sufficiently large `x`, letting
`y = ⌊c * x * log x * log (log (log x)) / log (log x)⌋₊`, `w = ⌊(log x) ^ 20⌋₊`, and
`z = ⌊x ^ (log (log (log x)) / (4 * log (log x)))⌋₊`, one can assign residue classes to the
primes in `(w, z]` and `(x / 2, x]` so that at most `C * x / log x` primes in `(x, y]` avoid
all chosen residue classes. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop,
    let y := ⌊c * (x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) /
      Real.log (Real.log x)⌋₊
    let w := ⌊(Real.log x) ^ (20 : ℕ)⌋₊
    let z := ⌊(x : ℝ) ^ (Real.log (Real.log (Real.log x)) /
      (4 * Real.log (Real.log x)))⌋₊
    ∃ a b : ℕ → ℕ,
      (((Finset.Ioc x y).filter fun q : ℕ =>
        q.Prime ∧
        (∀ s ≤ z, w < s → s.Prime → ¬ (q ≡ a s [MOD s])) ∧
        (∀ p ≤ x, x / 2 < p → p.Prime → ¬ (q ≡ b p [MOD p]))).card : ℝ) ≤
        C * (x : ℝ) / Real.log x

lemma le_Y_of_isCovered {x y : ℕ} (h : Green46.IsCoveredByResidues x y) : y ≤ Erdos687.Y x := by
  rw [Erdos687.Y]
  refine le_csSup ?_ h
  exact ⟨primorial x, fun k hk => (Erdos687.lt_primorial_of_isCoveredByResidues hk).le⟩

lemma survivor_classification (x y w z : ℕ) (hwy : 2 * y ≤ x * w) (hzx : z ≤ x / 2)
    (a b : ℕ → ℕ) :
    ((Finset.Icc 1 y).filter fun m : ℕ =>
      (∀ p ≤ w, p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
      (∀ s ≤ z, w < s → s.Prime → ¬ (m ≡ a s [MOD s])) ∧
      (∀ p ≤ x / 2, z < p → p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
      (∀ p ≤ x, x / 2 < p → p.Prime → ¬ (m ≡ b p [MOD p]))) ⊆
    y.smoothNumbersUpTo (z + 1) ∪
      (((Finset.Ioc (x / 2) x).filter Nat.Prime) ∪
        ((Finset.Ioc x y).filter fun q : ℕ =>
          q.Prime ∧
          (∀ s ≤ z, w < s → s.Prime → ¬ (q ≡ a s [MOD s])) ∧
          (∀ p ≤ x, x / 2 < p → p.Prime → ¬ (q ≡ b p [MOD p])))) := by
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨hm1, hmy⟩, h1, h2, h3, h4⟩ := hm
  by_cases hcase : ∃ q, q.Prime ∧ q ∣ m ∧ z < q
  · obtain ⟨q, hqprime, hqm, hzq⟩ := hcase
    have hxpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx; omega
      · exact hx
    have hxq : x / 2 < q := by
      by_contra hcon
      push Not at hcon
      exact h3 q hcon hzq hqprime (Nat.modEq_zero_iff_dvd.mpr hqm)
    obtain ⟨k, hk⟩ := hqm
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; rw [mul_zero] at hk; omega
      · exact hk0
    have hkm : k ∣ m := ⟨q, by rw [hk, mul_comm]⟩
    have hqx : x < 2 * q := by omega
    have hklt : k < w := by
      have hxkw : x * k < x * w := by
        calc x * k < 2 * q * k := Nat.mul_lt_mul_of_pos_right hqx hkpos
          _ = 2 * m := by rw [hk]; ring
          _ ≤ 2 * y := by omega
          _ ≤ x * w := hwy
      exact (Nat.mul_lt_mul_left hxpos).mp hxkw
    have hk1 : k = 1 := by
      by_contra hne
      have hk2 : 2 ≤ k := by omega
      have hp : k.minFac.Prime := Nat.minFac_prime hne
      have hpdvd : k.minFac ∣ k := Nat.minFac_dvd k
      have hpw : k.minFac ≤ w := by
        have := Nat.minFac_le hkpos
        omega
      exact h1 k.minFac hpw hp (Nat.modEq_zero_iff_dvd.mpr (hpdvd.trans hkm))
    have hmq : m = q := by rw [hk, hk1, mul_one]
    have hmprime : m.Prime := by rw [hmq]; exact hqprime
    by_cases hmx : m ≤ x
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hmx⟩, hmprime⟩))
    · push Not at hmx
      exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hmx, hmy⟩, hmprime, h2, h4⟩))
  · push Not at hcase
    refine Finset.mem_union_left _ (Nat.mem_smoothNumbersUpTo.mpr ⟨hmy, ?_⟩)
    refine Nat.mem_smoothNumbers'.mpr ?_
    intro p hpp hpd
    have hzp : p ≤ z := hcase p hpp hpd
    omega

lemma card_primes_Ioc_third_ge :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) / (5 * Real.log x) ≤ (((Finset.Ioc (x / 3) x).filter Nat.Prime).card : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (500 ^ 4)] with x hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hge := Chebyshev.theta_ge x
  have hle := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (x / 3))
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hdiv3 : ((x / 3 : ℕ) : ℝ) ≤ (x : ℝ) / 3 := by
    simpa using (Nat.cast_div_le (m := x) (n := 3) (α := ℝ))
  have hle' : Chebyshev.theta ((x / 3 : ℕ) : ℝ) ≤ (2 / 3) * Real.log 2 * (x : ℝ) := by
    have hlog2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc Chebyshev.theta ((x / 3 : ℕ) : ℝ)
        ≤ Real.log 4 * ((x / 3 : ℕ) : ℝ) := hle
      _ = 2 * Real.log 2 * ((x / 3 : ℕ) : ℝ) := by rw [hlog4]
      _ ≤ 2 * Real.log 2 * ((x : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hdiv3 (by positivity)
      _ = (2 / 3) * Real.log 2 * (x : ℝ) := by ring
  set s : ℝ := Real.sqrt (x : ℝ) with hs_def
  set r : ℝ := Real.sqrt s with hr_def
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = (x : ℝ) := Real.sq_sqrt (Nat.cast_nonneg x)
  have hr_sq : r ^ 2 = s := Real.sq_sqrt hs_nonneg
  have hr_pow4 : r ^ 4 = (x : ℝ) := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = s ^ 2 := by rw [hr_sq]
      _ = (x : ℝ) := hs_sq
  have hr_ge : (500 : ℝ) ≤ r := by
    by_contra hlt
    push Not at hlt
    have h1 : r ^ 4 < (500 : ℝ) ^ 4 := by
      have hr2 : r ^ 2 < (500 : ℝ) ^ 2 := by nlinarith
      nlinarith
    have h2 : ((500 ^ 4 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    push_cast at h2
    linarith
  have hr_pos : 0 < r := by linarith
  have hlogr : Real.log r ≤ r := (Real.log_le_sub_one_of_pos hr_pos).trans (by linarith)
  have hlogx_eq : Real.log (x : ℝ) = 4 * Real.log r := by
    rw [← hr_pow4, Real.log_pow]
    push_cast
    ring
  have hterm1 : 2 * s * Real.log (x : ℝ) ≤ 8 * r ^ 3 := by
    rw [hlogx_eq, ← hr_sq]
    nlinarith
  have hterm2 : Real.log ((x : ℝ) + 1) ≤ 5 * r ^ 3 := by
    have hxadd : (x : ℝ) + 1 ≤ 2 * r ^ 4 := by linarith
    have h1 : Real.log ((x : ℝ) + 1) ≤ Real.log (2 * r ^ 4) :=
      Real.log_le_log (by positivity) hxadd
    have h2 : Real.log (2 * r ^ 4) = Real.log 2 + 4 * Real.log r := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have hlog2lt : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    nlinarith
  have hdiff_ge : (x : ℝ) / 5 ≤ Chebyshev.theta (x : ℝ) - Chebyshev.theta ((x / 3 : ℕ) : ℝ) := by
    have hlog2gt : (0.69 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hgap : (13 : ℝ) * r ^ 3 ≤ ((Real.log 2 / 3) - 1 / 5) * r ^ 4 := by
      have hcoef : (0.03 : ℝ) ≤ Real.log 2 / 3 - 1 / 5 := by linarith
      have hr3_nonneg : 0 ≤ r ^ 3 := by positivity
      have hmul1 : (13 : ℝ) * r ^ 3 ≤ (0.03 : ℝ) * r ^ 4 := by
        have : (13 : ℝ) ≤ 0.03 * r := by linarith
        nlinarith
      have hmul2 : (0.03 : ℝ) * r ^ 4 ≤ (Real.log 2 / 3 - 1 / 5) * r ^ 4 :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      linarith
    rw [hr_pow4] at hgap
    linarith [hge, hle', hterm1, hterm2, hgap]
  have hsub : Nat.primesLE (x / 3) ⊆ Nat.primesLE x := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsdiff : Nat.primesLE x \ Nat.primesLE (x / 3) = (Finset.Ioc (x / 3) x).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Nat.primesLE, Nat.primesBelow, Finset.mem_filter,
      Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpx, hp⟩, hnot⟩
      refine ⟨⟨?_, by omega⟩, hp⟩
      by_contra hle3
      exact hnot ⟨by omega, hp⟩
    · rintro ⟨⟨hgt, hle⟩, hp⟩
      exact ⟨⟨by omega, hp⟩, fun h => by omega⟩
  have hdiff_eq : Chebyshev.theta (x : ℝ) - Chebyshev.theta ((x / 3 : ℕ) : ℝ) =
      ∑ p ∈ (Finset.Ioc (x / 3) x).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log x, Chebyshev.theta_eq_sum_primesLE_log (x / 3)]
    have hsum := Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsub
    rw [hsdiff] at hsum
    linarith
  have hsum_le : ∑ p ∈ (Finset.Ioc (x / 3) x).filter Nat.Prime, Real.log (p : ℝ) ≤
      (((Finset.Ioc (x / 3) x).filter Nat.Prime).card : ℝ) * Real.log (x : ℝ) := by
    have hle_each : ∀ p ∈ (Finset.Ioc (x / 3) x).filter Nat.Prime,
        Real.log (p : ℝ) ≤ Real.log (x : ℝ) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
      have hp_le : (p : ℝ) ≤ (x : ℝ) := by exact_mod_cast hp.1.2
      exact Real.log_le_log hp_pos hp_le
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hle_each
  have hprod : (x : ℝ) / 5 ≤
      (((Finset.Ioc (x / 3) x).filter Nat.Prime).card : ℝ) * Real.log (x : ℝ) := by
    linarith [hdiff_ge, hdiff_eq, hsum_le]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 5 * Real.log (x : ℝ))]
  linarith

lemma card_primes_Ioc_half_le :
    ∀ᶠ x : ℕ in Filter.atTop,
      (((Finset.Ioc (x / 2) x).filter Nat.Prime).card : ℝ) ≤ 2 * (x : ℝ) / Real.log x := by
  have hε : (0 : ℝ) < 2 - Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h2 := Real.log_two_lt_d9
    linarith
  have hmain := Chebyshev.eventually_primeCounting_le (ε := 2 - Real.log 4) hε
  have htt : Filter.Tendsto (fun x : ℕ => (x : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [htt.eventually hmain] with x hx
  rw [Nat.floor_natCast] at hx
  have hcard : ((Finset.Ioc (x / 2) x).filter Nat.Prime).card ≤ Nat.primeCounting x := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨-, hle⟩, hp⟩ := hm
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp⟩
  have hcardR : (((Finset.Ioc (x / 2) x).filter Nat.Prime).card : ℝ) ≤
      (Nat.primeCounting x : ℝ) := by
    exact_mod_cast hcard
  have hx' : (Nat.primeCounting x : ℝ) ≤ 2 * (x : ℝ) / Real.log x := by
    simpa using hx
  exact le_trans hcardR hx'

lemma greedy_cover_of_card_le {x y x' w z : ℕ} (hwz : w ≤ z) (hzx : z ≤ x' / 2)
    (hxx : x' ≤ x / 3) (a b : ℕ → ℕ)
    (hcard :
      ((Finset.Icc 1 y).filter fun m : ℕ =>
        (∀ p ≤ w, p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
        (∀ s ≤ z, w < s → s.Prime → ¬ (m ≡ a s [MOD s])) ∧
        (∀ p ≤ x' / 2, z < p → p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
        (∀ p ≤ x', x' / 2 < p → p.Prime → ¬ (m ≡ b p [MOD p]))).card ≤
      ((Finset.Ioc (x / 3) x).filter Nat.Prime).card) :
    Green46.IsCoveredByResidues x y := by
  classical
  set U : Finset ℕ := (Finset.Icc 1 y).filter fun m : ℕ =>
        (∀ p ≤ w, p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
        (∀ s ≤ z, w < s → s.Prime → ¬ (m ≡ a s [MOD s])) ∧
        (∀ p ≤ x' / 2, z < p → p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
        (∀ p ≤ x', x' / 2 < p → p.Prime → ¬ (m ≡ b p [MOD p])) with hUdef
  set R : Finset ℕ := (Finset.Ioc (x / 3) x).filter Nat.Prime with hRdef
  have hUR : U.card ≤ R.card := by
    rw [hUdef, hRdef]
    exact hcard
  let e : U → R := fun u =>
    (Finset.equivFin R).symm (Fin.castLE hUR (Finset.equivFin U u))
  let f : ℕ → ℕ := fun p => if h : p ∈ U then ((e ⟨p, h⟩ : R) : ℕ) else 0
  have hf_apply : ∀ (p : ℕ) (hp : p ∈ U), f p = ((e ⟨p, hp⟩ : R) : ℕ) := by
    intro p hp
    simp only [f]
    rw [dif_pos hp]
  have hf_inj : Set.InjOn f (U : Set ℕ) := by
    intro p hp q hq hpq
    rw [hf_apply p hp, hf_apply q hq] at hpq
    have hR : e ⟨p, hp⟩ = e ⟨q, hq⟩ := Subtype.coe_injective hpq
    have h3 : Fin.castLE hUR (Finset.equivFin U ⟨p, hp⟩) =
        Fin.castLE hUR (Finset.equivFin U ⟨q, hq⟩) := by
      have := congrArg (Finset.equivFin R) hR
      simpa [e] using this
    have h4 : Finset.equivFin U ⟨p, hp⟩ = Finset.equivFin U ⟨q, hq⟩ :=
      Fin.castLE_injective hUR h3
    have h5 : (⟨p, hp⟩ : U) = ⟨q, hq⟩ := (Finset.equivFin U).injective h4
    exact congrArg Subtype.val h5
  let A : ℕ → ℕ := fun p =>
    if p ≤ w then 0
    else if p ≤ z then a p
    else if p ≤ x' / 2 then 0
    else if p ≤ x' then b p
    else if h : ∃ u ∈ U, f u = p then h.choose else 0
  have hA1 : ∀ p, p ≤ w → A p = 0 := by
    intro p hp
    simp only [A]
    rw [if_pos hp]
  have hA2 : ∀ p, w < p → p ≤ z → A p = a p := by
    intro p hwp hpz
    have h1 : ¬ p ≤ w := by omega
    simp only [A]
    rw [if_neg h1, if_pos hpz]
  have hA3 : ∀ p, z < p → p ≤ x' / 2 → A p = 0 := by
    intro p hzp hpz
    have h1 : ¬ p ≤ w := by omega
    have h2 : ¬ p ≤ z := by omega
    simp only [A]
    rw [if_neg h1, if_neg h2, if_pos hpz]
  have hA4 : ∀ p, x' / 2 < p → p ≤ x' → A p = b p := by
    intro p hhalf hp'
    have h1 : ¬ p ≤ w := by omega
    have h2 : ¬ p ≤ z := by omega
    have h3 : ¬ p ≤ x' / 2 := by omega
    simp only [A]
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos hp']
  have hA5 : ∀ (p : ℕ), x' < p → ∀ h : ∃ u ∈ U, f u = p, A p = h.choose := by
    intro p hp' h
    have h1 : ¬ p ≤ w := by omega
    have h2 : ¬ p ≤ z := by omega
    have h3 : ¬ p ≤ x' / 2 := by omega
    have h4 : ¬ p ≤ x' := by omega
    simp only [A]
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    exact dif_pos h
  refine ⟨A, ?_⟩
  intro m hm
  by_cases hU : m ∈ U
  · have hfmR : f m ∈ R := by
      rw [hf_apply m hU]
      exact (e ⟨m, hU⟩).2
    rw [hRdef] at hfmR
    obtain ⟨hmIoc, hprime⟩ := Finset.mem_filter.mp hfmR
    have hx'lt : x' < f m := by
      have h3lt : x / 3 < f m := (Finset.mem_Ioc.mp hmIoc).1
      have h4 : x' ≤ x / 3 := hxx
      omega
    have hex : ∃ u ∈ U, f u = f m := ⟨m, hU, rfl⟩
    have hAval : A (f m) = hex.choose := hA5 (f m) hx'lt hex
    refine ⟨f m, (Finset.mem_Ioc.mp hmIoc).2, hprime, ?_⟩
    rw [hAval]
    have hspec := hex.choose_spec
    have hchoose : hex.choose = m := hf_inj hspec.1 hU hspec.2
    rw [hchoose]
  · have hnotPred : ¬ ((∀ p ≤ w, p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
        (∀ s ≤ z, w < s → s.Prime → ¬ (m ≡ a s [MOD s])) ∧
        (∀ p ≤ x' / 2, z < p → p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
        (∀ p ≤ x', x' / 2 < p → p.Prime → ¬ (m ≡ b p [MOD p]))) := by
      intro hp
      exact hU (by rw [hUdef]; exact Finset.mem_filter.2 ⟨hm, hp⟩)
    by_cases hC1 : (∀ p ≤ w, p.Prime → ¬ (m ≡ 0 [MOD p]))
    · by_cases hC2 : (∀ s ≤ z, w < s → s.Prime → ¬ (m ≡ a s [MOD s]))
      · by_cases hC3 : (∀ p ≤ x' / 2, z < p → p.Prime → ¬ (m ≡ 0 [MOD p]))
        · have hC4 : ¬ (∀ p ≤ x', x' / 2 < p → p.Prime → ¬ (m ≡ b p [MOD p])) := by
            intro hC4
            exact hnotPred ⟨hC1, hC2, hC3, hC4⟩
          push Not at hC4
          obtain ⟨p, hp_le, hp_half, hp_prime, hp_cong⟩ := hC4
          have hpx : p ≤ x := by
            have h1 : x' / 2 ≤ x' := Nat.div_le_self x' 2
            have h2 : x' ≤ x := hxx.trans (Nat.div_le_self x 3)
            omega
          refine ⟨p, hpx, hp_prime, ?_⟩
          rw [hA4 p hp_half hp_le]
          exact hp_cong
        · push Not at hC3
          obtain ⟨p, hp_le, hp_z, hp_prime, hp_cong⟩ := hC3
          have hpx : p ≤ x := by
            have h1 : x' / 2 ≤ x' := Nat.div_le_self x' 2
            have h2 : x' ≤ x := hxx.trans (Nat.div_le_self x 3)
            omega
          refine ⟨p, hpx, hp_prime, ?_⟩
          rw [hA3 p hp_z hp_le]
          exact hp_cong
      · push Not at hC2
        obtain ⟨s, hs_le, hws, hs_prime, hs_cong⟩ := hC2
        have hsx : s ≤ x := by
          have h1 : s ≤ x' / 2 := hs_le.trans hzx
          have h2 : x' / 2 ≤ x' := Nat.div_le_self x' 2
          have h3 : x' ≤ x := hxx.trans (Nat.div_le_self x 3)
          omega
        refine ⟨s, hsx, hs_prime, ?_⟩
        rw [hA2 s hws hs_le]
        exact hs_cong
    · push Not at hC1
      obtain ⟨p, hp_le, hp_prime, hp_cong⟩ := hC1
      have hpx : p ≤ x := by
        have h1 : x' / 2 ≤ x' := Nat.div_le_self x' 2
        have h2 : x' ≤ x := hxx.trans (Nat.div_le_self x 3)
        omega
      refine ⟨p, hpx, hp_prime, ?_⟩
      rw [hA1 p hp_le]
      exact hp_cong

lemma asymptotic_cutoffs (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℕ in Filter.atTop,
      let y := ⌊c * (x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) /
        Real.log (Real.log x)⌋₊
      let w := ⌊(Real.log x) ^ (20 : ℕ)⌋₊
      let z := ⌊(x : ℝ) ^ (Real.log (Real.log (Real.log x)) /
        (4 * Real.log (Real.log x)))⌋₊
      0 < Real.log x ∧
      0 < Real.log (Real.log x) ∧
      0 < Real.log (Real.log (Real.log x)) ∧
      w ≤ z ∧
      z ≤ x / 2 ∧
      2 * y ≤ x * w := by
  have hT1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hT2 : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hT1
  have hT3 : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log (x : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hT2
  filter_upwards [Filter.eventually_ge_atTop 16,
    hT1.eventually (Filter.eventually_ge_atTop (max 2000000 (2 * c + 2))),
    hT2.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    hT3.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with x hx hL1 hL2 hL3
  dsimp only
  set L1 : ℝ := Real.log (x : ℝ) with hL1_def
  set L2 : ℝ := Real.log L1 with hL2_def
  set L3 : ℝ := Real.log L2 with hL3_def
  have hL1_big : (2000000 : ℝ) ≤ L1 := (le_max_left _ _).trans hL1
  have hL1_c : 2 * c + 2 ≤ L1 := (le_max_right _ _).trans hL1
  have hL1_pos : 0 < L1 := by linarith
  have hL2_pos : 0 < L2 := by linarith
  have hL3_pos : 0 < L3 := by linarith
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx_ge1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hL3_le_L2 : L3 ≤ L2 := (Real.log_le_sub_one_of_pos hL2_pos).trans (by linarith)
  refine ⟨hL1_pos, hL2_pos, hL3_pos, ?_, ?_, ?_⟩
  · apply Nat.floor_mono
    have hpow : L1 ^ (20 : ℕ) = Real.exp (20 * L2) := by
      rw [← Real.exp_log (pow_pos hL1_pos 20), Real.log_pow]
      push_cast
      rfl
    have hrpow : (x : ℝ) ^ (L3 / (4 * L2)) = Real.exp (L1 * (L3 / (4 * L2))) := by
      rw [Real.rpow_def_of_pos hx_pos]
    rw [hpow, hrpow]
    apply Real.exp_le_exp.mpr
    set r : ℝ := Real.sqrt (Real.sqrt L1) with hr_def
    have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
    have hs_nonneg : 0 ≤ Real.sqrt L1 := Real.sqrt_nonneg _
    have hr_sq : r ^ 2 = Real.sqrt L1 := Real.sq_sqrt hs_nonneg
    have hr_pow4 : r ^ 4 = L1 := by
      calc r ^ 4 = (r ^ 2) ^ 2 := by ring
        _ = (Real.sqrt L1) ^ 2 := by rw [hr_sq]
        _ = L1 := Real.sq_sqrt hL1_pos.le
    have hr_sq_ge : (1280 : ℝ) ≤ r ^ 2 := by
      by_contra hlt
      push Not at hlt
      have : r ^ 4 < (1280 : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hr_pos : 0 < r := by
      by_contra hle
      push Not at hle
      have : r = 0 := le_antisymm hle hr_nonneg
      rw [this] at hr_sq_ge
      norm_num at hr_sq_ge
    have hL2_le : L2 ≤ 4 * r := by
      have hlogr : Real.log r ≤ r := (Real.log_le_sub_one_of_pos hr_pos).trans (by linarith)
      have hL2_eq : L2 = 4 * Real.log r := by
        rw [hL2_def, ← hr_pow4, Real.log_pow]
        push_cast
        ring
      linarith
    have h80 : 80 * L2 ^ 2 ≤ L1 := by
      have h1 : L2 ^ 2 ≤ 16 * r ^ 2 := by nlinarith
      have h2 : 80 * L2 ^ 2 ≤ 1280 * r ^ 2 := by linarith
      have h3 : 1280 * r ^ 2 ≤ r ^ 4 := by nlinarith
      linarith
    have h80' : 80 * L2 ^ 2 ≤ L1 * L3 := by nlinarith
    rw [show L1 * (L3 / (4 * L2)) = (L1 * L3) / (4 * L2) by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < 4 * L2)]
    linarith
  · apply Nat.floor_le_of_le
    have hexp_le : L3 / (4 * L2) ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * L2)]
      linarith
    have hrpow_le : (x : ℝ) ^ (L3 / (4 * L2)) ≤ Real.sqrt (x : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx_ge1 hexp_le
    have hsqrt_le : Real.sqrt (x : ℝ) ≤ ((x / 2 : ℕ) : ℝ) := by
      rw [Real.sqrt_le_left (Nat.cast_nonneg _)]
      have hnat : x ≤ (x / 2) * (x / 2) := by
        have h1 : 2 * (x / 2) + 1 ≥ x := by omega
        have h2 : 8 ≤ x / 2 := by omega
        nlinarith
      have hreal : (x : ℝ) ≤ ((x / 2 : ℕ) : ℝ) * ((x / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith [sq ((x / 2 : ℕ) : ℝ)]
    exact hrpow_le.trans hsqrt_le
  · have hreal : (2 * ⌊c * (x : ℝ) * L1 * L3 / L2⌋₊ : ℝ) ≤
        ((x * ⌊L1 ^ (20 : ℕ)⌋₊ : ℕ) : ℝ) := by
      have hy_le : (⌊c * (x : ℝ) * L1 * L3 / L2⌋₊ : ℝ) ≤ c * (x : ℝ) * L1 * L3 / L2 :=
        Nat.floor_le (by positivity)
      have hfrac_le : c * (x : ℝ) * L1 * L3 / L2 ≤ c * (x : ℝ) * L1 := by
        rw [div_le_iff₀ hL2_pos]
        have : 0 ≤ c * (x : ℝ) * L1 := by positivity
        nlinarith
      have hw_gt : L1 ^ (20 : ℕ) - 1 < (⌊L1 ^ (20 : ℕ)⌋₊ : ℝ) :=
        Nat.sub_one_lt_floor (L1 ^ (20 : ℕ))
      have hpow20 : L1 ^ (2 : ℕ) ≤ L1 ^ (20 : ℕ) :=
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ L1) (by norm_num)
      have hw_ge : 2 * c * L1 ≤ (⌊L1 ^ (20 : ℕ)⌋₊ : ℝ) := by
        have : 2 * c * L1 ≤ L1 ^ (2 : ℕ) - 1 := by nlinarith
        linarith
      push_cast
      nlinarith
    exact_mod_cast hreal

lemma scaled_lower_bound (c : ℝ) (hc : 0 < c) (K : ℕ) (hK : 4 ≤ K) :
    ∀ᶠ x : ℕ in Filter.atTop,
      let x' := x / K
      let y' := ⌊c * (x' : ℝ) * Real.log x' * Real.log (Real.log (Real.log x')) /
        Real.log (Real.log x')⌋₊
      Real.log x / 2 ≤ Real.log x' ∧
      (x' : ℝ) ≤ (x : ℝ) / (K : ℝ) ∧
      c / (16 * (K : ℝ)) *
        ((x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) ≤
        (y' : ℝ) := by
  have hT1 : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hT2 : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hT1
  have hT3 : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log (x : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hT2
  filter_upwards [Filter.eventually_ge_atTop (max ((2 * K) ^ 2) ⌈16 * (K : ℝ) / c⌉₊),
    hT1.eventually (Filter.eventually_ge_atTop (4 : ℝ)),
    hT2.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hT3.eventually (Filter.eventually_ge_atTop (2 : ℝ))] with x hx hL1 hL2 hL3
  dsimp only
  set x' : ℕ := x / K with hx'_def
  have hKpos_nat : 0 < K := by omega
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos_nat
  have hxsq : (2 * K) ^ 2 ≤ x := (le_max_left _ _).trans hx
  have hx2K : 2 * K ≤ x := by nlinarith
  have hx_c : 16 * (K : ℝ) / c ≤ (x : ℝ) := by
    have h1 : ⌈16 * (K : ℝ) / c⌉₊ ≤ x := (le_max_right _ _).trans hx
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx'_le : (x' : ℝ) ≤ (x : ℝ) / (K : ℝ) := by
    simpa [hx'_def] using (Nat.cast_div_le (m := x) (n := K) (α := ℝ))
  have hx'_ge : (x : ℝ) / (2 * (K : ℝ)) ≤ (x' : ℝ) := by
    have hfloor : ⌊(x : ℝ) / (K : ℝ)⌋₊ = x' := by
      rw [hx'_def, Nat.floor_div_natCast, Nat.floor_natCast]
    have hlt : (x : ℝ) / (K : ℝ) - 1 < (x' : ℝ) := by
      have := Nat.sub_one_lt_floor ((x : ℝ) / (K : ℝ))
      rwa [hfloor] at this
    have hxr : 2 * (K : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2K
    have hle1 : (1 : ℝ) ≤ (x : ℝ) / (2 * (K : ℝ)) := by
      rw [one_le_div (by positivity : (0 : ℝ) < 2 * (K : ℝ))]
      linarith
    have hsplit : (x : ℝ) / (K : ℝ) - (x : ℝ) / (2 * (K : ℝ)) = (x : ℝ) / (2 * (K : ℝ)) := by
      field_simp
      ring
    linarith
  have hx'_pos : (0 : ℝ) < (x' : ℝ) := lt_of_lt_of_le (by positivity) hx'_ge
  have hlogHalf : Real.log (x : ℝ) / 2 ≤ Real.log (x' : ℝ) := by
    have hmono : Real.log ((x : ℝ) / (2 * (K : ℝ))) ≤ Real.log (x' : ℝ) :=
      Real.log_le_log (by positivity) hx'_ge
    have hlogdiv : Real.log ((x : ℝ) / (2 * (K : ℝ))) =
        Real.log (x : ℝ) - Real.log (2 * (K : ℝ)) :=
      Real.log_div hx_pos.ne' (by positivity)
    have hxsqr : (2 * (K : ℝ)) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hxsq
    have hlogsq : Real.log ((2 * (K : ℝ)) ^ 2) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by positivity) hxsqr
    have hlogpow : Real.log ((2 * (K : ℝ)) ^ 2) = 2 * Real.log (2 * (K : ℝ)) := by
      rw [Real.log_pow]
      push_cast
      ring
    linarith
  refine ⟨hlogHalf, hx'_le, ?_⟩
  set L1 : ℝ := Real.log (x : ℝ) with hL1_def
  set L2 : ℝ := Real.log L1 with hL2_def
  set L3 : ℝ := Real.log L2 with hL3_def
  set L1' : ℝ := Real.log (x' : ℝ) with hL1'_def
  set L2' : ℝ := Real.log L1' with hL2'_def
  set L3' : ℝ := Real.log L2' with hL3'_def
  have hL1'_pos : 0 < L1' := by linarith
  have hx'_le_x : (x' : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast Nat.div_le_self x K
  have hL1'_le : L1' ≤ L1 := Real.log_le_log hx'_pos hx'_le_x
  have hL2'_le : L2' ≤ L2 := Real.log_le_log hL1'_pos hL1'_le
  have hlog2_lt1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hL2'_ge : L2 / 2 ≤ L2' := by
    have h1 : Real.log (L1 / 2) ≤ L2' := Real.log_le_log (by positivity) hlogHalf
    have h2 : Real.log (L1 / 2) = L2 - Real.log 2 :=
      Real.log_div (by positivity) (by norm_num)
    linarith
  have hL2'_pos : 0 < L2' := by linarith
  have hL3'_ge : L3 / 2 ≤ L3' := by
    have h1 : Real.log (L2 / 2) ≤ L3' := Real.log_le_log (by positivity) hL2'_ge
    have h2 : Real.log (L2 / 2) = L3 - Real.log 2 :=
      Real.log_div (by positivity) (by norm_num)
    linarith
  have hL3'_pos : 0 < L3' := by linarith
  set M : ℝ := c / (8 * (K : ℝ)) * ((x : ℝ) * L1 * L3 / L2) with hM_def
  have hM_le : M ≤ c * (x' : ℝ) * L1' * L3' / L2' := by
    have hnum : c * ((x : ℝ) / (2 * (K : ℝ))) * (L1 / 2) * (L3 / 2) ≤
        c * (x' : ℝ) * L1' * L3' := by
      have h1 : c * ((x : ℝ) / (2 * (K : ℝ))) ≤ c * (x' : ℝ) :=
        mul_le_mul_of_nonneg_left hx'_ge hc.le
      have h2 : c * ((x : ℝ) / (2 * (K : ℝ))) * (L1 / 2) ≤ c * (x' : ℝ) * L1' :=
        mul_le_mul h1 hlogHalf (by positivity) (by positivity)
      exact mul_le_mul h2 hL3'_ge (by positivity) (by positivity)
    have hdiv : c * ((x : ℝ) / (2 * (K : ℝ))) * (L1 / 2) * (L3 / 2) / L2 ≤
        c * (x' : ℝ) * L1' * L3' / L2' :=
      div_le_div₀ (by positivity) hnum hL2'_pos hL2'_le
    have heq : M = c * ((x : ℝ) / (2 * (K : ℝ))) * (L1 / 2) * (L3 / 2) / L2 := by
      rw [hM_def]
      field_simp
      ring
    linarith
  have hM_ge2 : (2 : ℝ) ≤ M := by
    have hL2_le_L1 : L2 ≤ L1 := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hL1_div_L2 : (1 : ℝ) ≤ L1 / L2 := (one_le_div (by linarith)).2 hL2_le_L1
    have hcx : (2 : ℝ) ≤ c / (8 * (K : ℝ)) * (x : ℝ) := by
      have h1 : 16 * (K : ℝ) ≤ (x : ℝ) * c := (div_le_iff₀ hc).mp hx_c
      have h2 : (2 : ℝ) * (8 * (K : ℝ)) ≤ c * (x : ℝ) := by linarith
      rw [show c / (8 * (K : ℝ)) * (x : ℝ) = (c * (x : ℝ)) / (8 * (K : ℝ)) by ring,
        le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (K : ℝ))]
      linarith
    have hM_eq : M = (c / (8 * (K : ℝ)) * (x : ℝ)) * (L1 / L2) * L3 := by
      rw [hM_def]
      ring
    rw [hM_eq]
    have hstep1 : (2 : ℝ) ≤ (c / (8 * (K : ℝ)) * (x : ℝ)) * (L1 / L2) := by nlinarith
    nlinarith
  have hfloor_gt : c * (x' : ℝ) * L1' * L3' / L2' - 1 <
      (⌊c * (x' : ℝ) * L1' * L3' / L2'⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  have hhalf : c / (16 * (K : ℝ)) * ((x : ℝ) * L1 * L3 / L2) = M / 2 := by
    rw [hM_def]
    ring
  linarith

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.variants.fgkmt := by
  intro h1 h2
  obtain ⟨c, hc, C₂, hC₂, hH2⟩ := h2
  obtain ⟨C₁, hC₁, hH1⟩ := h1 c hc
  let K : ℕ := max 4 ⌈10 * (C₁ + C₂ + 2)⌉₊
  have hK4 : 4 ≤ K := le_max_left _ _
  have hKpos : 0 < K := by omega
  have hKbound : 10 * (C₁ + C₂ + 2) ≤ (K : ℝ) := by
    have h1' : ⌈10 * (C₁ + C₂ + 2)⌉₊ ≤ K := le_max_right _ _
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1')
  have hDiv : Tendsto (fun x : ℕ => x / K) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨b * K, fun x hx => (Nat.le_div_iff_mul_le hKpos).2 hx⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨16 * (K : ℝ) / c, ?_⟩
  filter_upwards [hDiv.eventually hH1, hDiv.eventually hH2,
    hDiv.eventually (asymptotic_cutoffs c hc), hDiv.eventually card_primes_Ioc_half_le,
    asymptotic_cutoffs c hc, card_primes_Ioc_third_ge, scaled_lower_bound c hc K hK4]
    with x hSmooth hSieve hCut' hMid' hCut hThird hScale
  let x' := x / K
  let y' := ⌊c * (x' : ℝ) * Real.log x' * Real.log (Real.log (Real.log x')) /
    Real.log (Real.log x')⌋₊
  let w' := ⌊(Real.log x') ^ (20 : ℕ)⌋₊
  let z' := ⌊(x' : ℝ) ^ (Real.log (Real.log (Real.log x')) /
    (4 * Real.log (Real.log x')))⌋₊
  obtain ⟨hlogx, hlog2x, hlog3x, _, _, _⟩ := hCut
  obtain ⟨hlogx', _, _, hwz', hzx', hwy'⟩ := hCut'
  obtain ⟨hlogHalf, hx'le, hy'ge⟩ := hScale
  obtain ⟨a, b, hQcard⟩ := hSieve
  let U := (Finset.Icc 1 y').filter fun m : ℕ =>
    (∀ p ≤ w', p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
    (∀ s ≤ z', w' < s → s.Prime → ¬ (m ≡ a s [MOD s])) ∧
    (∀ p ≤ x' / 2, z' < p → p.Prime → ¬ (m ≡ 0 [MOD p])) ∧
    (∀ p ≤ x', x' / 2 < p → p.Prime → ¬ (m ≡ b p [MOD p]))
  let UQ := (Finset.Ioc x' y').filter fun q : ℕ =>
    q.Prime ∧
    (∀ s ≤ z', w' < s → s.Prime → ¬ (q ≡ a s [MOD s])) ∧
    (∀ p ≤ x', x' / 2 < p → p.Prime → ¬ (q ≡ b p [MOD p]))
  have hUsub : U ⊆ y'.smoothNumbersUpTo (z' + 1) ∪
      (((Finset.Ioc (x' / 2) x').filter Nat.Prime) ∪ UQ) :=
    survivor_classification x' y' w' z' hwy' hzx' a b
  have hUcard_nat : U.card ≤ (y'.smoothNumbersUpTo (z' + 1)).card +
      (((Finset.Ioc (x' / 2) x').filter Nat.Prime).card + UQ.card) :=
    (Finset.card_le_card hUsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have hUcard_real : (U.card : ℝ) ≤ (C₁ + C₂ + 2) * (x' : ℝ) / Real.log x' := by
    have hcast : (U.card : ℝ) ≤ ((y'.smoothNumbersUpTo (z' + 1)).card : ℝ) +
        ((((Finset.Ioc (x' / 2) x').filter Nat.Prime).card : ℝ) + (UQ.card : ℝ)) := by
      exact_mod_cast hUcard_nat
    have hSmooth' : ((y'.smoothNumbersUpTo (z' + 1)).card : ℝ) ≤ C₁ * (x' : ℝ) / Real.log x' :=
      hSmooth
    have hQcard' : (UQ.card : ℝ) ≤ C₂ * (x' : ℝ) / Real.log x' := hQcard
    have hsum : C₁ * (x' : ℝ) / Real.log x' +
        (2 * (x' : ℝ) / Real.log x' + C₂ * (x' : ℝ) / Real.log x') =
        (C₁ + C₂ + 2) * (x' : ℝ) / Real.log x' := by ring
    linarith
  have hUleR_real : (U.card : ℝ) ≤ (((Finset.Ioc (x / 3) x).filter Nat.Prime).card : ℝ) := by
    have hKreal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hCpos : 0 < C₁ + C₂ + 2 := by linarith
    have hfrac : (C₁ + C₂ + 2) * (x' : ℝ) / Real.log x' ≤ (x : ℝ) / (5 * Real.log x) := by
      have hx'div : (x' : ℝ) / Real.log x' ≤ ((x : ℝ) / (K : ℝ)) / (Real.log x / 2) := by
        exact div_le_div₀ (by positivity) hx'le (by positivity) hlogHalf
      have hmul : (C₁ + C₂ + 2) * ((x' : ℝ) / Real.log x') ≤
          (C₁ + C₂ + 2) * (((x : ℝ) / (K : ℝ)) / (Real.log x / 2)) :=
        mul_le_mul_of_nonneg_left hx'div hCpos.le
      have hsimp : (C₁ + C₂ + 2) * (((x : ℝ) / (K : ℝ)) / (Real.log x / 2)) =
          (2 * (C₁ + C₂ + 2) / (K : ℝ)) * ((x : ℝ) / Real.log x) := by
        field_simp
      have hcoef : 2 * (C₁ + C₂ + 2) / (K : ℝ) ≤ 1 / 5 := by
        rw [div_le_div_iff₀ hKreal (by norm_num : (0 : ℝ) < 5)]
        linarith
      have hstep : (2 * (C₁ + C₂ + 2) / (K : ℝ)) * ((x : ℝ) / Real.log x) ≤
          (1 / 5) * ((x : ℝ) / Real.log x) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      calc (C₁ + C₂ + 2) * (x' : ℝ) / Real.log x'
          = (C₁ + C₂ + 2) * ((x' : ℝ) / Real.log x') := by ring
        _ ≤ (C₁ + C₂ + 2) * (((x : ℝ) / (K : ℝ)) / (Real.log x / 2)) := hmul
        _ = (2 * (C₁ + C₂ + 2) / (K : ℝ)) * ((x : ℝ) / Real.log x) := hsimp
        _ ≤ (1 / 5) * ((x : ℝ) / Real.log x) := hstep
        _ = (x : ℝ) / (5 * Real.log x) := by ring
    exact hUcard_real.trans (hfrac.trans hThird)
  have hUleR : U.card ≤ ((Finset.Ioc (x / 3) x).filter Nat.Prime).card := by
    exact_mod_cast hUleR_real
  have hxx : x' ≤ x / 3 := Nat.div_le_div_left (by omega : 3 ≤ K) (by omega)
  have hcov : Green46.IsCoveredByResidues x y' :=
    greedy_cover_of_card_le hwz' hzx' hxx a b hUleR
  have hyY : y' ≤ Erdos687.Y x := le_Y_of_isCovered hcov
  have hyY_real : (y' : ℝ) ≤ (Erdos687.Y x : ℝ) := by exact_mod_cast hyY
  have hfx_nonneg : 0 ≤ (x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) /
      Real.log (Real.log x) := by positivity
  rw [Real.norm_of_nonneg hfx_nonneg, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hKreal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hmul : (16 * (K : ℝ) / c) * (c / (16 * (K : ℝ))) = 1 := by field_simp
  calc (x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)
      = (16 * (K : ℝ) / c) * (c / (16 * (K : ℝ)) *
          ((x : ℝ) * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x))) := by
        rw [← mul_assoc, hmul, one_mul]
    _ ≤ (16 * (K : ℝ) / c) * (y' : ℝ) :=
        mul_le_mul_of_nonneg_left hy'ge (by positivity)
    _ ≤ (16 * (K : ℝ) / c) * (Erdos687.Y x : ℝ) :=
        mul_le_mul_of_nonneg_left hyY_real (by positivity)

end OMA.R_Erdos687_erdos_687_variants_fgkmt_R1
