import FormalConjectures.OEIS.«69004»
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log

/-!
# Disproof of `OeisA69004.conjecture2.variants.without_upper_bound`

We prove unconditionally that there exists `n > 1` with `5 * OeisA69004.a n < Nat.primeCounting n`,
refuting the conjecture `(∀ n > 1, 5 * a n ≥ π(n)) ∧ ...`.

The proof combines four elementary ingredients:
1. Chebyshev's lower bound `2 * m ≤ (Nat.log 2 (2 * m) + 1) * (π(2 * m) + 2)`.
2. Unboundedness of `∏_{p ∈ P3} p / (p - 1)` over finite sets `P3` of primes `p ≡ 3 (mod 4)`,
   via finite Euler products for `ζ(s)` and `L(s, χ₄)` as `s → 1⁺`.
3. A lower bound `S₁(2 * 4^K) ≥ (K - 1) / 192` on the squarefree `p ≡ 1 (mod 4)` sieve sum,
   via disjoint dyadic boxes and primitive sums of two squares.
4. Selberg's `Λ²` sieve upper bound on `a(n)` for `n = 2^r * ∏_{p ∈ P3} p`.
-/

namespace OeisA69004Disproof

open Finset BigOperators

/- ### Section 1: Chebyshev's elementary lower bound on `Nat.primeCounting` -/

private lemma pow_factorization_choose_le (m p : ℕ) (hm : 1 ≤ m) (hp : p.Prime) :
    p ^ (((2 * m).choose m).factorization p) ≤ 2 * m := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  have hval : padicValNat p ((2 * m).choose m) ≤ Nat.log p (2 * m) := by
    rw [padicValNat_choose (by omega) (Nat.lt_succ_self _)]
    calc #{i ∈ Finset.Ico 1 (Nat.log p (2 * m) + 1) |
            p ^ i ≤ m % p ^ i + (2 * m - m) % p ^ i}
        ≤ #(Finset.Ico 1 (Nat.log p (2 * m) + 1)) := card_filter_le _ _
      _ = Nat.log p (2 * m) := by simp
  calc p ^ padicValNat p ((2 * m).choose m)
      ≤ p ^ Nat.log p (2 * m) := Nat.pow_le_pow_right hp.pos hval
    _ ≤ 2 * m := Nat.pow_log_le_self p (by omega)

private lemma chebyshev_primeCounting_lower (m : ℕ) (hm : 1 ≤ m) :
    2 * m ≤ (Nat.log 2 (2 * m) + 1) * (Nat.primeCounting (2 * m) + 2) := by
  have h2m_pos : 0 < 2 * m := by omega
  have hchoose_pos : 0 < (2 * m).choose m := Nat.choose_pos (by omega)
  have h1 : 2 ^ (2 * m) ≤ (2 * m + 1) * (2 * m).choose m := by
    rw [← Nat.sum_range_choose (2 * m)]
    calc ∑ k ∈ range (2 * m + 1), (2 * m).choose k
        ≤ ∑ _k ∈ range (2 * m + 1), (2 * m).choose m := by
          refine sum_le_sum fun k _ => ?_
          have := Nat.choose_le_middle k (2 * m)
          simpa [Nat.mul_div_cancel_left m (by decide : 0 < 2)] using this
      _ = (2 * m + 1) * (2 * m).choose m := by simp
  have h2 : (2 * m).choose m ≤ (2 * m) ^ Nat.primeCounting (2 * m) := by
    have hfac := Nat.prod_factorization_pow_eq_self hchoose_pos.ne'
    rw [Finsupp.prod, Nat.support_factorization] at hfac
    have hsub : ((2 * m).choose m).primeFactors ⊆ Nat.primesLE (2 * m) := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      rw [Nat.mem_primesLE]
      refine ⟨?_, hp.1⟩
      have hdvd_fact : p ∣ (2 * m).factorial := by
        have hmul := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
        exact hp.2.1.trans ⟨m.factorial * (2 * m - m).factorial, by linarith⟩
      exact (hp.1.dvd_factorial).mp hdvd_fact
    calc (2 * m).choose m
        = ∏ p ∈ ((2 * m).choose m).primeFactors, p ^ (((2 * m).choose m).factorization p) :=
          hfac.symm
      _ ≤ ∏ p ∈ ((2 * m).choose m).primeFactors, (2 * m) := by
          refine prod_le_prod' fun p hp => ?_
          exact pow_factorization_choose_le m p hm (Nat.prime_of_mem_primeFactors hp)
      _ = (2 * m) ^ #(((2 * m).choose m).primeFactors) := by simp
      _ ≤ (2 * m) ^ #(Nat.primesLE (2 * m)) :=
          Nat.pow_le_pow_right h2m_pos (card_le_card hsub)
      _ = (2 * m) ^ Nat.primeCounting (2 * m) := by rw [Nat.primesLE_card_eq_primeCounting]
  have h3 : 2 ^ (2 * m) ≤ (2 * m) ^ (Nat.primeCounting (2 * m) + 2) := by
    have hlin : 2 * m + 1 ≤ (2 * m) ^ 2 := by nlinarith
    calc 2 ^ (2 * m)
        ≤ (2 * m + 1) * (2 * m).choose m := h1
      _ ≤ (2 * m) ^ 2 * (2 * m) ^ Nat.primeCounting (2 * m) :=
          Nat.mul_le_mul hlin h2
      _ = (2 * m) ^ (Nat.primeCounting (2 * m) + 2) := by ring
  have h4 : 2 * m ≤ 2 ^ (Nat.log 2 (2 * m) + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (2 * m)).le
  have h5 : 2 ^ (2 * m) ≤ 2 ^ ((Nat.log 2 (2 * m) + 1) * (Nat.primeCounting (2 * m) + 2)) := by
    calc 2 ^ (2 * m)
        ≤ (2 * m) ^ (Nat.primeCounting (2 * m) + 2) := h3
      _ ≤ (2 ^ (Nat.log 2 (2 * m) + 1)) ^ (Nat.primeCounting (2 * m) + 2) :=
          Nat.pow_le_pow_left h4 _
      _ = 2 ^ ((Nat.log 2 (2 * m) + 1) * (Nat.primeCounting (2 * m) + 2)) := by rw [← pow_mul]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h5

/- ### Section 2: Unboundedness of `prod_{p in P3} p / (p - 1)` for primes `p = 3 mod 4` -/

private def chi4Fun (n : ℕ) : ℝ :=
  if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1

private lemma chi4Fun_zero : chi4Fun 0 = 0 := by simp [chi4Fun]
private lemma chi4Fun_one : chi4Fun 1 = 1 := by simp [chi4Fun]

private lemma chi4Fun_mul (a b : ℕ) : chi4Fun (a * b) = chi4Fun a * chi4Fun b := by
  have hmod2 : ∀ k : ℕ, k % 2 = (k % 4) % 2 := fun k => by omega
  have hmul4 : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Nat.mul_mod a b 4
  have ha : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hb : b % 4 < 4 := Nat.mod_lt b (by decide)
  simp only [chi4Fun, hmod2 (a * b), hmod2 a, hmod2 b, hmul4]
  generalize a % 4 = x at ha ⊢
  generalize b % 4 = y at hb ⊢
  interval_cases x <;> interval_cases y <;> norm_num

private noncomputable def zetaTerm (s : ℝ) (hs : s ≠ 0) : ℕ →*₀ ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_zero' := by simp [Real.zero_rpow (neg_ne_zero.mpr hs)]
  map_one' := by simp
  map_mul' a b := by
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

private noncomputable def chi4Term (s : ℝ) : ℕ →*₀ ℝ where
  toFun n := chi4Fun n * (n : ℝ) ^ (-s)
  map_zero' := by simp [chi4Fun_zero]
  map_one' := by simp [chi4Fun_one]
  map_mul' a b := by
    rw [chi4Fun_mul]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
    ring

private lemma summable_norm_zetaTerm {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ‖zetaTerm s (by linarith) n‖) := by
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) := Real.summable_nat_rpow_inv.mpr hs
  refine hsum.congr fun n => ?_
  change ((n : ℝ) ^ s)⁻¹ = ‖(n : ℝ) ^ (-s)‖
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]

private lemma summable_norm_chi4Term {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ‖chi4Term s n‖) := by
  refine (summable_norm_zetaTerm hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  change ‖chi4Fun n * (n : ℝ) ^ (-s)‖ ≤ ‖(n : ℝ) ^ (-s)‖
  rw [norm_mul]
  have hle : ‖chi4Fun n‖ ≤ 1 := by
    simp only [chi4Fun]
    split_ifs <;> norm_num
  calc ‖chi4Fun n‖ * ‖(n : ℝ) ^ (-s)‖ ≤ 1 * ‖(n : ℝ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = ‖(n : ℝ) ^ (-s)‖ := one_mul _

private lemma tsum_chi4Term_le_one {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, chi4Term s n ≤ 1 := by
  have hsum : Summable (fun n : ℕ => chi4Term s n) :=
    (summable_norm_chi4Term hs).of_norm
  have htend : Filter.Tendsto (fun K : ℕ => ∑ n ∈ range (4 * K + 2), chi4Term s n)
      Filter.atTop (nhds (∑' n : ℕ, chi4Term s n)) := by
    refine hsum.hasSum.tendsto_sum_nat.comp ?_
    exact Filter.tendsto_atTop_mono (fun K => by omega : ∀ K, K ≤ 4 * K + 2) Filter.tendsto_id
  refine le_of_tendsto htend (Filter.Eventually.of_forall fun K => ?_)
  induction K with
  | zero =>
    simp [Finset.sum_range_succ, chi4Term, chi4Fun]
  | succ K ih =>
    have hsplit : ∑ n ∈ range (4 * (K + 1) + 2), chi4Term s n =
        (∑ n ∈ range (4 * K + 2), chi4Term s n) +
        (chi4Term s (4 * K + 2) + chi4Term s (4 * K + 3) +
         chi4Term s (4 * K + 4) + chi4Term s (4 * K + 5)) := by
      have : 4 * (K + 1) + 2 = (4 * K + 2) + 4 := by omega
      rw [this, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      ring
    rw [hsplit]
    have h2 : chi4Fun (4 * K + 2) = 0 := by simp [chi4Fun]; omega
    have h3 : chi4Fun (4 * K + 3) = -1 := by
      simp only [chi4Fun]
      rw [if_neg (by omega), if_neg (by omega)]
    have h4 : chi4Fun (4 * K + 4) = 0 := by simp [chi4Fun]; omega
    have h5 : chi4Fun (4 * K + 5) = 1 := by
      simp only [chi4Fun]
      rw [if_neg (by omega), if_pos (by omega)]
    have hblock : chi4Term s (4 * K + 2) + chi4Term s (4 * K + 3) +
        chi4Term s (4 * K + 4) + chi4Term s (4 * K + 5) ≤ 0 := by
      simp only [chi4Term, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, h2, h3, h4, h5]
      have hle : ((4 * K + 5 : ℕ) : ℝ) ^ (-s) ≤ ((4 * K + 3 : ℕ) : ℝ) ^ (-s) := by
        rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
        refine inv_anti₀ (Real.rpow_pos_of_pos (by positivity) s) ?_
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : 4 * K + 3 ≤ 4 * K + 5))
          (by linarith)
      linarith
    linarith

private lemma exists_finset_primes_mod4_eq3_prod_gt (B : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p % 4 = 3) ∧
      B < ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) := by
  by_contra h
  push Not at h
  set B' : ℝ := max B 1 with hB'_def
  have hB'_pos : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hbound_all : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p % 4 = 3) →
      ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) ≤ B' := fun P hP =>
    (h P hP).trans (le_max_left B 1)
  have hzeta_le : ∀ s : ℝ, (hs : 1 < s) → ∑' n : ℕ, zetaTerm s (by linarith) n ≤ 2 * B' ^ 2 := by
    intro s hs
    have hs0 : s ≠ 0 := by linarith
    have ht1 := EulerProduct.eulerProduct_completely_multiplicative (summable_norm_zetaTerm hs)
    have ht2 := EulerProduct.eulerProduct_completely_multiplicative (summable_norm_chi4Term hs)
    have hprod_le : ∀ N : ℕ,
        ∏ p ∈ Nat.primesBelow N, (1 - zetaTerm s hs0 p)⁻¹ ≤
        (2 * B' ^ 2) * ∏ p ∈ Nat.primesBelow N, (1 - chi4Term s p)⁻¹ := by
      intro N
      have hpos2 : 0 < ∏ p ∈ Nat.primesBelow N, (1 - chi4Term s p)⁻¹ := by
        refine prod_pos fun p hp => inv_pos.mpr ?_
        have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
        have hlt : chi4Term s p < 1 := by
          change chi4Fun p * (p : ℝ) ^ (-s) < 1
          have h1 : (p : ℝ) ^ (-s) < 1 := by
            rw [Real.rpow_neg (Nat.cast_nonneg p)]
            refine inv_lt_one_of_one_lt₀ ?_
            exact Real.one_lt_rpow (by exact_mod_cast hp'.one_lt) (by linarith)
          have h2 : chi4Fun p ≤ 1 := by simp only [chi4Fun]; split_ifs <;> norm_num
          have h3 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg p) _
          nlinarith
        linarith
      rw [← div_le_iff₀ hpos2, ← prod_div_distrib]
      have hratio : ∀ p ∈ Nat.primesBelow N,
          (1 - zetaTerm s hs0 p)⁻¹ / (1 - chi4Term s p)⁻¹ ≤
          (if p = 2 then (2 : ℝ) else if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 else 1) := by
        intro p hp
        have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
        have hps_le : (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ := by
          rw [Real.rpow_neg (by linarith)]
          refine inv_anti₀ (by linarith) ?_
          have : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ s :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
          simpa using this
        have h1sub_pos : 0 < 1 - (p : ℝ) ^ (-s) := by
          have : (p : ℝ)⁻¹ ≤ 1 / 2 := by
            rw [one_div]; exact inv_anti₀ (by positivity) hp2
          linarith
        change (1 - (p : ℝ) ^ (-s))⁻¹ / (1 - chi4Fun p * (p : ℝ) ^ (-s))⁻¹ ≤ _
        rw [inv_div_inv]
        by_cases hpeq2 : p = 2
        · subst hpeq2
          simp only [↓reduceIte, chi4Fun, Nat.mod_self, zero_mul, sub_zero]
          have hle2 : ((2 : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
            calc ((2 : ℕ) : ℝ) ^ (-s) ≤ ((2 : ℕ) : ℝ)⁻¹ := hps_le
              _ = 1 / 2 := by norm_num
          rw [div_le_iff₀ h1sub_pos]
          norm_num at hle2 ⊢
          linarith
        · simp only [hpeq2, ↓reduceIte]
          have hodd : p % 2 = 1 := hp'.odd_of_ne_two hpeq2 |> Nat.odd_iff.mp
          have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
          rcases hmod4 with h4 | h4
          · simp only [↓reduceIte, chi4Fun, hodd, h4]
            norm_num
            rw [div_self h1sub_pos.ne']
          · simp only [h4, ↓reduceIte, chi4Fun, hodd]
            norm_num
            have hnum : 1 - -1 * (p : ℝ) ^ (-s) = 1 + (p : ℝ) ^ (-s) := by ring
            have h1 : (1 + (p : ℝ) ^ (-s)) / (1 - (p : ℝ) ^ (-s)) ≤
                (1 - (p : ℝ) ^ (-s))⁻¹ ^ 2 := by
              rw [div_le_iff₀ h1sub_pos, inv_pow, mul_comm, ← div_eq_mul_inv,
                le_div_iff₀ (sq_pos_of_pos h1sub_pos)]
              nlinarith [sq_nonneg ((p : ℝ) ^ (-s))]
            have h2 : (1 - (p : ℝ) ^ (-s))⁻¹ ≤ (p : ℝ) / ((p : ℝ) - 1) := by
              have hne1 : (p : ℝ) - 1 ≠ 0 := by linarith
              have hpne : (p : ℝ) ≠ 0 := by linarith
              have heq : (p : ℝ) / ((p : ℝ) - 1) = (1 - (p : ℝ)⁻¹)⁻¹ := by
                field_simp [hne1, hpne]
              rw [heq]
              exact inv_anti₀ (by
                have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by positivity) hp2
                linarith) (by linarith)
            exact h1.trans (pow_le_pow_left₀ (inv_nonneg.mpr h1sub_pos.le) h2 2)
      calc ∏ p ∈ Nat.primesBelow N, (1 - zetaTerm s hs0 p)⁻¹ / (1 - chi4Term s p)⁻¹
          ≤ ∏ p ∈ Nat.primesBelow N,
              (if p = 2 then (2 : ℝ) else if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 else 1) := by
            refine prod_le_prod (fun p hp => ?_) hratio
            have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
            have hps_le : (p : ℝ) ^ (-s) ≤ 1 / 2 := by
              rw [Real.rpow_neg (by linarith), one_div]
              refine inv_anti₀ (by positivity) ?_
              calc (2 : ℝ) ≤ (p : ℝ) := hp2
                _ = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ (p : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
            have h1 : 0 ≤ (1 - zetaTerm s hs0 p)⁻¹ := by
              refine inv_nonneg.mpr ?_
              change 0 ≤ 1 - (p : ℝ) ^ (-s)
              linarith
            have h2 : 0 ≤ (1 - chi4Term s p)⁻¹ := by
              refine inv_nonneg.mpr ?_
              change 0 ≤ 1 - chi4Fun p * (p : ℝ) ^ (-s)
              have : chi4Fun p ≤ 1 := by simp only [chi4Fun]; split_ifs <;> norm_num
              have h3 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (by linarith) _
              nlinarith
            exact div_nonneg h1 h2
        _ ≤ 2 * (∏ p ∈ (Nat.primesBelow N).filter (fun p => p % 4 = 3),
              ((p : ℝ) / ((p : ℝ) - 1))) ^ 2 := by
            rw [← prod_pow]
            set S3 := (Nat.primesBelow N).filter (fun p => p % 4 = 3)
            have hprod_split :
                ∏ p ∈ Nat.primesBelow N,
                  (if p = 2 then (2 : ℝ) else if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 else 1) =
                (if 2 ∈ Nat.primesBelow N then (2 : ℝ) else 1) *
                ∏ p ∈ S3, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
              have h1 : ∀ p ∈ Nat.primesBelow N,
                  (if p = 2 then (2 : ℝ) else if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 else 1) =
                  (if p = 2 then (2 : ℝ) else 1) *
                  (if p % 4 = 3 then ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 else 1) := by
                intro p _
                by_cases h2 : p = 2
                · subst h2; norm_num
                · simp [h2]
              rw [prod_congr rfl h1, prod_mul_distrib, prod_ite_eq', prod_filter]
            rw [hprod_split]
            have h2le : (if 2 ∈ Nat.primesBelow N then (2 : ℝ) else 1) ≤ 2 := by
              split_ifs <;> norm_num
            have hnn : 0 ≤ ∏ p ∈ S3, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 :=
              prod_nonneg fun p _ => sq_nonneg _
            exact mul_le_mul_of_nonneg_right h2le hnn
        _ ≤ 2 * B' ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            have hP3 : ∀ p ∈ (Nat.primesBelow N).filter (fun p => p % 4 = 3),
                p.Prime ∧ p % 4 = 3 := by
              intro p hp
              rw [mem_filter, Nat.mem_primesBelow] at hp
              exact ⟨hp.1.2, hp.2⟩
            have hnn : 0 ≤ ∏ p ∈ (Nat.primesBelow N).filter (fun p => p % 4 = 3),
                ((p : ℝ) / ((p : ℝ) - 1)) := by
              refine prod_nonneg fun p hp => ?_
              have hp' := (hP3 p hp).1
              have : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
              exact div_nonneg (by linarith) (by linarith)
            exact pow_le_pow_left₀ hnn (hbound_all _ hP3) 2
    have hlim : ∑' n : ℕ, zetaTerm s hs0 n ≤ (2 * B' ^ 2) * ∑' n : ℕ, chi4Term s n :=
      le_of_tendsto_of_tendsto' ht1 (ht2.const_mul (2 * B' ^ 2)) hprod_le
    calc ∑' n : ℕ, zetaTerm s hs0 n
        ≤ (2 * B' ^ 2) * ∑' n : ℕ, chi4Term s n := hlim
      _ ≤ (2 * B' ^ 2) * 1 := mul_le_mul_of_nonneg_left (tsum_chi4Term_le_one hs) (by positivity)
      _ = 2 * B' ^ 2 := mul_one _
  have hharm := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [Filter.tendsto_atTop_atTop] at hharm
  obtain ⟨N, hN⟩ := hharm (4 * B' ^ 2)
  have hN_gt : 2 * B' ^ 2 < ∑ k ∈ range N, (1 : ℝ) / ((k : ℝ) + 1) := by
    have := hN N le_rfl
    nlinarith [sq_pos_of_pos hB'_pos]
  have hcont : Continuous (fun s : ℝ => ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (-s)) := by
    refine continuous_finsetSum _ fun k _ => ?_
    exact (continuous_const.rpow continuous_neg (fun _ => Or.inl (by positivity)))
  have hat1 : (∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (-(1 : ℝ))) =
      ∑ k ∈ range N, (1 : ℝ) / ((k : ℝ) + 1) := by
    refine sum_congr rfl fun k _ => ?_
    rw [Real.rpow_neg_one, one_div]
    push_cast
    rfl
  have hnhds : ∀ᶠ s in nhds (1 : ℝ), 2 * B' ^ 2 < ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (-s) := by
    refine hcont.continuousAt.eventually (lt_mem_nhds ?_)
    dsimp only
    rwa [hat1]
  rw [Metric.eventually_nhds_iff] at hnhds
  obtain ⟨δ, hδ, hball⟩ := hnhds
  set s : ℝ := 1 + δ / 2 with hs_def
  have hs1 : 1 < s := by linarith
  have hsdist : dist s 1 < δ := by
    rw [Real.dist_eq, show s - 1 = δ / 2 by linarith, abs_of_pos (by linarith)]
    linarith
  have hfin_gt : 2 * B' ^ 2 < ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (-s) := hball hsdist
  have hfin_le : ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (-s) ≤ ∑' n : ℕ, zetaTerm s (by linarith) n := by
    have hsum : Summable (fun n : ℕ => zetaTerm s (by linarith) n) :=
      (summable_norm_zetaTerm hs1).of_norm
    have hnn : ∀ n : ℕ, 0 ≤ zetaTerm s (by linarith) n := fun n =>
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hfin := hsum.sum_le_tsum (Finset.Icc 1 N) (fun n _ => hnn n)
    have heq : ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (-s) =
        ∑ n ∈ Finset.Icc 1 N, zetaTerm s (by linarith) n := by
      refine Finset.sum_bij (fun k _ => k + 1) (fun k hk => ?_) (fun _ _ _ _ h => by omega)
        (fun n hn => ⟨n - 1, ?_, by rw [mem_Icc] at hn; omega⟩) (fun k _ => rfl)
      · rw [mem_range] at hk; rw [mem_Icc]; omega
      · rw [mem_Icc] at hn; rw [mem_range]; omega
    rwa [heq]
  linarith [hzeta_le s hs1]

/- ### Section 3: Lower bound on `S_1(X)` via primitive sums of two squares -/

private lemma card_sq_eq_neg_one_zmod_prime_pow (p e : ℕ) [NeZero (p ^ e)]
    (hp : p.Prime) (hodd : p ≠ 2) :
    #{x : ZMod (p ^ e) | x ^ 2 = -1} ≤ 2 := by
  by_cases he : e = 0
  · subst he
    calc #{x : ZMod (p ^ 0) | x ^ 2 = -1} ≤ Fintype.card (ZMod (p ^ 0)) := card_le_univ _
      _ = 1 := by simp
      _ ≤ 2 := by decide
  by_cases hemp : ({x : ZMod (p ^ e) | x ^ 2 = -1} : Finset (ZMod (p ^ e))).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hemp
    rw [mem_filter] at hx₀
    have hsub : ({x : ZMod (p ^ e) | x ^ 2 = -1} : Finset (ZMod (p ^ e))) ⊆ {x₀, -x₀} := by
      intro y hy
      rw [mem_filter] at hy
      rw [mem_insert, mem_singleton]
      have hdiff : (y - x₀) * (y + x₀) = 0 := by
        linear_combination hy.2 - hx₀.2
      have hz_dvd : ((p ^ e : ℕ) : ℤ) ∣ ((y.val : ℤ) - x₀.val) * ((y.val : ℤ) + x₀.val) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        simpa [ZMod.natCast_zmod_val] using hdiff
      have hnotboth : ¬ ((p : ℤ) ∣ ((y.val : ℤ) - x₀.val) ∧ (p : ℤ) ∣ ((y.val : ℤ) + x₀.val)) := by
        rintro ⟨hd1, hd2⟩
        have hd2x : (p : ℤ) ∣ 2 * (x₀.val : ℤ) := by
          have : 2 * (x₀.val : ℤ) = ((y.val : ℤ) + x₀.val) - ((y.val : ℤ) - x₀.val) := by ring
          rw [this]
          exact dvd_sub hd2 hd1
        have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        have hpx : (p : ℤ) ∣ (x₀.val : ℤ) := by
          rcases hpz.dvd_or_dvd hd2x with h2 | hx
          · exfalso
            have h2' : p ∣ 2 := Int.ofNat_dvd.mp h2
            have := Nat.le_of_dvd (by decide) h2'
            have := hp.two_le
            omega
          · exact hx
        have hx0_sq : ((p : ℕ) : ℤ) ∣ (x₀.val : ℤ) ^ 2 + 1 := by
          have hdvd_pe : ((p ^ e : ℕ) : ℤ) ∣ (x₀.val : ℤ) ^ 2 + 1 := by
            rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
            push_cast
            simp [hx₀.2]
          exact (dvd_pow_self (p : ℤ) he).trans (by exact_mod_cast hdvd_pe)
        have hp1 : (p : ℤ) ∣ 1 := by
          have : (1 : ℤ) = ((x₀.val : ℤ) ^ 2 + 1) - (x₀.val : ℤ) * (x₀.val : ℤ) := by ring
          rw [this]
          exact dvd_sub hx0_sq (dvd_mul_of_dvd_left hpx _)
        exact hpz.not_isUnit (isUnit_of_dvd_one hp1)
      have hpz_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hcop_or : IsCoprime ((p ^ e : ℕ) : ℤ) ((y.val : ℤ) - x₀.val) ∨
          IsCoprime ((p ^ e : ℕ) : ℤ) ((y.val : ℤ) + x₀.val) := by
        by_cases h1 : (p : ℤ) ∣ ((y.val : ℤ) - x₀.val)
        · right
          have h2 : ¬ (p : ℤ) ∣ ((y.val : ℤ) + x₀.val) := fun h2 => hnotboth ⟨h1, h2⟩
          have hc : IsCoprime (p : ℤ) ((y.val : ℤ) + x₀.val) :=
            (hpz_prime.irreducible.coprime_iff_not_dvd).mpr h2
          simpa using hc.pow_left (m := e)
        · left
          have hc : IsCoprime (p : ℤ) ((y.val : ℤ) - x₀.val) :=
            (hpz_prime.irreducible.coprime_iff_not_dvd).mpr h1
          simpa using hc.pow_left (m := e)
      rcases hcop_or with hcop | hcop
      · right
        have hd : ((p ^ e : ℕ) : ℤ) ∣ ((y.val : ℤ) + x₀.val) := hcop.dvd_of_dvd_mul_left hz_dvd
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
        push_cast at hd
        simp only [ZMod.natCast_zmod_val] at hd
        exact eq_neg_of_add_eq_zero_left hd
      · left
        have hd : ((p ^ e : ℕ) : ℤ) ∣ ((y.val : ℤ) - x₀.val) := hcop.dvd_of_dvd_mul_right hz_dvd
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
        push_cast at hd
        simp only [ZMod.natCast_zmod_val] at hd
        exact sub_eq_zero.mp hd
    calc #{x : ZMod (p ^ e) | x ^ 2 = -1} ≤ #({x₀, -x₀} : Finset (ZMod (p ^ e))) := card_le_card hsub
      _ ≤ 2 := card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hemp]
    simp

private lemma card_sq_eq_neg_one_zmod_mul {a b : ℕ} [NeZero a] [NeZero b] [NeZero (a * b)]
    (hcop : Nat.Coprime a b) :
    #{x : ZMod (a * b) | x ^ 2 = -1} =
      #{x : ZMod a | x ^ 2 = -1} * #{x : ZMod b | x ^ 2 = -1} := by
  let e := ZMod.chineseRemainder hcop
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => e x) (fun x hx => ?_) (fun x₁ _ x₂ _ h => e.injective h)
    (fun p hp => ?_)
  · rw [mem_filter] at hx
    rw [mem_product, mem_filter, mem_filter]
    have hmap : (e x) ^ 2 = -1 := by rw [← map_pow, hx.2, map_neg, map_one]
    exact ⟨⟨mem_univ _, congr_arg Prod.fst hmap⟩, ⟨mem_univ _, congr_arg Prod.snd hmap⟩⟩
  · rw [mem_product, mem_filter, mem_filter] at hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    rw [mem_filter]
    refine ⟨mem_univ _, e.injective ?_⟩
    rw [map_pow, e.apply_symm_apply, map_neg, map_one]
    exact Prod.ext hp.1.2 hp.2.2

private lemma card_sq_eq_neg_one_zmod_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    #{x : ZMod a | x ^ 2 = -1} = #{x : ZMod b | x ^ 2 = -1} := by
  subst h; rfl

private lemma coprime_right_sum_sq {a b : ℕ} (h : Nat.Coprime a b) :
    Nat.Coprime b (a ^ 2 + b ^ 2) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  set p := (Nat.gcd b (a ^ 2 + b ^ 2)).minFac
  have hp : p.Prime := Nat.minFac_prime hne
  have hpb : p ∣ b := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hps : p ∣ a ^ 2 + b ^ 2 := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  have hpa2 : p ∣ a ^ 2 := by
    have := Nat.dvd_sub hps (dvd_pow hpb (by decide : 2 ≠ 0))
    simpa using this
  exact hp.not_dvd_one (Nat.dvd_gcd (hp.dvd_of_dvd_pow hpa2) hpb |>.trans (by rw [h]))

private lemma card_sq_eq_neg_one_zmod_odd :
    ∀ m : ℕ, [NeZero m] → Odd m → #{x : ZMod m | x ^ 2 = -1} ≤ 2 ^ m.primeFactors.card := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hne hm
    by_cases hm1 : m ≤ 1
    · have hmeq : m = 1 := by obtain ⟨k, rfl⟩ := hm; omega
      subst hmeq
      have : Fintype.card (ZMod 1) = 1 := ZMod.card 1
      calc #{x : ZMod 1 | x ^ 2 = -1} ≤ Fintype.card (ZMod 1) := card_le_univ _
        _ = 1 := this
        _ ≤ 2 ^ (1 : ℕ).primeFactors.card := by simp
    · push Not at hm1
      have hne0 : m ≠ 0 := by omega
      set p := m.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ m := Nat.minFac_dvd m
      have hodd_p : p ≠ 2 := by
        intro hp2
        rw [hp2] at hpdvd
        exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hpdvd)
      set e := m.factorization p with he_def
      have he_pos : 0 < e := hp.factorization_pos_of_dvd hne0 hpdvd
      have hpe_dvd : p ^ e ∣ m := Nat.ordProj_dvd m p
      set m' := m / p ^ e
      have hmul : p ^ e * m' = m := Nat.mul_div_cancel' hpe_dvd
      have hm'_pos : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | hpos
        · rw [h0, mul_zero] at hmul; exact absurd hmul.symm hne0
        · exact hpos
      have hm'_lt : m' < m := by
        have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt he_pos.ne'
        calc m' = 1 * m' := (one_mul m').symm
          _ < p ^ e * m' := Nat.mul_lt_mul_of_pos_right hpe_gt1 hm'_pos
          _ = m := hmul
      have hcop : Nat.Coprime (p ^ e) m' := by
        refine Nat.Coprime.pow_left e ?_
        rw [hp.coprime_iff_not_dvd]
        intro hpm'
        have hd : p ^ (e + 1) ∣ m := by
          rw [pow_succ, ← hmul]
          exact mul_dvd_mul_left (p ^ e) hpm'
        have hle := (hp.pow_dvd_iff_le_factorization hne0).mp hd
        rw [← he_def] at hle
        omega
      have hm'_odd : Odd m' := by
        rw [← hmul] at hm
        exact (Nat.odd_mul.mp hm).2
      have hpf : m.primeFactors = insert p m'.primeFactors := by
        rw [← hmul, Nat.primeFactors_mul (pow_ne_zero e hp.ne_zero) hm'_pos.ne',
          Nat.primeFactors_pow p he_pos.ne', hp.primeFactors]
        simp
      have hp_not_mem : p ∉ m'.primeFactors := by
        rw [Nat.mem_primeFactors]
        rintro ⟨_, hpm', _⟩
        have hcop1 : Nat.Coprime p m' := (Nat.coprime_pow_left_iff he_pos p m').mp hcop
        exact hp.not_dvd_one (hcop1.dvd_of_dvd_mul_right (dvd_mul_of_dvd_right hpm' _))
      have hcard_pf : m.primeFactors.card = m'.primeFactors.card + 1 := by
        rw [hpf, card_insert_of_notMem hp_not_mem]
      have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
      have : NeZero m' := ⟨hm'_pos.ne'⟩
      have : NeZero (p ^ e * m') := ⟨mul_ne_zero (pow_ne_zero e hp.ne_zero) hm'_pos.ne'⟩
      rw [card_sq_eq_neg_one_zmod_congr hmul.symm, card_sq_eq_neg_one_zmod_mul hcop, hcard_pf,
        pow_succ']
      exact Nat.mul_le_mul (card_sq_eq_neg_one_zmod_prime_pow p e hp hodd_p)
        (ih m' hm'_lt hm'_odd)

private lemma card_prim_sum_two_sq (m : ℕ) (hm : Odd m) :
    #{ab ∈ Icc 1 m ×ˢ Icc 1 m | ab.1 ^ 2 + ab.2 ^ 2 = m ∧ Nat.Coprime ab.1 ab.2} ≤
      2 ^ m.primeFactors.card := by
  have hm_ne0 : m ≠ 0 := by obtain ⟨k, rfl⟩ := hm; omega
  have : NeZero m := ⟨hm_ne0⟩
  calc #{ab ∈ Icc 1 m ×ˢ Icc 1 m | ab.1 ^ 2 + ab.2 ^ 2 = m ∧ Nat.Coprime ab.1 ab.2}
      ≤ #{x : ZMod m | x ^ 2 = -1} := by
        refine Finset.card_le_card_of_injOn
          (fun ab : ℕ × ℕ => (ab.1 : ZMod m) * (ab.2 : ZMod m)⁻¹) ?_ ?_
        · intro ab hab
          simp only [mem_coe, mem_filter, mem_product, mem_Icc] at hab
          simp only [mem_coe, mem_filter, mem_univ, true_and]
          have hcop_bm : Nat.Coprime ab.2 m := by
            rw [← hab.2.1]
            exact coprime_right_sum_sq hab.2.2
          have hunit : IsUnit (ab.2 : ZMod m) := (ZMod.isUnit_iff_coprime ab.2 m).mpr hcop_bm
          have hmul_inv : (ab.2 : ZMod m) * (ab.2 : ZMod m)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit
          have hsq : (ab.1 : ZMod m) ^ 2 + (ab.2 : ZMod m) ^ 2 = 0 := by
            have : ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ZMod m) = (m : ZMod m) := by rw [hab.2.1]
            simpa using this
          calc ((ab.1 : ZMod m) * (ab.2 : ZMod m)⁻¹) ^ 2
              = (ab.1 : ZMod m) ^ 2 * ((ab.2 : ZMod m)⁻¹) ^ 2 := by ring
            _ = (-(ab.2 : ZMod m) ^ 2) * ((ab.2 : ZMod m)⁻¹) ^ 2 := by
                rw [eq_neg_of_add_eq_zero_left hsq]
            _ = -((ab.2 : ZMod m) * (ab.2 : ZMod m)⁻¹) ^ 2 := by ring
            _ = -1 := by rw [hmul_inv, one_pow]
        · intro ab1 hab1 ab2 hab2 heq
          simp only [mem_coe, mem_filter, mem_product, mem_Icc] at hab1 hab2
          have hcop1 : Nat.Coprime ab1.2 m := by
            rw [← hab1.2.1]; exact coprime_right_sum_sq hab1.2.2
          have hcop2 : Nat.Coprime ab2.2 m := by
            rw [← hab2.2.1]; exact coprime_right_sum_sq hab2.2.2
          have hu1 : (ab1.2 : ZMod m) * (ab1.2 : ZMod m)⁻¹ = 1 :=
            ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hcop1)
          have hu2 : (ab2.2 : ZMod m) * (ab2.2 : ZMod m)⁻¹ = 1 :=
            ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hcop2)
          have hcross : (ab1.1 : ZMod m) * (ab2.2 : ZMod m) = (ab2.1 : ZMod m) * (ab1.2 : ZMod m) := by
            have h1 := congr_arg (fun z => z * (ab1.2 : ZMod m) * (ab2.2 : ZMod m)) heq
            calc (ab1.1 : ZMod m) * (ab2.2 : ZMod m)
                = (ab1.1 : ZMod m) * ((ab1.2 : ZMod m) * (ab1.2 : ZMod m)⁻¹) * (ab2.2 : ZMod m) := by
                  rw [hu1, mul_one]
              _ = ((ab1.1 : ZMod m) * (ab1.2 : ZMod m)⁻¹) * (ab1.2 : ZMod m) * (ab2.2 : ZMod m) := by ring
              _ = ((ab2.1 : ZMod m) * (ab2.2 : ZMod m)⁻¹) * (ab1.2 : ZMod m) * (ab2.2 : ZMod m) := h1
              _ = (ab2.1 : ZMod m) * ((ab2.2 : ZMod m) * (ab2.2 : ZMod m)⁻¹) * (ab1.2 : ZMod m) := by ring
              _ = (ab2.1 : ZMod m) * (ab1.2 : ZMod m) := by rw [hu2, mul_one]
          have hdvd : (m : ℤ) ∣ ((ab1.1 * ab2.2 : ℕ) : ℤ) - ((ab2.1 * ab1.2 : ℕ) : ℤ) := by
            rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
            push_cast
            exact sub_eq_zero.mpr hcross
          have hlt1 : ab1.1 * ab2.2 < m := by
            have h1 : ab1.1 ^ 2 < m := by
              have : 1 ≤ ab1.2 ^ 2 := Nat.one_le_pow 2 ab1.2 hab1.1.2.1
              omega
            have h2 : ab2.2 ^ 2 < m := by
              have : 1 ≤ ab2.1 ^ 2 := Nat.one_le_pow 2 ab2.1 hab2.1.1.1
              omega
            have hsq : (ab1.1 * ab2.2) ^ 2 < m ^ 2 := by
              rw [mul_pow, sq m]; exact Nat.mul_lt_mul'' h1 h2
            exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le m) hsq
          have hlt2 : ab2.1 * ab1.2 < m := by
            have h1 : ab2.1 ^ 2 < m := by
              have : 1 ≤ ab2.2 ^ 2 := Nat.one_le_pow 2 ab2.2 hab2.1.2.1
              omega
            have h2 : ab1.2 ^ 2 < m := by
              have : 1 ≤ ab1.1 ^ 2 := Nat.one_le_pow 2 ab1.1 hab1.1.1.1
              omega
            have hsq : (ab2.1 * ab1.2) ^ 2 < m ^ 2 := by
              rw [mul_pow, sq m]; exact Nat.mul_lt_mul'' h1 h2
            exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le m) hsq
          have hzero : ((ab1.1 * ab2.2 : ℕ) : ℤ) - ((ab2.1 * ab1.2 : ℕ) : ℤ) = 0 := by
            rcases hdvd with ⟨k, hk⟩
            have hlt1' : ((ab1.1 * ab2.2 : ℕ) : ℤ) < (m : ℤ) := by exact_mod_cast hlt1
            have hlt2' : ((ab2.1 * ab1.2 : ℕ) : ℤ) < (m : ℤ) := by exact_mod_cast hlt2
            have hm_pos : (0 : ℤ) < m := by omega
            have hk0 : k = 0 := by nlinarith
            rw [hk, hk0, mul_zero]
          have heq_nat : ab1.1 * ab2.2 = ab2.1 * ab1.2 := by omega
          have ha_eq : ab1.1 = ab2.1 := by
            have d1 : ab1.1 ∣ ab2.1 := hab1.2.2.dvd_of_dvd_mul_right ⟨ab2.2, heq_nat.symm⟩
            have d2 : ab2.1 ∣ ab1.1 := hab2.2.2.dvd_of_dvd_mul_right ⟨ab1.2, heq_nat⟩
            exact Nat.dvd_antisymm d1 d2
          have hb_eq : ab1.2 = ab2.2 := by
            rw [ha_eq] at heq_nat
            exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < ab2.1) heq_nat.symm
          exact Prod.ext ha_eq hb_eq
    _ ≤ 2 ^ m.primeFactors.card := card_sq_eq_neg_one_zmod_odd m hm

private lemma prime_mod4_eq1_of_dvd_prim_sum_sq {a b p : ℕ}
    (hp : p.Prime) (hodd : Odd (a ^ 2 + b ^ 2)) (hcop : Nat.Coprime a b) (hdvd : p ∣ a ^ 2 + b ^ 2) :
    p % 4 = 1 := by
  have hp_ne2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hpb : ¬ p ∣ b := by
    intro hpb
    have hpa2 : p ∣ a ^ 2 := by
      have hsub : p ∣ (a ^ 2 + b ^ 2) - b ^ 2 := Nat.dvd_sub hdvd (dvd_pow hpb (by decide : 2 ≠ 0))
      simpa using hsub
    have hpa : p ∣ a := hp.dvd_of_dvd_pow hpa2
    exact hp.not_dvd_one (Nat.dvd_gcd hpa hpb |>.trans (by rw [hcop]))
  have : Fact p.Prime := ⟨hp⟩
  have hb0 : (b : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hsq : ((a : ZMod p) * (b : ZMod p)⁻¹) ^ 2 = -1 := by
    have h0 : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
      have := (ZMod.natCast_eq_zero_iff (a ^ 2 + b ^ 2) p).mpr hdvd
      simpa using this
    calc ((a : ZMod p) * (b : ZMod p)⁻¹) ^ 2
        = (a : ZMod p) ^ 2 * ((b : ZMod p)⁻¹) ^ 2 := by ring
      _ = (-(b : ZMod p) ^ 2) * ((b : ZMod p)⁻¹) ^ 2 := by rw [eq_neg_of_add_eq_zero_left h0]
      _ = -((b : ZMod p) * (b : ZMod p)⁻¹) ^ 2 := by ring
      _ = -1 := by rw [mul_inv_cancel₀ hb0, one_pow]
  have h4 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp
    ⟨(a : ZMod p) * (b : ZMod p)⁻¹, by linear_combination -hsq⟩
  have hodd_p : p % 2 = 1 := (hp.odd_of_ne_two hp_ne2) |> Nat.odd_iff.mp
  omega

private lemma two_pow_card_primeFactors_le_sqrt {t : ℕ}
    (ht : ∀ p ∈ t.primeFactors, p % 4 = 1) (ht0 : t ≠ 0) :
    (2 : ℝ) ^ t.primeFactors.card ≤ Real.sqrt (t : ℝ) := by
  have h4 : 4 ^ t.primeFactors.card ≤ t := by
    have hprod_le : ∏ p ∈ t.primeFactors, p ≤ t := by
      have hdvd : ∏ p ∈ t.primeFactors, p ∣ t := Nat.prod_primeFactors_dvd t
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hdvd
    calc 4 ^ t.primeFactors.card
        = ∏ _p ∈ t.primeFactors, 4 := by simp
      _ ≤ ∏ p ∈ t.primeFactors, p := by
          refine prod_le_prod' fun p hp => ?_
          have hp' := Nat.prime_of_mem_primeFactors hp
          have h4' := ht p hp
          have := hp'.two_le
          omega
      _ ≤ t := hprod_le
  have hsq : ((2 : ℝ) ^ t.primeFactors.card) ^ 2 ≤ (t : ℝ) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
    exact_mod_cast h4
  exact Real.le_sqrt_of_sq_le hsq

private lemma sum_inv_sq_le_two (X : ℕ) :
    ∑ g ∈ Icc 1 X, (1 : ℝ) / ((g : ℝ) ^ 2) ≤ 2 := by
  have hstrong : ∀ N : ℕ, 1 ≤ N →
      ∑ g ∈ Icc 1 N, (1 : ℝ) / ((g : ℝ) ^ 2) ≤ 2 - 1 / (N : ℝ) := by
    intro N hN
    induction N with
    | zero => omega
    | succ k ih =>
      by_cases hk : k = 0
      · subst hk; norm_num
      · have hk1 : 1 ≤ k := by omega
        rw [show Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) by
          ext x; simp [mem_Icc]; omega]
        rw [sum_insert (by simp [mem_Icc])]
        have hkp : (0 : ℝ) < (k : ℝ) := by positivity
        have hk1p : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤
            1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
          have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [hcast, div_sub_div _ _ hkp.ne' (by linarith),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith [ih hk1]
  by_cases hX : X = 0
  · subst hX; simp
  · have h := hstrong X (by omega)
    have hnn : (0 : ℝ) ≤ 1 / (X : ℝ) := by positivity
    linarith

private lemma sum_sqrt_div_sq_le_three (X : ℕ) :
    ∑ t ∈ Icc 1 X, Real.sqrt (t : ℝ) / ((t : ℝ) ^ 2) ≤ 3 := by
  have hstrong : ∀ N : ℕ, 1 ≤ N →
      ∑ t ∈ Icc 1 N, Real.sqrt (t : ℝ) / ((t : ℝ) ^ 2) ≤ 3 - 2 / Real.sqrt (N : ℝ) := by
    intro N hN
    induction N with
    | zero => omega
    | succ k ih =>
      by_cases hk : k = 0
      · subst hk; norm_num
      · have hk1 : 1 ≤ k := by omega
        rw [show Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) by
          ext x; simp [mem_Icc]; omega]
        rw [sum_insert (by simp [mem_Icc])]
        have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
        have hsk1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
        have hle_sqrt : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)
        have hsq_diff : Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 - Real.sqrt (k : ℝ) ^ 2 = 1 := by
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
          push_cast; ring
        have hstep : Real.sqrt ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤
            2 / Real.sqrt (k : ℝ) - 2 / Real.sqrt ((k + 1 : ℕ) : ℝ) := by
          have hk1_sq : ((k + 1 : ℕ) : ℝ) = Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 :=
            (Real.sq_sqrt (by positivity)).symm
          rw [div_sub_div _ _ hsk.ne' hsk1.ne']
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          set u := Real.sqrt ((k + 1 : ℕ) : ℝ)
          set v := Real.sqrt (k : ℝ)
          have hvu : v ≤ u := hle_sqrt
          have hmul_eq : (2 * u - 2 * v) * (u + v) = 2 := by nlinarith [hsq_diff]
          have hu3v : u ^ 3 * v ≤ u ^ 4 := by
            have : u ^ 3 * v ≤ u ^ 3 * u := mul_le_mul_of_nonneg_left hvu (by positivity)
            linarith [show u ^ 3 * u = u ^ 4 by ring]
          have hu2v2 : u ^ 2 * v ^ 2 ≤ u ^ 4 := by
            have hv2 : v ^ 2 ≤ u ^ 2 := sq_le_sq' (by linarith) hvu
            have : u ^ 2 * v ^ 2 ≤ u ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_left hv2 (sq_nonneg u)
            linarith [show u ^ 2 * u ^ 2 = u ^ 4 by ring]
          have hkey : u * (v * u) * (u + v) ≤ 2 * (u ^ 2) ^ 2 := by
            have : u * (v * u) * (u + v) = u ^ 3 * v + u ^ 2 * v ^ 2 := by ring
            have : (u ^ 2) ^ 2 = u ^ 4 := by ring
            linarith
          rw [hk1_sq]
          have hpos_sum : 0 < u + v := by linarith
          nlinarith
        linarith [ih hk1]
  by_cases hX : X = 0
  · subst hX; simp
  · have h := hstrong X (by omega)
    have hnn : 0 ≤ 2 / Real.sqrt (X : ℝ) := by positivity
    linarith

private lemma sigma_lower_bound (K : ℕ) (hK : 2 ≤ K) :
    (((K : ℝ) - 1) / 32) ≤
      ∑ ab ∈ (Icc 1 (2 * 4 ^ K) ×ˢ Icc 1 (2 * 4 ^ K)).filter
        (fun ab : ℕ × ℕ => Odd ab.1 ∧ Even ab.2 ∧ ab.1 ^ 2 + ab.2 ^ 2 ≤ 2 * 4 ^ K),
        (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) := by
  set X : ℕ := 2 * 4 ^ K
  set Pairs := (Icc 1 X ×ˢ Icc 1 X).filter
    (fun ab : ℕ × ℕ => Odd ab.1 ∧ Even ab.2 ∧ ab.1 ^ 2 + ab.2 ^ 2 ≤ X)
  let B : ℕ → Finset (ℕ × ℕ) := fun k =>
      ((Ioc (2 ^ (k - 1)) (2 ^ k)).filter Odd) ×ˢ ((Ioc (2 ^ (k - 1)) (2 ^ k)).filter Even)
  have hsub : (Icc 2 K).biUnion B ⊆ Pairs := by
      intro ab hab
      rw [mem_biUnion] at hab
      obtain ⟨k, hk, habk⟩ := hab
      rw [mem_Icc] at hk
      simp only [B, mem_product, mem_filter, mem_Ioc] at habk
      have hsum_le : ab.1 ^ 2 + ab.2 ^ 2 ≤ X := by
        have h1 : ab.1 ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left habk.1.1.2 2
        have h2 : ab.2 ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left habk.2.1.2 2
        have h4 : (2 ^ k) ^ 2 = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have h4K : 4 ^ k ≤ 4 ^ K := Nat.pow_le_pow_right (by decide) hk.2
        omega
      have ha_pos : 1 ≤ ab.1 := by
        have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
        omega
      have hb_pos : 1 ≤ ab.2 := by
        have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
        omega
      have ha_le : ab.1 ≤ X := by nlinarith
      have hb_le : ab.2 ≤ X := by nlinarith
      simp only [Pairs, mem_filter, mem_product, mem_Icc]
      exact ⟨⟨⟨ha_pos, ha_le⟩, ⟨hb_pos, hb_le⟩⟩, habk.1.2, habk.2.2, hsum_le⟩
  have hdisj : Set.PairwiseDisjoint (↑(Icc 2 K) : Set ℕ) B := by
      intro k₁ _ k₂ _ hne
      change Disjoint (B k₁) (B k₂)
      rw [Finset.disjoint_left]
      intro ab h1 h2
      simp only [B, mem_product, mem_filter, mem_Ioc] at h1 h2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : 2 ^ k₁ ≤ 2 ^ (k₂ - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      · have hle : 2 ^ k₂ ≤ 2 ^ (k₁ - 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
  have hBk_card : ∀ k ∈ Icc 2 K, #(B k) = 2 ^ (2 * k - 4) := by
      intro k hk
      rw [mem_Icc] at hk
      simp only [B, card_product]
      have hodd_c : #((Ioc (2 ^ (k - 1)) (2 ^ k)).filter Odd) = 2 ^ (k - 2) := by
        have hbij : #((Ioc (2 ^ (k - 1)) (2 ^ k)).filter Odd) = #(range (2 ^ (k - 2))) := by
          refine Finset.card_bij (fun a _ => (a - 2 ^ (k - 1) - 1) / 2) ?_ ?_ ?_
          · intro a ha
            rw [mem_filter, mem_Ioc] at ha
            rw [mem_range]
            have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
              conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
            have hpow2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
              conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ']
            omega
          · intro a₁ ha₁ a₂ ha₂ heq
            rw [mem_filter, mem_Ioc] at ha₁ ha₂
            have hpow2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
              conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ']
            obtain ⟨m₁, hm₁⟩ := ha₁.2
            obtain ⟨m₂, hm₂⟩ := ha₂.2
            omega
          · intro j hj
            rw [mem_range] at hj
            have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
              conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
            have hpow2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
              conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ']
            refine ⟨2 ^ (k - 1) + 2 * j + 1, ?_, by omega⟩
            rw [mem_filter, mem_Ioc]
            refine ⟨⟨by omega, by omega⟩, ⟨2 ^ (k - 2) + j, by omega⟩⟩
        simpa using hbij
      have heven_c : #((Ioc (2 ^ (k - 1)) (2 ^ k)).filter Even) = 2 ^ (k - 2) := by
        have hbij : #((Ioc (2 ^ (k - 1)) (2 ^ k)).filter Even) = #(range (2 ^ (k - 2))) := by
          refine Finset.card_bij (fun b _ => (b - 2 ^ (k - 1)) / 2 - 1) ?_ ?_ ?_
          · intro b hb
            rw [mem_filter, mem_Ioc] at hb
            rw [mem_range]
            have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
              conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
            have hpow2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
              conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ']
            obtain ⟨m, hm⟩ := hb.2
            omega
          · intro b₁ hb₁ b₂ hb₂ heq
            rw [mem_filter, mem_Ioc] at hb₁ hb₂
            have hpow2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
              conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ']
            obtain ⟨m₁, hm₁⟩ := hb₁.2
            obtain ⟨m₂, hm₂⟩ := hb₂.2
            omega
          · intro j hj
            rw [mem_range] at hj
            have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
              conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
            have hpow2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
              conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ']
            refine ⟨2 ^ (k - 1) + 2 * (j + 1), ?_, by omega⟩
            rw [mem_filter, mem_Ioc]
            refine ⟨⟨by omega, by omega⟩, ⟨2 ^ (k - 2) + j + 1, by omega⟩⟩
        simpa using hbij
      rw [hodd_c, heven_c, ← pow_add]
      congr 1; omega
  have hBk_sum : ∀ k ∈ Icc 2 K,
        (1 : ℝ) / 32 ≤ ∑ ab ∈ B k, (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) := by
      intro k hk
      have hhk := mem_Icc.mp hk
      have hterm : ∀ ab ∈ B k,
          (1 : ℝ) / (2 * (2 : ℝ) ^ (2 * k)) ≤ (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) := by
        intro ab hab
        simp only [B, mem_product, mem_filter, mem_Ioc] at hab
        have hpos : (0 : ℝ) < ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) := by
          have : 1 ≤ ab.1 := by have := Nat.one_le_pow (k - 1) 2 (by decide); omega
          positivity
        refine one_div_le_one_div_of_le hpos ?_
        have h1 : ab.1 ^ 2 + ab.2 ^ 2 ≤ 2 * 2 ^ (2 * k) := by
          have ha : ab.1 ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hab.1.1.2 2
          have hb : ab.2 ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hab.2.1.2 2
          have h2k : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
          omega
        exact_mod_cast h1
      calc (1 : ℝ) / 32
          = ((2 ^ (2 * k - 4) : ℕ) : ℝ) * ((1 : ℝ) / (2 * (2 : ℝ) ^ (2 * k))) := by
            push_cast
            have hpow : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (2 * k - 4) * 16 := by
              rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add]
              congr 1; omega
            rw [hpow]
            have hne : (2 : ℝ) ^ (2 * k - 4) ≠ 0 := by positivity
            field_simp [hne]
            ring
        _ = ∑ _ab ∈ B k, (1 : ℝ) / (2 * (2 : ℝ) ^ (2 * k)) := by
            rw [sum_const, nsmul_eq_mul, hBk_card k hk]
        _ ≤ ∑ ab ∈ B k, (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) := sum_le_sum hterm
  calc (((K : ℝ) - 1) / 32)
      = ∑ _k ∈ Icc 2 K, ((1 : ℝ) / 32) := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
        have : K + 1 - 2 = K - 1 := by omega
        rw [this, Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
        ring
    _ ≤ ∑ k ∈ Icc 2 K, ∑ ab ∈ B k, (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) :=
        sum_le_sum hBk_sum
    _ = ∑ ab ∈ (Icc 2 K).biUnion B, (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) :=
        (sum_biUnion hdisj).symm
    _ ≤ ∑ ab ∈ Pairs, (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

private lemma sigma_upper_bound (X : ℕ) :
    ∑ ab ∈ (Icc 1 X ×ˢ Icc 1 X).filter
      (fun ab : ℕ × ℕ => Odd ab.1 ∧ Even ab.2 ∧ ab.1 ^ 2 + ab.2 ^ 2 ≤ X),
      (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) ≤
    6 * ∑ d ∈ (Finset.Icc (1 : ℕ) X).filter
      (fun d : ℕ => Squarefree d ∧ ∀ p ∈ d.primeFactors, p % 4 = 1),
      ∏ p ∈ d.primeFactors, ((2 : ℝ) / ((p : ℝ) - 2)) := by
  set Pairs := (Icc 1 X ×ˢ Icc 1 X).filter
    (fun ab : ℕ × ℕ => Odd ab.1 ∧ Even ab.2 ∧ ab.1 ^ 2 + ab.2 ^ 2 ≤ X)
  set Sigma : ℝ := ∑ ab ∈ Pairs, (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ)
  set D1 := (Finset.Icc 1 X).filter (fun d : ℕ => Squarefree d ∧ ∀ p ∈ d.primeFactors, p % 4 = 1)
  set T1 := (Finset.Icc 1 X).filter (fun t : ℕ => ∀ p ∈ t.primeFactors, p % 4 = 1)
  set M_odd := (Icc 1 X).filter (fun m : ℕ => Odd m ∧ ∀ p ∈ m.primeFactors, p % 4 = 1)
  have hgroup1 : Sigma ≤
      ∑ g ∈ Icc 1 X, ∑ m ∈ M_odd,
        ((2 : ℝ) ^ m.primeFactors.card) / (((g ^ 2 * m : ℕ) : ℝ)) := by
    let f : ℕ × ℕ → ℕ × ℕ := fun ab =>
      let g := Nat.gcd ab.1 ab.2
      (g, (ab.1 / g) ^ 2 + (ab.2 / g) ^ 2)
    have hmaps : ∀ ab ∈ Pairs, f ab ∈ Icc 1 X ×ˢ M_odd := by
      intro ab hab
      simp only [Pairs, mem_filter, mem_product, mem_Icc] at hab
      set g := Nat.gcd ab.1 ab.2
      have hg_pos : 1 ≤ g := Nat.pos_of_ne_zero (by
        intro h0; have := Nat.gcd_eq_zero_iff.mp h0; omega)
      have hg_le : g ≤ X := (Nat.gcd_le_left _ (by omega)).trans hab.1.1.2
      set a' := ab.1 / g
      set b' := ab.2 / g
      have ha_eq : g * a' = ab.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hb_eq : g * b' = ab.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hm_eq : g ^ 2 * (a' ^ 2 + b' ^ 2) = ab.1 ^ 2 + ab.2 ^ 2 := by
        calc g ^ 2 * (a' ^ 2 + b' ^ 2) = (g * a') ^ 2 + (g * b') ^ 2 := by ring
          _ = ab.1 ^ 2 + ab.2 ^ 2 := by rw [ha_eq, hb_eq]
      have hm_pos : 1 ≤ a' ^ 2 + b' ^ 2 := by
        have : 1 ≤ ab.1 ^ 2 + ab.2 ^ 2 := by nlinarith [hab.1.1.1]
        nlinarith
      have hm_le : a' ^ 2 + b' ^ 2 ≤ X := by
        have hg2 : 1 ≤ g ^ 2 := Nat.one_le_pow 2 g hg_pos
        have hleX : ab.1 ^ 2 + ab.2 ^ 2 ≤ X := hab.2.2.2
        nlinarith [hm_eq, hg2, hleX]
      have hodd_orig : Odd (ab.1 ^ 2 + ab.2 ^ 2) := by
        have h1 : Odd (ab.1 ^ 2) := hab.2.1.pow
        have h2 : Even (ab.2 ^ 2) := hab.2.2.1.pow_of_ne_zero (by decide)
        exact h1.add_even h2
      have hm_odd : Odd (a' ^ 2 + b' ^ 2) := by
        rw [← hm_eq] at hodd_orig
        exact (Nat.odd_mul.mp hodd_orig).2
      have hcop' : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hg_pos
      have hpf : ∀ p ∈ (a' ^ 2 + b' ^ 2).primeFactors, p % 4 = 1 := by
        intro p hp
        rw [Nat.mem_primeFactors] at hp
        exact prime_mod4_eq1_of_dvd_prim_sum_sq hp.1 hm_odd hcop' hp.2.1
      simp only [f, mem_product, mem_Icc, M_odd, mem_filter]
      exact ⟨⟨hg_pos, hg_le⟩, ⟨hm_pos, hm_le⟩, hm_odd, hpf⟩
    rw [← Finset.sum_product']
    have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
      (fun ab : ℕ × ℕ => (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ))
    dsimp only [Sigma]
    rw [← hfiber]
    refine sum_le_sum fun gm hgm => ?_
    simp only [mem_product, mem_Icc, M_odd, mem_filter] at hgm
    have hconst : ∀ ab ∈ Pairs.filter (fun ab => f ab = gm),
        (1 : ℝ) / ((ab.1 ^ 2 + ab.2 ^ 2 : ℕ) : ℝ) = 1 / ((gm.1 ^ 2 * gm.2 : ℕ) : ℝ) := by
      intro ab hab
      rw [mem_filter] at hab
      have h1 : Nat.gcd ab.1 ab.2 = gm.1 := congr_arg Prod.fst hab.2
      have h2 : (ab.1 / Nat.gcd ab.1 ab.2) ^ 2 + (ab.2 / Nat.gcd ab.1 ab.2) ^ 2 = gm.2 :=
        congr_arg Prod.snd hab.2
      have hsum_eq : ab.1 ^ 2 + ab.2 ^ 2 = gm.1 ^ 2 * gm.2 := by
        have ha := Nat.mul_div_cancel' (Nat.gcd_dvd_left ab.1 ab.2)
        have hb := Nat.mul_div_cancel' (Nat.gcd_dvd_right ab.1 ab.2)
        rw [← h1, ← h2]
        calc ab.1 ^ 2 + ab.2 ^ 2
            = (Nat.gcd ab.1 ab.2 * (ab.1 / Nat.gcd ab.1 ab.2)) ^ 2 +
              (Nat.gcd ab.1 ab.2 * (ab.2 / Nat.gcd ab.1 ab.2)) ^ 2 := by rw [ha, hb]
          _ = Nat.gcd ab.1 ab.2 ^ 2 *
              ((ab.1 / Nat.gcd ab.1 ab.2) ^ 2 + (ab.2 / Nat.gcd ab.1 ab.2) ^ 2) := by ring
      rw [hsum_eq]
    rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul, mul_one_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hcard_le : #(Pairs.filter (fun ab => f ab = gm)) ≤ 2 ^ gm.2.primeFactors.card := by
      calc #(Pairs.filter (fun ab => f ab = gm))
          ≤ #{ab' ∈ Icc 1 gm.2 ×ˢ Icc 1 gm.2 |
              ab'.1 ^ 2 + ab'.2 ^ 2 = gm.2 ∧ Nat.Coprime ab'.1 ab'.2} := by
            refine Finset.card_le_card_of_injOn (fun ab => (ab.1 / gm.1, ab.2 / gm.1)) ?_ ?_
            · intro ab hab
              simp only [mem_coe, mem_filter, Pairs, mem_product, mem_Icc] at hab
              have h1 : Nat.gcd ab.1 ab.2 = gm.1 := congr_arg Prod.fst hab.2
              have h2 : (ab.1 / gm.1) ^ 2 + (ab.2 / gm.1) ^ 2 = gm.2 := by
                simpa only [f, h1] using congr_arg Prod.snd hab.2
              have hcop : Nat.Coprime (ab.1 / gm.1) (ab.2 / gm.1) := by
                rw [← h1]; exact Nat.coprime_div_gcd_div_gcd (by omega)
              have ha_eq := Nat.mul_div_cancel' (h1 ▸ Nat.gcd_dvd_left ab.1 ab.2)
              have hb_eq := Nat.mul_div_cancel' (h1 ▸ Nat.gcd_dvd_right ab.1 ab.2)
              have ha_pos : 1 ≤ ab.1 / gm.1 := by nlinarith [hab.1.1.1.1]
              have hb_pos : 1 ≤ ab.2 / gm.1 := by nlinarith [hab.1.1.2.1]
              have ha_le : ab.1 / gm.1 ≤ gm.2 := by nlinarith
              have hb_le : ab.2 / gm.1 ≤ gm.2 := by nlinarith
              simp only [mem_coe, mem_filter, mem_product, mem_Icc]
              exact ⟨⟨⟨ha_pos, ha_le⟩, ⟨hb_pos, hb_le⟩⟩, h2, hcop⟩
            · intro ab1 hab1 ab2 hab2 heq
              simp only [mem_coe, mem_filter] at hab1 hab2
              have h1 : Nat.gcd ab1.1 ab1.2 = gm.1 := congr_arg Prod.fst hab1.2
              have h2 : Nat.gcd ab2.1 ab2.2 = gm.1 := congr_arg Prod.fst hab2.2
              have ha1 := Nat.mul_div_cancel' (h1 ▸ Nat.gcd_dvd_left ab1.1 ab1.2)
              have hb1 := Nat.mul_div_cancel' (h1 ▸ Nat.gcd_dvd_right ab1.1 ab1.2)
              have ha2 := Nat.mul_div_cancel' (h2 ▸ Nat.gcd_dvd_left ab2.1 ab2.2)
              have hb2 := Nat.mul_div_cancel' (h2 ▸ Nat.gcd_dvd_right ab2.1 ab2.2)
              have hfst : ab1.1 / gm.1 = ab2.1 / gm.1 := congr_arg Prod.fst heq
              have hsnd : ab1.2 / gm.1 = ab2.2 / gm.1 := congr_arg Prod.snd heq
              exact Prod.ext (by rw [← ha1, ← ha2, hfst]) (by rw [← hb1, ← hb2, hsnd])
        _ ≤ 2 ^ gm.2.primeFactors.card := card_prim_sum_two_sq gm.2 hgm.2.2.1
    exact_mod_cast hcard_le
  have hgroup2 : ∑ m ∈ M_odd, ((2 : ℝ) ^ m.primeFactors.card) / (m : ℝ) ≤
      (∑ t ∈ T1, Real.sqrt (t : ℝ) / ((t : ℝ) ^ 2)) *
      (∑ d ∈ D1, ((2 : ℝ) ^ d.primeFactors.card) / (d : ℝ)) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    let decomp : ℕ → ℕ × ℕ := fun m =>
      (∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2),
       ∏ p ∈ m.primeFactors, p ^ (m.factorization p % 2))
    have hdecomp_eq : ∀ m ∈ M_odd, (decomp m).1 ^ 2 * (decomp m).2 = m := by
      intro m hm
      simp only [M_odd, mem_filter, mem_Icc] at hm
      have hm0 : m ≠ 0 := by omega
      simp only [decomp]
      rw [← prod_pow, ← prod_mul_distrib]
      have hfac := Nat.prod_factorization_pow_eq_self hm0
      rw [Finsupp.prod, Nat.support_factorization] at hfac
      conv_rhs => rw [← hfac]
      refine prod_congr rfl fun p _ => ?_
      rw [← pow_mul, ← pow_add]
      congr 1; omega
    have hdecomp_mem : ∀ m ∈ M_odd, decomp m ∈ T1 ×ˢ D1 := by
      intro m hm
      have heq := hdecomp_eq m hm
      simp only [M_odd, mem_filter, mem_Icc] at hm
      have hm0 : m ≠ 0 := by omega
      have ht_pos : 1 ≤ (decomp m).1 := Nat.one_le_iff_ne_zero.mpr <|
        prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
      have hd_pos : 1 ≤ (decomp m).2 := Nat.one_le_iff_ne_zero.mpr <|
        prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
      have ht2_pos : 1 ≤ (decomp m).1 ^ 2 := Nat.one_le_pow 2 _ ht_pos
      have ht_le : (decomp m).1 ≤ X := by nlinarith [heq, hm.1.2, hd_pos]
      have hd_le : (decomp m).2 ≤ X := by nlinarith [heq, hm.1.2, ht2_pos]
      have ht_pf : ∀ p ∈ (decomp m).1.primeFactors, p % 4 = 1 := by
        intro p hp
        rw [Nat.mem_primeFactors] at hp
        have hpm : p ∣ m := by
          rw [← heq]
          exact dvd_mul_of_dvd_left (dvd_pow hp.2.1 (by decide : 2 ≠ 0)) _
        exact hm.2.2 p (Nat.mem_primeFactors.mpr ⟨hp.1, hpm, hm0⟩)
      have hd_pf : ∀ p ∈ (decomp m).2.primeFactors, p % 4 = 1 := by
        intro p hp
        rw [Nat.mem_primeFactors] at hp
        have hpm : p ∣ m := by rw [← heq]; exact dvd_mul_of_dvd_right hp.2.1 _
        exact hm.2.2 p (Nat.mem_primeFactors.mpr ⟨hp.1, hpm, hm0⟩)
      have hd_sqf : Squarefree (decomp m).2 := by
        rw [Nat.squarefree_iff_prime_squarefree]
        intro q hq hq2
        have hqm : q ∈ m.primeFactors := by
          rw [Nat.mem_primeFactors]
          refine ⟨hq, ?_, hm0⟩
          rw [← heq]
          exact dvd_mul_of_dvd_right (dvd_of_mul_left_dvd hq2) _
        have hq_not_dvd : ¬ q ∣ ∏ p ∈ m.primeFactors.erase q, p ^ (m.factorization p % 2) := by
          intro hdiv
          rw [hq.prime.dvd_finsetProd_iff] at hdiv
          obtain ⟨p, hp, hqp⟩ := hdiv
          have hp' := Nat.prime_of_mem_primeFactors (mem_of_mem_erase hp)
          exact (mem_erase.mp hp).1 ((Nat.prime_dvd_prime_iff_eq hq hp').mp (hq.dvd_of_dvd_pow hqp)).symm
        have hsplit : (decomp m).2 = q ^ (m.factorization q % 2) *
            ∏ p ∈ m.primeFactors.erase q, p ^ (m.factorization p % 2) :=
          (Finset.mul_prod_erase _ _ hqm).symm
        rw [hsplit] at hq2
        have hcop : Nat.Coprime (q ^ 2)
            (∏ p ∈ m.primeFactors.erase q, p ^ (m.factorization p % 2)) :=
          (hq.coprime_iff_not_dvd.mpr hq_not_dvd).pow_left 2
        have hq2' : q ^ 2 ∣ q ^ (m.factorization q % 2) := by
          have hq2_pow : q ^ 2 ∣ q ^ (m.factorization q % 2) *
              ∏ p ∈ m.primeFactors.erase q, p ^ (m.factorization p % 2) := by
            simpa [sq] using hq2
          exact hcop.dvd_of_dvd_mul_right hq2_pow
        have := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hq2'
        omega
      simp only [mem_product, T1, D1, mem_filter, mem_Icc]
      exact ⟨⟨⟨ht_pos, ht_le⟩, ht_pf⟩, ⟨⟨hd_pos, hd_le⟩, hd_sqf, hd_pf⟩⟩
    have hdecomp_inj : ∀ m1 ∈ M_odd, ∀ m2 ∈ M_odd, decomp m1 = decomp m2 → m1 = m2 := by
      intro m1 hm1 m2 hm2 heq
      have h1 := hdecomp_eq m1 hm1
      have h2 := hdecomp_eq m2 hm2
      rw [heq] at h1
      exact h1.symm.trans h2
    have hterm_le : ∀ m ∈ M_odd,
        ((2 : ℝ) ^ m.primeFactors.card) / (m : ℝ) ≤
        (Real.sqrt ((decomp m).1 : ℝ) / (((decomp m).1 : ℝ) ^ 2)) *
        (((2 : ℝ) ^ (decomp m).2.primeFactors.card) / ((decomp m).2 : ℝ)) := by
      intro m hm
      have heq := hdecomp_eq m hm
      have hmem := hdecomp_mem m hm
      simp only [mem_product, T1, D1, mem_filter, mem_Icc] at hmem
      have hcard_le : m.primeFactors.card ≤
          (decomp m).1.primeFactors.card + (decomp m).2.primeFactors.card := by
        have hsub : m.primeFactors ⊆ (decomp m).1.primeFactors ∪ (decomp m).2.primeFactors := by
          intro p hp
          rw [← heq] at hp
          rw [Nat.primeFactors_mul (pow_ne_zero 2 (by omega)) (by omega),
            Nat.primeFactors_pow _ (by decide)] at hp
          exact hp
        exact (card_le_card hsub).trans (card_union_le _ _)
      have h2pow : (2 : ℝ) ^ m.primeFactors.card ≤
          Real.sqrt ((decomp m).1 : ℝ) * (2 : ℝ) ^ (decomp m).2.primeFactors.card := by
        calc (2 : ℝ) ^ m.primeFactors.card
            ≤ (2 : ℝ) ^ ((decomp m).1.primeFactors.card + (decomp m).2.primeFactors.card) :=
              pow_le_pow_right₀ (by norm_num) hcard_le
          _ = (2 : ℝ) ^ (decomp m).1.primeFactors.card *
              (2 : ℝ) ^ (decomp m).2.primeFactors.card := pow_add _ _ _
          _ ≤ Real.sqrt ((decomp m).1 : ℝ) * (2 : ℝ) ^ (decomp m).2.primeFactors.card := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact two_pow_card_primeFactors_le_sqrt hmem.1.2 (by omega)
      have hm_cast : (m : ℝ) = ((decomp m).1 : ℝ) ^ 2 * ((decomp m).2 : ℝ) := by
        exact_mod_cast heq.symm
      rw [hm_cast, div_mul_div_comm]
      exact div_le_div_of_nonneg_right h2pow (by positivity)
    calc ∑ m ∈ M_odd, ((2 : ℝ) ^ m.primeFactors.card) / (m : ℝ)
        ≤ ∑ m ∈ M_odd, (Real.sqrt ((decomp m).1 : ℝ) / (((decomp m).1 : ℝ) ^ 2)) *
            (((2 : ℝ) ^ (decomp m).2.primeFactors.card) / ((decomp m).2 : ℝ)) :=
          sum_le_sum hterm_le
      _ = ∑ td ∈ M_odd.image decomp,
            (Real.sqrt (td.1 : ℝ) / ((td.1 : ℝ) ^ 2)) *
            (((2 : ℝ) ^ td.2.primeFactors.card) / (td.2 : ℝ)) := by
          symm
          exact Finset.sum_image (f := fun td : ℕ × ℕ =>
            (Real.sqrt (td.1 : ℝ) / ((td.1 : ℝ) ^ 2)) *
            (((2 : ℝ) ^ td.2.primeFactors.card) / (td.2 : ℝ)))
            (fun m1 hm1 m2 hm2 h => hdecomp_inj m1 hm1 m2 hm2 h)
      _ ≤ ∑ td ∈ T1 ×ˢ D1,
            (Real.sqrt (td.1 : ℝ) / ((td.1 : ℝ) ^ 2)) *
            (((2 : ℝ) ^ td.2.primeFactors.card) / (td.2 : ℝ)) := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro td htd
          rw [mem_image] at htd
          obtain ⟨m, hm, rfl⟩ := htd
          exact hdecomp_mem m hm
  have hd_term : ∀ d ∈ D1,
      ((2 : ℝ) ^ d.primeFactors.card) / (d : ℝ) ≤
      ∏ p ∈ d.primeFactors, ((2 : ℝ) / ((p : ℝ) - 2)) := by
    intro d hd
    simp only [D1, mem_filter, mem_Icc] at hd
    have hprod_d : (∏ p ∈ d.primeFactors, p) = d :=
      Nat.prod_primeFactors_of_squarefree hd.2.1
    have hd_cast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      conv_lhs => rw [← hprod_d]
      push_cast; rfl
    rw [hd_cast, show (2 : ℝ) ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, (2 : ℝ) by simp,
      ← prod_div_distrib]
    refine prod_le_prod (fun p hp => by positivity) fun p hp => ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    have h4 := hd.2.2 p hp
    have hp5 : (5 : ℝ) ≤ p := by
      have := hp'.two_le; exact_mod_cast (show 5 ≤ p by omega)
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  calc Sigma
      ≤ ∑ g ∈ Icc 1 X, ∑ m ∈ M_odd,
          ((2 : ℝ) ^ m.primeFactors.card) / (((g ^ 2 * m : ℕ) : ℝ)) := hgroup1
    _ = (∑ g ∈ Icc 1 X, (1 : ℝ) / ((g : ℝ) ^ 2)) *
        (∑ m ∈ M_odd, ((2 : ℝ) ^ m.primeFactors.card) / (m : ℝ)) := by
        rw [Finset.sum_mul]
        refine sum_congr rfl fun g _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun m _ => ?_
        push_cast; ring
    _ ≤ 2 * ((∑ t ∈ T1, Real.sqrt (t : ℝ) / ((t : ℝ) ^ 2)) *
        (∑ d ∈ D1, ((2 : ℝ) ^ d.primeFactors.card) / (d : ℝ))) := by
        refine mul_le_mul (sum_inv_sq_le_two X) hgroup2
          (sum_nonneg fun _ _ => by positivity) (by norm_num)
    _ ≤ 2 * (3 * (∑ d ∈ D1, ∏ p ∈ d.primeFactors, ((2 : ℝ) / ((p : ℝ) - 2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine mul_le_mul ?_ (sum_le_sum hd_term) (sum_nonneg fun _ _ => by positivity) (by norm_num)
        calc ∑ t ∈ T1, Real.sqrt (t : ℝ) / ((t : ℝ) ^ 2)
            ≤ ∑ t ∈ Icc 1 X, Real.sqrt (t : ℝ) / ((t : ℝ) ^ 2) :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
          _ ≤ 3 := sum_sqrt_div_sq_le_three X
    _ = 6 * ∑ d ∈ D1, ∏ p ∈ d.primeFactors, ((2 : ℝ) / ((p : ℝ) - 2)) := by ring

private lemma sum_h_mod4_eq1_lower (K : ℕ) (hK : 2 ≤ K) :
    (((K : ℝ) - 1) / 192) ≤
      ∑ d ∈ (Finset.Icc (1 : ℕ) (2 * 4 ^ K)).filter
        (fun d : ℕ => Squarefree d ∧ ∀ p ∈ d.primeFactors, p % 4 = 1),
        ∏ p ∈ d.primeFactors, ((2 : ℝ) / ((p : ℝ) - 2)) := by
  have hlo := sigma_lower_bound K hK
  have hhi := sigma_upper_bound (2 * 4 ^ K)
  linarith

/- ### Section 4: Selberg's Lambda^2 sieve upper bound on `OeisA69004.a n` -/

private lemma prod_one_add_primeFactors_eq_sum_divisors {d : ℕ} (hd : Squarefree d) (f : ℕ → ℝ) :
    ∏ p ∈ d.primeFactors, (1 + f p) = ∑ t ∈ d.divisors, ∏ p ∈ t.primeFactors, f p := by
  have hd0 : d ≠ 0 := hd.ne_zero
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd1 : d = 1
    · subst hd1; simp
    · set p := d.minFac
      have hp : p.Prime := Nat.minFac_prime hd1
      have hpdvd : p ∣ d := Nat.minFac_dvd d
      set d' := d / p
      have hmul : p * d' = d := Nat.mul_div_cancel' hpdvd
      have hd'_pos : 0 < d' := by
        rcases Nat.eq_zero_or_pos d' with h0 | hpos
        · rw [h0, mul_zero] at hmul; exact absurd hmul.symm hd0
        · exact hpos
      have hd'_lt : d' < d := by
        calc d' = 1 * d' := (one_mul _).symm
          _ < p * d' := Nat.mul_lt_mul_of_pos_right hp.one_lt hd'_pos
          _ = d := hmul
      have hd'_sqf : Squarefree d' := hd.squarefree_of_dvd ⟨p, by linarith⟩
      have hndvd : ¬ p ∣ d' := by
        intro hpd'
        have hp2 : p * p ∣ d := by rw [← hmul]; exact mul_dvd_mul_left p hpd'
        exact hp.not_isUnit (hd p hp2)
      have hp_not_mem : p ∉ d'.primeFactors := by
        rw [Nat.mem_primeFactors]; rintro ⟨_, h, _⟩; exact hndvd h
      have hpf : d.primeFactors = insert p d'.primeFactors := by
        rw [← hmul, Nat.primeFactors_mul hp.ne_zero hd'_pos.ne', hp.primeFactors]
        simp
      have hdiv : d.divisors = d'.divisors ∪ d'.divisors.image (p * ·) := by
        ext x
        simp only [mem_union, mem_image, Nat.mem_divisors]
        constructor
        · rintro ⟨hxd, _⟩
          by_cases hpx : p ∣ x
          · right
            obtain ⟨y, rfl⟩ := hpx
            refine ⟨y, ⟨?_, hd'_pos.ne'⟩, rfl⟩
            rw [← hmul] at hxd
            exact (mul_dvd_mul_iff_left hp.ne_zero).mp hxd
          · left
            rw [← hmul] at hxd
            exact ⟨(hp.coprime_iff_not_dvd.mpr hpx).symm.dvd_of_dvd_mul_left hxd, hd'_pos.ne'⟩
        · rintro (⟨hxd', _⟩ | ⟨y, ⟨hyd', _⟩, rfl⟩)
          · exact ⟨hxd'.trans ⟨p, by linarith⟩, hd0⟩
          · exact ⟨by rw [← hmul]; exact mul_dvd_mul_left p hyd', hd0⟩
      have hdisj : Disjoint d'.divisors (d'.divisors.image (p * ·)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [mem_image] at hx2
        obtain ⟨y, _, rfl⟩ := hx2
        exact hndvd ((dvd_mul_right p y).trans (Nat.dvd_of_mem_divisors hx1))
      rw [hpf, prod_insert hp_not_mem, ih d' hd'_lt hd'_sqf hd'_pos.ne',
        hdiv, sum_union hdisj, add_mul, one_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
      refine sum_congr rfl fun t ht => ?_
      have ht0 : t ≠ 0 := (Nat.mem_divisors.mp ht).1 |> fun h =>
        ne_of_gt (Nat.pos_of_dvd_of_pos h hd'_pos)
      have hp_not_t : p ∉ t.primeFactors := by
        rw [Nat.mem_primeFactors]
        rintro ⟨_, hpt, _⟩
        exact hndvd (hpt.trans (Nat.dvd_of_mem_divisors ht))
      rw [Nat.primeFactors_mul hp.ne_zero ht0, hp.primeFactors]
      simp [prod_insert hp_not_t]

private lemma solCount_mul_of_coprime (n a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)]
    (hcop : Nat.Coprime a b) :
    #{x : ZMod (a * b) | x ^ 2 + (n : ZMod (a * b)) ^ 2 = 0} =
      #{x : ZMod a | x ^ 2 + (n : ZMod a) ^ 2 = 0} *
      #{x : ZMod b | x ^ 2 + (n : ZMod b) ^ 2 = 0} := by
  let e := ZMod.chineseRemainder hcop
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => e x) (fun x hx => ?_) (fun x₁ _ x₂ _ h => e.injective h)
    (fun p hp => ?_)
  · rw [mem_filter] at hx
    rw [mem_product, mem_filter, mem_filter]
    have hmap : e x ^ 2 + (n : ZMod a × ZMod b) ^ 2 = 0 := by
      have : e (x ^ 2 + (n : ZMod (a * b)) ^ 2) = 0 := by rw [hx.2, map_zero]
      simpa [map_add, map_pow, map_natCast] using this
    exact ⟨⟨mem_univ _, congr_arg Prod.fst hmap⟩, ⟨mem_univ _, congr_arg Prod.snd hmap⟩⟩
  · rw [mem_product, mem_filter, mem_filter] at hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    rw [mem_filter]
    refine ⟨mem_univ _, e.injective ?_⟩
    rw [map_add, map_pow, map_pow, map_natCast, map_zero, e.apply_symm_apply]
    exact Prod.ext hp.1.2 hp.2.2

private lemma solCount_prime_of_dvd {n p : ℕ} [NeZero p] (hp : p.Prime) (hdvd : p ∣ n) :
    #{x : ZMod p | x ^ 2 + (n : ZMod p) ^ 2 = 0} = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hdvd
  have hset : ({x : ZMod p | x ^ 2 + (n : ZMod p) ^ 2 = 0} : Finset (ZMod p)) = {0} := by
    ext x
    simp [hn0]
  rw [hset, card_singleton]

private lemma solCount_prime_of_mod4_eq1 {n p : ℕ} [NeZero p] (hp : p.Prime)
    (h4 : p % 4 = 1) (hnd : ¬ p ∣ n) :
    #{x : ZMod p | x ^ 2 + (n : ZMod p) ^ 2 = 0} = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  obtain ⟨u, hu⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have := Nat.le_of_dvd (by decide) hd
    have := hp.two_le
    omega
  have hne : u * (n : ZMod p) ≠ -(u * (n : ZMod p)) := by
    intro h
    have : (2 : ZMod p) * (u * (n : ZMod p)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h2 | hun
    · exact h2ne0 h2
    · rcases mul_eq_zero.mp hun with hu' | hn'
      · exact hu0 hu'
      · exact hn0 hn'
  have hset : ({x : ZMod p | x ^ 2 + (n : ZMod p) ^ 2 = 0} : Finset (ZMod p)) =
      {u * (n : ZMod p), -(u * (n : ZMod p))} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    have hfac : x ^ 2 + (n : ZMod p) ^ 2 = (x - u * (n : ZMod p)) * (x + u * (n : ZMod p)) := by
      linear_combination -(n : ZMod p) ^ 2 * hu
    rw [hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  rw [hset, card_pair hne]

private lemma solCount_zmod_congr (n : ℕ) {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    #{x : ZMod a | x ^ 2 + (n : ZMod a) ^ 2 = 0} =
      #{x : ZMod b | x ^ 2 + (n : ZMod b) ^ 2 = 0} := by
  subst h; rfl

private lemma solCount_squarefree_eq {P3 : Finset ℕ} (_hP3 : ∀ p ∈ P3, p.Prime ∧ p % 4 = 3)
    {n : ℕ} (hn_dvd : ∀ p ∈ P3, p ∣ n) (hn_ndvd : ∀ p : ℕ, p.Prime → p % 4 = 1 → ¬ p ∣ n) :
    ∀ D : ℕ, [NeZero D] → Squarefree D → (∀ p ∈ D.primeFactors, p ∈ P3 ∨ p % 4 = 1) →
      #{x : ZMod D | x ^ 2 + (n : ZMod D) ^ 2 = 0} =
        ∏ p ∈ D.primeFactors, (if p ∈ P3 then 1 else 2) := by
  intro D
  induction D using Nat.strong_induction_on with
  | h D ih =>
    intro hne hD_sqf hD_pf
    have hD0 : D ≠ 0 := hD_sqf.ne_zero
    by_cases hD1 : D = 1
    · subst hD1
      have : Fintype.card (ZMod 1) = 1 := ZMod.card 1
      have hset : ({x : ZMod 1 | x ^ 2 + (n : ZMod 1) ^ 2 = 0} : Finset (ZMod 1)) = univ := by
        ext x
        simp only [mem_filter, mem_univ, true_and, iff_true]
        exact Subsingleton.elim _ _
      rw [hset, card_univ, this]; simp
    · set p := D.minFac
      have hp : p.Prime := Nat.minFac_prime hD1
      have hpdvd : p ∣ D := Nat.minFac_dvd D
      set D' := D / p
      have hmul : p * D' = D := Nat.mul_div_cancel' hpdvd
      have hD'_pos : 0 < D' := by
        rcases Nat.eq_zero_or_pos D' with h0 | hpos
        · rw [h0, mul_zero] at hmul; exact absurd hmul.symm hD0
        · exact hpos
      have hD'_lt : D' < D := by
        calc D' = 1 * D' := (one_mul _).symm
          _ < p * D' := Nat.mul_lt_mul_of_pos_right hp.one_lt hD'_pos
          _ = D := hmul
      have hD'_sqf : Squarefree D' := hD_sqf.squarefree_of_dvd ⟨p, by linarith⟩
      have hndvd : ¬ p ∣ D' := by
        intro hpd'
        exact hp.not_isUnit (hD_sqf p (by rw [← hmul]; exact mul_dvd_mul_left p hpd'))
      have hcop : Nat.Coprime p D' := hp.coprime_iff_not_dvd.mpr hndvd
      have hp_not_mem : p ∉ D'.primeFactors := by
        rw [Nat.mem_primeFactors]; rintro ⟨_, h, _⟩; exact hndvd h
      have hpf_eq : D.primeFactors = insert p D'.primeFactors := by
        rw [← hmul, Nat.primeFactors_mul hp.ne_zero hD'_pos.ne', hp.primeFactors]; simp
      have hD'_pf : ∀ q ∈ D'.primeFactors, q ∈ P3 ∨ q % 4 = 1 := fun q hq =>
        hD_pf q (by rw [hpf_eq]; exact mem_insert_of_mem hq)
      have hp_cases := hD_pf p (by rw [hpf_eq]; exact mem_insert_self p _)
      have : NeZero p := ⟨hp.ne_zero⟩
      have : NeZero D' := ⟨hD'_pos.ne'⟩
      have : NeZero (p * D') := ⟨mul_ne_zero hp.ne_zero hD'_pos.ne'⟩
      have hp_count : #{x : ZMod p | x ^ 2 + (n : ZMod p) ^ 2 = 0} =
          if p ∈ P3 then 1 else 2 := by
        by_cases hpP3 : p ∈ P3
        · simp only [hpP3, ↓reduceIte]
          exact solCount_prime_of_dvd hp (hn_dvd p hpP3)
        · simp only [hpP3, ↓reduceIte]
          have h4 : p % 4 = 1 := hp_cases.resolve_left hpP3
          exact solCount_prime_of_mod4_eq1 hp h4 (hn_ndvd p hp h4)
      rw [solCount_zmod_congr n hmul.symm, solCount_mul_of_coprime n p D' hcop,
        hp_count, ih D' hD'_lt hD'_sqf hD'_pf, hpf_eq, prod_insert hp_not_mem]

private lemma card_Ico_block_dvd (n D a : ℕ) [NeZero D] (_hD : 1 ≤ D) :
    #{s ∈ Ico a (a + D) | D ∣ n ^ 2 + s ^ 2} =
      #{x : ZMod D | x ^ 2 + (n : ZMod D) ^ 2 = 0} := by
  refine Finset.card_bij (fun s _ => (s : ZMod D)) ?_ ?_ ?_
  · intro s hs
    rw [mem_filter] at hs
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h0 := (ZMod.natCast_eq_zero_iff (n ^ 2 + s ^ 2) D).mpr hs.2
    push_cast at h0
    linear_combination h0
  · intro s₁ hs₁ s₂ hs₂ heq
    rw [mem_filter, mem_Ico] at hs₁ hs₂
    have hmod : s₁ ≡ s₂ [MOD D] := (ZMod.natCast_eq_natCast_iff s₁ s₂ D).mp heq
    rcases le_total s₁ s₂ with hle | hle
    · have hdvd : D ∣ s₂ - s₁ := (Nat.modEq_iff_dvd' hle).mp hmod
      have hlt : s₂ - s₁ < D := by omega
      have h0 : s₂ - s₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      omega
    · have hdvd : D ∣ s₁ - s₂ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      have hlt : s₁ - s₂ < D := by omega
      have h0 : s₁ - s₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      omega
  · intro x hx
    rw [mem_filter] at hx
    set r := (x - (a : ZMod D)).val
    have hr : r < D := ZMod.val_lt _
    have hcast : (a : ZMod D) + (r : ZMod D) = x := by
      simp [r]
    refine ⟨a + r, ?_, by push_cast; exact hcast⟩
    rw [mem_filter, mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hcast]
    linear_combination hx.2

private lemma card_Ico_partial_dvd_le (n D a b : ℕ) [NeZero D] (hD : 1 ≤ D) (hle : b ≤ a + D) :
    #{s ∈ Ico a b | D ∣ n ^ 2 + s ^ 2} ≤
      #{x : ZMod D | x ^ 2 + (n : ZMod D) ^ 2 = 0} := by
  rw [← card_Ico_block_dvd n D a hD]
  exact card_le_card (filter_subset_filter _ (Ico_subset_Ico_right hle))

private lemma abs_card_Ico_dvd_sub_le (n D : ℕ) [NeZero D] (hn : 1 ≤ n) (hD : 1 ≤ D) :
    |(#{s ∈ Ico 1 n | D ∣ n ^ 2 + s ^ 2} : ℝ) -
      (n : ℝ) * (#{x : ZMod D | x ^ 2 + (n : ZMod D) ^ 2 = 0} : ℝ) / (D : ℝ)| ≤
      (#{x : ZMod D | x ^ 2 + (n : ZMod D) ^ 2 = 0} : ℝ) := by
  set q := (n - 1) / D
  set S := #{x : ZMod D | x ^ 2 + (n : ZMod D) ^ 2 = 0}
  have hqD_le : q * D ≤ n - 1 := Nat.div_mul_le_self (n - 1) D
  have hqD_gt : n - 1 < q * D + D := by
    have := Nat.lt_div_mul_add (a := n - 1) (b := D) (by omega)
    omega
  have hpart : Ico 1 n = (Ico 1 (1 + q * D)) ∪ (Ico (1 + q * D) n) :=
    (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  have hdisj : Disjoint (Ico 1 (1 + q * D)) (Ico (1 + q * D) n) :=
    Finset.Ico_disjoint_Ico_consecutive 1 (1 + q * D) n
  have hfull : #{s ∈ Ico 1 (1 + q * D) | D ∣ n ^ 2 + s ^ 2} = q * S := by
    clear hqD_le hqD_gt hpart hdisj
    induction q with
    | zero => simp
    | succ k ih =>
      have hsp : Ico 1 (1 + (k + 1) * D) =
          Ico 1 (1 + k * D) ∪ Ico (1 + k * D) (1 + k * D + D) := by
        have h1 : 1 + (k + 1) * D = 1 + k * D + D := by ring
        rw [h1]
        exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
      rw [hsp, filter_union, card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 1 (1 + k * D) _))]
      rw [ih, card_Ico_block_dvd n D (1 + k * D) hD]
      ring
  have hrem_le : #{s ∈ Ico (1 + q * D) n | D ∣ n ^ 2 + s ^ 2} ≤ S :=
    card_Ico_partial_dvd_le n D (1 + q * D) n hD (by omega)
  have htot : #{s ∈ Ico 1 n | D ∣ n ^ 2 + s ^ 2} =
      q * S + #{s ∈ Ico (1 + q * D) n | D ∣ n ^ 2 + s ^ 2} := by
    rw [hpart, filter_union, card_union_of_disjoint (Finset.disjoint_filter_filter hdisj), hfull]
  have hlo : (q : ℝ) * (S : ℝ) ≤ (#{s ∈ Ico 1 n | D ∣ n ^ 2 + s ^ 2} : ℝ) := by
    rw [htot]; push_cast
    linarith [Nat.cast_nonneg (α := ℝ) #{s ∈ Ico (1 + q * D) n | D ∣ n ^ 2 + s ^ 2}]
  have hhi : (#{s ∈ Ico 1 n | D ∣ n ^ 2 + s ^ 2} : ℝ) ≤ ((q : ℝ) + 1) * (S : ℝ) := by
    rw [htot]; push_cast
    linarith [show (#{s ∈ Ico (1 + q * D) n | D ∣ n ^ 2 + s ^ 2} : ℝ) ≤ S by exact_mod_cast hrem_le]
  have hq_le_div : (q : ℝ) ≤ (n : ℝ) / (D : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have : q * D ≤ n := by omega
    exact_mod_cast this
  have hdiv_le_q1 : (n : ℝ) / (D : ℝ) ≤ (q : ℝ) + 1 := by
    rw [div_le_iff₀ (by positivity)]
    have : n ≤ (q + 1) * D := by rw [add_mul, one_mul]; omega
    exact_mod_cast this
  have hS_nn : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  rw [abs_le]
  constructor
  · have : ((n : ℝ) / (D : ℝ) - 1) * (S : ℝ) ≤ (q : ℝ) * (S : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hS_nn
    linarith [show (n : ℝ) * (S : ℝ) / (D : ℝ) = (n : ℝ) / (D : ℝ) * (S : ℝ) by ring]
  · have : ((q : ℝ) + 1) * (S : ℝ) ≤ ((n : ℝ) / (D : ℝ) + 1) * (S : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hS_nn
    linarith [show (n : ℝ) * (S : ℝ) / (D : ℝ) = (n : ℝ) / (D : ℝ) * (S : ℝ) by ring]

private lemma selberg_sieve_upper (P3 : Finset ℕ) (hP3 : ∀ p ∈ P3, p.Prime ∧ p % 4 = 3)
    (r Q : ℕ) (_hr : 1 ≤ r) (hQ : 1 ≤ Q) (hQn : Q ≤ 2 ^ r * ∏ p ∈ P3, p) :
    let n := 2 ^ r * ∏ p ∈ P3, p
    let Dset := (Finset.Icc 1 Q).filter
      (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, p ∈ P3 ∨ p % 4 = 1)
    let h : ℕ → ℝ := fun d => ∏ p ∈ d.primeFactors,
      ((if p ∈ P3 then (1 : ℝ) else 2) / ((p : ℝ) - (if p ∈ P3 then 1 else 2)))
    (OeisA69004.a n : ℝ) ≤ (n : ℝ) / (∑ d ∈ Dset, h d) + (Q : ℝ) ^ 4 := by
  intro n Dset h
  have hM_pos : 1 ≤ ∏ p ∈ P3, p := Nat.one_le_iff_ne_zero.mpr <|
    prod_ne_zero_iff.mpr fun p hp => (hP3 p hp).1.ne_zero
  have hn_pos : 1 ≤ n := Nat.mul_pos (Nat.pow_pos (by decide)) hM_pos
  have hn_dvd : ∀ p ∈ P3, p ∣ n := fun p hp =>
    dvd_mul_of_dvd_right (dvd_prod_of_mem _ hp) _
  have hn_ndvd : ∀ p : ℕ, p.Prime → p % 4 = 1 → ¬ p ∣ n := by
    intro p hp h4 hdvd
    rcases hp.dvd_mul.mp hdvd with h2 | hprod
    · have := hp.dvd_of_dvd_pow h2
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
      omega
    · rw [hp.prime.dvd_finsetProd_iff] at hprod
      obtain ⟨q, hq, hpq⟩ := hprod
      have := (Nat.prime_dvd_prime_iff_eq hp (hP3 q hq).1).mp hpq
      have := (hP3 q hq).2
      omega
  let ν : ℕ → ℝ := fun d => ∏ p ∈ d.primeFactors, (if p ∈ P3 then (1 : ℝ) else 2)
  let g : ℕ → ℝ := fun d => ν d / (d : ℝ)
  have h1_mem : 1 ∈ Dset := by
    simp [Dset, hQ]
  have h_pos : ∀ d ∈ Dset, 0 < h d := by
    intro d hd
    simp only [Dset, mem_filter, mem_Icc] at hd
    refine prod_pos fun p hp => ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    rcases hd.2.2 p hp with h3 | h4
    · simp only [h3, ↓reduceIte]
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
      exact div_pos zero_lt_one (by linarith)
    · have hnot : p ∉ P3 := fun h => by have := (hP3 p h).2; omega
      simp only [hnot, ↓reduceIte]
      have : (5 : ℝ) ≤ p := by have := hp'.two_le; exact_mod_cast (show 5 ≤ p by omega)
      exact div_pos (by norm_num) (by linarith)
  have g_pos : ∀ d ∈ Dset, 0 < g d := by
    intro d hd
    simp only [Dset, mem_filter, mem_Icc] at hd
    have hν : 0 < ν d := prod_pos fun p _ => by split_ifs <;> norm_num
    have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact div_pos hν hd_pos
  set L : ℝ := ∑ m ∈ Dset, h m
  have hL_pos : 0 < L := by
    have : h 1 ≤ L := single_le_sum (fun m hm => (h_pos m hm).le) h1_mem
    have h1 : h 1 = 1 := by simp [h]
    linarith
  have hg_prod : ∀ d : ℕ, Squarefree d → g d = ∏ p ∈ d.primeFactors,
      ((if p ∈ P3 then (1 : ℝ) else 2) / (p : ℝ)) := by
    intro d hd
    have hpd : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hd
    have hd_cast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      conv_lhs => rw [← hpd]
      push_cast; rfl
    simp only [g, ν]
    rw [hd_cast, prod_div_distrib]
  have hg_inv_eq : ∀ d ∈ Dset, (g d)⁻¹ = ∑ m ∈ d.divisors, (h m)⁻¹ := by
    intro d hd
    simp only [Dset, mem_filter, mem_Icc] at hd
    rw [hg_prod d hd.2.1, ← prod_inv_distrib]
    have hstep : ∀ p ∈ d.primeFactors,
        ((if p ∈ P3 then (1 : ℝ) else 2) / (p : ℝ))⁻¹ =
        1 + ((if p ∈ P3 then (1 : ℝ) else 2) / ((p : ℝ) - (if p ∈ P3 then 1 else 2)))⁻¹ := by
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      rcases hd.2.2 p hp with h3 | h4
      · simp only [h3, ↓reduceIte]
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hne]; ring
      · have hnot : p ∉ P3 := fun h => by have := (hP3 p h).2; omega
        simp only [hnot, ↓reduceIte]
        have : (5 : ℝ) ≤ p := by have := hp'.two_le; exact_mod_cast (show 5 ≤ p by omega)
        have hne : (p : ℝ) - 2 ≠ 0 := by linarith
        field_simp [hne]; ring
    rw [prod_congr rfl hstep, prod_one_add_primeFactors_eq_sum_divisors hd.2.1]
    refine sum_congr rfl fun t _ => ?_
    simp only [h, prod_inv_distrib]
  have hdiv_mem : ∀ d ∈ Dset, ∀ m ∈ d.divisors, m ∈ Dset := by
    intro d hd m hm
    simp only [Dset, mem_filter, mem_Icc] at hd ⊢
    have hmd := Nat.dvd_of_mem_divisors hm
    have hm0 : m ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hmd (by omega))
    refine ⟨⟨by omega, (Nat.le_of_dvd (by omega) hmd).trans hd.1.2⟩,
      hd.2.1.squarefree_of_dvd hmd, fun p hp => ?_⟩
    rw [Nat.mem_primeFactors] at hp
    exact hd.2.2 p (Nat.mem_primeFactors.mpr ⟨hp.1, hp.2.1.trans hmd, by omega⟩)
  have hlcm_pf : ∀ d₁ ∈ Dset, ∀ d₂ ∈ Dset,
      (Nat.lcm d₁ d₂).primeFactors = d₁.primeFactors ∪ d₂.primeFactors := by
    intro d₁ hd₁ d₂ hd₂
    have h10 : d₁ ≠ 0 := (mem_filter.mp hd₁).2.1.ne_zero
    have h20 : d₂ ≠ 0 := (mem_filter.mp hd₂).2.1.ne_zero
    ext p
    simp only [Nat.mem_primeFactors, mem_union, Nat.lcm_ne_zero h10 h20,
      h10, h20, ne_eq, not_false_eq_true, and_true]
    constructor
    · rintro ⟨hp, hdvd⟩
      have hpos := (hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero h10 h20)).mp
        (show p ^ 1 ∣ Nat.lcm d₁ d₂ by simpa using hdvd)
      rw [Nat.factorization_lcm h10 h20, Finsupp.sup_apply] at hpos
      rcases le_max_iff.mp hpos with hl | hr
      · left; exact ⟨hp, by simpa using (hp.pow_dvd_iff_le_factorization h10).mpr hl⟩
      · right; exact ⟨hp, by simpa using (hp.pow_dvd_iff_le_factorization h20).mpr hr⟩
    · rintro (⟨hp, hdvd⟩ | ⟨hp, hdvd⟩)
      · exact ⟨hp, hdvd.trans (Nat.dvd_lcm_left d₁ d₂)⟩
      · exact ⟨hp, hdvd.trans (Nat.dvd_lcm_right d₁ d₂)⟩
  have hg_lcm : ∀ d₁ ∈ Dset, ∀ d₂ ∈ Dset,
      g (Nat.lcm d₁ d₂) = g d₁ * g d₂ * (g (Nat.gcd d₁ d₂))⁻¹ := by
    intro d₁ hd₁ d₂ hd₂
    have h1 := (mem_filter.mp hd₁).2.1
    have h2 := (mem_filter.mp hd₂).2.1
    have h10 : d₁ ≠ 0 := h1.ne_zero
    have h20 : d₂ ≠ 0 := h2.ne_zero
    have hg_sqf : Squarefree (Nat.gcd d₁ d₂) := h1.squarefree_of_dvd (Nat.gcd_dvd_left d₁ d₂)
    have hl_sqf : Squarefree (Nat.lcm d₁ d₂) := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro q hq hq2
      have hfac := (hq.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero h10 h20)).mp
        (show q ^ 2 ∣ Nat.lcm d₁ d₂ by simpa [sq] using hq2)
      rw [Nat.factorization_lcm h10 h20, Finsupp.sup_apply] at hfac
      rcases le_max_iff.mp hfac with hl | hr
      · exact hq.not_isUnit (h1 q (by simpa [sq] using (hq.pow_dvd_iff_le_factorization h10).mpr hl))
      · exact hq.not_isUnit (h2 q (by simpa [sq] using (hq.pow_dvd_iff_le_factorization h20).mpr hr))
    rw [hg_prod _ hl_sqf, hg_prod _ h1, hg_prod _ h2, hg_prod _ hg_sqf]
    have hunion := hlcm_pf d₁ hd₁ d₂ hd₂
    have hinter : (Nat.gcd d₁ d₂).primeFactors = d₁.primeFactors ∩ d₂.primeFactors := by
      ext p
      simp only [Nat.mem_primeFactors, mem_inter, Nat.dvd_gcd_iff]
      have hg0 : Nat.gcd d₁ d₂ ≠ 0 := mt Nat.gcd_eq_zero_iff.mp (by tauto)
      exact ⟨fun ⟨hp, ⟨h1d, h2d⟩, _⟩ => ⟨⟨hp, h1d, h10⟩, ⟨hp, h2d, h20⟩⟩,
        fun ⟨⟨hp, h1d, _⟩, ⟨_, h2d, _⟩⟩ => ⟨hp, ⟨h1d, h2d⟩, hg0⟩⟩
    rw [hunion, hinter]
    have hne : ∏ p ∈ d₁.primeFactors ∩ d₂.primeFactors,
        ((if p ∈ P3 then (1 : ℝ) else 2) / (p : ℝ)) ≠ 0 := by
      rw [← hinter, ← hg_prod _ hg_sqf]
      exact (g_pos _ (hdiv_mem d₁ hd₁ _ (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left d₁ d₂, h10⟩))).ne'
    have hprod_ui := Finset.prod_union_inter (s₁ := d₁.primeFactors) (s₂ := d₂.primeFactors)
      (f := fun p => (if p ∈ P3 then (1 : ℝ) else 2) / (p : ℝ))
    field_simp [hne]
    linarith
  let lam : ℕ → ℝ := fun d =>
    (1 / (g d * L)) * ∑ m ∈ Dset.filter (fun m => d ∣ m),
      ((ArithmeticFunction.moebius (m / d) : ℝ) * (ArithmeticFunction.moebius m : ℝ) * h m)
  have hlam1 : lam 1 = 1 := by
    simp only [lam, Nat.div_one, one_dvd, filter_true]
    have hg1 : g 1 = 1 := by simp [g, ν]
    rw [hg1, one_mul]
    have hsum_eq : ∑ m ∈ Dset,
        ((ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius m : ℝ) * h m) = L := by
      refine sum_congr rfl fun m hm => ?_
      have hsq : (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius m : ℝ) = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (mem_filter.mp hm).2.1
        rw [sq] at this
        exact_mod_cast this
      rw [hsq, one_mul]
    rw [hsum_eq, one_div, inv_mul_cancel₀ hL_pos.ne']
  have hy_eq : ∀ m ∈ Dset,
      ∑ d ∈ Dset.filter (fun d => m ∣ d), lam d * g d =
      (ArithmeticFunction.moebius m : ℝ) * h m / L := by
    intro m hm
    have hterm : ∀ d ∈ Dset.filter (fun d => m ∣ d),
        lam d * g d = (1 / L) * ∑ k ∈ Dset.filter (fun k => d ∣ k),
          ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ) * h k) := by
      intro d hd
      have hd_mem := (mem_filter.mp hd).1
      have hgd_ne : g d ≠ 0 := (g_pos d hd_mem).ne'
      simp only [lam]
      field_simp [hgd_ne, hL_pos.ne']
    rw [sum_congr rfl hterm, ← Finset.mul_sum]
    have hswap :
        ∑ d ∈ Dset.filter (fun d => m ∣ d),
          ∑ k ∈ Dset.filter (fun k => d ∣ k),
            ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ) * h k) =
        ∑ k ∈ Dset.filter (fun k => m ∣ k),
          ((ArithmeticFunction.moebius k : ℝ) * h k) *
          (∑ d ∈ Dset.filter (fun d => m ∣ d ∧ d ∣ k),
            (ArithmeticFunction.moebius (k / d) : ℝ)) := by
      have h1 :
          ∑ d ∈ Dset.filter (fun d => m ∣ d),
            ∑ k ∈ Dset.filter (fun k => d ∣ k),
              ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ) * h k) =
          ∑ d ∈ Dset, ∑ k ∈ Dset,
            if m ∣ d ∧ d ∣ k then
              (ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ) * h k
            else 0 := by
        rw [Finset.sum_filter]
        refine sum_congr rfl fun d _ => ?_
        by_cases hmd : m ∣ d
        · simp only [hmd, ↓reduceIte, true_and, Finset.sum_filter]
        · simp only [hmd, ↓reduceIte, false_and]
          simp
      have h2 :
          ∑ k ∈ Dset.filter (fun k => m ∣ k),
            ((ArithmeticFunction.moebius k : ℝ) * h k) *
            (∑ d ∈ Dset.filter (fun d => m ∣ d ∧ d ∣ k),
              (ArithmeticFunction.moebius (k / d) : ℝ)) =
          ∑ k ∈ Dset, ∑ d ∈ Dset,
            if m ∣ d ∧ d ∣ k then
              (ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ) * h k
            else 0 := by
        rw [Finset.sum_filter]
        refine sum_congr rfl fun k _ => ?_
        by_cases hmk : m ∣ k
        · simp only [hmk, ↓reduceIte, Finset.mul_sum, Finset.sum_filter]
          refine sum_congr rfl fun d _ => by split_ifs <;> ring
        · simp only [hmk, ↓reduceIte]
          symm
          refine Finset.sum_eq_zero fun d _ => ?_
          split_ifs with hcond
          · exact absurd (hcond.1.trans hcond.2) hmk
          · rfl
      rw [h1, h2, Finset.sum_comm]
    have hmoeb : ∀ k ∈ Dset.filter (fun k => m ∣ k),
        ∑ d ∈ Dset.filter (fun d => m ∣ d ∧ d ∣ k),
          (ArithmeticFunction.moebius (k / d) : ℝ) = if k = m then 1 else 0 := by
      intro k hk
      rw [mem_filter] at hk
      have hk0 : k ≠ 0 := (mem_filter.mp hk.1).2.1.ne_zero
      have hm0 : m ≠ 0 := (mem_filter.mp hm).2.1.ne_zero
      have hkm_pos : 1 ≤ k / m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hk.2)
        (Nat.pos_of_ne_zero hm0)
      have hbij : ∑ d ∈ Dset.filter (fun d => m ∣ d ∧ d ∣ k),
            (ArithmeticFunction.moebius (k / d) : ℝ) =
          ∑ t ∈ (k / m).divisors, (ArithmeticFunction.moebius t : ℝ) := by
        refine Finset.sum_bij (fun d _ => k / d) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro d hd
          rw [mem_filter] at hd
          rw [Nat.mem_divisors]
          refine ⟨?_, by omega⟩
          obtain ⟨q, rfl⟩ := hd.2.1
          obtain ⟨r, hr⟩ := hd.2.2
          have hkm : k / m = q * r := by
            rw [hr, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)]
          have hkd : k / (m * q) = r := by
            rw [hr, Nat.mul_div_cancel_left _ (Nat.mul_pos (Nat.pos_of_ne_zero hm0) (by
              rcases Nat.eq_zero_or_pos q with rfl | hqp
              · simp at hr; exact absurd hr hk0
              · exact hqp))]
          rw [hkm, hkd]
          exact dvd_mul_left r q
        · intro d₁ hd₁ d₂ hd₂ heq
          rw [mem_filter] at hd₁ hd₂
          have h1 := Nat.mul_div_cancel' hd₁.2.2
          have h2 := Nat.mul_div_cancel' hd₂.2.2
          have hpos : 0 < k / d₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd₁.2.2)
            (Nat.pos_of_ne_zero (mem_filter.mp hd₁.1).2.1.ne_zero)
          rw [← heq] at h2
          exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
        · intro t ht
          rw [Nat.mem_divisors] at ht
          obtain ⟨q, hq⟩ := ht.1
          have hmul : m * q * t = k := by
            calc m * q * t = m * (t * q) := by ring
              _ = m * (k / m) := by rw [← hq]
              _ = k := Nat.mul_div_cancel' hk.2
          have hd_mem : m * q ∈ Dset :=
            hdiv_mem k hk.1 (m * q) (Nat.mem_divisors.mpr ⟨⟨t, hmul.symm⟩, hk0⟩)
          refine ⟨m * q, ?_, ?_⟩
          · rw [mem_filter]
            exact ⟨hd_mem, dvd_mul_right m q, ⟨t, hmul.symm⟩⟩
          · rw [← hmul, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by
              intro h0; rw [h0, zero_mul] at hmul; exact hk0 hmul.symm))]
      rw [hbij]
      have hzeta : (∑ t ∈ (k / m).divisors, (ArithmeticFunction.moebius t : ℝ)) =
          if k / m = 1 then 1 else 0 := by
        have hmz := congr_arg (fun f : ArithmeticFunction ℝ => f (k / m))
          (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
        rw [ArithmeticFunction.coe_mul_zeta_apply] at hmz
        simpa [ArithmeticFunction.one_apply] using hmz
      rw [hzeta]
      have hiff : k / m = 1 ↔ k = m := by
        constructor
        · intro h1; have := Nat.mul_div_cancel' hk.2; rw [h1, mul_one] at this; exact this.symm
        · rintro rfl; exact Nat.div_self (Nat.pos_of_ne_zero hm0)
      simp [hiff]
    have hsum_final :
        ∑ k ∈ Dset.filter (fun k => m ∣ k),
          ((ArithmeticFunction.moebius k : ℝ) * h k) *
          (∑ d ∈ Dset.filter (fun d => m ∣ d ∧ d ∣ k),
            (ArithmeticFunction.moebius (k / d) : ℝ)) =
        (ArithmeticFunction.moebius m : ℝ) * h m := by
      have heq_f : ∀ k ∈ Dset.filter (fun k => m ∣ k),
          ((ArithmeticFunction.moebius k : ℝ) * h k) *
          (∑ d ∈ Dset.filter (fun d => m ∣ d ∧ d ∣ k),
            (ArithmeticFunction.moebius (k / d) : ℝ)) =
          if k = m then (ArithmeticFunction.moebius m : ℝ) * h m else 0 := by
        intro k hk
        rw [hmoeb k hk]
        split_ifs with hkm
        · subst hkm; ring
        · ring
      rw [sum_congr rfl heq_f, Finset.sum_ite_eq']
      simp [hm]
    calc (1 / L) * ∑ d ∈ Dset.filter (fun d => m ∣ d),
            ∑ k ∈ Dset.filter (fun k => d ∣ k),
              ((ArithmeticFunction.moebius (k / d) : ℝ) * (ArithmeticFunction.moebius k : ℝ) * h k)
        = (1 / L) * ((ArithmeticFunction.moebius m : ℝ) * h m) := by
          rw [hswap, hsum_final]
      _ = (ArithmeticFunction.moebius m : ℝ) * h m / L := by ring
  have hlam_abs : ∀ d ∈ Dset, |lam d| ≤ 1 := by
    intro d hd
    have hd_sqf := (mem_filter.mp hd).2.1
    have hd0 : d ≠ 0 := hd_sqf.ne_zero
    have hsum_sign : ∑ m ∈ Dset.filter (fun m => d ∣ m),
        ((ArithmeticFunction.moebius (m / d) : ℝ) * (ArithmeticFunction.moebius m : ℝ) * h m) =
        (ArithmeticFunction.moebius d : ℝ) * h d *
        ∑ r ∈ Dset.filter (fun r => Nat.Coprime d r ∧ d * r ≤ Q), h r := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun m _ => m / d) ?_ ?_ ?_ ?_
      · intro m hm
        rw [mem_filter] at hm
        have hr_mem : m / d ∈ Dset :=
          hdiv_mem m hm.1 (m / d) (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hm.2,
            (mem_filter.mp hm.1).2.1.ne_zero⟩)
        have hmul : d * (m / d) = m := Nat.mul_div_cancel' hm.2
        have hcop : Nat.Coprime d (m / d) := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          set g := Nat.gcd d (m / d)
          have hp := Nat.minFac_prime hne
          have h1 : g.minFac ∣ d := (Nat.minFac_dvd g).trans (Nat.gcd_dvd_left _ _)
          have h2 : g.minFac ∣ m / d := (Nat.minFac_dvd g).trans (Nat.gcd_dvd_right _ _)
          have hsq : g.minFac * g.minFac ∣ m := by
            rw [← hmul]; exact mul_dvd_mul h1 h2
          exact hp.not_isUnit ((mem_filter.mp hm.1).2.1 _ hsq)
        rw [mem_filter]
        exact ⟨hr_mem, hcop, by rw [hmul]; exact (mem_Icc.mp (mem_filter.mp hm.1).1).2⟩
      · intro m₁ hm₁ m₂ hm₂ heq
        rw [mem_filter] at hm₁ hm₂
        have h1 := Nat.mul_div_cancel' hm₁.2
        have h2 := Nat.mul_div_cancel' hm₂.2
        rw [heq] at h1
        exact h1.symm.trans h2
      · intro r hr
        rw [mem_filter] at hr
        have hrm := mem_filter.mp hr.1
        have hdm := mem_filter.mp hd
        have hdr_sqf : Squarefree (d * r) := (Nat.squarefree_mul hr.2.1).mpr ⟨hdm.2.1, hrm.2.1⟩
        have hdr_mem : d * r ∈ Dset := by
          simp only [Dset, mem_filter, mem_Icc]
          refine ⟨⟨Nat.mul_pos (by omega) (by have := (mem_Icc.mp hrm.1).1; omega), hr.2.2⟩,
            hdr_sqf, fun p hp => ?_⟩
          rw [Nat.primeFactors_mul hd0 hrm.2.1.ne_zero, mem_union] at hp
          rcases hp with h | h
          · exact hdm.2.2 p h
          · exact hrm.2.2 p h
        refine ⟨d * r, ?_, Nat.mul_div_cancel_left r (Nat.pos_of_ne_zero hd0)⟩
        rw [mem_filter]
        exact ⟨hdr_mem, dvd_mul_right d r⟩
      · intro m hm
        rw [mem_filter] at hm
        have hmul : d * (m / d) = m := Nat.mul_div_cancel' hm.2
        have hcop : Nat.Coprime d (m / d) := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          set g := Nat.gcd d (m / d)
          have hp := Nat.minFac_prime hne
          have h1 : g.minFac ∣ d := (Nat.minFac_dvd g).trans (Nat.gcd_dvd_left _ _)
          have h2 : g.minFac ∣ m / d := (Nat.minFac_dvd g).trans (Nat.gcd_dvd_right _ _)
          exact hp.not_isUnit ((mem_filter.mp hm.1).2.1 _ (by rw [← hmul]; exact mul_dvd_mul h1 h2))
        have hmu_mul : (ArithmeticFunction.moebius m : ℝ) =
            (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius (m / d) : ℝ) := by
          conv_lhs => rw [← hmul]
          have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
          exact_mod_cast this
        have hmu_sq : (ArithmeticFunction.moebius (m / d) : ℝ) *
            (ArithmeticFunction.moebius (m / d) : ℝ) = 1 := by
          have hr_sqf : Squarefree (m / d) :=
            (mem_filter.mp hm.1).2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hm.2)
          have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr_sqf
          rw [sq] at this
          exact_mod_cast this
        have hh_mul : h m = h d * h (m / d) := by
          have hr0 : m / d ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hmul
            exact (mem_filter.mp hm.1).2.1.ne_zero hmul.symm
          simp only [h]
          conv_lhs => rw [← hmul]
          rw [Nat.primeFactors_mul hd0 hr0,
            prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
        rw [hmu_mul, hh_mul]
        calc (ArithmeticFunction.moebius (m / d) : ℝ) *
              ((ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius (m / d) : ℝ)) *
              (h d * h (m / d))
            = (ArithmeticFunction.moebius d : ℝ) * h d *
              ((ArithmeticFunction.moebius (m / d) : ℝ) * (ArithmeticFunction.moebius (m / d) : ℝ)) *
              h (m / d) := by ring
          _ = (ArithmeticFunction.moebius d : ℝ) * h d * h (m / d) := by rw [hmu_sq, mul_one]
    have hh_div_g : h d / g d = ∑ t ∈ d.divisors, h t := by
      have hdm := mem_filter.mp hd
      rw [hg_prod d hdm.2.1]
      simp only [h]
      rw [← prod_div_distrib]
      have hstep : ∀ p ∈ d.primeFactors,
          ((if p ∈ P3 then (1 : ℝ) else 2) / ((p : ℝ) - (if p ∈ P3 then 1 else 2))) /
          ((if p ∈ P3 then (1 : ℝ) else 2) / (p : ℝ)) =
          1 + (if p ∈ P3 then (1 : ℝ) else 2) / ((p : ℝ) - (if p ∈ P3 then 1 else 2)) := by
        intro p hp
        have hp' := Nat.prime_of_mem_primeFactors hp
        rcases hdm.2.2 p hp with h3 | h4
        · simp only [h3, ↓reduceIte]
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
          have hne : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp [hne]; ring
        · have hnot : p ∉ P3 := fun h => by have := (hP3 p h).2; omega
          simp only [hnot, ↓reduceIte]
          have : (5 : ℝ) ≤ p := by have := hp'.two_le; exact_mod_cast (show 5 ≤ p by omega)
          have hne : (p : ℝ) - 2 ≠ 0 := by linarith
          field_simp [hne]; ring
      rw [prod_congr rfl hstep, prod_one_add_primeFactors_eq_sum_divisors hdm.2.1]
    have hlam_eq : lam d = (ArithmeticFunction.moebius d : ℝ) / L *
        ((∑ t ∈ d.divisors, h t) *
         ∑ r ∈ Dset.filter (fun r => Nat.Coprime d r ∧ d * r ≤ Q), h r) := by
      simp only [lam]
      rw [hsum_sign, ← hh_div_g]
      have hgd_ne : g d ≠ 0 := (g_pos d hd).ne'
      field_simp [hgd_ne, hL_pos.ne']
    rw [hlam_eq, abs_mul, abs_div]
    have habs_mu : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
      have := ArithmeticFunction.abs_moebius_eq_one_of_squarefree hd_sqf
      exact_mod_cast this
    rw [habs_mu, abs_of_pos hL_pos, abs_of_nonneg (mul_nonneg
      (sum_nonneg fun t ht => (h_pos t (hdiv_mem d hd t ht)).le)
      (sum_nonneg fun r hr => (h_pos r (mem_filter.mp hr).1).le))]
    rw [one_div, inv_mul_le_iff₀ hL_pos, mul_one]
    set R := Dset.filter (fun r => Nat.Coprime d r ∧ d * r ≤ Q)
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    have hinj : ∀ tr1 ∈ d.divisors ×ˢ R, ∀ tr2 ∈ d.divisors ×ˢ R,
        tr1.1 * tr1.2 = tr2.1 * tr2.2 → tr1 = tr2 := by
      intro tr1 h1 tr2 h2 heq
      rw [mem_product, mem_filter] at h1 h2
      have hd1 := Nat.dvd_of_mem_divisors h1.1
      have hd2 := Nat.dvd_of_mem_divisors h2.1
      have hcop1 : Nat.Coprime d tr1.2 := h1.2.2.1
      have hcop2 : Nat.Coprime d tr2.2 := h2.2.2.1
      have hgcd1 : Nat.gcd (tr1.1 * tr1.2) d = tr1.1 := by
        rw [hcop1.symm.gcd_mul_right_cancel tr1.1, Nat.gcd_eq_left hd1]
      have hgcd2 : Nat.gcd (tr2.1 * tr2.2) d = tr2.1 := by
        rw [hcop2.symm.gcd_mul_right_cancel tr2.1, Nat.gcd_eq_left hd2]
      have ht_eq : tr1.1 = tr2.1 := by rw [← hgcd1, heq, hgcd2]
      have ht_pos : 0 < tr1.1 := Nat.pos_of_dvd_of_pos hd1 (Nat.pos_of_ne_zero hd0)
      have hr_eq : tr1.2 = tr2.2 := Nat.eq_of_mul_eq_mul_left ht_pos (by rwa [← ht_eq] at heq)
      exact Prod.ext ht_eq hr_eq
    have hmaps : ∀ tr ∈ d.divisors ×ˢ R, tr.1 * tr.2 ∈ Dset := by
      intro tr htr
      rw [mem_product, mem_filter] at htr
      have ht_mem := hdiv_mem d hd tr.1 htr.1
      have hr_mem := htr.2.1
      have hdvd := Nat.dvd_of_mem_divisors htr.1
      have hcop : Nat.Coprime tr.1 tr.2 := htr.2.2.1.coprime_dvd_left hdvd
      have hle : tr.1 * tr.2 ≤ Q :=
        (Nat.mul_le_mul_right tr.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hdvd)).trans htr.2.2.2
      simp only [Dset, mem_filter, mem_Icc] at ht_mem hr_mem ⊢
      refine ⟨⟨Nat.mul_pos (by omega) (by omega), hle⟩,
        (Nat.squarefree_mul hcop).mpr ⟨ht_mem.2.1, hr_mem.2.1⟩, fun p hp => ?_⟩
      rw [Nat.primeFactors_mul (by omega) (by omega), mem_union] at hp
      rcases hp with h | h
      · exact ht_mem.2.2 p h
      · exact hr_mem.2.2 p h
    have hmul_h : ∀ tr ∈ d.divisors ×ˢ R, h tr.1 * h tr.2 = h (tr.1 * tr.2) := by
      intro tr htr
      rw [mem_product, mem_filter] at htr
      have hdvd := Nat.dvd_of_mem_divisors htr.1
      have hcop : Nat.Coprime tr.1 tr.2 := htr.2.2.1.coprime_dvd_left hdvd
      have ht0 : tr.1 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hd0))
      have hr0 : tr.2 ≠ 0 := (mem_filter.mp htr.2.1).2.1.ne_zero
      simp only [h]
      rw [Nat.primeFactors_mul ht0 hr0, prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
    calc ∑ tr ∈ d.divisors ×ˢ R, h tr.1 * h tr.2
        = ∑ tr ∈ d.divisors ×ˢ R, h (tr.1 * tr.2) := sum_congr rfl hmul_h
      _ = ∑ k ∈ (d.divisors ×ˢ R).image (fun tr => tr.1 * tr.2), h k :=
          (Finset.sum_image (f := h) (fun tr1 h1 tr2 h2 heq => hinj tr1 h1 tr2 h2 heq)).symm
      _ ≤ ∑ k ∈ Dset, h k := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun k hk _ => (h_pos k hk).le)
          intro k hk
          rw [mem_image] at hk
          obtain ⟨tr, htr, rfl⟩ := hk
          exact hmaps tr htr
  have hsieve1 : (OeisA69004.a n : ℝ) ≤
      ∑ s ∈ Ico 1 n, (∑ d ∈ Dset.filter (fun d => d ∣ n ^ 2 + s ^ 2), lam d) ^ 2 := by
    simp only [OeisA69004.a, Nat.cast_sum]
    refine sum_le_sum fun s hs => ?_
    split_ifs with hprime
    · rw [Nat.cast_one]
      have honly1 : Dset.filter (fun d => d ∣ n ^ 2 + s ^ 2) = {1} := by
        ext d
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hd, hdvd⟩
          by_contra hd1
          have hdm := mem_filter.mp hd
          have hp : d.minFac.Prime := Nat.minFac_prime hd1
          have hpd : d.minFac ∣ n ^ 2 + s ^ 2 := (Nat.minFac_dvd d).trans hdvd
          have hp_eq : d.minFac = n ^ 2 + s ^ 2 :=
            (Nat.prime_dvd_prime_iff_eq hp hprime).mp hpd
          have hpleQ : d.minFac ≤ Q :=
            (Nat.minFac_le (by have := (mem_Icc.mp hdm.1).1; omega)).trans (mem_Icc.mp hdm.1).2
          have hs1 : 1 ≤ s := (mem_Ico.mp hs).1
          have hQn' : Q ≤ n := hQn
          nlinarith [hn_pos, hpleQ, hs1, hp_eq, hQn']
        · rintro rfl
          exact ⟨h1_mem, one_dvd _⟩
      rw [honly1, sum_singleton, hlam1, one_pow]
    · rw [Nat.cast_zero]
      exact sq_nonneg _
  have hexpand :
      ∑ s ∈ Ico 1 n, (∑ d ∈ Dset.filter (fun d => d ∣ n ^ 2 + s ^ 2), lam d) ^ 2 =
      ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset,
        lam d₁ * lam d₂ * (#{s ∈ Ico 1 n | Nat.lcm d₁ d₂ ∣ n ^ 2 + s ^ 2} : ℝ) := by
    have hsq : ∀ s ∈ Ico 1 n,
        (∑ d ∈ Dset.filter (fun d => d ∣ n ^ 2 + s ^ 2), lam d) ^ 2 =
        ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset,
          if Nat.lcm d₁ d₂ ∣ n ^ 2 + s ^ 2 then lam d₁ * lam d₂ else 0 := by
      intro s _
      rw [sq, Finset.sum_mul_sum, Finset.sum_filter]
      refine sum_congr rfl fun d₁ _ => ?_
      rw [Finset.sum_filter]
      by_cases h1 : d₁ ∣ n ^ 2 + s ^ 2
      · simp only [h1, ↓reduceIte]
        refine sum_congr rfl fun d₂ _ => ?_
        by_cases h2 : d₂ ∣ n ^ 2 + s ^ 2
        · simp [h2, Nat.lcm_dvd h1 h2]
        · have : ¬ Nat.lcm d₁ d₂ ∣ n ^ 2 + s ^ 2 := fun h => h2 ((Nat.dvd_lcm_right d₁ d₂).trans h)
          simp [h2, this]
      · simp only [h1, ↓reduceIte]
        symm
        refine Finset.sum_eq_zero fun d₂ _ => ?_
        have : ¬ Nat.lcm d₁ d₂ ∣ n ^ 2 + s ^ 2 := fun h => h1 ((Nat.dvd_lcm_left d₁ d₂).trans h)
        simp [this]
    rw [sum_congr rfl hsq, Finset.sum_comm]
    refine sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun d₂ _ => ?_
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have hmain_err :
      ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset,
        lam d₁ * lam d₂ * (#{s ∈ Ico 1 n | Nat.lcm d₁ d₂ ∣ n ^ 2 + s ^ 2} : ℝ) ≤
      (n : ℝ) * (∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂)) +
      ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, |lam d₁| * |lam d₂| * ν (Nat.lcm d₁ d₂) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_le_sum fun d₁ hd₁ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_le_sum fun d₂ hd₂ => ?_
    have h1 := mem_filter.mp hd₁
    have h2 := mem_filter.mp hd₂
    have hl_ne0 : Nat.lcm d₁ d₂ ≠ 0 := Nat.lcm_ne_zero h1.2.1.ne_zero h2.2.1.ne_zero
    have hl_pos : 1 ≤ Nat.lcm d₁ d₂ := Nat.pos_of_ne_zero hl_ne0
    have : NeZero (Nat.lcm d₁ d₂) := ⟨hl_ne0⟩
    have hl_sqf : Squarefree (Nat.lcm d₁ d₂) := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro q hq hq2
      have hfac := (hq.pow_dvd_iff_le_factorization hl_ne0).mp
        (show q ^ 2 ∣ Nat.lcm d₁ d₂ by simpa [sq] using hq2)
      rw [Nat.factorization_lcm h1.2.1.ne_zero h2.2.1.ne_zero, Finsupp.sup_apply] at hfac
      rcases le_max_iff.mp hfac with hl | hr
      · exact hq.not_isUnit (h1.2.1 q (by simpa [sq] using (hq.pow_dvd_iff_le_factorization h1.2.1.ne_zero).mpr hl))
      · exact hq.not_isUnit (h2.2.1 q (by simpa [sq] using (hq.pow_dvd_iff_le_factorization h2.2.1.ne_zero).mpr hr))
    have hl_pf : ∀ p ∈ (Nat.lcm d₁ d₂).primeFactors, p ∈ P3 ∨ p % 4 = 1 := by
      intro p hp
      rw [hlcm_pf d₁ hd₁ d₂ hd₂, mem_union] at hp
      rcases hp with hp1 | hp2
      · exact h1.2.2 p hp1
      · exact h2.2.2 p hp2
    have hsol : (#{x : ZMod (Nat.lcm d₁ d₂) | x ^ 2 + (n : ZMod (Nat.lcm d₁ d₂)) ^ 2 = 0} : ℝ) =
        ν (Nat.lcm d₁ d₂) := by
      rw [solCount_squarefree_eq hP3 hn_dvd hn_ndvd (Nat.lcm d₁ d₂) hl_sqf hl_pf]
      simp only [ν, Nat.cast_prod]
      refine prod_congr rfl fun p _ => by split_ifs <;> norm_num
    have habs := abs_card_Ico_dvd_sub_le n (Nat.lcm d₁ d₂) hn_pos hl_pos
    rw [hsol] at habs
    have hrew : (n : ℝ) * ν (Nat.lcm d₁ d₂) / (Nat.lcm d₁ d₂ : ℝ) = (n : ℝ) * g (Nat.lcm d₁ d₂) := by
      simp only [g]; ring
    rw [hrew] at habs
    set C := (#{s ∈ Ico 1 n | Nat.lcm d₁ d₂ ∣ n ^ 2 + s ^ 2} : ℝ)
    set M := (n : ℝ) * g (Nat.lcm d₁ d₂)
    set E := ν (Nat.lcm d₁ d₂)
    have hdiff : lam d₁ * lam d₂ * (C - M) ≤ |lam d₁| * |lam d₂| * E := by
      calc lam d₁ * lam d₂ * (C - M)
          ≤ |lam d₁ * lam d₂ * (C - M)| := le_abs_self _
        _ = |lam d₁| * |lam d₂| * |C - M| := by rw [abs_mul, abs_mul]
        _ ≤ |lam d₁| * |lam d₂| * E := mul_le_mul_of_nonneg_left habs (by positivity)
    linarith
  have hmain_eq :
      ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂) = 1 / L := by
    have hdiag :
        ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂) =
        ∑ m ∈ Dset, (h m)⁻¹ * (∑ d ∈ Dset.filter (fun d => m ∣ d), lam d * g d) ^ 2 := by
      have h1 : ∀ d₁ ∈ Dset, ∀ d₂ ∈ Dset,
          lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂) =
          ∑ m ∈ Dset, if m ∣ d₁ ∧ m ∣ d₂ then
            (h m)⁻¹ * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0 := by
        intro d₁ hd₁ d₂ hd₂
        rw [hg_lcm d₁ hd₁ d₂ hd₂]
        have hgcd_mem : Nat.gcd d₁ d₂ ∈ Dset :=
          hdiv_mem d₁ hd₁ _ (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left d₁ d₂, (mem_filter.mp hd₁).2.1.ne_zero⟩)
        rw [hg_inv_eq _ hgcd_mem]
        have hsum_eq : ∑ m ∈ (Nat.gcd d₁ d₂).divisors, (h m)⁻¹ =
            ∑ m ∈ Dset, if m ∣ d₁ ∧ m ∣ d₂ then (h m)⁻¹ else 0 := by
          rw [← Finset.sum_filter]
          refine sum_congr ?_ (fun _ _ => rfl)
          ext m
          simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
          constructor
          · rintro ⟨⟨hm1, hm2⟩, _⟩
            exact ⟨hdiv_mem d₁ hd₁ m (Nat.mem_divisors.mpr ⟨hm1, (mem_filter.mp hd₁).2.1.ne_zero⟩), hm1, hm2⟩
          · rintro ⟨hm_mem, hm1, hm2⟩
            exact ⟨⟨hm1, hm2⟩, (mem_filter.mp hgcd_mem).2.1.ne_zero⟩
        rw [hsum_eq, Finset.mul_sum, Finset.mul_sum]
        refine sum_congr rfl fun m _ => by split_ifs <;> ring
      calc ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂)
          = ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, ∑ m ∈ Dset,
              if m ∣ d₁ ∧ m ∣ d₂ then (h m)⁻¹ * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0 :=
            sum_congr rfl fun d₁ hd₁ => sum_congr rfl fun d₂ hd₂ => h1 d₁ hd₁ d₂ hd₂
        _ = ∑ m ∈ Dset, ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset,
              if m ∣ d₁ ∧ m ∣ d₂ then (h m)⁻¹ * (lam d₁ * g d₁) * (lam d₂ * g d₂) else 0 := by
            rw [Finset.sum_comm]
            conv_lhs =>
              arg 2; ext d₂
              rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            refine sum_congr rfl fun m _ => Finset.sum_comm
        _ = ∑ m ∈ Dset, (h m)⁻¹ * (∑ d ∈ Dset.filter (fun d => m ∣ d), lam d * g d) ^ 2 := by
            refine sum_congr rfl fun m _ => ?_
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            rw [Finset.sum_filter (s := Dset) (p := fun d => m ∣ d)]
            refine sum_congr rfl fun d₁ _ => ?_
            by_cases hmd1 : m ∣ d₁
            · simp only [hmd1, ↓reduceIte, true_and, Finset.mul_sum]
              rw [Finset.sum_filter (s := Dset) (p := fun d => m ∣ d)]
              refine sum_congr rfl fun d₂ _ => by split_ifs <;> ring
            · simp only [hmd1, ↓reduceIte, false_and]
              simp
    rw [hdiag]
    have hterm : ∀ m ∈ Dset,
        (h m)⁻¹ * (∑ d ∈ Dset.filter (fun d => m ∣ d), lam d * g d) ^ 2 = h m / L ^ 2 := by
      intro m hm
      rw [hy_eq m hm]
      have hmu2 : (ArithmeticFunction.moebius m : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (mem_filter.mp hm).2.1
      have hhm : h m ≠ 0 := (h_pos m hm).ne'
      field_simp [hhm, hL_pos.ne']
      exact hmu2
    rw [sum_congr rfl hterm, ← Finset.sum_div]
    change L / L ^ 2 = 1 / L
    field_simp [hL_pos.ne']
  have herr_le : ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, |lam d₁| * |lam d₂| * ν (Nat.lcm d₁ d₂) ≤ (Q : ℝ) ^ 4 := by
    have hν_le : ∀ d ∈ Dset, ν d ≤ (Q : ℝ) := by
      intro d hd
      have hdm := mem_filter.mp hd
      have hle_d : ν d ≤ (d : ℝ) := by
        have hpd : (∏ p ∈ d.primeFactors, p) = d := Nat.prod_primeFactors_of_squarefree hdm.2.1
        have hd_cast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
          conv_lhs => rw [← hpd]
          push_cast; rfl
        rw [hd_cast]
        simp only [ν]
        refine prod_le_prod (fun p _ => by split_ifs <;> norm_num) fun p hp => ?_
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        split_ifs <;> linarith
      have hdQ : (d : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hdm.1).2
      exact hle_d.trans hdQ
    have hν_lcm : ∀ d₁ ∈ Dset, ∀ d₂ ∈ Dset, ν (Nat.lcm d₁ d₂) ≤ ν d₁ * ν d₂ := by
      intro d₁ hd₁ d₂ hd₂
      have hunion := hlcm_pf d₁ hd₁ d₂ hd₂
      have hprod_ui := Finset.prod_union_inter (s₁ := d₁.primeFactors) (s₂ := d₂.primeFactors)
        (f := fun p => if p ∈ P3 then (1 : ℝ) else 2)
      have hinter_ge1 : (1 : ℝ) ≤ ∏ p ∈ d₁.primeFactors ∩ d₂.primeFactors,
          (if p ∈ P3 then (1 : ℝ) else 2) :=
        Finset.one_le_prod fun p _ => by split_ifs <;> norm_num
      simp only [ν, hunion]
      have hnn : 0 ≤ ∏ p ∈ d₁.primeFactors ∪ d₂.primeFactors, (if p ∈ P3 then (1 : ℝ) else 2) :=
        prod_nonneg fun p _ => by split_ifs <;> norm_num
      nlinarith
    have hcard_le : (#Dset : ℝ) ≤ Q := by
      have : #Dset ≤ #(Icc 1 Q) := card_le_card (filter_subset _ _)
      rw [Nat.card_Icc] at this
      have : #Dset ≤ Q := by omega
      exact_mod_cast this
    calc ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, |lam d₁| * |lam d₂| * ν (Nat.lcm d₁ d₂)
        ≤ ∑ _d₁ ∈ Dset, ∑ _d₂ ∈ Dset, (Q : ℝ) ^ 2 := by
          refine sum_le_sum fun d₁ hd₁ => sum_le_sum fun d₂ hd₂ => ?_
          have h1 := hlam_abs d₁ hd₁
          have h2 := hlam_abs d₂ hd₂
          have h3 := (hν_lcm d₁ hd₁ d₂ hd₂).trans
            (mul_le_mul (hν_le d₁ hd₁) (hν_le d₂ hd₂)
              (prod_nonneg fun _ _ => by split_ifs <;> norm_num) (by positivity))
          have hnn : 0 ≤ ν (Nat.lcm d₁ d₂) := prod_nonneg fun _ _ => by split_ifs <;> norm_num
          calc |lam d₁| * |lam d₂| * ν (Nat.lcm d₁ d₂)
              ≤ 1 * 1 * (Q : ℝ) ^ 2 := by
                have h12 : |lam d₁| * |lam d₂| ≤ 1 := by
                  nlinarith [abs_nonneg (lam d₁), abs_nonneg (lam d₂)]
                nlinarith [sq (Q : ℝ)]
            _ = (Q : ℝ) ^ 2 := by ring
      _ = (#Dset : ℝ) * ((#Dset : ℝ) * (Q : ℝ) ^ 2) := by simp [sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * ((Q : ℝ) * (Q : ℝ) ^ 2) := by
          refine mul_le_mul hcard_le (mul_le_mul_of_nonneg_right hcard_le (by positivity))
            (by positivity) (by positivity)
      _ = (Q : ℝ) ^ 4 := by ring
  calc (OeisA69004.a n : ℝ)
      ≤ ∑ s ∈ Ico 1 n, (∑ d ∈ Dset.filter (fun d => d ∣ n ^ 2 + s ^ 2), lam d) ^ 2 := hsieve1
    _ = ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset,
          lam d₁ * lam d₂ * (#{s ∈ Ico 1 n | Nat.lcm d₁ d₂ ∣ n ^ 2 + s ^ 2} : ℝ) := hexpand
    _ ≤ (n : ℝ) * (∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, lam d₁ * lam d₂ * g (Nat.lcm d₁ d₂)) +
        ∑ d₁ ∈ Dset, ∑ d₂ ∈ Dset, |lam d₁| * |lam d₂| * ν (Nat.lcm d₁ d₂) := hmain_err
    _ ≤ (n : ℝ) * (1 / L) + (Q : ℝ) ^ 4 := by rw [hmain_eq]; linarith [herr_le]
    _ = (n : ℝ) / L + (Q : ℝ) ^ 4 := by ring

/- ### Section 5: Assemble the disproof -/

private lemma exists_counterexample :
    ∃ n : ℕ, 1 < n ∧ 5 * OeisA69004.a n < Nat.primeCounting n := by
  obtain ⟨P3, hP3, hB⟩ := exists_finset_primes_mod4_eq3_prod_gt 200000
  set M := ∏ p ∈ P3, p
  have hM_pos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr <|
    prod_ne_zero_iff.mpr fun p hp => (hP3 p hp).1.ne_zero
  set r := 60 * (M + 1000) with hr_def
  have hr_ge : 60000 ≤ r := by omega
  set n := 2 ^ r * M
  set Q := 2 ^ (r / 5)
  set K := r / 12
  have hn_gt1 : 1 < n := by
    have h2r : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2
    calc 1 < 2 := by decide
      _ ≤ 2 ^ r := h2r
      _ ≤ 2 ^ r * M := Nat.le_mul_of_pos_right _ hM_pos
  have hQ_ge1 : 1 ≤ Q := Nat.one_le_pow _ _ (by decide)
  have hQ_le_n : Q ≤ n := by
    have h1 : Q ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    exact h1.trans (Nat.le_mul_of_pos_right _ hM_pos)
  have hK_ge2 : 2 ≤ K := by omega
  have hM_le_pow : M ≤ 2 ^ M := (Nat.lt_two_pow_self (n := M)).le
  have h24KM_le_Q : 2 * 4 ^ K * M ≤ Q := by
    have h4K : 4 ^ K = 2 ^ (2 * K) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    calc 2 * 4 ^ K * M
        = 2 ^ (2 * K + 1) * M := by rw [h4K, pow_succ']
      _ ≤ 2 ^ (2 * K + 1) * 2 ^ M := Nat.mul_le_mul_left _ hM_le_pow
      _ = 2 ^ (2 * K + 1 + M) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (r / 5) := Nat.pow_le_pow_right (by decide) (by omega)
  set Dset := (Finset.Icc 1 Q).filter
    (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, p ∈ P3 ∨ p % 4 = 1)
  let h : ℕ → ℝ := fun d => ∏ p ∈ d.primeFactors,
    ((if p ∈ P3 then (1 : ℝ) else 2) / ((p : ℝ) - (if p ∈ P3 then 1 else 2)))
  have h_pos : ∀ d ∈ Dset, 0 < h d := by
    intro d hd
    simp only [Dset, mem_filter, mem_Icc] at hd
    refine prod_pos fun p hp => ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    rcases hd.2.2 p hp with h3 | h4
    · simp only [h3, ↓reduceIte]
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
      exact div_pos zero_lt_one (by linarith)
    · have hnot : p ∉ P3 := fun h => by have := (hP3 p h).2; omega
      simp only [hnot, ↓reduceIte]
      have : (5 : ℝ) ≤ p := by have := hp'.two_le; exact_mod_cast (show 5 ≤ p by omega)
      exact div_pos (by norm_num) (by linarith)
  set D1 := (Finset.Icc (1 : ℕ) (2 * 4 ^ K)).filter
    (fun d : ℕ => Squarefree d ∧ ∀ p ∈ d.primeFactors, p % 4 = 1)
  have hM_sqf : Squarefree M := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro q hq hq2
    by_cases hqP : q ∈ P3
    · have hsplit : M = q * ∏ p ∈ P3.erase q, p := (Finset.mul_prod_erase P3 id hqP).symm
      rw [hsplit] at hq2
      have hqd : q ∣ ∏ p ∈ P3.erase q, p := (mul_dvd_mul_iff_left hq.ne_zero).mp hq2
      rw [hq.prime.dvd_finsetProd_iff] at hqd
      obtain ⟨p, hp, hqp⟩ := hqd
      exact (mem_erase.mp hp).1
        ((Nat.prime_dvd_prime_iff_eq hq (hP3 p (mem_of_mem_erase hp)).1).mp hqp).symm
    · have hqd : q ∣ M := dvd_of_mul_left_dvd hq2
      rw [hq.prime.dvd_finsetProd_iff] at hqd
      obtain ⟨p, hp, hqp⟩ := hqd
      have := (Nat.prime_dvd_prime_iff_eq hq (hP3 p hp).1).mp hqp
      exact hqP (this ▸ hp)
  have hM_pf : M.primeFactors = P3 := by
    ext p
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpd, _⟩
      rw [hp.prime.dvd_finsetProd_iff] at hpd
      obtain ⟨q, hq, hpq⟩ := hpd
      have := (Nat.prime_dvd_prime_iff_eq hp (hP3 q hq).1).mp hpq
      exact this ▸ hq
    · intro hp
      exact ⟨(hP3 p hp).1, dvd_prod_of_mem _ hp, by omega⟩
  have hB_eq : ∏ p ∈ P3, ((p : ℝ) / ((p : ℝ) - 1)) = ∑ d3 ∈ M.divisors, h d3 := by
    have hstep : ∀ p ∈ P3, ((p : ℝ) / ((p : ℝ) - 1)) = 1 + (1 : ℝ) / ((p : ℝ) - 1) := by
      intro p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hP3 p hp).1.two_le
      have hne : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hne]; ring
    rw [prod_congr rfl hstep, ← hM_pf, prod_one_add_primeFactors_eq_sum_divisors hM_sqf]
    refine sum_congr rfl fun t ht => ?_
    simp only [h]
    refine prod_congr rfl fun p hp => ?_
    have hpP3 : p ∈ P3 := by
      rw [← hM_pf]
      rw [Nat.mem_primeFactors] at hp ⊢
      exact ⟨hp.1, hp.2.1.trans (Nat.dvd_of_mem_divisors ht), by omega⟩
    simp [hpP3]
  have hS1_eq : ∑ d1 ∈ D1, ∏ p ∈ d1.primeFactors, ((2 : ℝ) / ((p : ℝ) - 2)) =
      ∑ d1 ∈ D1, h d1 := by
    refine sum_congr rfl fun d1 hd1 => ?_
    simp only [h]
    refine prod_congr rfl fun p hp => ?_
    have hnot : p ∉ P3 := by
      intro hmem
      have h3 := (hP3 p hmem).2
      have h1 := (mem_filter.mp hd1).2.2 p hp
      omega
    simp [hnot]
  have hL_ge : (∏ p ∈ P3, ((p : ℝ) / ((p : ℝ) - 1))) * (((K : ℝ) - 1) / 192) ≤
      ∑ d ∈ Dset, h d := by
    have hS1 := sum_h_mod4_eq1_lower K hK_ge2
    change (((K : ℝ) - 1) / 192) ≤ ∑ d1 ∈ D1, ∏ p ∈ d1.primeFactors, ((2 : ℝ) / ((p : ℝ) - 2)) at hS1
    rw [hS1_eq] at hS1
    have hprod_le : (∑ d3 ∈ M.divisors, h d3) * (∑ d1 ∈ D1, h d1) ≤ ∑ d ∈ Dset, h d := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      have hcop_pair : ∀ p ∈ M.divisors ×ˢ D1, Nat.Coprime p.1 p.2 := by
        intro p hp
        rw [mem_product] at hp
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        set q := (Nat.gcd p.1 p.2).minFac
        have hq : q.Prime := Nat.minFac_prime hne
        have hq1 : q ∣ M := (Nat.minFac_dvd _).trans ((Nat.gcd_dvd_left _ _).trans (Nat.dvd_of_mem_divisors hp.1))
        have hq2 : q ∣ p.2 := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
        have hqP3 : q ∈ P3 := by
          rw [← hM_pf]; exact Nat.mem_primeFactors.mpr ⟨hq, hq1, by omega⟩
        have h3 := (hP3 q hqP3).2
        have h1 := (mem_filter.mp hp.2).2.2 q (Nat.mem_primeFactors.mpr ⟨hq, hq2, (mem_filter.mp hp.2).2.1.ne_zero⟩)
        omega
      have hinj : ∀ p1 ∈ M.divisors ×ˢ D1, ∀ p2 ∈ M.divisors ×ˢ D1,
          p1.1 * p1.2 = p2.1 * p2.2 → p1 = p2 := by
        intro p1 h1 p2 h2 heq
        have hcopM1 : Nat.Coprime M p1.2 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          set q := (Nat.gcd M p1.2).minFac
          have hq : q.Prime := Nat.minFac_prime hne
          have hqM : q ∈ P3 := by
            rw [← hM_pf]
            exact Nat.mem_primeFactors.mpr ⟨hq, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _), by omega⟩
          have hq2 := (mem_filter.mp (mem_product.mp h1).2).2.2 q
            (Nat.mem_primeFactors.mpr ⟨hq, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _),
              (mem_filter.mp (mem_product.mp h1).2).2.1.ne_zero⟩)
          have := (hP3 q hqM).2; omega
        have hcopM2 : Nat.Coprime M p2.2 := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          set q := (Nat.gcd M p2.2).minFac
          have hq : q.Prime := Nat.minFac_prime hne
          have hqM : q ∈ P3 := by
            rw [← hM_pf]
            exact Nat.mem_primeFactors.mpr ⟨hq, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _), by omega⟩
          have hq2 := (mem_filter.mp (mem_product.mp h2).2).2.2 q
            (Nat.mem_primeFactors.mpr ⟨hq, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _),
              (mem_filter.mp (mem_product.mp h2).2).2.1.ne_zero⟩)
          have := (hP3 q hqM).2; omega
        have hg1 : Nat.gcd (p1.1 * p1.2) M = p1.1 := by
          rw [hcopM1.symm.gcd_mul_right_cancel p1.1,
            Nat.gcd_eq_left (Nat.dvd_of_mem_divisors (mem_product.mp h1).1)]
        have hg2 : Nat.gcd (p2.1 * p2.2) M = p2.1 := by
          rw [hcopM2.symm.gcd_mul_right_cancel p2.1,
            Nat.gcd_eq_left (Nat.dvd_of_mem_divisors (mem_product.mp h2).1)]
        have hfst : p1.1 = p2.1 := by rw [← hg1, heq, hg2]
        have hp1_pos : 0 < p1.1 := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors (mem_product.mp h1).1) hM_pos
        have hsnd : p1.2 = p2.2 := Nat.eq_of_mul_eq_mul_left hp1_pos (by rwa [← hfst] at heq)
        exact Prod.ext hfst hsnd
      have hmaps : ∀ p ∈ M.divisors ×ˢ D1, p.1 * p.2 ∈ Dset := by
        intro p hp
        have hcop := hcop_pair p hp
        rw [mem_product] at hp
        have hd1 := Nat.dvd_of_mem_divisors hp.1
        have hp1_sqf : Squarefree p.1 := hM_sqf.squarefree_of_dvd hd1
        have hp2_m := mem_filter.mp hp.2
        have hle : p.1 * p.2 ≤ Q := by
          calc p.1 * p.2 ≤ M * (2 * 4 ^ K) :=
                Nat.mul_le_mul (Nat.le_of_dvd hM_pos hd1) (mem_Icc.mp hp2_m.1).2
            _ = 2 * 4 ^ K * M := by ring
            _ ≤ Q := h24KM_le_Q
        simp only [Dset, mem_filter, mem_Icc]
        refine ⟨⟨Nat.mul_pos (Nat.pos_of_dvd_of_pos hd1 hM_pos)
          (by have := (mem_Icc.mp hp2_m.1).1; omega), hle⟩,
          (Nat.squarefree_mul hcop).mpr ⟨hp1_sqf, hp2_m.2.1⟩, fun q hq => ?_⟩
        rw [Nat.primeFactors_mul hp1_sqf.ne_zero hp2_m.2.1.ne_zero, mem_union] at hq
        rcases hq with hq1 | hq2
        · left
          rw [← hM_pf]
          rw [Nat.mem_primeFactors] at hq1 ⊢
          exact ⟨hq1.1, hq1.2.1.trans hd1, by omega⟩
        · right
          exact hp2_m.2.2 q hq2
      have hmul_h : ∀ p ∈ M.divisors ×ˢ D1, h p.1 * h p.2 = h (p.1 * p.2) := by
        intro p hp
        have hcop := hcop_pair p hp
        rw [mem_product] at hp
        have hp10 : p.1 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hp.1) hM_pos)
        have hp20 : p.2 ≠ 0 := (mem_filter.mp hp.2).2.1.ne_zero
        simp only [h]
        rw [Nat.primeFactors_mul hp10 hp20, prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
      calc ∑ p ∈ M.divisors ×ˢ D1, h p.1 * h p.2
          = ∑ p ∈ M.divisors ×ˢ D1, h (p.1 * p.2) := sum_congr rfl hmul_h
        _ = ∑ d ∈ (M.divisors ×ˢ D1).image (fun p => p.1 * p.2), h d :=
            (Finset.sum_image (f := h) (fun p1 h1 p2 h2 heq => hinj p1 h1 p2 h2 heq)).symm
        _ ≤ ∑ d ∈ Dset, h d := by
            refine sum_le_sum_of_subset_of_nonneg ?_ (fun d hd _ => (h_pos d hd).le)
            intro d hd
            rw [mem_image] at hd
            obtain ⟨p, hp, rfl⟩ := hd
            exact hmaps p hp
    calc (∏ p ∈ P3, ((p : ℝ) / ((p : ℝ) - 1))) * (((K : ℝ) - 1) / 192)
        ≤ (∏ p ∈ P3, ((p : ℝ) / ((p : ℝ) - 1))) * (∑ d1 ∈ D1, h d1) := by
          refine mul_le_mul_of_nonneg_left hS1 ?_
          linarith
      _ = (∑ d3 ∈ M.divisors, h d3) * (∑ d1 ∈ D1, h d1) := by rw [hB_eq]
      _ ≤ ∑ d ∈ Dset, h d := hprod_le
  have hlog_le : Nat.log 2 n + 1 ≤ r + M + 1 := by
    have hn_lt : n < 2 ^ (r + M + 1) := by
      calc n = 2 ^ r * M := rfl
        _ < 2 ^ r * 2 ^ M := Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self) (Nat.pow_pos (by decide))
        _ = 2 ^ (r + M) := (pow_add 2 r M).symm
        _ < 2 ^ (r + M + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
    have := Nat.log_lt_of_lt_pow (by omega : n ≠ 0) hn_lt
    omega
  have hL_big : 20 * ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ ∑ d ∈ Dset, h d := by
    have h1 : (K : ℝ) - 1 ≥ (r : ℝ) / 12 - 2 := by
      have hdiv : 12 * K = r := by omega
      have : (12 : ℝ) * (K : ℝ) = (r : ℝ) := by exact_mod_cast hdiv
      linarith
    have h2 : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ (r : ℝ) + (M : ℝ) + 1 := by exact_mod_cast hlog_le
    have h3 : (M : ℝ) + 1 ≤ (r : ℝ) / 30 := by
      have : 30 * (M + 1) ≤ r := by omega
      have : (30 : ℝ) * ((M : ℝ) + 1) ≤ (r : ℝ) := by exact_mod_cast this
      linarith
    have hr_real : (60000 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
    have hK_nn : (0 : ℝ) ≤ (((K : ℝ) - 1) / 192) := by
      have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_ge2
      linarith
    have hB_mul : 200000 * (((K : ℝ) - 1) / 192) ≤
        (∏ p ∈ P3, ((p : ℝ) / ((p : ℝ) - 1))) * (((K : ℝ) - 1) / 192) :=
      mul_le_mul_of_nonneg_right hB.le hK_nn
    linarith
  have hsieve := selberg_sieve_upper P3 hP3 r Q (by omega) hQ_ge1 hQ_le_n
  have hcheb : (n : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * ((Nat.primeCounting n : ℝ) + 2) := by
    have heven : n = 2 * (2 ^ (r - 1) * M) := by
      have hr1 : r = (r - 1) + 1 := by omega
      conv_lhs => rw [show n = 2 ^ r * M from rfl, hr1, pow_succ']
      ring
    have hm1 : 1 ≤ 2 ^ (r - 1) * M := Nat.mul_pos (Nat.one_le_pow _ _ (by decide)) hM_pos
    have hc := chebyshev_primeCounting_lower (2 ^ (r - 1) * M) hm1
    rw [← heven] at hc
    exact_mod_cast hc
  have herr_small :
      (5 * (Q : ℝ) ^ 4 + 2) * ((Nat.log 2 n + 1 : ℕ) : ℝ) < (n : ℝ) / 2 := by
    have hnat : (5 * Q ^ 4 + 2) * (2 * (r + M + 1)) < n := by
      have hQ4 : Q ^ 4 = 2 ^ (4 * (r / 5)) := by rw [← pow_mul, mul_comm]
      have hle_sum : 5 * Q ^ 4 + 2 ≤ 8 * 2 ^ (4 * (r / 5)) := by
        rw [hQ4]
        have : 1 ≤ 2 ^ (4 * (r / 5)) := Nat.one_le_pow _ _ (by decide)
        omega
      have hlin_le : 2 * (r + M + 1) ≤ 2 ^ (r / 5 - 4) := by
        have h1 : 2 * (r + M + 1) ≤ (M + 1) * 2 ^ 18 := by omega
        have h2 : M + 1 ≤ 2 ^ (M + 1) := (Nat.lt_two_pow_self (n := M + 1)).le
        calc 2 * (r + M + 1)
            ≤ (M + 1) * 2 ^ 18 := h1
          _ ≤ 2 ^ (M + 1) * 2 ^ 18 := Nat.mul_le_mul_right _ h2
          _ = 2 ^ (M + 19) := (pow_add 2 _ _).symm
          _ ≤ 2 ^ (r / 5 - 4) := Nat.pow_le_pow_right (by decide) (by omega)
      calc (5 * Q ^ 4 + 2) * (2 * (r + M + 1))
          ≤ (8 * 2 ^ (4 * (r / 5))) * 2 ^ (r / 5 - 4) := Nat.mul_le_mul hle_sum hlin_le
        _ = 2 ^ (3 + 4 * (r / 5) + (r / 5 - 4)) := by
            rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
        _ < 2 ^ r := Nat.pow_lt_pow_right (by decide) (by omega)
        _ ≤ 2 ^ r * M := Nat.le_mul_of_pos_right _ hM_pos
    have hnat' : (5 * Q ^ 4 + 2) * (2 * (Nat.log 2 n + 1)) < n :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hlog_le)) hnat
    have hreal : ((5 * (Q : ℝ) ^ 4 + 2) * (2 * ((Nat.log 2 n + 1 : ℕ) : ℝ))) < (n : ℝ) := by
      exact_mod_cast hnat'
    linarith
  refine ⟨n, hn_gt1, ?_⟩
  have hlog_pos : (0 : ℝ) < ((Nat.log 2 n + 1 : ℕ) : ℝ) := by positivity
  have hL_pos : 0 < ∑ d ∈ Dset, h d := by linarith
  have h5a : (5 * OeisA69004.a n : ℝ) < (Nat.primeCounting n : ℝ) := by
    have hmain_bound : 5 * ((n : ℝ) / (∑ d ∈ Dset, h d)) ≤
        (n : ℝ) / (4 * ((Nat.log 2 n + 1 : ℕ) : ℝ)) := by
      rw [mul_div_assoc', div_le_div_iff₀ hL_pos (by positivity)]
      calc 5 * (n : ℝ) * (4 * ((Nat.log 2 n + 1 : ℕ) : ℝ))
          = (n : ℝ) * (20 * ((Nat.log 2 n + 1 : ℕ) : ℝ)) := by ring
        _ ≤ (n : ℝ) * ∑ d ∈ Dset, h d := mul_le_mul_of_nonneg_left hL_big (Nat.cast_nonneg n)
    have hcheb_div : (n : ℝ) / ((Nat.log 2 n + 1 : ℕ) : ℝ) - 2 ≤ (Nat.primeCounting n : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hlog_pos]
      linarith
    have herr_div : 5 * (Q : ℝ) ^ 4 + 2 < (n : ℝ) / (2 * ((Nat.log 2 n + 1 : ℕ) : ℝ)) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have h1 : (5 * OeisA69004.a n : ℝ) ≤ 5 * ((n : ℝ) / (∑ d ∈ Dset, h d)) + 5 * (Q : ℝ) ^ 4 := by
      linarith
    have hn_pos_r : (0 : ℝ) < (n : ℝ) / ((Nat.log 2 n + 1 : ℕ) : ℝ) := by positivity
    have h4 : (n : ℝ) / (4 * ((Nat.log 2 n + 1 : ℕ) : ℝ)) +
        (n : ℝ) / (2 * ((Nat.log 2 n + 1 : ℕ) : ℝ)) <
        (n : ℝ) / ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
      have : (n : ℝ) / (4 * ((Nat.log 2 n + 1 : ℕ) : ℝ)) =
          (1 / 4) * ((n : ℝ) / ((Nat.log 2 n + 1 : ℕ) : ℝ)) := by ring
      have : (n : ℝ) / (2 * ((Nat.log 2 n + 1 : ℕ) : ℝ)) =
          (1 / 2) * ((n : ℝ) / ((Nat.log 2 n + 1 : ℕ) : ℝ)) := by ring
      linarith
    linarith
  exact_mod_cast h5a

end OeisA69004Disproof

theorem OMA.disproof : ¬ (type_of% @OeisA69004.conjecture2.variants.without_upper_bound) := by
  rintro ⟨hforall, _⟩
  obtain ⟨n, hn, hlt⟩ := OeisA69004Disproof.exists_counterexample
  exact absurd (hforall n hn) (not_le_of_gt hlt)
