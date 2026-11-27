import FormalConjectures.ErdosProblems.«675»
import Mathlib.NumberTheory.Chebyshev

/-!
# Proof of Erdős Problem 675 (Brun's Sieve Variant)

We prove `Erdos675.erdos_675.variants.brun`: if `B ⊆ ℕ` is a set of pairwise coprime integers
satisfying `∑_{b ∈ B, b < x} 1 / b = o(log log x)`, then `A = {n : ∀ b ∈ B, ¬ b ∣ n}` has the
translation property.

The proof combines:
1. A maximizer lemma on `g(v) = ∑_{b ∈ B', b < ⌊exp(exp v)⌋} 1/b = o(v)` producing arbitrarily
   large scales `K = ⌊exp(exp u)⌋ - 1` where `f(K+1) - f(a) ≤ ε (log(log K / log a) + 2)` holds
   uniformly for all `16 ≤ a ≤ K`.
2. An injection `b ↦ b.minFac` from `B' ∩ [2, X]` into primes `≤ X`, giving `#(B' ∩ [2, X]) ≤ π(X)`
   and Abel summation bounds on `∑_{a < b ≤ c, b ∈ B'} 1/b`.
3. A self-contained Rosser-Iwaniec β-sieve (`β = 2`) with CRT counting on arithmetic progressions,
   yielding both lower and upper bounds on `k ∈ [1, K]` avoiding `B' ∩ (y, z]`.
4. Combining the lower bound for `B' ∩ (y, z]` with β-sieve upper bounds on `(z, K / exp(√(log K))]`
   (split into `(z, K^{1/2}]`, `(K^{1/2}, K^{1 - 2^{-J₀}}]`, and dyadic shells `j > J₀`) and
   elementary prime-counting bounds on `(K / exp(√(log K)), n + K * M]`.
-/

open scoped Classical
open Filter Asymptotics Finset Real

namespace Erdos675Proof

/- ---------------------------------------------------------------------------
   Part 1: Pairwise coprime counting via Chebyshev + Abel summation + Maximizer
   --------------------------------------------------------------------------- -/

/-- Any finite set of pairwise coprime integers `≥ 2` in `[2, X]` has cardinality at most `π(X)`,
via the injection `b ↦ b.minFac`. -/
private lemma card_coprime_le_primeCounting (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (_hge2 : ∀ b ∈ B', 2 ≤ b) (X : ℕ) :
    ((Finset.Icc 2 X).filter (· ∈ B')).card ≤ Nat.primeCounting X := by
  have hpi : Nat.primeCounting X = ((Finset.Icc 2 X).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    congr 1; ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · intro ⟨h1, hp⟩; exact ⟨⟨hp.two_le, Nat.lt_succ_iff.mp h1⟩, hp⟩
    · intro ⟨⟨_, h2⟩, hp⟩; exact ⟨Nat.lt_succ_of_le h2, hp⟩
  rw [hpi]
  refine Finset.card_le_card_of_injOn Nat.minFac ?_ ?_
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hb ⊢
    have hb1 : b ≠ 1 := by omega
    have hpr : b.minFac.Prime := Nat.minFac_prime hb1
    exact ⟨⟨hpr.two_le, (Nat.minFac_le (by omega)).trans hb.1.2⟩, hpr⟩
  · intro b₁ hb₁ b₂ hb₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hb₁ hb₂
    by_contra hne
    have hcop := hB' hb₁.2 hb₂.2 hne
    have hpr : b₁.minFac.Prime := Nat.minFac_prime (by omega)
    have hdvd1 : b₁.minFac ∣ b₁ := Nat.minFac_dvd b₁
    have hdvd2 : b₁.minFac ∣ b₂ := heq ▸ Nat.minFac_dvd b₂
    have hdvdg : b₁.minFac ∣ b₁.gcd b₂ := Nat.dvd_gcd hdvd1 hdvd2
    rw [hcop.gcd_eq_one] at hdvdg
    exact hpr.not_dvd_one hdvdg

/-- Chebyshev upper bound: eventually `π(x) ≤ 2 * x / log x`. -/
private lemma eventually_primeCounting_le_two :
    ∀ᶠ x : ℕ in atTop, (Nat.primeCounting x : ℝ) ≤ 2 * (x : ℝ) / Real.log (x : ℝ) := by
  have hε : (0 : ℝ) < 2 - Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith [Real.log_two_lt_d9]
  have hcheb := Chebyshev.eventually_primeCounting_le hε
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hcheb] with x hx
  simpa [Nat.floor_natCast, add_sub_cancel] using hx

/-- Elementary integral bound: for `2 ≤ a ≤ b`, `∑ k ∈ Ioc a b, 1 / (k * log k) ≤ log (log b / log a) + 1 / (a * log a)`. -/
private lemma sum_inv_mul_log_le (a b : ℕ) (ha : 3 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) ≤
      Real.log (Real.log (b : ℝ) / Real.log (a : ℝ)) + 1 / ((a : ℝ) * Real.log (a : ℝ)) := by
  -- Use telescoping with `log (log k)`: for `k ≥ 3`, `1 / (k * log k) ≤ log (log k) - log (log (k - 1))`
  have hstep : ∀ k : ℕ, 3 ≤ k →
      (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) ≤
        Real.log (Real.log (k : ℝ)) - Real.log (Real.log ((k - 1 : ℕ) : ℝ)) := by
    intro k hk
    have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk1R : (2 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      have : 2 ≤ k - 1 := by omega
      exact_mod_cast this
    have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
    have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hlogkm1_pos : 0 < Real.log ((k - 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
    -- Step A: log k - log (k - 1) = -log(1 - 1/k) ≥ 1/k
    have hlog_diff : (1 : ℝ) / (k : ℝ) ≤ Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ) := by
      have h1 : Real.log ((k - 1 : ℕ) : ℝ) - Real.log (k : ℝ) =
          Real.log (((k - 1 : ℕ) : ℝ) / (k : ℝ)) :=
        (Real.log_div (by linarith) (by linarith)).symm
      have h2 : Real.log (((k - 1 : ℕ) : ℝ) / (k : ℝ)) ≤ ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h3 : ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
        rw [hkm1]; field_simp; ring
      linarith
    -- Step B: log (log k) - log (log (k - 1)) ≥ (log k - log (k - 1)) / log k ≥ 1 / (k * log k)
    have hll_diff : (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) / Real.log (k : ℝ) ≤
        Real.log (Real.log (k : ℝ)) - Real.log (Real.log ((k - 1 : ℕ) : ℝ)) := by
      have h1 : Real.log (Real.log ((k - 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)) =
          Real.log (Real.log ((k - 1 : ℕ) : ℝ) / Real.log (k : ℝ)) :=
        (Real.log_div hlogkm1_pos.ne' hlogk_pos.ne').symm
      have h2 : Real.log (Real.log ((k - 1 : ℕ) : ℝ) / Real.log (k : ℝ)) ≤
          Real.log ((k - 1 : ℕ) : ℝ) / Real.log (k : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hlogkm1_pos hlogk_pos)
      have h3 : Real.log ((k - 1 : ℕ) : ℝ) / Real.log (k : ℝ) - 1 =
          -(Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) / Real.log (k : ℝ) := by
        field_simp [hlogk_pos.ne']; ring
      rw [neg_div] at h3; linarith
    have hdiv : (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) ≤
        (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) / Real.log (k : ℝ) := by
      rw [show (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) = (1 / (k : ℝ)) / Real.log (k : ℝ) by ring]
      exact div_le_div_of_nonneg_right hlog_diff hlogk_pos.le
    exact hdiv.trans hll_diff
  have htel : ∑ k ∈ Finset.Ioc a b,
      (Real.log (Real.log (k : ℝ)) - Real.log (Real.log ((k - 1 : ℕ) : ℝ))) =
      Real.log (Real.log (b : ℝ)) - Real.log (Real.log (a : ℝ)) := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ioc_succ_top hm, ih]
      simp only [Nat.add_sub_cancel]
      ring
  have hsum_le : ∑ k ∈ Finset.Ioc a b, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) ≤
      Real.log (Real.log (b : ℝ)) - Real.log (Real.log (a : ℝ)) := by
    rw [← htel]
    refine Finset.sum_le_sum fun k hk => hstep k (by have := (Finset.mem_Ioc.mp hk).1; omega)
  have hloga_pos : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < a))
  have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  rw [Real.log_div hlogb_pos.ne' hloga_pos.ne']
  linarith [show (0 : ℝ) ≤ 1 / ((a : ℝ) * Real.log (a : ℝ)) by positivity]

/-- Abel summation bound for pairwise coprime sets: if `π(k) ≤ 2 k / log k` for all `k ≥ a`,
then `∑_{a < b ≤ c, b ∈ B'} 1/b ≤ 2 / log c + 4 * log (log c / log a) + 4 / (a * log a)`. -/
private lemma sum_inv_coprime_Ioc_le (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (a c : ℕ) (ha : 3 ≤ a) (hac : a ≤ c)
    (hpi : ∀ k : ℕ, a ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ)) :
    ∑ b ∈ (Finset.Ioc a c).filter (· ∈ B'), (1 : ℝ) / (b : ℝ) ≤
      2 / Real.log (c : ℝ) + 4 * Real.log (Real.log (c : ℝ) / Real.log (a : ℝ)) +
        8 / ((a : ℝ) * Real.log (a : ℝ)) := by
  let S : ℕ → ℝ := fun k => (((Finset.Icc 2 k).filter (· ∈ B')).card : ℝ)
  have hS_le : ∀ k : ℕ, a ≤ k → S k ≤ 2 * (k : ℝ) / Real.log (k : ℝ) := by
    intro k hk
    exact (Nat.cast_le.mpr (card_coprime_le_primeCounting B' hB' hge2 k)).trans (hpi k hk)
  -- Express ∑_{a < b ≤ c, b ∈ B'} 1/b as ∑_{k ∈ Ioc a c} (S k - S (k - 1)) / k
  have hdiff : ∀ k : ℕ, 2 ≤ k →
      S k - S (k - 1) = if k ∈ B' then 1 else 0 := by
    intro k hk
    dsimp only [S]
    have hIcc : Finset.Icc 2 k = insert k (Finset.Icc 2 (k - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : k ∉ Finset.Icc 2 (k - 1) := by simp; omega
    rw [hIcc, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp [hnotmem]), Nat.cast_add, Nat.cast_one]; ring
    · ring
  -- Summation by parts on Ioc a c
  have hparts : ∑ k ∈ Finset.Ioc a c, (S k - S (k - 1)) / (k : ℝ) =
      S c / (c : ℝ) - S a / (a : ℝ) +
        ∑ k ∈ Finset.Ico a c, S k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    induction c, hac using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ioc_succ_top hm, ih, Finset.sum_Ico_succ_top hm]
      simp only [Nat.add_sub_cancel]
      ring
  have hsum_eq : ∑ b ∈ (Finset.Ioc a c).filter (· ∈ B'), (1 : ℝ) / (b : ℝ) =
      ∑ k ∈ Finset.Ioc a c, (S k - S (k - 1)) / (k : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hdiff k (by have := (Finset.mem_Ioc.mp hk).1; omega)]
    split_ifs <;> simp
  rw [hsum_eq, hparts]
  have hSa_nn : 0 ≤ S a / (a : ℝ) := by dsimp only [S]; positivity
  have hSc : S c / (c : ℝ) ≤ 2 / Real.log (c : ℝ) := by
    have hc_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
    calc S c / (c : ℝ) ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) / (c : ℝ) :=
          div_le_div_of_nonneg_right (hS_le c hac) hc_pos.le
      _ = 2 / Real.log (c : ℝ) := by field_simp [hc_pos.ne']
  have hmid : ∑ k ∈ Finset.Ico a c, S k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤
      4 * (1 / ((a : ℝ) * Real.log (a : ℝ)) +
        ∑ k ∈ Finset.Ioc a c, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ))) := by
    calc
      ∑ k ∈ Finset.Ico a c, S k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.Ico a c, 4 * ((1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk_ico := Finset.mem_Ico.mp hk
          have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 3 ≤ k)
          have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
          have hdiff_k : 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
            push_cast; field_simp; ring
          rw [hdiff_k]
          have hSk := hS_le k hk_ico.1
          calc S k * (1 / ((k : ℝ) * ((k : ℝ) + 1)))
              ≤ (2 * (k : ℝ) / Real.log (k : ℝ)) * (1 / ((k : ℝ) * ((k : ℝ) + 1))) :=
                mul_le_mul_of_nonneg_right hSk (by positivity)
            _ = 2 / (((k : ℝ) + 1) * Real.log (k : ℝ)) := by field_simp
            _ ≤ 4 * (1 / ((k : ℝ) * Real.log (k : ℝ))) := by
                rw [show 4 * (1 / ((k : ℝ) * Real.log (k : ℝ))) = 4 / ((k : ℝ) * Real.log (k : ℝ)) by ring]
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith
      _ = 4 * ∑ k ∈ Finset.Ico a c, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ 4 * (1 / ((a : ℝ) * Real.log (a : ℝ)) +
            ∑ k ∈ Finset.Ioc a c, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          have hsub : Finset.Ico a c ⊆ insert a (Finset.Ioc a c) := by
            intro k hk; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioc] at hk ⊢; omega
          calc ∑ k ∈ Finset.Ico a c, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ))
              ≤ ∑ k ∈ insert a (Finset.Ioc a c), (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => by
                  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by
                    simp only [Finset.mem_insert, Finset.mem_Ioc] at hk
                    exact_mod_cast (by omega : 3 ≤ k)
                  have : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
                  positivity
            _ = 1 / ((a : ℝ) * Real.log (a : ℝ)) +
                  ∑ k ∈ Finset.Ioc a c, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) :=
                Finset.sum_insert (by simp)
  have hint := sum_inv_mul_log_le a c ha hac
  rw [show 8 / ((a : ℝ) * Real.log (a : ℝ)) =
      4 * (1 / ((a : ℝ) * Real.log (a : ℝ)) + 1 / ((a : ℝ) * Real.log (a : ℝ))) by ring]
  linarith

/-- Maximizer lemma: if `f(x) = ∑_{b ∈ B', b < x} 1/b = o(log log x)`, then for any `ε > 0` and
`U₀ : ℕ`, there exists `u ≥ U₀` such that for `K = ⌊exp(exp u)⌋₊ - 1`, every `16 ≤ a ≤ K`
satisfies `f(K + 1) - f(a) ≤ ε * (log(log K / log a) + 2)`. -/
private lemma exists_good_K (B' : Set ℕ)
    (hsum : (fun x : ℕ => ∑ b ∈ (Finset.range x).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) =o[atTop]
      fun x : ℕ => Real.log (Real.log (x : ℝ)))
    (ε : ℝ) (hε : 0 < ε) (U₀ : ℕ) :
    ∃ u : ℕ, U₀ ≤ u ∧
      let K := ⌊Real.exp (Real.exp (u : ℝ))⌋₊ - 1
      ∀ a : ℕ, 16 ≤ a → a ≤ K →
        (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) -
        (∑ b ∈ (Finset.range a).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) ≤
          ε * (Real.log (Real.log (K : ℝ) / Real.log (a : ℝ)) + 2) := by
  let f : ℕ → ℝ := fun x => ∑ b ∈ (Finset.range x).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)
  let g : ℕ → ℝ := fun v => f ⌊Real.exp (Real.exp (v : ℝ))⌋₊
  have hf_mono : Monotone f := by
    intro x y hxy
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ (Finset.range_mono hxy)) (fun _ _ _ => by positivity)
  have hf_nn : ∀ x, 0 ≤ f x := fun x => Finset.sum_nonneg fun _ _ => by positivity
  -- g(v) ≤ (ε / 4) * v for sufficiently large v
  have hg_small : ∀ᶠ v : ℕ in atTop, g v ≤ (ε / 4) * (v : ℝ) := by
    have hbound := hsum.bound (show (0 : ℝ) < ε / 8 by positivity)
    have hfl_atTop : Tendsto (fun v : ℕ => ⌊Real.exp (Real.exp (v : ℝ))⌋₊) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      obtain ⟨v₀, hv₀⟩ := (Real.tendsto_exp_atTop.comp
        (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop (b : ℝ) |>.exists_forall_of_atTop
      exact ⟨v₀, fun v hv => Nat.le_floor (hv₀ v hv)⟩
    filter_upwards [hfl_atTop.eventually hbound, eventually_ge_atTop 4] with v hv hv4
    have hpos_fl : (16 : ℝ) ≤ (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ) := by
      have hvR : (4 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv4
      have he4 : (5 : ℝ) ≤ Real.exp (v : ℝ) := by linarith [Real.add_one_le_exp (v : ℝ)]
      have hee : (17 : ℝ) ≤ Real.exp (Real.exp (v : ℝ)) := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h5 : Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
        have h25 : (17 : ℝ) ≤ Real.exp 5 := by
          rw [h5]
          calc (17 : ℝ) ≤ 2 ^ 5 := by norm_num
            _ ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) h1 5
        exact h25.trans (Real.exp_le_exp.mpr he4)
      have := Nat.sub_one_lt_floor (Real.exp (Real.exp (v : ℝ)))
      linarith
    have hfl_le : (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ) ≤ Real.exp (Real.exp (v : ℝ)) :=
      Nat.floor_le (by positivity)
    have hll_pos : 0 < Real.log (Real.log (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ)) := by
      have hlog16 : 1 < Real.log (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ) := by
        have : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
        exact (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
      exact Real.log_pos hlog16
    have hll_le : Real.log (Real.log (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ)) ≤ (v : ℝ) := by
      have h1 : Real.log (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ) ≤ Real.exp (v : ℝ) := by
        calc Real.log (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ)
            ≤ Real.log (Real.exp (Real.exp (v : ℝ))) := Real.log_le_log (by linarith) hfl_le
          _ = Real.exp (v : ℝ) := Real.log_exp _
      have h2 := Real.log_le_log (Real.log_pos (by linarith : (1 : ℝ) < (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ))) h1
      rwa [Real.log_exp] at h2
    rw [Real.norm_of_nonneg (hf_nn _), Real.norm_of_nonneg hll_pos.le] at hv
    calc g v ≤ (ε / 8) * Real.log (Real.log (⌊Real.exp (Real.exp (v : ℝ))⌋₊ : ℝ)) := hv
      _ ≤ (ε / 8) * (v : ℝ) := mul_le_mul_of_nonneg_left hll_le (by positivity)
      _ ≤ (ε / 4) * (v : ℝ) := by nlinarith [show (0 : ℝ) ≤ (v : ℝ) by positivity]
  obtain ⟨U, hU_ge, hU_small⟩ := (hg_small.and (eventually_ge_atTop (max (2 * U₀ + 4) 20))).exists
  -- Pick u ∈ Icc 0 U maximizing ε * v - g v
  obtain ⟨u, hu_mem, hu_max⟩ :=
    Finset.exists_max_image (Finset.Icc 0 U) (fun v => ε * (v : ℝ) - g v)
      (Finset.nonempty_Icc.mpr (Nat.zero_le U))
  have hu_gt : U / 2 < u := by
    by_contra hle
    push Not at hle
    have hU_val : (3 * ε / 4) * (U : ℝ) ≤ ε * (U : ℝ) - g U := by linarith
    have hu_val : ε * (u : ℝ) - g u ≤ (ε / 2) * (U : ℝ) := by
      have huR : (u : ℝ) ≤ (U : ℝ) / 2 := by
        have : 2 * u ≤ U := by omega
        have : (2 : ℝ) * (u : ℝ) ≤ (U : ℝ) := by exact_mod_cast this
        linarith
      have hgnn : 0 ≤ g u := hf_nn _
      nlinarith
    have hcomp := hu_max U (Finset.mem_Icc.mpr ⟨Nat.zero_le U, le_rfl⟩)
    have hUpos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
    nlinarith
  have hu_ge_U0 : U₀ ≤ u := by omega
  have hu_ge10 : 10 ≤ u := by omega
  refine ⟨u, hu_ge_U0, ?_⟩
  intro K a ha16 haK
  have hfl_ge : 16 ≤ ⌊Real.exp (Real.exp (u : ℝ))⌋₊ := by
    have huR : (10 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu_ge10
    have he10 : (11 : ℝ) ≤ Real.exp (u : ℝ) := by linarith [Real.add_one_le_exp (u : ℝ)]
    have hee : (16 : ℝ) ≤ Real.exp (Real.exp (u : ℝ)) := by
      have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h4 : (16 : ℝ) ≤ Real.exp 4 := by
        rw [show Real.exp 4 = (Real.exp 1) ^ 4 by rw [← Real.exp_nat_mul]; norm_num]
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
      exact h4.trans (Real.exp_le_exp.mpr (by linarith))
    exact Nat.le_floor hee
  have hK1 : K + 1 = ⌊Real.exp (Real.exp (u : ℝ))⌋₊ := by dsimp only [K]; omega
  -- Let v = ⌊log (log a)⌋₊
  have hloga_gt1 : 1 < Real.log (a : ℝ) := by
    have haR : (16 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha16
    have : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
  have hlla_pos : 0 < Real.log (Real.log (a : ℝ)) := Real.log_pos hloga_gt1
  let v : ℕ := ⌊Real.log (Real.log (a : ℝ))⌋₊
  have hv_le_u : v ≤ u := by
    have ha_le_exp : (a : ℝ) ≤ Real.exp (Real.exp (u : ℝ)) := by
      have h1 : (a : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : a ≤ K + 1)
      rw [hK1] at h1
      exact h1.trans (Nat.floor_le (by positivity))
    have h1 : Real.log (a : ℝ) ≤ Real.exp (u : ℝ) := by
      calc Real.log (a : ℝ) ≤ Real.log (Real.exp (Real.exp (u : ℝ))) :=
            Real.log_le_log (by positivity) ha_le_exp
        _ = Real.exp (u : ℝ) := Real.log_exp _
    have h2 : Real.log (Real.log (a : ℝ)) ≤ (u : ℝ) := by
      calc Real.log (Real.log (a : ℝ)) ≤ Real.log (Real.exp (u : ℝ)) :=
            Real.log_le_log (by linarith) h1
        _ = (u : ℝ) := Real.log_exp _
    exact Nat.floor_le_of_le h2
  have hflv_le_a : ⌊Real.exp (Real.exp (v : ℝ))⌋₊ ≤ a := by
    have hv_le : (v : ℝ) ≤ Real.log (Real.log (a : ℝ)) := Nat.floor_le hlla_pos.le
    have h1 : Real.exp (v : ℝ) ≤ Real.log (a : ℝ) := by
      calc Real.exp (v : ℝ) ≤ Real.exp (Real.log (Real.log (a : ℝ))) := Real.exp_le_exp.mpr hv_le
        _ = Real.log (a : ℝ) := Real.exp_log (by linarith)
    have h2 : Real.exp (Real.exp (v : ℝ)) ≤ (a : ℝ) := by
      calc Real.exp (Real.exp (v : ℝ)) ≤ Real.exp (Real.log (a : ℝ)) := Real.exp_le_exp.mpr h1
        _ = (a : ℝ) := Real.exp_log (by positivity)
    exact Nat.floor_le_of_le h2
  have hgu_sub : g u - g v ≤ ε * ((u : ℝ) - (v : ℝ)) := by
    have hv_mem : v ∈ Finset.Icc 0 U := Finset.mem_Icc.mpr ⟨Nat.zero_le _, hv_le_u.trans (Finset.mem_Icc.mp hu_mem).2⟩
    have := hu_max v hv_mem
    linarith
  have hfa_ge : g v ≤ f a := hf_mono hflv_le_a
  have hfu_eq : f (K + 1) = g u := by dsimp only [g]; rw [hK1]
  -- Relate u - v to log(log K / log a) + 2
  have hu_le_llK : (u : ℝ) ≤ Real.log (Real.log (K : ℝ)) + 1 := by
    have hK_ge : Real.exp (Real.exp (u : ℝ)) / 2 ≤ (K : ℝ) := by
      have hfl := Nat.sub_one_lt_floor (Real.exp (Real.exp (u : ℝ)))
      have hee : (16 : ℝ) ≤ Real.exp (Real.exp (u : ℝ)) := by
        have h1 : (16 : ℝ) ≤ (⌊Real.exp (Real.exp (u : ℝ))⌋₊ : ℝ) := by exact_mod_cast hfl_ge
        exact h1.trans (Nat.floor_le (by positivity))
      have hK_R : (K : ℝ) = (⌊Real.exp (Real.exp (u : ℝ))⌋₊ : ℝ) - 1 := by
        dsimp only [K]; rw [Nat.cast_sub (by omega : 1 ≤ ⌊Real.exp (Real.exp (u : ℝ))⌋₊)]; simp
      linarith
    have hlogK_ge : Real.exp (u : ℝ) / 2 ≤ Real.log (K : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hK_ge
      rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
      have heu : (10 : ℝ) ≤ Real.exp (u : ℝ) := by
        have huR : (10 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu_ge10
        linarith [Real.add_one_le_exp (u : ℝ)]
      have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hllK := Real.log_le_log (by positivity) hlogK_ge
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at hllK
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hv_ge : Real.log (Real.log (a : ℝ)) - 1 < (v : ℝ) := Nat.sub_one_lt_floor _
  have hlogK_pos : 0 < Real.log (K : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < K))
  have hdiff_uv : (u : ℝ) - (v : ℝ) ≤ Real.log (Real.log (K : ℝ) / Real.log (a : ℝ)) + 2 := by
    rw [Real.log_div hlogK_pos.ne' (by linarith)]
    linarith
  change f (K + 1) - f a ≤ ε * (Real.log (Real.log (K : ℝ) / Real.log (a : ℝ)) + 2)
  rw [hfu_eq]
  calc g u - f a ≤ g u - g v := by linarith
    _ ≤ ε * ((u : ℝ) - (v : ℝ)) := hgu_sub
    _ ≤ ε * (Real.log (Real.log (K : ℝ) / Real.log (a : ℝ)) + 2) :=
        mul_le_mul_of_nonneg_left hdiff_uv hε.le

/- ---------------------------------------------------------------------------
   Part 2: CRT Counting on Arithmetic Progressions
   --------------------------------------------------------------------------- -/

/-- Exact count of `t ∈ range N` with `t ≡ r [MOD d]` lies in `[N/d - 1, N/d + 1]`. -/
private lemma abs_card_modEq_sub_le (N d r : ℕ) (hd : 0 < d) :
    |(((Finset.range N).filter (fun t => t ≡ r [MOD d])).card : ℝ) - (N : ℝ) / (d : ℝ)| ≤ 1 := by
  let S := (Finset.range N).filter (fun t => t ≡ r [MOD d])
  have hmod : ∀ t ∈ S, t % d = r % d := fun t ht => (Finset.mem_filter.mp ht).2
  have hle : S.card ≤ N / d + 1 := by
    have hinj : S.card ≤ (Finset.range (N / d + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun t => t / d) ?_ ?_
      · intro t ht
        have htN : t < N := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right htN.le)))
      · intro t₁ ht₁ t₂ ht₂ heq
        dsimp only at heq
        have h1 := Nat.div_add_mod t₁ d
        have h2 := Nat.div_add_mod t₂ d
        rw [hmod t₁ ht₁, ← hmod t₂ ht₂, heq] at h1
        linarith
    simpa using hinj
  have hge : N / d ≤ S.card := by
    have hinj : (Finset.range (N / d)).card ≤ S.card := by
      refine Finset.card_le_card_of_injOn (fun q => q * d + r % d) ?_ ?_
      · intro q hq
        have hq_lt : q < N / d := Finset.mem_range.mp hq
        have hq1 : q + 1 ≤ N / d := hq_lt
        have hltN : q * d + r % d < N := by
          have h1 : (q + 1) * d ≤ (N / d) * d := Nat.mul_le_mul_right d hq1
          have h2 : (N / d) * d ≤ N := Nat.div_mul_le_self N d
          have h3 : r % d < d := Nat.mod_lt r hd
          nlinarith
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hltN, ?_⟩)
        simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod_left]
      · intro q₁ _ q₂ _ heq
        dsimp only at heq
        have h1 : q₁ * d = q₂ * d := by omega
        exact Nat.eq_of_mul_eq_mul_right hd h1
    simpa using hinj
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdiv_le : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]; exact_mod_cast Nat.div_mul_le_self N d
  have hdiv_ge : (N : ℝ) / (d : ℝ) - 1 < ((N / d : ℕ) : ℝ) := by
    have hlt : N < (N / d + 1) * d := by
      have := Nat.div_add_mod N d
      have := Nat.mod_lt N hd
      nlinarith
    have hltR : (N : ℝ) < ((N / d : ℕ) + 1 : ℝ) * (d : ℝ) := by exact_mod_cast hlt
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hdR]; linarith
  have hcard_ge : ((N / d : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hge
  have hcard_le : (S.card : ℝ) ≤ ((N / d : ℕ) : ℝ) + 1 := by exact_mod_cast hle
  rw [abs_le]
  constructor <;> linarith

/-- CRT for a finite set of pairwise coprime moduli: there exists `r` such that
`∀ b ∈ T, t ≡ a b [MOD b] ↔ t ≡ r [MOD ∏ b ∈ T, b]`. -/
private lemma crt_finset_coprime (T : Finset ℕ) (hcop : (T : Set ℕ).Pairwise Nat.Coprime)
    (a : ℕ → ℕ) :
    ∃ r : ℕ, ∀ t : ℕ, (∀ b ∈ T, t ≡ a b [MOD b]) ↔ t ≡ r [MOD ∏ b ∈ T, b] := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, fun t => ?_⟩
    simp [Nat.ModEq, Nat.mod_one]
  | @insert b T hb ih =>
    have hcop_T : (T : Set ℕ).Pairwise Nat.Coprime :=
      hcop.mono (by intro x hx; exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx))
    obtain ⟨r₀, hr₀⟩ := ih hcop_T
    have hcop_b : Nat.Coprime b (∏ c ∈ T, c) :=
      Nat.Coprime.prod_right fun c hc =>
        hcop (Finset.mem_coe.mpr (Finset.mem_insert_self b T))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hc)) (fun h => hb (h ▸ hc))
    let cr := Nat.chineseRemainder hcop_b (a b) r₀
    refine ⟨cr.val, fun t => ?_⟩
    rw [Finset.prod_insert hb]
    constructor
    · intro hall
      have h1 : t ≡ cr.val [MOD b] :=
        (hall b (Finset.mem_insert_self b T)).trans cr.property.1.symm
      have h2 : t ≡ cr.val [MOD ∏ c ∈ T, c] :=
        ((hr₀ t).mp (fun c hc => hall c (Finset.mem_insert_of_mem hc))).trans cr.property.2.symm
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_b).mp ⟨h1, h2⟩
    · intro hmod
      have ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hcop_b).mpr hmod
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hcT
      · exact h1.trans cr.property.1
      · exact (hr₀ t).mpr (h2.trans cr.property.2) c hcT

/-- For a single modulus `b > 0` coprime to `s`, `b ∣ u + t * s` is equivalent to a unique
congruence `t ≡ r [MOD b]`. -/
private lemma dvd_linear_iff_modEq (b u s : ℕ) (hb : 0 < b) (hcop : Nat.Coprime b s) :
    ∃ r : ℕ, ∀ t : ℕ, b ∣ u + t * s ↔ t ≡ r [MOD b] := by
  have hunit : IsUnit (s : ZMod b) := (ZMod.isUnit_iff_coprime s b).mpr hcop.symm
  have : NeZero b := ⟨hb.ne'⟩
  let r : ℕ := (-(u : ZMod b) * ((hunit.unit⁻¹ : (ZMod b)ˣ) : ZMod b)).val
  refine ⟨r, fun t => ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  have hr_cast : (r : ZMod b) = -(u : ZMod b) * ((hunit.unit⁻¹ : (ZMod b)ˣ) : ZMod b) :=
    ZMod.natCast_zmod_val _
  have hcancel1 : ((hunit.unit⁻¹ : (ZMod b)ˣ) : ZMod b) * (s : ZMod b) = 1 := hunit.unit.inv_mul
  have hcancel2 : (s : ZMod b) * ((hunit.unit⁻¹ : (ZMod b)ˣ) : ZMod b) = 1 := hunit.unit.mul_inv
  constructor
  · intro h
    have h1 : (t : ZMod b) * (s : ZMod b) = -(u : ZMod b) := eq_neg_of_add_eq_zero_right h
    have h2 := congrArg (fun x : ZMod b => x * ((hunit.unit⁻¹ : (ZMod b)ˣ) : ZMod b)) h1
    rw [mul_assoc, hcancel2, mul_one] at h2
    rw [hr_cast, h2]
  · intro h
    rw [h, hr_cast, mul_assoc, hcancel1, mul_one, add_neg_cancel]

/-- Counting `t ∈ range N` such that every `b ∈ T` divides `a + (k₀ + t * d₀) * M` for some
`a ∈ A_n` (`A_n ⊆ Icc 1 n`, every `b ∈ T` satisfies `2 * n < b` and `Nat.Coprime b (d₀ * M)`). -/
private lemma abs_card_hit_all_sub_le (N n k₀ d₀ M : ℕ) (A_n T : Finset ℕ)
    (hAn : A_n ⊆ Finset.Icc 1 n)
    (hT_cop : (T : Set ℕ).Pairwise Nat.Coprime)
    (hT_gt : ∀ b ∈ T, 2 * n < b)
    (hT_cop_s : ∀ b ∈ T, Nat.Coprime b (d₀ * M)) :
    |(((Finset.range N).filter (fun t =>
          ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) -
        (N : ℝ) * ((A_n.card : ℝ) ^ T.card / (∏ b ∈ T, (b : ℝ)))| ≤
      (A_n.card : ℝ) ^ T.card := by
  let S_all := (Finset.range N).filter (fun t =>
    ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)
  -- Uniqueness of `a ∈ A_n` for each `b ∈ T` and `t`
  have huniq : ∀ b ∈ T, ∀ t : ℕ, ∀ a₁ ∈ A_n, ∀ a₂ ∈ A_n,
      b ∣ a₁ + (k₀ + t * d₀) * M → b ∣ a₂ + (k₀ + t * d₀) * M → a₁ = a₂ := by
    intro b hb t a₁ ha₁ a₂ ha₂ h1 h2
    have ha1_icc := Finset.mem_Icc.mp (hAn ha₁)
    have ha2_icc := Finset.mem_Icc.mp (hAn ha₂)
    have hb_gt := hT_gt b hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub : b ∣ (a₂ + (k₀ + t * d₀) * M) - (a₁ + (k₀ + t * d₀) * M) := Nat.dvd_sub h2 h1
      have heq : (a₂ + (k₀ + t * d₀) * M) - (a₁ + (k₀ + t * d₀) * M) = a₂ - a₁ := by omega
      rw [heq] at hsub
      have := Nat.le_of_dvd (by omega) hsub
      omega
    · have hsub : b ∣ (a₁ + (k₀ + t * d₀) * M) - (a₂ + (k₀ + t * d₀) * M) := Nat.dvd_sub h1 h2
      have heq : (a₁ + (k₀ + t * d₀) * M) - (a₂ + (k₀ + t * d₀) * M) = a₁ - a₂ := by omega
      rw [heq] at hsub
      have := Nat.le_of_dvd (by omega) hsub
      omega
  -- Partition S_all by the choice function f : T → A_n
  let F_set : Finset (∀ _b : T, ℕ) := Fintype.piFinset (fun _b : T => A_n)
  let S_f : (∀ _b : T, ℕ) → Finset ℕ := fun f =>
    (Finset.range N).filter (fun t => ∀ b : T, (b : ℕ) ∣ f b + (k₀ + t * d₀) * M)
  have hbiUnion : S_all = F_set.biUnion S_f := by
    ext t
    simp only [S_all, S_f, F_set, Finset.mem_filter, Finset.mem_biUnion, Fintype.mem_piFinset]
    constructor
    · intro ⟨htN, hall⟩
      let f : ∀ _b : T, ℕ := fun b => Classical.choose (hall b.1 b.2)
      refine ⟨f, fun b => (Classical.choose_spec (hall b.1 b.2)).1, htN,
        fun b => (Classical.choose_spec (hall b.1 b.2)).2⟩
    · intro ⟨f, hf, htN, hdiv⟩
      exact ⟨htN, fun b hb => ⟨f ⟨b, hb⟩, hf ⟨b, hb⟩, hdiv ⟨b, hb⟩⟩⟩
  have hdisj : Set.PairwiseDisjoint (F_set : Set (∀ _b : T, ℕ)) S_f := by
    intro f₁ hf₁ f₂ hf₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [S_f, Finset.mem_filter] at ht1 ht2
    simp only [F_set, Finset.mem_coe, Fintype.mem_piFinset] at hf₁ hf₂
    apply hne
    funext b
    exact huniq b.1 b.2 t (f₁ b) (hf₁ b) (f₂ b) (hf₂ b) (ht1.2 b) (ht2.2 b)
  have hcard_eq : (S_all.card : ℝ) = ∑ f ∈ F_set, ((S_f f).card : ℝ) := by
    rw [hbiUnion, Finset.card_biUnion hdisj, Nat.cast_sum]
  have hF_card : F_set.card = A_n.card ^ T.card := by
    simp [F_set]
  -- Bound each S_f f by CRT
  have hD_pos : 0 < ∏ b ∈ T, b :=
    Finset.prod_pos fun b hb => by have := hT_gt b hb; omega
  have hS_f_bound : ∀ f ∈ F_set,
      |((S_f f).card : ℝ) - (N : ℝ) / (∏ b ∈ T, (b : ℝ))| ≤ 1 := by
    intro f _
    have hlin : ∀ b : T, ∃ r : ℕ, ∀ t : ℕ, (b : ℕ) ∣ (f b + k₀ * M) + t * (d₀ * M) ↔ t ≡ r [MOD b] := by
      intro b
      exact dvd_linear_iff_modEq b.1 (f b + k₀ * M) (d₀ * M)
        (by have := hT_gt b.1 b.2; omega) (hT_cop_s b.1 b.2)
    let r_b : ℕ → ℕ := fun b => if hb : b ∈ T then Classical.choose (hlin ⟨b, hb⟩) else 0
    obtain ⟨r_all, hr_all⟩ := crt_finset_coprime T hT_cop r_b
    have hSf_eq : S_f f = (Finset.range N).filter (fun t => t ≡ r_all [MOD ∏ b ∈ T, b]) := by
      ext t
      simp only [S_f, Finset.mem_filter]
      refine and_congr_right fun _ => ?_
      rw [← hr_all t]
      constructor
      · intro h b hb
        have hspec := Classical.choose_spec (hlin ⟨b, hb⟩)
        have hrb : r_b b = Classical.choose (hlin ⟨b, hb⟩) := by simp [r_b, hb]
        rw [hrb, ← hspec t]
        have heq : f ⟨b, hb⟩ + (k₀ + t * d₀) * M = (f ⟨b, hb⟩ + k₀ * M) + t * (d₀ * M) := by ring
        rw [← heq]
        exact h ⟨b, hb⟩
      · intro h b
        have hspec := Classical.choose_spec (hlin b)
        have hrb : r_b b.1 = Classical.choose (hlin b) := by simp [r_b, b.2]
        have heq : f b + (k₀ + t * d₀) * M = (f b + k₀ * M) + t * (d₀ * M) := by ring
        rw [heq, hspec t, ← hrb]
        exact h b.1 b.2
    rw [hSf_eq, ← Nat.cast_prod]
    exact abs_card_modEq_sub_le N (∏ b ∈ T, b) r_all hD_pos
  -- Sum the error bounds over f ∈ F_set
  have hmain_eq : (N : ℝ) * ((A_n.card : ℝ) ^ T.card / (∏ b ∈ T, (b : ℝ))) =
      ∑ _f ∈ F_set, (N : ℝ) / (∏ b ∈ T, (b : ℝ)) := by
    rw [Finset.sum_const, hF_card, nsmul_eq_mul, Nat.cast_pow]; ring
  rw [hcard_eq, hmain_eq, ← Finset.sum_sub_distrib]
  calc
    |∑ f ∈ F_set, (((S_f f).card : ℝ) - (N : ℝ) / (∏ b ∈ T, (b : ℝ)))|
      ≤ ∑ f ∈ F_set, |((S_f f).card : ℝ) - (N : ℝ) / (∏ b ∈ T, (b : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f ∈ F_set, (1 : ℝ) := Finset.sum_le_sum hS_f_bound
    _ = (A_n.card : ℝ) ^ T.card := by rw [Finset.sum_const, hF_card, nsmul_eq_mul, mul_one, Nat.cast_pow]


/- ---------------------------------------------------------------------------
   Part 3: Block-Bonferroni Combinatorial Sieve
   --------------------------------------------------------------------------- -/

/-- Alternating binomial sum identity:
`∑ j ∈ range (s + 1), (-1)^j * C(m, j) = if m = 0 then 1 else (-1)^s * C(m - 1, s)`. -/
private lemma alt_sum_choose (m s : ℕ) :
    ∑ j ∈ Finset.range (s + 1), (-1 : ℝ) ^ j * (Nat.choose m j : ℝ) =
      if m = 0 then 1 else (-1 : ℝ) ^ s * (Nat.choose (m - 1) s : ℝ) := by
  cases m with
  | zero =>
    rw [Finset.sum_range_succ']
    simp
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ m s, Nat.cast_add, pow_succ]
      ring

/-- Single-block Bonferroni upper bound (even truncation `2 * r`):
`(if E = ∅ then 1 else 0) ≤ ∑ T ∈ E.powerset.filter (fun T => T.card ≤ 2 * r), (-1)^|T|`. -/
private lemma bonferroni_upper (E : Finset ℕ) (r : ℕ) :
    (if E = ∅ then (1 : ℝ) else 0) ≤
      ∑ T ∈ E.powerset.filter (fun T => T.card ≤ 2 * r), (-1 : ℝ) ^ T.card := by
  have hgroup : ∑ T ∈ E.powerset.filter (fun T => T.card ≤ 2 * r), (-1 : ℝ) ^ T.card =
      ∑ j ∈ Finset.range (2 * r + 1), (-1 : ℝ) ^ j * (Nat.choose E.card j : ℝ) := by
    have hbi : E.powerset.filter (fun T => T.card ≤ 2 * r) =
        (Finset.range (2 * r + 1)).biUnion (fun j => E.powersetCard j) := by
      ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard]
      constructor
      · intro ⟨hsub, hle⟩; exact ⟨T.card, by omega, hsub, rfl⟩
      · intro ⟨j, hj, hsub, hcard⟩; exact ⟨hsub, by omega⟩
    rw [hbi, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hconst : ∑ T ∈ E.powersetCard j, (-1 : ℝ) ^ T.card =
          ∑ _T ∈ E.powersetCard j, (-1 : ℝ) ^ j :=
        Finset.sum_congr rfl fun T hT => by rw [(Finset.mem_powersetCard.mp hT).2]
      rw [hconst, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
    · intro i _ j _ hij
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro T hi hj
      exact hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)
  rw [hgroup, alt_sum_choose]
  by_cases hE : E = ∅
  · simp [hE]
  · have hne : E.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hE)
    simp only [hE, hne, ↓reduceIte, Even.neg_one_pow (even_two_mul r), one_mul]
    positivity

/-- Single-block Bonferroni lower bound (odd truncation `2 * r - 1`, for `r ≥ 1`):
`∑ T ∈ E.powerset.filter (fun T => T.card ≤ 2 * r - 1), (-1)^|T| ≤ if E = ∅ then 1 else 0`. -/
private lemma bonferroni_lower (E : Finset ℕ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ T ∈ E.powerset.filter (fun T => T.card ≤ 2 * r - 1), (-1 : ℝ) ^ T.card ≤
      if E = ∅ then (1 : ℝ) else 0 := by
  have hgroup : ∑ T ∈ E.powerset.filter (fun T => T.card ≤ 2 * r - 1), (-1 : ℝ) ^ T.card =
      ∑ j ∈ Finset.range ((2 * r - 1) + 1), (-1 : ℝ) ^ j * (Nat.choose E.card j : ℝ) := by
    have hbi : E.powerset.filter (fun T => T.card ≤ 2 * r - 1) =
        (Finset.range ((2 * r - 1) + 1)).biUnion (fun j => E.powersetCard j) := by
      ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard]
      constructor
      · intro ⟨hsub, hle⟩; exact ⟨T.card, by omega, hsub, rfl⟩
      · intro ⟨j, hj, hsub, hcard⟩; exact ⟨hsub, by omega⟩
    rw [hbi, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have hconst : ∑ T ∈ E.powersetCard j, (-1 : ℝ) ^ T.card =
          ∑ _T ∈ E.powersetCard j, (-1 : ℝ) ^ j :=
        Finset.sum_congr rfl fun T hT => by rw [(Finset.mem_powersetCard.mp hT).2]
      rw [hconst, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]
    · intro i _ j _ hij
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro T hi hj
      exact hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)
  rw [hgroup, alt_sum_choose]
  by_cases hE : E = ∅
  · simp [hE]
  · have hne : E.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hE)
    have hodd : Odd (2 * r - 1) := ⟨r - 1, by omega⟩
    simp only [hE, hne, ↓reduceIte, Odd.neg_one_pow hodd]
    linarith [show (0 : ℝ) ≤ (Nat.choose (E.card - 1) (2 * r - 1) : ℝ) by positivity]

/-- Telescoping lower bound for products: for `0 ≤ x_j ≤ u_j` and `l_j ≤ x_j`,
`∏ j ∈ s, u_j - ∑ j ∈ s, (u_j - l_j) * ∏ i ∈ s.erase j, u_i ≤ ∏ j ∈ s, x_j`. -/
private lemma prod_lower_of_bounds {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x u l : ι → ℝ) (hx0 : ∀ i ∈ s, 0 ≤ x i) (hxu : ∀ i ∈ s, x i ≤ u i)
    (hlx : ∀ i ∈ s, l i ≤ x i) :
    (∏ i ∈ s, u i) - ∑ j ∈ s, (u j - l j) * ∏ i ∈ s.erase j, u i ≤ ∏ i ∈ s, x i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hu0 : ∀ i ∈ s, 0 ≤ u i := fun i hi =>
      (hx0 i (Finset.mem_insert_of_mem hi)).trans (hxu i (Finset.mem_insert_of_mem hi))
    have hih := ih (fun i hi => hx0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hxu i (Finset.mem_insert_of_mem hi))
      (fun i hi => hlx i (Finset.mem_insert_of_mem hi))
    have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
    have hxau : x a ≤ u a := hxu a (Finset.mem_insert_self a s)
    have hlxa : l a ≤ x a := hlx a (Finset.mem_insert_self a s)
    have hpx_nn : 0 ≤ ∏ i ∈ s, x i := Finset.prod_nonneg fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
    have hpu_nn : 0 ≤ ∏ i ∈ s, u i := Finset.prod_nonneg hu0
    have hpx_le_pu : ∏ i ∈ s, x i ≤ ∏ i ∈ s, u i :=
      Finset.prod_le_prod (fun i hi => hx0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hxu i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha]
    have hsum_er : ∑ j ∈ s, (u j - l j) * ∏ i ∈ (insert a s).erase j, u i =
        u a * ∑ j ∈ s, (u j - l j) * ∏ i ∈ s.erase j, u i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : a ≠ j := fun h => ha (h ▸ hj)
      rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (by simp [ha])]; ring
    rw [hsum_er]
    have h1 : (u a - x a) * ∏ i ∈ s, u i ≤ (u a - l a) * ∏ i ∈ s, u i :=
      mul_le_mul_of_nonneg_right (by linarith) hpu_nn
    have h2 : x a * ((∏ i ∈ s, u i) - ∏ i ∈ s, x i) ≤
        u a * ∑ j ∈ s, (u j - l j) * ∏ i ∈ s.erase j, u i := by
      have hdiff_nn : 0 ≤ (∏ i ∈ s, u i) - ∏ i ∈ s, x i := by linarith
      have hsum_ge : (∏ i ∈ s, u i) - ∏ i ∈ s, x i ≤ ∑ j ∈ s, (u j - l j) * ∏ i ∈ s.erase j, u i := by linarith
      exact mul_le_mul hxau hsum_ge hdiff_nn (by linarith)
    linarith

/-- Elementary symmetric polynomial bound:
`∑ T ∈ I.powersetCard j, ∏ b ∈ T, g b ≤ (∑ b ∈ I, g b)^j / j!`. -/
private lemma elem_symm_le_pow_div_fact (I : Finset ℕ) (g : ℕ → ℝ) (hg0 : ∀ b ∈ I, 0 ≤ g b) (j : ℕ) :
    ∑ T ∈ I.powersetCard j, (∏ b ∈ T, g b) ≤ (∑ b ∈ I, g b) ^ j / (j.factorial : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hS_nn : 0 ≤ ∑ b ∈ I, g b := Finset.sum_nonneg hg0
    -- Double-count pairs (T, b) with T ∈ powersetCard j, b ∈ I \ T
    have hdouble : ((j + 1 : ℕ) : ℝ) * ∑ U ∈ I.powersetCard (j + 1), (∏ x ∈ U, g x) =
        ∑ T ∈ I.powersetCard j, (∏ x ∈ T, g x) * ∑ b ∈ I \ T, g b := by
      have h1 : ∑ U ∈ I.powersetCard (j + 1), ((j + 1 : ℕ) : ℝ) * (∏ x ∈ U, g x) =
          ∑ U ∈ I.powersetCard (j + 1), ∑ b ∈ U, g b * (∏ x ∈ U.erase b, g x) := by
        refine Finset.sum_congr rfl fun U hU => ?_
        have hcard : U.card = j + 1 := (Finset.mem_powersetCard.mp hU).2
        have hconst : ∑ b ∈ U, g b * (∏ x ∈ U.erase b, g x) =
            ∑ _b ∈ U, (∏ x ∈ U, g x) :=
          Finset.sum_congr rfl fun b hb => Finset.mul_prod_erase U g hb
        rw [hconst, Finset.sum_const, hcard, nsmul_eq_mul]
      rw [Finset.mul_sum, h1]
      simp_rw [Finset.mul_sum]
      -- Swap sum over (U, b ∈ U) with sum over (T, b ∈ I \ T) via U = insert b T
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_bij (fun p _ => ⟨p.1.erase p.2, p.2⟩) ?_ ?_ ?_ ?_
      · intro ⟨U, b⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hp ⊢
        refine ⟨⟨(Finset.erase_subset b U).trans hp.1.1, by rw [Finset.card_erase_of_mem hp.2, hp.1.2]; omega⟩,
          hp.1.1 hp.2, Finset.notMem_erase b U⟩
      · intro ⟨U₁, b₁⟩ hp₁ ⟨U₂, b₂⟩ hp₂ heq
        simp only [Finset.mem_sigma] at hp₁ hp₂
        simp only [Sigma.mk.inj_iff] at heq
        obtain ⟨hU, hb⟩ := heq
        subst hb
        have hU' : U₁.erase b₁ = U₂.erase b₁ := by simpa using hU
        have : U₁ = U₂ := by
          rw [← Finset.insert_erase hp₁.2, ← Finset.insert_erase hp₂.2, hU']
        subst this; rfl
      · intro ⟨T, b⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hp
        refine ⟨⟨insert b T, b⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_powersetCard]
          exact ⟨⟨Finset.insert_subset_iff.mpr ⟨hp.2.1, hp.1.1⟩,
            by rw [Finset.card_insert_of_notMem hp.2.2, hp.1.2]⟩, Finset.mem_insert_self b T⟩
        · simp [Finset.erase_insert hp.2.2]
      · intro ⟨U, b⟩ _
        dsimp only
        rw [mul_comm]
    have hle : ∑ T ∈ I.powersetCard j, (∏ x ∈ T, g x) * ∑ b ∈ I \ T, g b ≤
        (∑ T ∈ I.powersetCard j, (∏ x ∈ T, g x)) * (∑ b ∈ I, g b) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun T hT => ?_
      have hprod_nn : 0 ≤ ∏ x ∈ T, g x :=
        Finset.prod_nonneg fun x hx => hg0 x ((Finset.mem_powersetCard.mp hT).1 hx)
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun b hb _ => hg0 b hb) hprod_nn
    have hj1_pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((j + 1).factorial : ℝ))]
    calc (∑ U ∈ I.powersetCard (j + 1), (∏ x ∈ U, g x)) * ((j + 1).factorial : ℝ)
        = (((j + 1 : ℕ) : ℝ) * ∑ U ∈ I.powersetCard (j + 1), (∏ x ∈ U, g x)) * (j.factorial : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul]; ring
      _ = (∑ T ∈ I.powersetCard j, (∏ x ∈ T, g x) * ∑ b ∈ I \ T, g b) * (j.factorial : ℝ) := by rw [hdouble]
      _ ≤ ((∑ T ∈ I.powersetCard j, (∏ x ∈ T, g x)) * (∑ b ∈ I, g b)) * (j.factorial : ℝ) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
      _ ≤ ((∑ b ∈ I, g b) ^ j / (j.factorial : ℝ) * (∑ b ∈ I, g b)) * (j.factorial : ℝ) := by gcongr
      _ = (∑ b ∈ I, g b) ^ (j + 1) := by
            rw [pow_succ]; field_simp [(Nat.cast_pos.mpr (Nat.factorial_pos j)).ne']

/-- Exponential lower bound on `1 - x`: for `0 ≤ x ≤ 1/2`, `exp (-2 * x) ≤ 1 - x`. -/
private lemma exp_neg_two_mul_le_one_sub (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have hprod : 1 ≤ (1 - x) * Real.exp (2 * x) := by
    calc (1 : ℝ) ≤ (1 - x) * (1 + 2 * x) := by nlinarith
      _ ≤ (1 - x) * Real.exp (2 * x) := mul_le_mul_of_nonneg_left hexp (by linarith)
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
  calc (Real.exp (2 * x))⁻¹ = 1 * (Real.exp (2 * x))⁻¹ := (one_mul _).symm
    _ ≤ ((1 - x) * Real.exp (2 * x)) * (Real.exp (2 * x))⁻¹ :=
        mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = 1 - x := by field_simp [(Real.exp_pos _).ne']

/-- Single-block Bonferroni main-term bounds: if `S = ∑ b ∈ I, g b ≤ 1 / 20` and `r ≥ 2`, then
`M_upper := ∑_{T ⊆ I, |T| ≤ 2r} (-1)^|T| ∏_{b ∈ T} g b` and
`M_lower := ∑_{T ⊆ I, |T| ≤ 2r - 1} (-1)^|T| ∏_{b ∈ T} g b` satisfy:
1. `V ≤ M_upper ≤ V * (1 + 4 * (1 / 20) ^ (2 * r + 1))`
2. `0 ≤ M_upper - M_lower ≤ (1 / 20) ^ (2 * r)`
3. `1 / 2 ≤ V` (where `V = ∏ b ∈ I, (1 - g b)`). -/
private lemma single_block_main_bounds (I : Finset ℕ) (g : ℕ → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hg0 : ∀ b ∈ I, 0 ≤ g b) (hS : ∑ b ∈ I, g b ≤ 1 / 20) :
    let V := ∏ b ∈ I, (1 - g b)
    let M_u := ∑ T ∈ I.powerset.filter (fun T => T.card ≤ 2 * r), (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)
    let M_l := ∑ T ∈ I.powerset.filter (fun T => T.card ≤ 2 * r - 1), (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)
    (1 / 2 : ℝ) ≤ V ∧
    V * (1 - 4 * (1 / 20 : ℝ) ^ (2 * r + 1)) ≤ M_u ∧
    M_u ≤ V * (1 + 4 * (1 / 20 : ℝ) ^ (2 * r + 1)) ∧
    0 ≤ M_u - M_l ∧
    M_u - M_l ≤ (1 / 20 : ℝ) ^ (2 * r) := by
  intro V M_u M_l
  have hS_nn : 0 ≤ ∑ b ∈ I, g b := Finset.sum_nonneg hg0
  have hg1 : ∀ b ∈ I, g b ≤ 1 / 2 := fun b hb =>
    (Finset.single_le_sum hg0 hb).trans (by linarith)
  have hV_ge : (1 / 2 : ℝ) ≤ V := by
    have h1 : Real.exp (-2 * ∑ b ∈ I, g b) ≤ V := by
      unfold V
      rw [show -2 * ∑ b ∈ I, g b = ∑ b ∈ I, (-2 * g b) by rw [← Finset.mul_sum], Real.exp_sum]
      exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun b hb =>
        exp_neg_two_mul_le_one_sub (g b) (hg0 b hb) (hg1 b hb)
    have h2 : (1 / 2 : ℝ) ≤ Real.exp (-2 * ∑ b ∈ I, g b) := by
      have : Real.exp (1 / 10 : ℝ) ≤ 2 := by
        have h10 : (Real.exp (1 / 10 : ℝ)) ^ 10 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
        have hlt : Real.exp 1 < 2 ^ 10 := by linarith [Real.exp_one_lt_d9]
        by_contra hgt; push Not at hgt
        linarith [pow_lt_pow_left₀ hgt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 10 ≠ 0)]
      calc (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
        _ ≤ (Real.exp (1 / 10 : ℝ))⁻¹ := inv_anti₀ (Real.exp_pos _) this
        _ = Real.exp (-(1 / 10 : ℝ)) := (Real.exp_neg _).symm
        _ ≤ Real.exp (-2 * ∑ b ∈ I, g b) := Real.exp_le_exp.mpr (by linarith)
    exact h2.trans h1
  -- Full expansion of V = ∑_{T ⊆ I} (-1)^|T| ∏_{b ∈ T} g b
  have hV_exp : V = ∑ T ∈ I.powerset, (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b) := by
    dsimp only [V]
    have h1 : ∏ b ∈ I, (1 - g b) = ∏ b ∈ I, ((-g b) + 1) :=
      Finset.prod_congr rfl fun b _ => by ring
    rw [h1, Finset.prod_add_one]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_neg]
  -- Difference M_u - V = - ∑_{T ⊆ I, 2r < |T|} (-1)^|T| ∏ g b
  have hdiff_u : M_u - V =
      -(∑ T ∈ I.powerset.filter (fun T => ¬ T.card ≤ 2 * r), (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)) := by
    have hsp := Finset.sum_filter_add_sum_filter_not I.powerset (fun T => T.card ≤ 2 * r)
      (fun T => (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b))
    dsimp only [M_u]; rw [hV_exp]; linarith
  -- Bound |M_u - V| ≤ ∑_{j = 2r + 1}^{|I|} S^j / j! ≤ 2 * (1/20)^(2r+1)
  have htail_bound : |M_u - V| ≤ 2 * (1 / 20 : ℝ) ^ (2 * r + 1) := by
    rw [hdiff_u, abs_neg]
    have hbi : I.powerset.filter (fun T => ¬ T.card ≤ 2 * r) =
        (Finset.Icc (2 * r + 1) I.card).biUnion (fun j => I.powersetCard j) := by
      ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
        Finset.mem_Icc, Finset.mem_powersetCard]
      constructor
      · intro ⟨hsub, hgt⟩; exact ⟨T.card, ⟨by omega, Finset.card_le_card hsub⟩, hsub, rfl⟩
      · intro ⟨j, hj, hsub, hcard⟩; exact ⟨hsub, by omega⟩
    have hdisj : Set.PairwiseDisjoint (Finset.Icc (2 * r + 1) I.card : Set ℕ) (fun j => I.powersetCard j) := by
      intro i _ j _ hij
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro T hi hj
      exact hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)
    calc |∑ T ∈ I.powerset.filter (fun T => ¬ T.card ≤ 2 * r), (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)|
        ≤ ∑ T ∈ I.powerset.filter (fun T => ¬ T.card ≤ 2 * r), |(-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ T ∈ I.powerset.filter (fun T => ¬ T.card ≤ 2 * r), (∏ b ∈ T, g b) := by
          refine Finset.sum_congr rfl fun T hT => ?_
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (Finset.prod_nonneg fun b hb => hg0 b ((Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) hb))]
      _ = ∑ j ∈ Finset.Icc (2 * r + 1) I.card, ∑ T ∈ I.powersetCard j, (∏ b ∈ T, g b) := by
          rw [hbi, Finset.sum_biUnion hdisj]
      _ ≤ ∑ j ∈ Finset.Icc (2 * r + 1) I.card, (∑ b ∈ I, g b) ^ j / (j.factorial : ℝ) :=
          Finset.sum_le_sum fun j _ => elem_symm_le_pow_div_fact I g hg0 j
      _ ≤ ∑ j ∈ Finset.Icc (2 * r + 1) I.card, (1 / 20 : ℝ) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 : (∑ b ∈ I, g b) ^ j / (j.factorial : ℝ) ≤ (∑ b ∈ I, g b) ^ j :=
            div_le_self (pow_nonneg hS_nn j) (by exact_mod_cast Nat.factorial_pos j)
          exact h1.trans (pow_le_pow_left₀ hS_nn hS j)
      _ ≤ 2 * (1 / 20 : ℝ) ^ (2 * r + 1) := by
          by_cases hle : 2 * r + 1 ≤ I.card
          · have hreindex : ∑ j ∈ Finset.Icc (2 * r + 1) I.card, (1 / 20 : ℝ) ^ j =
                (1 / 20 : ℝ) ^ (2 * r + 1) * ∑ m ∈ Finset.range (I.card + 1 - (2 * r + 1)), (1 / 20 : ℝ) ^ m := by
              rw [Finset.mul_sum]
              refine Finset.sum_bij (fun j _ => j - (2 * r + 1)) ?_ ?_ ?_ ?_
              · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
              · intro j₁ hj₁ j₂ hj₂ h; rw [Finset.mem_Icc] at hj₁ hj₂; omega
              · intro m hm; rw [Finset.mem_range] at hm
                exact ⟨m + (2 * r + 1), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro j hj; rw [Finset.mem_Icc] at hj
                rw [← pow_add, show 2 * r + 1 + (j - (2 * r + 1)) = j by omega]
            rw [hreindex, geom_sum_eq (by norm_num)]
            have hnn : (0 : ℝ) ≤ (1 / 20 : ℝ) ^ (I.card + 1 - (2 * r + 1)) := by positivity
            have hdiv : ((1 / 20 : ℝ) ^ (I.card + 1 - (2 * r + 1)) - 1) / (1 / 20 - 1) =
                (1 - (1 / 20 : ℝ) ^ (I.card + 1 - (2 * r + 1))) * (20 / 19) := by ring
            have hgeom : ((1 / 20 : ℝ) ^ (I.card + 1 - (2 * r + 1)) - 1) / (1 / 20 - 1) ≤ 2 := by
              rw [hdiv]; linarith
            calc (1 / 20 : ℝ) ^ (2 * r + 1) * (((1 / 20 : ℝ) ^ (I.card + 1 - (2 * r + 1)) - 1) / (1 / 20 - 1))
                ≤ (1 / 20 : ℝ) ^ (2 * r + 1) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
              _ = 2 * (1 / 20 : ℝ) ^ (2 * r + 1) := by ring
          · have : Finset.Icc (2 * r + 1) I.card = ∅ := Finset.Icc_eq_empty (by omega)
            rw [this, Finset.sum_empty]; positivity
  have hdiff_ul : M_u - M_l = ∑ T ∈ I.powersetCard (2 * r), (∏ b ∈ T, g b) := by
    have hpart : I.powerset.filter (fun T => T.card ≤ 2 * r) =
        I.powerset.filter (fun T => T.card ≤ 2 * r - 1) ∪ I.powersetCard (2 * r) := by
      ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_powersetCard]
      constructor
      · intro ⟨h1, h2⟩
        by_cases h3 : T.card = 2 * r
        · exact Or.inr ⟨h1, h3⟩
        · exact Or.inl ⟨h1, by omega⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
    have hdisj : Disjoint (I.powerset.filter (fun T => T.card ≤ 2 * r - 1)) (I.powersetCard (2 * r)) := by
      rw [Finset.disjoint_left]
      intro T h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_powersetCard.mp h2).2
      omega
    dsimp only [M_u, M_l]
    rw [hpart, Finset.sum_union hdisj, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [(Finset.mem_powersetCard.mp hT).2, Even.neg_one_pow (even_two_mul r), one_mul]
  have hMu_l_nn : 0 ≤ M_u - M_l := by
    rw [hdiff_ul]
    exact Finset.sum_nonneg fun T hT =>
      Finset.prod_nonneg fun b hb => hg0 b ((Finset.mem_powersetCard.mp hT).1 hb)
  have hMu_l_le : M_u - M_l ≤ (1 / 20 : ℝ) ^ (2 * r) := by
    rw [hdiff_ul]
    calc ∑ T ∈ I.powersetCard (2 * r), (∏ b ∈ T, g b)
        ≤ (∑ b ∈ I, g b) ^ (2 * r) / ((2 * r).factorial : ℝ) := elem_symm_le_pow_div_fact I g hg0 (2 * r)
      _ ≤ (∑ b ∈ I, g b) ^ (2 * r) :=
          div_le_self (pow_nonneg hS_nn _) (by exact_mod_cast Nat.factorial_pos _)
      _ ≤ (1 / 20 : ℝ) ^ (2 * r) := pow_le_pow_left₀ hS_nn hS _
  have htail_abs := abs_le.mp htail_bound
  have h4V : 2 * (1 / 20 : ℝ) ^ (2 * r + 1) ≤ V * (4 * (1 / 20 : ℝ) ^ (2 * r + 1)) := by
    nlinarith [hV_ge, show (0 : ℝ) ≤ (1 / 20 : ℝ) ^ (2 * r + 1) by positivity]
  exact ⟨hV_ge, by linarith, by linarith, hMu_l_nn, hMu_l_le⟩

/- ---------------------------------------------------------------------------
   Part 4: Block-Bonferroni Sieve on Arithmetic Progressions
   --------------------------------------------------------------------------- -/

/-- Injectivity of `T ↦ ∏ b ∈ T, b` on subsets of a pairwise coprime set of integers `≥ 2`. -/
private lemma prod_injOn_powerset_coprime (B : Finset ℕ) (hcop : (B : Set ℕ).Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B, 2 ≤ b) :
    Set.InjOn (fun T : Finset ℕ => ∏ b ∈ T, b) (B.powerset : Set (Finset ℕ)) := by
  intro T₁ hT₁ T₂ hT₂ heq
  dsimp only at heq
  have hsub1 : T₁ ⊆ B := Finset.mem_powerset.mp (Finset.mem_coe.mp hT₁)
  have hsub2 : T₂ ⊆ B := Finset.mem_powerset.mp (Finset.mem_coe.mp hT₂)
  ext b
  constructor
  · intro hb1
    by_contra hb2
    have hdvd1 : b ∣ ∏ x ∈ T₁, x := Finset.dvd_prod_of_mem id hb1
    rw [heq] at hdvd1
    have hcop_b : Nat.Coprime b (∏ x ∈ T₂, x) :=
      Nat.Coprime.prod_right fun x hx =>
        hcop (hsub1 hb1) (hsub2 hx) (fun h => hb2 (h ▸ hx))
    have hdvd_one : b ∣ 1 := hcop_b.dvd_of_dvd_mul_left (by simpa using hdvd1)
    have := Nat.le_of_dvd one_pos hdvd_one
    have := hge2 b (hsub1 hb1)
    omega
  · intro hb2
    by_contra hb1
    have hdvd2 : b ∣ ∏ x ∈ T₂, x := Finset.dvd_prod_of_mem id hb2
    rw [← heq] at hdvd2
    have hcop_b : Nat.Coprime b (∏ x ∈ T₁, x) :=
      Nat.Coprime.prod_right fun x hx =>
        hcop (hsub2 hb2) (hsub1 hx) (fun h => hb1 (h ▸ hx))
    have hdvd_one : b ∣ 1 := hcop_b.dvd_of_dvd_mul_left (by simpa using hdvd2)
    have := Nat.le_of_dvd one_pos hdvd_one
    have := hge2 b (hsub2 hb2)
    omega

/-- Expanding a product of block sums over pairwise disjoint blocks `I j` (`j ∈ s`)
into a single sum over `T ⊆ s.biUnion I`. -/
private lemma prod_sum_disjoint_blocks {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (I : ι → Finset ℕ) (hdisj : Set.PairwiseDisjoint (s : Set ι) I)
    (P : ι → Finset ℕ → Prop) [∀ j T, Decidable (P j T)] (h : Finset ℕ → ℝ)
    (hh_mul : ∀ T₁ T₂ : Finset ℕ, Disjoint T₁ T₂ → h (T₁ ∪ T₂) = h T₁ * h T₂)
    (hh_empty : h ∅ = 1) :
    ∏ j ∈ s, ∑ T ∈ (I j).powerset.filter (P j), h T =
      ∑ T ∈ (s.biUnion I).powerset.filter (fun T => ∀ j ∈ s, P j (T ∩ I j)), h T := by
  induction s using Finset.induction_on with
  | empty =>
    simp [hh_empty]
  | @insert a s ha ih =>
    have hdisj_s : Set.PairwiseDisjoint (s : Set ι) I :=
      hdisj.subset (Finset.subset_insert a s)
    have hdisj_a : Disjoint (I a) (s.biUnion I) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_insert_self a s))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hj)) (fun h => ha (h ▸ hj))
    rw [Finset.prod_insert ha, ih hdisj_s, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
    · intro ⟨T₁, T₂⟩ hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp ⊢
      refine ⟨?_, ?_⟩
      · rw [Finset.biUnion_insert]
        exact Finset.union_subset_union hp.1.1 hp.2.1
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · have hT2_disj : Disjoint T₂ (I j) := (Finset.disjoint_of_subset_right hp.2.1 hdisj_a).symm
          have hinter : (T₁ ∪ T₂) ∩ I j = T₁ := by
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.1.1,
              Finset.disjoint_iff_inter_eq_empty.mp hT2_disj, Finset.union_empty]
          rw [hinter]; exact hp.1.2
        · have hT1_disj : Disjoint T₁ (I j) :=
            Finset.disjoint_of_subset_left hp.1.1
              (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem I hjs) hdisj_a)
          have hinter : (T₁ ∪ T₂) ∩ I j = T₂ ∩ I j := by
            rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hT1_disj,
              Finset.empty_union]
          rw [hinter]; exact hp.2.2 j hjs
    · intro ⟨T₁, T₂⟩ hp₁ ⟨U₁, U₂⟩ hp₂ heq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp₁ hp₂
      have hd1 : Disjoint T₂ (I a) := (Finset.disjoint_of_subset_right hp₁.2.1 hdisj_a).symm
      have hd2 : Disjoint U₂ (I a) := (Finset.disjoint_of_subset_right hp₂.2.1 hdisj_a).symm
      have hd3 : Disjoint T₁ (s.biUnion I) := Finset.disjoint_of_subset_left hp₁.1.1 hdisj_a
      have hd4 : Disjoint U₁ (s.biUnion I) := Finset.disjoint_of_subset_left hp₂.1.1 hdisj_a
      have h1 : T₁ = U₁ := by
        have := congrArg (· ∩ I a) heq
        simp only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp₁.1.1,
          Finset.inter_eq_left.mpr hp₂.1.1, Finset.disjoint_iff_inter_eq_empty.mp hd1,
          Finset.disjoint_iff_inter_eq_empty.mp hd2, Finset.union_empty] at this
        exact this
      have h2 : T₂ = U₂ := by
        have := congrArg (· ∩ s.biUnion I) heq
        simp only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp₁.2.1,
          Finset.inter_eq_left.mpr hp₂.2.1, Finset.disjoint_iff_inter_eq_empty.mp hd3,
          Finset.disjoint_iff_inter_eq_empty.mp hd4, Finset.empty_union] at this
        exact this
      exact Prod.ext h1 h2
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      refine ⟨(T ∩ I a, T ∩ s.biUnion I), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨⟨Finset.inter_subset_right, hT.2 a (Finset.mem_insert_self a s)⟩,
          ⟨Finset.inter_subset_right, fun j hj => ?_⟩⟩
        have hinter : T ∩ s.biUnion I ∩ I j = T ∩ I j := by
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem I hj)]
        rw [hinter]; exact hT.2 j (Finset.mem_insert_of_mem hj)
      · rw [← Finset.inter_union_distrib_left, ← Finset.biUnion_insert, Finset.inter_eq_left.mpr hT.1]
    · intro ⟨T₁, T₂⟩ hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
      have hd : Disjoint T₁ T₂ :=
        Disjoint.mono hp.1.1 hp.2.1 hdisj_a
      exact (hh_mul T₁ T₂ hd).symm

/-- Numeric bounds on the product of upper-bound block main terms `∏ j ∈ range L, M_u j`. -/
private lemma block_bonferroni_mu_bounds (L : ℕ) (V_j M_u : ℕ → ℝ)
    (hblock : ∀ j ∈ Finset.range L,
      (1 / 2 : ℝ) ≤ V_j j ∧
      V_j j * (1 - 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) ≤ M_u j ∧
      M_u j ≤ V_j j * (1 + 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1))) :
    let V := ∏ j ∈ Finset.range L, V_j j
    (99 / 100 : ℝ) * V ≤ ∏ j ∈ Finset.range L, M_u j ∧
    ∏ j ∈ Finset.range L, M_u j ≤ (102 / 100 : ℝ) * V := by
  intro V
  have hV_nn : 0 ≤ V := Finset.prod_nonneg fun j hj => by linarith [(hblock j hj).1]
  have hsum_eps : ∑ j ∈ Finset.range L, 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) ≤ 1 / 1000 := by
    have hpull : ∑ j ∈ Finset.range L, 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) =
        4 * (1 / 20 : ℝ) ^ 5 * ∑ j ∈ Finset.range L, (1 / 400 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show 2 * (2 + j) + 1 = 5 + 2 * j by omega, pow_add, pow_mul]
      norm_num; ring
    rw [hpull, geom_sum_eq (by norm_num)]
    have hnn : (0 : ℝ) ≤ (1 / 400 : ℝ) ^ L := by positivity
    have hdiv : ((1 / 400 : ℝ) ^ L - 1) / (1 / 400 - 1) = (1 - (1 / 400 : ℝ) ^ L) * (400 / 399) := by ring
    rw [hdiv]
    linarith
  constructor
  · have h1 : ∏ j ∈ Finset.range L, V_j j * (1 - 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) ≤
        ∏ j ∈ Finset.range L, M_u j := by
      refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => (hblock j hj).2.1)
      have hb := hblock j hj
      have hsmall : 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) ≤ 1 / 2 := by
        calc 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) ≤ 4 * (1 / 20 : ℝ) ^ 1 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
          _ ≤ 1 / 2 := by norm_num
      nlinarith [hb.1]
    rw [Finset.prod_mul_distrib] at h1
    have h2 : Real.exp (-2 * ∑ j ∈ Finset.range L, 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) ≤
        ∏ j ∈ Finset.range L, (1 - 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) := by
      rw [show -2 * ∑ j ∈ Finset.range L, 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) =
          ∑ j ∈ Finset.range L, (-2 * (4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1))) by
            rw [Finset.mul_sum],
        Real.exp_sum]
      refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun j _ =>
        exp_neg_two_mul_le_one_sub _ (by positivity) (by
          calc 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) ≤ 4 * (1 / 20 : ℝ) ^ 1 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
            _ ≤ 1 / 2 := by norm_num)
    have h3 : (99 / 100 : ℝ) ≤ Real.exp (-(2 / 1000 : ℝ)) := by
      have := Real.add_one_le_exp (-(2 / 1000 : ℝ))
      linarith
    calc (99 / 100 : ℝ) * V = V * (99 / 100 : ℝ) := by ring
      _ ≤ V * Real.exp (-(2 / 1000 : ℝ)) := mul_le_mul_of_nonneg_left h3 hV_nn
      _ ≤ V * Real.exp (-2 * ∑ j ∈ Finset.range L, 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hV_nn
      _ ≤ V * ∏ j ∈ Finset.range L, (1 - 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) :=
            mul_le_mul_of_nonneg_left h2 hV_nn
      _ ≤ ∏ j ∈ Finset.range L, M_u j := h1
  · have h1 : ∏ j ∈ Finset.range L, M_u j ≤
        ∏ j ∈ Finset.range L, V_j j * (1 + 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) := by
      refine Finset.prod_le_prod (fun j hj => ?_) (fun j hj => (hblock j hj).2.2)
      have hb := hblock j hj
      have hsmall : 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) ≤ 1 := by
        calc 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) ≤ 4 * (1 / 20 : ℝ) ^ 1 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
          _ ≤ 1 := by norm_num
      nlinarith [hb.1, hb.2.1]
    rw [Finset.prod_mul_distrib] at h1
    have h2 : ∏ j ∈ Finset.range L, (1 + 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) ≤
        Real.exp (∑ j ∈ Finset.range L, 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) := by
      rw [Real.exp_sum]
      exact Finset.prod_le_prod (fun _ _ => by positivity) fun j _ => by
        linarith [Real.add_one_le_exp (4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1))]
    have h3 : Real.exp (1 / 1000 : ℝ) ≤ 102 / 100 := by
      have h100 : (Real.exp (1 / 100 : ℝ)) ^ 100 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      have h200 : (3 : ℝ) ≤ (102 / 100 : ℝ) ^ 100 := by
        have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ 2 / 100 by norm_num) 100
        rw [show (1 : ℝ) + 2 / 100 = 102 / 100 by norm_num] at h1
        linarith
      have hlt : Real.exp 1 < (102 / 100 : ℝ) ^ 100 := by linarith [Real.exp_one_lt_d9]
      have h100_le : Real.exp (1 / 100 : ℝ) ≤ 102 / 100 := by
        by_contra hgt; push Not at hgt
        linarith [pow_lt_pow_left₀ hgt (by norm_num : (0 : ℝ) ≤ 102 / 100) (by norm_num : 100 ≠ 0)]
      exact (Real.exp_le_exp.mpr (by norm_num)).trans h100_le
    calc ∏ j ∈ Finset.range L, M_u j
        ≤ V * ∏ j ∈ Finset.range L, (1 + 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) := h1
      _ ≤ V * Real.exp (∑ j ∈ Finset.range L, 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) :=
            mul_le_mul_of_nonneg_left h2 hV_nn
      _ ≤ V * Real.exp (1 / 1000 : ℝ) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_eps) hV_nn
      _ ≤ V * (102 / 100 : ℝ) := mul_le_mul_of_nonneg_left h3 hV_nn
      _ = (102 / 100 : ℝ) * V := by ring

/-- Main Block-Bonferroni sieve theorem on arithmetic progressions:
gives both lower and upper bounds on the number of `t ∈ range N` avoiding all `b ∈ B_med`. -/
private lemma block_bonferroni_ap (N n k₀ d₀ M L : ℕ) (A_n : Finset ℕ)
    (I : ℕ → Finset ℕ) (D_bound : ℝ)
    (hn1 : 1 ≤ n)
    (hAn : A_n ⊆ Finset.Icc 1 n)
    (hdisj : Set.PairwiseDisjoint (Finset.range L : Set ℕ) I)
    (hB_cop : (((Finset.range L).biUnion I) : Set ℕ).Pairwise Nat.Coprime)
    (hB_gt : ∀ b ∈ (Finset.range L).biUnion I, 2 * n < b)
    (hB_cop_s : ∀ b ∈ (Finset.range L).biUnion I, Nat.Coprime b (d₀ * M))
    (hS : ∀ j ∈ Finset.range L, ∑ b ∈ I j, (A_n.card : ℝ) / (b : ℝ) ≤ 1 / 20)
    (hD_ge1 : 1 ≤ D_bound)
    (hD_supp : ∀ T ∈ ((Finset.range L).biUnion I).powerset.filter
        (fun T => ∀ j ∈ Finset.range L, (T ∩ I j).card ≤ 2 * (2 + j)),
      ∏ b ∈ T, (b : ℝ) ≤ D_bound) :
    let B_med := (Finset.range L).biUnion I
    let S_good := (Finset.range N).filter (fun t =>
      ∀ b ∈ B_med, ∀ a ∈ A_n, ¬ b ∣ a + (k₀ + t * d₀) * M)
    let V := ∏ b ∈ B_med, (1 - (A_n.card : ℝ) / (b : ℝ))
    (98 / 100 : ℝ) * (N : ℝ) * V - 2 * D_bound ^ 2 ≤ (S_good.card : ℝ) ∧
    (S_good.card : ℝ) ≤ (102 / 100 : ℝ) * (N : ℝ) * V + D_bound ^ 2 := by
  intro B_med S_good V
  let w : ℕ := A_n.card
  let g : ℕ → ℝ := fun b => (w : ℝ) / (b : ℝ)
  have hw_le_n : w ≤ n := by
    have h1 := Finset.card_le_card hAn
    rw [Nat.card_Icc] at h1
    dsimp only [w]; omega
  have hB_ge2 : ∀ b ∈ B_med, 2 ≤ b := fun b hb => by have := hB_gt b hb; omega
  let Supp : Finset (Finset ℕ) := B_med.powerset.filter (fun T => ∀ j ∈ Finset.range L, (T ∩ I j).card ≤ 2 * (2 + j))
  -- Cardinality of Supp is ≤ D_bound via injection T ↦ ∏ b ∈ T, b into Icc 1 ⌊D_bound⌋₊
  have hSupp_card : (Supp.card : ℝ) ≤ D_bound := by
    have hinj : Supp.card ≤ (Finset.Icc 1 ⌊D_bound⌋₊).card := by
      refine Finset.card_le_card_of_injOn (fun T => ∏ b ∈ T, b) ?_ ?_
      · intro T hT
        have hT_mem := Finset.mem_coe.mp hT
        have hsub : T ⊆ B_med := Finset.mem_powerset.mp (Finset.mem_filter.mp hT_mem).1
        have hpos : 1 ≤ ∏ b ∈ T, b :=
          Finset.prod_pos fun b hb => Nat.lt_of_lt_of_le (by norm_num) (hB_ge2 b (hsub hb))
        have hle : ∏ b ∈ T, b ≤ ⌊D_bound⌋₊ := by
          refine Nat.le_floor ?_
          rw [Nat.cast_prod]
          exact hD_supp T hT_mem
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hpos, hle⟩)
      · exact (prod_injOn_powerset_coprime B_med hB_cop hB_ge2).mono
          (by intro T hT; exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).1)
    rw [Nat.card_Icc, show ⌊D_bound⌋₊ + 1 - 1 = ⌊D_bound⌋₊ by omega] at hinj
    exact (Nat.cast_le.mpr hinj).trans (Nat.floor_le (by linarith))
  -- For every T ∈ Supp, (2 * w)^|T| ≤ ∏ b ∈ T, b ≤ D_bound
  have h2w_le : ∀ T ∈ Supp, ((2 * w : ℕ) : ℝ) ^ T.card ≤ D_bound := by
    intro T hT
    have hsub : T ⊆ B_med := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have h1 : ((2 * w : ℕ) : ℝ) ^ T.card ≤ ∏ b ∈ T, (b : ℝ) := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun _ _ => by positivity) fun b hb => ?_
      have h1 := hB_gt b (hsub hb)
      have h2 : 2 * w ≤ b := by omega
      exact_mod_cast h2
    exact h1.trans (hD_supp T hT)
  have herr_sum : ∑ T ∈ Supp, (w : ℝ) ^ T.card ≤ D_bound ^ 2 := by
    calc ∑ T ∈ Supp, (w : ℝ) ^ T.card
        ≤ ∑ _T ∈ Supp, D_bound := Finset.sum_le_sum fun T hT => by
          have h1 : (w : ℝ) ^ T.card ≤ ((2 * w : ℕ) : ℝ) ^ T.card := by
            refine pow_le_pow_left₀ (by positivity) ?_ _
            exact_mod_cast (by omega : w ≤ 2 * w)
          exact h1.trans (h2w_le T hT)
      _ = (Supp.card : ℝ) * D_bound := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D_bound * D_bound := mul_le_mul_of_nonneg_right hSupp_card (by linarith)
      _ = D_bound ^ 2 := (sq D_bound).symm
  -- Helper: for each t ∈ range N, define E(t) = {b ∈ B_med | ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M}
  let E : ℕ → Finset ℕ := fun t => B_med.filter (fun b => ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)
  have hS_good_eq : (S_good.card : ℝ) = ∑ t ∈ Finset.range N, if E t = ∅ then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1; congr 1; ext t
    simp only [S_good, E, Finset.mem_filter, Finset.eq_empty_iff_forall_notMem]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h b ⟨hbB, a, ha, hdvd⟩; exact h b hbB a ha hdvd
    · intro h b hbB a ha hdvd; exact h b ⟨hbB, a, ha, hdvd⟩
  -- For each t and j < L, define u j t and l j t
  let u : ℕ → ℕ → ℝ := fun j t =>
    ∑ T ∈ (I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j)),
      if T ⊆ E t then (-1 : ℝ) ^ T.card else 0
  let l : ℕ → ℕ → ℝ := fun j t =>
    ∑ T ∈ (I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j) - 1),
      if T ⊆ E t then (-1 : ℝ) ^ T.card else 0
  have hu_eq : ∀ j ∈ Finset.range L, ∀ t,
      u j t = ∑ T ∈ (E t ∩ I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j)), (-1 : ℝ) ^ T.card := by
    intro j _ t
    dsimp only [u]
    rw [← Finset.sum_filter]
    congr 1; ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
    tauto
  have hl_eq : ∀ j ∈ Finset.range L, ∀ t,
      l j t = ∑ T ∈ (E t ∩ I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j) - 1), (-1 : ℝ) ^ T.card := by
    intro j _ t
    dsimp only [l]
    rw [← Finset.sum_filter]
    congr 1; ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
    tauto
  have hprod_ind : ∀ t, (if E t = ∅ then (1 : ℝ) else 0) =
      ∏ j ∈ Finset.range L, if E t ∩ I j = ∅ then (1 : ℝ) else 0 := by
    intro t
    by_cases hE : E t = ∅
    · simp [hE]
    · simp only [hE, ↓reduceIte]
      obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      have hbB : b ∈ B_med := (Finset.mem_filter.mp hb).1
      obtain ⟨j, hj, hbI⟩ := Finset.mem_biUnion.mp hbB
      symm
      apply Finset.prod_eq_zero hj
      have hne : E t ∩ I j ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨b, Finset.mem_inter.mpr ⟨hb, hbI⟩⟩
      simp [hne]
  -- Expand ∏ j ∈ range L, u j t into ∑ T ∈ Supp, if T ⊆ E t then (-1)^|T| else 0
  have hprod_u : ∀ t, ∏ j ∈ Finset.range L, u j t =
      ∑ T ∈ Supp, if T ⊆ E t then (-1 : ℝ) ^ T.card else 0 := by
    intro t
    dsimp only [u, Supp, B_med]
    exact prod_sum_disjoint_blocks (Finset.range L) I hdisj
      (fun j T => T.card ≤ 2 * (2 + j))
      (fun T => if T ⊆ E t then (-1 : ℝ) ^ T.card else 0)
      (fun T₁ T₂ hd => by
        by_cases h1 : T₁ ⊆ E t <;> by_cases h2 : T₂ ⊆ E t
        · simp [h1, h2, Finset.union_subset_iff, Finset.card_union_of_disjoint hd, pow_add]
        · simp [h1, h2, Finset.union_subset_iff]
        · simp [h1, h2, Finset.union_subset_iff]
        · simp [h1, h2, Finset.union_subset_iff])
      (by simp)
  -- Block main terms M_u j and M_l j
  let V_j : ℕ → ℝ := fun j => ∏ b ∈ I j, (1 - g b)
  let M_u : ℕ → ℝ := fun j =>
    ∑ T ∈ (I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j)), (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)
  let M_l : ℕ → ℝ := fun j =>
    ∑ T ∈ (I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j) - 1), (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)
  have hV_prod : V = ∏ j ∈ Finset.range L, V_j j := by
    dsimp only [V, V_j, B_med, g, w]
    exact Finset.prod_biUnion hdisj
  have hblock : ∀ j ∈ Finset.range L,
      (1 / 2 : ℝ) ≤ V_j j ∧
      V_j j * (1 - 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) ≤ M_u j ∧
      M_u j ≤ V_j j * (1 + 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1)) ∧
      0 ≤ M_u j - M_l j ∧
      M_u j - M_l j ≤ (1 / 20 : ℝ) ^ (2 * (2 + j)) := fun j hj =>
    single_block_main_bounds (I j) g (2 + j) (by omega)
      (fun b _ => by dsimp only [g]; positivity) (hS j hj)
  have hprod_Mu_eq : ∏ j ∈ Finset.range L, M_u j =
      ∑ T ∈ Supp, (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b) := by
    dsimp only [M_u, Supp, B_med]
    exact prod_sum_disjoint_blocks (Finset.range L) I hdisj
      (fun j T => T.card ≤ 2 * (2 + j))
      (fun T => (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b))
      (fun T₁ T₂ hd => by rw [Finset.card_union_of_disjoint hd, Finset.prod_union hd, pow_add]; ring)
      (by simp)
  -- Helper: ∑ t ∈ range N, ∏ j, u j t is within D_bound^2 of N * ∏ j, M_u j
  have hsum_u_approx :
      |(∑ t ∈ Finset.range N, ∏ j ∈ Finset.range L, u j t) - (N : ℝ) * ∏ j ∈ Finset.range L, M_u j| ≤
        D_bound ^ 2 := by
    have hswap : ∑ t ∈ Finset.range N, ∏ j ∈ Finset.range L, u j t =
        ∑ T ∈ Supp, (-1 : ℝ) ^ T.card *
          (((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) := by
      simp_rw [hprod_u]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun T hT => ?_
      have hsub : T ⊆ B_med := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      congr 1; congr 1; congr 1; ext t
      simp only [Finset.mem_filter, E, Finset.subset_iff]
      refine and_congr_right fun _ => ?_
      exact ⟨fun h b hb => (h hb).2,
        fun h b hb => ⟨hsub hb, h b hb⟩⟩
    rw [hswap, hprod_Mu_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      |∑ T ∈ Supp, ((-1 : ℝ) ^ T.card *
            (((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) -
            (N : ℝ) * ((-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)))|
        ≤ ∑ T ∈ Supp, |(-1 : ℝ) ^ T.card *
            (((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) -
            (N : ℝ) * ((-1 : ℝ) ^ T.card * (∏ b ∈ T, g b))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ T ∈ Supp, (w : ℝ) ^ T.card := by
          refine Finset.sum_le_sum fun T hT => ?_
          have hsub : T ⊆ B_med := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
          have hg_prod : ∏ b ∈ T, g b = (w : ℝ) ^ T.card / (∏ b ∈ T, (b : ℝ)) := by
            dsimp only [g]
            rw [Finset.prod_div_distrib, Finset.prod_const]
          have hfact : (-1 : ℝ) ^ T.card *
              (((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) -
              (N : ℝ) * ((-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)) =
              (-1 : ℝ) ^ T.card *
                ((((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) -
                  (N : ℝ) * ((A_n.card : ℝ) ^ T.card / (∏ b ∈ T, (b : ℝ)))) := by
            rw [hg_prod]; dsimp only [w]; ring
          rw [hfact, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          exact abs_card_hit_all_sub_le N n k₀ d₀ M A_n T hAn
            (hB_cop.mono hsub) (fun b hb => hB_gt b (hsub hb)) (fun b hb => hB_cop_s b (hsub hb))
      _ ≤ D_bound ^ 2 := herr_sum
  -- Numeric bounds on ∏ j ∈ range L, M_u j
  have hMu_both := block_bonferroni_mu_bounds L V_j M_u (fun j hj =>
    ⟨(hblock j hj).1, (hblock j hj).2.1, (hblock j hj).2.2.1⟩)
  have hMu_lb : (99 / 100 : ℝ) * V ≤ ∏ j ∈ Finset.range L, M_u j := by
    rw [hV_prod]; exact hMu_both.1
  have hMu_ub : ∏ j ∈ Finset.range L, M_u j ≤ (102 / 100 : ℝ) * V := by
    rw [hV_prod]; exact hMu_both.2
  -- Now prove both the upper bound and the lower bound!
  constructor
  · -- LOWER BOUND
    have hlow_pt : ∀ t ∈ Finset.range N,
        (∏ j ∈ Finset.range L, u j t) -
          ∑ j ∈ Finset.range L, (u j t - l j t) * ∏ i ∈ (Finset.range L).erase j, u i t ≤
        if E t = ∅ then (1 : ℝ) else 0 := by
      intro t _
      rw [hprod_ind t]
      refine prod_lower_of_bounds (Finset.range L)
        (fun j => if E t ∩ I j = ∅ then 1 else 0) (fun j => u j t) (fun j => l j t)
        (fun _ _ => by split_ifs <;> norm_num)
        (fun j hj => by rw [hu_eq j hj t]; exact bonferroni_upper (E t ∩ I j) (2 + j))
        (fun j hj => by rw [hl_eq j hj t]; exact bonferroni_lower (E t ∩ I j) (2 + j) (by omega))
    have hlow_sum : (∑ t ∈ Finset.range N, ∏ j ∈ Finset.range L, u j t) -
        ∑ j ∈ Finset.range L, ∑ t ∈ Finset.range N,
          (u j t - l j t) * ∏ i ∈ (Finset.range L).erase j, u i t ≤ (S_good.card : ℝ) := by
      rw [hS_good_eq, Finset.sum_comm (s := Finset.range L), ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum hlow_pt
    -- Expand each j-term in the correction sum
    let Supp_j : ℕ → Finset (Finset ℕ) := fun j =>
      Supp.filter (fun T => (T ∩ I j).card = 2 * (2 + j))
    have hcorr_expand : ∀ j ∈ Finset.range L, ∀ t,
        (u j t - l j t) * ∏ i ∈ (Finset.range L).erase j, u i t =
          ∑ T ∈ Supp_j j, if T ⊆ E t then (-1 : ℝ) ^ T.card else 0 := by
      intro j hj t
      have hul_eq : u j t - l j t =
          ∑ T ∈ (I j).powerset.filter (fun T => T.card = 2 * (2 + j)),
            if T ⊆ E t then (-1 : ℝ) ^ T.card else 0 := by
        dsimp only [u, l]
        have hpart : (I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j)) =
            (I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j) - 1) ∪
            (I j).powerset.filter (fun T => T.card = 2 * (2 + j)) := by
          ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union]
          constructor
          · intro ⟨h1, h2⟩
            by_cases h3 : T.card = 2 * (2 + j)
            · exact Or.inr ⟨h1, h3⟩
            · exact Or.inl ⟨h1, by omega⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
        have hd : Disjoint ((I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j) - 1))
            ((I j).powerset.filter (fun T => T.card = 2 * (2 + j))) := by
          rw [Finset.disjoint_left]; intro T h1 h2
          have := (Finset.mem_filter.mp h1).2
          have := (Finset.mem_filter.mp h2).2
          omega
        rw [hpart, Finset.sum_union hd, add_sub_cancel_left]
      have hprod_eq : (u j t - l j t) * ∏ i ∈ (Finset.range L).erase j, u i t =
          ∏ i ∈ Finset.range L, ∑ T ∈ (I i).powerset.filter
            (fun T => if i = j then T.card = 2 * (2 + i) else T.card ≤ 2 * (2 + i)),
            if T ⊆ E t then (-1 : ℝ) ^ T.card else 0 := by
        rw [← Finset.mul_prod_erase (Finset.range L) _ hj]
        congr 1
        · rw [hul_eq]; simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          have hne : i ≠ j := Finset.ne_of_mem_erase hi
          simp [hne, u]
      rw [hprod_eq]
      have hexp := prod_sum_disjoint_blocks (Finset.range L) I hdisj
        (fun i T => if i = j then T.card = 2 * (2 + i) else T.card ≤ 2 * (2 + i))
        (fun T => if T ⊆ E t then (-1 : ℝ) ^ T.card else 0)
        (fun T₁ T₂ hd => by
          by_cases h1 : T₁ ⊆ E t <;> by_cases h2 : T₂ ⊆ E t
          · simp [h1, h2, Finset.union_subset_iff, Finset.card_union_of_disjoint hd, pow_add]
          · simp [h1, h2, Finset.union_subset_iff]
          · simp [h1, h2, Finset.union_subset_iff]
          · simp [h1, h2, Finset.union_subset_iff])
        (by simp)
      trans (∑ T ∈ ((Finset.range L).biUnion I).powerset.filter
        (fun T => ∀ i ∈ Finset.range L, if i = j then (T ∩ I i).card = 2 * (2 + i) else (T ∩ I i).card ≤ 2 * (2 + i)),
        if T ⊆ E t then (-1 : ℝ) ^ T.card else 0)
      · exact hexp
      · congr 1; ext T
        simp only [Supp_j, Supp, B_med, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro ⟨hsub, hall⟩
          refine ⟨⟨hsub, fun i hi => ?_⟩, ?_⟩
          · have := hall i hi
            by_cases hij : i = j
            · subst hij; simp only [↓reduceIte] at this; omega
            · simpa [hij] using this
          · have := hall j hj; simpa using this
        · intro ⟨⟨hsub, hall⟩, heq⟩
          refine ⟨hsub, fun i hi => ?_⟩
          by_cases hij : i = j
          · subst hij; simpa using heq
          · simpa [hij] using hall i hi
    have hcorr_main : ∀ j ∈ Finset.range L,
        (M_u j - M_l j) * ∏ i ∈ (Finset.range L).erase j, M_u i =
          ∑ T ∈ Supp_j j, (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b) := by
      intro j hj
      have hul_eq : M_u j - M_l j =
          ∑ T ∈ (I j).powerset.filter (fun T => T.card = 2 * (2 + j)),
            (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b) := by
        dsimp only [M_u, M_l]
        have hpart : (I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j)) =
            (I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j) - 1) ∪
            (I j).powerset.filter (fun T => T.card = 2 * (2 + j)) := by
          ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union]
          constructor
          · intro ⟨h1, h2⟩
            by_cases h3 : T.card = 2 * (2 + j)
            · exact Or.inr ⟨h1, h3⟩
            · exact Or.inl ⟨h1, by omega⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
        have hd : Disjoint ((I j).powerset.filter (fun T => T.card ≤ 2 * (2 + j) - 1))
            ((I j).powerset.filter (fun T => T.card = 2 * (2 + j))) := by
          rw [Finset.disjoint_left]; intro T h1 h2
          have := (Finset.mem_filter.mp h1).2
          have := (Finset.mem_filter.mp h2).2
          omega
        rw [hpart, Finset.sum_union hd, add_sub_cancel_left]
      have hprod_eq : (M_u j - M_l j) * ∏ i ∈ (Finset.range L).erase j, M_u i =
          ∏ i ∈ Finset.range L, ∑ T ∈ (I i).powerset.filter
            (fun T => if i = j then T.card = 2 * (2 + i) else T.card ≤ 2 * (2 + i)),
            (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b) := by
        rw [← Finset.mul_prod_erase (Finset.range L) _ hj]
        congr 1
        · rw [hul_eq]; simp
        · refine Finset.prod_congr rfl fun i hi => ?_
          have hne : i ≠ j := Finset.ne_of_mem_erase hi
          simp [hne, M_u]
      rw [hprod_eq]
      have hexp := prod_sum_disjoint_blocks (Finset.range L) I hdisj
        (fun i T => if i = j then T.card = 2 * (2 + i) else T.card ≤ 2 * (2 + i))
        (fun T => (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b))
        (fun T₁ T₂ hd => by rw [Finset.card_union_of_disjoint hd, Finset.prod_union hd, pow_add]; ring)
        (by simp)
      trans (∑ T ∈ ((Finset.range L).biUnion I).powerset.filter
        (fun T => ∀ i ∈ Finset.range L, if i = j then (T ∩ I i).card = 2 * (2 + i) else (T ∩ I i).card ≤ 2 * (2 + i)),
        (-1 : ℝ) ^ T.card * (∏ b ∈ T, g b))
      · exact hexp
      · congr 1; ext T
        simp only [Supp_j, Supp, B_med, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro ⟨hsub, hall⟩
          refine ⟨⟨hsub, fun i hi => ?_⟩, ?_⟩
          · have := hall i hi
            by_cases hij : i = j
            · subst hij; simp only [↓reduceIte] at this; omega
            · simpa [hij] using this
          · have := hall j hj; simpa using this
        · intro ⟨⟨hsub, hall⟩, heq⟩
          refine ⟨hsub, fun i hi => ?_⟩
          by_cases hij : i = j
          · subst hij; simpa using heq
          · simpa [hij] using hall i hi
    -- Bound ∑ j ∈ range L, ∑ t ∈ range N, (u j t - l j t) * ∏_{i ≠ j} u i t
    have hcorr_bound :
        ∑ j ∈ Finset.range L, ∑ t ∈ Finset.range N,
          (u j t - l j t) * ∏ i ∈ (Finset.range L).erase j, u i t ≤
        (1 / 100 : ℝ) * (N : ℝ) * V + D_bound ^ 2 := by
      have hterm_j : ∀ j ∈ Finset.range L,
          ∑ t ∈ Finset.range N, (u j t - l j t) * ∏ i ∈ (Finset.range L).erase j, u i t ≤
            (N : ℝ) * ((M_u j - M_l j) * ∏ i ∈ (Finset.range L).erase j, M_u i) +
            ∑ T ∈ Supp_j j, (w : ℝ) ^ T.card := by
        intro j hj
        have hswap : ∑ t ∈ Finset.range N, (u j t - l j t) * ∏ i ∈ (Finset.range L).erase j, u i t =
            ∑ T ∈ Supp_j j, (-1 : ℝ) ^ T.card *
              (((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) := by
          simp_rw [hcorr_expand j hj]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun T hT => ?_
          have hsub : T ⊆ B_med := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).1
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          congr 1; congr 1; congr 1; ext t
          simp only [Finset.mem_filter, E, Finset.subset_iff]
          refine and_congr_right fun _ => ?_
          exact ⟨fun h b hb => (h hb).2,
            fun h b hb => ⟨hsub hb, h b hb⟩⟩
        rw [hswap, hcorr_main j hj, Finset.mul_sum]
        have hdiff : |(∑ T ∈ Supp_j j, (-1 : ℝ) ^ T.card *
              (((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ)) -
              ∑ T ∈ Supp_j j, (N : ℝ) * ((-1 : ℝ) ^ T.card * (∏ b ∈ T, g b))| ≤
            ∑ T ∈ Supp_j j, (w : ℝ) ^ T.card := by
          rw [← Finset.sum_sub_distrib]
          calc |∑ T ∈ Supp_j j, _|
              ≤ ∑ T ∈ Supp_j j, |(-1 : ℝ) ^ T.card *
                  (((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) -
                  (N : ℝ) * ((-1 : ℝ) ^ T.card * (∏ b ∈ T, g b))| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ T ∈ Supp_j j, (w : ℝ) ^ T.card := by
                refine Finset.sum_le_sum fun T hT => ?_
                have hsub : T ⊆ B_med := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).1
                have hg_prod : ∏ b ∈ T, g b = (w : ℝ) ^ T.card / (∏ b ∈ T, (b : ℝ)) := by
                  dsimp only [g]; rw [Finset.prod_div_distrib, Finset.prod_const]
                have hfact : (-1 : ℝ) ^ T.card *
                    (((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) -
                    (N : ℝ) * ((-1 : ℝ) ^ T.card * (∏ b ∈ T, g b)) =
                    (-1 : ℝ) ^ T.card *
                      ((((Finset.range N).filter (fun t => ∀ b ∈ T, ∃ a ∈ A_n, b ∣ a + (k₀ + t * d₀) * M)).card : ℝ) -
                        (N : ℝ) * ((A_n.card : ℝ) ^ T.card / (∏ b ∈ T, (b : ℝ)))) := by
                  rw [hg_prod]; dsimp only [w]; ring
                rw [hfact, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
                exact abs_card_hit_all_sub_le N n k₀ d₀ M A_n T hAn
                  (hB_cop.mono hsub) (fun b hb => hB_gt b (hsub hb)) (fun b hb => hB_cop_s b (hsub hb))
        linarith [(abs_le.mp hdiff).2]
      -- Main part of correction sum ≤ (1/100) * N * V
      have hmain_corr : ∑ j ∈ Finset.range L, (M_u j - M_l j) * ∏ i ∈ (Finset.range L).erase j, M_u i ≤
          (1 / 100 : ℝ) * V := by
        have hV_nn : 0 ≤ V := by
          rw [hV_prod]; exact Finset.prod_nonneg fun j hj => by linarith [(hblock j hj).1]
        have hMu_pos : ∀ j ∈ Finset.range L, (1 / 4 : ℝ) ≤ M_u j := fun j hj => by
          have hb := hblock j hj
          have hsmall : 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) ≤ 1 / 2 := by
            calc 4 * (1 / 20 : ℝ) ^ (2 * (2 + j) + 1) ≤ 4 * (1 / 20 : ℝ) ^ 1 :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
              _ ≤ 1 / 2 := by norm_num
          nlinarith [hb.1, hb.2.1]
        have hprod_er : ∀ j ∈ Finset.range L, ∏ i ∈ (Finset.range L).erase j, M_u i ≤ 5 * V := by
          intro j hj
          have hmul : M_u j * ∏ i ∈ (Finset.range L).erase j, M_u i = ∏ i ∈ Finset.range L, M_u i :=
            Finset.mul_prod_erase (Finset.range L) M_u hj
          have h1 : (1 / 4 : ℝ) * ∏ i ∈ (Finset.range L).erase j, M_u i ≤ (102 / 100 : ℝ) * V := by
            have hnn : 0 ≤ ∏ i ∈ (Finset.range L).erase j, M_u i :=
              Finset.prod_nonneg fun i hi => by linarith [hMu_pos i (Finset.mem_of_mem_erase hi)]
            calc (1 / 4 : ℝ) * ∏ i ∈ (Finset.range L).erase j, M_u i
                ≤ M_u j * ∏ i ∈ (Finset.range L).erase j, M_u i :=
                  mul_le_mul_of_nonneg_right (hMu_pos j hj) hnn
              _ = ∏ i ∈ Finset.range L, M_u i := hmul
              _ ≤ (102 / 100 : ℝ) * V := hMu_ub
          linarith
        calc ∑ j ∈ Finset.range L, (M_u j - M_l j) * ∏ i ∈ (Finset.range L).erase j, M_u i
            ≤ ∑ j ∈ Finset.range L, (1 / 20 : ℝ) ^ (2 * (2 + j)) * (5 * V) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hb := hblock j hj
              have hnn : 0 ≤ ∏ i ∈ (Finset.range L).erase j, M_u i :=
                Finset.prod_nonneg fun i hi => by linarith [hMu_pos i (Finset.mem_of_mem_erase hi)]
              exact mul_le_mul hb.2.2.2.2 (hprod_er j hj) hnn (by positivity)
          _ = (5 * (1 / 20 : ℝ) ^ 4 * ∑ j ∈ Finset.range L, (1 / 400 : ℝ) ^ j) * V := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [show 2 * (2 + j) = 4 + 2 * j by omega, pow_add, pow_mul]
              norm_num; ring
          _ ≤ (1 / 100 : ℝ) * V := by
              refine mul_le_mul_of_nonneg_right ?_ hV_nn
              rw [geom_sum_eq (by norm_num)]
              have hnn : (0 : ℝ) ≤ (1 / 400 : ℝ) ^ L := by positivity
              have hdiv : ((1 / 400 : ℝ) ^ L - 1) / (1 / 400 - 1) =
                  (1 - (1 / 400 : ℝ) ^ L) * (400 / 399) := by ring
              rw [hdiv]
              linarith
      -- Error part of correction sum ≤ D_bound^2
      have herr_corr : ∑ j ∈ Finset.range L, ∑ T ∈ Supp_j j, (w : ℝ) ^ T.card ≤ D_bound ^ 2 := by
        have hswap : ∑ j ∈ Finset.range L, ∑ T ∈ Supp_j j, (w : ℝ) ^ T.card =
            ∑ T ∈ Supp, (((Finset.range L).filter (fun j => (T ∩ I j).card = 2 * (2 + j))).card : ℝ) *
              (w : ℝ) ^ T.card := by
          simp_rw [Supp_j, Finset.sum_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [hswap]
        calc ∑ T ∈ Supp, (((Finset.range L).filter (fun j => (T ∩ I j).card = 2 * (2 + j))).card : ℝ) *
                (w : ℝ) ^ T.card
            ≤ ∑ _T ∈ Supp, D_bound := by
              refine Finset.sum_le_sum fun T hT => ?_
              let J_T := (Finset.range L).filter (fun j => (T ∩ I j).card = 2 * (2 + j))
              have hJ_le_T : J_T.card ≤ T.card := by
                have hbi : J_T.biUnion (fun j => T ∩ I j) ⊆ T := by
                  intro b hb; exact (Finset.mem_inter.mp (Finset.mem_biUnion.mp hb).choose_spec.2).1
                have hdisj_T : Set.PairwiseDisjoint (J_T : Set ℕ) (fun j => T ∩ I j) := by
                  intro i hi j hj hij
                  dsimp only [Function.onFun]
                  exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
                    (hdisj (Finset.mem_coe.mpr (Finset.mem_filter.mp hi).1)
                      (Finset.mem_coe.mpr (Finset.mem_filter.mp hj).1) hij)
                have hcard1 : (J_T.biUnion (fun j => T ∩ I j)).card ≤ T.card := Finset.card_le_card hbi
                rw [Finset.card_biUnion hdisj_T] at hcard1
                have hcard2 : J_T.card ≤ ∑ j ∈ J_T, (T ∩ I j).card := by
                  calc J_T.card = ∑ _j ∈ J_T, 1 := Finset.card_eq_sum_ones J_T
                    _ ≤ ∑ j ∈ J_T, (T ∩ I j).card := Finset.sum_le_sum fun j hj => by
                        have h4 : (T ∩ I j).card = 2 * (2 + j) := (Finset.mem_filter.mp hj).2
                        omega
                exact hcard2.trans hcard1
              have hJ_le_2T : (J_T.card : ℝ) ≤ (2 : ℝ) ^ T.card := by
                have : J_T.card ≤ 2 ^ T.card := hJ_le_T.trans (Nat.lt_two_pow_self.le)
                exact_mod_cast this
              calc (J_T.card : ℝ) * (w : ℝ) ^ T.card
                  ≤ (2 : ℝ) ^ T.card * (w : ℝ) ^ T.card := mul_le_mul_of_nonneg_right hJ_le_2T (by positivity)
                _ = ((2 * w : ℕ) : ℝ) ^ T.card := by push_cast; rw [← mul_pow]
                _ ≤ D_bound := h2w_le T hT
          _ = (Supp.card : ℝ) * D_bound := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ D_bound * D_bound := mul_le_mul_of_nonneg_right hSupp_card (by linarith)
          _ = D_bound ^ 2 := (sq D_bound).symm
      calc ∑ j ∈ Finset.range L, ∑ t ∈ Finset.range N,
              (u j t - l j t) * ∏ i ∈ (Finset.range L).erase j, u i t
          ≤ ∑ j ∈ Finset.range L, ((N : ℝ) * ((M_u j - M_l j) * ∏ i ∈ (Finset.range L).erase j, M_u i) +
              ∑ T ∈ Supp_j j, (w : ℝ) ^ T.card) := Finset.sum_le_sum hterm_j
        _ = (N : ℝ) * (∑ j ∈ Finset.range L, (M_u j - M_l j) * ∏ i ∈ (Finset.range L).erase j, M_u i) +
              ∑ j ∈ Finset.range L, ∑ T ∈ Supp_j j, (w : ℝ) ^ T.card := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ (N : ℝ) * ((1 / 100 : ℝ) * V) + D_bound ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hmain_corr (by positivity)) herr_corr
        _ = (1 / 100 : ℝ) * (N : ℝ) * V + D_bound ^ 2 := by ring
    have hu_low := (abs_le.mp hsum_u_approx).1
    have hNu : (99 / 100 : ℝ) * (N : ℝ) * V ≤ (N : ℝ) * ∏ j ∈ Finset.range L, M_u j := by
      calc (99 / 100 : ℝ) * (N : ℝ) * V = (N : ℝ) * ((99 / 100 : ℝ) * V) := by ring
        _ ≤ (N : ℝ) * ∏ j ∈ Finset.range L, M_u j := mul_le_mul_of_nonneg_left hMu_lb (Nat.cast_nonneg N)
    linarith
  · -- UPPER BOUND
    have hup_pt : ∀ t ∈ Finset.range N,
        (if E t = ∅ then (1 : ℝ) else 0) ≤ ∏ j ∈ Finset.range L, u j t := by
      intro t _
      rw [hprod_ind t]
      refine Finset.prod_le_prod (fun _ _ => by split_ifs <;> norm_num) fun j hj => ?_
      rw [hu_eq j hj t]; exact bonferroni_upper (E t ∩ I j) (2 + j)
    have hup_sum : (S_good.card : ℝ) ≤ ∑ t ∈ Finset.range N, ∏ j ∈ Finset.range L, u j t := by
      rw [hS_good_eq]; exact Finset.sum_le_sum hup_pt
    have hu_hi := (abs_le.mp hsum_u_approx).2
    have hNu : (N : ℝ) * ∏ j ∈ Finset.range L, M_u j ≤ (102 / 100 : ℝ) * (N : ℝ) * V := by
      calc (N : ℝ) * ∏ j ∈ Finset.range L, M_u j
          ≤ (N : ℝ) * ((102 / 100 : ℝ) * V) := mul_le_mul_of_nonneg_left hMu_ub (Nat.cast_nonneg N)
        _ = (102 / 100 : ℝ) * (N : ℝ) * V := by ring
    linarith

/- ---------------------------------------------------------------------------
   Part 5: Geometric Block Partition + Sieve Wrapper + Main Theorem
   --------------------------------------------------------------------------- -/

/-- Weighted geometric series bound: for `0 ≤ c < 1`,
`∑ j ∈ range L, (4 + 2 * j) * c^j ≤ 4 / (1 - c) + 2 / (1 - c)^2`. -/
private lemma sum_linear_geom_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (L : ℕ) :
    ∑ j ∈ Finset.range L, ((4 + 2 * j : ℕ) : ℝ) * c ^ j ≤
      4 / (1 - c) + 2 / (1 - c) ^ 2 := by
  have h1c : 0 < 1 - c := by linarith
  have hgeom : ∑ j ∈ Finset.range L, c ^ j ≤ 1 / (1 - c) := by
    rw [geom_sum_eq hc1.ne]
    have hnn : 0 ≤ c ^ L := pow_nonneg hc0 L
    have hne : c - 1 ≠ 0 := by linarith
    have heq : (c ^ L - 1) / (c - 1) = (1 - c ^ L) / (1 - c) := by field_simp [hne, h1c.ne']; ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) h1c.le
  -- Bound ∑ j ∈ range L, j * c^j ≤ 1 / (1 - c)^2 via (1 - c) * ∑ j c^j ≤ ∑ c^j
  have hlin : ∑ j ∈ Finset.range L, (j : ℝ) * c ^ j ≤ 1 / (1 - c) ^ 2 := by
    have hid_all : ∀ m : ℕ, (1 - c) * ∑ j ∈ Finset.range (m + 1), (j : ℝ) * c ^ j =
        (∑ j ∈ Finset.range m, c ^ (j + 1)) - (m : ℝ) * c ^ (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ (fun j => (j : ℝ) * c ^ j), mul_add, ih,
          Finset.sum_range_succ (fun j => c ^ (j + 1))]
        push_cast; rw [pow_succ c (k + 1), pow_succ c k]; ring
    have hmul : (1 - c) * ∑ j ∈ Finset.range L, (j : ℝ) * c ^ j ≤ ∑ j ∈ Finset.range L, c ^ j := by
      cases L with
      | zero => simp
      | succ m =>
        rw [hid_all m]
        have h1 : ∑ j ∈ Finset.range m, c ^ (j + 1) ≤ ∑ j ∈ Finset.range (m + 1), c ^ j := by
          rw [Finset.sum_range_succ']
          have h0 : (0 : ℝ) ≤ c ^ 0 := by simp
          linarith
        have h2 : 0 ≤ (m : ℝ) * c ^ (m + 1) := mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hc0 _)
        linarith
    calc ∑ j ∈ Finset.range L, (j : ℝ) * c ^ j
        ≤ (∑ j ∈ Finset.range L, c ^ j) / (1 - c) := (le_div_iff₀' h1c).mpr hmul
      _ ≤ (1 / (1 - c)) / (1 - c) := div_le_div_of_nonneg_right hgeom h1c.le
      _ = 1 / (1 - c) ^ 2 := by rw [div_div, sq]
  calc ∑ j ∈ Finset.range L, ((4 + 2 * j : ℕ) : ℝ) * c ^ j
      = 4 * ∑ j ∈ Finset.range L, c ^ j + 2 * ∑ j ∈ Finset.range L, (j : ℝ) * c ^ j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by push_cast; ring
    _ ≤ 4 * (1 / (1 - c)) + 2 * (1 / (1 - c) ^ 2) := by linarith
    _ = 4 / (1 - c) + 2 / (1 - c) ^ 2 := by ring

/-- Geometric block partition of `B' ∩ (y, z]` with `c = 1 - 1 / (200 * n)`:
each block has reciprocal sum `≤ 1 / 20`, and every supported `T` has product `≤ z ^ s₀`. -/
private lemma block_partition_bounds (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (n y z : ℕ) (A_n : Finset ℕ)
    (hn1 : 1 ≤ n) (hAn : A_n ⊆ Finset.Icc 1 n)
    (hy : 2 * n + 2 ≤ y) (hy16 : 16 ≤ y)
    (hy_exp : Real.exp (2000 * (n : ℝ)) ≤ (y : ℝ))
    (hyz : y ≤ z)
    (hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ)) :
    let s₀ : ℕ := 800 * n + 80000 * n ^ 2 + 1
    ∃ (L : ℕ) (I : ℕ → Finset ℕ),
      Set.PairwiseDisjoint (Finset.range L : Set ℕ) I ∧
      (Finset.range L).biUnion I = (Finset.Ioc y z).filter (· ∈ B') ∧
      (∀ j ∈ Finset.range L, ∑ b ∈ I j, (A_n.card : ℝ) / (b : ℝ) ≤ 1 / 20) ∧
      (∀ T ∈ ((Finset.range L).biUnion I).powerset.filter
          (fun T => ∀ j ∈ Finset.range L, (T ∩ I j).card ≤ 2 * (2 + j)),
        ∏ b ∈ T, (b : ℝ) ≤ (z : ℝ) ^ s₀) := by
  intro s₀
  let c : ℝ := 1 - 1 / (200 * (n : ℝ))
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hc_pos : 0 < c := by
    dsimp only [c]
    have : 1 / (200 * (n : ℝ)) ≤ 1 / 200 := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    linarith
  have hc_lt1 : c < 1 := by dsimp only [c]; linarith [show (0 : ℝ) < 1 / (200 * (n : ℝ)) by positivity]
  have h1c : 1 - c = 1 / (200 * (n : ℝ)) := by dsimp only [c]; ring
  have hz_gt1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlogz_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt1
  -- Pick L so that z ^ (c ^ L) ≤ y
  have hlim : Tendsto (fun L : ℕ => c ^ L * Real.log (z : ℝ)) atTop (nhds 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hc_pos.le hc_lt1).mul_const (Real.log (z : ℝ))
    simpa using h1
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  obtain ⟨L, hL⟩ := (hlim.eventually (gt_mem_nhds hlogy_pos)).exists
  have hzL_le_y : (z : ℝ) ^ (c ^ L) ≤ (y : ℝ) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    calc Real.exp (Real.log (z : ℝ) * c ^ L) ≤ Real.exp (Real.log (y : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = (y : ℝ) := Real.exp_log (by exact_mod_cast (by omega : 0 < y))
  let B_med := (Finset.Ioc y z).filter (· ∈ B')
  let I : ℕ → Finset ℕ := fun j =>
    B_med.filter (fun p => (z : ℝ) ^ (c ^ (j + 1)) < (p : ℝ) ∧ (p : ℝ) ≤ (z : ℝ) ^ (c ^ j))
  have hdisj : Set.PairwiseDisjoint (Finset.range L : Set ℕ) I := by
    intro i _ j _ hij
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]
    intro p hpi_m hpj_m
    have h1 := (Finset.mem_filter.mp hpi_m).2
    have h2 := (Finset.mem_filter.mp hpj_m).2
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hpow : c ^ j ≤ c ^ (i + 1) := pow_le_pow_of_le_one hc_pos.le hc_lt1.le hlt
      have hzp : (z : ℝ) ^ (c ^ j) ≤ (z : ℝ) ^ (c ^ (i + 1)) :=
        Real.rpow_le_rpow_of_exponent_le hz_gt1.le hpow
      linarith
    · have hpow : c ^ i ≤ c ^ (j + 1) := pow_le_pow_of_le_one hc_pos.le hc_lt1.le hgt
      have hzp : (z : ℝ) ^ (c ^ i) ≤ (z : ℝ) ^ (c ^ (j + 1)) :=
        Real.rpow_le_rpow_of_exponent_le hz_gt1.le hpow
      linarith
  refine ⟨L, I, hdisj, ?_, ?_, ?_⟩
  · -- Covering B_med
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_range, I, Finset.mem_filter]
    constructor
    · rintro ⟨_, _, hp, _, _⟩; exact Finset.mem_filter.mp hp
    · intro hp
      have hp_ioc := Finset.mem_Ioc.mp hp.1
      have hpB : p ∈ B_med := Finset.mem_filter.mpr hp
      have hp_gt : (z : ℝ) ^ (c ^ L) < (p : ℝ) := lt_of_le_of_lt hzL_le_y (by exact_mod_cast hp_ioc.1)
      have hp_le : (p : ℝ) ≤ (z : ℝ) ^ (c ^ 0) := by simpa using (by exact_mod_cast hp_ioc.2 : (p : ℝ) ≤ (z : ℝ))
      -- Find least j < L with (z : ℝ) ^ (c ^ (j + 1)) < (p : ℝ)
      have hex : ∃ j < L, (z : ℝ) ^ (c ^ (j + 1)) < (p : ℝ) ∧ (p : ℝ) ≤ (z : ℝ) ^ (c ^ j) := by
        have hS : (Finset.range L).filter (fun j => (z : ℝ) ^ (c ^ (j + 1)) < (p : ℝ)) |>.Nonempty := by
          have hL_pos : 0 < L := by
            by_contra h0; push Not at h0
            have hL0 : L = 0 := by omega
            subst hL0; simp at hp_gt; linarith
          exact ⟨L - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rwa [Nat.sub_add_cancel hL_pos]⟩⟩
        let j := ((Finset.range L).filter (fun j => (z : ℝ) ^ (c ^ (j + 1)) < (p : ℝ))).min' hS
        have hj_mem := Finset.min'_mem _ hS
        have hj_lt : j < L := Finset.mem_range.mp (Finset.mem_filter.mp hj_mem).1
        have hj_gt : (z : ℝ) ^ (c ^ (j + 1)) < (p : ℝ) := (Finset.mem_filter.mp hj_mem).2
        refine ⟨j, hj_lt, hj_gt, ?_⟩
        by_cases hj0 : j = 0
        · rw [hj0]; exact hp_le
        · by_contra hnot; push Not at hnot
          have hprev : j - 1 ∈ (Finset.range L).filter (fun j => (z : ℝ) ^ (c ^ (j + 1)) < (p : ℝ)) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rwa [Nat.sub_add_cancel (by omega)]⟩
          have := Finset.min'_le _ (j - 1) hprev
          omega
      obtain ⟨j, hjL, h1, h2⟩ := hex
      exact ⟨j, hjL, hpB, h1, h2⟩
  · -- Each block has ∑_{b ∈ I j} w / b ≤ 1 / 20
    intro j _
    by_cases hIe : I j = ∅
    · rw [hIe, Finset.sum_empty]; norm_num
    · have hw_le_n : A_n.card ≤ n := by
        have := Finset.card_le_card hAn; rw [Nat.card_Icc] at this; omega
      let a_j := max y ⌊(z : ℝ) ^ (c ^ (j + 1))⌋₊
      let b_j := ⌊(z : ℝ) ^ (c ^ j)⌋₊
      have hsub_j : I j ⊆ (Finset.Ioc a_j b_j).filter (· ∈ B') := by
        intro p hp
        have hp_f := Finset.mem_filter.mp hp
        have hp_B := Finset.mem_filter.mp hp_f.1
        have hp_ioc := Finset.mem_Ioc.mp hp_B.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, Nat.le_floor hp_f.2.2⟩, hp_B.2⟩
        rw [max_lt_iff]
        exact ⟨hp_ioc.1, Nat.floor_lt' (by omega) |>.mpr hp_f.2.1⟩
      have hab : a_j ≤ b_j := by
        obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hIe
        have := Finset.mem_Ioc.mp (Finset.mem_filter.mp (hsub_j hp)).1
        omega
      have hlogy_ge : 2000 * (n : ℝ) ≤ Real.log (y : ℝ) := by
        have := Real.log_le_log (Real.exp_pos _) hy_exp
        rwa [Real.log_exp] at this
      have ha_ge_y : y ≤ a_j := le_max_left _ _
      have hb_ge_y : y ≤ b_j := ha_ge_y.trans hab
      have hsum_inv := sum_inv_coprime_Ioc_le B' hB' hge2 a_j b_j (by omega) hab
        (fun k hk => hpi k (ha_ge_y.trans hk))
      have hlog_ratio : Real.log (Real.log (b_j : ℝ) / Real.log (a_j : ℝ)) ≤ 11 / (1000 * (n : ℝ)) := by
        have hlogb_le : Real.log (b_j : ℝ) ≤ c ^ j * Real.log (z : ℝ) := by
          have h1 : (b_j : ℝ) ≤ (z : ℝ) ^ (c ^ j) := Nat.floor_le (by positivity)
          have h2 := Real.log_le_log (by exact_mod_cast (by omega : 0 < b_j)) h1
          rwa [Real.log_rpow (by linarith)] at h2
        have hloga_ge_y : 2000 * (n : ℝ) ≤ Real.log (a_j : ℝ) :=
          hlogy_ge.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast ha_ge_y))
        have hloga_ge_pow : c ^ (j + 1) * Real.log (z : ℝ) - 1 ≤ Real.log (a_j : ℝ) := by
          have haj_ge : (z : ℝ) ^ (c ^ (j + 1)) / 2 ≤ (a_j : ℝ) := by
            by_cases hle : (z : ℝ) ^ (c ^ (j + 1)) ≤ (y : ℝ)
            · have : (y : ℝ) ≤ (a_j : ℝ) := by exact_mod_cast ha_ge_y
              linarith [Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < (z : ℝ)) (c ^ (j + 1))]
            · push Not at hle
              have hfl : (z : ℝ) ^ (c ^ (j + 1)) - 1 < (⌊(z : ℝ) ^ (c ^ (j + 1))⌋₊ : ℝ) := Nat.sub_one_lt_floor _
              have hle_a : (⌊(z : ℝ) ^ (c ^ (j + 1))⌋₊ : ℝ) ≤ (a_j : ℝ) := by exact_mod_cast le_max_right y _
              have hyR : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy16
              linarith
          have h1 := Real.log_le_log (by positivity) haj_ge
          rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow (by linarith)] at h1
          linarith [Real.log_two_lt_d9]
        have hratio_le : Real.log (b_j : ℝ) / Real.log (a_j : ℝ) ≤ (1 / c) * (1 + 1 / (2000 * (n : ℝ))) := by
          rw [div_le_iff₀ (by linarith)]
          have h1 : c ^ (j + 1) * Real.log (z : ℝ) ≤ Real.log (a_j : ℝ) + 1 := by linarith
          have h2 : c ^ j * Real.log (z : ℝ) ≤ (1 / c) * (Real.log (a_j : ℝ) + 1) := by
            rw [pow_succ'] at h1
            have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 / c by positivity)
            have hcancel : (1 / c) * (c * c ^ j * Real.log (z : ℝ)) = c ^ j * Real.log (z : ℝ) := by
              field_simp [hc_pos.ne']
            rwa [hcancel] at this
          have h3 : (1 : ℝ) ≤ Real.log (a_j : ℝ) / (2000 * (n : ℝ)) :=
            (one_le_div (by positivity)).mpr hloga_ge_y
          have h4 : Real.log (a_j : ℝ) + 1 ≤ (1 + 1 / (2000 * (n : ℝ))) * Real.log (a_j : ℝ) := by
            have : Real.log (a_j : ℝ) / (2000 * (n : ℝ)) = (1 / (2000 * (n : ℝ))) * Real.log (a_j : ℝ) := by ring
            linarith
          calc Real.log (b_j : ℝ) ≤ c ^ j * Real.log (z : ℝ) := hlogb_le
            _ ≤ (1 / c) * (Real.log (a_j : ℝ) + 1) := h2
            _ ≤ (1 / c) * ((1 + 1 / (2000 * (n : ℝ))) * Real.log (a_j : ℝ)) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
            _ = (1 / c) * (1 + 1 / (2000 * (n : ℝ))) * Real.log (a_j : ℝ) := by ring
        have hlog1c : Real.log (1 / c) ≤ 1 / (100 * (n : ℝ)) := by
          have hle : 1 / c ≤ Real.exp (1 / (100 * (n : ℝ))) := by
            have hx : 1 / (200 * (n : ℝ)) ≤ 1 / 2 := by
              calc 1 / (200 * (n : ℝ)) ≤ 1 / 200 := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
                _ ≤ 1 / 2 := by norm_num
            have h1 := exp_neg_two_mul_le_one_sub (1 / (200 * (n : ℝ))) (by positivity) hx
            rw [show -2 * (1 / (200 * (n : ℝ))) = -(1 / (100 * (n : ℝ))) by ring, Real.exp_neg] at h1
            have hinv : (Real.exp (1 / (100 * (n : ℝ))))⁻¹ ≤ c := h1
            rw [one_div]
            have := inv_anti₀ (inv_pos.mpr (Real.exp_pos _)) hinv
            rwa [inv_inv] at this
          calc Real.log (1 / c) ≤ Real.log (Real.exp (1 / (100 * (n : ℝ)))) :=
                Real.log_le_log (by positivity) hle
            _ = 1 / (100 * (n : ℝ)) := Real.log_exp _
        have hlog_add : Real.log (1 + 1 / (2000 * (n : ℝ))) ≤ 1 / (2000 * (n : ℝ)) := by
          linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (2000 * (n : ℝ)) by positivity)]
        have hlogb_pos : 0 < Real.log (b_j : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < b_j))
        have hloga_pos : 0 < Real.log (a_j : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < a_j))
        calc Real.log (Real.log (b_j : ℝ) / Real.log (a_j : ℝ))
            ≤ Real.log ((1 / c) * (1 + 1 / (2000 * (n : ℝ)))) :=
              Real.log_le_log (div_pos hlogb_pos hloga_pos) hratio_le
          _ = Real.log (1 / c) + Real.log (1 + 1 / (2000 * (n : ℝ))) :=
              Real.log_mul (by positivity) (by positivity)
          _ ≤ 1 / (100 * (n : ℝ)) + 1 / (2000 * (n : ℝ)) := add_le_add hlog1c hlog_add
          _ ≤ 11 / (1000 * (n : ℝ)) := by
              rw [show 1 / (100 * (n : ℝ)) + 1 / (2000 * (n : ℝ)) = 21 / (2000 * (n : ℝ)) by ring,
                show 11 / (1000 * (n : ℝ)) = 22 / (2000 * (n : ℝ)) by ring]
              exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
      -- Combine with hsum_inv and multiply by A_n.card ≤ n
      have hinv_j : ∑ b ∈ I j, (1 : ℝ) / (b : ℝ) ≤ 46 / (1000 * (n : ℝ)) := by
        have h1 : ∑ b ∈ I j, (1 : ℝ) / (b : ℝ) ≤ ∑ b ∈ (Finset.Ioc a_j b_j).filter (· ∈ B'), (1 : ℝ) / (b : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_j fun _ _ _ => by positivity
        have hlogb_ge : 2000 * (n : ℝ) ≤ Real.log (b_j : ℝ) :=
          hlogy_ge.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hb_ge_y))
        have hloga_ge : 2000 * (n : ℝ) ≤ Real.log (a_j : ℝ) :=
          hlogy_ge.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast ha_ge_y))
        have ht1 : 2 / Real.log (b_j : ℝ) ≤ 1 / (1000 * (n : ℝ)) := by
          rw [show (1 : ℝ) / (1000 * (n : ℝ)) = 2 / (2000 * (n : ℝ)) by ring]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hlogb_ge
        have ht2 : 8 / ((a_j : ℝ) * Real.log (a_j : ℝ)) ≤ 1 / (1000 * (n : ℝ)) := by
          have ha16 : (16 : ℝ) ≤ (a_j : ℝ) := by exact_mod_cast (by omega : 16 ≤ a_j)
          have hprod : 8000 * (n : ℝ) ≤ (a_j : ℝ) * Real.log (a_j : ℝ) := by nlinarith
          rw [show (1 : ℝ) / (1000 * (n : ℝ)) = 8 / (8000 * (n : ℝ)) by ring]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod
        calc ∑ b ∈ I j, (1 : ℝ) / (b : ℝ)
            ≤ 2 / Real.log (b_j : ℝ) + 4 * Real.log (Real.log (b_j : ℝ) / Real.log (a_j : ℝ)) +
                8 / ((a_j : ℝ) * Real.log (a_j : ℝ)) := h1.trans hsum_inv
          _ ≤ 1 / (1000 * (n : ℝ)) + 4 * (11 / (1000 * (n : ℝ))) + 1 / (1000 * (n : ℝ)) := by linarith
          _ = 46 / (1000 * (n : ℝ)) := by ring
      calc ∑ b ∈ I j, (A_n.card : ℝ) / (b : ℝ)
          = (A_n.card : ℝ) * ∑ b ∈ I j, (1 : ℝ) / (b : ℝ) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
        _ ≤ (n : ℝ) * (46 / (1000 * (n : ℝ))) :=
              mul_le_mul (by exact_mod_cast hw_le_n) hinv_j (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = 46 / 1000 := by field_simp [show (n : ℝ) ≠ 0 by positivity]
        _ ≤ 1 / 20 := by norm_num
  · -- Product bound ∏ b ∈ T, b ≤ z ^ s₀
    intro T hT
    have hT_f := Finset.mem_filter.mp hT
    have hsub : T ⊆ (Finset.range L).biUnion I := Finset.mem_powerset.mp hT_f.1
    have hpart : T = (Finset.range L).biUnion (fun j => T ∩ I j) := by
      ext b; simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_inter]
      constructor
      · intro hb
        obtain ⟨j, hj, hbI⟩ := Finset.mem_biUnion.mp (hsub hb)
        exact ⟨j, Finset.mem_range.mp hj, hb, hbI⟩
      · rintro ⟨_, _, hb, _⟩; exact hb
    have hdisj_T : Set.PairwiseDisjoint (Finset.range L : Set ℕ) (fun j => T ∩ I j) := by
      intro i hi j hj hij
      dsimp only [Function.onFun]
      exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hdisj hi hj hij)
    rw [hpart, Finset.prod_biUnion hdisj_T]
    have hblock_prod : ∀ j ∈ Finset.range L,
        ∏ b ∈ T ∩ I j, (b : ℝ) ≤ (z : ℝ) ^ (((4 + 2 * j : ℕ) : ℝ) * c ^ j) := by
      intro j hj
      have hcard : (T ∩ I j).card ≤ 4 + 2 * j := by have := hT_f.2 j hj; omega
      have hle : ∏ b ∈ T ∩ I j, (b : ℝ) ≤ ((z : ℝ) ^ (c ^ j)) ^ (T ∩ I j).card := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod (fun _ _ => by positivity) fun b hb =>
          (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2.2
      have hpow_le : ((z : ℝ) ^ (c ^ j)) ^ (T ∩ I j).card ≤ ((z : ℝ) ^ (c ^ j)) ^ (4 + 2 * j) :=
        pow_le_pow_right₀ (Real.one_le_rpow hz_gt1.le (by positivity)) hcard
      have hpow_eq : ((z : ℝ) ^ (c ^ j)) ^ (4 + 2 * j) = (z : ℝ) ^ (((4 + 2 * j : ℕ) : ℝ) * c ^ j) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; ring
      exact hle.trans (hpow_le.trans hpow_eq.le)
    calc ∏ j ∈ Finset.range L, ∏ b ∈ T ∩ I j, (b : ℝ)
        ≤ ∏ j ∈ Finset.range L, (z : ℝ) ^ (((4 + 2 * j : ℕ) : ℝ) * c ^ j) :=
          Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity) hblock_prod
      _ = (z : ℝ) ^ (∑ j ∈ Finset.range L, ((4 + 2 * j : ℕ) : ℝ) * c ^ j) := by
          rw [← Real.rpow_sum_of_pos (by linarith)]
      _ ≤ (z : ℝ) ^ (s₀ : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le hz_gt1.le ?_
          have hsum := sum_linear_geom_le c hc_pos.le hc_lt1 L
          have hs0 : 4 / (1 - c) + 2 / (1 - c) ^ 2 ≤ (s₀ : ℝ) := by
            rw [h1c]; dsimp only [s₀]; push_cast; field_simp; linarith
          exact hsum.trans hs0
      _ = (z : ℝ) ^ s₀ := Real.rpow_natCast _ _

/-- Clean wrapper combining `block_partition_bounds` and `block_bonferroni_ap` for any `z ≥ y`. -/
private lemma sieve_ap_bounds (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (N n k₀ d₀ M y z : ℕ) (A_n : Finset ℕ)
    (hn1 : 1 ≤ n) (hAn : A_n ⊆ Finset.Icc 1 n)
    (hy : 2 * n + 2 ≤ y) (hy16 : 16 ≤ y)
    (hy_exp : Real.exp (2000 * (n : ℝ)) ≤ (y : ℝ))
    (hyz : y ≤ z)
    (hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ))
    (hcop_s : ∀ b ∈ (Finset.Ioc y z).filter (· ∈ B'), Nat.Coprime b (d₀ * M)) :
    let s₀ : ℕ := 800 * n + 80000 * n ^ 2 + 1
    let B_med := (Finset.Ioc y z).filter (· ∈ B')
    let S_good := (Finset.range N).filter (fun t =>
      ∀ b ∈ B_med, ∀ a ∈ A_n, ¬ b ∣ a + (k₀ + t * d₀) * M)
    let V := ∏ b ∈ B_med, (1 - (A_n.card : ℝ) / (b : ℝ))
    (98 / 100 : ℝ) * (N : ℝ) * V - 2 * (z : ℝ) ^ (2 * s₀) ≤ (S_good.card : ℝ) ∧
    (S_good.card : ℝ) ≤ (102 / 100 : ℝ) * (N : ℝ) * V + (z : ℝ) ^ (2 * s₀) := by
  intro s₀ B_med S_good V
  obtain ⟨L, I, hdisj, hcover, hS, hD_supp⟩ :=
    block_partition_bounds B' hB' hge2 n y z A_n hn1 hAn hy hy16 hy_exp hyz hpi
  have hB_cop : (((Finset.range L).biUnion I) : Set ℕ).Pairwise Nat.Coprime := by
    rw [hcover]; exact hB'.mono (fun b hb => (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2)
  have hB_gt : ∀ b ∈ (Finset.range L).biUnion I, 2 * n < b := by
    rw [hcover]; intro b hb; have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).1; omega
  have hB_cop_s : ∀ b ∈ (Finset.range L).biUnion I, Nat.Coprime b (d₀ * M) := by
    rw [hcover]; exact hcop_s
  have hD_ge1 : (1 : ℝ) ≤ (z : ℝ) ^ s₀ := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ z))
  have hres := block_bonferroni_ap N n k₀ d₀ M L A_n I ((z : ℝ) ^ s₀) hn1 hAn hdisj
    hB_cop hB_gt hB_cop_s hS hD_ge1 hD_supp
  have hsq : ((z : ℝ) ^ s₀) ^ 2 = (z : ℝ) ^ (2 * s₀) := by rw [← pow_mul, mul_comm]
  simpa only [hcover, hsq] using hres

/- Part 5b: Upper range bounds and main theorem -/

/-- Bounds on the Euler-like sieve product `V(z) = ∏_{b ∈ (y, z] ∩ B'} (1 - |A_n| / b)`. -/
private lemma V_ratio_bound (B' : Set ℕ) (n y z₁ z₂ : ℕ) (A_n : Finset ℕ)
    (hAn : A_n ⊆ Finset.Icc 1 n) (hy : 2 * n + 2 ≤ y) (hyz₁ : y ≤ z₁) (hz₁₂ : z₁ ≤ z₂) :
    let V : ℕ → ℝ := fun z => ∏ b ∈ (Finset.Ioc y z).filter (· ∈ B'), (1 - (A_n.card : ℝ) / (b : ℝ))
    0 < V z₂ ∧ V z₂ ≤ V z₁ ∧ V z₁ ≤ 1 ∧
    V z₁ / V z₂ ≤ Real.exp (2 * (n : ℝ) * ∑ b ∈ (Finset.Ioc z₁ z₂).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) := by
  intro V
  have hw_le_n : A_n.card ≤ n := by
    have := Finset.card_le_card hAn; rw [Nat.card_Icc] at this; omega
  have hfactor : ∀ b ∈ (Finset.Ioc y z₂).filter (· ∈ B'),
      Real.exp (-2 * (n : ℝ) / (b : ℝ)) ≤ 1 - (A_n.card : ℝ) / (b : ℝ) ∧
      1 - (A_n.card : ℝ) / (b : ℝ) ≤ 1 := by
    intro b hb
    have hby : y < b := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1).1
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    have hwb_nn : (0 : ℝ) ≤ (A_n.card : ℝ) / (b : ℝ) := by positivity
    have hwb_le : (A_n.card : ℝ) / (b : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hb_pos (by norm_num : (0 : ℝ) < 2)]
      have : (2 * A_n.card : ℕ) ≤ b := by omega
      exact_mod_cast (by omega : A_n.card * 2 ≤ 1 * b)
    have h1 := exp_neg_two_mul_le_one_sub ((A_n.card : ℝ) / (b : ℝ)) hwb_nn hwb_le
    have h2 : -2 * (n : ℝ) / (b : ℝ) ≤ -2 * ((A_n.card : ℝ) / (b : ℝ)) := by
      rw [show -2 * ((A_n.card : ℝ) / (b : ℝ)) = -(2 * (A_n.card : ℝ)) / (b : ℝ) by ring,
          show -2 * (n : ℝ) / (b : ℝ) = -(2 * (n : ℝ)) / (b : ℝ) by ring]
      exact div_le_div_of_nonneg_right (by linarith [show (A_n.card : ℝ) ≤ (n : ℝ) by exact_mod_cast hw_le_n]) hb_pos.le
    exact ⟨(Real.exp_le_exp.mpr h2).trans h1, by linarith⟩
  have hsplit : (Finset.Ioc y z₂).filter (· ∈ B') =
      (Finset.Ioc y z₁).filter (· ∈ B') ∪ (Finset.Ioc z₁ z₂).filter (· ∈ B') := by
    ext b; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hb⟩
      by_cases hle : b ≤ z₁
      · exact Or.inl ⟨⟨h1, hle⟩, hb⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hb⟩
    · rintro (⟨⟨h1, h2⟩, hb⟩ | ⟨⟨h1, h2⟩, hb⟩)
      · exact ⟨⟨h1, by omega⟩, hb⟩
      · exact ⟨⟨by omega, h2⟩, hb⟩
  have hdisj : Disjoint ((Finset.Ioc y z₁).filter (· ∈ B')) ((Finset.Ioc z₁ z₂).filter (· ∈ B')) := by
    rw [Finset.disjoint_left]; intro b h1 h2
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h1).1).2
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h2).1).1
    omega
  have hV_split : V z₂ = V z₁ * ∏ b ∈ (Finset.Ioc z₁ z₂).filter (· ∈ B'), (1 - (A_n.card : ℝ) / (b : ℝ)) := by
    dsimp only [V]; rw [hsplit, Finset.prod_union hdisj]
  have hV₂_pos : 0 < V z₂ :=
    Finset.prod_pos fun b hb => lt_of_lt_of_le (Real.exp_pos _) (hfactor b hb).1
  have hV₁_le1 : V z₁ ≤ 1 := by
    refine Finset.prod_le_one (fun b hb => ?_) (fun b hb => ?_)
    · have hb2 : b ∈ (Finset.Ioc y z₂).filter (· ∈ B') := by rw [hsplit]; exact Finset.mem_union_left _ hb
      exact (Real.exp_pos _).le.trans (hfactor b hb2).1
    · have hb2 : b ∈ (Finset.Ioc y z₂).filter (· ∈ B') := by rw [hsplit]; exact Finset.mem_union_left _ hb
      exact (hfactor b hb2).2
  have htail_le1 : ∏ b ∈ (Finset.Ioc z₁ z₂).filter (· ∈ B'), (1 - (A_n.card : ℝ) / (b : ℝ)) ≤ 1 := by
    refine Finset.prod_le_one (fun b hb => ?_) (fun b hb => ?_)
    · have hb2 : b ∈ (Finset.Ioc y z₂).filter (· ∈ B') := by rw [hsplit]; exact Finset.mem_union_right _ hb
      exact (Real.exp_pos _).le.trans (hfactor b hb2).1
    · have hb2 : b ∈ (Finset.Ioc y z₂).filter (· ∈ B') := by rw [hsplit]; exact Finset.mem_union_right _ hb
      exact (hfactor b hb2).2
  have htail_ge : Real.exp (-(2 * (n : ℝ) * ∑ b ∈ (Finset.Ioc z₁ z₂).filter (· ∈ B'), (1 : ℝ) / (b : ℝ))) ≤
      ∏ b ∈ (Finset.Ioc z₁ z₂).filter (· ∈ B'), (1 - (A_n.card : ℝ) / (b : ℝ)) := by
    have hsum_eq : -(2 * (n : ℝ) * ∑ b ∈ (Finset.Ioc z₁ z₂).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) =
        ∑ b ∈ (Finset.Ioc z₁ z₂).filter (· ∈ B'), (-2 * (n : ℝ) / (b : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => by ring
    rw [hsum_eq, Real.exp_sum]
    refine Finset.prod_le_prod (fun b _ => (Real.exp_pos _).le) fun b hb => ?_
    have hb2 : b ∈ (Finset.Ioc y z₂).filter (· ∈ B') := by rw [hsplit]; exact Finset.mem_union_right _ hb
    exact (hfactor b hb2).1
  have hV₁_pos : 0 < V z₁ := by
    refine Finset.prod_pos fun b hb => ?_
    have hb2 : b ∈ (Finset.Ioc y z₂).filter (· ∈ B') := by rw [hsplit]; exact Finset.mem_union_left _ hb
    exact lt_of_lt_of_le (Real.exp_pos _) (hfactor b hb2).1
  refine ⟨hV₂_pos, ?_, hV₁_le1, ?_⟩
  · rw [hV_split]; nlinarith
  · rw [hV_split, div_mul_eq_div_div, div_self hV₁_pos.ne']
    rw [div_le_iff₀ (Finset.prod_pos fun b hb => by
      have hb2 : b ∈ (Finset.Ioc y z₂).filter (· ∈ B') := by rw [hsplit]; exact Finset.mem_union_right _ hb
      exact lt_of_lt_of_le (Real.exp_pos _) (hfactor b hb2).1)]
    have hmul := mul_le_mul_of_nonneg_left htail_ge (Real.exp_pos (2 * (n : ℝ) * ∑ b ∈ (Finset.Ioc z₁ z₂).filter (· ∈ B'), (1 : ℝ) / (b : ℝ))).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul

/-- Trivial upper bound on `#{k ∈ Icc 1 K | b ∣ a + k * M}` when `Nat.Coprime b M`. -/
private lemma card_ap_hit_trivial_upper (K a b M : ℕ) (hb : 0 < b) (hcop : Nat.Coprime b M) :
    (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ) ≤ (K : ℝ) / (b : ℝ) + 1 := by
  obtain ⟨r₀, hiff₀⟩ := dvd_linear_iff_modEq b a M hb hcop
  let r := r₀ % b
  have hr : r < b := Nat.mod_lt r₀ hb
  have hiff : ∀ k, b ∣ a + k * M ↔ k ≡ r [MOD b] := by
    intro k; rw [hiff₀ k, Nat.ModEq, Nat.ModEq, Nat.mod_mod]
  let k₀ : ℕ := if 1 ≤ r then r else b
  have hk₀_pos : 1 ≤ k₀ := by dsimp only [k₀]; split_ifs <;> omega
  have hk₀_mod : k₀ % b = r := by
    dsimp only [k₀]; split_ifs with h1
    · exact Nat.mod_eq_of_lt hr
    · have hr0 : r = 0 := by omega
      rw [hr0, Nat.mod_self]
  have hinj : ((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card ≤ K / b + 1 := by
    rw [← Finset.card_range (K / b + 1)]
    refine Finset.card_le_card_of_injOn (fun k => (k - k₀) / b) ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hk ⊢
      have hdiv : (k - k₀) / b ≤ K / b := Nat.div_le_div_right (by omega)
      omega
    · intro k₁ hk₁ k₂ hk₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk₁ hk₂
      have hm1 : k₁ % b = r := by
        have h := (hiff k₁).mp hk₁.2; rw [Nat.ModEq] at h; rwa [Nat.mod_eq_of_lt hr] at h
      have hm2 : k₂ % b = r := by
        have h := (hiff k₂).mp hk₂.2; rw [Nat.ModEq] at h; rwa [Nat.mod_eq_of_lt hr] at h
      have hge1 : k₀ ≤ k₁ := by
        dsimp only [k₀]; split_ifs with h1
        · have := Nat.mod_le k₁ b; omega
        · have hr0 : r = 0 := by omega
          have hd : b ∣ k₁ := Nat.dvd_of_mod_eq_zero (by omega)
          exact Nat.le_of_dvd (by omega) hd
      have hge2 : k₀ ≤ k₂ := by
        dsimp only [k₀]; split_ifs with h1
        · have := Nat.mod_le k₂ b; omega
        · have hr0 : r = 0 := by omega
          have hd : b ∣ k₂ := Nat.dvd_of_mod_eq_zero (by omega)
          exact Nat.le_of_dvd (by omega) hd
      have hd1 : b ∣ k₁ - k₀ := (Nat.modEq_iff_dvd' hge1).mp (by rw [Nat.ModEq, hk₀_mod, hm1])
      have hd2 : b ∣ k₂ - k₀ := (Nat.modEq_iff_dvd' hge2).mp (by rw [Nat.ModEq, hk₀_mod, hm2])
      have h1 : k₁ - k₀ = b * ((k₁ - k₀) / b) := (Nat.mul_div_cancel' hd1).symm
      have h2 : k₂ - k₀ = b * ((k₂ - k₀) / b) := (Nat.mul_div_cancel' hd2).symm
      dsimp only at heq
      rw [heq] at h1
      omega
  have hcast : ((K / b + 1 : ℕ) : ℝ) ≤ (K : ℝ) / (b : ℝ) + 1 := by
    push_cast
    have hdiv : ((K / b : ℕ) : ℝ) ≤ (K : ℝ) / (b : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < (b : ℝ))]
      exact_mod_cast Nat.div_mul_le_self K b
    linarith
  exact (Nat.cast_le.mpr hinj).trans hcast

/-- Sieve upper bound on `#{k ∈ Icc 1 K | b ∣ a + k * M ∧ ∀ p ∈ (y, z_b] ∩ B', ∀ a' ∈ A_n, ¬ p ∣ a' + k * M}`. -/
private lemma card_ap_hit_sieve_upper (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (K n M y z_b a b : ℕ) (A_n : Finset ℕ)
    (hn1 : 1 ≤ n) (hAn : A_n ⊆ Finset.Icc 1 n)
    (hy : 2 * n + 2 ≤ y) (hy16 : 16 ≤ y)
    (hy_exp : Real.exp (2000 * (n : ℝ)) ≤ (y : ℝ))
    (hyzb : y ≤ z_b) (hzbb : z_b < b) (hbK : b ≤ K)
    (hbB : b ∈ B') (hcop_bM : Nat.Coprime b M)
    (hcop_M : ∀ p ∈ B', y < p → Nat.Coprime p M)
    (hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ)) :
    let s₀ : ℕ := 800 * n + 80000 * n ^ 2 + 1
    let B_med := (Finset.Ioc y z_b).filter (· ∈ B')
    let V_b := ∏ p ∈ B_med, (1 - (A_n.card : ℝ) / (p : ℝ))
    let S_hit := (Finset.Icc 1 K).filter (fun k =>
      b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)
    (S_hit.card : ℝ) ≤ (102 / 100 : ℝ) * (2 * (K : ℝ) / (b : ℝ)) * V_b + (z_b : ℝ) ^ (2 * s₀) := by
  intro s₀ B_med V_b S_hit
  have hb_pos : 0 < b := by omega
  obtain ⟨r₀, hiff₀⟩ := dvd_linear_iff_modEq b a M hb_pos hcop_bM
  let r := r₀ % b
  have hr : r < b := Nat.mod_lt r₀ hb_pos
  have hiff : ∀ k, b ∣ a + k * M ↔ k ≡ r [MOD b] := by
    intro k; rw [hiff₀ k, Nat.ModEq, Nat.ModEq, Nat.mod_mod]
  let k₀ : ℕ := if 1 ≤ r then r else b
  have hk₀_mod : k₀ % b = r := by
    dsimp only [k₀]; split_ifs with h1
    · exact Nat.mod_eq_of_lt hr
    · have hr0 : r = 0 := by omega
      rw [hr0, Nat.mod_self]
  let N_b : ℕ := K / b + 1
  let S_ap := (Finset.range N_b).filter (fun t =>
    ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + (k₀ + t * b) * M)
  have hcard_le : S_hit.card ≤ S_ap.card := by
    refine Finset.card_le_card_of_injOn (fun k => (k - k₀) / b) ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, S_hit, S_ap, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hk ⊢
      have hm : k % b = r := by
        have h := (hiff k).mp hk.2.1; rw [Nat.ModEq] at h; rwa [Nat.mod_eq_of_lt hr] at h
      have hge : k₀ ≤ k := by
        dsimp only [k₀]; split_ifs with h1
        · have := Nat.mod_le k b; omega
        · have hr0 : r = 0 := by omega
          exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
      have hd : b ∣ k - k₀ := (Nat.modEq_iff_dvd' hge).mp (by rw [Nat.ModEq, hk₀_mod, hm])
      have hk_eq : k₀ + (k - k₀) / b * b = k := by
        have := Nat.div_mul_cancel hd; omega
      refine ⟨?_, ?_⟩
      · have : (k - k₀) / b ≤ K / b := Nat.div_le_div_right (by omega)
        omega
      · rw [hk_eq]; exact hk.2.2
    · intro k₁ hk₁ k₂ hk₂ heq
      simp only [Finset.mem_coe, S_hit, Finset.mem_filter, Finset.mem_Icc] at hk₁ hk₂
      have hm1 : k₁ % b = r := by
        have h := (hiff k₁).mp hk₁.2.1; rw [Nat.ModEq] at h; rwa [Nat.mod_eq_of_lt hr] at h
      have hm2 : k₂ % b = r := by
        have h := (hiff k₂).mp hk₂.2.1; rw [Nat.ModEq] at h; rwa [Nat.mod_eq_of_lt hr] at h
      have hge1 : k₀ ≤ k₁ := by
        dsimp only [k₀]; split_ifs with h1
        · have := Nat.mod_le k₁ b; omega
        · have hr0 : r = 0 := by omega
          exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
      have hge2 : k₀ ≤ k₂ := by
        dsimp only [k₀]; split_ifs with h1
        · have := Nat.mod_le k₂ b; omega
        · have hr0 : r = 0 := by omega
          exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
      have hd1 : b ∣ k₁ - k₀ := (Nat.modEq_iff_dvd' hge1).mp (by rw [Nat.ModEq, hk₀_mod, hm1])
      have hd2 : b ∣ k₂ - k₀ := (Nat.modEq_iff_dvd' hge2).mp (by rw [Nat.ModEq, hk₀_mod, hm2])
      have h1 : k₁ - k₀ = b * ((k₁ - k₀) / b) := (Nat.mul_div_cancel' hd1).symm
      have h2 : k₂ - k₀ = b * ((k₂ - k₀) / b) := (Nat.mul_div_cancel' hd2).symm
      dsimp only at heq
      rw [heq] at h1
      omega
  have hcop_s : ∀ p ∈ B_med, Nat.Coprime p (b * M) := by
    intro p hp
    have hpf := Finset.mem_filter.mp hp
    have hpioc := Finset.mem_Ioc.mp hpf.1
    exact (hB' hpf.2 hbB (by omega)).mul_right (hcop_M p hpf.2 hpioc.1)
  have hsieve := (sieve_ap_bounds B' hB' hge2 N_b n k₀ b M y z_b A_n hn1 hAn hy hy16 hy_exp hyzb hpi hcop_s).2
  have hV_nn : 0 ≤ V_b := (V_ratio_bound B' n y y z_b A_n hAn hy le_rfl hyzb).1.le
  have hNb_le : (N_b : ℝ) ≤ 2 * (K : ℝ) / (b : ℝ) := by
    dsimp only [N_b]; push_cast
    have hdiv : ((K / b : ℕ) : ℝ) ≤ (K : ℝ) / (b : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hb_pos : (0 : ℝ) < (b : ℝ))]
      exact_mod_cast Nat.div_mul_le_self K b
    have h1_le : (1 : ℝ) ≤ (K : ℝ) / (b : ℝ) :=
      (one_le_div (by exact_mod_cast hb_pos : (0 : ℝ) < (b : ℝ))).mpr (by exact_mod_cast hbK)
    linarith [show 2 * (K : ℝ) / (b : ℝ) = (K : ℝ) / (b : ℝ) + (K : ℝ) / (b : ℝ) by ring]
  calc (S_hit.card : ℝ) ≤ (S_ap.card : ℝ) := Nat.cast_le.mpr hcard_le
    _ ≤ (102 / 100 : ℝ) * (N_b : ℝ) * V_b + (z_b : ℝ) ^ (2 * s₀) := hsieve
    _ ≤ (102 / 100 : ℝ) * (2 * (K : ℝ) / (b : ℝ)) * V_b + (z_b : ℝ) ^ (2 * s₀) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNb_le (by norm_num : (0 : ℝ) ≤ 102 / 100)) hV_nn
        linarith

/-- Union-bound helper: count `k ∈ Icc 1 K` that avoid `(y, z] ∩ B'` and are hit by some `a ∈ A_n`, `b ∈ R`. -/
private lemma card_bad_in_range_le (B' : Set ℕ) (K M y z : ℕ) (A_n R : Finset ℕ) :
    let B_med := (Finset.Ioc y z).filter (· ∈ B')
    (((Finset.Icc 1 K).filter (fun k =>
        (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
        ∃ a ∈ A_n, ∃ b ∈ R, b ∣ a + k * M)).card : ℝ) ≤
      ∑ a ∈ A_n, ∑ b ∈ R, (((Finset.Icc 1 K).filter (fun k =>
        b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) := by
  intro B_med
  have hsub : (Finset.Icc 1 K).filter (fun k =>
      (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
      ∃ a ∈ A_n, ∃ b ∈ R, b ∣ a + k * M) ⊆
      A_n.biUnion (fun a => R.biUnion (fun b =>
        (Finset.Icc 1 K).filter (fun k =>
          b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M))) := by
    intro k hk
    have hkf := Finset.mem_filter.mp hk
    obtain ⟨a, ha, b, hb, hdvd⟩ := hkf.2.2
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr ⟨b, hb,
      Finset.mem_filter.mpr ⟨hkf.1, hdvd, hkf.2.1⟩⟩⟩
  have h1 : ((Finset.Icc 1 K).filter (fun k =>
      (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
      ∃ a ∈ A_n, ∃ b ∈ R, b ∣ a + k * M)).card ≤
      ∑ a ∈ A_n, ∑ b ∈ R, ((Finset.Icc 1 K).filter (fun k =>
        b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card := by
    calc _ ≤ (A_n.biUnion (fun a => R.biUnion (fun b =>
          (Finset.Icc 1 K).filter (fun k =>
            b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)))).card := Finset.card_le_card hsub
      _ ≤ ∑ a ∈ A_n, (R.biUnion (fun b =>
          (Finset.Icc 1 K).filter (fun k =>
            b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M))).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ A_n, ∑ b ∈ R, ((Finset.Icc 1 K).filter (fun k =>
          b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
  exact_mod_cast h1

/-- Elementary bound: for `x ≥ 4`, `Real.log (⌊x⌋₊ : ℝ) ≥ Real.log x / 2`. -/
private lemma log_floor_ge_half_log (x : ℝ) (hx : 4 ≤ x) :
    Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := by
  have hx_pos : 0 < x := by linarith
  have hfl_ge : Real.sqrt x ≤ (⌊x⌋₊ : ℝ) := by
    have h1 : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
    have hsq : Real.sqrt x ≤ x / 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    linarith
  have hlog := Real.log_le_log (Real.sqrt_pos.mpr hx_pos) hfl_ge
  rwa [Real.log_sqrt hx_pos.le] at hlog

private lemma le_pow_four_of_one_le {x : ℝ} (hx : 1 ≤ x) : x ≤ x ^ 4 := by
  calc x = x ^ 1 := (pow_one x).symm
    _ ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)

private lemma mul_three_ge_one {a b c : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : 1 ≤ a * b * c :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) hc

set_option maxHeartbeats 400000 in
/-- Range 1: `b ∈ (z, ⌊K^{1/2}⌋₊]`. -/
private lemma range1_bound (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (K n M y J₀ : ℕ) (A_n : Finset ℕ)
    (hn1 : 1 ≤ n) (hAn : A_n ⊆ Finset.Icc 1 n)
    (hy : 2 * n + 2 ≤ y) (hy16 : 16 ≤ y)
    (hy_exp : Real.exp (2000 * (n : ℝ)) ≤ (y : ℝ))
    (hcop_M : ∀ p ∈ B', y < p → Nat.Coprime p M)
    (hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ))
    (hK_ge : 16 ≤ K)
    (hL_ge : (1000 * (n : ℝ) * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ) * (Real.log (y : ℝ) + 10)) ^ 4 ≤ Real.log (K : ℝ))
    (hf_good : ∀ a : ℕ, 16 ≤ a → a ≤ K →
      (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) -
      (∑ b ∈ (Finset.range a).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) ≤
        (1 / (1000 * (n : ℝ) * ((J₀ : ℝ) + 1) * (Real.log (8 * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ)) + 10))) *
        (Real.log (Real.log (K : ℝ) / Real.log (a : ℝ)) + 2))
    (hVz_ge : 1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤
      ∏ p ∈ (Finset.Ioc y ⌊(K : ℝ) ^ (1 / (8 * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ)))⌋₊).filter (· ∈ B'),
        (1 - (A_n.card : ℝ) / (p : ℝ))) :
    let s₀ : ℕ := 800 * n + 80000 * n ^ 2 + 1
    let z : ℕ := ⌊(K : ℝ) ^ (1 / (8 * (s₀ : ℝ)))⌋₊
    let R₁ := (Finset.Ioc z ⌊Real.sqrt (K : ℝ)⌋₊).filter (· ∈ B')
    let B_med := (Finset.Ioc y z).filter (· ∈ B')
    let V_z := ∏ p ∈ B_med, (1 - (A_n.card : ℝ) / (p : ℝ))
    (((Finset.Icc 1 K).filter (fun k =>
      (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
      ∃ a ∈ A_n, ∃ b ∈ R₁, b ∣ a + k * M)).card : ℝ) ≤
      (2 / 100 : ℝ) * (K : ℝ) * V_z := by
  intro s₀ z R₁ B_med V_z
  have hs₀_pos : (0 : ℝ) < (s₀ : ℝ) := by dsimp only [s₀]; positivity
  have hs₀_ge1 : (1 : ℝ) ≤ (s₀ : ℝ) := by dsimp only [s₀]; exact_mod_cast (by omega : 1 ≤ s₀)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hC_ge : (1000 : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h1 : (1 : ℝ) ≤ (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := mul_three_ge_one hnR hs₀_ge1 (by linarith)
    nlinarith
  have hL_pos : (0 : ℝ) < Real.log (K : ℝ) := lt_of_lt_of_le (by positivity) hL_ge
  have hL_big : 16 * (s₀ : ℝ) * (Real.log (y : ℝ) + 4) ≤ Real.log (K : ℝ) := by
    have h1 : 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) ≤
        (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 4 := le_pow_four_of_one_le (by linarith)
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h2 : 16 * (s₀ : ℝ) * (Real.log (y : ℝ) + 4) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by
      have hns : (s₀ : ℝ) ≤ (n : ℝ) * (s₀ : ℝ) := le_mul_of_one_le_left hs₀_pos.le hnR
      nlinarith
    linarith
  have hKz_ge : 4 * (y : ℝ) ≤ (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) := by
    rw [Real.rpow_def_of_pos hK_pos]
    have h4y : 4 * (y : ℝ) ≤ Real.exp (Real.log (y : ℝ) + 2) := by
      rw [Real.exp_add, Real.exp_log (by exact_mod_cast (by omega : 0 < y))]
      have he2 : (4 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (1 : ℝ)
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
      nlinarith [show (0 : ℝ) ≤ (y : ℝ) by positivity]
    refine h4y.trans (Real.exp_le_exp.mpr ?_)
    have : Real.log (y : ℝ) + 2 ≤ Real.log (K : ℝ) / (8 * (s₀ : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith [show Real.log (K : ℝ) * (1 / (8 * (s₀ : ℝ))) = Real.log (K : ℝ) / (8 * (s₀ : ℝ)) by ring]
  have hyz : y ≤ z := by
    have hfl : (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) - 1 < (z : ℝ) := Nat.sub_one_lt_floor _
    have hyR : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy16
    exact_mod_cast (show (y : ℝ) ≤ (z : ℝ) by linarith)
  have hz_le_K : z ≤ K := by
    have h1 : (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) ≤ (K : ℝ) := by
      conv_rhs => rw [← Real.rpow_one (K : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hK_ge1 (by rw [div_le_one (by positivity)]; linarith)
    exact Nat.floor_le_of_le (by exact_mod_cast h1)
  have hlogz_ge : Real.log (K : ℝ) / (16 * (s₀ : ℝ)) ≤ Real.log (z : ℝ) := by
    have h4 : (4 : ℝ) ≤ (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) := by
      have : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy16
      linarith
    have h1 := log_floor_ge_half_log ((K : ℝ) ^ (1 / (8 * (s₀ : ℝ)))) h4
    rw [Real.log_rpow hK_pos] at h1
    linarith [show 1 / (8 * (s₀ : ℝ)) * Real.log (K : ℝ) / 2 = Real.log (K : ℝ) / (16 * (s₀ : ℝ)) by ring]
  have hstep1 := card_bad_in_range_le B' K M y z A_n R₁
  have hterm : ∀ a ∈ A_n, ∀ b ∈ R₁,
      (((Finset.Icc 1 K).filter (fun k =>
        b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
      (102 / 100 : ℝ) * (2 * (K : ℝ) / (b : ℝ)) * V_z + (z : ℝ) ^ (2 * s₀) := by
    intro a _ b hb
    have hbf := Finset.mem_filter.mp hb
    have hbi := Finset.mem_Ioc.mp hbf.1
    have hbK : b ≤ K := by
      have hsq : Real.sqrt (K : ℝ) ≤ (K : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨hK_pos.le, by nlinarith⟩
      exact hbi.2.trans (Nat.floor_le_of_le (by exact_mod_cast hsq))
    exact card_ap_hit_sieve_upper B' hB' hge2 K n M y z a b A_n hn1 hAn hy hy16 hy_exp
      hyz hbi.1 hbK hbf.2 (hcop_M b hbf.2 (by omega)) hcop_M hpi
  have hsum_le : ∑ a ∈ A_n, ∑ b ∈ R₁,
      (((Finset.Icc 1 K).filter (fun k =>
        b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
      (A_n.card : ℝ) * ((204 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₁, (1 : ℝ) / (b : ℝ)) +
        (R₁.card : ℝ) * (z : ℝ) ^ (2 * s₀)) := by
    have h1 := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    refine h1.trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]; congr 1
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun b _ => by ring
  -- Bound ∑_{b ∈ R₁} 1 / b via hf_good at a = z
  have hinv_R1 : ∑ b ∈ R₁, (1 : ℝ) / (b : ℝ) ≤ 1 / (1000 * (n : ℝ)) := by
    have hsub_R1 : R₁ ⊆ ((Finset.range (K + 1)).filter (· ∈ B')) \ ((Finset.range z).filter (· ∈ B')) := by
      intro b hb
      have hbf := Finset.mem_filter.mp hb
      have hbi := Finset.mem_Ioc.mp hbf.1
      have hbK : b ≤ K := by
        have hsq : Real.sqrt (K : ℝ) ≤ (K : ℝ) := by rw [Real.sqrt_le_iff]; exact ⟨hK_pos.le, by nlinarith⟩
        exact hbi.2.trans (Nat.floor_le_of_le (by exact_mod_cast hsq))
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨by omega, hbf.2⟩, fun h => by omega⟩
    have hdiff_eq : ∑ b ∈ ((Finset.range (K + 1)).filter (· ∈ B')) \ ((Finset.range z).filter (· ∈ B')), (1 : ℝ) / (b : ℝ) =
        (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) -
        (∑ b ∈ (Finset.range z).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) := by
      rw [Finset.sum_sdiff_eq_sub (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))]
    have hfg := hf_good z (by omega) hz_le_K
    have hratio : Real.log (K : ℝ) / Real.log (z : ℝ) ≤ 16 * (s₀ : ℝ) := by
      rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hlogz_ge)]
      have := mul_le_mul_of_nonneg_left hlogz_ge (show (0 : ℝ) ≤ 16 * (s₀ : ℝ) by positivity)
      have hcancel : 16 * (s₀ : ℝ) * (Real.log (K : ℝ) / (16 * (s₀ : ℝ))) = Real.log (K : ℝ) := by field_simp
      linarith
    have hlog_rat : Real.log (Real.log (K : ℝ) / Real.log (z : ℝ)) + 2 ≤
        Real.log (8 * (s₀ : ℝ)) + 10 := by
      have h1 : Real.log (Real.log (K : ℝ) / Real.log (z : ℝ)) ≤ Real.log (16 * (s₀ : ℝ)) :=
        Real.log_le_log (div_pos hL_pos (lt_of_lt_of_le (by positivity) hlogz_ge)) hratio
      rw [show (16 : ℝ) * (s₀ : ℝ) = 2 * (8 * (s₀ : ℝ)) by ring, Real.log_mul (by norm_num) (by positivity)] at h1
      linarith [Real.log_two_lt_d9]
    have hlog8s_pos : 0 < Real.log (8 * (s₀ : ℝ)) + 10 := by
      have : 0 ≤ Real.log (8 * (s₀ : ℝ)) := Real.log_nonneg (by linarith)
      linarith
    have hJ0_ge1 : (1 : ℝ) ≤ (J₀ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) J₀]
    calc ∑ b ∈ R₁, (1 : ℝ) / (b : ℝ)
        ≤ (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) -
          (∑ b ∈ (Finset.range z).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) := by
            rw [← hdiff_eq]; exact Finset.sum_le_sum_of_subset_of_nonneg hsub_R1 fun _ _ _ => by positivity
      _ ≤ (1 / (1000 * (n : ℝ) * ((J₀ : ℝ) + 1) * (Real.log (8 * (s₀ : ℝ)) + 10))) *
            (Real.log (Real.log (K : ℝ) / Real.log (z : ℝ)) + 2) := hfg
      _ ≤ (1 / (1000 * (n : ℝ) * 1 * (Real.log (8 * (s₀ : ℝ)) + 10))) *
            (Real.log (8 * (s₀ : ℝ)) + 10) := by
          refine mul_le_mul ?_ hlog_rat ?_ (by positivity)
          · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ0_ge1 (by positivity)) hlog8s_pos.le)
          · have hzkR : (z : ℝ) ≤ (K : ℝ) := by exact_mod_cast hz_le_K
            have := Real.log_nonneg ((one_le_div (lt_of_lt_of_le (by positivity) hlogz_ge)).mpr
              (Real.log_le_log (by exact_mod_cast (by omega : 0 < z)) hzkR))
            linarith
      _ = 1 / (1000 * (n : ℝ)) := by field_simp
  -- Bound error term: (R₁.card : ℝ) * (z : ℝ) ^ (2 * s₀) ≤ (1 / (100 * n)) * K * V_z
  have herr_R1 : (A_n.card : ℝ) * ((R₁.card : ℝ) * (z : ℝ) ^ (2 * s₀)) ≤ (1 / 100 : ℝ) * (K : ℝ) * V_z := by
    have hcard_An : (A_n.card : ℝ) ≤ (n : ℝ) := by
      have := Finset.card_le_card hAn; rw [Nat.card_Icc] at this; exact_mod_cast (by omega : A_n.card ≤ n)
    have hcard_R1 : (R₁.card : ℝ) ≤ (K : ℝ) ^ (1 / 2 : ℝ) := by
      have h1 : R₁.card ≤ ⌊Real.sqrt (K : ℝ)⌋₊ := by
        calc R₁.card ≤ (Finset.Ioc z ⌊Real.sqrt (K : ℝ)⌋₊).card := Finset.card_filter_le _ _
          _ = ⌊Real.sqrt (K : ℝ)⌋₊ - z := Nat.card_Ioc _ _
          _ ≤ ⌊Real.sqrt (K : ℝ)⌋₊ := Nat.sub_le _ _
      calc (R₁.card : ℝ) ≤ (⌊Real.sqrt (K : ℝ)⌋₊ : ℝ) := Nat.cast_le.mpr h1
        _ ≤ Real.sqrt (K : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
        _ = (K : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hz_pow : (z : ℝ) ^ (2 * s₀) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by
      have hz_le : (z : ℝ) ≤ (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) := Nat.floor_le (by positivity)
      calc (z : ℝ) ^ (2 * s₀) ≤ ((K : ℝ) ^ (1 / (8 * (s₀ : ℝ)))) ^ (2 * s₀) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hz_le _
        _ = (K : ℝ) ^ (1 / (8 * (s₀ : ℝ)) * ((2 * s₀ : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hK_pos.le]
        _ = (K : ℝ) ^ (1 / 4 : ℝ) := by congr 1; push_cast; field_simp; ring
    have hK_quarter : 100 * (n : ℝ) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by
      have hL_large : 3200 * (n : ℝ) ≤ Real.log (K : ℝ) := by
        have h1 : 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) ≤
            (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 4 := le_pow_four_of_one_le (by linarith)
        have h2 : (10 : ℝ) ≤ (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by nlinarith
        nlinarith
      have hL4 : (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤ Real.log (K : ℝ) := by
        conv_rhs => rw [← Real.rpow_one (Real.log (K : ℝ))]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn1]) (by norm_num)
      have hK4 : (Real.log (K : ℝ)) ^ 2 / 32 ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_def_of_pos hK_pos]
        have h2 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ Real.log (K : ℝ) * (1 / 4) by positivity) 3
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
          pow_zero, pow_one, div_one, zero_add] at h2
        nlinarith only [h2, hL_pos]
      nlinarith only [hL_large, hL4, hK4, hL_pos, hn_pos]
    have hK_prod : (K : ℝ) ^ (1 / 2 : ℝ) * (K : ℝ) ^ (1 / 4 : ℝ) * (K : ℝ) ^ (1 / 4 : ℝ) = (K : ℝ) := by
      rw [← Real.rpow_add hK_pos, ← Real.rpow_add hK_pos]; norm_num
    have hprod_le : (n : ℝ) * ((K : ℝ) ^ (1 / 2 : ℝ) * (K : ℝ) ^ (1 / 4 : ℝ)) ≤
        (1 / 100 : ℝ) * (K : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) := by
      have hpos_L4 : (0 : ℝ) < (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL_pos _
      rw [mul_one_div, le_div_iff₀ hpos_L4]
      have hmul := mul_le_mul_of_nonneg_left hK_quarter (show (0 : ℝ) ≤ (K : ℝ) ^ (1 / 2 : ℝ) * (K : ℝ) ^ (1 / 4 : ℝ) by positivity)
      linarith [show (K : ℝ) ^ (1 / 2 : ℝ) * (K : ℝ) ^ (1 / 4 : ℝ) * (100 * (n : ℝ) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) =
        100 * ((n : ℝ) * ((K : ℝ) ^ (1 / 2 : ℝ) * (K : ℝ) ^ (1 / 4 : ℝ)) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) by ring]
    calc (A_n.card : ℝ) * ((R₁.card : ℝ) * (z : ℝ) ^ (2 * s₀))
        ≤ (n : ℝ) * ((K : ℝ) ^ (1 / 2 : ℝ) * (K : ℝ) ^ (1 / 4 : ℝ)) := by
          refine mul_le_mul hcard_An (mul_le_mul hcard_R1 hz_pow (by positivity) (by positivity)) (by positivity) hn_pos.le
      _ ≤ (1 / 100 : ℝ) * (K : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) := hprod_le
      _ ≤ (1 / 100 : ℝ) * (K : ℝ) * V_z :=
          mul_le_mul_of_nonneg_left hVz_ge (by positivity)
  have hVz_nn : 0 ≤ V_z := (V_ratio_bound B' n y y z A_n hAn hy le_rfl hyz).1.le
  have hcard_An : (A_n.card : ℝ) ≤ (n : ℝ) := by
    have := Finset.card_le_card hAn; rw [Nat.card_Icc] at this; exact_mod_cast (by omega : A_n.card ≤ n)
  have hmain_R1 : (A_n.card : ℝ) * ((204 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₁, (1 : ℝ) / (b : ℝ))) ≤
      (1 / 100 : ℝ) * (K : ℝ) * V_z := by
    calc (A_n.card : ℝ) * ((204 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₁, (1 : ℝ) / (b : ℝ)))
        ≤ (n : ℝ) * ((204 / 100 : ℝ) * (K : ℝ) * V_z * (1 / (1000 * (n : ℝ)))) := by
          refine mul_le_mul hcard_An
            (mul_le_mul_of_nonneg_left hinv_R1 (by positivity))
            (by exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)) hn_pos.le
      _ = (204 / 100000 : ℝ) * (K : ℝ) * V_z := by field_simp; ring
      _ ≤ (1 / 100 : ℝ) * (K : ℝ) * V_z := by linarith only [mul_nonneg hK_pos.le hVz_nn]
  calc _ ≤ (A_n.card : ℝ) * ((204 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₁, (1 : ℝ) / (b : ℝ)) +
            (R₁.card : ℝ) * (z : ℝ) ^ (2 * s₀)) := hstep1.trans hsum_le
    _ = (A_n.card : ℝ) * ((204 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₁, (1 : ℝ) / (b : ℝ))) +
          (A_n.card : ℝ) * ((R₁.card : ℝ) * (z : ℝ) ^ (2 * s₀)) := by ring
    _ ≤ (1 / 100 : ℝ) * (K : ℝ) * V_z + (1 / 100 : ℝ) * (K : ℝ) * V_z := add_le_add hmain_R1 herr_R1
    _ = (2 / 100 : ℝ) * (K : ℝ) * V_z := by ring

/-- Helper for Ranges 2 & 3: for `b ∈ (⌊√K⌋₊, ⌊K / exp(√(log K))⌋₊] ∩ B'` with `K / b ≥ K ^ δ`,
    bound the count of `k ∈ Icc 1 K` avoiding `(y, z] ∩ B'` and hit by `b ∣ a + k * M`. -/
private lemma zb_sieve_term (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (K n M y J₀ a b j_idx : ℕ) (A_n : Finset ℕ)
    (hn1 : 1 ≤ n) (hAn : A_n ⊆ Finset.Icc 1 n)
    (hy : 2 * n + 2 ≤ y) (hy16 : 16 ≤ y)
    (hy_exp : Real.exp (2000 * (n : ℝ)) ≤ (y : ℝ))
    (hcop_M : ∀ p ∈ B', y < p → Nat.Coprime p M)
    (hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ))
    (hK_ge : 16 ≤ K)
    (hL_ge : (1000 * (n : ℝ) * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ) * (Real.log (y : ℝ) + 10)) ^ 4 ≤ Real.log (K : ℝ))
    (hf_good : ∀ a' : ℕ, 16 ≤ a' → a' ≤ K →
      (∑ p ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (p : ℝ)) -
      (∑ p ∈ (Finset.range a').filter (· ∈ B'), (1 : ℝ) / (p : ℝ)) ≤
        (1 / (1000 * (n : ℝ) * ((J₀ : ℝ) + 1) * (Real.log (8 * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ)) + 10))) *
        (Real.log (Real.log (K : ℝ) / Real.log (a' : ℝ)) + 2))
    (hbB : b ∈ B') (hb_lo : ⌊Real.sqrt (K : ℝ)⌋₊ < b)
    (hb_hi : b ≤ ⌊(K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ)))⌋₊)
    (hb_pow : (b : ℝ) ≤ (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j_idx))
    (hj_ge : 1 ≤ j_idx) :
    let s₀ : ℕ := 800 * n + 80000 * n ^ 2 + 1
    let z : ℕ := ⌊(K : ℝ) ^ (1 / (8 * (s₀ : ℝ)))⌋₊
    let B_med := (Finset.Ioc y z).filter (· ∈ B')
    let V_z := ∏ p ∈ B_med, (1 - (A_n.card : ℝ) / (p : ℝ))
    (((Finset.Icc 1 K).filter (fun k =>
      b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
      (204 / 100 : ℝ) * ((K : ℝ) / (b : ℝ)) *
        Real.exp (((j_idx : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1))) * V_z +
        ((K : ℝ) / (b : ℝ)) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) := by
  intro s₀ z B_med V_z
  have hs₀_pos : (0 : ℝ) < (s₀ : ℝ) := by dsimp only [s₀]; positivity
  have hs₀_ge1 : (1 : ℝ) ≤ (s₀ : ℝ) := by dsimp only [s₀]; exact_mod_cast (by omega : 1 ≤ s₀)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hC_ge : (1000 : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h1 : (1 : ℝ) ≤ (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := mul_three_ge_one hnR hs₀_ge1 (by linarith)
    nlinarith
  have hL_pos : (0 : ℝ) < Real.log (K : ℝ) := lt_of_lt_of_le (by positivity) hL_ge
  have hsqrtL_ge : (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 2 ≤ Real.sqrt (Real.log (K : ℝ)) := by
    rw [Real.le_sqrt (by positivity) hL_pos.le]
    have : ((1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 2) ^ 2 =
        (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 4 := by ring
    linarith
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by have := hge2 b hbB; omega : 0 < b)
  have hbK_R : (b : ℝ) ≤ (K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ))) :=
    (Nat.cast_le.mpr hb_hi).trans (Nat.floor_le (by positivity))
  have hbK : b ≤ K := by
    have h1 : (K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ))) ≤ (K : ℝ) :=
      div_le_self hK_pos.le (Real.one_le_exp (Real.sqrt_nonneg _))
    exact_mod_cast (hbK_R.trans h1)
  have hKb_ge_exp : Real.exp (Real.sqrt (Real.log (K : ℝ))) ≤ (K : ℝ) / (b : ℝ) := by
    rw [le_div_iff₀ hb_pos]
    have := (le_div_iff₀ (Real.exp_pos (Real.sqrt (Real.log (K : ℝ))))).mp hbK_R
    linarith
  have hKb_pos : 0 < (K : ℝ) / (b : ℝ) := div_pos hK_pos hb_pos
  let z_b : ℕ := ⌊((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ)))⌋₊
  have hzb_le_z : z_b ≤ z := by
    refine Nat.floor_mono (Real.rpow_le_rpow hKb_pos.le (div_le_self hK_pos.le (by exact_mod_cast (by have := hge2 b hbB; omega : 1 ≤ b))) (by positivity))
  have hzb_ge_4y : 4 * (y : ℝ) ≤ ((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ))) := by
    have h1 : Real.exp (Real.sqrt (Real.log (K : ℝ)) / (8 * (s₀ : ℝ))) ≤
        ((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ))) := by
      have := Real.rpow_le_rpow (Real.exp_pos _).le hKb_ge_exp (show (0 : ℝ) ≤ 1 / (8 * (s₀ : ℝ)) by positivity)
      rwa [← Real.exp_mul, show Real.sqrt (Real.log (K : ℝ)) * (1 / (8 * (s₀ : ℝ))) =
        Real.sqrt (Real.log (K : ℝ)) / (8 * (s₀ : ℝ)) by ring] at this
    have h4y : 4 * (y : ℝ) ≤ Real.exp (Real.log (y : ℝ) + 2) := by
      rw [Real.exp_add, Real.exp_log (by exact_mod_cast (by omega : 0 < y))]
      have he2 : (4 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (1 : ℝ)
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
      nlinarith [show (0 : ℝ) ≤ (y : ℝ) by positivity]
    have hexp_le : Real.log (y : ℝ) + 2 ≤ Real.sqrt (Real.log (K : ℝ)) / (8 * (s₀ : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hsq1 : 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) ≤
          (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 2 := by nlinarith
      nlinarith
    exact h4y.trans ((Real.exp_le_exp.mpr hexp_le).trans h1)
  have hyzb : y ≤ z_b := by
    have hfl : ((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ))) - 1 < (z_b : ℝ) := Nat.sub_one_lt_floor _
    have hyR : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy16
    exact_mod_cast (show (y : ℝ) ≤ (z_b : ℝ) by linarith)
  have hzbb : z_b < b := by
    have hzb_le_Kb : (z_b : ℝ) ≤ (K : ℝ) / (b : ℝ) := by
      have h1 : (z_b : ℝ) ≤ ((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ))) := Nat.floor_le (by positivity)
      have hKb_ge1 : (1 : ℝ) ≤ (K : ℝ) / (b : ℝ) := (Real.one_le_exp (Real.sqrt_nonneg _)).trans hKb_ge_exp
      have h2 : ((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ))) ≤ (K : ℝ) / (b : ℝ) := by
        conv_rhs => rw [← Real.rpow_one ((K : ℝ) / (b : ℝ))]
        exact Real.rpow_le_rpow_of_exponent_le hKb_ge1 (by rw [div_le_one (by positivity)]; linarith)
      exact h1.trans h2
    have hsqrt_lt_b : Real.sqrt (K : ℝ) < (b : ℝ) := (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hb_lo)
    have hKb_lt_b : (K : ℝ) / (b : ℝ) < (b : ℝ) := by
      rw [div_lt_iff₀ hb_pos]
      have hsq : Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) = (K : ℝ) := Real.mul_self_sqrt hK_pos.le
      nlinarith [Real.sqrt_nonneg (K : ℝ)]
    exact_mod_cast (lt_of_le_of_lt hzb_le_Kb hKb_lt_b)
  -- Drop constraints from (z_b, z] to apply card_ap_hit_sieve_upper with z_b
  let B_med_b := (Finset.Ioc y z_b).filter (· ∈ B')
  let V_b := ∏ p ∈ B_med_b, (1 - (A_n.card : ℝ) / (p : ℝ))
  have hsub_hit : (Finset.Icc 1 K).filter (fun k =>
      b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ⊆
      (Finset.Icc 1 K).filter (fun k =>
      b ∣ a + k * M ∧ ∀ p ∈ B_med_b, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) := by
    intro k hk
    have hkf := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hkf.1, hkf.2.1, fun p hp => hkf.2.2 p ?_⟩
    have hpf := Finset.mem_filter.mp hp
    have hpi := Finset.mem_Ioc.mp hpf.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpi.1, hpi.2.trans hzb_le_z⟩, hpf.2⟩
  have hsieve := card_ap_hit_sieve_upper B' hB' hge2 K n M y z_b a b A_n hn1 hAn hy hy16 hy_exp
    hyzb hzbb hbK hbB (hcop_M b hbB (by omega)) hcop_M hpi
  -- Bound V_b / V_z via V_ratio_bound + hf_good
  have hV_rat := V_ratio_bound B' n y z_b z A_n hAn hy hyzb hzb_le_z
  have hVz_pos : 0 < V_z := hV_rat.1
  have hlog_zb_ge : ((1 / 2 : ℝ) ^ j_idx) * Real.log (K : ℝ) / (16 * (s₀ : ℝ)) ≤ Real.log (z_b : ℝ) := by
    have h4 : (4 : ℝ) ≤ ((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ))) := by
      have : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy16
      linarith
    have h1 := log_floor_ge_half_log (((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ)))) h4
    rw [Real.log_rpow hKb_pos] at h1
    have hKb_pow : (K : ℝ) ^ ((1 / 2 : ℝ) ^ j_idx) ≤ (K : ℝ) / (b : ℝ) := by
      rw [le_div_iff₀ hb_pos]
      calc (K : ℝ) ^ ((1 / 2 : ℝ) ^ j_idx) * (b : ℝ)
          ≤ (K : ℝ) ^ ((1 / 2 : ℝ) ^ j_idx) * (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j_idx) :=
            mul_le_mul_of_nonneg_left hb_pow (by positivity)
        _ = (K : ℝ) := by rw [← Real.rpow_add hK_pos]; ring_nf; exact Real.rpow_one _
    have hlogKb : (1 / 2 : ℝ) ^ j_idx * Real.log (K : ℝ) ≤ Real.log ((K : ℝ) / (b : ℝ)) := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hK_pos _) hKb_pow
      rwa [Real.log_rpow hK_pos] at this
    have hmul := mul_le_mul_of_nonneg_left hlogKb (show (0 : ℝ) ≤ 1 / (8 * (s₀ : ℝ)) / 2 by positivity)
    linarith [show 1 / (8 * (s₀ : ℝ)) / 2 * ((1 / 2 : ℝ) ^ j_idx * Real.log (K : ℝ)) =
      (1 / 2 : ℝ) ^ j_idx * Real.log (K : ℝ) / (16 * (s₀ : ℝ)) by ring,
      show 1 / (8 * (s₀ : ℝ)) * Real.log ((K : ℝ) / (b : ℝ)) / 2 =
      1 / (8 * (s₀ : ℝ)) / 2 * Real.log ((K : ℝ) / (b : ℝ)) by ring]
  have hlogzb_pos : 0 < Real.log (z_b : ℝ) :=
    lt_of_lt_of_le (by positivity) hlog_zb_ge
  have hV_le : V_b ≤ Real.exp (((j_idx : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1))) * V_z := by
    have hinv_sub : ∑ p ∈ (Finset.Ioc z_b z).filter (· ∈ B'), (1 : ℝ) / (p : ℝ) ≤
        (∑ p ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (p : ℝ)) -
        (∑ p ∈ (Finset.range z_b).filter (· ∈ B'), (1 : ℝ) / (p : ℝ)) := by
      have hsub : (Finset.Ioc z_b z).filter (· ∈ B') ⊆
          ((Finset.range (K + 1)).filter (· ∈ B')) \ ((Finset.range z_b).filter (· ∈ B')) := by
        intro p hp
        have hpf := Finset.mem_filter.mp hp
        have hpi := Finset.mem_Ioc.mp hpf.1
        have hzK : z ≤ K := by
          have h1 : (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) ≤ (K : ℝ) := by
            conv_rhs => rw [← Real.rpow_one (K : ℝ)]
            exact Real.rpow_le_rpow_of_exponent_le hK_ge1 (by rw [div_le_one (by positivity)]; linarith)
          exact Nat.floor_le_of_le (by exact_mod_cast h1)
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
        exact ⟨⟨by omega, hpf.2⟩, fun h => by omega⟩
      rw [← Finset.sum_sdiff_eq_sub (Finset.filter_subset_filter _ (Finset.range_mono (by omega : z_b ≤ K + 1)))]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have hfg := hf_good z_b (by omega) (by omega)
    have hrat_le : Real.log (K : ℝ) / Real.log (z_b : ℝ) ≤ 16 * (s₀ : ℝ) * (2 : ℝ) ^ j_idx := by
      rw [div_le_iff₀ hlogzb_pos]
      have hmul := mul_le_mul_of_nonneg_left hlog_zb_ge (show (0 : ℝ) ≤ 16 * (s₀ : ℝ) * (2 : ℝ) ^ j_idx by positivity)
      have hcancel : 16 * (s₀ : ℝ) * (2 : ℝ) ^ j_idx * ((1 / 2 : ℝ) ^ j_idx * Real.log (K : ℝ) / (16 * (s₀ : ℝ))) =
          Real.log (K : ℝ) := by
        have h2p : (2 : ℝ) ^ j_idx * (1 / 2 : ℝ) ^ j_idx = 1 := by rw [← mul_pow]; norm_num
        calc 16 * (s₀ : ℝ) * (2 : ℝ) ^ j_idx * ((1 / 2 : ℝ) ^ j_idx * Real.log (K : ℝ) / (16 * (s₀ : ℝ)))
            = ((2 : ℝ) ^ j_idx * (1 / 2 : ℝ) ^ j_idx) * (16 * (s₀ : ℝ) / (16 * (s₀ : ℝ))) * Real.log (K : ℝ) := by ring
          _ = 1 * 1 * Real.log (K : ℝ) := by rw [h2p, div_self (by positivity)]
          _ = Real.log (K : ℝ) := by ring
      linarith
    have hlog_rat : Real.log (Real.log (K : ℝ) / Real.log (z_b : ℝ)) + 2 ≤
        ((j_idx : ℝ) + 1) * (Real.log (8 * (s₀ : ℝ)) + 10) := by
      have h1 := Real.log_le_log (div_pos hL_pos hlogzb_pos) hrat_le
      rw [show 16 * (s₀ : ℝ) * (2 : ℝ) ^ j_idx = (2 * (8 * (s₀ : ℝ))) * (2 : ℝ) ^ j_idx by ring,
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
      have hlog8_nn : 0 ≤ Real.log (8 * (s₀ : ℝ)) := Real.log_nonneg (by linarith only [hs₀_ge1])
      have hlog2 := Real.log_two_lt_d9
      nlinarith only [h1, hlog8_nn, hlog2, Nat.cast_nonneg (α := ℝ) j_idx]
    have h2n_sum : 2 * (n : ℝ) * ∑ p ∈ (Finset.Ioc z_b z).filter (· ∈ B'), (1 : ℝ) / (p : ℝ) ≤
        ((j_idx : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1)) := by
      have hlog8s_pos : 0 < Real.log (8 * (s₀ : ℝ)) + 10 := by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ 8 * (s₀ : ℝ) by linarith)]
      have hJ0_pos : (0 : ℝ) < (J₀ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) J₀]
      calc 2 * (n : ℝ) * ∑ p ∈ (Finset.Ioc z_b z).filter (· ∈ B'), (1 : ℝ) / (p : ℝ)
          ≤ 2 * (n : ℝ) * ((1 / (1000 * (n : ℝ) * ((J₀ : ℝ) + 1) * (Real.log (8 * (s₀ : ℝ)) + 10))) *
              (((j_idx : ℝ) + 1) * (Real.log (8 * (s₀ : ℝ)) + 10))) := by
            refine mul_le_mul_of_nonneg_left (hinv_sub.trans (hfg.trans ?_)) (by positivity)
            exact mul_le_mul_of_nonneg_left hlog_rat (by positivity)
        _ = ((j_idx : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1)) := by field_simp; ring
    have hdiv := hV_rat.2.2.2.trans (Real.exp_le_exp.mpr h2n_sum)
    exact (div_le_iff₀ hVz_pos).mp hdiv
  -- Bound error term (z_b : ℝ) ^ (2 * s₀) ≤ (K / b) / exp((3 / 4) * √(log K))
  have herr_zb : (z_b : ℝ) ^ (2 * s₀) ≤
      ((K : ℝ) / (b : ℝ)) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) := by
    have hzb_pow : (z_b : ℝ) ^ (2 * s₀) ≤ ((K : ℝ) / (b : ℝ)) ^ (1 / 4 : ℝ) := by
      have h1 : (z_b : ℝ) ≤ ((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ))) := Nat.floor_le (by positivity)
      calc (z_b : ℝ) ^ (2 * s₀) ≤ (((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ)))) ^ (2 * s₀) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) h1 _
        _ = ((K : ℝ) / (b : ℝ)) ^ (1 / (8 * (s₀ : ℝ)) * ((2 * s₀ : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hKb_pos.le]
        _ = ((K : ℝ) / (b : ℝ)) ^ (1 / 4 : ℝ) := by congr 1; push_cast; field_simp; ring
    have hexp34 : Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) ≤ ((K : ℝ) / (b : ℝ)) ^ (3 / 4 : ℝ) := by
      have := Real.rpow_le_rpow (Real.exp_pos _).le hKb_ge_exp (by norm_num : (0 : ℝ) ≤ 3 / 4)
      rwa [← Real.exp_mul, mul_comm] at this
    have hmul_eq : ((K : ℝ) / (b : ℝ)) ^ (1 / 4 : ℝ) * ((K : ℝ) / (b : ℝ)) ^ (3 / 4 : ℝ) = (K : ℝ) / (b : ℝ) := by
      rw [← Real.rpow_add hKb_pos]; norm_num
    refine hzb_pow.trans ?_
    rw [le_div_iff₀ (Real.exp_pos _)]
    calc ((K : ℝ) / (b : ℝ)) ^ (1 / 4 : ℝ) * Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ)))
        ≤ ((K : ℝ) / (b : ℝ)) ^ (1 / 4 : ℝ) * ((K : ℝ) / (b : ℝ)) ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hexp34 (by positivity)
      _ = (K : ℝ) / (b : ℝ) := hmul_eq
  calc (((Finset.Icc 1 K).filter (fun k =>
          b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ)
      ≤ (((Finset.Icc 1 K).filter (fun k =>
          b ∣ a + k * M ∧ ∀ p ∈ B_med_b, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub_hit)
    _ ≤ (102 / 100 : ℝ) * (2 * (K : ℝ) / (b : ℝ)) * V_b + (z_b : ℝ) ^ (2 * s₀) := hsieve
    _ ≤ (102 / 100 : ℝ) * (2 * (K : ℝ) / (b : ℝ)) *
          (Real.exp (((j_idx : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1))) * V_z) +
          ((K : ℝ) / (b : ℝ)) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left hV_le (by positivity)) herr_zb
    _ = (204 / 100 : ℝ) * ((K : ℝ) / (b : ℝ)) *
          Real.exp (((j_idx : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1))) * V_z +
          ((K : ℝ) / (b : ℝ)) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) := by ring

/-- Common error bound for Ranges 2 & 3:
    `n * K * (∑_{b ≤ K, b ∈ B'} 1 / b) / exp((3 / 4) * √(log K)) ≤ (1 / 100) * K * V_z`. -/
private lemma range23_err_le (K n : ℕ) (V_z S_inv : ℝ) (hn1 : 1 ≤ n)
    (hL_ge : (1000 * (n : ℝ)) ^ 4 ≤ Real.log (K : ℝ))
    (hS_le : S_inv ≤ Real.log (K : ℝ))
    (hVz_ge : 1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤ V_z) :
    (n : ℝ) * (K : ℝ) * S_inv / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) ≤
      (1 / 100 : ℝ) * (K : ℝ) * V_z := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hL_pos : (0 : ℝ) < Real.log (K : ℝ) := lt_of_lt_of_le (by positivity) hL_ge
  have hL_ge1 : (1 : ℝ) ≤ Real.log (K : ℝ) :=
    (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1000 * (n : ℝ))).trans hL_ge
  have hexp_ge : ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) ^ 4 / 24 ≤
      Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) := by
    have h4 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ)) by positivity) 5
    simp [Finset.sum_range_succ, Nat.factorial] at h4
    have hsq_nn : 0 ≤ (3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ)) := by positivity
    nlinarith [pow_nonneg hsq_nn 2, pow_nonneg hsq_nn 3]
  have hpow4 : ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) ^ 4 = (81 / 256 : ℝ) * (Real.log (K : ℝ)) ^ 2 := by
    rw [mul_pow, show (Real.sqrt (Real.log (K : ℝ))) ^ 4 = ((Real.sqrt (Real.log (K : ℝ))) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hL_pos.le]; norm_num
  have hdenom : 100 * (n : ℝ) * Real.log (K : ℝ) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤
      Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) := by
    have hL4_ge : 1000 * (n : ℝ) ≤ (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) hL_ge (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one] at h1
    have hL4_pow4 : ((Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) ^ 4 = Real.log (K : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]; norm_num
    have hL4_pos : 0 < (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL_pos _
    have hcomp : 100 * (n : ℝ) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤ (81 / 6144 : ℝ) * Real.log (K : ℝ) := by
      have hcube : 100 * (n : ℝ) ≤ (81 / 6144 : ℝ) * ((Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) ^ 3 := by
        have h1 : (1000 : ℝ) ^ 3 * (n : ℝ) ^ 3 ≤ ((Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) ^ 3 := by
          have := pow_le_pow_left₀ (by positivity) hL4_ge 3
          rwa [mul_pow] at this
        have hn3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
          calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hnR (by norm_num)
        nlinarith
      calc 100 * (n : ℝ) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)
          ≤ (81 / 6144 : ℝ) * ((Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) ^ 3 * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right hcube hL4_pos.le
        _ = (81 / 6144 : ℝ) * ((Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) ^ 4 := by ring
        _ = (81 / 6144 : ℝ) * Real.log (K : ℝ) := by rw [hL4_pow4]
    have hmul := mul_le_mul_of_nonneg_right hcomp hL_pos.le
    linarith [hpow4, hexp_ge, show (81 / 256 : ℝ) * (Real.log (K : ℝ)) ^ 2 / 24 = (81 / 6144 : ℝ) * Real.log (K : ℝ) * Real.log (K : ℝ) by ring,
      show 100 * (n : ℝ) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) * Real.log (K : ℝ) =
        100 * (n : ℝ) * Real.log (K : ℝ) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) by ring]
  have hK_nn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hdiv_le : (n : ℝ) * S_inv / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) ≤
      (1 / 100 : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) := by
    have hL4_pos : 0 < (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL_pos _
    rw [div_le_iff₀ (Real.exp_pos _)]
    calc (n : ℝ) * S_inv ≤ (n : ℝ) * Real.log (K : ℝ) := mul_le_mul_of_nonneg_left hS_le hn_pos.le
      _ = (1 / 100 : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) *
            (100 * (n : ℝ) * Real.log (K : ℝ) * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) := by field_simp
      _ ≤ (1 / 100 : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) *
            Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) :=
          mul_le_mul_of_nonneg_left hdenom (by positivity)
  calc (n : ℝ) * (K : ℝ) * S_inv / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ)))
      = (K : ℝ) * ((n : ℝ) * S_inv / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ)))) := by ring
    _ ≤ (K : ℝ) * ((1 / 100 : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hdiv_le hK_nn
    _ ≤ (K : ℝ) * ((1 / 100 : ℝ) * V_z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVz_ge (by norm_num)) hK_nn
    _ = (1 / 100 : ℝ) * (K : ℝ) * V_z := by ring

/-- Range 2: `b ∈ (⌊√K⌋₊, ⌊K ^ (1 - 2 ^ (-J₀))⌋₊]`. -/
private lemma range2_bound (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (K n M y J₀ : ℕ) (A_n : Finset ℕ)
    (hn1 : 1 ≤ n) (hAn : A_n ⊆ Finset.Icc 1 n) (hJ₀ : 6 ≤ J₀)
    (hy : 2 * n + 2 ≤ y) (hy16 : 16 ≤ y)
    (hy_exp : Real.exp (2000 * (n : ℝ)) ≤ (y : ℝ))
    (hcop_M : ∀ p ∈ B', y < p → Nat.Coprime p M)
    (hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ))
    (hK_ge : 16 ≤ K)
    (hL_ge : (1000 * (n : ℝ) * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀) ^ 4 ≤ Real.log (K : ℝ))
    (hfK_le : ∑ p ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (p : ℝ) ≤ Real.log (K : ℝ))
    (hf_good : ∀ a' : ℕ, 16 ≤ a' → a' ≤ K →
      (∑ p ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (p : ℝ)) -
      (∑ p ∈ (Finset.range a').filter (· ∈ B'), (1 : ℝ) / (p : ℝ)) ≤
        (1 / (1000 * (n : ℝ) * ((J₀ : ℝ) + 1) * (Real.log (8 * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ)) + 10))) *
        (Real.log (Real.log (K : ℝ) / Real.log (a' : ℝ)) + 2))
    (hVz_ge : 1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤
      ∏ p ∈ (Finset.Ioc y ⌊(K : ℝ) ^ (1 / (8 * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ)))⌋₊).filter (· ∈ B'),
        (1 - (A_n.card : ℝ) / (p : ℝ))) :
    let s₀ : ℕ := 800 * n + 80000 * n ^ 2 + 1
    let z : ℕ := ⌊(K : ℝ) ^ (1 / (8 * (s₀ : ℝ)))⌋₊
    let R₂ := (Finset.Ioc ⌊Real.sqrt (K : ℝ)⌋₊ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J₀)⌋₊).filter (· ∈ B')
    let B_med := (Finset.Ioc y z).filter (· ∈ B')
    let V_z := ∏ p ∈ B_med, (1 - (A_n.card : ℝ) / (p : ℝ))
    (((Finset.Icc 1 K).filter (fun k =>
      (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
      ∃ a ∈ A_n, ∃ b ∈ R₂, b ∣ a + k * M)).card : ℝ) ≤
      (2 / 100 : ℝ) * (K : ℝ) * V_z := by
  intro s₀ z R₂ B_med V_z
  have hs₀_ge1 : (1 : ℝ) ≤ (s₀ : ℝ) := by dsimp only [s₀]; exact_mod_cast (by omega : 1 ≤ s₀)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have h2J_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ J₀ := one_le_pow₀ (by norm_num)
  have hL_ge' : (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 4 ≤ Real.log (K : ℝ) := by
    have h1 : 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) ≤
        1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ :=
      le_mul_of_one_le_right (by positivity) h2J_ge1
    exact (pow_le_pow_left₀ (by positivity) h1 4).trans hL_ge
  have hL_pos : 0 < Real.log (K : ℝ) := lt_of_lt_of_le (by positivity) hL_ge'
  -- Show ⌊K ^ (1 - 2 ^ (-J₀))⌋₊ ≤ ⌊K / exp(√(log K))⌋₊
  have hhi_le : ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J₀)⌋₊ ≤
      ⌊(K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ)))⌋₊ := by
    refine Nat.floor_mono ?_
    rw [Real.rpow_def_of_pos hK_pos, show Real.log (K : ℝ) * (1 - (1 / 2 : ℝ) ^ J₀) =
      Real.log (K : ℝ) - (1 / 2 : ℝ) ^ J₀ * Real.log (K : ℝ) by ring,
      Real.exp_sub, Real.exp_log hK_pos]
    refine div_le_div_of_nonneg_left hK_pos.le (Real.exp_pos _) (Real.exp_le_exp.mpr ?_)
    have hsqrt_le : Real.sqrt (Real.log (K : ℝ)) * (2 : ℝ) ^ J₀ ≤ Real.log (K : ℝ) := by
      have h1 : (2 : ℝ) ^ J₀ ≤ Real.sqrt (Real.log (K : ℝ)) := by
        rw [Real.le_sqrt (by positivity) hL_pos.le]
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have hbase : (2 : ℝ) ^ J₀ ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ := by
          have h1 : (1 : ℝ) ≤ (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := mul_three_ge_one hnR hs₀_ge1 (by linarith)
          exact le_mul_of_one_le_left (by positivity) (by linarith)
        have hsq : ((2 : ℝ) ^ J₀) ^ 2 ≤ ((2 : ℝ) ^ J₀) ^ 4 := pow_le_pow_right₀ h2J_ge1 (by norm_num)
        exact hsq.trans ((pow_le_pow_left₀ (by positivity) hbase 4).trans hL_ge)
      calc Real.sqrt (Real.log (K : ℝ)) * (2 : ℝ) ^ J₀
          ≤ Real.sqrt (Real.log (K : ℝ)) * Real.sqrt (Real.log (K : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
        _ = Real.log (K : ℝ) := Real.mul_self_sqrt hL_pos.le
    have h2inv : (1 / 2 : ℝ) ^ J₀ = ((2 : ℝ) ^ J₀)⁻¹ := by rw [one_div, inv_pow]
    rw [h2inv, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    exact hsqrt_le
  have hstep1 := card_bad_in_range_le B' K M y z A_n R₂
  have hexp_le2 : Real.exp (((J₀ : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1))) ≤ 2 := by
    have hJ0_pos : (0 : ℝ) < (J₀ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) J₀]
    rw [show ((J₀ : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1)) = 1 / 500 by field_simp]
    have h1 := Real.exp_bound (show |(1 / 500 : ℝ)| ≤ 1 by norm_num) (show 0 < 1 by omega)
    simp at h1
    linarith [abs_le.mp h1]
  have hterm : ∀ a ∈ A_n, ∀ b ∈ R₂,
      (((Finset.Icc 1 K).filter (fun k =>
        b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
      (408 / 100 : ℝ) * (K : ℝ) * V_z * (1 / (b : ℝ)) +
        (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (1 / (b : ℝ)) := by
    intro a _ b hb
    have hbf := Finset.mem_filter.mp hb
    have hbi := Finset.mem_Ioc.mp hbf.1
    have hb_pow : (b : ℝ) ≤ (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J₀) :=
      (Nat.cast_le.mpr hbi.2).trans (Nat.floor_le (by positivity))
    have hzbt := zb_sieve_term B' hB' hge2 K n M y J₀ a b J₀ A_n hn1 hAn hy hy16 hy_exp
      hcop_M hpi hK_ge hL_ge' hf_good hbf.2 hbi.1 (hbi.2.trans hhi_le) hb_pow (by omega)
    have hVz_nn : 0 ≤ V_z := le_trans (by positivity) hVz_ge
    refine hzbt.trans ?_
    have h1 : (204 / 100 : ℝ) * ((K : ℝ) / (b : ℝ)) *
        Real.exp (((J₀ : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1))) * V_z ≤
        (408 / 100 : ℝ) * (K : ℝ) * V_z * (1 / (b : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp_le2 (show (0 : ℝ) ≤ (204 / 100 : ℝ) * ((K : ℝ) / (b : ℝ)) by positivity)) hVz_nn
      linarith [show (204 / 100 : ℝ) * ((K : ℝ) / (b : ℝ)) * 2 * V_z = (408 / 100 : ℝ) * (K : ℝ) * V_z * (1 / (b : ℝ)) by ring]
    linarith [show ((K : ℝ) / (b : ℝ)) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) =
      (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (1 / (b : ℝ)) by ring]
  have hsum_le : ∑ a ∈ A_n, ∑ b ∈ R₂,
      (((Finset.Icc 1 K).filter (fun k =>
        b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
      (A_n.card : ℝ) * ((408 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ)) +
        (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ))) := by
    have h1 := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    refine h1.trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]; congr 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Bound ∑_{b ∈ R₂} 1/b ≤ 1 / (1000 * n) via hf_good at a = ⌊√K⌋₊
  have hR2_sub_K : R₂ ⊆ (Finset.range (K + 1)).filter (· ∈ B') := by
    intro b hb
    have hbf := Finset.mem_filter.mp hb
    have hbi := Finset.mem_Ioc.mp hbf.1
    have hbK : b ≤ K := by
      have h1 : (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J₀) ≤ (K : ℝ) := by
        conv_rhs => rw [← Real.rpow_one (K : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ K)) (by linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) J₀])
      exact hbi.2.trans (Nat.floor_le_of_le (by exact_mod_cast h1))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbf.2⟩
  have hinv_R2 : ∑ b ∈ R₂, (1 : ℝ) / (b : ℝ) ≤ 1 / (1000 * (n : ℝ)) := by
    let a₂ := ⌊Real.sqrt (K : ℝ)⌋₊
    have hK_ge_256 : (256 : ℝ) ≤ (K : ℝ) := by
      have hL10 : (10 : ℝ) ≤ Real.log (K : ℝ) := by
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        have h1 : (1000 : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by
          have := mul_three_ge_one hnR hs₀_ge1 (by linarith : (1 : ℝ) ≤ Real.log (y : ℝ) + 10); linarith
        have h2 : (1000 : ℝ) ^ 4 ≤ Real.log (K : ℝ) := (pow_le_pow_left₀ (by norm_num) h1 4).trans hL_ge'
        linarith
      have h1 := Real.exp_le_exp.mpr hL10
      rw [Real.exp_log hK_pos] at h1
      have h2 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10) 5
      simp [Finset.sum_range_succ, Nat.factorial] at h2
      norm_num at h2
      linarith only [h1, h2]
    have ha₂_ge16 : 16 ≤ a₂ := Nat.le_floor (by
      rw [Real.le_sqrt (by norm_num) hK_pos.le]
      linarith only [hK_ge_256, show ((16 : ℕ) : ℝ) ^ 2 = 256 by norm_num])
    have ha₂_leK : a₂ ≤ K := Nat.floor_le_of_le (by rw [Real.sqrt_le_iff]; exact ⟨hK_pos.le, by nlinarith⟩)
    have hsub : R₂ ⊆ ((Finset.range (K + 1)).filter (· ∈ B')) \ ((Finset.range a₂).filter (· ∈ B')) := by
      intro b hb
      have hbf := Finset.mem_filter.mp hb
      have hbi := Finset.mem_Ioc.mp hbf.1
      rw [Finset.mem_sdiff]
      exact ⟨hR2_sub_K hb, fun h => by have := Finset.mem_range.mp (Finset.mem_filter.mp h).1; omega⟩
    have hdiff : ∑ b ∈ ((Finset.range (K + 1)).filter (· ∈ B')) \ ((Finset.range a₂).filter (· ∈ B')), (1 : ℝ) / (b : ℝ) =
        (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) -
        (∑ b ∈ (Finset.range a₂).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) :=
      Finset.sum_sdiff_eq_sub (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    have hlog_a2 : Real.log (K : ℝ) / 4 ≤ Real.log (a₂ : ℝ) := by
      have h4 : (4 : ℝ) ≤ Real.sqrt (K : ℝ) := by rw [Real.le_sqrt (by norm_num) hK_pos.le]; linarith
      have h1 := log_floor_ge_half_log (Real.sqrt (K : ℝ)) h4
      rw [Real.log_sqrt hK_pos.le] at h1; linarith
    have hrat : Real.log (K : ℝ) / Real.log (a₂ : ℝ) ≤ 4 := by
      rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hlog_a2)]; linarith
    have hlog_rat : Real.log (Real.log (K : ℝ) / Real.log (a₂ : ℝ)) + 2 ≤ Real.log (8 * (s₀ : ℝ)) + 10 := by
      have h1 := Real.log_le_log (div_pos hL_pos (lt_of_lt_of_le (by positivity) hlog_a2)) hrat
      have h4 : Real.log 4 = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      linarith [Real.log_two_lt_d9, Real.log_nonneg (show (1 : ℝ) ≤ 8 * (s₀ : ℝ) by linarith)]
    have hfg := hf_good a₂ ha₂_ge16 ha₂_leK
    have hlog8s_pos : 0 < Real.log (8 * (s₀ : ℝ)) + 10 := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 8 * (s₀ : ℝ) by linarith)]
    have hJ0_ge1 : (1 : ℝ) ≤ (J₀ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) J₀]
    calc ∑ b ∈ R₂, (1 : ℝ) / (b : ℝ)
        ≤ (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) -
          (∑ b ∈ (Finset.range a₂).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) := by
            rw [← hdiff]; exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ (1 / (1000 * (n : ℝ) * ((J₀ : ℝ) + 1) * (Real.log (8 * (s₀ : ℝ)) + 10))) *
            (Real.log (8 * (s₀ : ℝ)) + 10) :=
          hfg.trans (mul_le_mul_of_nonneg_left hlog_rat (by positivity))
      _ ≤ (1 / (1000 * (n : ℝ) * 1 * (Real.log (8 * (s₀ : ℝ)) + 10))) *
            (Real.log (8 * (s₀ : ℝ)) + 10) := by
          refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ0_ge1 (by positivity)) hlog8s_pos.le)) hlog8s_pos.le
      _ = 1 / (1000 * (n : ℝ)) := by field_simp
  have hcard_An : (A_n.card : ℝ) ≤ (n : ℝ) := by
    have := Finset.card_le_card hAn; rw [Nat.card_Icc] at this; exact_mod_cast (by omega : A_n.card ≤ n)
  have hVz_nn : 0 ≤ V_z := le_trans (by positivity) hVz_ge
  have hmain : (A_n.card : ℝ) * ((408 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ))) ≤
      (1 / 100 : ℝ) * (K : ℝ) * V_z := by
    calc _ ≤ (n : ℝ) * ((408 / 100 : ℝ) * (K : ℝ) * V_z * (1 / (1000 * (n : ℝ)))) := by
          refine mul_le_mul hcard_An (mul_le_mul_of_nonneg_left hinv_R2 (by positivity))
            (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)) hn_pos.le
      _ = (408 / 100000 : ℝ) * (K : ℝ) * V_z := by field_simp; ring
      _ ≤ (1 / 100 : ℝ) * (K : ℝ) * V_z := by nlinarith [mul_nonneg hK_pos.le hVz_nn]
  have herr : (A_n.card : ℝ) * ((K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
      (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ))) ≤ (1 / 100 : ℝ) * (K : ℝ) * V_z := by
    have hS_le : ∑ b ∈ R₂, (1 : ℝ) / (b : ℝ) ≤ Real.log (K : ℝ) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hR2_sub_K fun _ _ _ => by positivity).trans hfK_le
    have hL_n : (1000 * (n : ℝ)) ^ 4 ≤ Real.log (K : ℝ) := by
      have h1 : 1000 * (n : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by
        have : (1 : ℝ) ≤ (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by nlinarith
        nlinarith
      exact (pow_le_pow_left₀ (by positivity) h1 4).trans hL_ge'
    have h1 := range23_err_le K n V_z (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ)) hn1 hL_n hS_le hVz_ge
    have h2 : (A_n.card : ℝ) * ((K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
        (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ))) ≤
        (n : ℝ) * (K : ℝ) * (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ)) /
          Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) := by
      rw [show (n : ℝ) * (K : ℝ) * (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ)) /
          Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) =
        (n : ℝ) * ((K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
          (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ))) by ring]
      exact mul_le_mul_of_nonneg_right hcard_An (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity))
    exact h2.trans h1
  calc _ ≤ (A_n.card : ℝ) * ((408 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ)) +
            (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ))) :=
        hstep1.trans hsum_le
    _ = (A_n.card : ℝ) * ((408 / 100 : ℝ) * (K : ℝ) * V_z * (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ))) +
          (A_n.card : ℝ) * ((K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
            (∑ b ∈ R₂, (1 : ℝ) / (b : ℝ))) := by ring
    _ ≤ (1 / 100 : ℝ) * (K : ℝ) * V_z + (1 / 100 : ℝ) * (K : ℝ) * V_z := add_le_add hmain herr
    _ = (2 / 100 : ℝ) * (K : ℝ) * V_z := by ring

set_option maxHeartbeats 400000 in
/-- Range 3: dyadic shells covering `(⌊K ^ (1 - 2 ^ (-J₀))⌋₊, ⌊K / exp(√(log K))⌋₊]`. -/
private lemma range3_bound (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (K n M y J₀ : ℕ) (A_n : Finset ℕ)
    (hn1 : 1 ≤ n) (hAn : A_n ⊆ Finset.Icc 1 n) (hJ₀ : 6 ≤ J₀)
    (hJ₀_pow : 3000 * (n : ℝ) ≤ (5 / 3 : ℝ) ^ J₀)
    (hy : 2 * n + 2 ≤ y) (hy16 : 16 ≤ y)
    (hy_exp : Real.exp (2000 * (n : ℝ)) ≤ (y : ℝ))
    (hcop_M : ∀ p ∈ B', y < p → Nat.Coprime p M)
    (hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ))
    (hK_ge : max 16 (y ^ 2) ≤ K)
    (hL_ge : (1000 * (n : ℝ) * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀) ^ 4 ≤ Real.log (K : ℝ))
    (hfK_le : ∑ p ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (p : ℝ) ≤ Real.log (K : ℝ))
    (hf_good : ∀ a' : ℕ, 16 ≤ a' → a' ≤ K →
      (∑ p ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (p : ℝ)) -
      (∑ p ∈ (Finset.range a').filter (· ∈ B'), (1 : ℝ) / (p : ℝ)) ≤
        (1 / (1000 * (n : ℝ) * ((J₀ : ℝ) + 1) * (Real.log (8 * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ)) + 10))) *
        (Real.log (Real.log (K : ℝ) / Real.log (a' : ℝ)) + 2))
    (hVz_ge : 1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤
      ∏ p ∈ (Finset.Ioc y ⌊(K : ℝ) ^ (1 / (8 * ((800 * n + 80000 * n ^ 2 + 1 : ℕ) : ℝ)))⌋₊).filter (· ∈ B'),
        (1 - (A_n.card : ℝ) / (p : ℝ))) :
    let s₀ : ℕ := 800 * n + 80000 * n ^ 2 + 1
    let z : ℕ := ⌊(K : ℝ) ^ (1 / (8 * (s₀ : ℝ)))⌋₊
    let B_cut_exp : ℕ := ⌊(K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ)))⌋₊
    let R₃ := (Finset.Ioc ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J₀)⌋₊ B_cut_exp).filter (· ∈ B')
    let B_med := (Finset.Ioc y z).filter (· ∈ B')
    let V_z := ∏ p ∈ B_med, (1 - (A_n.card : ℝ) / (p : ℝ))
    (((Finset.Icc 1 K).filter (fun k =>
      (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
      ∃ a ∈ A_n, ∃ b ∈ R₃, b ∣ a + k * M)).card : ℝ) ≤
      (6 / 100 : ℝ) * (K : ℝ) * V_z := by
  intro s₀ z B_cut_exp R₃ B_med V_z
  have hs₀_ge1 : (1 : ℝ) ≤ (s₀ : ℝ) := by dsimp only [s₀]; exact_mod_cast (by omega : 1 ≤ s₀)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hK16 : 16 ≤ K := le_trans (le_max_left _ _) hK_ge
  have hKy2 : y ^ 2 ≤ K := le_trans (le_max_right _ _) hK_ge
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have h2J_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ J₀ := one_le_pow₀ (by norm_num)
  have hL_ge' : (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 4 ≤ Real.log (K : ℝ) := by
    have h1 : 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) ≤
        1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ :=
      le_mul_of_one_le_right (by positivity) h2J_ge1
    exact (pow_le_pow_left₀ (by positivity) h1 4).trans hL_ge
  have hL_pos : 0 < Real.log (K : ℝ) := lt_of_lt_of_le (by positivity) hL_ge'
  have hsqrtL_ge100 : (100 : ℝ) ≤ Real.sqrt (Real.log (K : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) hL_pos.le]
    have h1 : (1000 : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by
      have := mul_three_ge_one hnR hs₀_ge1 (by linarith : (1 : ℝ) ≤ Real.log (y : ℝ) + 10); linarith
    have h2 : (1000 : ℝ) ^ 4 ≤ Real.log (K : ℝ) := (pow_le_pow_left₀ (by norm_num) h1 4).trans hL_ge'
    linarith
  let J_max : ℕ := Nat.log 2 ⌈Real.sqrt (Real.log (K : ℝ))⌉₊ + 1
  have hceil_pos : 0 < ⌈Real.sqrt (Real.log (K : ℝ))⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hBcut_le_Jmax : B_cut_exp ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J_max)⌋₊ := by
    refine Nat.floor_mono ?_
    rw [Real.rpow_def_of_pos hK_pos, show Real.log (K : ℝ) * (1 - (1 / 2 : ℝ) ^ J_max) =
      Real.log (K : ℝ) - (1 / 2 : ℝ) ^ J_max * Real.log (K : ℝ) by ring,
      Real.exp_sub, Real.exp_log hK_pos]
    refine div_le_div_of_nonneg_left hK_pos.le (Real.exp_pos _) (Real.exp_le_exp.mpr ?_)
    have h2Jmax : Real.sqrt (Real.log (K : ℝ)) < (2 : ℝ) ^ J_max := by
      have hnat : ⌈Real.sqrt (Real.log (K : ℝ))⌉₊ < 2 ^ J_max := Nat.lt_pow_succ_log_self (by omega) _
      exact (Nat.le_ceil _).trans_lt (by exact_mod_cast hnat)
    have h2inv : (1 / 2 : ℝ) ^ J_max = ((2 : ℝ) ^ J_max)⁻¹ := by rw [one_div, inv_pow]
    rw [h2inv, inv_mul_eq_div, div_le_iff₀ (by positivity)]
    calc Real.log (K : ℝ) = Real.sqrt (Real.log (K : ℝ)) * Real.sqrt (Real.log (K : ℝ)) :=
          (Real.mul_self_sqrt hL_pos.le).symm
      _ ≤ Real.sqrt (Real.log (K : ℝ)) * (2 : ℝ) ^ J_max :=
          mul_le_mul_of_nonneg_left h2Jmax.le (Real.sqrt_nonneg _)
  let Sh : ℕ → Finset ℕ := fun j =>
    (Finset.Ioc ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j)⌋₊
      (min B_cut_exp ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1))⌋₊)).filter (· ∈ B')
  have hcover : R₃ ⊆ (Finset.Ico J₀ J_max).biUnion Sh := by
    intro b hb
    have hbf := Finset.mem_filter.mp hb
    have hbi := Finset.mem_Ioc.mp hbf.1
    have hne : ((Finset.Ico J₀ J_max).filter (fun j => b ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1))⌋₊)).Nonempty := by
      have hJ0_lt : J₀ < J_max := by
        have h1 : (2 : ℝ) ^ J₀ ≤ Real.sqrt (Real.log (K : ℝ)) := by
          rw [Real.le_sqrt (by positivity) hL_pos.le]
          have hbase : (2 : ℝ) ^ J₀ ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ := by
            have := mul_three_ge_one hnR hs₀_ge1 (by linarith : (1 : ℝ) ≤ Real.log (y : ℝ) + 10)
            exact le_mul_of_one_le_left (by positivity) (by linarith)
          have hsq : ((2 : ℝ) ^ J₀) ^ 2 ≤ ((2 : ℝ) ^ J₀) ^ 4 := pow_le_pow_right₀ h2J_ge1 (by norm_num)
          exact hsq.trans ((pow_le_pow_left₀ (by positivity) hbase 4).trans hL_ge)
        have h2 : 2 ^ J₀ ≤ ⌈Real.sqrt (Real.log (K : ℝ))⌉₊ := by
          exact_mod_cast (h1.trans (Nat.le_ceil _))
        have h3 : J₀ ≤ Nat.log 2 ⌈Real.sqrt (Real.log (K : ℝ))⌉₊ := Nat.le_log_of_pow_le (by omega) h2
        omega
      refine ⟨J_max - 1, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩⟩
      rw [Nat.sub_add_cancel (by omega)]
      exact hbi.2.trans hBcut_le_Jmax
    let j := ((Finset.Ico J₀ J_max).filter (fun j => b ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1))⌋₊)).min' hne
    have hj_mem := Finset.min'_mem _ hne
    have hj_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hj_mem).1
    have hj_le : b ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1))⌋₊ := (Finset.mem_filter.mp hj_mem).2
    have hj_gt : ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j)⌋₊ < b := by
      by_cases hj0 : j = J₀
      · rw [hj0]; exact hbi.1
      · by_contra hnot; push Not at hnot
        have hprev : j - 1 ∈ (Finset.Ico J₀ J_max).filter (fun j => b ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1))⌋₊) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
          rwa [Nat.sub_add_cancel (by omega)]
        have := Finset.min'_le _ (j - 1) hprev
        omega
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ico.mpr hj_ico,
      Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hj_gt, le_min hbi.2 hj_le⟩, hbf.2⟩⟩
  have hstep1 := card_bad_in_range_le B' K M y z A_n R₃
  have hexp500 : Real.exp (1 / 500 : ℝ) ≤ 6 / 5 := by
    have h1 := Real.exp_bound (show |(1 / 500 : ℝ)| ≤ 1 by norm_num) (show 0 < 1 by omega)
    simp at h1; linarith [abs_le.mp h1]
  have hshell_bound : ∀ j ∈ Finset.Ico J₀ J_max,
      ∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ) ≤ 18 * (1 / 2 : ℝ) ^ j := by
    intro j hj
    have hj_ico := Finset.mem_Ico.mp hj
    let a_j := ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j)⌋₊
    let c_j := min B_cut_exp ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1))⌋₊
    by_cases hac : a_j ≤ c_j
    · have hhalf_le : (1 / 2 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ j := by
        have : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        linarith
      have hsqrt_le_pow : Real.sqrt (K : ℝ) ≤ (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hK_ge1 hhalf_le
      have hy_le_aj : y ≤ a_j := by
        have hy_le_sqrt : (y : ℝ) ≤ Real.sqrt (K : ℝ) := by
          rw [Real.le_sqrt (Nat.cast_nonneg y) hK_pos.le]
          exact_mod_cast hKy2
        exact Nat.le_floor (hy_le_sqrt.trans hsqrt_le_pow)
      have hsum_inv := sum_inv_coprime_Ioc_le B' hB' hge2 a_j c_j (by omega) hac
        (fun k hk => hpi k (hy_le_aj.trans hk))
      have h2j_le : (2 : ℝ) ^ j ≤ 2 * Real.sqrt (Real.log (K : ℝ)) := by
        have h1 : 2 ^ j ≤ ⌈Real.sqrt (Real.log (K : ℝ))⌉₊ := by
          have hle : j ≤ Nat.log 2 ⌈Real.sqrt (Real.log (K : ℝ))⌉₊ := by omega
          exact (Nat.pow_le_pow_right (by omega) hle).trans (Nat.pow_log_le_self 2 (by omega))
        have h2 : (⌈Real.sqrt (Real.log (K : ℝ))⌉₊ : ℝ) < Real.sqrt (Real.log (K : ℝ)) + 1 :=
          Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
        have h1R : (2 : ℝ) ^ j ≤ (⌈Real.sqrt (Real.log (K : ℝ))⌉₊ : ℝ) := by exact_mod_cast h1
        linarith
      have h2jL_ge : Real.sqrt (Real.log (K : ℝ)) / 2 ≤ (1 / 2 : ℝ) ^ j * Real.log (K : ℝ) := by
        have h2inv : (1 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ := by rw [one_div, inv_pow]
        rw [h2inv, inv_mul_eq_div, le_div_iff₀ (by positivity)]
        calc Real.sqrt (Real.log (K : ℝ)) / 2 * (2 : ℝ) ^ j
            ≤ Real.sqrt (Real.log (K : ℝ)) / 2 * (2 * Real.sqrt (Real.log (K : ℝ))) :=
              mul_le_mul_of_nonneg_left h2j_le (by positivity)
          _ = Real.sqrt (Real.log (K : ℝ)) * Real.sqrt (Real.log (K : ℝ)) := by ring
          _ = Real.log (K : ℝ) := Real.mul_self_sqrt hL_pos.le
      have hlog_cj_le : Real.log (c_j : ℝ) ≤ (1 - (1 / 2 : ℝ) ^ (j + 1)) * Real.log (K : ℝ) := by
        have h1 : (c_j : ℝ) ≤ (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1)) :=
          (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le (by positivity))
        have h2 := Real.log_le_log (by exact_mod_cast (by omega : 0 < c_j)) h1
        rwa [Real.log_rpow hK_pos] at h2
      have hlog_aj_ge : (1 - (1 / 2 : ℝ) ^ j) * Real.log (K : ℝ) - 1 ≤ Real.log (a_j : ℝ) := by
        have hfl : (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j) - 1 < (a_j : ℝ) := Nat.sub_one_lt_floor _
        have hpow_ge4 : (4 : ℝ) ≤ (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j) := by
          have : (4 : ℝ) ≤ Real.sqrt (K : ℝ) := by
            rw [Real.le_sqrt (by norm_num) hK_pos.le]; exact_mod_cast hK16
          linarith
        have haj_half : (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j) / 2 ≤ (a_j : ℝ) := by linarith
        have h1 := Real.log_le_log (by positivity) haj_half
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hK_pos] at h1
        linarith [Real.log_two_lt_d9]
      have hlog_aj_q : Real.log (K : ℝ) / 4 ≤ Real.log (a_j : ℝ) := by
        have hL_ge4 : (4 : ℝ) ≤ Real.log (K : ℝ) := by
          have := Real.mul_self_sqrt hL_pos.le; nlinarith
        nlinarith
      have hlog_aj_pos : 0 < Real.log (a_j : ℝ) := lt_of_lt_of_le (by positivity) hlog_aj_q
      have hlog_cj_q : Real.log (K : ℝ) / 4 ≤ Real.log (c_j : ℝ) :=
        hlog_aj_q.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < a_j)) (by exact_mod_cast hac))
      have hlog_rat : Real.log (Real.log (c_j : ℝ) / Real.log (a_j : ℝ)) ≤ 4 * (1 / 2 : ℝ) ^ j := by
        have h1 := Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le (by positivity) hlog_cj_q) hlog_aj_pos)
        have h2 : Real.log (c_j : ℝ) / Real.log (a_j : ℝ) - 1 =
            (Real.log (c_j : ℝ) - Real.log (a_j : ℝ)) / Real.log (a_j : ℝ) := by field_simp
        have hnum : Real.log (c_j : ℝ) - Real.log (a_j : ℝ) ≤ (1 / 2 : ℝ) ^ j * Real.log (K : ℝ) := by
          have hpow_half : (1 / 2 : ℝ) ^ (j + 1) = (1 / 2 : ℝ) ^ j / 2 := by rw [pow_succ]; ring
          rw [hpow_half] at hlog_cj_le
          linarith only [hlog_cj_le, hlog_aj_ge, h2jL_ge, hsqrtL_ge100]
        have h3 : (Real.log (c_j : ℝ) - Real.log (a_j : ℝ)) / Real.log (a_j : ℝ) ≤ 4 * (1 / 2 : ℝ) ^ j := by
          rw [div_le_iff₀ hlog_aj_pos]
          calc Real.log (c_j : ℝ) - Real.log (a_j : ℝ) ≤ (1 / 2 : ℝ) ^ j * Real.log (K : ℝ) := hnum
            _ = 4 * (1 / 2 : ℝ) ^ j * (Real.log (K : ℝ) / 4) := by ring
            _ ≤ 4 * (1 / 2 : ℝ) ^ j * Real.log (a_j : ℝ) :=
                mul_le_mul_of_nonneg_left hlog_aj_q (by positivity)
        linarith only [h1, h2, h3]
      have ht1 : 2 / Real.log (c_j : ℝ) ≤ (1 / 2 : ℝ) ^ j := by
        rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hlog_cj_q)]
        have hmul : (1 / 2 : ℝ) ^ j * (Real.log (K : ℝ) / 4) ≤ (1 / 2 : ℝ) ^ j * Real.log (c_j : ℝ) :=
          mul_le_mul_of_nonneg_left hlog_cj_q (by positivity)
        linarith only [hmul, h2jL_ge, hsqrtL_ge100]
      have ht2 : 8 / ((a_j : ℝ) * Real.log (a_j : ℝ)) ≤ (1 / 2 : ℝ) ^ j := by
        have haj4 : (4 : ℝ) ≤ (a_j : ℝ) := by exact_mod_cast (by omega : 4 ≤ a_j)
        have hprod : Real.log (K : ℝ) ≤ (a_j : ℝ) * Real.log (a_j : ℝ) := by
          nlinarith only [haj4, hlog_aj_q, hlog_aj_pos]
        rw [div_le_iff₀ (mul_pos (by linarith only [haj4]) hlog_aj_pos)]
        have hmul : (1 / 2 : ℝ) ^ j * Real.log (K : ℝ) ≤ (1 / 2 : ℝ) ^ j * ((a_j : ℝ) * Real.log (a_j : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        linarith only [hmul, h2jL_ge, hsqrtL_ge100]
      linarith only [hsum_inv, hlog_rat, ht1, ht2]
    · push Not at hac
      have hemp : Sh j = ∅ := by
        ext b; simp only [Sh, Finset.mem_filter, Finset.mem_Ioc, Finset.notMem_empty, iff_false]
        intro h; omega
      rw [hemp, Finset.sum_empty]; positivity
  -- Combine per-shell bounds
  have hVz_nn : 0 ≤ V_z := le_trans (by positivity) hVz_ge
  have hcard_An : (A_n.card : ℝ) ≤ (n : ℝ) := by
    have := Finset.card_le_card hAn; rw [Nat.card_Icc] at this; exact_mod_cast (by omega : A_n.card ≤ n)
  have hsum_a : ∀ a ∈ A_n,
      ∑ b ∈ R₃, (((Finset.Icc 1 K).filter (fun k =>
        b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
      (60 : ℝ) * (K : ℝ) * V_z * (∑ j ∈ Finset.Ico J₀ J_max, (3 / 5 : ℝ) ^ j) +
        (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
          (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) := by
    intro a _
    -- Partition R₃ across shells j ∈ Ico J₀ J_max (pairwise disjoint!)
    have hdisj : Set.PairwiseDisjoint (Finset.Ico J₀ J_max : Set ℕ) Sh := by
      intro i _ j _ hij
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro b hbi hbj
      have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hbi).1
      have hj := Finset.mem_Ioc.mp (Finset.mem_filter.mp hbj).1
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hle : (1 - (1 / 2 : ℝ) ^ (i + 1)) ≤ (1 - (1 / 2 : ℝ) ^ j) := by
          have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show i + 1 ≤ j by omega)
          linarith
        have hfl : ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (i + 1))⌋₊ ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j)⌋₊ :=
          Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hK_ge1 hle)
        have : b ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (i + 1))⌋₊ := hi.2.trans (min_le_right _ _)
        omega
      · have hle : (1 - (1 / 2 : ℝ) ^ (j + 1)) ≤ (1 - (1 / 2 : ℝ) ^ i) := by
          have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show j + 1 ≤ i by omega)
          linarith
        have hfl : ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1))⌋₊ ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ i)⌋₊ :=
          Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hK_ge1 hle)
        have : b ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1))⌋₊ := hj.2.trans (min_le_right _ _)
        omega
    have hsub_sum : ∑ b ∈ R₃, (((Finset.Icc 1 K).filter (fun k =>
        b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
        ∑ j ∈ Finset.Ico J₀ J_max, ∑ b ∈ Sh j, (((Finset.Icc 1 K).filter (fun k =>
          b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) := by
      rw [← Finset.sum_biUnion hdisj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => Nat.cast_nonneg _
    have hper_j : ∀ j ∈ Finset.Ico J₀ J_max,
        ∑ b ∈ Sh j, (((Finset.Icc 1 K).filter (fun k =>
          b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
        (60 : ℝ) * (K : ℝ) * V_z * (3 / 5 : ℝ) ^ j +
          (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ)) := by
      intro j hj
      have hj_ico := Finset.mem_Ico.mp hj
      have hexp_j : Real.exp ((((j + 1 : ℕ) : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1))) ≤ (6 / 5 : ℝ) ^ (j + 2) := by
        have hle1 : (((j + 1 : ℕ) : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1)) ≤ ((j + 2 : ℕ) : ℝ) * (1 / 500 : ℝ) := by
          push_cast
          have hJ0_ge1 : (1 : ℝ) ≤ (J₀ : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) J₀]
          rw [show ((j : ℝ) + 2) * (1 / 500) = ((j : ℝ) + 1 + 1) / (500 * 1) by ring]
          exact div_le_div_of_nonneg_left (by linarith only [Nat.cast_nonneg (α := ℝ) j]) (by norm_num) (by linarith only [hJ0_ge1])
        calc Real.exp ((((j + 1 : ℕ) : ℝ) + 1) / (500 * ((J₀ : ℝ) + 1)))
            ≤ Real.exp (((j + 2 : ℕ) : ℝ) * (1 / 500 : ℝ)) := Real.exp_le_exp.mpr hle1
          _ = (Real.exp (1 / 500 : ℝ)) ^ (j + 2) := by rw [Real.exp_nat_mul]
          _ ≤ (6 / 5 : ℝ) ^ (j + 2) := pow_le_pow_left₀ (Real.exp_pos _).le hexp500 _
      have hb_term : ∀ b ∈ Sh j,
          (((Finset.Icc 1 K).filter (fun k =>
            b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ) ≤
          (204 / 100 : ℝ) * (K : ℝ) * (6 / 5 : ℝ) ^ (j + 2) * V_z * (1 / (b : ℝ)) +
            (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (1 / (b : ℝ)) := by
        intro b hb
        have hbf := Finset.mem_filter.mp hb
        have hbi := Finset.mem_Ioc.mp hbf.1
        have hb_lo : ⌊Real.sqrt (K : ℝ)⌋₊ < b := by
          have hhalf : (1 / 2 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ j := by
            have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show 1 ≤ j by omega)
            linarith
          have hfl : ⌊Real.sqrt (K : ℝ)⌋₊ ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ j)⌋₊ := by
            rw [Real.sqrt_eq_rpow]
            exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hK_ge1 hhalf)
          omega
        have hb_hi : b ≤ B_cut_exp := hbi.2.trans (min_le_left _ _)
        have hb_pow : (b : ℝ) ≤ (K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ (j + 1)) :=
          (Nat.cast_le.mpr (hbi.2.trans (min_le_right _ _))).trans (Nat.floor_le (by positivity))
        have hzbt := zb_sieve_term B' hB' hge2 K n M y J₀ a b (j + 1) A_n hn1 hAn hy hy16 hy_exp
          hcop_M hpi hK16 hL_ge' hf_good hbf.2 hb_lo hb_hi hb_pow (by omega)
        refine hzbt.trans ?_
        have h1 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp_j (show (0 : ℝ) ≤ (204 / 100 : ℝ) * ((K : ℝ) / (b : ℝ)) by positivity)) hVz_nn
        linarith [show (204 / 100 : ℝ) * ((K : ℝ) / (b : ℝ)) * (6 / 5 : ℝ) ^ (j + 2) * V_z =
          (204 / 100 : ℝ) * (K : ℝ) * (6 / 5 : ℝ) ^ (j + 2) * V_z * (1 / (b : ℝ)) by ring,
          show ((K : ℝ) / (b : ℝ)) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) =
          (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (1 / (b : ℝ)) by ring]
      calc ∑ b ∈ Sh j, (((Finset.Icc 1 K).filter (fun k =>
              b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ)
          ≤ (204 / 100 : ℝ) * (K : ℝ) * (6 / 5 : ℝ) ^ (j + 2) * V_z * (∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ)) +
              (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ)) := by
            have h1 := Finset.sum_le_sum hb_term
            rwa [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
        _ ≤ (204 / 100 : ℝ) * (K : ℝ) * (6 / 5 : ℝ) ^ (j + 2) * V_z * (18 * (1 / 2 : ℝ) ^ j) +
              (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left (hshell_bound j hj)
              (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK_pos.le) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 5) _)) hVz_nn)) le_rfl
        _ ≤ (60 : ℝ) * (K : ℝ) * V_z * (3 / 5 : ℝ) ^ j +
              (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ)) := by
            have hpow_eq : (6 / 5 : ℝ) ^ (j + 2) * (1 / 2 : ℝ) ^ j = (36 / 25 : ℝ) * (3 / 5 : ℝ) ^ j := by
              rw [pow_add, show (6 / 5 : ℝ) ^ j * (6 / 5 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j =
                (6 / 5 : ℝ) ^ 2 * ((6 / 5 : ℝ) * (1 / 2 : ℝ)) ^ j by rw [mul_pow]; ring]
              norm_num
            have hcoeff : (204 / 100 : ℝ) * 18 * (36 / 25 : ℝ) ≤ 60 := by norm_num
            have hnn : 0 ≤ (K : ℝ) * V_z * (3 / 5 : ℝ) ^ j :=
              mul_nonneg (mul_nonneg hK_pos.le hVz_nn) (by positivity)
            have heq_t : (204 / 100 : ℝ) * (K : ℝ) * (6 / 5 : ℝ) ^ (j + 2) * V_z * (18 * (1 / 2 : ℝ) ^ j) =
                ((204 / 100 : ℝ) * 18 * (36 / 25 : ℝ)) * ((K : ℝ) * V_z * (3 / 5 : ℝ) ^ j) := by
              rw [show (204 / 100 : ℝ) * (K : ℝ) * (6 / 5 : ℝ) ^ (j + 2) * V_z * (18 * (1 / 2 : ℝ) ^ j) =
                (204 / 100 : ℝ) * 18 * ((6 / 5 : ℝ) ^ (j + 2) * (1 / 2 : ℝ) ^ j) * ((K : ℝ) * V_z) by ring, hpow_eq]; ring
            nlinarith only [hcoeff, hnn, heq_t]
    have hSh_sub : (Finset.Ico J₀ J_max).biUnion Sh ⊆ (Finset.range (K + 1)).filter (· ∈ B') := by
      intro b hb
      obtain ⟨j, _, hbj⟩ := Finset.mem_biUnion.mp hb
      have hbf := Finset.mem_filter.mp hbj
      have hbi := Finset.mem_Ioc.mp hbf.1
      have hb_le_B : b ≤ B_cut_exp := hbi.2.trans (min_le_left _ _)
      have hbK : b ≤ K := by
        have h1 : (B_cut_exp : ℝ) ≤ (K : ℝ) :=
          (Nat.floor_le (by positivity)).trans (div_le_self hK_pos.le (Real.one_le_exp (Real.sqrt_nonneg _)))
        exact hb_le_B.trans (by exact_mod_cast h1)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbf.2⟩
    have hsum_inv_Sh : ∑ j ∈ Finset.Ico J₀ J_max, ∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ) ≤
        ∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ) := by
      rw [← Finset.sum_biUnion hdisj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hSh_sub fun _ _ _ => by positivity
    calc ∑ b ∈ R₃, (((Finset.Icc 1 K).filter (fun k =>
            b ∣ a + k * M ∧ ∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M)).card : ℝ)
        ≤ ∑ j ∈ Finset.Ico J₀ J_max, ((60 : ℝ) * (K : ℝ) * V_z * (3 / 5 : ℝ) ^ j +
            (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) * (∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ))) :=
          hsub_sum.trans (Finset.sum_le_sum hper_j)
      _ = (60 : ℝ) * (K : ℝ) * V_z * (∑ j ∈ Finset.Ico J₀ J_max, (3 / 5 : ℝ) ^ j) +
            (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
              (∑ j ∈ Finset.Ico J₀ J_max, ∑ b ∈ Sh j, (1 : ℝ) / (b : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (60 : ℝ) * (K : ℝ) * V_z * (∑ j ∈ Finset.Ico J₀ J_max, (3 / 5 : ℝ) ^ j) +
            (K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
              (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum_inv_Sh (div_nonneg hK_pos.le (Real.exp_pos _).le))
  -- Geometric series bound: ∑_{j ∈ Ico J₀ J_max} (3/5)^j ≤ (5/2) * (3/5)^J₀
  have hgeom : ∑ j ∈ Finset.Ico J₀ J_max, (3 / 5 : ℝ) ^ j ≤ (5 / 2 : ℝ) * (3 / 5 : ℝ) ^ J₀ := by
    by_cases hle : J₀ ≤ J_max
    · have h1 : (2 / 5 : ℝ) * ∑ j ∈ Finset.Ico J₀ J_max, (3 / 5 : ℝ) ^ j =
          (3 / 5 : ℝ) ^ J₀ - (3 / 5 : ℝ) ^ J_max := by
        have hstep : ∀ m : ℕ, (2 / 5 : ℝ) * ∑ j ∈ Finset.Ico J₀ (J₀ + m), (3 / 5 : ℝ) ^ j =
            (3 / 5 : ℝ) ^ J₀ - (3 / 5 : ℝ) ^ (J₀ + m) := by
          intro m; induction m with
          | zero => simp
          | succ m ih =>
            rw [show J₀ + (m + 1) = (J₀ + m) + 1 by omega, Finset.sum_Ico_succ_top (by omega),
              mul_add, ih, pow_succ]; ring
        have := hstep (J_max - J₀)
        rwa [Nat.add_sub_cancel' hle] at this
      have hnn : 0 ≤ (3 / 5 : ℝ) ^ J_max := by positivity
      linarith
    · have hemp : Finset.Ico J₀ J_max = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]; positivity
  have hmain : (A_n.card : ℝ) * ((60 : ℝ) * (K : ℝ) * V_z * (∑ j ∈ Finset.Ico J₀ J_max, (3 / 5 : ℝ) ^ j)) ≤
      (5 / 100 : ℝ) * (K : ℝ) * V_z := by
    have hinv_J0 : (3 / 5 : ℝ) ^ J₀ ≤ 1 / (3000 * (n : ℝ)) := by
      have hprod : (3 / 5 : ℝ) ^ J₀ * (5 / 3 : ℝ) ^ J₀ = 1 := by rw [← mul_pow]; norm_num
      rw [le_div_iff₀ (by positivity)]
      calc (3 / 5 : ℝ) ^ J₀ * (3000 * (n : ℝ))
          ≤ (3 / 5 : ℝ) ^ J₀ * (5 / 3 : ℝ) ^ J₀ := mul_le_mul_of_nonneg_left hJ₀_pow (by positivity)
        _ = 1 := hprod
    calc (A_n.card : ℝ) * ((60 : ℝ) * (K : ℝ) * V_z * (∑ j ∈ Finset.Ico J₀ J_max, (3 / 5 : ℝ) ^ j))
        ≤ (n : ℝ) * ((60 : ℝ) * (K : ℝ) * V_z * ((5 / 2 : ℝ) * (1 / (3000 * (n : ℝ))))) := by
          refine mul_le_mul hcard_An
            (mul_le_mul_of_nonneg_left (hgeom.trans (mul_le_mul_of_nonneg_left hinv_J0 (by norm_num))) (by positivity))
            (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)) hn_pos.le
      _ = (5 / 100 : ℝ) * (K : ℝ) * V_z := by field_simp; ring
  have herr : (A_n.card : ℝ) * ((K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
      (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ))) ≤ (1 / 100 : ℝ) * (K : ℝ) * V_z := by
    have hL_n : (1000 * (n : ℝ)) ^ 4 ≤ Real.log (K : ℝ) := by
      have h1 : 1000 * (n : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by
        have : (1 : ℝ) ≤ (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by nlinarith
        nlinarith
      exact (pow_le_pow_left₀ (by positivity) h1 4).trans hL_ge'
    have h1 := range23_err_le K n V_z (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ))
      hn1 hL_n hfK_le hVz_ge
    have h2 : (A_n.card : ℝ) * ((K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
        (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ))) ≤
        (n : ℝ) * (K : ℝ) * (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) /
          Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) := by
      rw [show (n : ℝ) * (K : ℝ) * (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) /
          Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) =
        (n : ℝ) * ((K : ℝ) / Real.exp ((3 / 4 : ℝ) * Real.sqrt (Real.log (K : ℝ))) *
          (∑ b ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ))) by ring]
      exact mul_le_mul_of_nonneg_right hcard_An (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity))
    exact h2.trans h1
  have hsum_all := Finset.sum_le_sum hsum_a
  rw [Finset.sum_const, nsmul_eq_mul, mul_add] at hsum_all
  exact (hstep1.trans hsum_all).trans (by linarith)

/-- Range 4: `b ∈ (⌊K / exp(√(log K))⌋₊, n + K * M]`, bounded by trivial union bound + Chebyshev. -/
private lemma range4_bound (B' : Set ℕ) (hB' : B'.Pairwise Nat.Coprime)
    (hge2 : ∀ b ∈ B', 2 ≤ b) (K n M y : ℕ) (A_n : Finset ℕ) (V_z : ℝ)
    (hn1 : 1 ≤ n) (hM1 : 1 ≤ M) (hAn : A_n ⊆ Finset.Icc 1 n)
    (hy16 : 16 ≤ y) (hcop_M : ∀ p ∈ B', y < p → Nat.Coprime p M)
    (hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ))
    (hK_ge : max n (y ^ 2) ≤ K)
    (hL_ge : (10000 * (n : ℝ) * (M : ℝ)) ^ 4 ≤ Real.log (K : ℝ))
    (hVz_ge : 1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤ V_z) :
    let B_cut_exp : ℕ := ⌊(K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ)))⌋₊
    let R₄ := (Finset.Ioc B_cut_exp (n + K * M)).filter (· ∈ B')
    (((Finset.Icc 1 K).filter (fun k =>
      ∃ a ∈ A_n, ∃ b ∈ R₄, b ∣ a + k * M)).card : ℝ) ≤
      (2 / 100 : ℝ) * (K : ℝ) * V_z := by
  intro B_cut_exp R₄
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hKn : n ≤ K := le_trans (le_max_left _ _) hK_ge
  have hKy2 : y ^ 2 ≤ K := le_trans (le_max_right _ _) hK_ge
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hL_pos : 0 < Real.log (K : ℝ) := lt_of_lt_of_le (by positivity) hL_ge
  have hL4_ge : 10000 * (n : ℝ) * (M : ℝ) ≤ (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := by
    have h1 := Real.rpow_le_rpow (by positivity) hL_ge (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one] at h1
  have hsqrtL_eq : ((Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (Real.log (K : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le, Real.sqrt_eq_rpow]; norm_num
  have hsqrtL_ge100 : (10000 : ℝ) ≤ Real.sqrt (Real.log (K : ℝ)) := by
    have h1 : (10000 : ℝ) ≤ (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := by
      have := one_le_mul_of_one_le_of_one_le hnR hMR; nlinarith
    rw [← hsqrtL_eq]; nlinarith
  let B_cut_sqrt : ℕ := ⌊(K : ℝ) / Real.sqrt (Real.log (K : ℝ))⌋₊
  have hcut_le : B_cut_exp ≤ B_cut_sqrt := by
    refine Nat.floor_mono (div_le_div_of_nonneg_left hK_pos.le (Real.sqrt_pos.mpr hL_pos) ?_)
    linarith [Real.add_one_le_exp (Real.sqrt (Real.log (K : ℝ)))]
  have hBcut_ge_y : y ≤ B_cut_exp := by
    have h1 : Real.exp (Real.sqrt (Real.log (K : ℝ))) ≤ Real.sqrt (K : ℝ) := by
      conv_rhs => rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hK_pos]
      refine Real.exp_le_exp.mpr ?_
      have := Real.mul_self_sqrt hL_pos.le
      nlinarith
    have h2 : Real.sqrt (K : ℝ) ≤ (K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ))) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      calc Real.sqrt (K : ℝ) * Real.exp (Real.sqrt (Real.log (K : ℝ)))
          ≤ Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
        _ = (K : ℝ) := Real.mul_self_sqrt hK_pos.le
    have hy_le_sqrt : (y : ℝ) ≤ Real.sqrt (K : ℝ) := by
      rw [Real.le_sqrt (Nat.cast_nonneg y) hK_pos.le]; exact_mod_cast hKy2
    exact Nat.le_floor (hy_le_sqrt.trans h2)
  have hBcut_sqrt_le : B_cut_sqrt ≤ n + K * M := by
    have h1 : (B_cut_sqrt : ℝ) ≤ (K : ℝ) :=
      (Nat.floor_le (by positivity)).trans (div_le_self hK_pos.le (by linarith))
    have h2 : B_cut_sqrt ≤ K := by exact_mod_cast h1
    have h3 : K ≤ K * M := Nat.le_mul_of_pos_right K hM1
    omega
  let R₄a := (Finset.Ioc B_cut_exp B_cut_sqrt).filter (· ∈ B')
  let R₄b := (Finset.Ioc B_cut_sqrt (n + K * M)).filter (· ∈ B')
  have hR4_split : R₄ = R₄a ∪ R₄b := by
    ext b; simp only [R₄, R₄a, R₄b, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hb⟩
      by_cases hle : b ≤ B_cut_sqrt
      · exact Or.inl ⟨⟨h1, hle⟩, hb⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hb⟩
    · rintro (⟨⟨h1, h2⟩, hb⟩ | ⟨⟨h1, h2⟩, hb⟩)
      · exact ⟨⟨h1, by omega⟩, hb⟩
      · exact ⟨⟨by omega, h2⟩, hb⟩
  -- Union bound over a ∈ A_n and b ∈ R₄a, R₄b
  have hunion : (((Finset.Icc 1 K).filter (fun k => ∃ a ∈ A_n, ∃ b ∈ R₄, b ∣ a + k * M)).card : ℝ) ≤
      (∑ a ∈ A_n, ∑ b ∈ R₄a, (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ)) +
      (∑ a ∈ A_n, ∑ b ∈ R₄b, (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ)) := by
    have hsub : (Finset.Icc 1 K).filter (fun k => ∃ a ∈ A_n, ∃ b ∈ R₄, b ∣ a + k * M) ⊆
        (A_n.biUnion (fun a => R₄a.biUnion (fun b => (Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)))) ∪
        (A_n.biUnion (fun a => R₄b.biUnion (fun b => (Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)))) := by
      intro k hk
      have hkf := Finset.mem_filter.mp hk
      obtain ⟨a, ha, b, hb, hdvd⟩ := hkf.2
      rw [hR4_split] at hb
      rcases Finset.mem_union.mp hb with hba | hbb
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨a, ha,
          Finset.mem_biUnion.mpr ⟨b, hba, Finset.mem_filter.mpr ⟨hkf.1, hdvd⟩⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha,
          Finset.mem_biUnion.mpr ⟨b, hbb, Finset.mem_filter.mpr ⟨hkf.1, hdvd⟩⟩⟩)
    have hcard : ((Finset.Icc 1 K).filter (fun k => ∃ a ∈ A_n, ∃ b ∈ R₄, b ∣ a + k * M)).card ≤
        (∑ a ∈ A_n, ∑ b ∈ R₄a, ((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card) +
        (∑ a ∈ A_n, ∑ b ∈ R₄b, ((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card) := by
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ _ := Nat.add_le_add
            (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))
            (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))
    exact_mod_cast hcard
  have hcard_An : (A_n.card : ℝ) ≤ (n : ℝ) := by
    have := Finset.card_le_card hAn; rw [Nat.card_Icc] at this; exact_mod_cast (by omega : A_n.card ≤ n)
  -- Bound R₄a
  have hR4a : ∑ a ∈ A_n, ∑ b ∈ R₄a, (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ) ≤
      (1 / 100 : ℝ) * (K : ℝ) * V_z := by
    have hterm : ∀ a ∈ A_n, ∀ b ∈ R₄a,
        (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ) ≤ 2 * (K : ℝ) / (b : ℝ) := by
      intro a _ b hb
      have hbf := Finset.mem_filter.mp hb
      have hbi := Finset.mem_Ioc.mp hbf.1
      have hbK : b ≤ K := by
        have h1 : (B_cut_sqrt : ℝ) ≤ (K : ℝ) :=
          (Nat.floor_le (by positivity)).trans (div_le_self hK_pos.le (by linarith))
        exact hbi.2.trans (by exact_mod_cast h1)
      have htriv := card_ap_hit_trivial_upper K a b M (by omega) (hcop_M b hbf.2 (by omega))
      have h1_le : (1 : ℝ) ≤ (K : ℝ) / (b : ℝ) :=
        (one_le_div (by exact_mod_cast (by omega : 0 < b))).mpr (by exact_mod_cast hbK)
      linarith [show 2 * (K : ℝ) / (b : ℝ) = (K : ℝ) / (b : ℝ) + (K : ℝ) / (b : ℝ) by ring]
    have hinv_4a : ∑ b ∈ R₄a, (1 : ℝ) / (b : ℝ) ≤ 25 / Real.sqrt (Real.log (K : ℝ)) := by
      have hsum_inv := sum_inv_coprime_Ioc_le B' hB' hge2 B_cut_exp B_cut_sqrt (by omega) hcut_le
        (fun k hk => hpi k (hBcut_ge_y.trans hk))
      have hlog_exp_ge : Real.log (K : ℝ) - Real.sqrt (Real.log (K : ℝ)) - 1 ≤ Real.log (B_cut_exp : ℝ) := by
        have hfl : (K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ))) - 1 < (B_cut_exp : ℝ) := Nat.sub_one_lt_floor _
        have hge4 : (4 : ℝ) ≤ (K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ))) := by
          have : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 4 ≤ y)
          have h2 : (B_cut_exp : ℝ) ≤ (K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ))) := Nat.floor_le (by positivity)
          have h3 : (y : ℝ) ≤ (B_cut_exp : ℝ) := by exact_mod_cast hBcut_ge_y
          linarith
        have hhalf : (K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ))) / 2 ≤ (B_cut_exp : ℝ) := by linarith
        have h1 := Real.log_le_log (by positivity) hhalf
        rw [Real.log_div (by positivity) (by norm_num), Real.log_div hK_pos.ne' (Real.exp_pos _).ne',
          Real.log_exp] at h1
        linarith [Real.log_two_lt_d9]
      have hlog_exp_half : Real.log (K : ℝ) / 2 ≤ Real.log (B_cut_exp : ℝ) := by
        have hsq := Real.mul_self_sqrt hL_pos.le; nlinarith only [hlog_exp_ge, hsq, hsqrtL_ge100]
      have hlog_sqrt_le : Real.log (B_cut_sqrt : ℝ) ≤ Real.log (K : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < B_cut_sqrt))
          ((Nat.floor_le (by positivity)).trans (div_le_self hK_pos.le (by linarith only [hsqrtL_ge100])))
      have hlog_sqrt_half : Real.log (K : ℝ) / 2 ≤ Real.log (B_cut_sqrt : ℝ) :=
        hlog_exp_half.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < B_cut_exp)) (by exact_mod_cast hcut_le))
      have hlog_rat : Real.log (Real.log (B_cut_sqrt : ℝ) / Real.log (B_cut_exp : ℝ)) ≤
          4 / Real.sqrt (Real.log (K : ℝ)) := by
        have hpos_e : 0 < Real.log (B_cut_exp : ℝ) := lt_of_lt_of_le (by positivity) hlog_exp_half
        have h1 := Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le (by positivity) hlog_sqrt_half) hpos_e)
        have h2 : Real.log (B_cut_sqrt : ℝ) / Real.log (B_cut_exp : ℝ) - 1 =
            (Real.log (B_cut_sqrt : ℝ) - Real.log (B_cut_exp : ℝ)) / Real.log (B_cut_exp : ℝ) := by field_simp
        have h3 : (Real.log (B_cut_sqrt : ℝ) - Real.log (B_cut_exp : ℝ)) / Real.log (B_cut_exp : ℝ) ≤
            4 / Real.sqrt (Real.log (K : ℝ)) := by
          rw [div_le_div_iff₀ hpos_e (Real.sqrt_pos.mpr hL_pos)]
          have hsq := Real.mul_self_sqrt hL_pos.le
          nlinarith only [hlog_sqrt_le, hlog_exp_ge, hlog_exp_half, hsq, hsqrtL_ge100]
        linarith only [h1, h2, h3]
      have ht1 : 2 / Real.log (B_cut_sqrt : ℝ) ≤ 4 / Real.sqrt (Real.log (K : ℝ)) := by
        rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hlog_sqrt_half) (Real.sqrt_pos.mpr hL_pos)]
        have hsq := Real.mul_self_sqrt hL_pos.le; nlinarith only [hlog_sqrt_half, hsq, hsqrtL_ge100]
      have ht2 : 8 / ((B_cut_exp : ℝ) * Real.log (B_cut_exp : ℝ)) ≤ 4 / Real.sqrt (Real.log (K : ℝ)) := by
        have hge4 : (4 : ℝ) ≤ (B_cut_exp : ℝ) := by exact_mod_cast (by omega : 4 ≤ B_cut_exp)
        rw [div_le_div_iff₀ (mul_pos (by linarith only [hge4]) (lt_of_lt_of_le (by positivity) hlog_exp_half)) (Real.sqrt_pos.mpr hL_pos)]
        have hsq := Real.mul_self_sqrt hL_pos.le; nlinarith only [hge4, hlog_exp_half, hsq, hsqrtL_ge100]
      have h24_le : (24 : ℝ) / Real.sqrt (Real.log (K : ℝ)) ≤ 25 / Real.sqrt (Real.log (K : ℝ)) :=
        div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
      linarith only [hsum_inv, hlog_rat, ht1, ht2, h24_le, show 4 / Real.sqrt (Real.log (K : ℝ)) + 4 * (4 / Real.sqrt (Real.log (K : ℝ))) +
        4 / Real.sqrt (Real.log (K : ℝ)) = 24 / Real.sqrt (Real.log (K : ℝ)) by ring]
    have h4a_sum : ∑ a ∈ A_n, ∑ b ∈ R₄a, (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ) ≤
        (n : ℝ) * (2 * (K : ℝ) * (25 / Real.sqrt (Real.log (K : ℝ)))) := by
      have h1 := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
      have h2 : ∑ a ∈ A_n, ∑ b ∈ R₄a, 2 * (K : ℝ) / (b : ℝ) =
          (A_n.card : ℝ) * (2 * (K : ℝ) * ∑ b ∈ R₄a, (1 : ℝ) / (b : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]; congr 1
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
      rw [h2] at h1
      exact h1.trans (mul_le_mul hcard_An (mul_le_mul_of_nonneg_left hinv_4a (by positivity))
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)) hn_pos.le)
    have hratio : 50 * (n : ℝ) / Real.sqrt (Real.log (K : ℝ)) ≤ (1 / 100 : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) := by
      have hL4_pos : 0 < (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL_pos _
      rw [mul_one_div, div_le_div_iff₀ (Real.sqrt_pos.mpr hL_pos) (by positivity), ← hsqrtL_eq]
      nlinarith only [hL4_ge, hL4_pos, hMR, hnR]
    calc _ ≤ (K : ℝ) * (50 * (n : ℝ) / Real.sqrt (Real.log (K : ℝ))) := by
          linarith [h4a_sum, show (n : ℝ) * (2 * (K : ℝ) * (25 / Real.sqrt (Real.log (K : ℝ)))) =
            (K : ℝ) * (50 * (n : ℝ) / Real.sqrt (Real.log (K : ℝ))) by ring]
      _ ≤ (K : ℝ) * ((1 / 100 : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hratio hK_pos.le
      _ ≤ (K : ℝ) * ((1 / 100 : ℝ) * V_z) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVz_ge (by norm_num)) hK_pos.le
      _ = (1 / 100 : ℝ) * (K : ℝ) * V_z := by ring
  -- Bound R₄b
  have hR4b : ∑ a ∈ A_n, ∑ b ∈ R₄b, (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ) ≤
      (1 / 100 : ℝ) * (K : ℝ) * V_z := by
    have hterm : ∀ a ∈ A_n, ∀ b ∈ R₄b,
        (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ) ≤ 2 * Real.sqrt (Real.log (K : ℝ)) := by
      intro a _ b hb
      have hbf := Finset.mem_filter.mp hb
      have hbi := Finset.mem_Ioc.mp hbf.1
      have htriv := card_ap_hit_trivial_upper K a b M (by omega) (hcop_M b hbf.2 (by omega))
      have hb_gt : (K : ℝ) / Real.sqrt (Real.log (K : ℝ)) < (b : ℝ) :=
        (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hbi.1)
      have hKb_le : (K : ℝ) / (b : ℝ) ≤ Real.sqrt (Real.log (K : ℝ)) := by
        rw [div_le_iff₀ (by exact_mod_cast (by omega : 0 < b))]
        have := (div_lt_iff₀ (Real.sqrt_pos.mpr hL_pos)).mp hb_gt
        linarith
      linarith
    have hcard_4b : (R₄b.card : ℝ) ≤ 4 * (K : ℝ) * (M : ℝ) / Real.log (K : ℝ) := by
      have hsub : R₄b ⊆ (Finset.Icc 2 (n + K * M)).filter (· ∈ B') := by
        intro b hb
        have hbf := Finset.mem_filter.mp hb
        have hbi := Finset.mem_Ioc.mp hbf.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hge2 b hbf.2, hbi.2⟩, hbf.2⟩
      have h1 : (R₄b.card : ℝ) ≤ (Nat.primeCounting (n + K * M) : ℝ) :=
        Nat.cast_le.mpr ((Finset.card_le_card hsub).trans (card_coprime_le_primeCounting B' hB' hge2 (n + K * M)))
      have h2 : (Nat.primeCounting (n + K * M) : ℝ) ≤ 2 * ((n + K * M : ℕ) : ℝ) / Real.log ((n + K * M : ℕ) : ℝ) :=
        hpi (n + K * M) (by omega)
      have hlog_ge : Real.log (K : ℝ) ≤ Real.log ((n + K * M : ℕ) : ℝ) :=
        Real.log_le_log hK_pos (by exact_mod_cast (show K ≤ n + K * M by have := Nat.le_mul_of_pos_right K hM1; omega))
      have hnum_le : ((n + K * M : ℕ) : ℝ) ≤ 2 * (K : ℝ) * (M : ℝ) := by
        push_cast
        have hKM : (K : ℝ) ≤ (K : ℝ) * (M : ℝ) := le_mul_of_one_le_right hK_pos.le hMR
        have hnK : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKn
        linarith only [hKM, hnK]
      calc (R₄b.card : ℝ) ≤ 2 * ((n + K * M : ℕ) : ℝ) / Real.log ((n + K * M : ℕ) : ℝ) := h1.trans h2
        _ ≤ 2 * (2 * (K : ℝ) * (M : ℝ)) / Real.log (K : ℝ) :=
            div_le_div₀ (by positivity) (by linarith only [hnum_le]) hL_pos hlog_ge
        _ = 4 * (K : ℝ) * (M : ℝ) / Real.log (K : ℝ) := by ring
    have h4b_sum : ∑ a ∈ A_n, ∑ b ∈ R₄b, (((Finset.Icc 1 K).filter (fun k => b ∣ a + k * M)).card : ℝ) ≤
        8 * (n : ℝ) * (M : ℝ) * (K : ℝ) / Real.sqrt (Real.log (K : ℝ)) := by
      have h1 := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
      simp only [Finset.sum_const, nsmul_eq_mul] at h1
      calc _ ≤ (n : ℝ) * ((4 * (K : ℝ) * (M : ℝ) / Real.log (K : ℝ)) * (2 * Real.sqrt (Real.log (K : ℝ)))) :=
            h1.trans (mul_le_mul hcard_An (mul_le_mul_of_nonneg_right hcard_4b (by positivity)) (by positivity) hn_pos.le)
        _ = 8 * (n : ℝ) * (M : ℝ) * (K : ℝ) / Real.sqrt (Real.log (K : ℝ)) := by
            have hsq := Real.mul_self_sqrt hL_pos.le
            have hsp : Real.sqrt (Real.log (K : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hL_pos).ne'
            field_simp [hL_pos.ne', hsp]
            nlinarith only [hsq]
    have hratio : 8 * (n : ℝ) * (M : ℝ) / Real.sqrt (Real.log (K : ℝ)) ≤
        (1 / 100 : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) := by
      have hL4_pos : 0 < (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL_pos _
      rw [mul_one_div, div_le_div_iff₀ (Real.sqrt_pos.mpr hL_pos) (by positivity), ← hsqrtL_eq]
      nlinarith only [hL4_ge, hL4_pos, hMR, hnR]
    calc _ ≤ (K : ℝ) * (8 * (n : ℝ) * (M : ℝ) / Real.sqrt (Real.log (K : ℝ))) := by
          linarith [h4b_sum, show 8 * (n : ℝ) * (M : ℝ) * (K : ℝ) / Real.sqrt (Real.log (K : ℝ)) =
            (K : ℝ) * (8 * (n : ℝ) * (M : ℝ) / Real.sqrt (Real.log (K : ℝ))) by ring]
      _ ≤ (K : ℝ) * ((1 / 100 : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hratio hK_pos.le
      _ ≤ (K : ℝ) * ((1 / 100 : ℝ) * V_z) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVz_ge (by norm_num)) hK_pos.le
      _ = (1 / 100 : ℝ) * (K : ℝ) * V_z := by ring
  linarith

set_option maxHeartbeats 400000 in
/-- Main theorem proving `Erdos675.erdos_675.variants.brun`. -/
private lemma main_theorem (B : Set ℕ) (hB : B.Pairwise Nat.Coprime)
    (hsum : (fun x : ℕ => ∑ b ∈ Finset.range x with b ∈ B, (1 : ℝ) / (b : ℝ)) =o[atTop]
      fun x : ℕ => Real.log (Real.log (x : ℝ))) :
    Erdos675.HasTranslationProperty {n : ℕ | ∀ b ∈ B, ¬ b ∣ n} := by
  intro n
  -- Edge case 1: n = 0
  by_cases hn0 : n = 0
  · refine ⟨1, le_rfl, fun a ha1 han => by omega⟩
  have hn1 : 1 ≤ n := by omega
  -- Edge case 2: 1 ∈ B (then A = ∅, t = 1 works)
  by_cases h1B : 1 ∈ B
  · refine ⟨1, le_rfl, fun a _ _ => ?_⟩
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => (h 1 h1B (one_dvd a)).elim, fun h => (h 1 h1B (one_dvd (a + 1))).elim⟩
  -- Define B' = B \ {0} so ∀ b ∈ B', 2 ≤ b
  let B' : Set ℕ := B \ {0}
  have hB' : B'.Pairwise Nat.Coprime := hB.mono Set.diff_subset
  have hge2 : ∀ b ∈ B', 2 ≤ b := by
    intro b hb
    have h0 : b ≠ 0 := fun h => hb.2 (Set.mem_singleton_iff.mpr h)
    have h1 : b ≠ 1 := fun h => h1B (h ▸ hb.1)
    omega
  have hsum' : (fun x : ℕ => ∑ b ∈ (Finset.range x).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) =o[atTop]
      fun x : ℕ => Real.log (Real.log (x : ℝ)) := by
    have heq : (fun x : ℕ => ∑ b ∈ (Finset.range x).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)) =
        (fun x : ℕ => ∑ b ∈ Finset.range x with b ∈ B, (1 : ℝ) / (b : ℝ)) := by
      ext x
      have hsub : (Finset.range x).filter (· ∈ B') ⊆ (Finset.range x).filter (· ∈ B) := by
        intro b hb
        have h := Finset.mem_filter.mp hb
        exact Finset.mem_filter.mpr ⟨h.1, h.2.1⟩
      rw [← Finset.sum_subset hsub]
      · intro b hb hnot
        have hbf := Finset.mem_filter.mp hb
        have hb0 : b = 0 := by
          by_contra hne
          exact hnot (Finset.mem_filter.mpr ⟨hbf.1, hbf.2, fun h => hne (Set.mem_singleton_iff.mp h)⟩)
        subst hb0; simp
    rw [heq]; exact hsum
  -- Define A_n = {a ∈ [1, n] : a ∈ A}
  let A_n : Finset ℕ := (Finset.Icc 1 n).filter (fun a => ∀ b ∈ B, ¬ b ∣ a)
  have hAn : A_n ⊆ Finset.Icc 1 n := Finset.filter_subset _ _
  -- Obtain Chebyshev threshold X_cheb
  obtain ⟨X_cheb, hX_cheb⟩ := eventually_primeCounting_le_two.exists_forall_of_atTop
  let y : ℕ := max (2 * n + 2) (max 16 (max X_cheb (⌈Real.exp (2000 * (n : ℝ))⌉₊ + 1)))
  have hy : 2 * n + 2 ≤ y := le_max_left _ _
  have hy16 : 16 ≤ y := le_trans (le_max_left _ _) (le_max_right _ _)
  have hy_cheb : X_cheb ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hy_exp : Real.exp (2000 * (n : ℝ)) ≤ (y : ℝ) := by
    have h1 : ⌈Real.exp (2000 * (n : ℝ))⌉₊ ≤ y :=
      le_trans (Nat.le_succ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hpi : ∀ k : ℕ, y ≤ k → (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log (k : ℝ) :=
    fun k hk => hX_cheb k (hy_cheb.trans hk)
  let M : ℕ := ∏ b ∈ (Finset.Icc 2 y).filter (· ∈ B'), b
  have hM1 : 1 ≤ M := Finset.one_le_prod' fun b hb => by have := hge2 b (Finset.mem_filter.mp hb).2; omega
  have hcop_M : ∀ p ∈ B', y < p → Nat.Coprime p M := by
    intro p hp hpy
    refine Nat.Coprime.prod_right fun q hq => ?_
    have hqf := Finset.mem_filter.mp hq
    have hqi := Finset.mem_Icc.mp hqf.1
    exact hB' hp hqf.2 (by omega)
  -- Edge case 3: A_n = ∅ (then t = M works!)
  by_cases hAn_empty : A_n = ∅
  · refine ⟨M, hM1, fun a ha1 han => ?_⟩
    have ha_not : ¬ (∀ b ∈ B, ¬ b ∣ a) := by
      intro haA
      have hmem : a ∈ A_n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, han⟩, haA⟩
      rw [hAn_empty] at hmem; exact Finset.notMem_empty a hmem
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h; exact (ha_not h).elim
    · intro h
      push Not at ha_not
      obtain ⟨b, hbB, hba⟩ := ha_not
      have hb0 : b ≠ 0 := by intro h0; subst h0; rw [zero_dvd_iff] at hba; omega
      have hb_le : b ≤ y := (Nat.le_of_dvd (by omega) hba).trans (by omega)
      have hbB' : b ∈ B' := ⟨hbB, fun h0 => hb0 (Set.mem_singleton_iff.mp h0)⟩
      have hb_mem : b ∈ (Finset.Icc 2 y).filter (· ∈ B') :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hge2 b hbB', hb_le⟩, hbB'⟩
      have hbM : b ∣ M := Finset.dvd_prod_of_mem _ hb_mem
      exact (h b hbB (dvd_add hba hbM)).elim
  -- Main case: A_n is nonempty
  let s₀ : ℕ := 800 * n + 80000 * n ^ 2 + 1
  let J₀ : ℕ := 2 * (Nat.log 2 (3000 * n) + 2) + 6
  have hJ₀_ge6 : 6 ≤ J₀ := by omega
  have hJ₀_pow : 3000 * (n : ℝ) ≤ (5 / 3 : ℝ) ^ J₀ := by
    have h1 : 3000 * n < 2 ^ (Nat.log 2 (3000 * n) + 2) := by
      have := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (3000 * n)
      have h2 : 2 ^ (Nat.log 2 (3000 * n) + 1) ≤ 2 ^ (Nat.log 2 (3000 * n) + 2) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h2 : (2 : ℝ) ^ (Nat.log 2 (3000 * n) + 2) ≤ (5 / 3 : ℝ) ^ (2 * (Nat.log 2 (3000 * n) + 2)) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ (5 / 3 : ℝ) ^ 2) _
    have h3 : (5 / 3 : ℝ) ^ (2 * (Nat.log 2 (3000 * n) + 2)) ≤ (5 / 3 : ℝ) ^ J₀ :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (by exact_mod_cast h1.le : 3000 * (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (3000 * n) + 2)).trans (h2.trans h3)
  let ε : ℝ := 1 / (1000 * (n : ℝ) * ((J₀ : ℝ) + 1) * (Real.log (8 * (s₀ : ℝ)) + 10))
  have hε_pos : 0 < ε := by
    have : 0 < Real.log (8 * (s₀ : ℝ)) + 10 := by
      have hs1 : (1 : ℝ) ≤ 8 * (s₀ : ℝ) := by dsimp only [s₀]; exact_mod_cast (by omega : 1 ≤ 8 * s₀)
      linarith [Real.log_nonneg hs1]
    dsimp only [ε]; positivity
  -- Threshold U₀ so K = ⌊exp(exp u)⌋₊ - 1 satisfies all size bounds and f(K+1) ≤ (1/(8n)) * log log K
  have hsmall : ∀ᶠ x : ℕ in atTop,
      ∑ b ∈ (Finset.range (x + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ) ≤
        (1 / (8 * (n : ℝ))) * Real.log (Real.log (x : ℝ)) := by
    have hbnd := hsum'.bound (show (0 : ℝ) < 1 / (16 * (n : ℝ)) by positivity)
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hbnd, eventually_ge_atTop 16] with x hx hx16
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
    have hlogx_gt1 : (1 : ℝ) < Real.log (x : ℝ) := by
      have h1 := Real.log_le_log (by norm_num) (show (16 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx16)
      have h16 : Real.log 16 = 4 * Real.log 2 := by rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; ring
      linarith [Real.log_two_gt_d9]
    have hlogx1 : Real.log (Real.log ((x + 1 : ℕ) : ℝ)) ≤ 2 * Real.log (Real.log (x : ℝ)) := by
      have hx1_le : ((x + 1 : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 := by
        push_cast
        have hxR : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx16
        nlinarith
      have hlog1 : Real.log ((x + 1 : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
        have := Real.log_le_log (by positivity) hx1_le; rwa [Real.log_pow] at this
      have hlog2 := Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1 < x + 1))) hlog1
      rw [Real.log_mul (by norm_num) (by linarith)] at hlog2
      have hloglog_ge : Real.log 2 ≤ Real.log (Real.log (x : ℝ)) := by
        have h2 : (2 : ℝ) ≤ Real.log (x : ℝ) := by
          have h1 := Real.log_le_log (by norm_num) (show (16 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx16)
          have h16 : Real.log 16 = 4 * Real.log 2 := by rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; ring
          linarith [Real.log_two_gt_d9]
        exact Real.log_le_log (by norm_num) h2
      linarith
    have hnn_lhs : 0 ≤ ∑ b ∈ (Finset.range (x + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hnn_rhs : 0 ≤ Real.log (Real.log ((x + 1 : ℕ) : ℝ)) :=
      Real.log_nonneg (hlogx_gt1.le.trans (Real.log_le_log hx_pos (by exact_mod_cast (by omega : x ≤ x + 1))))
    rw [Real.norm_of_nonneg hnn_lhs, Real.norm_of_nonneg hnn_rhs] at hx
    calc ∑ b ∈ (Finset.range (x + 1)).filter (· ∈ B'), (1 : ℝ) / (b : ℝ)
        ≤ (1 / (16 * (n : ℝ))) * Real.log (Real.log ((x + 1 : ℕ) : ℝ)) := hx
      _ ≤ (1 / (16 * (n : ℝ))) * (2 * Real.log (Real.log (x : ℝ))) :=
          mul_le_mul_of_nonneg_left hlogx1 (by positivity)
      _ = (1 / (8 * (n : ℝ))) * Real.log (Real.log (x : ℝ)) := by ring
  obtain ⟨X_sm, hX_sm⟩ := hsmall.exists_forall_of_atTop
  let C_big : ℝ := (10000 * (n : ℝ) * (M : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀) ^ 4
  let U₀ : ℕ := max 4 (max (⌈Real.log (C_big + 10)⌉₊ + 2) (⌈Real.log (Real.log ((max X_sm (max 16 (max n (y ^ 2))) + 4 : ℕ) : ℝ) + 2)⌉₊ + 2))
  obtain ⟨u, hu_ge, hf_good⟩ := exists_good_K B' (by convert hsum') ε hε_pos U₀
  let K : ℕ := ⌊Real.exp (Real.exp (u : ℝ))⌋₊ - 1
  -- Establish K size bounds from u ≥ U₀
  have hu4 : 4 ≤ u := le_trans (le_max_left _ _) hu_ge
  have hexp_u_ge : C_big + 10 ≤ Real.exp (u : ℝ) := by
    have h1 : ⌈Real.log (C_big + 10)⌉₊ + 2 ≤ u :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hu_ge)
    have h2 : Real.log (C_big + 10) ≤ (u : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.log (C_big + 10)⌉₊ ≤ u))
    have h3 := Real.exp_le_exp.mpr h2
    rwa [Real.exp_log (by dsimp only [C_big]; positivity)] at h3
  have hK_ge_half : Real.exp (Real.exp (u : ℝ)) / 2 ≤ (K : ℝ) := by
    have heu : (5 : ℝ) ≤ Real.exp (u : ℝ) := by
      have : (4 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu4
      linarith [Real.add_one_le_exp (u : ℝ)]
    have heeu : (6 : ℝ) ≤ Real.exp (Real.exp (u : ℝ)) := by linarith [Real.add_one_le_exp (Real.exp (u : ℝ))]
    have hfl : Real.exp (Real.exp (u : ℝ)) - 1 < (⌊Real.exp (Real.exp (u : ℝ))⌋₊ : ℝ) := Nat.sub_one_lt_floor _
    have hfl_ge1 : 1 ≤ ⌊Real.exp (Real.exp (u : ℝ))⌋₊ := Nat.le_floor (by norm_num; linarith)
    dsimp only [K]; rw [Nat.cast_sub hfl_ge1, Nat.cast_one]; linarith
  have hL_ge_C : C_big ≤ Real.log (K : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hK_ge_half
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
    linarith [Real.log_two_lt_d9]
  have hK_ge_target : max X_sm (max 16 (max n (y ^ 2))) ≤ K := by
    let T := max X_sm (max 16 (max n (y ^ 2)))
    have h1 : ⌈Real.log (Real.log ((T + 4 : ℕ) : ℝ) + 2)⌉₊ + 2 ≤ u :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hu_ge)
    have h2 : Real.log (Real.log ((T + 4 : ℕ) : ℝ) + 2) ≤ (u : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.log (Real.log ((T + 4 : ℕ) : ℝ) + 2)⌉₊ ≤ u))
    have h3 : Real.log ((T + 4 : ℕ) : ℝ) + 2 ≤ Real.exp (u : ℝ) := by
      have := Real.exp_le_exp.mpr h2
      have hpos : 0 < Real.log ((T + 4 : ℕ) : ℝ) + 2 := by
        have : (1 : ℝ) ≤ ((T + 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ T + 4)
        linarith [Real.log_nonneg this]
      rwa [Real.exp_log hpos] at this
    have h4 : ((T + 4 : ℕ) : ℝ) * 2 ≤ Real.exp (Real.exp (u : ℝ)) := by
      have h_e := Real.exp_le_exp.mpr h3
      rw [Real.exp_add, Real.exp_log (by exact_mod_cast (by omega : 0 < T + 4))] at h_e
      have he2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
      nlinarith [show (0 : ℝ) ≤ ((T + 4 : ℕ) : ℝ) by positivity]
    have hTK : (T : ℝ) ≤ (K : ℝ) := by push_cast at h4; linarith
    exact_mod_cast hTK
  have hK_Xsm : X_sm ≤ K := le_trans (le_max_left _ _) hK_ge_target
  have hK16 : 16 ≤ K := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hK_ge_target)
  have hKn : n ≤ K := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hK_ge_target))
  have hKy2 : y ^ 2 ≤ K := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hK_ge_target))
  -- Establish V_z ≥ 1 / (log K) ^ (1 / 4)
  let z : ℕ := ⌊(K : ℝ) ^ (1 / (8 * (s₀ : ℝ)))⌋₊
  let B_med := (Finset.Ioc y z).filter (· ∈ B')
  let V_z := ∏ p ∈ B_med, (1 - (A_n.card : ℝ) / (p : ℝ))
  have hs₀_ge1 : (1 : ℝ) ≤ (s₀ : ℝ) := by dsimp only [s₀]; exact_mod_cast (by omega : 1 ≤ s₀)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have h2J_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ J₀ := one_le_pow₀ (by norm_num)
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hL_pos : 0 < Real.log (K : ℝ) := lt_of_lt_of_le (by dsimp only [C_big]; positivity) hL_ge_C
  have hL_ge_r1 : (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10)) ^ 4 ≤ Real.log (K : ℝ) := by
    have h1 : 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) ≤
        10000 * (n : ℝ) * (M : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ := by
      have : (1 : ℝ) ≤ 10 * (M : ℝ) * (2 : ℝ) ^ J₀ := by nlinarith
      nlinarith [show (0 : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) by positivity]
    exact (pow_le_pow_left₀ (by positivity) h1 4).trans hL_ge_C
  have hL_ge_r23 : (1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀) ^ 4 ≤ Real.log (K : ℝ) := by
    have h1 : 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ ≤
        10000 * (n : ℝ) * (M : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ := by
      nlinarith [show (0 : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ by positivity]
    exact (pow_le_pow_left₀ (by positivity) h1 4).trans hL_ge_C
  have hL_ge_r4 : (10000 * (n : ℝ) * (M : ℝ)) ^ 4 ≤ Real.log (K : ℝ) := by
    have h1 : 10000 * (n : ℝ) * (M : ℝ) ≤
        10000 * (n : ℝ) * (M : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ := by
      have hge : (1 : ℝ) ≤ (s₀ : ℝ) * (Real.log (y : ℝ) + 10) * (2 : ℝ) ^ J₀ :=
        mul_three_ge_one hs₀_ge1 (by linarith) h2J_ge1
      have := le_mul_of_one_le_right (show (0 : ℝ) ≤ 10000 * (n : ℝ) * (M : ℝ) by positivity) hge
      linarith
    exact (pow_le_pow_left₀ (by positivity) h1 4).trans hL_ge_C
  have hyz : y ≤ z := by
    have h1 : 4 * (y : ℝ) ≤ (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) := by
      rw [Real.rpow_def_of_pos hK_pos]
      have h4y : 4 * (y : ℝ) ≤ Real.exp (Real.log (y : ℝ) + 2) := by
        rw [Real.exp_add, Real.exp_log (by exact_mod_cast (by omega : 0 < y))]
        have he2 : (4 : ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp (1 : ℝ)
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
        nlinarith [show (0 : ℝ) ≤ (y : ℝ) by positivity]
      refine h4y.trans (Real.exp_le_exp.mpr ?_)
      have hL_lin : 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) ≤ Real.log (K : ℝ) := by
        have hge : (1 : ℝ) ≤ (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) :=
          mul_three_ge_one hnR hs₀_ge1 (by linarith)
        exact (le_pow_four_of_one_le (by linarith)).trans hL_ge_r1
      have : Real.log (y : ℝ) + 2 ≤ Real.log (K : ℝ) / (8 * (s₀ : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have hns : (s₀ : ℝ) ≤ (n : ℝ) * (s₀ : ℝ) := le_mul_of_one_le_left (by positivity) hnR
        nlinarith only [hL_lin, hns, hlogy_pos, hs₀_ge1]
      linarith [show Real.log (K : ℝ) * (1 / (8 * (s₀ : ℝ))) = Real.log (K : ℝ) / (8 * (s₀ : ℝ)) by ring]
    have hfl : (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) - 1 < (z : ℝ) := Nat.sub_one_lt_floor _
    have hyR : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy16
    exact_mod_cast (show (y : ℝ) ≤ (z : ℝ) by linarith)
  have hzK : z ≤ K := by
    have h1 : (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) ≤ (K : ℝ) := by
      conv_rhs => rw [← Real.rpow_one (K : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ K)) (by rw [div_le_one (by positivity)]; linarith)
    exact Nat.floor_le_of_le (by exact_mod_cast h1)
  have hL_ge1000 : (1000 : ℝ) ^ 4 ≤ Real.log (K : ℝ) := by
    have h1 : (1000 : ℝ) ≤ 1000 * (n : ℝ) * (s₀ : ℝ) * (Real.log (y : ℝ) + 10) := by
      have := mul_three_ge_one hnR hs₀_ge1 (by linarith only [hlogy_pos] : (1 : ℝ) ≤ Real.log (y : ℝ) + 10)
      linarith only [this]
    exact (pow_le_pow_left₀ (by norm_num) h1 4).trans hL_ge_r1
  have hfK_sm := hX_sm K hK_Xsm
  have hfK_le : ∑ p ∈ (Finset.range (K + 1)).filter (· ∈ B'), (1 : ℝ) / (p : ℝ) ≤ Real.log (K : ℝ) := by
    have hloglog : Real.log (Real.log (K : ℝ)) ≤ Real.log (K : ℝ) :=
      (Real.log_le_sub_one_of_pos hL_pos).trans (by linarith only [hL_pos])
    have h18 : (1 / (8 * (n : ℝ))) ≤ 1 := by rw [div_le_one (by positivity)]; linarith only [hnR]
    have hnn : 0 ≤ Real.log (Real.log (K : ℝ)) := Real.log_nonneg (by linarith only [hL_ge1000])
    exact hfK_sm.trans ((mul_le_of_le_one_left hnn h18).trans hloglog)
  have hVz_ge : 1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤ V_z := by
    have hVr := V_ratio_bound B' n y y z A_n hAn hy le_rfl hyz
    have hVr_pos : 0 < V_z := by dsimp only [V_z, B_med]; convert hVr.1
    have hVr_rat : 1 / V_z ≤ Real.exp (2 * (n : ℝ) * ∑ b ∈ B_med, (1 : ℝ) / (b : ℝ)) := by
      have h1 := hVr.2.2.2
      dsimp only at h1
      rw [Finset.Ioc_self, Finset.filter_empty, Finset.prod_empty] at h1
      dsimp only [V_z, B_med]
      convert h1
    have hinv_le : ∑ b ∈ B_med, (1 : ℝ) / (b : ℝ) ≤ (1 / (8 * (n : ℝ))) * Real.log (Real.log (K : ℝ)) := by
      have hsub : B_med ⊆ (Finset.range (K + 1)).filter (· ∈ B') := by
        intro b hb
        have hbf := Finset.mem_filter.mp hb
        have hbi := Finset.mem_Ioc.mp hbf.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbf.2⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans hfK_sm
    have hdiv : 1 / V_z ≤ (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := by
      refine hVr_rat.trans ?_
      rw [Real.rpow_def_of_pos hL_pos]
      refine Real.exp_le_exp.mpr ?_
      have hmul := mul_le_mul_of_nonneg_left hinv_le (show (0 : ℝ) ≤ 2 * (n : ℝ) by positivity)
      have hcancel : 2 * (n : ℝ) * (1 / (8 * (n : ℝ)) * Real.log (Real.log (K : ℝ))) =
          Real.log (Real.log (K : ℝ)) * (1 / 4) := by field_simp; ring
      linarith only [hmul, hcancel]
    have hL4_pos : 0 < (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL_pos _
    rw [div_le_iff₀ hL4_pos]
    have h2 := (div_le_iff₀ hVr_pos).mp hdiv
    linarith only [h2]
  have hVz_pos : 0 < V_z := lt_of_lt_of_le (by positivity) hVz_ge
  -- Lower bound on S_good = {k ∈ Icc 1 K | ∀ p ∈ B_med, ∀ a ∈ A_n, ¬ p ∣ a + k * M}
  let S_good := (Finset.Icc 1 K).filter (fun k => ∀ p ∈ B_med, ∀ a ∈ A_n, ¬ p ∣ a + k * M)
  have hSgood_lower : (90 / 100 : ℝ) * (K : ℝ) * V_z ≤ (S_good.card : ℝ) := by
    have hcop_s : ∀ b ∈ B_med, Nat.Coprime b (1 * M) := by
      intro b hb; rw [one_mul]
      have hbf := Finset.mem_filter.mp hb
      exact hcop_M b hbf.2 (Finset.mem_Ioc.mp hbf.1).1
    have hsieve := (sieve_ap_bounds B' hB' hge2 K n 1 1 M y z A_n hn1 hAn hy hy16 hy_exp hyz hpi (by convert hcop_s)).1
    have hcard_eq : S_good.card =
        ((Finset.range K).filter (fun t => ∀ b ∈ B_med, ∀ a ∈ A_n, ¬ b ∣ a + (1 + t * 1) * M)).card := by
      refine Finset.card_bij (fun k _ => k - 1) ?_ ?_ ?_
      · intro k hk
        simp only [S_good, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hk ⊢
        refine ⟨by omega, ?_⟩
        rw [mul_one, show 1 + (k - 1) = k by omega]; exact hk.2
      · intro k₁ hk₁ k₂ hk₂ heq
        have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hk₁).1
        have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hk₂).1
        omega
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_range] at ht
        refine ⟨t + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩, by omega⟩
        simpa [add_comm, mul_one] using ht.2
    rw [hcard_eq]
    have hz_pow : (z : ℝ) ^ (2 * s₀) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by
      have hz_le : (z : ℝ) ≤ (K : ℝ) ^ (1 / (8 * (s₀ : ℝ))) := Nat.floor_le (by positivity)
      calc (z : ℝ) ^ (2 * s₀) ≤ ((K : ℝ) ^ (1 / (8 * (s₀ : ℝ)))) ^ (2 * s₀) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hz_le _
        _ = (K : ℝ) ^ (1 / (8 * (s₀ : ℝ)) * ((2 * s₀ : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hK_pos.le]
        _ = (K : ℝ) ^ (1 / 4 : ℝ) := by congr 1; push_cast; field_simp; ring
    have herr_lb : 2 * (K : ℝ) ^ (1 / 4 : ℝ) ≤ (8 / 100 : ℝ) * (K : ℝ) * V_z := by
      have hK34 : 25 * (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤ (K : ℝ) ^ (3 / 4 : ℝ) := by
        have hL4 : (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) ≤ Real.log (K : ℝ) := by
          conv_rhs => rw [← Real.rpow_one (Real.log (K : ℝ))]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hL_ge1000]) (by norm_num)
        have hK34_exp : (Real.log (K : ℝ)) ^ 2 / 4 ≤ (K : ℝ) ^ (3 / 4 : ℝ) := by
          rw [Real.rpow_def_of_pos hK_pos]
          have h2 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ Real.log (K : ℝ) * (3 / 4) by positivity) 3
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
            pow_zero, pow_one, div_one, zero_add] at h2
          nlinarith only [h2, hL_pos]
        have hL_big : (1000 : ℝ) ≤ Real.log (K : ℝ) := by linarith only [hL_ge1000]
        nlinarith only [hL4, hK34_exp, hL_big]
      have hK_prod : (K : ℝ) ^ (1 / 4 : ℝ) * (K : ℝ) ^ (3 / 4 : ℝ) = (K : ℝ) := by
        rw [← Real.rpow_add hK_pos]; norm_num
      have hL4_pos : 0 < (Real.log (K : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL_pos _
      have h1 : 2 * (K : ℝ) ^ (1 / 4 : ℝ) ≤ (8 / 100 : ℝ) * (K : ℝ) * (1 / (Real.log (K : ℝ)) ^ (1 / 4 : ℝ)) := by
        rw [mul_one_div, le_div_iff₀ hL4_pos]
        have := mul_le_mul_of_nonneg_left hK34 (show (0 : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) by positivity)
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_left hVz_ge (by positivity))
    have hsieve' : (98 / 100 : ℝ) * (K : ℝ) * V_z - 2 * (z : ℝ) ^ (2 * s₀) ≤
        (((Finset.range K).filter (fun t => ∀ b ∈ B_med, ∀ a ∈ A_n, ¬ b ∣ a + (1 + t * 1) * M)).card : ℝ) := by
      convert hsieve
    linarith only [hsieve', hz_pow, herr_lb]
  -- Upper bounds on bad k ∈ S_good hit by b ∈ (z, n + K * M] ∩ B'
  have hr1 := range1_bound B' hB' hge2 K n M y J₀ A_n hn1 hAn hy hy16 hy_exp hcop_M hpi hK16 hL_ge_r1
    (by convert hf_good) (by convert hVz_ge)
  have hr2 := range2_bound B' hB' hge2 K n M y J₀ A_n hn1 hAn hJ₀_ge6 hy hy16 hy_exp hcop_M hpi hK16 hL_ge_r23
    (by convert hfK_le) (by convert hf_good) (by convert hVz_ge)
  have hr3 := range3_bound B' hB' hge2 K n M y J₀ A_n hn1 hAn hJ₀_ge6 hJ₀_pow hy hy16 hy_exp hcop_M hpi
    (max_le hK16 hKy2) hL_ge_r23 (by convert hfK_le) (by convert hf_good) (by convert hVz_ge)
  have hr4 := range4_bound B' hB' hge2 K n M y A_n V_z hn1 hM1 hAn hy16 hcop_M hpi
    (max_le hKn hKy2) hL_ge_r4 hVz_ge
  -- Combine: S_good has strictly more elements than the 4 bad sets combined
  let B_cut_exp : ℕ := ⌊(K : ℝ) / Real.exp (Real.sqrt (Real.log (K : ℝ)))⌋₊
  let Bad1 := (Finset.Icc 1 K).filter (fun k => (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
    ∃ a ∈ A_n, ∃ b ∈ (Finset.Ioc z ⌊Real.sqrt (K : ℝ)⌋₊).filter (· ∈ B'), b ∣ a + k * M)
  let Bad2 := (Finset.Icc 1 K).filter (fun k => (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
    ∃ a ∈ A_n, ∃ b ∈ (Finset.Ioc ⌊Real.sqrt (K : ℝ)⌋₊ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J₀)⌋₊).filter (· ∈ B'), b ∣ a + k * M)
  let Bad3 := (Finset.Icc 1 K).filter (fun k => (∀ p ∈ B_med, ∀ a' ∈ A_n, ¬ p ∣ a' + k * M) ∧
    ∃ a ∈ A_n, ∃ b ∈ (Finset.Ioc ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J₀)⌋₊ B_cut_exp).filter (· ∈ B'), b ∣ a + k * M)
  let Bad4 := (Finset.Icc 1 K).filter (fun k =>
    ∃ a ∈ A_n, ∃ b ∈ (Finset.Ioc B_cut_exp (n + K * M)).filter (· ∈ B'), b ∣ a + k * M)
  let S_surv := S_good \ (Bad1 ∪ Bad2 ∪ Bad3 ∪ Bad4)
  have hsurv_pos : (0 : ℝ) < (S_surv.card : ℝ) := by
    have hcard_sdiff : S_good.card ≤ S_surv.card + (Bad1 ∪ Bad2 ∪ Bad3 ∪ Bad4).card := by
      have h1 := Finset.card_sdiff_add_card_inter S_good (Bad1 ∪ Bad2 ∪ Bad3 ∪ Bad4)
      have hinter : (S_good ∩ (Bad1 ∪ Bad2 ∪ Bad3 ∪ Bad4)).card ≤ (Bad1 ∪ Bad2 ∪ Bad3 ∪ Bad4).card :=
        Finset.card_le_card Finset.inter_subset_right
      dsimp only [S_surv]
      omega
    have hunion_card : (Bad1 ∪ Bad2 ∪ Bad3 ∪ Bad4).card ≤ Bad1.card + Bad2.card + Bad3.card + Bad4.card := by
      calc (Bad1 ∪ Bad2 ∪ Bad3 ∪ Bad4).card
          ≤ (Bad1 ∪ Bad2 ∪ Bad3).card + Bad4.card := Finset.card_union_le _ _
        _ ≤ (Bad1 ∪ Bad2).card + Bad3.card + Bad4.card := by linarith [Finset.card_union_le (Bad1 ∪ Bad2) Bad3]
        _ ≤ Bad1.card + Bad2.card + Bad3.card + Bad4.card := by linarith [Finset.card_union_le Bad1 Bad2]
    have hcast : (S_good.card : ℝ) ≤ (S_surv.card : ℝ) + (Bad1.card : ℝ) + (Bad2.card : ℝ) + (Bad3.card : ℝ) + (Bad4.card : ℝ) := by
      exact_mod_cast (show S_good.card ≤ S_surv.card + Bad1.card + Bad2.card + Bad3.card + Bad4.card by omega)
    have hKV_pos : 0 < (K : ℝ) * V_z := mul_pos hK_pos hVz_pos
    have hb1 : (Bad1.card : ℝ) ≤ (2 / 100 : ℝ) * (K : ℝ) * V_z := by convert hr1
    have hb2 : (Bad2.card : ℝ) ≤ (2 / 100 : ℝ) * (K : ℝ) * V_z := by convert hr2
    have hb3 : (Bad3.card : ℝ) ≤ (6 / 100 : ℝ) * (K : ℝ) * V_z := by convert hr3
    have hb4 : (Bad4.card : ℝ) ≤ (2 / 100 : ℝ) * (K : ℝ) * V_z := by convert hr4
    linarith only [hSgood_lower, hcast, hb1, hb2, hb3, hb4, hKV_pos]
  have hsurv_ne : S_surv.Nonempty := Finset.card_pos.mp (by exact_mod_cast hsurv_pos)
  obtain ⟨k, hk⟩ := hsurv_ne
  have hk_sdiff := Finset.mem_sdiff.mp hk
  have hk_good := Finset.mem_filter.mp hk_sdiff.1
  have hk_icc := Finset.mem_Icc.mp hk_good.1
  have hk_not_bad : k ∉ Bad1 ∧ k ∉ Bad2 ∧ k ∉ Bad3 ∧ k ∉ Bad4 := by
    have h := hk_sdiff.2
    simp only [Finset.mem_union, not_or] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  -- Set t = k * M and verify HasTranslationProperty
  refine ⟨k * M, Nat.mul_pos hk_icc.1 hM1, fun a ha1 han => ?_⟩
  simp only [Set.mem_setOf_eq]
  constructor
  · intro haA b hbB hdvd
    have hb0 : b ≠ 0 := by intro h0; subst h0; rw [zero_dvd_iff] at hdvd; have := Nat.mul_pos hk_icc.1 hM1; omega
    have hbB' : b ∈ B' := ⟨hbB, fun h0 => hb0 (Set.mem_singleton_iff.mp h0)⟩
    have ha_mem : a ∈ A_n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, han⟩, haA⟩
    have hb_le_max : b ≤ n + K * M := by
      have hpos : 0 < a + k * M := by omega
      have hle : a + k * M ≤ n + K * M := Nat.add_le_add han (Nat.mul_le_mul_right M hk_icc.2)
      exact (Nat.le_of_dvd hpos hdvd).trans hle
    by_cases hby : b ≤ y
    · have hbM : b ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hge2 b hbB', hby⟩, hbB'⟩)
      have hba : b ∣ a := (Nat.dvd_add_left (dvd_mul_of_dvd_right hbM k)).mp hdvd
      exact haA b hbB hba
    · push Not at hby
      by_cases hbz : b ≤ z
      · exact hk_good.2 b (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hby, hbz⟩, hbB'⟩) a ha_mem hdvd
      · push Not at hbz
        by_cases hb1 : b ≤ ⌊Real.sqrt (K : ℝ)⌋₊
        · exact hk_not_bad.1 (Finset.mem_filter.mpr ⟨hk_good.1, hk_good.2, a, ha_mem, b,
            Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hbz, hb1⟩, hbB'⟩, hdvd⟩)
        · push Not at hb1
          by_cases hb2 : b ≤ ⌊(K : ℝ) ^ (1 - (1 / 2 : ℝ) ^ J₀)⌋₊
          · exact hk_not_bad.2.1 (Finset.mem_filter.mpr ⟨hk_good.1, hk_good.2, a, ha_mem, b,
              Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hb1, hb2⟩, hbB'⟩, hdvd⟩)
          · push Not at hb2
            by_cases hb3 : b ≤ B_cut_exp
            · exact hk_not_bad.2.2.1 (Finset.mem_filter.mpr ⟨hk_good.1, hk_good.2, a, ha_mem, b,
                Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hb2, hb3⟩, hbB'⟩, hdvd⟩)
            · push Not at hb3
              exact hk_not_bad.2.2.2 (Finset.mem_filter.mpr ⟨hk_good.1, a, ha_mem, b,
                Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hb3, hb_le_max⟩, hbB'⟩, hdvd⟩)
  · intro hatA b hbB hba
    have hb0 : b ≠ 0 := by intro h0; subst h0; rw [zero_dvd_iff] at hba; omega
    have hbB' : b ∈ B' := ⟨hbB, fun h0 => hb0 (Set.mem_singleton_iff.mp h0)⟩
    have hb_le : b ≤ y := (Nat.le_of_dvd (by omega) hba).trans (by omega)
    have hbM : b ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hge2 b hbB', hb_le⟩, hbB'⟩)
    exact hatA b hbB (dvd_add hba (dvd_mul_of_dvd_right hbM k))

end Erdos675Proof

theorem OMA.solution : type_of% @Erdos675.erdos_675.variants.brun :=
  Erdos675Proof.main_theorem

