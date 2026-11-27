import FormalConjectures.ErdosProblems.«360»

/-!
# Reduction of Erdős Problem 360 (Conlon-Fox-Pham)

Conlon, Fox, and Pham [CFP21, Theorem 1.5] proved that
$$f(n) \asymp \frac{n^{1/3}(n/\phi(n))}{(\log n)^{1/3}(\log\log n)^{2/3}}.$$

We decompose the theorem into four independent subgoals:
- `H1`: Constructive upper bound coloring (pure combinatorics and modular arithmetic):
  given `r`, a finite set `S` of primes not dividing `n`, and a modulus `d` coprime to `n`
  whose prime factors all lie in `S`, the four-step CFP21 coloring gives
  `Erdos360.f n ≤ r / 2 + S.card + 2 * d.totient + (R'.card / d + 1)`.
- `H2`: Analytic upper bound parameter existence and sieve estimate (CFP21 Claim 5.12 and
  Lemma 5.9): there exist `r`, `d`, `S` satisfying the hypotheses of `H1` such that the resulting
  color bound is `O(answer n)`.
- `H3`: Analytic lower bound scale selection (CFP21 Claim B.4): for every `c > 0` and
  sufficiently large `n`, setting `r = ⌊c * answer n⌋₊`, there exists a scale `y` with `2 * y < n`,
  `r ^ 2 ≤ y`, `n ^ (3 / 5) ≤ y`, and `n` lying in the critical window
  `[y ^ 2 * (n / φ(n)) * τ(r, n) / (25 * r), y ^ 2 * (n / φ(n)) * τ(r, n) / (15 * r)]`.
- `H4`: Ramsey subset-sum lower bound (CFP21 Lemma 5.1): for some `c > 0` and sufficiently large
  `n`, at any valid scale `y`, every `Finpartition` of `{1, ..., n - 1}` with at most
  `r = ⌊c * answer n⌋₊` parts has some part containing `n` among its subset sums.
-/

-- Credit: @green-notes

namespace OMA.R_Erdos360_erdos_360_R1

open Filter Asymptotics

def H1 : Prop :=
  ∀ n r d : ℕ, ∀ S : Finset ℕ, 2 ≤ n → 1 ≤ d →
    (∀ p ∈ S, p.Prime ∧ ¬ p ∣ n) →
    Nat.Coprime d n →
    (∀ p : ℕ, p.Prime → p ∣ d → p ∈ S) →
    let R' := (Finset.Icc 1 (n / d)).filter (fun t ↦ ∀ p ∈ S, ¬ p ∣ t)
    Erdos360.f n ≤ r / 2 + S.card + 2 * d.totient + (R'.card / d + 1)

def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∃ r d : ℕ, ∃ S : Finset ℕ,
    1 ≤ d ∧ (∀ p ∈ S, p.Prime ∧ ¬ p ∣ n) ∧ Nat.Coprime d n ∧
    (∀ p : ℕ, p.Prime → p ∣ d → p ∈ S) ∧
    let R' := (Finset.Icc 1 (n / d)).filter (fun t ↦ ∀ p ∈ S, ¬ p ∣ t)
    ((r / 2 + S.card + 2 * d.totient + (R'.card / d + 1) : ℕ) : ℝ) ≤
      C * ((n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
        (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ)))

def H3 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop,
    let psi := (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
      (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ))
    let r := ⌊c * psi⌋₊
    let tau := ∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
      (1 - (1 : ℝ) / p)
    ∃ y : ℕ, 2 * y < n ∧ r ^ 2 ≤ y ∧ (n : ℝ) ^ (3 / 5 : ℝ) ≤ (y : ℝ) ∧
      (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (25 * (r : ℝ)) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (15 * (r : ℝ))

def H4 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ y : ℕ,
    let psi := (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
      (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ))
    let r := ⌊c * psi⌋₊
    let tau := ∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
      (1 - (1 : ℝ) / p)
    2 * y < n → r ^ 2 ≤ y → (n : ℝ) ^ (3 / 5 : ℝ) ≤ (y : ℝ) →
    (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (25 * (r : ℝ)) ≤ (n : ℝ) →
    (n : ℝ) ≤ (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (15 * (r : ℝ)) →
    ∀ P : Finpartition (Finset.Icc 1 (n - 1)), P.parts.card ≤ r →
      ∃ A ∈ P.parts, n ∈ subsetSums (A : Set ℕ)

lemma answer_pos_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    0 < Erdos360.erdos_360.answer n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htot_pos : (0 : ℝ) < n.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < n)
  have h3 : Real.exp 1 < (n : ℝ) := by
    have hlt : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    exact lt_of_lt_of_le hlt (by exact_mod_cast hn)
  have hlog1 : 1 < Real.log (n : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) h3
  have hlog_pos : 0 < Real.log (n : ℝ) := lt_trans zero_lt_one hlog1
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog1
  unfold Erdos360.erdos_360.answer
  positivity

lemma admissible_nonempty {n : ℕ} (hn : 2 ≤ n) :
    {r : ℕ | ∃ P : Finpartition (Finset.Icc 1 (n - 1)),
      P.parts.card = r ∧ ∀ A ∈ P.parts, n ∉ subsetSums (A : Set ℕ)}.Nonempty := by
  refine ⟨(⊥ : Finpartition (Finset.Icc 1 (n - 1))).parts.card,
    (⊥ : Finpartition (Finset.Icc 1 (n - 1))), rfl, fun A hA hmem ↦ ?_⟩
  rw [Finpartition.mem_bot_iff] at hA
  obtain ⟨a, ha, rfl⟩ := hA
  have ha_lt : a < n := by
    have := (Finset.mem_Icc.mp ha).2
    omega
  obtain ⟨B, hBA, hsum⟩ := hmem
  have hB_sub : B ⊆ ({a} : Finset ℕ) := by
    intro x hx
    exact hBA hx
  rcases Finset.subset_singleton_iff.mp hB_sub with rfl | rfl
  · simp at hsum
    omega
  · simp at hsum
    omega

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos360.erdos_360 := by
  intro h1 h2 h3 h4
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, hC_ev⟩ := h2
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [hC_ev, eventually_ge_atTop 3] with n hn hn3
    obtain ⟨r, d, S, hd, hS, hd_cop, hd_fac, hbound⟩ := hn
    have hf : Erdos360.f n ≤
        r / 2 + S.card + 2 * d.totient +
          (((Finset.Icc 1 (n / d)).filter (fun t ↦ ∀ p ∈ S, ¬ p ∣ t)).card / d + 1) :=
      h1 n r d S (by omega) hd hS hd_cop hd_fac
    have hf_real : (Erdos360.f n : ℝ) ≤ C * Erdos360.erdos_360.answer n := by
      have hf' : (Erdos360.f n : ℝ) ≤
          ((r / 2 + S.card + 2 * d.totient +
            (((Finset.Icc 1 (n / d)).filter (fun t ↦ ∀ p ∈ S, ¬ p ∣ t)).card / d + 1) : ℕ) : ℝ) := by
        exact_mod_cast hf
      exact hf'.trans hbound
    have hans_pos : 0 < Erdos360.erdos_360.answer n := answer_pos_of_three_le hn3
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hans_pos.le]
    exact hf_real
  · obtain ⟨c, hc, hc_ev⟩ := h4
    have hy_ev := h3 c hc
    rw [Asymptotics.isBigO_iff]
    refine ⟨c⁻¹, ?_⟩
    filter_upwards [hc_ev, hy_ev, eventually_ge_atTop 3] with n h4n h3n hn3
    obtain ⟨y, hy1, hy2, hy3, hy4, hy5⟩ := h3n
    have hS_ne := admissible_nonempty (by omega : 2 ≤ n)
    have hmem := Nat.sInf_mem hS_ne
    change ∃ P : Finpartition (Finset.Icc 1 (n - 1)),
      P.parts.card = Erdos360.f n ∧ ∀ A ∈ P.parts, n ∉ subsetSums (A : Set ℕ) at hmem
    obtain ⟨P, hP_card, hP_avoid⟩ := hmem
    have hnot_le : ¬ Erdos360.f n ≤ ⌊c * Erdos360.erdos_360.answer n⌋₊ := by
      intro hle
      have hP_le : P.parts.card ≤ ⌊c * Erdos360.erdos_360.answer n⌋₊ := hP_card ▸ hle
      obtain ⟨A, hA_mem, hA_sum⟩ := h4n y hy1 hy2 hy3 hy4 hy5 P hP_le
      exact hP_avoid A hA_mem hA_sum
    have hlt : ⌊c * Erdos360.erdos_360.answer n⌋₊ < Erdos360.f n := lt_of_not_ge hnot_le
    have hle_succ : (⌊c * Erdos360.erdos_360.answer n⌋₊ : ℝ) + 1 ≤ (Erdos360.f n : ℝ) := by
      exact_mod_cast hlt
    have hans_pos : 0 < Erdos360.erdos_360.answer n := answer_pos_of_three_le hn3
    have hmul_pos : 0 ≤ c * Erdos360.erdos_360.answer n := (mul_pos hc hans_pos).le
    have hfloor_lt : c * Erdos360.erdos_360.answer n <
        (⌊c * Erdos360.erdos_360.answer n⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hcf : c * Erdos360.erdos_360.answer n ≤ (Erdos360.f n : ℝ) :=
      (lt_of_lt_of_le hfloor_lt hle_succ).le
    have hbound : Erdos360.erdos_360.answer n ≤ c⁻¹ * (Erdos360.f n : ℝ) := by
      calc Erdos360.erdos_360.answer n = c⁻¹ * (c * Erdos360.erdos_360.answer n) := by
            field_simp [hc.ne']
        _ ≤ c⁻¹ * (Erdos360.f n : ℝ) := mul_le_mul_of_nonneg_left hcf (inv_pos.mpr hc).le
    rw [Real.norm_of_nonneg hans_pos.le, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hbound

end OMA.R_Erdos360_erdos_360_R1
