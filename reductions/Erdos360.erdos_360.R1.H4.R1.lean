import OMAReductions.R_Erdos360_erdos_360_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- Reduction Erdos360.erdos_360.R1.H4.R1 of step Erdos360.erdos_360.R1.H4
-- Credit: @green-notes

namespace OMA.R_Erdos360_erdos_360_R1_H4_R1

open Filter Classical

def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ r x : ℕ, r ≤ n → (n : ℝ) ^ (1 / 10 : ℝ) ≤ (r : ℝ) →
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (x : ℝ) →
    let S := n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime)
    let tau := ∏ p ∈ S, (1 - (1 : ℝ) / p)
    let Y_up := (Finset.Ico x (2 * x)).filter (fun m ↦ ∃ u q : ℕ,
      m = q * u ∧ u ∣ n ∧ (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ p ∈ S, ¬ p ∣ q)
    let Y_lo := (Finset.Ico x (2 * x)).filter (fun m ↦ ∃ u q : ℕ,
      m = q * u ∧ u ∣ n ∧ (u : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ p ∈ S, ¬ p ∣ q)
    ((Y_up.card : ℝ) ≤ 8 * ((n : ℝ) / (n.totient : ℝ)) * tau * (x : ℝ)) ∧
      (r ^ 2 ≤ x → ((n : ℝ) / (n.totient : ℝ)) * tau * (x : ℝ) / 8 ≤ (Y_lo.card : ℝ))

def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ r a b L : ℕ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ (r : ℝ) → r ≤ n →
    1 ≤ b → b ≤ n → (r : ℝ) ^ (1 / 16 : ℝ) ≤ (L : ℝ) →
    let P := (Finset.range r).image (Nat.nth Nat.Prime) \ n.primeFactors
    (((Finset.range L).filter (fun k ↦ ∀ p ∈ P, ¬ p ∣ a + b * k)).card : ℝ) ≤
      256 * (L : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)

def H3 : Prop :=
  ∀ ℓ q m : ℕ, 8 ≤ ℓ → 1 ≤ q → 3 ≤ m → 3 * q ≤ ℓ * (m - 2) →
    ∀ S : Fin ℓ → Finset ℕ,
      (∀ i, m ≤ (S i).card) →
      (∀ i, ∃ a : ℕ, S i ⊆ Finset.Icc a (a + q)) →
      (∀ i, ∀ d : ℕ, 1 < d → ¬ (∀ x ∈ S i, ∀ y ∈ S i, x % d = y % d)) →
      ∃ a b : ℕ, a + ℓ * (m - 1) ≤ b ∧
        ∀ t ∈ Finset.Icc a b, ∃ f : Fin ℓ → ℕ, (∀ i, f i ∈ S i) ∧ ∑ i, f i = t

def H4 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ℓ : ℕ, 8 ≤ ℓ ∧ ∀ᶠ n : ℕ in atTop,
    ∀ y r v : ℕ, ∀ Q : Finset ℕ,
      let psi := (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
        (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ))
      r = ⌊c * psi⌋₊ →
      let tau := ∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
        (1 - (1 : ℝ) / p)
      2 * y < n → r ^ 2 ≤ y → (n : ℝ) ^ (3 / 5 : ℝ) ≤ (y : ℝ) →
      (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (25 * (r : ℝ)) ≤ (n : ℝ) →
      (n : ℝ) ≤ (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (15 * (r : ℝ)) →
      1 ≤ v → (v : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) →
      (∀ x ∈ Q, y ≤ v * x ∧ v * x < 2 * y) →
      (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ (1 / 7 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) →
      (∀ d : ℕ, 2 ≤ d → (y : ℝ) ^ (1 / 4 : ℝ) ≤ ((Q.filter (fun x ↦ ¬ d ∣ x)).card : ℝ)) →
      (∀ T : Finset ℕ, T ⊆ Q →
        64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) < (T.card : ℝ) →
        (v : ℝ) * ((T.gcd (fun x ↦ x) : ℕ) : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ)) →
      (∀ a b L : ℕ, 1 ≤ b → b ≤ n → (r : ℝ) ^ (1 / 16 : ℝ) ≤ (L : ℝ) →
        (((Finset.range L).filter (fun k ↦ a + b * k ∈ Q)).card : ℝ) ≤
          256 * (L : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ)) →
      ∃ V : Fin ℓ → Finset ℕ,
        (∀ i, V i ⊆ Q) ∧ (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
        (∀ i, ((V i).card : ℝ) ≤ (Q.card : ℝ) / (8 * (ℓ : ℝ))) ∧
        (∀ i, let S := (V i).powerset.image (fun B ↦ ∑ x ∈ B, x)
          (y : ℝ) * (Q.card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) ≤ (S.card : ℝ) ∧
          ∀ d : ℕ, 1 < d → ¬ (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ % d = s₂ % d))

section Helpers

private lemma inv_one_sub_inv_le_exp {p : ℝ} (hp : 2 ≤ p) :
    (1 - 1 / p)⁻¹ ≤ Real.exp (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hsub : 1 - 1 / p = (p - 1) / p := by field_simp
  rw [hsub, inv_div]
  have hsplit : p / (p - 1) = 1 / (p - 1) + 1 := by field_simp; ring
  rw [hsplit]
  refine (Real.add_one_le_exp (1 / (p - 1))).trans (Real.exp_le_exp.mpr ?_)
  rw [div_le_div_iff₀ hp1 hp0]
  linarith

private lemma exp_neg_le_one_sub_inv {p : ℝ} (hp : 2 ≤ p) :
    Real.exp (- (2 / p)) ≤ 1 - 1 / p := by
  have hp0 : 0 < p := by linarith
  have hpos : 0 < 1 - 1 / p := by rw [sub_pos, div_lt_one hp0]; linarith
  have h1 := inv_one_sub_inv_le_exp hp
  rw [Real.exp_neg]
  simpa using inv_anti₀ (inv_pos.mpr hpos) h1

private lemma nth_prime_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → (k : ℝ) * Real.log (k : ℝ) ≤ C * (Nat.nth Nat.Prime k : ℝ) := by
  have hev := Chebyshev.eventually_primeCounting_le (ε := 1 / 2) (by norm_num)
  have htend : Tendsto (fun k : ℕ ↦ (Nat.nth Nat.Prime k : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨⌈b⌉₊, fun k hk ↦ ?_⟩
    have h1 : b ≤ (k : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast hk)
    have h2 : k ≤ Nat.nth Nat.Prime k := (Nat.add_two_le_nth_prime k).trans' (by omega)
    exact h1.trans (by exact_mod_cast h2)
  have hev_k := htend.eventually hev
  rw [eventually_atTop] at hev_k
  obtain ⟨K₀, hK₀⟩ := hev_k
  let term : ℕ → ℝ := fun j ↦ (j : ℝ) * Real.log (j : ℝ) / (Nat.nth Nat.Prime j : ℝ)
  let K := max K₀ 2
  let C := max (Real.log 4 + 1 / 2) (∑ k ∈ Finset.Ico 2 K, term k + 1)
  have hCpos : 0 < C := by
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  refine ⟨C, hCpos, fun k hk ↦ ?_⟩
  by_cases hlt : k < K
  · have hmem : k ∈ Finset.Ico 2 K := Finset.mem_Ico.mpr ⟨hk, hlt⟩
    have hterm_nonneg : ∀ j ∈ Finset.Ico 2 K, 0 ≤ term j := by
      intro j hj
      have hj2 : (1 : ℝ) ≤ (j : ℝ) := by
        exact_mod_cast (show 1 ≤ j by have := (Finset.mem_Ico.mp hj).1; omega)
      have hlog : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg hj2
      dsimp only [term]
      positivity
    have hterm_le : term k ≤ ∑ j ∈ Finset.Ico 2 K, term j :=
      Finset.single_le_sum hterm_nonneg hmem
    have hmax : ∑ j ∈ Finset.Ico 2 K, term j + 1 ≤ C := le_max_right _ _
    have hleC : term k ≤ C := by linarith
    have hp_pos : (0 : ℝ) < (Nat.nth Nat.Prime k : ℝ) := by
      exact_mod_cast (Nat.add_two_le_nth_prime k).trans_lt' (by omega)
    exact (div_le_iff₀ hp_pos).mp hleC
  · have hkK₀ : K₀ ≤ k := (le_max_left K₀ 2).trans (not_lt.mp hlt)
    have hpi := hK₀ k hkK₀
    have hfl : ⌊(Nat.nth Nat.Prime k : ℝ)⌋₊ = Nat.nth Nat.Prime k := Nat.floor_natCast _
    rw [hfl] at hpi
    have hk_le_pi : k ≤ Nat.primeCounting (Nat.nth Nat.Prime k) := by
      calc k = Nat.primeCounting' (Nat.nth Nat.Prime k) := (Nat.primeCounting'_nth_eq k).symm
        _ ≤ Nat.primeCounting' (Nat.nth Nat.Prime k + 1) :=
          Nat.monotone_primeCounting' (Nat.le_succ _)
        _ = Nat.primeCounting (Nat.nth Nat.Prime k) := rfl
    have hkp : k ≤ Nat.nth Nat.Prime k := by
      have := Nat.add_two_le_nth_prime k
      omega
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime k : ℝ) := by
      exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)
    have hlogp_pos : 0 < Real.log (Nat.nth Nat.Prime k : ℝ) := Real.log_pos (by linarith)
    have h1 : (k : ℝ) ≤ (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) /
        Real.log (Nat.nth Nat.Prime k : ℝ) :=
      (by exact_mod_cast hk_le_pi : (k : ℝ) ≤ Nat.primeCounting (Nat.nth Nat.Prime k)).trans hpi
    have h2 : (k : ℝ) * Real.log (Nat.nth Nat.Prime k : ℝ) ≤
        (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) := (le_div_iff₀ hlogp_pos).mp h1
    have hlog_le : Real.log (k : ℝ) ≤ Real.log (Nat.nth Nat.Prime k : ℝ) :=
      Real.log_le_log hk_pos (by exact_mod_cast hkp)
    have h3 : (k : ℝ) * Real.log (k : ℝ) ≤ (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) :=
      (mul_le_mul_of_nonneg_left hlog_le hk_pos.le).trans h2
    exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

private lemma nth_prime_ge_div_four :
    ∀ᶠ r : ℕ in atTop, (r : ℝ) * Real.log (r : ℝ) / 4 ≤ (Nat.nth Nat.Prime r : ℝ) := by
  have hev := Chebyshev.eventually_primeCounting_le (ε := 1 / 2) (by norm_num)
  have htend : Tendsto (fun k : ℕ ↦ (Nat.nth Nat.Prime k : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨⌈b⌉₊, fun k hk ↦ ?_⟩
    have h1 : b ≤ (k : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast hk)
    have h2 : k ≤ Nat.nth Nat.Prime k := (Nat.add_two_le_nth_prime k).trans' (by omega)
    exact h1.trans (by exact_mod_cast h2)
  filter_upwards [htend.eventually hev, eventually_ge_atTop 2] with k hpi hk2
  have hfl : ⌊(Nat.nth Nat.Prime k : ℝ)⌋₊ = Nat.nth Nat.Prime k := Nat.floor_natCast _
  rw [hfl] at hpi
  have hk_le_pi : k ≤ Nat.primeCounting (Nat.nth Nat.Prime k) := by
    calc k = Nat.primeCounting' (Nat.nth Nat.Prime k) := (Nat.primeCounting'_nth_eq k).symm
      _ ≤ Nat.primeCounting' (Nat.nth Nat.Prime k + 1) :=
        Nat.monotone_primeCounting' (Nat.le_succ _)
      _ = Nat.primeCounting (Nat.nth Nat.Prime k) := rfl
  have hkp : k ≤ Nat.nth Nat.Prime k := by
    have := Nat.add_two_le_nth_prime k
    omega
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime k : ℝ) := by
    exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)
  have hlogp_pos : 0 < Real.log (Nat.nth Nat.Prime k : ℝ) := Real.log_pos (by linarith)
  have h1 : (k : ℝ) ≤ (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) /
      Real.log (Nat.nth Nat.Prime k : ℝ) :=
    (by exact_mod_cast hk_le_pi : (k : ℝ) ≤ Nat.primeCounting (Nat.nth Nat.Prime k)).trans hpi
  have h2 : (k : ℝ) * Real.log (Nat.nth Nat.Prime k : ℝ) ≤
      (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) := (le_div_iff₀ hlogp_pos).mp h1
  have hlog_le : Real.log (k : ℝ) ≤ Real.log (Nat.nth Nat.Prime k : ℝ) :=
    Real.log_le_log hk_pos (by exact_mod_cast hkp)
  have h3 : (k : ℝ) * Real.log (k : ℝ) ≤ (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) :=
    (mul_le_mul_of_nonneg_left hlog_le hk_pos.le).trans h2
  have hlog4_lt : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have hexp1 : (2.5 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith
  have h4 : (Real.log 4 + 1 / 2) ≤ 4 := by linarith
  have hp_nn : 0 ≤ (Nat.nth Nat.Prime k : ℝ) := by positivity
  linarith [mul_le_mul_of_nonneg_right h4 hp_nn]

private lemma exp_one_lt_three : Real.exp 1 < 3 :=
  lt_trans Real.exp_one_lt_d9 (by norm_num)

private lemma log_thirty_gt_three : 3 < Real.log 30 := by
  rw [← Real.log_exp 3]
  refine Real.log_lt_log (Real.exp_pos 3) ?_
  have hexp3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hexp3]
  have hpow : (Real.exp 1) ^ 3 < 3 ^ 3 := by
    gcongr
    exact exp_one_lt_three
  linarith

private lemma log_log_thirty_gt_one : 1 < Real.log (Real.log 30) := by
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) (lt_trans exp_one_lt_three log_thirty_gt_three)

private lemma log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]

private lemma sum_inv_nth_prime_le :
    ∃ D : ℝ, 0 < D ∧ ∀ r : ℕ, 30 ≤ r →
      ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤ D * Real.log (Real.log r) := by
  obtain ⟨C, hCpos, hC⟩ := nth_prime_lower
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D : ℝ := 4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2)) + C / Real.log 2
  have hDpos : 0 < D := by
    have h2 : 1 < 2 / Real.log 2 := (one_lt_div hlog2_pos).mpr (by linarith [log_two_lt_one])
    have hlog_pos : 0 < Real.log (2 / Real.log 2) := Real.log_pos h2
    positivity
  refine ⟨D, hDpos, fun r hr30 ↦ ?_⟩
  have hr4 : 4 ≤ r := by omega
  have hsplit : Finset.range r = Finset.range 4 ∪ Finset.Ico 4 r := by
    ext i
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range 4) (Finset.Ico 4 r) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    rw [Finset.mem_range] at h1
    rw [Finset.mem_Ico] at h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hhead : ∑ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤ 4 := by
    calc ∑ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ)⁻¹
        ≤ ∑ _ ∈ Finset.range 4, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by
            exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
          exact inv_le_one_of_one_le₀ (by linarith)
      _ = 4 := by simp
  let K := Nat.log 2 r + 1
  have hK4 : 4 ≤ Nat.log 2 r := by
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    omega
  have hK5 : 5 ≤ K := by omega
  have hsub_dyad : Finset.Ico 4 r ⊆
      (Finset.Ico 2 K).biUnion (fun m ↦ Finset.Ico (2 ^ m) (2 ^ (m + 1))) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_biUnion]
    let m := Nat.log 2 i
    refine ⟨m, Finset.mem_Ico.mpr ⟨?_, ?_⟩, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
      omega
    · have hm_le : m ≤ Nat.log 2 r := Nat.log_mono_right hi.2.le
      omega
    · exact Nat.pow_log_le_self 2 (by omega)
    · exact Nat.lt_pow_succ_log_self (by norm_num) i
  have htail_le : ∑ i ∈ Finset.Ico 4 r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
      ∑ m ∈ Finset.Ico 2 K,
        ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ := by
    have hdisj_dyad : (Finset.Ico 2 K : Set ℕ).PairwiseDisjoint
        (fun m ↦ Finset.Ico (2 ^ m) (2 ^ (m + 1))) := by
      intro m₁ _ m₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i hi1 hi2
      rw [Finset.mem_Ico] at hi1 hi2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : 2 ^ (m₁ + 1) ≤ 2 ^ m₂ := Nat.pow_le_pow_right (by norm_num) hlt
        omega
      · have hpow : 2 ^ (m₂ + 1) ≤ 2 ^ m₁ := Nat.pow_le_pow_right (by norm_num) hgt
        omega
    calc ∑ i ∈ Finset.Ico 4 r, (Nat.nth Nat.Prime i : ℝ)⁻¹
        ≤ ∑ i ∈ (Finset.Ico 2 K).biUnion (fun m ↦ Finset.Ico (2 ^ m) (2 ^ (m + 1))),
            (Nat.nth Nat.Prime i : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_dyad fun _ _ _ ↦ by positivity
      _ = ∑ m ∈ Finset.Ico 2 K,
            ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ :=
          Finset.sum_biUnion hdisj_dyad
  have hblock : ∀ m ∈ Finset.Ico 2 K,
      ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
        (C / Real.log 2) * (m : ℝ)⁻¹ := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm2 : 2 ≤ m := hm.1
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have h2m_pos : (0 : ℝ) < (2 ^ m : ℕ) := by positivity
    have hterm : ∀ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)),
        (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤ C / ((2 ^ m : ℝ) * (m * Real.log 2)) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi2 : 2 ≤ i := by
        have : 4 ≤ 2 ^ m := calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
        omega
      have hp_pos : (0 : ℝ) < (Nat.nth Nat.Prime i : ℝ) := by
        exact_mod_cast (Nat.add_two_le_nth_prime i).trans_lt' (by omega)
      have hCi := hC i hi2
      have hi_ge : (2 ^ m : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi.1
      have hlog_ge : (m : ℝ) * Real.log 2 ≤ Real.log (i : ℝ) := by
        have hpow : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := Real.log_pow 2 m
        rw [← hpow]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hi.1)
      have hden_le : (2 ^ m : ℝ) * (m * Real.log 2) ≤ (i : ℝ) * Real.log (i : ℝ) :=
        mul_le_mul hi_ge hlog_ge (by positivity) (by positivity)
      have hmul_pos : 0 < (2 ^ m : ℝ) * (m * Real.log 2) := by positivity
      have hCi' : (2 ^ m : ℝ) * (m * Real.log 2) ≤ C * (Nat.nth Nat.Prime i : ℝ) :=
        hden_le.trans hCi
      rw [inv_eq_one_div, div_le_div_iff₀ hp_pos hmul_pos]
      linarith
    have hsum_b : ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
        ((Finset.Ico (2 ^ m) (2 ^ (m + 1))).card : ℝ) *
          (C / ((2 ^ m : ℝ) * (m * Real.log 2))) := by
      calc ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹
          ≤ ∑ _ ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)),
              (C / ((2 ^ m : ℝ) * (m * Real.log 2))) := Finset.sum_le_sum hterm
        _ = _ := by simp
    have hcard : (Finset.Ico (2 ^ m) (2 ^ (m + 1))).card = 2 ^ m := by
      rw [Nat.card_Ico]
      have hpow2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      rw [hpow2, Nat.add_sub_cancel]
    rw [hcard] at hsum_b
    refine hsum_b.trans_eq ?_
    push_cast
    field_simp
  have hsum_blocks : ∑ m ∈ Finset.Ico 2 K,
      ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
      (C / Real.log 2) * (1 + Real.log K) := by
    calc ∑ m ∈ Finset.Ico 2 K,
          ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹
        ≤ ∑ m ∈ Finset.Ico 2 K, (C / Real.log 2) * (m : ℝ)⁻¹ := Finset.sum_le_sum hblock
      _ = (C / Real.log 2) * ∑ m ∈ Finset.Ico 2 K, (m : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ (C / Real.log 2) * ∑ m ∈ Finset.Icc 1 K, (m : ℝ)⁻¹ := by
          gcongr
          intro m hm
          rw [Finset.mem_Ico] at hm
          rw [Finset.mem_Icc]
          omega
      _ = (C / Real.log 2) * (harmonic K : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          push_cast
          rfl
      _ ≤ (C / Real.log 2) * (1 + Real.log K) := by
          gcongr
          exact harmonic_le_one_add_log K
  have hlogr3 : 3 < Real.log (r : ℝ) :=
    lt_of_lt_of_le log_thirty_gt_three (Real.log_le_log (by norm_num) (by exact_mod_cast hr30))
  have hloglogr1 : 1 < Real.log (Real.log (r : ℝ)) :=
    lt_of_lt_of_le log_log_thirty_gt_one
      (Real.log_le_log (by linarith [log_thirty_gt_three])
        (Real.log_le_log (by norm_num) (by exact_mod_cast hr30)))
  have hK_le : (K : ℝ) ≤ (2 / Real.log 2) * Real.log (r : ℝ) := by
    have hpow_le : (2 : ℝ) ^ (Nat.log 2 r) ≤ (r : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog_pow : (Nat.log 2 r : ℝ) * Real.log 2 ≤ Real.log (r : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpow_le
    have hlogr_div : (Nat.log 2 r : ℝ) ≤ Real.log (r : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlog2_pos).mpr hlog_pow
    have hK4' : (4 : ℝ) ≤ (Nat.log 2 r : ℝ) := by exact_mod_cast hK4
    have hK_real : (K : ℝ) = (Nat.log 2 r : ℝ) + 1 := by push_cast [K]; rfl
    rw [hK_real]
    have : (1 : ℝ) ≤ Real.log (r : ℝ) / Real.log 2 := by linarith
    linarith [show (2 / Real.log 2) * Real.log (r : ℝ) = 2 * (Real.log (r : ℝ) / Real.log 2) by ring]
  have hlogK_le : Real.log (K : ℝ) ≤ Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ)) := by
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    calc Real.log (K : ℝ)
        ≤ Real.log ((2 / Real.log 2) * Real.log (r : ℝ)) := Real.log_le_log hK_pos hK_le
      _ = Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ)) :=
        Real.log_mul (by positivity) (by linarith)
  have hfinal_tail : ∑ i ∈ Finset.Ico 4 r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
      (C / Real.log 2) * (1 + Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ))) := by
    have h1K : 1 + Real.log (K : ℝ) ≤ 1 + Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ)) := by
      linarith
    exact htail_le.trans (hsum_blocks.trans (mul_le_mul_of_nonneg_left h1K (by positivity)))
  calc ∑ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ)⁻¹ +
        ∑ i ∈ Finset.Ico 4 r, (Nat.nth Nat.Prime i : ℝ)⁻¹
      ≤ 4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ))) :=
        add_le_add hhead hfinal_tail
    _ = (4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2))) * 1 +
          (C / Real.log 2) * Real.log (Real.log (r : ℝ)) := by ring
    _ ≤ (4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2))) * Real.log (Real.log (r : ℝ)) +
          (C / Real.log 2) * Real.log (Real.log (r : ℝ)) := by
        have hpos_coef : 0 ≤ 4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2)) := by
          have h2 : 1 < 2 / Real.log 2 := (one_lt_div hlog2_pos).mpr (by linarith [log_two_lt_one])
          have : 0 < Real.log (2 / Real.log 2) := Real.log_pos h2
          positivity
        have := mul_le_mul_of_nonneg_left hloglogr1.le hpos_coef
        linarith
    _ = D * Real.log (Real.log (r : ℝ)) := by ring

private lemma prod_nth_prime_lower :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℕ,
      (Real.log ((r : ℝ) + 30) ^ M)⁻¹ ≤
        ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) := by
  obtain ⟨D, _, hD⟩ := sum_inv_nth_prime_le
  let M : ℕ := max (⌈2 * D⌉₊) 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have h2DM : 2 * D ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_left (⌈2 * D⌉₊) 1)
  refine ⟨M, hM1, fun r ↦ ?_⟩
  let R := max r 30
  have hrR : r ≤ R := le_max_left _ _
  have hR30 : 30 ≤ R := le_max_right _ _
  have hRr30 : (R : ℝ) ≤ (r : ℝ) + 30 := by exact_mod_cast (by omega : R ≤ r + 30)
  have hlogR3 : 3 < Real.log (R : ℝ) :=
    lt_of_lt_of_le log_thirty_gt_three (Real.log_le_log (by norm_num) (by exact_mod_cast hR30))
  have hloglogR_pos : 0 < Real.log (Real.log (R : ℝ)) := Real.log_pos (by linarith)
  have hsum_le : 2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
      (M : ℝ) * Real.log (Real.log ((r : ℝ) + 30)) := by
    have h1 : ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
        ∑ i ∈ Finset.range R, (Nat.nth Nat.Prime i : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrR) fun _ _ _ ↦ by positivity
    have h2 : ∑ i ∈ Finset.range R, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤ D * Real.log (Real.log (R : ℝ)) :=
      hD R hR30
    have h3 : Real.log (Real.log (R : ℝ)) ≤ Real.log (Real.log ((r : ℝ) + 30)) :=
      Real.log_le_log (by linarith) (Real.log_le_log (by exact_mod_cast (by omega : 0 < R)) hRr30)
    calc 2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹
        ≤ 2 * (D * Real.log (Real.log (R : ℝ))) := by linarith
      _ = (2 * D) * Real.log (Real.log (R : ℝ)) := by ring
      _ ≤ (M : ℝ) * Real.log (Real.log (R : ℝ)) :=
          mul_le_mul_of_nonneg_right h2DM hloglogR_pos.le
      _ ≤ (M : ℝ) * Real.log (Real.log ((r : ℝ) + 30)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hlogr30_pos : 0 < Real.log ((r : ℝ) + 30) := by
    refine lt_trans (by norm_num : (0 : ℝ) < 3) ?_
    refine lt_of_lt_of_le log_thirty_gt_three (Real.log_le_log (by norm_num) ?_)
    linarith [show (0 : ℝ) ≤ r by positivity]
  have hexp_pow : Real.exp (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹) ≤
      Real.log ((r : ℝ) + 30) ^ M := by
    calc Real.exp (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹)
        ≤ Real.exp ((M : ℝ) * Real.log (Real.log ((r : ℝ) + 30))) := Real.exp_le_exp.mpr hsum_le
      _ = Real.exp (Real.log (Real.log ((r : ℝ) + 30) ^ M)) := by rw [Real.log_pow]
      _ = Real.log ((r : ℝ) + 30) ^ M := Real.exp_log (pow_pos hlogr30_pos M)
  have hprod_exp : Real.exp (- (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹)) ≤
      ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) := by
    have heq : - (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹) =
        ∑ i ∈ Finset.range r, - (2 / (Nat.nth Nat.Prime i : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [heq, Real.exp_sum]
    refine Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le) fun i _ ↦ ?_
    have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by
      exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
    exact exp_neg_le_one_sub_inv hp2
  have hinv_exp : (Real.log ((r : ℝ) + 30) ^ M)⁻¹ ≤
      Real.exp (- (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹)) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hexp_pow
  exact hinv_exp.trans hprod_exp

private lemma totient_ratio_eq {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / (n.totient : ℝ) = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
  have hq := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
  push_cast at hq
  have hn_r : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
    simpa only [one_div] using hq
  rw [hq', div_mul_eq_div_div, div_self hn_r.ne', one_div, Finset.prod_inv_distrib]

private lemma orderEmb_ge_add_two {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∀ i : Fin S.card, i.1 + 2 ≤ S.orderEmbOfFin rfl i := by
  rintro ⟨i, hi⟩
  induction i with
  | zero =>
    exact (hS _ (Finset.orderEmbOfFin_mem S rfl ⟨0, hi⟩)).two_le
  | succ i ih =>
    have hi0 : i < S.card := Nat.lt_of_succ_lt hi
    have h1 := ih hi0
    have h2 : S.orderEmbOfFin rfl ⟨i, hi0⟩ < S.orderEmbOfFin rfl ⟨i + 1, hi⟩ :=
      (S.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
    dsimp only at h1 ⊢
    omega

private lemma prod_succ_div_eq (k : ℕ) :
    ∏ i : Fin k, ((i.1 + 2 : ℝ) / (i.1 + 1 : ℝ)) = (k : ℝ) + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    push_cast
    ring

private lemma totient_ratio_le_log {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / (n.totient : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
  have hn1 : 1 ≤ n := by omega
  rw [totient_ratio_eq hn1]
  let k := n.primeFactors.card
  have heq : ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))⁻¹ =
      ∏ i : Fin k, (1 - (1 : ℝ) / (n.primeFactors.orderEmbOfFin rfl i : ℝ))⁻¹ := by
    refine (Finset.prod_bij (fun i _ ↦ n.primeFactors.orderEmbOfFin rfl i)
      (fun i _ ↦ Finset.orderEmbOfFin_mem _ _ i)
      (fun i _ j _ hij ↦ (n.primeFactors.orderEmbOfFin rfl).injective hij)
      (fun p hp ↦ ⟨(n.primeFactors.orderIsoOfFin rfl).symm ⟨p, hp⟩, Finset.mem_univ _, by
        simp [Finset.orderEmbOfFin]⟩) (fun _ _ ↦ rfl)).symm
  rw [heq]
  have hle_prod : ∏ i : Fin k, (1 - (1 : ℝ) / (n.primeFactors.orderEmbOfFin rfl i : ℝ))⁻¹ ≤
      ∏ i : Fin k, ((i.1 + 2 : ℝ) / (i.1 + 1 : ℝ)) := by
    refine Finset.prod_le_prod (fun i _ ↦ ?_) fun i _ ↦ ?_
    · have hp2 : (2 : ℝ) ≤ n.primeFactors.orderEmbOfFin rfl i := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ _ i)).two_le
      have hpos : 0 < 1 - (1 : ℝ) / (n.primeFactors.orderEmbOfFin rfl i : ℝ) := by
        rw [sub_pos, div_lt_one (by linarith)]
        linarith
      exact (inv_pos.mpr hpos).le
    · have hge : (i.1 + 2 : ℝ) ≤ (n.primeFactors.orderEmbOfFin rfl i : ℝ) := by
        exact_mod_cast orderEmb_ge_add_two (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) i
      have hi1 : (0 : ℝ) < (i.1 : ℝ) + 1 := by positivity
      have hi2 : (0 : ℝ) < (i.1 : ℝ) + 2 := by positivity
      have hsub_eq : 1 - (1 : ℝ) / ((i.1 : ℝ) + 2) = ((i.1 : ℝ) + 1) / ((i.1 : ℝ) + 2) := by
        field_simp
        ring
      have hinv_eq : ((1 - (1 : ℝ) / ((i.1 : ℝ) + 2))⁻¹) = ((i.1 + 2 : ℝ) / (i.1 + 1 : ℝ)) := by
        rw [hsub_eq, inv_div]
      rw [← hinv_eq]
      have hpos : 0 < 1 - (1 : ℝ) / ((i.1 : ℝ) + 2) := by rw [hsub_eq]; positivity
      refine inv_anti₀ hpos ?_
      gcongr
  have h2pow : 2 ^ k ≤ n := by
    calc 2 ^ k = ∏ _p ∈ n.primeFactors, 2 := by simp [k]
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        refine Finset.prod_le_prod' fun p hp ↦ ?_
        exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ n := Nat.le_of_dvd hn1 (Nat.prod_primeFactors_dvd n)
  have hk_log : (k : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [le_div_iff₀ hlog2_pos, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h2pow)
  calc ∏ i : Fin k, (1 - (1 : ℝ) / (n.primeFactors.orderEmbOfFin rfl i : ℝ))⁻¹
      ≤ ∏ i : Fin k, ((i.1 + 2 : ℝ) / (i.1 + 1 : ℝ)) := hle_prod
    _ = (k : ℝ) + 1 := prod_succ_div_eq k
    _ ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by linarith

private lemma tau_mul_totient_ge {n r : ℕ} (hn : 1 ≤ n) :
    ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) ≤
      ((n : ℝ) / (n.totient : ℝ)) *
        ∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
          (1 - (1 : ℝ) / (p : ℝ)) := by
  let P_r := (Finset.range r).image (Nat.nth Nat.Prime)
  let S := n.primeFactors ∪ P_r
  have hdisj : Disjoint n.primeFactors (P_r \ n.primeFactors) := disjoint_sdiff_self_right
  have hunion : n.primeFactors ∪ (P_r \ n.primeFactors) = S := by
    ext x
    simp [S]
  have hsplit : ∏ p ∈ S, (1 - (1 : ℝ) / (p : ℝ)) =
      (∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) *
        (∏ p ∈ P_r \ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) := by
    rw [← hunion, Finset.prod_union hdisj]
  have hprod_ne : (∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hlt : (1 : ℝ) / p < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  rw [totient_ratio_eq hn, hsplit, ← mul_assoc, Finset.prod_inv_distrib,
    inv_mul_cancel₀ hprod_ne, one_mul]
  have hPr_eq : ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) =
      ∏ p ∈ P_r, (1 - (1 : ℝ) / (p : ℝ)) := by
    dsimp only [P_r]
    symm
    rw [Finset.prod_image]
    intro i _ j _ hij
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
  rw [hPr_eq]
  have hsub : P_r \ n.primeFactors ⊆ P_r := Finset.sdiff_subset
  rw [← Finset.prod_sdiff hsub]
  have hle1 : ∏ p ∈ P_r \ (P_r \ n.primeFactors), (1 - (1 : ℝ) / (p : ℝ)) ≤ 1 := by
    refine Finset.prod_le_one (fun p hp ↦ ?_) fun p _ ↦ ?_
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hp).1
      have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by
        exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
      have : (1 : ℝ) / Nat.nth Nat.Prime i ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      linarith
    · exact sub_le_self 1 (by positivity)
  have hnn : 0 ≤ ∏ p ∈ P_r \ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
    refine Finset.prod_nonneg fun p hp ↦ ?_
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.sdiff_subset hp)
    have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by
      exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
    have : (1 : ℝ) / Nat.nth Nat.Prime i ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hle1 hnn

private lemma graham_interval (a b : ℕ) (U W : Finset ℕ) (hab : a ≤ b)
    (hI : ∀ t ∈ Finset.Icc a b, t ∈ subsetSums (U : Set ℕ))
    (hdisj : Disjoint W U)
    (hW : ∀ x ∈ W, 1 ≤ x ∧ x ≤ b - a + 1) :
    ∀ t ∈ Finset.Icc a (b + ∑ x ∈ W, x), t ∈ subsetSums ((U ∪ W : Finset ℕ) : Set ℕ) := by
  classical
  induction W using Finset.induction with
  | empty =>
    simpa using hI
  | @insert x W hxW ih =>
    have hxU : x ∉ U := (Finset.disjoint_left.mp hdisj) (Finset.mem_insert_self x W)
    have hdisj' : Disjoint W U := Disjoint.mono_left (Finset.subset_insert x W) hdisj
    have hW' : ∀ w ∈ W, 1 ≤ w ∧ w ≤ b - a + 1 := fun w hw ↦ hW w (Finset.mem_insert_of_mem hw)
    have ih' := ih hdisj' hW'
    have hx_bounds := hW x (Finset.mem_insert_self x W)
    rw [Finset.sum_insert hxW]
    intro t ht
    rw [Finset.mem_Icc] at ht
    by_cases hle : t ≤ b + ∑ w ∈ W, w
    · have ht' : t ∈ Finset.Icc a (b + ∑ w ∈ W, w) := Finset.mem_Icc.mpr ⟨ht.1, hle⟩
      have hsub : ((U ∪ W : Finset ℕ) : Set ℕ) ⊆ ((U ∪ insert x W : Finset ℕ) : Set ℕ) := by
        intro z hz
        simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_insert] at hz ⊢
        tauto
      exact subsetSums_mono hsub (ih' t ht')
    · have hge : b + ∑ w ∈ W, w < t := not_le.mp hle
      have hsum_nn : b ≤ b + ∑ w ∈ W, w := Nat.le_add_right _ _
      have htx_ge : a ≤ t - x := by omega
      have htx_le : t - x ≤ b + ∑ w ∈ W, w := by omega
      obtain ⟨B, hBU, hBsum⟩ := ih' (t - x) (Finset.mem_Icc.mpr ⟨htx_ge, htx_le⟩)
      have hxB : x ∉ B := by
        intro hxmem
        have := hBU hxmem
        simp only [Finset.mem_coe, Finset.mem_union] at this
        rcases this with h | h <;> contradiction
      refine ⟨insert x B, ?_, ?_⟩
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_insert] at hz ⊢
        rcases hz with hzx | hzB
        · rw [hzx]
          exact Finset.mem_coe.mpr (Finset.mem_union_right U (Finset.mem_insert_self x W))
        · have hzUW := hBU hzB
          simp only [Finset.mem_coe, Finset.mem_union] at hzUW ⊢
          rcases hzUW with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_insert_of_mem h)
      · rw [Finset.sum_insert hxB, ← hBsum]
        omega

private lemma diversity_extract_aux (Q₀ : Finset ℕ) (y k : ℕ) (hy : 1 ≤ y)
    (hQ0_range : ∀ x ∈ Q₀, y ≤ x ∧ x < 2 * y)
    (hQ0_card : (Nat.log 2 (2 * y) + 1) * k + 1 ≤ Q₀.card) :
    ∀ t s v : ℕ, ∀ Q : Finset ℕ, t = Nat.log 2 (2 * y) + 1 - s →
      s ≤ Nat.log 2 (2 * y) + 1 → 1 ≤ v → 2 ^ s ≤ v →
      Q₀.card ≤ Q.card + s * k → Q.card ≤ Q₀.card → (∀ x ∈ Q, v * x ∈ Q₀) →
      ∃ v' : ℕ, ∃ Q' : Finset ℕ, 1 ≤ v' ∧
        Q₀.card ≤ Q'.card + (Nat.log 2 (2 * y) + 1) * k ∧ Q'.card ≤ Q₀.card ∧
        (∀ x ∈ Q', v' * x ∈ Q₀) ∧
        ∀ d : ℕ, 2 ≤ d → k ≤ (Q'.filter (fun x ↦ ¬ d ∣ x)).card := by
  intro t
  induction t with
  | zero =>
    intro s v Q ht hs hv h2s hcard_lo hcard_hi hmem
    exfalso
    have hsM : s = Nat.log 2 (2 * y) + 1 := by omega
    have hQpos : 1 ≤ Q.card := by
      have : s * k ≤ (Nat.log 2 (2 * y) + 1) * k := Nat.mul_le_mul_right k hs
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hQpos
    obtain ⟨hlo, hhi⟩ := hQ0_range (v * x) (hmem x hx)
    have hx1 : 1 ≤ x := by nlinarith
    have hv_lt : v < 2 * y := by nlinarith
    have hpow : 2 * y < 2 ^ (Nat.log 2 (2 * y) + 1) := Nat.lt_pow_succ_log_self (by norm_num) (2 * y)
    rw [← hsM] at hpow
    omega
  | succ t ih =>
    intro s v Q ht hs hv h2s hcard_lo hcard_hi hmem
    by_cases hdiv : ∀ d : ℕ, 2 ≤ d → k ≤ (Q.filter (fun x ↦ ¬ d ∣ x)).card
    · refine ⟨v, Q, hv, ?_, hcard_hi, hmem, hdiv⟩
      have : s * k ≤ (Nat.log 2 (2 * y) + 1) * k := Nat.mul_le_mul_right k hs
      omega
    · push_neg at hdiv
      obtain ⟨d, hd2, hd_lt⟩ := hdiv
      let Q_keep := Q.filter (fun x ↦ d ∣ x)
      let Q_next := Q_keep.image (fun x ↦ x / d)
      have hinj : Set.InjOn (fun x ↦ x / d) (Q_keep : Set ℕ) := by
        intro a ha b hb hab
        dsimp only at hab
        have ha_dvd : d ∣ a := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
        have hb_dvd : d ∣ b := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
        calc a = d * (a / d) := (Nat.mul_div_cancel' ha_dvd).symm
          _ = d * (b / d) := by rw [hab]
          _ = b := Nat.mul_div_cancel' hb_dvd
      have hcard_eq : Q_next.card = Q_keep.card := Finset.card_image_of_injOn hinj
      have hcard_split : Q_keep.card + (Q.filter (fun x ↦ ¬ d ∣ x)).card = Q.card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext x
          simp only [Q_keep, Finset.mem_union, Finset.mem_filter]
          tauto
        · rw [Finset.disjoint_left]
          intro x hx1 hx2
          exact (Finset.mem_filter.mp hx2).2 (Finset.mem_filter.mp hx1).2
      have hs_lt : s < Nat.log 2 (2 * y) + 1 := by omega
      have hcard_next_lo : Q₀.card ≤ Q_next.card + (s + 1) * k := by
        rw [hcard_eq]
        have : s * k + k = (s + 1) * k := by ring
        omega
      have hcard_next_hi : Q_next.card ≤ Q₀.card := by
        rw [hcard_eq]
        exact (Finset.card_filter_le _ _).trans hcard_hi
      have h2s_next : 2 ^ (s + 1) ≤ v * d := by
        rw [pow_succ]
        exact Nat.mul_le_mul h2s hd2
      have hmem_next : ∀ x ∈ Q_next, v * d * x ∈ Q₀ := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        have haQ : a ∈ Q := (Finset.mem_filter.mp ha).1
        have ha_dvd : d ∣ a := (Finset.mem_filter.mp ha).2
        rw [mul_assoc, Nat.mul_div_cancel' ha_dvd]
        exact hmem a haQ
      exact ih (s + 1) (v * d) Q_next (by omega) (by omega) (by nlinarith) h2s_next
        hcard_next_lo hcard_next_hi hmem_next

private lemma diversity_extract (Q₀ : Finset ℕ) (y k : ℕ) (hy : 1 ≤ y)
    (hQ0_range : ∀ x ∈ Q₀, y ≤ x ∧ x < 2 * y)
    (hQ0_card : (Nat.log 2 (2 * y) + 1) * k + 1 ≤ Q₀.card) :
    ∃ v : ℕ, ∃ Q : Finset ℕ, 1 ≤ v ∧
      Q₀.card ≤ Q.card + (Nat.log 2 (2 * y) + 1) * k ∧ Q.card ≤ Q₀.card ∧
      (∀ x ∈ Q, v * x ∈ Q₀) ∧
      ∀ d : ℕ, 2 ≤ d → k ≤ (Q.filter (fun x ↦ ¬ d ∣ x)).card :=
  diversity_extract_aux Q₀ y k hy hQ0_range hQ0_card (Nat.log 2 (2 * y) + 1) 0 1 Q₀
    (by omega) (by omega) le_rfl (by simp) (by simp) le_rfl (fun x hx ↦ by simpa using hx)

private lemma div_by_divisors {n r y w : ℕ} {T' : Finset ℕ}
    (hn : 2 ≤ n) (hr2 : 2 ≤ r) (hrn : r ≤ n) (hy1 : 1 ≤ y) (hyn : 2 * y < n)
    (hpr : (r : ℝ) * Real.log (r : ℝ) / 4 ≤ (Nat.nth Nat.Prime r : ℝ))
    (hT'_sub : ∀ m ∈ T', m ∈ Finset.Ico y (2 * y) ∧ ∃ u q : ℕ, m = q * u ∧ u ∣ n ∧
      (u : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) ∧
      ∀ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime), ¬ p ∣ q)
    (hw_dvd : ∀ m ∈ T', w ∣ m)
    (hH1_up : ∀ x : ℕ, (n : ℝ) ^ (1 / 4 : ℝ) ≤ (x : ℝ) →
      (((Finset.Ico x (2 * x)).filter (fun m ↦ ∃ u q : ℕ, m = q * u ∧ u ∣ n ∧
        (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) ∧
        ∀ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime), ¬ p ∣ q)).card : ℝ) ≤
        8 * ((n : ℝ) / (n.totient : ℝ)) *
          (∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
            (1 - (1 : ℝ) / p)) * (x : ℝ))
    (hsmall_n4 : (n : ℝ) ^ (1 / 4 : ℝ) + 2 ≤
      64 * ((n : ℝ) / (n.totient : ℝ)) *
        (∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
          (1 - (1 : ℝ) / p)) * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)))
    (hsmall_y : 32 * ((n : ℝ) / (n.totient : ℝ)) *
        (∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
          (1 - (1 : ℝ) / p)) * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) + 2 ≤
      64 * ((n : ℝ) / (n.totient : ℝ)) *
        (∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
          (1 - (1 : ℝ) / p)) * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)))
    (hT'_card : 64 * ((n : ℝ) / (n.totient : ℝ)) *
        (∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
          (1 - (1 : ℝ) / p)) * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) < (T'.card : ℝ)) :
    w ∣ n ∧ (w : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) := by
  let S := n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime)
  let tau := ∏ p ∈ S, (1 - (1 : ℝ) / p)
  have hr : 1 ≤ r := by omega
  have hlogr_pos : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have htot_pos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have htau_nn : 0 ≤ tau := by
    refine Finset.prod_nonneg fun p hp ↦ ?_
    have hp2 : (2 : ℝ) ≤ p := by
      rcases Finset.mem_union.mp hp with hp_n | hp_r
      · exact_mod_cast (Nat.prime_of_mem_primeFactors hp_n).two_le
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp_r
        exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
    have : (1 : ℝ) / p ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hT'_pos : 0 < T'.card := by
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
    have hnn : 0 ≤ 64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) := by
      positivity
    have : (0 : ℝ) < T'.card := lt_of_le_of_lt hnn hT'_card
    exact_mod_cast this
  obtain ⟨m0, hm0⟩ := Finset.card_pos.mp hT'_pos
  have hw_pos : 0 < w := by
    have hm0_pos : 0 < m0 := by
      have := (Finset.mem_Ico.mp (hT'_sub m0 hm0).1).1
      omega
    exact Nat.pos_of_dvd_of_pos (hw_dvd m0 hm0) hm0_pos
  by_contra hbad
  have hexp_p : ∃ p ∈ w.primeFactors, p ∉ S := by
    by_contra hall
    push_neg at hall
    obtain ⟨_, u, q, hm0_eq, hu_dvd, hu_le, hq_cop⟩ := hT'_sub m0 hm0
    have hcop_wq : Nat.Coprime w q := by
      refine Nat.coprime_of_dvd fun p hp hpw hpq ↦ ?_
      have hp_fac : p ∈ w.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpw, hw_pos.ne'⟩
      exact hq_cop p (hall p hp_fac) hpq
    have hwm : w ∣ q * u := hm0_eq ▸ hw_dvd m0 hm0
    have hwu : w ∣ u := hcop_wq.dvd_of_dvd_mul_left hwm
    have hwn : w ∣ n := hwu.trans hu_dvd
    have hu_pos : 0 < u := Nat.pos_of_dvd_of_pos hu_dvd (by omega)
    have hw_le_u : (w : ℝ) ≤ (u : ℝ) := by exact_mod_cast Nat.le_of_dvd hu_pos hwu
    exact hbad ⟨hwn, hw_le_u.trans hu_le⟩
  obtain ⟨p, hp_mem, hp_notS⟩ := hexp_p
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp_dvd_w : p ∣ w := Nat.dvd_of_mem_primeFactors hp_mem
  have hp_ge_nth : Nat.nth Nat.Prime r ≤ p := by
    by_contra hlt
    have hlt' : p < Nat.nth Nat.Prime r := not_le.mp hlt
    have hcnt : Nat.count Nat.Prime p < r := by
      by_contra hge
      have hge' : r ≤ Nat.count Nat.Prime p := not_lt.mp hge
      have hle_p : Nat.nth Nat.Prime r ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime p) :=
        Nat.nth_monotone Nat.infinite_setOfPred_prime hge'
      rw [Nat.nth_count hp_prime] at hle_p
      omega
    have : p ∈ (Finset.range r).image (Nat.nth Nat.Prime) :=
      Finset.mem_image.mpr ⟨Nat.count Nat.Prime p, Finset.mem_range.mpr hcnt, Nat.nth_count hp_prime⟩
    exact hp_notS (Finset.mem_union_right _ this)
  let T_div := T'.image (fun m ↦ m / p)
  have hT_inj : Set.InjOn (fun m ↦ m / p) (T' : Set ℕ) := by
    intro a ha b hb hab
    dsimp only at hab
    have hpa : p ∣ a := hp_dvd_w.trans (hw_dvd a ha)
    have hpb : p ∣ b := hp_dvd_w.trans (hw_dvd b hb)
    calc a = p * (a / p) := (Nat.mul_div_cancel' hpa).symm
      _ = p * (b / p) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hpb
  have hT_div_card : T_div.card = T'.card := Finset.card_image_of_injOn hT_inj
  have hT_div_sub : T_div ⊆ Finset.Ico (y / p) (2 * (y / p) + 2) := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    have hm_ico := Finset.mem_Ico.mp (hT'_sub m hm).1
    have hpm : p ∣ m := hp_dvd_w.trans (hw_dvd m hm)
    have h1 : y / p ≤ m / p := Nat.div_le_div_right hm_ico.1
    have h2 : m / p < 2 * (y / p) + 2 := by
      have hmul : p * (m / p) = m := Nat.mul_div_cancel' hpm
      have hp_pos : 0 < p := hp_prime.pos
      have hdiv_lt : 2 * y < p * (2 * (y / p) + 2) := by
        have hlt_y : y < p * (y / p + 1) := Nat.lt_mul_div_succ y hp_pos
        linarith
      nlinarith
    exact Finset.mem_Ico.mpr ⟨h1, h2⟩
  have hT_div_form : ∀ t ∈ T_div, ∃ u q' : ℕ, t = q' * u ∧ u ∣ n ∧
      (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ s ∈ S, ¬ s ∣ q' := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨_, u, q, hm_eq, hu_dvd, hu_le, hq_cop⟩ := hT'_sub m hm
    have hpm : p ∣ m := hp_dvd_w.trans (hw_dvd m hm)
    have hpn : ¬ p ∣ n := fun h ↦ hp_notS (Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp_prime, h, by omega⟩))
    have hpu : ¬ p ∣ u := fun h ↦ hpn (h.trans hu_dvd)
    have hpq : p ∣ q := (hp_prime.dvd_mul.mp (hm_eq ▸ hpm)).resolve_right hpu
    refine ⟨u, q / p, ?_, hu_dvd, ?_, ?_⟩
    · have h1 : m = p * ((q / p) * u) := by
        calc m = q * u := hm_eq
          _ = (p * (q / p)) * u := by rw [Nat.mul_div_cancel' hpq]
          _ = p * ((q / p) * u) := by ring
      calc m / p = (p * ((q / p) * u)) / p := by rw [h1]
        _ = (q / p) * u := Nat.mul_div_right _ hp_prime.pos
    · have hyn' : (y : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : y ≤ n)
      exact hu_le.trans (Real.rpow_le_rpow (by positivity) hyn' (by norm_num))
    · intro s hs hsd
      exact hq_cop s hs (hsd.trans (Nat.div_dvd_of_dvd hpq))
  by_cases hlt : ((y / p : ℕ) : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ)
  · have hcard1 : (T_div.card : ℝ) ≤ (Finset.Ico (y / p) (2 * (y / p) + 2)).card :=
      by exact_mod_cast Finset.card_le_card hT_div_sub
    have hcard2 : (Finset.Ico (y / p) (2 * (y / p) + 2)).card = y / p + 2 := by
      rw [Nat.card_Ico]
      omega
    rw [hcard2] at hcard1
    push_cast at hcard1
    have hcard3 : (T'.card : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) + 2 := by
      rw [← hT_div_card]
      linarith
    linarith
  · have hge : (n : ℝ) ^ (1 / 4 : ℝ) ≤ ((y / p : ℕ) : ℝ) := not_lt.mp hlt
    let Yp := (Finset.Ico (y / p) (2 * (y / p))).filter (fun m ↦ ∃ u q : ℕ, m = q * u ∧
      u ∣ n ∧ (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ s ∈ S, ¬ s ∣ q)
    have hsub_Yp : T_div ⊆ Yp ∪ {2 * (y / p), 2 * (y / p) + 1} := by
      intro t ht
      have ht_ico := Finset.mem_Ico.mp (hT_div_sub ht)
      by_cases ht2 : t < 2 * (y / p)
      · refine Finset.mem_union_left _ ?_
        dsimp only [Yp]
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ht_ico.1, ht2⟩, hT_div_form t ht⟩
      · exact Finset.mem_union_right _ (by simp; omega)
    have hcard_Yp : (T_div.card : ℝ) ≤ (Yp.card : ℝ) + 2 := by
      have h1 : T_div.card ≤ Yp.card + ({2 * (y / p), 2 * (y / p) + 1} : Finset ℕ).card :=
        (Finset.card_le_card hsub_Yp).trans (Finset.card_union_le _ _)
      have h2 : ({2 * (y / p), 2 * (y / p) + 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      have h3 : T_div.card ≤ Yp.card + 2 := h1.trans (Nat.add_le_add_left h2 _)
      exact_mod_cast h3
    have hup := hH1_up (y / p) hge
    have hp_real : (r : ℝ) * Real.log (r : ℝ) / 4 ≤ (p : ℝ) :=
      hpr.trans (by exact_mod_cast hp_ge_nth)
    have hyp_le : ((y / p : ℕ) : ℝ) ≤ (y : ℝ) / (p : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hp_prime.pos)]
      exact_mod_cast Nat.div_mul_le_self y p
    have hden_pos : 0 < (r : ℝ) * Real.log (r : ℝ) / 4 := by
      have : (0 : ℝ) < r := by exact_mod_cast hr
      positivity
    have hdiv_le : (y : ℝ) / (p : ℝ) ≤ (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ) / 4) :=
      div_le_div_of_nonneg_left (by positivity) hden_pos hp_real
    have hcoef_nn : 0 ≤ 8 * ((n : ℝ) / (n.totient : ℝ)) * tau := by positivity
    have hup2 : (Yp.card : ℝ) ≤
        32 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) := by
      calc (Yp.card : ℝ) ≤ 8 * ((n : ℝ) / (n.totient : ℝ)) * tau * ((y / p : ℕ) : ℝ) := hup
        _ ≤ 8 * ((n : ℝ) / (n.totient : ℝ)) * tau * ((y : ℝ) / ((r : ℝ) * Real.log (r : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (hyp_le.trans hdiv_le) hcoef_nn
        _ = 32 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) := by
          ring
    rw [hT_div_card] at hcard_Yp
    linarith

private lemma div_loss_le {n y r k M₁ ℓ : ℕ} {tau : ℝ}
    (hn1_pos : 1 ≤ n) (hy1 : 1 ≤ y) (hr1 : 1 ≤ r)
    (hlog1 : 1 < Real.log (n : ℝ)) (hy35 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (y : ℝ))
    (hk_le : (k : ℝ) ≤ (y : ℝ) ^ (1 / 4 : ℝ) + 1)
    (hlog2y_le : (Nat.log 2 (2 * y) + 1 : ℝ) ≤ 2 * Real.log (n : ℝ) / Real.log 2)
    (hpoly_n : 2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) * Real.log (n : ℝ) ^ (M₁ + 2) ≤
      (n : ℝ) ^ (1 / 20 : ℝ))
    (hntau_ge : ((2 * Real.log (n : ℝ)) ^ M₁)⁻¹ ≤ ((n : ℝ) / (n.totient : ℝ)) * tau)
    (hy_r_ge_sqrt : (y : ℝ) ^ (1 / 2 : ℝ) ≤ (y : ℝ) / (r : ℝ)) :
    ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1 ≤
      (1 / 40 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1_pos
  have hy_pos : (0 : ℝ) < y := by exact_mod_cast hy1
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hntau_nn : 0 ≤ ((n : ℝ) / (n.totient : ℝ)) * tau := le_trans (by positivity) hntau_ge
  have hy4_le : (y : ℝ) ^ (1 / 4 : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ) := by
    have : (y : ℝ) ^ (1 / 2 : ℝ) = (y : ℝ) ^ (1 / 4 : ℝ) * (y : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hy_pos]
      norm_num
    have hy4_ge : (n : ℝ) ^ (3 / 20 : ℝ) ≤ (y : ℝ) ^ (1 / 4 : ℝ) := by
      calc (n : ℝ) ^ (3 / 20 : ℝ) = ((n : ℝ) ^ (3 / 5 : ℝ)) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]
            norm_num
        _ ≤ (y : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hy35 (by norm_num)
    rw [le_div_iff₀ (by positivity)]
    calc (y : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 20 : ℝ)
        ≤ (y : ℝ) ^ (1 / 4 : ℝ) * (y : ℝ) ^ (1 / 4 : ℝ) := by gcongr
      _ = (y : ℝ) ^ (1 / 2 : ℝ) := this.symm
  have h1_le : (1 : ℝ) ≤ (y : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hy1) (by norm_num)
  have hk_le' : (k : ℝ) ≤ 2 * ((y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ)) := by
    linarith
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    rw [← Real.log_exp (1 / 2)]
    have : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have hexp_sq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h4 : Real.exp (1 / 2 : ℝ) ^ 2 ≤ 4 := by linarith [exp_one_lt_three]
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) this
  have hlog2y_le' : ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    push_cast
    have : 2 * Real.log (n : ℝ) / Real.log 2 ≤ 4 * Real.log (n : ℝ) := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num))]
      nlinarith
    exact hlog2y_le.trans this
  have hprod_le : ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1 ≤
      9 * Real.log (n : ℝ) * ((y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ)) := by
    have h1_small : (1 : ℝ) ≤ Real.log (n : ℝ) * ((y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ)) := by
      have : (1 : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ) := by
        rw [le_div_iff₀ (by positivity), one_mul]
        have : (n : ℝ) ^ (3 / 20 : ℝ) ≤ (y : ℝ) ^ (1 / 4 : ℝ) := by
          calc (n : ℝ) ^ (3 / 20 : ℝ) = ((n : ℝ) ^ (3 / 5 : ℝ)) ^ (1 / 4 : ℝ) := by
                rw [← Real.rpow_mul (by positivity)]
                norm_num
            _ ≤ (y : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hy35 (by norm_num)
        have : (y : ℝ) ^ (1 / 4 : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hy1) (by norm_num)
        linarith
      nlinarith
    have hmul : ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) ≤
        (4 * Real.log (n : ℝ)) * (2 * ((y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ))) :=
      mul_le_mul hlog2y_le' hk_le' (by positivity) (by positivity)
    linarith
  have hpoly_bound : 360 * Real.log (n : ℝ) * (2 * Real.log (n : ℝ)) ^ M₁ ≤ (n : ℝ) ^ (3 / 20 : ℝ) := by
    have h1 : (2 * Real.log (n : ℝ)) ^ M₁ = (2 : ℝ) ^ M₁ * Real.log (n : ℝ) ^ M₁ := mul_pow _ _ _
    have h2 : 360 * Real.log (n : ℝ) * ((2 : ℝ) ^ M₁ * Real.log (n : ℝ) ^ M₁) ≤
        2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) * Real.log (n : ℝ) ^ (M₁ + 2) := by
      have h360 : (360 : ℝ) ≤ 2 ^ 10 * ((ℓ : ℝ) ^ 2 + 1) := by
        have : (0 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by positivity
        nlinarith
      have hlog_pow : Real.log (n : ℝ) * Real.log (n : ℝ) ^ M₁ ≤ Real.log (n : ℝ) ^ (M₁ + 2) := by
        have : Real.log (n : ℝ) ^ (M₁ + 2) = Real.log (n : ℝ) ^ M₁ * Real.log (n : ℝ) ^ 2 := by ring
        rw [this]
        have : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
        nlinarith [pow_nonneg hlog_pos.le M₁]
      calc 360 * Real.log (n : ℝ) * ((2 : ℝ) ^ M₁ * Real.log (n : ℝ) ^ M₁)
          = (360 * (2 : ℝ) ^ M₁) * (Real.log (n : ℝ) * Real.log (n : ℝ) ^ M₁) := by ring
        _ ≤ (2 ^ 10 * ((ℓ : ℝ) ^ 2 + 1) * (2 : ℝ) ^ M₁) * Real.log (n : ℝ) ^ (M₁ + 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h360 (by positivity)) hlog_pow (by positivity) (by positivity)
        _ = 2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) * Real.log (n : ℝ) ^ (M₁ + 2) := by
            rw [pow_add]
            ring
    have h3 : (n : ℝ) ^ (1 / 20 : ℝ) ≤ (n : ℝ) ^ (3 / 20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1_pos) (by norm_num)
    rw [h1]
    exact h2.trans (hpoly_n.trans h3)
  have hcomp : 9 * Real.log (n : ℝ) * ((y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ)) ≤
      (1 / 40 : ℝ) * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) := by
    have hstep1 : 360 * Real.log (n : ℝ) * ((y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ)) ≤
        (y : ℝ) ^ (1 / 2 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁ := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      calc 360 * Real.log (n : ℝ) * (y : ℝ) ^ (1 / 2 : ℝ) * (2 * Real.log (n : ℝ)) ^ M₁
          = (360 * Real.log (n : ℝ) * (2 * Real.log (n : ℝ)) ^ M₁) * (y : ℝ) ^ (1 / 2 : ℝ) := by ring
        _ ≤ (n : ℝ) ^ (3 / 20 : ℝ) * (y : ℝ) ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hpoly_bound (by positivity)
        _ = (y : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 20 : ℝ) := by ring
    have hstep2 : (y : ℝ) ^ (1 / 2 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁ ≤
        ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
      have h1 : ((2 * Real.log (n : ℝ)) ^ M₁)⁻¹ * (y : ℝ) ^ (1 / 2 : ℝ) ≤
          (((n : ℝ) / (n.totient : ℝ)) * tau) * ((y : ℝ) / (r : ℝ)) :=
        mul_le_mul hntau_ge hy_r_ge_sqrt (by positivity) hntau_nn
      linarith [show ((2 * Real.log (n : ℝ)) ^ M₁)⁻¹ * (y : ℝ) ^ (1 / 2 : ℝ) =
          (y : ℝ) ^ (1 / 2 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁ by ring,
        show (((n : ℝ) / (n.totient : ℝ)) * tau) * ((y : ℝ) / (r : ℝ)) =
          ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) by ring]
    linarith
  calc ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1
      ≤ 9 * Real.log (n : ℝ) * ((y : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (3 / 20 : ℝ)) := hprod_le
    _ ≤ (1 / 40 : ℝ) * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) := hcomp
    _ = (1 / 40 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by ring

private lemma small_n4_and_y {n y r M₁ ℓ : ℕ} {tau : ℝ}
    (hn30 : 30 ≤ n) (hr2 : 2 ≤ r) (hr_le_n : r ≤ n) (hlog1 : 1 < Real.log (n : ℝ))
    (hpoly_n : 2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) * Real.log (n : ℝ) ^ (M₁ + 2) ≤
      (n : ℝ) ^ (1 / 20 : ℝ))
    (hz0_ge : (n : ℝ) ^ (3 / 10 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁ ≤
      ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) :
    ((n : ℝ) ^ (1 / 4 : ℝ) + 2 ≤
      64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ))) ∧
    (32 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) + 2 ≤
      64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ))) := by
  have hn1_pos : 1 ≤ n := by omega
  have hr1 : 1 ≤ r := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1_pos
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlogr_pos : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hlogr_le_n : Real.log (r : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hr_pos (by exact_mod_cast hr_le_n)
  have hX_nn : 0 ≤ ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) :=
    le_trans (by positivity) hz0_ge
  have h2_le : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    have : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 16 ≤ n)
    have h1 : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow (by norm_num) this (by norm_num)
  have hsmall_n4 : (n : ℝ) ^ (1 / 4 : ℝ) + 2 ≤
      64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) := by
    have hstep : (n : ℝ) ^ (1 / 4 : ℝ) + 2 ≤
        64 * ((n : ℝ) ^ (3 / 10 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁) / Real.log (n : ℝ) := by
      have hpoly2 : 2 * ((2 * Real.log (n : ℝ)) ^ M₁ * Real.log (n : ℝ)) ≤ 64 * (n : ℝ) ^ (1 / 20 : ℝ) := by
        have h1 : (2 * Real.log (n : ℝ)) ^ M₁ * Real.log (n : ℝ) =
            (2 : ℝ) ^ M₁ * (Real.log (n : ℝ) ^ M₁ * Real.log (n : ℝ)) := by ring
        have h2 : Real.log (n : ℝ) ^ M₁ * Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ (M₁ + 2) := by
          have : Real.log (n : ℝ) ^ (M₁ + 2) = Real.log (n : ℝ) ^ M₁ * Real.log (n : ℝ) ^ 2 := by ring
          rw [this]
          have : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
          nlinarith [pow_nonneg hlog_pos.le M₁]
        have h3 : 2 * (2 : ℝ) ^ M₁ ≤ 64 * (2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1)) := by
          have : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 + 1 := by nlinarith
          rw [pow_add]
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) M₁]
        calc 2 * ((2 * Real.log (n : ℝ)) ^ M₁ * Real.log (n : ℝ))
            = (2 * (2 : ℝ) ^ M₁) * (Real.log (n : ℝ) ^ M₁ * Real.log (n : ℝ)) := by rw [h1]; ring
          _ ≤ (2 * (2 : ℝ) ^ M₁) * Real.log (n : ℝ) ^ (M₁ + 2) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ ≤ (64 * (2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1))) * Real.log (n : ℝ) ^ (M₁ + 2) := by gcongr
          _ = 64 * (2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) * Real.log (n : ℝ) ^ (M₁ + 2)) := by ring
          _ ≤ 64 * (n : ℝ) ^ (1 / 20 : ℝ) := by gcongr
      have hsplit : (n : ℝ) ^ (3 / 10 : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ) := by
        rw [← Real.rpow_add (by positivity)]
        norm_num
      rw [le_div_iff₀ (by positivity)]
      calc ((n : ℝ) ^ (1 / 4 : ℝ) + 2) * Real.log (n : ℝ)
          ≤ (2 * (n : ℝ) ^ (1 / 4 : ℝ)) * Real.log (n : ℝ) := by gcongr; linarith
        _ ≤ 64 * ((n : ℝ) ^ (3 / 10 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁) := by
            rw [mul_div_assoc', le_div_iff₀ (by positivity), hsplit]
            calc 2 * (n : ℝ) ^ (1 / 4 : ℝ) * Real.log (n : ℝ) * (2 * Real.log (n : ℝ)) ^ M₁
                = (n : ℝ) ^ (1 / 4 : ℝ) * (2 * ((2 * Real.log (n : ℝ)) ^ M₁ * Real.log (n : ℝ))) := by ring
              _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (64 * (n : ℝ) ^ (1 / 20 : ℝ)) := by gcongr
              _ = 64 * ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ)) := by ring
    have hstep2 : 64 * ((n : ℝ) ^ (3 / 10 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁) / Real.log (n : ℝ) ≤
        64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) := by
      have hdiv_r : 64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) =
          64 * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) / Real.log (r : ℝ) := by ring
      rw [hdiv_r]
      exact div_le_div₀ (mul_nonneg (by norm_num) hX_nn) (by gcongr) hlogr_pos hlogr_le_n
    exact hstep.trans hstep2
  refine ⟨hsmall_n4, ?_⟩
  let Z := ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ))
  have hZ64 : (n : ℝ) ^ (1 / 4 : ℝ) + 2 ≤ 64 * Z := by
    calc (n : ℝ) ^ (1 / 4 : ℝ) + 2
        ≤ 64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) := hsmall_n4
      _ = 64 * Z := by dsimp only [Z]; ring
  have h4_le : 4 ≤ 64 * Z := by linarith
  have h32 : 32 * Z + 2 ≤ 64 * Z := by linarith
  calc 32 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) + 2
      = 32 * Z + 2 := by dsimp only [Z]; ring
    _ ≤ 64 * Z := h32
    _ = 64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) := by
        dsimp only [Z]; ring

private lemma sumset_params_bounds {n y r v ℓ q_card : ℕ} {tau : ℝ}
    (hn1_pos : 1 ≤ n) (hr1 : 1 ≤ r) (hy_le_n : y ≤ n) (hv1 : 1 ≤ v) (hℓ8 : 8 ≤ ℓ)
    (h100l : 100 * (ℓ : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ))
    (hhigh_y : (n : ℝ) ≤ (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (15 * (r : ℝ)))
    (hv_le16 : (v : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ))
    (hQ_ge_lo : (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) ≤ (q_card : ℝ)) :
    let q_bound := ⌊(y : ℝ) * (q_card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ))⌋₊
    let m_bound := ⌈(y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ))⌉₊
    10 ≤ m_bound ∧ 1 ≤ q_bound ∧ 3 * q_bound ≤ ℓ * (m_bound - 2) := by
  intro q_bound m_bound
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1_pos
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hv_pos : (0 : ℝ) < v := by exact_mod_cast hv1
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hm_ge_big : 10 ≤ m_bound := by
    have hprod_ge : (15 : ℝ) * (n : ℝ) ≤ (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (r : ℝ) := by
      rw [le_div_iff₀ hr_pos]
      rw [le_div_iff₀ (by positivity)] at hhigh_y
      linarith
    have hyQ_ge : (3 / 2 : ℝ) * (n : ℝ) ^ (15 / 16 : ℝ) ≤ (y : ℝ) * (q_card : ℝ) / (v : ℝ) := by
      have h1 : (y : ℝ) * (q_card : ℝ) ≥ (3 / 2 : ℝ) * (n : ℝ) := by
        calc (y : ℝ) * (q_card : ℝ)
            ≥ (y : ℝ) * ((1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) := by
              gcongr
          _ = (1 / 10 : ℝ) * ((y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (r : ℝ)) := by ring
          _ ≥ (1 / 10 : ℝ) * ((15 : ℝ) * (n : ℝ)) := by gcongr
          _ = (3 / 2 : ℝ) * (n : ℝ) := by ring
      have hv_n : (v : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) :=
        hv_le16.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hy_le_n) (by norm_num))
      have hsplit_n : (n : ℝ) = (n : ℝ) ^ (15 / 16 : ℝ) * (n : ℝ) ^ (1 / 16 : ℝ) := by
        rw [← Real.rpow_add hn_pos]
        norm_num
      rw [le_div_iff₀ hv_pos]
      calc (3 / 2 : ℝ) * (n : ℝ) ^ (15 / 16 : ℝ) * (v : ℝ)
          ≤ (3 / 2 : ℝ) * (n : ℝ) ^ (15 / 16 : ℝ) * (n : ℝ) ^ (1 / 16 : ℝ) := by gcongr
        _ = (3 / 2 : ℝ) * (n : ℝ) := by linarith
        _ ≤ (y : ℝ) * (q_card : ℝ) := h1
    have hdiv_ge : (10 : ℝ) ≤ (y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) := by
      have h1 : (n : ℝ) ^ (15 / 16 : ℝ) ≥ (n : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1_pos) (by norm_num)
      have hℓ2_nn : (0 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by positivity
      have h2 : 10 * (ℓ : ℝ) ^ 2 ≤ (3 / 2 : ℝ) * (n : ℝ) ^ (15 / 16 : ℝ) := by linarith
      calc (10 : ℝ) = (10 * (ℓ : ℝ) ^ 2) / (ℓ : ℝ) ^ 2 := by field_simp [hℓ_pos.ne']
        _ ≤ ((3 / 2 : ℝ) * (n : ℝ) ^ (15 / 16 : ℝ)) / (ℓ : ℝ) ^ 2 := by gcongr
        _ ≤ ((y : ℝ) * (q_card : ℝ) / (v : ℝ)) / (ℓ : ℝ) ^ 2 := by gcongr
        _ = (y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) := by ring
    exact Nat.cast_le.mp (show ((10 : ℕ) : ℝ) ≤ (m_bound : ℝ) from
      (by norm_num : ((10 : ℕ) : ℝ) = 10).symm ▸ hdiv_ge.trans (Nat.le_ceil _))
  have hq_ge1 : 1 ≤ q_bound := by
    have hm10 : (10 : ℝ) ≤ (m_bound : ℝ) := by exact_mod_cast hm_ge_big
    have hm_lt : (m_bound : ℝ) < (y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hq_real : (1 : ℝ) ≤ (y : ℝ) * (q_card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ)) := by
      have : 9 ≤ (y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) := by linarith
      have : 4 * (ℓ : ℝ) * (v : ℝ) ≤ (ℓ : ℝ) ^ 2 * (v : ℝ) := by
        have hℓ8r : (8 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ8
        calc 4 * (ℓ : ℝ) * (v : ℝ) ≤ (ℓ : ℝ) * (ℓ : ℝ) * (v : ℝ) := by gcongr; linarith
          _ = (ℓ : ℝ) ^ 2 * (v : ℝ) := by ring
      have hdiv : (y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) ≤
          (y : ℝ) * (q_card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) this
      linarith
    exact Nat.floor_pos.mpr hq_real
  have h3q : 3 * q_bound ≤ ℓ * (m_bound - 2) := by
    have hq_le : (q_bound : ℝ) ≤ (y : ℝ) * (q_card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ)) :=
      Nat.floor_le (by positivity)
    have hm_ge : (y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) ≤ (m_bound : ℝ) :=
      Nat.le_ceil _
    have hm_sub : (m_bound : ℝ) - 2 ≥ (3 / 4 : ℝ) * (m_bound : ℝ) := by
      have : (10 : ℝ) ≤ (m_bound : ℝ) := by exact_mod_cast hm_ge_big
      linarith
    have h_real : (3 * q_bound : ℝ) ≤ (ℓ : ℝ) * ((m_bound : ℝ) - 2) := by
      calc (3 * q_bound : ℝ) ≤ 3 * ((y : ℝ) * (q_card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ))) := by gcongr
        _ = (3 / 4 : ℝ) * (ℓ : ℝ) * ((y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ))) := by
            field_simp [hℓ_pos.ne', hv_pos.ne']
        _ ≤ (3 / 4 : ℝ) * (ℓ : ℝ) * (m_bound : ℝ) := by gcongr
        _ = (ℓ : ℝ) * ((3 / 4 : ℝ) * (m_bound : ℝ)) := by ring
        _ ≤ (ℓ : ℝ) * ((m_bound : ℝ) - 2) := by gcongr
    have hm_le2 : 2 ≤ m_bound := by omega
    have hcast : ((m_bound - 2 : ℕ) : ℝ) = (m_bound : ℝ) - 2 := by
      rw [Nat.cast_sub hm_le2]
      norm_num
    have h3q_cast : ((3 * q_bound : ℕ) : ℝ) ≤ ((ℓ * (m_bound - 2) : ℕ) : ℝ) := by
      push_cast
      rw [hcast]
      exact h_real
    exact Nat.cast_le.mp h3q_cast
  exact ⟨hm_ge_big, hq_ge1, h3q⟩

private lemma q_card_ge_four_ell {n y r M₁ ℓ q_card : ℕ} {tau : ℝ}
    (hn1_pos : 1 ≤ n) (hℓ1 : 1 ≤ ℓ) (hlog1 : 1 < Real.log (n : ℝ))
    (h100l : 100 * (ℓ : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ))
    (hpoly_n : 2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) * Real.log (n : ℝ) ^ (M₁ + 2) ≤
      (n : ℝ) ^ (1 / 20 : ℝ))
    (hz0_ge : (n : ℝ) ^ (3 / 10 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁ ≤
      ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ))
    (hQ_ge_lo : (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) ≤ (q_card : ℝ)) :
    (4 * ℓ : ℝ) ≤ (q_card : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1_pos
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have h_card : (n : ℝ) ^ (3 / 10 : ℝ) / (10 * (2 * Real.log (n : ℝ)) ^ M₁) ≤ (q_card : ℝ) := by
    calc (n : ℝ) ^ (3 / 10 : ℝ) / (10 * (2 * Real.log (n : ℝ)) ^ M₁)
        = (1 / 10 : ℝ) * ((n : ℝ) ^ (3 / 10 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁) := by ring
      _ ≤ (1 / 10 : ℝ) * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) := by gcongr
      _ = (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by ring
      _ ≤ (q_card : ℝ) := hQ_ge_lo
  have hpoly4 : (40 * (ℓ : ℝ)) * (2 * Real.log (n : ℝ)) ^ M₁ ≤ (n : ℝ) ^ (3 / 10 : ℝ) := by
    have h1 : (2 * Real.log (n : ℝ)) ^ M₁ ≤
        2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) * Real.log (n : ℝ) ^ (M₁ + 2) := by
      have h2p : (2 * Real.log (n : ℝ)) ^ M₁ = (2 : ℝ) ^ M₁ * Real.log (n : ℝ) ^ M₁ := mul_pow _ _ _
      have hlog_le2 : Real.log (n : ℝ) ^ M₁ ≤ Real.log (n : ℝ) ^ (M₁ + 2) := by
        have : Real.log (n : ℝ) ^ (M₁ + 2) = Real.log (n : ℝ) ^ M₁ * Real.log (n : ℝ) ^ 2 := by ring
        rw [this]
        have : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
        nlinarith [pow_nonneg hlog_pos.le M₁]
      have h2_le_K : (2 : ℝ) ^ M₁ ≤ 2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) := by
        rw [pow_add]
        have : (1 : ℝ) ≤ 2 ^ 10 * ((ℓ : ℝ) ^ 2 + 1) := by nlinarith
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) M₁]
      exact h2p.le.trans (mul_le_mul h2_le_K hlog_le2 (by positivity) (by positivity))
    have h40_le : (40 * (ℓ : ℝ)) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      have : (ℓ : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
        nlinarith
      linarith
    have hsplit : (n : ℝ) ^ (3 / 10 : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ) := by
      rw [← Real.rpow_add hn_pos]
      norm_num
    rw [hsplit]
    exact mul_le_mul h40_le (h1.trans hpoly_n) (by positivity) (by positivity)
  have h_ge : (4 * (ℓ : ℝ)) ≤ (n : ℝ) ^ (3 / 10 : ℝ) / (10 * (2 * Real.log (n : ℝ)) ^ M₁) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [show (4 * (ℓ : ℝ)) * (10 * (2 * Real.log (n : ℝ)) ^ M₁) =
        (40 * (ℓ : ℝ)) * (2 * Real.log (n : ℝ)) ^ M₁ by ring]
  exact h_ge.trans h_card

private lemma sumset_sub_Icc {y v ℓ : ℕ} (hv1 : 1 ≤ v)
    {V : Fin ℓ → Finset ℕ} {Q : Finset ℕ}
    (hVQ : ∀ i, V i ⊆ Q)
    (hVcard : ∀ i, ((V i).card : ℝ) ≤ (Q.card : ℝ) / (8 * (ℓ : ℝ)))
    (hQ_range : ∀ x ∈ Q, y ≤ v * x ∧ v * x < 2 * y) :
    ∀ i, ∃ a : ℕ, ((V i).powerset.image (fun B ↦ ∑ x ∈ B, x)) ⊆
      Finset.Icc a (a + ⌊(y : ℝ) * (Q.card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ))⌋₊) := by
  intro i
  by_cases hℓ0 : ℓ = 0
  · exfalso; subst hℓ0; exact Fin.elim0 i
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hℓ0)
  have hv_pos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
  refine ⟨0, fun s hs ↦ ?_⟩
  rw [zero_add, Finset.mem_Icc]
  refine ⟨Nat.zero_le s, ?_⟩
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hs
  have hB_V : B ⊆ V i := Finset.mem_powerset.mp hB
  have hsum_le : (∑ x ∈ B, x : ℝ) ≤ ((V i).card : ℝ) * (2 * (y : ℝ) / (v : ℝ)) := by
    have h1 : (∑ x ∈ B, x : ℝ) ≤ ∑ _x ∈ B, (2 * (y : ℝ) / (v : ℝ)) := by
      refine Finset.sum_le_sum fun x hx ↦ ?_
      have hxQ : x ∈ Q := hVQ i (hB_V hx)
      have hlt := (hQ_range x hxQ).2
      rw [le_div_iff₀ hv_pos]
      exact_mod_cast (by nlinarith : x * v ≤ 2 * y)
    have h2 : ∑ _x ∈ B, (2 * (y : ℝ) / (v : ℝ)) = (B.card : ℝ) * (2 * (y : ℝ) / (v : ℝ)) := by
      simp [nsmul_eq_mul]
    have h3 : (B.card : ℝ) ≤ ((V i).card : ℝ) := by exact_mod_cast Finset.card_le_card hB_V
    exact h1.trans (h2.le.trans (mul_le_mul_of_nonneg_right h3 (by positivity)))
  have hle_q : ((∑ x ∈ B, x : ℕ) : ℝ) ≤ (y : ℝ) * (Q.card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ)) := by
    calc ((∑ x ∈ B, x : ℕ) : ℝ) = ∑ x ∈ B, (x : ℝ) := by push_cast; rfl
      _ ≤ ((V i).card : ℝ) * (2 * (y : ℝ) / (v : ℝ)) := hsum_le
      _ ≤ ((Q.card : ℝ) / (8 * (ℓ : ℝ))) * (2 * (y : ℝ) / (v : ℝ)) := by
          gcongr
          exact hVcard i
      _ = (y : ℝ) * (Q.card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ)) := by
          field_simp [hℓ_pos.ne', hv_pos.ne']
          ring
  exact Nat.le_floor hle_q

private lemma ba_len_helper {y v ℓ q_card m_bound a b : ℕ}
    (hv1 : 1 ≤ v) (hℓ1 : 1 ≤ ℓ) (hm_ge_big : 10 ≤ m_bound)
    (hm_ge : (y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)) ≤ (m_bound : ℝ))
    (hQ_ge_4l : (4 * ℓ : ℝ) ≤ (q_card : ℝ))
    (hab : a + ℓ * (m_bound - 1) ≤ b) :
    (2 * y) / v ≤ b - a := by
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hv_pos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
  have hm1_ge : (m_bound : ℝ) - 1 ≥ (9 / 10 : ℝ) * (m_bound : ℝ) := by
    have : (10 : ℝ) ≤ (m_bound : ℝ) := by exact_mod_cast hm_ge_big
    linarith
  have h1 : (ℓ : ℝ) * ((m_bound : ℝ) - 1) ≥ 2 * (y : ℝ) / (v : ℝ) := by
    calc (ℓ : ℝ) * ((m_bound : ℝ) - 1)
        ≥ (ℓ : ℝ) * ((9 / 10 : ℝ) * (m_bound : ℝ)) := by gcongr
      _ ≥ (ℓ : ℝ) * ((9 / 10 : ℝ) * ((y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ)))) := by gcongr
      _ = (9 / 10 : ℝ) * (y : ℝ) * (q_card : ℝ) / ((ℓ : ℝ) * (v : ℝ)) := by
          field_simp [hℓ_pos.ne', hv_pos.ne']
      _ ≥ (9 / 10 : ℝ) * (y : ℝ) * (4 * (ℓ : ℝ)) / ((ℓ : ℝ) * (v : ℝ)) := by gcongr
      _ = (18 / 5 : ℝ) * (y : ℝ) / (v : ℝ) := by
          field_simp [hℓ_pos.ne', hv_pos.ne']
          ring
      _ ≥ 2 * (y : ℝ) / (v : ℝ) := by
          have : (2 : ℝ) * (y : ℝ) ≤ (18 / 5 : ℝ) * (y : ℝ) := by linarith
          exact div_le_div_of_nonneg_right this hv_pos.le
  have h2 : (((2 * y) / v : ℕ) : ℝ) ≤ 2 * (y : ℝ) / (v : ℝ) := by
    rw [le_div_iff₀ hv_pos]
    exact_mod_cast Nat.div_mul_le_self (2 * y) v
  have h3' : (((2 * y) / v : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) := by
    have hba_real : ((b - a : ℕ) : ℝ) ≥ (ℓ : ℝ) * ((m_bound : ℝ) - 1) := by
      have h2' : ℓ * (m_bound - 1) ≤ b - a := by omega
      have hcast1 : ((ℓ * (m_bound - 1) : ℕ) : ℝ) = (ℓ : ℝ) * ((m_bound : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]
        push_cast
        rfl
      rw [← hcast1]
      exact_mod_cast h2'
    linarith
  exact_mod_cast h3'

private lemma endpoints_helper {n y r v ℓ a b : ℕ} {tau : ℝ}
    (hn1_pos : 1 ≤ n) (hr1 : 1 ≤ r) (hv1 : 1 ≤ v) (hℓ1 : 1 ≤ ℓ)
    (hv_dvd_n : v ∣ n)
    {V : Fin ℓ → Finset ℕ} {Q : Finset ℕ}
    (hVQ : ∀ i, V i ⊆ Q)
    (hVdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hVcard : ∀ i, ((V i).card : ℝ) ≤ (Q.card : ℝ) / (8 * (ℓ : ℝ)))
    (hQ_range : ∀ x ∈ Q, y ≤ v * x ∧ v * x < 2 * y)
    (hQ_ge_lo : (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) ≤ (Q.card : ℝ))
    (hQ_le_hi : (Q.card : ℝ) ≤ (1 / 7 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ))
    (hlow_y : (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (25 * (r : ℝ)) ≤ (n : ℝ))
    (hhigh_y : (n : ℝ) ≤ (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (15 * (r : ℝ)))
    (ha_le_b : a ≤ b)
    (hb_in_U : b ∈ subsetSums ((Finset.univ.biUnion V : Finset ℕ) : Set ℕ)) :
    a ≤ n / v ∧ n / v ≤ b + ∑ x ∈ (Q \ Finset.univ.biUnion V), x := by
  let U : Finset ℕ := Finset.univ.biUnion V
  let W : Finset ℕ := Q \ U
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1_pos
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hv_pos : (0 : ℝ) < v := by exact_mod_cast hv1
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hU_sub : U ⊆ Q := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hVQ i hxi
  have ha_le : a ≤ n / v := by
    obtain ⟨B, hBU, hBsum⟩ := hb_in_U
    have ha_sum : (a : ℝ) ≤ ∑ x ∈ B, (x : ℝ) := by
      have : a ≤ ∑ x ∈ B, x := ha_le_b.trans hBsum.le
      calc (a : ℝ) ≤ ((∑ x ∈ B, x : ℕ) : ℝ) := by exact_mod_cast this
        _ = ∑ x ∈ B, (x : ℝ) := by push_cast; rfl
    have hBU_U : B ⊆ U := Finset.coe_subset.mp hBU
    have hB_le_U : ∑ x ∈ B, (x : ℝ) ≤ ∑ x ∈ U, (x : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hBU_U fun _ _ _ ↦ by positivity
    have hU_le : ∑ x ∈ U, (x : ℝ) ≤ ∑ i : Fin ℓ, ∑ x ∈ V i, (x : ℝ) :=
      le_of_eq (Finset.sum_biUnion (s := (Finset.univ : Finset (Fin ℓ))) (t := V)
        (f := fun x : ℕ ↦ (x : ℝ)) (fun i _ j _ hij ↦ hVdisj i j hij))
    have hVi_le : ∀ i, ∑ x ∈ V i, (x : ℝ) ≤ ((V i).card : ℝ) * (2 * (y : ℝ) / (v : ℝ)) := by
      intro i
      calc ∑ x ∈ V i, (x : ℝ) ≤ ∑ _x ∈ V i, (2 * (y : ℝ) / (v : ℝ)) := by
            refine Finset.sum_le_sum fun x hx ↦ ?_
            have hlt := (hQ_range x (hVQ i hx)).2
            rw [le_div_iff₀ hv_pos]
            exact_mod_cast (by nlinarith : x * v ≤ 2 * y)
        _ = ((V i).card : ℝ) * (2 * (y : ℝ) / (v : ℝ)) := by simp [nsmul_eq_mul]
    have hsum_V : ∑ i : Fin ℓ, ∑ x ∈ V i, (x : ℝ) ≤ (Q.card : ℝ) * (y : ℝ) / (4 * (v : ℝ)) := by
      calc ∑ i : Fin ℓ, ∑ x ∈ V i, (x : ℝ)
          ≤ ∑ _i : Fin ℓ, ((Q.card : ℝ) / (8 * (ℓ : ℝ))) * (2 * (y : ℝ) / (v : ℝ)) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact (hVi_le i).trans (mul_le_mul_of_nonneg_right (hVcard i) (by positivity))
        _ = (ℓ : ℝ) * (((Q.card : ℝ) / (8 * (ℓ : ℝ))) * (2 * (y : ℝ) / (v : ℝ))) := by
            simp [nsmul_eq_mul]
        _ = (Q.card : ℝ) * (y : ℝ) / (4 * (v : ℝ)) := by
            field_simp [hℓ_pos.ne', hv_pos.ne']
            ring
    have h_va_lt : (v : ℝ) * (a : ℝ) < (n : ℝ) := by
      calc (v : ℝ) * (a : ℝ) ≤ (v : ℝ) * ((Q.card : ℝ) * (y : ℝ) / (4 * (v : ℝ))) := by
            gcongr
            exact ha_sum.trans (hB_le_U.trans (hU_le.trans hsum_V))
        _ = (Q.card : ℝ) * (y : ℝ) / 4 := by field_simp [hv_pos.ne']
        _ ≤ ((1 / 7 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) * (y : ℝ) / 4 := by
            gcongr
        _ = (1 / 28 : ℝ) * ((y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (r : ℝ)) := by ring
        _ ≤ (1 / 28 : ℝ) * (25 * (n : ℝ)) := by
            have h1 : (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (r : ℝ) ≤ 25 * (n : ℝ) := by
              rw [div_le_iff₀ hr_pos]
              rw [div_le_iff₀ (by positivity)] at hlow_y
              linarith
            gcongr
        _ < (n : ℝ) := by linarith
    have hva_nat : v * a < n := by exact_mod_cast h_va_lt
    rw [Nat.le_div_iff_mul_le hv1, mul_comm]
    exact hva_nat.le
  have hnv_le : n / v ≤ b + ∑ x ∈ W, x := by
    have hU_card : U.card ≤ ∑ i : Fin ℓ, (V i).card := Finset.card_biUnion_le
    have hU_card_real : (U.card : ℝ) ≤ (Q.card : ℝ) / 8 := by
      calc (U.card : ℝ) ≤ ∑ i : Fin ℓ, ((V i).card : ℝ) := by exact_mod_cast hU_card
        _ ≤ ∑ _i : Fin ℓ, (Q.card : ℝ) / (8 * (ℓ : ℝ)) := Finset.sum_le_sum fun i _ ↦ hVcard i
        _ = (ℓ : ℝ) * ((Q.card : ℝ) / (8 * (ℓ : ℝ))) := by simp [nsmul_eq_mul]
        _ = (Q.card : ℝ) / 8 := by field_simp [hℓ_pos.ne']
    have hW_card_real : (7 / 8 : ℝ) * (Q.card : ℝ) ≤ (W.card : ℝ) := by
      have hcard_sdiff : W.card + U.card = Q.card := Finset.card_sdiff_add_card_eq_card hU_sub
      have h1 : (W.card : ℝ) + (U.card : ℝ) = (Q.card : ℝ) := by exact_mod_cast hcard_sdiff
      linarith
    have hW_sum_real : (n : ℝ) < (v : ℝ) * (b + ∑ x ∈ W, x : ℕ) := by
      have h1 : (W.card : ℝ) * (y : ℝ) ≤ ∑ x ∈ W, ((v : ℝ) * (x : ℝ)) := by
        calc (W.card : ℝ) * (y : ℝ) = ∑ _x ∈ W, (y : ℝ) := by simp [nsmul_eq_mul]
          _ ≤ ∑ x ∈ W, ((v : ℝ) * (x : ℝ)) := by
              refine Finset.sum_le_sum fun x hx ↦ ?_
              have hxQ : x ∈ Q := (Finset.mem_sdiff.mp hx).1
              exact_mod_cast (hQ_range x hxQ).1
      have h2 : ∑ x ∈ W, ((v : ℝ) * (x : ℝ)) = (v : ℝ) * (∑ x ∈ W, (x : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
      have h3 : (v : ℝ) * (∑ x ∈ W, (x : ℝ)) ≤ (v : ℝ) * ((b : ℝ) + ∑ x ∈ W, (x : ℝ)) := by
        have : 0 ≤ (v : ℝ) * (b : ℝ) := by positivity
        linarith
      have h4 : (105 / 80 : ℝ) * (n : ℝ) ≤ (W.card : ℝ) * (y : ℝ) := by
        calc (W.card : ℝ) * (y : ℝ) ≥ ((7 / 8 : ℝ) * (Q.card : ℝ)) * (y : ℝ) := by gcongr
          _ ≥ (7 / 8 : ℝ) * ((1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) * (y : ℝ) := by
              gcongr
          _ = (7 / 80 : ℝ) * ((y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (r : ℝ)) := by ring
          _ ≥ (7 / 80 : ℝ) * (15 * (n : ℝ)) := by
              have hhigh' : 15 * (n : ℝ) ≤ (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (r : ℝ) := by
                rw [le_div_iff₀ hr_pos]
                rw [le_div_iff₀ (by positivity)] at hhigh_y
                linarith
              gcongr
          _ = (105 / 80 : ℝ) * (n : ℝ) := by ring
      have hcast_sum : ((b + ∑ x ∈ W, x : ℕ) : ℝ) = (b : ℝ) + ∑ x ∈ W, (x : ℝ) := by
        push_cast
        rfl
      rw [hcast_sum]
      linarith
    have hv_mul_lt : n < v * (b + ∑ x ∈ W, x) := by exact_mod_cast hW_sum_real
    have hmul_eq : v * (n / v) = n := Nat.mul_div_cancel' hv_dvd_n
    nlinarith
  exact ⟨ha_le, hnv_le⟩

private lemma ev_n_props (c : ℝ) (hc : 0 < c) (ℓ M₁ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      30 ≤ n ∧
      Real.exp 3 < (n : ℝ) ∧
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) ∧
      (n : ℝ) ^ (1 / 10 : ℝ) + 2 ≤ c * (n : ℝ) ^ (1 / 4 : ℝ) ∧
      c * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1) ≤ (n : ℝ) ∧
      640 < (1 / 10 : ℝ) * Real.log (n : ℝ) ∧
      (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) ∧
      2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1) * Real.log (n : ℝ) ^ (M₁ + 2) ≤ (n : ℝ) ^ (1 / 20 : ℝ) ∧
      100 * (ℓ : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hlog_1_12 : Real.log =o[atTop] (fun x : ℝ ↦ x ^ (1 / 12 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hlog_poly_1_20 : (fun x : ℝ ↦ Real.log x ^ (M₁ + 2)) =o[atTop] (fun x : ℝ ↦ x ^ (1 / 20 : ℝ)) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (M₁ + 2 : ℕ) (by norm_num)
  let K_poly : ℝ := 2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1)
  have hK_poly_pos : 0 < K_poly := by positivity
  have hn30 : ∀ᶠ n : ℕ in atTop, 30 ≤ n := eventually_ge_atTop 30
  have hexp3 : ∀ᶠ n : ℕ in atTop, Real.exp 3 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (Real.exp 3))
  have h1_12 : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := by
    have h := tendsto_natCast_atTop_atTop.eventually (hlog_1_12.bound one_pos)
    filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (by positivity), one_mul] at hn
    exact hn
  have hrpow_cmp : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / 10 : ℝ) + 2 ≤ c * (n : ℝ) ^ (1 / 4 : ℝ) := by
    have ht := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 20)).comp
      tendsto_natCast_atTop_atTop
    have h1_4 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (c / 2) * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have ht2 := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
        tendsto_natCast_atTop_atTop
      filter_upwards [ht2.eventually (eventually_ge_atTop (4 / c))] with n hn
      dsimp only [Function.comp_def] at hn
      calc (2 : ℝ) = (c / 2) * (4 / c) := by field_simp; norm_num
        _ ≤ (c / 2) * (n : ℝ) ^ (1 / 4 : ℝ) := by gcongr
    filter_upwards [ht.eventually (eventually_ge_atTop (2 / c)), h1_4, eventually_ge_atTop 1] with
      n hn h2 hn1
    dsimp only [Function.comp_def] at hn
    have hsplit : (n : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (3 / 20 : ℝ) := by
      rw [← Real.rpow_add (by exact_mod_cast hn1)]
      norm_num
    have hpart1 : (n : ℝ) ^ (1 / 10 : ℝ) ≤ (c / 2) * (n : ℝ) ^ (1 / 4 : ℝ) := by
      rw [hsplit]
      calc (n : ℝ) ^ (1 / 10 : ℝ)
          = (n : ℝ) ^ (1 / 10 : ℝ) * ((c / 2) * (2 / c)) := by field_simp
        _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) * ((c / 2) * (n : ℝ) ^ (3 / 20 : ℝ)) := by gcongr
        _ = (c / 2) * ((n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (3 / 20 : ℝ)) := by ring
    linarith
  have hupper_r : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1) ≤ (n : ℝ) := by
    have ht := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 12)).comp
      tendsto_natCast_atTop_atTop
    filter_upwards [h1_12, ht.eventually (eventually_ge_atTop (c * (1 / Real.log 2 + 1))),
      eventually_ge_atTop 2] with n hln hpow hn2
    dsimp only [Function.comp_def] at hpow
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h1_12' : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
    have hfac : Real.log (n : ℝ) / Real.log 2 + 1 ≤
        (1 / Real.log 2 + 1) * (n : ℝ) ^ (1 / 12 : ℝ) := by
      calc Real.log (n : ℝ) / Real.log 2 + 1
          ≤ (n : ℝ) ^ (1 / 12 : ℝ) / Real.log 2 + (n : ℝ) ^ (1 / 12 : ℝ) := by gcongr
        _ = (1 / Real.log 2 + 1) * (n : ℝ) ^ (1 / 12 : ℝ) := by ring
    have hmul : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) ^ (7 / 12 : ℝ) = (n : ℝ) := by
      rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
      norm_num
    calc c * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1)
        ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) * ((1 / Real.log 2 + 1) * (n : ℝ) ^ (1 / 12 : ℝ)) := by gcongr
      _ = (c * (1 / Real.log 2 + 1)) * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ)) := by ring
      _ ≤ (n : ℝ) ^ (7 / 12 : ℝ) * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ)) := by gcongr
      _ = (n : ℝ) := by linarith
  have hlog640 : ∀ᶠ n : ℕ in atTop, 640 < (1 / 10 : ℝ) * Real.log (n : ℝ) := by
    have h := tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually (eventually_gt_atTop (6400 : ℝ)))
    filter_upwards [h] with n hn
    linarith
  have h3_5 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
  have hpoly : ∀ᶠ n : ℕ in atTop,
      K_poly * Real.log (n : ℝ) ^ (M₁ + 2) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
    have hb := tendsto_natCast_atTop_atTop.eventually (hlog_poly_1_20.bound (inv_pos.mpr hK_poly_pos))
    filter_upwards [hb, eventually_ge_atTop 2] with n hn hn2
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    rw [Real.norm_of_nonneg (pow_nonneg hlog0 _), Real.norm_of_nonneg (by positivity)] at hn
    calc K_poly * Real.log (n : ℝ) ^ (M₁ + 2)
        ≤ K_poly * (K_poly⁻¹ * (n : ℝ) ^ (1 / 20 : ℝ)) := by gcongr
      _ = (n : ℝ) ^ (1 / 20 : ℝ) := by field_simp [hK_poly_pos.ne']
  have h100l : ∀ᶠ n : ℕ in atTop, 100 * (ℓ : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    have ht := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop (100 * (ℓ : ℝ) ^ 2))
  filter_upwards [hn30, hexp3, h1_12, hrpow_cmp, hupper_r, hlog640, h3_5, hpoly, h100l] with
    n a1 a2 a3 a4 a5 a6 a7 a8 a9
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

private lemma h1_up_adapter {n r : ℕ} (hr_le_n : r ≤ n) (hr_ge_10 : (n : ℝ) ^ (1 / 10 : ℝ) ≤ (r : ℝ))
    (hn1 : ∀ r x : ℕ, r ≤ n → (n : ℝ) ^ (1 / 10 : ℝ) ≤ (r : ℝ) → (n : ℝ) ^ (1 / 4 : ℝ) ≤ (x : ℝ) →
      let S := n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime)
      let tau := ∏ p ∈ S, (1 - (1 : ℝ) / p)
      let Y_up := (Finset.Ico x (2 * x)).filter (fun m ↦ ∃ u q : ℕ,
        m = q * u ∧ u ∣ n ∧ (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ p ∈ S, ¬ p ∣ q)
      let Y_lo := (Finset.Ico x (2 * x)).filter (fun m ↦ ∃ u q : ℕ,
        m = q * u ∧ u ∣ n ∧ (u : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ p ∈ S, ¬ p ∣ q)
      ((Y_up.card : ℝ) ≤ 8 * ((n : ℝ) / (n.totient : ℝ)) * tau * (x : ℝ)) ∧
        (r ^ 2 ≤ x → ((n : ℝ) / (n.totient : ℝ)) * tau * (x : ℝ) / 8 ≤ (Y_lo.card : ℝ))) :
    ∀ x : ℕ, (n : ℝ) ^ (1 / 4 : ℝ) ≤ (x : ℝ) →
      (((Finset.Ico x (2 * x)).filter (fun m ↦ ∃ u q : ℕ, m = q * u ∧ u ∣ n ∧
        (u : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) ∧
        ∀ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime), ¬ p ∣ q)).card : ℝ) ≤
        8 * ((n : ℝ) / (n.totient : ℝ)) *
          (∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
            (1 - (1 : ℝ) / p)) * (x : ℝ) := by
  intro x hx
  have h := (hn1 r x hr_le_n hr_ge_10 hx).1
  refine le_trans (le_of_eq ?_) h
  congr 1

end Helpers

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos360_erdos_360_R1.H4 := by
  intro h1 h2 h3 h4
  obtain ⟨c, hc, ℓ, hℓ8, h4_ev⟩ := h4
  obtain ⟨M₁, hM₁_pos, hprod_lo⟩ := prod_nth_prime_lower
  refine ⟨c, hc, ?_⟩
  let K_poly : ℝ := 2 ^ (M₁ + 10) * ((ℓ : ℝ) ^ 2 + 1)
  have hev_n : ∀ᶠ n : ℕ in atTop,
      30 ≤ n ∧
      Real.exp 3 < (n : ℝ) ∧
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) ∧
      (n : ℝ) ^ (1 / 10 : ℝ) + 2 ≤ c * (n : ℝ) ^ (1 / 4 : ℝ) ∧
      c * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1) ≤ (n : ℝ) ∧
      640 < (1 / 10 : ℝ) * Real.log (n : ℝ) ∧
      (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) ∧
      K_poly * Real.log (n : ℝ) ^ (M₁ + 2) ≤ (n : ℝ) ^ (1 / 20 : ℝ) ∧
      100 * (ℓ : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    ev_n_props c hc ℓ M₁
  have hpr_ev : ∀ᶠ n : ℕ in atTop,
      ∀ r : ℕ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ (r : ℝ) →
        (r : ℝ) * Real.log (r : ℝ) / 4 ≤ (Nat.nth Nat.Prime r : ℝ) := by
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp nth_prime_ge_div_four
    have ht := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop (R₀ : ℝ))] with n hn r hr
    apply hR₀ r
    exact_mod_cast hn.trans hr
  filter_upwards [h1, h2, h4_ev, hev_n, hpr_ev] with n hn1 hn2_ap hn4 hn_asymp hpr_fn
  obtain ⟨hn30, hexp3, hlog_1_12', hr_lo_cmp, hr_hi_cmp, hlog640, h_35, hpoly_n, h100l⟩ := hn_asymp
  intro y psi r tau h2y hr2y hy35 hlow_y hhigh_y P hP_card
  have hn2 : 2 ≤ n := by omega
  have hn1_pos : 1 ≤ n := by omega
  have htot_pos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn1_pos
  have hlog1 : 1 < Real.log (n : ℝ) := by
    have hexp1_lt : Real.exp 1 < Real.exp 3 := Real.exp_lt_exp.mpr (by norm_num)
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_trans hexp1_lt hexp3)
  have hlog3 : 3 < Real.log (n : ℝ) := by
    rw [← Real.log_exp 3]
    exact Real.log_lt_log (Real.exp_pos 3) hexp3
  have hloglog1 : 1 < Real.log (Real.log (n : ℝ)) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_trans exp_one_lt_three hlog3)
  have htot_ge1 : 1 ≤ (n : ℝ) / (n.totient : ℝ) := by
    rw [one_le_div htot_pos]
    exact_mod_cast Nat.totient_le n
  have hloglog_le : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
    Real.log_le_self (by linarith)
  have hden_le : Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) ≤
      Real.log (n : ℝ) := by
    have h1 : Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) ≤ Real.log (n : ℝ) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hloglog_le (by norm_num)
    have h2 : Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) ≤
        Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (n : ℝ) ^ (2 / 3 : ℝ) := by
      gcongr
    have h3 : Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (n : ℝ) ^ (2 / 3 : ℝ) = Real.log (n : ℝ) := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    linarith
  have hden_pos : 0 < Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) := by
    positivity
  have hpsi_ge : (n : ℝ) ^ (1 / 3 : ℝ) / (n : ℝ) ^ (1 / 12 : ℝ) ≤ psi := by
    dsimp only [psi]
    calc (n : ℝ) ^ (1 / 3 : ℝ) / (n : ℝ) ^ (1 / 12 : ℝ)
        ≤ (n : ℝ) ^ (1 / 3 : ℝ) * 1 / Real.log (n : ℝ) := by
          gcongr
          simp
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
            (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ)) := by
          gcongr
  have hpsi_ge' : (n : ℝ) ^ (1 / 4 : ℝ) ≤ psi := by
    calc (n : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) / (n : ℝ) ^ (1 / 12 : ℝ) := by
          rw [← Real.rpow_sub (by positivity)]
          norm_num
      _ ≤ psi := hpsi_ge
  have hr_ge_lo : (n : ℝ) ^ (1 / 10 : ℝ) + 1 ≤ (r : ℝ) := by
    have hc_psi : (n : ℝ) ^ (1 / 10 : ℝ) + 2 ≤ c * psi := hr_lo_cmp.trans (by gcongr)
    have hfl : c * psi < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hr_ge_10 : (n : ℝ) ^ (1 / 10 : ℝ) ≤ (r : ℝ) := by linarith
  have hr2 : 2 ≤ r := by
    have : (1 : ℝ) < (n : ℝ) ^ (1 / 10 : ℝ) := Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < n)) (by norm_num)
    have : (2 : ℝ) < (r : ℝ) := by linarith
    exact_mod_cast this.le
  have hr1 : 1 ≤ r := by omega
  have hr_le_n : r ≤ n := by
    have hden_ge1 : 1 ≤ Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) := by
      have h1 : 1 ≤ Real.log (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hlog1.le (by norm_num)
      have h2 : 1 ≤ Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ) := Real.one_le_rpow hloglog1.le (by norm_num)
      nlinarith
    have hpsi_le : psi ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1) := by
      dsimp only [psi]
      calc (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
            (Real.log (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log (n : ℝ)) ^ (2 / 3 : ℝ))
          ≤ (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) / 1 := by
            gcongr
        _ = (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) := div_one _
        _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1) := by
            gcongr
            exact totient_ratio_le_log hn2
    have hfl : (r : ℝ) ≤ c * psi := Nat.floor_le (by positivity)
    have : (r : ℝ) ≤ (n : ℝ) := hfl.trans ((mul_le_mul_of_nonneg_left hpsi_le hc.le).trans (by
      calc c * ((n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1))
          = c * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ) / Real.log 2 + 1) := by ring
        _ ≤ (n : ℝ) := hr_hi_cmp))
    exact_mod_cast this
  have hy_n4 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (y : ℝ) := h_35.trans hy35
  have hy1 : 1 ≤ y := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    exact_mod_cast this.trans hy35
  have hH1_y := hn1 r y hr_le_n hr_ge_10 hy_n4
  let S := n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime)
  let Y := (Finset.Ico y (2 * y)).filter (fun m ↦ ∃ u q : ℕ, m = q * u ∧ u ∣ n ∧
    (u : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ p ∈ S, ¬ p ∣ q)
  have hY_lo : ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / 8 ≤ (Y.card : ℝ) :=
    hH1_y.2 hr2y
  have htau_ge : (Real.log ((r : ℝ) + 30) ^ M₁)⁻¹ ≤ ((n : ℝ) / (n.totient : ℝ)) * tau :=
    (hprod_lo r).trans (tau_mul_totient_ge hn1_pos)
  have hr30_le_2n : (r : ℝ) + 30 ≤ 2 * (n : ℝ) := by
    have : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr_le_n
    have : (30 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn30
    linarith
  have hlog_r30_le : Real.log ((r : ℝ) + 30) ≤ 2 * Real.log (n : ℝ) := by
    have hr30_pos : 0 < (r : ℝ) + 30 := by positivity
    calc Real.log ((r : ℝ) + 30) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hr30_pos hr30_le_2n
      _ = Real.log 2 + Real.log (n : ℝ) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ Real.log (n : ℝ) + Real.log (n : ℝ) := by linarith [log_two_lt_one]
      _ = 2 * Real.log (n : ℝ) := by ring
  have hlog_r30_pos : 0 < Real.log ((r : ℝ) + 30) := by
    refine lt_of_lt_of_le (by linarith [log_thirty_gt_three] : 0 < Real.log 30) ?_
    exact Real.log_le_log (by norm_num) (by linarith [show (0 : ℝ) ≤ r by positivity])
  have hntau_ge : ((2 * Real.log (n : ℝ)) ^ M₁)⁻¹ ≤ ((n : ℝ) / (n.totient : ℝ)) * tau := by
    refine le_trans (inv_anti₀ (pow_pos hlog_r30_pos M₁) ?_) htau_ge
    exact pow_le_pow_left₀ hlog_r30_pos.le hlog_r30_le M₁
  have hy_r_ge_sqrt : (y : ℝ) ^ (1 / 2 : ℝ) ≤ (y : ℝ) / (r : ℝ) := by
    have hr_sq_r : (r : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by exact_mod_cast hr2y)
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr1
    have hsqrt_pos : 0 < (y : ℝ) ^ (1 / 2 : ℝ) := by positivity
    rw [le_div_iff₀ hr_pos]
    calc (y : ℝ) ^ (1 / 2 : ℝ) * (r : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ) * (y : ℝ) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = (y : ℝ) := by rw [← Real.rpow_add (by exact_mod_cast hy1)]; norm_num
  have hy_sqrt_ge : (n : ℝ) ^ (3 / 10 : ℝ) ≤ (y : ℝ) ^ (1 / 2 : ℝ) := by
    calc (n : ℝ) ^ (3 / 10 : ℝ) = ((n : ℝ) ^ (3 / 5 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]
          norm_num
      _ ≤ (y : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hy35 (by norm_num)
  have hz0_ge : (n : ℝ) ^ (3 / 10 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁ ≤
      ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
    have hntau_nn : 0 ≤ ((n : ℝ) / (n.totient : ℝ)) * tau := le_trans (by positivity) hntau_ge
    have h1 : ((2 * Real.log (n : ℝ)) ^ M₁)⁻¹ * (n : ℝ) ^ (3 / 10 : ℝ) ≤
        (((n : ℝ) / (n.totient : ℝ)) * tau) * ((y : ℝ) / (r : ℝ)) :=
      mul_le_mul hntau_ge (hy_sqrt_ge.trans hy_r_ge_sqrt) (by positivity) hntau_nn
    linarith [show ((2 * Real.log (n : ℝ)) ^ M₁)⁻¹ * (n : ℝ) ^ (3 / 10 : ℝ) =
        (n : ℝ) ^ (3 / 10 : ℝ) / (2 * Real.log (n : ℝ)) ^ M₁ by ring,
      show (((n : ℝ) / (n.totient : ℝ)) * tau) * ((y : ℝ) / (r : ℝ)) =
        ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) by ring]
  have hY_sub : Y ⊆ Finset.Icc 1 (n - 1) := by
    intro m hm
    dsimp only [Y] at hm
    have hm_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hP_sum : Y.card ≤ ∑ A ∈ P.parts, (A ∩ Y).card := by
    have hsub_u : Y ⊆ P.parts.biUnion (fun A ↦ A ∩ Y) := by
      intro m hm
      have hm_icc : m ∈ Finset.Icc 1 (n - 1) := hY_sub hm
      rw [← P.sup_parts] at hm_icc
      rw [Finset.sup_eq_biUnion, Finset.mem_biUnion] at hm_icc
      obtain ⟨A, hAP, hmA⟩ := hm_icc
      exact Finset.mem_biUnion.mpr ⟨A, hAP, Finset.mem_inter.mpr ⟨hmA, hm⟩⟩
    exact (Finset.card_le_card hsub_u).trans Finset.card_biUnion_le
  have hP_pos : 0 < P.parts.card := by
    by_contra h0
    have h0' : P.parts.card = 0 := by omega
    rw [Finset.card_eq_zero.mp h0'] at hP_sum
    simp only [Finset.sum_empty, Nat.le_zero] at hP_sum
    have hY_pos : 0 < (Y.card : ℝ) := by
      have hntau_pos : 0 < ((n : ℝ) / (n.totient : ℝ)) * tau :=
        lt_of_lt_of_le (by positivity) hntau_ge
      have hy_pos : (0 : ℝ) < y := by exact_mod_cast hy1
      have h8 : 0 < ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / 8 :=
        div_pos (mul_pos hntau_pos hy_pos) (by norm_num)
      linarith
    rw [hP_sum] at hY_pos
    simp at hY_pos
  have h_exists_A : ∃ A ∈ P.parts, (Y.card : ℝ) / (r : ℝ) ≤ ((A ∩ Y).card : ℝ) := by
    by_contra hno
    push Not at hno
    have hlt_sum : (∑ A ∈ P.parts, ((A ∩ Y).card : ℝ)) <
        ∑ _A ∈ P.parts, (Y.card : ℝ) / (r : ℝ) :=
      Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hP_pos) hno
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr1
    have hcard_r : (P.parts.card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hP_card
    have hle_Y : ∑ _A ∈ P.parts, (Y.card : ℝ) / (r : ℝ) ≤ (Y.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc (P.parts.card : ℝ) * ((Y.card : ℝ) / (r : ℝ))
          ≤ (r : ℝ) * ((Y.card : ℝ) / (r : ℝ)) := by gcongr
        _ = (Y.card : ℝ) := by field_simp [hr_pos.ne']
    have hsum_real : (Y.card : ℝ) ≤ ∑ A ∈ P.parts, ((A ∩ Y).card : ℝ) := by
      exact_mod_cast hP_sum
    linarith
  obtain ⟨A, hA_mem, hA_card⟩ := h_exists_A
  let m₀ := ⌈(1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)⌉₊
  have hm₀_le : m₀ ≤ (A ∩ Y).card := by
    apply Nat.ceil_le.mpr
    have h1 : (1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) ≤
        (Y.card : ℝ) / (r : ℝ) := by
      have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr1
      rw [div_le_div_iff_of_pos_right hr_pos]
      linarith
    exact h1.trans hA_card
  obtain ⟨Q₀, hQ₀_sub, hQ₀_card⟩ := Finset.exists_subset_card_eq hm₀_le
  let k := ⌈(y : ℝ) ^ (1 / 4 : ℝ)⌉₊
  have hk_le : (k : ℝ) ≤ (y : ℝ) ^ (1 / 4 : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hlog2y_le : (Nat.log 2 (2 * y) + 1 : ℝ) ≤ 2 * Real.log (n : ℝ) / Real.log 2 := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2pow : (2 : ℝ) ^ Nat.log 2 (2 * y) ≤ (2 * y : ℕ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2y_lt_n : ((2 * y : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 * y ≤ n)
    have hlog_n_ge : (Nat.log 2 (2 * y) : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (h2pow.trans h2y_lt_n)
    have h1 : (Nat.log 2 (2 * y) : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlog2_pos).mpr hlog_n_ge
    have h2 : 1 ≤ Real.log (n : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2_pos, one_mul]
      linarith [log_two_lt_one]
    have h12 : (Nat.log 2 (2 * y) : ℝ) + 1 ≤ 2 * (Real.log (n : ℝ) / Real.log 2) := by linarith
    linarith [show 2 * (Real.log (n : ℝ) / Real.log 2) = 2 * Real.log (n : ℝ) / Real.log 2 by ring]
  have hdiv_loss_le : ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1 ≤
      (1 / 40 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) :=
    div_loss_le hn1_pos hy1 hr1 hlog1 hy35 hk_le hlog2y_le hpoly_n hntau_ge hy_r_ge_sqrt
  have hQ₀_range : ∀ x ∈ Q₀, y ≤ x ∧ x < 2 * y := by
    intro x hx
    have hxY : x ∈ Y := (Finset.mem_inter.mp (hQ₀_sub hx)).2
    dsimp only [Y] at hxY
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hxY).1
  let X_qty : ℝ := ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)
  have hdiv_loss_X : ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1 ≤ (1 / 40 : ℝ) * X_qty := by
    convert hdiv_loss_le using 1
    dsimp only [X_qty]
    ring
  have hQ₀_card_big : (Nat.log 2 (2 * y) + 1) * k + 1 ≤ Q₀.card := by
    have h1 : ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1 ≤ (1 / 8 : ℝ) * X_qty := by
      have hnn : 0 ≤ X_qty := by
        have : (0 : ℝ) ≤ ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1 := by positivity
        linarith
      linarith
    have h2 : ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1 ≤ (Q₀.card : ℝ) := by
      rw [hQ₀_card]
      calc ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1
          ≤ (1 / 8 : ℝ) * X_qty := h1
        _ = (1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
            dsimp only [X_qty]; ring
        _ ≤ ⌈(1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)⌉₊ := Nat.le_ceil _
    exact_mod_cast h2
  obtain ⟨v, Q, hv1, hQ_lo_nat, hQ_hi_nat, hQ_mem, hQ_div⟩ :=
    diversity_extract Q₀ y k hy1 hQ₀_range hQ₀_card_big
  have hQ_ge_lo : (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) ≤
      (Q.card : ℝ) := by
    have h1 : (Q₀.card : ℝ) ≤ (Q.card : ℝ) + ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) := by
      exact_mod_cast hQ_lo_nat
    have h2 : (1 / 8 : ℝ) * X_qty ≤ (Q₀.card : ℝ) := by
      rw [hQ₀_card, show (1 / 8 : ℝ) * X_qty =
          (1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) by dsimp only [X_qty]; ring]
      exact Nat.le_ceil _
    have h3 : (1 / 10 : ℝ) * X_qty ≤ (Q.card : ℝ) := by linarith
    calc (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)
        = (1 / 10 : ℝ) * X_qty := by dsimp only [X_qty]; ring
      _ ≤ (Q.card : ℝ) := h3
  have hQ_le_hi : (Q.card : ℝ) ≤ (1 / 7 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
    have h1 : (Q.card : ℝ) ≤ (Q₀.card : ℝ) := by exact_mod_cast hQ_hi_nat
    have h2 : (Q₀.card : ℝ) < (1 / 8 : ℝ) * X_qty + 1 := by
      rw [hQ₀_card, show (1 / 8 : ℝ) * X_qty =
          (1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) by dsimp only [X_qty]; ring]
      exact Nat.ceil_lt_add_one (by
        have hnt_nn : 0 ≤ ((n : ℝ) / (n.totient : ℝ)) * tau := le_trans (by positivity) hntau_ge
        rw [show (1 / 8 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) =
            (1 / 8 : ℝ) * (((n : ℝ) / (n.totient : ℝ)) * tau) * (y : ℝ) / (r : ℝ) by ring]
        positivity)
    have hloss_ge3 : (3 : ℝ) ≤ ((Nat.log 2 (2 * y) + 1 : ℕ) : ℝ) * (k : ℝ) + 1 := by
      have hlog_ge1 : 1 ≤ Nat.log 2 (2 * y) := by
        rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
        omega
      have hk_ge1 : 1 ≤ k := Nat.ceil_pos.mpr (by positivity)
      have hnat3 : 3 ≤ (Nat.log 2 (2 * y) + 1) * k + 1 := by nlinarith
      exact_mod_cast hnat3
    have h3 : (1 : ℝ) ≤ (1 / 56 : ℝ) * X_qty := by linarith
    have h4 : (Q.card : ℝ) ≤ (1 / 7 : ℝ) * X_qty := by linarith
    calc (Q.card : ℝ) ≤ (1 / 7 : ℝ) * X_qty := h4
      _ = (1 / 7 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
          dsimp only [X_qty]; ring
  obtain ⟨hsmall_n4, hsmall_y⟩ := small_n4_and_y hn30 hr2 hr_le_n hlog1 hpoly_n hz0_ge
  have hH1_up := h1_up_adapter hr_le_n hr_ge_10 hn1
  have h_small_gcd : ∀ T : Finset ℕ, T ⊆ Q →
      64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) < (T.card : ℝ) →
      (v : ℝ) * ((T.gcd id : ℕ) : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) := by
    intro T hTQ hT_card
    let T' := T.image (fun x ↦ v * x)
    have hT'_inj : Set.InjOn (fun x ↦ v * x) (T : Set ℕ) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hv1 hab
    have hT'_card : T'.card = T.card := Finset.card_image_of_injOn hT'_inj
    have hT'_sub : ∀ m ∈ T', m ∈ Finset.Ico y (2 * y) ∧ ∃ u q : ℕ, m = q * u ∧ u ∣ n ∧
        (u : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ p ∈ S, ¬ p ∣ q := by
      intro m hm
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
      have hxQ₀ : v * x ∈ Q₀ := hQ_mem x (hTQ hx)
      have hxY : v * x ∈ Y := (Finset.mem_inter.mp (hQ₀_sub hxQ₀)).2
      dsimp only [Y] at hxY
      exact Finset.mem_filter.mp hxY
    have hw_dvd : ∀ m ∈ T', v * T.gcd id ∣ m := by
      intro m hm
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
      exact Nat.mul_dvd_mul_left v (Finset.gcd_dvd hx)
    have hres := div_by_divisors hn2 hr2 hr_le_n hy1 h2y (hpr_fn r hr_ge_10)
      hT'_sub hw_dvd hH1_up hsmall_n4 hsmall_y (by rwa [hT'_card])
    push_cast at hres
    exact hres.2
  have hv_le16 : (v : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) := by
    have hlogr_gt : 640 < Real.log (r : ℝ) := by
      have h1 : (1 / 10 : ℝ) * Real.log (n : ℝ) ≤ Real.log (r : ℝ) := by
        have h1' : Real.log ((n : ℝ) ^ (1 / 10 : ℝ)) ≤ Real.log (r : ℝ) :=
          Real.log_le_log (by positivity) hr_ge_10
        rwa [Real.log_rpow (by positivity)] at h1'
      exact lt_of_lt_of_le hlog640 h1
    have hpos_num : 0 < ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
      have : 0 < ((n : ℝ) / (n.totient : ℝ)) * tau := lt_of_lt_of_le (by positivity) hntau_ge
      positivity
    have hQ_big : 64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) <
        (Q.card : ℝ) := by
      have h64_lt : 64 / Real.log (r : ℝ) < 1 / 10 := by
        rw [div_lt_iff₀ (by linarith)]
        linarith
      calc 64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ))
          = (64 / Real.log (r : ℝ)) * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) := by ring
        _ < (1 / 10 : ℝ) * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) := by gcongr
        _ = (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by ring
        _ ≤ (Q.card : ℝ) := hQ_ge_lo
    have hres := h_small_gcd Q Finset.Subset.rfl hQ_big
    have hQ_pos : 0 < (Q.card : ℝ) := by
      have h1 : 0 < (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
        rw [show (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) =
            (1 / 10 : ℝ) * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) by ring]
        exact mul_pos (by norm_num) hpos_num
      exact lt_of_lt_of_le h1 hQ_ge_lo
    have hQ_ne : Q.Nonempty := Finset.card_pos.mp (by exact_mod_cast hQ_pos)
    have hgcd_pos : 1 ≤ Q.gcd id := by
      by_contra h0
      have h0' : Q.gcd id = 0 := by omega
      rw [Finset.gcd_eq_zero_iff] at h0'
      obtain ⟨x, hx⟩ := hQ_ne
      have hx0 : x = 0 := h0' x hx
      have hxY : v * x ∈ Y := (Finset.mem_inter.mp (hQ₀_sub (hQ_mem x hx))).2
      dsimp only [Y] at hxY
      have hx_ico := Finset.mem_Ico.mp (Finset.mem_filter.mp hxY).1
      rw [hx0, mul_zero] at hx_ico
      omega
    calc (v : ℝ) = (v : ℝ) * 1 := (mul_one _).symm
      _ ≤ (v : ℝ) * ((Q.gcd id : ℕ) : ℝ) := by gcongr; exact_mod_cast hgcd_pos
      _ ≤ (y : ℝ) ^ (1 / 16 : ℝ) := hres
  have hv_dvd_n : v ∣ n := by
    let Q' := Q.image (fun x ↦ v * x)
    have hQ'_inj : Set.InjOn (fun x ↦ v * x) (Q : Set ℕ) :=
      fun a _ b _ hab ↦ Nat.eq_of_mul_eq_mul_left hv1 hab
    have hQ'_card : Q'.card = Q.card := Finset.card_image_of_injOn hQ'_inj
    have hQ'_sub : ∀ m ∈ Q', m ∈ Finset.Ico y (2 * y) ∧ ∃ u q : ℕ, m = q * u ∧ u ∣ n ∧
        (u : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) ∧ ∀ p ∈ S, ¬ p ∣ q := by
      intro m hm
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
      have hxY : v * x ∈ Y := (Finset.mem_inter.mp (hQ₀_sub (hQ_mem x hx))).2
      dsimp only [Y] at hxY
      exact Finset.mem_filter.mp hxY
    have hw_dvd : ∀ m ∈ Q', v ∣ m := by
      intro m hm
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
      exact dvd_mul_right v x
    have hQ_big : 64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ)) <
        (Q'.card : ℝ) := by
      rw [hQ'_card]
      have hlogr_gt : 640 < Real.log (r : ℝ) := by
        have h1 : (1 / 10 : ℝ) * Real.log (n : ℝ) ≤ Real.log (r : ℝ) := by
          have h1' : Real.log ((n : ℝ) ^ (1 / 10 : ℝ)) ≤ Real.log (r : ℝ) :=
            Real.log_le_log (by positivity) hr_ge_10
          rwa [Real.log_rpow (by positivity)] at h1'
        exact lt_of_lt_of_le hlog640 h1
      have hpos_num : 0 < ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by
        have : 0 < ((n : ℝ) / (n.totient : ℝ)) * tau := lt_of_lt_of_le (by positivity) hntau_ge
        positivity
      have h64_lt : 64 / Real.log (r : ℝ) < 1 / 10 := by
        rw [div_lt_iff₀ (by linarith)]
        linarith
      calc 64 * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / ((r : ℝ) * Real.log (r : ℝ))
          = (64 / Real.log (r : ℝ)) * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) := by ring
        _ < (1 / 10 : ℝ) * (((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ)) := by gcongr
        _ = (1 / 10 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) * tau * (y : ℝ) / (r : ℝ) := by ring
        _ ≤ (Q.card : ℝ) := hQ_ge_lo
    exact (div_by_divisors hn2 hr2 hr_le_n hy1 h2y (hpr_fn r hr_ge_10)
      hQ'_sub hw_dvd hH1_up hsmall_n4 hsmall_y hQ_big).1
  have hQ_range : ∀ x ∈ Q, y ≤ v * x ∧ v * x < 2 * y := by
    intro x hx
    exact hQ₀_range (v * x) (hQ_mem x hx)
  have hQ_div_real : ∀ d : ℕ, 2 ≤ d →
      (y : ℝ) ^ (1 / 4 : ℝ) ≤ ((Q.filter (fun x ↦ ¬ d ∣ x)).card : ℝ) := by
    intro d hd
    have h1 : k ≤ (Q.filter (fun x ↦ ¬ d ∣ x)).card := hQ_div d hd
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hQ_ap : ∀ a b L : ℕ, 1 ≤ b → b ≤ n → (r : ℝ) ^ (1 / 16 : ℝ) ≤ (L : ℝ) →
      (((Finset.range L).filter (fun k ↦ a + b * k ∈ Q)).card : ℝ) ≤
        256 * (L : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (r : ℝ) := by
    intro a b L hb1 hbn hLr
    have hsel := hn2_ap r a b L hr_ge_10 hr_le_n hb1 hbn hLr
    let P_set := (Finset.range r).image (Nat.nth Nat.Prime) \ n.primeFactors
    have hsub_ap : (Finset.range L).filter (fun k ↦ a + b * k ∈ Q) ⊆
        (Finset.range L).filter (fun k ↦ ∀ p ∈ P_set, ¬ p ∣ a + b * k) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      refine ⟨hk.1, fun p hp hpd ↦ ?_⟩
      have hxY : v * (a + b * k) ∈ Y := (Finset.mem_inter.mp (hQ₀_sub (hQ_mem _ hk.2))).2
      dsimp only [Y] at hxY
      obtain ⟨u, q, hmul, hu_dvd, _, hq_cop⟩ := (Finset.mem_filter.mp hxY).2
      have hp_pr : p.Prime := by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.sdiff_subset hp)
        exact Nat.prime_nth_prime i
      have hp_not_n : ¬ p ∣ n := fun hdvd ↦
        (Finset.mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr ⟨hp_pr, hdvd, by omega⟩)
      have hp_mul : p ∣ q * u := hmul ▸ (hpd.trans (dvd_mul_left (a + b * k) v))
      rcases hp_pr.dvd_mul.mp hp_mul with hpq | hpu
      · exact hq_cop p (Finset.mem_union_right _ (Finset.sdiff_subset hp)) hpq
      · exact hp_not_n (hpu.trans hu_dvd)
    exact (by exact_mod_cast Finset.card_le_card hsub_ap : (((Finset.range L).filter (fun k ↦ a + b * k ∈ Q)).card : ℝ) ≤ _).trans hsel
  obtain ⟨V, hVQ, hVdisj, hVcard, hVS⟩ :=
    hn4 y r v Q rfl h2y hr2y hy35 hlow_y hhigh_y hv1 hv_le16 hQ_range hQ_ge_lo hQ_le_hi
      hQ_div_real h_small_gcd hQ_ap
  let S_sum : Fin ℓ → Finset ℕ := fun i ↦ (V i).powerset.image (fun B ↦ ∑ x ∈ B, x)
  let q_bound : ℕ := ⌊(y : ℝ) * (Q.card : ℝ) / (4 * (ℓ : ℝ) * (v : ℝ))⌋₊
  let m_bound : ℕ := ⌈(y : ℝ) * (Q.card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ))⌉₊
  obtain ⟨hm_ge_big, hq_ge1, h3q⟩ :=
    sumset_params_bounds hn1_pos hr1 (by omega : y ≤ n) hv1 hℓ8 h100l hhigh_y hv_le16 hQ_ge_lo
  have hS_card : ∀ i, m_bound ≤ (S_sum i).card := by
    intro i
    exact Nat.ceil_le.mpr (hVS i).1
  have hS_sub : ∀ i, ∃ a : ℕ, S_sum i ⊆ Finset.Icc a (a + q_bound) :=
    sumset_sub_Icc hv1 hVQ hVcard hQ_range
  have hS_noap : ∀ i, ∀ d : ℕ, 1 < d → ¬ (∀ x ∈ S_sum i, ∀ y' ∈ S_sum i, x % d = y' % d) :=
    fun i ↦ (hVS i).2
  obtain ⟨a, b, hab, hLev⟩ := h3 ℓ q_bound m_bound hℓ8 hq_ge1 (by omega) h3q S_sum hS_card hS_sub hS_noap
  let U : Finset ℕ := Finset.univ.biUnion V
  have hU_sub : U ⊆ Q := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hVQ i hxi
  have hI_sub : ∀ t ∈ Finset.Icc a b, t ∈ subsetSums (U : Set ℕ) := by
    intro t ht
    obtain ⟨f, hf_mem, rfl⟩ := hLev t ht
    choose B hBV hBsum using fun i ↦ Finset.mem_image.mp (hf_mem i)
    have hB_sub : ∀ i, B i ⊆ V i := fun i ↦ Finset.mem_powerset.mp (hBV i)
    have hB_disj : ((Finset.univ : Finset (Fin ℓ)) : Set (Fin ℓ)).PairwiseDisjoint B := by
      intro i _ j _ hij
      exact Disjoint.mono (hB_sub i) (hB_sub j) (hVdisj i j hij)
    refine ⟨Finset.univ.biUnion B, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_biUnion] at hx ⊢
      obtain ⟨i, _, hxi⟩ := hx
      exact ⟨i, Finset.mem_univ i, hB_sub i hxi⟩
    · rw [Finset.sum_biUnion hB_disj]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (hBsum i).symm
  let W : Finset ℕ := Q \ U
  have hUW : U ∪ W = Q := Finset.union_sdiff_of_subset hU_sub
  have hW_disj : Disjoint W U := disjoint_sdiff_self_left
  have hba_len : (2 * y) / v ≤ b - a :=
    ba_len_helper hv1 (by omega : 1 ≤ ℓ) hm_ge_big
      (Nat.le_ceil ((y : ℝ) * (Q.card : ℝ) / ((ℓ : ℝ) ^ 2 * (v : ℝ))))
      (q_card_ge_four_ell hn1_pos (by omega : 1 ≤ ℓ) hlog1 h100l hpoly_n hz0_ge hQ_ge_lo) hab
  have hW_bounds : ∀ x ∈ W, 1 ≤ x ∧ x ≤ b - a + 1 := by
    intro x hx
    have hxQ : x ∈ Q := (Finset.mem_sdiff.mp hx).1
    have hxr := hQ_range x hxQ
    have hx1 : 1 ≤ x := by
      by_contra h0
      have : x = 0 := by omega
      rw [this, mul_zero] at hxr
      omega
    have hxv : x ≤ (2 * y) / v := by
      rw [Nat.le_div_iff_mul_le hv1, mul_comm]
      exact hxr.2.le
    exact ⟨hx1, hxv.trans (Nat.le_succ_of_le hba_len)⟩
  have hQ_int := graham_interval a b U W (by omega) hI_sub hW_disj hW_bounds
  rw [hUW] at hQ_int
  obtain ⟨ha_le, hnv_le⟩ :=
    endpoints_helper hn1_pos hr1 hv1 (by omega : 1 ≤ ℓ) hv_dvd_n hVQ hVdisj hVcard hQ_range
      hQ_ge_lo hQ_le_hi hlow_y hhigh_y (by omega : a ≤ b)
      (hI_sub b (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
  obtain ⟨B, hBQ, hBsum⟩ := hQ_int (n / v) (Finset.mem_Icc.mpr ⟨ha_le, hnv_le⟩)
  refine ⟨A, hA_mem, B.image (fun x ↦ v * x), ?_, ?_⟩
  · intro m hm
    rw [Finset.mem_coe] at hm ⊢
    obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hm
    have hxQ : x ∈ Q := hBQ (Finset.mem_coe.mpr hxB)
    exact (Finset.mem_inter.mp (hQ₀_sub (hQ_mem x hxQ))).1
  · have hinj : Set.InjOn (fun x ↦ v * x) (B : Set ℕ) :=
      fun a _ b _ hab ↦ Nat.eq_of_mul_eq_mul_left hv1 hab
    rw [Finset.sum_image hinj, ← Finset.mul_sum, ← hBsum, Nat.mul_div_cancel' hv_dvd_n]

end OMA.R_Erdos360_erdos_360_R1_H4_R1
