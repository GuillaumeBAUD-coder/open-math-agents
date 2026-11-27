import FormalConjectures.ErdosProblems.«161»

-- Reduction Erdos161.erdos_161.parts.ii.R2 of Erdős Problem 161 — ii
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Write `L(n) = (log n)^(1/(t-1))`. The target compares the balanced-colouring thresholds
`F_t(n, α)` and `F_t(n, β)`. We reduce it to two explicit bounds at the common scale `L(n)`:

* `H1` (upper bound, the classical random-colouring estimate): for every `t ≥ 3` and
  `α ∈ (0, 1/2)` there is a colouring of the `t`-subsets of `Fin n` in which every vertex set of
  size at least `C L(n)` sees both colours, each on at least an `α`-fraction of its `t`-subsets.
* `H2` (matching lower bound, the open core; CFS11 for `t = 3`): for every `t ≥ 3` and
  `ρ ∈ (0, 1/2)`, every colouring has a set of size at least `c L(n)` in which some colour
  covers fewer than a `ρ`-fraction of its `t`-subsets.

Then both thresholds are `Θ(L)`, hence `Θ` of each other.
-/

namespace OMA.R_Erdos161_erdos_161_parts_ii_R2

open Filter Asymptotics Finset

private lemma threshold_feasible (n t : ℕ) (α : ℝ) :
    ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n),
      Hypergraph.balancedColoringThreshold n t α ≤ X.card →
      ∀ b : Bool, 0 < ((X.powersetCard t).filter (fun e ↦ c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤ ((X.powersetCard t).filter (fun e ↦ c e = b)).card := by
  classical
  unfold Hypergraph.balancedColoringThreshold
  have := Nat.sInf_mem (s := {m | ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool, let count := ((X.powersetCard t).filter (fun e ↦ c e = b)).card
    0 < count ∧ α * (X.card.choose t : ℝ) ≤ count}) ⟨n + 1, fun _ ↦ false, fun X hX ↦ by
      have hcard : X.card ≤ n := by simpa using Finset.card_le_univ X
      omega⟩
  obtain ⟨c, hc⟩ := this
  refine ⟨c, fun X hX b ↦ ?_⟩
  have h := hc X hX b
  simp only at h
  convert h using 3

private lemma threshold_le_of_feasible {n t m : ℕ} {α : ℝ}
    (h : ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
      ∀ b : Bool, 0 < ((X.powersetCard t).filter (fun e ↦ c e = b)).card ∧
        α * (X.card.choose t : ℝ) ≤ ((X.powersetCard t).filter (fun e ↦ c e = b)).card) :
    Hypergraph.balancedColoringThreshold n t α ≤ m := by
  classical
  unfold Hypergraph.balancedColoringThreshold
  apply Nat.sInf_le
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun X hX b ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hc X hX b
  simp only
  constructor
  · convert h1 using 2
  · convert h2 using 3

/-- Upper bound from a colouring that is balanced on all sets of size at least `C L(n)`. -/
private lemma threshold_upper {t : ℕ} {α : ℝ} (ht : 3 ≤ t)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ col : Finset (Fin n) → Bool,
      ∀ X : Finset (Fin n), C * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) ≤ (X.card : ℝ) →
        ∀ b : Bool, 0 < ((X.powersetCard t).filter (fun e ↦ col e = b)).card ∧
          α * (X.card.choose t : ℝ) ≤ ((X.powersetCard t).filter (fun e ↦ col e = b)).card) :
    (fun n ↦ (Hypergraph.balancedColoringThreshold n t α : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (Real.log n) ^ (((t : ℝ) - 1)⁻¹)) := by
  obtain ⟨C, hC⟩ := h
  apply IsBigO.of_bound (|C| + 1)
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have h3 : Real.exp 1 ≤ (n : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]
    exact h3
  filter_upwards [hC, hlog] with n ⟨col, hcol⟩ hn
  set L := (Real.log n) ^ (((t : ℝ) - 1)⁻¹)
  have ht' : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 1 ≤ L := Real.one_le_rpow hn (inv_nonneg.mpr (by linarith))
  have hle : Hypergraph.balancedColoringThreshold n t α ≤ ⌈C * L⌉₊ := by
    apply threshold_le_of_feasible
    refine ⟨col, fun X hX b ↦ hcol X ?_ b⟩
    exact (Nat.le_ceil _).trans (by exact_mod_cast hX)
  have hceil : (⌈C * L⌉₊ : ℝ) ≤ |C| * L + 1 := by
    rcases le_or_gt (C * L) 0 with h0 | h0
    · rw [Nat.ceil_eq_zero.mpr h0]
      simp only [Nat.cast_zero]
      positivity
    · have := Nat.ceil_lt_add_one h0.le
      have : C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      linarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by linarith)]
  calc (Hypergraph.balancedColoringThreshold n t α : ℝ) ≤ ⌈C * L⌉₊ := by exact_mod_cast hle
    _ ≤ |C| * L + 1 := hceil
    _ ≤ (|C| + 1) * L := by nlinarith [abs_nonneg C]

/-- Lower bound from an unbalanced set of size at least `c L(n)` in every colouring. -/
private lemma threshold_lower {t : ℕ} {ρ : ℝ}
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ col : Finset (Fin n) → Bool,
      ∃ X : Finset (Fin n), c * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) ≤ (X.card : ℝ) ∧
        ∃ b : Bool, (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) <
          ρ * (X.card.choose t : ℝ)) :
    (fun n : ℕ ↦ (Real.log n) ^ (((t : ℝ) - 1)⁻¹)) =O[atTop]
      (fun n ↦ (Hypergraph.balancedColoringThreshold n t ρ : ℝ)) := by
  obtain ⟨c, hc, hev⟩ := h
  apply IsBigO.of_bound c⁻¹
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  obtain ⟨col, hcol⟩ := threshold_feasible n t ρ
  obtain ⟨X, hX, b, hb⟩ := hn col
  have hlt : X.card < Hypergraph.balancedColoringThreshold n t ρ := by
    by_contra! hge
    exact absurd (hcol X hge b).2 (not_le.mpr hb)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hL : 0 ≤ (Real.log n) ^ (((t : ℝ) - 1)⁻¹) := Real.rpow_nonneg hlog _
  rw [Real.norm_of_nonneg hL, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have h2 : c * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) ≤
      (Hypergraph.balancedColoringThreshold n t ρ : ℝ) :=
    hX.trans (by exact_mod_cast hlt.le)
  rw [le_inv_mul_iff₀ hc]
  exact h2

/-- Upper bound: the random-colouring estimate at scale `(log n)^(1/(t-1))`. -/
def H1 : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ col : Finset (Fin n) → Bool,
      ∀ X : Finset (Fin n), C * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) ≤ (X.card : ℝ) →
        ∀ b : Bool, 0 < ((X.powersetCard t).filter (fun e ↦ col e = b)).card ∧
          α * (X.card.choose t : ℝ) ≤ ((X.powersetCard t).filter (fun e ↦ col e = b)).card

/-- Lower bound: every colouring has an unbalanced set of size `Ω((log n)^(1/(t-1)))`. -/
def H2 : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ col : Finset (Fin n) → Bool,
      ∃ X : Finset (Fin n), c * (Real.log n) ^ (((t : ℝ) - 1)⁻¹) ≤ (X.card : ℝ) ∧
        ∃ b : Bool, (((X.powersetCard t).filter (fun e ↦ col e = b)).card : ℝ) <
          ρ * (X.card.choose t : ℝ)

theorem main : H1 → H2 → type_of% @Erdos161.erdos_161.parts.ii := by
  intro h1 h2 t ht α β hα0 hα1 hβ0 hβ1
  exact ⟨(threshold_upper ht (h1 t ht α hα0 hα1)).trans (threshold_lower (h2 t ht β hβ0 hβ1)),
    (threshold_upper ht (h1 t ht β hβ0 hβ1)).trans (threshold_lower (h2 t ht α hα0 hα1))⟩

end OMA.R_Erdos161_erdos_161_parts_ii_R2
