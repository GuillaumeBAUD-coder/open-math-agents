import FormalConjectures.ErdosProblems.«357»
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Linear growth would give too many distinct consecutive sums below a common bound.
For each block length the number of available starting positions is proportional to its
reciprocal, and the resulting harmonic sums are unbounded. -/

-- Problem: Erdős Problem 357 — infinite set lower density
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/357.lean:122 (declaration Erdos357.erdos_357.variants.infinite_set_lower_density)
-- Credit: @dk8827 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Erdos357 Filter

namespace OMA.Erdos357

lemma eventually_linear_of_pos_lowerDensity {A : ℕ → ℕ} (hmono : StrictMono A)
    (hpos : 0 < (Set.range A).lowerDensity) :
    ∃ B N : ℕ, ∀ j ≥ N, A j ≤ B * (j + 1) := by
  let ε := (Set.range A).lowerDensity / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hlt : ε < (Set.range A).lowerDensity := by dsimp [ε]; linarith
  have he : ∀ᶠ n : ℕ in atTop, ε < (Set.range A).partialDensity Set.univ n :=
    eventually_lt_of_lt_liminf hlt
      (isBoundedUnder_of_eventually_ge (a := 0) (Filter.Eventually.of_forall fun _ => by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  obtain ⟨B, hB⟩ := exists_nat_gt ε⁻¹
  have hindex (j : ℕ) : j ≤ A j := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (hmono (Nat.lt_succ_self j)))
  refine ⟨B, N + 1, fun j hj => ?_⟩
  have hAj : N ≤ A j := by have := hindex j; omega
  have hp : 0 < (A j : ℝ) := by
    exact_mod_cast (by have := hindex j; omega : 0 < A j)
  have hrange : Set.range A ∩ Set.Iio (A j) = A '' Set.Iio j := by
    ext x
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hmono.lt_iff_lt.mp hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hmono hi⟩
  have hfrac := hN (A j) hAj
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, hrange,
    Set.ncard_image_of_injective _ hmono.injective, Set.ncard_Iio_nat] at hfrac
  have hprod := (lt_div_iff₀ hp).mp hfrac
  have hlinear : (A j : ℝ) ≤ (B : ℝ) * (j + 1 : ℕ) := by
    calc
      (A j : ℝ) ≤ (j : ℝ) / ε := (le_div_iff₀ hε).mpr (by linarith)
      _ = ε⁻¹ * j := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ (B : ℝ) * (j + 1 : ℕ) :=
        mul_le_mul hB.le (by exact_mod_cast Nat.le_succ j) (by positivity) (Nat.cast_nonneg B)
  exact_mod_cast hlinear

lemma unbounded_harmonic_quotients (B : ℕ) :
    ∃ m : ℕ, B * m.factorial < ∑ l ∈ Finset.Icc 1 m, m.factorial / l := by
  let m := ⌊Real.exp ((B : ℝ) + 1)⌋₊
  refine ⟨m, ?_⟩
  have hlog := log_le_harmonic_floor (Real.exp ((B : ℝ) + 1)) (Real.exp_pos _).le
  rw [Real.log_exp] at hlog
  have hB : (B : ℚ) < harmonic m := by
    have : (B : ℝ) < (harmonic m : ℝ) := by dsimp [m]; linarith
    exact_mod_cast this
  have hf : (0 : ℚ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hquot : (↑(∑ l ∈ Finset.Icc 1 m, m.factorial / l) : ℚ) =
      (m.factorial : ℚ) * harmonic m := by
    rw [harmonic_eq_sum_Icc, Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hp, hle⟩ := Finset.mem_Icc.mp hl
    rw [Rat.natCast_div _ _ (Nat.dvd_factorial (by omega) hle), div_eq_mul_inv]
  have hh : (B : ℚ) * m.factorial <
      (↑(∑ l ∈ Finset.Icc 1 m, m.factorial / l) : ℚ) := by
    rw [hquot, mul_comm (B : ℚ)]
    exact mul_lt_mul_of_pos_left hB hf
  exact_mod_cast hh

lemma interval_indices {r s a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (he : Finset.Ico r (r + a) = Finset.Ico s (s + b)) : r = s ∧ a = b := by
  have hfirst (u v k l : ℕ) (hk : 0 < k)
      (h : Finset.Ico u (u + k) = Finset.Ico v (v + l)) :
      v ≤ u ∧ u + k ≤ v + l := by
    have hleft : u ∈ Finset.Ico u (u + k) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hright : u + k - 1 ∈ Finset.Ico u (u + k) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    rw [h] at hleft hright
    exact ⟨(Finset.mem_Ico.mp hleft).1, by
      have := (Finset.mem_Ico.mp hright).2
      omega⟩
  have h₁ := hfirst r s a b ha he
  have h₂ := hfirst s r b a hb he.symm
  omega

lemma no_linear_growth {A : ℕ → ℕ} (hdistinct : HasDistinctSums A)
    {B N : ℕ} (hlinear : ∀ j ≥ N, A j ≤ B * (j + 1)) : False := by
  obtain ⟨m, hm⟩ := unbounded_harmonic_quotients B
  let D := m.factorial
  let t := B * (m * (N + m)) + 2
  let starts : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.Icc 1 m).sigma fun l => Finset.range (D / l * t)
  let block (p : Σ _ : ℕ, ℕ) := Finset.Ico (N + p.2) (N + p.2 + p.1)
  let value (p : Σ _ : ℕ, ℕ) := ∑ j ∈ block p, A j
  let limit := B * (D * t + m * (N + m)) + 1
  have hmem {p : Σ _ : ℕ, ℕ} (hp : p ∈ starts) :
      1 ≤ p.1 ∧ p.1 ≤ m ∧ p.2 < D / p.1 * t := by
    obtain ⟨hl, hj⟩ := Finset.mem_sigma.mp hp
    exact ⟨(Finset.mem_Icc.mp hl).1, (Finset.mem_Icc.mp hl).2, Finset.mem_range.mp hj⟩
  have hmap : Set.MapsTo value (starts : Set _) (Finset.range limit : Set ℕ) := by
    intro p hp
    obtain ⟨hl₁, hlm, hj⟩ := hmem hp
    have hdvd : p.1 ∣ D := Nat.dvd_factorial (by omega) hlm
    have hstart : p.1 * p.2 ≤ D * t := by
      calc
        _ ≤ p.1 * (D / p.1 * t) := Nat.mul_le_mul_left _ hj.le
        _ = _ := by rw [← Nat.mul_assoc, Nat.mul_div_cancel' hdvd]
    have hlen : p.1 * (N + p.2 + p.1) ≤ D * t + m * (N + m) := by
      calc
        _ = p.1 * p.2 + p.1 * (N + p.1) := by ring
        _ ≤ _ := Nat.add_le_add hstart (Nat.mul_le_mul hlm (by omega))
    change value p ∈ Finset.range limit
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    calc
      value p ≤ ∑ _j ∈ block p, B * (N + p.2 + p.1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        exact (hlinear j (by omega)).trans (Nat.mul_le_mul_left _ (by omega))
      _ = B * (p.1 * (N + p.2 + p.1)) := by
        simp [block, Nat.card_Ico, mul_left_comm]
      _ ≤ _ := Nat.mul_le_mul_left B hlen
  have hinj : (starts : Set _).InjOn value := by
    have hinterval (p : Σ _ : ℕ, ℕ) : (block p : Set ℕ).OrdConnected := by
      change ((Finset.Ico (N + p.2) (N + p.2 + p.1) : Finset ℕ) : Set ℕ).OrdConnected
      rw [Finset.coe_Ico]
      infer_instance
    intro p hp q hq he
    have hb : block p = block q := hdistinct (hinterval p) (hinterval q) he
    have h := interval_indices (by have := (hmem hp).1; omega)
      (by have := (hmem hq).1; omega) hb
    exact Sigma.ext h.2 (heq_of_eq (by omega : p.2 = q.2))
  have hcard := Finset.card_le_card_of_injOn value hmap hinj
  change ((Finset.Icc 1 m).sigma fun l => Finset.range (D / l * t)).card ≤
    (Finset.range limit).card at hcard
  simp only [Finset.card_sigma, Finset.card_range, ← Finset.sum_mul] at hcard
  have hsum : B * D + 1 ≤ ∑ l ∈ Finset.Icc 1 m, D / l := Nat.succ_le_of_lt hm
  have htooMany := Nat.mul_le_mul_right t hsum
  simp only [Nat.add_mul, one_mul] at htooMany
  have hlimit : limit = (B * D) * t + B * (m * (N + m)) + 1 := by
    dsimp only [limit]
    ring
  rw [hlimit] at hcard
  have ht : t = B * (m * (N + m)) + 2 := rfl
  omega

end OMA.Erdos357

theorem OMA.solution : type_of% @Erdos357.erdos_357.variants.infinite_set_lower_density := by
  intro A hmono hdistinct
  apply le_antisymm _ (Set.lowerDensity_nonneg _ _)
  by_contra! hpos
  obtain ⟨B, N, hlinear⟩ := OMA.Erdos357.eventually_linear_of_pos_lowerDensity hmono hpos
  exact OMA.Erdos357.no_linear_growth hdistinct hlinear
