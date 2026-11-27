import OMAReductions.R_Erdos344_erdos_344_variants_sqrt_two_R1
import Mathlib

-- Step Erdos344.erdos_344.variants.sqrt_two.R1.H1: hypothesis H1 of reduction Erdos344.erdos_344.variants.sqrt_two.R1
-- Credit: @ivillar

/-!
The increasing enumeration of the positive elements of `A` satisfies `2 a n ≤ n ^ 2 + 2`
eventually: with `N = (n ^ 2 + 2) / 2` there are more than `n` elements of `A` in `[1, N]`.
-/
open Filter Finset

namespace F2E344

theorem count_eq (A : Set ℕ) [DecidablePred fun n => n ∈ A ∧ 0 < n] (N : ℕ) :
    Nat.count (fun n => n ∈ A ∧ 0 < n) (N + 1) = A.countUpTo N := by
  rw [Nat.count_eq_card_filter_range, Set.countUpTo, ← Set.ncard_coe_finset]
  congr 1
  ext k
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h1, by omega⟩

theorem enum : ∀ A : Set ℕ, (∀ᶠ N : ℕ in atTop, Real.sqrt (2 * N) ≤ A.countUpTo N) →
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, a n ∈ A ∧ 0 < a n) ∧
      (∀ᶠ n : ℕ in atTop, 2 * a n ≤ n ^ 2 + 2) := by
  intro A hA
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hA
  have hinf : {n : ℕ | n ∈ A ∧ 0 < n}.Infinite := by
    intro hfin
    have h := hN₀ (max N₀ ({n : ℕ | n ∈ A ∧ 0 < n}.ncard ^ 2 + 1)) (le_max_left _ _)
    have hle : A.countUpTo (max N₀ ({n : ℕ | n ∈ A ∧ 0 < n}.ncard ^ 2 + 1)) ≤
        {n : ℕ | n ∈ A ∧ 0 < n}.ncard :=
      Set.ncard_le_ncard (fun k hk => ⟨hk.1, hk.2.1⟩) hfin
    have h1 : {n : ℕ | n ∈ A ∧ 0 < n}.ncard ^ 2 + 1 ≤
        max N₀ ({n : ℕ | n ∈ A ∧ 0 < n}.ncard ^ 2 + 1) := le_max_right _ _
    have h1' : (({n : ℕ | n ∈ A ∧ 0 < n}.ncard : ℝ)) ^ 2 + 1 ≤
        ((max N₀ ({n : ℕ | n ∈ A ∧ 0 < n}.ncard ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : (({n : ℕ | n ∈ A ∧ 0 < n}.ncard : ℝ)) <
        Real.sqrt (2 * ((max N₀ ({n : ℕ | n ∈ A ∧ 0 < n}.ncard ^ 2 + 1) : ℕ) : ℝ)) := by
      apply Real.lt_sqrt_of_sq_lt
      nlinarith [sq_nonneg (({n : ℕ | n ∈ A ∧ 0 < n}.ncard : ℝ))]
    have h3 : ((A.countUpTo (max N₀ ({n : ℕ | n ∈ A ∧ 0 < n}.ncard ^ 2 + 1)) : ℕ) : ℝ) ≤
        (({n : ℕ | n ∈ A ∧ 0 < n}.ncard : ℝ)) := by exact_mod_cast hle
    linarith
  refine ⟨Nat.nth (fun n => n ∈ A ∧ 0 < n), Nat.nth_strictMono hinf,
    fun n => Nat.nth_mem_of_infinite hinf n, ?_⟩
  refine eventually_atTop.mpr ⟨2 * N₀ + 2, fun n hn => ?_⟩
  have hsq : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have hN1 : n ^ 2 + 1 ≤ 2 * ((n ^ 2 + 2) / 2) := by omega
  have hN2 : 2 * ((n ^ 2 + 2) / 2) ≤ n ^ 2 + 2 := by omega
  have hNN : N₀ ≤ (n ^ 2 + 2) / 2 := by omega
  have hc := hN₀ _ hNN
  have hlt : (n : ℝ) < Real.sqrt (2 * (((n ^ 2 + 2) / 2 : ℕ) : ℝ)) := by
    apply Real.lt_sqrt_of_sq_lt
    have h : ((n ^ 2 + 1 : ℕ) : ℝ) ≤ ((2 * ((n ^ 2 + 2) / 2) : ℕ) : ℝ) := by exact_mod_cast hN1
    push_cast at h
    linarith
  have hcnt : n < A.countUpTo ((n ^ 2 + 2) / 2) := by exact_mod_cast lt_of_lt_of_le hlt hc
  rw [← count_eq] at hcnt
  have hnth := Nat.nth_lt_of_lt_count hcnt
  omega

end F2E344

theorem OMA.solution : OMA.R_Erdos344_erdos_344_variants_sqrt_two_R1.H1 :=
  F2E344.enum
