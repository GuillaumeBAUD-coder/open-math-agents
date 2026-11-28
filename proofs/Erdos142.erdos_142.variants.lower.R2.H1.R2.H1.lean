import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R2
import Mathlib

/-!
# Erdős 142, step `R2.H1.R2.H1`: shift covering from a divergent reciprocal sum

Write `N = 4 ^ j` and `B_j = {b ∈ [1, N] | 4 * N + b ∈ A}`. If `|B_j| * (j + 1) ^ 2 ≤ 2 * N` held for
all large `j`, the block of `A` at scale `j` would contribute at most `1 / (j + 1) - 1 / (j + 2)` to the
reciprocal sum, which would then converge. So arbitrarily large `j` have a dense slice `B_j`.

For such `j`, a greedy pigeonhole step finds a shift that covers at least a `|B_j| / (2 * N)` fraction of
the still uncovered part of `[1, N]`. After `q_j = (⌈log N⌉₊ + 1) ^ 4` steps at most
`N * (1 - |B_j| / (2 * N)) ^ q_j ≤ exp (log N - q_j * |B_j| / (2 * N)) < 1` points remain, so none do.
-/

namespace OMA_Erdos142_R2_H1_R2_H1_Cover

open Finset

/-- One greedy step: some shift `s` covers at least a `|B| / (2N)` fraction of `U`. -/
lemma greedy_step (N : ℕ) (hN : 0 < N) (B U : Finset ℕ) (hB : B ⊆ Icc 1 N)
    (hU : U ⊆ Icc 1 N) :
    ∃ s : ℕ, ((U.filter (fun x => ¬ ∃ b ∈ B, x + N = s + b)).card : ℝ) ≤
      (1 - (B.card : ℝ) / (2 * N)) * U.card := by
  classical
  have hx : ∀ x ∈ U,
      B.card ≤ ((range (2 * N)).filter (fun s => ∃ b ∈ B, x + N = s + b)).card := by
    intro x hxU
    have hxN := mem_Icc.mp (hU hxU)
    apply card_le_card_of_injOn (fun b => x + N - b)
    · intro b hb
      have hbN := mem_Icc.mp (hB (mem_coe.mp hb))
      rw [mem_coe, mem_filter, mem_range]
      dsimp only
      exact ⟨by omega, b, mem_coe.mp hb, by omega⟩
    · intro b1 hb1 b2 hb2 h
      have h1 := mem_Icc.mp (hB (mem_coe.mp hb1))
      have h2 := mem_Icc.mp (hB (mem_coe.mp hb2))
      simp only at h
      omega
  have hsum : U.card * B.card ≤
      ∑ s ∈ range (2 * N), (U.filter (fun x => ∃ b ∈ B, x + N = s + b)).card := by
    calc U.card * B.card = ∑ _x ∈ U, B.card := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ U, ((range (2 * N)).filter (fun s => ∃ b ∈ B, x + N = s + b)).card :=
          sum_le_sum hx
      _ = ∑ s ∈ range (2 * N), (U.filter (fun x => ∃ b ∈ B, x + N = s + b)).card := by
          simp only [card_filter]
          exact sum_comm
  obtain ⟨s, -, hs⟩ : ∃ s ∈ range (2 * N),
      U.card * B.card ≤ 2 * N * (U.filter (fun x => ∃ b ∈ B, x + N = s + b)).card := by
    apply exists_le_of_sum_le
    · exact ⟨0, mem_range.mpr (by omega)⟩
    · rw [sum_const, card_range, smul_eq_mul, ← mul_sum]
      exact Nat.mul_le_mul_left _ hsum
  refine ⟨s, ?_⟩
  have hsplit := card_filter_add_card_filter_not (s := U) (fun x => ∃ b ∈ B, x + N = s + b)
  have hsplit' : (((U.filter (fun x => ∃ b ∈ B, x + N = s + b)).card : ℕ) : ℝ) +
      ((U.filter (fun x => ¬ ∃ b ∈ B, x + N = s + b)).card : ℝ) = U.card := by
    exact_mod_cast hsplit
  have hs' : (U.card : ℝ) * B.card ≤
      2 * N * ((U.filter (fun x => ∃ b ∈ B, x + N = s + b)).card : ℝ) := by
    exact_mod_cast hs
  have hNpos : (0 : ℝ) < 2 * N := by positivity
  have hfrac : (B.card : ℝ) / (2 * N) * U.card ≤
      ((U.filter (fun x => ∃ b ∈ B, x + N = s + b)).card : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
    linarith
  rw [sub_mul, one_mul]
  linarith

/-- Iterating the greedy step `k` times. -/
lemma greedy_iter (N : ℕ) (hN : 0 < N) (B : Finset ℕ) (hB : B ⊆ Icc 1 N) :
    ∀ (k : ℕ) (U : Finset ℕ), U ⊆ Icc 1 N → ∃ s : Fin k → ℕ,
      ((U.filter (fun x => ¬ ∃ t : Fin k, ∃ b ∈ B, x + N = s t + b)).card : ℝ) ≤
        (1 - (B.card : ℝ) / (2 * N)) ^ k * U.card := by
  classical
  have hδ : 0 ≤ 1 - (B.card : ℝ) / (2 * N) := by
    have hBc : B.card ≤ N := by simpa using card_le_card hB
    have hBr : (B.card : ℝ) ≤ N := by exact_mod_cast hBc
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  intro k
  induction k with
  | zero =>
    intro U _
    refine ⟨Fin.elim0, ?_⟩
    simp
  | succ k ih =>
    intro U hU
    obtain ⟨s0, hs0⟩ := greedy_step N hN B U hB hU
    obtain ⟨s', hs'⟩ := ih (U.filter (fun x => ¬ ∃ b ∈ B, x + N = s0 + b))
      ((filter_subset _ _).trans hU)
    refine ⟨Fin.cons s0 s', ?_⟩
    have hsub : U.filter (fun x => ¬ ∃ t : Fin (k + 1), ∃ b ∈ B,
          x + N = (Fin.cons s0 s' : Fin (k + 1) → ℕ) t + b) ⊆
        (U.filter (fun x => ¬ ∃ b ∈ B, x + N = s0 + b)).filter
          (fun x => ¬ ∃ t : Fin k, ∃ b ∈ B, x + N = s' t + b) := by
      intro x hx
      rw [mem_filter] at hx
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hx.1, fun h => hx.2 ⟨0, by simpa using h⟩⟩, ?_⟩
      rintro ⟨t, ht⟩
      exact hx.2 ⟨t.succ, by simpa using ht⟩
    calc _ ≤ (((U.filter (fun x => ¬ ∃ b ∈ B, x + N = s0 + b)).filter
          (fun x => ¬ ∃ t : Fin k, ∃ b ∈ B, x + N = s' t + b)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ (1 - (B.card : ℝ) / (2 * N)) ^ k *
          ((U.filter (fun x => ¬ ∃ b ∈ B, x + N = s0 + b)).card : ℝ) := hs'
      _ ≤ (1 - (B.card : ℝ) / (2 * N)) ^ k *
          ((1 - (B.card : ℝ) / (2 * N)) * U.card) :=
          mul_le_mul_of_nonneg_left hs0 (pow_nonneg hδ k)
      _ = _ := by ring

/-- If `N (1 - |B| / (2N)) ^ q < 1`, then `q` shifts of `B` cover `[N + 1, 2N]`. -/
lemma shift_cover (N q : ℕ) (hN : 0 < N) (B : Finset ℕ) (hB : B ⊆ Icc 1 N)
    (h : (N : ℝ) * (1 - (B.card : ℝ) / (2 * N)) ^ q < 1) :
    ∃ s : Fin q → ℕ, ∀ x ∈ Icc 1 N, ∃ t : Fin q, ∃ b ∈ B, x + N = s t + b := by
  classical
  obtain ⟨s, hs⟩ := greedy_iter N hN B hB q (Icc 1 N) subset_rfl
  refine ⟨s, fun x hx => ?_⟩
  by_contra hcon
  have hpos : 0 < ((Icc 1 N).filter
      (fun x => ¬ ∃ t : Fin q, ∃ b ∈ B, x + N = s t + b)).card :=
    card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, hcon⟩⟩
  have hone : (1 : ℝ) ≤ ((Icc 1 N).filter
      (fun x => ¬ ∃ t : Fin q, ∃ b ∈ B, x + N = s t + b)).card := by
    exact_mod_cast hpos
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hs
  have hc := mul_comm ((1 - (B.card : ℝ) / (2 * N)) ^ q) (N : ℝ)
  linarith

/-- A large block slice makes `N (1 - m / (2N)) ^ q_j` smaller than `1`. -/
lemma analytic (N j m : ℕ) (hN : N = 4 ^ j) (hm : 2 * N < m * (j + 1) ^ 2) (hmN : m ≤ N) :
    (N : ℝ) * (1 - (m : ℝ) / (2 * N)) ^ ((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4) < 1 := by
  have hN0 : 0 < N := by rw [hN]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hL : Real.log (N : ℝ) = j * Real.log 4 := by
    rw [hN, Nat.cast_pow, Real.log_pow]
    norm_num
  have hLX : Real.log (N : ℝ) ≤ (⌈Real.log (N : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hjX : j ≤ ⌈Real.log (N : ℝ)⌉₊ := by
    have hj : (j : ℝ) ≤ (⌈Real.log (N : ℝ)⌉₊ : ℝ) := by
      calc (j : ℝ) ≤ j * Real.log 4 := le_mul_of_one_le_right (Nat.cast_nonneg j) hlog4
        _ = Real.log N := hL.symm
        _ ≤ _ := hLX
    exact_mod_cast hj
  have hnat : ⌈Real.log (N : ℝ)⌉₊ * (2 * N) < m * (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 := by
    have h1 : 2 * N < m * (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 2 :=
      lt_of_lt_of_le hm (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have h2 : ⌈Real.log (N : ℝ)⌉₊ < (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 2 := by nlinarith
    calc ⌈Real.log (N : ℝ)⌉₊ * (2 * N)
        ≤ ⌈Real.log (N : ℝ)⌉₊ * (m * (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 2) :=
          Nat.mul_le_mul_left _ h1.le
      _ < (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 2 * (m * (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 2) :=
          mul_lt_mul_of_pos_right h2 (lt_of_le_of_lt (Nat.zero_le _) h1)
      _ = m * (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 := by ring
  have hnatr : ((⌈Real.log (N : ℝ)⌉₊ * (2 * N) : ℕ) : ℝ) <
      ((m * (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hreal : Real.log (N : ℝ) * (2 * N) <
      (m : ℝ) * (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
    have hle : Real.log (N : ℝ) * (2 * N) ≤ (⌈Real.log (N : ℝ)⌉₊ : ℝ) * (2 * N) :=
      mul_le_mul_of_nonneg_right hLX (by positivity)
    have hcast : ((⌈Real.log (N : ℝ)⌉₊ * (2 * N) : ℕ) : ℝ) =
        (⌈Real.log (N : ℝ)⌉₊ : ℝ) * (2 * N) := by push_cast; ring
    have hcast2 : ((m * (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) =
        (m : ℝ) * (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, hcast2] at hnatr
    linarith
  have hδ0 : 0 ≤ 1 - (m : ℝ) / (2 * N) := by
    have hmr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have hδq : Real.log (N : ℝ) <
      (m : ℝ) / (2 * N) * (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    exact hreal
  calc (N : ℝ) * (1 - (m : ℝ) / (2 * N)) ^ ((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4)
      ≤ (N : ℝ) * (Real.exp (-((m : ℝ) / (2 * N)))) ^ ((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ hNr.le
        apply pow_le_pow_left₀ hδ0
        linarith [Real.add_one_le_exp (-((m : ℝ) / (2 * N)))]
    _ = Real.exp (Real.log (N : ℝ) +
          (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) * (-((m : ℝ) / (2 * N)))) := by
        rw [Real.exp_add, Real.exp_log hNr, Real.exp_nat_mul]
    _ < Real.exp 0 := by
        apply Real.exp_lt_exp.mpr
        nlinarith [hδq]
    _ = 1 := Real.exp_zero

/-- Each block of `A` lies in `[4 ^ (j + 1), 4 ^ (j + 2))`, and its reciprocal sum is at most
`|B_j| / (4 * 4 ^ j)`. -/
lemma block_sum (A : Set ℕ) (hA : ∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j)
    [DecidablePred (· ∈ A)] (j : ℕ) :
    ∑ n ∈ Ico (4 * 4 ^ j) (16 * 4 ^ j), A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n ≤
      (((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card : ℝ) *
        ((4 * 4 ^ j : ℕ) : ℝ)⁻¹ := by
  have hsub : Icc (4 * 4 ^ j + 1) (4 * 4 ^ j + 4 ^ j) ⊆ Ico (4 * 4 ^ j) (16 * 4 ^ j) := by
    intro n hn
    rw [mem_Icc] at hn
    rw [mem_Ico]
    constructor <;> omega
  rw [← sum_subset hsub]
  · rw [← map_add_left_Icc, sum_map]
    simp only [addLeftEmbedding_apply]
    calc ∑ b ∈ Icc 1 (4 ^ j), A.indicator (fun n : ℕ => (n : ℝ)⁻¹) (4 * 4 ^ j + b)
        ≤ ∑ b ∈ Icc 1 (4 ^ j), (if 4 * 4 ^ j + b ∈ A then ((4 * 4 ^ j : ℕ) : ℝ)⁻¹ else 0) := by
          apply sum_le_sum
          intro b _
          by_cases hb : 4 * 4 ^ j + b ∈ A
          · rw [Set.indicator_of_mem hb, if_pos hb]
            apply inv_anti₀ (by positivity)
            exact_mod_cast Nat.le_add_right _ _
          · rw [Set.indicator_of_notMem hb, if_neg hb]
      _ = ∑ _b ∈ (Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A),
          ((4 * 4 ^ j : ℕ) : ℝ)⁻¹ := by rw [sum_filter]
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  · intro n hn hn'
    apply Set.indicator_of_notMem
    intro hnA
    obtain ⟨i, hi1, hi2⟩ := hA n hnA
    rw [mem_Ico] at hn
    rw [mem_Icc] at hn'
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hp : 4 ^ (i + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hij
      rw [pow_succ] at hp
      omega
    · omega
    · have hp : 4 ^ (j + 1) ≤ 4 ^ i := Nat.pow_le_pow_right (by norm_num) hij
      rw [pow_succ] at hp
      omega

/-- Small block slices from some point on force a summable reciprocal sum. -/
lemma summable_of_small (A : Set ℕ) (hA : ∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j)
    [DecidablePred (· ∈ A)] (J : ℕ)
    (hsmall : ∀ j : ℕ, J ≤ j →
      ((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card * (j + 1) ^ 2 ≤ 2 * 4 ^ j) :
    Summable (A.indicator (fun n : ℕ => (n : ℝ)⁻¹)) := by
  have hf : ∀ n, 0 ≤ A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n :=
    fun n => Set.indicator_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)) n
  have hblock : ∀ j : ℕ, J ≤ j →
      ∑ n ∈ Ico (4 * 4 ^ j) (16 * 4 ^ j), A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n ≤
        ((j : ℝ) + 1)⁻¹ - ((j : ℝ) + 2)⁻¹ := by
    intro j hj
    refine (block_sum A hA j).trans ?_
    have hs := hsmall j hj
    have hnat : ((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card *
        ((j + 1) * (j + 2)) ≤ 4 * 4 ^ j := by
      have : (j + 1) * (j + 2) ≤ 2 * (j + 1) ^ 2 := by nlinarith
      calc _ ≤ ((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card *
            (2 * (j + 1) ^ 2) := Nat.mul_le_mul_left _ this
        _ = 2 * (((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card *
            (j + 1) ^ 2) := by ring
        _ ≤ 2 * (2 * 4 ^ j) := Nat.mul_le_mul_left _ hs
        _ = 4 * 4 ^ j := by ring
    have hreal : (((Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card : ℝ) *
        (((j : ℝ) + 1) * ((j : ℝ) + 2)) ≤ ((4 * 4 ^ j : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hid : ((j : ℝ) + 1)⁻¹ - ((j : ℝ) + 2)⁻¹ = 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      field_simp; ring
    rw [hid, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hT : ∀ k : ℕ,
      ∑ n ∈ range (4 * 4 ^ (J + k)), A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n +
          (((J + k : ℕ) : ℝ) + 1)⁻¹ ≤
        ∑ n ∈ range (4 * 4 ^ J), A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n + ((J : ℝ) + 1)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hpow : 4 * 4 ^ (J + (k + 1)) = 16 * 4 ^ (J + k) := by ring
      have hle : 4 * 4 ^ (J + k) ≤ 16 * 4 ^ (J + k) := by omega
      rw [hpow, ← sum_range_add_sum_Ico _ hle]
      have hb := hblock (J + k) (Nat.le_add_right J k)
      have hcast : (((J + (k + 1) : ℕ) : ℝ) + 1) = ((J + k : ℕ) : ℝ) + 2 := by
        push_cast; ring
      rw [hcast]
      linarith
  apply summable_of_sum_range_le hf (c := ∑ n ∈ range (4 * 4 ^ J),
    A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n + 1)
  intro K
  have hK : K ≤ 4 * 4 ^ (J + K) := by
    have h1 : K < 4 ^ K := Nat.lt_pow_self (by norm_num)
    have h2 : 4 ^ K ≤ 4 ^ (J + K) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left K J)
    omega
  have hmono : ∑ n ∈ range K, A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n ≤
      ∑ n ∈ range (4 * 4 ^ (J + K)), A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hK) (fun n _ _ => hf n)
  have hpos : (0 : ℝ) ≤ (((J + K : ℕ) : ℝ) + 1)⁻¹ := by positivity
  have hJ1 : ((J : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)])
  linarith [hT K]

end OMA_Erdos142_R2_H1_R2_H1_Cover

open OMA_Erdos142_R2_H1_R2_H1_Cover in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H1 := by
  classical
  intro A hA hns J
  by_contra hcon
  apply hns
  apply summable_of_small A hA J
  intro j hj
  by_contra hbig
  replace hbig := not_le.mp hbig
  apply hcon
  refine ⟨j, hj, ?_⟩
  have hBsub : (Finset.Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A) ⊆
      Finset.Icc 1 (4 ^ j) := Finset.filter_subset _ _
  have hmN : ((Finset.Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)).card ≤ 4 ^ j := by
    simpa using Finset.card_le_card hBsub
  obtain ⟨s, hs⟩ := shift_cover (4 ^ j) ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4)
    (by positivity) _ hBsub (analytic (4 ^ j) j _ rfl hbig hmN)
  refine ⟨s, fun x hx => ?_⟩
  obtain ⟨t, b, hb, he⟩ := hs x hx
  rw [Finset.mem_filter] at hb
  exact ⟨t, b, hb.1, hb.2, he⟩
