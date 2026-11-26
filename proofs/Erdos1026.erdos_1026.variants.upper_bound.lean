import FormalConjectures.ErdosProblems.«1026»

-- Problem: Erdős Problem 1026 — upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1026.lean:101 (declaration Erdos1026.erdos_1026.variants.upper_bound)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea (Cambie-type construction): for n = k*k take k blocks of length k, each block
-- decreasing, the blocks increasing, all values in [M, M + k*k) with M huge. Every monotone
-- subsequence has at most k terms, so its sum is at most k*(M + k*k), while the total sum is
-- at least k*k*M. This rules out every constant c > 1.

namespace OMA.O5

open Erdos1026 Filter

/-- Position value of index `i`: block `i / k` increasing, decreasing inside a block. -/
def v (k : ℕ) (i : ℕ) : ℕ := k * (i / k) + (k - 1 - i % k)

lemma v_lt_of_same (k i j : ℕ) (hk : 0 < k) (hij : i < j) (hq : i / k = j / k) :
    v k j < v k i := by
  unfold v
  have h1 := Nat.div_add_mod i k
  have h2 := Nat.div_add_mod j k
  have h3 := Nat.mod_lt i hk
  have h4 := Nat.mod_lt j hk
  rw [hq] at h1 ⊢
  generalize k * (j / k) = A at *
  generalize i % k = a at *
  generalize j % k = b at *
  omega

lemma v_lt_of_lt (k i j : ℕ) (hk : 0 < k) (hq : i / k < j / k) : v k i < v k j := by
  unfold v
  have h5 : k * (i / k + 1) ≤ k * (j / k) := Nat.mul_le_mul_left k hq
  rw [mul_add, mul_one] at h5
  have h3 := Nat.mod_lt i hk
  generalize k * (i / k) = A at *
  generalize k * (j / k) = B at *
  generalize i % k = a at *
  generalize j % k = b at *
  omega

lemma v_lt (k i : ℕ) (hk : 0 < k) (hi : i < k * k) : v k i < k * k := by
  unfold v
  have hq : i / k < k := Nat.div_lt_of_lt_mul hi
  have h5 : k * (i / k + 1) ≤ k * k := Nat.mul_le_mul_left k hq
  rw [mul_add, mul_one] at h5
  have h6 : k - 1 - i % k ≤ k - 1 := Nat.sub_le _ _
  generalize k * (i / k) = A at *
  generalize k - 1 - i % k = B at *
  generalize k * k = C at *
  omega

lemma v_inj (k i j : ℕ) (hk : 0 < k) (h : v k i = v k j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exfalso
    have hq : i / k ≤ j / k := Nat.div_le_div_right hij.le
    rcases hq.lt_or_eq with hq | hq
    · exact absurd h (v_lt_of_lt k i j hk hq).ne
    · exact absurd h (v_lt_of_same k i j hk hij hq).ne'
  · exact hij
  · exfalso
    have hq : j / k ≤ i / k := Nat.div_le_div_right hij.le
    rcases hq.lt_or_eq with hq | hq
    · exact absurd h (v_lt_of_lt k j i hk hq).ne'
    · exact absurd h (v_lt_of_same k j i hk hij hq).ne

/-- The sequence. -/
noncomputable def x (k : ℕ) (M : ℝ) : Fin (k * k) → ℝ := fun i => M + ((v k i : ℕ) : ℝ)

lemma card_le (k : ℕ) (hk : 0 < k) (M : ℝ) (I : Finset (Fin (k * k)))
    (hI : MonotoneOn (x k M) ↑I ∨ AntitoneOn (x k M) ↑I) : I.card ≤ k := by
  rcases hI with hI | hI
  · have : I.card ≤ (Finset.range k).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin (k * k) => (i : ℕ) / k)
      · intro i hi
        simpa using Nat.div_lt_of_lt_mul i.isLt
      · intro i hi j hj hij
        simp only at hij
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have h1 := hI hi hj h.le
          have h2 := v_lt_of_same k i j hk (Fin.lt_def.mp h) hij
          simp only [x] at h1
          have : ((v k j : ℕ) : ℝ) < ((v k i : ℕ) : ℝ) := by exact_mod_cast h2
          linarith
        · have h1 := hI hj hi h.le
          have h2 := v_lt_of_same k j i hk (Fin.lt_def.mp h) hij.symm
          simp only [x] at h1
          have : ((v k i : ℕ) : ℝ) < ((v k j : ℕ) : ℝ) := by exact_mod_cast h2
          linarith
    simpa using this
  · have key : ∀ i ∈ I, ∀ j ∈ I, i < j → (i : ℕ) / k = (j : ℕ) / k := by
      intro i hi j hj h
      have hle : (i : ℕ) / k ≤ (j : ℕ) / k :=
        Nat.div_le_div_right (Fin.lt_def.mp h).le
      rcases hle.lt_or_eq with hq | hq
      · exfalso
        have h1 := hI hi hj h.le
        have h2 := v_lt_of_lt k i j hk hq
        simp only [x] at h1
        have : ((v k i : ℕ) : ℝ) < ((v k j : ℕ) : ℝ) := by exact_mod_cast h2
        linarith
      · exact hq
    have hsame : ∀ i ∈ I, ∀ j ∈ I, (i : ℕ) / k = (j : ℕ) / k := by
      intro i hi j hj
      rcases lt_trichotomy i j with h | h | h
      · exact key i hi j hj h
      · rw [h]
      · exact (key j hj i hi h).symm
    have : I.card ≤ (Finset.range k).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin (k * k) => (i : ℕ) % k)
      · intro i hi
        simpa using Nat.mod_lt (i : ℕ) hk
      · intro i hi j hj hij
        simp only at hij
        have hq := hsame i hi j hj
        apply Fin.ext
        rw [← Nat.div_add_mod (i : ℕ) k, ← Nat.div_add_mod (j : ℕ) k, hq, hij]
    simpa using this

end OMA.O5

open OMA.O5 in
theorem OMA.solution : type_of% @Erdos1026.erdos_1026.variants.upper_bound := by
  rw [mem_upperBounds]
  intro c hc
  simp only [Erdos1026.admissibleConstants, Set.mem_setOf_eq] at hc
  by_contra hlt
  push_neg at hlt
  set ε : ℝ := (c - 1) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hce : c - ε = 1 + ε := by rw [hε_def]; ring
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hc ε hε)
  set k : ℕ := N + 1 with hk_def
  have hk : 0 < k := Nat.succ_pos N
  have hkN : N ≤ k * k := by nlinarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set M : ℝ := (k : ℝ) * k / ε + 1 with hM_def
  have hMε : ε * M = k * k + ε := by rw [hM_def]; field_simp
  have hM : 0 < M := by positivity
  have hinj : Function.Injective (x k M) := by
    intro i j h
    simp only [x, add_right_inj, Nat.cast_inj] at h
    exact Fin.ext (v_inj k i j hk h)
  have hpos : ∀ i, 0 < x k M i := by
    intro i
    simp only [x]
    positivity
  obtain ⟨S, ⟨I, hI, rfl⟩, hS⟩ := hN (k * k) hkN (x k M) hinj hpos
  have hsq : Real.sqrt (((k * k : ℕ) : ℝ)) = k := by
    push_cast
    exact Real.sqrt_mul_self hkR.le
  rw [hsq, hce] at hS
  have hT : (k : ℝ) * k * M ≤ ∑ i, x k M i := by
    have : ∑ _i : Fin (k * k), M ≤ ∑ i, x k M i := by
      apply Finset.sum_le_sum
      intro i _
      simp only [x]
      have := (v k i).cast_nonneg (α := ℝ)
      linarith
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hU : ∑ i ∈ I, x k M i ≤ k * (M + k * k) := by
    have h1 : ∑ i ∈ I, x k M i ≤ ∑ _i ∈ I, (M + (k : ℝ) * k) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [x]
      have h2 := v_lt k i hk i.isLt
      have : ((v k i : ℕ) : ℝ) < (k : ℝ) * k := by exact_mod_cast h2
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hc2 := card_le k hk M I hI
    have : (I.card : ℝ) ≤ k := by exact_mod_cast hc2
    have hpos2 : (0 : ℝ) ≤ M + k * k := by positivity
    have := mul_le_mul_of_nonneg_right this hpos2
    linarith
  have h2 : (1 + ε) * k * M ≤ (1 + ε) / k * ∑ i, x k M i := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hkR]
    have := mul_le_mul_of_nonneg_left hT (le_of_lt (by linarith : (0 : ℝ) < 1 + ε))
    nlinarith [this]
  have h3 : ε * M * k = (k * k + ε) * k := by rw [hMε]
  nlinarith [mul_pos hkR hε, h3, h2, hS, hU]
