import OMAReductions.R_Erdos295_erdos_295_variants_erdos_straus_R1

-- Step Erdos295.erdos_295.variants.erdos_straus.R1.H1: hypothesis H1 of reduction Erdos295.erdos_295.variants.erdos_straus.R1
-- Credit: @mrmario2202

open Filter

namespace OMAH1

/-- `1/x ≤ log x - log (x - 1)` for `x > 1`. -/
lemma inv_le_log_sub (x : ℝ) (hx : 1 < x) : 1 / x ≤ Real.log x - Real.log (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (x - 1) / x by positivity)
  rw [Real.log_div hx1.ne' hx0.ne'] at h
  have : (x - 1) / x - 1 = -(1 / x) := by field_simp; ring
  linarith

/-- A strictly monotone `Fin m → ℕ` bounded below by `N` satisfies `N + i ≤ n i`. -/
lemma add_le_of_strictMono {m N : ℕ} (n : Fin m → ℕ) (hn : ∀ i, N ≤ n i) (hmono : StrictMono n) :
    ∀ i : Fin m, N + i ≤ n i := by
  intro ⟨j, hj⟩
  induction j with
  | zero => simpa using hn ⟨0, hj⟩
  | succ j ih =>
    have h1 := ih (by omega)
    have h2 : n ⟨j, by omega⟩ < n ⟨j + 1, hj⟩ := hmono (Fin.mk_lt_mk.mpr (by omega))
    simp only at h1 ⊢
    omega

/-- Telescoping: `∑_{j<m} 1/(N+j) ≤ log (N - 1 + m) - log (N - 1)` for `N ≥ 2`. -/
lemma harmonic_le_log (N : ℕ) (hN : 2 ≤ N) (m : ℕ) :
    ∑ j ∈ Finset.range m, (1 / ((N : ℝ) + j)) ≤
      Real.log ((N : ℝ) - 1 + m) - Real.log ((N : ℝ) - 1) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have key : ∀ j ∈ Finset.range m, (1 / ((N : ℝ) + j)) ≤
      Real.log ((N : ℝ) - 1 + (j + 1 : ℕ)) - Real.log ((N : ℝ) - 1 + j) := by
    intro j _
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have := inv_le_log_sub ((N : ℝ) + j) (by linarith)
    have e1 : (N : ℝ) - 1 + ((j + 1 : ℕ) : ℝ) = (N : ℝ) + j := by push_cast; ring
    have e2 : (N : ℝ) - 1 + j = (N : ℝ) + j - 1 := by ring
    rw [e1, e2]
    exact this
  calc ∑ j ∈ Finset.range m, (1 / ((N : ℝ) + j))
      ≤ ∑ j ∈ Finset.range m,
          (Real.log ((N : ℝ) - 1 + (j + 1 : ℕ)) - Real.log ((N : ℝ) - 1 + j)) :=
        Finset.sum_le_sum key
    _ = Real.log ((N : ℝ) - 1 + m) - Real.log ((N : ℝ) - 1) := by
        rw [Finset.sum_range_sub (fun j : ℕ => Real.log ((N : ℝ) - 1 + j))]
        simp

theorem lower :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ (m : ℕ) (n : Fin m → ℕ),
      (∀ i, N ≤ n i) → StrictMono n → ∑ i, (1 / n i : ℝ) = 1 →
        (Real.exp 1 - 1) * N - C < m := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with N hN m n hn hmono hsum
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hadd := add_le_of_strictMono n hn hmono
  -- 1 ≤ ∑_{j<m} 1/(N+j)
  have h1 : (1 : ℝ) ≤ ∑ j ∈ Finset.range m, (1 / ((N : ℝ) + j)) := by
    calc (1 : ℝ) = ∑ i, (1 / n i : ℝ) := hsum.symm
      _ ≤ ∑ i : Fin m, (1 / ((N : ℝ) + (i : ℕ))) := by
          apply Finset.sum_le_sum
          intro i _
          have hpos : (0 : ℝ) < (N : ℝ) + (i : ℕ) := by positivity
          apply one_div_le_one_div_of_le hpos
          exact_mod_cast hadd i
      _ = ∑ j ∈ Finset.range m, (1 / ((N : ℝ) + j)) :=
          (Finset.sum_range (fun j => 1 / ((N : ℝ) + j))).symm
  have h2 := harmonic_le_log N hN m
  set A : ℝ := (N : ℝ) - 1 with hA
  have hA1 : 1 ≤ A := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlog : 1 ≤ Real.log ((A + m) / A) := by
    rw [Real.log_div (by linarith) (by linarith)]
    linarith
  have hexp : Real.exp 1 ≤ (A + m) / A := by
    calc Real.exp 1 ≤ Real.exp (Real.log ((A + m) / A)) := Real.exp_le_exp.mpr hlog
      _ = (A + m) / A := Real.exp_log (by positivity)
  have hmul : Real.exp 1 * A ≤ A + m := by
    rwa [le_div_iff₀ (by linarith)] at hexp
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have : (Real.exp 1 - 1) * N = (Real.exp 1 - 1) * A + (Real.exp 1 - 1) := by rw [hA]; ring
  rw [this]
  linarith

end OMAH1

theorem OMA.solution : OMA.R_Erdos295_erdos_295_variants_erdos_straus_R1.H1 :=
  OMAH1.lower
