import FormalConjectures.ErdosProblems.«285»

-- Problem: Erdős Problem 285 — trivial lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/285.lean (declaration Erdos285.erdos_285.variants.lb)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA285

open Finset

lemma log_le_sum (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    Real.log (((m : ℝ) + k + 1) / m) ≤ ∑ i ∈ range (k + 1), 1 / ((m : ℝ) + i) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  induction k with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, Nat.cast_zero, add_zero]
    have := Real.log_le_sub_one_of_pos (x := ((m : ℝ) + 1) / m) (by positivity)
    have e : ((m : ℝ) + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  | succ k ih =>
    rw [sum_range_succ]
    have h1 : ((m : ℝ) + ((k + 1 : ℕ) : ℝ) + 1) / m =
        (((m : ℝ) + k + 1) / m) * (((m : ℝ) + k + 2) / ((m : ℝ) + k + 1)) := by
      push_cast
      field_simp
      ring
    rw [h1, Real.log_mul (by positivity) (by positivity)]
    have h2 := Real.log_le_sub_one_of_pos (x := ((m : ℝ) + k + 2) / ((m : ℝ) + k + 1))
      (by positivity)
    have e : ((m : ℝ) + k + 2) / ((m : ℝ) + k + 1) - 1 = 1 / ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      ring
    linarith

/-- Strictly increasing maps on `Fin (k+1)` grow by at least one per step. -/
lemma mono_gap {k : ℕ} (n : Fin (k + 1) → ℕ) (hn : StrictMono n) :
    ∀ d : ℕ, ∀ i : Fin (k + 1), ∀ h : i.val + d < k + 1, n i + d ≤ n ⟨i.val + d, h⟩ := by
  intro d
  induction d with
  | zero => intro i h; simp
  | succ d ih =>
    intro i h
    have h' : i.val + d < k + 1 := by omega
    have := ih i h'
    have hlt : n ⟨i.val + d, h'⟩ < n ⟨i.val + (d + 1), h⟩ := by
      apply hn
      rw [Fin.lt_def]
      simp
    omega

end OMA285

theorem OMA.solution : type_of% @Erdos285.erdos_285.variants.lb := by
  intro f S hS h
  refine ⟨fun k => -(1 / ((k : ℝ) + 1)), ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ => (1 : ℝ) from rfl, Asymptotics.isLittleO_one_iff]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    simpa using this
  · intro k hk
    obtain ⟨n, hn, h0, hsum, hF⟩ := (h k hk).1
    set F := f k
    have hpos : ∀ i, 1 ≤ n i := by
      intro i
      rcases Nat.eq_zero_or_pos (n i) with h' | h'
      · exact absurd ⟨i, h'⟩ h0
      · exact h'
    -- n i + (k - i) ≤ F
    have hgap : ∀ i : Fin (k + 1), n i + (k - i.val) ≤ F := by
      intro i
      have hi := i.isLt
      have := OMA285.mono_gap n hn (k - i.val) i (by omega)
      have e : (⟨i.val + (k - i.val), by omega⟩ : Fin (k + 1)) = Fin.last k := by
        ext; simp; omega
      rw [e, hF] at this
      exact this
    set m := F - k with hm
    have hkF : k ≤ F := by
      have := hgap 0
      simp at this
      have := hpos 0
      omega
    have hm1 : 1 ≤ m := by
      have := hgap 0
      have := hpos 0
      simp at *
      omega
    have hFm : F = m + k := by omega
    -- lower bound on the sum
    have hle : ∀ i : Fin (k + 1), 1 / ((m : ℝ) + (i.val : ℝ)) ≤ 1 / (n i : ℝ) := by
      intro i
      have h1 : (n i : ℝ) ≤ (m : ℝ) + i.val := by
        have := hgap i
        have hi := i.isLt
        have : n i ≤ m + i.val := by omega
        exact_mod_cast this
      have h2 : (0 : ℝ) < n i := by exact_mod_cast hpos i
      exact one_div_le_one_div_of_le h2 h1
    have hsum2 : ∑ i ∈ Finset.range (k + 1), 1 / ((m : ℝ) + i) ≤ 1 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => 1 / ((m : ℝ) + i))]
      calc ∑ i : Fin (k + 1), 1 / ((m : ℝ) + (i : ℕ)) ≤ ∑ i, 1 / (n i : ℝ) :=
            Finset.sum_le_sum (fun i _ => hle i)
        _ = 1 := hsum.symm
    have hlog := (OMA285.log_le_sum m hm1 k).trans hsum2
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
    have hx : ((m : ℝ) + k + 1) / m ≤ Real.exp 1 := by
      rw [← Real.log_le_iff_le_exp (by positivity)]
      exact hlog
    have hx2 : (m : ℝ) + k + 1 ≤ Real.exp 1 * m := by
      rwa [div_le_iff₀ hm'] at hx
    have hFr : (F : ℝ) = m + k := by rw [hFm]; push_cast; ring
    have he : (1 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := 1) (by norm_num)
      linarith
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have eq : (1 + -(1 / ((k : ℝ) + 1))) * Real.exp 1 / (Real.exp 1 - 1) * ((k : ℝ) + 1) =
        Real.exp 1 * k / (Real.exp 1 - 1) := by
      field_simp
      ring
    rw [eq, div_le_iff₀ (by linarith), hFr]
    nlinarith
