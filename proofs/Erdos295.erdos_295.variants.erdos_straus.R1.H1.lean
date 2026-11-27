import OMAReductions.R_Erdos295_erdos_295_variants_erdos_straus_R1
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The logarithmic comparison for the lower bound follows the argument in
mrmario2202's Erdős–Straus reduction, project PR 3069. -/

open Filter

namespace OMA.ErdosStrausLower

lemma denominator_bound {N m : ℕ} (n : Fin m → ℕ)
    (hN : ∀ i, N ≤ n i) (hn : StrictMono n) (i : Fin m) : N + i.val ≤ n i := by
  rcases i with ⟨i, hi⟩
  induction i with
  | zero => simpa using hN ⟨0, hi⟩
  | succ i ih =>
    have hprev := ih (Nat.lt_of_succ_lt hi)
    have hstep := hn (show (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin m) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i)
    change N + i ≤ _ at hprev
    change N + (i + 1) ≤ _
    omega

lemma reciprocal_le_log_increment {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have hp : 0 < x + 1 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hp hx)
  rw [Real.log_div hp.ne' hx.ne', inv_div] at h
  calc
    1 / (x + 1) = 1 - x / (x + 1) := by field_simp; ring
    _ ≤ _ := h

end OMA.ErdosStrausLower

theorem OMA.solution : OMA.R_Erdos295_erdos_295_variants_erdos_straus_R1.H1 := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with N hN
  intro m n hn hmono hsum
  let a : ℝ := (N : ℝ) - 1
  have ha : 0 < a := by
    apply sub_pos.mpr
    exact_mod_cast (show 1 < N from by omega)
  let f (j : ℕ) := Real.log (a + j)
  have hterm (i : Fin m) : 1 / (n i : ℝ) ≤ f (i.val + 1) - f i.val := by
    have hden := OMA.ErdosStrausLower.denominator_bound n hn hmono i
    have hreal : (N : ℝ) + (i.val : ℝ) ≤ n i := by exact_mod_cast hden
    have hpos : 0 < a + i.val := by positivity
    calc
      1 / (n i : ℝ) ≤ 1 / (a + i.val + 1) :=
        one_div_le_one_div_of_le (by linarith) (by dsimp [a]; linarith)
      _ ≤ _ := by
        simpa [f, Nat.cast_add, add_assoc] using
          OMA.ErdosStrausLower.reciprocal_le_log_increment hpos
  have hlog : 1 ≤ Real.log (a + m) - Real.log a := calc
    1 = ∑ i : Fin m, 1 / (n i : ℝ) := hsum.symm
    _ ≤ ∑ i : Fin m, (f (i.val + 1) - f i.val) := Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ i ∈ Finset.range m, (f (i + 1) - f i) :=
      Fin.sum_univ_eq_sum_range (fun j => f (j + 1) - f j) m
    _ = f m - f 0 := Finset.sum_range_sub f m
    _ = _ := by simp [f]
  have hend : 0 < a + m := by positivity
  rw [← Real.log_div hend.ne' ha.ne', Real.le_log_iff_exp_le (div_pos hend ha),
    le_div_iff₀ ha] at hlog
  dsimp [a] at hlog
  nlinarith [Real.exp_one_lt_d9]
