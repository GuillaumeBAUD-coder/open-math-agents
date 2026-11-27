import OMAStatements.S_oeis_a003477
import Mathlib

/-! Arie Bos’s proposed recurrence misses the term 2*a(0)=2. -/
namespace DragonCurves
open OMA.S_oeis_a003477 PowerSeries Finset
open scoped PowerSeries
private noncomputable abbrev U : ℤ⟦X⟧ := (1-C 2*X)*(1+X^2)
private noncomputable abbrev D : ℤ⟦X⟧ := 1-X-C 2*X^3
private noncomputable abbrev E : ℤ⟦X⟧ := 1-X
private noncomputable abbrev F : ℤ⟦X⟧ := invOfUnit (U*D) 1
private noncomputable abbrev G : ℤ⟦X⟧ := invOfUnit (U*E) 1

private lemma series_key : F-G = (F-G)*X^1 + (F*X^3)*C 2 := by
  have hf : F*(U*D)=1 := invOfUnit_mul _ _ (by simp [U,D])
  have hg : G*(U*E)=1 := invOfUnit_mul _ _ (by simp [U,E])
  have hu : U≠0 := by
    intro h
    have := congrArg (constantCoeff (R:=ℤ)) h
    simp [U] at this
  have eq : F*D=G*E := by
    apply mul_left_cancel₀ hu
    calc U*(F*D) = F*(U*D) := by ring
         _ = G*(U*E) := hf.trans hg.symm
         _ = U*(G*E) := by ring
  unfold D E at eq
  linear_combination eq

private lemma coeff_key (n : ℕ) :
    a n-b n = (if 1≤n then a (n-1)-b (n-1) else 0) +
      (if 3≤n then a (n-3) else 0)*2 := by
  have h := congrArg (coeff (R:=ℤ) n) series_key
  have fa (j : ℕ) : coeff j F = a j := rfl
  have gb (j : ℕ) : coeff j G = b j := rfl
  simpa only [map_sub,map_add,coeff_mul_C,coeff_mul_X_pow',fa,gb] using h

/-- The corrected cumulative formula, including the constant coefficient. -/
theorem corrected (n : ℕ) :
    a n = b n + 2 * ∑ j ∈ range (n-2), a j := by
  induction n with
  | zero => have := coeff_key 0; simp_all; omega
  | succ n ih =>
    by_cases hn : 2≤n
    · have h := coeff_key (n+1)
      rw [if_pos (by omega),if_pos (by omega)] at h
      rw [show n+1-2=(n-2)+1 by omega,sum_range_succ]
      rw [show n+1-3=n-2 by omega] at h
      simp only [Nat.add_sub_cancel] at h
      linarith
    · interval_cases n <;> simp_all <;> have h := coeff_key 1 <;>
        have h' := coeff_key 2 <;> norm_num at * <;> omega

theorem refuted : ¬ (∀ n : ℕ, 4 ≤ n →
    a n = b n + 2*(∑ j ∈ range (n-3), a (j+1))) := by
  intro h
  have h1 := h 4 (by decide)
  have h2 := corrected 4
  have zero : a 0 = 1 := by
    change coeff 0 F = 1
    simp [F,coeff_zero_eq_constantCoeff_apply]
  norm_num [sum_range_succ,zero] at h1 h2
  omega

end DragonCurves

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a003477.main) := DragonCurves.refuted
