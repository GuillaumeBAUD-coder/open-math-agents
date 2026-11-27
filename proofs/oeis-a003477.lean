import OMAStatements.S_oeis_a003477
import Mathlib

/-!
# Disproof of the stated A003477 identity at n = 4

The first terms are a = 1, 3, 6, 14, 33 and b = 1, 3, 6, 12, 25. At n = 4 the
statement asks 33 = 25 + 2 * a(1) = 31. Arie Bos's conjecture (OEIS A003477,
Nov 29 2019) omits the term a(0) from the sum; the generating functions give
a(n) = b(n) + 2 * (a(0) + ... + a(n-3)) instead, so the stated form is off by 2.
-/

namespace OMA.P_oeis_a003477

open PowerSeries Finset

noncomputable def cm : ℤ⟦X⟧ := (1 - C 2 * X) * (1 + X ^ 2)
noncomputable def f1 : ℤ⟦X⟧ := 1 - X - C 2 * X ^ 3
noncomputable def f2 : ℤ⟦X⟧ := 1 - X
noncomputable def s1 : ℤ⟦X⟧ := invOfUnit (cm * f1) 1
noncomputable def s2 : ℤ⟦X⟧ := invOfUnit (cm * f2) 1

lemma a_eq (n : ℕ) : OMA.S_oeis_a003477.a n = coeff n s1 := rfl
lemma b_eq (n : ℕ) : OMA.S_oeis_a003477.b n = coeff n s2 := rfl

lemma s1_mul : s1 * (cm * f1) = 1 := by
  unfold s1
  apply invOfUnit_mul
  simp [cm, f1]

lemma s2_mul : s2 * (cm * f2) = 1 := by
  unfold s2
  apply invOfUnit_mul
  simp [cm, f2]

lemma e1 (S : ℤ⟦X⟧) : S * (cm * f1) = S - C 3 * (X ^ 1 * S) + C 3 * (X ^ 2 * S)
    - C 5 * (X ^ 3 * S) + C 6 * (X ^ 4 * S) - C 2 * (X ^ 5 * S) + C 4 * (X ^ 6 * S) := by
  unfold cm f1
  simp only [map_ofNat]
  ring

lemma e2 (S : ℤ⟦X⟧) : S * (cm * f2) = S - C 3 * (X ^ 1 * S) + C 3 * (X ^ 2 * S)
    - C 3 * (X ^ 3 * S) + C 2 * (X ^ 4 * S) := by
  unfold cm f2
  simp only [map_ofNat]
  ring

lemma c1 (n : ℕ) : coeff n (s1 * (cm * f1)) = coeff n s1
    - 3 * (if 1 ≤ n then coeff (n - 1) s1 else 0) + 3 * (if 2 ≤ n then coeff (n - 2) s1 else 0)
    - 5 * (if 3 ≤ n then coeff (n - 3) s1 else 0) + 6 * (if 4 ≤ n then coeff (n - 4) s1 else 0)
    - 2 * (if 5 ≤ n then coeff (n - 5) s1 else 0) + 4 * (if 6 ≤ n then coeff (n - 6) s1 else 0) := by
  rw [e1]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

lemma c2 (n : ℕ) : coeff n (s2 * (cm * f2)) = coeff n s2
    - 3 * (if 1 ≤ n then coeff (n - 1) s2 else 0) + 3 * (if 2 ≤ n then coeff (n - 2) s2 else 0)
    - 3 * (if 3 ≤ n then coeff (n - 3) s2 else 0) + 2 * (if 4 ≤ n then coeff (n - 4) s2 else 0) := by
  rw [e2]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

lemma vals1 : coeff 1 s1 = 3 ∧ coeff 4 s1 = 33 := by
  have h : ∀ n, coeff n (s1 * (cm * f1)) = if n = 0 then 1 else 0 := by
    intro n; rw [s1_mul, coeff_one]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rw [c1] at h0 h1 h2 h3 h4
  norm_num at h0 h1 h2 h3 h4
  constructor <;> linarith

lemma vals2 : coeff 4 s2 = 25 := by
  have h : ∀ n, coeff n (s2 * (cm * f2)) = if n = 0 then 1 else 0 := by
    intro n; rw [s2_mul, coeff_one]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rw [c2] at h0 h1 h2 h3 h4
  norm_num at h0 h1 h2 h3 h4
  linarith

end OMA.P_oeis_a003477

open OMA.P_oeis_a003477 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a003477.main) := by
  intro h
  have h4 := h 4 le_rfl
  simp only [a_eq, b_eq, show 4 - 3 = 1 from rfl, Finset.sum_range_one, zero_add] at h4
  obtain ⟨v1, v4⟩ := vals1
  rw [v4, vals2, v1] at h4
  norm_num at h4
