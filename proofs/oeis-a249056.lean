import OMAStatements.S_oeis_a249056
import Mathlib

namespace OMA.S_oeis_a249056

lemma fac_shift (x k : ℕ) : (((x + k).factorial : ℕ) : ℚ) =
    (∏ i ∈ Finset.range k, ((x + i + 1 : ℕ) : ℚ)) * (x.factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, Finset.prod_range_succ]
    push_cast at ih ⊢
    rw [ih]; ring

lemma a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) =
    ((2*n-1).factorial : ℚ) / ((2*n-1-n/2).factorial : ℚ) * (((2*n+n/2).factorial : ℚ) / ((2*n).factorial : ℚ)) := by
  have h1 : ∏ i ∈ Finset.range (n/2), (2*n-(i+1)) = (2*n-1).descFactorial (n/2) := by
    rw [Nat.descFactorial_eq_prod_range]
    apply Finset.prod_congr rfl; intro i _; omega
  have h2 : ∏ i ∈ Finset.range (n/2), (2*n+(i+1)) = (2*n+1).ascFactorial (n/2) := by
    rw [Nat.ascFactorial_eq_prod_range]
    apply Finset.prod_congr rfl; intro i _; ring
  have e : a n = (2*n-1).descFactorial (n/2) * (2*n+1).ascFactorial (n/2) := by
    unfold a; rw [Finset.prod_mul_distrib, h1, h2]
  have d := Nat.factorial_mul_descFactorial (show n/2 ≤ 2*n-1 by omega)
  have s := Nat.factorial_mul_ascFactorial (2*n) (n/2)
  have hd : ((2*n-1-n/2).factorial : ℚ) ≠ 0 := by positivity
  have hs : ((2*n).factorial : ℚ) ≠ 0 := by positivity
  rw [e]; push_cast
  have d' : ((2*n-1-n/2).factorial : ℚ) * ((2*n-1).descFactorial (n/2) : ℚ) = ((2*n-1).factorial : ℚ) := by exact_mod_cast d
  have s' : ((2*n).factorial : ℚ) * ((2*n+1).ascFactorial (n/2) : ℚ) = ((2*n+n/2).factorial : ℚ) := by exact_mod_cast s
  rw [← d', ← s']
  field_simp

lemma A2 (p : ℕ) : (a (2*p+2) : ℚ) =
    ((4*p+3).factorial : ℚ) * ((5*p+5).factorial : ℚ) / (((3*p+2).factorial : ℚ) * ((4*p+4).factorial : ℚ)) := by
  rw [a_closed _ (by omega)]
  have h1 : 2*(2*p+2)-1 = 4*p+3 := by omega
  have h2 : 2*(2*p+2)-1-(2*p+2)/2 = 3*p+2 := by omega
  have h3 : 2*(2*p+2)+(2*p+2)/2 = 5*p+5 := by omega
  have h4 : 2*(2*p+2) = 4*p+4 := by omega
  rw [h2, h1, h3, h4]; ring

lemma A3 (p : ℕ) : (a (2*p+3) : ℚ) =
    ((4*p+5).factorial : ℚ) * ((5*p+7).factorial : ℚ) / (((3*p+4).factorial : ℚ) * ((4*p+6).factorial : ℚ)) := by
  rw [a_closed _ (by omega)]
  have h1 : 2*(2*p+3)-1 = 4*p+5 := by omega
  have h2 : 2*(2*p+3)-1-(2*p+3)/2 = 3*p+4 := by omega
  have h3 : 2*(2*p+3)+(2*p+3)/2 = 5*p+7 := by omega
  have h4 : 2*(2*p+3) = 4*p+6 := by omega
  rw [h2, h1, h3, h4]; ring

lemma AG (n m N1 N2 N3 N4 : ℕ) (hn : 1 ≤ n) (hm : m = n/2) (h1 : N1 = 2*n-1)
    (h2 : N3 = 2*n-1-m) (h3 : N2 = 2*n+m) (h4 : N4 = 2*n) :
    (a n : ℚ) = (N1.factorial : ℚ) * (N2.factorial : ℚ) / ((N3.factorial : ℚ) * (N4.factorial : ℚ)) := by
  rw [a_closed n hn, ← hm, ← h2, ← h1, ← h3, ← h4]; ring

lemma FS (x k y : ℕ) (h : y = x + k) : (y.factorial : ℚ) =
    (∏ i ∈ Finset.range k, ((x + i + 1 : ℕ) : ℚ)) * (x.factorial : ℚ) := by
  subst h; exact fac_shift x k

theorem main_aux : ∀ k : ℕ, let n : ℚ := k+3
  c0 n * a (k+3) + c1 n * a (k+2) + c2 n * a (k+1) + c3 n * a k = 0 := by
  intro k
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> norm_num [a, c0, c1, c2, c3, Finset.prod_range_succ]
  obtain ⟨p, hp | hp⟩ : ∃ p, k = 2*p+2 ∨ k = 2*p+3 := by
    rcases Nat.even_or_odd' k with ⟨q, hq | hq⟩
    · exact ⟨q-1, Or.inl (by omega)⟩
    · exact ⟨q-1, Or.inr (by omega)⟩
  all_goals subst hp
  all_goals
    have u0 : (0:ℚ) < ((4*p+3).factorial : ℚ) := by positivity
    have v0 : (0:ℚ) < ((5*p+5).factorial : ℚ) := by positivity
    have w0 : (0:ℚ) < ((3*p+2).factorial : ℚ) := by positivity
  · -- k = 2p+2
    rw [show 2*p+2+3 = 2*(p+1)+3 by ring, show 2*p+2+2 = 2*p+4 by ring, show 2*p+2+1 = 2*p+3 by ring]
    rw [AG (2*(p+1)+3) (p+2) (4*p+9) (5*p+12) (3*p+7) (4*p+10) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        AG (2*p+4) (p+2) (4*p+7) (5*p+10) (3*p+5) (4*p+8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        AG (2*p+3) (p+1) (4*p+5) (5*p+7) (3*p+4) (4*p+6) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        AG (2*p+2) (p+1) (4*p+3) (5*p+5) (3*p+2) (4*p+4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    have e4_1 := FS (4*p+3) 1 (4*p+4) (by omega)
    have e4_2 := FS (4*p+3) 2 (4*p+5) (by omega)
    have e4_3 := FS (4*p+3) 3 (4*p+6) (by omega)
    have e4_4 := FS (4*p+3) 4 (4*p+7) (by omega)
    have e4_5 := FS (4*p+3) 5 (4*p+8) (by omega)
    have e4_6 := FS (4*p+3) 6 (4*p+9) (by omega)
    have e4_7 := FS (4*p+3) 7 (4*p+10) (by omega)
    have e4_8 := FS (4*p+3) 8 (4*p+11) (by omega)
    have e4_9 := FS (4*p+3) 9 (4*p+12) (by omega)
    have e5_2 := FS (5*p+5) 2 (5*p+7) (by omega)
    have e5_5 := FS (5*p+5) 5 (5*p+10) (by omega)
    have e5_7 := FS (5*p+5) 7 (5*p+12) (by omega)
    have e5_10 := FS (5*p+5) 10 (5*p+15) (by omega)
    have e3_2 := FS (3*p+2) 2 (3*p+4) (by omega)
    have e3_3 := FS (3*p+2) 3 (3*p+5) (by omega)
    have e3_5 := FS (3*p+2) 5 (3*p+7) (by omega)
    have e3_6 := FS (3*p+2) 6 (3*p+8) (by omega)
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at e4_1 e4_2 e4_3 e4_4 e4_5 e4_6 e4_7 e4_8 e4_9 e5_2 e5_5 e5_7 e5_10 e3_2 e3_3 e3_5 e3_6
    push_cast at e4_1 e4_2 e4_3 e4_4 e4_5 e4_6 e4_7 e4_8 e4_9 e5_2 e5_5 e5_7 e5_10 e3_2 e3_3 e3_5 e3_6
    simp only [e4_1, e4_2, e4_3, e4_4, e4_5, e4_6, e4_7, e4_8, e4_9, e5_2, e5_5, e5_7, e5_10, e3_2, e3_3, e3_5, e3_6]
    simp only [c0, c1, c2, c3]
    push_cast
    field_simp
    ring
  · rw [show 2*p+3+3 = 2*(p+2)+2 by ring, show 2*p+3+2 = 2*p+5 by ring, show 2*p+3+1 = 2*p+4 by ring]
    rw [AG (2*(p+2)+2) (p+3) (4*p+11) (5*p+15) (3*p+8) (4*p+12) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        AG (2*p+5) (p+2) (4*p+9) (5*p+12) (3*p+7) (4*p+10) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        AG (2*p+4) (p+2) (4*p+7) (5*p+10) (3*p+5) (4*p+8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        AG (2*p+3) (p+1) (4*p+5) (5*p+7) (3*p+4) (4*p+6) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    have e4_1 := FS (4*p+3) 1 (4*p+4) (by omega)
    have e4_2 := FS (4*p+3) 2 (4*p+5) (by omega)
    have e4_3 := FS (4*p+3) 3 (4*p+6) (by omega)
    have e4_4 := FS (4*p+3) 4 (4*p+7) (by omega)
    have e4_5 := FS (4*p+3) 5 (4*p+8) (by omega)
    have e4_6 := FS (4*p+3) 6 (4*p+9) (by omega)
    have e4_7 := FS (4*p+3) 7 (4*p+10) (by omega)
    have e4_8 := FS (4*p+3) 8 (4*p+11) (by omega)
    have e4_9 := FS (4*p+3) 9 (4*p+12) (by omega)
    have e5_2 := FS (5*p+5) 2 (5*p+7) (by omega)
    have e5_5 := FS (5*p+5) 5 (5*p+10) (by omega)
    have e5_7 := FS (5*p+5) 7 (5*p+12) (by omega)
    have e5_10 := FS (5*p+5) 10 (5*p+15) (by omega)
    have e3_2 := FS (3*p+2) 2 (3*p+4) (by omega)
    have e3_3 := FS (3*p+2) 3 (3*p+5) (by omega)
    have e3_5 := FS (3*p+2) 5 (3*p+7) (by omega)
    have e3_6 := FS (3*p+2) 6 (3*p+8) (by omega)
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at e4_1 e4_2 e4_3 e4_4 e4_5 e4_6 e4_7 e4_8 e4_9 e5_2 e5_5 e5_7 e5_10 e3_2 e3_3 e3_5 e3_6
    push_cast at e4_1 e4_2 e4_3 e4_4 e4_5 e4_6 e4_7 e4_8 e4_9 e5_2 e5_5 e5_7 e5_10 e3_2 e3_3 e3_5 e3_6
    simp only [e4_1, e4_2, e4_3, e4_4, e4_5, e4_6, e4_7, e4_8, e4_9, e5_2, e5_5, e5_7, e5_10, e3_2, e3_3, e3_5, e3_6]
    simp only [c0, c1, c2, c3]
    push_cast
    field_simp
    ring


end OMA.S_oeis_a249056

theorem OMA.solution : type_of% @OMA.S_oeis_a249056.main := fun k => OMA.S_oeis_a249056.main_aux k
