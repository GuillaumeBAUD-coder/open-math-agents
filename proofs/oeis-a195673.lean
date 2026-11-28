import OMAStatements.S_oeis_a195673
import Mathlib

namespace OMA.S_oeis_a195673

lemma T_zero (p q : ℤ) : ∀ n k : ℕ, n < k → T p q n k = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    match n with
    | 0 => simp [T] <;> omega
    | 1 => simp [T] <;> omega
    | m + 2 =>
      simp only [T]
      rw [ih (m+1) (by omega) k (by omega)]
      split_ifs with h
      · rw [ih m (by omega) (k-2) (by omega)]; simp
      · simp

lemma poly_coeff (p q : ℤ) (n i : ℕ) :
    (poly p q n).coeff i = if i ≤ n then T p q n (n - i) else 0 := by
  unfold poly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : i ≤ n
  · rw [if_pos h, Finset.sum_eq_single (n - i)]
    · simp <;> omega
    · intro b hb hne
      have : ¬ i = n - b := by
        intro e; apply hne; have := Finset.mem_range.mp hb; omega
      simp [this]
    · intro hn; exfalso; apply hn; simp <;> omega
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    have : ¬ i = n - b := by omega
    simp [this]

lemma poly_rec (p q : ℤ) (n : ℕ) :
    poly p q (n+2) = Polynomial.X * poly p q (n+1) - poly p q n := by
  ext i
  have e1 := poly_coeff p q (n+2) i
  have e3 := poly_coeff p q n i
  rw [Polynomial.coeff_sub, e1, e3]
  rcases i with _ | i
  · rw [Polynomial.coeff_X_mul_zero]
    simp only [Nat.zero_le, if_true, Nat.sub_zero]
    show T p q (n+1) (n+2) - (if 2 ≤ n+2 then T p q n (n+2-2) else 0) = 0 - T p q n (n - 0)
    rw [T_zero p q (n+1) (n+2) (by omega), if_pos (by omega)]
    simp
  · rw [Polynomial.coeff_X_mul, poly_coeff]
    by_cases h : i ≤ n + 1
    · have hm : n + 2 - (i+1) = n+1-i := by omega
      rw [if_pos (by omega), if_pos h, hm]
      show T p q (n+1) (n+1-i) - (if 2 ≤ n+1-i then T p q n (n+1-i-2) else 0) = _
      by_cases h2 : i + 1 ≤ n
      · have : n+1-i-2 = n-(i+1) := by omega
        rw [if_pos (by omega), if_pos h2, this]
      · rw [if_neg (by omega), if_neg h2]; try simp
    · rw [if_neg (by omega), if_neg h, if_neg (by omega)]; simp

lemma T_lin (p q : ℤ) : ∀ n k : ℕ, T (p+1) (q+1) n k - T p q n k = T 1 1 n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    match n with
    | 0 => by_cases h : k = 0 <;> simp [T, h]
    | 1 => by_cases h : k = 0 <;> simp [T, h]
    | m + 2 =>
      simp only [T]
      have h1 := ih (m+1) (by omega) k
      split_ifs with h
      · have h2 := ih m (by omega) (k-2)
        linarith
      · linarith

theorem main_aux : type_of% @OMA.S_oeis_a195673.main := by
  intro p q n
  have hd : ∀ n, poly (p+1) (q+1) n - poly p q n = poly 1 1 n := by
    intro n
    ext i
    rw [Polynomial.coeff_sub, poly_coeff, poly_coeff, poly_coeff]
    split_ifs
    · exact T_lin p q n (n - i)
    · simp
  rw [hd]
  have h : ∀ n : ℕ, poly 1 1 n = Polynomial.Chebyshev.S ℤ (n : ℤ) ∧
      poly 1 1 (n+1) = Polynomial.Chebyshev.S ℤ ((n+1 : ℕ) : ℤ) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simp [poly, T, Polynomial.Chebyshev.S_zero]
      · simp [poly, T, Finset.sum_range_succ, Polynomial.Chebyshev.S_one]
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [poly_rec, ih.1, ih.2]
      have := Polynomial.Chebyshev.S_add_two ℤ (m : ℤ)
      push_cast at this ⊢
      rw [show (m:ℤ)+1+1 = (m:ℤ)+2 by ring, this]
  exact (h n).1

end OMA.S_oeis_a195673

theorem OMA.solution : type_of% @OMA.S_oeis_a195673.main := OMA.S_oeis_a195673.main_aux
