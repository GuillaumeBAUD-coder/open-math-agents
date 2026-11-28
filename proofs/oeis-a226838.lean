import OMAStatements.S_oeis_a226838
import Mathlib

/-!
# Proof of OEIS A226838 Conjecture

For every `m >= 2`, the `m - 1` distinct multiples `m, 2*m, ..., (m-1)*m` all lie in
`{1, ..., m^2 - 1}`, so `m^(m - 1) * (m - 1)! = m^(m - 2) * m!` divides `(m^2 - 1)!`.
Hence `6 * m^(m - 2)` divides `(m^2 - 1)!` for all `m >= 2` (checked directly for `m = 2`,
and via `6 = 3! ∣ m!` for `m >= 3`).
Since `(m^2 - 1)! * (n + 1 - m^2)! ∣ n!` whenever `m^2 <= n + 1`, every `k >= 1` term
(with `m = k + 1 >= 2`) in the recurrence for `a(n + 1)` is divisible by `6`, while the
`k = 0` (`m = 1`) term is `a(n)`. Thus `a(n + 1) ≡ a(n) [MOD 6]` and by induction
`a(n) ≡ a(0) = 1 [MOD 6]` for all `n`.
-/

namespace OeisA226838Proof

open Finset

private lemma prod_Icc_one_eq_factorial (N : ℕ) :
    ∏ x ∈ Finset.Icc 1 N, x = N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.prod_insert (by simp), ih, Nat.factorial_succ]

private lemma six_mul_pow_dvd_sq_sub_one_fact (m : ℕ) (hm : 2 ≤ m) :
    6 * m ^ (m - 2) ∣ (m ^ 2 - 1).factorial := by
  by_cases hm2 : m = 2
  · subst hm2; decide
  · have hm3 : 3 ≤ m := by omega
    have hmul_prod : ∏ i ∈ Finset.Icc 1 (m - 1), (m * i) = m ^ (m - 1) * (m - 1).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, prod_Icc_one_eq_factorial]
      have hsub : m - 1 + 1 - 1 = m - 1 := by omega
      rw [hsub]
    have himg : (Finset.Icc 1 (m - 1)).image (fun i => m * i) ⊆ Finset.Icc 1 (m ^ 2 - 1) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      simp only [Finset.mem_Icc] at hi ⊢
      have h1 : 1 ≤ m * i := by nlinarith
      have h2 : m * i ≤ m * (m - 1) := Nat.mul_le_mul_left m hi.2
      have h3 : m * (m - 1) + m = m ^ 2 := by
        rw [sq]
        have := Nat.mul_sub_left_distrib m m 1
        omega
      omega
    have hinj : Set.InjOn (fun i : ℕ => m * i) (Finset.Icc 1 (m - 1) : Set ℕ) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) hab
    have hprod_img : ∏ x ∈ (Finset.Icc 1 (m - 1)).image (fun i => m * i), x = ∏ i ∈ Finset.Icc 1 (m - 1), (m * i) :=
      Finset.prod_image (fun a ha b hb hab => hinj ha hb hab)
    have hdvd1 : m ^ (m - 1) * (m - 1).factorial ∣ (m ^ 2 - 1).factorial := by
      rw [← hmul_prod, ← hprod_img, ← prod_Icc_one_eq_factorial]
      exact Finset.prod_dvd_prod_of_subset _ _ _ himg
    have hpow : m ^ (m - 1) * (m - 1).factorial = m.factorial * m ^ (m - 2) := by
      have h1 : m - 1 = (m - 2) + 1 := by omega
      have h2 : m = (m - 1) + 1 := by omega
      calc m ^ (m - 1) * (m - 1).factorial
          = (m ^ (m - 2) * m) * (m - 1).factorial := by rw [h1, pow_succ]
        _ = (m * (m - 1).factorial) * m ^ (m - 2) := by ring
        _ = m.factorial * m ^ (m - 2) := by
          conv_rhs => rw [h2, Nat.factorial_succ]
          rw [← h2]
    rw [hpow] at hdvd1
    have h6 : 6 ∣ m.factorial := by
      have h3 : (3 : ℕ).factorial ∣ m.factorial := Nat.factorial_dvd_factorial hm3
      exact dvd_trans (by decide : 6 ∣ (3 : ℕ).factorial) h3
    exact dvd_trans (Nat.mul_dvd_mul_right h6 (m ^ (m - 2))) hdvd1

private lemma six_dvd_term_coeff (n m : ℕ) (hm : 2 ≤ m) (hmn : m ^ 2 ≤ n + 1) :
    6 ∣ n.factorial / ((n + 1 - m ^ 2).factorial * m ^ (m - 2)) := by
  have hm2pos : 1 ≤ m ^ 2 := by nlinarith
  have hle : m ^ 2 - 1 ≤ n := by omega
  have hsub : n - (m ^ 2 - 1) = n + 1 - m ^ 2 := by omega
  have hchoose : (m ^ 2 - 1).factorial * (n + 1 - m ^ 2).factorial ∣ n.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at h
    exact ⟨Nat.choose n (m ^ 2 - 1), by linarith⟩
  have h6 := six_mul_pow_dvd_sq_sub_one_fact m hm
  have hcomb : ((n + 1 - m ^ 2).factorial * m ^ (m - 2)) * 6 ∣ n.factorial := by
    rcases h6 with ⟨q1, hq1⟩
    rcases hchoose with ⟨q2, hq2⟩
    refine ⟨q1 * q2, ?_⟩
    rw [hq2, hq1]
    ring
  rcases hcomb with ⟨q, hq⟩
  have hpos : 0 < (n + 1 - m ^ 2).factorial * m ^ (m - 2) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos (by omega))
  rw [hq, mul_assoc, Nat.mul_div_cancel_left _ hpos]
  exact dvd_mul_right 6 q

end OeisA226838Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a226838.main := by
  intro n
  induction n with
  | zero => simp [OMA.S_oeis_a226838.a, Nat.ModEq]
  | succ n ih =>
    rw [OMA.S_oeis_a226838.a, Fin.sum_univ_succ]
    have hfirst :
        (if ((0 : Fin (n + 1)).1 + 1) ^ 2 ≤ n + 1 then
          n.factorial / ((n + 1 - ((0 : Fin (n + 1)).1 + 1) ^ 2).factorial *
            ((0 : Fin (n + 1)).1 + 1) ^ ((0 : Fin (n + 1)).1 + 1 - 2)) *
            OMA.S_oeis_a226838.a (n + 1 - ((0 : Fin (n + 1)).1 + 1) ^ 2)
        else 0) = OMA.S_oeis_a226838.a n := by
      simp [Nat.div_self (Nat.factorial_pos n)]
    rw [hfirst]
    have hrest : 6 ∣ ∑ k : Fin n,
        if (k.succ.1 + 1) ^ 2 ≤ n + 1 then
          n.factorial / ((n + 1 - (k.succ.1 + 1) ^ 2).factorial *
            (k.succ.1 + 1) ^ (k.succ.1 + 1 - 2)) *
            OMA.S_oeis_a226838.a (n + 1 - (k.succ.1 + 1) ^ 2)
        else 0 := by
      apply Finset.dvd_sum
      intro k _
      split_ifs with hle
      · exact dvd_mul_of_dvd_left
          (OeisA226838Proof.six_dvd_term_coeff n (k.succ.1 + 1) (by simp) hle) _
      · exact dvd_zero 6
    rcases hrest with ⟨q, hq⟩
    rw [hq]
    calc OMA.S_oeis_a226838.a n + 6 * q
        ≡ OMA.S_oeis_a226838.a n + 0 [MOD 6] :=
          Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 6 q))
      _ = OMA.S_oeis_a226838.a n := by omega
      _ ≡ 1 [MOD 6] := ih
