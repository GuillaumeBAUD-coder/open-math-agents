import OMAStatements.S_oeis_a226890
import Mathlib

/-!
# Proof of OEIS A226890 Conjecture

For every `m >= 2`:
- If `m = 2`, `sigmaSelf 2 = 1^2 + 2^2 = 5` and `(2^2 - 1)! / 2^0 = 6`, so `30 ∣ 5 * 6`.
- If `m = 3`, `(3^2 - 1)! / 3^1 = 8! / 3 = 13440`, which is divisible by `30`.
- If `m = 4`, `(4^2 - 1)! / 4^2 = 15! / 16`, which is divisible by `30`.
- If `m >= 5`, the `m - 1` distinct multiples `m, 2*m, ..., (m-1)*m` lie in `{1, ..., m^2 - 1}`,
  so `m! * m^(m - 2) ∣ (m^2 - 1)!`, and `30 ∣ 5! ∣ m!`, hence `30 * m^(m - 2) ∣ (m^2 - 1)!`.
Thus every `m >= 2` term in the recurrence for `a(n + 1)` is divisible by `30`, while the `m = 1`
term is `a(n)`. By induction, `a(n) ≡ a(0) = 1 [MOD 30]` for all `n`.
-/

namespace OeisA226890Proof

open Finset OMA.S_oeis_a226890

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

private lemma thirty_mul_pow_dvd_sq_sub_one_fact (m : ℕ) (hm : 3 ≤ m) :
    30 * m ^ (m - 2) ∣ (m ^ 2 - 1).factorial := by
  by_cases hm3 : m = 3
  · subst hm3; decide
  · by_cases hm4 : m = 4
    · subst hm4; decide
    · have hm5 : 5 ≤ m := by omega
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
      have hprod_img : ∏ x ∈ (Finset.Icc 1 (m - 1)).image (fun i => m * i), x =
          ∏ i ∈ Finset.Icc 1 (m - 1), (m * i) :=
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
      have h30 : 30 ∣ m.factorial := by
        have h5 : (5 : ℕ).factorial ∣ m.factorial := Nat.factorial_dvd_factorial hm5
        exact dvd_trans (by decide : 30 ∣ (5 : ℕ).factorial) h5
      exact dvd_trans (Nat.mul_dvd_mul_right h30 (m ^ (m - 2))) hdvd1

private lemma thirty_dvd_term_coeff (n m : ℕ) (hm : 2 ≤ m) (hmn : m ^ 2 ≤ n + 1) :
    30 ∣ sigmaSelf m * (n.factorial / ((n + 1 - m ^ 2).factorial * m ^ (m - 2))) := by
  have hm2pos : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m (by omega)
  have hle : m ^ 2 - 1 ≤ n := by omega
  have hsub : n - (m ^ 2 - 1) = n + 1 - m ^ 2 := by omega
  have hchoose : (m ^ 2 - 1).factorial * (n + 1 - m ^ 2).factorial ∣ n.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at h
    exact ⟨Nat.choose n (m ^ 2 - 1), by linarith⟩
  have hpos : 0 < (n + 1 - m ^ 2).factorial * m ^ (m - 2) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos (by omega))
  by_cases hm2 : m = 2
  · subst hm2
    have hsig : sigmaSelf 2 = 5 := by decide
    rw [hsig]
    have h6 : ((n + 1 - 2 ^ 2).factorial * 2 ^ (2 - 2)) * 6 ∣ n.factorial := by
      rcases hchoose with ⟨q2, hq2⟩
      refine ⟨q2, ?_⟩
      have h3f : (2 ^ 2 - 1).factorial = 6 := by decide
      rw [h3f] at hq2
      simp only [Nat.sub_self, pow_zero, mul_one]
      linarith
    rcases h6 with ⟨q, hq⟩
    rw [hq, mul_assoc, Nat.mul_div_cancel_left _ hpos]
    exact ⟨q, by ring⟩
  · have hm3 : 3 ≤ m := by omega
    have h30 := thirty_mul_pow_dvd_sq_sub_one_fact m hm3
    have hcomb : ((n + 1 - m ^ 2).factorial * m ^ (m - 2)) * 30 ∣ n.factorial := by
      rcases h30 with ⟨q1, hq1⟩
      rcases hchoose with ⟨q2, hq2⟩
      refine ⟨q1 * q2, ?_⟩
      rw [hq2, hq1]
      ring
    rcases hcomb with ⟨q, hq⟩
    rw [hq, mul_assoc, Nat.mul_div_cancel_left _ hpos]
    exact dvd_mul_of_dvd_right (dvd_mul_right 30 q) _

end OeisA226890Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a226890.main := by
  intro n
  induction n with
  | zero => simp [OMA.S_oeis_a226890.a, Nat.ModEq]
  | succ n ih =>
    rw [OMA.S_oeis_a226890.a, Fin.sum_univ_succ]
    have hsig1 : OMA.S_oeis_a226890.sigmaSelf 1 = 1 := by decide
    have hfirst :
        (if ((0 : Fin (n + 1)).1 + 1) ^ 2 ≤ n + 1 then
          OMA.S_oeis_a226890.sigmaSelf ((0 : Fin (n + 1)).1 + 1) *
            (n.factorial / ((n + 1 - ((0 : Fin (n + 1)).1 + 1) ^ 2).factorial *
              ((0 : Fin (n + 1)).1 + 1) ^ ((0 : Fin (n + 1)).1 + 1 - 2))) *
            OMA.S_oeis_a226890.a (n + 1 - ((0 : Fin (n + 1)).1 + 1) ^ 2)
        else 0) = OMA.S_oeis_a226890.a n := by
      simp [hsig1, Nat.div_self (Nat.factorial_pos n)]
    rw [hfirst]
    have hrest : 30 ∣ ∑ k : Fin n,
        if (k.succ.1 + 1) ^ 2 ≤ n + 1 then
          OMA.S_oeis_a226890.sigmaSelf (k.succ.1 + 1) *
            (n.factorial / ((n + 1 - (k.succ.1 + 1) ^ 2).factorial *
              (k.succ.1 + 1) ^ (k.succ.1 + 1 - 2))) *
            OMA.S_oeis_a226890.a (n + 1 - (k.succ.1 + 1) ^ 2)
        else 0 := by
      apply Finset.dvd_sum
      intro k _
      split_ifs with hle
      · exact dvd_mul_of_dvd_left
          (OeisA226890Proof.thirty_dvd_term_coeff n (k.succ.1 + 1) (by simp) hle) _
      · exact dvd_zero 30
    rcases hrest with ⟨q, hq⟩
    rw [hq]
    calc OMA.S_oeis_a226890.a n + 30 * q
        ≡ OMA.S_oeis_a226890.a n + 0 [MOD 30] :=
          Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 30 q))
      _ = OMA.S_oeis_a226890.a n := by omega
      _ ≡ 1 [MOD 30] := ih
