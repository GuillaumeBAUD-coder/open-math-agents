import OMAStatements.S_oeis_a091539
import Mathlib.Tactic

open OMA.S_oeis_a091539

/-!
Original Lean proof: @treybeathard-jpg.

Proof of OEIS A091539: for n >= 2, 10 divides block n and 6 divides numerator n,
so 60 * a n = X n - Y n where X n = block n * 3^n * n! and Y n = 3 * block n * q n.
Both X and Y satisfy the target second-order linear recurrence identically for n >= 4.
-/

private lemma ten_dvd_block {n : ℕ} (hn : 2 ≤ n) : (10 : ℤ) ∣ block n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction m with
  | zero =>
    unfold block
    norm_num [Finset.prod_range_succ]
  | succ m ih =>
    have hstep : block (m + 3) =
        block (m + 2) * (3 * ((m + 2 : ℕ) : ℤ) + 2) := by
      unfold block
      rw [Finset.prod_range_succ]
    rw [hstep]
    exact dvd_mul_of_dvd_left ih _

private lemma two_dvd_q {n : ℕ} (hn : 2 ≤ n) : (2 : ℤ) ∣ q n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction m with
  | zero =>
    unfold q
    norm_num [Finset.prod_range_succ]
  | succ m ih =>
    have hstep : q (m + 3) =
        q (m + 2) * (3 * ((m + 2 : ℕ) : ℤ) + 1) := by
      unfold q
      rw [Finset.prod_range_succ]
    rw [hstep]
    exact dvd_mul_of_dvd_left ih _

private lemma six_dvd_numerator {n : ℕ} (hn : 2 ≤ n) :
    (6 : ℤ) ∣ numerator n := by
  have h2fac : (2 : ℤ) ∣ (n.factorial : ℤ) := by
    exact_mod_cast Nat.dvd_factorial (by decide) hn
  have h2num : (2 : ℤ) ∣ numerator n := by
    unfold numerator
    exact dvd_sub (dvd_mul_of_dvd_right h2fac _) (dvd_mul_of_dvd_right (two_dvd_q hn) _)
  have h3pow : (3 : ℤ) ∣ (3 : ℤ) ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]
    exact dvd_mul_left _ _
  have h3num : (3 : ℤ) ∣ numerator n := by
    unfold numerator
    exact dvd_sub (dvd_mul_of_dvd_left h3pow _) (dvd_mul_right _ _)
  rcases h2num with ⟨u, hu⟩
  rcases h3num with ⟨v, hv⟩
  exact ⟨u - v, by linarith⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a091539.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  let X (k : ℕ) : ℤ := block k * ((3 : ℤ) ^ k * (k.factorial : ℤ))
  let Y (k : ℕ) : ℤ := 3 * block k * q k
  have h60 (k : ℕ) (hk : 2 ≤ k) : 60 * a k = X k - Y k := by
    have hf : factor k * 10 = block k := by
      unfold factor
      exact Int.ediv_mul_cancel (ten_dvd_block hk)
    have hr : rescaled k * 6 = numerator k := by
      unfold rescaled
      exact Int.ediv_mul_cancel (six_dvd_numerator hk)
    calc
      60 * a k
          = (factor k * 10) * (rescaled k * 6) := by
        unfold a
        ring
      _ = block k * numerator k := by
        rw [hf, hr]
      _ = X k - Y k := by
        unfold numerator
        dsimp [X, Y]
        ring
  have hX (k : ℕ) : X (k + 1) = (3 * (k : ℤ) + 2) * 3 * ((k : ℤ) + 1) * X k := by
    dsimp [X]
    have hb : block (k + 1) =
        block k * (3 * (k : ℤ) + 2) := by
      unfold block
      exact Finset.prod_range_succ _ k
    rw [hb, pow_succ, Nat.factorial_succ]
    push_cast
    ring
  have hY (k : ℕ) : Y (k + 1) = (3 * (k : ℤ) + 2) * (3 * (k : ℤ) + 1) * Y k := by
    dsimp [Y]
    have hb : block (k + 1) =
        block k * (3 * (k : ℤ) + 2) := by
      unfold block
      exact Finset.prod_range_succ _ k
    have hq : q (k + 1) =
        q k * (3 * (k : ℤ) + 1) := by
      unfold q
      exact Finset.prod_range_succ _ k
    rw [hb, hq]
    ring
  let A : ℤ := (3 * ((m + 4 : ℕ) : ℤ) - 1) * (6 * ((m + 4 : ℕ) : ℤ) - 5)
  let B : ℤ := 3 * (3 * ((m + 4 : ℕ) : ℤ) - 5) * (((m + 4 : ℕ) : ℤ) - 1) *
    (3 * ((m + 4 : ℕ) : ℤ) - 1) * (3 * ((m + 4 : ℕ) : ℤ) - 4)
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
  change a (m + 4) - A * a (m + 3) + B * a (m + 2) = 0
  have hrec : (X (m + 4) - Y (m + 4)) - A * (X (m + 3) - Y (m + 3)) +
      B * (X (m + 2) - Y (m + 2)) = 0 := by
    rw [hX (m + 3), hX (m + 2), hY (m + 3), hY (m + 2)]
    dsimp [A, B]
    ring
  have hscaled : 60 * (a (m + 4) - A * a (m + 3) + B * a (m + 2)) = 0 := by
    linear_combination hrec + h60 (m + 4) (by omega) - A * h60 (m + 3) (by omega) +
      B * h60 (m + 2) (by omega)
  exact (mul_eq_zero.mp hscaled).resolve_left (by decide)
