import OMAStatements.S_oeis_a091539
import Mathlib.Tactic

/-!
Proof of OEIS A091539: for n >= 2, 10 divides block n and 6 divides numerator n,
so 60 * a n = X n - Y n where X n = block n * 3^n * n! and Y n = 3 * block n * q n.
Both X and Y satisfy the target second-order linear recurrence identically for n >= 4.
-/

private lemma ten_dvd_block {n : ℕ} (hn : 2 ≤ n) : (10 : ℤ) ∣ OMA.S_oeis_a091539.block n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction m with
  | zero =>
    unfold OMA.S_oeis_a091539.block
    norm_num [Finset.prod_range_succ]
  | succ m ih =>
    have hstep : OMA.S_oeis_a091539.block (m + 3) =
        OMA.S_oeis_a091539.block (m + 2) * (3 * ((m + 2 : ℕ) : ℤ) + 2) := by
      unfold OMA.S_oeis_a091539.block
      rw [Finset.prod_range_succ]
    rw [hstep]
    exact dvd_mul_of_dvd_left ih _

private lemma two_dvd_q {n : ℕ} (hn : 2 ≤ n) : (2 : ℤ) ∣ OMA.S_oeis_a091539.q n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  induction m with
  | zero =>
    unfold OMA.S_oeis_a091539.q
    norm_num [Finset.prod_range_succ]
  | succ m ih =>
    have hstep : OMA.S_oeis_a091539.q (m + 3) =
        OMA.S_oeis_a091539.q (m + 2) * (3 * ((m + 2 : ℕ) : ℤ) + 1) := by
      unfold OMA.S_oeis_a091539.q
      rw [Finset.prod_range_succ]
    rw [hstep]
    exact dvd_mul_of_dvd_left ih _

private lemma six_dvd_numerator {n : ℕ} (hn : 2 ≤ n) :
    (6 : ℤ) ∣ OMA.S_oeis_a091539.numerator n := by
  have h2fac : (2 : ℤ) ∣ (n.factorial : ℤ) := by
    exact_mod_cast Nat.dvd_factorial (by decide) hn
  have h2num : (2 : ℤ) ∣ OMA.S_oeis_a091539.numerator n := by
    unfold OMA.S_oeis_a091539.numerator
    exact dvd_sub (dvd_mul_of_dvd_right h2fac _) (dvd_mul_of_dvd_right (two_dvd_q hn) _)
  have h3pow : (3 : ℤ) ∣ (3 : ℤ) ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]
    exact dvd_mul_left _ _
  have h3num : (3 : ℤ) ∣ OMA.S_oeis_a091539.numerator n := by
    unfold OMA.S_oeis_a091539.numerator
    exact dvd_sub (dvd_mul_of_dvd_left h3pow _) (dvd_mul_right _ _)
  rcases h2num with ⟨u, hu⟩
  rcases h3num with ⟨v, hv⟩
  exact ⟨u - v, by linarith⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a091539.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  let X (k : ℕ) : ℤ := OMA.S_oeis_a091539.block k * ((3 : ℤ) ^ k * (k.factorial : ℤ))
  let Y (k : ℕ) : ℤ := 3 * OMA.S_oeis_a091539.block k * OMA.S_oeis_a091539.q k
  have h60 (k : ℕ) (hk : 2 ≤ k) : 60 * OMA.S_oeis_a091539.a k = X k - Y k := by
    have hf : OMA.S_oeis_a091539.factor k * 10 = OMA.S_oeis_a091539.block k := by
      unfold OMA.S_oeis_a091539.factor
      exact Int.ediv_mul_cancel (ten_dvd_block hk)
    have hr : OMA.S_oeis_a091539.rescaled k * 6 = OMA.S_oeis_a091539.numerator k := by
      unfold OMA.S_oeis_a091539.rescaled
      exact Int.ediv_mul_cancel (six_dvd_numerator hk)
    calc
      60 * OMA.S_oeis_a091539.a k
          = (OMA.S_oeis_a091539.factor k * 10) * (OMA.S_oeis_a091539.rescaled k * 6) := by
        unfold OMA.S_oeis_a091539.a
        ring
      _ = OMA.S_oeis_a091539.block k * OMA.S_oeis_a091539.numerator k := by
        rw [hf, hr]
      _ = X k - Y k := by
        unfold OMA.S_oeis_a091539.numerator
        dsimp [X, Y]
        ring
  have hX (k : ℕ) : X (k + 1) = (3 * (k : ℤ) + 2) * 3 * ((k : ℤ) + 1) * X k := by
    dsimp [X]
    have hb : OMA.S_oeis_a091539.block (k + 1) =
        OMA.S_oeis_a091539.block k * (3 * (k : ℤ) + 2) := by
      unfold OMA.S_oeis_a091539.block
      exact Finset.prod_range_succ _ k
    rw [hb, pow_succ, Nat.factorial_succ]
    push_cast
    ring
  have hY (k : ℕ) : Y (k + 1) = (3 * (k : ℤ) + 2) * (3 * (k : ℤ) + 1) * Y k := by
    dsimp [Y]
    have hb : OMA.S_oeis_a091539.block (k + 1) =
        OMA.S_oeis_a091539.block k * (3 * (k : ℤ) + 2) := by
      unfold OMA.S_oeis_a091539.block
      exact Finset.prod_range_succ _ k
    have hq : OMA.S_oeis_a091539.q (k + 1) =
        OMA.S_oeis_a091539.q k * (3 * (k : ℤ) + 1) := by
      unfold OMA.S_oeis_a091539.q
      exact Finset.prod_range_succ _ k
    rw [hb, hq]
    ring
  have h60_4 := h60 (m + 4) (by omega)
  have h60_3 := h60 (m + 3) (by omega)
  have h60_2 := h60 (m + 2) (by omega)
  have hX3 := hX (m + 2)
  have hX4 := hX (m + 3)
  have hY3 := hY (m + 2)
  have hY4 := hY (m + 3)
  have hsub1 : m + 4 - 1 = m + 3 := by omega
  have hsub2 : m + 4 - 2 = m + 2 := by omega
  rw [hsub1, hsub2]
  push_cast at hX3 hX4 hY3 hY4 ⊢
  have h60_lhs :
      60 * (OMA.S_oeis_a091539.a (m + 4) -
        (3 * ((m : ℤ) + 4) - 1) * (6 * ((m : ℤ) + 4) - 5) * OMA.S_oeis_a091539.a (m + 3) +
        3 * (3 * ((m : ℤ) + 4) - 5) * (((m : ℤ) + 4) - 1) *
          (3 * ((m : ℤ) + 4) - 1) * (3 * ((m : ℤ) + 4) - 4) * OMA.S_oeis_a091539.a (m + 2)) = 0 := by
    calc
      60 * (OMA.S_oeis_a091539.a (m + 4) -
          (3 * ((m : ℤ) + 4) - 1) * (6 * ((m : ℤ) + 4) - 5) * OMA.S_oeis_a091539.a (m + 3) +
          3 * (3 * ((m : ℤ) + 4) - 5) * (((m : ℤ) + 4) - 1) *
            (3 * ((m : ℤ) + 4) - 1) * (3 * ((m : ℤ) + 4) - 4) * OMA.S_oeis_a091539.a (m + 2))
          = 60 * OMA.S_oeis_a091539.a (m + 4) -
              (3 * ((m : ℤ) + 4) - 1) * (6 * ((m : ℤ) + 4) - 5) *
                (60 * OMA.S_oeis_a091539.a (m + 3)) +
              3 * (3 * ((m : ℤ) + 4) - 5) * (((m : ℤ) + 4) - 1) *
                (3 * ((m : ℤ) + 4) - 1) * (3 * ((m : ℤ) + 4) - 4) *
                (60 * OMA.S_oeis_a091539.a (m + 2)) := by ring
      _ = (X (m + 4) - Y (m + 4)) -
            (3 * ((m : ℤ) + 4) - 1) * (6 * ((m : ℤ) + 4) - 5) * (X (m + 3) - Y (m + 3)) +
            3 * (3 * ((m : ℤ) + 4) - 5) * (((m : ℤ) + 4) - 1) *
              (3 * ((m : ℤ) + 4) - 1) * (3 * ((m : ℤ) + 4) - 4) * (X (m + 2) - Y (m + 2)) := by
          rw [h60_4, h60_3, h60_2]
      _ = 0 := by
          rw [hX4, hX3, hY4, hY3]
          ring
  linarith
