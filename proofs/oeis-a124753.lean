import OMAStatements.S_oeis_a124753
import Mathlib

open OMA.S_oeis_a124753

private def g (m : ℕ) : ℚ := ((4 * m).choose m : ℚ)

private lemma G1 (m : ℕ) : ((4 * m + 1).choose m : ℚ) = g m * (4 * m + 1) / (3 * m + 1) := by
  have h := Nat.choose_mul_succ_eq (4 * m) m
  rw [show 4 * m + 1 - m = 3 * m + 1 by omega] at h
  have h2 := congrArg (fun x : ℕ => (x : ℚ)) h
  push_cast at h2
  have : (3 * (m : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff this]; unfold g; linarith

private lemma G2 (m : ℕ) : ((4 * m + 2).choose m : ℚ) =
    ((4 * m + 1).choose m : ℚ) * (4 * m + 2) / (3 * m + 2) := by
  have h := Nat.choose_mul_succ_eq (4 * m + 1) m
  rw [show 4 * m + 1 + 1 - m = 3 * m + 2 by omega] at h
  have h2 := congrArg (fun x : ℕ => (x : ℚ)) h
  push_cast at h2
  have : (3 * (m : ℚ) + 2) ≠ 0 := by positivity
  rw [eq_div_iff this]; linarith

private lemma G3 (m : ℕ) : ((4 * m + 3).choose m : ℚ) =
    ((4 * m + 2).choose m : ℚ) * (4 * m + 3) / (3 * m + 3) := by
  have h := Nat.choose_mul_succ_eq (4 * m + 2) m
  rw [show 4 * m + 2 + 1 - m = 3 * m + 3 by omega] at h
  have h2 := congrArg (fun x : ℕ => (x : ℚ)) h
  push_cast at h2
  have : (3 * (m : ℚ) + 3) ≠ 0 := by positivity
  rw [eq_div_iff this]; linarith

private lemma G4 (m : ℕ) : g (m + 1) = ((4 * m + 3).choose m : ℚ) * (4 * m + 4) / (m + 1) := by
  have h := Nat.add_one_mul_choose_eq (4 * m + 3) m
  have h2 := congrArg (fun x : ℕ => (x : ℚ)) h
  push_cast at h2
  have : ((m : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff this]; unfold g; rw [show 4 * (m + 1) = 4 * m + 3 + 1 by ring]
  push_cast; linarith

private def r1 (x : ℚ) : ℚ := (4 * x + 1) / (3 * x + 1)
private def r2 (x : ℚ) : ℚ := (4 * x + 1) / (3 * x + 1) * ((4 * x + 2) / (3 * x + 2))
private def r4 (x : ℚ) : ℚ :=
  (4 * x + 1) / (3 * x + 1) * ((4 * x + 2) / (3 * x + 2)) * ((4 * x + 3) / (3 * x + 3)) *
    ((4 * x + 4) / (x + 1))

private lemma gs (m : ℕ) : g (m + 1) = g m * r4 m := by
  rw [G4, G3, G2, G1]; unfold r4; ring

private lemma A0 (m : ℕ) : a (3 * m) = g m / (3 * m + 1) := by
  unfold a g
  rw [show 3 * m % 3 = 0 by omega, show 3 * m / 3 = m by omega]
  push_cast; ring

private lemma A1 (m : ℕ) : a (3 * m + 1) = 2 * (g m * r1 m) / (3 * m + 2) := by
  unfold a
  rw [show (3 * m + 1) % 3 = 1 by omega, show (3 * m + 1) / 3 = m by omega, G1]
  unfold r1; push_cast; ring

private lemma A2 (m : ℕ) : a (3 * m + 2) = 3 * (g m * r2 m) / (3 * m + 3) := by
  unfold a
  rw [show (3 * m + 2) % 3 = 2 by omega, show (3 * m + 2) / 3 = m by omega, G2, G1]
  unfold r2; push_cast; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a124753.main := by
  intro n hn
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ n = 3 * q + r + 6 := ⟨(n - 6) / 3, (n - 6) % 3, by omega, by omega⟩
  have g1 := gs q
  have g2 := gs (q + 1)
  have hq1 : ((q : ℚ) + 1) ≠ 0 := by positivity
  have hq2 : ((q : ℚ) + 2) ≠ 0 := by positivity
  have hq3 : ((q : ℚ) + 3) ≠ 0 := by positivity
  have h31 : (3 * (q : ℚ) + 1) ≠ 0 := by positivity
  have h32 : (3 * (q : ℚ) + 2) ≠ 0 := by positivity
  have h33 : (3 * (q : ℚ) + 3) ≠ 0 := by positivity
  have h34 : (3 * (q : ℚ) + 4) ≠ 0 := by positivity
  have h35 : (3 * (q : ℚ) + 5) ≠ 0 := by positivity
  have h36 : (3 * (q : ℚ) + 6) ≠ 0 := by positivity
  have h37 : (3 * (q : ℚ) + 7) ≠ 0 := by positivity
  have h38 : (3 * (q : ℚ) + 8) ≠ 0 := by positivity
  have h39 : (3 * (q : ℚ) + 9) ≠ 0 := by positivity
  interval_cases r
  · rw [show 3 * q + 0 + 6 = 3 * (q + 2) by ring, show 3 * (q + 2) - 1 = 3 * (q + 1) + 2 by omega,
      show 3 * (q + 2) - 2 = 3 * (q + 1) + 1 by omega, show 3 * (q + 2) - 3 = 3 * (q + 1) by omega,
      show 3 * (q + 2) - 4 = 3 * q + 2 by omega, show 3 * (q + 2) - 5 = 3 * q + 1 by omega,
      show 3 * (q + 2) - 6 = 3 * q by omega]
    rw [A0, A2, A1, A0, A2, A1, A0, g2, g1]
    unfold r1 r2 r4; push_cast
    field_simp; ring
  · rw [show 3 * q + 1 + 6 = 3 * (q + 2) + 1 by ring, show 3 * (q + 2) + 1 - 1 = 3 * (q + 2) by omega,
      show 3 * (q + 2) + 1 - 2 = 3 * (q + 1) + 2 by omega, show 3 * (q + 2) + 1 - 3 = 3 * (q + 1) + 1 by omega,
      show 3 * (q + 2) + 1 - 4 = 3 * (q + 1) by omega, show 3 * (q + 2) + 1 - 5 = 3 * q + 2 by omega,
      show 3 * (q + 2) + 1 - 6 = 3 * q + 1 by omega]
    rw [A1, A0, A2, A1, A0, A2, A1, g2, g1]
    unfold r1 r2 r4; push_cast
    field_simp; ring
  · rw [show 3 * q + 2 + 6 = 3 * (q + 2) + 2 by ring, show 3 * (q + 2) + 2 - 1 = 3 * (q + 2) + 1 by omega,
      show 3 * (q + 2) + 2 - 2 = 3 * (q + 2) by omega, show 3 * (q + 2) + 2 - 3 = 3 * (q + 1) + 2 by omega,
      show 3 * (q + 2) + 2 - 4 = 3 * (q + 1) + 1 by omega, show 3 * (q + 2) + 2 - 5 = 3 * (q + 1) by omega,
      show 3 * (q + 2) + 2 - 6 = 3 * q + 2 by omega]
    rw [A2, A1, A0, A2, A1, A0, A2, g2, g1]
    unfold r1 r2 r4; push_cast
    field_simp; ring
