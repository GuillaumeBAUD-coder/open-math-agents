import OMAStatements.S_oeis_a118109

-- Problem: A118109: Binary representation of n-th iteration of the Rule 54 elementary cellular automaton starting with a single black cell.
-- Upstream: formal-conjectures statements/oeis-a118109.lean:0 (declaration OMA.S_oeis_a118109.main)
-- Credit: @caa1982 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace R54
open OMA.S_oeis_a118109

def f (t : ℕ) (i : ℤ) : Bool :=
  decide (-(t : ℤ) ≤ i ∧ i ≤ t ∧ ((t % 2 = 0 ∧ (i + t) % 4 = 0) ∨ (t % 2 = 1 ∧ (i + t) % 4 ≠ 3)))

lemma rule54 (l c r : Bool) : ruleOut 54 l c r = xor c (l || r) := by
  cases l <;> cases c <;> cases r <;> rfl

lemma cell_eq (t : ℕ) (i : ℤ) : cell 54 t i = f t i := by
  induction t generalizing i with
  | zero =>
    simp only [cell, f]
    by_cases h : i = 0 <;> simp [h] <;> omega
  | succ t ih =>
    show ruleOut 54 (cell 54 t (i - 1)) (cell 54 t i) (cell 54 t (i + 1)) = _
    rw [rule54, ih, ih, ih]
    cases h1 : f t (i - 1) <;> cases h2 : f t i <;> cases h3 : f t (i + 1) <;>
      cases h4 : f (t + 1) i <;>
      simp only [f, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 h4 <;>
      first | rfl | (exfalso; omega)

def c (n : ℕ) : ℤ := if n % 2 = 0 then 1 else 111

lemma hlast (n : ℕ) : ∑ k ∈ Finset.range 4, (if cell 54 (n+2) (((2*n+1+k : ℕ) : ℤ) - ((n+2 : ℕ) : ℤ)) then (10:ℤ) ^ (2*(n+2) - (2*n+1+k)) else 0) = c n := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cell_eq]
  have e0 : 2*(n+2) - (2*n+1+0) = 3 := by omega
  have e1 : 2*(n+2) - (2*n+1+1) = 2 := by omega
  have e2 : 2*(n+2) - (2*n+1+2) = 1 := by omega
  have e3 : 2*(n+2) - (2*n+1+3) = 0 := by omega
  rw [e0, e1, e2, e3]
  unfold c
  cases h1 : f (n+2) (((2*n+1+0 : ℕ) : ℤ) - ((n+2 : ℕ) : ℤ)) <;>
  cases h2 : f (n+2) (((2*n+1+1 : ℕ) : ℤ) - ((n+2 : ℕ) : ℤ)) <;>
  cases h3 : f (n+2) (((2*n+1+2 : ℕ) : ℤ) - ((n+2 : ℕ) : ℤ)) <;>
  cases h4 : f (n+2) (((2*n+1+3 : ℕ) : ℤ) - ((n+2 : ℕ) : ℤ)) <;>
  simp only [f, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 h4 <;>
  simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> first | (exfalso; omega) | norm_num

lemma a_succ2 (n : ℕ) : a (n+2) = 10000 * a n + c n := by
  unfold a
  rw [show 2*(n+2)+1 = (2*n+1)+4 by ring, Finset.sum_range_add, hlast]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [cell_eq, cell_eq]
  have hf : f (n+2) ((j:ℤ) - ((n+2:ℕ):ℤ)) = f n ((j:ℤ) - (n:ℤ)) := by
    cases h1 : f (n+2) ((j:ℤ) - ((n+2:ℕ):ℤ)) <;> cases h2 : f n ((j:ℤ) - (n:ℤ)) <;>
      simp only [f, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 <;>
      first | rfl | (exfalso; omega)
  rw [hf]
  split_ifs
  · rw [show 2*(n+2) - j = 4 + (2*n - j) by omega, pow_add]; norm_num
  · simp

lemma a0 : a 0 = 1 := by decide
lemma a1 : a 1 = 111 := by decide

lemma c_succ2 (n : ℕ) : c (n+2) = c n := by
  unfold c
  have : (n + 2) % 2 = n % 2 := by omega
  rw [this]

lemma rec1 (m : ℕ) : a (m+4) = 10001 * a (m+2) - 10000 * a m := by
  have h1 := a_succ2 (m+2)
  have h2 := a_succ2 m
  rw [c_succ2] at h1
  linarith

lemma key (n : ℕ) : 9999 * a n = (10000 + 1100 * ((n:ℤ) % 2)) * 100 ^ n - c n ∧
    9999 * a (n+1) = (10000 + 1100 * (((n+1 : ℕ):ℤ) % 2)) * 100 ^ (n+1) - c (n+1) := by
  induction n with
  | zero => rw [a0, a1]; decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [a_succ2, c_succ2]
    have e : (((n+1+1 : ℕ):ℤ) % 2) = ((n:ℤ) % 2) := by omega
    rw [e, pow_succ, pow_succ]
    have := ih.1
    linarith

lemma c_bounds (n : ℕ) : 1 ≤ c n ∧ c n ≤ 111 := by
  unfold c; split_ifs <;> norm_num

open PowerSeries in
theorem sol :
    (∀ n > 3, a n = 10001 * a (n - 2) - 10000 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) = 1 + 111 * X) ∧
    (∀ n : ℕ, (a n : ℚ) = ((⌊((10000 + 1100 * (((n : ℤ) % 2 : ℤ) : ℚ)) * (100 : ℚ) ^ (n : ℤ) / 9999 : ℚ)⌋ : ℤ) : ℚ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega]
    exact rec1 m
  · have hC1 : (C (10001:ℚ) : ℚ⟦X⟧) = 10001 := map_ofNat C 10001
    have hC2 : (C (10000:ℚ) : ℚ⟦X⟧) = 10000 := map_ofNat C 10000
    have hC3 : (C (111:ℚ) : ℚ⟦X⟧) = 111 := map_ofNat C 111
    have hP : ∀ A : ℚ⟦X⟧, A * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) =
        A - C (10001:ℚ) * (A * X^2) + C (10000:ℚ) * (A * X^4) := by
      intro A; rw [hC1, hC2]; ring
    rw [hP, ← hC3]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one, coeff_X]
    rcases n with _ | _ | _ | _ | n
    · simp [a0]
    · simp [a1]
    · simp [a0, show a 2 = 10001 by decide]
    · norm_num [a1, show a 3 = 1110111 by decide]
    · simp only [show n + 1 + 1 + 1 + 1 = n + 4 by omega]
      simp only [show 2 ≤ n + 4 by omega, show 4 ≤ n + 4 by omega, if_true,
        show n + 4 - 2 = n + 2 by omega, show n + 4 - 4 = n by omega]
      simp
      have := rec1 n
      have h : ((a (n+4) : ℤ) : ℚ) = 10001 * (a (n+2) : ℚ) - 10000 * (a n : ℚ) := by
        rw [this]; push_cast; ring
      linarith
  · intro n
    have hk := (key n).1
    have hc := c_bounds n
    have hx : ((10000 + 1100 * (((n:ℤ) % 2 : ℤ) : ℚ)) * (100:ℚ) ^ (n:ℤ) / 9999) =
        (a n : ℚ) + (c n : ℚ) / 9999 := by
      rw [zpow_natCast]
      have h := congrArg (fun z : ℤ => (z:ℚ)) hk
      push_cast at h
      field_simp
      linarith
    rw [hx]
    have hf : ⌊(a n : ℚ) + (c n : ℚ) / 9999⌋ = a n := by
      rw [Int.floor_eq_iff]
      have h1 : (1:ℚ) ≤ c n := by exact_mod_cast hc.1
      have h2 : (c n : ℚ) ≤ 111 := by exact_mod_cast hc.2
      constructor
      · have : (0:ℚ) ≤ (c n : ℚ) / 9999 := by positivity
        linarith
      · have : (c n : ℚ) / 9999 < 1 := by rw [div_lt_one (by norm_num)]; linarith
        linarith
    rw [hf]

end R54

theorem OMA.solution : type_of% @OMA.S_oeis_a118109.main := R54.sol
