import OMAStatements.S_oeis_a266717
import Mathlib

open OMA.S_oeis_a266717

private def live (t : ℕ) (i : ℤ) : Prop :=
    (t = 0 ∧ (i = 0)) ∨
    (t = 1 ∧ (i ≠ 0)) ∨
    (2 ≤ t ∧ t % 2 = 0 ∧ (-(t : ℤ) ≤ i ∧ i ≤ t ∧ (i = ((t / 2 : ℕ) : ℤ) - 1 ∨ i = ((t / 2 : ℕ) : ℤ)))) ∨
    (2 ≤ t ∧ t % 2 = 1 ∧ ((-(t : ℤ) ≤ i ∧ i ≤ t ∧ ¬(i = ((t / 2 : ℕ) : ℤ))) ∨ ((i < -(t : ℤ) ∨ (t : ℤ) < i))))

private lemma table (l c r : Bool) :
    eca 59 l c r = true ↔ c = false ∨ (l = false ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih]
    rcases Nat.lt_or_ge t 2 with h | h
    · simp only [live]
      interval_cases t <;> omega
    · simp only [live, eq_false (show ¬ t = 0 by omega), eq_false (show ¬ t = 1 by omega), eq_false (show ¬ t + 1 = 0 by omega), eq_false (show ¬ t + 1 = 1 by omega), eq_true (show 2 ≤ t by omega), eq_true (show 2 ≤ t + 1 by omega), false_and, false_or, or_false, true_and]
      omega

private lemma wsum (n : ℕ) (f : ℕ → ℤ) (c : ℤ) (w : ℕ → ℤ) (E : Finset ℕ)
    (hE : E ⊆ Finset.range n) (h : ∀ k < n, k ∉ E → f k = c * w k) :
    ∑ k ∈ Finset.range n, f k = c * ∑ k ∈ Finset.range n, w k + ∑ k ∈ E, (f k - c * w k) := by
  rw [Finset.sum_subset hE (fun k hk hkE => by rw [h k (Finset.mem_range.mp hk) hkE]; ring),
    Finset.sum_sub_distrib, Finset.mul_sum]
  ring

private lemma geo (t : ℕ) : ((10 : ℤ) - 1) * ∑ k ∈ Finset.range (2 * t + 1), (10 : ℤ) ^ (2 * t - k) =
    (10 : ℤ) ^ (2 * t + 1) - 1 := by
  have := Finset.sum_range_reflect (fun j => (10 : ℤ) ^ j) (2 * t + 1)
  simp only [show 2 * t + 1 - 1 = 2 * t by omega] at this
  rw [this, mul_comm, geom_sum_mul]

private lemma aval (t : ℕ) : (a t : ℤ) =
    ∑ k ∈ Finset.range (2 * t + 1), (if state t ((k : ℤ) - t) then (10 : ℤ) ^ (2 * t - k) else 0) := by
  unfold a; push_cast; rfl

private lemma row0 (m : ℕ) (hm : 1 ≤ m) :
    ((9 : ℤ) * (10 : ℤ) ^ 0) * (a (2 * m) : ℤ) = (9 : ℤ) * (10 : ℤ) ^ (1 * m + 1) + (9 : ℤ) * (10 : ℤ) ^ (1 * m + 0) := by
  have key := wsum (2 * (2 * m) + 1)
    (fun k => if state (2 * m) ((k : ℤ) - ((2 * m) : ℕ)) then (10 : ℤ) ^ (2 * (2 * m) - k) else 0) (0 : ℤ)
    (fun k => (10 : ℤ) ^ (2 * (2 * m) - k)) ({3 * m - 1, 3 * m + 0} : Finset ℕ)
    (by intro k hk; simp at hk ⊢ <;> omega)
    (by
      intro k hk hkE
      have hs : state (2 * m) ((k : ℤ) - ((2 * m) : ℕ)) = false := by
        rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; unfold live at hh; simp at hkE; push_cast at hh <;> omega
      beta_reduce; rw [hs]; simp)
  rw [Finset.sum_insert (by simp <;> omega), Finset.sum_singleton] at key
  have h0 : state (2 * m) (((3 * m - 1 : ℕ) : ℤ) - ((2 * m) : ℕ)) = true := by
    rw [state_iff]; unfold live; push_cast <;> omega
  have h1 : state (2 * m) (((3 * m + 0 : ℕ) : ℤ) - ((2 * m) : ℕ)) = true := by
    rw [state_iff]; unfold live; push_cast <;> omega
  simp only [h0, h1, if_true, if_false, Bool.false_eq_true, ↓reduceIte] at key
  have q0 : (10 : ℤ) ^ 0 * (10 : ℤ) ^ (2 * (2 * m) - (3 * m - 1)) = (10 : ℤ) ^ (1 * m + 1) := by
    rw [← pow_add]; congr 1; omega
  have q1 : (10 : ℤ) ^ 0 * (10 : ℤ) ^ (2 * (2 * m) - (3 * m + 0)) = (10 : ℤ) ^ (1 * m + 0) := by
    rw [← pow_add]; congr 1; omega
  have g := geo (2 * m)
  rw [aval]
  linear_combination ((9 : ℤ) * (10 : ℤ) ^ 0) * key + (0 : ℤ) * (10 : ℤ) ^ 0 * g + (9 : ℤ) * q0 + (9 : ℤ) * q1

private lemma row1 (m : ℕ) (hm : 1 ≤ m) :
    ((9 : ℤ) * (10 : ℤ) ^ 0) * (a (2 * m + 1) : ℤ) = ((10 : ℤ) ^ (2 * (2 * m + 1) + 1 + 0) - (10 : ℤ) ^ 0) - (9 : ℤ) * (10 : ℤ) ^ (1 * m + 1) := by
  have key := wsum (2 * (2 * m + 1) + 1)
    (fun k => if state (2 * m + 1) ((k : ℤ) - ((2 * m + 1) : ℕ)) then (10 : ℤ) ^ (2 * (2 * m + 1) - k) else 0) (1 : ℤ)
    (fun k => (10 : ℤ) ^ (2 * (2 * m + 1) - k)) ({3 * m + 1} : Finset ℕ)
    (by intro k hk; simp at hk ⊢ <;> omega)
    (by
      intro k hk hkE
      have hs : state (2 * m + 1) ((k : ℤ) - ((2 * m + 1) : ℕ)) = true := by
        rw [state_iff]; unfold live; simp at hkE; push_cast <;> omega
      beta_reduce; rw [hs]; simp)
  rw [Finset.sum_singleton] at key
  have h0 : state (2 * m + 1) (((3 * m + 1 : ℕ) : ℤ) - ((2 * m + 1) : ℕ)) = false := by
    rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; unfold live at hh; push_cast at hh <;> omega
  simp only [h0, if_true, if_false, Bool.false_eq_true, ↓reduceIte] at key
  have q0 : (10 : ℤ) ^ 0 * (10 : ℤ) ^ (2 * (2 * m + 1) - (3 * m + 1)) = (10 : ℤ) ^ (1 * m + 1) := by
    rw [← pow_add]; congr 1; omega
  have g := geo (2 * m + 1)
  rw [aval]
  linear_combination ((9 : ℤ) * (10 : ℤ) ^ 0) * key + (1 : ℤ) * (10 : ℤ) ^ 0 * g + (-9 : ℤ) * q0

private lemma v0 : a 0 = 1 := by decide

private lemma v1 : a 1 = 101 := by decide

set_option maxRecDepth 100000 in
private lemma v2 : a 2 = 110 := by
  have h := row0 1 (by norm_num)
  rw [show 2 * 1 = 2 from rfl] at h
  generalize a 2 = x at h ⊢
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v3 : a 3 = 1111011 := by
  have h := row1 1 (by norm_num)
  rw [show 2 * 1 + 1 = 3 from rfl] at h
  generalize a 3 = x at h ⊢
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v4 : a 4 = 1100 := by
  have h := row0 2 (by norm_num)
  rw [show 2 * 2 = 4 from rfl] at h
  generalize a 4 = x at h ⊢
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v5 : a 5 = 11111110111 := by
  have h := row1 2 (by norm_num)
  rw [show 2 * 2 + 1 = 5 from rfl] at h
  generalize a 5 = x at h ⊢
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v6 : a 6 = 11000 := by
  have h := row0 3 (by norm_num)
  rw [show 2 * 3 = 6 from rfl] at h
  generalize a 6 = x at h ⊢
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v7 : a 7 = 111111111101111 := by
  have h := row1 3 (by norm_num)
  rw [show 2 * 3 + 1 = 7 from rfl] at h
  generalize a 7 = x at h ⊢
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v8 : a 8 = 110000 := by
  have h := row0 4 (by norm_num)
  rw [show 2 * 4 = 8 from rfl] at h
  generalize a 8 = x at h ⊢
  norm_num at h
  omega

set_option maxRecDepth 100000 in
private lemma v9 : a 9 = 1111111111111011111 := by
  have h := row1 4 (by norm_num)
  rw [show 2 * 4 + 1 = 9 from rfl] at h
  generalize a 9 = x at h ⊢
  norm_num at h
  omega

private lemma recur (n : ℕ) (hn : 6 < n) : (a n : ℤ) = (10011 : ℤ) * a (n - 2) + (-110010 : ℤ) * a (n - 4) + (100000 : ℤ) * a (n - 6) := by
  by_cases h : 9 < n
  · rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
    · obtain ⟨p, rfl⟩ : ∃ p, q = p + 4 := ⟨q - 4, by omega⟩
      simp only [show 2 * (p + 4) - 2 = 2 * (p + 3) + 0 by omega, show 2 * (p + 4) - 4 = 2 * (p + 2) + 0 by omega, show 2 * (p + 4) - 6 = 2 * (p + 1) + 0 by omega]
      have h0 := row0 (p + 4) (by omega)
      have h1 := row0 (p + 3) (by omega)
      have h2 := row0 (p + 2) (by omega)
      have h3 := row0 (p + 1) (by omega)
      have : (2 * ((9 : ℤ) * (10 : ℤ) ^ 0)) * (a (2 * (p + 4)) - ((10011 : ℤ) * a (2 * (p + 3) + 0) + (-110010 : ℤ) * a (2 * (p + 2) + 0) + (100000 : ℤ) * a (2 * (p + 1) + 0))) = 0 := by
        linear_combination 2 * (h0 - (10011) * h1 - (-110010) * h2 - (100000) * h3)
      have := (mul_eq_zero.mp this).resolve_left (by norm_num)
      linarith
    · obtain ⟨p, rfl⟩ : ∃ p, q = p + 4 := ⟨q - 4, by omega⟩
      simp only [show 2 * (p + 4) + 1 - 2 = 2 * (p + 3) + 1 by omega, show 2 * (p + 4) + 1 - 4 = 2 * (p + 2) + 1 by omega, show 2 * (p + 4) + 1 - 6 = 2 * (p + 1) + 1 by omega]
      have h0 := row1 (p + 4) (by omega)
      have h1 := row1 (p + 3) (by omega)
      have h2 := row1 (p + 2) (by omega)
      have h3 := row1 (p + 1) (by omega)
      have : (2 * ((9 : ℤ) * (10 : ℤ) ^ 0)) * (a (2 * (p + 4) + 1) - ((10011 : ℤ) * a (2 * (p + 3) + 1) + (-110010 : ℤ) * a (2 * (p + 2) + 1) + (100000 : ℤ) * a (2 * (p + 1) + 1))) = 0 := by
        linear_combination 2 * (h0 - (10011) * h1 - (-110010) * h2 - (100000) * h3)
      have := (mul_eq_zero.mp this).resolve_left (by norm_num)
      linarith
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]

open PowerSeries in
private lemma gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2)) = (1 + 101 * X - 9901 * X ^ 2 + 99900 * X ^ 3 - 990100 * X ^ 4 - 110000 * X ^ 5 + 1000000 * X ^ 6 : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2)) = F + (-10011 : ℤ) • (F * X ^ 2) + (110010 : ℤ) • (F * X ^ 4) + (-100000 : ℤ) • (F * X ^ 6) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 + 101 * X - 9901 * X ^ 2 + 99900 * X ^ 3 - 990100 * X ^ 4 - 110000 * X ^ 5 + 1000000 * X ^ 6 : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (101 : ℤ) • X ^ 1 + (-9901 : ℤ) • X ^ 2 + (99900 : ℤ) • X ^ 3 + (-990100 : ℤ) • X ^ 4 + (-110000 : ℤ) • X ^ 5 + (1000000 : ℤ) • X ^ 6 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 6 < n
  · have hr := recur n (by omega)
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, show 6 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9]

theorem OMA.solution : type_of% @OMA.S_oeis_a266717.main := by
  exact ⟨fun n hn => by have := recur n hn; linarith, gf⟩
