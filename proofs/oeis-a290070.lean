import OMAStatements.S_oeis_a290070

open OMA.S_oeis_a290070 PowerSeries

namespace Diagonal641

def background (r : ℕ) : ℕ → Bool
  | 0 => false
  | n+1 => r.testBit (9*(background r n).toNat)

lemma outside (r t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| ∨ (t : ℤ) < |y|) :
    state r t x y = background r t := by
  induction t generalizing x y with
  | zero =>
    simp only [state, background, decide_eq_false_iff_not]
    rintro ⟨rfl,rfl⟩
    simp at h
  | succ t ih =>
    simp only [Nat.cast_succ, lt_abs] at h
    simp only [state, background]
    rw [ih x y (by simp only [lt_abs]; omega),
        ih (x-1) y (by simp only [lt_abs]; omega),
        ih (x+1) y (by simp only [lt_abs]; omega),
        ih x (y-1) (by simp only [lt_abs]; omega),
        ih x (y+1) (by simp only [lt_abs]; omega)]
    cases background r t <;> rfl

lemma iterate_cycle (r s p n : ℕ) (h : state r (s+p) = state r s) :
    state r (s+n+p) = state r (s+n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [show s+(n+1)+p = (s+n+p)+1 by omega, show s+(n+1) = (s+n)+1 by omega]
    funext x y
    simp only [state,ih]

lemma cycle : state 641 4 = state 641 2 := by
  funext x y
  by_cases h : (4 : ℤ) < |x| ∨ (4 : ℤ) < |y|
  · rw [outside 641 4 x y h, outside 641 2 x y (by rcases h with h|h <;> omega)]
    decide
  · simp only [not_or, not_lt, abs_le] at h
    obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := h
    interval_cases x <;> interval_cases y <;> decide

lemma cycle_at (n : ℕ) (hn : 2 ≤ n) : state 641 (n+2) = state 641 n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2+k := ⟨n-2, by omega⟩
  exact iterate_cycle 641 2 2 k cycle

lemma bg_on (n : ℕ) : background 641 (n+1) = true := by
  induction n with
  | zero => decide
  | succ n ih => rw [background, ih]; decide

lemma word (n : ℕ) : a n =
    ∑ i ∈ Finset.range (n+1), ((state 641 n (-(i:ℤ)) (-(i:ℤ))).toNat:ℤ)*10^i := by
  unfold a digits
  rw [← Finset.sum_range_reflect (fun i => ((state 641 n (-(i:ℤ)) (-(i:ℤ))).toNat:ℤ)*10^i) (n+1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  simp only [Nat.add_sub_cancel]
  rw [show -((n-i:ℕ):ℤ) = (i:ℤ)-n by omega]

lemma advance (n : ℕ) (hn : 2 ≤ n) : a (n+2) = a n + 10^(n+1) + 10^(n+2) := by
  have bg : background 641 n = true := by convert bg_on (n-1) using 2 <;> omega
  have edge (k : ℕ) (hk : n < k) : state 641 n (-(k:ℤ)) (-(k:ℤ)) = true :=
    (outside _ _ _ _ (Or.inl (by simp only [abs_neg, Int.abs_natCast]; exact_mod_cast hk))).trans bg
  rw [word, word, Finset.sum_range_succ, Finset.sum_range_succ, cycle_at n hn,
    edge (n+1) (by omega), edge (n+2) (by omega)]
  simp

lemma recurrence (n : ℕ) (hn : 4 < n) :
    a n = 10*a (n-1)+a (n-2)-10*a (n-3) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+5 := ⟨n-5, by omega⟩
  have h := advance (k+3) (by omega)
  have j := advance (k+2) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, pow_add] at h j
  simp only [show k+5-1=k+4 by omega, show k+5-2=k+3 by omega, show k+5-3=k+2 by omega]
  linarith only [h,j]
lemma axis_agrees (n : ℕ) (hn : 2 ≤ n) (x : ℤ) : state 641 n x x = state 641 n x 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < 4
    · by_cases hx : (3 : ℤ) < |x|
      · rw [outside _ _ _ _ (Or.inl (by omega)), outside _ _ _ _ (Or.inl (by omega))]
      · simp only [not_lt, abs_le] at hx
        obtain ⟨_, _⟩ := hx
        interval_cases n <;> interval_cases x <;> first | omega | decide
    · obtain ⟨k, rfl⟩ : ∃ k, n=k+2 := ⟨n-2, by omega⟩
      rw [cycle_at k (by omega)]
      exact ih k (by omega) (by omega)


lemma left_axis (n : ℕ) (h : 2 ≤ n) : a n =
    ∑ i ∈ Finset.range (n+1), ((state 641 n ((i:ℤ)-n) 0).toNat:ℤ)*10^(n-i) := by
  unfold a digits
  apply Finset.sum_congr rfl
  intro i _
  rw [axis_agrees n h]

lemma gf : mk a * ((1 - X) * (1 + X) * (1 - 10 * X)) = 1 + 90 * X ^ 3 + 100 * X ^ 4 := by
  have hd : mk a * ((1 - X) * (1 + X) * (1 - 10 * X)) = (1 : ℤ) • (mk a * X ^ 0)
      + (-10 : ℤ) • (mk a * X ^ 1)
      + (-1 : ℤ) • (mk a * X ^ 2)
      + (10 : ℤ) • (mk a * X ^ 3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have hp : (1 + 90 * X ^ 3 + 100 * X ^ 4 : PowerSeries ℤ) = (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (90 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (100 : ℤ) • (X ^ 4 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [hd,hp]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
  by_cases h : n ≤ 4
  · have h0 : a 0 = 1 := by decide
    have h1 : a 1 = 10 := by decide
    have h2 : a 2 = 101 := by decide
    have h3 : a 3 = 1100 := by decide
    have h4 : a 4 = 11101 := by decide
    interval_cases n <;> norm_num [zsmul_eq_mul, h0, h1, h2, h3, h4]
  · simp only [Nat.sub_zero, zsmul_eq_mul, if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_pos (show 0 ≤ n by omega),
      if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega)]
    norm_num
    linarith only [recurrence n (by omega)]


end Diagonal641

theorem OMA.solution : type_of% @OMA.S_oeis_a290070.main := by
  exact ⟨Diagonal641.gf, fun n hn => ⟨Diagonal641.recurrence n hn, Diagonal641.left_axis n (by omega)⟩⟩
