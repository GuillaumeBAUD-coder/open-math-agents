import OMAStatements.S_oeis_a193663

namespace OMA.P193663

open OMA.S_oeis_a193663

/-- The coefficient of x^k in the n-th Fibonacci polynomial. -/
noncomputable def c (n k : ℕ) : ℤ := (F n).coeff k

lemma F_succ (n : ℕ) : F (n + 2) = Polynomial.X * F (n + 1) + F n := by
  rw [F]

lemma c_zero (k : ℕ) : c 0 k = 0 := by
  simp [c, F]

lemma c_one_zero : c 1 0 = 1 := by
  simp [c, F]

lemma c_one_succ (k : ℕ) : c 1 (k + 1) = 0 := by
  simp [c, F, Polynomial.coeff_one]

lemma c_zero_right (n : ℕ) : c (n + 2) 0 = c n 0 := by
  unfold c
  rw [F_succ, Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, zero_add]

lemma c_succ (n k : ℕ) : c (n + 2) (k + 1) = c (n + 1) k + c n (k + 1) := by
  unfold c
  rw [F_succ, Polynomial.coeff_add, Polynomial.coeff_X_mul]

lemma c_big (n : ℕ) : (∀ k, n ≤ k → c n k = 0) ∧ (∀ k, n + 1 ≤ k → c (n + 1) k = 0) := by
  induction n with
  | zero =>
    constructor
    · intro k _
      exact c_zero k
    · intro k hk
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact c_one_succ m
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e : c (n + 1 + 1) (m + 1) = c (n + 1) m + c n (m + 1) := c_succ n m
    rw [e, h1 m (by omega), h0 (m + 1) (by omega)]
    norm_num

lemma r_zero : r 0 = 1 := by
  rw [r]

lemma r_succ (k : ℕ) :
    r (k + 1) = ∑ m ∈ Finset.range (k + 1), ((k : ℤ) + 1 - (m : ℤ)) * r m := by
  rw [r]
  refine (Fin.sum_univ_eq_sum_range (fun j : ℕ => ((j : ℤ) + 1) * r (k - j)) (k + 1)).trans ?_
  refine Eq.trans ?_
    (Finset.sum_range_reflect (fun m : ℕ => ((k : ℤ) + 1 - (m : ℤ)) * r m) (k + 1))
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by
    have h := Finset.mem_range.mp hj
    omega
  have e : k + 1 - 1 - j = k - j := by omega
  show ((j : ℤ) + 1) * r (k - j) = ((k : ℤ) + 1 - ((k + 1 - 1 - j : ℕ) : ℤ)) * r (k + 1 - 1 - j)
  rw [e, Nat.cast_sub hjk]
  ring

lemma r_diff (k : ℕ) : r (k + 2) - r (k + 1) = ∑ m ∈ Finset.range (k + 2), r m := by
  have h2 : r (k + 2) = ∑ m ∈ Finset.range (k + 2), (((k + 1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m :=
    r_succ (k + 1)
  have h1 := r_succ k
  have hs : ∑ m ∈ Finset.range (k + 1), (((k + 1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m
      = ∑ m ∈ Finset.range (k + 1), ((k : ℤ) + 1 - (m : ℤ)) * r m
        + ∑ m ∈ Finset.range (k + 1), r m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    ring
  have e2 : ∑ m ∈ Finset.range (k + 2), (((k + 1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m
      = ∑ m ∈ Finset.range (k + 1), (((k + 1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m
        + (((k + 1 : ℕ) : ℤ) + 1 - ((k + 1 : ℕ) : ℤ)) * r (k + 1) :=
    Finset.sum_range_succ _ (k + 1)
  have e3 : ∑ m ∈ Finset.range (k + 2), r m
      = ∑ m ∈ Finset.range (k + 1), r m + r (k + 1) := Finset.sum_range_succ _ (k + 1)
  rw [h2, e2, hs, e3, h1]
  ring

lemma r_rec (k : ℕ) : r (k + 3) = 3 * r (k + 2) - r (k + 1) := by
  have d1 := r_diff k
  have d2 : r (k + 3) - r (k + 2) = ∑ m ∈ Finset.range (k + 3), r m := r_diff (k + 1)
  have e3 : ∑ m ∈ Finset.range (k + 3), r m
      = ∑ m ∈ Finset.range (k + 2), r m + r (k + 2) := Finset.sum_range_succ _ (k + 2)
  linarith

lemma r_one : r 1 = 1 := by
  have h : r 1 = ∑ m ∈ Finset.range 1, (((0 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m := r_succ 0
  rw [h, Finset.sum_range_one, r_zero]
  norm_num

lemma r_two : r 2 = 3 := by
  have h : r 2 = ∑ m ∈ Finset.range 2, (((1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m := r_succ 1
  have e : ∑ m ∈ Finset.range 2, (((1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m
      = ∑ m ∈ Finset.range 1, (((1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m
        + (((1 : ℕ) : ℤ) + 1 - ((1 : ℕ) : ℤ)) * r 1 := Finset.sum_range_succ _ 1
  rw [h, e, Finset.sum_range_one, r_zero, r_one]
  norm_num

/-- The weighted sums with the weights shifted by s. -/
noncomputable def B (s n : ℕ) : ℤ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c n p.1 * r (p.2 + s)

lemma a_eq (n : ℕ) : a n = B 0 n := by
  unfold a B
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

lemma B_step (s n : ℕ) : B s (n + 2) = B s (n + 1) + B (s + 2) n := by
  have h0 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 2), c (n + 2) p.1 * r (p.2 + s)
      = c (n + 2) 0 * r (n + 2 + s)
        + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c (n + 2) (p.1 + 1) * r (p.2 + s) :=
    Finset.Nat.sum_antidiagonal_succ (n := n + 1) (f := fun p => c (n + 2) p.1 * r (p.2 + s))
  have h1 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 2), c n p.1 * r (p.2 + s)
      = c n 0 * r (n + 2 + s)
        + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c n (p.1 + 1) * r (p.2 + s) :=
    Finset.Nat.sum_antidiagonal_succ (n := n + 1) (f := fun p => c n p.1 * r (p.2 + s))
  have h2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 2), c n p.1 * r (p.2 + s)
      = c n (n + 2) * r (0 + s)
        + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c n p.1 * r (p.2 + 1 + s) :=
    Finset.Nat.sum_antidiagonal_succ' (n := n + 1) (f := fun p => c n p.1 * r (p.2 + s))
  have h3 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c n p.1 * r (p.2 + 1 + s)
      = c n (n + 1) * r (0 + 1 + s)
        + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c n p.1 * r (p.2 + 1 + 1 + s) :=
    Finset.Nat.sum_antidiagonal_succ' (n := n) (f := fun p => c n p.1 * r (p.2 + 1 + s))
  have h4 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c (n + 2) (p.1 + 1) * r (p.2 + s)
      = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c (n + 1) p.1 * r (p.2 + s)
        + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c n (p.1 + 1) * r (p.2 + s) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [c_succ]
    ring
  have h5 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c n p.1 * r (p.2 + 1 + 1 + s)
      = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c n p.1 * r (p.2 + (s + 2)) := by
    apply Finset.sum_congr rfl
    intro p _
    have e : p.2 + 1 + 1 + s = p.2 + (s + 2) := by omega
    rw [e]
  have z1 : c n (n + 2) = 0 := (c_big n).1 (n + 2) (by omega)
  have z2 : c n (n + 1) = 0 := (c_big n).1 (n + 1) (by omega)
  have z3 := c_zero_right n
  unfold B
  rw [h0, h4, z3]
  rw [h3, h5, z1, z2] at h2
  linarith

lemma B_rec2 (n : ℕ) : B 2 n = 3 * B 1 n - B 0 n := by
  unfold B
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨k, m⟩ := p
  have hkm : k + m = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  show c n k * r (m + 2) = 3 * (c n k * r (m + 1)) - c n k * r (m + 0)
  rcases m with _ | m
  · have hz : c n k = 0 := (c_big n).1 k (by omega)
    rw [hz]
    ring
  · have h : r (m + 3) = 3 * r (m + 2) - r (m + 1) := r_rec m
    have e1 : m + 1 + 2 = m + 3 := by omega
    have e2 : m + 1 + 1 = m + 2 := by omega
    have e3 : m + 1 + 0 = m + 1 := by omega
    rw [e1, e2, e3, h]
    ring

lemma B_rec3 (n : ℕ) : B 3 n = 3 * B 2 n - B 1 n := by
  unfold B
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have h : r (p.2 + 3) = 3 * r (p.2 + 2) - r (p.2 + 1) := r_rec p.2
  rw [h]
  ring

lemma U (n : ℕ) : B 0 (n + 2) = B 0 (n + 1) + 3 * B 1 n - B 0 n := by
  have h : B 0 (n + 2) = B 0 (n + 1) + B 2 n := B_step 0 n
  rw [h, B_rec2]
  ring

lemma W (n : ℕ) : B 1 (n + 2) = B 1 (n + 1) + 8 * B 1 n - 3 * B 0 n := by
  have h : B 1 (n + 2) = B 1 (n + 1) + B 3 n := B_step 1 n
  rw [h, B_rec3, B_rec2]
  ring

lemma B_zero (s : ℕ) : B s 0 = 0 := by
  unfold B
  apply Finset.sum_eq_zero
  intro p _
  rw [c_zero]
  ring

lemma B_one (s : ℕ) : B s 1 = r (1 + s) := by
  have h0 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 1, c 1 p.1 * r (p.2 + s)
      = c 1 0 * r (0 + 1 + s)
        + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0, c 1 (p.1 + 1) * r (p.2 + s) :=
    Finset.Nat.sum_antidiagonal_succ (n := 0) (f := fun p => c 1 p.1 * r (p.2 + s))
  have h1 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0, c 1 (p.1 + 1) * r (p.2 + s) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    rw [c_one_succ]
    ring
  unfold B
  rw [h0, h1, c_one_zero]
  have e : 0 + 1 + s = 1 + s := by omega
  rw [e]
  ring

lemma a0 : a 0 = 0 := by rw [a_eq, B_zero]

lemma a1 : a 1 = 1 := by rw [a_eq, B_one, r_one]

lemma a2 : a 2 = 1 := by
  have h : B 0 2 = B 0 1 + 3 * B 1 0 - B 0 0 := U 0
  rw [a_eq, h, B_one, B_zero, B_zero, r_one]
  norm_num

lemma a3 : a 3 = 9 := by
  have h : B 0 3 = B 0 2 + 3 * B 1 1 - B 0 1 := U 1
  have h2 : B 0 2 = B 0 1 + 3 * B 1 0 - B 0 0 := U 0
  have e : r (1 + 1) = 3 := r_two
  rw [a_eq, h, h2, B_one, B_one, B_zero, B_zero, r_one, e]
  norm_num

lemma arec (k : ℕ) : a (k + 4) = 2 * a (k + 3) + 6 * a (k + 2) - 7 * a (k + 1) - a k := by
  rw [a_eq, a_eq, a_eq, a_eq, a_eq]
  have u0 : B 0 (k + 2) = B 0 (k + 1) + 3 * B 1 k - B 0 k := U k
  have u1 : B 0 (k + 3) = B 0 (k + 2) + 3 * B 1 (k + 1) - B 0 (k + 1) := U (k + 1)
  have u2 : B 0 (k + 4) = B 0 (k + 3) + 3 * B 1 (k + 2) - B 0 (k + 2) := U (k + 2)
  have w0 : B 1 (k + 2) = B 1 (k + 1) + 8 * B 1 k - 3 * B 0 k := W k
  linarith

end OMA.P193663

open OMA.S_oeis_a193663 OMA.P193663 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a193663.main := by
  have hD : ∀ f : ℤ⟦X⟧, f * (1 - 2 * X - 6 * X ^ 2 + 7 * X ^ 3 + X ^ 4)
      = f - (f * X + f * X) - (f * X ^ 2 + f * X ^ 2 + f * X ^ 2 + f * X ^ 2 + f * X ^ 2
          + f * X ^ 2)
        + (f * X ^ 3 + f * X ^ 3 + f * X ^ 3 + f * X ^ 3 + f * X ^ 3 + f * X ^ 3 + f * X ^ 3)
        + f * X ^ 4 := by
    intro f; ring
  have hN : (X : ℤ⟦X⟧) * (1 - X + X ^ 2) = X - X ^ 2 + X ^ 3 := by ring
  rw [hD, hN]
  ext n
  have hx : ∀ f : ℤ⟦X⟧,
      PowerSeries.coeff n (f * X) = if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
    intro f
    have := PowerSeries.coeff_mul_X_pow' (p := f) (n := 1) (d := n)
    simpa using this
  simp only [map_sub, map_add, PowerSeries.coeff_mul_X_pow', hx, PowerSeries.coeff_mk,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | k
  · simp [a0]
  · simp [a0, a1]
  · simp [a0, a1, a2]
  · simp [a0, a1, a2, a3]
  · have h := arec k
    have e4 : k + 1 + 1 + 1 + 1 = k + 4 := rfl
    simp only [e4]
    have c4 : 4 ≤ k + 4 := by omega
    have c3 : 3 ≤ k + 4 := by omega
    have c2 : 2 ≤ k + 4 := by omega
    have c1 : 1 ≤ k + 4 := by omega
    have n1 : ¬ (k + 4 = 1) := by omega
    have n2 : ¬ (k + 4 = 2) := by omega
    have n3 : ¬ (k + 4 = 3) := by omega
    have s4 : k + 4 - 4 = k := by omega
    have s3 : k + 4 - 3 = k + 1 := by omega
    have s2 : k + 4 - 2 = k + 2 := by omega
    have s1 : k + 4 - 1 = k + 3 := by omega
    simp only [c4, c3, c2, c1, n1, n2, n3, s4, s3, s2, s1, if_true, if_false]
    linarith
