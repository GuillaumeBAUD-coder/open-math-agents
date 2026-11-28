import OMAStatements.S_oeis_a177169

namespace OMA.P_oeis_a177169

open OMA.S_oeis_a177169

private def conv (u v : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), u i * v (n - i)

private lemma conv_comm (u v : ℕ → ℤ) (n : ℕ) : conv u v n = conv v u n := by
  unfold conv
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsub : n + 1 - 1 - k = n - k := by omega
  rw [hsub, Nat.sub_sub_self hk', mul_comm]

private lemma conv_assoc (u v w : ℕ → ℤ) (n : ℕ) :
    conv (conv u v) w n = conv u (conv v w) n := by
  unfold conv
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma' (Finset.range (n + 1)) (fun m => Finset.range (m + 1))
        (fun m i => u i * v (m - i) * w (n - m)),
      Finset.sum_sigma' (Finset.range (n + 1)) (fun i => Finset.range (n - i + 1))
        (fun i j => u i * (v j * w (n - i - j)))]
  refine Finset.sum_nbij' (fun p : Σ _ : ℕ, ℕ => (⟨p.2, p.1 - p.2⟩ : Σ _ : ℕ, ℕ))
      (fun q : Σ _ : ℕ, ℕ => (⟨q.1 + q.2, q.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢
    omega
  · rintro ⟨m, i⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    exact Sigma.ext (by dsimp only; omega) HEq.rfl
  · rintro ⟨i, j⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq
    exact Sigma.ext rfl (heq_of_eq (by dsimp only; omega))
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    dsimp only
    have hsub : n - p.2 - (p.1 - p.2) = n - p.1 := by omega
    rw [hsub, mul_assoc]

private lemma two_mul_conv_mul_nat (u : ℕ → ℤ) (n : ℕ) :
    2 * conv (fun k => (k : ℤ) * u k) u n = (n : ℤ) * conv u u n := by
  have hrefl : conv (fun k => (k : ℤ) * u k) u n =
      ∑ k ∈ Finset.range (n + 1), ((n - k : ℕ) : ℤ) * u (n - k) * u k := by
    unfold conv
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n + 1 - 1 - k = n - k := by omega
    rw [hsub, Nat.sub_sub_self hk']
  calc
    2 * conv (fun k => (k : ℤ) * u k) u n
        = conv (fun k => (k : ℤ) * u k) u n + conv (fun k => (k : ℤ) * u k) u n := by ring
    _ = (∑ k ∈ Finset.range (n + 1), (k : ℤ) * u k * u (n - k)) +
        (∑ k ∈ Finset.range (n + 1), ((n - k : ℕ) : ℤ) * u (n - k) * u k) := by
          conv_rhs => rw [← hrefl]
          rfl
    _ = ∑ k ∈ Finset.range (n + 1),
        ((k : ℤ) * u k * u (n - k) + ((n - k : ℕ) : ℤ) * u (n - k) * u k) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.range (n + 1), (n : ℤ) * (u k * u (n - k)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [Nat.cast_sub hk']
          ring
    _ = (n : ℤ) * conv u u n := by
          rw [← Finset.mul_sum]
          rfl

private lemma conv_deriv_identity (u : ℕ → ℤ) (n : ℕ) :
    conv (fun k => (k : ℤ) * conv u u k) u n =
      2 * conv (conv u u) (fun k => (k : ℤ) * u k) n := by
  have h1 : conv (fun k => (k : ℤ) * conv u u k) u n =
      conv (fun k => 2 * conv (fun j => (j : ℤ) * u j) u k) u n := by
    congr 1
    funext k
    exact (two_mul_conv_mul_nat u k).symm
  have h2 : conv (fun k => 2 * conv (fun j => (j : ℤ) * u j) u k) u n =
      2 * conv (conv (fun j => (j : ℤ) * u j) u) u n := by
    change ∑ k ∈ Finset.range (n + 1), (2 * conv (fun j => (j : ℤ) * u j) u k) * u (n - k) =
      2 * ∑ k ∈ Finset.range (n + 1), conv (fun j => (j : ℤ) * u j) u k * u (n - k)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2, conv_assoc, conv_comm]

private lemma a_rec (m : ℕ) : a (m + 2) = conv a a (m + 1) - 2 := by
  conv_lhs => rw [a]
  rw [conv, Fin.sum_univ_eq_sum_range (fun p => a p * a (m + 1 - p) + 0) (m + 2)]
  simp only [add_zero]
  ring

private lemma a_0 : a 0 = 1 := by simp [a]
private lemma a_1 : a 1 = 7 := by simp [a]

private lemma a_2 : a 2 = 12 := by
  rw [a_rec 0]
  unfold conv
  simp [Finset.sum_range_succ, a_0, a_1]

private lemma a_3 : a 3 = 71 := by
  rw [a_rec 1]
  unfold conv
  simp [Finset.sum_range_succ, a_0, a_1, a_2]

private lemma a_4 : a 4 = 308 := by
  rw [a_rec 2]
  unfold conv
  simp [Finset.sum_range_succ, a_0, a_1, a_2, a_3]

private def f : ℕ → ℤ
  | 0 => -1
  | k + 1 => 2 * a k

private def d : ℕ → ℤ
  | 0 => 1
  | 1 => -1
  | _ + 2 => 0

private def g : ℕ → ℤ := conv d f

private lemma conv_d_zero (u : ℕ → ℤ) : conv d u 0 = u 0 := by
  simp [conv, d]

private lemma conv_d_succ (u : ℕ → ℤ) (k : ℕ) : conv d u (k + 1) = u (k + 1) - u k := by
  unfold conv
  have hsub : ∑ i ∈ Finset.range (k + 2), d i * u (k + 1 - i) =
      ∑ i ∈ Finset.range 2, d i * u (k + 1 - i) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
    simp only [Finset.mem_range, not_lt] at hi
    rcases i with _ | _ | i
    · omega
    · omega
    · simp [d]
  rw [hsub]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.sub_zero, Nat.add_sub_cancel, d]
  ring

private lemma conv_f_f_0 : conv f f 0 = 1 := by
  simp [conv, f]

private lemma conv_f_f_1 : conv f f 1 = -4 := by
  unfold conv
  simp [Finset.sum_range_succ, f, a_0]

private lemma conv_f_f_2 : conv f f 2 = -24 := by
  unfold conv
  simp [Finset.sum_range_succ, f, a_0, a_1]

private lemma conv_f_f_ge3 (k : ℕ) : conv f f (k + 3) = 8 := by
  unfold conv
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have hmid : ∑ i ∈ Finset.range (k + 2), f (i + 1) * f (k + 3 - (i + 1)) =
      4 * conv a a (k + 1) := by
    unfold conv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < k + 2 := Finset.mem_range.mp hi
    have hidx : k + 3 - (i + 1) = (k + 1 - i) + 1 := by omega
    rw [hidx]
    simp only [f]
    ring
  rw [hmid]
  have hsub1 : k + 3 - (k + 2 + 1) = 0 := by omega
  have hsub2 : k + 3 - 0 = k + 3 := by omega
  rw [hsub1, hsub2]
  simp only [f]
  rw [a_rec k]
  ring

private lemma conv_g_g_eq (n : ℕ) : conv g g n = conv d (conv d (conv f f)) n := by
  have h1 : conv g g n = conv d (conv f (conv d f)) n := by
    unfold g
    exact conv_assoc d f (conv d f) n
  have h2 : conv d (conv f (conv d f)) n = conv d (conv d (conv f f)) n := by
    congr 1
    funext m
    calc
      conv f (conv d f) m = conv (conv d f) f m := conv_comm f (conv d f) m
      _ = conv d (conv f f) m := conv_assoc d f f m
  rw [h1, h2]

private lemma conv_g_g_0 : conv g g 0 = 1 := by
  rw [conv_g_g_eq, conv_d_zero, conv_d_zero, conv_f_f_0]

private lemma conv_g_g_1 : conv g g 1 = -6 := by
  rw [conv_g_g_eq, conv_d_succ, conv_d_succ, conv_d_zero, conv_f_f_1, conv_f_f_0]
  norm_num

private lemma conv_g_g_2 : conv g g 2 = -15 := by
  rw [conv_g_g_eq, conv_d_succ, conv_d_succ, conv_d_succ, conv_f_f_2, conv_f_f_1, conv_f_f_0]
  norm_num

private lemma conv_g_g_3 : conv g g 3 = 52 := by
  rw [conv_g_g_eq, conv_d_succ, conv_d_succ, conv_d_succ, conv_f_f_ge3 0, conv_f_f_2, conv_f_f_1]
  norm_num

private lemma conv_g_g_4 : conv g g 4 = -32 := by
  rw [conv_g_g_eq, conv_d_succ, conv_d_succ, conv_d_succ, conv_f_f_ge3 1, conv_f_f_ge3 0, conv_f_f_2]
  norm_num

private lemma conv_g_g_ge5 (k : ℕ) : conv g g (k + 5) = 0 := by
  rw [conv_g_g_eq, conv_d_succ, conv_d_succ, conv_d_succ,
    conv_f_f_ge3 (k + 2), conv_f_f_ge3 (k + 1), conv_f_f_ge3 k]
  norm_num

private lemma g_add_two (k : ℕ) : g (k + 2) = 2 * a (k + 1) - 2 * a k := by
  unfold g
  rw [conv_d_succ]
  simp only [f]

private lemma conv_deg4 (c u : ℕ → ℤ) (hc : ∀ k, 5 ≤ k → c k = 0) (m : ℕ) :
    conv c u (m + 4) =
      c 0 * u (m + 4) + c 1 * u (m + 3) + c 2 * u (m + 2) + c 3 * u (m + 1) + c 4 * u m := by
  unfold conv
  have hsub : ∑ i ∈ Finset.range (m + 5), c i * u (m + 4 - i) =
      ∑ i ∈ Finset.range 5, c i * u (m + 4 - i) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
    simp only [Finset.mem_range, not_lt] at hi
    rw [hc i hi, zero_mul]
  rw [hsub]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have h0 : m + 4 - 0 = m + 4 := by omega
  have h1 : m + 4 - 1 = m + 3 := by omega
  have h2 : m + 4 - 2 = m + 2 := by omega
  have h3 : m + 4 - 3 = m + 1 := by omega
  have h4 : m + 4 - 4 = m := by omega
  rw [h0, h1, h2, h3, h4]

private def L (n : ℕ) : ℤ :=
  (((n : ℤ) + 1)) * a n +
    (2 * (-3 * (n : ℤ) + 1)) * a (n - 1) +
    (5 * (-3 * (n : ℤ) + 7)) * a (n - 2) +
    (2 * (26 * (n : ℤ) - 81)) * a (n - 3) +
    (32 * (-(n : ℤ) + 4)) * a (n - 4)

private lemma L_four : L 4 = 0 := by
  unfold L
  simp [a_4, a_3, a_2, a_1, a_0]

private lemma L_step (k : ℕ) : L (k + 5) = L (k + 4) := by
  have hgg_zero : ∀ j, 5 ≤ j → conv g g j = 0 := by
    intro j hj
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hj
    exact conv_g_g_ge5 r
  have hgg_k_zero : ∀ j : ℕ, 5 ≤ j → (j : ℤ) * conv g g j = 0 := by
    intro j hj
    rw [hgg_zero j hj, mul_zero]
  have hid := conv_deriv_identity g (k + 6)
  have hLhs := conv_deg4 (fun j => (j : ℤ) * conv g g j) g hgg_k_zero (k + 2)
  have hRhs := conv_deg4 (conv g g) (fun j => (j : ℤ) * g j) hgg_zero (k + 2)
  have h6 : k + 2 + 4 = k + 6 := by omega
  rw [h6] at hLhs hRhs
  rw [hLhs, hRhs] at hid
  simp only [conv_g_g_0, conv_g_g_1, conv_g_g_2, conv_g_g_3, conv_g_g_4] at hid
  have h5 : k + 2 + 3 = k + 5 := by omega
  have h4 : k + 2 + 2 = k + 4 := by omega
  have h3 : k + 2 + 1 = k + 3 := by omega
  rw [h5, h4, h3] at hid
  have hg6 : g (k + 6) = 2 * a (k + 5) - 2 * a (k + 4) := g_add_two (k + 4)
  have hg5 : g (k + 5) = 2 * a (k + 4) - 2 * a (k + 3) := g_add_two (k + 3)
  have hg4 : g (k + 4) = 2 * a (k + 3) - 2 * a (k + 2) := g_add_two (k + 2)
  have hg3 : g (k + 3) = 2 * a (k + 2) - 2 * a (k + 1) := g_add_two (k + 1)
  have hg2 : g (k + 2) = 2 * a (k + 1) - 2 * a k := g_add_two k
  rw [hg6, hg5, hg4, hg3, hg2] at hid
  have hL5 : L (k + 5) =
      (((k + 5 : ℕ) : ℤ) + 1) * a (k + 5) +
      (2 * (-3 * ((k + 5 : ℕ) : ℤ) + 1)) * a (k + 4) +
      (5 * (-3 * ((k + 5 : ℕ) : ℤ) + 7)) * a (k + 3) +
      (2 * (26 * ((k + 5 : ℕ) : ℤ) - 81)) * a (k + 2) +
      (32 * (-((k + 5 : ℕ) : ℤ) + 4)) * a (k + 1) := by
    unfold L
    have s1 : k + 5 - 1 = k + 4 := by omega
    have s2 : k + 5 - 2 = k + 3 := by omega
    have s3 : k + 5 - 3 = k + 2 := by omega
    have s4 : k + 5 - 4 = k + 1 := by omega
    rw [s1, s2, s3, s4]
  have hL4 : L (k + 4) =
      (((k + 4 : ℕ) : ℤ) + 1) * a (k + 4) +
      (2 * (-3 * ((k + 4 : ℕ) : ℤ) + 1)) * a (k + 3) +
      (5 * (-3 * ((k + 4 : ℕ) : ℤ) + 7)) * a (k + 2) +
      (2 * (26 * ((k + 4 : ℕ) : ℤ) - 81)) * a (k + 1) +
      (32 * (-((k + 4 : ℕ) : ℤ) + 4)) * a k := by
    unfold L
    have s1 : k + 4 - 1 = k + 3 := by omega
    have s2 : k + 4 - 2 = k + 2 := by omega
    have s3 : k + 4 - 3 = k + 1 := by omega
    have s4 : k + 4 - 4 = k := by omega
    rw [s1, s2, s3, s4]
  rw [hL5, hL4]
  push_cast at hid ⊢
  generalize a (k + 5) = x5, a (k + 4) = x4, a (k + 3) = x3, a (k + 2) = x2, a (k + 1) = x1,
    a k = x0 at hid ⊢
  apply sub_eq_zero.mp
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  rw [mul_zero]
  linear_combination -hid

private lemma L_add_four (k : ℕ) : L (k + 4) = 0 := by
  induction k with
  | zero => exact L_four
  | succ k ih =>
    have h : k + 1 + 4 = k + 5 := by omega
    rw [h, L_step k, ih]

theorem solution : type_of% @OMA.S_oeis_a177169.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact L_add_four k

end OMA.P_oeis_a177169

theorem OMA.solution : type_of% @OMA.S_oeis_a177169.main := OMA.P_oeis_a177169.solution
