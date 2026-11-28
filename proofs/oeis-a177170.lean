import OMAStatements.S_oeis_a177170

namespace OMA.P_oeis_a177170

private def conv (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

private lemma conv_comm (f g : ℕ → ℤ) (n : ℕ) : conv f g n = conv g f n := by
  unfold conv
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsub : n + 1 - 1 - k = n - k := by omega
  rw [hsub, Nat.sub_sub_self hk', mul_comm]

private lemma conv_assoc (f g h : ℕ → ℤ) (n : ℕ) :
    conv (conv f g) h n = conv f (conv g h) n := by
  unfold conv
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma' (Finset.range (n + 1)) (fun m => Finset.range (m + 1))
        (fun m i => f i * g (m - i) * h (n - m)),
      Finset.sum_sigma' (Finset.range (n + 1)) (fun i => Finset.range (n - i + 1))
        (fun i j => f i * (g j * h (n - i - j)))]
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

private lemma two_mul_conv_mul_nat (b : ℕ → ℤ) (n : ℕ) :
    2 * conv (fun k => (k : ℤ) * b k) b n = (n : ℤ) * conv b b n := by
  have hrefl : conv (fun k => (k : ℤ) * b k) b n =
      ∑ k ∈ Finset.range (n + 1), ((n - k : ℕ) : ℤ) * b (n - k) * b k := by
    unfold conv
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n + 1 - 1 - k = n - k := by omega
    rw [hsub, Nat.sub_sub_self hk']
  calc
    2 * conv (fun k => (k : ℤ) * b k) b n
        = conv (fun k => (k : ℤ) * b k) b n + conv (fun k => (k : ℤ) * b k) b n := by ring
    _ = (∑ k ∈ Finset.range (n + 1), (k : ℤ) * b k * b (n - k)) +
        (∑ k ∈ Finset.range (n + 1), ((n - k : ℕ) : ℤ) * b (n - k) * b k) := by
          conv_rhs => rw [← hrefl]
          rfl
    _ = ∑ k ∈ Finset.range (n + 1),
        ((k : ℤ) * b k * b (n - k) + ((n - k : ℕ) : ℤ) * b (n - k) * b k) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.range (n + 1), (n : ℤ) * (b k * b (n - k)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [Nat.cast_sub hk']
          ring
    _ = (n : ℤ) * conv b b n := by
          rw [← Finset.mul_sum]
          rfl

private lemma conv_deriv_identity (b : ℕ → ℤ) (n : ℕ) :
    conv (fun k => (k : ℤ) * conv b b k) b n =
      2 * conv (conv b b) (fun k => (k : ℤ) * b k) n := by
  have h1 : conv (fun k => (k : ℤ) * conv b b k) b n =
      conv (fun k => 2 * conv (fun j => (j : ℤ) * b j) b k) b n := by
    congr 1
    funext k
    exact (two_mul_conv_mul_nat b k).symm
  have h2 : conv (fun k => 2 * conv (fun j => (j : ℤ) * b j) b k) b n =
      2 * conv (conv (fun j => (j : ℤ) * b j) b) b n := by
    unfold conv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2, conv_assoc, conv_comm]

private def shift1 (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => f n

private lemma conv_shift1 (f g : ℕ → ℤ) (n : ℕ) :
    conv (shift1 f) g (n + 1) = conv f g n := by
  unfold conv
  rw [Finset.sum_range_succ']
  simp only [shift1, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : n + 1 - (i + 1) = n - i := by omega
  rw [hsub]

private def diff2 (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => f 0
  | 1 => f 1 - 2 * f 0
  | n + 2 => f (n + 2) - 2 * f (n + 1) + f n

private lemma diff2_eq (f : ℕ → ℤ) (k : ℕ) :
    diff2 f k = f k - 2 * shift1 f k + shift1 (shift1 f) k := by
  rcases k with _ | _ | k <;> simp [diff2, shift1]

private lemma conv_diff2 (f g : ℕ → ℤ) (n : ℕ) :
    conv (diff2 f) g (n + 2) =
      conv f g (n + 2) - 2 * conv f g (n + 1) + conv f g n := by
  have hlin : conv (diff2 f) g (n + 2) =
      conv f g (n + 2) - 2 * conv (shift1 f) g (n + 2) +
        conv (shift1 (shift1 f)) g (n + 2) := by
    unfold conv
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [diff2_eq]
    ring
  rw [hlin, conv_shift1, conv_shift1, conv_shift1]

private lemma conv_of_support_lt_five (f g : ℕ → ℤ) (N : ℕ) (hN : 4 ≤ N)
    (hf : ∀ k, 5 ≤ k → f k = 0) :
    conv f g N =
      f 0 * g N + f 1 * g (N - 1) + f 2 * g (N - 2) +
        f 3 * g (N - 3) + f 4 * g (N - 4) := by
  unfold conv
  have hsub : Finset.range 5 ⊆ Finset.range (N + 1) :=
    Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub]
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, Nat.sub_zero]
  · intro i hi hni
    simp only [Finset.mem_range] at hi hni
    rw [hf i (by omega), zero_mul]

private def b : ℕ → ℤ
  | 0 => -1
  | n + 1 => 2 * OMA.S_oeis_a177170.a n

private lemma a_zero : OMA.S_oeis_a177170.a 0 = 1 := by
  rw [OMA.S_oeis_a177170.a]

private lemma a_one : OMA.S_oeis_a177170.a 1 = 8 := by
  rw [OMA.S_oeis_a177170.a]

private lemma a_succ_succ (m : ℕ) :
    OMA.S_oeis_a177170.a (m + 2) =
      (∑ j ∈ Finset.range (m + 2),
        OMA.S_oeis_a177170.a j * OMA.S_oeis_a177170.a (m + 1 - j)) - 2 := by
  rw [OMA.S_oeis_a177170.a]
  simp_rw [add_zero]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => OMA.S_oeis_a177170.a j * OMA.S_oeis_a177170.a (m + 1 - j))]
  ring

private lemma conv_b_b_eval :
    conv b b 0 = 1 ∧
    conv b b 1 = -4 ∧
    conv b b 2 = -28 ∧
    ∀ m : ℕ, conv b b (m + 3) = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [conv, b]
  · simp [conv, Finset.sum_range_succ, b, a_zero]
  · simp [conv, Finset.sum_range_succ, b, a_zero, a_one]
  · intro m
    unfold conv
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hfirst : b 0 * b (m + 3 - 0) = -2 * OMA.S_oeis_a177170.a (m + 2) := by
      simp [b]
    have hlast : b (m + 3) * b (m + 3 - (m + 3)) = -2 * OMA.S_oeis_a177170.a (m + 2) := by
      simp [b]
    have hmid :
        ∑ j ∈ Finset.range (m + 2), b (j + 1) * b (m + 3 - (j + 1)) =
          4 * ∑ j ∈ Finset.range (m + 2),
            OMA.S_oeis_a177170.a j * OMA.S_oeis_a177170.a (m + 1 - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < m + 2 := Finset.mem_range.mp hj
      have hidx : m + 3 - (j + 1) = (m + 1 - j) + 1 := by omega
      rw [hidx]
      simp only [b]
      ring
    rw [hfirst, hlast, hmid]
    have ha := a_succ_succ m
    linarith

private lemma diff2_c_eval :
    diff2 (conv b b) 0 = 1 ∧
    diff2 (conv b b) 1 = -6 ∧
    diff2 (conv b b) 2 = -19 ∧
    diff2 (conv b b) 3 = 60 ∧
    diff2 (conv b b) 4 = -36 ∧
    ∀ k : ℕ, 5 ≤ k → diff2 (conv b b) k = 0 := by
  obtain ⟨hc0, hc1, hc2, hcg⟩ := conv_b_b_eval
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [diff2, hc0]
  · simp [diff2, hc0, hc1]
  · simp [diff2, hc0, hc1, hc2]
  · simp [diff2, hc1, hc2, hcg 0]
  · simp [diff2, hc2, hcg 0, hcg 1]
  · intro k hk
    rcases k with _ | _ | _ | _ | _ | j
    · omega
    · omega
    · omega
    · omega
    · omega
    · simp only [diff2]
      rw [hcg (j + 2), hcg (j + 1), hcg j]
      ring

private lemma diff2_kc_eval :
    diff2 (fun k => (k : ℤ) * conv b b k) 0 = 0 ∧
    diff2 (fun k => (k : ℤ) * conv b b k) 1 = -4 ∧
    diff2 (fun k => (k : ℤ) * conv b b k) 2 = -48 ∧
    diff2 (fun k => (k : ℤ) * conv b b k) 3 = 132 ∧
    diff2 (fun k => (k : ℤ) * conv b b k) 4 = -72 ∧
    ∀ k : ℕ, 5 ≤ k → diff2 (fun k => (k : ℤ) * conv b b k) k = 0 := by
  obtain ⟨hc0, hc1, hc2, hcg⟩ := conv_b_b_eval
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [diff2]
  · simp [diff2, hc1]
  · simp [diff2, hc1, hc2]
  · simp [diff2, hc1, hc2, hcg 0]
  · simp [diff2, hc2, hcg 0, hcg 1]
  · intro k hk
    rcases k with _ | _ | _ | _ | _ | j
    · omega
    · omega
    · omega
    · omega
    · omega
    · simp only [diff2]
      rw [hcg (j + 2), hcg (j + 1), hcg j]
      push_cast
      ring

theorem main_proof : ∀ n : ℕ, 4 ≤ n →
    (((n : ℤ) + 1)) * OMA.S_oeis_a177170.a n +
      (2 * (-3 * (n : ℤ) + 1)) * OMA.S_oeis_a177170.a (n - 1) +
      ((-19 * (n : ℤ) + 43)) * OMA.S_oeis_a177170.a (n - 2) +
      (6 * (10 * (n : ℤ) - 31)) * OMA.S_oeis_a177170.a (n - 3) +
      (36 * (-(n : ℤ) + 4)) * OMA.S_oeis_a177170.a (n - 4) = 0 := by
  intro n hn
  rcases n with _ | _ | _ | _ | m
  · omega
  · omega
  · omega
  · omega
  have hid2 := conv_deriv_identity b (m + 5)
  have hid1 := conv_deriv_identity b (m + 4)
  have hid0 := conv_deriv_identity b (m + 3)
  have hdiff :
      conv (diff2 (fun k => (k : ℤ) * conv b b k)) b (m + 5) =
        2 * conv (diff2 (conv b b)) (fun k => (k : ℤ) * b k) (m + 5) := by
    have hL := conv_diff2 (fun k => (k : ℤ) * conv b b k) b (m + 3)
    have hR := conv_diff2 (conv b b) (fun k => (k : ℤ) * b k) (m + 3)
    linarith
  obtain ⟨dc0, dc1, dc2, dc3, dc4, dcg⟩ := diff2_c_eval
  obtain ⟨dk0, dk1, dk2, dk3, dk4, dkg⟩ := diff2_kc_eval
  rw [conv_of_support_lt_five _ _ (m + 5) (by omega) dkg,
      conv_of_support_lt_five _ _ (m + 5) (by omega) dcg] at hdiff
  rw [dk0, dk1, dk2, dk3, dk4, dc0, dc1, dc2, dc3, dc4] at hdiff
  have hs1 : m + 5 - 1 = m + 4 := by omega
  have hs2 : m + 5 - 2 = m + 3 := by omega
  have hs3 : m + 5 - 3 = m + 2 := by omega
  have hs4 : m + 5 - 4 = m + 1 := by omega
  rw [hs1, hs2, hs3, hs4] at hdiff
  simp only [b] at hdiff
  have h1 : m + 4 - 1 = m + 3 := by omega
  have h2 : m + 4 - 2 = m + 2 := by omega
  have h3 : m + 4 - 3 = m + 1 := by omega
  have h4 : m + 4 - 4 = m := by omega
  rw [h1, h2, h3, h4]
  push_cast at hdiff ⊢
  linarith

end OMA.P_oeis_a177170

theorem OMA.solution : type_of% @OMA.S_oeis_a177170.main :=
  OMA.P_oeis_a177170.main_proof
