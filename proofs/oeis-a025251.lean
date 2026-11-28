import OMAStatements.S_oeis_a025251

namespace OMA.P_oeis_a025251

private def conv (f g : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

private lemma conv_comm (f g : ℕ → ℚ) (n : ℕ) : conv f g n = conv g f n := by
  unfold conv
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsub : n + 1 - 1 - k = n - k := by omega
  rw [hsub, Nat.sub_sub_self hk', mul_comm]

private lemma conv_assoc (f g h : ℕ → ℚ) (n : ℕ) :
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
    exact Sigma.ext (by try dsimp only; omega) HEq.rfl
  · rintro ⟨i, j⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq
    exact Sigma.ext rfl (heq_of_eq (by try dsimp only; omega))
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    dsimp only
    have hsub : n - p.2 - (p.1 - p.2) = n - p.1 := by omega
    rw [hsub, mul_assoc]

private lemma two_mul_conv_mul_nat (b : ℕ → ℚ) (n : ℕ) :
    2 * conv (fun k => (k : ℚ) * b k) b n = (n : ℚ) * conv b b n := by
  have hrefl : conv (fun k => (k : ℚ) * b k) b n =
      ∑ k ∈ Finset.range (n + 1), ((n - k : ℕ) : ℚ) * b (n - k) * b k := by
    unfold conv
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n + 1 - 1 - k = n - k := by omega
    rw [hsub, Nat.sub_sub_self hk']
  calc
    2 * conv (fun k => (k : ℚ) * b k) b n
        = conv (fun k => (k : ℚ) * b k) b n + conv (fun k => (k : ℚ) * b k) b n := by ring
    _ = (∑ k ∈ Finset.range (n + 1), (k : ℚ) * b k * b (n - k)) +
        (∑ k ∈ Finset.range (n + 1), ((n - k : ℕ) : ℚ) * b (n - k) * b k) := by
          conv_rhs => rw [← hrefl]
          rfl
    _ = ∑ k ∈ Finset.range (n + 1),
        ((k : ℚ) * b k * b (n - k) + ((n - k : ℕ) : ℚ) * b (n - k) * b k) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.range (n + 1), (n : ℚ) * (b k * b (n - k)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [Nat.cast_sub hk']
          ring
    _ = (n : ℚ) * conv b b n := by
          rw [← Finset.mul_sum]
          rfl

private lemma conv_deriv_identity (b : ℕ → ℚ) (n : ℕ) :
    conv (fun k => (k : ℚ) * conv b b k) b n =
      2 * conv (conv b b) (fun k => (k : ℚ) * b k) n := by
  have h1 : conv (fun k => (k : ℚ) * conv b b k) b n =
      conv (fun k => 2 * conv (fun j => (j : ℚ) * b j) b k) b n := by
    congr 1
    funext k
    exact (two_mul_conv_mul_nat b k).symm
  have h2 : conv (fun k => 2 * conv (fun j => (j : ℚ) * b j) b k) b n =
      2 * conv (conv (fun j => (j : ℚ) * b j) b) b n := by
    change ∑ k ∈ Finset.range (n + 1), (2 * conv (fun j => (j : ℚ) * b j) b k) * b (n - k) =
      2 * ∑ k ∈ Finset.range (n + 1), conv (fun j => (j : ℚ) * b j) b k * b (n - k)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [h1, h2, conv_assoc, conv_comm]

private def bSeq (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | n + 3 => -2 * a (n + 3)

private lemma bSeq_ge3 (a : ℕ → ℚ) {k : ℕ} (hk : 3 ≤ k) : bSeq a k = -2 * a k := by
  rcases k with _ | _ | _ | k
  · omega
  · omega
  · omega
  · rfl

private lemma sum_Icc_one_add_two (G : ℕ → ℚ) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 (m + 2), G k = G 1 + G 2 + ∑ i ∈ Finset.range m, G (i + 3) := by
  induction m with
  | zero =>
    have h : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    rw [h]
    simp
  | succ m ih =>
    have hsucc : m + 1 + 2 = (m + 2) + 1 := by omega
    rw [hsucc, Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    ring

private lemma conv_bSeq_eval (a : ℕ → ℚ)
    (ha1 : a 1 = 0) (ha2 : a 2 = 1) (ha3 : a 3 = 2)
    (hrec : ∀ n : ℕ, 4 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 3), a k * a (n - k)) :
    conv (bSeq a) (bSeq a) 0 = 1 ∧
    conv (bSeq a) (bSeq a) 1 = 0 ∧
    conv (bSeq a) (bSeq a) 2 = -2 ∧
    conv (bSeq a) (bSeq a) 3 = -8 ∧
    conv (bSeq a) (bSeq a) 4 = 1 ∧
    (∀ n : ℕ, 5 ≤ n → conv (bSeq a) (bSeq a) n = 0) := by
  have ha4 : a 4 = 0 := by
    have h := hrec 4 (by omega)
    have hIcc : Finset.Icc 1 1 = ({1} : Finset ℕ) := by decide
    simpa [hIcc, ha1, ha3] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [conv, bSeq]
  · simp [conv, Finset.sum_range_succ, bSeq]
  · simp [conv, Finset.sum_range_succ, bSeq]
    ring
  · simp [conv, Finset.sum_range_succ, bSeq, ha3]
    ring
  · simp [conv, Finset.sum_range_succ, bSeq, ha4]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    unfold conv
    have hsplit :
        ∑ k ∈ Finset.range (m + 5 + 1), bSeq a k * bSeq a (m + 5 - k) =
        (∑ i ∈ Finset.range m, bSeq a (i + 3) * bSeq a (m + 5 - (i + 3))) +
          bSeq a 2 * bSeq a (m + 3) +
          bSeq a 1 * bSeq a (m + 4) +
          bSeq a 0 * bSeq a (m + 5) +
          bSeq a (m + 3) * bSeq a 2 +
          bSeq a (m + 4) * bSeq a 1 +
          bSeq a (m + 5) * bSeq a 0 := by
      have htop :
          ∑ k ∈ Finset.range (m + 5 + 1), bSeq a k * bSeq a (m + 5 - k) =
          (∑ k ∈ Finset.range (m + 3), bSeq a k * bSeq a (m + 5 - k)) +
            bSeq a (m + 3) * bSeq a 2 +
            bSeq a (m + 4) * bSeq a 1 +
            bSeq a (m + 5) * bSeq a 0 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        have h1 : m + 5 - (m + 5) = 0 := by omega
        have h2 : m + 5 - (m + 4) = 1 := by omega
        have h3 : m + 5 - (m + 3) = 2 := by omega
        rw [h1, h2, h3]
      have hbot :
          ∑ k ∈ Finset.range (m + 3), bSeq a k * bSeq a (m + 5 - k) =
          (∑ i ∈ Finset.range m, bSeq a (i + 3) * bSeq a (m + 5 - (i + 3))) +
            bSeq a 2 * bSeq a (m + 3) +
            bSeq a 1 * bSeq a (m + 4) +
            bSeq a 0 * bSeq a (m + 5) := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
        have h1 : m + 5 - 0 = m + 5 := by omega
        have h2 : m + 5 - 1 = m + 4 := by omega
        have h3 : m + 5 - 2 = m + 3 := by omega
        rw [h1, h2, h3]
      rw [htop, hbot]
    rw [hsplit]
    have hmid :
        ∑ i ∈ Finset.range m, bSeq a (i + 3) * bSeq a (m + 5 - (i + 3)) =
        4 * ∑ i ∈ Finset.range m, a (i + 3) * a (m + 5 - (i + 3)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < m := Finset.mem_range.mp hi
      rw [bSeq_ge3 a (by omega), bSeq_ge3 a (by omega)]
      ring
    have harec :
        a (m + 5) = a (m + 3) + ∑ i ∈ Finset.range m, a (i + 3) * a (m + 5 - (i + 3)) := by
      have h := hrec (m + 5) (by omega)
      have hsub : m + 5 - 3 = m + 2 := by omega
      rw [hsub, sum_Icc_one_add_two] at h
      have h1 : m + 5 - 1 = m + 4 := by omega
      have h2 : m + 5 - 2 = m + 3 := by omega
      rw [h1, h2, ha1, ha2] at h
      linarith
    rw [hmid, bSeq_ge3 a (k := m + 3) (by omega), bSeq_ge3 a (k := m + 4) (by omega),
      bSeq_ge3 a (k := m + 5) (by omega)]
    simp only [bSeq]
    linarith

private lemma sum_range_eq_five (f : ℕ → ℚ) (hf : ∀ k, 5 ≤ k → f k = 0)
    {n : ℕ} (hn : 4 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), f k = f 0 + f 1 + f 2 + f 3 + f 4 := by
  have hsub : Finset.range 5 ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub]
  · simp [Finset.sum_range_succ]
  · intro k _ hk
    exact hf k (by simpa [Finset.mem_range] using hk)

private lemma simple_rec (a : ℕ → ℚ)
    (ha1 : a 1 = 0) (ha2 : a 2 = 1) (ha3 : a 3 = 2)
    (hrec : ∀ n : ℕ, 4 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 3), a k * a (n - k))
    {n : ℕ} (hn : 6 ≤ n) :
    (n : ℚ) * a n - 2 * ((n : ℚ) - 3) * a (n - 2) -
      4 * (2 * (n : ℚ) - 9) * a (n - 3) + ((n : ℚ) - 6) * a (n - 4) = 0 := by
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩ := conv_bSeq_eval a ha1 ha2 ha3 hrec
  set b := bSeq a
  set c := conv b b
  have hid : conv (fun k => (k : ℚ) * c k) b n =
      2 * conv c (fun k => (k : ℚ) * b k) n := conv_deriv_identity b n
  have hlhs : conv (fun k => (k : ℚ) * c k) b n =
      0 * c 0 * b n + 1 * c 1 * b (n - 1) + 2 * c 2 * b (n - 2) +
        3 * c 3 * b (n - 3) + 4 * c 4 * b (n - 4) := by
    change ∑ k ∈ Finset.range (n + 1), ((k : ℚ) * c k) * b (n - k) = _
    rw [sum_range_eq_five _ (fun k hk => by rw [hc5 k hk]; ring) (by omega)]
    norm_num
  have hrhs : conv c (fun k => (k : ℚ) * b k) n =
      c 0 * ((n : ℚ) * b n) +
      c 1 * (((n - 1 : ℕ) : ℚ) * b (n - 1)) +
      c 2 * (((n - 2 : ℕ) : ℚ) * b (n - 2)) +
      c 3 * (((n - 3 : ℕ) : ℚ) * b (n - 3)) +
      c 4 * (((n - 4 : ℕ) : ℚ) * b (n - 4)) := by
    change ∑ k ∈ Finset.range (n + 1), c k * (((n - k : ℕ) : ℚ) * b (n - k)) = _
    rw [sum_range_eq_five _ (fun k hk => by rw [hc5 k hk]; ring) (by omega)]
    simp
  rw [hlhs, hrhs, hc0, hc1, hc2, hc3, hc4] at hid
  rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n),
      Nat.cast_sub (by omega : 4 ≤ n)] at hid
  norm_num at hid
  have hb0 : b n = -2 * a n := bSeq_ge3 a (by omega)
  have hb2 : b (n - 2) = -2 * a (n - 2) := bSeq_ge3 a (by omega)
  have hb3 : b (n - 3) = -2 * a (n - 3) := bSeq_ge3 a (by omega)
  have hb4 : ((n : ℚ) - 6) * b (n - 4) = ((n : ℚ) - 6) * (-2 * a (n - 4)) := by
    by_cases h6 : n = 6
    · subst h6
      norm_num
    · have h4 : b (n - 4) = -2 * a (n - 4) := bSeq_ge3 a (by omega)
      rw [h4]
  rw [hb0, hb2, hb3] at hid
  linarith

end OMA.P_oeis_a025251

theorem OMA.solution : type_of% @OMA.S_oeis_a025251.main := by
  intro a ha1 ha2 ha3 hrec n hn
  have h1 := OMA.P_oeis_a025251.simple_rec a ha1 ha2 ha3 hrec (n := n) (by omega)
  have h2 := OMA.P_oeis_a025251.simple_rec a ha1 ha2 ha3 hrec (n := n - 1) (by omega)
  have hs2 : n - 1 - 2 = n - 3 := by omega
  have hs3 : n - 1 - 3 = n - 4 := by omega
  have hs4 : n - 1 - 4 = n - 5 := by omega
  rw [hs2, hs3, hs4, Nat.cast_sub (by omega : 1 ≤ n)] at h2
  norm_num at h2
  linear_combination ((n : ℚ) ^ 2 + (n : ℚ) + 1) * h1 + ((n : ℚ) ^ 2 + 2 * (n : ℚ) + 3) * h2
