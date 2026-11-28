import OMAStatements.S_oeis_a380944

-- Problem: A380944: a(n) = b(n,A000120(n)) for n >= 0 where b(n,k) is defined in Comments.
-- Upstream: formal-conjectures statements/oeis-a380944.lean:0 (declaration OMA.S_oeis_a380944.main)
-- Credit: @marcusbuffett

/-!
Proof outline. Put x = 2^n - 1, so b(x, k) = C(n, k), and B_m(k) = b(2^m x, k) satisfies
B_{m+1}(k) = (n - k + 1)(B_m(k) + B_m(k - 1)) for k >= 1, with B_m(0) = 1.
The binomial row C(n, k)(n + 1)^m solves the recurrence without the boundary at k = 0; the
correction is n * n.descFactorial k * q(k + 1, m - k - 1), where q is the coefficient table of
1 / ((1 - t)(1 - (n + 1)t)...(1 - (n + 1 - k)t)). At k = n the same power series is
1 / ((1 - t)(1 - t)...(1 - (n + 1)t)), whose coefficients are the partial sums of S(n + 1 + i, n + 1).
-/
namespace A380944Proof
open OMA.S_oeis_a380944 PowerSeries

lemma b_k0 (n : ℕ) : b n 0 = 1 := by rw [b]; simp

lemma b_n0 (k : ℕ) (hk : k ≠ 0) : b 0 k = 0 := by rw [b]; simp [hk]

lemma b_odd (r k : ℕ) (hk : k ≠ 0) : b (2*r+1) k = b r k + b r (k-1) := by
  have h0 : 2*r+1 ≠ 0 := by omega
  have h1 : (2*r+1)/2 = r := by omega
  have h2 : (2*r+1)%2 = 1 := by omega
  rw [b]; simp [hk, h1, h2]

lemma b_even (r k : ℕ) (hk : k ≠ 0) (hr : r ≠ 0) :
    b (2*r) k = ((binaryWeight r : ℤ) - k + 1) * (b r k + b r (k-1)) := by
  have h0 : 2*r ≠ 0 := by omega
  have h1 : (2*r)/2 = r := by omega
  have h2 : (2*r)%2 = 0 := by omega
  rw [b]; simp [hk, hr, h0, h1, h2]

lemma bw_odd (r : ℕ) : binaryWeight (2*r+1) = binaryWeight r + 1 := by
  unfold binaryWeight
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2*r+1)/2 = r := by omega
  have h2 : (2*r+1)%2 = 1 := by omega
  rw [h1, h2]; simp

lemma bw_even (r : ℕ) (hr : 0 < r) : binaryWeight (2*r) = binaryWeight r := by
  unfold binaryWeight
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2*r)/2 = r := by omega
  have h2 : (2*r)%2 = 0 := by omega
  rw [h1, h2]; simp

lemma two_pow_sub_one_succ (n : ℕ) : 2^(n+1) - 1 = 2*(2^n-1)+1 := by
  have := Nat.one_le_two_pow (n := n); rw [pow_succ]; omega

lemma bw_ones (n : ℕ) : binaryWeight (2^n - 1) = n := by
  induction n with
  | zero => simp [binaryWeight]
  | succ n ih => rw [two_pow_sub_one_succ, bw_odd, ih]

lemma b_ones (n k : ℕ) : b (2^n - 1) k = (n.choose k : ℤ) := by
  induction n generalizing k with
  | zero =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [b_k0]
    · simp [b_n0 k (by omega), Nat.choose_eq_zero_of_lt hk]
  | succ n ih =>
    rcases k with _ | k
    · simp [b_k0]
    · rw [two_pow_sub_one_succ, b_odd _ _ (by omega), ih, ih, Nat.choose_succ_succ']
      simp; ring

lemma bw_pow_mul (m x : ℕ) (hx : 0 < x) : binaryWeight (2^m * x) = binaryWeight x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2^(m+1)*x = 2*(2^m*x) by ring, bw_even _ (by positivity), ih]

lemma B_succ (m x k : ℕ) (hx : 0 < x) (hk : k ≠ 0) :
    b (2^(m+1)*x) k = ((binaryWeight x : ℤ) - k + 1) * (b (2^m*x) k + b (2^m*x) (k-1)) := by
  rw [show 2^(m+1)*x = 2*(2^m*x) by ring, b_even _ _ hk (by positivity), bw_pow_mul _ _ hx]

def q (n : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 1
  | _+1, 0 => 1
  | l+1, r+1 => q n l (r+1) + ((n:ℤ)+1-l) * q n (l+1) r

lemma q_zero_right (n l : ℕ) : q n l 0 = 1 := by
  cases l <;> simp [q]

lemma q_one (n r : ℕ) : (n:ℤ) * q n 1 r + 1 = ((n:ℤ)+1)^(r+1) := by
  induction r with
  | zero => simp [q]
  | succ r ih =>
    rw [q, q]; simp only [Nat.cast_zero, sub_zero]
    rw [pow_succ]; linear_combination ((n:ℤ)+1) * ih

lemma formula (n : ℕ) (hn : 0 < n) (m : ℕ) : ∀ k, k ≤ n →
    b (2^m*(2^n-1)) k = (n.choose k : ℤ) * ((n:ℤ)+1)^m -
      (if k+1 ≤ m then (n:ℤ) * (n.descFactorial k : ℤ) * q n (k+1) (m-k-1) else 0) := by
  have hx : 0 < 2^n - 1 := by
    have : 2 ≤ 2^n := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  induction m with
  | zero => intro k hk; simp [b_ones]
  | succ m ih =>
    intro k hk
    rcases k with _ | k
    · rw [b_k0]
      have := q_one n m
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add,
        show (1 ≤ m+1) = True by simp, if_true, Nat.descFactorial_zero, mul_one,
        show m + 1 - 0 - 1 = m by omega]
      linarith
    · rw [B_succ _ _ _ hx (by omega), bw_ones, Nat.add_sub_cancel, ih (k+1) hk, ih k (by omega)]
      have hd : ((n.descFactorial (k+1) : ℕ) : ℤ) = ((n:ℤ) - k) * (n.descFactorial k : ℤ) := by
        rw [Nat.descFactorial_succ]; push_cast [Nat.cast_sub (show k ≤ n by omega)]; ring
      have hc : ((n.choose (k+1) : ℕ) : ℤ) * ((n:ℤ)+1) =
          ((n:ℤ) - k) * ((n.choose (k+1) : ℤ) + (n.choose k : ℤ)) := by
        have h := Nat.choose_mul_succ_eq n (k+1)
        rw [Nat.choose_succ_succ'] at h
        have h' : ((n.choose (k+1) * (n+1) : ℕ) : ℤ) = (((n.choose k + n.choose (k+1)) * (n + 1 - (k+1)) : ℕ) : ℤ) := by
          rw [h]
        rw [show n + 1 - (k+1) = n - k by omega] at h'
        push_cast [Nat.cast_sub (show k ≤ n by omega)] at h'
        linear_combination h'
      rcases Nat.lt_or_ge m (k+1) with hm | hm
      · have e1 : ¬ (k+1+1 ≤ m+1) := by omega
        have e2 : ¬ (k+1+1 ≤ m) := by omega
        have e3 : ¬ (k+1 ≤ m) := by omega
        simp only [e1, e2, e3, if_false, sub_zero]
        rw [pow_succ]; push_cast
        linear_combination -((n:ℤ)+1)^m * hc
      · rcases Nat.eq_or_lt_of_le hm with hm | hm
        · subst hm
          have e1 : (k+1+1 ≤ k+1+1) := le_refl _
          have e2 : ¬ (k+1+1 ≤ k+1) := by omega
          have e3 : (k+1 ≤ k+1) := le_refl _
          simp only [e1, e2, e3, if_true, if_false, sub_zero, q_zero_right,
            show k + 1 + 1 - (k + 1) - 1 = 0 by omega, show k + 1 - k - 1 = 0 by omega]
          rw [hd, pow_succ]; push_cast
          linear_combination -((n:ℤ)+1)^(k+1) * hc
        · obtain ⟨r, rfl⟩ : ∃ r, m = k + 2 + r := ⟨m - (k+2), by omega⟩
          have e1 : (k+1+1 ≤ k+2+r+1) := by omega
          have e2 : (k+1+1 ≤ k+2+r) := by omega
          have e3 : (k+1 ≤ k+2+r) := by omega
          simp only [e1, e2, e3, if_true,
            show k + 2 + r + 1 - (k + 1) - 1 = r + 1 by omega,
            show k + 2 + r - (k + 1) - 1 = r by omega,
            show k + 2 + r - k - 1 = r + 1 by omega]
          rw [show q n (k+1+1) (r+1) = q n (k+1) (r+1) + ((n:ℤ)+1-(k+1:ℕ)) * q n (k+1+1) r by rw [q]]
          rw [hd, pow_succ]; push_cast
          linear_combination -((n:ℤ)+1)^(k+2+r) * hc

end A380944Proof

namespace A380944Proof
open OMA.S_oeis_a380944 PowerSeries

lemma mul_lin (A : PowerSeries ℤ) (c : ℤ) (r : ℕ) :
    coeff (r+1) (A * (1 - C c * X)) = coeff (r+1) A - c * coeff r A := by
  rw [show A * (1 - C c * X) = A - C c * (A * X) by ring, map_sub, coeff_C_mul, coeff_succ_mul_X]

lemma mul_lin0 (A : PowerSeries ℤ) (c : ℤ) :
    coeff 0 (A * (1 - C c * X)) = coeff 0 A := by
  rw [show A * (1 - C c * X) = A - C c * (A * X) by ring, map_sub, coeff_C_mul, coeff_zero_mul_X]
  simp

lemma G_rec (n l : ℕ) :
    mk (q n (l+1)) * (1 - C ((n:ℤ)+1-l) * X) = mk (q n l) := by
  ext r
  rcases r with _ | r
  · rw [mul_lin0]; simp [q_zero_right]
  · rw [mul_lin]; simp only [coeff_mk]
    rw [show q n (l+1) (r+1) = q n l (r+1) + ((n:ℤ)+1-l) * q n (l+1) r by rw [q]]
    ring

lemma G_zero (n : ℕ) : mk (q n 0) * (1 - C (1:ℤ) * X) = 1 := by
  ext r
  rcases r with _ | r
  · rw [mul_lin0]; simp [q]
  · rw [mul_lin]; simp [q]

lemma G_prod (n l : ℕ) :
    mk (q n l) * (∏ i ∈ Finset.range l, (1 - C ((n:ℤ)+1-i) * X)) * (1 - C (1:ℤ) * X) = 1 := by
  induction l with
  | zero => simpa using G_zero n
  | succ l ih =>
    rw [Finset.prod_range_succ]
    calc _ = (mk (q n (l+1)) * (1 - C ((n:ℤ)+1-l) * X)) *
          (∏ i ∈ Finset.range l, (1 - C ((n:ℤ)+1-i) * X)) * (1 - C (1:ℤ) * X) := by ring
      _ = 1 := by rw [G_rec]; exact ih

lemma H_rec (K : ℕ) :
    mk (fun i => ((Nat.stirlingSecond (K+1+i) (K+1) : ℕ) : ℤ)) * (1 - C ((K:ℤ)+1) * X) =
      mk (fun i => ((Nat.stirlingSecond (K+i) K : ℕ) : ℤ)) := by
  ext r
  rcases r with _ | r
  · rw [mul_lin0]; simp [Nat.stirlingSecond_self]
  · rw [mul_lin]; simp only [coeff_mk]
    rw [show K + 1 + (r+1) = (K+1+r) + 1 by ring, Nat.stirlingSecond_succ_succ,
      show K + (r+1) = K+1+r by ring]
    push_cast; ring

lemma H_zero : mk (fun i => ((Nat.stirlingSecond (0+i) 0 : ℕ) : ℤ)) = 1 := by
  ext r
  rcases r with _ | r
  · simp
  · simp [Nat.stirlingSecond_succ_zero]

lemma H_prod (K : ℕ) :
    mk (fun i => ((Nat.stirlingSecond (K+i) K : ℕ) : ℤ)) *
      (∏ i ∈ Finset.range K, (1 - C ((i:ℤ)+1) * X)) = 1 := by
  induction K with
  | zero => simpa using H_zero
  | succ K ih =>
    rw [Finset.prod_range_succ]
    calc _ = (mk (fun i => ((Nat.stirlingSecond (K+1+i) (K+1) : ℕ) : ℤ)) * (1 - C ((K:ℤ)+1) * X)) *
          (∏ i ∈ Finset.range K, (1 - C ((i:ℤ)+1) * X)) := by ring
      _ = 1 := by rw [H_rec]; exact ih

lemma Sg_rec (K : ℕ) :
    mk (fun r => ∑ i ∈ Finset.range (r+1), ((Nat.stirlingSecond (K+i) K : ℕ) : ℤ)) *
      (1 - C (1:ℤ) * X) = mk (fun i => ((Nat.stirlingSecond (K+i) K : ℕ) : ℤ)) := by
  ext r
  rcases r with _ | r
  · rw [mul_lin0]; simp
  · rw [mul_lin]; simp only [coeff_mk]
    rw [Finset.sum_range_succ _ (r+1)]; ring

lemma q_top (n r : ℕ) :
    q n (n+1) r = ∑ i ∈ Finset.range (r+1), ((Nat.stirlingSecond (n+1+i) (n+1) : ℕ) : ℤ) := by
  have hP : ∏ i ∈ Finset.range (n+1), (1 - C ((n:ℤ)+1-i) * X) =
      ∏ i ∈ Finset.range (n+1), (1 - C ((i:ℤ)+1) * X) := by
    rw [← Finset.prod_range_reflect (fun i : ℕ => (1 - C ((i:ℤ)+1) * X)) (n+1)]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have : ((n + 1 - 1 - i : ℕ) : ℤ) + 1 = (n:ℤ) + 1 - i := by
      rw [show n + 1 - 1 - i = n - i by omega]
      push_cast [Nat.cast_sub (show i ≤ n by omega)]; ring
    simp only [this]
  have h1 : mk (q n (n+1)) * (∏ i ∈ Finset.range (n+1), (1 - C ((i:ℤ)+1) * X)) *
      (1 - C (1:ℤ) * X) = 1 := by rw [← hP]; exact G_prod n (n+1)
  have h2 : mk (fun r => ∑ i ∈ Finset.range (r+1), ((Nat.stirlingSecond (n+1+i) (n+1) : ℕ) : ℤ)) *
      (1 - C (1:ℤ) * X) * (∏ i ∈ Finset.range (n+1), (1 - C ((i:ℤ)+1) * X)) = 1 := by
    rw [Sg_rec, H_prod]
  have h : mk (q n (n+1)) =
      mk (fun r => ∑ i ∈ Finset.range (r+1), ((Nat.stirlingSecond (n+1+i) (n+1) : ℕ) : ℤ)) := by
    linear_combination
      (mk (fun r => ∑ i ∈ Finset.range (r+1), ((Nat.stirlingSecond (n+1+i) (n+1) : ℕ) : ℤ))) * h1 -
        (mk (q n (n+1))) * h2
  have := congrArg (coeff r) h
  simpa using this

end A380944Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a380944.main := by
  intro m n
  open OMA.S_oeis_a380944 A380944Proof in
  unfold a
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [OMA.S_oeis_a380944.binaryWeight, A380944Proof.b_k0]
  · have hx : 0 < 2^n - 1 := by
      have : 2 ≤ 2^n := by
        calc 2 = 2^1 := by norm_num
          _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    rw [A380944Proof.bw_pow_mul _ _ hx, A380944Proof.bw_ones,
      A380944Proof.formula n hn m n le_rfl]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.descFactorial_self]
    unfold OMA.S_oeis_a380944.c
    split_ifs with h
    · rw [A380944Proof.q_top, show m + 1 - (n+1) = (m - n - 1) + 1 by omega]
      push_cast; ring
    · rw [show m + 1 - (n+1) = 0 by omega]; simp
