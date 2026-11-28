import OMAStatements.S_oeis_a026975

namespace OMA.P026975

open OMA.S_oeis_a026975 Finset

lemma T_zero (n : ℕ) : T n 0 = 1 := by
  cases n with
  | zero => rfl
  | succ m => cases m <;> rfl

lemma T_gt : ∀ n k : ℕ, n < k → T n k = 0
  | 0, 0, h => by omega
  | 0, k + 1, _ => by rw [T]
  | 1, 0, h => by omega
  | 1, k + 1, h => by rw [T, if_neg (by omega)]
  | n + 2, 0, h => by omega
  | n + 2, k + 1, h => by rw [T, if_neg (by omega), if_neg (by omega)]

lemma T_diag : ∀ n : ℕ, T n n = 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by rw [T, if_pos rfl]

lemma T_rec (n k : ℕ) : T (n + 2) (k + 1)
    = T (n + 1) k + T (n + 1) (k + 1) + (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0) := by
  conv_lhs => rw [T]
  by_cases h1 : k + 1 = n + 2
  · have hk : k = n + 1 := by omega
    subst hk
    rw [if_pos h1, T_diag (n + 1), T_gt (n + 1) (n + 1 + 1) (by omega), if_neg (by omega)]
    norm_num
  · by_cases h2 : k + 1 < n + 2
    · rw [if_neg h1, if_pos h2]
      by_cases hc : (n + 2) % 2 = 0 ∧ (k + 1) % 2 = 1
      · rw [if_pos hc, if_pos (by omega)]; ring
      · rw [if_neg hc, if_neg (by omega)]; ring
    · rw [if_neg h1, if_neg h2, T_gt (n + 1) k (by omega), T_gt (n + 1) (k + 1) (by omega),
        T_gt n k (by omega)]
      simp

/-- weighted row sum -/
def W (n : ℕ) (g : ℕ → ℤ) : ℤ := ∑ k ∈ range (n + 1), g k * T n k

/-- weighted row sum over even columns -/
def Fe (n : ℕ) (h : ℕ → ℤ) : ℤ := ∑ k ∈ range (n + 1), (if k % 2 = 0 then h k * T n k else 0)

lemma W_congr (n : ℕ) (g g2 : ℕ → ℤ) (h : ∀ k, g k = g2 k) : W n g = W n g2 := by
  unfold W
  exact sum_congr rfl (fun k _ => by rw [h k])

lemma W_succ2 (n : ℕ) (g : ℕ → ℤ) :
    W (n + 2) g = W (n + 1) g + W (n + 1) (fun k => g (k + 1))
      + (if n % 2 = 0 then Fe n (fun k => g (k + 1)) else 0) := by
  have h1 : W (n + 2) g = ∑ k ∈ range (n + 2), g (k + 1) * T (n + 2) (k + 1)
      + g 0 * T (n + 2) 0 := sum_range_succ' _ _
  have h2 : ∑ k ∈ range (n + 2), g (k + 1) * T (n + 2) (k + 1)
      = ∑ k ∈ range (n + 2), g (k + 1) * T (n + 1) k
        + ∑ k ∈ range (n + 2), g (k + 1) * T (n + 1) (k + 1)
        + ∑ k ∈ range (n + 2), g (k + 1) * (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun k _ => ?_)
    rw [T_rec]
    ring
  have h3 : W (n + 1) g = ∑ k ∈ range (n + 1), g (k + 1) * T (n + 1) (k + 1)
      + g 0 * T (n + 1) 0 := sum_range_succ' _ _
  have h4 : ∑ k ∈ range (n + 2), g (k + 1) * T (n + 1) (k + 1)
      = ∑ k ∈ range (n + 1), g (k + 1) * T (n + 1) (k + 1)
        + g (n + 1 + 1) * T (n + 1) (n + 1 + 1) := sum_range_succ _ _
  have h5 : W (n + 1) (fun k => g (k + 1)) = ∑ k ∈ range (n + 2), g (k + 1) * T (n + 1) k := rfl
  have h6 : ∑ k ∈ range (n + 2), g (k + 1) * (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0)
      = ∑ k ∈ range (n + 1), g (k + 1) * (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0)
        + g (n + 1 + 1) * (if n % 2 = 0 ∧ (n + 1) % 2 = 0 then T n (n + 1) else 0) :=
    sum_range_succ _ _
  have h7 : ∑ k ∈ range (n + 1), g (k + 1) * (if n % 2 = 0 ∧ k % 2 = 0 then T n k else 0)
      = (if n % 2 = 0 then Fe n (fun k => g (k + 1)) else 0) := by
    by_cases hn : n % 2 = 0
    · rw [if_pos hn]
      unfold Fe
      refine sum_congr rfl (fun k _ => ?_)
      by_cases hk : k % 2 = 0
      · rw [if_pos ⟨hn, hk⟩, if_pos hk]
      · rw [if_neg (fun h => hk h.2), if_neg hk, mul_zero]
    · rw [if_neg hn]
      exact sum_eq_zero (fun k _ => by rw [if_neg (fun h => hn h.1), mul_zero])
  have z1 : T (n + 1) (n + 1 + 1) = 0 := T_gt _ _ (by omega)
  have z2 : (if n % 2 = 0 ∧ (n + 1) % 2 = 0 then T n (n + 1) else 0) = 0 := by
    rw [if_neg (by omega)]
  rw [h1, h2, h4, h6, h7, z1, z2, T_zero, h3, T_zero, h5]
  ring

def s (k : ℕ) : ℤ := (-1) ^ k

lemma s_succ (k : ℕ) : s (k + 1) = - s k := by
  unfold s; rw [pow_succ]; ring

lemma s_sq (k : ℕ) : s k * s k = 1 := by
  unfold s; rw [← mul_pow]; norm_num

lemma Fe_two (n : ℕ) (h : ℕ → ℤ) : 2 * Fe n h = W n h + W n (fun k => s k * h k) := by
  unfold Fe W
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  beta_reduce
  by_cases hk : k % 2 = 0
  · have hs : s k = 1 := Even.neg_one_pow (Nat.even_iff.mpr hk)
    rw [if_pos hk, hs]; ring
  · have hs : s k = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
    rw [if_neg hk, hs]; ring

def u (n : ℕ) : ℤ := W n (fun _ => 1)
def d (n : ℕ) : ℤ := W n (fun k => (k : ℤ))
def v (n : ℕ) : ℤ := W n s
def e (n : ℕ) : ℤ := W n (fun k => s k * (k : ℤ))

lemma W_add (n : ℕ) (g h : ℕ → ℤ) : W n (fun k => g k + h k) = W n g + W n h := by
  unfold W; rw [← sum_add_distrib]; exact sum_congr rfl (fun k _ => by ring)

lemma W_neg (n : ℕ) (g : ℕ → ℤ) : W n (fun k => - g k) = - W n g := by
  unfold W; rw [← sum_neg_distrib]; exact sum_congr rfl (fun k _ => by ring)

lemma a_eq (n : ℕ) : a n = u n + d n := by
  unfold a u d W
  rw [← sum_add_distrib]
  exact sum_congr rfl (fun k _ => by ring)

lemma lin (n : ℕ) (g g1 g2 : ℕ → ℤ) (a b : ℤ) (h : ∀ k, g k = a * g1 k + b * g2 k) :
    W n g = a * W n g1 + b * W n g2 := by
  unfold W
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun k _ => by rw [h k]; ring)

lemma uW (n : ℕ) : W n (fun _ => (1 : ℤ)) = u n := rfl
lemma dW (n : ℕ) : W n (fun k => (k : ℤ)) = d n := rfl
lemma vW (n : ℕ) : W n s = v n := rfl
lemma eW (n : ℕ) : W n (fun k => s k * (k : ℤ)) = e n := rfl

lemma step_odd (n : ℕ) (hn : ¬ n % 2 = 0) :
    u (n + 2) = 2 * u (n + 1) ∧ d (n + 2) = 2 * d (n + 1) + u (n + 1)
    ∧ v (n + 2) = 0 ∧ e (n + 2) = - v (n + 1) := by
  have hu := W_succ2 n (fun _ => (1 : ℤ))
  have hd := W_succ2 n (fun k => (k : ℤ))
  have hv := W_succ2 n s
  have he := W_succ2 n (fun k => s k * (k : ℤ))
  rw [if_neg hn] at hu hd hv he
  have l1 := lin (n + 1) (fun k => (((k + 1 : ℕ) : ℤ))) (fun k => (k : ℤ)) (fun _ => 1) 1 1
    (fun k => by push_cast; ring)
  have l2 := lin (n + 1) (fun k => s (k + 1)) s s (-1) 0 (fun k => by rw [s_succ]; ring)
  have l3 := lin (n + 1) (fun k => s (k + 1) * (((k + 1 : ℕ) : ℤ)))
    (fun k => s k * (k : ℤ)) s (-1) (-1) (fun k => by rw [s_succ]; push_cast; ring)
  simp only [uW, dW, vW, eW] at hu hd hv he l1 l2 l3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma step_even (n : ℕ) (hn : n % 2 = 0) :
    2 * u (n + 2) = 4 * u (n + 1) + u n + v n
    ∧ 2 * d (n + 2) = 4 * d (n + 1) + 2 * u (n + 1) + d n + u n + e n + v n
    ∧ 2 * v (n + 2) = -(v n + u n)
    ∧ 2 * e (n + 2) = - 2 * v (n + 1) - (e n + v n + d n + u n) := by
  have hu := W_succ2 n (fun _ => (1 : ℤ))
  have hd := W_succ2 n (fun k => (k : ℤ))
  have hv := W_succ2 n s
  have he := W_succ2 n (fun k => s k * (k : ℤ))
  rw [if_pos hn] at hu hd hv he
  have l1 := lin (n + 1) (fun k => (((k + 1 : ℕ) : ℤ))) (fun k => (k : ℤ)) (fun _ => 1) 1 1
    (fun k => by push_cast; ring)
  have l2 := lin (n + 1) (fun k => s (k + 1)) s s (-1) 0 (fun k => by rw [s_succ]; ring)
  have l3 := lin (n + 1) (fun k => s (k + 1) * (((k + 1 : ℕ) : ℤ)))
    (fun k => s k * (k : ℤ)) s (-1) (-1) (fun k => by rw [s_succ]; push_cast; ring)
  have fu := Fe_two n (fun _ => (1 : ℤ))
  have fd := Fe_two n (fun k => (((k + 1 : ℕ) : ℤ)))
  have fv := Fe_two n (fun k => s (k + 1))
  have fe := Fe_two n (fun k => s (k + 1) * (((k + 1 : ℕ) : ℤ)))
  have m1 := lin n (fun k => s k * 1) s s 1 0 (fun k => by ring)
  have m2 := lin n (fun k => (((k + 1 : ℕ) : ℤ))) (fun k => (k : ℤ)) (fun _ => 1) 1 1
    (fun k => by push_cast; ring)
  have m3 := lin n (fun k => s k * (((k + 1 : ℕ) : ℤ))) (fun k => s k * (k : ℤ)) s 1 1
    (fun k => by push_cast; ring)
  have m4 := lin n (fun k => s k * s (k + 1)) (fun _ => (1 : ℤ)) s (-1) 0
    (fun k => by rw [s_succ]; have := s_sq k; linarith)
  have m5 := lin n (fun k => s k * (s (k + 1) * (((k + 1 : ℕ) : ℤ))))
    (fun k => (k : ℤ)) (fun _ => (1 : ℤ)) (-1) (-1)
    (fun k => by rw [s_succ]; have := s_sq k; push_cast; linear_combination (-((k : ℤ) + 1)) * this)
  have m6 := lin n (fun k => s (k + 1)) s s (-1) 0 (fun k => by rw [s_succ]; ring)
  have m7 := lin n (fun k => s (k + 1) * (((k + 1 : ℕ) : ℤ)))
    (fun k => s k * (k : ℤ)) s (-1) (-1) (fun k => by rw [s_succ]; push_cast; ring)
  have m8 := lin n (fun k => s k * 1) s s 1 0 (fun k => by ring)
  simp only [uW, dW, vW, eW] at hu hd hv he l1 l2 l3 fu fd fv fe m1 m2 m3 m4 m5 m6 m7 m8
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma core (b : ℕ) (hb : b % 2 = 0) :
    a (b + 10) = 8 * a (b + 8) - 12 * a (b + 6) - 16 * a (b + 4) - 4 * a (b + 2)
    ∧ a (b + 11) = 8 * a (b + 9) - 12 * a (b + 7) - 16 * a (b + 5) - 4 * a (b + 3) := by
  obtain ⟨p0, q0, r0, t0⟩ := step_even b hb
  obtain ⟨p1, q1, r1, t1⟩ := step_odd (b + 1) (by omega)
  obtain ⟨p2, q2, r2, t2⟩ := step_even (b + 2) (by omega)
  obtain ⟨p3, q3, r3, t3⟩ := step_odd (b + 3) (by omega)
  obtain ⟨p4, q4, r4, t4⟩ := step_even (b + 4) (by omega)
  obtain ⟨p5, q5, r5, t5⟩ := step_odd (b + 5) (by omega)
  obtain ⟨p6, q6, r6, t6⟩ := step_even (b + 6) (by omega)
  obtain ⟨p7, q7, r7, t7⟩ := step_odd (b + 7) (by omega)
  obtain ⟨p8, q8, r8, t8⟩ := step_even (b + 8) (by omega)
  obtain ⟨p9, q9, r9, t9⟩ := step_odd (b + 9) (by omega)
  simp only [a_eq]
  constructor <;> linarith

lemma a8 : a 8 = 8 * a 6 - 12 * a 4 - 16 * a 2 - 4 * a 0 := by
  simp [a, T, Finset.sum_range_succ]

lemma a9 : a 9 = 8 * a 7 - 12 * a 5 - 16 * a 3 - 4 * a 1 := by
  simp [a, T, Finset.sum_range_succ]

end OMA.P026975

open OMA.S_oeis_a026975 OMA.P026975 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026975.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
  rw [show j + 8 - 2 = j + 6 by omega, show j + 8 - 4 = j + 4 by omega,
    show j + 8 - 6 = j + 2 by omega, show j + 8 - 8 = j by omega]
  rcases j with _ | _ | i
  · exact a8
  · exact a9
  · rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact (core i (by omega)).1
    · obtain ⟨c, rfl⟩ : ∃ c, i = c + 1 := ⟨i - 1, by omega⟩
      exact (core c (by omega)).2
