import OMAStatements.S_oeis_a000579

namespace A000579Proof

open scoped BigOperators

-- 同时对普通和与加权和归纳。平移指标后，权重 k+1 分裂为 k 与 1。
theorem choose_sums (c r : ℕ) (hc : c ≤ r) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), Nat.choose (n - k + c) r) =
        Nat.choose (n + c + 1) (r + 1) ∧
    (∑ k ∈ Finset.range (n + 1), k * Nat.choose (n - k + c) r) =
        Nat.choose (n + c + 1) (r + 2) := by
  induction n with
  | zero =>
    have h₁ : Nat.choose c (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h₂ : Nat.choose (c + 1) (r + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    constructor
    · simp [Nat.choose_succ_succ, h₁]
    · simp [h₂]
  | succ n ih =>
    obtain ⟨hu, hw⟩ := ih
    have e : n.succ + c = n + c + 1 := by omega
    constructor
    · rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, hu, e]
      rw [Nat.choose_succ_succ (n + c + 1) r]
      exact Nat.add_comm _ _
    · rw [Finset.sum_range_succ']
      simp only [Nat.succ_sub_succ_eq_sub, Nat.add_mul, one_mul, zero_mul,
        add_zero, Finset.sum_add_distrib, hu, hw, e]
      rw [Nat.choose_succ_succ (n + c + 1) (r + 1)]
      exact Nat.add_comm _ _

-- s 是已经选定的指标之和，p 是它们的乘积。
theorem sum_layer (n s p c r : ℕ) (hc : c ≤ r) :
    (∑ i ∈ Finset.range (n + 1),
      if s + i ≤ n then p * i * Nat.choose (n - (s + i) + c) r else 0) =
    if s ≤ n then p * Nat.choose (n - s + c + 1) (r + 2) else 0 := by
  by_cases hs : s ≤ n
  · simp only [hs, ite_true]
    let f := fun i => if s + i ≤ n then p * i * Nat.choose (n - (s + i) + c) r else 0
    change (∑ i ∈ Finset.range (n + 1), f i) = _
    have hz : ∀ i ≥ n - s + 1, f i = 0 := by
      intro i hi
      simp [f, show ¬ s + i ≤ n by omega]
    rw [Finset.eventually_constant_sum hz (show n - s + 1 ≤ n + 1 by omega)]
    rw [← (choose_sums c r hc (n - s)).2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [f, show s + i ≤ n by omega, Nat.sub_sub, Nat.mul_assoc]
  · simp [hs, show ∀ i, ¬ s + i ≤ n by intro i; omega]

end A000579Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a000579.main := by
  intro n
  unfold OMA.S_oeis_a000579.weightedTripleSimplexSum
  have inner (k l : ℕ) := A000579Proof.sum_layer n (k + l) (k * l) 0 0 (by decide)
  have middle (k : ℕ) := A000579Proof.sum_layer n k k 1 2 (by decide)
  have outer := A000579Proof.sum_layer n 0 1 2 4 (by decide)
  simp only [Nat.choose_zero_right, Nat.mul_one, Nat.add_zero, Nat.reduceAdd] at inner
  simp only [Nat.reduceAdd, Nat.add_assoc] at middle outer
  simpa only [inner, middle, Nat.zero_add, Nat.sub_zero, Nat.one_mul, Nat.zero_le,
    ite_true] using outer.symm
