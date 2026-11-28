import OMAStatements.S_oeis_a000247

/-!
# OEIS A000247: Jeffery's matrix identity

Write `w k = M ^ k *ᵥ 1`, where `M = unitPrimitiveMatrix n`. Row `i` of `M` has ones at
`i - 1` (when `i > 0`) and at `i + 1` (when `i + 1 < n`), plus a one on the diagonal in the last
row. So `w (k + 1) i = w k (i - 1) + w k (i + 1)`, with the first term dropped at `i = 0` and the
second replaced by `w k i` in the last row. We model this by `f n k i` on `ℕ` and show:

* `f n k i = 2 ^ k` when `k ≤ i` (the walk cannot reach the wall below row `0`);
* `f n (i + 1) i = 2 ^ (i + 1) - 1`;
* `f n (i + 3) i = 2 ^ (i + 3) - i - 5` when `i + 1 < n`.

With `i = n - 3` the last line reads `2 ^ n - n - 2`.
-/

open scoped Matrix

namespace OMA.P_oeis_a000247

open OMA.S_oeis_a000247

/-- The entries of `M ^ k *ᵥ 1`, indexed by `ℕ`. -/
def f (N : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, i => (if i = 0 then 0 else f N k (i - 1)) +
      (if i + 1 < N then f N k (i + 1) else f N k i)

lemma f_succ (N k i : ℕ) : f N (k + 1) i = (if i = 0 then 0 else f N k (i - 1)) +
    (if i + 1 < N then f N k (i + 1) else f N k i) := rfl

lemma f_low (N : ℕ) : ∀ k i, k ≤ i → f N k i = 2 ^ k := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i hi
    rw [f_succ, if_neg (by omega), ih (i - 1) (by omega)]
    split_ifs
    · rw [ih (i + 1) (by omega)]; ring
    · rw [ih i (by omega)]; ring

lemma f_diag (N : ℕ) : ∀ i, f N (i + 1) i = 2 ^ (i + 1) - 1 := by
  intro i
  induction i with
  | zero =>
    rw [f_succ, if_pos rfl]
    split_ifs <;> rfl
  | succ i ih =>
    rw [f_succ, if_neg (by omega), Nat.add_sub_cancel, ih]
    have h1 : f N (i + 1) (i + 1 + 1) = 2 ^ (i + 1) := f_low N _ _ (by omega)
    have h2 : f N (i + 1) (i + 1) = 2 ^ (i + 1) := f_low N _ _ le_rfl
    have h3 : 1 ≤ 2 ^ (i + 1) := Nat.one_le_two_pow
    split_ifs <;> [rw [h1]; rw [h2]] <;> rw [pow_succ 2 (i + 1)] <;> omega

lemma five_le (i : ℕ) : i + 5 ≤ 2 ^ (i + 3) := by
  have := Nat.lt_two_pow_self (n := i)
  rw [pow_add]
  norm_num
  omega

lemma f_third (N : ℕ) : ∀ i, i + 1 < N → f N (i + 3) i = 2 ^ (i + 3) - i - 5 := by
  intro i
  induction i with
  | zero =>
    intro hN
    rw [f_succ, if_pos rfl, if_pos hN]
    have := f_diag N 1
    simp only [Nat.reduceAdd] at this ⊢
    rw [this]; rfl
  | succ i ih =>
    intro hN
    rw [show i + 1 + 3 = (i + 3) + 1 by ring, f_succ, if_neg (by omega), if_pos hN,
      Nat.add_sub_cancel, ih (by omega), show i + 3 = (i + 1 + 1) + 1 by ring, f_diag]
    have h5 := five_le i
    rw [show i + 1 + 1 + 1 = i + 3 by ring, show i + 1 + 1 + 1 + 1 = i + 3 + 1 by ring,
      pow_succ 2 (i + 3)]
    omega

/-- One row of `M` applied to a vector. -/
lemma row_sum (n : ℕ) (g : ℕ → ℕ) (i : ℕ) (hi : i < n) :
    (∑ j ∈ Finset.range n,
      (if i + 1 = j ∨ j + 1 = i ∨ (i = j ∧ i + 1 = n) then 1 else 0) * g j) =
      (if i = 0 then 0 else g (i - 1)) + (if i + 1 < n then g (i + 1) else g i) := by
  have hsplit : ∀ j, (if i + 1 = j ∨ j + 1 = i ∨ (i = j ∧ i + 1 = n) then 1 else 0) * g j =
      ((if i = 0 then 0 else if j = i - 1 then g j else 0) +
        (if j = i + 1 then g j else 0)) + (if i + 1 = n then (if j = i then g j else 0) else 0) := by
    intro j
    split_ifs <;> omega
  rw [Finset.sum_congr rfl (fun j _ => hsplit j)]
  simp only [Finset.sum_add_distrib]
  by_cases h1 : i = 0 <;> by_cases h4 : i + 1 = n <;>
    simp [h1, h4, Finset.sum_ite_eq', Finset.mem_range] <;> split_ifs <;> omega

lemma key (n : ℕ) : ∀ k (i : Fin n),
    (unitPrimitiveMatrix n ^ k *ᵥ (fun _ : Fin n => 1)) i = f n k i.val := by
  intro k
  induction k with
  | zero => intro i; simp [f]
  | succ k ih =>
    intro i
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    have := row_sum n (f n k) i.val i.isLt
    rw [f_succ, ← this, Matrix.mulVec, dotProduct,
      Finset.sum_range (fun j => (if i.val + 1 = j ∨ j + 1 = i.val ∨ (i.val = j ∧ i.val + 1 = n)
        then 1 else 0) * f n k j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ih j]
    simp only [unitPrimitiveMatrix, Matrix.of_apply, Fin.ext_iff]

theorem prove_main : a 2 = 0 ∧
    ∀ (n : ℕ) (hn : 2 < n),
      ((unitPrimitiveMatrix n ^ n) *ᵥ (fun _ : Fin n => 1))
        ⟨n - 3, by omega⟩ = a n := by
  refine ⟨rfl, fun n hn => ?_⟩
  rw [key]
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 3 := ⟨n - 3, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [f_third _ i (by omega), a]
  omega

end OMA.P_oeis_a000247

theorem OMA.solution : type_of% @OMA.S_oeis_a000247.main :=
  OMA.P_oeis_a000247.prove_main
