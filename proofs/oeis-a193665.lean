import OMAStatements.S_oeis_a193665

namespace OMA.P193665

open OMA.S_oeis_a193665

/-- The convolution of r with the weights n+1-m. -/
def cc (n : ℕ) : ℤ := ∑ m ∈ Finset.range (n + 1), ((n : ℤ) + 1 - (m : ℤ)) * r m

lemma a_eq (n : ℕ) : a n = ((n : ℤ) + 1) * cc n := by
  unfold a cc
  rw [Finset.mul_sum]
  refine Eq.trans ?_
    (Finset.sum_range_reflect
      (fun m : ℕ => ((n : ℤ) + 1) * (((n : ℤ) + 1 - (m : ℤ)) * r m)) (n + 1))
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have h := Finset.mem_range.mp hk
    omega
  have e : n + 1 - 1 - k = n - k := by omega
  show (((k : ℤ) + 1) * ((n : ℤ) + 1)) * r (n - k)
    = ((n : ℤ) + 1) * (((n : ℤ) + 1 - ((n + 1 - 1 - k : ℕ) : ℤ)) * r (n + 1 - 1 - k))
  rw [e, Nat.cast_sub hkn]
  ring

lemma r_a (n : ℕ) : r (n + 1) = a n := by
  rw [r]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (((j : ℤ) + 1) * ((n : ℤ) + 1)) * r (n - j)) (n + 1)

lemma c_diff (n : ℕ) : cc (n + 1) - cc n = ∑ m ∈ Finset.range (n + 2), r m := by
  have hs : ∑ m ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m
      = ∑ m ∈ Finset.range (n + 1), ((n : ℤ) + 1 - (m : ℤ)) * r m
        + ∑ m ∈ Finset.range (n + 1), r m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    ring
  have e2 : ∑ m ∈ Finset.range (n + 2), (((n + 1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m
      = ∑ m ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m
        + (((n + 1 : ℕ) : ℤ) + 1 - ((n + 1 : ℕ) : ℤ)) * r (n + 1) :=
    Finset.sum_range_succ _ (n + 1)
  have e3 : ∑ m ∈ Finset.range (n + 2), r m
      = ∑ m ∈ Finset.range (n + 1), r m + r (n + 1) := Finset.sum_range_succ _ (n + 1)
  have h2 : cc (n + 1)
      = ∑ m ∈ Finset.range (n + 2), (((n + 1 : ℕ) : ℤ) + 1 - (m : ℤ)) * r m := rfl
  have h1 : cc n = ∑ m ∈ Finset.range (n + 1), ((n : ℤ) + 1 - (m : ℤ)) * r m := rfl
  rw [h2, e2, hs, e3, h1]
  ring

lemma c_rec (n : ℕ) : cc (n + 2) = ((n : ℤ) + 4) * cc (n + 1) - cc n := by
  have d1 := c_diff n
  have d2 : cc (n + 2) - cc (n + 1) = ∑ m ∈ Finset.range (n + 3), r m := c_diff (n + 1)
  have e3 : ∑ m ∈ Finset.range (n + 3), r m
      = ∑ m ∈ Finset.range (n + 2), r m + r (n + 2) := Finset.sum_range_succ _ (n + 2)
  have hr : r (n + 2) = a (n + 1) := r_a (n + 1)
  have ha := a_eq (n + 1)
  push_cast at ha
  linear_combination d2 + e3 - d1 + hr + ha

end OMA.P193665

open OMA.S_oeis_a193665 OMA.P193665 in
theorem OMA.solution : type_of% @OMA.S_oeis_a193665.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have e1 : j + 3 - 1 = j + 2 := by omega
  have e2 : j + 3 - 2 = j + 1 := by omega
  have e3 : j + 3 - 3 = j := by omega
  rw [e1, e2, e3, a_eq, a_eq, a_eq, a_eq]
  have c3 : cc (j + 3) = (((j + 1 : ℕ) : ℤ) + 4) * cc (j + 2) - cc (j + 1) := c_rec (j + 1)
  have c2 := c_rec j
  push_cast at c3 ⊢
  linear_combination ((j : ℤ) + 4) * c3 - ((j : ℤ) + 1) * c2
