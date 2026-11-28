import OMAStatements.S_oeis_a006218

-- Problem: A006218, the partial sums of Sum_{k<=m} floor(m/k) count arithmetic subsequences.
-- Credit: @ShoQo
-- Proof: (x, d, l) -> (n - x, d, l - 1) is a bijection onto {(m, k, j) : m < n, k, j >= 1,
-- k j <= m}, and for fixed m the pairs (k, j) number Sum_{k<=m} floor(m/k).

namespace OMA_A006218_Proof

def U (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun x => x.2.1 * x.2.2 ≤ x.1)

lemma inner (n m k : ℕ) (hm : m < n) (hk : 1 ≤ k) :
    ((Finset.Icc 1 n).filter (fun j => k * j ≤ m)).card = m / k := by
  have : (Finset.Icc 1 n).filter (fun j => k * j ≤ m) = Finset.Icc 1 (m / k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by nlinarith⟩, h3⟩
  rw [this, Nat.card_Icc]; simp

lemma card_U (n : ℕ) : (U n).card = ∑ m ∈ Finset.range n, OMA.S_oeis_a006218.a m := by
  unfold U
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [Finset.sum_product]
  unfold OMA.S_oeis_a006218.a
  have hsplit : ∑ k ∈ Finset.Icc 1 n, m / k = ∑ k ∈ Finset.Icc 1 m, m / k := by
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hm.le)]
    intro k hk hk'
    simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
    exact Nat.div_eq_of_lt (hk' hk.1)
  rw [← hsplit]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [← inner n m k hm hk.1, Finset.card_filter]

lemma card_T (n : ℕ) : (OMA.S_oeis_a006218.T n).card = (U n).card := by
  refine Finset.card_nbij' (fun x => (n - x.1, x.2.1, x.2.2 - 1)) (fun y => (n - y.1, y.2.1, y.2.2 + 1))
    ?_ ?_ ?_ ?_
  · rintro ⟨a, d, l⟩ h
    simp only [OMA.S_oeis_a006218.T, U, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range] at h ⊢
    obtain ⟨⟨⟨ha1, ha2⟩, ⟨hd1, hd2⟩, ⟨hl1, hl2⟩⟩, h⟩ := h
    refine ⟨⟨by omega, ⟨hd1, hd2⟩, by omega, by omega⟩, ?_⟩
    rw [mul_comm]; omega
  · rintro ⟨m, k, j⟩ h
    simp only [OMA.S_oeis_a006218.T, U, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range] at h ⊢
    obtain ⟨⟨hm, ⟨hk1, hk2⟩, ⟨hj1, hj2⟩⟩, h⟩ := h
    have : k * j ≥ j := Nat.le_mul_of_pos_left j hk1
    refine ⟨⟨by omega, ⟨hk1, hk2⟩, by omega, by omega⟩, ?_⟩
    rw [show j + 1 - 1 = j by omega, mul_comm]; omega
  · rintro ⟨a, d, l⟩ h
    simp only [OMA.S_oeis_a006218.T, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_Icc] at h
    dsimp only; rw [Prod.mk.injEq, Prod.mk.injEq]; omega
  · rintro ⟨m, k, j⟩ h
    simp only [U, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range] at h
    dsimp only; rw [Prod.mk.injEq, Prod.mk.injEq]; omega

end OMA_A006218_Proof

open OMA_A006218_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a006218.main :=
  fun n _ => (card_T n).trans (card_U n)
