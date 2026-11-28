import OMAStatements.S_oeis_a054390

/-!
Weight-preserving bijection by @wtho704, pinned commit
1c01ffbf471b1aef4bd8c9e2fedce9f9d17091bd (linked from PR21186).
This port retains that construction and omits unused auxiliary lemmas.

The binary digits of a multiplicity in {0,1,2,3} select the parts w and 2w.
This gives a weight-preserving bijection for any finite indexed family of
weights. For the powers of 3 the resulting parts are pairwise distinct.

Sources: https://oeis.org/A054390 and https://oeis.org/A038754
-/

open OMA.S_oeis_a054390

namespace OMA.TernaryPartitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def encode (d : ι → Fin 4) : Finset (ι × Bool) :=
  Finset.univ.filter fun p => if p.2 then 2 ≤ (d p.1).val else (d p.1).val % 2 = 1

def decode (s : Finset (ι × Bool)) (i : ι) : Fin 4 :=
  ⟨(if (i, false) ∈ s then 1 else 0) + (if (i, true) ∈ s then 2 else 0),
    by split <;> split <;> decide⟩

theorem decode_encode (d : ι → Fin 4) : decode (encode d) = d := by
  funext i
  apply Fin.ext
  simp only [decode, encode, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.false_eq_true, if_false, if_true]
  have h := (d i).isLt
  split <;> split <;> omega

theorem encode_decode (s : Finset (ι × Bool)) : encode (decode s) = s := by
  apply Finset.ext
  rintro ⟨i, t⟩
  unfold encode
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  cases t <;> by_cases h₁ : (i, false) ∈ s <;> by_cases h₂ : (i, true) ∈ s <;>
    simp [decode, h₁, h₂]

def selectionEquiv : (ι → Fin 4) ≃ Finset (ι × Bool) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem decode_preserves (w : ι → ℕ) (s : Finset (ι × Bool)) :
    distinctWeight w s = boundedWeight w (decode s) := by
  unfold distinctWeight boundedWeight
  have sum_slots (f : ι × Bool → ℕ) :
      ∑ p ∈ s, f p = ∑ p : ι × Bool, if p ∈ s then f p else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [sum_slots, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  by_cases h₁ : (i, false) ∈ s <;> by_cases h₂ : (i, true) ∈ s <;>
    simp [decode, h₁, h₂]
  all_goals omega

/-- For every target sum, multiplicities below four and subsets of labelled
single and double weights have the same cardinality. -/
theorem count_equal (w : ι → ℕ) (n : ℕ) :
    Fintype.card {d : ι → Fin 4 // boundedWeight w d = n} =
    Fintype.card {s : Finset (ι × Bool) // distinctWeight w s = n} := by
  apply Fintype.card_congr
  apply selectionEquiv.subtypeEquiv
  intro d
  change boundedWeight w d = n ↔ distinctWeight w (encode d) = n
  rw [decode_preserves, decode_encode]

end OMA.TernaryPartitions

theorem OMA.solution : type_of% @OMA.S_oeis_a054390.main := by
  intro n
  exact OMA.TernaryPartitions.count_equal (fun i : Fin n => 3 ^ (i : ℕ)) n

