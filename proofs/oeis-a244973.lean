import OMAStatements.S_oeis_a244973
import Mathlib

/-!
Proof of the binomial-transform identity in A244973 (Peter Bala's conjecture):
`a(n) = Σ_k C(n,k) b(k)`. Swapping the two sums, it suffices that for `j ≤ n`
`Σ_k C(n,k) C(k,j)^2 C(2j,k) = C(n,j)^2 C(2j,j)`. This follows from
`C(n,k) C(k,j) = C(n,j) C(n-j,k-j)`, `C(2j,k) C(k,j) = C(2j,j) C(j,k-j)` and Vandermonde's
identity `Σ_i C(n-j,i) C(j,i) = C(n,j)`.
-/

namespace OMA.P_oeis_a244973

open Finset

/-- The term identity behind the swap of sums. -/
lemma term_eq (n j k : ℕ) :
    n.choose k * k.choose j ^ 2 * (2 * j).choose k =
      n.choose j * (2 * j).choose j *
        (if j ≤ k then (n - j).choose (k - j) * j.choose (k - j) else 0) := by
  split_ifs with hjk
  · have h1 := Nat.choose_mul (n := n) hjk
    have h2 := Nat.choose_mul (n := 2 * j) hjk
    rw [show 2 * j - j = j by omega] at h2
    calc n.choose k * k.choose j ^ 2 * (2 * j).choose k
        = (n.choose k * k.choose j) * ((2 * j).choose k * k.choose j) := by ring
      _ = _ := by rw [h1, h2]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : k < j)]
    simp

/-- Vandermonde in the form `Σ_i C(m,i) C(j,i) = C(m+j, j)`, summed far enough. -/
lemma vandermonde (m j N : ℕ) (hN : j ≤ N) :
    ∑ i ∈ range (N + 1), m.choose i * j.choose i = (m + j).choose j := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsub : range (j + 1) ⊆ range (N + 1) := by
    intro x hx; simp at hx ⊢; omega
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro i hi
    simp at hi
    rw [Nat.choose_symm (by omega : i ≤ j)]
  · intro i _ hi
    simp at hi
    rw [Nat.choose_eq_zero_of_lt (by omega : j < i)]
    simp

lemma inner_sum (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ range (n + 1), n.choose k * k.choose j ^ 2 * (2 * j).choose k =
      n.choose j ^ 2 * (2 * j).choose j := by
  rw [Finset.sum_congr rfl (fun k _ => term_eq n j k), ← Finset.mul_sum]
  have hsplit : n + 1 = j + (n - j + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h0 : ∑ x ∈ range j,
      (if j ≤ x then (n - j).choose (x - j) * j.choose (x - j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp at hx
    simp [show ¬ j ≤ x by omega]
  rw [h0, zero_add]
  have h1 : ∑ x ∈ range (n - j + 1),
      (if j ≤ j + x then (n - j).choose (j + x - j) * j.choose (j + x - j) else 0) =
      ∑ x ∈ range (n - j + 1), (n - j).choose x * j.choose x := by
    apply Finset.sum_congr rfl
    intro x _
    simp
  rw [h1]
  have hsub : range (n - j + 1) ⊆ range (n + 1) := by
    intro x hx; simp at hx ⊢; omega
  rw [Finset.sum_subset hsub, vandermonde (n - j) j n hj,
    show n - j + j = n by omega]
  · ring
  · intro i _ hi
    simp at hi
    rw [Nat.choose_eq_zero_of_lt (by omega : n - j < i)]
    simp

end OMA.P_oeis_a244973

open OMA.S_oeis_a244973 OMA.P_oeis_a244973 Finset in
theorem main_proof : ∀ n : ℕ, a n = ∑ k ∈ range (n + 1), (n.choose k : ℤ) * b k := by
  intro n
  unfold a b
  -- extend each inner sum to `range (n + 1)`
  have hext : ∀ k ∈ range (n + 1),
      (n.choose k : ℤ) * ∑ j ∈ range (k + 1),
        (-1 : ℤ) ^ j * (k.choose j : ℤ) ^ 2 * ((2 * j).choose k : ℤ) =
      ∑ j ∈ range (n + 1),
        (n.choose k : ℤ) * ((-1 : ℤ) ^ j * (k.choose j : ℤ) ^ 2 * ((2 * j).choose k : ℤ)) := by
    intro k hk
    simp at hk
    rw [Finset.mul_sum]
    have hsub : range (k + 1) ⊆ range (n + 1) := by
      intro x hx; simp at hx ⊢; omega
    apply Finset.sum_subset hsub
    intro j _ hj
    simp at hj
    rw [Nat.choose_eq_zero_of_lt (by omega : k < j)]
    simp
  rw [Finset.sum_congr rfl hext, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp at hj
  have key := inner_sum n j (by omega)
  have keyZ : ∑ k ∈ range (n + 1),
      ((n.choose k : ℤ) * (k.choose j : ℤ) ^ 2 * ((2 * j).choose k : ℤ)) =
      (n.choose j : ℤ) ^ 2 * ((2 * j).choose j : ℤ) := by exact_mod_cast key
  rw [mul_assoc, ← keyZ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

open OMA.S_oeis_a244973 in
theorem OMA.solution : type_of% @OMA.S_oeis_a244973.main := main_proof
