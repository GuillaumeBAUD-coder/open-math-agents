import OMAStatements.S_oeis_a134195
import Mathlib

/-
A134195: the antidiagonal sums of the array e(q, k), with e(q, 0) = 0 and
e(q, k+1) = q e(q, k) + (k+1), are the partial sums of the row sums of geometric sums.

- geo_succ: G(q, k+1) = q G(q, k) + 1 for G(q, k) = 1 + q + ... + q^(k-1).
- entry_succ: e(q, m+1) = e(q, m) + G(q, m+1), by induction on m.
- The claim follows by induction on n: passing from n to n + 1 adds G(q, n+2-q) to every term
  with q <= n and adds the new term e(n+1, 1) = G(n+1, 1), which together are the next row sum.
-/

namespace OMA.P134195

open Finset

lemma geo_succ (q k : ℕ) : ∑ j ∈ range (k + 1), q ^ j = q * ∑ j ∈ range k, q ^ j + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma entry_succ (e : ℕ → ℕ → ℕ) (he0 : ∀ q, e q 0 = 0)
    (hes : ∀ q k, e q (k + 1) = q * e q k + (k + 1)) (q m : ℕ) :
    e q (m + 1) = e q m + ∑ j ∈ range (m + 1), q ^ j := by
  induction m with
  | zero =>
    rw [hes, he0]
    simp
  | succ m ih =>
    have h1 := hes q (m + 1)
    have h2 := hes q m
    have h3 := geo_succ q (m + 1)
    have hq : q * e q (m + 1) = q * e q m + q * ∑ j ∈ range (m + 1), q ^ j := by
      rw [ih, mul_add]
    rw [h3, h1]
    linarith

lemma main' (e : ℕ → ℕ → ℕ) (he0 : ∀ q, e q 0 = 0)
    (hes : ∀ q k, e q (k + 1) = q * e q k + (k + 1)) :
    ∀ n : ℕ, ∑ q ∈ range (n + 1), e q (n + 1 - q) =
      ∑ k ∈ range (n + 1), ∑ q ∈ range (k + 1), ∑ j ∈ range (k + 1 - q), q ^ j := by
  intro n
  induction n with
  | zero => simp [hes, he0]
  | succ n ih =>
    rw [Finset.sum_range_succ _ (n + 1),
      Finset.sum_range_succ (fun k => ∑ q ∈ range (k + 1), ∑ j ∈ range (k + 1 - q), q ^ j) (n + 1),
      ← ih, Finset.sum_range_succ (fun q => ∑ j ∈ range (n + 1 + 1 - q), q ^ j) (n + 1)]
    have h1 : ∀ q ∈ range (n + 1), e q (n + 1 + 1 - q) =
        e q (n + 1 - q) + ∑ j ∈ range (n + 1 + 1 - q), q ^ j := by
      intro q hq
      have hq' := mem_range.1 hq
      rw [show n + 1 + 1 - q = (n + 1 - q) + 1 by omega]
      exact entry_succ e he0 hes q (n + 1 - q)
    have h2 : e (n + 1) (n + 1 + 1 - (n + 1)) =
        ∑ j ∈ range (n + 1 + 1 - (n + 1)), (n + 1) ^ j := by
      rw [show n + 1 + 1 - (n + 1) = 0 + 1 by omega, entry_succ e he0 hes (n + 1) 0, he0]
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]
    ring

end OMA.P134195

theorem OMA.solution : type_of% @OMA.S_oeis_a134195.main := OMA.P134195.main' OMA.S_oeis_a134195.arrayEntry (fun _ => rfl) (fun _ _ => rfl)
