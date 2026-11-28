import OMAStatements.S_oeis_a104722
import Mathlib

/-!
Proof of Mathar's recurrence for the self-convolution of repeated Catalan numbers.
Source: https://oeis.org/A104722
Statement: @vivanpoddar, PR #16151.

Split the convolution into its even and odd indices and use the Catalan convolution
identity and first-order recurrence. The resulting parity formulas agree with the
Catalan generating-function description discussed by James Sellers in the OEIS entry.
-/

open Finset OMA.S_oeis_a104722

namespace A104722Proof

lemma pair_sum (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range (2*n), f i = ∑ i ∈ range n, (f (2*i) + f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n+1) = 2*n+1+1 by omega, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

lemma catalan_sum (n : ℕ) :
    ∑ i ∈ range (n+1), (catalan i : ℤ) * catalan (n-i) = catalan (n+1) := by
  have h := catalan_succ n
  rw [← Finset.sum_range (fun i => catalan i * catalan (n-i))] at h
  exact_mod_cast h.symm

lemma a_odd (n : ℕ) : a (2*n+1) = 2 * (catalan (n+1) : ℤ) := by
  unfold a
  rw [show 2*n+1+1 = 2*(n+1) by omega, pair_sum]
  calc
    _ = ∑ i ∈ range (n+1), 2 * ((catalan i : ℤ) * catalan (n-i)) := by
      apply sum_congr rfl
      intro i hi
      have hi' : i ≤ n := by simpa using hi
      have h0 : (2*n+1-2*i)/2 = n-i := by omega
      have h1 : (2*n+1-(2*i+1))/2 = n-i := by omega
      simp only [b, h0, h1, show (2*i)/2 = i by omega, show (2*i+1)/2 = i by omega]
      ring
    _ = 2 * (catalan (n+1) : ℤ) := by rw [← mul_sum, catalan_sum]

lemma a_even (n : ℕ) :
    a (2*(n+1)) = (catalan (n+2) : ℤ) + catalan (n+1) := by
  unfold a
  rw [sum_range_succ, pair_sum]
  have hs :
      (∑ i ∈ range (n+1), ((b (2*i) : ℤ) * b (2*(n+1)-2*i) +
        (b (2*i+1) : ℤ) * b (2*(n+1)-(2*i+1)))) =
      (∑ i ∈ range (n+1), (catalan i : ℤ) * catalan (n+1-i)) +
      (catalan (n+1) : ℤ) := by
    rw [← catalan_sum n, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ n := by simpa using hi
    have h0 : (2*(n+1)-2*i)/2 = n+1-i := by omega
    have h1 : (2*(n+1)-(2*i+1))/2 = n-i := by omega
    simp [b, h0, h1, show (2*i+1)/2 = i by omega]
  rw [hs]
  have hc := catalan_sum (n+1)
  rw [sum_range_succ] at hc
  simp only [Nat.sub_self, catalan_zero, Nat.cast_one, mul_one] at hc
  simp [b]
  linarith

lemma catalan_rec (n : ℕ) :
    ((n : ℤ)+2) * catalan (n+1) = (4*(n : ℤ)+2) * catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1),
    ← succ_mul_catalan_eq_centralBinom n] at h
  have hz : ((n : ℤ)+1) * (((n : ℤ)+2) * catalan (n+1)) =
      2*(2*(n : ℤ)+1) * (((n : ℤ)+1) * catalan n) := by exact_mod_cast h
  apply mul_left_cancel₀ (show (n : ℤ)+1 ≠ 0 by omega)
  nlinarith only [hz]

theorem candidate : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 4) * a n + ((n : ℤ) + 1) * a (n - 1) - 4 * ((n : ℤ) + 1) * a (n - 2)
      + 4 * (2 - (n : ℤ)) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
  have hc1 := catalan_rec (k/2+1)
  have hc2 := catalan_rec (k/2+2)
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have he : k = 2*(k/2) := by omega
    have h0 : k+4 = 2*(k/2+2) := by omega
    have h1 : k+4-1 = 2*(k/2+1)+1 := by omega
    have h2 : k+4-2 = 2*(k/2+1) := by omega
    have h3 : k+4-3 = 2*(k/2)+1 := by omega
    have ha0 : a (k+4) = (catalan (k/2+3) : ℤ) + catalan (k/2+2) := by
      simpa [h0, Nat.add_assoc] using a_even (k/2+1)
    have ha1 : a (k+4-1) = 2*(catalan (k/2+2) : ℤ) := by
      simpa [h1, Nat.add_assoc] using a_odd (k/2+1)
    have ha2 : a (k+4-2) = (catalan (k/2+2) : ℤ) + catalan (k/2+1) := by
      simpa [h2] using a_even (k/2)
    have ha3 : a (k+4-3) = 2*(catalan (k/2+1) : ℤ) := by
      simpa [h3] using a_odd (k/2)
    rw [ha0, ha1, ha2, ha3]
    have hez : (k : ℤ) = 2 * (k/2 : ℕ) := by exact_mod_cast he
    push_cast at *
    nlinarith
  · have he : k = 2*(k/2)+1 := by omega
    have h0 : k+4 = 2*(k/2+2)+1 := by omega
    have h1 : k+4-1 = 2*(k/2+2) := by omega
    have h2 : k+4-2 = 2*(k/2+1)+1 := by omega
    have h3 : k+4-3 = 2*(k/2+1) := by omega
    have ha0 : a (k+4) = 2*(catalan (k/2+3) : ℤ) := by
      simpa [h0, Nat.add_assoc] using a_odd (k/2+2)
    have ha1 : a (k+4-1) = (catalan (k/2+3) : ℤ) + catalan (k/2+2) := by
      simpa [h1, Nat.add_assoc] using a_even (k/2+1)
    have ha2 : a (k+4-2) = 2*(catalan (k/2+2) : ℤ) := by
      simpa [h2, Nat.add_assoc] using a_odd (k/2+1)
    have ha3 : a (k+4-3) = (catalan (k/2+2) : ℤ) + catalan (k/2+1) := by
      simpa [h3] using a_even (k/2)
    rw [ha0, ha1, ha2, ha3]
    have hez : (k : ℤ) = 2 * (k/2 : ℕ) + 1 := by exact_mod_cast he
    push_cast at *
    nlinarith

end A104722Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a104722.main := A104722Proof.candidate
