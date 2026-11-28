import OMAStatements.S_oeis_a192431
import Mathlib

open Polynomial

namespace OMA.S_oeis_a192431

/-- state (a,b,c,d): P ≡ a + b x, Q ≡ c + d x mod x^2 - x - 1 -/
def st : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n + 1 =>
    let s := st n
    (s.2.1 + s.2.2.2 + 2 * s.2.2.1, s.1 + s.2.1 + s.2.2.1 + 3 * s.2.2.2,
      s.1 + s.2.2.2, s.2.1 + s.2.2.1 + s.2.2.2)

lemma cong (n : ℕ) :
    (X ^ 2 - X - 1 : ℤ[X]) ∣ (pq n).1 - (C (st n).1 + C (st n).2.1 * X) ∧
    (X ^ 2 - X - 1 : ℤ[X]) ∣ (pq n).2 - (C (st n).2.2.1 + C (st n).2.2.2 * X) := by
  induction n with
  | zero => simp [pq, st]
  | succ n ih =>
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := ih
    set m : ℤ[X] := X ^ 2 - X - 1 with hm
    have hP : (pq n).1 = C (st n).1 + C (st n).2.1 * X + m * u := by rw [← hu]; ring
    have hQ : (pq n).2 = C (st n).2.2.1 + C (st n).2.2.2 * X + m * v := by rw [← hv]; ring
    simp only [pq, st]
    refine ⟨?_, ?_⟩
    · refine ⟨X * u + (X + 2) * v + C (st n).2.1 + C (st n).2.2.2, ?_⟩
      rw [hP, hQ, hm]; simp only [map_add, map_mul, map_ofNat]; ring_nf
    · refine ⟨u + X * v + C (st n).2.2.2, ?_⟩
      rw [hP, hQ, hm]; simp only [map_add, map_mul]; ring_nf

lemma a_eq (n : ℕ) : a n = (st n).2.1 + (st n).2.2.2 := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := cong n
  have h : p n = (C ((st n).2.1 + (st n).2.2.2) * X + C ((st n).1 + (st n).2.2.1)) + (X ^ 2 - X - 1) * (u + v) := by
    unfold p
    have e1 : (pq n).1 = C (st n).1 + C (st n).2.1 * X + (X ^ 2 - X - 1) * u := by rw [← hu]; ring
    have e2 : (pq n).2 = C (st n).2.2.1 + C (st n).2.2.2 * X + (X ^ 2 - X - 1) * v := by rw [← hv]; ring
    rw [e1, e2]; simp only [map_add]; ring
  have hm : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!
  have hm : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!
  have h2 : p n %ₘ (X ^ 2 - X - 1) = C ((st n).2.1 + (st n).2.2.2) * X + C ((st n).1 + (st n).2.2.1) := by
    rw [Polynomial.modByMonic_eq_of_dvd_sub hm (q := (X ^ 2 - X - 1 : ℤ[X])) (p₂ := C ((st n).2.1 + (st n).2.2.2) * X + C ((st n).1 + (st n).2.2.1)) ⟨u + v, by rw [h]; ring⟩]
    rw [Polynomial.modByMonic_eq_self_iff hm]
    have hd : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!
    rw [hd]
    compute_degree!
  unfold a
  rw [h2, Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp

lemma rec_st (n : ℕ) : (st (n + 4)).2.1 + (st (n + 4)).2.2.2 =
    2 * ((st (n + 3)).2.1 + (st (n + 3)).2.2.2) + 6 * ((st (n + 2)).2.1 + (st (n + 2)).2.2.2)
    - 2 * ((st (n + 1)).2.1 + (st (n + 1)).2.2.2) - ((st n).2.1 + (st n).2.2.2) := by
  simp only [st]
  ring

end OMA.S_oeis_a192431

theorem OMA.solution : type_of% @OMA.S_oeis_a192431.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  simp only [OMA.S_oeis_a192431.a_eq]
  exact OMA.S_oeis_a192431.rec_st k
