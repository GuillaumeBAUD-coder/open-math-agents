import OMAStatements.S_oeis_a230044
import Mathlib

namespace A230044Proof

open OMA.S_oeis_a230044

lemma two_T (m : ℕ) : 2 * T m = m * (m + 1) := by
  unfold T
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self m)

/-- Iterating the Pell step (m, s) -> (3m + 4s + 1, 2m + 3s + 1) keeps 2k = m(m+1) - 2s^2. -/
lemma grow (N : ℕ) : ∀ s m k : ℕ, 2 * k + 2 * s ^ 2 = m * (m + 1) →
    ∃ s' m' : ℕ, s + N ≤ s' ∧ m + N ≤ m' ∧ 2 * k + 2 * s' ^ 2 = m' * (m' + 1) := by
  induction N with
  | zero =>
    intro s m k h
    exact ⟨s, m, by omega, by omega, h⟩
  | succ N ih =>
    intro s m k h
    have h' : 2 * k + 2 * (2 * m + 3 * s + 1) ^ 2
        = (3 * m + 4 * s + 1) * (3 * m + 4 * s + 1 + 1) := by
      nlinarith [h]
    obtain ⟨s', m', h1, h2, h3⟩ := ih (2 * m + 3 * s + 1) (3 * m + 4 * s + 1) k h'
    exact ⟨s', m', by omega, by omega, h3⟩

end A230044Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a230044.main := by
  ext k
  constructor
  · rintro ⟨s, m, h⟩
    have h2 : 2 * k + 2 * s ^ 2 = m * (m + 1) := by
      rw [← A230044Proof.two_T m, ← h]
      ring
    obtain ⟨s', m', h3, h4, h5⟩ := A230044Proof.grow (k + 1) s m k h2
    have hT : OMA.S_oeis_a230044.T m' = k + s' ^ 2 := by
      have := A230044Proof.two_T m'
      omega
    have hsq : s' = Nat.sqrt (OMA.S_oeis_a230044.T m') := by
      rw [Nat.eq_sqrt', hT]
      constructor
      · omega
      · nlinarith
    refine ⟨m', by omega, ?_⟩
    unfold OMA.S_oeis_a230044.A064784
    rw [← hsq, hT]
    omega
  · rintro ⟨n, _, rfl⟩
    refine ⟨Nat.sqrt (OMA.S_oeis_a230044.T n), n, ?_⟩
    unfold OMA.S_oeis_a230044.A064784
    have := Nat.sqrt_le' (OMA.S_oeis_a230044.T n)
    omega
