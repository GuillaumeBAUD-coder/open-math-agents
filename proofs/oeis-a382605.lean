import OMAStatements.S_oeis_a382605
import Mathlib

namespace A382605

open OMA.S_oeis_a382605

lemma two_total (n : ℕ) : 2 * total n = n * (n + 1) := by
  induction n with
  | zero => simp [total]
  | succ k ih =>
    rw [total, mul_add, ih]
    ring

lemma even_cases (n : ℕ) (h : Even (total n)) : ∃ m, n = 4 * m ∨ n = 4 * m + 3 := by
  obtain ⟨r, hr⟩ := h
  have h2 := two_total n
  obtain ⟨m, hm⟩ : ∃ m, n = 4 * m ∨ n = 4 * m + 1 ∨ n = 4 * m + 2 ∨ n = 4 * m + 3 :=
    ⟨n / 4, by omega⟩
  rcases hm with rfl | rfl | rfl | rfl
  · exact ⟨m, Or.inl rfl⟩
  · exfalso
    have e : (4 * m + 1) * (4 * m + 1 + 1) = 4 * (4 * (m * m) + 3 * m) + 2 := by ring
    rw [e] at h2
    omega
  · exfalso
    have e : (4 * m + 2) * (4 * m + 2 + 1) = 4 * (4 * (m * m) + 5 * m + 1) + 2 := by ring
    rw [e] at h2
    omega
  · exact ⟨m, Or.inr rfl⟩

lemma folds_iff (n : ℕ) (hn : 0 < n) : folds n ↔ Even (total n) := by
  constructor
  · rintro ⟨i, j, _, _, h⟩
    exact ⟨total j - total i, by omega⟩
  · intro h
    obtain ⟨m, rfl | rfl⟩ := even_cases n h
    · refine ⟨m, 3 * m, by omega, by omega, ?_⟩
      have h1 := two_total (3 * m)
      have h2 := two_total (4 * m)
      have h3 := two_total m
      have e : 2 * (2 * total (3 * m)) = 2 * (total (4 * m) + 2 * total m) := by
        rw [h1, show 2 * (total (4 * m) + 2 * total m) = 2 * total (4 * m) + 2 * (2 * total m) by ring,
          h2, h3]
        ring
      omega
    · refine ⟨m, 3 * m + 2, by omega, by omega, ?_⟩
      have h1 := two_total (3 * m + 2)
      have h2 := two_total (4 * m + 3)
      have h3 := two_total m
      have e : 2 * (2 * total (3 * m + 2)) = 2 * (total (4 * m + 3) + 2 * total m) := by
        rw [h1, show 2 * (total (4 * m + 3) + 2 * total m) =
          2 * total (4 * m + 3) + 2 * (2 * total m) by ring, h2, h3]
        ring
      omega

lemma inA_iff (n : ℕ) (hn : 0 < n) : inA154708 n ↔ Even (total n) := by
  constructor
  · rintro ⟨b, c, hb, hc, h⟩
    obtain ⟨d, rfl⟩ : ∃ d, c = b + d := ⟨c - b, by omega⟩
    have h2 : n * (n + 1) = d * (2 * b + d) := by
      have h' : n * (n + 1) + b ^ 2 = d * (2 * b + d) + b ^ 2 := by
        rw [h]
        ring
      exact Nat.add_right_cancel h'
    have h3 := two_total n
    rw [h2] at h3
    rcases Nat.even_or_odd' d with ⟨e, rfl | rfl⟩
    · refine ⟨e * (b + e), ?_⟩
      have e1 : 2 * e * (2 * b + 2 * e) = 2 * (e * (b + e) + e * (b + e)) := by ring
      rw [e1] at h3
      omega
    · exfalso
      have e1 : (2 * e + 1) * (2 * b + (2 * e + 1)) = 2 * (2 * (e * b) + 2 * (e * e) + 2 * e + b) + 1 := by
        ring
      rw [e1] at h3
      omega
  · intro h
    obtain ⟨m, rfl | rfl⟩ := even_cases n h
    · refine ⟨3 * m + 1, 5 * m + 1, by omega, by omega, ?_⟩
      ring
    · refine ⟨3 * m + 2, 5 * m + 4, by omega, by omega, ?_⟩
      ring

end A382605

theorem OMA.solution : type_of% @OMA.S_oeis_a382605.main := by
  intro n hn
  have h1 := A382605.folds_iff n hn
  exact ⟨h1, h1.trans (A382605.inA_iff n hn).symm⟩
