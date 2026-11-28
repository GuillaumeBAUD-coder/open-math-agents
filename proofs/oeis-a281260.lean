import OMAStatements.S_oeis_a281260
import Mathlib

namespace A281260

open OMA.S_oeis_a281260 Finset

theorem c_rec (n : ℕ) :
    ∑ i ∈ range (n + 1), nar (n + 1) (i + 1) * c (i + 1) = if n = 0 then 1 else 0 := by
  rw [Finset.sum_range_succ]
  have h1 : nar (n + 1) (n + 1) = 1 := by
    unfold nar
    simp only [Nat.add_sub_cancel, Nat.choose_self, Nat.choose_succ_self_right]
    have : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  have h2 : c (n + 1) = (if n = 0 then 1 else 0)
      - ∑ i : Fin n, nar (n + 1) (i.val + 1) * c (i.val + 1) := by
    rw [c]
  rw [h1, h2, Fin.sum_univ_eq_sum_range (fun i => nar (n + 1) (i + 1) * c (i + 1)) n]
  ring

theorem key (m k d : ℕ) :
    (Nat.choose (m + (d + 1)) m : ℚ) * (Nat.choose ((k + 1) + (m + d + 1)) (k + 1) : ℚ)
        * ((d : ℚ) + 1)
      = (Nat.choose (m + (k + d + 1)) m : ℚ) * (Nat.choose (d + (k + 1)) d : ℚ)
        * ((m : ℚ) + k + d + 2) := by
  rw [Nat.cast_add_choose, Nat.cast_add_choose, Nat.cast_add_choose, Nat.cast_add_choose]
  have e1 : ((k + 1) + (m + d + 1)) = (m + (k + d + 1)) + 1 := by ring
  have e2 : m + d + 1 = m + (d + 1) := by ring
  rw [e1, e2]
  have f1 : ((m + (k + d + 1) + 1).factorial : ℚ)
      = ((m : ℚ) + k + d + 2) * ((m + (k + d + 1)).factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : ((d + 1).factorial : ℚ) = ((d : ℚ) + 1) * (d.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f3 : d + (k + 1) = k + d + 1 := by ring
  rw [f1, f2, f3]
  have g1 : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have g2 : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have g3 : ((k + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have g4 : ((m + (d + 1)).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have g5 : ((k + d + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have g6 : ((d : ℚ) + 1) ≠ 0 := by positivity
  field_simp

theorem term (m k d : ℕ) :
    (Nat.choose (m + k + d + 1 + 1 - (k + 1)) m : ℚ) * N m (m + k + d + 1) (k + 1)
      = ((m : ℚ) + 1) * (Nat.choose (m + k + d + 1) m : ℚ) * nar (k + d + 1) (d + 1) := by
  have a1 : m + k + d + 1 + 1 - (k + 1) = m + (d + 1) := by omega
  have a2 : m + k + d + 1 - m - 1 = k + d := by omega
  have a3 : m + k + d + 1 + 1 = (k + 1) + (m + d + 1) := by ring
  have a4 : m + k + d + 1 = m + (k + d + 1) := by ring
  have a5 : k + d + 1 = d + (k + 1) := by ring
  have hk := key m k d
  unfold N nar
  rw [if_neg (Nat.succ_ne_zero k), a1, a2, a3]
  simp only [Nat.add_sub_cancel]
  rw [a4, Nat.choose_symm_add (a := k) (b := d)]
  rw [← a5] at hk
  have g6 : ((d : ℚ) + 1) ≠ 0 := by positivity
  have g7 : ((m : ℚ) + k + d + 2) ≠ 0 := by positivity
  have g8 : (((m + (k + d + 1) : ℕ) : ℚ) + 1) = (m : ℚ) + k + d + 2 := by push_cast; ring
  have g9 : (((d + 1 : ℕ)) : ℚ) = (d : ℚ) + 1 := by push_cast; ring
  rw [g8, g9]
  generalize (Nat.choose (m + (d + 1)) m : ℚ) = A at hk ⊢
  generalize (Nat.choose (k + 1 + (m + d + 1)) (k + 1) : ℚ) = B at hk ⊢
  generalize (Nat.choose (m + (k + d + 1)) m : ℚ) = C at hk ⊢
  generalize (Nat.choose (k + d + 1) d : ℚ) = D at hk ⊢
  generalize (Nat.choose (k + d) d : ℚ) = E at hk ⊢
  have hk' : A * B = C * D * ((m : ℚ) + k + d + 2) / ((d : ℚ) + 1) := by
    rw [eq_div_iff g6]; exact hk
  have r1 : A * (((m : ℚ) + 1) / ((m : ℚ) + k + d + 2) * B * E)
      = ((m : ℚ) + 1) / ((m : ℚ) + k + d + 2) * E * (A * B) := by ring
  rw [r1, hk']
  field_simp

theorem main : ∀ m n : ℕ, m < n →
    ∑ k ∈ Finset.Icc 1 (n - m),
        (Nat.choose (n + 1 - k) m : ℚ) * N m n k * c (n + 1 - m - k)
      = ((m : ℚ) + 1) ^ 2 * (if n - m - 1 = 0 then 1 else 0) := by
  intro m n h
  obtain ⟨p, rfl⟩ : ∃ p, n = m + p + 1 := ⟨n - m - 1, by omega⟩
  have e0 : m + p + 1 - m = p + 1 := by omega
  have e1 : m + p + 1 - m - 1 = p := by omega
  rw [e0]
  simp only [Nat.add_sub_cancel]
  have s1 : ∑ k ∈ Finset.Icc 1 (p + 1),
        (Nat.choose (m + p + 1 + 1 - k) m : ℚ) * N m (m + p + 1) k * c (m + p + 1 + 1 - m - k)
      = ∑ i ∈ range (p + 1), (Nat.choose (m + p + 1 + 1 - (i + 1)) m : ℚ)
          * N m (m + p + 1) (i + 1) * c (m + p + 1 + 1 - m - (i + 1)) := by
    refine Finset.sum_nbij' (fun k => k - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [mem_Icc] at hk; simp only [mem_range]; omega
    · intro i hi; simp only [mem_range] at hi; simp only [mem_Icc]; omega
    · intro k hk; simp only [mem_Icc] at hk; omega
    · intro i hi; simp
    · intro k hk; simp only [mem_Icc] at hk
      have : k - 1 + 1 = k := by omega
      rw [this]
  rw [s1, ← Finset.sum_range_reflect]
  have s2 : ∀ d ∈ range (p + 1),
      (Nat.choose (m + p + 1 + 1 - (p + 1 - 1 - d + 1)) m : ℚ)
          * N m (m + p + 1) (p + 1 - 1 - d + 1) * c (m + p + 1 + 1 - m - (p + 1 - 1 - d + 1))
        = ((m : ℚ) + 1) * (Nat.choose (m + p + 1) m : ℚ) * (nar (p + 1) (d + 1) * c (d + 1)) := by
    intro d hd
    simp only [mem_range] at hd
    obtain ⟨k, rfl⟩ : ∃ k, p = k + d := ⟨p - d, by omega⟩
    have b1 : k + d + 1 - 1 - d = k := by omega
    have b2 : m + (k + d) + 1 + 1 - m - (k + 1) = d + 1 := by omega
    have b3 : m + (k + d) + 1 = m + k + d + 1 := by ring
    rw [b1, b2, b3, term m k d]
    ring
  rw [Finset.sum_congr rfl s2, ← Finset.mul_sum, c_rec]
  by_cases hp : p = 0
  · subst hp
    simp only [if_true, Nat.add_zero, Nat.choose_succ_self_right]
    push_cast; ring
  · simp [hp]

end A281260

theorem OMA.solution : type_of% @OMA.S_oeis_a281260.main := A281260.main
