import OMAStatements.S_oeis_a212797
import Mathlib

namespace OMA.S_oeis_a212797

lemma c2 (n : ℕ) : c (n+2) = 6 * c (n+1) - c n := rfl

lemma b_form : ∀ n : ℕ, 2 * squareTriIndex n + 1 = c (n+1) - 3 * c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [squareTriIndex, c]
    | 1, _ => simp [squareTriIndex, c]
    | m+2, ih =>
      have h0 := ih m (by omega)
      have h1 := ih (m+1) (by omega)
      have e1 : squareTriIndex (m+2) = 6 * squareTriIndex (m+1) - squareTriIndex m + 2 := rfl
      have e2 : c (m+3) = 6 * c (m+2) - c (m+1) := rfl
      have e3 : c (m+2) = 6 * c (m+1) - c m := rfl
      rw [e1, e2]
      linarith

def F (n : ℕ) : ℤ := (n:ℤ) * (17 * c (n+1) - 3 * c n) - 3 * c n + 16 * c (n+1)

lemma g_form : ∀ n : ℕ, 16 * g n = F n ∧ 16 * g (n+1) = F (n+1) ∧ 16 * g (n+2) = F (n+2) ∧ 16 * g (n+3) = F (n+3) := by
  intro n
  induction n with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [F, g, c]
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨h1, h2, h3, ?_⟩
    have e : g (m+1+3) = 12 * g (m+3) - 38 * g (m+2) + 12 * g (m+1) - g m := rfl
    rw [e]
    have c2' := c2 m
    have c3 := c2 (m+1)
    have c4 := c2 (m+2)
    have c5 := c2 (m+3)
    simp only [F] at h0 h1 h2 h3 ⊢
    push_cast at *
    have : c (m+1+3+1) = 6 * c (m+1+3) - c (m+1+2) := c5
    nlinarith [h0, h1, h2, h3, c2', c3, c4, c5]

theorem main_aux : type_of% @OMA.S_oeis_a212797.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hb := b_form (m+1)
    have hF := g_form m
    have hF1 := (g_form (m+1)).1
    have h2 := c2 m
    simp only [Nat.add_sub_cancel]
    simp only [a, F] at *
    push_cast at *
    have h3 := c2 (m+1)
    nlinarith [hb, hF.1, hF1, h2, h3]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have hb := b_form (m+3)
    have hF := g_form m
    have h2 := c2 m
    have h3 := c2 (m+1)
    have h4 := c2 (m+2)
    have e1 : m + 3 - 1 = m + 2 := by omega
    have e2 : m + 3 - 2 = m + 1 := by omega
    have e3 : m + 3 - 3 = m := by omega
    rw [e1, e2, e3]
    simp only [a, F] at *
    push_cast at *
    nlinarith [hb, hF.1, hF.2.1, hF.2.2.1, hF.2.2.2, h2, h3, h4]

end OMA.S_oeis_a212797

theorem OMA.solution : type_of% @OMA.S_oeis_a212797.main := OMA.S_oeis_a212797.main_aux
