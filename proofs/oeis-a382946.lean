import OMAStatements.S_oeis_a382946
import Mathlib

/-!
# A382946 : `a(n) > 0` for every `n > 2`.

Port of the kernel-verified proof (0 sorry, axioms propext / Classical.choice /
Quot.sound) from `E:\DemosMathNT\lean\A382946.lean`. The statement's own `P` and
`a_val` are used via `open OMA.S_oeis_a382946`.

Witness : `d(n) = n^3 + (n-2)·n + (n-1)` has base-`n` digits `[n-1, n-2, 0, 1]`,
and `k(n) = (n-1)·n^3 + (n-2)·n^2 + 1 = (n-1)·d(n)` has digits `[1, 0, n-2, n-1]`,
the exact reversal, hence `Perm`. The admissible set contains `kw n` (nonempty)
and does not contain `0`, so `sInf > 0`.
-/

namespace OMA.A382946Port

open OMA.S_oeis_a382946

/-- Witness `d(n) = n^3 + (n-2)·n + (n-1)` : in base `n`, digits
`[n-1, n-2, 0, 1]` (least significant first). -/
def dw (n : ℕ) : ℕ := n^3 + (n-2)*n + (n-1)

/-- Witness `k(n) = (n-1)·n^3 + (n-2)·n^2 + 1 = (n-1)·d(n)` : digits
`[1, 0, n-2, n-1]`, the reversal of those of `d`. -/
def kw (n : ℕ) : ℕ := (n-1)*n^3 + (n-2)*n^2 + 1

set_option maxHeartbeats 800000 in
/-- The witness is admissible for every `n = m + 3` :
`dw (m+3) = (m+3)^3 + (m+1)·(m+3) + (m+2)` has digits `[m+2, m+1, 0, 1]`, and
`kw (m+3) = (m+2)·dw (m+3)` has digits `[1, 0, m+1, m+2]`, the reversal,
hence `Perm`. -/
theorem witness_ok (m : ℕ) : P (m+3) (kw (m+3)) (dw (m+3)) := by
  have sub1 : m + 3 - 1 = m + 2 := by omega
  have sub2 : m + 3 - 2 = m + 1 := by omega
  have hDm : dw (m+3) = (m+3)^3 + (m+1)*(m+3) + (m+2) := by
    unfold dw; rw [sub2, sub1]
  have hKm : kw (m+3) = (m+2)*(m+3)^3 + (m+1)*(m+3)^2 + 1 := by
    unfold kw; rw [sub1, sub2]
  have hdigD : Nat.digits (m+3) (dw (m+3)) = [m+2, m+1, 0, 1] := by
    have e : (m+3)^3 + (m+1)*(m+3) + (m+2)
        = Nat.ofDigits (m+3) [m+2, m+1, 0, 1] := by
      simp only [Nat.ofDigits_cons, Nat.ofDigits_nil]; ring
    rw [hDm, e]
    refine Nat.digits_ofDigits (m+3) (by omega) _ ?_ ?_
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (rfl | rfl | rfl | rfl) <;> omega
    · intro _
      exact Nat.succ_ne_zero _
  have hdigK : Nat.digits (m+3) (kw (m+3)) = [1, 0, m+1, m+2] := by
    have e : (m+2)*(m+3)^3 + (m+1)*(m+3)^2 + 1
        = Nat.ofDigits (m+3) [1, 0, m+1, m+2] := by
      simp only [Nat.ofDigits_cons, Nat.ofDigits_nil]; ring
    rw [hKm, e]
    refine Nat.digits_ofDigits (m+3) (by omega) _ ?_ ?_
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (rfl | rfl | rfl | rfl) <;> omega
    · intro _
      exact Nat.succ_ne_zero _
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨m+2, by rw [hKm, hDm]; ring⟩
  · rw [hKm, hDm]
    have hK : (m+2)*(m+3)^3 + (m+1)*(m+3)^2 + 1
        = ((m+3)^3 + (m+1)*(m+3) + (m+2)) * (m+2) := by ring
    rw [hK]
    have hD : 0 < (m+3)^3 + (m+1)*(m+3) + (m+2) := by omega
    calc (m+3)^3 + (m+1)*(m+3) + (m+2)
        < ((m+3)^3 + (m+1)*(m+3) + (m+2)) * 2 := by omega
      _ ≤ ((m+3)^3 + (m+1)*(m+3) + (m+2)) * (m+2) :=
          Nat.mul_le_mul (le_refl _) (by omega)
  · rw [hdigK, hdigD]
    simpa using ([m+2, m+1, 0, 1] : List ℕ).reverse_perm

/-- `a(n) > 0` for `n ≥ 3` : the admissible set contains `kw n` (nonempty) and
does not contain `0` (no `d < 0`), so `sInf > 0`. -/
theorem a382946_pos (n : ℕ) (hn : 3 ≤ n) : 0 < a_val n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hs : ({k : ℕ | ∃ d, P (m+3) k d}).Nonempty :=
    ⟨kw (m+3), dw (m+3), witness_ok m⟩
  have h0 : (0 : ℕ) ∉ {k : ℕ | ∃ d, P (m+3) k d} := by
    rintro ⟨d, -, hlt, -⟩
    omega
  have hne : a_val (m+3) ≠ 0 := by
    intro hz
    have hz' : sInf {k : ℕ | ∃ d, P (m+3) k d} = 0 := hz
    rw [Nat.sInf_eq_zero] at hz'
    rcases hz' with hz0 | hnil
    · exact h0 hz0
    · exact hs.ne_empty hnil
  omega

end OMA.A382946Port

theorem OMA.solution : type_of% @OMA.S_oeis_a382946.main := by
  intro n hn
  exact OMA.A382946Port.a382946_pos n hn
