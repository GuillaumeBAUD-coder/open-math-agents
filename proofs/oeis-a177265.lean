import OMAStatements.S_oeis_a177265

-- Problem: A177265: Number of permutations of {1,2,...,n} having exactly one string of consecutive fixed points (including singletons).
-- Upstream: formal-conjectures statements/oeis-a177265.lean:0 (declaration OMA.S_oeis_a177265.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The derangement numbers satisfy d(k+2) = (k+1) (d(k) + d(k+1)). For n ≥ 5 the defining recurrence
a(k) = a(k-1) + k d(k-1) applies to a(n), ..., a(n-3). Substituting these four instances leaves
n d(n-1) + (2-n)(n-1) d(n-2) + (3-2n)(n-2) d(n-3) + (2-n)(n-3) d(n-4), which vanishes by the
recurrence for d at n-1 and n-2. -/

namespace A177265Aux

open OMA.S_oeis_a177265

theorem a_step (k : ℕ) : a (k + 2) = a (k + 1) + ((k : ℤ) + 2) * (numDerangements (k + 1) : ℤ) := by
  rw [a]

theorem d_step (k : ℕ) : (numDerangements (k + 2) : ℤ) =
    ((k : ℤ) + 1) * ((numDerangements k : ℤ) + (numDerangements (k + 1) : ℤ)) := by
  have h := numDerangements_add_two k
  exact_mod_cast h

end A177265Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a177265.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 + 2 := ⟨n - 5, by omega⟩
  have e1 : m + 3 + 2 - 1 = m + 2 + 2 := rfl
  have e2 : m + 3 + 2 - 2 = m + 1 + 2 := rfl
  have e3 : m + 3 + 2 - 3 = m + 2 := rfl
  have e4 : m + 3 + 2 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  have h0 := A177265Aux.a_step (m + 3)
  have h1 := A177265Aux.a_step (m + 2)
  have h2 := A177265Aux.a_step (m + 1)
  have h3 := A177265Aux.a_step m
  have hd1 := A177265Aux.d_step (m + 2)
  have hd2 := A177265Aux.d_step (m + 1)
  push_cast at h0 h1 h2 h3 hd1 hd2 ⊢
  linear_combination h0 + (2 - ((m : ℤ) + 5)) * h1 + (3 - 2 * ((m : ℤ) + 5)) * h2 +
    (2 - ((m : ℤ) + 5)) * h3 + ((m : ℤ) + 5) * hd1 + (((m : ℤ) + 5) - 2) * hd2
