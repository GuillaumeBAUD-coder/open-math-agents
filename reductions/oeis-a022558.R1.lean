import OMAStatements.S_oeis_a022558

-- Credit: @qu1r0ra

/-!
Reduction of `OMA.S_oeis_a022558.main` (OEIS A022558: `Av(1342)` vs `Av(2143, 415263)`)
to two holonomic recurrence hypotheses.

* `H1`: the 1342-avoidance counts satisfy Bóna's second-order P-recursive recurrence
  `(k + 4) * a(k + 4) = (7k + 6) * a(k + 3) + (8k + 28) * a(k + 2)` for all `k : ℕ`.
* `H2`: the `(2143, 415263)`-avoidance counts satisfy the same recurrence for all `k : ℕ`.

The base cases `n ≤ 3` hold unconditionally because no strictly increasing map
`Fin 4 ↪o Fin n` or `Fin 6 ↪o Fin n` exists when `n ≤ 3`, so both avoidance sets coincide
with all of `Equiv.Perm (Fin n)`. Strong induction then yields equality for all `n : ℕ`.
-/

namespace OMA.R_oeis_a022558_R1

def H1 : Prop :=
  ∀ k : ℕ,
    (k + 4) * Nat.card {perm : Equiv.Perm (Fin (k + 4)) //
        OMA.S_oeis_a022558.AvoidsPattern perm ![1, 3, 4, 2]} =
      (7 * k + 6) * Nat.card {perm : Equiv.Perm (Fin (k + 3)) //
        OMA.S_oeis_a022558.AvoidsPattern perm ![1, 3, 4, 2]} +
      (8 * k + 28) * Nat.card {perm : Equiv.Perm (Fin (k + 2)) //
        OMA.S_oeis_a022558.AvoidsPattern perm ![1, 3, 4, 2]}

def H2 : Prop :=
  ∀ k : ℕ,
    (k + 4) * Nat.card {perm : Equiv.Perm (Fin (k + 4)) //
        OMA.S_oeis_a022558.AvoidsPattern perm ![2, 1, 4, 3] ∧
          OMA.S_oeis_a022558.AvoidsPattern perm ![4, 1, 5, 2, 6, 3]} =
      (7 * k + 6) * Nat.card {perm : Equiv.Perm (Fin (k + 3)) //
        OMA.S_oeis_a022558.AvoidsPattern perm ![2, 1, 4, 3] ∧
          OMA.S_oeis_a022558.AvoidsPattern perm ![4, 1, 5, 2, 6, 3]} +
      (8 * k + 28) * Nat.card {perm : Equiv.Perm (Fin (k + 2)) //
        OMA.S_oeis_a022558.AvoidsPattern perm ![2, 1, 4, 3] ∧
          OMA.S_oeis_a022558.AvoidsPattern perm ![4, 1, 5, 2, 6, 3]}

section

lemma orderEmb_val_ge {k n : ℕ} (f : Fin k ↪o Fin n) :
    ∀ m : ℕ, (hm : m < k) → m ≤ (f ⟨m, hm⟩).val := by
  intro m
  induction m with
  | zero =>
    intro _
    exact Nat.zero_le _
  | succ m ih =>
    intro hm
    have hlt : f ⟨m, by omega⟩ < f ⟨m + 1, hm⟩ :=
      f.strictMono (by show m < m + 1; omega)
    have hle : m ≤ (f ⟨m, by omega⟩).val := ih (by omega)
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hle hlt)

lemma avoidsPattern_of_lt {n k : ℕ} (h : n < k) (perm : Equiv.Perm (Fin n))
    (pattern : Fin k → ℕ) : OMA.S_oeis_a022558.AvoidsPattern perm pattern := by
  rintro ⟨f, _⟩
  have hle : n ≤ (f ⟨n, h⟩).val := orderEmb_val_ge f n h
  exact Nat.not_lt_of_ge hle (f ⟨n, h⟩).isLt

lemma base_eq (n : ℕ) (hn : n ≤ 3) :
    Nat.card {perm : Equiv.Perm (Fin n) //
        OMA.S_oeis_a022558.AvoidsPattern perm ![1, 3, 4, 2]} =
      Nat.card {perm : Equiv.Perm (Fin n) //
        OMA.S_oeis_a022558.AvoidsPattern perm ![2, 1, 4, 3] ∧
          OMA.S_oeis_a022558.AvoidsPattern perm ![4, 1, 5, 2, 6, 3]} := by
  have h1 : ∀ perm : Equiv.Perm (Fin n),
      OMA.S_oeis_a022558.AvoidsPattern perm ![1, 3, 4, 2] :=
    fun perm => avoidsPattern_of_lt (by omega) perm ![1, 3, 4, 2]
  have h2 : ∀ perm : Equiv.Perm (Fin n),
      OMA.S_oeis_a022558.AvoidsPattern perm ![2, 1, 4, 3] ∧
        OMA.S_oeis_a022558.AvoidsPattern perm ![4, 1, 5, 2, 6, 3] :=
    fun perm =>
      ⟨avoidsPattern_of_lt (by omega) perm ![2, 1, 4, 3],
        avoidsPattern_of_lt (by omega) perm ![4, 1, 5, 2, 6, 3]⟩
  exact (Nat.card_congr (Equiv.subtypeUnivEquiv h1)).trans
    (Nat.card_congr (Equiv.subtypeUnivEquiv h2)).symm

end

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a022558.main := by
  intro h1 h2 n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => exact base_eq 0 (by omega)
    | 1 => exact base_eq 1 (by omega)
    | 2 => exact base_eq 2 (by omega)
    | 3 => exact base_eq 3 (by omega)
    | k + 4 =>
      have hk3 := ih (k + 3) (by omega)
      have hk2 := ih (k + 2) (by omega)
      have heq :
          (k + 4) * Nat.card {perm : Equiv.Perm (Fin (k + 4)) //
              OMA.S_oeis_a022558.AvoidsPattern perm ![1, 3, 4, 2]} =
          (k + 4) * Nat.card {perm : Equiv.Perm (Fin (k + 4)) //
              OMA.S_oeis_a022558.AvoidsPattern perm ![2, 1, 4, 3] ∧
                OMA.S_oeis_a022558.AvoidsPattern perm ![4, 1, 5, 2, 6, 3]} := by
        rw [h1 k, h2 k, hk3, hk2]
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 4) heq

end OMA.R_oeis_a022558_R1
