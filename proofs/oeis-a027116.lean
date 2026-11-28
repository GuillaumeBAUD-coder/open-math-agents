import OMAStatements.S_oeis_a027116

namespace OMA.P_oeis_a027116

open OMA.S_oeis_a027116

/-- Tribonacci numbers A000073. -/
def t : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => t n + t (n + 1) + t (n + 2)

lemma T_gen (n k : ℕ) (h3 : 3 ≤ k) (hk : k ≤ 2 * n + 1) :
    T (n + 1) k = T n (k - 3) + T n (k - 2) + T n (k - 1) := by
  rw [T, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]

lemma T_trib : ∀ n : ℕ, 1 ≤ n → ∀ k, k ≤ n + 1 → T n k = t (k + 2) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro k hk
    interval_cases k <;> rfl
  | succ n hn ih =>
    intro k hk
    rcases Nat.lt_or_ge k 3 with h | h
    · interval_cases k <;> simp [T, t]
    · rw [T_gen n k h (by omega), ih (k - 3) (by omega), ih (k - 2) (by omega),
        ih (k - 1) (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      rw [show j + 3 - 3 + 2 = j + 2 by omega, show j + 3 - 2 + 2 = j + 3 by omega,
        show j + 3 - 1 + 2 = j + 4 by omega]
      rfl

lemma b_step (n : ℕ) (hn : 2 ≤ n) :
    T (n + 1) (n + 1 + 2) = T n (n + 2) + t (n + 3) + t (n + 2) := by
  rw [T_gen n _ (by omega) (by omega), show n + 1 + 2 - 3 = n by omega,
    show n + 1 + 2 - 2 = n + 1 by omega, show n + 1 + 2 - 1 = n + 2 by omega,
    T_trib n (by omega) n (by omega), T_trib n (by omega) (n + 1) (by omega)]
  ring

lemma a_step (n : ℕ) (hn : 3 ≤ n) :
    a (n + 1) = a n + T n (n + 2) + t (n + 3) := by
  unfold a
  rw [T_gen n _ (by omega) (by omega), show n + 1 + 3 - 3 = n + 1 by omega,
    show n + 1 + 3 - 2 = n + 2 by omega, show n + 1 + 3 - 1 = n + 3 by omega,
    T_trib n (by omega) (n + 1) (by omega)]
  ring

end OMA.P_oeis_a027116

theorem OMA.solution : type_of% @OMA.S_oeis_a027116.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
    show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega]
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have A4 : a (m + 4) = a (m + 3) + T (m + 3) (m + 5) + t (m + 6) := a_step (m + 3) (by omega)
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have A5 : a (m + 5) = a (m + 4) + T (m + 4) (m + 6) + t (m + 7) := a_step (m + 4) (by omega)
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have A6 : a (m + 6) = a (m + 5) + T (m + 5) (m + 7) + t (m + 8) := a_step (m + 5) (by omega)
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have A7 : a (m + 7) = a (m + 6) + T (m + 6) (m + 8) + t (m + 9) := a_step (m + 6) (by omega)
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have A8 : a (m + 8) = a (m + 7) + T (m + 7) (m + 9) + t (m + 10) := a_step (m + 7) (by omega)
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have B4 : T (m + 4) (m + 6) = T (m + 3) (m + 5) + t (m + 6) + t (m + 5) :=
    b_step (m + 3) (by omega)
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have B5 : T (m + 5) (m + 7) = T (m + 4) (m + 6) + t (m + 7) + t (m + 6) :=
    b_step (m + 4) (by omega)
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have B6 : T (m + 6) (m + 8) = T (m + 5) (m + 7) + t (m + 8) + t (m + 7) :=
    b_step (m + 5) (by omega)
  open OMA.S_oeis_a027116 OMA.P_oeis_a027116 in
  have B7 : T (m + 7) (m + 9) = T (m + 6) (m + 8) + t (m + 9) + t (m + 8) :=
    b_step (m + 6) (by omega)
  open OMA.P_oeis_a027116 in
  have t8 : t (m + 8) = t (m + 5) + t (m + 6) + t (m + 7) := rfl
  open OMA.P_oeis_a027116 in
  have t9 : t (m + 9) = t (m + 6) + t (m + 7) + t (m + 8) := rfl
  open OMA.P_oeis_a027116 in
  have t10 : t (m + 10) = t (m + 7) + t (m + 8) + t (m + 9) := rfl
  omega
