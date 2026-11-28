import OMAStatements.S_oeis_a027117

namespace OMA.P027117

open OMA.S_oeis_a027117

def tr : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n + 3 => tr n + tr (n + 1) + tr (n + 2)

lemma Tstep (n k : ℕ) (h : k + 3 ≤ 2 * n + 1) :
    T (n + 1) (k + 3) = T n k + T n (k + 1) + T n (k + 2) := by
  have : k + 3 ≤ 2 * (n + 1) - 1 := by omega
  rw [T, if_pos this]

lemma Tleft : ∀ n k : ℕ, k ≤ n + 2 → T (n + 1) k = tr k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    interval_cases k <;> simp [T, tr]
  | succ n ih =>
    intro k hk
    match k, hk with
    | 0, _ => simp [T, tr]
    | 1, _ => simp [T, tr]
    | 2, _ => simp [T, tr]
    | j + 3, hj =>
      rw [Tstep (n + 1) j (by omega), ih j (by omega), ih (j + 1) (by omega),
        ih (j + 2) (by omega), tr]

lemma Tleft' (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n + 1) : T n k = tr k := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  exact Tleft p k (by omega)

def A (i : ℕ) : ℤ := T i (i + 4)
def B (i : ℕ) : ℤ := T i (i + 3)
def C (i : ℕ) : ℤ := T i (i + 2)

lemma A_succ (i : ℕ) (hi : 4 ≤ i) : A (i + 1) = A i + B i + C i := by
  unfold A B C
  have := Tstep i (i + 2) (by omega)
  rw [show i + 1 + 4 = i + 2 + 3 by ring, this]
  rw [show i + 2 + 1 = i + 3 by ring, show i + 2 + 2 = i + 4 by ring]
  ring

lemma B_succ (i : ℕ) (hi : 3 ≤ i) : B (i + 1) = B i + C i + tr (i + 1) := by
  unfold B C
  have := Tstep i (i + 1) (by omega)
  rw [show i + 1 + 3 = i + 1 + 3 by ring, this]
  rw [show i + 1 + 1 = i + 2 by ring, show i + 1 + 2 = i + 3 by ring,
    Tleft' i (i + 1) (by omega) (by omega)]
  ring

lemma C_succ (i : ℕ) (hi : 2 ≤ i) : C (i + 1) = C i + tr i + tr (i + 1) := by
  unfold C
  have := Tstep i i (by omega)
  rw [show i + 1 + 2 = i + 3 by ring, this]
  rw [Tleft' i i (by omega) (by omega), Tleft' i (i + 1) (by omega) (by omega),
    show i + 2 = i + 2 by ring]
  have h2 : T i (i + 2) = C i := rfl
  rw [h2]
  ring

end OMA.P027117

open OMA.S_oeis_a027117 OMA.P027117 in
theorem OMA.solution : type_of% @OMA.S_oeis_a027117.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have e : ∀ j : ℕ, j ≤ 6 → m + 10 - j = m + (10 - j) := fun j hj => by omega
  rw [e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega)]
  show A (m + 10) = 4 * A (m + 9) - 5 * A (m + 8) + 2 * A (m + 7) - A (m + 6) + 2 * A (m + 5)
    - A (m + 4)
  have a4 := A_succ (m + 4) (by omega)
  have a5 := A_succ (m + 5) (by omega)
  have a6 := A_succ (m + 6) (by omega)
  have a7 := A_succ (m + 7) (by omega)
  have a8 := A_succ (m + 8) (by omega)
  have a9 := A_succ (m + 9) (by omega)
  have b4 := B_succ (m + 4) (by omega)
  have b5 := B_succ (m + 5) (by omega)
  have b6 := B_succ (m + 6) (by omega)
  have b7 := B_succ (m + 7) (by omega)
  have b8 := B_succ (m + 8) (by omega)
  have c4 := C_succ (m + 4) (by omega)
  have c5 := C_succ (m + 5) (by omega)
  have c6 := C_succ (m + 6) (by omega)
  have c7 := C_succ (m + 7) (by omega)
  have c8 := C_succ (m + 8) (by omega)
  have t7 : tr (m + 7) = tr (m + 4) + tr (m + 5) + tr (m + 6) := by rw [tr]
  have t8 : tr (m + 8) = tr (m + 5) + tr (m + 6) + tr (m + 7) := by rw [tr]
  have t9 : tr (m + 9) = tr (m + 6) + tr (m + 7) + tr (m + 8) := by rw [tr]
  simp only [show m + 4 + 1 = m + 5 from rfl, show m + 5 + 1 = m + 6 from rfl,
    show m + 6 + 1 = m + 7 from rfl, show m + 7 + 1 = m + 8 from rfl,
    show m + 8 + 1 = m + 9 from rfl, show m + 9 + 1 = m + 10 from rfl] at *
  linarith
