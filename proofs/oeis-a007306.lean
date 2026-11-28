import OMAStatements.S_oeis_a007306

-- Problem: OEIS A007306, denominators of Farey tree fractions, a(n) = s(2n-1) with s Stern's
-- diatomic sequence. Conjecture of the entry: a(n) = a(n-1) + b(n-1) - 2 (a(n-1) mod b(n-1)),
-- b(n) = a(n) - b(n-1).
-- Proof. The pair of the recursion is (s(n) + s(n+1), s(n+1)), by Newman's formula
-- s(n+2) + 2 (s(n) mod s(n+1)) = s(n) + s(n+1), proved by strong induction on n.

open OMA.S_oeis_a007306

lemma OMA.stern_zero : stern 0 = 0 := by
  rw [stern]

lemma OMA.stern_one : stern 1 = 1 := by
  rw [stern]

lemma OMA.stern_even (m : ℕ) : stern (2 * m) = stern m := by
  rcases m with _ | m
  · rfl
  · have h : 2 * (m + 1) = 2 * m + 2 := by ring
    have h1 : (2 * m + 2) % 2 = 0 := by omega
    have h2 : (2 * m + 2) / 2 = m + 1 := by omega
    rw [h, stern, if_pos h1, h2]

lemma OMA.stern_odd (m : ℕ) : stern (2 * m + 1) = stern m + stern (m + 1) := by
  rcases m with _ | m
  · rw [OMA.stern_zero]
    simp
  · have h : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    have h1 : ¬ (2 * m + 1 + 2) % 2 = 0 := by omega
    have h2 : (2 * m + 1 + 2) / 2 = m + 1 := by omega
    rw [h, stern, if_neg h1, h2]

lemma OMA.stern_pos (n : ℕ) : 0 < stern (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' (n + 1) with ⟨m, h | h⟩
    · rw [h, OMA.stern_even]
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      exact ih j (by omega)
    · rw [h, OMA.stern_odd]
      rcases m with _ | j
      · rw [OMA.stern_zero, OMA.stern_one]
        norm_num
      · have hj := ih j (by omega)
        omega

/-- Newman's formula for Stern's diatomic sequence. -/
lemma OMA.newman (n : ℕ) :
    stern (n + 2) + 2 * (stern n % stern (n + 1)) = stern n + stern (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, h | h⟩
    · subst h
      have e1 : stern (2 * m + 2) = stern (m + 1) := by
        have h' : 2 * m + 2 = 2 * (m + 1) := by ring
        rw [h', OMA.stern_even]
      have hpos := OMA.stern_pos m
      have hlt : stern m < stern m + stern (m + 1) := by omega
      rw [e1, OMA.stern_even, OMA.stern_odd, Nat.mod_eq_of_lt hlt]
      ring
    · subst h
      have e1 : stern (2 * m + 1 + 2) = stern (m + 1) + stern (m + 2) := by
        have h' : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by ring
        rw [h', OMA.stern_odd]
      have e2 : stern (2 * m + 1 + 1) = stern (m + 1) := by
        have h' : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
        rw [h', OMA.stern_even]
      have hm := ih m (by omega)
      rw [e1, e2, OMA.stern_odd, Nat.add_mod_right]
      linarith

lemma OMA.ab_eq (n : ℕ) :
    ab n = ((stern n : ℤ) + (stern (n + 1) : ℤ), (stern (n + 1) : ℤ)) := by
  induction n with
  | zero =>
    have h : ab 0 = (1, 1) := rfl
    rw [h, OMA.stern_zero, OMA.stern_one]
    simp
  | succ n ih =>
    have hN := OMA.newman n
    have hN' : ((stern (n + 2) : ℕ) : ℤ) + 2 * ((stern n % stern (n + 1) : ℕ) : ℤ)
        = (stern n : ℤ) + (stern (n + 1) : ℤ) := by exact_mod_cast hN
    have hmod : ((stern n : ℤ) + (stern (n + 1) : ℤ)) % (stern (n + 1) : ℤ)
        = ((stern n % stern (n + 1) : ℕ) : ℤ) := by
      rw [Int.add_emod_right, Int.natCast_mod]
    have hstep : ab (n + 1) = ((ab n).1 + (ab n).2 - 2 * ((ab n).1 % (ab n).2),
        (ab n).1 + (ab n).2 - 2 * ((ab n).1 % (ab n).2) - (ab n).2) := rfl
    rw [hstep, ih]
    simp only []
    rw [hmod]
    refine Prod.ext ?_ ?_
    · show (stern n : ℤ) + (stern (n + 1) : ℤ) + (stern (n + 1) : ℤ)
          - 2 * ((stern n % stern (n + 1) : ℕ) : ℤ) = (stern (n + 1) : ℤ) + (stern (n + 1 + 1) : ℤ)
      linarith
    · show (stern n : ℤ) + (stern (n + 1) : ℤ) + (stern (n + 1) : ℤ)
          - 2 * ((stern n % stern (n + 1) : ℕ) : ℤ) - (stern (n + 1) : ℤ) = (stern (n + 1 + 1) : ℤ)
      linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a007306.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : m + 1 - 1 = m := rfl
  have h2 : a (m + 1) = stern m + stern (m + 1) := by
    unfold a
    have h3 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [if_neg (by omega), h3, OMA.stern_odd]
  rw [h1, OMA.ab_eq, h2]
  push_cast
  rfl
