import OMAReductions.R_BoundedBurnsideProblem_bounded_burnside_problem_R1_H1_R1

/-!
Proof of `OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1_H1_R1.H1`: there are binary
cube-free words of every length (Thue). The prefixes of the Thue–Morse word work.

`t (2 j) = t j` and `t (2 j + 1) = ¬ t j`. A cube of period `p` at `i` means
`t (i + k) = t (i + k + p)` for `k < 2 p`; there is none, by strong induction on `p`:
* `p = 1`: two consecutive positions `2 j, 2 j + 1` always differ;
* `p = 2 q`: halving positions gives a cube of period `q` at `(i + 1) / 2`;
* `p` odd, `p ≥ 3`: consecutive letters differ on `[i + p, i + 3 p - 1]`, so a cube of period `2`
  starts at `i + p`.
-/

namespace OMAProof.ThueMorse

/-- The Thue–Morse word. -/
def tm (n : ℕ) : Bool :=
  if h : n = 0 then false else if n % 2 = 0 then tm (n / 2) else !tm (n / 2)
termination_by n
decreasing_by all_goals omega

theorem tm_even (j : ℕ) : tm (2 * j) = tm j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  · rw [tm, dif_neg (by omega), if_pos (by omega)]
    congr 1
    omega

theorem tm_odd (j : ℕ) : tm (2 * j + 1) = !tm j := by
  rw [tm, dif_neg (by omega), if_neg (by omega)]
  congr 2
  omega

/-- Consecutive positions `2 j` and `2 j + 1` carry different letters. -/
theorem tm_pair (m : ℕ) (hm : m % 2 = 0) : tm m ≠ tm (m + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j := ⟨m / 2, by omega⟩
  rw [tm_even, tm_odd]
  cases tm j <;> simp

/-- A cube of period `p` starting at position `i`. -/
def Cube (i p : ℕ) : Prop := ∀ k < 2 * p, tm (i + k) = tm (i + k + p)

theorem bool_trans {a b c : Bool} (h1 : a ≠ b) (h2 : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem no_cube : ∀ p : ℕ, 0 < p → ∀ i : ℕ, ¬ Cube i p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp i hc
    rcases Nat.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩
    · -- even period: halve
      have hq0 : 0 < q := by omega
      apply ih q (by omega) hq0 ((i + 1) / 2)
      intro k hk
      rcases Nat.even_or_odd i with ⟨a, ha⟩ | ⟨a, ha⟩
      · have h1 := hc (2 * k) (by omega)
        have e1 : i + 2 * k = 2 * ((i + 1) / 2 + k) := by omega
        have e2 : i + 2 * k + p = 2 * ((i + 1) / 2 + k + q) := by omega
        rw [e2, e1, tm_even, tm_even] at h1
        exact h1
      · have h1 := hc (2 * k + 1) (by omega)
        have e1 : i + (2 * k + 1) = 2 * ((i + 1) / 2 + k) := by omega
        have e2 : i + (2 * k + 1) + p = 2 * ((i + 1) / 2 + k + q) := by omega
        rw [e2, e1, tm_even, tm_even] at h1
        exact h1
    · rcases Nat.eq_zero_or_pos q with rfl | hq1
      · -- period 1
        have h0 := hc 0 (by omega)
        have h1 := hc 1 (by omega)
        rcases Nat.even_or_odd i with ⟨a, ha⟩ | ⟨a, ha⟩
        · exact tm_pair i (by omega) (by simpa [hq] using h0)
        · exact tm_pair (i + 1) (by omega) (by simpa [hq, add_assoc] using h1)
      · -- odd period at least 3: alternation, then a cube of period 2
        have halt : ∀ m, i + p ≤ m → m + 2 ≤ i + 3 * p → tm m ≠ tm (m + 1) := by
          intro m hm1 hm2
          rcases Nat.even_or_odd m with ⟨c, hc'⟩ | ⟨c, hc'⟩
          · exact tm_pair m (by omega)
          · have hA := hc (m - p - i) (by omega)
            have hB := hc (m - p - i + 1) (by omega)
            have e1 : i + (m - p - i) = m - p := by omega
            have e2 : i + (m - p - i) + p = m := by omega
            have e3 : i + (m - p - i + 1) = m - p + 1 := by omega
            have e4 : i + (m - p - i + 1) + p = m + 1 := by omega
            rw [e2, e1] at hA
            rw [e4, e3] at hB
            rw [← hA, ← hB]
            exact tm_pair (m - p) (by omega)
        apply ih 2 (by omega) (by norm_num) (i + p)
        intro k hk
        have h1 := halt (i + p + k) (by omega) (by omega)
        have h2 := halt (i + p + k + 1) (by omega) (by omega)
        exact bool_trans h1 h2

/-- The letter `t j` as an element of `Fin 2`. -/
def letter (b : Bool) : Fin 2 := if b then 1 else 0

theorem letter_inj {a b : Bool} (h : letter a = letter b) : a = b := by
  cases a <;> cases b <;> simp_all [letter]

/-- The Thue–Morse prefix of length `n`. -/
def word (n : ℕ) : List (Fin 2) := (List.range n).map (fun j => letter (tm j))

theorem word_get (n j : ℕ) (hj : j < n) : (word n)[j]? = some (letter (tm j)) := by
  simp [word, hj]

end OMAProof.ThueMorse

open OMAProof.ThueMorse in
theorem OMA.solution : OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1_H1_R1.H1 := by
  intro n
  refine ⟨word n, by simp [word], ?_⟩
  intro l u r hu heq
  set i := l.length with hi
  set p := u.length with hp
  have hp0 : 0 < p := List.length_pos_iff.mpr hu
  have hlen : n = i + 3 * p + r.length := by
    have := congrArg List.length heq
    simp [word] at this
    omega
  -- positions inside the three copies of `u`
  have g1 : ∀ k < p, (l ++ u ++ u ++ u ++ r)[i + k]? = u[k]? := by
    intro k hk
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]
    congr 1
    omega
  have g2 : ∀ k < p, (l ++ u ++ u ++ u ++ r)[i + p + k]? = u[k]? := by
    intro k hk
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by simp; omega)]
    congr 1
    simp
    omega
  have g3 : ∀ k < p, (l ++ u ++ u ++ u ++ r)[i + 2 * p + k]? = u[k]? := by
    intro k hk
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    congr 1
    simp
    omega
  apply no_cube p hp0 i
  intro k hk
  have hshift : (l ++ u ++ u ++ u ++ r)[i + k]? = (l ++ u ++ u ++ u ++ r)[i + k + p]? := by
    rcases lt_or_ge k p with hkp | hkp
    · rw [g1 k hkp, show i + k + p = i + p + k by omega, g2 k hkp]
    · rw [show i + k + p = i + 2 * p + (k - p) by omega, g3 (k - p) (by omega),
        show i + k = i + p + (k - p) by omega, g2 (k - p) (by omega)]
  rw [← heq, word_get n _ (by omega), word_get n _ (by omega)] at hshift
  exact letter_inj (Option.some_injective _ hshift)
