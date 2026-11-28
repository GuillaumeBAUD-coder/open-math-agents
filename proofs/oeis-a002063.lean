import OMAStatements.S_oeis_a002063

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: strong induction on i. Even x halves both sides (i decreases by 2); odd x forces i = 0 and
-- x = 2y+1 with y(y+1) = 2^(j-2), so y = 1 and x = 3. Converse: i = 2n, j = 2n+3.

open OMA.S_oeis_a002063

namespace P_oeis_a002063

lemma consec_pow (y m : ℕ) (h : y * (y + 1) = 2 ^ m) : y = 1 := by
  have hy : y ∣ 2 ^ m := ⟨y + 1, h.symm⟩
  have hy1 : y + 1 ∣ 2 ^ m := ⟨y, by rw [← h]; ring⟩
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy1
  have hpos : 0 < 2 ^ m := by positivity
  rcases a with _ | a
  · simpa using ha
  rcases b with _ | b
  · simp at hb; subst hb; simp at h; omega
  rw [pow_succ] at ha hb
  omega

lemma fwd : ∀ i x j : ℕ, i < j → x ^ 2 = 2 ^ i + 2 ^ j → ∃ n : ℕ, x ^ 2 = 9 * 4 ^ n := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro x j hij hx
  rcases x.even_or_odd with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · -- x = y + y
    rcases i with _ | _ | i
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hx' : 2 * (2 * (y * y)) = 1 + 2 * 2 ^ j' := by
        rw [show 2 * (2 * (y * y)) = (y + y) ^ 2 by ring, hx]; ring
      omega
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have hx' : 4 * (y * y) = 2 + 4 * 2 ^ j' := by
        rw [show 4 * (y * y) = (y + y) ^ 2 by ring, hx]; ring
      omega
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have hy : y ^ 2 = 2 ^ i + 2 ^ j' := by
        have e1 : (y + y) ^ 2 = 4 * y ^ 2 := by ring
        have e2 : 2 ^ (i + 2) + 2 ^ (j' + 2) = 4 * (2 ^ i + 2 ^ j') := by ring
        rw [e1, e2] at hx
        omega
      obtain ⟨n, hn⟩ := ih i (by omega) y j' (by omega) hy
      exact ⟨n + 1, by rw [show (y + y) ^ 2 = 4 * y ^ 2 by ring, hn]; ring⟩
  · rcases i with _ | i
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rcases j' with _ | m
      · have : (2 * y + 1) ^ 2 = 4 * (y * y + y) + 1 := by ring
        simp at hx; omega
      · have e1 : (2 * y + 1) ^ 2 = 4 * (y * (y + 1)) + 1 := by ring
        have e2 : 2 ^ 0 + 2 ^ (m + 1 + 1) = 4 * 2 ^ m + 1 := by ring
        rw [e1, e2] at hx
        have h := consec_pow y m (by omega)
        subst h
        exact ⟨0, by norm_num⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hx' : 2 * (2 * (y * y + y)) + 1 = 2 * (2 ^ i + 2 ^ j') := by
        rw [show 2 * (2 * (y * y + y)) + 1 = (2 * y + 1) ^ 2 by ring, hx]; ring
      omega

theorem main_proved : ∀ x : ℕ,
    (∃ i j : ℕ, i < j ∧ x ^ 2 = 2 ^ i + 2 ^ j) ↔
      ∃ n : ℕ, x ^ 2 = 9 * 4 ^ n := by
  intro x
  constructor
  · rintro ⟨i, j, hij, hx⟩
    exact fwd i x j hij hx
  · rintro ⟨n, hn⟩
    refine ⟨2 * n, 2 * n + 3, by omega, ?_⟩
    rw [hn, pow_add, pow_mul]
    norm_num
    ring

end P_oeis_a002063

theorem OMA.solution : type_of% @OMA.S_oeis_a002063.main := P_oeis_a002063.main_proved
