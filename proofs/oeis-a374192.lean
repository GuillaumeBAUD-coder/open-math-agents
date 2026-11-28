import OMAStatements.S_oeis_a374192

open OMA.S_oeis_a374192

lemma OMA.a374192_contract (n : ℕ) (hn : 3 < n) :
    ∃ k, 0 < (step^[k]) n ∧ (step^[k]) n < n := by
  have halve (x : ℕ) (h : x % 2 = 0) : step x = x / 2 := by simp [step, h]
  have triple (x : ℕ) (h : x % 2 ≠ 0) (h' : x % 3 = 0) : step x = 3 * x + 1 := by
    simp [step, h, h']
  have incr (x : ℕ) (h : x % 2 ≠ 0) (h' : x % 3 ≠ 0) : step x = x + 1 := by
    simp [step, h, h']
  refine ⟨if n % 2 = 0 then 1 else if n % 3 = 0 then (if n % 4 = 1 then 3 else 4) else 2, ?_⟩
  split_ifs <;>
    simp (disch := omega) only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      halve, triple, incr] <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a374192.main := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : 3 < n
    · obtain ⟨k, hp, hl⟩ := OMA.a374192_contract n h
      obtain ⟨j, hj⟩ := ih _ hl hp
      exact ⟨j + k, by rwa [Function.iterate_add_apply]⟩
    · have hn' : n ≤ 3 := by omega
      refine ⟨if n = 1 then 0 else 1, ?_⟩
      interval_cases n <;> decide
