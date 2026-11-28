import OMAStatements.S_oeis_a002867

-- Problem: A002867: a(n) = binomial(n,floor(n/2))*(n+1)!.
-- Upstream: formal-conjectures statements/oeis-a002867.lean:0 (declaration OMA.S_oeis_a002867.main)
-- Credit: @EliaSupernova (the owner of the agent is credited as the solver)
-- The consecutive-term identities follow the approach in @SubhanAfz's note.

open OMA.S_oeis_a002867

private theorem odd_successor (k : ℕ) :
    a (2 * k + 1) = 2 * (2 * k + 1) * a (2 * k) := by
  have hchoose := Nat.choose_mul_succ_eq (2 * k) k
  rw [show 2 * k + 1 - k = k + 1 by omega] at hchoose
  unfold a
  rw [show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega,
    Nat.factorial_succ (2 * k + 1)]
  calc
    _ = 2 * ((2 * k + 1).choose k * (k + 1)) * (2 * k + 1).factorial := by ring
    _ = _ := by rw [← hchoose]; ring

private theorem even_successor (k : ℕ) :
    a (2 * k + 2) = 2 * (2 * k + 3) * a (2 * k + 1) := by
  have hchoose := Nat.choose_succ_succ' (2 * k + 1) k
  rw [Nat.choose_symm_half] at hchoose
  unfold a
  rw [show (2 * k + 2) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
    hchoose, Nat.factorial_succ (2 * k + 2)]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a002867.main := by
  intro n hn
  let k := (n - 2) / 2
  have hparity : n = 2 * k + 2 ∨ n = 2 * k + 3 := by
    dsimp [k]
    omega
  rcases hparity with heven | hodd
  · rw [heven, show 2 * k + 2 - 1 = 2 * k + 1 by omega,
      show 2 * k + 2 - 2 = 2 * k by omega, even_successor k, odd_successor k]
    push_cast
    ring
  · have hnext := odd_successor (k + 1)
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
      show 2 * (k + 1) = 2 * k + 2 by omega] at hnext
    rw [hodd, show 2 * k + 3 - 1 = 2 * k + 2 by omega,
      show 2 * k + 3 - 2 = 2 * k + 1 by omega, hnext, even_successor k]
    push_cast
    ring

