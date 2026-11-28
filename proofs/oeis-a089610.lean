import OMAStatements.S_oeis_a089610

-- Problem: A089610: Number of primes between n^2 and (n+1/2)^2.
-- Upstream: formal-conjectures statements/oeis-a089610.lean:0 (declaration OMA.S_oeis_a089610.main)
-- Credit: @julianibarz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset
lemma prime_count_bound (n : ℕ) (hn : 2 ≤ n) : OMA.S_oeis_a089610.a n ≤ n / 2 + 1 := by
  unfold OMA.S_oeis_a089610.a
  apply le_trans (Finset.card_le_card_of_injOn (s := (Finset.Ioc (n ^ 2) (n ^ 2 + n)).filter Nat.Prime) (t := Finset.range (n / 2 + 1)) (fun p => (p - n ^ 2) / 2) ?_ ?_) (by simp)
  · intro p hp
    simp only [Finset.mem_coe, mem_filter, mem_Ioc] at hp
    simp only [Finset.mem_coe, mem_range]
    omega
  · intro p hp q hq heq
    dsimp at heq
    simp only [Finset.mem_coe, mem_filter, mem_Ioc] at hp hq
    have hn2 : 2 < n ^ 2 := by nlinarith
    have hpodd := hp.2.eq_two_or_odd
    have hqodd := hq.2.eq_two_or_odd
    omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a089610.main) := by
  intro h
  obtain ⟨N, hN⟩ := h.2.1
  have growth : ∀ k : ℕ, k + OMA.S_oeis_a089610.a N ≤ OMA.S_oeis_a089610.a (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hN (N + k) (by omega)
      have heq : N + (k + 1) = N + k + 1 := by omega
      rw [heq]
      omega
  have lower := growth (N + 4)
  have upper := prime_count_bound (N + (N + 4)) (by omega)
  omega
