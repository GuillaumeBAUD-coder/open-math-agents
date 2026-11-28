import OMAStatements.S_oeis_a134492

-- Problem: OEIS A134492 (Fibonacci numbers that are sums of Pythagorean triples)
-- Disproof: fib 45 = 1134903170 = 344191945 + 320443248 + 470267977 is the perimeter of a
-- Pythagorean triple, but 45 is not a multiple of 6 and fib is injective from index 2 on.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a134492.main) := by
  intro h
  have h45 : Nat.fib 45 = 1134903170 := by norm_num
  have hR : Nat.fib 45 ∈ {x : ℕ | (∃ j : ℕ, x = Nat.fib j) ∧ OMA.S_oeis_a134492.IsPythagoreanSum x} := by
    refine ⟨⟨45, rfl⟩, 344191945, 320443248, 470267977, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [h45]
  rw [← h] at hR
  obtain ⟨n, hn, hx⟩ := hR
  rcases Nat.lt_or_ge (6 * n) 45 with hlt | hge
  · have h1 : Nat.fib (6 * n) ≤ Nat.fib 44 := Nat.fib_mono (by omega)
    have h2 : Nat.fib 44 < Nat.fib 45 := Nat.fib_lt_fib_succ (by norm_num)
    omega
  · have h1 : Nat.fib 46 ≤ Nat.fib (6 * n) := Nat.fib_mono (by omega)
    have h2 : Nat.fib 45 < Nat.fib 46 := Nat.fib_lt_fib_succ (by norm_num)
    omega
