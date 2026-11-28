import OMAStatements.S_oeis_a134492

-- Problem: A134492: a(n) = Fibonacci(6*n).
-- Upstream: statements/oeis-a134492.lean (declaration OMA.S_oeis_a134492.main)
-- Credit: @Coglizer
--
-- Disproof. The statement says that the Fibonacci numbers which are the sum of the three sides
-- of a Pythagorean triple are exactly F(6n), n >= 2. But
--   F(45) = 1134903170 = 344191945 + 320443248 + 470267977
-- and 344191945^2 + 320443248^2 = 470267977^2 (this is 109441 * (3145, 2928, 4297), the triple
-- with m = 61, n = 24), while 45 is not a multiple of 6.

namespace A134492

lemma fib45 : Nat.fib 45 = 1134903170 := by norm_num [Nat.fib_add_two]

lemma fib_inj {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (h : Nat.fib i = Nat.fib j) : i = j := by
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 2 := ⟨i - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 2 := ⟨j - 2, by omega⟩
  have := Nat.fib_add_two_strictMono.injective h
  omega

end A134492

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a134492.main) := by
  intro h
  have hmem : Nat.fib 45 ∈ {x : ℕ | (∃ j : ℕ, x = Nat.fib j) ∧
      OMA.S_oeis_a134492.IsPythagoreanSum x} := by
    refine ⟨⟨45, rfl⟩, 344191945, 320443248, 470267977, by norm_num, by norm_num, by norm_num,
      by norm_num, ?_⟩
    rw [A134492.fib45]
  rw [← h] at hmem
  obtain ⟨n, hn, he⟩ := hmem
  have := A134492.fib_inj (by omega) (by omega) he
  omega
