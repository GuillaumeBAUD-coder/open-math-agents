import OMAReductions.R_FibonacciPrimes_fib_primes_infinite_R1

/-! The set of Fibonacci primes is the image under `Nat.fib` of the set of indices `n` with
`fib n` prime. `fib n` is prime only for `n ≥ 2`, and `fib` is strictly increasing there
(`Nat.fib_add_two_strictMono`). So `fib` is injective on that set, and the image is infinite
exactly when the set is (`Set.infinite_image_iff`). -/

theorem OMA.solution : OMA.R_FibonacciPrimes_fib_primes_infinite_R1.H2 := by
  have hT : {n : ℕ | (∃ m : ℕ, m.fib = n) ∧ n.Prime} = Nat.fib '' {n : ℕ | n.fib.Prime} := by
    ext p
    constructor
    · rintro ⟨⟨m, rfl⟩, hp⟩
      exact ⟨m, hp, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, rfl⟩, hm⟩
  have two_le : ∀ a : ℕ, (Nat.fib a).Prime → 2 ≤ a := by
    intro a ha
    by_contra h
    push Not at h
    interval_cases a <;> simp at ha
  have hinj : Set.InjOn Nat.fib {n : ℕ | n.fib.Prime} := by
    intro a ha b hb hab
    have ha2 := two_le a ha
    have hb2 := two_le b hb
    have h := Nat.fib_add_two_strictMono.injective
      (show Nat.fib (a - 2 + 2) = Nat.fib (b - 2 + 2) by
        rw [Nat.sub_add_cancel ha2, Nat.sub_add_cancel hb2]
        exact hab)
    omega
  unfold OMA.R_FibonacciPrimes_fib_primes_infinite_R1.H2
  rw [hT]
  exact (Set.infinite_image_iff hinj).symm
