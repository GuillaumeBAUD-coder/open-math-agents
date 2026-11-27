import OMAReductions.R_OeisA182126_conjecture3_R1

-- Step OeisA182126.conjecture3.R1.H2
-- Credit: @caa1982

private def primes63 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307]

private lemma primes63_spec :
    ∀ k ∈ Finset.range 63,
      (primes63.getD k 0).Prime ∧ Nat.count Nat.Prime (primes63.getD k 0) = k := by
  decide +kernel

private lemma nth_prime_eq (k : ℕ) (hk : k < 63) :
    Nat.nth Nat.Prime k = primes63.getD k 0 := by
  obtain ⟨hp, hcnt⟩ := primes63_spec k (Finset.mem_range.mpr hk)
  calc Nat.nth Nat.Prime k
      = Nat.nth Nat.Prime (Nat.count Nat.Prime (primes63.getD k 0)) := by rw [hcnt]
    _ = primes63.getD k 0 := Nat.nth_count hp

private lemma check_a :
    ∀ n ∈ Finset.Icc 1 61,
      let v := (primes63.getD (n - 1) 0 * primes63.getD n 0) % primes63.getD (n + 1) 0
      v.Prime → v ∈ ([2, 7, 11, 13, 29] : List ℕ) := by
  decide +kernel

theorem OMA.solution : OMA.R_OeisA182126_conjecture3_R1.H2 := by
  intro n hn0 hn61 hprime
  have ha : OeisA182126.a n =
      (primes63.getD (n - 1) 0 * primes63.getD n 0) % primes63.getD (n + 1) 0 := by
    unfold OeisA182126.a OeisA182126.prime
    have hne : n ≠ 0 := by omega
    simp only [hne, ↓reduceIte, Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega]
    rw [nth_prime_eq (n - 1) (by omega), nth_prime_eq n (by omega), nth_prime_eq (n + 1) (by omega)]
  rw [ha] at hprime ⊢
  exact check_a n (Finset.mem_Icc.mpr ⟨hn0, hn61⟩) hprime
