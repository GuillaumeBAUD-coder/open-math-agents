import FormalConjectures.Wikipedia.PerfectNumbers

-- Reduction PerfectNumbers.infinitely_many_even_perfect.R1 of the question whether there are infinitely many
-- even perfect numbers
-- Credit: @marcusbuffett

/-!
# Infinitely many even perfect numbers from infinitely many Mersenne primes

By the Euclid-Euler theorem the even perfect numbers are the numbers `2^(p-1) * (2^p - 1)` with
`2^p - 1` prime. Only Euclid's half is needed for infinitude.

* `H1` (open): there are infinitely many Mersenne primes. This is the catalogue statement
  `Mersenne.infinitely_many_mersenne_primes`.
* `H2` (Euclid, Elements IX.36): if `2^(k+1) - 1` is prime then `2^k * (2^(k+1) - 1)` is perfect.

`main` shows that `p ↦ 2^(p-1) * (2^p - 1)` is injective on the Mersenne exponents and takes even
perfect values there.
-/

namespace OMA.R_PerfectNumbers_infinitely_many_even_perfect_R1

/-- There are infinitely many Mersenne primes. -/
def H1 : Prop :=
  Set.Infinite {p : ℕ | (mersenne p).Prime}

/-- Euclid: a Mersenne prime gives a perfect number. -/
def H2 : Prop :=
  ∀ k : ℕ, (mersenne (k + 1)).Prime → Nat.Perfect (2 ^ k * mersenne (k + 1))

lemma two_le_of_prime {p : ℕ} (h : (mersenne p).Prime) : 2 ≤ p := by
  rcases p with _ | _ | p
  · norm_num [mersenne] at h
  · norm_num [mersenne] at h
  · omega

lemma strict {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q) :
    2 ^ (p - 1) * mersenne p < 2 ^ (q - 1) * mersenne q := by
  have h1 : 2 ^ (p - 1) ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ p < 2 ^ q := Nat.pow_lt_pow_right (by norm_num) hpq
  have h3 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have h4 : mersenne p < mersenne q := by
    unfold mersenne
    omega
  exact Nat.mul_lt_mul_of_le_of_lt h1 h4 (by positivity)

theorem main : H1 → H2 → type_of% @PerfectNumbers.infinitely_many_even_perfect := by
  intro hM hE
  have hinj : Set.InjOn (fun p : ℕ => 2 ^ (p - 1) * mersenne p) {p : ℕ | (mersenne p).Prime} := by
    intro p hp q hq h
    have hp2 := two_le_of_prime hp
    have hq2 := two_le_of_prime hq
    simp only at h
    rcases lt_trichotomy p q with h1 | h1 | h1
    · have := strict (by omega) h1
      omega
    · exact h1
    · have := strict (by omega) h1
      omega
  refine (hM.image hinj).mono ?_
  rintro n ⟨p, hp, rfl⟩
  have hp2 := two_le_of_prime hp
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  refine ⟨hE k hp, ?_⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨2 ^ j * mersenne (j + 1 + 1), by rw [pow_succ]; ring⟩

end OMA.R_PerfectNumbers_infinitely_many_even_perfect_R1
