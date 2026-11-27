import FormalConjectures.OEIS.«7468»

-- Reduction OeisA7468.conjecture.R1 of Sum of next $n$ primes
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
`main` proves the witness direction outright: `a 38 = 207936 = 456 ^ 2`. The 38 primes
`p_704, ..., p_741` (5309 to 5641) are certified in the kernel: below `76 ^ 2 = 5776`, primality
is trial division by `d < 76`, proved equivalent to `Nat.Prime` through `Nat.prime_def_le_sqrt`.
`Nat.count` of that predicate is computed once up to 5309 (it is 703) and then on the window
5309 to 5641, using `Nat.count_add`.

The converse direction (only `n = 38` gives a square) is split into
* `H1`, a finite range: for `0 < n <= 100` a square value forces `n = 38` (checked numerically up
  to `n = 2000`; a computational step), and
* `H2`, the open tail: `a n` is never a square for `n > 100`.
-/

namespace OMA.R_OeisA7468_conjecture_R1

open OeisA7468

/-- Finite range: below 101, only `n = 38` gives a square. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → n ≤ 100 → IsSquare (a n) → n = 38

/-- The open tail: no square values beyond `n = 100`. -/
def H2 : Prop := ∀ n : ℕ, 100 < n → ¬ IsSquare (a n)

/-- Trial division below 76 decides primality below `76 ^ 2`. -/
lemma prime_iff_small (n : ℕ) (hn : n < 5776) :
    Nat.Prime n ↔ (2 ≤ n ∧ ∀ d ∈ List.range 76, 2 ≤ d → d * d ≤ n → n % d ≠ 0) := by
  rw [Nat.prime_def_le_sqrt]
  apply and_congr_right
  intro _
  constructor
  · intro H d _ hd hdd hmod
    exact H d hd (Nat.le_sqrt.mpr hdd) (Nat.dvd_of_mod_eq_zero hmod)
  · intro H m hm hms hdvd
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
    have hm76 : m < 76 := by
      by_contra hc
      push Not at hc
      have : 76 * 76 ≤ m * m := Nat.mul_le_mul hc hc
      omega
    exact H m (List.mem_range.mpr hm76) hm hmm (Nat.mod_eq_zero_of_dvd hdvd)

lemma count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (n : ℕ)
    (h : ∀ k < n, p k ↔ q k) : Nat.count p n = Nat.count q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  exact Finset.filter_congr fun k hk => h k (Finset.mem_range.mp hk)

lemma count_base :
    Nat.count (fun n => 2 ≤ n ∧ ∀ d ∈ List.range 76, 2 ≤ d → d * d ≤ n → n % d ≠ 0) 5309
      = 703 := by
  decide +kernel

lemma window :
    ∀ i ∈ List.range 38,
      (2 ≤ 5309 + ([0, 14, 24, 38, 42, 72, 78, 84, 90, 98, 104, 108, 110, 122, 128, 132, 134,
        140, 162, 168, 170, 174, 192, 194, 198, 210, 212, 218, 222, 248, 254, 260, 264, 272,
        282, 314, 330, 332].getD i 0) ∧
        ∀ d ∈ List.range 76, 2 ≤ d →
          d * d ≤ 5309 + ([0, 14, 24, 38, 42, 72, 78, 84, 90, 98, 104, 108, 110, 122, 128, 132,
            134, 140, 162, 168, 170, 174, 192, 194, 198, 210, 212, 218, 222, 248, 254, 260, 264,
            272, 282, 314, 330, 332].getD i 0) →
          (5309 + ([0, 14, 24, 38, 42, 72, 78, 84, 90, 98, 104, 108, 110, 122, 128, 132, 134,
            140, 162, 168, 170, 174, 192, 194, 198, 210, 212, 218, 222, 248, 254, 260, 264, 272,
            282, 314, 330, 332].getD i 0)) % d ≠ 0) ∧
      Nat.count (fun k => 2 ≤ 5309 + k ∧ ∀ d ∈ List.range 76, 2 ≤ d → d * d ≤ 5309 + k →
          (5309 + k) % d ≠ 0)
        ([0, 14, 24, 38, 42, 72, 78, 84, 90, 98, 104, 108, 110, 122, 128, 132, 134, 140, 162,
          168, 170, 174, 192, 194, 198, 210, 212, 218, 222, 248, 254, 260, 264, 272, 282, 314,
          330, 332].getD i 0) = i := by
  decide +kernel

lemma nth_prime_window (i : ℕ) (hi : i < 38) :
    Nat.nth Nat.Prime (703 + i) = 5309 + ([0, 14, 24, 38, 42, 72, 78, 84, 90, 98, 104, 108, 110,
      122, 128, 132, 134, 140, 162, 168, 170, 174, 192, 194, 198, 210, 212, 218, 222, 248, 254,
      260, 264, 272, 282, 314, 330, 332].getD i 0) := by
  obtain ⟨hpr, hcnt⟩ := window i (List.mem_range.mpr hi)
  set g := [0, 14, 24, 38, 42, 72, 78, 84, 90, 98, 104, 108, 110, 122, 128, 132, 134, 140, 162,
    168, 170, 174, 192, 194, 198, 210, 212, 218, 222, 248, 254, 260, 264, 272, 282, 314, 330,
    332].getD i 0 with hg
  have hg333 : g ≤ 332 := by
    rw [hg]
    interval_cases i <;> decide
  have hprime : Nat.Prime (5309 + g) := (prime_iff_small _ (by omega)).mpr hpr
  have hcount : Nat.count Nat.Prime (5309 + g) = 703 + i := by
    have e1 : Nat.count Nat.Prime 5309 = 703 :=
      (count_congr_lt _ fun k _ => prime_iff_small k (by omega)).trans count_base
    have e2 : Nat.count (fun k => Nat.Prime (5309 + k)) g = i :=
      (count_congr_lt _ fun k hk => prime_iff_small (5309 + k) (by omega)).trans hcnt
    rw [Nat.count_add, e1, e2]
  rw [← hcount]
  exact Nat.nth_count hprime

lemma a_38 : a 38 = 207936 := by
  have h703 : 38 * (38 - 1) / 2 = 703 := by norm_num
  simp only [a, h703]
  rw [Finset.sum_congr rfl fun i hi => nth_prime_window i (Finset.mem_range.mp hi)]
  decide +kernel

theorem main : H1 → H2 → type_of% @OeisA7468.conjecture := by
  intro h1 h2 n hn
  constructor
  · intro hsq
    by_cases hle : n ≤ 100
    · exact h1 n hn hle hsq
    · exact absurd hsq (h2 n (by omega))
  · rintro rfl
    rw [a_38]
    exact ⟨456, by norm_num⟩

end OMA.R_OeisA7468_conjecture_R1
