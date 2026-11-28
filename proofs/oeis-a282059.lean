import OMAStatements.S_oeis_a282059
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-! OEIS A282059: for `k ≥ 1`, `[10 k, 10 k + 30]` holds at most `8` primes, and exactly `8` only
when `k ≡ 1` or `17 (mod 21)`.

Every prime `x` in the interval is at least `10`, so it is prime to `2, 3, 5, 7`. Write
`x = 10 k + j` with `j ≤ 30`. Since `210 ∣ 10 k - 10 (k % 21)`, the residues of `x` modulo
`2, 3, 5, 7` are those of `10 (k % 21) + j`. So the primes inject into the `j < 31` for which
`10 r + j` (with `r = k % 21`) survives the sieve by `2, 3, 5, 7`, and a direct check over the
`21` values of `r` shows there are at most `8` such `j`, with `8` only for `r = 1, 17`. -/

namespace OpenMath.A282059

open Finset OMA.S_oeis_a282059

/-- `j` survives the sieve by `2, 3, 5, 7` at offset `10 r`. -/
private abbrev Q (r j : ℕ) : Prop :=
  (10 * r + j) % 2 ≠ 0 ∧ (10 * r + j) % 3 ≠ 0 ∧ (10 * r + j) % 5 ≠ 0 ∧ (10 * r + j) % 7 ≠ 0

private theorem table (r : ℕ) (hr : r < 21) :
    ((range 31).filter (Q r)).card ≤ 8 ∧
      (8 ≤ ((range 31).filter (Q r)).card → r = 1 ∨ r = 17) := by
  interval_cases r <;> decide

private theorem prime_Q (k x : ℕ) (hk : 1 ≤ k) (h1 : 10 * k ≤ x) (h2 : x ≤ 10 * k + 30)
    (hp : x.Prime) : x - 10 * k ∈ (range 31).filter (Q (k % 21)) := by
  have key : ∀ q, 2 ≤ q → q ≤ 7 → x % q ≠ 0 := by
    intro q hq2 hq7 h
    rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
  have h2' := key 2 (by norm_num) (by norm_num)
  have h3' := key 3 (by norm_num) (by norm_num)
  have h5' := key 5 (by norm_num) (by norm_num)
  have h7' := key 7 (by norm_num) (by norm_num)
  rw [mem_filter, mem_range]
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem card_le (k : ℕ) (hk : 1 ≤ k) :
    countPrimes k ≤ ((range 31).filter (Q (k % 21))).card := by
  unfold countPrimes
  calc _ ≤ (((range 31).filter (Q (k % 21))).image (fun j => 10 * k + j)).card := by
        apply card_le_card
        intro x hx
        obtain ⟨hx1, hp⟩ := mem_filter.1 hx
        obtain ⟨h1, h2⟩ := mem_Icc.1 hx1
        rw [mem_image]
        exact ⟨x - 10 * k, prime_Q k x hk h1 h2 hp, by show 10 * k + (x - 10 * k) = x; omega⟩
    _ ≤ ((range 31).filter (Q (k % 21))).card := card_image_le

theorem main :
    (∀ k : ℕ, 1 ≤ k → countPrimes k ≤ 8) ∧
    (∀ k : ℕ, 1 ≤ k → countPrimes k = 8 → k % 21 = 1 ∨ k % 21 = 17) := by
  refine ⟨fun k hk => (card_le k hk).trans (table _ (Nat.mod_lt _ (by norm_num))).1,
    fun k hk h8 => (table _ (Nat.mod_lt _ (by norm_num))).2 ?_⟩
  rw [← h8]
  exact card_le k hk

end OpenMath.A282059

theorem OMA.solution : type_of% @OMA.S_oeis_a282059.main := OpenMath.A282059.main
