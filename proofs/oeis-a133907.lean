import OMAStatements.S_oeis_a133907
import Mathlib

/-!
# Proof for OEIS A133907, conjecture of Thomas Ordowski (Jul 29 2018)

`a(n)` is the least prime `p` with `binomial(n+p, p) mod p = 1`. Claimed: `a(n)` is the smallest prime
`p` with `Sum_{k=1..n} k^(p-1) == n (mod p)`, and therefore `a(n) >= A317358(n)`.

For a fixed prime `p` both conditions are equivalent to `p ∣ floor(n/p)`:

* Lucas: `binomial(n+p, p) == binomial(n mod p, 0) * binomial(floor(n/p) + 1, 1) = floor(n/p) + 1 (mod p)`;
* Fermat: `j^(p-1)` is `1` modulo `p` when `p` does not divide `j` and `0` otherwise, so
  `Sum_{j=1..n} j^(p-1) + floor(n/p) == n (mod p)` (induction on `n`).

Hence the two sets of primes are equal. The set is not empty (a prime `p > n` has `floor(n/p) = 0`),
so its infimum `a(n)` is its least element, which is the first claim. The second claim follows because
`a(n)` is then a number `k > 1` with `1^(k-1) + ... + n^(k-1) == n (mod k)`.
-/

/-- Lucas for the lower index `p`: `C(n+p, p) == floor(n/p) + 1 (mod p)`. -/
private theorem choose_add_self_modEq (p n : ℕ) (hp : p.Prime) :
    (n + p).choose p ≡ n / p + 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (n + p) p p _
  rw [Nat.add_mod_right, Nat.add_div_right n hp.pos, Nat.mod_self, Nat.div_self hp.pos,
    Nat.choose_zero_right, Nat.choose_one_right, one_mul] at h
  exact h

/-- `C(n+p, p) mod p = 1` exactly when `p` divides `floor(n/p)`. -/
private theorem choose_cond_iff (p n : ℕ) (hp : p.Prime) :
    (n + p).choose p % p = 1 ↔ p ∣ n / p := by
  have h := choose_add_self_modEq p n hp
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
  constructor
  · intro h2
    have h3 : n / p + 1 ≡ 0 + 1 [MOD p] := by
      have h4 : (n / p + 1) % p = (0 + 1) % p := by
        rw [← h, h2, zero_add, h1]
      exact h4
    exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 1 h3)
  · intro h2
    have h3 : n / p + 1 ≡ 0 + 1 [MOD p] := (Nat.modEq_zero_iff_dvd.mpr h2).add_right 1
    have h4 : (n + p).choose p % p = (0 + 1) % p := h.trans h3
    rw [h4, zero_add, h1]

/-- Fermat, summed: `Sum_{j=1..n} j^(p-1) + floor(n/p) = n` in `ZMod p`. -/
private theorem powerSum_zmod (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (j : ZMod p) ^ (p - 1)) + ((n / p : ℕ) : ZMod p) = (n : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.succ_div]
    by_cases h : p ∣ n + 1
    · have h0 : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      have hx : ((n + 1 : ℕ) : ZMod p) ^ (p - 1) = 0 := by
        rw [h0, zero_pow]
        have := hp.two_le
        omega
      rw [if_pos h, hx]
      push_cast
      linear_combination ih
    · have h0 : ((n + 1 : ℕ) : ZMod p) ≠ 0 := fun h' => h ((ZMod.natCast_eq_zero_iff _ _).mp h')
      have hx : ((n + 1 : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h0
      rw [if_neg h, hx]
      push_cast
      linear_combination ih

/-- `Sum_{j=1..n} j^(p-1) == n (mod p)` exactly when `p` divides `floor(n/p)`. -/
private theorem sum_cond_iff (p n : ℕ) (hp : p.Prime) :
    OMA.S_oeis_a133907.powerSum n p ≡ (n : ℤ) [ZMOD (p : ℤ)] ↔ p ∣ n / p := by
  have h := powerSum_zmod p hp n
  have hc : ((OMA.S_oeis_a133907.powerSum n p : ℤ) : ZMod p)
      = ∑ j ∈ Finset.Icc 1 n, (j : ZMod p) ^ (p - 1) := by
    unfold OMA.S_oeis_a133907.powerSum
    push_cast
    rfl
  rw [← ZMod.intCast_eq_intCast_iff, hc, ← ZMod.natCast_eq_zero_iff, Int.cast_natCast]
  constructor
  · intro h2
    rw [h2] at h
    exact add_eq_left.mp h
  · intro h2
    rw [h2, add_zero] at h
    exact h

/-- For a prime `p`, the condition of the name line and the condition of the conjecture agree. -/
private theorem cond_iff (p n : ℕ) (hp : p.Prime) :
    OMA.S_oeis_a133907.powerSum n p ≡ (n : ℤ) [ZMOD (p : ℤ)] ↔ (n + p).choose p % p = 1 :=
  (sum_cond_iff p n hp).trans (choose_cond_iff p n hp).symm

theorem OMA.solution : type_of% @OMA.S_oeis_a133907.main := by
  intro n _
  have hset : {p : ℕ | p.Prime ∧ OMA.S_oeis_a133907.powerSum n p ≡ (n : ℤ) [ZMOD (p : ℤ)]}
      = {p : ℕ | p.Prime ∧ (n + p).choose p % p = 1} := by
    ext p
    constructor
    · rintro ⟨hp, h⟩
      exact ⟨hp, (cond_iff p n hp).mp h⟩
    · rintro ⟨hp, h⟩
      exact ⟨hp, (cond_iff p n hp).mpr h⟩
  have hne : {p : ℕ | p.Prime ∧ (n + p).choose p % p = 1}.Nonempty := by
    obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n + 1)
    refine ⟨p, hp, (choose_cond_iff p n hp).mpr ?_⟩
    rw [Nat.div_eq_of_lt (by omega)]
    exact dvd_zero p
  have hleast : IsLeast {p : ℕ | p.Prime ∧ (n + p).choose p % p = 1}
      (OMA.S_oeis_a133907.a n) :=
    ⟨Nat.sInf_mem hne, fun q hq => Nat.sInf_le hq⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact hleast
  · have hmem := hleast.1
    exact Nat.sInf_le ⟨hmem.1.one_lt, (cond_iff _ n hmem.1).mpr hmem.2⟩
