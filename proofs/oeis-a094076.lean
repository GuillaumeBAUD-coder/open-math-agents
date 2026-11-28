import OMAStatements.S_oeis_a094076
import Mathlib.Tactic

-- Problem: A094076: is p + 2^k prime for some k, for every prime p?
-- Upstream: formal-conjectures statements/oeis-a094076.lean
-- Credit: @LordDavidDev (the owner of the agent is credited as the solver)
--
-- The conjecture is false: p = 271129 is a counterexample, recorded in the OEIS entry
-- (Bruno Mishutka, Mar 11 2009). For every k, 271129 + 2^k is divisible by one of
-- 3, 5, 7, 13, 17, 241 according to the residue of k modulo 24:
--   k odd            -> 3      (271129 = 1 mod 3, 2^k = 2 mod 3)
--   k = 0 mod 4      -> 5      (271129 = 4 mod 5, 2^k = 1 mod 5)
--   k = 2 mod 8      -> 17     (271129 = 13 mod 17, 2^k = 4 mod 17)
--   k = 6 mod 24     -> 13     (271129 = 1 mod 13, 2^k = -1 mod 13)
--   k = 14 mod 24    -> 241    (271129 = 4 mod 241, 2^k = -4 mod 241)
--   k = 22 mod 24    -> 7      (271129 = 5 mod 7, 2^k = 2 mod 7)
-- These six classes cover all residues modulo 24, and each of 3, 5, 7, 13, 17, 241 divides
-- 2^24 - 1, so the divisor only depends on k mod 24. Each quotient is at least
-- (271129 + 1) / 241 > 1, so 271129 + 2^k is never prime.

/-- The divisor attached to the residue of `k` modulo 24 covers every residue class. -/
private lemma covering :
    ∀ r : Fin 24, ∃ d ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ),
      ((271129 + 2 ^ (r : ℕ) : ℕ) : ZMod d) = 0 ∧ (2 : ZMod d) ^ 24 = 1 := by
  decide

/-- If `2 ^ 24 = 1` in `ZMod d` and `d` divides `271129 + 2 ^ (k % 24)`, then `d` divides
`271129 + 2 ^ k`. -/
private lemma shift_eq {d : ℕ} [NeZero d] (hd : (2 : ZMod d) ^ 24 = 1) (k : ℕ)
    (h : ((271129 + 2 ^ (k % 24) : ℕ) : ZMod d) = 0) :
    ((271129 + 2 ^ k : ℕ) : ZMod d) = 0 := by
  have hk24 : k = 24 * (k / 24) + k % 24 := (Nat.div_add_mod k 24).symm
  have h2 : (2 : ZMod d) ^ k = (2 : ZMod d) ^ (k % 24) := by
    conv_lhs => rw [hk24]
    rw [pow_add, pow_mul, hd, one_pow, one_mul]
  have hcast : ((271129 + 2 ^ k : ℕ) : ZMod d) = (271129 : ZMod d) + (2 : ZMod d) ^ k := by
    push_cast
    ring
  have hcastr : ((271129 + 2 ^ (k % 24) : ℕ) : ZMod d)
      = (271129 : ZMod d) + (2 : ZMod d) ^ (k % 24) := by
    push_cast
    ring
  rw [hcast, h2, ← hcastr]
  exact h

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a094076.main) := by
  intro h
  obtain ⟨k, hk⟩ := h 271129 (by norm_num)
  obtain ⟨d, hdmem, hdz, hd24⟩ := covering ⟨k % 24, Nat.mod_lt _ (by norm_num)⟩
  have hdpos : 0 < d := by
    have hall : ∀ e ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), 0 < e := by decide
    exact hall d hdmem
  haveI : NeZero d := ⟨hdpos.ne'⟩
  have hzero : ((271129 + 2 ^ k : ℕ) : ZMod d) = 0 := shift_eq hd24 k hdz
  have hdvd : d ∣ 271129 + 2 ^ k := (ZMod.natCast_eq_zero_iff _ d).mp hzero
  have hd1 : 1 < d := by
    have hall : ∀ e ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), 1 < e := by decide
    exact hall d hdmem
  have hdle : d ≤ 241 := by
    have hall : ∀ e ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), e ≤ 241 := by decide
    exact hall d hdmem
  have hbig : 241 < 271129 + 2 ^ k := by
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
    omega
  rcases hk.eq_one_or_self_of_dvd d hdvd with h1 | h1 <;> omega
