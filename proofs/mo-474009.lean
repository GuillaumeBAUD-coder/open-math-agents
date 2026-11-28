import OMAStatements.S_mo_474009
import Mathlib

-- Problem mo-474009: for an odd prime p and n > 1 there is no integer polynomial f with
-- f(x) = floor(x / p^(n-1)) mod p for all 0 <= x < p^n.
-- Upstream: statements/mo-474009.lean (declaration OMA.S_mo_474009.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: an integer polynomial satisfies f(y) = f(x) mod (y - x). Take y = p^(n-1) and x = p^(n-1) - p, both
-- below p^n, with y - x = p. Then floor(x / p^(n-1)) = 0 and floor(y / p^(n-1)) = 1, so 1 = f(y) = f(x) = 0
-- mod p, which is impossible.

theorem OMA.solution : type_of% @OMA.S_mo_474009.main := by
  intro p n hp _ hn
  rintro ⟨f, hf⟩
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : p ≤ p ^ (n - 1) := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : p ^ (n - 1) < p ^ n := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpos : 0 < p ^ (n - 1) := by omega
  have hx := hf (p ^ (n - 1) - p) (by omega)
  have hy := hf (p ^ (n - 1)) h2
  rw [Nat.div_eq_of_lt (by omega)] at hx
  rw [Nat.div_self hpos] at hy
  have hdvd : ((p ^ (n - 1) : ℕ) : ℤ) - ((p ^ (n - 1) - p : ℕ) : ℤ) ∣
      f.eval ((p ^ (n - 1) : ℕ) : ℤ) - f.eval ((p ^ (n - 1) - p : ℕ) : ℤ) :=
    Polynomial.sub_dvd_eval_sub _ _ f
  have hdiff : ((p ^ (n - 1) : ℕ) : ℤ) - ((p ^ (n - 1) - p : ℕ) : ℤ) = (p : ℤ) := by
    rw [Nat.cast_sub h1]
    ring
  rw [hdiff] at hdvd
  have h3 : f.eval ((p ^ (n - 1) : ℕ) : ℤ) ≡ f.eval ((p ^ (n - 1) - p : ℕ) : ℤ) [ZMOD (p : ℤ)] :=
    (Int.modEq_iff_dvd.mpr hdvd).symm
  have h4 : ((1 : ℕ) : ℤ) ≡ ((0 : ℕ) : ℤ) [ZMOD (p : ℤ)] := hy.symm.trans (h3.trans hx)
  have h5 : (p : ℤ) ∣ 1 := by
    have h := Int.modEq_iff_dvd.mp h4.symm
    simpa using h
  have h6 : p ∣ 1 := by exact_mod_cast h5
  have h7 := Nat.le_of_dvd (by norm_num) h6
  omega
