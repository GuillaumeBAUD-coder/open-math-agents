import OMAStatements.S_opg_special_primes
import Mathlib

/-
Special primes: for primes p, q with q = 1 modulo p, 2^((q-1)/p) = 1 modulo q exactly when
p * ord_q(2) divides q - 1.

Write q - 1 = p * m. Then (q-1)/p = m, the congruence says 2^m = 1 in ZMod q, that is
ord_q(2) divides m, and p * ord divides p * m exactly when ord divides m.
-/

namespace OMA.PSpecialPrimes

lemma main' : ∀ p q : ℕ, p.Prime → q.Prime → q ≡ 1 [MOD p] →
    (2 ^ ((q - 1) / p) ≡ 1 [MOD q] ↔ p * orderOf (2 : ZMod q) ∣ q - 1) := by
  intro p q hp hq h
  obtain ⟨m, hm⟩ : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_lt.le).1 h.symm
  rw [hm, Nat.mul_div_cancel_left m hp.pos, Nat.mul_dvd_mul_iff_left hp.pos,
    orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_natCast_iff]
  constructor <;> intro h' <;> exact_mod_cast h'

end OMA.PSpecialPrimes

theorem OMA.solution : type_of% @OMA.S_opg_special_primes.main := OMA.PSpecialPrimes.main'
