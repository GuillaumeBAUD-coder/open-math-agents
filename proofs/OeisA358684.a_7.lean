import FormalConjectures.OEIS.«358684»
import Mathlib.NumberTheory.LucasPrimality

namespace OMA

def pm (a m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f+1, e => (if e % 2 = 1 then a else 1) * pm a m f (e/2) ^ 2 % m

theorem pm_eq (a m : ℕ) : ∀ f e, e < 2^f → pm a m f e ≡ a^e [MOD m]
  | 0, e, h => by
    obtain rfl : e = 0 := by simpa using h
    rfl
  | f+1, e, h => by
    have ih := pm_eq a m f (e/2) (by rw [pow_succ] at h; omega)
    have hx : (if e % 2 = 1 then a else 1) ≡ a^(e%2) [MOD m] := by
      rcases Nat.mod_two_eq_zero_or_one e with h | h <;> simp [h] <;> rfl
    rw [show a^e = a^(e%2) * (a^(e/2))^2 by rw [← pow_mul, ← pow_add]; congr 1; omega]
    exact (Nat.mod_modEq _ _).trans (hx.mul (ih.pow 2))

theorem L (p a : ℕ) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime)
    (h : 1 < p ∧ p < 2^99 ∧ l.prod ^ 99 % (p-1) = 0 ∧ pm a p 99 (p-1) = 1 ∧
      l.all (fun q => pm a p 99 ((p-1)/q) ≠ 1) := by decide +kernel) : p.Prime := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have k (e) (he : e ≤ p - 1) : (a : ZMod p)^e = 1 ↔ pm a p 99 e = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', ← pm_eq a p 99 e (by omega),
      Nat.one_mod_eq_one.mpr (by omega), show pm a p 99 e % p = pm a p 99 e from Nat.mod_mod _ _]
  refine lucas_primality p a ((k _ le_rfl).mpr h3) fun q hq hd => ?_
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp
    (hq.dvd_of_dvd_pow (hd.trans (Nat.dvd_of_mod_eq_zero h2)))
  rw [(Nat.prime_dvd_prime_iff_eq hq (hl r hr)).mp hqr, Ne, k _ (Nat.div_le_self _ _)]
  simpa using List.all_eq_true.mp h4 r hr

lemma prime_18533742247 : Nat.Prime 18533742247 := L _ 6 [2,3,181,1896229] (by norm_num)
lemma prime_116503103764643 : Nat.Prime 116503103764643 :=
  L _ 2 [2,7,449,18533742247] (by simp [prime_18533742247]; norm_num)
lemma prime_59649589127497217 : Nat.Prime 59649589127497217 :=
  L _ 3 [2,116503103764643] (by simp [prime_116503103764643]; norm_num)
lemma prime_733803839347 : Nat.Prime 733803839347 := L _ 2 [2,3,2203,55515497] (by norm_num)
lemma prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 :=
  L _ 21 [2,3,5,12497,733803839347] (by simp [prime_733803839347]; norm_num)

end OMA

theorem OMA.solution : type_of% @OeisA358684.a_7 := by
  let n := Nat.fermatNumber 7
  have hprod : n = 59649589127497217 * 5704689200685129054721 := by decide
  have hprime : n.minFac.Prime := Nat.minFac_prime (by rw [hprod]; decide)
  have hd := Nat.minFac_dvd n
  have hle : n.minFac ≤ 59649589127497217 := Nat.minFac_le_of_dvd (by decide) (by rw [hprod]; exact dvd_mul_right _ _)
  rw [hprod] at hd
  have heq : n.minFac = 59649589127497217 := by
    rcases hprime.dvd_mul.mp hd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hprime OMA.prime_59649589127497217).mp h
    · have := (Nat.prime_dvd_prime_iff_eq hprime OMA.prime_5704689200685129054721).mp h
      omega
  change 2 ^ 7 - Nat.log2 n.minFac = 73
  rw [heq]
  decide
