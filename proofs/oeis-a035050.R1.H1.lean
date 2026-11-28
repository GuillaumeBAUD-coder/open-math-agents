import OMAReductions.R_oeis_a035050_R1
import Mathlib

namespace DyadicPrimeWitnesses

private def modularPower (m a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | k + 1, e =>
    let r := modularPower m a k (e / 2)
    ((if e % 2 = 0 then 1 else a) * r * r) % m

private theorem modularPower_lt (m a k e : ℕ) (hm : 0 < m) :
    modularPower m a k e < m := by
  cases k <;> exact Nat.mod_lt _ hm

private theorem modularPower_cast (m a k e : ℕ) (he : e < 2 ^ k) :
    (modularPower m a k e : ZMod m) = (a : ZMod m) ^ e := by
  induction k generalizing e with
  | zero =>
    have ez : e = 0 := by simpa using he
    subst e
    simp [modularPower, ZMod.natCast_mod]
  | succ k ih =>
    have half : e / 2 < 2 ^ k := by
      rw [pow_succ] at he
      omega
    have eq := ih (e / 2) half
    by_cases hz : e % 2 = 0
    · simp only [modularPower, if_pos hz, one_mul, ZMod.natCast_mod, Nat.cast_mul, eq]
      rw [← pow_add]
      congr 1
      omega
    · simp only [modularPower, if_neg hz, ZMod.natCast_mod, Nat.cast_mul, eq]
      calc
        _ = (a : ZMod m) ^ (1 + e / 2 + e / 2) := by simp only [pow_add, pow_one]
        _ = _ := by congr 1; omega

private theorem prime_mem_of_dvd_product (p : ℕ) (hp : p.Prime) (l : List ℕ)
    (h : ∀ x ∈ l, Nat.Prime x) (hd : p ∣ l.prod) : p ∈ l := by
  induction l with
  | nil =>
    exact False.elim (hp.ne_one (Nat.dvd_one.mp hd))
  | cons x l ih =>
    rw [List.prod_cons, hp.dvd_mul] at hd
    rcases hd with hd | hd
    · exact List.mem_cons.mpr
        (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (h x (by simp))).mp hd))
    · exact List.mem_cons_of_mem _ (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hd)

private inductive Certificate
  | small (p : ℕ)
  | branch (p a : ℕ) (factors : List Certificate)

private def value : Certificate → ℕ
  | .small p => p
  | .branch p _ _ => p

private def verified : ℕ → Certificate → Bool
  | _, .small p => decide p.Prime
  | 0, .branch _ _ _ => false
  | k + 1, .branch p a factors =>
    decide (1 < p) &&
      (decide (p - 1 < 2 ^ 48) &&
        (decide ((factors.map value).prod = p - 1) &&
          ((factors.all fun c => verified k c &&
              decide (modularPower p a 48 ((p - 1) / value c) ≠ 1)) &&
            decide (modularPower p a 48 (p - 1) = 1))))

set_option maxHeartbeats 2000000 in
private theorem verified_prime (k : ℕ) (c : Certificate) (h : verified k c = true) :
    (value c).Prime := by
  induction k generalizing c with
  | zero =>
    cases c with
    | small p => exact of_decide_eq_true h
    | branch p a factors => cases h
  | succ k ih =>
    cases c with
    | small p => exact of_decide_eq_true h
    | branch p a factors =>
      simp only [verified, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hp, bound, product, factorsOk, powOne⟩ := h
      have allPrimes : ∀ q ∈ factors.map value, Nat.Prime q := by
        intro q hq
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
        exact ih c (Bool.and_eq_true_iff.mp (List.all_eq_true.mp factorsOk c hc)).1
      apply lucas_primality p (a : ZMod p)
      · rw [← modularPower_cast p a 48 (p - 1) bound, powOne, Nat.cast_one]
      · intro q hq hd hone
        rw [← product] at hd
        have found := prime_mem_of_dvd_product q hq (factors.map value) allPrimes hd
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp found
        have hneq := of_decide_eq_true
          ((Bool.and_eq_true_iff.mp (List.all_eq_true.mp factorsOk c hc)).2)
        let e := (p - 1) / value c
        have eBound : e < 2 ^ 48 := (Nat.div_le_self _ _).trans_lt bound
        have hcast : (modularPower p a 48 e : ZMod p) = (1 : ℕ) := by
          rw [modularPower_cast p a 48 e eBound, hone, Nat.cast_one]
        have modEq := (ZMod.natCast_eq_natCast_iff (modularPower p a 48 e) 1 p).mp hcast
        change modularPower p a 48 e % p = 1 % p at modEq
        rw [Nat.mod_eq_of_lt (modularPower_lt p a 48 e (by omega)), Nat.mod_eq_of_lt hp] at modEq
        exact hneq modEq

private def Witness (n : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ k < 2 ^ n ∧ Nat.Prime (k * 2 ^ n + 1)

private theorem witness1 : Witness 1 := by
  refine ⟨1, by decide, by decide, ?_⟩
  exact verified_prime 8 (.small 3) (by decide +kernel)

private theorem witness2 : Witness 2 := by
  refine ⟨1, by decide, by decide, ?_⟩
  exact verified_prime 8 (.small 5) (by decide +kernel)

private theorem witness3 : Witness 3 := by
  refine ⟨2, by decide, by decide, ?_⟩
  exact verified_prime 8 (.small 17) (by decide +kernel)

private theorem witness4 : Witness 4 := by
  refine ⟨1, by decide, by decide, ?_⟩
  exact verified_prime 8 (.small 17) (by decide +kernel)

private theorem witness5 : Witness 5 := by
  refine ⟨3, by decide, by decide, ?_⟩
  exact verified_prime 8 (.small 97) (by decide +kernel)

private theorem witness6 : Witness 6 := by
  refine ⟨3, by decide, by decide, ?_⟩
  exact verified_prime 8 (.small 193) (by decide +kernel)

private theorem witness7 : Witness 7 := by
  refine ⟨2, by decide, by decide, ?_⟩
  exact verified_prime 8 (.small 257) (by decide +kernel)

private theorem witness8 : Witness 8 := by
  refine ⟨1, by decide, by decide, ?_⟩
  exact verified_prime 8 (.small 257) (by decide +kernel)

private theorem witness9 : Witness 9 := by
  refine ⟨15, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 7681 17 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3, .small 5]) (by decide +kernel)

private theorem witness10 : Witness 10 := by
  refine ⟨12, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 12289 11 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3]) (by decide +kernel)

private theorem witness11 : Witness 11 := by
  refine ⟨6, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 12289 11 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3]) (by decide +kernel)

private theorem witness12 : Witness 12 := by
  refine ⟨3, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 12289 11 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3]) (by decide +kernel)

private theorem witness13 : Witness 13 := by
  refine ⟨5, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 40961 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 5]) (by decide +kernel)

private theorem witness14 : Witness 14 := by
  refine ⟨4, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 65537 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2]) (by decide +kernel)

private theorem witness15 : Witness 15 := by
  refine ⟨2, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 65537 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2]) (by decide +kernel)

private theorem witness16 : Witness 16 := by
  refine ⟨1, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 65537 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2]) (by decide +kernel)

private theorem witness17 : Witness 17 := by
  refine ⟨6, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 786433 10 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3]) (by decide +kernel)

private theorem witness18 : Witness 18 := by
  refine ⟨3, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 786433 10 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3]) (by decide +kernel)

private theorem witness19 : Witness 19 := by
  refine ⟨11, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 5767169 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 11]) (by decide +kernel)

private theorem witness20 : Witness 20 := by
  refine ⟨7, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 7340033 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 7]) (by decide +kernel)

private theorem witness21 : Witness 21 := by
  refine ⟨11, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 23068673 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 11]) (by decide +kernel)

private theorem witness22 : Witness 22 := by
  refine ⟨25, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 104857601 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 5, .small 5]) (by decide +kernel)

private theorem witness23 : Witness 23 := by
  refine ⟨20, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 167772161 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 5]) (by decide +kernel)

private theorem witness24 : Witness 24 := by
  refine ⟨10, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 167772161 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 5]) (by decide +kernel)

private theorem witness25 : Witness 25 := by
  refine ⟨5, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 167772161 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 5]) (by decide +kernel)

private theorem witness26 : Witness 26 := by
  refine ⟨7, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 469762049 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 7]) (by decide +kernel)

private theorem witness27 : Witness 27 := by
  refine ⟨15, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 2013265921 31 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3, .small 5]) (by decide +kernel)

private theorem witness28 : Witness 28 := by
  refine ⟨12, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 3221225473 5 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3]) (by decide +kernel)

private theorem witness29 : Witness 29 := by
  refine ⟨6, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 3221225473 5 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3]) (by decide +kernel)

private theorem witness30 : Witness 30 := by
  refine ⟨3, by decide, by decide, ?_⟩
  exact verified_prime 8 (.branch 3221225473 5 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 3]) (by decide +kernel)

theorem result : OMA.R_oeis_a035050_R1.H1 := by
  intro n lo hi
  interval_cases n
  · exact witness1
  · exact witness2
  · exact witness3
  · exact witness4
  · exact witness5
  · exact witness6
  · exact witness7
  · exact witness8
  · exact witness9
  · exact witness10
  · exact witness11
  · exact witness12
  · exact witness13
  · exact witness14
  · exact witness15
  · exact witness16
  · exact witness17
  · exact witness18
  · exact witness19
  · exact witness20
  · exact witness21
  · exact witness22
  · exact witness23
  · exact witness24
  · exact witness25
  · exact witness26
  · exact witness27
  · exact witness28
  · exact witness29
  · exact witness30

end DyadicPrimeWitnesses

theorem OMA.solution : OMA.R_oeis_a035050_R1.H1 :=
  DyadicPrimeWitnesses.result