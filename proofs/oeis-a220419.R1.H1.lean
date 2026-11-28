import OMAReductions.R_oeis_a220419_R1
import Mathlib

namespace PrimeCubicSums

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
      (decide (p - 1 < 2 ^ 32) &&
        (decide ((factors.map value).prod = p - 1) &&
          ((factors.all fun c => verified k c &&
              decide (modularPower p a 32 ((p - 1) / value c) ≠ 1)) &&
            decide (modularPower p a 32 (p - 1) = 1))))

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
      · rw [← modularPower_cast p a 32 (p - 1) bound, powOne, Nat.cast_one]
      · intro q hq hd hone
        rw [← product] at hd
        have found := prime_mem_of_dvd_product q hq (factors.map value) allPrimes hd
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp found
        have hneq := of_decide_eq_true
          ((Bool.and_eq_true_iff.mp (List.all_eq_true.mp factorsOk c hc)).2)
        let e := (p - 1) / value c
        have eBound : e < 2 ^ 32 := (Nat.div_le_self _ _).trans_lt bound
        have hcast : (modularPower p a 32 e : ZMod p) = (1 : ℕ) := by
          rw [modularPower_cast p a 32 e eBound, hone, Nat.cast_one]
        have modEq := (ZMod.natCast_eq_natCast_iff (modularPower p a 32 e) 1 p).mp hcast
        change modularPower p a 32 e % p = 1 % p at modEq
        rw [Nat.mod_eq_of_lt (modularPower_lt p a 32 e (by omega)), Nat.mod_eq_of_lt hp] at modEq
        exact hneq modEq

private def Witness (n : ℕ) : Prop :=
  ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime (2 * x + 1) ∧
    Nat.Prime (2 * y - 1) ∧ Nat.Prime (x ^ 3 + 2 * y ^ 3)

private theorem witness528 : Witness 528 := by
  refine ⟨299, 229, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 50748877 5 [.small 2, .small 2, .small 3, .small 3, .small 3, .small 17, .small 131, .small 211]) (by decide +kernel)

private theorem witness529 : Witness 529 := by
  refine ⟨219, 310, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 70085459 2 [.small 2, .small 17, .small 127, .branch 16231 3 [.small 2, .small 3, .small 5, .small 541]]) (by decide +kernel)

private theorem witness530 : Witness 530 := by
  refine ⟨131, 399, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 129290489 3 [.small 2, .small 2, .small 2, .branch 16161311 11 [.small 2, .small 5, .small 11, .branch 146921 3 [.small 2, .small 2, .small 2, .small 5, .branch 3673 5 [.small 2, .small 2, .small 2, .small 3, .small 3, .small 3, .small 17]]]]) (by decide +kernel)

private theorem witness531 : Witness 531 := by
  refine ⟨11, 520, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 281217331 12 [.small 2, .small 3, .small 3, .small 5, .small 101, .branch 30937 15 [.small 2, .small 2, .small 2, .small 3, .branch 1289 6 [.small 2, .small 2, .small 2, .small 7, .small 23]]]) (by decide +kernel)

private theorem witness532 : Witness 532 := by
  refine ⟨261, 271, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 57584603 2 [.small 2, .small 89, .branch 323509 11 [.small 2, .small 2, .small 3, .branch 26959 6 [.small 2, .small 3, .branch 4493 2 [.small 2, .small 2, .branch 1123 2 [.small 2, .small 3, .small 11, .small 17]]]]]) (by decide +kernel)

private theorem witness533 : Witness 533 := by
  refine ⟨23, 510, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 265314167 5 [.small 2, .small 13, .branch 10204391 7 [.small 2, .small 5, .small 7, .branch 145777 5 [.small 2, .small 2, .small 2, .small 2, .small 3, .branch 3037 2 [.small 2, .small 2, .small 3, .small 11, .small 23]]]]) (by decide +kernel)

private theorem witness534 : Witness 534 := by
  refine ⟨23, 511, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 266877829 6 [.small 2, .small 2, .small 3, .small 3, .small 3, .small 3, .small 7, .branch 117671 11 [.small 2, .small 5, .small 7, .small 41, .small 41]]) (by decide +kernel)

private theorem witness535 : Witness 535 := by
  refine ⟨3, 532, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 301137563 2 [.small 2, .small 11, .branch 13688071 21 [.small 2, .small 3, .small 5, .small 11, .branch 41479 3 [.small 2, .small 3, .small 31, .small 223]]]) (by decide +kernel)

private theorem witness536 : Witness 536 := by
  refine ⟨5, 531, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 299442707 2 [.small 2, .small 79, .branch 1895207 5 [.small 2, .branch 947603 2 [.small 2, .small 229, .branch 2069 2 [.small 2, .small 2, .small 11, .small 47]]]]) (by decide +kernel)

private theorem witness537 : Witness 537 := by
  refine ⟨41, 496, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 244116793 5 [.small 2, .small 2, .small 2, .small 3, .small 3, .branch 1013 3 [.small 2, .small 2, .small 11, .small 23], .branch 3347 2 [.small 2, .small 7, .small 239]]) (by decide +kernel)

private theorem witness538 : Witness 538 := by
  refine ⟨21, 517, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 276386087 5 [.small 2, .branch 7247 5 [.small 2, .branch 3623 5 [.small 2, .branch 1811 6 [.small 2, .small 5, .small 181]]], .branch 19069 2 [.small 2, .small 2, .small 3, .small 7, .small 227]]) (by decide +kernel)

private theorem witness539 : Witness 539 := by
  refine ⟨83, 456, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 190209419 6 [.small 2, .small 7, .small 19, .branch 715073 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .branch 11173 5 [.small 2, .small 2, .small 3, .small 7, .small 7, .small 19]]]) (by decide +kernel)

private theorem witness540 : Witness 540 := by
  refine ⟨29, 511, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 266890051 3 [.small 2, .small 3, .small 3, .small 5, .small 5, .small 7, .small 193, .small 439]) (by decide +kernel)

private theorem witness541 : Witness 541 := by
  refine ⟨81, 460, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 195203441 3 [.small 2, .small 2, .small 2, .small 2, .small 5, .branch 2440043 2 [.small 2, .small 11, .small 197, .small 563]]) (by decide +kernel)

private theorem witness542 : Witness 542 := by
  refine ⟨11, 531, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 299443913 3 [.small 2, .small 2, .small 2, .small 499, .branch 75011 6 [.small 2, .small 5, .small 13, .small 577]]) (by decide +kernel)

private theorem witness543 : Witness 543 := by
  refine ⟨233, 310, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 72231337 5 [.small 2, .small 2, .small 2, .small 3, .small 3, .small 379, .branch 2647 3 [.small 2, .small 3, .small 3, .small 3, .small 7, .small 7]]) (by decide +kernel)

private theorem witness544 : Witness 544 := by
  refine ⟨9, 535, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 306261479 19 [.small 2, .small 523, .branch 292793 3 [.small 2, .small 2, .small 2, .branch 36599 19 [.small 2, .small 29, .small 631]]]) (by decide +kernel)

private theorem witness545 : Witness 545 := by
  refine ⟨53, 492, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 238339853 2 [.small 2, .small 2, .branch 59584963 3 [.small 2, .small 3, .branch 9930827 2 [.small 2, .branch 4965413 2 [.small 2, .small 2, .small 653, .branch 1901 2 [.small 2, .small 2, .small 5, .small 5, .small 19]]]]]) (by decide +kernel)

private theorem witness546 : Witness 546 := by
  refine ⟨41, 505, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 257644171 3 [.small 2, .small 3, .small 3, .small 5, .small 7, .branch 408959 11 [.small 2, .small 11, .small 29, .small 641]]) (by decide +kernel)

private theorem witness547 : Witness 547 := by
  refine ⟨21, 526, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 291072413 2 [.small 2, .small 2, .branch 1231 3 [.small 2, .small 3, .small 5, .small 41], .branch 59113 7 [.small 2, .small 2, .small 2, .small 3, .small 3, .small 821]]) (by decide +kernel)

private theorem witness548 : Witness 548 := by
  refine ⟨83, 465, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 201661037 2 [.small 2, .small 2, .small 263, .branch 191693 2 [.small 2, .small 2, .small 17, .branch 2819 2 [.small 2, .branch 1409 3 [.small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 2, .small 11]]]]) (by decide +kernel)

private theorem witness549 : Witness 549 := by
  refine ⟨89, 460, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 195376969 11 [.small 2, .small 2, .small 2, .small 3, .small 3, .small 3, .branch 904523 2 [.small 2, .small 617, .small 733]]) (by decide +kernel)

private theorem witness550 : Witness 550 := by
  refine ⟨219, 331, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 83032841 3 [.small 2, .small 2, .small 2, .small 5, .small 11, .branch 188711 17 [.small 2, .small 5, .small 113, .small 167]]) (by decide +kernel)

private theorem witness551 : Witness 551 := by
  refine ⟨35, 516, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 274819067 2 [.small 2, .branch 137409533 2 [.small 2, .small 2, .small 13, .small 41, .branch 64451 2 [.small 2, .small 5, .small 5, .branch 1289 6 [.small 2, .small 2, .small 2, .small 7, .small 23]]]]) (by decide +kernel)

private theorem witness552 : Witness 552 := by
  refine ⟨5, 547, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 327334771 7 [.small 2, .small 3, .small 3, .small 3, .small 3, .small 5, .small 7, .branch 57731 2 [.small 2, .small 5, .small 23, .small 251]]) (by decide +kernel)

private theorem witness553 : Witness 553 := by
  refine ⟨99, 454, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 188123627 2 [.small 2, .branch 94061813 2 [.small 2, .small 2, .small 13, .small 23, .small 31, .small 43, .small 59]]) (by decide +kernel)

private theorem witness554 : Witness 554 := by
  refine ⟨215, 339, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 87854813 2 [.small 2, .small 2, .small 137, .branch 160319 11 [.small 2, .small 71, .branch 1129 11 [.small 2, .small 2, .small 2, .small 3, .small 47]]]) (by decide +kernel)

private theorem witness555 : Witness 555 := by
  refine ⟨11, 544, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 321979699 3 [.small 2, .small 3, .small 3, .small 3, .small 3, .small 37, .branch 53717 2 [.small 2, .small 2, .small 13, .branch 1033 5 [.small 2, .small 2, .small 2, .small 3, .small 43]]]) (by decide +kernel)

private theorem witness556 : Witness 556 := by
  refine ⟨141, 415, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 145749971 2 [.small 2, .small 5, .branch 2963 2 [.small 2, .branch 1481 3 [.small 2, .small 2, .small 2, .small 5, .small 37]], .branch 4919 13 [.small 2, .branch 2459 2 [.small 2, .branch 1229 2 [.small 2, .small 2, .small 307]]]]) (by decide +kernel)

private theorem witness557 : Witness 557 := by
  refine ⟨11, 546, by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_⟩
  exact verified_prime 8 (.branch 325544003 5 [.small 2, .small 7, .branch 23253143 5 [.small 2, .small 11, .small 251, .branch 4211 6 [.small 2, .small 5, .small 421]]]) (by decide +kernel)

theorem result : OMA.R_oeis_a220419_R1.H1 := by
  intro n lo hi
  interval_cases n
  · exact witness528
  · exact witness529
  · exact witness530
  · exact witness531
  · exact witness532
  · exact witness533
  · exact witness534
  · exact witness535
  · exact witness536
  · exact witness537
  · exact witness538
  · exact witness539
  · exact witness540
  · exact witness541
  · exact witness542
  · exact witness543
  · exact witness544
  · exact witness545
  · exact witness546
  · exact witness547
  · exact witness548
  · exact witness549
  · exact witness550
  · exact witness551
  · exact witness552
  · exact witness553
  · exact witness554
  · exact witness555
  · exact witness556
  · exact witness557

end PrimeCubicSums

theorem OMA.solution : OMA.R_oeis_a220419_R1.H1 :=
  PrimeCubicSums.result