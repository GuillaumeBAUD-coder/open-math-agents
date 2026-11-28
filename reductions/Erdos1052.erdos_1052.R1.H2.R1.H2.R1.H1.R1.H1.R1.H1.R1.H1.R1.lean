import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1

-- Credit: @jakubkrcmar
-- uses note #190225
-- The two product bounds confine the number of repeated odd primes to 44
-- and force a second such prime below 1738537. With exactly two repeated
-- primes, the second lies between 2735 and 40421. The two large-kernel
-- branches distinguish the valuation of 65537 and its forced factor 4365089.
-- Bounds in the new problems may depend on the named prime and cardinality.

namespace Erdos1052FiniteKernel

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7

lemma sum_lower_product (S : Finset ℕ) (f : ℕ → ℚ) (hf : ∀ z ∈ S, 0 ≤ f z) :
    1 + ∑ z ∈ S, f z ≤ ∏ z ∈ S, (1 + f z) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert y S hy ih =>
    rw [Finset.sum_insert hy, Finset.prod_insert hy]
    have hy0 := hf y (Finset.mem_insert_self y S)
    have hs0 : ∀ z ∈ S, 0 ≤ f z := fun z hz => hf z (Finset.mem_insert_of_mem hz)
    have hs := Finset.sum_nonneg hs0
    calc
      1 + (f y + ∑ z ∈ S, f z) ≤ (1 + f y) * (1 + ∑ z ∈ S, f z) := by
        nlinarith only [mul_nonneg hy0 hs]
      _ ≤ (1 + f y) * ∏ z ∈ S, (1 + f z) :=
        mul_le_mul_of_nonneg_left (ih hs0) (by linarith)

-- The reciprocal-sum argument is due to @RhizomeSlopGenerator, note 190225.
lemma card_and_second {S : Finset ℕ}
    (hadm : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hW : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (hY : 5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) (hF : 65537 ∈ S) :
    S.card ≤ 44 ∧ ∃ z ∈ S, z ≠ 65537 ∧ z ≤ 1738536 := by
  have hL := one_sub_sum_mul_prod_le S (fun z => 5 / (z : ℚ)) (fun z _ => by positivity)
  have hFive : (∑ z ∈ S, 5 / (z : ℚ)) = 5 * ∑ z ∈ S, 1 / (z : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hFive] at hL
  have hT : (1 : ℚ) / 25005 < ∑ z ∈ S, 1 / (z : ℚ) := by
    by_contra! hsmall
    have hpos : 0 < 1 - 5 * ∑ z ∈ S, 1 / (z : ℚ) := by linarith only [hsmall]
    have hmul := mul_lt_mul_of_pos_left hY hpos
    nlinarith only [hL, hmul, hsmall]
  have hcard : S.card ≤ 44 := by
    by_contra! hbig
    have hk : (45 : ℚ) ≤ S.card := by
      exact_mod_cast (show 45 ≤ S.card by omega)
    have hp : ∏ z ∈ S, (1 + 48 / (z : ℚ)) ≤ 2101 / 2097 := by
      refine (Finset.prod_le_prod (fun z _ => by positivity) (fun z hz => ?_)).trans hW
      have hzq : (S.card : ℚ) + 3 ≤ z := by exact_mod_cast (hadm z hz).2
      have hz0 : (0 : ℚ) < z := by linarith
      have hd : 0 < (z : ℚ) - 2 - S.card := by linarith
      rw [le_div_iff₀ hd]
      have he : (48 / (z : ℚ)) * (z : ℚ) = 48 := div_mul_cancel₀ _ (ne_of_gt hz0)
      have hnn : 0 ≤ (48 / (z : ℚ)) * (2 + (S.card : ℚ)) := by positivity
      nlinarith only [he, hnn, hk]
    have hs := sum_lower_product S (fun z => 48 / (z : ℚ)) (fun z _ => by positivity)
    have h48 : (∑ z ∈ S, 48 / (z : ℚ)) = 48 * ∑ z ∈ S, 1 / (z : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    rw [h48] at hs
    linarith only [hT, hs, hp]
  refine ⟨hcard, ?_⟩
  by_contra hnone
  have hterm : ∀ z ∈ S.erase 65537, 1 / (z : ℚ) ≤ 1 / 1738537 := by
    intro z hz
    have hm := Finset.mem_erase.mp hz
    have hn : ¬ z ≤ 1738536 := fun hle => hnone ⟨z, hm.2, hm.1, hle⟩
    have hzq : (1738537 : ℚ) ≤ z := by exact_mod_cast (show 1738537 ≤ z by omega)
    exact one_div_le_one_div_of_le (by norm_num) hzq
  have hrest : (∑ z ∈ S.erase 65537, 1 / (z : ℚ)) ≤
      ((S.erase 65537).card : ℚ) * (1 / 1738537) := by
    calc
      _ ≤ ∑ _z ∈ S.erase 65537, (1 : ℚ) / 1738537 := Finset.sum_le_sum hterm
      _ = _ := by simp [nsmul_eq_mul]
  have hecard : (S.erase 65537).card ≤ 43 := by
    rw [Finset.card_erase_of_mem hF]
    omega
  have hecardq : ((S.erase 65537).card : ℚ) ≤ 43 := by exact_mod_cast hecard
  have hadd : 1 / (65537 : ℚ) + (∑ z ∈ S.erase 65537, 1 / (z : ℚ)) =
      ∑ z ∈ S, 1 / (z : ℚ) :=
    Finset.add_sum_erase S (fun z => 1 / (z : ℚ)) hF
  linarith only [hT, hrest, hecardq, hadd]

end Erdos1052FiniteKernel

namespace Erdos1052FiniteKernel

lemma pair_range_of_card {S : Finset ℕ} {q : ℕ}
    (hadm : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hW : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (hY : 5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ)))
    (hc : S.card = 2) (hF : 65537 ∈ S) (hq : q ∈ S) (hne : q ≠ 65537) :
    S = {65537, q} ∧ 2735 ≤ q ∧ q ≤ 40421 := by
  have hsingle : (S.erase 65537).card = 1 := by rw [Finset.card_erase_of_mem hF, hc]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hsingle
  have hqerase : q ∈ S.erase 65537 := Finset.mem_erase.mpr ⟨hne, hq⟩
  rw [hv] at hqerase
  have hqv : q = v := Finset.mem_singleton.mp hqerase
  subst v
  have hpair : S = {65537, q} := by rw [← hv, Finset.insert_erase hF]
  have hnot : 65537 ∉ ({q} : Finset ℕ) := fun h => hne (Finset.mem_singleton.mp h).symm
  have hq128 : (128 : ℚ) ≤ q := by exact_mod_cast (hadm q hq).1
  have hq0 : 0 < (q : ℚ) := by linarith
  have hq4 : 0 < (q : ℚ) - 4 := by linarith
  rw [hc, hpair, Finset.prod_insert hnot, Finset.prod_singleton] at hW
  rw [hpair, Finset.prod_insert hnot, Finset.prod_singleton] at hY
  have hden : (q : ℚ) - 2 - 2 = q - 4 := by ring
  have hw : (65538 : ℚ) / 65533 * (((q : ℚ) + 1) / ((q : ℚ) - 4)) ≤ 2101 / 2097 := by
    norm_num [hden] at hW ⊢ <;> exact hW
  have hterm : 1 + 5 / (q : ℚ) = ((q : ℚ) + 5) / (q : ℚ) := by
    field_simp [ne_of_gt hq0] <;> ring
  rw [hterm] at hY
  have hy : 5001 / 5000 < (65542 : ℚ) / 65537 * (((q : ℚ) + 5) / q) := by
    norm_num at hY ⊢ <;> exact hY
  have hlow : (65538 : ℚ) / 65533 * ((q : ℚ) + 1) ≤ 2101 / 2097 * ((q : ℚ) - 4) := by
    rw [← div_le_iff₀ hq4]
    simpa only [mul_div_assoc] using hw
  have hhigh : 5001 / 5000 * (q : ℚ) < 65542 / 65537 * ((q : ℚ) + 5) := by
    rw [← lt_div_iff₀ hq0]
    simpa only [mul_div_assoc] using hy
  refine ⟨hpair, ?_, ?_⟩
  · by_contra! hbad
    have hb : (q : ℚ) ≤ 2734 := by exact_mod_cast (show q ≤ 2734 by omega)
    linarith only [hlow, hb]
  · by_contra! hbad
    have hb : (40422 : ℚ) ≤ q := by exact_mod_cast (show 40422 ≤ q by omega)
    linarith only [hhigh, hb]

end Erdos1052FiniteKernel

namespace UnitaryExponentSieve

theorem no_residue {b e k q : ℕ} (root : q ∣ b ^ k + 1) (excluded : ¬ q ∣ b ^ e + 1) :
    e % (2 * k) ≠ k := by
  intro he
  have division := Nat.div_add_mod e (2 * k)
  rw [he] at division
  have shape : k * (2 * (e / (2 * k)) + 1) = e := by
    calc
      _ = 2 * k * (e / (2 * k)) + k := by ring
      _ = e := division
  have odd : Odd (2 * (e / (2 * k)) + 1) := ⟨e / (2 * k), rfl⟩
  have multiple := Odd.nat_add_dvd_pow_add_pow (b ^ k) 1 odd
  rw [one_pow, ← pow_mul, shape] at multiple
  exact excluded (root.trans multiple)

theorem sieve {e : ℕ}
    (h11 : ¬ 11 ∣ 65537 ^ e + 1) (h5 : ¬ 5 ∣ 65537 ^ e + 1)
    (h17 : ¬ 17 ∣ 65537 ^ e + 1) (h257 : ¬ 257 ∣ 65537 ^ e + 1)
    (h1409 : ¬ 1409 ∣ 65537 ^ e + 1) (h641 : ¬ 641 ∣ 65537 ^ e + 1) :
    e % 32 = 16 ∨ 128 ∣ e := by
  let r : Fin 128 := ⟨e % 128, Nat.mod_lt _ (by decide)⟩
  have rem (d : ℕ) (hd : d ∣ 128) : r.val % d = e % d := Nat.mod_mod_of_dvd e hd
  have cases : ∀ t : Fin 128,
      t.val % 2 ≠ 1 → t.val % 4 ≠ 2 → t.val % 8 ≠ 4 → t.val % 16 ≠ 8 →
      t.val % 64 ≠ 32 → t.val ≠ 64 → t.val % 32 = 16 ∨ t.val = 0 := by decide
  have h := cases r
    (by rw [rem 2 (by decide)]; exact no_residue (k := 1) (by decide) h11)
    (by rw [rem 4 (by decide)]; exact no_residue (k := 2) (by decide) h5)
    (by rw [rem 8 (by decide)]; exact no_residue (k := 4) (by decide) h17)
    (by rw [rem 16 (by decide)]; exact no_residue (k := 8) (by decide) h257)
    (by rw [rem 64 (by decide)]; exact no_residue (k := 32) (by decide) h1409)
    (no_residue (k := 64) (by decide) h641)
  rcases h with h | h
  · exact Or.inl ((rem 32 (by decide)).symm.trans h)
  · exact Or.inr (Nat.dvd_of_mod_eq_zero h)

theorem exponent_sieve {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hlower : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (h19 : 19 ∣ n) (h65537 : 65537 ^ 2 ∣ n)
    (hlist : ∀ q : ℕ, q.Prime → q ∣ n → q < 2100 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607) :
    n.factorization 65537 % 32 = 16 ∨ 128 ∣ n.factorization 65537 := by
  have hn : n ≠ 0 := h.2.ne'
  have not_square (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hlt : q < 128) :
      ¬ q ^ 2 ∣ n := by
    intro hd
    have hge := (hlower q ((hS q).mpr ⟨hq, hq2, hd⟩)).1
    omega
  have p19 : (19 : ℕ).Prime := by decide
  have e19 : n.factorization 19 = 1 := by
    have hpos := p19.factorization_pos_of_dvd hn h19
    have hnot : ¬ 2 ≤ n.factorization 19 :=
      fun he => not_square 19 p19 (by decide) (by decide)
        ((p19.pow_dvd_iff_le_factorization hn).mpr he)
    omega
  let F := fun p : ℕ => 1 + p ^ n.factorization p
  have balance : ∏ p ∈ n.primeFactors, F p = 2 * n :=
    OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul h
  have mem19 : 19 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨p19, h19, hn⟩
  have mem65537 : 65537 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨by norm_num, (show (65537 : ℕ) ∣ 65537 ^ 2 by decide).trans h65537, hn⟩
  have component : 65537 ^ n.factorization 65537 + 1 ∣ 2 * n := by
    rw [← balance, add_comm]
    exact Finset.dvd_prod_of_mem F mem65537
  have lift {q : ℕ} (hq : Nat.Coprime q 2) (hd : q ∣ 65537 ^ n.factorization 65537 + 1) :
      q ∣ n := (Nat.Coprime.dvd_mul_left hq).mp (hd.trans component)
  have exclude {q : ℕ} (hq : q.Prime) (hcop : Nat.Coprime q 2) (hsmall : q < 2100)
      (hother : ¬ (q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607)) :
      ¬ q ∣ 65537 ^ n.factorization 65537 + 1 :=
    fun hd => hother (hlist q hq (lift hcop hd) hsmall)
  have h5 : ¬ 5 ∣ 65537 ^ n.factorization 65537 + 1 := by
    intro hd
    have hA : 5 ∣ F 19 := by
      change 5 ∣ 1 + 19 ^ n.factorization 19
      rw [e19]
      decide
    have hB : 5 ∣ F 65537 := by
      simpa only [F, Nat.add_comm] using hd
    have other : 65537 ∈ n.primeFactors.erase 19 :=
      Finset.mem_erase.mpr ⟨by decide, mem65537⟩
    have hprod : 25 ∣ 2 * n := by
      rw [← balance, ← Finset.mul_prod_erase n.primeFactors F mem19]
      exact mul_dvd_mul hA (hB.trans (Finset.dvd_prod_of_mem F other))
    have h25 : 25 ∣ n := (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 25 2)).mp hprod
    exact not_square 5 (by decide) (by decide) (by decide) h25
  apply sieve
  · exact exclude (by decide) (by decide) (by decide) (by decide)
  · exact h5
  · exact exclude (by decide) (by decide) (by decide) (by decide)
  · exact exclude (by decide) (by decide) (by decide) (by decide)
  · exact exclude (by decide) (by decide) (by decide) (by decide)
  · exact exclude (by decide) (by decide) (by decide) (by decide)

end UnitaryExponentSieve

namespace UnitaryForcedKernelPrime

theorem component_dvd {n p : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hp : p.Prime) (hd : p ∣ n) :
    p ^ n.factorization p + 1 ∣ 2 * n := by
  have hm : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, h.2.ne'⟩
  rw [← OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul h, add_comm]
  exact Finset.dvd_prod_of_mem (fun r => 1 + r ^ n.factorization r) hm

theorem forced_mem {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (h65537 : 65537 ^ 2 ∣ n) (h17 : ¬ 17 ∣ n) (he : n.factorization 65537 % 32 = 16) :
    4365089 ∈ S := by
  let e := n.factorization 65537
  have shape : 16 * (2 * (e / 32) + 1) = e := by
    change e % 32 = 16 at he
    omega
  have odd : Odd (2 * (e / 32) + 1) := ⟨e / 32, rfl⟩
  have mult := Odd.nat_add_dvd_pow_add_pow ((65537 : ℕ) ^ 16) 1 odd
  rw [one_pow, ← pow_mul, shape] at mult
  have seed : 4365089 ∣ 65537 ^ e + 1 :=
    (show (4365089 : ℕ) ∣ 65537 ^ 16 + 1 by decide).trans mult
  have hv : 65537 ∣ n := (show (65537 : ℕ) ∣ 65537 ^ 2 by decide).trans h65537
  have prime : (4365089 : ℕ).Prime := by norm_num
  have hq : 4365089 ∣ n := (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 4365089 2)).mp
    (seed.trans (component_dvd h (by norm_num) hv))
  apply (hS 4365089).mpr
  refine ⟨prime, by decide, (prime.pow_dvd_iff_le_factorization h.2.ne').mpr ?_⟩
  by_contra hlow
  have hpos := prime.factorization_pos_of_dvd h.2.ne' hq
  have first : n.factorization 4365089 = 1 := by omega
  have comp := component_dvd h prime hq
  rw [first, pow_one] at comp
  have h17twice : 17 ∣ 2 * n := (show (17 : ℕ) ∣ 4365089 + 1 by decide).trans comp
  exact h17 ((Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 17 2)).mp h17twice)

theorem thick_card {S : Finset ℕ} (h65537 : 65537 ∈ S) (hq : 4365089 ∈ S)
    (hthick : 5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) : 3 ≤ S.card := by
  have subset : ({65537, 4365089} : Finset ℕ) ⊆ S := by
    simp [Finset.insert_subset_iff, h65537, hq]
  by_contra hcard
  have card : ({65537, 4365089} : Finset ℕ).card = 2 := by decide
  have same : ({65537, 4365089} : Finset ℕ) = S :=
    Finset.eq_of_subset_of_card_le subset (by omega)
  rw [← same, Finset.prod_insert (by decide), Finset.prod_singleton] at hthick
  norm_num at hthick

theorem forced_mem_and_card {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (h65537 : 65537 ^ 2 ∣ n) (he : n.factorization 65537 % 32 = 16)
    (hlist : ∀ q : ℕ, q.Prime → q ∣ n → q < 2100 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607)
    (hthick : 5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) :
    4365089 ∈ S ∧ 3 ≤ S.card := by
  have h17 : ¬ 17 ∣ n := fun hd => by
    have hsmall := hlist 17 (by decide) hd (by decide)
    norm_num at hsmall
  have hq := forced_mem h hS h65537 h17 he
  have hp := (hS 65537).mpr ⟨by norm_num, by decide, h65537⟩
  exact ⟨hq, thick_card hp hq hthick⟩

end UnitaryForcedKernelPrime

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1

-- For each possible second prime in a two-prime kernel.
def H1 : Prop :=
  ∀ q : Fin 40422, ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 2100 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607) →
    223 ∣ n → 607 ∣ n → 48 ≤ padicValNat 2 n →
    5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    2 ≤ S.card → padicValNat 2 n % 32 = 16 → 65537 ^ 2 ∣ n →
    2735 ≤ q.val → S = {65537, q.val} → 128 ∣ n.factorization 65537 →
    padicValNat 2 n ≤ A

-- For a fixed kernel size and second prime when 128 divides the multiplicity.
def H2 : Prop :=
  ∀ j : Fin 45 × Fin 1738537, ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 2100 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607) →
    223 ∣ n → 607 ∣ n → 48 ≤ padicValNat 2 n →
    5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    2 ≤ S.card → padicValNat 2 n % 32 = 16 → 65537 ^ 2 ∣ n →
    3 ≤ j.1.val → S.card = j.1.val → j.2.val ∈ S → j.2.val ≠ 65537 →
    128 ∣ n.factorization 65537 →
    padicValNat 2 n ≤ A

-- For a fixed kernel size and second prime when 4365089 is also repeated.
def H3 : Prop :=
  ∀ j : Fin 45 × Fin 1738537, ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 2100 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607) →
    223 ∣ n → 607 ∣ n → 48 ≤ padicValNat 2 n →
    5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    2 ≤ S.card → padicValNat 2 n % 32 = 16 → 65537 ^ 2 ∣ n →
    3 ≤ j.1.val → S.card = j.1.val → j.2.val ∈ S → j.2.val ≠ 65537 →
    n.factorization 65537 % 32 = 16 → 4365089 ∈ S →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 := by
  classical
  intro b1 b2 b3
  let f1 (q : Fin 40422) := Classical.choose (b1 q)
  let f2 (j : Fin 45 × Fin 1738537) := Classical.choose (b2 j)
  let f3 (j : Fin 45 × Fin 1738537) := Classical.choose (b3 j)
  refine ⟨max (Finset.univ.sup f1) (max (Finset.univ.sup f2) (Finset.univ.sup f3)), ?_⟩
  intro n h hsq S hS hpoint hW h4 h3 h5 h7 h19 hres h16 h64 h31 hlist h223 h607 h48 hY htwo h32 hF2
  have hF : 65537 ∈ S := (hS _).mpr ⟨by norm_num, by decide, hF2⟩
  obtain ⟨hcard, q, hq, hne, hbound⟩ :=
    Erdos1052FiniteKernel.card_and_second hpoint hW hY hF
  have ecase := UnitaryExponentSieve.exponent_sieve h hS hpoint h19 hF2 hlist
  by_cases hpair : S.card = 2
  · obtain ⟨hset, hlo, hhi⟩ := Erdos1052FiniteKernel.pair_range_of_card hpoint hW hY hpair hF hq hne
    have h128 : 128 ∣ n.factorization 65537 := by
      rcases ecase with he | he
      · have hthree := (UnitaryForcedKernelPrime.forced_mem_and_card h hS hF2 he hlist hY).2
        omega
      · exact he
    let p : Fin 40422 := ⟨q, by omega⟩
    have hA : padicValNat 2 n ≤ f1 p := Classical.choose_spec (b1 p) n h hsq S hS hpoint hW
      h4 h3 h5 h7 h19 hres h16 h64 h31 hlist h223 h607 h48 hY htwo h32 hF2 hlo hset h128
    exact hA.trans ((Finset.le_sup (f := f1) (Finset.mem_univ p)).trans (le_max_left _ _))
  · let j : Fin 45 × Fin 1738537 := (⟨S.card, by omega⟩, ⟨q, by omega⟩)
    have hthree : 3 ≤ S.card := by omega
    rcases ecase with he | he
    · have hm := (UnitaryForcedKernelPrime.forced_mem_and_card h hS hF2 he hlist hY).1
      have hA : padicValNat 2 n ≤ f3 j := Classical.choose_spec (b3 j) n h hsq S hS hpoint hW
        h4 h3 h5 h7 h19 hres h16 h64 h31 hlist h223 h607 h48 hY htwo h32 hF2 hthree rfl hq hne he hm
      exact hA.trans ((Finset.le_sup (f := f3) (Finset.mem_univ j)).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
    · have hA : padicValNat 2 n ≤ f2 j := Classical.choose_spec (b2 j) n h hsq S hS hpoint hW
        h4 h3 h5 h7 h19 hres h16 h64 h31 hlist h223 h607 h48 hY htwo h32 hF2 hthree rfl hq hne he
      exact hA.trans ((Finset.le_sup (f := f2) (Finset.mem_univ j)).trans
        ((le_max_left _ _).trans (le_max_right _ _)))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1
