import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1

/-!
# Fixed-prime bounds for the thick kernel when the two-adic valuation is 64 modulo 128

Write Q = 67280421310721 and a = v₂(n). The unitary divisor product forces
Q to have positive multiplicity divisible by eight. If the multiplicity of
274177 is even, it too is positive and divisible by eight. If it is odd,
137089 occurs with positive multiplicity divisible by eight.

In either case the least repeated odd prime p other than 137089 is between
3151 and 247625. Both hypotheses ask for a bound depending on this fixed p.
Taking a maximum over the finite interval recovers a uniform bound.
The seed obstructions below further restrict the exponents in both hypotheses.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1

-- The Lucas certificate below is from the merged reduction by @adammcarter.

theorem zmod_ne_one {p c : ℕ} (h : c % p ≠ 1 % p) : ((c : ℕ) : ZMod p) ≠ 1 := by
  intro h'
  apply h
  have h2 : ((c : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h'
  exact (ZMod.natCast_eq_natCast_iff' c 1 p).mp h2

theorem prime_67280421310721 : Nat.Prime 67280421310721 := by
  refine lucas_primality 67280421310721 (3 : ZMod 67280421310721) ?_ (fun q hq hd => ?_)
  · rw [show 67280421310721 - 1 = 67280421310720 from by norm_num]
    reduce_mod_char
  · have e : 67280421310721 - 1 = [2 ^ 8, 5 ^ 1, 47 ^ 1, 373 ^ 1, 2998279 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 2 = 33640210655360 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 33640210655360 = ((67280421310720 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 5 = 13456084262144 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 13456084262144 = ((8348471219631 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 47 = 1431498325760 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 1431498325760 = ((29801263682154 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 373 = 180376464640 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 180376464640 = ((65541179653181 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 2998279 = 22439680 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 22439680 = ((61150258807256 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1.Erdos1052C17

-- Isolate one factor of the admissibility product and clear its denominator.
lemma kernel_pointwise_budget {S : Finset ℕ} {p : ℕ} (hp : p ∈ S)
    (hz : ∀ z ∈ S, S.card + 3 ≤ z)
    (hupper : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) :
    2101 * S.card + 6299 ≤ 4 * p := by
  let f (w : ℕ) : ℚ := ((w : ℚ) + 1) / ((w : ℚ) - 2 - (S.card : ℚ))
  have hden (w : ℕ) (hw : w ∈ S) : 0 < (w : ℚ) - 2 - S.card := by
    have ha : (S.card : ℚ) + 3 ≤ w := by exact_mod_cast hz w hw
    linarith
  have hOne (w : ℕ) (hw : w ∈ S) : 1 ≤ f w := by
    apply (le_div_iff₀ (hden w hw)).2
    have : (0 : ℚ) ≤ S.card := by positivity
    linarith
  have hsub : {p} ⊆ S := Finset.singleton_subset_iff.mpr hp
  have hle : f p ≤ ∏ w ∈ S, f w := by
    simpa using Finset.prod_le_prod_of_subset_of_one_le (f := f) hsub
      (fun w hw ↦ (by norm_num : (0 : ℚ) ≤ 1).trans (hOne w (hsub hw)))
      (fun w hw _ ↦ hOne w hw)
  have h := hle.trans hupper
  change ((p : ℚ) + 1) / ((p : ℚ) - 2 - S.card) ≤ 2101 / 2097 at h
  exact_mod_cast (show 2101 * (S.card : ℚ) + 6299 ≤ 4 * p by
    linarith only [(div_le_iff₀ (hden p hp)).mp h])

-- A small factor of 2^192+1 rules out every multiple of 3 in this branch.
lemma exponent_not_multiple_of_three {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (ha : padicValNat 2 n % 128 = 64) (h769 : ¬ 769 ∣ n) :
    ¬ 3 ∣ padicValNat 2 n := by
  intro h3
  let a := padicValNat 2 n
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega)
  have hmem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, h.2.ne'⟩
  have hprod := Finset.dvd_prod_of_mem (fun p ↦ 1 + p ^ n.factorization p) hmem
  rw [prod_eq_two_mul h, Nat.factorization_def n Nat.prime_two, add_comm] at hprod
  have he : padicValNat 2 n = 192 * (2 * (a / 384) + 1) := by dsimp [a]; omega
  have hd : 769 ∣ 2 ^ padicValNat 2 n + 1 := by
    rw [he]
    exact (by decide : 769 ∣ 2 ^ 192 + 1).trans (odd_mult ⟨a / 384, rfl⟩)
  exact h769 (((show Nat.Prime 769 by norm_num).dvd_mul.mp (hd.trans hprod)).resolve_left (by decide))

-- An odd multiple of 832 forces three different repeated primes that are 2 mod 3.
-- The known repeated prime 137089 or 274177 then exceeds the budget at 3329.
set_option maxRecDepth 4096 in
lemma exponent_not_multiple_of_thirteen {n : ℕ} {S : Finset ℕ}
    (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hz : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hupper : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (ha : padicValNat 2 n % 128 = 64) (h5 : 5 ∣ n)
    (hb : 274177 ^ 2 ∣ n ∨ 137089 ^ 2 ∣ n) : ¬ 13 ∣ padicValNat 2 n := by
  intro h13
  let a := padicValNat 2 n
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega)
  obtain ⟨K, K', P, hP, hK, _, _, E, hmem⟩ := setup7 h hS h2
  obtain ⟨_, seed, uniqueParent, _⟩ := facts hP hK E
  have small (x : ℕ) (hx : x < 128) : x ∉ S := fun hxS ↦ (not_le.mpr hx) (hz x hxS).1
  have h5P := (hmem 5).mpr ⟨by decide, by decide, h5, small 5 (by decide)⟩
  have he : padicValNat 2 n = 832 * (2 * (a / 1664) + 1) := by dsimp [a]; omega
  have hseed : 2 ^ 832 + 1 ∣ 2 ^ padicValNat 2 n + 1 := by
    rw [he]
    exact odd_mult ⟨a / 1664, rfl⟩
  have repeatedFactor (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ 832 + 1) (hm : p % 3 = 2) : p ∈ S := by
    have ne2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ (2 : ℕ) ∣ 2 ^ 832 + 1) hd
    have ne5 : p ≠ 5 := by rintro rfl; exact (by decide : ¬ (5 : ℕ) ∣ 2 ^ 832 + 1) hd
    by_contra hs
    have hpP := seed p hp ne2 hs (hd.trans hseed)
    exact ne5 (uniqueParent 3 (by decide) (by decide) (small 3 (by decide))
      p hpP 5 h5P (by omega) (by decide))
  let F : ℕ := 2 ^ 64 + 1
  let C : ℕ := (2 ^ 832 + 1) / F / 3329
  obtain ⟨q, hq, hqF, hqm⟩ := exists_prime_mod3 F (by dsimp only [C, F]; decide)
  obtain ⟨r, hr, hrC, hrm⟩ := exists_prime_mod3 C (by dsimp only [C, F]; decide)
  have qS := repeatedFactor q hq (hqF.trans (by dsimp only [C, F]; decide : F ∣ 2 ^ 832 + 1)) hqm
  have rS := repeatedFactor r hr (hrC.trans (by dsimp only [C, F]; decide : C ∣ 2 ^ 832 + 1)) hrm
  have tS := repeatedFactor 3329 (by norm_num) (by decide) (by decide)
  have qr : q ≠ r := fun eq ↦ hq.ne_one (Nat.eq_one_of_dvd_coprimes
    (by dsimp only [C, F]; decide : F.Coprime C) hqF (eq ▸ hrC))
  have qt : q ≠ 3329 := by rintro rfl; exact (by dsimp only [C, F]; decide : ¬ 3329 ∣ F) hqF
  have rt : r ≠ 3329 := by rintro rfl; exact (by dsimp only [C, F]; decide : ¬ 3329 ∣ C) hrC
  obtain ⟨b, bS, bm⟩ : ∃ b ∈ S, b % 3 = 1 := by
    rcases hb with hd | hd
    · exact ⟨274177, (hS _).mpr ⟨by norm_num, by decide, hd⟩, by decide⟩
    · exact ⟨137089, (hS _).mpr ⟨by norm_num, by decide, hd⟩, by decide⟩
  have qb : q ≠ b := by omega
  have rb : r ≠ b := by omega
  have tb : 3329 ≠ b := by omega
  have hsub : ({q, r, 3329, b} : Finset ℕ) ⊆ S := by
    simpa [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro qS ⟨rS, tS, bS⟩
  have hn := Finset.card_le_card hsub
  have hfour : ({q, r, 3329, b} : Finset ℕ).card = 4 := by simp [qr, qt, rt, qb, rb, tb]
  have hbudget := kernel_pointwise_budget tS (fun z hzs ↦ (hz z hzs).2) hupper
  omega




lemma repeated_of_seed_mod_three {n : ℕ} {S : Finset ℕ}
    (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hz : ∀ z ∈ S, 128 ≤ z)
    (ha : padicValNat 2 n % 128 = 64) (h5 : 5 ∣ n)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ padicValNat 2 n + 1) (hm : p % 3 = 2) : p ∈ S := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega)
  obtain ⟨K, K', P, hP, hK, _, _, E, hmem⟩ := setup7 h hS h2
  obtain ⟨_, seed, uniqueParent, _⟩ := facts hP hK E
  have small (x : ℕ) (hx : x < 128) : x ∉ S := fun hxS ↦ (not_le.mpr hx) (hz x hxS)
  have h5P := (hmem 5).mpr ⟨by decide, by decide, h5, small 5 (by decide)⟩
  have ne2 : p ≠ 2 := by
    rintro rfl
    have he : 0 < padicValNat 2 n := by omega
    have heven := dvd_pow_self 2 he.ne'
    omega
  have ne5 : p ≠ 5 := by
    rintro rfl
    exact no_div (c := 4) (t := 1) (by decide) (by decide) (by decide) (by omega) hd
  by_contra hs
  exact ne5 (uniqueParent 3 (by decide) (by decide) (small 3 (by decide))
    p (seed p hp ne2 hs hd) 5 h5P (by omega) (by decide))

lemma kernel_subset_budget {S T : Finset ℕ} {k : ℕ} (hT : T ⊆ S) (hk : k ≤ S.card)
    (hz : ∀ z ∈ S, S.card + 3 ≤ z)
    (hupper : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) :
    ∏ z ∈ T, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (k : ℚ))) ≤ 2101 / 2097 := by
  let f (w : ℕ) : ℚ := ((w : ℚ) + 1) / ((w : ℚ) - 2 - S.card)
  have hden (w : ℕ) (hw : w ∈ S) : 0 < (w : ℚ) - 2 - S.card := by
    have ha : (S.card : ℚ) + 3 ≤ w := by exact_mod_cast hz w hw
    linarith
  have hk' : (k : ℚ) ≤ S.card := by exact_mod_cast hk
  have hone (w : ℕ) (hw : w ∈ S) : 1 ≤ f w := by
    apply (le_div_iff₀ (hden w hw)).mpr
    have : (0 : ℚ) ≤ S.card := by positivity
    linarith
  refine le_trans (b := ∏ z ∈ T, f z) (Finset.prod_le_prod ?_ ?_) ?_
  · intro z hzT
    exact div_nonneg (by positivity) (by linarith only [hden z (hT hzT), hk'])
  · intro z hzT
    exact div_le_div_of_nonneg_left (by positivity) (hden z (hT hzT)) (by linarith)
  exact (Finset.prod_le_prod_of_subset_of_one_le (f := f) hT
    (fun z hzt ↦ (by norm_num : (0 : ℚ) ≤ 1).trans (hone z (hT hzt)))
    (fun z hzs _ ↦ hone z hzs)).trans hupper

-- Pairwise coprime divisors each equal to 2 modulo 3 require different prime factors.
lemma cofactor_count {k a b : ℕ} {S : Finset ℕ} (D : Fin k → ℕ)
    (hmod : ∀ i, D i % 3 = 2) (hcop : ∀ i j, i ≠ j → (D i).Coprime (D j))
    (hdiv : ∀ i, D i ∣ 2 ^ a + 1)
    (hforced : ∀ p : ℕ, p.Prime → p ∣ 2 ^ a + 1 → p % 3 = 2 → p ∈ S)
    (hbS : b ∈ S) (hbm : b % 3 = 1) : k + 1 ≤ S.card := by
  classical
  choose q hq hqd hqm using fun i ↦ exists_prime_mod3 (D i) (hmod i)
  have hinj : Function.Injective q := by
    intro i j he
    by_contra hne
    exact (hq i).ne_one (Nat.eq_one_of_dvd_coprimes (hcop i j hne) (hqd i) (he ▸ hqd j))
  have hmem : ∀ i, q i ∈ S.erase b := by
    intro i
    have hdiff : q i ≠ b := fun he ↦ by have hm := hqm i; rw [he, hbm] at hm; contradiction
    exact Finset.mem_erase.mpr ⟨hdiff, hforced _ (hq i) ((hqd i).trans (hdiv i)) (hqm i)⟩
  have hle := Finset.card_le_card_of_injOn (s := Finset.univ) (t := S.erase b) q
    (fun i _ ↦ hmem i) hinj.injOn
  simpa [Finset.card_erase_of_mem hbS, Nat.le_sub_one_iff_lt (Finset.card_pos.mpr ⟨b, hbS⟩)] using hle

set_option maxRecDepth 4096 in
lemma exponent_not_multiple_of_713 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hz : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hupper : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (ha : padicValNat 2 n % 128 = 64) (h5 : 5 ∣ n)
    (hb : 274177 ^ 2 ∣ n ∨ 137089 ^ 2 ∣ n) : ¬ 713 ∣ padicValNat 2 n := by
  intro h713
  let a := padicValNat 2 n
  have he23 : a = 1472 * (2 * (a / 2944) + 1) := by dsimp [a]; omega
  have he31 : a = 1984 * (2 * (a / 3968) + 1) := by dsimp [a]; omega
  have seed23 : 2 ^ 1472 + 1 ∣ 2 ^ a + 1 := he23 ▸ odd_mult (c := 1472) ⟨a / 2944, rfl⟩
  have seed31 : 2 ^ 1984 + 1 ∣ 2 ^ a + 1 := he31 ▸ odd_mult (c := 1984) ⟨a / 3968, rfl⟩
  let F : ℕ := 2 ^ 64 + 1
  let D : Fin 5 → ℕ := ![F, 11777, (2 ^ 1472 + 1) / F / 11777, 7937, (2 ^ 1984 + 1) / F / 7937]
  have hmod : ∀ i, D i % 3 = 2 := by dsimp only [D, F]; decide
  have hcop : ∀ i j, i ≠ j → (D i).Coprime (D j) := by dsimp only [D, F]; decide
  have hdiv : ∀ i, D i ∣ 2 ^ a + 1 := by
    have hn : ∀ i, D i ∣ 2 ^ 1472 + 1 ∨ D i ∣ 2 ^ 1984 + 1 := by dsimp only [D, F]; decide
    intro i
    exact (hn i).elim (fun hd ↦ hd.trans seed23) (fun hd ↦ hd.trans seed31)
  have hforced (p : ℕ) (hp : p.Prime) (hd : p ∣ 2 ^ a + 1) (hm : p % 3 = 2) : p ∈ S :=
    repeated_of_seed_mod_three h hS (fun z zS ↦ (hz z zS).1) ha h5 hp hd hm
  have s23 := hforced 11777 (by norm_num) ((by decide : 11777 ∣ 2 ^ 1472 + 1).trans seed23) (by decide)
  have s31 := hforced 7937 (by norm_num) ((by decide : 7937 ∣ 2 ^ 1984 + 1).trans seed31) (by decide)
  obtain ⟨b, bS, bval⟩ : ∃ b ∈ S, b = 137089 ∨ b = 274177 := by
    rcases hb with hd | hd
    · exact ⟨274177, (hS _).mpr ⟨by norm_num, by decide, hd⟩, Or.inr rfl⟩
    · exact ⟨137089, (hS _).mpr ⟨by norm_num, by decide, hd⟩, Or.inl rfl⟩
  have bm : b % 3 = 1 := bval.elim (fun e ↦ e ▸ (by decide)) (fun e ↦ e ▸ (by decide))
  have hc := cofactor_count D hmod hcop hdiv hforced bS bm
  have hsub : ({7937, 11777, b} : Finset ℕ) ⊆ S := by
    simpa [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro s31 ⟨s23, bS⟩
  have hBudget := kernel_subset_budget hsub hc (fun z zS ↦ (hz z zS).2) hupper
  rcases bval with rfl | rfl <;> norm_num [Finset.prod_insert] at hBudget



theorem exponent_sieve {n : ℕ} {S : Finset ℕ}
    (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hz : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hupper : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (ha : padicValNat 2 n % 128 = 64) (h5 : 5 ∣ n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783)
    (hb : 274177 ^ 2 ∣ n ∨ 137089 ^ 2 ∣ n) :
    Nat.Coprime (padicValNat 2 n) 39 ∧ ¬ 713 ∣ padicValNat 2 n := by
  have h769 : ¬ 769 ∣ n := by
    intro hd
    have hcases := hsmall 769 (by norm_num) hd (by decide)
    omega
  have h3 := exponent_not_multiple_of_three h ha h769
  have h13 := exponent_not_multiple_of_thirteen h hS hz hupper ha h5 hb
  refine ⟨?_, exponent_not_multiple_of_713 h hS hz hupper ha h5 hb⟩
  rw [show 39 = 3 * 13 by decide, Nat.coprime_mul_iff_right]
  exact ⟨((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr h3).symm,
    ((show Nat.Prime 13 by decide).coprime_iff_not_dvd.mpr h13).symm⟩

lemma component_factor {n p q : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hpn : p ∣ n) (hq : q.Prime) (hq2 : ¬ q ∣ 2)
    (hd : q ∣ p ^ n.factorization p + 1) : q ∣ n := by
  have hmem := Nat.mem_primeFactors.mpr ⟨hp, hpn, h.2.ne'⟩
  have hprod := Finset.dvd_prod_of_mem (fun t ↦ 1 + t ^ n.factorization t) hmem
  rw [prod_eq_two_mul h, add_comm] at hprod
  exact (hq.dvd_mul.mp (hd.trans hprod)).resolve_left hq2

lemma component_odd_multiple {p q e d : ℕ}
    (hd : q ∣ p ^ d + 1) (he : e = d * (2 * (e / (2*d)) + 1)) : q ∣ p ^ e + 1 := by
  have ho : Odd (2 * (e / (2*d)) + 1) := ⟨e / (2*d), rfl⟩
  have ht := ho.nat_add_dvd_pow_add_pow (p ^ d) 1
  rw [one_pow, ← pow_mul, ← he] at ht
  exact hd.trans ht

lemma no_second_five {n p : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h25 : ¬ 5 ^ 2 ∣ n) (h19 : 19 ∣ n) (he19 : n.factorization 19 = 1)
    (hp : p.Prime) (hpn : p ∣ n) (hne : p ≠ 19) : ¬ 5 ∣ p ^ n.factorization p + 1 := by
  intro hd
  have hsub : ({19, p} : Finset ℕ) ⊆ n.primeFactors := by
    exact Finset.insert_subset (Nat.mem_primeFactors.mpr ⟨by decide, h19, h.2.ne'⟩)
      (Finset.singleton_subset_iff.mpr (Nat.mem_primeFactors.mpr ⟨hp, hpn, h.2.ne'⟩))
  have hh := Finset.prod_dvd_prod_of_subset _ _ (fun t ↦ 1 + t ^ n.factorization t) hsub
  rw [Finset.prod_pair (Ne.symm hne), prod_eq_two_mul h, he19, pow_one] at hh
  have h25d : 25 ∣ 2*n := (mul_dvd_mul (by decide : 5 ∣ 1 + 19) (by simpa [add_comm] using hd)).trans hh
  exact h25 ((by decide : Nat.Coprime 25 2).dvd_of_dvd_mul_left h25d)

lemma eight_dvd_of_components {p e u v w : ℕ}
    (hu : u ∣ p + 1) (hv : v ∣ p ^ 2 + 1) (hw : w ∣ p ^ 4 + 1)
    (nu : ¬ u ∣ p ^ e + 1) (nv : ¬ v ∣ p ^ e + 1) (nw : ¬ w ∣ p ^ e + 1) : 8 ∣ e := by
  have h1 : 2 ∣ e := by
    by_contra hh
    apply nu
    exact component_odd_multiple (d := 1) (by simpa using hu) (by omega)
  have h2 : 4 ∣ e := by
    by_contra hh
    exact nv (component_odd_multiple hv (by omega))
  by_contra hh
  exact nw (component_odd_multiple hw (by omega))

lemma exponent_double_class {e : ℕ} (he : 2 ∣ e) (h : ¬ 4 ∣ e) : e = 2 * (2 * (e / 4) + 1) := by omega

lemma exponent_four_class {e : ℕ} (he : 4 ∣ e) (h : ¬ 8 ∣ e) : e = 4 * (2 * (e / 8) + 1) := by omega

lemma exponent_odd_class {e : ℕ} (he : Odd e) : e = 1 * (2 * (e / 2) + 1) := by
  obtain ⟨t, ht⟩ := he
  omega

set_option maxHeartbeats 600000 in
theorem forced_eighth_powers {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hz : ∀ z ∈ S, S.card + 3 ≤ z)
    (hupper : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - S.card)) ≤ 2101 / 2097)
    (hsz : 2 ≤ S.card) (ha : padicValNat 2 n % 128 = 64) (h19 : 19 ∣ n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) :
    (67280421310721 ^ 8 ∣ n ∧ 8 ∣ n.factorization 67280421310721) ∧
    ((274177 ^ 8 ∣ n ∧ 8 ∣ n.factorization 274177) ∨
     (137089 ^ 8 ∣ n ∧ 8 ∣ n.factorization 137089 ∧ Odd (n.factorization 274177))) := by
  have primeA : Nat.Prime 274177 := by norm_num
  have primeB : Nat.Prime 137089 := by norm_num
  have primeQ := prime_67280421310721
  have absent (q : ℕ) (hq : q.Prime) (hs : q < 1899)
      (hbad : q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7 ∧ q ≠ 19 ∧ q ≠ 31 ∧ q ≠ 223 ∧ q ≠ 991 ∧ q ≠ 1783) : ¬ q ∣ n := by
    intro hqN
    have hx := hsmall q hq hqN hs
    rcases hbad with ⟨q2, q3, q5, q7, q19, q31, q223, q991, q1783⟩
    simp [q2, q3, q5, q7, q19, q31, q223, q991, q1783] at hx
  have noSq (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hlt : p < 2626) : ¬ p ^ 2 ∣ n := by
    intro hd
    have hbound := kernel_pointwise_budget ((hS p).mpr ⟨hp, hodd, hd⟩) hz hupper
    omega
  have single (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hpn : p ∣ n) (hlt : p < 2626) :
      n.factorization p = 1 := by
    have hpos := hp.factorization_pos_of_dvd h.2.ne' hpn
    have hlt2 : ¬ 2 ≤ n.factorization p := fun hh ↦ noSq p hp hodd hlt ((hp.pow_dvd_iff_le_factorization h.2.ne').mpr hh)
    omega
  have no2617 : ¬ 2617 ∣ n := by
    intro hd
    have hp : Nat.Prime 2617 := by norm_num
    have he := single 2617 hp (by decide) hd (by decide)
    apply absent 11 (by decide) (by decide) (by decide)
    apply component_factor h hp hd (by decide) (by decide)
    rw [he]
    decide
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega)
  have seedbase : 2 ^ 64 + 1 ∣ 2 ^ padicValNat 2 n + 1 := by
    have he : padicValNat 2 n = 64 * (2 * (padicValNat 2 n / 128) + 1) := by omega
    rw [he]
    exact odd_mult ⟨padicValNat 2 n / 128, rfl⟩
  have seedFactor (q : ℕ) (hq : q.Prime) (hq2 : ¬ q ∣ 2) (hd : q ∣ 2 ^ 64 + 1) : q ∣ n := by
    apply component_factor h Nat.prime_two h2 hq hq2
    rw [Nat.factorization_def n Nat.prime_two]
    exact hd.trans seedbase
  have hQN := seedFactor _ primeQ (by decide) (by decide)
  have hAN := seedFactor _ primeA (by decide) (by decide)
  have banned {p q : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hq : q.Prime) (hq2 : ¬ q ∣ 2) (hnq : ¬ q ∣ n) :
      ¬ q ∣ p ^ n.factorization p + 1 := fun hd ↦ hnq (component_factor h hp hpn hq hq2 hd)
  have notFive {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hne : p ≠ 19) : ¬ 5 ∣ p ^ n.factorization p + 1 :=
    no_second_five h (noSq 5 (by decide) (by decide) (by decide)) h19 (single 19 (by decide) (by decide) h19 (by decide)) hp hpn hne
  have lift8 {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (he : 8 ∣ n.factorization p) : p ^ 8 ∣ n := by
    exact (hp.pow_dvd_iff_le_factorization h.2.ne').mpr
      (Nat.le_of_dvd (hp.factorization_pos_of_dvd h.2.ne' hpn) he)
  have hQ8 : 8 ∣ n.factorization 67280421310721 := by
    apply eight_dvd_of_components (p := 67280421310721) (u := 109) (v := 13) (w := 17) (by decide) (by decide) (by decide)
    all_goals exact banned primeQ hQN (by decide) (by decide) (absent _ (by decide) (by decide) (by decide))
  refine ⟨⟨lift8 primeQ hQN hQ8, hQ8⟩, ?_⟩
  by_cases he : Odd (n.factorization 274177)
  · have hd : 137089 ∣ 274177 ^ n.factorization 274177 + 1 := by
      apply component_odd_multiple (d := 1) (by decide)
      exact exponent_odd_class he
    have hBN := component_factor h primeA hAN primeB (by decide) hd
    have hB8 : 8 ∣ n.factorization 137089 := by
      apply eight_dvd_of_components (p := 137089) (u := 5) (v := 109) (w := 313) (by decide) (by decide) (by decide)
      · exact notFive primeB hBN (by decide)
      all_goals exact banned primeB hBN (by norm_num) (by decide) (absent _ (by norm_num) (by decide) (by decide))
    exact Or.inr ⟨lift8 primeB hBN hB8, hB8, he⟩
  · have hev : 2 ∣ n.factorization 274177 := by
      exact (Nat.not_odd_iff_even.mp he).two_dvd
    have h4 : 4 ∣ n.factorization 274177 := by
      by_contra hh
      exact notFive primeA hAN (by decide) (component_odd_multiple (d := 2) (by decide) (exponent_double_class hev hh))
    have h8 : 8 ∣ n.factorization 274177 := by
      by_contra hh
      exact banned primeA hAN (show Nat.Prime 2617 by norm_num) (by decide) no2617
        (component_odd_multiple (d := 4) (by decide) (exponent_four_class h4 hh))
    exact Or.inl ⟨lift8 primeA hAN h8, h8⟩

lemma kernel_card_le_twenty {S : Finset ℕ}
    (hz : ∀ z ∈ S, S.card + 3 ≤ z)
    (hupper : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - S.card)) ≤ 2101 / 2097)
    (hlower : 2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) : S.card ≤ 20 := by
  by_contra! hlarge
  have hm : (21 : ℚ) ≤ S.card := by exact_mod_cast (show 21 ≤ S.card by omega)
  have h24 : ∏ z ∈ S, (1 + 24 / (z : ℚ)) ≤
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) := by
    refine Finset.prod_le_prod (fun z _ ↦ by positivity) ?_
    intro z hzS
    have hsize : (S.card : ℚ) + 3 ≤ z := by exact_mod_cast hz z hzS
    have hd : 0 < (z : ℚ) - 2 - S.card := by linarith
    have hzpos : 0 < (z : ℚ) := by linarith
    have hid : ((z : ℚ) + 1) / (z - 2 - S.card) = 1 + ((S.card : ℚ) + 3) / (z - 2 - S.card) := by
      field_simp
      ring
    rw [hid]
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℚ) ≤ 24) hd
      (by linarith : (z : ℚ) - 2 - S.card ≤ z)
    have h2 := div_le_div_of_nonneg_right (by linarith : (24 : ℚ) ≤ S.card + 3) hd.le
    linarith only [h1, h2]
  have hscale := prod_one_add_mul_le S (fun z ↦ 24 / (z : ℚ)) (5 / 24) (by norm_num)
    (by norm_num) (fun z _ ↦ by positivity)
  have heq (z : ℕ) : (5 : ℚ) / 24 * (24 / (z : ℚ)) = 5 / z := by ring
  simp only [heq] at hscale
  linarith only [hlower, hscale, h24.trans hupper]

lemma small_additional_prime {S : Finset ℕ} (hcard : S.card ≤ 20)
    (hQ : 67280421310721 ∈ S) (hlo : 2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) :
    ∃ z ∈ S, z ≠ 137089 ∧ z ≤ 247625 := by
  let f (z : ℕ) : ℚ := 1 + 5 / (z : ℚ)
  let R : ℚ := 1 + 5 / 247626
  by_contra! no
  have other (T : Finset ℕ) (hT : T ⊆ S) (hB : 137089 ∉ T) (k : ℕ) (hk : T.card ≤ k) :
      ∏ z ∈ T, f z ≤ R ^ k := by
    calc
      _ ≤ R ^ T.card := by
        rw [← Finset.prod_const]
        apply Finset.prod_le_prod (fun z _ ↦ by dsimp [f]; positivity)
        intro z hz
        have ne : z ≠ 137089 := fun eq ↦ hB (eq ▸ hz)
        have hlarge : (247626 : ℚ) ≤ z := by exact_mod_cast (show 247626 ≤ z from no z (hT hz) ne)
        dsimp [R, f]
        linarith only [div_le_div_of_nonneg_left (a := (5 : ℚ)) (by norm_num) (by norm_num) hlarge]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num [R]) hk
  let T := S.erase 67280421310721
  have hT : T ⊆ S := Finset.erase_subset _ _
  have hcT : T.card ≤ 19 := by dsimp [T]; rw [Finset.card_erase_of_mem hQ]; omega
  have splitQ : (∏ z ∈ S, f z) = (∏ z ∈ T, f z) * f 67280421310721 :=
    (Finset.prod_erase_mul S f hQ).symm
  change 2501 / 2500 < ∏ z ∈ S, f z at hlo
  rw [splitQ] at hlo
  by_cases hb : 137089 ∈ T
  · have h18 : (T.erase 137089).card ≤ 18 := by rw [Finset.card_erase_of_mem hb]; omega
    have hh := other (T.erase 137089) ((Finset.erase_subset _ _).trans hT) (Finset.notMem_erase _ _) 18 h18
    have hs := Finset.prod_erase_mul T f hb
    rw [← hs] at hlo
    have hB : 0 ≤ f 137089 := by norm_num [f]
    have hq : 0 ≤ f 67280421310721 := by norm_num [f]
    have ht := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hB) hq)
    exact (not_lt_of_ge (ht.trans (by norm_num [R, f]))) hlo
  · have hh := other T hT hb 19 hcT
    have ht := mul_le_mul_of_nonneg_right hh (show 0 ≤ f 67280421310721 by norm_num [f])
    exact (not_lt_of_ge (ht.trans (by norm_num [R, f]))) hlo



lemma least_additional_prime {S : Finset ℕ} (hcard : S.card ≤ 20)
    (hQ : 67280421310721 ∈ S) (hb : 137089 ∈ S ∨ 274177 ∈ S)
    (hbudget : ∀ p ∈ S, 2101 * S.card + 6299 ≤ 4 * p)
    (hlo : 2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) :
    3 ≤ S.card ∧ ∃ p ∈ S, 3151 ≤ p ∧ p ≤ 247625 ∧ p ≠ 137089 ∧ ∀ z ∈ S, z ≠ 137089 → p ≤ z := by
  obtain ⟨z, hz, hzB, hzmax⟩ := small_additional_prime hcard hQ hlo
  let T := S.erase 137089
  have hzT : z ∈ T := Finset.mem_erase.mpr ⟨hzB, hz⟩
  have hne : T.Nonempty := ⟨z, hzT⟩
  let p := T.min' hne
  have hpT : p ∈ T := Finset.min'_mem T hne
  obtain ⟨hpB, hpS⟩ := Finset.mem_erase.mp hpT
  have hpmax : p ≤ 247625 := (Finset.min'_le T z hzT).trans hzmax
  obtain ⟨b, bS, bval⟩ : ∃ b ∈ S, b = 137089 ∨ b = 274177 := by
    rcases hb with hh | hh
    · exact ⟨137089, hh, Or.inl rfl⟩
    · exact ⟨274177, hh, Or.inr rfl⟩
  have hpq : p ≠ 67280421310721 := by omega
  have hpb : p ≠ b := by rcases bval with rfl | rfl <;> omega
  have hbq : b ≠ 67280421310721 := by rcases bval with rfl | rfl <;> decide
  have hsub : ({p, b, 67280421310721} : Finset ℕ) ⊆ S := by
    simpa [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hpS ⟨bS, hQ⟩
  have hs := Finset.card_le_card hsub
  have hthree : ({p, b, 67280421310721} : Finset ℕ).card = 3 := by simp [hpb, hpq, hbq]
  have hge := hbudget p hpS
  exact ⟨by omega, p, hpS, by omega, hpmax, hpB, fun v hv hvB ↦ Finset.min'_le T v (Finset.mem_erase.mpr ⟨hvB, hv⟩)⟩

-- Fixed p when 274177 occurs to positive multiplicity divisible by eight.
def H1 : Prop :=
  ∀ p ∈ (Finset.Icc 3151 247625).filter (fun p : ℕ ↦ p.Prime ∧ p ≠ 137089),
    ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ r, r ∈ S ↔ r.Prime ∧ r ≠ 2 ∧ r ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - S.card)) ≤ 2101 / 2097 →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - N.card)) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) →
    (3 ∣ n ∧ 5 ∣ n ∧ 7 ∣ n ∧ 19 ∣ n ∧ 31 ∣ n ∧ 223 ∣ n ∧ 991 ∣ n ∧ 1783 ∣ n) →
    2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    padicValNat 2 n % 128 = 64 →
    ((padicValNat 2 n).Coprime 39 ∧ ¬ 713 ∣ padicValNat 2 n) →
    3 ≤ S.card → S.card ≤ 20 → p ∈ S → (∀ z ∈ S, z ≠ 137089 → p ≤ z) →
    (67280421310721 ^ 8 ∣ n ∧ 8 ∣ n.factorization 67280421310721) →
    (274177 ^ 8 ∣ n ∧ 8 ∣ n.factorization 274177) → padicValNat 2 n ≤ A

-- Fixed p when 274177 has odd multiplicity and 137089 has positive multiplicity divisible by eight.
def H2 : Prop :=
  ∀ p ∈ (Finset.Icc 3151 247625).filter (fun p : ℕ ↦ p.Prime ∧ p ≠ 137089),
    ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ r, r ∈ S ↔ r.Prime ∧ r ≠ 2 ∧ r ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - S.card)) ≤ 2101 / 2097 →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - N.card)) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) →
    (3 ∣ n ∧ 5 ∣ n ∧ 7 ∣ n ∧ 19 ∣ n ∧ 31 ∣ n ∧ 223 ∣ n ∧ 991 ∣ n ∧ 1783 ∣ n) →
    2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    padicValNat 2 n % 128 = 64 →
    ((padicValNat 2 n).Coprime 39 ∧ ¬ 713 ∣ padicValNat 2 n) →
    3 ≤ S.card → S.card ≤ 20 → p ∈ S → (∀ z ∈ S, z ≠ 137089 → p ≤ z) →
    (67280421310721 ^ 8 ∣ n ∧ 8 ∣ n.factorization 67280421310721) →
    (137089 ^ 8 ∣ n ∧ 8 ∣ n.factorization 137089 ∧ Odd (n.factorization 274177)) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1.H2 := by
  classical
  intro h1 h2
  let T := (Finset.Icc 3151 247625).filter (fun p : ℕ ↦ p.Prime ∧ p ≠ 137089)
  choose B1 HB1 using fun p : ↥T ↦ h1 p.1 p.2
  choose B2 HB2 using fun p : ↥T ↦ h2 p.1 p.2
  refine ⟨max (Finset.univ.sup B1) (Finset.univ.sup B2), ?_⟩
  intro n hn _ S hS hz upper _ h3 h5 h7 h19 residue _ _ h31 small h223 h991 h1783 _ lower hcard ha hb
  have size := kernel_card_le_twenty (fun z zs ↦ (hz z zs).2) upper lower
  obtain ⟨hQ, cases⟩ := forced_eighth_powers hn hS (fun z zs ↦ (hz z zs).2) upper hcard ha h19 small
  have hQmem : 67280421310721 ∈ S := (hS _).mpr ⟨prime_67280421310721, by decide,
    (pow_dvd_pow 67280421310721 (by decide : 2 ≤ 8)).trans hQ.1⟩
  have hbmem : 137089 ∈ S ∨ 274177 ∈ S := by
    rcases hb with hA | hB
    · exact Or.inr ((hS _).mpr ⟨by norm_num, by decide, hA⟩)
    · exact Or.inl ((hS _).mpr ⟨by norm_num, by decide, hB⟩)
  obtain ⟨size3, p, pS, pl, pu, pne, least⟩ := least_additional_prime size hQmem hbmem
    (fun _ mem ↦ kernel_pointwise_budget mem (fun z zs ↦ (hz z zs).2) upper) lower
  have pc : p ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨pl, pu⟩, ((hS p).mp pS).1, pne⟩
  let t : ↥T := ⟨p, pc⟩
  have sieve := exponent_sieve hn hS hz upper ha h5 small hb
  rcases cases with evenCase | oddCase
  · have hbnd := HB1 t n hn S hS hz upper residue small ⟨h3,h5,h7,h19,h31,h223,h991,h1783⟩
      lower ha sieve size3 size pS least hQ evenCase
    exact hbnd.trans ((Finset.le_sup (f := B1) (Finset.mem_univ t)).trans (le_max_left _ _))
  · have hbnd := HB2 t n hn S hS hz upper residue small ⟨h3,h5,h7,h19,h31,h223,h991,h1783⟩
      lower ha sieve size3 size pS least hQ oddCase
    exact hbnd.trans ((Finset.le_sup (f := B2) (Finset.mem_univ t)).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1
