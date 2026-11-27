import FormalConjectures.OEIS.«114137»

-- Credit: @TaifengYi

/-!
# Two disjoint covers for an odd offset

The offset and divisor sets come from Arkadiusz Wesołowski's contribution to
[Multiple covering sets for Sierpinski and for Riesel integers](https://www.primepuzzles.net/problems/prob_092.htm).
Reversing the exponent modulo the order of 2 converts his multiplicative
congruences into congruences for the additive offset. The trees below verify
all the resulting classes directly.
-/

namespace OMA



private def H : ℕ := 132430318140059718398963877387394625974301919973914223179202469722051481175208904289855942288693205424628143798648568555082755511814932143700294388691289

/-- Every exponent in this progression admits a divisor from the indicated product. -/
private def Progression (P m r : ℕ) : Prop :=
  ∀ t : ℕ, ∃ p : ℕ, 1 < p ∧ p ≤ 15790321 ∧ p ∣ P ∧ p ∣ 2^(m*t+r) + H

private theorem progressionLeaf (P m r p : ℕ) (h₁ : 1 < p) (h₂ : p ≤ 15790321)
    (hP : p ∣ P) (hm : 2^m ≡ 1 [MOD p]) (hr : p ∣ 2^r+H) : Progression P m r := by
  intro t
  refine ⟨p, h₁, h₂, hP, Nat.modEq_zero_iff_dvd.mp ?_⟩
  rw [pow_add, pow_mul]
  have h : (2^m)^t ≡ 1 [MOD p] := by simpa using hm.pow t
  exact ((h.mul_right (2^r)).add_right H).trans (by simpa using hr.modEq_zero_nat)

private theorem progressionSplit {P m r s : ℕ} (hs : 0 < s)
    (children : ∀ i : Fin s, Progression P (m*s) (m*i.val+r)) : Progression P m r := by
  intro t
  have e : (m*s)*(t/s)+(m*(t%s)+r) = m*t+r := by
    calc
      _ = m*(t%s+s*(t/s))+r := by ring
      _ = _ := by rw [Nat.mod_add_div]
  rw [← e]
  exact children ⟨t%s, Nat.mod_lt t hs⟩ (t/s)

private theorem split2 {P m r : ℕ}
    (h0 : Progression P (m*2) (m*0+r))
    (h1 : Progression P (m*2) (m*1+r))
    : Progression P m r := by
  apply progressionSplit (s := 2) (by decide)
  intro i
  fin_cases i
  · exact h0
  · exact h1

private theorem split3 {P m r : ℕ}
    (h0 : Progression P (m*3) (m*0+r))
    (h1 : Progression P (m*3) (m*1+r))
    (h2 : Progression P (m*3) (m*2+r))
    : Progression P m r := by
  apply progressionSplit (s := 3) (by decide)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem split5 {P m r : ℕ}
    (h0 : Progression P (m*5) (m*0+r))
    (h1 : Progression P (m*5) (m*1+r))
    (h2 : Progression P (m*5) (m*2+r))
    (h3 : Progression P (m*5) (m*3+r))
    (h4 : Progression P (m*5) (m*4+r))
    : Progression P m r := by
  apply progressionSplit (s := 5) (by decide)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

private theorem split7 {P m r : ℕ}
    (h0 : Progression P (m*7) (m*0+r))
    (h1 : Progression P (m*7) (m*1+r))
    (h2 : Progression P (m*7) (m*2+r))
    (h3 : Progression P (m*7) (m*3+r))
    (h4 : Progression P (m*7) (m*4+r))
    (h5 : Progression P (m*7) (m*5+r))
    (h6 : Progression P (m*7) (m*6+r))
    : Progression P m r := by
  apply progressionSplit (s := 7) (by decide)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

private theorem split11 {P m r : ℕ}
    (h0 : Progression P (m*11) (m*0+r))
    (h1 : Progression P (m*11) (m*1+r))
    (h2 : Progression P (m*11) (m*2+r))
    (h3 : Progression P (m*11) (m*3+r))
    (h4 : Progression P (m*11) (m*4+r))
    (h5 : Progression P (m*11) (m*5+r))
    (h6 : Progression P (m*11) (m*6+r))
    (h7 : Progression P (m*11) (m*7+r))
    (h8 : Progression P (m*11) (m*8+r))
    (h9 : Progression P (m*11) (m*9+r))
    (h10 : Progression P (m*11) (m*10+r))
    : Progression P m r := by
  apply progressionSplit (s := 11) (by decide)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

private def productA : ℕ := 444482897840456965274785

private theorem blockA_4_0 : Progression productA 4 0 :=
  progressionLeaf _ _ _ 5 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_24_2 : Progression productA 24 2 :=
  progressionLeaf _ _ _ 13 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_24_10 : Progression productA 24 10 :=
  progressionLeaf _ _ _ 7 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_24_18 : Progression productA 24 18 :=
  progressionLeaf _ _ _ 241 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_8_2 : Progression productA 8 2 :=
  split3 blockA_24_2 blockA_24_10 blockA_24_18

private theorem blockA_8_6 : Progression productA 8 6 :=
  progressionLeaf _ _ _ 17 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_4_2 : Progression productA 4 2 :=
  split2 blockA_8_2 blockA_8_6

private theorem blockA_2_0 : Progression productA 2 0 :=
  split2 blockA_4_0 blockA_4_2

private theorem blockA_6_1 : Progression productA 6 1 :=
  progressionLeaf _ _ _ 7 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_30_3 : Progression productA 30 3 :=
  progressionLeaf _ _ _ 151 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_30_9 : Progression productA 30 9 :=
  progressionLeaf _ _ _ 31 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_30_15 : Progression productA 30 15 :=
  progressionLeaf _ _ _ 11 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_30_21 : Progression productA 30 21 :=
  progressionLeaf _ _ _ 331 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_60_27 : Progression productA 60 27 :=
  progressionLeaf _ _ _ 41 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_60_57 : Progression productA 60 57 :=
  progressionLeaf _ _ _ 61 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_30_27 : Progression productA 30 27 :=
  split2 blockA_60_27 blockA_60_57

private theorem blockA_6_3 : Progression productA 6 3 :=
  split5 blockA_30_3 blockA_30_9 blockA_30_15 blockA_30_21 blockA_30_27

private theorem blockA_18_5 : Progression productA 18 5 :=
  progressionLeaf _ _ _ 73 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_18_11 : Progression productA 18 11 :=
  progressionLeaf _ _ _ 19 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_36_17 : Progression productA 36 17 :=
  progressionLeaf _ _ _ 37 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_36_35 : Progression productA 36 35 :=
  progressionLeaf _ _ _ 109 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockA_18_17 : Progression productA 18 17 :=
  split2 blockA_36_17 blockA_36_35

private theorem blockA_6_5 : Progression productA 6 5 :=
  split3 blockA_18_5 blockA_18_11 blockA_18_17

private theorem blockA_2_1 : Progression productA 2 1 :=
  split3 blockA_6_1 blockA_6_3 blockA_6_5

private theorem blockA_1_0 : Progression productA 1 0 :=
  split2 blockA_2_0 blockA_2_1

private def productB : ℕ := 5775853299681451668894958980930700538410348146299420324286304259569769292417933544248200692693632090158473360293233441817380118681

private theorem blockB_140_0 : Progression productB 140 0 :=
  progressionLeaf _ _ _ 7416361 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_140_28 : Progression productB 140 28 :=
  progressionLeaf _ _ _ 122921 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_140_56 : Progression productB 140 56 :=
  progressionLeaf _ _ _ 86171 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_140_84 : Progression productB 140 84 :=
  progressionLeaf _ _ _ 281 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_140_112 : Progression productB 140 112 :=
  progressionLeaf _ _ _ 71 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_28_0 : Progression productB 28 0 :=
  split5 blockB_140_0 blockB_140_28 blockB_140_56 blockB_140_84 blockB_140_112

private theorem blockB_224_4 : Progression productB 224 4 :=
  progressionLeaf _ _ _ 2689 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_224_116 : Progression productB 224 116 :=
  progressionLeaf _ _ _ 449 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_112_4 : Progression productB 112 4 :=
  split2 blockB_224_4 blockB_224_116

private theorem blockB_112_60 : Progression productB 112 60 :=
  progressionLeaf _ _ _ 5153 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_56_4 : Progression productB 56 4 :=
  split2 blockB_112_4 blockB_112_60

private theorem blockB_56_32 : Progression productB 56 32 :=
  progressionLeaf _ _ _ 15790321 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_28_4 : Progression productB 28 4 :=
  split2 blockB_56_4 blockB_56_32

private theorem blockB_84_8 : Progression productB 84 8 :=
  progressionLeaf _ _ _ 5419 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_84_36 : Progression productB 84 36 :=
  progressionLeaf _ _ _ 1429 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_84_64 : Progression productB 84 64 :=
  progressionLeaf _ _ _ 337 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_28_8 : Progression productB 28 8 :=
  split3 blockB_84_8 blockB_84_36 blockB_84_64

private theorem blockB_28_12 : Progression productB 28 12 :=
  progressionLeaf _ _ _ 127 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_28_16 : Progression productB 28 16 :=
  progressionLeaf _ _ _ 113 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_28_20 : Progression productB 28 20 :=
  progressionLeaf _ _ _ 43 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_28_24 : Progression productB 28 24 :=
  progressionLeaf _ _ _ 29 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_4_0 : Progression productB 4 0 :=
  split7 blockB_28_0 blockB_28_4 blockB_28_8 blockB_28_12 blockB_28_16 blockB_28_20 blockB_28_24

private theorem blockB_264_2 : Progression productB 264 2 :=
  progressionLeaf _ _ _ 599479 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_26 : Progression productB 264 26 :=
  progressionLeaf _ _ _ 312709 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_50 : Progression productB 264 50 :=
  progressionLeaf _ _ _ 20857 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_74 : Progression productB 264 74 :=
  progressionLeaf _ _ _ 7393 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_98 : Progression productB 264 98 :=
  progressionLeaf _ _ _ 2113 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_122 : Progression productB 264 122 :=
  progressionLeaf _ _ _ 683 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_146 : Progression productB 264 146 :=
  progressionLeaf _ _ _ 397 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_170 : Progression productB 264 170 :=
  progressionLeaf _ _ _ 353 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_194 : Progression productB 264 194 :=
  progressionLeaf _ _ _ 89 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_218 : Progression productB 264 218 :=
  progressionLeaf _ _ _ 67 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_264_242 : Progression productB 264 242 :=
  progressionLeaf _ _ _ 23 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_24_2 : Progression productB 24 2 :=
  split11 blockB_264_2 blockB_264_26 blockB_264_50 blockB_264_74 blockB_264_98 blockB_264_122 blockB_264_146 blockB_264_170 blockB_264_194 blockB_264_218 blockB_264_242

private theorem blockB_288_10 : Progression productB 288 10 :=
  progressionLeaf _ _ _ 6337 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_288_154 : Progression productB 288 154 :=
  progressionLeaf _ _ _ 1153 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_144_10 : Progression productB 144 10 :=
  split2 blockB_288_10 blockB_288_154

private theorem blockB_144_82 : Progression productB 144 82 :=
  progressionLeaf _ _ _ 577 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_72_10 : Progression productB 72 10 :=
  split2 blockB_144_10 blockB_144_82

private theorem blockB_72_34 : Progression productB 72 34 :=
  progressionLeaf _ _ _ 38737 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_72_58 : Progression productB 72 58 :=
  progressionLeaf _ _ _ 433 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_24_10 : Progression productB 24 10 :=
  split3 blockB_72_10 blockB_72_34 blockB_72_58

private theorem blockB_48_18 : Progression productB 48 18 :=
  progressionLeaf _ _ _ 673 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_48_42 : Progression productB 48 42 :=
  progressionLeaf _ _ _ 97 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_24_18 : Progression productB 24 18 :=
  split2 blockB_48_18 blockB_48_42

private theorem blockB_8_2 : Progression productB 8 2 :=
  split3 blockB_24_2 blockB_24_10 blockB_24_18

private theorem blockB_64_6 : Progression productB 64 6 :=
  progressionLeaf _ _ _ 6700417 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_64_38 : Progression productB 64 38 :=
  progressionLeaf _ _ _ 641 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_32_6 : Progression productB 32 6 :=
  split2 blockB_64_6 blockB_64_38

private theorem blockB_32_22 : Progression productB 32 22 :=
  progressionLeaf _ _ _ 65537 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_16_6 : Progression productB 16 6 :=
  split2 blockB_32_6 blockB_32_22

private theorem blockB_16_14 : Progression productB 16 14 :=
  progressionLeaf _ _ _ 257 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_8_6 : Progression productB 8 6 :=
  split2 blockB_16_6 blockB_16_14

private theorem blockB_4_2 : Progression productB 4 2 :=
  split2 blockB_8_2 blockB_8_6

private theorem blockB_2_0 : Progression productB 2 0 :=
  split2 blockB_4_0 blockB_4_2

private theorem blockB_2_1 : Progression productB 2 1 :=
  progressionLeaf _ _ _ 3 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem blockB_1_0 : Progression productB 1 0 :=
  split2 blockB_2_0 blockB_2_1

private theorem cover (n : ℕ) : ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a*b ∣ 2^n+H ∧ a*b < H := by
  obtain ⟨a, ha, ha', haP, had⟩ := blockA_1_0 n
  obtain ⟨b, hb, hb', hbP, hbd⟩ := blockB_1_0 n
  simp only [one_mul, Nat.add_zero] at had hbd
  have hab := Nat.Coprime.of_dvd haP hbP (by decide : Nat.Coprime productA productB)
  exact ⟨a, b, ha, hb, hab.mul_dvd_of_dvd_of_dvd had hbd,
    (Nat.mul_le_mul ha' hb').trans_lt (by decide)⟩

private theorem semiprime_at_offset (n : ℕ) :
    (2^n + OeisA114137.a n).IsSemiprime := by
  let s : Set ℕ := {t | 2^n < t ∧ t.IsSemiprime ∧ Odd t}
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (2^n + 3)
  have hodd : Odd p := hprime.odd_of_ne_two ((show 2 < p from lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 2 < 3) (Nat.le_add_left 3 _)) hp).ne')
  have hs : s.Nonempty :=
    ⟨p^2, by nlinarith [Nat.le_mul_self p], hprime.sq_isAlmostPrime_two,
      hodd.pow⟩
  have ht : 2^n < sInf s ∧ (sInf s).IsSemiprime ∧ Odd (sInf s) := csInf_mem hs
  change (2^n + (sInf s - 2^n)).IsSemiprime
  rw [Nat.add_sub_of_le ht.1.le]
  exact ht.2.1

private theorem not_semiprime_of_factors {a b t : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hd : a*b ∣ t) (hlt : a*b < t) : ¬ t.IsSemiprime := by
  obtain ⟨c, rfl⟩ := hd
  have hc : 1 < c := by
    by_contra! h
    interval_cases c <;> simp_all
  intro hsemi
  have h := hsemi.2
  rw [ArithmeticFunction.cardFactors_mul (by positivity : a*b ≠ 0) (by omega),
      ArithmeticFunction.cardFactors_mul (by omega) (by omega)] at h
  have h₁ := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr ha
  have h₂ := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hb
  have h₃ := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hc
  omega

private theorem disproof_of_cover {H : ℕ} (hodd : Odd H)
    (hcover : ∀ n : ℕ, ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a*b ∣ 2^n+H ∧ a*b < H) :
    ¬ (type_of% @OeisA114137.conjecture2) := by
  intro hall
  obtain ⟨n, hn⟩ := hall H hodd
  obtain ⟨a,b,ha,hb,hd,hlt⟩ := hcover n
  have hs := semiprime_at_offset n
  rw [hn] at hs
  exact not_semiprime_of_factors ha hb hd (hlt.trans_le (Nat.le_add_left H _)) hs

end OMA

theorem OMA.disproof : ¬ (type_of% @OeisA114137.conjecture2) := by
  apply OMA.disproof_of_cover (H := OMA.H) _ OMA.cover
  exact ⟨OMA.H / 2, by decide⟩
