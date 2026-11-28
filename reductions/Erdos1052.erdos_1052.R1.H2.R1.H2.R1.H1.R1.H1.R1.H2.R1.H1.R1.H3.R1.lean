import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

/-!
# A reduction of the thin four-prime branch of Erdős problem 1052

Let a be the exponent of 2 in a unitary perfect number. Discounting the
contribution of a repeated prime congruent to 2 modulo 3 in the smooth-number
sum forces every such prime above 117000. This rules out the entire class
a = 16 modulo 32 and the entire class a = 4096 modulo 8192. The path weights
and their local inequalities are adapted from node_E in the merged parent
reduction 24494. The order argument extends the earlier Erdos1052C17
order and odd-period lemmas.

H1 treats the remaining exponents divisible by 64 but not by 2048.
It includes certified exclusions on the odd cofactors when the exponent
has exactly six or seven factors of 2. Related cofactor exclusions appear
on a different branch in pull request 39881. Here the cutoff for repeated
primes supplies the exclusions at 18433 and 19457. H2 treats exponents divisible by
2048. Every prime divisor of 2^a+1 in that branch is at least 163841.
-/

namespace OMA.Erdos1052Thin

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C7
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C9
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C11
  OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.Erdos1052C16
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.Erdos1052C17

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.Erdos1052C19

theorem one_discount {z : ℕ} (hz0 : 25000 ≤ z) (hz1 : z ≤ 117000) (hz2 : z % 3 = 2) :
    (if z % 3 = 1 then 4 / (3 * (z : ℚ) - 4) else 2 / (3 * (z : ℚ) - 2)) + (2 / (3 * 117000) : ℚ) ≤ (4 / 3 * (75000 / 74996) : ℚ) * (1 / (z : ℚ)) := by
  have hl : (25000 : ℚ) ≤ z := by exact_mod_cast hz0
  have hh : (z : ℚ) ≤ 117000 := by exact_mod_cast hz1
  have zw : (if z % 3 = 1 then 4 / (3 * (z : ℚ) - 4) else 2 / (3 * (z : ℚ) - 2)) = 2 / (3 * (z:ℚ) - 2) := by simp [hz2]
  have hw : (if z % 3 = 1 then 4 / (3 * (z : ℚ) - 4) else 2 / (3 * (z : ℚ) - 2)) ≤ ((4 / 3 * (75000 / 74996) : ℚ)/2) / (z:ℚ) := by
    rw [zw, div_le_div_iff₀ (by linarith) (by linarith)]
    norm_num
    linarith
  have hd : (2 / (3 * 117000) : ℚ) ≤ ((4 / 3 * (75000 / 74996) : ℚ)/2) / (z:ℚ) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    norm_num
    linarith
  calc
    _ ≤ (4 / 3 * (75000 / 74996) : ℚ)/2/(z:ℚ) + (4 / 3 * (75000 / 74996) : ℚ)/2/(z:ℚ) := add_le_add hw hd
    _ = _ := by ring

theorem finite_discount {U : Finset ℕ} {z : ℕ}
    (hz0 : 25000 ≤ z) (hz1 : z ≤ 117000) (hz2 : z % 3 = 2)
    (hpos : ∀ u ∈ insert z U, 0 ≤ (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)))
    (hstep : ∀ u ∈ insert z U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ (4 / 3 * (75000 / 74996) : ℚ) * (1 / (u:ℚ)))
    (hrec : ∑ u ∈ insert z U, 1 / (u : ℚ) ≤ 1 / 24999) :
    ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ (4 / 3 * (75000 / 74996) : ℚ) * (1 / 24999) - (2 / (3 * 117000) : ℚ) := by
  let V := insert z U
  have hzV : z ∈ V := Finset.mem_insert_self _ _
  have hUV : U ⊆ V := Finset.subset_insert _ _
  have hw := Finset.sum_le_sum_of_subset_of_nonneg hUV (fun u hu _ => hpos u hu)
  have hsum : (∑ u ∈ V, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2))) + (2 / (3 * 117000) : ℚ) ≤ (4 / 3 * (75000 / 74996) : ℚ) * (1 / 24999) := calc
    _ = ∑ u ∈ V, ((if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) + if u = z then (2 / (3 * 117000) : ℚ) else 0) := by
      simp [Finset.sum_add_distrib, hzV]
    _ ≤ ∑ u ∈ V, (4 / 3 * (75000 / 74996) : ℚ) * (1 / (u:ℚ)) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases he : u = z
      · subst u
        simpa using one_discount hz0 hz1 hz2
      · simpa [he] using hstep u hu
    _ = (4 / 3 * (75000 / 74996) : ℚ) * (∑ u ∈ V, 1 / (u : ℚ)) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by norm_num)
  linarith



theorem smooth_discount {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 25000 ≤ z)
    (hY : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000)
    {z : ℕ} (hzN : z ∈ N) (hz1 : z ≤ 117000) (hz2 : z % 3 = 2) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) :
    ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ (4 / 3 * (75000 / 74996) : ℚ) * (1 / 24999) - (2 / (3 * 117000) : ℚ) := by
  let V := insert z U
  have hV : ∀ u ∈ V, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N := by
    intro u hu
    rcases Finset.mem_insert.mp hu with he | hu
    · subst u
      have hz := (hN z hzN).1
      refine ⟨hz.ne_zero, hz.ne_one, fun r hr hd => ?_⟩
      rwa [(Nat.prime_dvd_prime_iff_eq hr hz).mp hd]
    · exact hU u hu
  have hge : ∀ u ∈ V, 25000 ≤ u := by
    intro u hu
    obtain ⟨h0,h1,hs⟩ := hV u hu
    have := (hN _ (hs _ (Nat.minFac_prime h1) (Nat.minFac_dvd u))).2
    exact this.trans (Nat.minFac_le (Nat.pos_of_ne_zero h0))
  apply finite_discount (hN z hzN).2 hz1 hz2
  · intro u hu
    have hq : (25000 : ℚ) ≤ u := by exact_mod_cast hge u hu
    split <;> exact div_nonneg (by norm_num) (by linarith)
  · intro u hu
    have hh := xw_le (c := 25000) (by norm_num) (hge u hu)
    norm_num at hh ⊢
    exact hh
  · have h1V : 1 ∉ V := fun h => (hV 1 h).2.1 rfl
    have hs := smooth_recip N (fun y hy => (hN y hy).1) (insert 1 V) (fun u hu => by
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
          have := hr.two_le; omega)⟩
      · exact ⟨(hV u hu).1, (hV u hu).2.2⟩)
    rw [Finset.sum_insert h1V] at hs
    simp only [Nat.cast_one, div_one] at hs
    have hp := prod_recip_25000 (fun y hy => (hN y hy).2) hY
    change (∑ u ∈ V, 1 / (u : ℚ)) ≤ _
    linarith


/-- The path bound from sanchan's node_E with the fixed-prime improvement proved above.
The endpoint weights are unchanged. -/

private theorem node_with_discount {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hPN : ∀ p ∈ P, p ∉ N)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (125000 * 5000)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hN25 : ∀ z ∈ N, 25000 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
        4 / 3 * (75000 / 74996) * (1 / 24999) - 2 / (3 * 117000))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 48 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∈ P) (h8191 : 8191 ∈ P)
    (h126 : 126943 ∈ P) (h262 : 262111 ∈ P) (h19423 : 19423 ∉ P) :
    False := by
  obtain ⟨S1, -, S2, -, -, S4b, -, -⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by have := hs 127 h (by norm_num); omega
  have h3967N : 3967 ∉ N := fun h => by have := hN25 3967 h; omega
  have h8191N : 8191 ∉ N := fun h => by have := hN25 8191 h; omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 3967 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3967 h3967 hd (by norm_num)
  have T3967 : ∀ p ∈ P, 3967 ∣ p + 1 → p = 126943 := fun p hp hd =>
    S2 3967 (by norm_num) (by norm_num) h3967N p hp 126943 h126 hd (by decide)
  have T8191 : ∀ p ∈ P, 8191 ∣ p + 1 → p = 262111 := fun p hp hd =>
    S2 8191 (by norm_num) (by norm_num) h8191N p hp 262111 h262 hd (by decide)
  have gap := gap9_8191 hP hN hK hKK1 E m3 m5 m7 m19 m31 h223 h607 h3967 h8191
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      25000 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨
        r = 3967 ∨ r = 8191 ∨ 13215 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hN25 r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3; · exact Or.inl e3
      by_cases e5 : r = 5; · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7; · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19; · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      by_cases e607 : r = 607; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e607))))))
      by_cases e3967 : r = 3967; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3967)))))))
      by_cases e8191 : r = 8191; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e8191))))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (gap r hrP e3 e5 e7 e19 e31 e223 e607 e3967 e8191)))))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) else
      if p = 19 then 20 / 19 * (608 / 607 * (16043010 / 16043008)) else
      if p = 607 then 608 / 607 * (16043010 / 16043008) else
      if p = 7 then 8 / 7 * (224 / 223 * (5893890 / 5893888)) else
      if p = 223 then 224 / 223 * (5893890 / 5893888) else
      if p = 31 then 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) else
      if p = 3967 then 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) else
      if p = 126943 then 126944 / 126943 * (16248704 / 16248702) else
      if p = 127 then 1 else
      if p = 8191 then 8192 / 8191 * (262112 / 262111 * (524222 / 524220)) else
      if p = 262111 then 262112 / 262111 * (524222 / 524220) else
      if p = 131071 then 131072 / 131071 * (4194272 / 4194270) else
      if p = 524287 then 524288 / 524287 * (1048574 / 1048572) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (16043010 / 16043008))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (16043010 / 16043008)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (16043010 / 16043008) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (5893890 / 5893888)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (5893890 / 5893888) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3967 * (126944 / 126943 * (16248704 / 16248702))) := by rw [hβ]; norm_num
  have b3967 : β 3967 = 3968 / 3967 * (126944 / 126943 * (16248704 / 16248702)) := by rw [hβ]; norm_num
  have b126 : β 126943 = 126944 / 126943 * (16248704 / 16248702) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (262112 / 262111 * (524222 / 524220)) := by rw [hβ]; norm_num
  have b262 : β 262111 = 262112 / 262111 * (524222 / 524220) := by rw [hβ]; norm_num
  have b131071 : β 131071 = 131072 / 131071 * (4194272 / 4194270) := by rw [hβ]; norm_num
  have b524287 : β 524287 = 524288 / 524287 * (1048574 / 1048572) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 3967 →
      c ≠ 126943 → c ≠ 127 → c ≠ 8191 → c ≠ 262111 → c ≠ 131071 → c ≠ 524287 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31,
        if_neg e3967, if_neg e126, if_neg e127, if_neg e8191, if_neg e262, if_neg e131,
        if_neg e524]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3; · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5; · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19; · subst e19; rw [b19]; norm_num
    by_cases e607 : p = 607; · subst e607; rw [b607]; norm_num
    by_cases e7 : p = 7; · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223; · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31; · subst e31; rw [b31]; norm_num
    by_cases e3967 : p = 3967; · subst e3967; rw [b3967]; norm_num
    by_cases e126 : p = 126943; · subst e126; rw [b126]; norm_num
    by_cases e127 : p = 127; · subst e127; exact absurd hp h127
    by_cases e8191 : p = 8191; · subst e8191; rw [b8191]; norm_num
    by_cases e262 : p = 262111; · subst e262; rw [b262]; norm_num
    by_cases e131 : p = 131071; · subst e131; rw [b131071]; norm_num
    by_cases e524 : p = 524287; · subst e524; rw [b524287]; norm_num
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterU_48 hP hN hK hKr hNb
    (4 / 3 * (75000 / 74996) * (1 / 24999) - 2 / (3 * 117000))
    (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3; · subst e3; obtain rfl : p = 5 := T3 p hp hd; rw [b3, b5]; norm_num
    by_cases e5 : c = 5; · subst e5; obtain rfl : p = 19 := T5 p hp hd; rw [b5, b19]; norm_num
    by_cases e19 : c = 19; · subst e19; obtain rfl : p = 607 := T19 p hp hd; rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 16043009 ≤ p := T607_16043009 (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
        (fun h => h19423 (h ▸ hp))
        (fun h => by
          have := T8191 9943873 (h ▸ hp) (by decide)
          omega)
      rw [b607]
      exact step_ge (t := 16043009) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7; · subst e7; obtain rfl : p = 223 := T7 p hp hd; rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 5893889 ≤ p := T223_5893889 (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            by_cases e3967 : r = 3967
            · subst e3967; obtain rfl := T3967 p hp hrd; norm_num at hd
            · omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega)
      rw [b223]
      exact step_ge (t := 5893889) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31; · subst e31; obtain rfl : p = 3967 := T31 p hp hd; rw [b31, b3967]; norm_num
    by_cases e3967 : c = 3967; · subst e3967; obtain rfl : p = 126943 := T3967 p hp hd; rw [b3967, b126]; norm_num
    by_cases e126 : c = 126943
    · subst e126
      have hge : 16248703 ≤ p := T126943_13215 (hP p hp).1 hd
        (S4b 126943 (hP 126943 hc).1 (by norm_num) (hPN 126943 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b126]
      exact step_ge (t := 16248703) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127; · subst e127; exact absurd hc h127
    by_cases e8191 : c = 8191; · subst e8191; obtain rfl : p = 262111 := T8191 p hp hd; rw [b8191, b262]; norm_num
    by_cases e262 : c = 262111
    · subst e262
      have hge : 524221 ≤ p := by
        have := two_mul_le (hP 262111 hc).1 (by norm_num) (hP p hp).1 (hP p hp).2 hd
        omega
      rw [b262]
      exact step_ge (t := 524221) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e131 : c = 131071
    · subst e131
      have hge : 4194271 ≤ p := T131071_13215 (hP p hp).1 hd
        (S4b 131071 (hP 131071 hc).1 (by norm_num) (hPN 131071 hc) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd; omega)
      rw [b131071]
      exact step_ge (t := 4194271) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e524 : c = 524287
    · subst e524
      have hge : 1048573 ≤ p := by
        have := two_mul_le (hP 524287 hc).1 (by norm_num) (hP p hp).1 (hP p hp).2 hd
        omega
      rw [b524287]
      exact step_ge (t := 1048573) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e3967 e126 e127 e8191 e262 e131 e524) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b131071]; norm_num
  · rw [b524287]; norm_num
  · rw [b3, b7, b31, b127, b8191, b131071, b524287]; norm_num



private theorem succ_dvd_three {q : ℕ} (h : q % 3 = 2) : 3 ∣ q + 1 := by omega

set_option maxHeartbeats 450000 in
theorem large_twomod3 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hthin : ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000)
    (hge : ∀ z ∈ S, 25000 ≤ z) (hm : 48 ≤ padicValNat 2 n)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h19 : 19 ∣ n) (h31 : 31 ∣ n)
    (h223 : 223 ∣ n) (h607 : 607 ∣ n) (h3967 : 3967 ∣ n) (h8191 : 8191 ∣ n)
    (hn19423 : ¬19423 ∣ n) (h126 : 126943 ∣ n) (hn126 : ¬126943 ^ 2 ∣ n)
    (h262 : 262111 ∣ n) (hn262 : ¬262111 ^ 2 ∣ n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨
      q = 3967 ∨ q = 8191) :
    (∀ z ∈ S, z % 3 = 2 → 117000 < z) ∧
    (∀ q : ℕ, q.Prime → 5 < q → q % 3 = 2 → q ∣ 2 ^ padicValNat 2 n + 1 → 117000 < q) := by
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (le_trans (by norm_num) hm)
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z :=
    fun z hz => ⟨((hS z).mp hz).1, hadm z hz⟩
  have hNb : ∀ z ∈ S, 2100 ≤ z := fun z hz => (by norm_num : 2100 ≤ 25000).trans (hge z hz)
  obtain ⟨K, K', P, hP, hK, hKK1, hKr0, E, hmem⟩ := setup7 h hS h2
  have hPN : ∀ p ∈ P, p ∉ S := fun p hp => ((hmem p).mp hp).2.2.2
  have hKr : (K' : ℚ) / K ≤ 1 + 1 / (125000 * 5000) := hKr0.trans (kk_bound_25000 hge hthin)
  have mem (q : ℕ) (hq : q.Prime) (hqn : q ∣ n) (hne : q ≠ 2) (hlow : q < 25000) : q ∈ P :=
    (hmem q).mpr ⟨hq, hne, hqn, fun hz => absurd (hge q hz) (not_le.mpr hlow)⟩
  have m3 := mem 3 (by norm_num) h3 (by norm_num) (by norm_num)
  have m5 := mem 5 (by norm_num) h5 (by norm_num) (by norm_num)
  have m7 := mem 7 (by norm_num) h7 (by norm_num) (by norm_num)
  have m19 := mem 19 (by norm_num) h19 (by norm_num) (by norm_num)
  have m31 := mem 31 (by norm_num) h31 (by norm_num) (by norm_num)
  have m223 := mem 223 (by norm_num) h223 (by norm_num) (by norm_num)
  have m607 := mem 607 (by norm_num) h607 (by norm_num) (by norm_num)
  have m3967 := mem 3967 (by norm_num) h3967 (by norm_num) (by norm_num)
  have m8191 := mem 8191 (by norm_num) h8191 (by norm_num) (by norm_num)
  have m126 : 126943 ∈ P := (hmem _).mpr ⟨by norm_num, by norm_num, h126,
    fun hz => hn126 ((hS _).mp hz).2.2⟩
  have m262 : 262111 ∈ P := (hmem _).mpr ⟨by norm_num, by norm_num, h262,
    fun hz => hn262 ((hS _).mp hz).2.2⟩
  have m19423 : 19423 ∉ P := fun hp => hn19423 ((hmem _).mp hp).2.2.1
  obtain ⟨_, S5, S2, _⟩ := facts hP hK E
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5 := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 5 m5 hd (by norm_num)
  have T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19 := fun p hp hd =>
    S2 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 19 m19 hd (by norm_num)
  have hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 := by
    intro q hq hlt
    obtain ⟨hqp,hq2,hqn,_⟩ := (hmem q).mp hq
    rcases hsmall q hqp hqn (hlt.trans (by norm_num)) with
      he | he | he | he | he | he | he | he | he | he
    · exact (hq2 he).elim
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
    all_goals exact absurd (he ▸ hlt) (by norm_num)
  have hzbig : ∀ z ∈ S, z % 3 = 2 → 117000 < z := by
    intro z hz hz2
    by_contra! hlt
    exact node_with_discount hP hPN hNS hK hKr hKK1 hNb hge
      (smooth_discount (fun y hy => ⟨(hNS y hy).1, hge y hy⟩) hthin hz hlt hz2)
      E hm T3 T5 hs m3 m5 m7 m19 m31 m223 m607 m3967 m8191 m126 m262 m19423
  refine ⟨hzbig, fun q hq hq5 hq2 hd => ?_⟩
  apply hzbig q _ hq2
  by_contra hN
  have hqP := S5 q hq (ne_of_gt ((by norm_num : 2 < 5).trans hq5)) hN hd
  exact (ne_of_gt hq5) (T3 q hqP (succ_dvd_three hq2))

theorem valuation_residues {a : ℕ} (h16 : 16 ∣ a) (hn32 : a % 64 ≠ 32)
    (large : ∀ q : ℕ, q.Prime → 5 < q → q % 3 = 2 → q ∣ 2^a + 1 → 117000 < q) :
    64 ∣ a ∧ a % 8192 ≠ 4096 := by
  have hmod (d q : ℕ) (he : a % (2*d) = d) (hqd : q ∣ 2^d + 1) : q ∣ 2^a + 1 := by
    have hdiv := Nat.mod_add_div a (2*d)
    rw [he] at hdiv
    have e : a = d*(2*(a/(2*d))+1) := by nlinarith
    rw [e,pow_mul]
    have hodd : Odd (2*(a/(2*d))+1) := ⟨a/(2*d), rfl⟩
    exact hqd.trans (by simpa only [one_pow] using hodd.nat_add_dvd_pow_add_pow (2^d) 1)
  have hbad : a % 32 ≠ 16 := by
    intro ha
    have := large 65537 (by norm_num) (by decide) (by decide)
      (hmod 16 65537 ha (by decide))
    omega
  refine ⟨by omega, ?_⟩
  intro ha
  have hdiv : 114689 ∣ (2:ℕ)^4096 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
    rw [show (4096:ℕ) = 64*64 by decide, pow_mul]
    rw [show (2 : ZMod 114689)^64 = 2484 by reduce_mod_char]
    reduce_mod_char
  have := large 114689 (by norm_num) (by decide) (by decide)
    (hmod 4096 114689 ha hdiv)
  omega



end OMA.Erdos1052Thin

namespace Erdos1052.CofactorCuts

private theorem odd_source {n p c : ℕ} (hn : IsUnitaryPerfect n)
    (hp : p ∈ n.primeFactors) (hc : Odd c) (h : c ∣ p ^ n.factorization p + 1) : c ∣ n := by
  apply hc.coprime_two_right.dvd_of_dvd_mul_left
  rw [← OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul hn]
  exact h.trans (by
    simpa only [Nat.add_comm 1] using Finset.dvd_prod_of_mem (fun r => 1 + r ^ n.factorization r) hp)

private theorem source_at_two {n b m d q : ℕ} (hn : IsUnitaryPerfect n)
    (ha : padicValNat 2 n = b * m) (hm : Odd m) (hd : d ∣ m) (hq : Odd q)
    (hf : (2 ^ (b * d) + 1) % q = 0) : q ∣ n := by
  obtain ⟨k, rfl⟩ := hd
  have hsrc : q ∣ 2 ^ padicValNat 2 n + 1 := by
    rw [ha]
    apply (Nat.dvd_iff_mod_eq_zero.mpr hf).trans
    simpa only [← Nat.mul_assoc, pow_mul, one_pow] using
      (Nat.odd_mul.mp hm).2.nat_add_dvd_pow_add_pow (2 ^ (b * d)) 1
  by_cases h2 : 2 ∣ n
  · apply odd_source hn (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn.2.ne'⟩) hq
    simpa only [Nat.factorization_def n Nat.prime_two] using hsrc
  · rw [padicValNat.eq_zero_of_not_dvd h2] at hsrc
    exact hq.coprime_two_right.dvd_of_dvd_mul_left (hsrc.trans (dvd_mul_right 2 n))

private theorem direct_row {n b m d q : ℕ} (hn : IsUnitaryPerfect n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191)
    (ha : padicValNat 2 n = b * m) (hm : Odd m)
    (hrow : q.Prime ∧ q % 2 = 1 ∧ q < 18369 ∧
      ¬ (q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191) ∧
      (2 ^ (b * d) + 1) % q = 0) : ¬ d ∣ m := by
  obtain ⟨hprime, hodd, hlt, hbad, hrem⟩ := hrow
  intro hd
  exact hbad (hsmall q hprime (source_at_two hn ha hm hd (Nat.odd_iff.mpr hodd) hrem) hlt)

private theorem simple_row {n b m d q r : ℕ} {S : Finset ℕ} (hn : IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (hlarge : ∀ z ∈ S, 25000 ≤ z)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191)
    (ha : padicValNat 2 n = b * m) (hm : Odd m)
    (hrow : q.Prime ∧ r.Prime ∧ q % 2 = 1 ∧ q ≠ 2 ∧ q < 25000 ∧
      (2 ^ (b * d) + 1) % q = 0 ∧ r % 2 = 1 ∧ r < 18369 ∧
      ¬ (r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨ r = 3967 ∨ r = 8191) ∧
      (q + 1) % r = 0) : ¬ d ∣ m := by
  obtain ⟨hq, hr, hqo, hq₂, hql, hqrem, hro, hrl, hbad, hrrem⟩ := hrow
  intro hd
  have hqn := source_at_two hn ha hm hd (Nat.odd_iff.mpr hqo) hqrem
  have hsq : ¬ q ^ 2 ∣ n := fun h =>
    (Nat.not_le_of_lt hql) (hlarge q ((hS q).mpr ⟨hq, hq₂, h⟩))
  have h₁ := (hq.dvd_iff_one_le_factorization hn.2.ne').mp hqn
  have h₂ : ¬ 2 ≤ n.factorization q := fun h => hsq ((hq.pow_dvd_iff_le_factorization hn.2.ne').mpr h)
  have he : n.factorization q = 1 := by omega
  apply hbad (hsmall r hr _ hrl)
  apply odd_source hn (Nat.mem_primeFactors.mpr ⟨hq, hqn, hn.2.ne'⟩) (Nat.odd_iff.mpr hro)
  simpa only [he, pow_one] using Nat.dvd_iff_mod_eq_zero.mpr hrrem

theorem exclude_u6 {n m : ℕ} (hn : IsUnitaryPerfect n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191)
    (ha : padicValNat 2 n = 64 * m) (hm : Odd m) :
    (¬ 3 ∣ m) ∧ (¬ 13 ∣ m) ∧ (¬ 23 ∣ m) ∧ (¬ 31 ∣ m) ∧ (¬ 55 ∣ m) := by
  refine ⟨direct_row (q := 769) hn hsmall ha hm ?_,
    direct_row (q := 3329) hn hsmall ha hm ?_, direct_row (q := 11777) hn hsmall ha hm ?_,
    direct_row (q := 7937) hn hsmall ha hm ?_, direct_row (q := 14081) hn hsmall ha hm ?_⟩ <;>
    exact ⟨by norm_num1, by decide +kernel⟩

theorem exclude_u7 {n m : ℕ} {S : Finset ℕ} (hn : IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (hlarge : ∀ z ∈ S, 25000 ≤ z)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191)
    (ha : padicValNat 2 n = 128 * m) (hm : Odd m) :
    (¬ 7 ∣ m) ∧ (¬ 9 ∣ m) ∧ (¬ 15 ∣ m) ∧ (¬ 19 ∣ m) := by
  refine ⟨direct_row (q := 10753) hn hsmall ha hm ?_,
    simple_row (q := 18433) (r := 13) hn hS hlarge hsmall ha hm ?_,
    direct_row (q := 7681) hn hsmall ha hm ?_,
    simple_row (q := 19457) (r := 23) hn hS hlarge hsmall ha hm ?_⟩
  · exact ⟨by norm_num1, by decide +kernel⟩
  · exact ⟨by norm_num1, by norm_num1, by decide +kernel⟩
  · exact ⟨by norm_num1, by decide +kernel⟩
  · exact ⟨by norm_num1, by norm_num1, by decide +kernel⟩

end Erdos1052.CofactorCuts

namespace UnitaryPrimeCutoff

private lemma minus_one_ne_one {q : ℕ} (hq : 2 < q) :
    (-1 : ZMod q) ≠ 1 := by
  intro h
  have hzero : (2 : ZMod q) = 0 := by linear_combination -h
  have hzero' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast hzero
  have := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 q).mp hzero')
  omega

theorem two_part {q a u : ℕ} (hq : q.Prime) (hq2 : 2 < q)
    (hpow : 2 ^ u ∣ a) (hd : q ∣ 2 ^ a + 1) : 2 ^ (u+1) ∣ q-1 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, rfl⟩ := hpow
  have hzero := (ZMod.natCast_eq_zero_iff (2 ^ (2 ^ u * m) + 1) q).mpr hd
  push_cast at hzero
  have hneg : ((2 : ZMod q) ^ m) ^ 2 ^ u = -1 := by
    rw [← pow_mul, Nat.mul_comm m]
    exact eq_neg_of_add_eq_zero_left hzero
  have horder : orderOf ((2 : ZMod q) ^ m) = 2 ^ (u+1) :=
    orderOf_eq_prime_pow (p := 2) (n := u)
      (by rw [hneg]; exact minus_one_ne_one hq2)
      (by rw [pow_succ, pow_mul, hneg]; norm_num)
  have hnz : (2 : ZMod q) ^ m ≠ 0 := by
    intro h
    rw [h, zero_pow (by positivity)] at hneg
    exact one_ne_zero (neg_eq_zero.mp hneg.symm)
  rw [← horder]
  exact ZMod.orderOf_dvd_card_sub_one hnz

private lemma odd_period {q a c t : ℕ} (hq : 2 < q) (ht : Odd t)
    (hone : (2 ^ c) ^ t % q = 1) (hc : c ∣ a) (hd : q ∣ 2 ^ a + 1) : False := by
  obtain ⟨m, rfl⟩ := hc
  have hzero := (ZMod.natCast_eq_zero_iff (2 ^ (c*m) + 1) q).mpr hd
  push_cast at hzero
  have hneg : (2 : ZMod q) ^ (c*m) = -1 := eq_neg_of_add_eq_zero_left hzero
  have hcast : (((2 ^ c) ^ t : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    rw [ZMod.natCast_eq_natCast_iff', hone, Nat.mod_eq_of_lt (by omega)]
  push_cast at hcast
  have h1 : ((2 : ZMod q) ^ (c*m)) ^ t = 1 := by
    rw [← pow_mul, mul_right_comm, pow_mul, pow_mul, hcast, one_pow]
  rw [hneg, ht.neg_one_pow] at h1
  exact minus_one_ne_one hq h1

private theorem candidates_complete :
    ∀ i : Fin 28, (4096*i.val+1).Prime →
      4096*i.val+1 ∈ ([12289, 40961, 61441, 65537, 86017] : List ℕ) := by
  rintro ⟨i, hi⟩ hp
  change (4096*i+1).Prime at hp
  change 4096*i+1 ∈ ([12289, 40961, 61441, 65537, 86017] : List ℕ)
  interval_cases i <;> first | decide | norm_num at hp

private theorem periods : ∀ q ∈ ([12289, 40961, 61441, 65537, 86017] : List ℕ),
    (2 ^ 2048 : ℕ) ^ 105 % q = 1 := by
  intro q h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply (ZMod.natCast_eq_natCast_iff' _ 1 _).mp
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [← pow_mul]
    reduce_mod_char

theorem least_prime_bound {a q : ℕ} (ha : 0 < a) (h2048 : 2048 ∣ a)
    (hq : q.Prime) (hd : q ∣ 2 ^ a + 1) : 114689 ≤ q := by
  have hq2 : 2 < q := by
    have hne : q ≠ 2 := by
      rintro rfl
      exact absurd ((Nat.dvd_add_right (dvd_pow_self 2 (by omega : a ≠ 0))).mp hd) (by decide)
    have := hq.two_le
    omega
  by_contra! hlt
  have hp : 4096 ∣ q - 1 := two_part (u := 11) hq hq2 h2048 hd
  obtain ⟨i, hi⟩ := hp
  have hi' : i < 28 := by omega
  have heq : 4096*i+1 = q := by omega
  have hmem := candidates_complete ⟨i,hi'⟩ (by simpa only [heq] using hq)
  change 4096*i+1 ∈ ([12289, 40961, 61441, 65537, 86017] : List ℕ) at hmem
  rw [heq] at hmem
  exact odd_period hq2 (by decide : Odd 105) (periods q hmem) h2048 hd

theorem next_prime_bound {a q : ℕ} (ha : 0 < a) (h2048 : 2048 ∣ a)
    (hq : q.Prime) (hd : q ∣ 2 ^ a + 1) (hne : q ≠ 114689) : 163841 ≤ q := by
  have hlow := least_prime_bound ha h2048 hq hd
  by_contra! hhigh
  obtain ⟨i, hi⟩ := two_part (u := 11) hq (by omega) h2048 hd
  change q - 1 = 4096*i at hi
  have heq : q = 4096*i+1 := by omega
  have hilo : 29 ≤ i := by omega
  have hihi : i ≤ 39 := by omega
  have htwo : q = 147457 ∨ q = 151553 := by
    rw [heq] at hq ⊢
    interval_cases i <;> first | decide | norm_num at hq
  rcases htwo with rfl | rfl
  · apply odd_period (by decide) (by decide : Odd 9) _ h2048 hd
    apply (ZMod.natCast_eq_natCast_iff' _ 1 _).mp
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [← pow_mul]
    reduce_mod_char
  · apply odd_period (by decide) (by decide : Odd 37) _ h2048 hd
    apply (ZMod.natCast_eq_natCast_iff' _ 1 _).mp
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [← pow_mul]
    reduce_mod_char

end UnitaryPrimeCutoff

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H3_R1

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → ¬ 19423 ∣ n →
    126943 ∣ n → ¬ 126943 ^ 2 ∣ n → 262111 ∣ n → ¬ 262111 ^ 2 ∣ n →
    131071 ∣ n → ¬ 131071 ^ 2 ∣ n → 524287 ∣ n → ¬ 524287 ^ 2 ∣ n → (∃ z ∈ S, z % 3 = 1) →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191) →
    64 ∣ padicValNat 2 n → ¬ 2048 ∣ padicValNat 2 n →
    (∀ z ∈ S, z % 3 = 2 → 117000 < z) →
    (∀ m : ℕ, padicValNat 2 n = 64*m → Odd m →
      (¬ 3 ∣ m) ∧ (¬ 13 ∣ m) ∧ (¬ 23 ∣ m) ∧ (¬ 31 ∣ m) ∧ (¬ 55 ∣ m)) →
    (∀ m : ℕ, padicValNat 2 n = 128*m → Odd m →
      (¬ 7 ∣ m) ∧ (¬ 9 ∣ m) ∧ (¬ 15 ∣ m) ∧ (¬ 19 ∣ m)) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    31 ∣ n → 223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 → (∀ z ∈ S, 25000 ≤ z) →
    8191 ∣ n → ¬ 7933 ∣ n → ¬ 16381 ∣ n → ¬ 19423 ∣ n →
    126943 ∣ n → ¬ 126943 ^ 2 ∣ n → 262111 ∣ n → ¬ 262111 ^ 2 ∣ n →
    131071 ∣ n → ¬ 131071 ^ 2 ∣ n → 524287 ∣ n → ¬ 524287 ^ 2 ∣ n → (∃ z ∈ S, z % 3 = 1) →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 18369 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 ∨ q = 8191) →
    2048 ∣ padicValNat 2 n → padicValNat 2 n % 8192 ≠ 4096 →
    (∀ z ∈ S, z % 3 = 2 → 117000 < z) →
    (∀ q : ℕ, q.Prime → q ∣ 2 ^ padicValNat 2 n + 1 → 163841 ≤ q) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H3 := by
  rintro ⟨A, low⟩ ⟨B, high⟩
  refine ⟨max A B, ?_⟩
  intro n hn hsq S hS hadm hprod h4 h3 h5 h7 h19 hres h16 hn32 h31 h223 h607 h3967
    h48 hthin hlarge h8191 hn7933 hn16381 hn19423 h126 hn126 h262 hn262 h131 hn131
    h524 hn524 hex hsmall
  obtain ⟨hrepeated, hfactor⟩ := OMA.Erdos1052Thin.large_twomod3 hn hS hadm hthin hlarge h48
    h3 h5 h7 h19 h31 h223 h607 h3967 h8191 hn19423 h126 hn126 h262 hn262 hsmall
  obtain ⟨h64, hresidue⟩ := OMA.Erdos1052Thin.valuation_residues h16 hn32 hfactor
  by_cases h2048 : 2048 ∣ padicValNat 2 n
  · apply le_trans _ (le_max_right A B)
    apply high n hn hsq S hS hadm hprod h3 h5 h7 h19 hres h31 h223 h607 h3967 h48
      hthin hlarge h8191 hn7933 hn16381 hn19423 h126 hn126 h262 hn262 h131 hn131 h524
      hn524 hex hsmall h2048 hresidue hrepeated
    intro q hq hd
    apply UnitaryPrimeCutoff.next_prime_bound (lt_of_lt_of_le (by decide : 0 < 48) h48) h2048 hq hd
    rintro rfl
    exact (by decide : ¬ 117000 < 114689) (hfactor 114689 hq (by decide) (by decide) hd)
  · apply le_trans _ (le_max_left A B)
    apply low n hn hsq S hS hadm hprod h3 h5 h7 h19 hres h31 h223 h607 h3967 h48
      hthin hlarge h8191 hn7933 hn16381 hn19423 h126 hn126 h262 hn262 h131 hn131 h524
      hn524 hex hsmall h64 h2048 hrepeated
    · exact fun m hm hodd => Erdos1052.CofactorCuts.exclude_u6 hn hsmall hm hodd
    · exact fun m hm hodd => Erdos1052.CofactorCuts.exclude_u7 hn hS hlarge hsmall hm hodd

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H3_R1
