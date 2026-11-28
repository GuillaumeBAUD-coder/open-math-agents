import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

/-!
## Prime divisors of a unitary perfect number with repeated odd prime 257

Write the unitary-divisor-sum identity as a product over the simple odd primes.
If the exponent of 2 is at least 11, upper estimates for this product force 5
and 7, as well as one of 13, 19, or 31. The factor 5 forces 3. When 13
is present, the four factors from 3, 5, 7 and 13 already multiply to 128/65.
Adding either 19 or 31 then exceeds the required ratio of 2.

What remains is the uniform exponent bound in the two resulting families.
The chain-product estimates use the previously established master_gen,
table_finish_skip, and their ancestor lemmas.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H3_R2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

set_option maxRecDepth 16384 in
theorem close257 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hm : 11 ≤ m) (he : 2 ≤ e) (β : ℕ → ℚ)
    (hBd : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({257} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hnum : (1 + 1 / (2 : ℚ)^11) * ((1+257^2)/(257^2)) *
      ((β 3 * β 7 * β 31 * β 127 * (2048/2047)) * ((257^2/(257^2-3))*(2056/2054))) < 2) :
    False := by
  classical
  have hz : Nat.Prime 257 := by norm_num
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    fun c hc hd => Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hd))
  obtain ⟨L,hLP,hL,hmain⟩ := master_gen hP hK (by positivity) E β hBd h4
  have hleaf : ∀ x ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c = 257 :=
    fun x hx c hc h2 hd => Finset.mem_singleton.mp (hL x hx c hc h2 hd)
  have hpos : ∀ x ∈ L, 0 < β x :=
    fun x hx => lt_of_lt_of_le (by positivity) (hBd x (hLP hx)).1
  have hM : ∏ x ∈ L.filter (fun x => ¬ 257 ∣ x + 1), β x ≤
      β 3 * β 7 * β 31 * β 127 * (2048 / 2047) := by
    apply mersenne_bound
    · exact fun x hx => (hP _ (hLP (Finset.mem_filter.mp hx).1)).1
    · intro x hx
      obtain ⟨hxL,hxn⟩ := Finset.mem_filter.mp hx
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hxn (hleaf x hxL c hc h2 hd ▸ hd))
    · exact fun x hx => ⟨hpos x (Finset.mem_filter.mp hx).1, (hBd x (hLP (Finset.mem_filter.mp hx).1)).2⟩
    · exact h1
  have hZ : ∏ x ∈ L.filter (fun x => 257 ∣ x + 1), β x ≤
      ∏ x ∈ L.filter (fun x => 257 ∣ x + 1), (((x : ℚ) + 1) / ((x : ℚ) - 1)) := by
    exact Finset.prod_le_prod (fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le)
      (fun x hx => (hBd x (hLP (Finset.mem_filter.mp hx).1)).2)
  have hC : 0 ≤ β 3 * β 7 * β 31 * β 127 * (2048 / 2047) := by
    obtain ⟨h3,h7,h31,h127⟩ := h1
    positivity
  refine table_finish_skip (z := 257) (s := 3) hP hz (by norm_num) ?_ hm he hC ?_ ?_
  · intro k hlow hhigh
    interval_cases k <;> norm_num
  · refine ⟨L,hLP,hleaf,hmain.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun x => 257 ∣ x + 1) β, mul_comm]
    exact mul_le_mul hM hZ (Finset.prod_nonneg fun x hx => (hpos x (Finset.mem_filter.mp hx).1).le) hC
  · norm_num at hnum ⊢
    exact hnum

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

-- Every solution with a large 2-component has 5 among its simple prime factors.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem five_mem {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (m+1) * 257 ^ e * ∏ p ∈ P, p)
    (hm : 11 ≤ m) (he : 2 ≤ e) : 5 ∈ P := by
  let weights (p : ℕ) : ℚ :=
    if p = 3 then 4/3 * (12/11 * (44/43 * (401/399))) else
    if p = 7 then 8/7 * (14/13 * (104/103 * (824/822))) else
    if p = 11 then 12/11 * (44/43 * (401/399)) else
    if p = 13 then 14/13 * (104/103 * (824/822)) else
    if p = 31 then 32/31 * (62/61 * (488/486)) else
    if p = 43 then 44/43 * (401/399) else
    if p = 61 then 62/61 * (488/486) else
    if p = 103 then 104/103 * (824/822) else
    ((p : ℚ) + 1) / ((p : ℚ) - 1)

  have weights_bounds {p : ℕ} (hp : 2 ≤ p) :
      1 + 1 / (p : ℚ) ≤ weights p ∧ weights p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    by_cases h3 : p = 3
    · subst p
      norm_num [weights]
    by_cases h7 : p = 7
    · subst p
      norm_num [weights]
    by_cases h11 : p = 11
    · subst p
      norm_num [weights]
    by_cases h13 : p = 13
    · subst p
      norm_num [weights]
    by_cases h31 : p = 31
    · subst p
      norm_num [weights]
    by_cases h43 : p = 43
    · subst p
      norm_num [weights]
    by_cases h61 : p = 61
    · subst p
      norm_num [weights]
    by_cases h103 : p = 103
    · subst p
      norm_num [weights]
    simp only [weights, if_neg h3, if_neg h7, if_neg h11, if_neg h13, if_neg h31, if_neg h43, if_neg h61, if_neg h103]
    exact ⟨one_add_le_B hp, le_rfl⟩

  have table_step {p c : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hc : c.Prime) (h5 : p ≠ 5)
      (h9 : ¬9 ∣ p+1) (hd : c ∣ p+1) (hmin : 3 ∣ p+1 → c ≤ 3)
      (hspec : weights c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1)) :
      (1 + 1 / (c : ℚ)) * weights p ≤ weights c := by
    have hbp := (weights_bounds hp.two_le).2
    by_cases h3 : c = 3
    · subst c
      by_cases he : p = 11
      · subst p
        norm_num [weights]
      have hN : 18 ≤ p := by
        by_contra! hl
        obtain ⟨k, hk⟩ := hd
        have hklt : k < 7 := by omega
        have hp_eq : p = 3*k-1 := by omega
        have ht : ∀ j : Fin 7, let i := 3*(j:ℕ)-1
            i.Prime → i ≠ 2 → i ≠ 5 → ¬9 ∣ i+1 → (3 ∣ i+1 → 3 ≤ 3) → i ≠ 11 → False := by decide +kernel
        rw [hp_eq] at hp h2 h5 h9 hmin  he
        exact ht ⟨k, hklt⟩ hp h2 h5 h9 hmin he
      have hfar := hbp.trans (B_anti (by decide : 2 ≤ 18) hN)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0:ℚ) ≤ 1 + 1 / (3:ℚ))).trans (by norm_num [weights])
    by_cases h7 : c = 7
    · subst c
      by_cases he : p = 13
      · subst p
        norm_num [weights]
      have hN : 24 ≤ p := by
        by_contra! hl
        obtain ⟨k, hk⟩ := hd
        have hklt : k < 4 := by omega
        have hp_eq : p = 7*k-1 := by omega
        have ht : ∀ j : Fin 4, let i := 7*(j:ℕ)-1
            i.Prime → i ≠ 2 → i ≠ 5 → ¬9 ∣ i+1 → (3 ∣ i+1 → 7 ≤ 3) → i ≠ 13 → False := by decide +kernel
        rw [hp_eq] at hp h2 h5 h9 hmin  he
        exact ht ⟨k, hklt⟩ hp h2 h5 h9 hmin he
      have hfar := hbp.trans (B_anti (by decide : 2 ≤ 24) hN)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0:ℚ) ≤ 1 + 1 / (7:ℚ))).trans (by norm_num [weights])
    by_cases h11 : c = 11
    · subst c
      by_cases he : p = 43
      · subst p
        norm_num [weights]
      have hN : 72 ≤ p := by
        by_contra! hl
        obtain ⟨k, hk⟩ := hd
        have hklt : k < 7 := by omega
        have hp_eq : p = 11*k-1 := by omega
        have ht : ∀ j : Fin 7, let i := 11*(j:ℕ)-1
            i.Prime → i ≠ 2 → i ≠ 5 → ¬9 ∣ i+1 → (3 ∣ i+1 → 11 ≤ 3) → i ≠ 43 → False := by decide +kernel
        rw [hp_eq] at hp h2 h5 h9 hmin  he
        exact ht ⟨k, hklt⟩ hp h2 h5 h9 hmin he
      have hfar := hbp.trans (B_anti (by decide : 2 ≤ 72) hN)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0:ℚ) ≤ 1 + 1 / (11:ℚ))).trans (by norm_num [weights])
    by_cases h13 : c = 13
    · subst c
      by_cases he : p = 103
      · subst p
        norm_num [weights]
      have hN : 166 ≤ p := by
        by_contra! hl
        obtain ⟨k, hk⟩ := hd
        have hklt : k < 13 := by omega
        have hp_eq : p = 13*k-1 := by omega
        have ht : ∀ j : Fin 13, let i := 13*(j:ℕ)-1
            i.Prime → i ≠ 2 → i ≠ 5 → ¬9 ∣ i+1 → (3 ∣ i+1 → 13 ≤ 3) → i ≠ 103 → False := by decide +kernel
        rw [hp_eq] at hp h2 h5 h9 hmin  he
        exact ht ⟨k, hklt⟩ hp h2 h5 h9 hmin he
      have hfar := hbp.trans (B_anti (by decide : 2 ≤ 166) hN)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0:ℚ) ≤ 1 + 1 / (13:ℚ))).trans (by norm_num [weights])
    by_cases h31 : c = 31
    · subst c
      by_cases he : p = 61
      · subst p
        norm_num [weights]
      have hN : 99 ≤ p := by
        by_contra! hl
        obtain ⟨k, hk⟩ := hd
        have hklt : k < 4 := by omega
        have hp_eq : p = 31*k-1 := by omega
        have ht : ∀ j : Fin 4, let i := 31*(j:ℕ)-1
            i.Prime → i ≠ 2 → i ≠ 5 → ¬9 ∣ i+1 → (3 ∣ i+1 → 31 ≤ 3) → i ≠ 61 → False := by decide +kernel
        rw [hp_eq] at hp h2 h5 h9 hmin  he
        exact ht ⟨k, hklt⟩ hp h2 h5 h9 hmin he
      have hfar := hbp.trans (B_anti (by decide : 2 ≤ 99) hN)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0:ℚ) ≤ 1 + 1 / (31:ℚ))).trans (by norm_num [weights])
    by_cases h43 : c = 43
    · subst c
      have hN : 400 ≤ p := by
        by_contra! hl
        obtain ⟨k, hk⟩ := hd
        have hklt : k < 10 := by omega
        have hp_eq : p = 43*k-1 := by omega
        have ht : ∀ j : Fin 10, let i := 43*(j:ℕ)-1
            i.Prime → i ≠ 2 → i ≠ 5 → ¬9 ∣ i+1 → (3 ∣ i+1 → 43 ≤ 3) → False := by decide +kernel
        rw [hp_eq] at hp h2 h5 h9 hmin 
        exact ht ⟨k, hklt⟩ hp h2 h5 h9 hmin
      have hfar := hbp.trans (B_anti (by decide : 2 ≤ 400) hN)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0:ℚ) ≤ 1 + 1 / (43:ℚ))).trans (by norm_num [weights])
    by_cases h61 : c = 61
    · subst c
      have hN : 487 ≤ p := by
        by_contra! hl
        obtain ⟨k, hk⟩ := hd
        have hklt : k < 8 := by omega
        have hp_eq : p = 61*k-1 := by omega
        have ht : ∀ j : Fin 8, let i := 61*(j:ℕ)-1
            i.Prime → i ≠ 2 → i ≠ 5 → ¬9 ∣ i+1 → (3 ∣ i+1 → 61 ≤ 3) → False := by decide +kernel
        rw [hp_eq] at hp h2 h5 h9 hmin 
        exact ht ⟨k, hklt⟩ hp h2 h5 h9 hmin
      have hfar := hbp.trans (B_anti (by decide : 2 ≤ 487) hN)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0:ℚ) ≤ 1 + 1 / (61:ℚ))).trans (by norm_num [weights])
    by_cases h103 : c = 103
    · subst c
      have hN : 823 ≤ p := by
        by_contra! hl
        obtain ⟨k, hk⟩ := hd
        have hklt : k < 8 := by omega
        have hp_eq : p = 103*k-1 := by omega
        have ht : ∀ j : Fin 8, let i := 103*(j:ℕ)-1
            i.Prime → i ≠ 2 → i ≠ 5 → ¬9 ∣ i+1 → (3 ∣ i+1 → 103 ≤ 3) → False := by decide +kernel
        rw [hp_eq] at hp h2 h5 h9 hmin 
        exact ht ⟨k, hklt⟩ hp h2 h5 h9 hmin
      have hfar := hbp.trans (B_anti (by decide : 2 ≤ 823) hN)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0:ℚ) ≤ 1 + 1 / (103:ℚ))).trans (by norm_num [weights])
    exact (hspec (by simp [weights, h3, h7, h11, h13, h31, h43, h61, h103])).elim


  by_contra h5
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257}: Finset ℕ) := fun c hc hd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc (by norm_num)).mp (hc.dvd_of_dvd_pow hd))
  obtain ⟨_, _, _, _, _, hsquare, _, _⟩ := facts hP hK E
  apply close257 hP E hm he weights (fun p hp => weights_bounds (hP p hp).1.two_le)
  · intro p hp c hc hd hmin hspec
    apply table_step (hP p hp).1 (hP p hp).2 (hP c hc).1 (fun h => h5 (h ▸ hp)) _ hd _ hspec
    · exact hsquare 3 Nat.prime_three (by decide) (by decide) p hp
    · exact hmin 3 Nat.prime_three (by decide) (by decide)
  · norm_num [weights]
  · norm_num [weights]

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

set_option maxRecDepth 4096 in
theorem five_requires_seven {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hm : 11 ≤ m) (he : 2 ≤ e) (h5 : 5 ∈ P) : 7 ∈ P := by
  by_contra h7
  let fiveWeights (p : ℕ) : ℚ :=
    if p = 3 then (4 / 3) * ((6 / 5) * (20 / 18))
    else if p = 5 then (6 / 5) * (20 / 18)
    else if p = 7 then 1
    else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have fiveWeights_bounds {p : ℕ} (hp : 2 ≤ p) (h7 : p ≠ 7) :
      1 + 1 / (p : ℚ) ≤ fiveWeights p ∧
        fiveWeights p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    by_cases h3 : p = 3
    · subst p
      norm_num [fiveWeights]
    by_cases h5 : p = 5
    · subst p
      norm_num [fiveWeights]
    simp only [fiveWeights, if_neg h3, if_neg h5, if_neg h7]
    exact ⟨one_add_le_B hp, le_rfl⟩
  have fiveWeights_transfer {p c : ℕ} (hp : p ∈ P) (hc : c ∈ P)
      (hd : c ∣ p + 1)
      (hne : fiveWeights c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1)) :
      (1 + 1 / (c : ℚ)) * fiveWeights p ≤ fiveWeights c := by
    have hc7 : c ≠ 7 := fun h => h7 (h ▸ hc)
    by_cases hc3 : c = 3
    · subst c
      have hz : Nat.Prime 257 := by norm_num1
      have hK : ∀ d : ℕ, d.Prime → d ∣ 257 ^ e → d ∈ ({257} : Finset ℕ) :=
        fun d h hd' => Finset.mem_singleton.mpr
          ((Nat.prime_dvd_prime_iff_eq h hz).mp (h.dvd_of_dvd_pow hd'))
      obtain ⟨-, -, huniq, -, -, -, -⟩ := facts hP hK E
      have heq : p = 5 := huniq 3 Nat.prime_three (by norm_num) (by simp) p hp 5 h5 hd (by decide)
      subst p
      norm_num [fiveWeights]
    by_cases hc5 : c = 5
    · subst c
      have h19 : 19 ≤ p := by
        by_contra! hl
        have small : ∀ i : Fin 19, (i : ℕ).Prime → ¬5 ∣ (i : ℕ) + 1 := by decide
        exact small ⟨p, hl⟩ (hP p hp).1 hd
      have hwt := (fiveWeights_bounds (hP p hp).1.two_le (fun h => h7 (h ▸ hp))).2
      have hfar := hwt.trans (B_anti (by decide : 2 ≤ 19) h19)
      exact (mul_le_mul_of_nonneg_left hfar (by positivity : (0 : ℚ) ≤ 1 + 1 / (5 : ℚ))).trans
        (by norm_num [fiveWeights])
    exact (hne (by simp [fiveWeights, hc3, hc5, hc7])).elim
  apply close257 hP E hm he fiveWeights
  · intro p hp
    exact fiveWeights_bounds (hP p hp).1.two_le (fun h => h7 (h ▸ hp))
  · intro p hp c hc hd _ hne
    exact fiveWeights_transfer hp hc hd hne
  · norm_num [fiveWeights]
  · norm_num [fiveWeights]

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

theorem support_mem_of_balance {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
      2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p)
    (hm : 11 ≤ m) (he : 2 ≤ e) : 13 ∈ P ∨ 19 ∈ P ∨ 31 ∈ P := by
  let supportWeights (p : ℕ) : ℚ :=
    if p = 3 then 4/3*(6/5*(80/78)) else
    if p = 5 then 6/5*(80/78) else
    if p = 7 then 8/7*(98/96) else
    if p = 31 then 1 else ((p : ℚ) + 1) / ((p : ℚ) - 1)

  have support_bounds {p : ℕ} (hp : 2 ≤ p) (hp31 : p ≠ 31) :
      1+1/(p:ℚ) ≤ supportWeights p ∧ supportWeights p ≤ ((p:ℚ)+1)/((p:ℚ)-1) := by
    by_cases h3 : p = 3
    · subst p
      norm_num [supportWeights]
    by_cases h5 : p = 5
    · subst p
      norm_num [supportWeights]
    by_cases h7 : p = 7
    · subst p
      norm_num [supportWeights]
    simp only [supportWeights, if_neg h3, if_neg h5, if_neg h7, if_neg hp31]
    exact ⟨one_add_le_B hp, le_rfl⟩

  have support_step {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp31 : p ≠ 31)
      (hp13 : p ≠ 13) (hp19 : p ≠ 19) (hc31 : c ≠ 31)
      (hd : c ∣ p+1) (hmin : 3 ∣ p+1 → c ≤ 3)
      (hs : supportWeights c ≠ ((c : ℚ)+1)/((c : ℚ)-1)) :
      (1+1/(c : ℚ))*supportWeights p ≤ supportWeights c := by
    have hb := (support_bounds hp.two_le hp31).2
    by_cases h3 : c = 3
    · subst c
      by_cases he : p = 5
      · subst p
        norm_num [supportWeights]
      have hn : 11 ≤ p := by
        by_contra! hl
        have hx : ∀ i : Fin 11, (i:ℕ).Prime → (i:ℕ) ≠ 2 → (i:ℕ) ≠ 5 → 3 ∣ (i:ℕ)+1 → False := by decide +kernel
        exact hx ⟨p,hl⟩ hp hp2 he hd
      have hu := hb.trans (B_anti (by decide : 2 ≤ 11) hn)
      exact (mul_le_mul_of_nonneg_left hu (by positivity : (0:ℚ) ≤ 1+1/(3:ℚ))).trans (by norm_num [supportWeights])
    by_cases h5 : c = 5
    · subst c
      have hn : 79 ≤ p := by
        by_contra! hl
        have hx : ∀ i : Fin 79, (i:ℕ).Prime → (i:ℕ) ≠ 19 → 5 ∣ (i:ℕ)+1 →
            (3 ∣ (i:ℕ)+1 → 5 ≤ 3) → False := by decide +kernel
        exact hx ⟨p,hl⟩ hp hp19 hd hmin
      have hu := hb.trans (B_anti (by decide : 2 ≤ 79) hn)
      exact (mul_le_mul_of_nonneg_left hu (by positivity : (0:ℚ) ≤ 1+1/(5:ℚ))).trans (by norm_num [supportWeights])
    by_cases h7 : c = 7
    · subst c
      have hn : 97 ≤ p := by
        by_contra! hl
        have hx : ∀ i : Fin 97, (i:ℕ).Prime → (i:ℕ) ≠ 13 → 7 ∣ (i:ℕ)+1 →
            (3 ∣ (i:ℕ)+1 → 7 ≤ 3) → False := by decide +kernel
        exact hx ⟨p,hl⟩ hp hp13 hd hmin
      have hu := hb.trans (B_anti (by decide : 2 ≤ 97) hn)
      exact (mul_le_mul_of_nonneg_left hu (by positivity : (0:ℚ) ≤ 1+1/(7:ℚ))).trans (by norm_num [supportWeights])
    exact (hs (by simp [supportWeights,h3,h5,h7,hc31])).elim
  by_contra! hh
  obtain ⟨h13,h19,h31⟩ := hh
  have hne {k : ℕ} (hk : k ∉ P) : ∀ p ∈ P, p ≠ k := fun _ hp h => hk (h ▸ hp)
  apply close257 hP E hm he supportWeights
  · exact fun p hp => support_bounds (hP p hp).1.two_le (hne h31 p hp)
  · intro p hp c hc hd hmin hs
    exact support_step (hP p hp).1 (hP p hp).2 (hne h31 p hp) (hne h13 p hp) (hne h19 p hp)
      (hne h31 c hc) hd (fun h => hmin 3 Nat.prime_three (by decide) (by simp) h) hs
  · norm_num [supportWeights]
  · norm_num [supportWeights]

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1

theorem below_sixty_five {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hz : z.Prime)
    (E : (2^m+1)*(1+z^e)*∏ p ∈ P, (p+1) = 2^(m+1)*z^e*∏ p ∈ P, p)
    (h3 : 3 ∈ P) (h5 : 5 ∈ P) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    {p : ℕ} (hp : p ∈ P) (hp64 : p ≤ 64) : p ∈ ({3,5,7,13} : Finset ℕ) := by
  by_contra hn
  apply lower_kill hP hz E (S := insert p {3,5,7,13})
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [Finset.prod_insert hn, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
    have hp0 : (0:ℚ) < p := by exact_mod_cast (hP p hp).1.pos
    have hle : (p:ℚ) ≤ 64 := by exact_mod_cast hp64
    have hi : (1:ℚ)/64 ≤ 1/(p:ℚ) := by
      rw [div_le_div_iff₀ (by norm_num) hp0]
      simpa using hle
    rw [one_div (p:ℚ)] at hi
    norm_num
    linarith

/-- Bound the exponent in the branch with 13 and without either 19 or 31. -/
def H1 : Prop := ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    n.factorization 257 % 32 = 0 → padicValNat 2 n % 16 = 8 →
    3 ∣ n → 5 ∣ n → 7 ∣ n → 13 ∣ n → ¬19 ∣ n → ¬31 ∣ n →
    padicValNat 2 n ≤ A

/-- Bound the exponent in the branch without 13 where 19 or 31 occurs. -/
def H2 : Prop := ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    n.factorization 257 % 32 = 0 → padicValNat 2 n % 16 = 8 →
    3 ∣ n → 5 ∣ n → 7 ∣ n → ¬13 ∣ n → (19 ∣ n ∨ 31 ∣ n) →
    padicValNat 2 n ≤ A

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

set_option maxHeartbeats 900000 in
theorem combine_prime_families
    (families : ∀ {m e : ℕ} {P : Finset ℕ}, (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
      (2 ^ m + 1) * (1 + 257 ^ e) * ∏ p ∈ P, (p + 1) =
        2 ^ (m + 1) * 257 ^ e * ∏ p ∈ P, p →
      11 ≤ m → 2 ≤ e →
      3 ∈ P ∧ 5 ∈ P ∧ 7 ∈ P ∧
        ((13 ∈ P ∧ 19 ∉ P ∧ 31 ∉ P) ∨ (13 ∉ P ∧ (19 ∈ P ∨ 31 ∈ P)))) :
    H1 → H2 → ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    n.factorization 257 % 32 = 0 → padicValNat 2 n % 16 = 8 →
    padicValNat 2 n ≤ A := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  refine ⟨max 10 (max A B), fun n h hS he32 hm16 => ?_⟩
  by_cases hm : 11 ≤ padicValNat 2 n
  · have hn := h.2.ne'
    have hz : Nat.Prime 257 := by norm_num
    have hzsq := ((hS 257).mpr rfl).2.2
    have he : 2 ≤ n.factorization 257 := (hz.pow_dvd_iff_le_factorization hn).mp hzsq
    have hzmem := Nat.mem_primeFactors.mpr ⟨hz, (dvd_pow_self 257 two_ne_zero).trans hzsq, hn⟩
    have hs : ∀ p ∈ n.primeFactors, p ≠ 2 → p ≠ 257 → n.factorization p = 1 := by
      intro p hp hp2 hpz
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hpos := hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
      by_contra hbad
      exact hpz ((hS p).mp ⟨hprime, hp2, (hprime.pow_dvd_iff_le_factorization hn).mpr (by omega)⟩)
    obtain ⟨hP, E⟩ := kernel_balance_one h hzmem (by decide) hs
    rw [Nat.factorization_def n Nat.prime_two] at E
    obtain ⟨h3, h5, h7, cases⟩ := families hP E hm he
    let P := (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({257} : Finset ℕ))
    have dvd_of_mem {q : ℕ} (hq : q ∈ P) : q ∣ n :=
      Nat.dvd_of_mem_primeFactors (Finset.mem_erase.mp (Finset.mem_filter.mp hq).1).2
    have mem_of_dvd {q : ℕ} (pq : q.Prime) (h2 : q ≠ 2) (hz : q ≠ 257) (hq : q ∣ n) : q ∈ P := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨h2, Nat.mem_primeFactors.mpr ⟨pq, hq, hn⟩⟩,
        fun h => hz (Finset.mem_singleton.mp h)⟩
    rcases cases with ⟨h13, h19, h31⟩ | ⟨h13, hrest⟩
    · exact (hA n h hS he32 hm16 (dvd_of_mem h3) (dvd_of_mem h5) (dvd_of_mem h7)
        (dvd_of_mem h13) (fun d => h19 (mem_of_dvd (by decide) (by decide) (by decide) d))
        (fun d => h31 (mem_of_dvd (by decide) (by decide) (by decide) d))).trans
        ((le_max_left A B).trans (le_max_right _ _))
    · exact (hB n h hS he32 hm16 (dvd_of_mem h3) (dvd_of_mem h5) (dvd_of_mem h7)
        (fun d => h13 (mem_of_dvd (by decide) (by decide) (by decide) d))
        (hrest.imp dvd_of_mem dvd_of_mem)).trans ((le_max_right A B).trans (le_max_right _ _))
  · exact (by omega : padicValNat 2 n ≤ 10).trans (le_max_left _ _)

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1.H3 := by
  apply combine_prime_families
  intro m e P hP E hm he
  have h5 := five_mem hP E hm he
  have h7 := five_requires_seven hP E hm he h5
  have hz : Nat.Prime 257 := by norm_num
  have hK : ∀ c : ℕ, c.Prime → c ∣ 257 ^ e → c ∈ ({257} : Finset ℕ) :=
    fun c hc hd => Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hd))
  have h3 := (facts hP hK E).1 3 Nat.prime_three (by decide) (by decide) 5 h5 (by decide)
  refine ⟨h3, h5, h7, ?_⟩
  by_cases h13 : 13 ∈ P
  · left
    exact ⟨h13, fun h19 => (by decide : 19 ∉ ({3,5,7,13} : Finset ℕ))
      (below_sixty_five hP hz E h3 h5 h7 h13 h19 (by decide)),
      fun h31 => (by decide : 31 ∉ ({3,5,7,13} : Finset ℕ))
      (below_sixty_five hP hz E h3 h5 h7 h13 h31 (by decide))⟩
  · exact Or.inr ⟨h13, (support_mem_of_balance hP E hm he).resolve_left h13⟩


end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1_H2_R1_H3_R2
