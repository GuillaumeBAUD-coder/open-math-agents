import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1.H1.R1.H2.R1
-- Eliminates padicValNat 2 n % 4 = 2 unconditionally via a multi-child rational forest
-- telescope with 3-adic Lagrange weight tau = 28/27, and splits the remaining classes
-- (padicValNat 2 n % 2 = 0, padicValNat 2 n % 16 ≠ 0) into H1 (% 8 = 4) and H2 (% 16 = 8).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1 hiding H1 H2 main

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n → padicValNat 2 n % 8 = 4 →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({268, 284, 316, 388, 412, 428, 436, 452, 508, 548, 604, 628, 652, 724, 788, 892,
      908, 932, 1076, 1084, 1108, 1172, 1324, 1388, 1396, 1468, 1492, 1604, 1636, 1756, 1796,
      1844, 1868, 2188, 2284, 2308, 2348, 2372, 2396, 2428, 2468, 2524, 2564, 2572, 2612, 2636,
      2644, 2692, 2764, 2908, 2932, 2972} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n → padicValNat 2 n % 16 = 8 →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({296, 328, 344, 376, 536, 568, 632, 712, 776, 808, 824, 856, 904, 1048, 1304, 1384,
      1432, 1528, 1544, 1688, 1784, 1816, 1864, 1912, 2056, 2104, 2168, 2216, 2536, 2648,
      2824} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

lemma small_consumers_ok :
    ∀ p ∈ List.range 3500,
      p ≠ 5 → p ≠ 31 → p ≠ 61 → p ≠ 3181 →
      ((List.range 60).all fun d => decide (d < 2 ∨ p ≤ d ∨ p % d ≠ 0)) = true →
      ¬ (5 ∣ p + 1) → ¬ (31 ∣ p + 1) → ¬ (61 ∣ p + 1) →
      (([7, 11, 13, 17, 23, 43, 47, 67, 103, 127, 367, 733, 823] : List ℕ).any fun q => decide (q ∣ p + 1)) = true →
      (([7, 11, 13, 17, 23, 43, 47, 67, 103, 127, 367, 733, 823] : List ℕ).all fun q => decide (¬ (q * q ∣ p + 1))) = true →
      (p + 1) * 27 ^ (if 27 ∣ p + 1 then 3 else if 9 ∣ p + 1 then 2 else if 3 ∣ p + 1 then 1 else 0) *
        (if p = 5 ∨ p = 31 ∨ p = 61 then (1, 1) else if p = 7 then (3683, 3381) else if p = 11 then (773, 755) else if p = 13 then (2372, 2345) else if p = 17 then (64, 63) else if p = 23 then (2368, 2357) else if p = 47 then (376, 375) else if p = 67 then (1072, 1071) else if p = 103 then (2802, 2797) else if p = 367 then (1552, 1549) else if p = 43 ∨ p = 127 ∨ p = 733 ∨ p = 823 then (3501, 3499) else (p, p - 1)).1 *
        ((({7, 11, 13, 17, 23, 43, 47, 67, 103, 127, 367, 733, 823} : Finset ℕ).filter (· ∣ p + 1)).prod
          fun q => (if q = 5 ∨ q = 31 ∨ q = 61 then (1, 1) else if q = 7 then (3683, 3381) else if q = 11 then (773, 755) else if q = 13 then (2372, 2345) else if q = 17 then (64, 63) else if q = 23 then (2368, 2357) else if q = 47 then (376, 375) else if q = 67 then (1072, 1071) else if q = 103 then (2802, 2797) else if q = 367 then (1552, 1549) else if q = 43 ∨ q = 127 ∨ q = 733 ∨ q = 823 then (3501, 3499) else (q, q - 1)).2) ≤
      p * 28 ^ (if 27 ∣ p + 1 then 3 else if 9 ∣ p + 1 then 2 else if 3 ∣ p + 1 then 1 else 0) *
        (if p = 5 ∨ p = 31 ∨ p = 61 then (1, 1) else if p = 7 then (3683, 3381) else if p = 11 then (773, 755) else if p = 13 then (2372, 2345) else if p = 17 then (64, 63) else if p = 23 then (2368, 2357) else if p = 47 then (376, 375) else if p = 67 then (1072, 1071) else if p = 103 then (2802, 2797) else if p = 367 then (1552, 1549) else if p = 43 ∨ p = 127 ∨ p = 733 ∨ p = 823 then (3501, 3499) else (p, p - 1)).2 *
        ((({7, 11, 13, 17, 23, 43, 47, 67, 103, 127, 367, 733, 823} : Finset ℕ).filter (· ∣ p + 1)).prod
          fun q => (if q = 5 ∨ q = 31 ∨ q = 61 then (1, 1) else if q = 7 then (3683, 3381) else if q = 11 then (773, 755) else if q = 13 then (2372, 2345) else if q = 17 then (64, 63) else if q = 23 then (2368, 2357) else if q = 47 then (376, 375) else if q = 67 then (1072, 1071) else if q = 103 then (2802, 2797) else if q = 367 then (1552, 1549) else if q = 43 ∨ q = 127 ∨ q = 733 ∨ q = 823 then (3501, 3499) else (q, q - 1)).1) := by
  decide +kernel

lemma nd_lt900_ok :
    ∀ p ∈ List.range 900, 5 ≤ p →
      let x := if p = 5 ∨ p = 31 ∨ p = 61 then (1, 1)
        else if p = 7 then (3683, 3381)
        else if p = 11 then (773, 755)
        else if p = 13 then (2372, 2345)
        else if p = 17 then (64, 63)
        else if p = 23 then (2368, 2357)
        else if p = 47 then (376, 375)
        else if p = 67 then (1072, 1071)
        else if p = 103 then (2802, 2797)
        else if p = 367 then (1552, 1549)
        else if p = 43 ∨ p = 127 ∨ p = 733 ∨ p = 823 then (3501, 3499)
        else (p, p - 1)
      0 < x.2 ∧ x.2 ≤ x.1 ∧ x.1 * (p - 1) ≤ p * x.2 := by
  decide +kernel

lemma small_pierpont_ok :
    ∀ p ∈ List.range 55,
      5 ≤ p → p ∉ ([5, 7, 11, 17, 23, 31] : List ℕ) →
      3 ∣ p + 1 → ¬ (5 ∣ p + 1) → ¬ (7 ∣ p + 1) →
      ((List.range 10).all fun d => decide (d < 2 ∨ p ≤ d ∨ p % d ≠ 0)) = true →
      p = 47 ∨ p = 53 := by
  decide

lemma kill_mod4_eq_2_core {m : ℕ} {P : Finset ℕ}
    (hm : 262 ≤ m) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * 244 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 243 * ∏ p ∈ P, p)
    (hS1 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 3 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P)
    (hS3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 3 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p')
    (hS6 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 3 → ∀ p ∈ P, ¬ c * c ∣ p + 1)
    (h5no : ∀ p ∈ P, ¬ 5 ∣ p + 1)
    (h61P : 61 ∈ P) (h61no : ∀ p ∈ P, ¬ 61 ∣ p + 1)
    (hbud : ¬ 3 ^ 6 ∣ ∏ p ∈ P, (p + 1))
    (htail : ∀ Q : Finset ℕ, (∀ q ∈ Q, 8191 ≤ q) → (∀ q ∈ Q, ∀ q' ∈ Q, q < q' → 2 * q + 1 ≤ q') →
      ∏ q ∈ Q, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 2048 / 2047)
    (hmers_small : ∀ q k : ℕ, q.Prime → q + 1 = 2 ^ k → q < 8191 → q = 3 ∨ q = 7 ∨ q = 31 ∨ q = 127)
    (htwo_three : ∀ M : ℕ, M ≠ 0 → (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ M → c = 3) → ∃ k j, M = 2 ^ k * 3 ^ j) :
    False := by
  have hp5 : ∀ {p}, p ∈ P → 5 ≤ p := by
    intro p hp
    have hp1 := (hP p hp).1
    have hp2 := (hP p hp).2
    have hp3 : p ≠ 3 := fun h => h3P (h ▸ hp)
    have := hp1.two_le
    by_contra! hlt
    interval_cases p <;> first | omega | (norm_num at hp1)
  have h31no : ∀ p ∈ P, p ≠ 61 → ¬ 31 ∣ p + 1 := fun p hp hne h31 =>
    hne (hS3 31 (by norm_num) (by norm_num) (by norm_num) p hp 61 h61P h31 (by norm_num))
  obtain ⟨Sc, hSc⟩ : ∃ Sc : Finset ℕ, Sc = {7, 11, 13, 17, 23, 43, 47, 67, 103, 127, 367, 733, 823} := ⟨_, rfl⟩
  obtain ⟨Sp, hSp_def⟩ : ∃ Sp : Finset ℕ, Sp = {5, 7, 11, 17, 23, 31, 61, 127} := ⟨_, rfl⟩
  obtain ⟨w3, hw3⟩ : ∃ w3 : ℕ → ℕ, ∀ p, w3 p = if 27 ∣ p + 1 then 3 else if 9 ∣ p + 1 then 2 else if 3 ∣ p + 1 then 1 else 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨nd, hnd⟩ : ∃ nd : ℕ → ℕ × ℕ, ∀ p, nd p =
    if p = 5 ∨ p = 31 ∨ p = 61 then (1, 1)
    else if p = 7 then (3683, 3381)
    else if p = 11 then (773, 755)
    else if p = 13 then (2372, 2345)
    else if p = 17 then (64, 63)
    else if p = 23 then (2368, 2357)
    else if p = 47 then (376, 375)
    else if p = 67 then (1072, 1071)
    else if p = 103 then (2802, 2797)
    else if p = 367 then (1552, 1549)
    else if p = 43 ∨ p = 127 ∨ p = 733 ∨ p = 823 then (3501, 3499)
    else (p, p - 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℚ, ∀ p, α p = ((nd p).1 : ℚ) / ((nd p).2 : ℚ) := ⟨_, fun _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ p, f p = (((p : ℚ) + 1) / (p : ℚ)) * (27 / 28 : ℚ) ^ (w3 p) := ⟨_, fun _ => rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℕ → ℚ, ∀ p, η p =
    if p ∈ Sp then f p * α p
    else if 8191 ≤ p ∧ p + 1 = 2 ^ Nat.log 2 (p + 1) then ((p : ℚ) + 1) / ((p : ℚ) - 1)
    else 1 := ⟨_, fun _ => rfl⟩
  have hnd_props : ∀ {p}, 5 ≤ p → 0 < (nd p).2 ∧ (nd p).2 ≤ (nd p).1 ∧ (nd p).1 * (p - 1) ≤ p * (nd p).2 := by
    intro p hp
    by_cases h900 : p < 900
    · have h := nd_lt900_ok p (List.mem_range.mpr h900) hp
      simpa only [← hnd p] using h
    · have hndp : nd p = (p, p - 1) := by
        rw [hnd, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [hndp]; exact ⟨by omega, by omega, le_rfl⟩
  have hdf_pos : ∀ {p}, 5 ≤ p → 0 < (nd p).2 := fun hp => (hnd_props hp).1
  have hdf_le_nf : ∀ {p}, 5 ≤ p → (nd p).2 ≤ (nd p).1 := fun hp => (hnd_props hp).2.1
  have hnf_le : ∀ {p}, 5 ≤ p → (nd p).1 * (p - 1) ≤ p * (nd p).2 := fun hp => (hnd_props hp).2.2
  have hα1 : ∀ {p}, 5 ≤ p → 1 ≤ α p := fun hp => by
    rw [hα, one_le_div (by exact_mod_cast hdf_pos hp)]; exact_mod_cast hdf_le_nf hp
  have hα_pos : ∀ {p}, 5 ≤ p → 0 < α p := fun hp => lt_of_lt_of_le zero_lt_one (hα1 hp)
  have hα_ub : ∀ {p}, 5 ≤ p → α p ≤ (p : ℚ) / ((p : ℚ) - 1) := fun {p} hp => by
    have hpq : (5 : ℚ) ≤ p := by exact_mod_cast hp
    rw [hα, div_le_div_iff₀ (by exact_mod_cast hdf_pos hp) (by linarith)]
    have h : (((nd p).1 * (p - 1) : ℕ) : ℚ) ≤ ((p * (nd p).2 : ℕ) : ℚ) := by exact_mod_cast hnf_le hp
    push_cast [show 1 ≤ p by omega] at h
    linarith
  have hSc_lb : ∀ {q}, q ∈ Sc → (3501 : ℚ) / 3499 ≤ α q := by
    intro q hq
    rw [hSc] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [hα, hnd]; norm_num
  have hf_pos : ∀ {p}, 5 ≤ p → 0 < f p := fun {p} hp => by
    have : (5 : ℚ) ≤ p := by exact_mod_cast hp
    rw [hf]; positivity
  have hfα_ub : ∀ {p}, 5 ≤ p → f p * α p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := fun {p} hp => by
    have hpq : (5 : ℚ) ≤ p := by exact_mod_cast hp
    have hw : (27 / 28 : ℚ) ^ (w3 p) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h1 : ((p : ℚ) + 1) / (p : ℚ) * (27 / 28 : ℚ) ^ (w3 p) ≤ ((p : ℚ) + 1) / (p : ℚ) * 1 :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    rw [hf]
    calc (((p : ℚ) + 1) / (p : ℚ) * (27 / 28 : ℚ) ^ (w3 p)) * α p
        ≤ (((p : ℚ) + 1) / (p : ℚ) * 1) * ((p : ℚ) / ((p : ℚ) - 1)) :=
          mul_le_mul h1 (hα_ub hp) (hα_pos hp).le (by positivity)
      _ = ((p : ℚ) + 1) / ((p : ℚ) - 1) := by field_simp
  have hη1 : ∀ {p}, 5 ≤ p → 1 ≤ η p := by
    intro p hp
    rw [hη]
    split_ifs with h1 h2
    · rw [hSp_def] at h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · rw [hf, hα, hw3, hnd]; norm_num
    · have : (5 : ℚ) ≤ p := by exact_mod_cast hp
      rw [one_le_div (by linarith)]; linarith
    · exact le_rfl
  have hone_prod : ∀ S : Finset ℕ, (∀ q ∈ S, 1 ≤ α q) → 1 ≤ ∏ q ∈ S, α q := by
    intro S; refine Finset.induction_on S (by simp) fun a s ha ih hs => ?_
    rw [Finset.prod_insert ha]
    have h1 := hs a (Finset.mem_insert_self a s)
    have h2 := ih fun q hq => hs q (Finset.mem_insert_of_mem hq)
    nlinarith
  have hsingle_le : ∀ {p q}, p ∈ P → q ∈ P.filter (· ∣ p + 1) → α q ≤ ∏ q' ∈ P.filter (· ∣ p + 1), α q' := by
    intro p q _ hqC
    have hq5 := hp5 (Finset.mem_filter.mp hqC).1
    rw [← Finset.mul_prod_erase (P.filter (· ∣ p + 1)) α hqC]
    exact le_mul_of_one_le_right (hα_pos hq5).le
      (hone_prod _ fun x hx => hα1 (hp5 (Finset.mem_filter.mp (Finset.mem_of_mem_erase hx)).1))
  -- Local inequality at every p ∈ P
  have hlocal : ∀ p ∈ P, f p * α p ≤ η p * ∏ q ∈ P.filter (· ∣ p + 1), α q := by
    intro p hp
    have hp5' := hp5 hp
    have hC1 : 1 ≤ ∏ q ∈ P.filter (· ∣ p + 1), α q :=
      hone_prod _ fun q hq => hα1 (hp5 (Finset.mem_filter.mp hq).1)
    rw [hη]
    split_ifs with hSp hmers
    · calc f p * α p = (f p * α p) * 1 := (mul_one _).symm
        _ ≤ (f p * α p) * ∏ q ∈ P.filter (· ∣ p + 1), α q :=
          mul_le_mul_of_nonneg_left hC1 (mul_pos (hf_pos hp5') (hα_pos hp5')).le
    · have hpq : (5 : ℚ) ≤ p := by exact_mod_cast hp5'
      have hpos_b : (0 : ℚ) ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := div_nonneg (by linarith) (by linarith)
      calc f p * α p ≤ (((p : ℚ) + 1) / ((p : ℚ) - 1)) * 1 := by rw [mul_one]; exact hfα_ub hp5'
        _ ≤ (((p : ℚ) + 1) / ((p : ℚ) - 1)) * ∏ q ∈ P.filter (· ∣ p + 1), α q :=
          mul_le_mul_of_nonneg_left hC1 hpos_b
    · rw [one_mul]
      by_cases hCemp : P.filter (· ∣ p + 1) = ∅
      · rw [hCemp, Finset.prod_empty]
        have honly3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ p + 1 → c = 3 := by
          intro c hc hc2 hcd
          by_contra hc3
          have hcC : c ∈ P.filter (· ∣ p + 1) := Finset.mem_filter.mpr ⟨hS1 c hc hc2 hc3 p hp hcd, hcd⟩
          rw [hCemp] at hcC; exact Finset.notMem_empty c hcC
        obtain ⟨u, j, huj⟩ := htwo_three (p + 1) (by omega) honly3
        rcases j with _ | j
        · rw [pow_zero, mul_one] at huj
          have hlt8191 : p < 8191 := by
            by_contra hge
            refine hmers ⟨by omega, ?_⟩
            rw [huj, Nat.log_pow (by norm_num)]
          rcases hmers_small p u (hP p hp).1 huj hlt8191 with rfl | rfl | rfl | rfl
          · exact (h3P hp).elim
          · exact (hSp (by rw [hSp_def]; simp)).elim
          · exact (hSp (by rw [hSp_def]; simp)).elim
          · exact (hSp (by rw [hSp_def]; simp)).elim
        · have h3dvd : 3 ∣ p + 1 := ⟨2 ^ u * 3 ^ j, by rw [huj, pow_succ]; ring⟩
          by_cases hp55 : 55 ≤ p
          · have hpq : (55 : ℚ) ≤ p := by exact_mod_cast hp55
            have hw1 : 1 ≤ w3 p := by rw [hw3]; split_ifs <;> omega
            have hwle : (27 / 28 : ℚ) ^ (w3 p) ≤ 27 / 28 := by
              calc (27 / 28 : ℚ) ^ (w3 p) ≤ (27 / 28 : ℚ) ^ 1 :=
                    pow_le_pow_of_le_one (by norm_num) (by norm_num) hw1
                _ = 27 / 28 := pow_one _
            have h1 : ((p : ℚ) + 1) / (p : ℚ) * (27 / 28 : ℚ) ^ (w3 p) ≤ ((p : ℚ) + 1) / (p : ℚ) * (27 / 28) :=
              mul_le_mul_of_nonneg_left hwle (by positivity)
            rw [hf]
            calc (((p : ℚ) + 1) / (p : ℚ) * (27 / 28 : ℚ) ^ (w3 p)) * α p
                ≤ (((p : ℚ) + 1) / (p : ℚ) * (27 / 28)) * ((p : ℚ) / ((p : ℚ) - 1)) :=
                  mul_le_mul h1 (hα_ub hp5') (hα_pos hp5').le (by positivity)
              _ = (((p : ℚ) + 1) / ((p : ℚ) - 1)) * (27 / 28) := by field_simp
              _ ≤ 1 := by rw [div_mul_div_comm, div_le_one (by linarith)]; linarith
          · have hp47_53 : p = 47 ∨ p = 53 := by
              apply small_pierpont_ok p (List.mem_range.mpr (by omega)) hp5'
              · intro hmL
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmL
                rcases hmL with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hSp (by rw [hSp_def]; simp)
              · exact h3dvd
              · exact h5no p hp
              · intro h7; exact absurd (honly3 7 (by norm_num) (by norm_num) h7) (by norm_num)
              · rw [List.all_eq_true]
                intro d _
                simp only [decide_eq_true_eq]
                by_cases hd2 : d < 2
                · exact Or.inl hd2
                · by_cases hpd : p ≤ d
                  · exact Or.inr (Or.inl hpd)
                  · refine Or.inr (Or.inr fun hmod => ?_)
                    have hdvd := Nat.dvd_of_mod_eq_zero hmod
                    rcases (hP p hp).1.eq_one_or_self_of_dvd d hdvd with rfl | rfl <;> omega
            rcases hp47_53 with rfl | rfl <;> · rw [hf, hα, hw3, hnd]; norm_num
      · obtain ⟨q0, hq0C⟩ := Finset.nonempty_iff_ne_empty.mpr hCemp
        by_cases hex : ∃ q ∈ P.filter (· ∣ p + 1), q ∉ Sc
        · obtain ⟨q, hqC, hqSc⟩ := hex
          obtain ⟨hqP, hqdvd⟩ := Finset.mem_filter.mp hqC
          have hq5 := hp5 hqP
          have hp61 : p ≠ 61 := fun h => hSp (by subst h; rw [hSp_def]; simp)
          have hq_not5 : q ≠ 5 := fun h => h5no p hp (h ▸ hqdvd)
          have hq_not61 : q ≠ 61 := fun h => h61no p hp (h ▸ hqdvd)
          have hq_not31 : q ≠ 31 := fun h => h31no p hp hp61 (h ▸ hqdvd)
          have hαq : α q = (q : ℚ) / ((q : ℚ) - 1) := by
            rw [hSc] at hqSc
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqSc
            have hndq : nd q = (q, q - 1) := by
              rw [hnd, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            rw [hα, hndq, Nat.cast_sub (by omega)]; norm_num
          have h2q : 2 * q ≤ p + 1 := by
            have h2dvd : 2 ∣ p + 1 := by
              rcases (hP p hp).1.eq_two_or_odd with h2 | hodd
              · exact absurd h2 (hP p hp).2
              · omega
            have hcop : Nat.Coprime 2 q :=
              (Nat.coprime_primes Nat.prime_two (hP q hqP).1).mpr (Ne.symm (hP q hqP).2)
            exact Nat.le_of_dvd (by omega) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2dvd hqdvd)
          have hqq : (5 : ℚ) ≤ q := by exact_mod_cast hq5
          have hpq : (5 : ℚ) ≤ p := by exact_mod_cast hp5'
          have h2qq : 2 * (q : ℚ) ≤ (p : ℚ) + 1 := by exact_mod_cast h2q
          calc f p * α p
              ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := hfα_ub hp5'
            _ ≤ (q : ℚ) / ((q : ℚ) - 1) := by
                rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
            _ = α q := hαq.symm
            _ ≤ ∏ q' ∈ P.filter (· ∣ p + 1), α q' := hsingle_le hp hqC
        · have hex' : ∀ q ∈ P.filter (· ∣ p + 1), q ∈ Sc := fun q hq => by
            by_contra hnq; exact hex ⟨q, hq, hnq⟩
          by_cases hp3500 : 3500 ≤ p
          · have hpq : (3500 : ℚ) ≤ p := by exact_mod_cast hp3500
            calc f p * α p
                ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := hfα_ub hp5'
              _ ≤ 3501 / 3499 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
              _ ≤ α q0 := hSc_lb (hex' q0 hq0C)
              _ ≤ ∏ q' ∈ P.filter (· ∣ p + 1), α q' := hsingle_le hp hq0C
          · have hp61 : p ≠ 61 := fun h => hSp (by subst h; rw [hSp_def]; simp)
            have hp5_ne : p ≠ 5 := fun h => hSp (by subst h; rw [hSp_def]; simp)
            have hp31_ne : p ≠ 31 := fun h => hSp (by subst h; rw [hSp_def]; simp)
            have hp3181 : p ≠ 3181 := by
              rintro rfl
              have h37C : 37 ∈ P.filter (· ∣ 3181 + 1) := Finset.mem_filter.mpr
                ⟨hS1 37 (by norm_num) (by norm_num) (by norm_num) 3181 hp (by norm_num), by norm_num⟩
              have h37Sc := hex' 37 h37C
              rw [hSc] at h37Sc; exact absurd h37Sc (by decide)
            have hQC : Sc.filter (· ∣ p + 1) = P.filter (· ∣ p + 1) := by
              ext q
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hqSc, hqd⟩
                rw [hSc] at hqSc
                have hqp : q.Prime ∧ q ≠ 2 ∧ q ≠ 3 := by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hqSc
                  rcases hqSc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                    norm_num
                exact ⟨hS1 q hqp.1 hqp.2.1 hqp.2.2 p hp hqd, hqd⟩
              · rintro ⟨hqP, hqd⟩
                exact ⟨hex' q (Finset.mem_filter.mpr ⟨hqP, hqd⟩), hqd⟩
            have hnat := small_consumers_ok p (List.mem_range.mpr (by omega))
              hp5_ne hp31_ne hp61 hp3181
              (by
                rw [List.all_eq_true]; intro d _
                simp only [decide_eq_true_eq]
                by_cases hd2 : d < 2; · exact Or.inl hd2
                by_cases hpd : p ≤ d; · exact Or.inr (Or.inl hpd)
                refine Or.inr (Or.inr fun hmod => ?_)
                rcases (hP p hp).1.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with rfl | rfl <;> omega)
              (h5no p hp) (h31no p hp hp61) (h61no p hp)
              (by
                rw [List.any_eq_true]
                have hq0Sc := hex' q0 hq0C
                rw [hSc] at hq0Sc
                have hq0d := (Finset.mem_filter.mp hq0C).2
                refine ⟨q0, ?_, decide_eq_true hq0d⟩
                simp only [Finset.mem_insert, Finset.mem_singleton] at hq0Sc
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                exact hq0Sc)
              (by
                rw [List.all_eq_true]; intro q hqL
                simp only [decide_eq_true_eq]
                have hqp : q.Prime ∧ q ≠ 2 ∧ q ≠ 3 := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hqL
                  rcases hqL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                    norm_num
                exact hS6 q hqp.1 hqp.2.1 hqp.2.2 p hp)
            have hnat' : (p + 1) * 27 ^ (w3 p) * (nd p).1 * (∏ q ∈ Sc.filter (· ∣ p + 1), (nd q).2) ≤
                p * 28 ^ (w3 p) * (nd p).2 * (∏ q ∈ Sc.filter (· ∣ p + 1), (nd q).1) := by
              simpa only [← hw3, ← hnd, ← hSc] using hnat
            rw [hQC] at hnat'
            have hq_rat : ((((p + 1) * 27 ^ (w3 p) * (nd p).1 * ∏ q ∈ P.filter (· ∣ p + 1), (nd q).2 : ℕ) : ℚ)) ≤
                (((p * 28 ^ (w3 p) * (nd p).2 * ∏ q ∈ P.filter (· ∣ p + 1), (nd q).1 : ℕ) : ℚ)) := by exact_mod_cast hnat'
            push_cast at hq_rat
            have hQdf_pos : (0 : ℚ) < ∏ q ∈ P.filter (· ∣ p + 1), ((nd q).2 : ℚ) :=
              Finset.prod_pos fun q hq => by
                exact_mod_cast hdf_pos (hp5 (Finset.mem_filter.mp hq).1)
            have hp_pos : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
            have hdfp_pos : (0 : ℚ) < (nd p).2 := by exact_mod_cast hdf_pos hp5'
            have h28_pos : (0 : ℚ) < (28 : ℚ) ^ (w3 p) := by positivity
            have hprod_eq : ∏ q ∈ P.filter (· ∣ p + 1), α q =
                (∏ q ∈ P.filter (· ∣ p + 1), ((nd q).1 : ℚ)) / (∏ q ∈ P.filter (· ∣ p + 1), ((nd q).2 : ℚ)) := by
              rw [← Finset.prod_div_distrib]
              exact Finset.prod_congr rfl fun q _ => hα q
            rw [hprod_eq, hf, hα, div_pow, div_mul_div_comm, div_mul_div_comm,
              div_le_div_iff₀ (by positivity) hQdf_pos]
            linarith
  -- Global forest telescope
  have hdisj : (P : Set ℕ).PairwiseDisjoint (fun p => P.filter (· ∣ p + 1)) := by
    intro p₁ hp₁ p₂ hp₂ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    obtain ⟨hqP, hqd₁⟩ := Finset.mem_filter.mp hq₁
    have hqd₂ := (Finset.mem_filter.mp hq₂).2
    have hq3 : q ≠ 3 := fun h => h3P (h ▸ hqP)
    exact hne (hS3 q (hP q hqP).1 (hP q hqP).2 hq3 p₁ hp₁ p₂ hp₂ hqd₁ hqd₂)
  have hbiU : ∏ p ∈ P, ∏ q ∈ P.filter (· ∣ p + 1), α q ≤ ∏ q ∈ P, α q := by
    rw [← Finset.prod_biUnion hdisj]
    refine Finset.prod_le_prod_of_subset_of_one_le
      (Finset.biUnion_subset.mpr fun p _ q hq => (Finset.mem_filter.mp hq).1)
      (fun q hq => ?_)
      (fun q hq _ => hα1 (hp5 hq))
    rcases Finset.mem_biUnion.mp hq with ⟨_, _, hqF⟩
    exact (hα_pos (hp5 (Finset.mem_filter.mp hqF).1)).le
  have hPα_pos : 0 < ∏ p ∈ P, α p := Finset.prod_pos fun p hp => hα_pos (hp5 hp)
  have htele : ∏ p ∈ P, f p ≤ ∏ p ∈ P, η p := by
    have h1 : (∏ p ∈ P, f p) * (∏ p ∈ P, α p) ≤ (∏ p ∈ P, η p) * (∏ p ∈ P, α p) := by
      calc (∏ p ∈ P, f p) * (∏ p ∈ P, α p)
          = ∏ p ∈ P, (f p * α p) := Finset.prod_mul_distrib.symm
        _ ≤ ∏ p ∈ P, (η p * ∏ q ∈ P.filter (· ∣ p + 1), α q) :=
          Finset.prod_le_prod (fun p hp => (mul_pos (hf_pos (hp5 hp)) (hα_pos (hp5 hp))).le) hlocal
        _ = (∏ p ∈ P, η p) * ∏ p ∈ P, ∏ q ∈ P.filter (· ∣ p + 1), α q := Finset.prod_mul_distrib
        _ ≤ (∏ p ∈ P, η p) * (∏ p ∈ P, α p) :=
          mul_le_mul_of_nonneg_left hbiU (Finset.prod_nonneg fun p hp => (lt_of_lt_of_le zero_lt_one (hη1 (hp5 hp))).le)
    exact le_of_mul_le_mul_right h1 hPα_pos
  -- Explicit values on Sp
  have hv5 : η 5 = 81 / 70 := by rw [hη, if_pos (by rw [hSp_def]; simp), hf, hα, hw3, hnd]; norm_num
  have hv7 : η 7 = 29464 / 23667 := by rw [hη, if_pos (by rw [hSp_def]; simp), hf, hα, hw3, hnd]; norm_num
  have hv11 : η 11 = 62613 / 58135 := by rw [hη, if_pos (by rw [hSp_def]; simp), hf, hα, hw3, hnd]; norm_num
  have hv17 : η 17 = 5832 / 5831 := by rw [hη, if_pos (by rw [hSp_def]; simp), hf, hα, hw3, hnd]; norm_num
  have hv23 : η 23 = 383616 / 379477 := by rw [hη, if_pos (by rw [hSp_def]; simp), hf, hα, hw3, hnd]; norm_num
  have hv31 : η 31 = 32 / 31 := by rw [hη, if_pos (by rw [hSp_def]; simp), hf, hα, hw3, hnd]; norm_num
  have hv61 : η 61 = 62 / 61 := by rw [hη, if_pos (by rw [hSp_def]; simp), hf, hα, hw3, hnd]; norm_num
  have hv127 : η 127 = 448128 / 444373 := by rw [hη, if_pos (by rw [hSp_def]; simp), hf, hα, hw3, hnd]; norm_num
  have hSp_val : ∏ p ∈ Sp, η p = (81 / 70) * (29464 / 23667) * (62613 / 58135) * (5832 / 5831) *
      (383616 / 379477) * (32 / 31) * (62 / 61) * (448128 / 444373) := by
    rw [hSp_def]
    repeat rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_singleton, hv5, hv7, hv11, hv17, hv23, hv31, hv61, hv127]
    ring
  -- Bound ∏ p ∈ P, η p
  have hsplit := Finset.prod_filter_mul_prod_filter_not P (· ∈ Sp) η
  have hSp_prod : ∏ p ∈ P.filter (· ∈ Sp), η p ≤ ∏ p ∈ Sp, η p :=
    Finset.prod_le_prod_of_subset_of_one_le
      (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p hp => (lt_of_lt_of_le zero_lt_one (hη1 (hp5 (Finset.mem_filter.mp hp).1))).le)
      (fun p hp _ => by
        rw [hSp_def] at hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact hη1 (by norm_num))
  obtain ⟨Mtail, hMtail⟩ : ∃ Mtail : Finset ℕ,
      Mtail = (P.filter (· ∉ Sp)).filter (fun p => 8191 ≤ p ∧ p + 1 = 2 ^ Nat.log 2 (p + 1)) := ⟨_, rfl⟩
  have hrest_eq : ∏ p ∈ P.filter (· ∉ Sp), η p = ∏ p ∈ Mtail, (((p : ℚ) + 1) / ((p : ℚ) - 1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (P.filter (· ∉ Sp)) (fun p => 8191 ≤ p ∧ p + 1 = 2 ^ Nat.log 2 (p + 1)) η, ← hMtail]
    have h1 : ∏ p ∈ Mtail, η p = ∏ p ∈ Mtail, (((p : ℚ) + 1) / ((p : ℚ) - 1)) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [hMtail] at hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      have hnSp := (Finset.mem_filter.mp hp1).2
      rw [hη, if_neg hnSp, if_pos hp2]
    have h2 : ∏ p ∈ (P.filter (· ∉ Sp)).filter (fun p => ¬ (8191 ≤ p ∧ p + 1 = 2 ^ Nat.log 2 (p + 1))), η p = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      have hnSp := (Finset.mem_filter.mp hp1).2
      rw [hη, if_neg hnSp, if_neg hp2]
    rw [h1, h2, mul_one]
  have hMtail_le : ∏ p ∈ Mtail, (((p : ℚ) + 1) / ((p : ℚ) - 1)) ≤ 2048 / 2047 := by
    refine htail Mtail (fun q hq => by rw [hMtail] at hq; exact (Finset.mem_filter.mp hq).2.1)
      (fun q hq q' hq' hlt => ?_)
    rw [hMtail] at hq hq'
    obtain ⟨_, _, hu⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, _, hu'⟩ := Finset.mem_filter.mp hq'
    set u := Nat.log 2 (q + 1)
    set u' := Nat.log 2 (q' + 1)
    have huu : u + 1 ≤ u' := by
      by_contra hcon
      have : 2 ^ u' ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ (u + 1) ≤ 2 ^ u' := Nat.pow_le_pow_right (by norm_num) huu
    rw [pow_succ] at this; omega
  have hη_tot : ∏ p ∈ P, η p ≤ ((81 / 70) * (29464 / 23667) * (62613 / 58135) * (5832 / 5831) *
      (383616 / 379477) * (32 / 31) * (62 / 61) * (448128 / 444373)) * (2048 / 2047) := by
    rw [← hsplit, hrest_eq, ← hSp_val]
    refine mul_le_mul hSp_prod hMtail_le
      (Finset.prod_nonneg fun p hp => ?_)
      (by rw [hSp_val]; norm_num)
    rw [hMtail] at hp
    have : (8191 : ℚ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    exact div_nonneg (by linarith) (by linarith)
  -- 3-adic budget: ∑ p ∈ P, w3 p ≤ 5
  have hw3_sum : ∑ p ∈ P, w3 p ≤ 5 := by
    by_contra! h6
    apply hbud
    have hd1 : 3 ^ 6 ∣ 3 ^ (∑ p ∈ P, w3 p) := Nat.pow_dvd_pow 3 h6
    rw [← Finset.prod_pow_eq_pow_sum] at hd1
    refine hd1.trans (Finset.prod_dvd_prod_of_dvd (fun p => 3 ^ w3 p) (fun p => p + 1) fun p _ => ?_)
    rw [hw3]
    split_ifs with h27 h9 h3
    · simpa using h27
    · simpa using h9
    · simpa using h3
    · simp
  have hratio_prod : ∏ p ∈ P, (((p : ℚ) + 1) / (p : ℚ)) ≤
      (28 / 27 : ℚ) ^ 5 * (((81 / 70) * (29464 / 23667) * (62613 / 58135) * (5832 / 5831) *
        (383616 / 379477) * (32 / 31) * (62 / 61) * (448128 / 444373)) * (2048 / 2047)) := by
    have heq : ∏ p ∈ P, (((p : ℚ) + 1) / (p : ℚ)) =
        ((28 / 27 : ℚ) ^ (∑ p ∈ P, w3 p)) * ∏ p ∈ P, f p := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [hf, ← mul_assoc, mul_comm ((28 / 27 : ℚ) ^ w3 p), mul_assoc, ← mul_pow]
      norm_num
    rw [heq]
    exact mul_le_mul
      (pow_le_pow_right₀ (by norm_num) hw3_sum)
      (htele.trans hη_tot)
      (Finset.prod_nonneg fun p hp => (hf_pos (hp5 hp)).le)
      (by norm_num)
  -- Balance equation in ℚ
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * (∏ p ∈ P, (((p : ℚ) + 1) / (p : ℚ))) = 243 / 122 := by
    have hPpos : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by have := hp5 hp; exact_mod_cast (show 0 < p by omega)
    have hcast : ((2 : ℚ) ^ m + 1) * 244 * ∏ p ∈ P, ((p : ℚ) + 1) =
        (2 : ℚ) ^ (m + 1) * 243 * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    rw [Finset.prod_div_distrib]
    have h2pos : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hm_pow : 1 + 1 / (2 : ℚ) ^ m ≤ 1 + 1 / (2 : ℚ) ^ 16 := by
    have hle : (2 : ℚ) ^ 16 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    gcongr
  have hfinal : (243 : ℚ) / 122 ≤ (1 + 1 / (2 : ℚ) ^ 16) *
      ((28 / 27 : ℚ) ^ 5 * (((81 / 70) * (29464 / 23667) * (62613 / 58135) * (5832 / 5831) *
        (383616 / 379477) * (32 / 31) * (62 / 61) * (448128 / 444373)) * (2048 / 2047))) := by
    rw [← hEq]
    exact mul_le_mul hm_pow hratio_prod
      (Finset.prod_nonneg fun p hp => by
        have : (5 : ℚ) ≤ p := by exact_mod_cast hp5 hp
        exact div_nonneg (by linarith) (by linarith))
      (by norm_num)
  norm_num at hfinal

lemma sub_d4 :
    ({268, 284, 316, 388, 412, 428, 436, 452, 508, 548, 604, 628, 652, 724, 788, 892,
      908, 932, 1076, 1084, 1108, 1172, 1324, 1388, 1396, 1468, 1492, 1604, 1636, 1756, 1796,
      1844, 1868, 2188, 2284, 2308, 2348, 2372, 2396, 2428, 2468, 2524, 2564, 2572, 2612, 2636,
      2644, 2692, 2764, 2908, 2932, 2972} : Finset ℕ) ⊆
    (({262, 268, 274, 278, 284, 296, 298, 302, 314, 316, 326, 328, 334, 344, 346, 358, 362, 376, 382,
      386, 388, 394, 398, 412, 422, 428, 436, 446, 452, 454, 458, 466, 478, 482, 502, 508, 514,
      526, 536, 538, 542, 548, 554, 562, 568, 586, 604, 614, 622, 626} : Finset ℕ) ∪
      ({628, 632, 634, 652, 662, 674, 694, 698, 712, 718, 724, 758, 766, 776, 778, 788, 794, 802, 808,
      818, 824, 838, 842, 856, 862, 866, 878, 892, 898, 904, 908, 914, 922, 932, 934, 958, 974,
      982, 998, 1006, 1018, 1042, 1046, 1048, 1076, 1082, 1084, 1108, 1126, 1138} : Finset ℕ) ∪
      ({1142, 1154, 1172, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294, 1304, 1318, 1324, 1346, 1382,
      1384, 1388, 1396, 1418, 1432, 1438, 1454, 1466, 1468, 1478, 1492, 1502, 1522, 1528, 1544,
      1546, 1574, 1604, 1618, 1622, 1636, 1646, 1654, 1678, 1688, 1698, 1706, 1718, 1726, 1754,
      1756, 1762, 1766, 1784} : Finset ℕ) ∪
      ({1796, 1816, 1822, 1838, 1844, 1858, 1864, 1868, 1874, 1882, 1894, 1912, 1934, 1942, 1982, 1994,
      2018, 2026, 2038, 2056, 2062, 2066, 2098, 2102, 2104, 2126, 2138, 2168, 2174, 2182, 2186,
      2188, 2194, 2206, 2216, 2218, 2234, 2238, 2246, 2284, 2302, 2306, 2308, 2326, 2342, 2348,
      2362, 2372, 2374, 2396} : Finset ℕ) ∪
      ({2402, 2428, 2434, 2446, 2458, 2462, 2468, 2474, 2498, 2518, 2524, 2536, 2554, 2564, 2566, 2572,
      2578, 2582, 2594, 2602, 2606, 2612, 2614, 2636, 2638, 2644, 2648, 2654, 2692, 2722, 2734,
      2762, 2764, 2778, 2798, 2818, 2824, 2846, 2854, 2858, 2878, 2902, 2906, 2908, 2932, 2942,
      2962, 2966, 2972} : Finset ℕ)) := by
  decide +kernel

lemma sub_d8 :
    ({296, 328, 344, 376, 536, 568, 632, 712, 776, 808, 824, 856, 904, 1048, 1304, 1384,
      1432, 1528, 1544, 1688, 1784, 1816, 1864, 1912, 2056, 2104, 2168, 2216, 2536, 2648,
      2824} : Finset ℕ) ⊆
    (({262, 268, 274, 278, 284, 296, 298, 302, 314, 316, 326, 328, 334, 344, 346, 358, 362, 376, 382,
      386, 388, 394, 398, 412, 422, 428, 436, 446, 452, 454, 458, 466, 478, 482, 502, 508, 514,
      526, 536, 538, 542, 548, 554, 562, 568, 586, 604, 614, 622, 626} : Finset ℕ) ∪
      ({628, 632, 634, 652, 662, 674, 694, 698, 712, 718, 724, 758, 766, 776, 778, 788, 794, 802, 808,
      818, 824, 838, 842, 856, 862, 866, 878, 892, 898, 904, 908, 914, 922, 932, 934, 958, 974,
      982, 998, 1006, 1018, 1042, 1046, 1048, 1076, 1082, 1084, 1108, 1126, 1138} : Finset ℕ) ∪
      ({1142, 1154, 1172, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294, 1304, 1318, 1324, 1346, 1382,
      1384, 1388, 1396, 1418, 1432, 1438, 1454, 1466, 1468, 1478, 1492, 1502, 1522, 1528, 1544,
      1546, 1574, 1604, 1618, 1622, 1636, 1646, 1654, 1678, 1688, 1698, 1706, 1718, 1726, 1754,
      1756, 1762, 1766, 1784} : Finset ℕ) ∪
      ({1796, 1816, 1822, 1838, 1844, 1858, 1864, 1868, 1874, 1882, 1894, 1912, 1934, 1942, 1982, 1994,
      2018, 2026, 2038, 2056, 2062, 2066, 2098, 2102, 2104, 2126, 2138, 2168, 2174, 2182, 2186,
      2188, 2194, 2206, 2216, 2218, 2234, 2238, 2246, 2284, 2302, 2306, 2308, 2326, 2342, 2348,
      2362, 2372, 2374, 2396} : Finset ℕ) ∪
      ({2402, 2428, 2434, 2446, 2458, 2462, 2468, 2474, 2498, 2518, 2524, 2536, 2554, 2564, 2566, 2572,
      2578, 2582, 2594, 2602, 2606, 2612, 2614, 2636, 2638, 2644, 2648, 2654, 2692, 2722, 2734,
      2762, 2764, 2778, 2798, 2818, 2824, 2846, 2854, 2858, 2878, 2902, 2906, 2908, 2932, 2942,
      2962, 2966, 2972} : Finset ℕ)) := by
  decide +kernel

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hiff he hlo hpar h16 hs hf => ?_⟩
  have hcases : padicValNat 2 n % 4 = 2 ∨ padicValNat 2 n % 8 = 4 ∨ padicValNat 2 n % 16 = 8 := by
    omega
  rcases hcases with hm4 | hm8 | hm16
  · exfalso
    have hn0 : n ≠ 0 := h.2.ne'
    have hsimple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
      intro r hr hr2 hr3
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
      have : ¬ 2 ≤ n.factorization r := fun he' =>
        hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
      omega
    have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
    have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
    have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
    obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hsimple
    have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
    rw [he, ha] at E
    have E' : (2 ^ padicValNat 2 n + 1) * 244 *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)), (p + 1) =
        2 ^ (padicValNat 2 n + 1) * 243 *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)), p := by
      simpa only [show 1 + 3 ^ 5 = 244 by norm_num, show 3 ^ 5 = 243 by norm_num] using E
    have hK : ∀ c : ℕ, c.Prime → c ∣ 243 → c ∈ ({3} : Finset ℕ) := fun c hc hd => by
      have hd' : c ∣ 3 ^ 5 := by simpa using hd
      exact Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd'))
    obtain ⟨S1, -, S3, S4, -, S6, S7, S8⟩ := facts hP hK E'
    have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun hc hm => hc (Finset.mem_singleton.mp hm)
    exact kill_mod4_eq_2_core hlo hP h3P E'
      (fun c hc hc2 hc3 => S1 c hc hc2 (hn3 hc3))
      (fun c hc hc2 hc3 => S3 c hc hc2 (hn3 hc3))
      (fun c hc hc2 hc3 => S6 c hc hc2 (hn3 hc3))
      (S4 5 (by norm_num) (by norm_num) (hn3 (by norm_num)) (five_dvd_two_pow_add_one hm4))
      (S7 61 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num))
      (S8 61 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num))
      (fun h6 => budget_kernel3 hP h3P E (Finset.Subset.refl _) (h6.mul_left _))
      (fun Q hge hdbl => (tail_bound Q.card Q 8191 rfl (by norm_num) hge hdbl).trans (by norm_num))
      (fun _ _ hq hk hlt => mersenne_small hq hk hlt)
      (fun _ hM hc => two_pow_mul_pow_of_odd_primes_eq hM hc)
  · exact (h1 n h hiff he hlo hm8 hs (fun d hd => hf d (sub_d4 hd))).trans (le_max_left _ _)
  · exact (h2 n h hiff he hlo hm16 hs (fun d hd => hf d (sub_d8 hd))).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
