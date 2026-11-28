import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1

-- The weight-tree cases below adapt the merged odd-exponent tree of @adammcarter.
-- Here a source of 3 is allowed: its prime is so large that its path weight
-- adds a factor of at most 1000001/999999 to the weight at 3.
namespace OMA.HighFiveFour
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main


theorem prime_large {m q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hm : 2 ^ 19 ∣ m) (hd : q ∣ 2 ^ m + 1) : 1000000 ≤ q := by
  obtain ⟨k, rfl⟩ := hm
  have hz : (((2 ^ (2 ^ 19 * k) + 1 : ℕ) : ZMod q)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hd
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hz
  rw [Nat.mul_comm (2 ^ 19) k, pow_mul] at hz
  let x := (2 : ZMod q) ^ k
  have hx : x ^ (2 ^ 19 : ℕ) = -1 := by
    change ((2 : ZMod q) ^ k) ^ (2 ^ 19 : ℕ) = -1
    linear_combination hz
  have hn : x ^ (2 ^ 19 : ℕ) ≠ 1 := by
    intro he
    have hzero : ((2 : ℕ) : ZMod q) = 0 := by rw [Nat.cast_ofNat]; linear_combination hx - he
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff _ _).1 hzero))
  have he : x ^ (2 ^ (19 + 1) : ℕ) = 1 := by
    rw [pow_succ (2 : ℕ), pow_mul, hx]
    norm_num
  have ho := orderOf_eq_prime_pow hn he
  have hlt := ZMod.orderOf_lt hq.one_lt x
  rw [ho] at hlt
  norm_num at hlt
  omega

theorem even_core_data {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 2 ^ 19 ∣ m) (hmpos : 13 ≤ m) :
    3 ∈ P ∧ (∀ p ∈ P, 3 ∣ p + 1 → 1000000 ≤ p) ∧ 313 ∈ P ∧ 157 ∈ P ∧ 79 ∈ P ∧ (∀ p ∈ P, ¬ 313 ∣ p + 1) := by
  obtain ⟨S1, S2, S3, -, -, -, S7, S8⟩ := facts hP hK54 E
  have hmod : (2 ^ m + 1) % 3 = 2 := by
    have h2 : 2 ∣ m := dvd_trans (by decide : 2 ∣ 2 ^ 19) hm
    obtain ⟨k, rfl⟩ := h2
    rw [pow_mul]
    have h4 : ∀ j : ℕ, (2 ^ 2) ^ j % 3 = 1 := by
      intro j
      induction j with
      | zero => norm_num
      | succ j hj => rw [pow_succ, Nat.mul_mod, hj]; norm_num
    have := h4 k
    omega
  obtain ⟨q, hq, hd, hq3⟩ := exists_prime_mod3 _ hmod
  have hn2 : q ≠ 2 := by
    rintro rfl
    have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have := (Nat.dvd_add_right h2m).mp hd
    omega
  have hlarge := prime_large hq hn2 hm hd
  have hqP := S2 q hq hn2 (by simp; omega) hd
  have hd3 : 3 ∣ q + 1 := by omega
  have g3 := S1 3 Nat.prime_three (by decide) (by decide) q hqP hd3
  have g313 := S7 313 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have g157 := S1 157 (by norm_num) (by norm_num) (by decide) 313 g313 (by norm_num)
  have g79 := S1 79 (by norm_num) (by norm_num) (by decide) 157 g157 (by norm_num)
  refine ⟨g3, ?_, g313, g157, g79, fun p hp => S8 313 (by norm_num) (by norm_num) (by decide) (by norm_num) p hp⟩
  intro p hp hpd
  rw [S3 3 Nat.prime_three (by decide) (by decide) p hp q hqP hpd hd3]
  exact hlarge

set_option maxHeartbeats 1000000 in
theorem high_node_12 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 488 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (5120 / 4869 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (4960 / 4869 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (1400 / 1389 : ℚ) else if p = 313 then (314 / 313 : ℚ) else if p = 397 then (1393 / 1389 : ℚ) else if p = 487 then (4880 / 4869 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 487 := S3 61 (by norm_num) (by norm_num) (by decide) p hp 487 (hIP 487 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 397 := S3 199 (by norm_num) (by norm_num) (by decide) p hp 397 (hIP 397 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 5557 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 9739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 199 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 61 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 488 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_13 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 488 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (224 / 213 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (217 / 213 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (1400 / 1389 : ℚ) else if p = 313 then (314 / 313 : ℚ) else if p = 397 then (1393 / 1389 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 853 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 397 := S3 199 (by norm_num) (by norm_num) (by decide) p hp 397 (hIP 397 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 5557 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 199 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 488 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_11 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 398 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_409 : 409 ∉ P := fun hq => budget5 hP hP5 E (A := insert 409 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have x_421 : 421 ∉ P := fun hq => absurd (hI 211 (S1 211 (by norm_num) (by norm_num) (by decide) 421 hq (by norm_num)) (by norm_num)) (by simp)
  have x_433 : 433 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 433 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_439 : 439 ∉ P := fun hq => budget5 hP hP5 E (A := insert 439 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have x_457 : 457 ∉ P := fun hq => absurd (hI 229 (S1 229 (by norm_num) (by norm_num) (by decide) 457 hq (by norm_num)) (by norm_num)) (by simp)
  have x_463 : 463 ∉ P := fun hq => by have := h3 29 (S1 29 (by norm_num) (by norm_num) (by decide) 463 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 487 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 398
    · exact hI p hp hpt
    have hge : 398 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 487 ∈ P
  · exact high_node_12 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 487
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 487 := by omega
            subst this
            simp)
  · exact high_node_13 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 487
          · exact hJ p hp h
          · have : p = 487 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_14 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 398 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (3200 / 3183 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 6367 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 32 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 398 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_10 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_211 : 211 ∉ P := fun hq => by have := h3 53 (S1 53 (by norm_num) (by norm_num) (by decide) 211 hq (by norm_num)) (by norm_num); omega
  have x_223 : 223 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 223 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_229 : 229 ∉ P := fun hq => budget5 hP hP5 E (A := insert 229 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have x_241 : 241 ∉ P := fun hq => S6 11 (by norm_num) (by norm_num) (by decide) 241 hq (by norm_num)
  have x_271 : 271 ∉ P := fun hq => by have := h3 17 (S1 17 (by norm_num) (by norm_num) (by decide) 271 hq (by norm_num)) (by norm_num); omega
  have x_277 : 277 ∉ P := fun hq => absurd (hI 139 (S1 139 (by norm_num) (by norm_num) (by decide) 277 hq (by norm_num)) (by norm_num)) (by simp)
  have x_283 : 283 ∉ P := fun hq => by have := h3 71 (S1 71 (by norm_num) (by norm_num) (by decide) 283 hq (by norm_num)) (by norm_num); omega
  have x_307 : 307 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 307 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_331 : 331 ∉ P := fun hq => by have := h3 83 (S1 83 (by norm_num) (by norm_num) (by decide) 331 hq (by norm_num)) (by norm_num); omega
  have x_337 : 337 ∉ P := fun hq => S6 13 (by norm_num) (by norm_num) (by decide) 337 hq (by norm_num)
  have x_349 : 349 ∉ P := fun hq => budget5 hP hP5 E (A := insert 349 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have x_367 : 367 ∉ P := fun hq => by have := h3 23 (S1 23 (by norm_num) (by norm_num) (by decide) 367 hq (by norm_num)) (by norm_num); omega
  have x_373 : 373 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 373 hq (by norm_num)) (by norm_num); omega
  have x_379 : 379 ∉ P := fun hq => budget5 hP hP5 E (A := insert 379 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have hJ : ∀ p ∈ P, p < 397 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 200
    · exact hI p hp hpt
    have hge : 200 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 397 ∈ P
  · exact high_node_11 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 397
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 397 := by omega
            subst this
            simp)
  · exact high_node_14 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 397
          · exact hJ p hp h
          · have : p = 397 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_16 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 488 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (5120 / 4869 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (4960 / 4869 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else if p = 487 then (4880 / 4869 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 487 := S3 61 (by norm_num) (by norm_num) (by decide) p hp 487 (hIP 487 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 9739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 61 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 488 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 488 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (224 / 213 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (217 / 213 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 853 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 488 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_15 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_211 : 211 ∉ P := fun hq => by have := h3 53 (S1 53 (by norm_num) (by norm_num) (by decide) 211 hq (by norm_num)) (by norm_num); omega
  have x_223 : 223 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 223 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_229 : 229 ∉ P := fun hq => by have := h3 23 (S1 23 (by norm_num) (by norm_num) (by decide) 229 hq (by norm_num)) (by norm_num); omega
  have x_241 : 241 ∉ P := fun hq => S6 11 (by norm_num) (by norm_num) (by decide) 241 hq (by norm_num)
  have x_271 : 271 ∉ P := fun hq => by have := h3 17 (S1 17 (by norm_num) (by norm_num) (by decide) 271 hq (by norm_num)) (by norm_num); omega
  have x_277 : 277 ∉ P := fun hq => absurd (hI 139 (S1 139 (by norm_num) (by norm_num) (by decide) 277 hq (by norm_num)) (by norm_num)) (by simp)
  have x_283 : 283 ∉ P := fun hq => by have := h3 71 (S1 71 (by norm_num) (by norm_num) (by decide) 283 hq (by norm_num)) (by norm_num); omega
  have x_307 : 307 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 307 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_331 : 331 ∉ P := fun hq => by have := h3 83 (S1 83 (by norm_num) (by norm_num) (by decide) 331 hq (by norm_num)) (by norm_num); omega
  have x_337 : 337 ∉ P := fun hq => S6 13 (by norm_num) (by norm_num) (by decide) 337 hq (by norm_num)
  have x_349 : 349 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 349 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_367 : 367 ∉ P := fun hq => by have := h3 23 (S1 23 (by norm_num) (by norm_num) (by decide) 367 hq (by norm_num)) (by norm_num); omega
  have x_373 : 373 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 373 hq (by norm_num)) (by norm_num); omega
  have x_379 : 379 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 379 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_397 : 397 ∉ P := fun hq => absurd (hI 199 (S1 199 (by norm_num) (by norm_num) (by decide) 397 hq (by norm_num)) (by norm_num)) (by simp)
  have x_409 : 409 ∉ P := fun hq => by have := h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 409 hq (by norm_num)) (by norm_num); omega
  have x_421 : 421 ∉ P := fun hq => x_211 (S1 211 (by norm_num) (by norm_num) (by decide) 421 hq (by norm_num))
  have x_433 : 433 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 433 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_439 : 439 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 439 hq (by norm_num)) (by norm_num); omega
  have x_457 : 457 ∉ P := fun hq => x_229 (S1 229 (by norm_num) (by norm_num) (by decide) 457 hq (by norm_num))
  have x_463 : 463 ∉ P := fun hq => by have := h3 29 (S1 29 (by norm_num) (by norm_num) (by decide) 463 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 487 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 200
    · exact hI p hp hpt
    have hge : 200 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 487 ∈ P
  · exact high_node_16 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 487
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 487 := by omega
            subst this
            simp)
  · exact high_node_17 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 487
          · exact hJ p hp h
          · have : p = 487 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_9 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => by have := h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num); omega
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 199 ∈ P
  · exact high_node_10 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 199
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 199 := by omega
            subst this
            simp)
  · exact high_node_15 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 199
          · exact hJ p hp h
          · have : p = 199 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (100 / 99 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 397 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_20 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_18 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => by have := h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num); omega
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 199 ∈ P
  · exact high_node_19 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 199
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 199 := by omega
            subst this
            simp)
  · exact high_node_20 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 199
          · exact hJ p hp h
          · have : p = 199 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_8 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_109 : 109 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact high_node_9 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact high_node_18 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_23 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (26 / 21 : ℚ) else if p = 13 then (13 / 12 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (100 / 99 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 337 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 26 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 397 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_24 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (26 / 21 : ℚ) else if p = 13 then (13 / 12 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 337 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 26 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_22 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => by have := h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num); omega
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 199 ∈ P
  · exact high_node_23 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 199
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 199 := by omega
            subst this
            simp)
  · exact high_node_24 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 199
          · exact hJ p hp h
          · have : p = 199 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_25 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => by have := h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num); omega
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (26 / 21 : ℚ) else if p = 13 then (13 / 12 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 199
      · have hpI := hJ p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 337 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 26 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 199
      · have hpI := hJ p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 199
      · have hpI := hJ p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 199 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hJ hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_21 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_109 : 109 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact high_node_22 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact high_node_25 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 74 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_97 : 97 ∉ P := fun hq => S6 7 (by norm_num) (by norm_num) (by decide) 97 hq (by norm_num)
  have hJ : ∀ p ∈ P, p < 103 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 74
    · exact hI p hp hpt
    have hge : 74 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 103 ∈ P
  · exact high_node_8 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 103
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 103 := by omega
            subst this
            simp)
  · exact high_node_21 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 103
          · exact hJ p hp h
          · have : p = 103 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_29 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (100 / 99 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 397 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_30 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_28 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => by have := h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num); omega
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 199 ∈ P
  · exact high_node_29 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 199
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 199 := by omega
            subst this
            simp)
  · exact high_node_30 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 199
          · exact hJ p hp h
          · have : p = 199 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_31 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_27 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_109 : 109 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact high_node_28 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact high_node_31 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_33 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (56 / 45 : ℚ) else if p = 13 then (49 / 45 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 181 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_34 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (56 / 45 : ℚ) else if p = 13 then (49 / 45 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 181 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_32 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_109 : 109 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact high_node_33 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact high_node_34 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_26 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 74 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_97 : 97 ∉ P := fun hq => S6 7 (by norm_num) (by norm_num) (by decide) 97 hq (by norm_num)
  have hJ : ∀ p ∈ P, p < 103 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 74
    · exact hI p hp hpt
    have hge : 74 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 103 ∈ P
  · exact high_node_27 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 103
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 103 := by omega
            subst this
            simp)
  · exact high_node_32 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 103
          · exact hJ p hp h
          · have : p = 103 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_6 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 62 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_67 : 67 ∉ P := fun hq => by have := h3 17 (S1 17 (by norm_num) (by norm_num) (by decide) 67 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 73 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 62
    · exact hI p hp hpt
    have hge : 62 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 73 ∈ P
  · exact high_node_7 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 73
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 73 := by omega
            subst this
            simp)
  · exact high_node_26 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 73
          · exact hJ p hp h
          · have : p = 73 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_38 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_39 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_37 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_109 : 109 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact high_node_38 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact high_node_39 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_41 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (56 / 45 : ℚ) else if p = 13 then (49 / 45 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 181 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_42 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (56 / 45 : ℚ) else if p = 13 then (49 / 45 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 181 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_40 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_109 : 109 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact high_node_41 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact high_node_42 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_36 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 74 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_97 : 97 ∉ P := fun hq => S6 7 (by norm_num) (by norm_num) (by decide) 97 hq (by norm_num)
  have hJ : ∀ p ∈ P, p < 103 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 74
    · exact hI p hp hpt
    have hge : 74 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 103 ∈ P
  · exact high_node_37 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 103
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 103 := by omega
            subst this
            simp)
  · exact high_node_40 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 103
          · exact hJ p hp h
          · have : p = 103 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_43 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 74 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 74
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 74
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 74
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 74 ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) ({127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_35 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 62 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_67 : 67 ∉ P := fun hq => by have := h3 17 (S1 17 (by norm_num) (by norm_num) (by decide) 67 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 73 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 62
    · exact hI p hp hpt
    have hge : 62 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 73 ∈ P
  · exact high_node_36 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 73
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 73 := by omega
            subst this
            simp)
  · exact high_node_43 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 73
          · exact hJ p hp h
          · have : p = 73 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 38 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_43 : 43 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 43 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 61 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 38
    · exact hI p hp hpt
    have hge : 38 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 61 ∈ P
  · exact high_node_6 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 61
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 61 := by omega
            subst this
            simp)
  · exact high_node_35 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 61
          · exact hJ p hp h
          · have : p = 61 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_45 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 62 → p ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 19 then (16 / 15 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 151 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 62 ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) ({127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_46 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 62 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 19 then (16 / 15 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 151 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 62 ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) ({127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_44 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 38 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_43 : 43 ∉ P := fun hq => by have := h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 43 hq (by norm_num)) (by norm_num); omega
  have hJ : ∀ p ∈ P, p < 61 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 38
    · exact hI p hp hpt
    have hge : 38 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 61 ∈ P
  · exact high_node_45 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 61
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 61 := by omega
            subst this
            simp)
  · exact high_node_46 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 61
          · exact hJ p hp h
          · have : p = 61 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 32 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have hJ : ∀ p ∈ P, p < 37 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 32
    · exact hI p hp hpt
    have hge : 32 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 37 ∈ P
  · exact high_node_5 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 37
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 37 := by omega
            subst this
            simp)
  · exact high_node_44 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 37
          · exact hJ p hp h
          · have : p = 37 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_47 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 32 → p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 19 then (10 / 9 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 32
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 32
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 37 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 32 ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 79} : Finset ℕ) ({127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have hJ : ∀ p ∈ P, p < 31 → p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 20
    · exact hI p hp hpt
    have hge : 20 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 31 ∈ P
  · exact high_node_4 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 31
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 31 := by omega
            subst this
            simp)
  · exact high_node_47 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 31
          · exact hJ p hp h
          · have : p = 31 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_48 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 7, 13, 79, 157, 313} : Finset ℕ) ({3, 7, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 1 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 14 → p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have hJ : ∀ p ∈ P, p < 19 → p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 14
    · exact hI p hp hpt
    have hge : 14 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 19 ∈ P
  · exact high_node_3 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 19
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 19 := by omega
            subst this
            simp)
  · exact high_node_48 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 19
          · exact hJ p hp h
          · have : p = 19 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_50 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (7 / 6 : ℚ) else if p = 19 then (10 / 9 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 97 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 37 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 7, 19, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_51 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 7 then (7 / 6 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 97 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 7, 79, 157, 313} : Finset ℕ) ({3, 7, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 1 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_49 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 14 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have hJ : ∀ p ∈ P, p < 19 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 14
    · exact hI p hp hpt
    have hge : 14 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 19 ∈ P
  · exact high_node_50 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 19
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 19 := by omega
            subst this
            simp)
  · exact high_node_51 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 19
          · exact hJ p hp h
          · have : p = 19 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 7, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 8 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have hJ : ∀ p ∈ P, p < 13 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 8
    · exact hI p hp hpt
    have hge : 8 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 13 ∈ P
  · exact high_node_2 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 13
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 13 := by omega
            subst this
            simp)
  · exact high_node_49 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 13
          · exact hJ p hp h
          · have : p = 13 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_53 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 19, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 19, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 19 then (10 / 9 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 19, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 19, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 37 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 19, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 19, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 19, 79, 157, 313} : Finset ℕ) ({3, 19, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_54 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then ((4 / 3) * (1000001 / 999999) : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl
    · refine step_ge (by norm_num) (h3 p hp hd) (hB p hp).2 ?_
      rw [hβ]
      norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 79, 157, 313} : Finset ℕ) ({3, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 1 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem high_node_52 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 8 → p ∈ ({3, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have x_13 : 13 ∉ P := fun hq => absurd (hI 7 (S1 7 (by norm_num) (by norm_num) (by decide) 13 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 19 → p ∈ ({3, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 8
    · exact hI p hp hpt
    have hge : 8 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 19 ∈ P
  · exact high_node_53 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 19
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 19 := by omega
            subst this
            simp)
  · exact high_node_54 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 19
          · exact hJ p hp h
          · have : p = 19 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem high_node_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m)
    (hIP : ∀ p ∈ ({3, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 3 → p ∈ ({3, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := even_core_data hP E hdiv hm
  have hJ : ∀ p ∈ P, p < 7 → p ∈ ({3, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 3
    · exact hI p hp hpt
    have hge : 3 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 7 ∈ P
  · exact high_node_1 hP hP5 E hm hdiv
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 7
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 7 := by omega
            subst this
            simp)
  · exact high_node_52 hP hP5 E hm hdiv hIP
      (by intro p hp hlt
          by_cases h : p < 7
          · exact hJ p hp h
          · have : p = 7 := by omega
            subst this
            exact absurd hp hc)

theorem high_core {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hdiv : 2 ^ 19 ∣ m) : False := by
  obtain ⟨g3, -, g313, g157, g79, -⟩ := even_core_data hP E hdiv hm
  exact high_node_0 hP hP5 E hm hdiv
    (by intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> assumption)
    (by intro p hp hlt
        have h1 := (hP p hp).1.two_le
        have h2 := (hP p hp).2
        omega)

end OMA.HighFiveFour

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1.H4 := by
  refine ⟨12, fun n hn hs he ha => ?_⟩
  by_contra! h
  obtain ⟨hP, h5, E⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.setup hn hs
  rw [he] at E
  exact OMA.HighFiveFour.high_core hP h5 E (by omega)
    (dvd_trans (by decide : 2 ^ 19 ∣ 2 ^ 33) (Nat.dvd_of_mod_eq_zero ha))
