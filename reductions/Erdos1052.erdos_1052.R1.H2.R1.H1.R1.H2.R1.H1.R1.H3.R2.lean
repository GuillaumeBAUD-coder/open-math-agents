import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1

-- The path weights and local successor cases below adapt the merged 5^2 odd-exponent proof by @aroth01.
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R2
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main

-- H1 isolates the five-divisible leaves. Such a leaf has q+1 = 2^i 5^j;
-- all of them together consume at most two factors of 5.
def H1 : Prop :=
  ∀ L : Finset ℕ, (∀ q ∈ L, q.Prime ∧ 5 ∣ q + 1 ∧
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5)) →
    (¬ 5 ^ 3 ∣ ∏ q ∈ L, (q + 1)) → ¬ (19 ∈ L ∧ 79 ∈ L) →
    (∏ q ∈ L, (if q = 19 then (800 / 729 : ℚ) else ((q : ℚ) + 1) / ((q : ℚ) - 1))) ≤
      (800 / 729) * (500 / 498)

-- H2 is the remaining balance problem after both factors of 5 have been spent.
def H2 : Prop :=
  ∃ A : ℕ, ∀ m : ℕ, ∀ P : Finset ℕ,
    (∀ p ∈ P, p.Prime ∧ p ≠ 2) → 5 ∉ P → 2 ^ 19 ∣ m →
    3 ∈ P → 7 ∈ P → 13 ∈ P → 19 ∈ P → 79 ∈ P →
    (∀ p ∈ P, 3 ∣ p + 1 → 1000000 ≤ p) →
    (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p →
    m ≤ A

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

theorem core25_data {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : 2 ^ 19 ∣ m) (hmpos : 13 ≤ m) :
    3 ∈ P ∧ (∀ p ∈ P, 3 ∣ p + 1 → 1000000 ≤ p) ∧ 13 ∈ P ∧ 7 ∈ P := by
  obtain ⟨S1, S2, S3, -, -, -, S7, S8⟩ := facts hP (hK5 2) E
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
  have g13 := S7 13 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have g7 := S1 7 (by norm_num) (by norm_num) (by decide) 13 g13 (by norm_num)
  refine ⟨g3, ?_, g13, g7⟩
  intro p hp hpd
  rw [S3 3 Nat.prime_three (by decide) (by decide) p hp q hqP hpd hd3]
  exact hlarge

theorem lift_exp {m r : ℕ} (h : m % 2 ^ r = 0) (hn : m % 2 ^ (r + 1) ≠ 2 ^ r) : m % 2 ^ (r + 1) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  rw [pow_succ] at hn ⊢
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · rw [show 2 ^ r * (2 * s) = 2 ^ r * 2 * s from by ring]
    exact Nat.mul_mod_right _ _
  · exfalso
    apply hn
    rw [show 2 ^ r * (2 * s + 1) = 2 ^ r * 2 * s + 2 ^ r from by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by
      have : 0 < 2 ^ r := by positivity
      omega)

theorem divisibility {m : ℕ} (hm : m % 4 = 0)
    (hs : ∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      m % 2 ^ (r + 1) ≠ 2 ^ r) : 2 ^ 19 ∣ m := by
  have h2 : m % 2 ^ 2 = 0 := hm
  have h3 := lift_exp (r := 2) h2 (hs 2 (by decide))
  have h4 := lift_exp (r := 3) h3 (hs 3 (by decide))
  have h5 := lift_exp (r := 4) h4 (hs 4 (by decide))
  have h6 := lift_exp (r := 5) h5 (hs 5 (by decide))
  have h7 := lift_exp (r := 6) h6 (hs 6 (by decide))
  have h8 := lift_exp (r := 7) h7 (hs 7 (by decide))
  have h9 := lift_exp (r := 8) h8 (hs 8 (by decide))
  have h10 := lift_exp (r := 9) h9 (hs 9 (by decide))
  have h11 := lift_exp (r := 10) h10 (hs 10 (by decide))
  have h12 := lift_exp (r := 11) h11 (hs 11 (by decide))
  have h13 := lift_exp (r := 12) h12 (hs 12 (by decide))
  have h14 := lift_exp (r := 13) h13 (hs 13 (by decide))
  have h15 := lift_exp (r := 14) h14 (hs 14 (by decide))
  have h16 := lift_exp (r := 15) h15 (hs 15 (by decide))
  have h17 := lift_exp (r := 16) h16 (hs 16 (by decide))
  have h18 := lift_exp (r := 17) h17 (hs 17 (by decide))
  have h19 := lift_exp (r := 18) h18 (hs 18 (by decide))
  exact Nat.dvd_of_mod_eq_zero h19

theorem w25_hK : ∀ c : ℕ, c.Prime → c ∣ 5 ^ 2 → c ∈ ({5} : Finset ℕ) := fun c hc hd =>
  Finset.mem_singleton.mpr
    ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_five).mp (hc.dvd_of_dvd_pow hd))

/-- The weights. Along a kept edge `p -> c` (`c` the least odd prime factor of `p + 1` other
than `5`) they satisfy `(1 + 1 / c) * w p ≤ w c`; elsewhere `w x = (x + 1) / (x - 1)`. -/
theorem w25_bw_of_ne {x : ℕ} (h1 : x ≠ 3) (h2 : x ≠ 7) (h3 : x ≠ 13) (h4 : x ≠ 19) (h5 : x ≠ 37)
    (h6 : x ≠ 73) (h7 : x ≠ 31) (h8 : x ≠ 61) (h9 : x ≠ 127) :
    (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) x = ((x : ℚ) + 1) / ((x : ℚ) - 1) := by
  dsimp only
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
    if_neg h9]

theorem w25_bw_big {x : ℕ} (h : 127 < x) : (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
  w25_bw_of_ne (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem w25_bw_special {x : ℕ} (h : (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) x ≠ ((x : ℚ) + 1) / ((x : ℚ) - 1)) :
    x = 3 ∨ x = 7 ∨ x = 13 ∨ x = 19 ∨ x = 37 ∨ x = 73 ∨ x = 31 ∨ x = 61 ∨ x = 127 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hcon
  exact h (w25_bw_of_ne h1 h2 h3 h4 h5 h6 h7 h8 h9)

theorem w25_bw_bounds {p : ℕ} (hp : 2 ≤ p) :
    1 + 1 / (p : ℚ) ≤ (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) p ∧ (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  by_cases h : (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) p = ((p : ℚ) + 1) / ((p : ℚ) - 1)
  · rw [h]
    exact ⟨one_add_le_B hp, le_refl _⟩
  · rcases w25_bw_special h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num

/-- A kept parent beyond `T > 127` carries the default weight, bounded by its value at `T`. -/
theorem w25_step_big {c T p : ℕ} (hT : 127 < T) (hTp : T ≤ p)
    (hnum : (1 + 1 / (c : ℚ)) * (((T : ℚ) + 1) / ((T : ℚ) - 1)) ≤ (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) c) :
    (1 + 1 / (c : ℚ)) * (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) p ≤ (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) c := by
  rw [w25_bw_big (by omega)]
  exact (mul_le_mul_of_nonneg_left (B_anti (by omega) hTp) (by positivity)).trans hnum

/-- The kept parents of `19`: `37`, or at least `151`. -/
theorem w25_next19 {p : ℕ} (hp : p.Prime) (hd : 19 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 19 ≤ c') :
    p = 37 ∨ 151 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 19 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `37`: `73`, or at least `739`. -/
theorem w25_next37 {p : ℕ} (hp : p.Prime) (hd : 37 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 37 ≤ c') :
    p = 73 ∨ 739 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 37 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `73` are at least `1459`. -/
theorem w25_next73 {p : ℕ} (hp : p.Prime) (hd : 73 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 73 ≤ c') :
    1459 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 73 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `31`: `61`, or at least `619`. -/
theorem w25_next31 {p : ℕ} (hp : p.Prime) (hd : 31 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 31 ≤ c') :
    p = 61 ∨ 619 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 31 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `61` are at least `487`. -/
theorem w25_next61 {p : ℕ} (hp : p.Prime) (hd : 61 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 61 ≤ c') :
    487 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 61 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The kept parents of `127` are at least `2539`. -/
theorem w25_next127 {p : ℕ} (hp : p.Prime) (hd : 127 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    2539 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 127 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

/-- The weights are consistent along kept edges. -/
theorem w25_h4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : 2 ^ 19 ∣ m) (hm43 : 43 ≤ m) :
    ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) p ≤ (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ)) c := by
  intro p hp c hc hd hl hne
  obtain ⟨-, -, F3, F4, -, -, F7, F8⟩ := facts hP w25_hK E
  have hpp := (hP p hp).1
  rcases w25_bw_special hne with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact w25_step_big (T := 1000000) (by norm_num) ((core25_data hP E hm (by omega)).2.1 p hp hd) (by norm_num)
  · have h13 : 13 ∈ P := F7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
    obtain rfl : p = 13 :=
      F3 7 (by norm_num) (by norm_num) (by simp) p hp 13 h13 hd (by norm_num)
    norm_num
  · exact absurd hd (F8 13 (by norm_num) (by norm_num) (by simp) (by norm_num) p hp)
  · rcases w25_next19 hpp hd hl with rfl | h
    · norm_num
    · exact w25_step_big (T := 151) (by norm_num) h (by norm_num)
  · rcases w25_next37 hpp hd hl with rfl | h
    · norm_num
    · exact w25_step_big (T := 739) (by norm_num) h (by norm_num)
  · exact w25_step_big (T := 1459) (by norm_num) (w25_next73 hpp hd hl) (by norm_num)
  · rcases w25_next31 hpp hd hl with rfl | h
    · norm_num
    · exact w25_step_big (T := 619) (by norm_num) h (by norm_num)
  · exact w25_step_big (T := 487) (by norm_num) (w25_next61 hpp hd hl) (by norm_num)
  · exact w25_step_big (T := 2539) (by norm_num) (w25_next127 hpp hd hl) (by norm_num)

/-- The ledger of `5`: the numbers `p + 1`, `p` in a subset of `P`, hold at most two factors
`5` between them. -/
theorem w25_ledger {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {T : Finset ℕ} (hT : T ⊆ P) : ¬ 5 ^ 3 ∣ ∏ p ∈ T, (p + 1) := by
  intro h
  have h1 : 5 ^ 3 ∣ ∏ p ∈ P, (p + 1) :=
    h.trans (Finset.prod_dvd_prod_of_subset _ _ (fun x => x + 1) hT)
  have h2 : 5 ^ 3 ∣ 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p := by
    rw [← E]
    exact Dvd.dvd.mul_left h1 _
  have h3 : 5 ^ 2 * 5 ∣ 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
    have e : 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p = 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
    rw [← e]
    exact h2
  have h4 : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h4 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  · obtain ⟨p, hp, h5p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_five.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five (hP p hp).1).mp h5p
    exact h5 (this ▸ hp)

theorem force_pair (hf : H1) {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : 2 ^ 19 ∣ m) (hm43 : 43 ≤ m) : 19 ∈ P ∧ 79 ∈ P := by
  classical
  by_contra hpair
  let β : ℕ → ℚ := (fun x : ℕ => (if x = 3 then (4 / 3) * (1000001 / 999999) else if x = 7 then 16 / 13 else if x = 13 then 14 / 13 else if x = 19 then 800 / 729 else if x = 37 then 760 / 729 else if x = 73 then 740 / 729 else if x = 31 then 256 / 243 else if x = 61 then 248 / 243 else if x = 127 then 1280 / 1269 else ((x : ℚ) + 1) / ((x : ℚ) - 1) : ℚ))
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP w25_hK (by norm_num) E β
    (fun p hp => w25_bw_bounds (hP p hp).1.two_le) (w25_h4 hP E hm hm43)
  have hleaf : ∀ q ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5 := fun q hq c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf q hq c hc h2 hd)
  have hpos : ∀ q ∈ L, 0 < β q := fun q hq =>
    lt_of_lt_of_le (by positivity) (w25_bw_bounds (hP q (hLP hq)).1.two_le).1
  let F := L.filter (fun q => 5 ∣ q + 1)
  have hfL : F ⊆ L := Finset.filter_subset _ _
  have hsum := hf F
    (fun q hq => ⟨(hP _ (hLP (hfL hq))).1, (Finset.mem_filter.mp hq).2, hleaf _ (hfL hq)⟩)
    (w25_ledger hP h5 E (hfL.trans hLP))
    (fun c => hpair ⟨hLP (hfL c.1), hLP (hfL c.2)⟩)
  have h5part : ∏ q ∈ F, β q ≤ (800 / 729) * (500 / 498) := by
    apply le_trans _ hsum
    apply Finset.prod_le_prod
    · intro q hq
      exact (hpos _ (hfL hq)).le
    · intro q hq
      split_ifs with he
      · subst q
        norm_num [β]
      · exact (w25_bw_bounds (hP _ (hLP (hfL hq))).1.two_le).2
  have hMpart : ∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro q hq
      exact (hP q (hLP (Finset.mem_filter.mp hq).1)).1
    · intro q hq
      obtain ⟨hqL, hq5⟩ := Finset.mem_filter.mp hq
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hq5 (hleaf q hqL c hc h2 hd ▸ hd))
    · intro q hq
      have hqL := (Finset.mem_filter.mp hq).1
      exact ⟨hpos q hqL, (w25_bw_bounds (hP q (hLP hqL)).1.two_le).2⟩
    · norm_num [β]
  have hM0 : (0 : ℚ) ≤ ∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), β q :=
    Finset.prod_nonneg fun q hq => (hpos q (Finset.mem_filter.mp hq).1).le
  have hX : (∏ q ∈ L.filter (fun q => 5 ∣ q + 1), β q) *
      (∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), β q) ≤
      ((800 / 729) * (500 / 498)) * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) :=
    mul_le_mul h5part hMpart hM0 (by norm_num)
  rw [Finset.prod_filter_mul_prod_filter_not L (fun q => 5 ∣ q + 1) β] at hX
  have hX0 : (0 : ℚ) ≤ ∏ q ∈ L, β q := Finset.prod_nonneg fun q hq => (hpos q hq).le
  have hpow : (1 : ℚ) / 2 ^ m ≤ 1 / 2 ^ 43 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hm43)
  have hKK : (((1 + 5 ^ 2 : ℕ) : ℚ) / ((5 ^ 2 : ℕ) : ℚ)) = 26 / 25 := by norm_num
  rw [hKK] at hmain
  have h1 : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) * ∏ q ∈ L, β q ≤
      (1 + 1 / 2 ^ 43) * (26 / 25) *
        (((800 / 729) * (500 / 498)) * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := by
    apply mul_le_mul _ hX hX0 (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith
  have h2 : (1 + 1 / (2 : ℚ) ^ 43) * (26 / 25) *
      (((800 / 729) * (500 / 498)) * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) < 2 := by
    norm_num [β]
  linarith



theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1.H3 := by
  rintro hf ⟨A, hA⟩
  refine ⟨A, fun n hn hs he h43 h4 hR _ => ?_⟩
  obtain ⟨hP, h5, E⟩ := setup hn hs
  rw [he] at E
  have hd := divisibility h4 hR
  obtain ⟨h3, hbig, h13, h7⟩ := core25_data hP E hd (by omega)
  obtain ⟨h19, h79⟩ := force_pair hf hP h5 E hd h43
  exact hA _ _ hP h5 hd h3 h7 h13 h19 h79 hbig E

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H3_R2
