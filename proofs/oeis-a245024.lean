import OMAStatements.S_oeis_a245024
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a245024

open OMA.S_oeis_a245024

private lemma minFac_eq_three {n : ℕ} (hodd : n % 2 = 1) (h3 : 3 ∣ n) :
    n.minFac = 3 := by
  have hne1 : n ≠ 1 := by omega
  have hpr : n.minFac.Prime := Nat.minFac_prime hne1
  have hle : n.minFac ≤ 3 := Nat.minFac_le_of_dvd (by decide) h3
  have hne2 : n.minFac ≠ 2 := by
    intro h2
    have hd2 : 2 ∣ n := h2 ▸ Nat.minFac_dvd n
    omega
  have hge2 : 2 ≤ n.minFac := hpr.two_le
  omega

private lemma five_le_minFac {n : ℕ} (hne1 : n ≠ 1) (hodd : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    5 ≤ n.minFac := by
  have hpr : n.minFac.Prime := Nat.minFac_prime hne1
  have hd : n.minFac ∣ n := Nat.minFac_dvd n
  have hne2 : n.minFac ≠ 2 := fun h => by rw [h] at hd; omega
  have hne3 : n.minFac ≠ 3 := fun h => by rw [h] at hd; omega
  have hne4 : n.minFac ≠ 4 := fun h => by rw [h] at hpr; exact absurd hpr (by decide)
  have hge2 : 2 ≤ n.minFac := hpr.two_le
  omega

private lemma minFac_eq_five {n : ℕ} (hodd : n % 2 = 1) (h3 : n % 3 ≠ 0) (h5 : 5 ∣ n) :
    n.minFac = 5 := by
  have hne1 : n ≠ 1 := by omega
  have hge : 5 ≤ n.minFac := five_le_minFac hne1 hodd h3
  have hle : n.minFac ≤ 5 := Nat.minFac_le_of_dvd (by decide) h5
  omega

private lemma seven_le_minFac {n : ℕ} (hne1 : n ≠ 1) (hodd : n % 2 = 1)
    (h3 : n % 3 ≠ 0) (h5 : n % 5 ≠ 0) : 7 ≤ n.minFac := by
  have hpr : n.minFac.Prime := Nat.minFac_prime hne1
  have hd : n.minFac ∣ n := Nat.minFac_dvd n
  have hge5 : 5 ≤ n.minFac := five_le_minFac hne1 hodd h3
  have hne5 : n.minFac ≠ 5 := fun h => by rw [h] at hd; omega
  have hne6 : n.minFac ≠ 6 := fun h => by rw [h] at hpr; exact absurd hpr (by decide)
  omega

private lemma isTerm_six_mul_add_four (m : ℕ) (hm : 1 ≤ m) : isTerm (6 * m + 4) := by
  refine ⟨by omega, ⟨3 * m + 2, by omega⟩, ?_⟩
  have h1 : (6 * m + 4 - 1).minFac = 3 := minFac_eq_three (by omega) ⟨2 * m + 1, by omega⟩
  have h2 : 5 ≤ (6 * m + 4 - 3).minFac := five_le_minFac (by omega) (by omega) (by omega)
  omega

private lemma not_isTerm_six_mul (m : ℕ) : ¬ isTerm (6 * m) := by
  rintro ⟨h4, _, hlt⟩
  have hm : 1 ≤ m := by omega
  have h1 : 5 ≤ (6 * m - 1).minFac := five_le_minFac (by omega) (by omega) (by omega)
  have h2 : (6 * m - 3).minFac = 3 := minFac_eq_three (by omega) ⟨2 * m - 1, by omega⟩
  omega

private lemma isTerm_thirty_mul_add_26 (m : ℕ) : isTerm (30 * m + 26) := by
  refine ⟨by omega, ⟨15 * m + 13, by omega⟩, ?_⟩
  have h1 : (30 * m + 26 - 1).minFac = 5 := minFac_eq_five (by omega) (by omega) ⟨6 * m + 5, by omega⟩
  have h2 : 7 ≤ (30 * m + 26 - 3).minFac := seven_le_minFac (by omega) (by omega) (by omega) (by omega)
  omega

private lemma not_isTerm_thirty_mul_add_8 (m : ℕ) : ¬ isTerm (30 * m + 8) := by
  rintro ⟨_, _, hlt⟩
  have h1 : 7 ≤ (30 * m + 8 - 1).minFac := seven_le_minFac (by omega) (by omega) (by omega) (by omega)
  have h2 : (30 * m + 8 - 3).minFac = 5 := minFac_eq_five (by omega) (by omega) ⟨6 * m + 1, by omega⟩
  omega

private lemma isTerm_ge_ten {n : ℕ} (hn : isTerm n) : 10 ≤ n := by
  rcases hn with ⟨h4, ⟨t, ht⟩, hlt⟩
  by_contra hlt10
  have hcases : n = 4 ∨ n = 6 ∨ n = 8 := by omega
  rcases hcases with rfl | rfl | rfl
  · have h1 : (4 - 1).minFac = 3 := (by norm_num : Nat.Prime (4 - 1)).minFac_eq
    have h2 : (4 - 3).minFac = 1 := by simp
    omega
  · have h1 : (6 - 1).minFac = 5 := (by norm_num : Nat.Prime (6 - 1)).minFac_eq
    have h2 : (6 - 3).minFac = 3 := (by norm_num : Nat.Prime (6 - 3)).minFac_eq
    omega
  · have h1 : (8 - 1).minFac = 7 := (by norm_num : Nat.Prime (8 - 1)).minFac_eq
    have h2 : (8 - 3).minFac = 5 := (by norm_num : Nat.Prime (8 - 3)).minFac_eq
    omega

private lemma isTerm_infinite : {n : ℕ | isTerm n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun m => 6 * (m + 1) + 4) ?_ ?_
  · intro m₁ m₂ h; dsimp at h; omega
  · intro m; exact isTerm_six_mul_add_four (m + 1) (by omega)

private lemma a_mem (i : ℕ) : isTerm (a i) :=
  Nat.nth_mem_of_infinite isTerm_infinite i

private lemma a_strictMono : StrictMono a :=
  Nat.nth_strictMono isTerm_infinite

private lemma a_ge_ten (i : ℕ) : 10 ≤ a i :=
  isTerm_ge_ten (a_mem i)

private lemma exists_a_eq {x : ℕ} (hx : isTerm x) : ∃ i, a i = x := by
  classical
  exact ⟨Nat.count isTerm x, Nat.nth_count hx⟩

private lemma a_succ_eq {i x y : ℕ} (hi : a i = x) (hy : isTerm y) (hxy : x < y)
    (hmid : ∀ z, x < z → z < y → ¬ isTerm z) : a (i + 1) = y := by
  have hgt : x < a (i + 1) := hi ▸ a_strictMono (Nat.lt_succ_self i)
  have hge : y ≤ a (i + 1) := by
    by_contra hlt
    exact hmid (a (i + 1)) hgt (by omega) (a_mem (i + 1))
  obtain ⟨j, hj⟩ := exists_a_eq hy
  have hij : i < j := by
    by_contra hle
    have : a j ≤ a i := a_strictMono.monotone (by omega)
    omega
  have hle : a (i + 1) ≤ y := hj ▸ a_strictMono.monotone (by omega : i + 1 ≤ j)
  omega

private lemma a_mod_six (i : ℕ) : a i % 6 = 4 ∨ a i % 6 = 2 := by
  have hm := a_mem i
  rcases hm with ⟨_, ⟨t, ht⟩, _⟩
  have hne0 : a i % 6 ≠ 0 := by
    intro h0
    have : a i = 6 * (a i / 6) := by omega
    exact not_isTerm_six_mul (a i / 6) (this ▸ a_mem i)
  omega

private lemma a_succ_of_mod2 {i : ℕ} (h2 : a i % 6 = 2) :
    a (i + 1) = a i + 2 ∧ d i = 2 := by
  have h10 := a_ge_ten i
  have hy : isTerm (a i + 2) := by
    have : a i + 2 = 6 * (a i / 6) + 4 := by omega
    rw [this]; exact isTerm_six_mul_add_four (a i / 6) (by omega)
  have hsucc : a (i + 1) = a i + 2 := a_succ_eq rfl hy (by omega) (fun z hz1 hz2 hz => by
    rcases hz with ⟨_, ⟨t, ht⟩, _⟩; omega)
  exact ⟨hsucc, by dsimp [d]; omega⟩

private lemma a_succ_of_mod4 {i : ℕ} (h4 : a i % 6 = 4) :
    (isTerm (a i + 4) → a (i + 1) = a i + 4 ∧ d i = 4 ∧ d (i + 1) = 2 ∧ a (i + 2) = a i + 6) ∧
    (¬ isTerm (a i + 4) → a (i + 1) = a i + 6 ∧ d i = 6) := by
  have h10 := a_ge_ten i
  have hnot2 : ¬ isTerm (a i + 2) := by
    have : a i + 2 = 6 * (a i / 6 + 1) := by omega
    rw [this]; exact not_isTerm_six_mul (a i / 6 + 1)
  have hy6 : isTerm (a i + 6) := by
    have : a i + 6 = 6 * (a i / 6 + 1) + 4 := by omega
    rw [this]; exact isTerm_six_mul_add_four (a i / 6 + 1) (by omega)
  constructor
  · intro h4t
    have hsucc : a (i + 1) = a i + 4 := a_succ_eq rfl h4t (by omega) (fun z hz1 hz2 hz => by
      have : z = a i + 2 := by rcases hz with ⟨_, ⟨t, ht⟩, _⟩; omega
      exact hnot2 (this ▸ hz))
    have hmod2 : a (i + 1) % 6 = 2 := by omega
    obtain ⟨hsucc2, hd2⟩ := a_succ_of_mod2 hmod2
    exact ⟨hsucc, by dsimp [d]; omega, hd2, by rw [show i + 2 = i + 1 + 1 by rfl, hsucc2, hsucc]⟩
  · intro h4f
    have hsucc : a (i + 1) = a i + 6 := a_succ_eq rfl hy6 (by omega) (fun z hz1 hz2 hz => by
      have hcases : z = a i + 2 ∨ z = a i + 4 := by rcases hz with ⟨_, ⟨t, ht⟩, _⟩; omega
      rcases hcases with rfl | rfl
      · exact hnot2 hz
      · exact h4f hz)
    exact ⟨hsucc, by dsimp [d]; omega⟩

private lemma d_mem_246 (i : ℕ) : d i = 2 ∨ d i = 4 ∨ d i = 6 := by
  rcases a_mod_six i with h4 | h2
  · by_cases h4t : isTerm (a i + 4)
    · exact Or.inr (Or.inl ((a_succ_of_mod4 h4).1 h4t).2.1)
    · exact Or.inr (Or.inr ((a_succ_of_mod4 h4).2 h4t).2)
  · exact Or.inl (a_succ_of_mod2 h2).2

private lemma a_mod4_of_d_eq_4_or_6 {i : ℕ} (h : d i = 4 ∨ d i = 6) : a i % 6 = 4 := by
  rcases a_mod_six i with h4 | h2
  · exact h4
  · have := (a_succ_of_mod2 h2).2; omega

private lemma d_no_22 (i : ℕ) : ¬ (d i = 2 ∧ d (i + 1) = 2) := by
  rintro ⟨h1, h2⟩
  have hmod2 : a i % 6 = 2 := by
    rcases a_mod_six i with h4 | h2'
    · by_cases ht : isTerm (a i + 4)
      · have := ((a_succ_of_mod4 h4).1 ht).2.1; omega
      · have := ((a_succ_of_mod4 h4).2 ht).2; omega
    · exact h2'
  have hsucc : a (i + 1) = a i + 2 := (a_succ_of_mod2 hmod2).1
  have hmod4 : a (i + 1) % 6 = 4 := by omega
  by_cases ht : isTerm (a (i + 1) + 4)
  · have := ((a_succ_of_mod4 hmod4).1 ht).2.1; omega
  · have := ((a_succ_of_mod4 hmod4).2 ht).2; omega

private lemma d_no_44 (i : ℕ) : ¬ (d i = 4 ∧ d (i + 1) = 4) := by
  rintro ⟨h1, h2⟩
  have hmod4 : a i % 6 = 4 := a_mod4_of_d_eq_4_or_6 (Or.inl h1)
  by_cases ht : isTerm (a i + 4)
  · have := ((a_succ_of_mod4 hmod4).1 ht).2.2.1; omega
  · have := ((a_succ_of_mod4 hmod4).2 ht).2; omega

private lemma d_no_five_6 (i : ℕ) : ¬ (∀ j < 5, d (i + j) = 6) := by
  intro hall
  have ha_step : ∀ j ≤ 5, a (i + j) = a i + 6 * j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hd : d (i + j) = 6 := hall j (by omega)
      have hgt : a (i + j) < a (i + j + 1) := a_strictMono (Nat.lt_succ_self _)
      have : a (i + (j + 1)) = a (i + j) + 6 := by
        rw [show i + (j + 1) = i + j + 1 by omega]; dsimp [d] at hd; omega
      have := ih (by omega)
      omega
  have hmod4 : a i % 6 = 4 := a_mod4_of_d_eq_4_or_6 (Or.inr (hall 0 (by omega)))
  have hnot_term : ∀ j < 5, ¬ isTerm (a i + 6 * j + 4) := by
    intro j hj ht
    have h4j : a (i + j) % 6 = 4 := by rw [ha_step j (by omega)]; omega
    have h4t : isTerm (a (i + j) + 4) := by rw [ha_step j (by omega)]; exact ht
    have hd4 : d (i + j) = 4 := ((a_succ_of_mod4 h4j).1 h4t).2.1
    have hd6 : d (i + j) = 6 := hall j hj
    omega
  -- Among `j ∈ {0,1,2,3,4}`, `a i + 6 * j + 4` hits `26 mod 30`!
  have hex : ∃ j < 5, (a i + 6 * j + 4) % 30 = 26 := by
    have hrem : a i % 30 = 4 ∨ a i % 30 = 10 ∨ a i % 30 = 16 ∨ a i % 30 = 22 ∨ a i % 30 = 28 := by omega
    rcases hrem with h | h | h | h | h
    · exact ⟨3, by omega, by omega⟩
    · exact ⟨2, by omega, by omega⟩
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
    · exact ⟨4, by omega, by omega⟩
  obtain ⟨j, hj, h26⟩ := hex
  have h26eq : a i + 6 * j + 4 = 30 * ((a i + 6 * j + 4) / 30) + 26 := by omega
  exact hnot_term j hj (h26eq ▸ isTerm_thirty_mul_add_26 _)

private lemma d_no_five_42 (i : ℕ) : ¬ (∀ j < 5, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2) := by
  intro hall
  have ha_step : ∀ j ≤ 5, a (i + 2 * j) = a i + 6 * j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨hd4, hd2⟩ := hall j (by omega)
      have hgt1 : a (i + 2 * j) < a (i + 2 * j + 1) := a_strictMono (Nat.lt_succ_self _)
      have hgt2 : a (i + 2 * j + 1) < a (i + 2 * j + 2) := a_strictMono (Nat.lt_succ_self _)
      have : a (i + 2 * (j + 1)) = a (i + 2 * j) + 6 := by
        rw [show i + 2 * (j + 1) = i + 2 * j + 1 + 1 by omega]; dsimp [d] at hd4 hd2; omega
      have := ih (by omega)
      omega
  have hmod4 : a i % 6 = 4 := a_mod4_of_d_eq_4_or_6 (Or.inl (hall 0 (by omega)).1)
  have his_term : ∀ j < 5, isTerm (a i + 6 * j + 4) := by
    intro j hj
    have h4j : a (i + 2 * j) % 6 = 4 := by rw [ha_step j (by omega)]; omega
    by_contra hf
    have h4f : ¬ isTerm (a (i + 2 * j) + 4) := by rw [ha_step j (by omega)]; exact hf
    have hd6 : d (i + 2 * j) = 6 := ((a_succ_of_mod4 h4j).2 h4f).2
    have hd4 : d (i + 2 * j) = 4 := (hall j hj).1
    omega
  -- Among `j ∈ {0,1,2,3,4}`, `a i + 6 * j + 4` hits `8 mod 30`!
  have hex : ∃ j < 5, (a i + 6 * j + 4) % 30 = 8 := by
    have hrem : a i % 30 = 4 ∨ a i % 30 = 10 ∨ a i % 30 = 16 ∨ a i % 30 = 22 ∨ a i % 30 = 28 := by omega
    rcases hrem with h | h | h | h | h
    · exact ⟨0, by omega, by omega⟩
    · exact ⟨4, by omega, by omega⟩
    · exact ⟨3, by omega, by omega⟩
    · exact ⟨2, by omega, by omega⟩
    · exact ⟨1, by omega, by omega⟩
  obtain ⟨j, hj, h8⟩ := hex
  have h8eq : a i + 6 * j + 4 = 30 * ((a i + 6 * j + 4) / 30) + 8 := by omega
  exact not_isTerm_thirty_mul_add_8 _ (h8eq ▸ his_term j hj)

-- Fast witness lemmas for concrete `isTerm` / `¬ isTerm` checks!
private lemma isTerm_of_witness {n p : ℕ} (h5 : 5 ≤ n) (hev : n % 2 = 0)
    (hp2 : 2 ≤ p) (hpd : p ∣ n - 1) (hnd : ∀ d ∈ Finset.Icc 2 p, ¬ d ∣ n - 3) : isTerm n := by
  refine ⟨by omega, Nat.even_iff.mpr hev, ?_⟩
  have hle : (n - 1).minFac ≤ p := Nat.minFac_le_of_dvd hp2 hpd
  have hgt : p < (n - 3).minFac := by
    by_contra h
    have hpr : (n - 3).minFac.Prime := Nat.minFac_prime (by omega)
    exact hnd (n - 3).minFac (Finset.mem_Icc.mpr ⟨hpr.two_le, by omega⟩) (Nat.minFac_dvd (n - 3))
  omega

private lemma not_isTerm_of_witness {n p : ℕ} (h4 : 4 ≤ n)
    (hp2 : 2 ≤ p) (hpd : p ∣ n - 3) (hnd : ∀ d ∈ Finset.Icc 2 (p - 1), ¬ d ∣ n - 1) : ¬ isTerm n := by
  rintro ⟨_, _, hlt⟩
  have hle : (n - 3).minFac ≤ p := Nat.minFac_le_of_dvd hp2 hpd
  have hge : p ≤ (n - 1).minFac := by
    by_contra h
    have hpr : (n - 1).minFac.Prime := Nat.minFac_prime (by omega)
    exact hnd (n - 1).minFac (Finset.mem_Icc.mpr ⟨hpr.two_le, by omega⟩) (Nat.minFac_dvd (n - 1))
  omega

private lemma not_isTerm_of_twin_prime {n : ℕ} (h1 : (n - 1).Prime) (h3 : (n - 3).Prime) :
    ¬ isTerm n := by
  rintro ⟨h4, _, hlt⟩
  rw [h1.minFac_eq, h3.minFac_eq] at hlt
  omega

private lemma a_0_eq_10 : a 0 = 10 := by
  have h10 : isTerm 10 := isTerm_six_mul_add_four 1 (by omega)
  obtain ⟨i, hi⟩ := exists_a_eq h10
  have hge := a_ge_ten 0
  have hle : a 0 ≤ 10 := hi ▸ a_strictMono.monotone (Nat.zero_le i)
  omega

private lemma step_6 {i x : ℕ} (hi : a i = x) (h4 : x % 6 = 4) (hf : ¬ isTerm (x + 4)) :
    a (i + 1) = x + 6 ∧ d i = 6 := by
  have hx4 : a i % 6 = 4 := hi.symm ▸ h4
  have hnf : ¬ isTerm (a i + 4) := hi.symm ▸ hf
  have h := (a_succ_of_mod4 hx4).2 hnf
  exact ⟨hi ▸ h.1, h.2⟩

private lemma step_42 {i x : ℕ} (hi : a i = x) (h4 : x % 6 = 4) (ht : isTerm (x + 4)) :
    a (i + 1) = x + 4 ∧ a (i + 2) = x + 6 ∧ d i = 4 ∧ d (i + 1) = 2 := by
  have hx4 : a i % 6 = 4 := hi.symm ▸ h4
  have hyt : isTerm (a i + 4) := hi.symm ▸ ht
  have h := (a_succ_of_mod4 hx4).1 hyt
  exact ⟨hi ▸ h.1, hi ▸ h.2.2.2, h.2.1, h.2.2.1⟩

private lemma exists_runs_6 (k : ℕ) (hk : k ∈ ({1, 2, 3, 4} : Set ℕ)) :
    ∃ i, (i = 0 ∨ d (i - 1) ≠ 6) ∧ (∀ j < k, d (i + j) = 6) ∧ d (i + k) ≠ 6 := by
  rcases hk with rfl | rfl | rfl | rfl
  · -- k = 1: 130 ->(4,2) 136 ->(6) 142 ->(4,2) 148
    obtain ⟨i0, hi0⟩ := exists_a_eq (isTerm_six_mul_add_four 21 (by omega))
    obtain ⟨_, h1, _, hd1⟩ := step_42 hi0 (by decide)
      (isTerm_of_witness (n := 134) (p := 7) (by omega) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨h2, hd2⟩ := step_6 h1 (by decide)
      (not_isTerm_of_twin_prime (n := 140) (by norm_num) (by norm_num))
    obtain ⟨_, _, hd3, _⟩ := step_42 h2 (by decide)
      (isTerm_thirty_mul_add_26 4)
    refine ⟨i0 + 2, Or.inr (by simp [hd1]), ?_, by omega⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa using hd2
  · -- k = 2: 10 ->(6) 16 ->(6) 22 ->(4,2) 28 (starts at i = 0!)
    obtain ⟨h1, hd0⟩ := step_6 a_0_eq_10 (by decide)
      (not_isTerm_of_twin_prime (n := 14) (by norm_num) (by norm_num))
    obtain ⟨h2, hd1⟩ := step_6 h1 (by decide)
      (not_isTerm_of_twin_prime (n := 20) (by norm_num) (by norm_num))
    obtain ⟨_, _, hd2, _⟩ := step_42 h2 (by decide)
      (isTerm_thirty_mul_add_26 0)
    refine ⟨0, Or.inl rfl, ?_, by simp [hd2]⟩
    intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simp [hd0]
    · simp [hd1]
  · -- k = 3: 22 ->(4,2) 28 ->(6) 34 ->(6) 40 ->(6) 46 ->(4,2) 52
    obtain ⟨i0, hi0⟩ := exists_a_eq (isTerm_six_mul_add_four 3 (by omega))
    obtain ⟨_, h1, _, hd1⟩ := step_42 hi0 (by decide) (isTerm_thirty_mul_add_26 0)
    obtain ⟨h2, hd2⟩ := step_6 h1 (by decide)
      (not_isTerm_of_twin_prime (n := 32) (by norm_num) (by norm_num))
    obtain ⟨h3, hd3⟩ := step_6 h2 (by decide) (not_isTerm_thirty_mul_add_8 1)
    obtain ⟨h4, hd4⟩ := step_6 h3 (by decide)
      (not_isTerm_of_twin_prime (n := 44) (by norm_num) (by norm_num))
    obtain ⟨_, _, hd5, _⟩ := step_42 h4 (by decide)
      (isTerm_of_witness (n := 50) (p := 7) (by omega) (by decide) (by decide) (by decide) (by decide))
    refine ⟨i0 + 2, Or.inr (by simp [hd1]), ?_, by
      rw [show i0 + 2 + 3 = i0 + 2 + 1 + 1 + 1 by omega]; omega⟩
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simpa using hd2
    · simpa [add_assoc] using hd3
    · simpa [add_assoc] using hd4
  · -- k = 4: 52 ->(4,2) 58 ->(6) 64 ->(6) 70 ->(6) 76 ->(6) 82 ->(4,2) 88
    obtain ⟨i0, hi0⟩ := exists_a_eq (isTerm_six_mul_add_four 8 (by omega))
    obtain ⟨_, h1, _, hd1⟩ := step_42 hi0 (by decide) (isTerm_thirty_mul_add_26 1)
    obtain ⟨h2, hd2⟩ := step_6 h1 (by decide)
      (not_isTerm_of_twin_prime (n := 62) (by norm_num) (by norm_num))
    obtain ⟨h3, hd3⟩ := step_6 h2 (by decide) (not_isTerm_thirty_mul_add_8 2)
    obtain ⟨h4, hd4⟩ := step_6 h3 (by decide)
      (not_isTerm_of_twin_prime (n := 74) (by norm_num) (by norm_num))
    obtain ⟨h5, hd5⟩ := step_6 h4 (by decide)
      (not_isTerm_of_witness (n := 80) (p := 7) (by omega) (by decide) (by decide) (by decide))
    obtain ⟨_, _, hd6, _⟩ := step_42 h5 (by decide) (isTerm_thirty_mul_add_26 2)
    refine ⟨i0 + 2, Or.inr (by simp [hd1]), ?_, by
      rw [show i0 + 2 + 4 = i0 + 2 + 1 + 1 + 1 + 1 by omega]; omega⟩
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · simpa using hd2
    · simpa [add_assoc] using hd3
    · simpa [add_assoc] using hd4
    · simpa [add_assoc] using hd5

private lemma exists_runs_42 (k : ℕ) (hk : k ∈ ({1, 2, 3, 4} : Set ℕ)) :
    ∃ i, (i < 2 ∨ ¬ (d (i - 2) = 4 ∧ d (i - 1) = 2)) ∧
      (∀ j < k, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2) ∧
      ¬ (d (i + 2 * k) = 4 ∧ d (i + 2 * k + 1) = 2) := by
  rcases hk with rfl | rfl | rfl | rfl
  · -- k = 1: 16 ->(6) 22 ->(4,2) 28 ->(6) 34
    obtain ⟨i0, hi0⟩ := exists_a_eq (isTerm_six_mul_add_four 2 (by omega))
    obtain ⟨h1, hd0⟩ := step_6 hi0 (by decide)
      (not_isTerm_of_twin_prime (n := 20) (by norm_num) (by norm_num))
    obtain ⟨_, h2, hd1, hd2⟩ := step_42 h1 (by decide) (isTerm_thirty_mul_add_26 0)
    obtain ⟨_, hd3⟩ := step_6 h2 (by decide)
      (not_isTerm_of_twin_prime (n := 32) (by norm_num) (by norm_num))
    refine ⟨i0 + 1, Or.inr (fun h => by simp [hd0] at h), ?_, fun h => by
      have : i0 + 1 + 2 * 1 = i0 + 1 + 2 := by omega
      rw [this] at h; omega⟩
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact ⟨by simpa using hd1, by simpa using hd2⟩
  · -- k = 2: 40 ->(6) 46 ->(4,2) 52 ->(4,2) 58 ->(6) 64
    obtain ⟨i0, hi0⟩ := exists_a_eq (isTerm_six_mul_add_four 6 (by omega))
    obtain ⟨h1, hd0⟩ := step_6 hi0 (by decide)
      (not_isTerm_of_twin_prime (n := 44) (by norm_num) (by norm_num))
    obtain ⟨_, h2, hd1, hd2⟩ := step_42 h1 (by decide)
      (isTerm_of_witness (n := 50) (p := 7) (by omega) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨_, h3, hd3, hd4⟩ := step_42 h2 (by decide) (isTerm_thirty_mul_add_26 1)
    obtain ⟨_, hd5⟩ := step_6 h3 (by decide)
      (not_isTerm_of_twin_prime (n := 62) (by norm_num) (by norm_num))
    refine ⟨i0 + 1, Or.inr (fun h => by simp [hd0] at h), ?_, fun h => by
      have : i0 + 1 + 2 * 2 = i0 + 1 + 2 + 2 := by omega
      rw [this] at h; omega⟩
    intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact ⟨by simpa using hd1, by simpa using hd2⟩
    · exact ⟨by simpa [add_assoc] using hd3, by simpa [add_assoc] using hd4⟩
  · -- k = 3: 244 ->(6) 250 ->(4,2) 256 ->(4,2) 262 ->(4,2) 268 ->(6) 274
    obtain ⟨i0, hi0⟩ := exists_a_eq (isTerm_six_mul_add_four 40 (by omega))
    obtain ⟨h1, hd0⟩ := step_6 hi0 (by decide) (not_isTerm_thirty_mul_add_8 8)
    obtain ⟨_, h2, hd1, hd2⟩ := step_42 h1 (by decide)
      (isTerm_of_witness (n := 254) (p := 11) (by omega) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨_, h3, hd3, hd4⟩ := step_42 h2 (by decide)
      (isTerm_of_witness (n := 260) (p := 7) (by omega) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨_, h4, hd5, hd6⟩ := step_42 h3 (by decide) (isTerm_thirty_mul_add_26 8)
    obtain ⟨_, hd7⟩ := step_6 h4 (by decide)
      (not_isTerm_of_twin_prime (n := 272) (by norm_num) (by norm_num))
    refine ⟨i0 + 1, Or.inr (fun h => by simp [hd0] at h), ?_, fun h => by
      have : i0 + 1 + 2 * 3 = i0 + 1 + 2 + 2 + 2 := by omega
      rw [this] at h; omega⟩
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact ⟨by simpa using hd1, by simpa using hd2⟩
    · exact ⟨by simpa [add_assoc] using hd3, by simpa [add_assoc] using hd4⟩
    · exact ⟨by simpa [add_assoc] using hd5, by simpa [add_assoc] using hd6⟩
  · -- k = 4: 1894 ->(6) 1900 ->(4,2) 1906 ->(4,2) 1912 ->(4,2) 1918 ->(4,2) 1924 ->(6) 1930
    obtain ⟨i0, hi0⟩ := exists_a_eq (isTerm_six_mul_add_four 315 (by omega))
    obtain ⟨h1, hd0⟩ := step_6 hi0 (by decide) (not_isTerm_thirty_mul_add_8 63)
    obtain ⟨_, h2, hd1, hd2⟩ := step_42 h1 (by decide)
      (isTerm_of_witness (n := 1904) (p := 11) (by omega) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨_, h3, hd3, hd4⟩ := step_42 h2 (by decide)
      (isTerm_of_witness (n := 1910) (p := 23) (by omega) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨_, h4, hd5, hd6⟩ := step_42 h3 (by decide) (isTerm_thirty_mul_add_26 63)
    obtain ⟨_, h5, hd7, hd8⟩ := step_42 h4 (by decide)
      (isTerm_of_witness (n := 1922) (p := 17) (by omega) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨_, hd9⟩ := step_6 h5 (by decide) (not_isTerm_thirty_mul_add_8 64)
    refine ⟨i0 + 1, Or.inr (fun h => by simp [hd0] at h), ?_, fun h => by
      have : i0 + 1 + 2 * 4 = i0 + 1 + 2 + 2 + 2 + 2 := by omega
      rw [this] at h; omega⟩
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact ⟨by simpa using hd1, by simpa using hd2⟩
    · exact ⟨by simpa [add_assoc] using hd3, by simpa [add_assoc] using hd4⟩
    · exact ⟨by simpa [add_assoc] using hd5, by simpa [add_assoc] using hd6⟩
    · exact ⟨by simpa [add_assoc] using hd7, by simpa [add_assoc] using hd8⟩

end OMA.P_oeis_a245024

theorem OMA.solution : type_of% @OMA.S_oeis_a245024.main := by
  open OMA.S_oeis_a245024 OMA.P_oeis_a245024 in
  exact ⟨d_mem_246, d_no_22, d_no_44, d_no_five_6, exists_runs_6, d_no_five_42, exists_runs_42⟩
