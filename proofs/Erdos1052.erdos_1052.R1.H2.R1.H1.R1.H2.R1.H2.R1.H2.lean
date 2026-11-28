import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1

/-! For sole repeated odd core 5^4, no positive a divisible by 8192 is possible.
New rational path weights and 5-adic leaf budget; builds on the existing Graham
path-bound lemmas and forced closure from the merged ancestor reductions. -/
namespace Core625
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main

-- Exact beta weights for the 5^4 core; uses ancestor B_step, step_ge, one_add_le_B, two_mul_le.
def beta (q : ℕ) : ℚ :=
  if q = 3 then 1667 / 1250 else
  if q = 7 then 640128 / 514375 else
  if q = 13 then 560112 / 514375 else
  if q = 103 then 520104 / 514375 else
  if q = 823 then 515103 / 514375 else
  if q = 31 then 224 / 213 else
  if q = 61 then 217 / 213 else
  if q = 487 then 4880 / 4869 else
  if q = 127 then 1280 / 1269 else
  if q = 1777 then 4445889 / 4442500 else
  if q = 19 then 800 / 729 else
  if q = 37 then 760 / 729 else
  if q = 73 then 740 / 729 else
  if q = 1021 then 4088 / 4083 else
  if q = 199 then 1400 / 1389 else
  if q = 397 then 1393 / 1389 else
  if q = 79 then 320 / 313 else
  if q = 157 then 316 / 313 else
  if q = 313 then 314 / 313 else
  ((q : ℚ) + 1) / ((q : ℚ) - 1)

private theorem beta_default {p : ℕ}
    (h : ¬ (p = 3 ∨ p = 7 ∨ p = 13 ∨ p = 103 ∨ p = 823 ∨ p = 31 ∨ p = 61 ∨ p = 487 ∨ p = 127 ∨ p = 1777 ∨ p = 19 ∨ p = 37 ∨ p = 73 ∨ p = 1021 ∨ p = 199 ∨ p = 397 ∨ p = 79 ∨ p = 157 ∨ p = 313)) :
    beta p = ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  push_neg at h
  rcases h with ⟨h3, h7, h13, h103, h823, h31, h61, h487, h127, h1777, h19, h37, h73, h1021, h199, h397, h79, h157, h313⟩
  simp only [beta, h3, h7, h13, h103, h823, h31, h61, h487, h127, h1777, h19, h37, h73, h1021, h199, h397, h79, h157, h313, if_false]

set_option maxHeartbeats 2000000 in
theorem beta_bounds {p : ℕ} (hp : 2 ≤ p) :
    1 + 1 / (p : ℚ) ≤ beta p ∧ beta p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  by_cases h : p = 3 ∨ p = 7 ∨ p = 13 ∨ p = 103 ∨ p = 823 ∨ p = 31 ∨ p = 61 ∨ p = 487 ∨ p = 127 ∨ p = 1777 ∨ p = 19 ∨ p = 37 ∨ p = 73 ∨ p = 1021 ∨ p = 199 ∨ p = 397 ∨ p = 79 ∨ p = 157 ∨ p = 313
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [beta]
  · rw [beta_default h]
    exact ⟨one_add_le_B hp, le_rfl⟩

theorem beta_pos {p : ℕ} (hp : 2 ≤ p) : 0 < beta p :=
  lt_of_lt_of_le (by positivity : (0 : ℚ) < 1 + 1 / (p : ℚ)) (beta_bounds hp).1

set_option maxHeartbeats 4000000 in
theorem beta_edge {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hmod : p ≤ 10000 → p % 3 ≠ 2) (hc : c.Prime) (hc2 : c ≠ 2)
    (hd : c ∣ p + 1) (hc79 : c ≠ 79) (hc157 : c ≠ 157) (hc313 : c ≠ 313) :
    (1 + 1 / (c : ℚ)) * beta p ≤ beta c := by
  have hB := (beta_bounds hp.two_le).2
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcop : Nat.Coprime 2 c := (Nat.coprime_primes Nat.prime_two hc).mpr (Ne.symm hc2)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hd
  by_cases hs : c = 3 ∨ c = 7 ∨ c = 13 ∨ c = 103 ∨ c = 823 ∨ c = 31 ∨ c = 61 ∨ c = 487 ∨ c = 127 ∨ c = 1777 ∨ c = 19 ∨ c = 37 ∨ c = 73 ∨ c = 1021 ∨ c = 199 ∨ c = 397
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hbig : 10001 ≤ p
      · exact step_ge (c := 3) (t := 10001) (by norm_num) hbig hB (by norm_num [beta])
      · exfalso
        exact hmod (by omega) (by omega)
    · by_cases hbig : 24 ≤ p
      · exact step_ge (c := 7) (t := 24) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 1 := by omega
        have hpeq : p = 14 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 181 ≤ p
      · exact step_ge (c := 13) (t := 181) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 6 := by omega
        have hpeq : p = 26 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 1415 ≤ p
      · exact step_ge (c := 103) (t := 1415) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 6 := by omega
        have hpeq : p = 206 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 10001 ≤ p
      · exact step_ge (c := 823) (t := 10001) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 6 := by omega
        have hpeq : p = 1646 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 108 ≤ p
      · exact step_ge (c := 31) (t := 108) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 1 := by omega
        have hpeq : p = 62 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 853 ≤ p
      · exact step_ge (c := 61) (t := 853) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 6 := by omega
        have hpeq : p = 122 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 9739 ≤ p
      · exact step_ge (c := 487) (t := 9739) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 9 := by omega
        have hpeq : p = 974 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 2539 ≤ p
      · exact step_ge (c := 127) (t := 2539) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 9 := by omega
        have hpeq : p = 254 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 10001 ≤ p
      · exact step_ge (c := 1777) (t := 10001) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 2 := by omega
        have hpeq : p = 3554 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 49 ≤ p
      · exact step_ge (c := 19) (t := 49) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 1 := by omega
        have hpeq : p = 38 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 134 ≤ p
      · exact step_ge (c := 37) (t := 134) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 1 := by omega
        have hpeq : p = 74 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 1459 ≤ p
      · exact step_ge (c := 73) (t := 1459) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 9 := by omega
        have hpeq : p = 146 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 8167 ≤ p
      · exact step_ge (c := 1021) (t := 8167) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 3 := by omega
        have hpeq : p = 2042 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 696 ≤ p
      · exact step_ge (c := 199) (t := 696) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 1 := by omega
        have hpeq : p = 398 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
    · by_cases hbig : 5557 ≤ p
      · exact step_ge (c := 397) (t := 5557) (by norm_num) hbig hB (by norm_num [beta])
      · have hkl : 1 ≤ k := by omega
        have hku : k ≤ 6 := by omega
        have hpeq : p = 794 * k - 1 := by omega
        interval_cases k <;> norm_num at hpeq <;> subst p
        all_goals first
          | (norm_num [beta]; done)
          | (norm_num at hp; done)
          | (norm_num at hp5; done)
          | (have hbad := hmod (by norm_num); norm_num at hbad)
  · have he : beta c = ((c : ℚ) + 1) / ((c : ℚ) - 1) := by
      apply beta_default
      push_neg at hs ⊢
      rcases hs with ⟨h3, h7, h13, h103, h823, h31, h61, h487, h127, h1777, h19, h37, h73, h1021, h199, h397⟩
      exact ⟨h3, h7, h13, h103, h823, h31, h61, h487, h127, h1777, h19, h37, h73, h1021, h199, h397, hc79, hc157, hc313⟩
    rw [he]
    exact (mul_le_mul_of_nonneg_left hB (by positivity)).trans (B_step hc.two_le (two_mul_le hc hc2 hp hp2 hd))

-- Paste inside namespace Core625, after beta, beta_bounds, beta_pos.
-- Assumes the same opens as the core proof.
private theorem beta_ge_one625 {q : ℕ} (hq : q.Prime) : (1 : ℚ) ≤ beta q := by
  have h : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
  linarith [(beta_bounds hq.two_le).1]

private theorem v5_sum_budget625 {m : ℕ} {P T : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) =
      2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hT : T ⊆ P) : ∑ q ∈ T, (q + 1).factorization 5 ≤ 4 := by
  have hb := budget5 hP hP5 E hT
  have hn : (∏ p ∈ T, (p + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => by omega)
  rw [Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5) hn,
    Nat.factorization_prod (fun p _ => by omega), Finsupp.finsetSum_apply] at hb
  omega

private theorem beta_smooth625 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hl : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({5} : Finset ℕ))
    (hnm : ¬ ∃ k : ℕ, q + 1 = 2 ^ k) (h19 : q ≠ 19) (h79 : q ≠ 79) :
    beta q ≤ (251/250 : ℚ) ^ (q+1).factorization 5 := by
  obtain ⟨k,j,hk,hj,he⟩ := zleaf_form (z := 5) (by norm_num) (by norm_num) hq hq2 hl hnm
  have hd : 5 ∣ q + 1 := by
    rw [he]
    exact (pow_dvd_pow 5 hj).mul_left _
  have hv : 1 ≤ (q+1).factorization 5 :=
    (by norm_num : Nat.Prime 5).factorization_pos_of_dvd (by omega) hd
  rcases zleaf_cases hq (fun c hc hc2 hcd => Finset.mem_singleton.mp (hl c hc hc2 hcd)) hd
    with h | h | h | h | h
  · exact (h19 h).elim
  · exact (h79 h).elim
  · subst q
    have hv2 : 2 ≤ (199+1 : ℕ).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5) (by norm_num)).mp (by decide)
    calc beta 199 ≤ (251/250 : ℚ)^2 := by norm_num [beta]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hv2
  · subst q
    have hv2 : 2 ≤ (499+1 : ℕ).factorization 5 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5) (by norm_num)).mp (by decide)
    calc beta 499 ≤ (251/250 : ℚ)^2 := by norm_num [beta]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hv2
  · have hB : beta q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := (beta_bounds hq.two_le).2
    calc beta q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := hB
      _ ≤ ((1249 : ℚ) + 1) / ((1249 : ℚ) - 1) := B_anti (by norm_num) h
      _ ≤ (251/250 : ℚ)^1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hv

private theorem prod_beta_pow625 (T : Finset ℕ)
    (h : ∀ q ∈ T, 0 ≤ beta q ∧ beta q ≤ (251/250 : ℚ)^(q+1).factorization 5) :
    ∏ q ∈ T, beta q ≤ (251/250 : ℚ)^(∑ q ∈ T, (q+1).factorization 5) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert q T hq ih =>
    rw [Finset.prod_insert hq, Finset.sum_insert hq, pow_add]
    exact mul_le_mul (h q (Finset.mem_insert_self _ _)).2
      (ih (fun p hp => h p (Finset.mem_insert_of_mem hp)))
      (Finset.prod_nonneg fun p hp => (h p (Finset.mem_insert_of_mem hp)).1)
      (by positivity)

private theorem nonmersenne_budget625 {m : ℕ} {P L : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) =
      2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hLP : L ⊆ P) (h79 : 79 ∈ P)
    (hl : ∀ q ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({5} : Finset ℕ))
    (hnm : ∀ q ∈ L, ¬ ∃ k : ℕ, q + 1 = 2 ^ k) :
    ∏ q ∈ L, beta q ≤ beta 79 * beta 19 * (251/250 : ℚ)^2 := by
  classical
  let U := L.erase 79
  have hUL : U ⊆ L := Finset.erase_subset _ _
  have hU79 : 79 ∉ U := Finset.notMem_erase _ _
  have hTP : insert 79 U ⊆ P := Finset.insert_subset_iff.mpr ⟨h79, hUL.trans hLP⟩
  have hLT : L ⊆ insert 79 U := by
    intro q hq
    by_cases he : q = 79
    · subst q; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he, hq⟩)
  have hpadded : ∏ q ∈ L, beta q ≤ ∏ q ∈ insert 79 U, beta q :=
    Finset.prod_le_prod_of_subset_of_one_le hLT
      (fun q hq => (beta_pos (hP q (hLP hq)).1.two_le).le)
      (fun q hq _ => beta_ge_one625 (hP q (hTP hq)).1)
  have hb := v5_sum_budget625 hP hP5 E hTP
  have h80 : (79+1 : ℕ).factorization 5 = 1 := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5)
      (by norm_num : (79+1 : ℕ) ≠ 0)).mp (by decide : 5^1 ∣ 79+1)
    have h2 : ¬ 2 ≤ (79+1 : ℕ).factorization 5 := by
      intro h
      have hd := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5)
        (by norm_num : (79+1 : ℕ) ≠ 0)).mpr h
      norm_num at hd
    omega
  rw [Finset.sum_insert hU79, h80] at hb
  have hUbudget : ∑ q ∈ U, (q+1).factorization 5 ≤ 3 := by omega
  have hp79 : (0 : ℚ) ≤ beta 79 := (beta_pos (by norm_num : 2 ≤ 79)).le
  have hp19 : (0 : ℚ) ≤ beta 19 := (beta_pos (by norm_num : 2 ≤ 19)).le
  have halpha19 : (251/250 : ℚ) ≤ beta 19 := by norm_num [beta]
  have hpoint : ∀ q ∈ U, q ≠ 19 →
      0 ≤ beta q ∧ beta q ≤ (251/250 : ℚ)^(q+1).factorization 5 := by
    intro q hq hq19
    have hqL := hUL hq
    have hqP := hP q (hLP hqL)
    exact ⟨(beta_pos hqP.1.two_le).le, beta_smooth625 hqP.1 hqP.2
      (hl q hqL) (hnm q hqL) hq19 (Finset.mem_erase.mp hq).1⟩
  apply hpadded.trans
  rw [Finset.prod_insert hU79, mul_assoc (beta 79) (beta 19)]
  apply mul_le_mul_of_nonneg_left _ hp79
  by_cases h19 : 19 ∈ U
  · let V := U.erase 19
    have hV19 : 19 ∉ V := Finset.notMem_erase _ _
    have hUV : insert 19 V = U := Finset.insert_erase h19
    have h20 : (19+1 : ℕ).factorization 5 = 1 := by
      have h1 := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5)
        (by norm_num : (19+1 : ℕ) ≠ 0)).mp (by decide : 5^1 ∣ 19+1)
      have h2 : ¬ 2 ≤ (19+1 : ℕ).factorization 5 := by
        intro h
        have hd := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 5)
          (by norm_num : (19+1 : ℕ) ≠ 0)).mpr h
        norm_num at hd
      omega
    rw [← hUV, Finset.sum_insert hV19, h20] at hUbudget
    have hVbudget : ∑ q ∈ V, (q+1).factorization 5 ≤ 2 := by omega
    rw [← hUV, Finset.prod_insert hV19]
    apply mul_le_mul_of_nonneg_left _ hp19
    exact (prod_beta_pow625 V (fun q hq =>
      hpoint q (Finset.mem_of_mem_erase hq) (Finset.mem_erase.mp hq).1)).trans
      (pow_le_pow_right₀ (by norm_num) hVbudget)
  · calc
      ∏ q ∈ U, beta q ≤ (251/250 : ℚ)^(∑ q ∈ U, (q+1).factorization 5) :=
        prod_beta_pow625 U (fun q hq => hpoint q hq (fun he => h19 (he ▸ hq)))
      _ ≤ (251/250 : ℚ)^3 := pow_le_pow_right₀ (by norm_num) hUbudget
      _ = (251/250 : ℚ) * (251/250)^2 := by ring
      _ ≤ beta 19 * (251/250)^2 := mul_le_mul_of_nonneg_right halpha19 (by positivity)

-- Assembly body for the 5^4 high-valuation exclusion. The edge and budget
-- helpers are being developed separately; this is not a checked proof yet.

private theorem top_large {r a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (ha : 8192 ∣ a) (hd : r ∣ 2 ^ a + 1) : 10000 < r := by
  have hgt : 2 < r := by have := hr.two_le; omega
  letI : Fact r.Prime := ⟨hr⟩
  obtain ⟨m, rfl⟩ := ha
  have hzero : ((2 ^ (8192 * m) + 1 : ℕ) : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hzero
  have he : (2 : ZMod r) ^ (8192 * m) = -1 := eq_neg_of_add_eq_zero_left hzero
  have hne : (-1 : ZMod r) ≠ 1 := by
    intro h
    have h2 : (2 : ZMod r) = 0 := by linear_combination -h
    have h2d : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by simpa using h2)
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h2d
    omega
  have hx : ((2 : ZMod r) ^ m) ^ 8192 = -1 := by rw [← pow_mul, mul_comm]; exact he
  have hord : orderOf ((2 : ZMod r) ^ m) = 2 ^ (13 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 13)
      (by rw [show (2 : ℕ) ^ 13 = 8192 by norm_num, hx]; exact hne)
      (by rw [show (2 : ℕ) ^ (13 + 1) = 8192 * 2 by norm_num, pow_mul, hx]; norm_num)
  have hx0 : (2 : ZMod r) ^ m ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by norm_num)] at hx
    exact one_ne_zero (neg_eq_zero.mp hx.symm)
  obtain ⟨k, hk⟩ := hord ▸ ZMod.orderOf_dvd_card_sub_one hx0
  norm_num at hk
  omega

set_option maxHeartbeats 4000000 in
private theorem kill_high {a : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ a + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) =
      2 ^ (a + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (ha : 8192 ∣ a) (ha0 : 0 < a) : False := by
  classical
  obtain ⟨S1, S2, S3, _, _, _, S7, S8⟩ := facts hP hK54 E
  have h313 := S7 313 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have h157 := S1 157 (by norm_num) (by norm_num) (by decide) 313 h313 (by norm_num)
  have h79 := S1 79 (by norm_num) (by norm_num) (by decide) 157 h157 (by norm_num)
  have ham : a % 2 = 0 := by obtain ⟨k, hk⟩ := ha; omega
  have hmod : (2 ^ a + 1) % 3 = 2 := by
    obtain ⟨k, hk⟩ : ∃ k, a = 2*k := ⟨a/2, by omega⟩
    rw [hk, pow_mul, Nat.add_mod, Nat.pow_mod]
    norm_num
  obtain ⟨r, hr, hrd, hrmod⟩ := exists_prime_mod3 _ hmod
  have hr2 : r ≠ 2 := by
    intro he
    subst r
    have hd := (Nat.dvd_add_right (dvd_pow_self 2 ha0.ne')).mp hrd
    norm_num at hd
  have hrlarge := top_large hr hr2 ha hrd
  have hrP := S2 r hr hr2 (by simp; omega) hrd
  have hr3 : 3 ∣ r + 1 := by omega
  have hsmall : ∀ p ∈ P, p ≤ 10000 → p % 3 ≠ 2 := by
    intro p hp hle hmodp
    have hp3 : 3 ∣ p + 1 := by omega
    have he := S3 3 (by norm_num) (by norm_num) (by decide) p hp r hrP hp3 hr3
    omega
  have hstep : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      beta c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * beta p ≤ beta c := by
    intro p hp c hc hd _ _
    by_cases hc79 : c = 79
    · subst c
      have he := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 h157 hd (by norm_num)
      subst p
      norm_num [beta]
    by_cases hc157 : c = 157
    · subst c
      have he := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 h313 hd (by norm_num)
      subst p
      norm_num [beta]
    by_cases hc313 : c = 313
    · subst c
      exact (S8 313 (by norm_num) (by norm_num) (by decide) (by norm_num) p hp hd).elim
    exact beta_edge (hP p hp).1 (hP p hp).2 (fun e => h5 (e ▸ hp))
      (hsmall p hp) (hP c hc).1 (hP c hc).2 hd hc79 hc157 hc313
  obtain ⟨L, hLP, hL, hmain⟩ := master_gen hP hK54 (by norm_num) E beta
    (fun p hp => beta_bounds (hP p hp).1.two_le) hstep
  let M := L.filter (fun q => ∃ k : ℕ, q + 1 = 2 ^ k)
  let Z := L.filter (fun q => ¬ ∃ k : ℕ, q + 1 = 2 ^ k)
  have hm := mersenne_bound beta M (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
    (fun q hq => (Finset.mem_filter.mp hq).2)
    (fun q hq => ⟨beta_pos (hP q (hLP (Finset.mem_filter.mp hq).1)).1.two_le,
      (beta_bounds (hP q (hLP (Finset.mem_filter.mp hq).1)).1.two_le).2⟩) (by norm_num [beta])
  have hZP : Z ⊆ P := (Finset.filter_subset _ _).trans hLP
  have hz := nonmersenne_budget625 hP h5 E hZP h79
    (fun q hq => hL q (Finset.mem_filter.mp hq).1) (fun q hq => (Finset.mem_filter.mp hq).2)
  have hprod : ∏ q ∈ L, beta q ≤
      ((beta 3 * beta 7 * beta 31 * beta 127) * (2048 / 2047)) *
      (beta 79 * beta 19 * (251/250)^2) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => ∃ k : ℕ, q + 1 = 2 ^ k) beta]
    exact mul_le_mul hm hz (Finset.prod_nonneg fun q hq =>
      (beta_pos (hP q (hLP (Finset.mem_filter.mp hq).1)).1.two_le).le) (by norm_num [beta])
  have ha13 : 13 ≤ a := by obtain ⟨k, hk⟩ := ha; omega
  have hmain' : (2 : ℚ) ≤ (1 + 1 / (2 : ℚ)^a) * (626/625) * ∏ q ∈ L, beta q := by
    norm_num at hmain ⊢
    exact hmain
  apply fin5 ha13 (hmain'.trans (mul_le_mul_of_nonneg_left hprod (by positivity)))
  norm_num [beta]

-- The three site targets differ only in the supplied congruence on a.
private theorem high_core_impossible {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5)
    (he : n.factorization 5 = 4) (ha : 8192 ∣ padicValNat 2 n) : False := by
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two, he] at E
  have h5 : 5 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) := by simp
  have ha0 : 0 < padicValNat 2 n := by
    rw [← Nat.factorization_def n Nat.prime_two]
    exact Nat.prime_two.factorization_pos_of_dvd h.2.ne' (two_dvd_of_isUnitaryPerfect h)
  exact kill_high hP h5 E ha ha0

end Core625

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H2_R1.H2 := by
  refine ⟨0, fun n h hS he ha => ?_⟩
  have hd : 8192 ∣ padicValNat 2 n := by norm_num at ha; omega
  exact (Core625.high_core_impossible h hS he hd).elim
