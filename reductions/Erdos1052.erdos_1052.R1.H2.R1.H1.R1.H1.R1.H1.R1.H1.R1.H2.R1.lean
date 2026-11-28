import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1
import Mathlib

-- Removes a = 2 mod 4 when the only repeated odd prime is 3, with exponent 5.
-- Parent reduction: @adammcarter, PR #13044; graph infrastructure PR #1834.
-- Further context: @aroth01 notes #87897/#88733; @MBimrose note #95054.
-- The two unbounded remaining classes are H1 (a = 4 mod 8) and H2 (a = 8 mod 16).
-- The weighted forest argument and finite parent bounds below are written for this reduction.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
lemma u1_kill_e5_no_five_consumer :
    ∀ {m : ℕ} {P : Finset ℕ},
    (∀ p ∈ P, p.Prime ∧ p ≠ 2) → 3 ∉ P →
    (2 ^ m + 1) * 244 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 243 * ∏ p ∈ P, p →
    20 ≤ m → (∀ p ∈ P, ¬ 5 ∣ p + 1) → False := by


  have weighted_forest {α : Type} [DecidableEq α] (P : Finset α)
      (g : α → α) (w b : α → ℚ)
      (hw : ∀ x ∈ P, 0 < w x) (hb : ∀ x ∈ P, 0 < b x)
      (hinj : ∀ x ∈ P, ∀ y ∈ P, g x ∈ P → g x = g y → x = y)
      (hbase : ∀ x ∈ P, w x ≤ b x)
      (hedge : ∀ x ∈ P, g x ∈ P → w (g x) * b x ≤ b (g x)) :
      ∏ x ∈ P, w x ≤ ∏ x ∈ P.filter (fun x => g x ∉ P), b x := by
    let A := P.filter (fun x => g x ∈ P)
    let C := A.image g
    have hAP : A ⊆ P := Finset.filter_subset _ _
    have hCP : C ⊆ P := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hy).2
    have hi : Set.InjOn g (A : Set α) := by
      intro x hx y hy he
      exact hinj x (hAP hx) y (hAP hy) (Finset.mem_filter.mp hx).2 he
    have hc (f : α → ℚ) : ∏ x ∈ C, f x = ∏ x ∈ A, f (g x) :=
      Finset.prod_image hi
    have he : (∏ x ∈ C, w x) * (∏ x ∈ A, b x) ≤ ∏ x ∈ C, b x := by
      rw [hc w, hc b, ← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod
      · intro x hx
        exact mul_nonneg (hw _ ((Finset.mem_filter.mp hx).2)).le (hb _ (hAP hx)).le
      · intro x hx
        exact hedge x (hAP hx) (Finset.mem_filter.mp hx).2
    have ht : ∏ x ∈ P \ C, w x ≤ ∏ x ∈ P \ C, b x :=
      Finset.prod_le_prod (fun x hx => (hw _ (Finset.mem_sdiff.mp hx).1).le)
        (fun x hx => hbase _ (Finset.mem_sdiff.mp hx).1)
    have hcombined := mul_le_mul he ht
      (Finset.prod_nonneg (fun x hx => (hw _ (Finset.mem_sdiff.mp hx).1).le))
      (Finset.prod_nonneg (fun x hx => (hb _ (hCP hx)).le))
    have hwp : (∏ x ∈ C, w x) * (∏ x ∈ P \ C, w x) = ∏ x ∈ P, w x :=
      by simpa [mul_comm] using Finset.prod_sdiff (f := w) hCP
    have hbp : (∏ x ∈ C, b x) * (∏ x ∈ P \ C, b x) = ∏ x ∈ P, b x :=
      by simpa [mul_comm] using Finset.prod_sdiff (f := b) hCP
    rw [mul_right_comm, hwp, hbp] at hcombined
    have hba : (∏ x ∈ A, b x) * (∏ x ∈ P \ A, b x) = ∏ x ∈ P, b x :=
      by simpa [mul_comm] using Finset.prod_sdiff (f := b) hAP
    rw [← hba, mul_comm (∏ x ∈ A, b x)] at hcombined
    have hpos : 0 < ∏ x ∈ A, b x := Finset.prod_pos (fun x hx => hb _ (hAP hx))
    have hfinal := (mul_le_mul_iff_left₀ hpos).mp hcombined
    have hl : P \ A = P.filter (fun x => g x ∉ P) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_filter, A]
      tauto
    simpa [hl] using hfinal



  have least_child_shape {p c Q : ℕ} (hp : p.Prime) (hc : c.Prime) (hc2 : c ≠ 2)
      (hd : c ∣ p + 1) (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → c ≤ r)
      (h3 : ¬ 3 ∣ p + 1) (hQ : p < Q) (hQc : Q < 2 * c ^ 2) :
      ∃ k : ℕ, p + 1 = 2 ^ (k + 1) * c := by
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      have hc3 : c = 3 := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp hd
      exact h3 (hc3 ▸ hd)
    have hpo := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hd2 : 2 ∣ p + 1 := by omega
    have hcop : Nat.Coprime 2 c := (hc.coprime_iff_not_dvd.mpr (fun he =>
      hc2 ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp he))).symm
    obtain ⟨u, hu⟩ := hcop.mul_dvd_of_dvd_of_dvd hd2 hd
    have hu0 : 0 < u := by nlinarith [hc.pos]
    have huc : u < c := by nlinarith [hc.pos]
    have hn : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ u := by
      intro r hr hr2 hru
      have hrp : r ∣ p + 1 := hru.trans ⟨2 * c, by nlinarith [hu]⟩
      have hr3 : r ≠ 3 := fun he => h3 (he ▸ hrp)
      have hcr := hmin r hr hr2 hr3 hrp
      have hru' := Nat.le_of_dvd hu0 hru
      omega
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd u with ⟨k, hk⟩ | ⟨r, hr, hru, hr2⟩
    · refine ⟨k, ?_⟩
      rw [hk] at hu
      rw [hu, pow_succ]
      ring
    · exact (hn r hr (fun he => by subst r; norm_num at hr2) hru).elim



  let tau : ℚ := 28 / 27
  let cost (p : ℕ) : ℕ := (p + 1).factorization 3
  let raw (p : ℕ) : ℚ := (1 + 1 / (p : ℚ)) / tau ^ cost p
  let base (p : ℕ) : ℚ := (((p : ℚ) + 1) / ((p : ℚ) - 1)) / tau ^ cost p
  let beta (p : ℕ) : ℚ :=
    if p = 3 then 1 else
    if p = 5 then 81 / 70 else
    if p = 7 then 384256 / 308625 else
    if p = 11 then 40527 / 37625 else
    if p = 13 then 336224 / 308625 else
    if p = 17 then 5832 / 5831 else
    if p = 23 then 1327185 / 1313536 else
    if p = 31 then 64 / 61 else
    if p = 43 then 16511 / 16125 else
    if p = 47 then 1 / 1 else
    if p = 61 then 62 / 61 else
    if p = 67 then 64 / 63 else
    if p = 103 then 312208 / 308625 else
    if p = 127 then 524288 / 520065 else
    if p = 367 then 376855 / 375296 else
    if p = 733 then 6013295 / 6004736 else
    if p = 823 then 309206 / 308625 else
    base p

  have raw_le_base {p : ℕ} (hp : 2 ≤ p) : raw p ≤ base p := by
    have hpp : (2 : ℚ) ≤ p := by exact_mod_cast hp
    have ht : 0 < tau := by norm_num [tau]
    apply div_le_div_of_nonneg_right _ (pow_nonneg ht.le _)
    rw [le_div_iff₀ (by linarith)]
    field_simp
    nlinarith

  have beta_bounds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
      0 < beta p ∧ raw p ≤ beta p ∧ beta p ≤ base p := by
    have hpp : 2 ≤ p := hp.two_le
    have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hpp
    by_cases h5 : p = 5
    · subst p
      have hc : cost 5 = 1 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h7 : p = 7
    · subst p
      have hc : cost 7 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h11 : p = 11
    · subst p
      have hc : cost 11 = 1 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h13 : p = 13
    · subst p
      have hc : cost 13 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h17 : p = 17
    · subst p
      have hc : cost 17 = 2 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h23 : p = 23
    · subst p
      have hc : cost 23 = 1 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h31 : p = 31
    · subst p
      have hc : cost 31 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h43 : p = 43
    · subst p
      have hc : cost 43 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h47 : p = 47
    · subst p
      have hc : cost 47 = 1 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h61 : p = 61
    · subst p
      have hc : cost 61 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h67 : p = 67
    · subst p
      have hc : cost 67 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h103 : p = 103
    · subst p
      have hc : cost 103 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h127 : p = 127
    · subst p
      have hc : cost 127 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h367 : p = 367
    · subst p
      have hc : cost 367 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h733 : p = 733
    · subst p
      have hc : cost 733 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    by_cases h823 : p = 823
    · subst p
      have hc : cost 823 = 0 := by decide +kernel
      norm_num [beta, raw, base, hc, tau]
    have hb : beta p = base p := by
      simp only [beta, if_neg hp3, if_neg h5, if_neg h7, if_neg h11, if_neg h13, if_neg h17, if_neg h23, if_neg h31, if_neg h43, if_neg h47, if_neg h61, if_neg h67, if_neg h103, if_neg h127, if_neg h367, if_neg h733, if_neg h823]
    rw [hb]
    have ht : 0 < tau := by norm_num [tau]
    have hbpos : 0 < base p := div_pos (div_pos (by linarith) (by linarith)) (pow_pos ht _)
    exact ⟨hbpos, raw_le_base hpp, le_rfl⟩


  let cap (p : ℕ) : ℚ := ((p : ℚ) + 1) / ((p : ℚ) - 1)

  have cap_antitone {p q : ℕ} (hq : 2 ≤ q) (hqp : q ≤ p) : cap p ≤ cap q := by
    have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
    have hpq : (q : ℚ) ≤ p := by exact_mod_cast hqp
    dsimp only [cap]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

  have beta_cap {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : beta p ≤ cap p := by
    have ht : 1 ≤ tau := by norm_num [tau]
    have hpow : 1 ≤ tau ^ cost p := one_le_pow₀ ht
    have hpos : 0 < tau ^ cost p := lt_of_lt_of_le (by norm_num) hpow
    refine (beta_bounds hp h2 h3).2.2.trans ?_
    change cap p / tau ^ cost p ≤ cap p
    apply (div_le_iff₀ hpos).mpr
    have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
    have hcap : 0 ≤ cap p := div_nonneg (by linarith) (by linarith)
    nlinarith

  have beta_three {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hp55 : 55 ≤ p) (hd3 : 3 ∣ p + 1) : beta p ≤ 1 := by
    have ht : 1 ≤ tau := by norm_num [tau]
    have hj : 1 ≤ cost p := Nat.prime_three.factorization_pos_of_dvd (by omega) hd3
    have hpow : tau ≤ tau ^ cost p := by
      calc tau = tau ^ 1 := by rw [pow_one]
        _ ≤ tau ^ cost p := pow_le_pow_right₀ ht hj
    have hpq : (55 : ℚ) ≤ p := by exact_mod_cast hp55
    have hcap : cap p ≤ tau := by
      dsimp only [cap]
      rw [div_le_iff₀ (by linarith)]
      norm_num [tau]
      linarith
    refine (beta_bounds hp h2 h3).2.2.trans ?_
    change cap p / tau ^ cost p ≤ 1
    have htpos : 0 < tau := by norm_num [tau]
    rw [div_le_one (pow_pos htpos _)]
    exact hcap.trans hpow

  have source_large {p c : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hc : c.Prime)
      (hc11 : 11 ≤ c) (hd : c ∣ p + 1) (hd3 : 3 ∣ p + 1) : 55 ≤ p := by
    have hpodd := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    have hd2 : 2 ∣ p + 1 := by omega
    have hd6 : 6 ∣ p + 1 := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd hd2 hd3
    obtain ⟨u, hu⟩ := hd6
    have hcu : c ∣ u := by
      rw [hu] at hd
      rcases hc.dvd_mul.mp hd with he | he
      · have : c ≤ 6 := Nat.le_of_dvd (by norm_num) he
        omega
      · exact he
    have hu0 : 0 < u := by omega
    have := Nat.le_of_dvd hu0 hcu
    omega

  have parent_bound {p c Q : ℕ} {M : ℚ}
      (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (hc : c.Prime) (hc11 : 11 ≤ c)
      (hd : c ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → c ≤ r)
      (hQ : 2 ≤ Q) (hQc : Q < 2 * c ^ 2)
      (hM : 1 ≤ M) (hMQ : cap Q ≤ M)
      (hsmall : ∀ k : ℕ, 2 ^ (k + 1) * c - 1 < Q →
        (2 ^ (k + 1) * c - 1).Prime → beta (2 ^ (k + 1) * c - 1) ≤ M) :
      beta p ≤ M := by
    by_cases hd3 : 3 ∣ p + 1
    · exact (beta_three hp h2 h3 (source_large hp h2 hc hc11 hd hd3) hd3).trans hM
    by_cases hpQ : p < Q
    · obtain ⟨k, hk⟩ := least_child_shape hp hc (by omega) hd hmin hd3 hpQ hQc
      have he : p = 2 ^ (k + 1) * c - 1 := by omega
      rw [he] at hp hpQ ⊢
      exact hsmall k hpQ hp
    · exact (beta_cap hp h2 h3).trans ((cap_antitone hQ (by omega)).trans hMQ)


  have parent_11 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 11 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 11 ≤ r) :
      beta p ≤ (16511 / 16125 : ℚ) := by
    apply parent_bound (Q := 85) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 2 := by
      by_contra h
      have hpow : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_13 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 13 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 13 ≤ r) :
      beta p ≤ (312208 / 308625 : ℚ) := by
    apply parent_bound (Q := 200) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 3 := by
      by_contra h
      have hpow : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_17 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 17 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 17 ≤ r) :
      beta p ≤ (64 / 63 : ℚ) := by
    apply parent_bound (Q := 129) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 2 := by
      by_contra h
      have hpow : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_23 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 23 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 23 ≤ r) :
      beta p ≤ (376855 / 375296 : ℚ) := by
    apply parent_bound (Q := 500) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 4 := by
      by_contra h
      have hpow : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_43 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 43 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 43 ≤ r) :
      beta p ≤ (1501 / 1500 : ℚ) := by
    apply parent_bound (Q := 3001) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 6 := by
      by_contra h
      have hpow : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_47 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 47 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 47 ≤ r) :
      beta p ≤ (329 / 324 : ℚ) := by
    apply parent_bound (Q := 131) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 1 := by
      by_contra h
      have hpow : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_67 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 67 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 67 ≤ r) :
      beta p ≤ (1072 / 1071 : ℚ) := by
    apply parent_bound (Q := 2143) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 4 := by
      by_contra h
      have hpow : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_103 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 103 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 103 ≤ r) :
      beta p ≤ (309206 / 308625 : ℚ) := by
    apply parent_bound (Q := 1065) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 3 := by
      by_contra h
      have hpow : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_127 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 127 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 127 ≤ r) :
      beta p ≤ (4096 / 4095 : ℚ) := by
    apply parent_bound (Q := 8191) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 6 := by
      by_contra h
      have hpow : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_367 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 367 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 367 ≤ r) :
      beta p ≤ (6013295 / 6004736 : ℚ) := by
    apply parent_bound (Q := 1405) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 1 := by
      by_contra h
      have hpow : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_733 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 733 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 733 ≤ r) :
      beta p ≤ (16385 / 16384 : ℚ) := by
    apply parent_bound (Q := 32769) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 5 := by
      by_contra h
      have hpow : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_823 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 823 ∣ p + 1)
      (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → 823 ≤ r) :
      beta p ≤ (1501 / 1500 : ℚ) := by
    apply parent_bound (Q := 3001) hp h2 h3 (by norm_num) (by norm_num) hd hmin
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap])
    intro k hcut hp'
    have hk : k < 1 := by
      by_contra h
      have hpow : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hpow
      rw [pow_succ] at hcut
      omega
    interval_cases k <;> norm_num at hp' <;> norm_num [beta]

  have parent_7 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd : 7 ∣ p + 1) : beta p ≤ beta 13 := by
    by_cases h : 24 ≤ p
    · exact (beta_cap hp h2 h3).trans ((cap_antitone (by norm_num : 2 ≤ 24) h).trans
        (by norm_num [cap, beta]))
    · have hlt : p < 24 := by omega
      interval_cases p <;> norm_num at hp <;> norm_num at hd <;> norm_num [beta]


  have fac_mul3 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
      (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

  have ledger {m : ℕ} {P : Finset ℕ}
      (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 3)
      (E : (2 ^ m + 1) * 244 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 243 * ∏ p ∈ P, p) :
      ∑ p ∈ P, cost p ≤ 5 := by
    have hprod0 : (∏ p ∈ P, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hP p hp).1.ne_zero)
    have hprod1 : (∏ p ∈ P, (p + 1)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p _ => by omega)
    have hpf : (∏ p ∈ P, p).factorization 3 = 0 := by
      rw [Nat.factorization_prod_apply (fun p hp => (hP p hp).1.ne_zero)]
      apply Finset.sum_eq_zero
      intro p hp
      exact Nat.factorization_eq_zero_of_not_dvd (fun hd => (hP p hp).2
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (hP p hp).1).mp hd).symm)
    have hpow : (2 ^ (m + 1)).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun hd => by
        have := Nat.prime_three.dvd_of_dvd_pow hd
        norm_num at this)
    have h243 : (243 : ℕ).factorization 3 = 5 := by decide +kernel
    have h244 : (244 : ℕ).factorization 3 = 0 := by decide +kernel
    have hfac := congrArg (fun x : ℕ => x.factorization 3) E
    have hl0 : (2 : ℕ) ^ m + 1 ≠ 0 := Nat.succ_ne_zero _
    rw [fac_mul3 (a := (2 ^ m + 1) * 244) (b := ∏ p ∈ P, (p + 1))
        (mul_ne_zero hl0 (by norm_num)) hprod1,
      fac_mul3 (a := 2 ^ m + 1) (b := 244) hl0 (by norm_num), h244,
      fac_mul3 (a := 2 ^ (m + 1) * 243) (b := ∏ p ∈ P, p)
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num)) hprod0,
      fac_mul3 (a := 2 ^ (m + 1)) (b := 243) (pow_ne_zero _ (by norm_num)) (by norm_num),
      hpow, h243, hpf, Nat.factorization_prod_apply (g := fun p : ℕ => p + 1) (fun p _ => by omega)] at hfac
    change _ + 0 + (∑ p ∈ P, cost p) = 0 + 5 + 0 at hfac
    omega


  have product_raw (P : Finset ℕ) :
      ∏ p ∈ P, (1 + 1 / (p : ℚ)) = tau ^ (∑ p ∈ P, cost p) * ∏ p ∈ P, raw p := by
    have hr : (∏ p ∈ P, raw p) = (∏ p ∈ P, (1 + 1 / (p : ℚ))) / tau ^ (∑ p ∈ P, cost p) := by
      simp only [raw, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    have he := (div_eq_iff (pow_ne_zero (∑ p ∈ P, cost p) (by norm_num [tau] : tau ≠ 0))).mp hr.symm
    rw [mul_comm] at he
    exact he

  have raw_budget {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
      (hcost : ∑ p ∈ P, cost p ≤ 5) :
      ∏ p ∈ P, (1 + 1 / (p : ℚ)) ≤ tau ^ 5 * ∏ p ∈ P, raw p := by
    rw [product_raw]
    apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_right₀ (by norm_num [tau]) hcost
    · apply Finset.prod_nonneg
      intro p hp
      unfold raw
      have ht : 0 < tau := by norm_num [tau]
      exact div_nonneg (by positivity) (pow_nonneg ht.le _)

  have balance_ratio {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
      (E : (2 ^ m + 1) * 244 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 243 * ∏ p ∈ P, p) :
      (1 + 1 / (2 : ℚ) ^ m) * (244 / 243) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hcast := congrArg (Nat.cast : ℕ → ℚ) E
    push_cast at hcast
    have hprod0 : (∏ p ∈ P, (p : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun p hp => Nat.cast_ne_zero.mpr (hP p hp).ne_zero)
    have hfrac : (∏ p ∈ P, (1 + 1 / (p : ℚ))) =
        (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hP p hp).ne_zero
      field_simp
    rw [hfrac]
    have htwo : (2 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    rw [pow_succ] at hcast
    nlinarith


  have geom_step {c p : ℕ} (hc : 2 ≤ c) (hp : 2 ≤ p) (hcp : 2 * c ≤ p + 1) :
      (1 + 1 / (c : ℚ)) * cap p ≤ cap c := by
    have hcq : (2 : ℚ) ≤ c := by exact_mod_cast hc
    have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp
    have hcpq : 2 * (c : ℚ) ≤ p + 1 := by exact_mod_cast hcp
    have he : 1 + 1 / (c : ℚ) = ((c : ℚ) + 1) / c := by field_simp
    dsimp only [cap]
    rw [he, div_mul_div_comm,
      div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)]
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ c + 1) (by linarith : (0 : ℚ) ≤ p + 1 - 2 * c)]

  have twice_child {c p : ℕ} (hc : c.Prime) (hc2 : c ≠ 2)
      (hp : p.Prime) (hp2 : p ≠ 2) (hd : c ∣ p + 1) : 2 * c ≤ p + 1 := by
    have hpodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hd2 : 2 ∣ p + 1 := by omega
    have hcop : Nat.Coprime 2 c := (hc.coprime_iff_not_dvd.mpr (fun he =>
      hc2 ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_two).mp he))).symm
    exact Nat.le_of_dvd (by omega) (hcop.mul_dvd_of_dvd_of_dvd hd2 hd)

  have compatibility {P : Finset ℕ}
      (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ p ≠ 3)
      (h5 : ∀ p ∈ P, ¬ 5 ∣ p + 1)
      (h61 : ∀ p ∈ P, ¬ 61 ∣ p + 1)
      (h31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 61) :
      ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → r ∣ p + 1 → c ≤ r) →
        raw c * beta p ≤ beta c := by
    intro p hp c hc hd hmin
    obtain ⟨hpp, hp2, hp3⟩ := hP p hp
    obtain ⟨hcp, hc2, hc3⟩ := hP c hc
    have hraw : 0 ≤ raw c := by
      unfold raw
      have ht : 0 < tau := by norm_num [tau]
      exact div_nonneg (by positivity) (pow_nonneg ht.le _)
    by_cases he5 : c = 5
    · subst c
      exact (h5 p hp hd).elim
    by_cases he7 : c = 7
    · subst c
      have hu := parent_7 hpp hp2 hp3 hd
      have hz : cost 7 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 7 * beta 13 = beta 7 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he11 : c = 11
    · subst c
      have hu := parent_11 hpp hp2 hp3 hd hmin
      have hz : cost 11 = 1 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 11 * (16511 / 16125 : ℚ) = beta 11 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he13 : c = 13
    · subst c
      have hu := parent_13 hpp hp2 hp3 hd hmin
      have hz : cost 13 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 13 * (312208 / 308625 : ℚ) = beta 13 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he17 : c = 17
    · subst c
      have hu := parent_17 hpp hp2 hp3 hd hmin
      have hz : cost 17 = 2 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 17 * (64 / 63 : ℚ) = beta 17 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he23 : c = 23
    · subst c
      have hu := parent_23 hpp hp2 hp3 hd hmin
      have hz : cost 23 = 1 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 23 * (376855 / 375296 : ℚ) = beta 23 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he31 : c = 31
    · subst c
      have he := h31 p hp hd
      subst p
      have hz : cost 31 = 0 := by decide +kernel
      norm_num [raw, beta, hz, tau]
    by_cases he43 : c = 43
    · subst c
      have hu := parent_43 hpp hp2 hp3 hd hmin
      have hz : cost 43 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 43 * (1501 / 1500 : ℚ) = beta 43 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he47 : c = 47
    · subst c
      have hu := parent_47 hpp hp2 hp3 hd hmin
      have hz : cost 47 = 1 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 47 * (329 / 324 : ℚ) = beta 47 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he61 : c = 61
    · subst c
      exact (h61 p hp hd).elim
    by_cases he67 : c = 67
    · subst c
      have hu := parent_67 hpp hp2 hp3 hd hmin
      have hz : cost 67 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 67 * (1072 / 1071 : ℚ) = beta 67 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he103 : c = 103
    · subst c
      have hu := parent_103 hpp hp2 hp3 hd hmin
      have hz : cost 103 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 103 * (309206 / 308625 : ℚ) = beta 103 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he127 : c = 127
    · subst c
      have hu := parent_127 hpp hp2 hp3 hd hmin
      have hz : cost 127 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 127 * (4096 / 4095 : ℚ) = beta 127 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he367 : c = 367
    · subst c
      have hu := parent_367 hpp hp2 hp3 hd hmin
      have hz : cost 367 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 367 * (6013295 / 6004736 : ℚ) = beta 367 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he733 : c = 733
    · subst c
      have hu := parent_733 hpp hp2 hp3 hd hmin
      have hz : cost 733 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 733 * (16385 / 16384 : ℚ) = beta 733 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    by_cases he823 : c = 823
    · subst c
      have hu := parent_823 hpp hp2 hp3 hd hmin
      have hz : cost 823 = 0 := by decide +kernel
      have h := mul_le_mul_of_nonneg_left hu hraw
      have he : raw 823 * (1501 / 1500 : ℚ) = beta 823 := by norm_num [raw, beta, hz, tau]
      exact h.trans_eq he
    have hb : beta c = base c := by
      simp only [beta, if_neg hc3, if_neg he5, if_neg he7, if_neg he11, if_neg he13, if_neg he17, if_neg he23, if_neg he31, if_neg he43, if_neg he47, if_neg he61, if_neg he67, if_neg he103, if_neg he127, if_neg he367, if_neg he733, if_neg he823]
    rw [hb]
    dsimp only [raw, base]
    rw [div_mul_eq_mul_div]
    have ht : 0 < tau := by norm_num [tau]
    apply div_le_div_of_nonneg_right _ (pow_nonneg ht.le _)
    exact (mul_le_mul_of_nonneg_left (beta_cap hpp hp2 hp3) (by positivity)).trans
      (geom_step hcp.two_le hpp.two_le (twice_child hcp hc2 hpp hp2 hd))


  let critical : Finset ℕ := {5, 11, 17, 23}

  let leafCap : ℚ := (beta 5 * beta 11 * beta 17 * beta 23) *
      ((beta 7 * beta 31 * beta 127) * (2048 / 2047))

  have leaf_three_small {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
      (hd3 : 3 ∣ p + 1)
      (hl : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 3)
      (hc : p ∉ critical) : beta p ≤ 1 := by
    by_cases h55 : 55 ≤ p
    · exact beta_three hp h2 h3 h55 hd3
    have hp55 : p < 55 := by omega
    have hno5 : ¬ 5 ∣ p + 1 := fun h => by
      have := hl 5 (by norm_num) (by norm_num) h
      norm_num at this
    have hno7 : ¬ 7 ∣ p + 1 := fun h => by
      have := hl 7 (by norm_num) (by norm_num) h
      norm_num at this
    have hz : cost 53 = 3 := by decide +kernel
    interval_cases p <;> norm_num at hp <;> norm_num at h2 <;> norm_num at h3 <;>
      norm_num at hd3 <;> norm_num [critical] at hc <;> norm_num at hno5 <;>
      norm_num at hno7 <;> norm_num [beta, base, hz, tau]

  have critical_bound {X : Finset ℕ}
      (hX : ∀ p ∈ X, p.Prime ∧ p ≠ 2 ∧ p ≠ 3)
      (hd3 : ∀ p ∈ X, 3 ∣ p + 1)
      (hl : ∀ p ∈ X, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 3) :
      ∏ p ∈ X, beta p ≤ beta 5 * beta 11 * beta 17 * beta 23 := by
    have hpos : ∀ p ∈ X, 0 ≤ beta p := fun p hp =>
      (beta_bounds (hX p hp).1 (hX p hp).2.1 (hX p hp).2.2).1.le
    have hA : ∏ p ∈ X, beta p ≤ ∏ p ∈ X ∩ critical, beta p :=
      Finset.prod_le_prod_of_subset_of_le_one (Finset.inter_subset_left : X ∩ critical ⊆ X) hpos
        (fun p hp hnot => leaf_three_small (hX p hp).1 (hX p hp).2.1 (hX p hp).2.2
          (hd3 p hp) (hl p hp) (fun hc => hnot (Finset.mem_inter.mpr ⟨hp, hc⟩)))
    have hB : ∏ p ∈ X ∩ critical, beta p ≤ ∏ p ∈ critical, beta p :=
      Finset.prod_le_prod_of_subset_of_one_le (Finset.inter_subset_right : X ∩ critical ⊆ critical)
        (fun p hp => hpos p (Finset.mem_inter.mp hp).1) (fun p hp _ => by
          simp only [critical, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl <;> norm_num [beta])
    apply (hA.trans hB).trans_eq
    norm_num [critical, beta]

  have leaf_bound {L : Finset ℕ}
      (hL : ∀ p ∈ L, p.Prime ∧ p ≠ 2 ∧ p ≠ 3)
      (hl : ∀ p ∈ L, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 3)
      (hM : ∏ p ∈ L.filter (fun p => ¬ 3 ∣ p + 1), beta p ≤
        (beta 7 * beta 31 * beta 127) * (2048 / 2047)) :
      ∏ p ∈ L, beta p ≤ leafCap := by
    have hA := critical_bound (X := L.filter (fun p => 3 ∣ p + 1))
      (fun p hp => hL p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p hp => hl p (Finset.mem_filter.mp hp).1)
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun p => 3 ∣ p + 1) beta]
    exact mul_le_mul hA hM
      (Finset.prod_nonneg (fun p hp => (beta_bounds (hL p (Finset.mem_filter.mp hp).1).1
        (hL p (Finset.mem_filter.mp hp).1).2.1 (hL p (Finset.mem_filter.mp hp).1).2.2).1.le))
      (by norm_num [beta])

  have final_number : (1 + 1 / (2 : ℚ) ^ 20) * (244 / 243) * (tau ^ 5 * leafCap) < 2 := by
    norm_num [tau, leafCap, beta]

  intro m P hP h3P E hm h5none
  have hK : ∀ c : ℕ, c.Prime → c ∣ 243 → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have hd' : c ∣ 3 ^ 5 := by simpa using hd
    have he := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd')
    simpa using he
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hPT : ∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ p ≠ 3 := by
    intro p hp
    exact ⟨(hP p hp).1, (hP p hp).2, fun he => h3P (he ▸ hp)⟩
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := by simpa
  have h61P : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h61none : ∀ p ∈ P, ¬ 61 ∣ p + 1 :=
    S8 61 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h31unique : ∀ p ∈ P, 31 ∣ p + 1 → p = 61 := fun p hp hd =>
    S3 31 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 61 h61P hd (by norm_num)
  obtain ⟨g, hg⟩ := exists_child ({3} : Finset ℕ)
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := by
    intro p hp he
    obtain ⟨hc, hc2, hc3⟩ := (hg p).2.2.1 he
    exact S1 (g p) hc hc2 hc3 p hp (hg p).1
  have hginj : ∀ p ∈ P, ∀ q ∈ P, g p ∈ P → g p = g q → p = q := by
    intro p hp q hq hgp he
    have hg1 : g p ≠ 1 := fun he => Nat.not_prime_one (he ▸ (hP (g p) hgp).1)
    obtain ⟨hc, hc2, hc3⟩ := (hg p).2.2.1 hg1
    exact S3 (g p) hc hc2 hc3 p hp q hq (hg p).1 (he ▸ (hg q).1)
  have hraw : ∀ p ∈ P, 0 < raw p := by
    intro p hp
    unfold raw
    have ht : 0 < tau := by norm_num [tau]
    exact div_pos (by positivity) (pow_pos ht _)
  have hwf := weighted_forest P g raw beta hraw
    (fun p hp => (beta_bounds (hPT p hp).1 (hPT p hp).2.1 (hPT p hp).2.2).1) hginj
    (fun p hp => (beta_bounds (hPT p hp).1 (hPT p hp).2.1 (hPT p hp).2.2).2.1)
    (fun p hp hgp => compatibility hPT h5none h61none h31unique p hp (g p) hgp (hg p).1
      (fun r hr hr2 hr3 hrd => (hg p).2.2.2 r hr hr2 (hn3 hr3) hrd))
  let L := P.filter (fun p => g p ∉ P)
  have hLP : L ⊆ P := Finset.filter_subset _ _
  have hLT : ∀ p ∈ L, p.Prime ∧ p ≠ 2 ∧ p ≠ 3 := fun p hp => hPT p (hLP hp)
  have hleaf : ∀ p ∈ L, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 3 := by
    intro p hp r hr hr2 hrd
    have hg1 : g p = 1 := by
      by_contra he
      exact (Finset.mem_filter.mp hp).2 (hgP p (hLP hp) he)
    exact Finset.mem_singleton.mp ((hg p).2.1 hg1 r hr hr2 hrd)
  have hM := mersenne_bound beta (L.filter (fun p => ¬ 3 ∣ p + 1))
    (fun p hp => (hLT p (Finset.mem_filter.mp hp).1).1)
    (fun p hp => two_pow_of_no_odd_prime (fun r hr hr2 hrd =>
      (Finset.mem_filter.mp hp).2 ((hleaf p (Finset.mem_filter.mp hp).1 r hr hr2 hrd) ▸ hrd)))
    (fun p hp => ⟨(beta_bounds (hLT p (Finset.mem_filter.mp hp).1).1
      (hLT p (Finset.mem_filter.mp hp).1).2.1 (hLT p (Finset.mem_filter.mp hp).1).2.2).1,
      beta_cap (hLT p (Finset.mem_filter.mp hp).1).1
        (hLT p (Finset.mem_filter.mp hp).1).2.1 (hLT p (Finset.mem_filter.mp hp).1).2.2⟩)
    (by norm_num [beta])
  have hM' : ∏ p ∈ L.filter (fun p => ¬ 3 ∣ p + 1), beta p ≤
      (beta 7 * beta 31 * beta 127) * (2048 / 2047) := by
    simpa only [show beta 3 = 1 from by norm_num [beta], one_mul] using hM
  have hleafB := leaf_bound hLT hleaf hM'
  have hcost := ledger (fun p hp => ⟨(hPT p hp).1, (hPT p hp).2.2⟩) E
  have hX : ∏ p ∈ P, (1 + 1 / (p : ℚ)) ≤ tau ^ 5 * leafCap := by
    apply (raw_budget (fun p hp => (hP p hp).1) hcost).trans
    exact mul_le_mul_of_nonneg_left (hwf.trans hleafB) (by norm_num [tau])
  have hpow : (2 : ℚ) ^ 20 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hmu : (1 + 1 / (2 : ℚ) ^ m) ≤ 1 + 1 / (2 : ℚ) ^ 20 := by
    exact add_le_add (le_refl 1)
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow)
  have hbalance := balance_ratio (fun p hp => (hP p hp).1) E
  have hfinal : (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ 20) * (244 / 243) * (tau ^ 5 * leafCap) := by
    calc (2 : ℚ) = (1 + 1 / (2 : ℚ) ^ m) * (244 / 243) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) := hbalance.symm
      _ ≤ (1 + 1 / (2 : ℚ) ^ 20) * (244 / 243) * (tau ^ 5 * leafCap) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hmu (by norm_num)) hX
          (Finset.prod_nonneg (fun p hp => by positivity)) (by norm_num)
  exact (not_le_of_gt final_number) hfinal


lemma u1_kill_e5_mod4 {m : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * 244 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 243 * ∏ p ∈ P, p)
    (hm : 20 ≤ m) (hmod : m % 4 = 2) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 243 → c ∈ ({3} : Finset ℕ) := by
    intro c hc hd
    have hd' : c ∣ 3 ^ 5 := by simpa using hd
    have he := (Nat.prime_dvd_prime_iff_eq hc Nat.prime_three).mp (hc.dvd_of_dvd_pow hd')
    simpa using he
  obtain ⟨-, -, -, S4, -, -, -, -⟩ := facts hP hK E
  have h5two : 5 ∣ 2 ^ m + 1 := by
    have := two_pow_add_one_dvd_of_odd_mul (d := 2) (m := m) (by omega)
    norm_num at this
    exact this
  exact u1_kill_e5_no_five_consumer hP h3P E hm
    (S4 5 (by norm_num) (by norm_num) (by simp) h5two)


def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 → 262 ≤ padicValNat 2 n →
    padicValNat 2 n % 8 = 4 → padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 → 262 ≤ padicValNat 2 n →
    padicValNat 2 n % 16 = 8 → padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n hn hiff he h262 heven hn16 _ _ => ?_⟩
  by_cases hm2 : padicValNat 2 n % 4 = 2
  · exfalso
    have hn0 : n ≠ 0 := hn.2.ne'
    have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), hn0⟩
    have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
      intro r hr hr2 hr3
      have hpr := Nat.prime_of_mem_primeFactors hr
      have hpos := hpr.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
      have hn2 : ¬ 2 ≤ n.factorization r := by
        intro hle
        exact hr3 ((hiff r).mp ⟨hpr, hr2, (hpr.pow_dvd_iff_le_factorization hn0).mpr hle⟩)
      omega
    obtain ⟨hP, hE⟩ := kernel_balance_one hn h3pf (by norm_num) hs
    rw [he, Nat.factorization_def n Nat.prime_two] at hE
    rw [show (1 + 3 ^ 5 : ℕ) = 244 from by norm_num,
      show (3 ^ 5 : ℕ) = 243 from by norm_num] at hE
    exact u1_kill_e5_mod4 hP (by simp) hE (by omega) hm2
  · by_cases hm4 : padicValNat 2 n % 8 = 4
    · exact (h1 n hn hiff he h262 hm4).trans (le_max_left _ _)
    · exact (h2 n hn hiff he h262 (by omega)).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
