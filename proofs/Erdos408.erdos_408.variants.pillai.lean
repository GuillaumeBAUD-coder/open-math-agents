import FormalConjectures.ErdosProblems.«408»

/-! The corrected totient height is additive, which controls the lower bound. -/

open Erdos408

lemma OMA.totient_hit (m : ℕ) (hm : 0 < m) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.totient^[k] m = 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h : m = 1
    · subst m
      exact ⟨1, le_rfl, by simp⟩
    have hgt : 1 < m := by omega
    obtain ⟨k, hk, hiter⟩ := ih m.totient (Nat.totient_lt m hgt) (Nat.totient_pos.mpr hm)
    exact ⟨k + 1, by omega, by rw [Function.iterate_succ_apply, hiter]⟩

lemma OMA.totient_height_spec (m : ℕ) (hm : 0 < m) :
    1 ≤ f m ∧ Nat.totient^[f m] m = 1 :=
  Nat.sInf_mem (OMA.totient_hit m hm)

lemma OMA.totient_step (m : ℕ) (hm : 2 < m) : f m = f m.totient + 1 := by
  have hm0 : 0 < m := by omega
  have hp0 : 0 < m.totient := Nat.totient_pos.mpr hm0
  have hp1 : m.totient ≠ 1 := by
    intro h
    rcases Nat.totient_eq_one_iff.mp h with h | h <;> omega
  obtain ⟨hpos, hφ⟩ := OMA.totient_height_spec m.totient hp0
  apply le_antisymm
  · exact Nat.sInf_le (show 1 ≤ f m.totient + 1 ∧
      Nat.totient^[f m.totient + 1] m = 1 from
        ⟨by omega, by rw [Function.iterate_succ_apply, hφ]⟩)
  · refine le_csInf (OMA.totient_hit m hm0) ?_
    rintro (k | k) ⟨hk, hiter⟩
    · omega
    · have htail : Nat.totient^[k] m.totient = 1 := by
        simpa only [Function.iterate_succ_apply] using hiter
      have hk' : 1 ≤ k := by
        by_contra! h
        have hk0 : k = 0 := by omega
        subst k
        exact hp1 (by simpa using htail)
      exact Nat.succ_le_succ (Nat.sInf_le (show 1 ≤ k ∧
        Nat.totient^[k] m.totient = 1 from ⟨hk', htail⟩))

noncomputable def OMA.corrected_height (m : ℕ) : ℕ :=
  f m - if Odd m then 1 else 0

lemma OMA.corrected_one : OMA.corrected_height 1 = 0 := by
  norm_num [OMA.corrected_height, f_one, Nat.odd_iff]

lemma OMA.corrected_two : OMA.corrected_height 2 = 1 := by
  norm_num [OMA.corrected_height, f_two, Nat.odd_iff]

lemma OMA.corrected_step (m : ℕ) (hm : 0 < m) :
    OMA.corrected_height m = OMA.corrected_height m.totient + if Even m then 1 else 0 := by
  by_cases h1 : m = 1
  · subst m
    simp [OMA.corrected_one]
  by_cases h2 : m = 2
  · subst m
    simp [OMA.corrected_one, OMA.corrected_two]
  have hgt : 2 < m := by omega
  have he : Even m.totient := Nat.totient_even hgt
  have hno : ¬ Odd m.totient := Nat.not_odd_iff_even.mpr he
  by_cases hmEven : Even m
  · simp only [OMA.corrected_height, if_neg (Nat.not_odd_iff_even.mpr hmEven),
      if_neg hno, if_pos hmEven, Nat.sub_zero, OMA.totient_step m hgt]
  · simp only [OMA.corrected_height, if_pos (Nat.not_even_iff_odd.mp hmEven),
      if_neg hno, if_neg hmEven, Nat.sub_zero, OMA.totient_step m hgt,
      Nat.add_sub_cancel, Nat.add_zero]

lemma OMA.corrected_prime_odd (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    OMA.corrected_height p = OMA.corrected_height (p - 1) := by
  have hne : ¬ Even p := Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two h2)
  rw [OMA.corrected_step p hp.pos, if_neg hne, Nat.add_zero, Nat.totient_prime hp]

lemma OMA.corrected_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    OMA.corrected_height (a * b) = OMA.corrected_height a + OMA.corrected_height b := by
  have hforall (z : ℕ) : ∀ a b : ℕ, 0 < a → 0 < b → a * b = z →
      OMA.corrected_height (a * b) = OMA.corrected_height a + OMA.corrected_height b := by
    induction z using Nat.strong_induction_on with
    | h z ih =>
      have smaller (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (huv : u * v < z) :
          OMA.corrected_height (u * v) = OMA.corrected_height u + OMA.corrected_height v :=
        ih (u * v) huv u v hu hv rfl
      have primeStep (p b : ℕ) (hp : p.Prime) (hb : 0 < b) (hz : p * b = z) :
          OMA.corrected_height (p * b) = OMA.corrected_height p + OMA.corrected_height b := by
        have hp_b : 0 < p * b := Nat.mul_pos hp.pos hb
        have hp_b_gt : 1 < p * b := hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hb)
        have hltφ : (p * b).totient < z := hz ▸ Nat.totient_lt _ hp_b_gt
        have hφb : 0 < b.totient := Nat.totient_pos.mpr hb
        by_cases hp2 : p = 2
        · subst p
          have he2 : Even (2 * b) := even_iff_two_dvd.mpr (dvd_mul_right _ _)
          by_cases he : Even b
          · have hφ := Nat.totient_two_mul_of_even he
            have hmul := smaller 2 b.totient (by decide) hφb (hφ ▸ hltφ)
            rw [OMA.corrected_step _ hp_b, OMA.corrected_step b hb, if_pos he2, if_pos he,
              hφ, hmul, OMA.corrected_two]
            omega
          · rw [OMA.corrected_step _ hp_b, OMA.corrected_step b hb, if_pos he2, if_neg he,
              Nat.totient_two_mul_of_odd (Nat.not_even_iff_odd.mp he), OMA.corrected_two]
            omega
        · have heq : Even (p * b) ↔ Even b := by
            rw [← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even, Nat.odd_mul]
            simp only [hp.odd_of_ne_two hp2, true_and]
          have hp_height := OMA.corrected_prime_odd p hp hp2
          by_cases hdiv : p ∣ b
          · have hφ := Nat.totient_mul_of_prime_of_dvd hp hdiv
            have hmul := smaller p b.totient hp.pos hφb (hφ ▸ hltφ)
            rw [OMA.corrected_step _ hp_b, OMA.corrected_step b hb, hφ, hmul]
            simp only [heq]
            omega
          · have hφ := Nat.totient_mul_of_prime_of_not_dvd hp hdiv
            have hmul := smaller (p - 1) b.totient (by have := hp.one_lt; omega)
              hφb (hφ ▸ hltφ)
            rw [OMA.corrected_step _ hp_b, OMA.corrected_step b hb, hφ, hmul, ← hp_height]
            simp only [heq]
            omega
      intro a b ha hb hz
      by_cases ha1 : a = 1
      · simp [ha1, OMA.corrected_one]
      by_cases hb1 : b = 1
      · simp [hb1, OMA.corrected_one]
      obtain ⟨p, hp, d, hd⟩ := Nat.exists_prime_and_dvd ha1
      have hdpos : 0 < d := by
        by_contra! hn
        have hd0 : d = 0 := by omega
        simp [hd0] at hd
        omega
      have hdb : 0 < d * b := Nat.mul_pos hdpos hb
      have hz' : p * (d * b) = z := by rw [← Nat.mul_assoc, ← hd, hz]
      have hdlt : d * b < z := by
        rw [← hz']
        simpa only [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right hp.one_lt hdb
      have halt : p * d < z := by
        rw [← hd, ← hz]
        simpa only [Nat.mul_one] using
          Nat.mul_lt_mul_of_pos_left (show 1 < b by omega) ha
      calc
        _ = OMA.corrected_height (p * (d * b)) := by rw [← Nat.mul_assoc, ← hd]
        _ = OMA.corrected_height p + OMA.corrected_height (d * b) :=
          primeStep p (d * b) hp hdb hz'
        _ = _ := by rw [smaller d b hdpos hb hdlt, ← Nat.add_assoc,
          ← smaller p d hp.pos hdpos halt, ← hd]
  exact hforall (a * b) a b ha hb rfl

lemma OMA.corrected_exponential (m : ℕ) (hm : 0 < m) :
    m ≤ 3 ^ OMA.corrected_height m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · simp [hm1, OMA.corrected_one]
    obtain ⟨p, hp, d, hd⟩ := Nat.exists_prime_and_dvd hm1
    have hdpos : 0 < d := by
      by_contra! h
      have hd0 : d = 0 := by omega
      simp [hd0] at hd
      omega
    by_cases hd1 : d = 1
    · have hmp : m = p := by simpa only [hd1, Nat.mul_one] using hd
      by_cases hp2 : p = 2
      · simp [hmp, hp2, OMA.corrected_two]
      obtain ⟨t, ht⟩ := (even_iff_exists_two_mul.mp (hp.even_sub_one hp2))
      have htpos : 0 < t := by have := hp.one_lt; omega
      have htl : t < m := by omega
      have ht_bound := ih t htl htpos
      have hc : OMA.corrected_height p = OMA.corrected_height t + 1 := by
        rw [OMA.corrected_prime_odd p hp hp2, ht,
          OMA.corrected_mul 2 t (by decide) htpos, OMA.corrected_two, Nat.add_comm]
      rw [hmp, hc, pow_succ']
      have hpos : 0 < (3 : ℕ) ^ OMA.corrected_height t := by positivity
      omega
    · have hp_lt : p < m := by
        rw [hd]
        simpa only [Nat.mul_one] using
          Nat.mul_lt_mul_of_pos_left (show 1 < d by omega) hp.pos
      have hd_lt : d < m := by
        rw [hd]
        simpa only [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right hp.one_lt hdpos
      calc
        m = p * d := hd
        _ ≤ (3 ^ OMA.corrected_height p) * (3 ^ OMA.corrected_height d) :=
          Nat.mul_le_mul (ih p hp_lt hp.pos) (ih d hd_lt hdpos)
        _ = _ := by rw [hd, OMA.corrected_mul p d hp.pos hdpos, pow_add]

lemma OMA.even_totient_le (m : ℕ) (hm : 0 < m) (he : Even m) :
    2 * m.totient ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp he
    have htpos : 0 < t := by omega
    have htl : t < m := by omega
    by_cases hte : Even t
    · have h := ih t htl htpos hte
      rw [ht, Nat.totient_two_mul_of_even hte]
      omega
    · rw [ht, Nat.totient_two_mul_of_odd (Nat.not_even_iff_odd.mp hte)]
      exact Nat.mul_le_mul_left _ (Nat.totient_le _)

lemma OMA.totient_even_power (m : ℕ) (hm : 0 < m) (he : Even m) :
    2 ^ f m ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm2 : m = 2
    · simp [hm2, f_two]
    have hgt : 2 < m := by
      obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp he
      omega
    have hφp : 0 < m.totient := Nat.totient_pos.mpr hm
    have hφ := ih m.totient (Nat.totient_lt m (by omega)) hφp (Nat.totient_even hgt)
    rw [OMA.totient_step m hgt, pow_succ']
    exact (Nat.mul_le_mul_left 2 hφ).trans (OMA.even_totient_le m hm he)

theorem OMA.solution : type_of% @Erdos408.erdos_408.variants.pillai := by
  intro n hn
  have hnpos : 0 < n := by omega
  have hfpos : 1 ≤ f n := (OMA.totient_height_spec n hnpos).1
  let k := f n - 1
  have hk : k + 1 = f n := by dsimp only [k]; omega
  have hupper : 2 ^ k ≤ n := by
    by_cases he : Even n
    · exact (Nat.pow_le_pow_right (by decide) (show k ≤ f n by omega)).trans
        (OMA.totient_even_power n hnpos he)
    · have hgt : 2 < n := by
        by_contra! h
        have hn2 : n = 2 := by omega
        exact he (hn2 ▸ (by decide : Even 2))
      have hk_eq : k = f n.totient := by
        dsimp only [k]
        rw [OMA.totient_step n hgt, Nat.add_sub_cancel]
      rw [hk_eq]
      exact (OMA.totient_even_power n.totient (Nat.totient_pos.mpr hnpos)
        (Nat.totient_even hgt)).trans (Nat.totient_le _)
  have hlower : n ≤ 2 * 3 ^ k := by
    by_cases he : Even n
    · obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp he
      have htpos : 0 < t := by omega
      have hcf : OMA.corrected_height n = f n := by
        simp only [OMA.corrected_height, if_neg (Nat.not_odd_iff_even.mpr he), Nat.sub_zero]
      have hct : k = OMA.corrected_height t := by
        dsimp only [k]
        rw [← hcf, ht, OMA.corrected_mul 2 t (by decide) htpos, OMA.corrected_two]
        omega
      rw [ht, hct]
      exact Nat.mul_le_mul_left 2 (OMA.corrected_exponential t htpos)
    · have hc : OMA.corrected_height n = k := by
        simp only [OMA.corrected_height, if_pos (Nat.not_even_iff_odd.mp he), k]
      have h : n ≤ 3 ^ k := hc ▸ OMA.corrected_exponential n hnpos
      exact h.trans (Nat.le_mul_of_pos_left _ (by decide))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
  constructor
  · have hcast : (n : ℝ) ≤ (2 : ℝ) * (3 : ℝ) ^ k := by exact_mod_cast hlower
    have hlog := Real.log_le_log hnpos' hcast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (3 : ℝ) ^ k ≠ 0),
      Real.log_pow] at hlog
    have hratio : (Real.log n - Real.log 2) / Real.log 3 ≤ (k : ℝ) :=
      (div_le_iff₀ hlog3).mpr (by linarith)
    exact (Nat.succ_le_succ (Nat.floor_le_of_le hratio)).trans_eq hk
  · have hcast : (2 : ℝ) ^ k ≤ (n : ℝ) := by exact_mod_cast hupper
    have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ k) hcast
    rw [Real.log_pow] at hlog
    have hratio : (k : ℝ) ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2).mpr hlog
    exact hk.symm.trans_le (Nat.succ_le_succ (Nat.le_floor hratio))