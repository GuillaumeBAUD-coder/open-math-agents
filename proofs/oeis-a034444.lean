import OMAStatements.S_oeis_a034444

namespace OMA.A034444Proof

open OMA.S_oeis_a034444

private lemma exists_two_pow_mul_odd :
    ∀ n : ℕ, 0 < n → ∃ a m : ℕ, Odd m ∧ n = 2 ^ a * m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
    · have hkpos : 0 < k := by omega
      have hkn : k < n := by omega
      obtain ⟨a, m, hm, hkm⟩ := ih k hkn hkpos
      refine ⟨a + 1, m, hm, ?_⟩
      rw [hk, hkm, pow_succ', ← two_mul, mul_assoc]
    · exact ⟨0, n, hodd, by simp⟩

private lemma odd_of_dvd_odd {d n : ℕ} (hdvd : d ∣ n) (hn : Odd n) : Odd d := by
  rcases Nat.even_or_odd d with ⟨c, hc⟩ | hodd
  · exfalso
    obtain ⟨q, rfl⟩ := hdvd
    obtain ⟨r, hr⟩ := hn
    have h2 : 2 ∣ d * q := ⟨c * q, by rw [hc, ← two_mul, mul_assoc]⟩
    obtain ⟨t, ht⟩ := h2
    omega
  · exact hodd

private lemma not_odd_of_two_dvd {x : ℕ} (h : 2 ∣ x) : ¬ Odd x := by
  rintro ⟨r, hr⟩
  obtain ⟨t, ht⟩ := h
  omega

private lemma coprime_two_pow_of_odd {a m : ℕ} (hm : Odd m) : Nat.Coprime (2 ^ a) m := by
  have h2m : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  exact h2m.pow_left a

private lemma mul_sum_nat (s : Finset ℕ) (c : ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ s, c * f x = c * ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, mul_add]

theorem main_proof : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
    (∑ d ∈ (unitary n).filter Odd, d ^ k) ∣ ∑ d ∈ unitary n, d ^ k := by
  intro n hn k
  obtain ⟨a, m, hm_odd, hn_eq⟩ := exists_two_pow_mul_odd n hn
  cases a with
  | zero =>
    have hn_odd : Odd n := by rw [hn_eq]; simpa using hm_odd
    have hfilt : (unitary n).filter Odd = unitary n := by
      apply Finset.filter_true_of_mem
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      exact odd_of_dvd_odd hdvd hn_odd
    rw [hfilt]
  | succ a' =>
    set p : ℕ := 2 ^ (a' + 1)
    have hp_pos : 0 < p := Nat.pow_pos (by decide)
    have hp_two : 2 ∣ p := ⟨2 ^ a', by dsimp only [p]; rw [pow_succ']⟩
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hn_eq; omega
      · exact hpos
    have hpm_cop : Nat.Coprime p m := coprime_two_pow_of_odd hm_odd
    set O := (unitary n).filter Odd
    set E := (unitary n).filter (fun d => ¬ Odd d)
    have hsplit : (∑ d ∈ O, d ^ k) + (∑ d ∈ E, d ^ k) = ∑ d ∈ unitary n, d ^ k :=
      Finset.sum_filter_add_sum_filter_not (unitary n) Odd (fun d => d ^ k)
    have hE_eq : E = O.image (fun d => p * d) := by
      ext e
      simp only [E, O, unitary, Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨⟨he_dvd, _⟩, he_cop⟩, he_not_odd⟩
        have he_two : 2 ∣ e := by
          rcases Nat.even_or_odd e with ⟨c, hc⟩ | hodd
          · exact ⟨c, by omega⟩
          · exact absurd hodd he_not_odd
        have hq_odd : Odd (n / e) := by
          rcases Nat.even_or_odd (n / e) with ⟨c, hc⟩ | hodd
          · exfalso
            have h2q : 2 ∣ n / e := ⟨c, by omega⟩
            have h2g : 2 ∣ Nat.gcd e (n / e) := Nat.dvd_gcd he_two h2q
            rw [he_cop.gcd_eq_one] at h2g
            exact absurd (Nat.le_of_dvd (by decide) h2g) (by decide)
          · exact hodd
        have hp_cop_q : Nat.Coprime p (n / e) := coprime_two_pow_of_odd hq_odd
        have hp_dvd_eq : p ∣ e * (n / e) := by
          rw [Nat.mul_div_cancel' he_dvd, hn_eq]
          exact dvd_mul_right p m
        have hp_dvd_e : p ∣ e := hp_cop_q.dvd_of_dvd_mul_right hp_dvd_eq
        obtain ⟨d, rfl⟩ := hp_dvd_e
        have hdm : d * (n / (p * d)) = m := by
          apply Nat.eq_of_mul_eq_mul_left hp_pos
          rw [← mul_assoc, Nat.mul_div_cancel' he_dvd, hn_eq]
        have hd_dvd_m : d ∣ m := ⟨n / (p * d), hdm.symm⟩
        have hd_odd : Odd d := odd_of_dvd_odd hd_dvd_m hm_odd
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_m hm_pos
        have hd_dvd_n : d ∣ n := dvd_trans hd_dvd_m (hn_eq ▸ dvd_mul_left m p)
        have hnd : n / d = p * (n / (p * d)) := by
          apply Nat.eq_of_mul_eq_mul_left hd_pos
          rw [Nat.mul_div_cancel' hd_dvd_n, ← mul_assoc, mul_comm d p, mul_assoc, hdm, hn_eq]
        have hd_cop_p : Nat.Coprime d p := (coprime_two_pow_of_odd hd_odd).symm
        have hd_cop_q : Nat.Coprime d (n / (p * d)) :=
          he_cop.coprime_dvd_left (dvd_mul_left d p)
        refine ⟨d, ⟨⟨⟨hd_dvd_n, hn.ne'⟩, ?_⟩, hd_odd⟩, rfl⟩
        rw [hnd]
        exact hd_cop_p.mul_right hd_cop_q
      · rintro ⟨d, ⟨⟨⟨hd_dvd_n, _⟩, hd_cop⟩, hd_odd⟩, rfl⟩
        have hd_cop_p : Nat.Coprime d p := (coprime_two_pow_of_odd hd_odd).symm
        have hd_dvd_m : d ∣ m := hd_cop_p.dvd_of_dvd_mul_left (hn_eq ▸ hd_dvd_n)
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_m hm_pos
        obtain ⟨q, hq⟩ := hd_dvd_m
        have hpd_dvd_n : p * d ∣ n := ⟨q, by rw [hn_eq, hq, mul_assoc]⟩
        have hpd_pos : 0 < p * d := Nat.mul_pos hp_pos hd_pos
        have hnpd : n / (p * d) = q := by
          apply Nat.eq_of_mul_eq_mul_left hpd_pos
          rw [Nat.mul_div_cancel' hpd_dvd_n, hn_eq, hq, mul_assoc]
        have hnd : n / d = p * q := by
          apply Nat.eq_of_mul_eq_mul_left hd_pos
          rw [Nat.mul_div_cancel' hd_dvd_n, hn_eq, hq, ← mul_assoc, mul_comm p d, mul_assoc]
        have hd_cop_q : Nat.Coprime d q := by
          rw [hnd] at hd_cop
          exact hd_cop.coprime_dvd_right (dvd_mul_left q p)
        have hp_cop_q : Nat.Coprime p q :=
          hpm_cop.coprime_dvd_right ⟨d, by rw [hq, mul_comm]⟩
        refine ⟨⟨⟨hpd_dvd_n, hn.ne'⟩, ?_⟩, not_odd_of_two_dvd (dvd_mul_of_dvd_left hp_two d)⟩
        rw [hnpd]
        exact hp_cop_q.mul_left hd_cop_q
    have hE_sum : ∑ e ∈ E, e ^ k = p ^ k * ∑ d ∈ O, d ^ k := by
      rw [hE_eq, Finset.sum_image]
      · simp_rw [mul_pow]
        exact mul_sum_nat O (p ^ k) (fun d => d ^ k)
      · intro x _ y _ hxy
        exact Nat.eq_of_mul_eq_mul_left hp_pos hxy
    rw [← hsplit, hE_sum]
    refine ⟨1 + p ^ k, ?_⟩
    rw [mul_add, mul_one, mul_comm (∑ d ∈ O, d ^ k) (p ^ k)]

end OMA.A034444Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a034444.main :=
  OMA.A034444Proof.main_proof
