import OMAStatements.S_oeis_a307864
import Mathlib

namespace OMA.S_oeis_a307864

lemma two_dvd (d n a : ℕ) (hd : d ∣ 2 * n + 1) (h1 : a ≡ 1 [MOD d]) (h2 : a ≡ 2 * n [MOD d]) :
    d ∣ 2 := by
  have h3 : 1 ≡ 2 * n [MOD d] := h1.symm.trans h2
  have h4 := (Nat.modEq_iff_dvd.1 h3)
  have h5 : (d : ℤ) ∣ ((2 * n + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hd
  have h6 : (d : ℤ) ∣ 2 := by
    have h7 := dvd_sub h5 h4
    push_cast at h7
    have e2 : ((2 : ℤ) * n + 1 - (2 * n - 1)) = 2 := by ring
    rwa [e2] at h7
  exact_mod_cast h6

lemma pp_case (p e n : ℕ) (hp : p.Prime) (he : 2 ≤ e) (hm : p ^ e = 2 * n + 1)
    (H : ∀ b : ℕ, Nat.Coprime b (2 * n + 1) →
      (b ^ n ≡ 1 [MOD 2 * n + 1] ∨ b ^ n ≡ 2 * n [MOD 2 * n + 1])) : False := by
  set x := p ^ (e - 1) with hx
  have hxx : x * p = p ^ e := by rw [hx, ← pow_succ]; congr 1; omega
  have hpm : p ∣ 2 * n + 1 := by rw [← hm]; exact dvd_pow_self p (by omega)
  have hpx : p ∣ x := dvd_pow_self p (by omega)
  have hxpos : 0 < x := pow_pos hp.pos _
  have hcop : Nat.Coprime (1 + x) (2 * n + 1) := by
    rw [← hm]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    rw [add_comm] at h
    have := (Nat.dvd_add_right hpx).1 h
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hdv : ((p : ℤ) ^ e) ∣ (x : ℤ) ^ 2 := by
    have : (x : ℤ) ^ 2 = (p : ℤ) ^ (2 * (e - 1)) := by rw [hx]; push_cast; ring
    rw [this]
    exact pow_dvd_pow _ (by omega)
  have key : ∀ k : ℕ, ((p : ℤ) ^ e) ∣ ((1 + x : ℤ)) ^ k - (1 + k * x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have : ((1 + x : ℤ)) ^ (k + 1) - (1 + ((k + 1 : ℕ) : ℤ) * x) =
          (1 + x) * (((1 + x : ℤ)) ^ k - (1 + k * x)) + k * (x : ℤ) ^ 2 := by push_cast; ring
      rw [this]
      exact dvd_add (Dvd.dvd.mul_left ih _) (Dvd.dvd.mul_left hdv _)
  have hme : ((p : ℤ) ^ e) = ((2 * n + 1 : ℕ) : ℤ) := by rw [← hm]; push_cast; ring
  have hk := key n
  have hpx' : (p : ℤ) ∣ (x : ℤ) := Int.natCast_dvd_natCast.2 hpx
  have hpm' : (p : ℤ) ∣ ((2 * n + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hpm
  have hpe : (p : ℤ) ∣ (p : ℤ) ^ e := dvd_pow_self _ (by omega)
  rcases H (1 + x) hcop with h | h
  · have h1 := Nat.modEq_iff_dvd.1 h
    rw [← hme] at h1
    push_cast at h1
    have h2 := dvd_add h1 hk
    have e1 : (1 : ℤ) - (1 + x) ^ n + ((1 + x) ^ n - (1 + n * x)) = -(n * x) := by ring
    rw [e1] at h2
    have h3 : ((x : ℤ) * p) ∣ (n : ℤ) * x := by
      have : ((x : ℤ) * p) = (p : ℤ) ^ e := by exact_mod_cast hxx
      rw [this]; simpa using h2
    have h4 : (p : ℤ) ∣ n := by
      have : (x : ℤ) * p ∣ x * n := by simpa [mul_comm] using h3
      have hx0 : (x : ℤ) ≠ 0 := by exact_mod_cast hxpos.ne'
      exact (mul_dvd_mul_iff_left hx0).1 this
    have h5 : (p : ℤ) ∣ 2 * n := dvd_mul_of_dvd_right h4 _
    have h6 := dvd_sub hpm' h5
    push_cast at h6
    have e2 : (2 : ℤ) * n + 1 - 2 * n = 1 := by ring
    rw [e2] at h6
    have h7 : p ∣ 1 := by exact_mod_cast h6
    exact hp.one_lt.ne' (Nat.dvd_one.1 h7)
  · have h1 := Nat.modEq_iff_dvd.1 h
    rw [← hme] at h1
    push_cast at h1
    have h2 := dvd_add h1 hk
    have e1 : (2 * (n : ℤ) - (1 + x) ^ n) + ((1 + x) ^ n - (1 + n * x)) = 2 * n - 1 - n * x := by ring
    rw [e1] at h2
    have h3 : (p : ℤ) ∣ 2 * n - 1 - n * x := dvd_trans hpe h2
    have h4 : (p : ℤ) ∣ (n : ℤ) * x := dvd_mul_of_dvd_right hpx' _
    have h5 := dvd_add (dvd_sub hpm' h3) h4
    push_cast at h5
    have h6 : (p : ℤ) ∣ 2 := by
      have e4 : ((2 * (n : ℤ) + 1 - (2 * n - 1 - n * x)) + n * x) = 2 + 2 * (n * x) := by ring
      rw [e4] at h5
      have h7 : (p : ℤ) ∣ 2 * (n * x) := dvd_mul_of_dvd_right h4 _
      have h8 := dvd_sub h5 h7
      have e5 : ((2 : ℤ) + 2 * (n * x) - 2 * (n * x)) = 2 := by ring
      rwa [e5] at h8
    have h9 : p ∣ 2 := by exact_mod_cast h6
    have h10 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h9
    have h11 : p = 2 := le_antisymm h10 hp.two_le
    subst h11
    omega

lemma all_one (n : ℕ) (hn : 1 ≤ n) (hnp : ¬ Nat.Prime (2 * n + 1))
    (H : ∀ b : ℕ, Nat.Coprime b (2 * n + 1) →
      (b ^ n ≡ 1 [MOD 2 * n + 1] ∨ b ^ n ≡ 2 * n [MOD 2 * n + 1])) :
    ∀ b : ℕ, Nat.Coprime b (2 * n + 1) → b ^ n ≡ 1 [MOD 2 * n + 1] := by
  intro b0 hb0
  rcases H b0 hb0 with h | h
  · exact h
  exfalso
  have hm0 : 2 * n + 1 ≠ 0 := by omega
  have hm1 : 2 * n + 1 ≠ 1 := by omega
  have hp := Nat.minFac_prime hm1
  set p := (2 * n + 1).minFac with hpdef
  set e := (2 * n + 1).factorization p with hedef
  have hpd : p ∣ 2 * n + 1 := Nat.minFac_dvd _
  have he1 : 1 ≤ e := (hp.factorization_pos_of_dvd hm0 hpd)
  have hmm : p ^ e * ((2 * n + 1) / p ^ e) = 2 * n + 1 :=
    Nat.mul_div_cancel' (Nat.ordProj_dvd _ p)
  have hco : Nat.Coprime (p ^ e) ((2 * n + 1) / p ^ e) :=
    Nat.Coprime.pow_left e (Nat.coprime_ordCompl hp hm0)
  set m' := (2 * n + 1) / p ^ e with hm'def
  clear_value m' e p
  by_cases hm'1 : m' = 1
  · have hpe : p ^ e = 2 * n + 1 := by rw [hm'1] at hmm; simpa using hmm
    have he2 : 2 ≤ e := by
      by_contra hlt
      have : e = 1 := by omega
      rw [this, pow_one] at hpe
      exact hnp (hpe ▸ hp)
    exact pp_case p e n hp he2 hpe H
  · have hm'0 : m' ≠ 0 := by
      intro h0; rw [h0] at hmm; omega
    have hm'd : m' ∣ 2 * n + 1 := Dvd.intro_left _ hmm
    have hpd2 : p ^ e ∣ 2 * n + 1 := Dvd.intro _ hmm
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco 1 b0
    have hcop1 : Nat.Coprime k (p ^ e) := by
      have := hk1.gcd_eq
      unfold Nat.Coprime; rw [this]; simp
    have hcop2 : Nat.Coprime k m' := by
      have := hk2.gcd_eq
      unfold Nat.Coprime; rw [this]
      exact Nat.Coprime.coprime_dvd_right hm'd hb0
    have hcopk : Nat.Coprime k (2 * n + 1) := by
      rw [← hmm]; exact Nat.Coprime.mul_right hcop1 hcop2
    rcases H k hcopk with h1 | h1
    · have a1 : k ^ n ≡ 1 [MOD m'] := Nat.ModEq.of_dvd hm'd h1
      have a2 : k ^ n ≡ b0 ^ n [MOD m'] := hk2.pow n
      have a3 : b0 ^ n ≡ 2 * n [MOD m'] := Nat.ModEq.of_dvd hm'd h
      have a4 : (k ^ n) ≡ 2 * n [MOD m'] := a2.trans a3
      have := two_dvd m' n _ hm'd a1 a4
      have h2 : m' ≤ 2 := Nat.le_of_dvd (by norm_num) this
      have h3 : m' = 2 := by omega
      rw [h3] at hm'd
      omega
    · have a1 : k ^ n ≡ 1 [MOD p ^ e] := by
        have := hk1.pow n
        simpa using this
      have a4 : (k ^ n) ≡ 2 * n [MOD p ^ e] := Nat.ModEq.of_dvd hpd2 h1
      have := two_dvd (p ^ e) n _ hpd2 a1 a4
      have h5 : p ∣ 2 := dvd_trans (dvd_pow_self p (by omega)) this
      have h10 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h5
      have h11 : p = 2 := le_antisymm h10 hp.two_le
      rw [h11] at hpd
      omega

end OMA.S_oeis_a307864

theorem OMA.solution : type_of% @OMA.S_oeis_a307864.main := by
  intro n hn
  obtain ⟨hn1, hnp, H⟩ := hn
  have hall := OMA.S_oeis_a307864.all_one n hn1 hnp H
  unfold OMA.S_oeis_a307864.a Nat.totient
  have hm : 1 < 2 * n + 1 := by omega
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hb, h⟩
    refine ⟨hb, ?_⟩
    have h1 : b ^ n ≡ 1 [MOD 2 * n + 1] := by
      unfold Nat.ModEq; rw [h, Nat.mod_eq_of_lt hm]
    have h2 : Nat.Coprime (b ^ n) (2 * n + 1) := by
      have := h1.gcd_eq
      unfold Nat.Coprime; rw [this]; simp
    rw [Nat.coprime_comm]
    exact (Nat.coprime_pow_left_iff (by omega) _ _).1 h2
  · rintro ⟨hb, h⟩
    refine ⟨hb, ?_⟩
    have := hall b (by rw [Nat.coprime_comm]; exact h)
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hm] at this
