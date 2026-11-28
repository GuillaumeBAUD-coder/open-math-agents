import OMAStatements.S_oeis_a096069

theorem OMA.solution : type_of% @OMA.S_oeis_a096069.main := by
  intro p hp hp2 hp5
  have h10 : p.Coprime 10 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    change p ∣ 2 * 5 at hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hd)
  let m := 10 ^ (Nat.digits 10 p).length
  have hm : m ≠ 0 := pow_ne_zero _ (by decide)
  have hpm : p.Coprime m := h10.pow_right _
  obtain ⟨a, ham, hap⟩ := Nat.chineseRemainder hpm.symm p 1
  have ha : a.Coprime (m * p) := by
    apply Nat.coprime_mul_iff_right.mpr
    constructor
    · simpa only [Nat.coprime_iff_gcd_eq_one, ham.gcd_eq] using hpm
    · simp [Nat.coprime_iff_gcd_eq_one, hap.gcd_eq]
  obtain ⟨q, -, hq, hqa⟩ :=
    Nat.forall_exists_prime_gt_and_modEq p (mul_ne_zero hm hp.ne_zero) ha
  exact ⟨q, hq, (hqa.of_dvd (dvd_mul_right m p)).trans ham,
    (hqa.of_dvd (dvd_mul_left p m)).trans hap⟩
