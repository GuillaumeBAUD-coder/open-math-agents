import OMAReductions.R_oeis_a050412_R1

-- Step oeis-a050412.R1.H1: hypothesis H1 of reduction oeis-a050412.R1
-- Credit: @keiichisince1986-bot

namespace OMA.OeisA050412R1H1

private lemma composite_riesel {p q r : ℕ} (hp : p.Prime) (hp_le : p ≤ 241)
    (h24 : 2 ^ 24 % p = 1) (hr : 509203 * 2 ^ r % p = 1)
    (hk : 1 ≤ 24 * q + r) : ¬ (509203 * 2 ^ (24 * q + r) - 1).Prime := by
  have hmod1 : 2 ^ 24 ≡ 1 [MOD p] := by
    change 2 ^ 24 % p = 1 % p
    rw [h24, Nat.mod_eq_of_lt hp.one_lt]
  have hpow : 2 ^ (24 * q + r) ≡ 2 ^ r [MOD p] := by
    rw [pow_add, pow_mul]
    simpa using (hmod1.pow q).mul_right (2 ^ r)
  have hcong : 509203 * 2 ^ (24 * q + r) ≡ 509203 * 2 ^ r [MOD p] :=
    hpow.mul_left 509203
  have hrem : 509203 * 2 ^ (24 * q + r) % p = 1 := by
    change 509203 * 2 ^ (24 * q + r) % p = 509203 * 2 ^ r % p at hcong
    rw [hcong, hr]
  have hdvd : p ∣ 509203 * 2 ^ (24 * q + r) - 1 := by
    refine ⟨509203 * 2 ^ (24 * q + r) / p, ?_⟩
    have hdm := Nat.div_add_mod (509203 * 2 ^ (24 * q + r)) p
    omega
  have hpos : 1 ≤ 2 ^ (24 * q + r) := Nat.one_le_pow _ 2 (by decide)
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p hdvd with rfl | hself
  · exact hp.ne_one rfl
  · omega

end OMA.OeisA050412R1H1

theorem OMA.solution : OMA.R_oeis_a050412_R1.H1 := by
  refine ⟨⟨254601, by norm_num⟩, ?_⟩
  intro k hk
  let q := k / 24
  let r := k % 24
  have hkeq : k = 24 * q + r := (Nat.div_add_mod k 24).symm
  have hrlt : r < 24 := Nat.mod_lt k (by decide)
  rw [hkeq] at hk ⊢
  interval_cases r
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 241) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
  · exact OMA.OeisA050412R1H1.composite_riesel (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk
