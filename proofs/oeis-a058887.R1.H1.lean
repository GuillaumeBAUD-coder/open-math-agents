import OMAReductions.R_oeis_a058887_R1

-- Step oeis-a058887.R1.H1: hypothesis H1 of reduction oeis-a058887.R1
-- Credit: @keiichisince1986-bot

namespace OMA.OeisA058887R1H1

private lemma composite_sierpinski {p q r : ℕ} (hp : p.Prime) (hp_le : p ≤ 241)
    (h24 : 2 ^ 24 % p = 1) (hr : (271129 * 2 ^ r + 1) % p = 0)
    (hn : 1 ≤ 24 * q + r) : ¬ (271129 * 2 ^ (24 * q + r) + 1).Prime := by
  have hmod1 : 2 ^ 24 ≡ 1 [MOD p] := by
    change 2 ^ 24 % p = 1 % p
    rw [h24, Nat.mod_eq_of_lt hp.one_lt]
  have hpow : 2 ^ (24 * q + r) ≡ 2 ^ r [MOD p] := by
    rw [pow_add, pow_mul]
    simpa using (hmod1.pow q).mul_right (2 ^ r)
  have hcong : 271129 * 2 ^ (24 * q + r) + 1 ≡ 271129 * 2 ^ r + 1 [MOD p] :=
    (hpow.mul_left 271129).add_right 1
  have hdvd : p ∣ 271129 * 2 ^ (24 * q + r) + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    change (271129 * 2 ^ (24 * q + r) + 1) % p = (271129 * 2 ^ r + 1) % p at hcong
    rw [hcong, hr]
  have hpos : 1 ≤ 2 ^ (24 * q + r) := Nat.one_le_pow _ 2 (by decide)
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p hdvd with rfl | hself
  · exact hp.ne_one rfl
  · omega

end OMA.OeisA058887R1H1

theorem OMA.solution : OMA.R_oeis_a058887_R1.H1 := by
  refine ⟨by norm_num, ⟨135564, by norm_num⟩, ?_⟩
  intro n hn
  let q := n / 24
  let r := n % 24
  have hneq : n = 24 * q + r := (Nat.div_add_mod n 24).symm
  have hrlt : r < 24 := Nat.mod_lt n (by decide)
  rw [hneq] at hn ⊢
  interval_cases r
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 241) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
  · exact OMA.OeisA058887R1H1.composite_sierpinski (p := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
