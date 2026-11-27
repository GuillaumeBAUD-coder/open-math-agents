import OMAStatements.S_oeis_a214074

/-!
Clark Kimberling conjectured that the least admissible shift is 3 precisely
for exponents of the form 330k − 209. Take k = 10421. For the resulting
exponent, both powers are 3 modulo 487891, so 3 is not an admissible shift.
-/

namespace A214074Counterexample

private theorem commonFactor (b : ℤ)
    (h : (b : ZMod 487891) ^ 3438721 = 3) :
    (487891 : ℤ) ∣ b ^ 3438721 - 3 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 487891).mp
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat, sub_eq_zero] using h

theorem gcd_ne_one :
    Int.gcd ((2 : ℤ) ^ 3438721 - 3) ((3 : ℤ) ^ 3438721 - 3) ≠ 1 := by
  have h₂ : (2 : ZMod 487891) ^ 3438721 = 3 := by reduce_mod_char
  have h₃ : (3 : ZMod 487891) ^ 3438721 = 3 := by reduce_mod_char
  have h := Int.dvd_gcd (c := 487891) (commonFactor 2 h₂) (commonFactor 3 h₃)
  intro hOne
  rw [hOne] at h
  exact (by decide : ¬ 487891 ∣ 1) h

end A214074Counterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a214074.main) := by
  intro claim
  have least := (claim 3438721 (by decide)).mpr ⟨10421, by decide, by decide⟩
  exact A214074Counterexample.gcd_ne_one least.1.2
