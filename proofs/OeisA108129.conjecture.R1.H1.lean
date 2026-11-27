import OMAReductions.R_OeisA108129_conjecture_R1

-- The six residues cover every exponent modulo 24.
set_option maxRecDepth 8192 in
lemma OMA.riesel_cover (r : Fin 24) :
    ((509203 : ZMod 3) * (2 : ZMod 3) ^ r.val = 1) ∨
    ((509203 : ZMod 5) * (2 : ZMod 5) ^ r.val = 1) ∨
    ((509203 : ZMod 7) * (2 : ZMod 7) ^ r.val = 1) ∨
    ((509203 : ZMod 13) * (2 : ZMod 13) ^ r.val = 1) ∨
    ((509203 : ZMod 17) * (2 : ZMod 17) ^ r.val = 1) ∨
    ((509203 : ZMod 241) * (2 : ZMod 241) ^ r.val = 1) := by
  revert r
  decide +kernel

lemma OMA.riesel_divisor (m p : ℕ) (hperiod : (2 : ZMod p) ^ 24 = 1)
    (hres : (509203 : ZMod p) * (2 : ZMod p) ^ (m % 24) = 1) :
    p ∣ 509203 * 2 ^ m - 1 := by
  have hpow : 0 < 2 ^ m := by positivity
  have hge : 1 ≤ 509203 * 2 ^ m := by omega
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  rw [Nat.cast_sub hge]
  push_cast
  rw [pow_eq_pow_mod m hperiod, hres, sub_self]

lemma OMA.riesel_composite (m p : ℕ) (hp : 2 ≤ p) (hpmax : p ≤ 241)
    (hperiod : (2 : ZMod p) ^ 24 = 1)
    (hres : (509203 : ZMod p) * (2 : ZMod p) ^ (m % 24) = 1) :
    ¬ (509203 * 2 ^ m - 1).Prime := by
  have hpow : 0 < 2 ^ m := by positivity
  apply Nat.not_prime_of_dvd_of_lt (OMA.riesel_divisor m p hperiod hres) hp
  omega

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  have hcomp : ∀ m : ℕ, ¬ (509203 * 2 ^ m - 1).Prime := by
    intro m
    rcases OMA.riesel_cover ⟨m % 24, Nat.mod_lt _ (by decide)⟩ with
      h3 | h5 | h7 | h13 | h17 | h241
    · exact OMA.riesel_composite m 3 (by decide) (by decide) (by decide) h3
    · exact OMA.riesel_composite m 5 (by decide) (by decide) (by decide) h5
    · exact OMA.riesel_composite m 7 (by decide) (by decide) (by decide) h7
    · exact OMA.riesel_composite m 13 (by decide) (by decide) (by decide) h13
    · exact OMA.riesel_composite m 17 (by decide) (by decide) (by decide) h17
    · exact OMA.riesel_composite m 241 (by decide) (by decide) (by decide) h241
  change OeisA108129.a 254602 = -1
  simp [OeisA108129.a, hcomp]
