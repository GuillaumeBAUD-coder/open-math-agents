import OMAReductions.R_Superperfect_twoFivePerfect_R1

-- Reduction Superperfect.twoFivePerfect.R1.H2.R1 of step Superperfect.twoFivePerfect.R1.H2
-- Credit: @Ciphore
-- The `p ≡ 4 (mod 5)` residue class has order `2` modulo `5`, and the exponent constraint
-- `2 ∣ e + 1` makes the geometric sum factor algebraically:
-- `σ(p^e) = (1 + p) * (1 + p^2 + ... + p^(e-1))`, with the factor `1 + p` divisible by `5`.
-- The stripped number therefore already carries a nontrivial two-factor structure, so the
-- single-prime-power core differs arithmetically from the order-one residue class.
-- As there, the equation separates by the coprime remainder `u`.

namespace OMA.R_Superperfect_twoFivePerfect_R1_H2_R1

open ArithmeticFunction ArithmeticFunction.sigma

/-- The single-prime-power core of the `p ≡ 4 (mod 5)` residue case. -/
def H1 : Prop := ∀ p e : ℕ, p.Prime → (p : ZMod 5) = 4 → 2 ∣ e + 1 →
  σ 1 (σ 1 (p ^ e) / 5) ≠ p ^ e

/-- The coprime-interaction core of the `p ≡ 4 (mod 5)` residue case. -/
def H2 : Prop := ∀ p e u : ℕ, p.Prime → p.Coprime u → 1 < u →
  (p : ZMod 5) = 4 → 2 ∣ e + 1 → σ 1 ((σ 1 (p ^ e) / 5) * σ 1 u) ≠ p ^ e * u

theorem main : H1 → H2 → OMA.R_Superperfect_twoFivePerfect_R1.H2 := by
  intro hpure hinter p e u hp hu hu0 hp1 h5
  by_cases hu1 : u = 1
  · subst hu1
    simpa using hpure p e hp hp1 h5
  · exact hinter p e u hp hu (by omega) hp1 h5

end OMA.R_Superperfect_twoFivePerfect_R1_H2_R1
