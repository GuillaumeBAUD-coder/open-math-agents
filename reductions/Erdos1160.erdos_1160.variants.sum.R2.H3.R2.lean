import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2
import Mathlib.Tactic.Linarith

-- Reduction Erdos1160.erdos_1160.variants.sum.R2.H3.R2 of step Erdos1160.erdos_1160.variants.sum.R2.H3
-- Credit: @TheLittleOne1234

/- Two steps of doubling the order gain a factor far above 2^(2m): with Higman's lower bound at
m and the sharp upper bound at m-2,
  27*log2 g(2^m) - 27*log2 g(2^(m-2)) >= 2m^3 - 13m^2 - 2(m-2)^3 + 9(m-2)^2,
which exceeds 54m once m >= 14.

H1 is, word for word, the statement of step Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H1 (Higman's
lower bound; merged proofs of this exact statement exist, for example
proofs/Erdos1160.erdos_1160.variants.sum.R2.H1.R1.H2.R1.H1.lean).
H2 is, word for word, the statement of step Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2 (the desk
lists R1.H2 as solved through it: reduction R1.H2.R1.H2.R2 with merged proofs of its four
hypotheses by @kamaleshanantha). -/

open Filter Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R2

def H1 : Prop :=
  ∀ᶠ m : ℕ in atTop, 2 ^ (2 * m^3) ≤ g (2^m)^27 * 2 ^ (13 * m^2)

def H2 : Prop :=
  ∀ᶠ m : ℕ in atTop, g (2^m)^27 * 2 ^ (9 * m^2) ≤ 2 ^ (2 * m^3)

theorem two_steps (n : ℕ) (hn : 12 ≤ n)
    (up : g (2^n)^27 * 2 ^ (9 * n^2) ≤ 2 ^ (2 * n^3))
    (low : 2 ^ (2 * (n+2)^3) ≤ g (2^(n+2))^27 * 2 ^ (13 * (n+2)^2)) :
    2 ^ (2 * (n+2)) * g (2^n) ≤ g (2^(n+2)) := by
  have hexp : 54 * (n+2) + 2 * n^3 + 13 * (n+2)^2 ≤ 2 * (n+2)^3 + 9 * n^2 := by
    nlinarith only [hn]
  have key : (2 ^ (2 * (n+2)) * g (2^n))^27 * (2 ^ (9 * n^2) * 2 ^ (13 * (n+2)^2)) ≤
      g (2^(n+2))^27 * (2 ^ (9 * n^2) * 2 ^ (13 * (n+2)^2)) := by
    calc (2 ^ (2 * (n+2)) * g (2^n))^27 * (2 ^ (9 * n^2) * 2 ^ (13 * (n+2)^2))
        = 2 ^ (54 * (n+2) + 13 * (n+2)^2) * (g (2^n)^27 * 2 ^ (9 * n^2)) := by
          rw [mul_pow, ← pow_mul, pow_add]; ring
      _ ≤ 2 ^ (54 * (n+2) + 13 * (n+2)^2) * 2 ^ (2 * n^3) := Nat.mul_le_mul_left _ up
      _ = 2 ^ (54 * (n+2) + 2 * n^3 + 13 * (n+2)^2) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (2 * (n+2)^3 + 9 * n^2) := Nat.pow_le_pow_right (by decide) hexp
      _ = 2 ^ (9 * n^2) * 2 ^ (2 * (n+2)^3) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (9 * n^2) * (g (2^(n+2))^27 * 2 ^ (13 * (n+2)^2)) := Nat.mul_le_mul_left _ low
      _ = g (2^(n+2))^27 * (2 ^ (9 * n^2) * 2 ^ (13 * (n+2)^2)) := by ring
  have hp : 0 < 2 ^ (9 * n^2) * 2 ^ (13 * (n+2)^2) := by positivity
  have h27 := Nat.le_of_mul_le_mul_right key hp
  exact (Nat.pow_le_pow_iff_left (by decide)).mp h27

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R2.H3 := by
  intro h1 h2
  obtain ⟨A, hA⟩ := eventually_atTop.mp h1
  obtain ⟨B, hB⟩ := eventually_atTop.mp h2
  refine eventually_atTop.mpr ⟨A + B + 14, fun m hm => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have e : n + 2 - 2 = n := by omega
  rw [e]
  exact two_steps n (by omega) (hB n (by omega)) (hA (n+2) (by omega))

end OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R2
