import FormalConjectures.Wikipedia.WolstenholmePrime

-- Reduction WolstenholmePrime.wolstenholme_bernoulli.R1 of Wolstenholme Prime — wolstenholme bernoulli
-- Credit: @mbilenko03
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_WolstenholmePrime_wolstenholme_bernoulli_R1

def H1 : Prop := ∀ p : ℕ, WolstenholmePrime.IsWolstenholmePrime p ↔
  (p > 7) ∧ Nat.Prime p ∧
    ↑(p ^ 3) ∣ (harmonic (p - 1)).num

def H2 : Prop := ∀ p : ℕ, p > 7 → Nat.Prime p →
  (↑(p ^ 3) ∣ (harmonic (p - 1)).num ↔
    ↑p ∣ (bernoulli' (p - 3)).num)

theorem main : H1 → H2 → type_of% @WolstenholmePrime.wolstenholme_bernoulli := by
  intro h1 h2 p
  constructor
  · intro hwp
    rcases (h1 p).mp hwp with ⟨hp7, hprime, hharmonic⟩
    exact ⟨hp7, hprime, (h2 p hp7 hprime).mp hharmonic⟩
  · rintro ⟨hp7, hprime, hbernoulli⟩
    exact (h1 p).mpr ⟨hp7, hprime, (h2 p hp7 hprime).mpr hbernoulli⟩

end OMA.R_WolstenholmePrime_wolstenholme_bernoulli_R1
