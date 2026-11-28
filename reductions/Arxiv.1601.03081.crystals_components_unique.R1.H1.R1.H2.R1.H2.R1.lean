import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1

-- Reduction Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H2.R1.H2.R1 of step Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H2.R1.H2
-- Credit: @avivorly

/-!
# Odd crystal multipliers from 21 to 31, quotient at least five

The step keeps its statement and is split by the odd multiplier m: the
finite ranges 21 <= m <= 25, 27 <= m <= 29, m = 31, and m at least 33.
Each finite hypothesis is proved, at fixed m, by the same eliminant residue
tables that the parent reduction uses below 21 (Lean checks every residue).
The last hypothesis is the open remainder.
-/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H2_R1

def H1 : Prop :=
  ∀ a c m p q : ℕ, 21 ≤ m → m ≤ 25 → Odd m → a.Coprime c → a ≤ c → c ≤ m*a →
    3 ≤ a → 5 ≤ c →
    (a+m*c)^2 = p*((a+1)*(m*c+1)) →
    (c+m*a)^2 = q*((c+1)*(m*a+1)) → 5 ≤ q → p = q

def H2 : Prop :=
  ∀ a c m p q : ℕ, 27 ≤ m → m ≤ 29 → Odd m → a.Coprime c → a ≤ c → c ≤ m*a →
    3 ≤ a → 5 ≤ c →
    (a+m*c)^2 = p*((a+1)*(m*c+1)) →
    (c+m*a)^2 = q*((c+1)*(m*a+1)) → 5 ≤ q → p = q

def H3 : Prop :=
  ∀ a c p q : ℕ, a.Coprime c → a ≤ c → c ≤ 31*a →
    3 ≤ a → 5 ≤ c →
    (a+31*c)^2 = p*((a+1)*(31*c+1)) →
    (c+31*a)^2 = q*((c+1)*(31*a+1)) → 5 ≤ q → p = q

def H4 : Prop :=
  ∀ a c m p q : ℕ, 33 ≤ m → Odd m → a.Coprime c → a ≤ c → c ≤ m*a →
    3 ≤ a → 5 ≤ c →
    (a+m*c)^2 = p*((a+1)*(m*c+1)) →
    (c+m*a)^2 = q*((c+1)*(m*a+1)) → 5 ≤ q → p = q

theorem main : H1 → H2 → H3 → H4 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1.H2 := by
  intro h1 h2 h3 h4 a c m p q hm ho hcop hac hca ha hc hf hg hq
  by_cases s25 : m ≤ 25
  · exact h1 a c m p q hm s25 ho hcop hac hca ha hc hf hg hq
  by_cases s29 : m ≤ 29
  · have hm27 : 27 ≤ m := by obtain ⟨k,hk⟩ := ho; omega
    exact h2 a c m p q hm27 s29 ho hcop hac hca ha hc hf hg hq
  by_cases s31 : m ≤ 31
  · have he : m = 31 := by obtain ⟨k,hk⟩ := ho; omega
    rw [he] at hca hf hg
    exact h3 a c p q hcop hac hca ha hc hf hg hq
  have hm33 : 33 ≤ m := by obtain ⟨k,hk⟩ := ho; omega
  exact h4 a c m p q hm33 ho hcop hac hca ha hc hf hg hq

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H2_R1
