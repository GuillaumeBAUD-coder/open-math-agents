import FormalConjectures.ErdosProblems.«564»

-- Credit: @ihateSAS
namespace OMA.R_Erdos564_erdos_564_R1

open Filter Combinatorics

/-- A three-colour tower lower bound, phrased at every forcing vertex count. -/
def H1 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ᶠ k : ℕ in atTop, ∀ m : ℕ,
    (∀ f : Finset (Fin m) → Fin 3, ∃ S : Finset (Fin m), S.card = k ∧
      ∃ b : Fin 3, ∀ e : Finset (Fin m), e ⊆ S → e.card = 3 → f e = b) →
    (2 : ℝ) ^ (2 : ℝ) ^ (a * k) ≤ m

/-- At the two-colour threshold, adding a third colour still forces a
monochromatic clique of size at least a fixed fraction of the old target. -/
def H2 : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, d * n ≤ k ∧
    ∀ f : Finset (Fin (hypergraphRamsey 3 n)) → Fin 3,
      ∃ S : Finset (Fin (hypergraphRamsey 3 n)), S.card = k ∧
        ∃ b : Fin 3, ∀ e : Finset (Fin (hypergraphRamsey 3 n)),
          e ⊆ S → e.card = 3 → f e = b

theorem main : H1 → H2 → type_of% @Erdos564.erdos_564 := by
  rintro ⟨a, ha, hthree⟩ ⟨d, hd, hcompare⟩
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 hthree
  obtain ⟨N, hN⟩ := exists_nat_gt ((k₀ : ℝ) / d)
  refine ⟨a * d, mul_pos ha hd, ?_⟩
  filter_upwards [hcompare, eventually_ge_atTop N] with n hn hNn
  obtain ⟨k, hsize, hforce⟩ := hn
  have hlarge : (k₀ : ℝ) ≤ (k : ℝ) := calc
    (k₀ : ℝ) ≤ (N : ℝ) * d := ((div_lt_iff₀ hd).mp hN).le
    _ ≤ (n : ℝ) * d := mul_le_mul_of_nonneg_right (by exact_mod_cast hNn) hd.le
    _ = d * n := mul_comm _ _
    _ ≤ k := hsize
  have hexp : (a * d) * n ≤ a * k := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsize ha.le
  exact le_trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp))
    (hk₀ k (by exact_mod_cast hlarge) (hypergraphRamsey 3 n) hforce)

end OMA.R_Erdos564_erdos_564_R1
