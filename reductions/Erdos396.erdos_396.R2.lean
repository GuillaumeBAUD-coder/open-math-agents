import FormalConjectures.ErdosProblems.«396»

/-!
The density of a single governor set is positive by Ford and Konyagin.
The correlation of consecutive governor indicators in H2 is an additional
hypothesis. H1 extends Pomerance's Theorem 4 for one shift to simultaneous
divisibility of the whole descending product for fixed window length.
-/

namespace OMA.R_Erdos396_erdos_396_R2

/-- The product condition agrees outside a set of asymptotic density zero
with every term of the block dividing its own central binomial coefficient. -/
def H1 : Prop := by
  classical
  exact ∀ k C : ℕ, ∃ N₀ : ℕ, ∀ N≥N₀,
    C * ((Finset.range N).filter (fun n => ¬(n.descFactorial (k+1) ∣ n.centralBinom ↔
      ∀ i≤k, n-i ∣ (n-i).centralBinom))).card ≤ N

/-- Consecutive runs of governor numbers of every fixed length have positive
upper density, written as rational counting inequalities. -/
def H2 : Prop := by
  classical
  exact ∀ k : ℕ, ∃ C : ℕ, ∀ L : ℕ, ∃ N≥L,
    N < C * ((Finset.range N).filter (fun n => ∀ i≤k, n-i ∣ (n-i).centralBinom)).card

theorem main : H1 → H2 → type_of% @Erdos396.erdos_396 := by
  classical
  intro h₁ h₂ k
  by_contra! fail
  obtain ⟨C,hC⟩ := h₂ k
  obtain ⟨L,hL⟩ := h₁ k C
  obtain ⟨N,hN,hnum⟩ := hC L
  let G : ℕ → Prop := fun n => ∀ i≤k, n-i ∣ (n-i).centralBinom
  let D : ℕ → Prop := fun n => ¬(n.descFactorial (k+1) ∣ n.centralBinom ↔ G n)
  have incl : (Finset.range N).filter G ⊆ (Finset.range N).filter D := by
    intro n hn
    obtain ⟨hn,hg⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn,fun eq => fail n (eq.mpr hg)⟩
  have le := Nat.mul_le_mul_left C (Finset.card_le_card incl)
  exact (Nat.not_lt_of_ge ((hL N hN).trans' le)) hnum

end OMA.R_Erdos396_erdos_396_R2
