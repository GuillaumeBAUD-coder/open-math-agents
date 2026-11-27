import OMAReductions.R_Erdos978_erdos_978_variants_sub_two_R1_H2_R1

/-! The primes between the square root of the block parameter and the parameter
itself have prime powers larger than every input in the block. Their residue
classes can therefore be counted directly. The remaining primes are the range
of the high-degree determinant estimate. -/

namespace OMA.R_Erdos978_erdos_978_variants_sub_two_R1_H2_R1_H2_R1

open scoped Classical

/-- The total number of roots in the intermediate range has zero relative density. -/
def H1 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∀ A : ℕ, 0 < A → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A * (∑ p ∈ (Finset.Ioc N.sqrt N).filter Nat.Prime,
        ((Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card) < N

/-- The determinant-method range starts with primes larger than the block parameter. -/
def H2 : Prop :=
  ∀ (f : Polynomial ℤ), Irreducible f → 9 ≤ f.natDegree →
    let k := f.natDegree - 2
    ∀ A : ℕ, 0 < A → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A * ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
        ∃ p : ℕ, p.Prime ∧ N < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card < N

section RootCounts

lemma block_lt_prime_power {N p k : ℕ} (hp : p.Prime) (hs : N.sqrt < p) (hk : 3 ≤ k) :
    2 * N < p ^ k := by
  have hsq : N < p ^ 2 := by
    rw [pow_two]
    exact lt_of_not_ge fun h => hs.not_ge (Nat.le_sqrt.mpr h)
  calc
    2 * N < 2 * p ^ 2 := Nat.mul_lt_mul_of_pos_left hsq (by decide)
    _ ≤ p * p ^ 2 := Nat.mul_le_mul_right _ hp.two_le
    _ = p ^ 3 := by ring
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk

lemma intermediate_hits_le_total_roots (f : Polynomial ℤ) (N k : ℕ) (hk : 3 ≤ k) :
    let S := (Finset.Ioc N.sqrt N).filter Nat.Prime
    ((Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
      ∃ p ∈ S, (p : ℤ) ^ k ∣ f.eval (n : ℤ)).card ≤
      ∑ p ∈ S, ((Finset.range (p ^ k)).filter fun (r : ℕ) =>
        (p : ℤ) ^ k ∣ f.eval (r : ℤ)).card := by
  classical
  intro S
  let roots (p : ℕ) := (Finset.range (p ^ k)).filter fun (r : ℕ) => (p : ℤ) ^ k ∣ f.eval (r : ℤ)
  apply (Finset.card_le_card ?_).trans (Finset.card_biUnion_le (s := S) (t := roots))
  intro n hn
  obtain ⟨hnI, p, hpS, hval⟩ := Finset.mem_filter.mp hn
  obtain ⟨hpI, hp⟩ := Finset.mem_filter.mp hpS
  have hbig := block_lt_prime_power hp (Finset.mem_Ioc.mp hpI).1 hk
  exact Finset.mem_biUnion.mpr ⟨p, hpS, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr ((Finset.mem_Ico.mp hnI).2.trans hbig), hval⟩⟩

end RootCounts

theorem main : H1 → H2 → OMA.R_Erdos978_erdos_978_variants_sub_two_R1_H2_R1.H2 := by
  classical
  intro hlocal htail f hi hd
  dsimp only
  intro A hA
  let k := f.natDegree - 2
  obtain ⟨N₁, h₁⟩ := hlocal f hi hd (2 * A) (by omega)
  obtain ⟨N₂, h₂⟩ := htail f hi hd (2 * A) (by omega)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  let S := (Finset.Ioc N.sqrt N).filter Nat.Prime
  let middle := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p ∈ S, (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  let far := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p : ℕ, p.Prime ∧ N < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  let hits := (Finset.Ico N (2 * N)).filter fun (n : ℕ) =>
    ∃ p : ℕ, p.Prime ∧ N.sqrt < p ∧ (p : ℤ) ^ k ∣ f.eval (n : ℤ)
  have hm : 2 * A * middle.card < N :=
    (Nat.mul_le_mul_left _ (intermediate_hits_le_total_roots f N k (by dsimp [k]; omega))).trans_lt
      (h₁ N ((le_max_left N₁ N₂).trans hN))
  have hf : 2 * A * far.card < N := h₂ N ((le_max_right N₁ N₂).trans hN)
  have cover : hits ⊆ middle ∪ far := by
    intro n hn
    obtain ⟨hnI, p, hp, hroot, hval⟩ := Finset.mem_filter.mp hn
    by_cases hcut : p ≤ N
    · have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hroot, hcut⟩, hp⟩
      exact Finset.mem_union.mpr (.inl <| Finset.mem_filter.mpr ⟨hnI, p, hpS, hval⟩)
    · exact Finset.mem_union.mpr (.inr <| Finset.mem_filter.mpr
        ⟨hnI, p, hp, Nat.lt_of_not_ge hcut, hval⟩)
  have hcount := Nat.mul_le_mul_left A
    ((Finset.card_le_card cover).trans (Finset.card_union_le middle far))
  change A * hits.card < N
  nlinarith only [hm, hf, hcount]

end OMA.R_Erdos978_erdos_978_variants_sub_two_R1_H2_R1_H2_R1
