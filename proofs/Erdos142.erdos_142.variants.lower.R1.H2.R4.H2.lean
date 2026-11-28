import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R4
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Shifted blocks 4*4^j + B j lie in (4^(j+1), 5*4^j] and are far apart, so three equally spaced
-- terms of the union always lie in one block; by induction a whole k-AP (k >= 3) lies in one
-- block j, and shifting it down by 4*4^j gives a k-AP inside B j, which is excluded.

namespace OMA.SolPack

lemma pack_pow_lt {i j : ℕ} (h : i < j) : 4 * 4 ^ i ≤ 4 ^ j := by
  calc 4 * 4 ^ i = 4 ^ (i + 1) := by ring
    _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) h

lemma pack_uniq {j j' b b' : ℕ} (h : 1 ≤ b ∧ b ≤ 4 ^ j) (h' : 1 ≤ b' ∧ b' ≤ 4 ^ j')
    (he : 4 * 4 ^ j + b = 4 * 4 ^ j' + b') : j = j' := by
  rcases lt_trichotomy j j' with hl | hl | hl
  · have := pack_pow_lt hl; omega
  · exact hl
  · have := pack_pow_lt hl; omega

lemma pack_triple {x y z j0 j1 j2 b0 b1 b2 : ℕ} (h0 : 1 ≤ b0 ∧ b0 ≤ 4 ^ j0)
    (h1 : 1 ≤ b1 ∧ b1 ≤ 4 ^ j1) (h2 : 1 ≤ b2 ∧ b2 ≤ 4 ^ j2)
    (hx : x = 4 * 4 ^ j0 + b0) (hy : y = 4 * 4 ^ j1 + b1) (hz : z = 4 * 4 ^ j2 + b2)
    (hs : x + z = 2 * y) (hxy : x < y) : j0 = j1 ∧ j1 = j2 := by
  rcases lt_trichotomy j0 j1 with ha | ha | ha <;>
  rcases lt_trichotomy j1 j2 with hb | hb | hb
  · have := pack_pow_lt ha; have := pack_pow_lt hb; omega
  · subst hb; have := pack_pow_lt ha; omega
  · have := pack_pow_lt ha; have := pack_pow_lt hb; omega
  · subst ha; have := pack_pow_lt hb; omega
  · exact ⟨ha, hb⟩
  · subst ha; have := pack_pow_lt hb; omega
  · have := pack_pow_lt ha; have := pack_pow_lt hb; omega
  · subst hb; have := pack_pow_lt ha; omega
  · have := pack_pow_lt ha; have := pack_pow_lt hb; omega

theorem pack_H2 : ∀ (k : ℕ), 3 ≤ k → ∀ (B : ℕ → Finset ℕ), (∀ j, B j ⊆ Finset.Icc 1 (4 ^ j)) →
    (∀ j, ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ B j) →
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, ∃ j b, b ∈ B j ∧ a + i * d = 4 * 4 ^ j + b := by
  intro k hk B hB hfree ⟨a, d, hd, h⟩
  have mem : ∀ j b, b ∈ B j → 1 ≤ b ∧ b ≤ 4 ^ j := fun j b hb => by
    have := hB j hb
    simpa [Finset.mem_Icc] using this
  obtain ⟨j0, b0, hb0, he0⟩ := h 0 (by omega)
  have key : ∀ i, i < k → ∀ j b, b ∈ B j → a + i * d = 4 * 4 ^ j + b → j = j0 := by
    intro i
    induction i with
    | zero =>
      intro _ j b hb he
      exact pack_uniq (mem j b hb) (mem j0 b0 hb0) (he.symm.trans he0)
    | succ i ih =>
      intro hi j b hb he
      obtain ⟨j1, b1, hb1, he1⟩ := h i (by omega)
      have hj1 := ih (by omega) j1 b1 hb1 he1
      by_cases h2 : i + 2 < k
      · obtain ⟨j2, b2, hb2, he2⟩ := h (i + 2) h2
        have hs : (a + i * d) + (a + (i + 2) * d) = 2 * (a + (i + 1) * d) := by ring
        have hxy : a + i * d < a + (i + 1) * d := by
          have : (i + 1) * d = i * d + d := by ring
          omega
        have := pack_triple (mem j1 b1 hb1) (mem j b hb) (mem j2 b2 hb2) he1 he he2 hs hxy
        omega
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        obtain ⟨jm, bm, hbm, hem⟩ := h m (by omega)
        have hs : (a + m * d) + (a + (m + 1 + 1) * d) = 2 * (a + (m + 1) * d) := by ring
        have hxy : a + m * d < a + (m + 1) * d := by
          have : (m + 1) * d = m * d + d := by ring
          omega
        have := pack_triple (mem jm bm hbm) (mem j1 b1 hb1) (mem j b hb) hem he1 he hs hxy
        omega
  apply hfree j0 ⟨a - 4 * 4 ^ j0, d, hd, fun i hi => ?_⟩
  obtain ⟨j, b, hb, he⟩ := h i hi
  have hj := key i hi j b hb he
  rw [hj] at hb he
  have : a - 4 * 4 ^ j0 + i * d = b := by
    simp at he0
    omega
  rw [this]
  exact hb

end OMA.SolPack

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R4.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R4.H2
  exact OMA.SolPack.pack_H2
