import FormalConjectures.ErdosProblems.«551»

-- Reduction Erdos551.erdos_551.variants.sufficiently_large.R1 of Erdős Problem 551 — sufficiently large
-- Credit: @ZenimXD
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- R(C_k, K_n) = (k-1)(n-1)+1 is a lower bound plus an upper bound.
-- * The lower bound is proved here in full: n-1 disjoint cliques of size k-1 (vertex u lies in block
--   u / (k-1)) contain no C_k, since a cycle is connected and would need k vertices in one block,
--   and their complement contains no K_n, since K_n would need n vertices in distinct blocks.
-- * The upper bound (every graph on (k-1)(n-1)+1 vertices contains C_k or its complement contains
--   K_n) is split along the literature, each range being a published theorem:
--     H1  k > n^2 - 2              Bondy and Erdős [BoEr73]
--     H2  4n + 2 ≤ k ≤ n^2 - 2     Nikiforov [Ni05] (who proved k ≥ 4n + 2)
--     H3  n ≤ k < 4n + 2, n large  Keevash, Long and Skokan [KLS21] (k ≥ C log n / log log n)

namespace OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R1

open SimpleGraph Filter

/-- Bondy–Erdős [BoEr73]: every graph on `(k-1)(n-1)+1` vertices contains `C_k` or its complement
contains `K_n`, whenever `k > n^2 - 2`. -/
def H1 : Prop :=
  ∀ n k : ℕ, 3 ≤ n → n ^ 2 - 2 < k →
    ∀ C : SimpleGraph (Fin ((k - 1) * (n - 1) + 1)),
      (cycleGraph k).IsContained C ∨ (completeGraph (Fin n)).IsContained Cᶜ

/-- Nikiforov [Ni05] (proved for all `k ≥ 4n + 2`), on the range `4n + 2 ≤ k ≤ n^2 - 2`. -/
def H2 : Prop :=
  ∀ n k : ℕ, 3 ≤ n → 4 * n + 2 ≤ k → k ≤ n ^ 2 - 2 →
    ∀ C : SimpleGraph (Fin ((k - 1) * (n - 1) + 1)),
      (cycleGraph k).IsContained C ∨ (completeGraph (Fin n)).IsContained Cᶜ

/-- Keevash–Long–Skokan [KLS21], on the range `n ≤ k < 4n + 2` for all large `n`. -/
def H3 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, n ≤ k → k < 4 * n + 2 →
    ∀ C : SimpleGraph (Fin ((k - 1) * (n - 1) + 1)),
      (cycleGraph k).IsContained C ∨ (completeGraph (Fin n)).IsContained Cᶜ

/-- The disjoint union of cliques `{u | u / (k-1) = b}` contains no cycle of length `k`. -/
lemma no_cycle (k N : ℕ) (hk : 3 ≤ k) :
    ¬ (cycleGraph k).IsContained
      (SimpleGraph.fromRel fun u v : Fin N => u.val / (k - 1) = v.val / (k - 1)) := by
  rintro ⟨f⟩
  have hblk : ∀ j (hj : j < k),
      (f.toHom ⟨j, hj⟩).val / (k - 1) = (f.toHom ⟨0, by omega⟩).val / (k - 1) := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      have hadj : (cycleGraph k).Adj ⟨j, by omega⟩ ⟨j + 1, hj⟩ :=
        pathGraph_le_cycleGraph (pathGraph_adj.2 (Or.inl rfl))
      have h := f.toHom.map_adj hadj
      rw [SimpleGraph.fromRel_adj] at h
      rw [← ih (by omega)]
      rcases h.2 with h' | h'
      · exact h'.symm
      · exact h'
  let φ : Fin k → Fin (k - 1) := fun i => ⟨(f.toHom i).val % (k - 1), Nat.mod_lt _ (by omega)⟩
  have hinj : Function.Injective φ := by
    intro i j hij
    have h1 : (f.toHom i).val % (k - 1) = (f.toHom j).val % (k - 1) := congrArg Fin.val hij
    have hi := hblk i.1 i.2
    have hj := hblk j.1 j.2
    simp only [Fin.eta] at hi hj
    have h2 : (f.toHom i).val / (k - 1) = (f.toHom j).val / (k - 1) := by rw [hi, hj]
    apply f.injective
    apply Fin.ext
    calc (f.toHom i).val = (k - 1) * ((f.toHom i).val / (k - 1)) + (f.toHom i).val % (k - 1) :=
          (Nat.div_add_mod _ _).symm
      _ = (k - 1) * ((f.toHom j).val / (k - 1)) + (f.toHom j).val % (k - 1) := by rw [h1, h2]
      _ = (f.toHom j).val := Nat.div_add_mod _ _
  have := Fintype.card_le_of_injective φ hinj
  simp only [Fintype.card_fin] at this
  omega

/-- The complement of `n - 1` disjoint cliques (on at most `(k-1)(n-1)` vertices) has no `K_n`. -/
lemma no_clique (n k N : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hN : N ≤ (k - 1) * (n - 1)) :
    ¬ (completeGraph (Fin n)).IsContained
      (SimpleGraph.fromRel fun u v : Fin N => u.val / (k - 1) = v.val / (k - 1))ᶜ := by
  rintro ⟨g⟩
  have hlt : ∀ i, (g.toHom i).val / (k - 1) < n - 1 := by
    intro i
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact lt_of_lt_of_le (g.toHom i).isLt (hN.trans (le_of_eq (Nat.mul_comm _ _)))
  let ψ : Fin n → Fin (n - 1) := fun i => ⟨(g.toHom i).val / (k - 1), hlt i⟩
  have hinj : Function.Injective ψ := by
    intro i j hij
    by_contra hne
    have hadj : (completeGraph (Fin n)).Adj i j := (SimpleGraph.top_adj i j).2 hne
    have h := g.toHom.map_adj hadj
    rw [SimpleGraph.compl_adj, SimpleGraph.fromRel_adj] at h
    have hval : (g.toHom i).val / (k - 1) = (g.toHom j).val / (k - 1) := congrArg Fin.val hij
    exact h.2 ⟨h.1, Or.inl hval⟩
  have := Fintype.card_le_of_injective ψ hinj
  simp only [Fintype.card_fin] at this
  omega

/-- Lower bound: below `(k-1)(n-1)+1` vertices there is a colouring with no red `C_k` and no blue `K_n`. -/
lemma lower_bound (n k N : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (hN : N ≤ (k - 1) * (n - 1)) :
    ∃ C : SimpleGraph (Fin N),
      ¬ (cycleGraph k).IsContained C ∧ ¬ (completeGraph (Fin n)).IsContained Cᶜ :=
  ⟨_, no_cycle k N hk, no_clique n k N hn (by omega) hN⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos551.erdos_551.variants.sufficiently_large := by
  intro h1 h2 h3
  filter_upwards [h3, eventually_ge_atTop 3] with n hn3 hn
  intro k hk
  have hmem : (k - 1) * (n - 1) + 1 ∈ { N : ℕ | ∀ C : SimpleGraph (Fin N),
      (cycleGraph k).IsContained C ∨ (completeGraph (Fin n)).IsContained Cᶜ } := by
    intro C
    by_cases hk1 : k < 4 * n + 2
    · exact hn3 k hk hk1 C
    · by_cases hk2 : k ≤ n ^ 2 - 2
      · exact h2 n k hn (not_lt.mp hk1) hk2 C
      · exact h1 n k hn (not_le.mp hk2) C
  unfold SimpleGraph.graphRamsey
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  intro N hN
  by_contra hlt
  push_neg at hlt
  obtain ⟨C, hC1, hC2⟩ := lower_bound n k N (by omega) (by omega) (by omega)
  rcases hN C with h | h
  · exact hC1 h
  · exact hC2 h

end OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R1
