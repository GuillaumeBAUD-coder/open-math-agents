import FormalConjectures.ErdosProblems.«61»

/-!
# Reduction `Erdos61.erdos_61.R1` — Erdős–Hajnal: small-`H` base case vs. open core

Target (`Erdos61.erdos_61`): for **every** finite simple graph `H` there is `c = c(H) > 0`
such that every graph `G` on `n` vertices with no induced copy of `H` has a clique or an
independent set of size at least `n ^ c`.  This is the Erdős–Hajnal conjecture
([ErHa89], erdosproblems.com/61), still open in this generality (as of 2026-11-28).

The target is split on the order of `H`, the only split that separates a *proved* part from
the *open* part.  Vertices of finite graphs are relabelled to `Fin k` (`k = |V(H)|`), so the
two hypotheses are statements about labelled graphs; the relabelling invariance used to
transport them to an arbitrary vertex type `α` is proved below (induced copies are
relabelling invariant, `exists_induced_copy_congr`).

* `H1` — the **base case** `|V(H)| ≤ 4`.  Erdős–Hajnal is known to hold for every graph on
  at most four vertices (folklore; it is the standard remark in the literature, cf. the
  introduction of [NSS23], arXiv:2312.15333).  Formalising it is a finite, self-contained
  case analysis over the eleven four-vertex graphs, e.g. `H = K₄` by Ramsey's theorem,
  `H = P₄` (cographs are perfect, so `ω(G)·α(G) ≥ |G|`), and `H = C₄`, `2K₂`, diamond by the
  classical arguments for those induced obstructions.  So `H1` is a *doable* standalone
  formalisation goal, not an instance of the conjecture's difficulty.
* `H2` — the **open core** `5 ≤ |V(H)|`.  This is where all remaining difficulty lives: it
  contains `H = P₅` (proved by [NSS23], arXiv:2312.15333) and `H = C₅` (proved by [CSSS23])
  as special cases, together with the unconditional log-factor bounds of [ErHa89]
  (`exp(c√log n)`) and [BNSS23] (`exp(c√(log n · log log n))`), but no proof is known for
  general `H` of five or more vertices.

`main` is the case split `|V(H)| ≤ 4` versus `5 ≤ |V(H)|`, plus the relabelling transport; it
is deliberately elementary — all mathematical content of this reduction is in the *statements*
of `H1` and `H2`, and `H2` is exactly the target minus a proved base case.

Credit: the solver of `Erdos61.erdos_61.R1` is credited in the pull request.
-/

namespace OMA.R_Erdos61_erdos_61_R1

open Filter

/-- Induced copies are relabelling invariant.  For a graph `H` on `α` and a labelling
`e : α ≃ Fin k` of its vertices, a graph `G` on `n` vertices contains an induced copy of `H`
iff it contains one of the labelled copy `H.comap e.symm`. -/
private lemma exists_induced_copy_congr {α : Type*} {k n : ℕ} (e : α ≃ Fin k)
    (H : SimpleGraph α) (G : SimpleGraph (Fin n)) :
    (∃ g : α ↪ Fin n, H = G.comap g) ↔
      ∃ g : Fin k ↪ Fin n, H.comap (fun i : Fin k => e.symm i) = G.comap g := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨e.symm.toEmbedding.trans g, ?_⟩
    rw [hg]
    rfl
  · rintro ⟨g, hg⟩
    refine ⟨e.toEmbedding.trans g, ?_⟩
    ext a b
    have h : (H.comap (fun i : Fin k => e.symm i)).Adj (e a) (e b) ↔
        (G.comap g).Adj (e a) (e b) := by rw [hg]
    rw [SimpleGraph.comap_adj] at h ⊢
    simpa [Equiv.symm_apply_apply] using h

/-- The Erdős–Hajnal bound is invariant under relabelling the vertices of `H`. -/
private lemma lowerBound_congr {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (e : α ≃ Fin k) (H : SimpleGraph α) (f : ℕ → ℝ) :
    Erdos61.IsErdosHajnalLowerBound (H.comap (fun i : Fin k => e.symm i)) f ↔
      Erdos61.IsErdosHajnalLowerBound H f := by
  unfold Erdos61.IsErdosHajnalLowerBound
  apply Filter.eventually_congr
  filter_upwards with n
  constructor
  · intro h G hG
    exact h G fun h2 => hG ((exists_induced_copy_congr e H G).mpr h2)
  · intro h G hG
    exact h G fun h1 => hG ((exists_induced_copy_congr e H G).mp h1)

/-- Transport the labelled statements to an arbitrary finite vertex type. -/
private lemma lowerBound_of_order
    (h1 : ∀ k : ℕ, k ≤ 4 → ∀ H : SimpleGraph (Fin k),
      ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c))
    (h2 : ∀ k : ℕ, 5 ≤ k → ∀ H : SimpleGraph (Fin k),
      ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c))
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α) :
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c) := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have hlab : ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound
      (H.comap (fun i : Fin (Fintype.card α) => e.symm i)) (fun n : ℕ => (n : ℝ) ^ c) := by
    by_cases hk : Fintype.card α ≤ 4
    · exact h1 _ hk _
    · exact h2 _ (Nat.succ_le_of_lt (Nat.not_le.mp hk)) _
  obtain ⟨c, hc, hb⟩ := hlab
  exact ⟨c, hc, (lowerBound_congr e H _).mp hb⟩

/-- Base case, `|V(H)| ≤ 4`: Erdős–Hajnal is a theorem for every graph on at most four
vertices (folklore), and this is what a formalisation of the base case has to supply. -/
def H1 : Prop :=
  ∀ k : ℕ, k ≤ 4 → ∀ H : SimpleGraph (Fin k),
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

/-- Open core, `5 ≤ |V(H)|`: the Erdős–Hajnal conjecture for all graphs of order at least
five.  No proof is known for general `H` here; the cases `P₅` and `C₅` are the two
five-vertex graphs whose conjecture has been settled ([NSS23], [CSSS23]). -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∀ H : SimpleGraph (Fin k),
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

theorem main : H1 → H2 → type_of% @Erdos61.erdos_61 :=
  fun h1 h2 => lowerBound_of_order h1 h2

end OMA.R_Erdos61_erdos_61_R1
