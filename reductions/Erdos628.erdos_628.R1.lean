import FormalConjectures.ErdosProblems.«628»

-- Reduction Erdos628.erdos_628.R1 of Erdős Problem 628
-- Credit: @divo12
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos628_erdos_628_R1

/-- The case `a = 2` (so `b = k - 1`) for vertex-critical graphs: every `K_k`-free graph with
chromatic number `k ≥ 3` in which deleting any vertex lowers the chromatic number has a vertex set
`s` containing an edge whose complement still needs `k - 1` colours. This is the form of the
`(2, k - 1)` case related to the Erdős–Lovász double-critical graph conjecture. -/
def H1 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    3 ≤ k →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (2 : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ ((k - 1 : ℕ) : ℕ∞)

/-- The cases `3 ≤ a ≤ b` for vertex-critical graphs: every `K_k`-free graph with chromatic
number `k` in which deleting any vertex lowers the chromatic number splits into two parts needing
at least `a` and at least `b` colours, whenever `3 ≤ a ≤ b` and `a + b = k + 1`. -/
def H2 : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.chromaticNumber = (k : ℕ∞) → G.CliqueFree k →
    (∀ v : Fin n, (G.induce ({v}ᶜ : Set (Fin n))).chromaticNumber < (k : ℕ∞)) →
    ∀ a b : ℕ, 3 ≤ a → a ≤ b → a + b = k + 1 →
    ∃ s : Set (Fin n), (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

lemma chrom_induce_le {V : Type*} (G : SimpleGraph V) (s : Set V) :
    (G.induce s).chromaticNumber ≤ G.chromaticNumber :=
  SimpleGraph.chromaticNumber_mono_of_hom ⟨fun x => x.1, fun h => by simpa using h⟩

lemma chrom_induce_univ {V : Type*} (G : SimpleGraph V) :
    (G.induce (Set.univ : Set V)).chromaticNumber = G.chromaticNumber :=
  le_antisymm (chrom_induce_le G _)
    (SimpleGraph.chromaticNumber_mono_of_hom ⟨fun x => ⟨x, Set.mem_univ x⟩, fun h => by simpa using h⟩)

lemma exists_critical {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (hG : G.chromaticNumber = (k : ℕ∞)) :
    ∃ T : Finset V, (G.induce (T : Set V)).chromaticNumber = (k : ℕ∞) ∧
      ∀ v ∈ T, (G.induce ((T.erase v : Finset V) : Set V)).chromaticNumber < (k : ℕ∞) := by
  have hP : ∃ n, ∃ T : Finset V, T.card = n ∧ (k : ℕ∞) ≤ (G.induce (T : Set V)).chromaticNumber :=
    ⟨_, Finset.univ, rfl, by rw [Finset.coe_univ, chrom_induce_univ, hG]⟩
  obtain ⟨T, hTc, hTk⟩ := Nat.find_spec hP
  refine ⟨T, le_antisymm (hG ▸ chrom_induce_le G _) hTk, fun v hv => ?_⟩
  by_contra hlt
  push Not at hlt
  have hcard : (T.erase v).card < Nat.find hP := by
    rw [Finset.card_erase_of_mem hv, hTc]
    have : 0 < Nat.find hP := by rw [← hTc]; exact Finset.card_pos.mpr ⟨v, hv⟩
    omega
  exact Nat.find_min hP hcard ⟨T.erase v, rfl, hlt⟩

lemma transfer {V W : Type*} (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f)
    (s' : Set W) :
    ((G.comap f).induce s').chromaticNumber ≤ (G.induce (f '' s')).chromaticNumber ∧
    ((G.comap f).induce s'ᶜ).chromaticNumber ≤ (G.induce (f '' s')ᶜ).chromaticNumber := by
  constructor
  · exact SimpleGraph.chromaticNumber_mono_of_hom
      ⟨fun x => ⟨f x.1, Set.mem_image_of_mem f x.2⟩, fun h => by simpa using h⟩
  · exact SimpleGraph.chromaticNumber_mono_of_hom
      ⟨fun x => ⟨f x.1, fun ⟨y, hy, hfy⟩ => x.2 (hf hfy ▸ hy)⟩, fun h => by simpa using h⟩

lemma key (h1 : H1) (h2 : H2) {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k)
    (a b : ℕ) (ha : 2 ≤ a) (hab' : a ≤ b) (hab : a + b = k + 1) :
    ∃ (s : Set V), (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞) := by
  classical
  obtain ⟨T, hTk, hTcrit⟩ := exists_critical G k hG_chrom
  set e : (T : Set V) ≃ Fin T.card := T.equivFin with he
  set f : Fin T.card → V := fun i => ((e.symm i : (T : Set V)) : V) with hf
  have hfi : Function.Injective f := fun i j h => e.symm.injective (Subtype.ext h)
  have hG'k : (G.comap f).chromaticNumber = (k : ℕ∞) := by
    rw [← hTk]
    refine le_antisymm (SimpleGraph.chromaticNumber_mono_of_hom
      ⟨fun i => e.symm i, fun h => h⟩) (SimpleGraph.chromaticNumber_mono_of_hom
      ⟨fun x => e x, fun {x y} h => by simpa [f] using h⟩)
  have hG'cl : (G.comap f).CliqueFree k :=
    SimpleGraph.CliqueFree.comap ⟨SimpleGraph.Hom.toCopy ⟨f, fun h => h⟩ hfi⟩ hG_clique
  have hG'crit : ∀ v : Fin T.card,
      ((G.comap f).induce ({v}ᶜ : Set (Fin T.card))).chromaticNumber < (k : ℕ∞) := fun v =>
    lt_of_le_of_lt (SimpleGraph.chromaticNumber_mono_of_hom
      ⟨fun x => ⟨f x.1, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun h => x.2 (hfi h),
        (e.symm x.1).2⟩)⟩, fun h => h⟩) (hTcrit _ (e.symm v).2)
  have fin : ∀ s' : Set (Fin T.card),
      ((G.comap f).induce s').chromaticNumber ≥ (a : ℕ∞) →
      ((G.comap f).induce s'ᶜ).chromaticNumber ≥ (b : ℕ∞) →
      ∃ (s : Set V), (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
        (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞) := fun s' hs1 hs2 =>
    ⟨f '' s', le_trans hs1 (transfer G f hfi s').1, le_trans hs2 (transfer G f hfi s').2⟩
  rcases Nat.lt_or_ge a 3 with h | h
  · have ha2 : a = 2 := by omega
    subst ha2
    obtain ⟨s', hs1, hs2⟩ := h1 _ k _ hG'k hG'cl hG'crit (by omega)
    have hb : b = k - 1 := by omega
    subst hb
    exact fin s' (by exact_mod_cast hs1) hs2
  · obtain ⟨s', hs1, hs2⟩ := h2 _ k _ hG'k hG'cl hG'crit a b h hab' hab
    exact fin s' hs1 hs2

theorem main : H1 → H2 → type_of% @Erdos628.erdos_628 := by
  intro h1 h2 V _ G k hG_chrom hG_clique a b ha hb hab
  rcases le_total a b with h | h
  · exact key h1 h2 G k hG_chrom hG_clique a b ha h hab
  · obtain ⟨s, hs1, hs2⟩ := key h1 h2 G k hG_chrom hG_clique b a hb h (by omega)
    exact ⟨sᶜ, hs2, by rw [compl_compl]; exact hs1⟩

end OMA.R_Erdos628_erdos_628_R1
