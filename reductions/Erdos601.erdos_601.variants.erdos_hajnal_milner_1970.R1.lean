import FormalConjectures.ErdosProblems.«601»

/-!
A reduction of the Erdős–Hajnal–Milner graph theorem.
Source: Set mappings and polarized partition relations (1970), Theorem 5 and pp. 358–362.
Credit: @HudZah
-/

namespace OMA.R_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1

open Ordinal Cardinal SimpleGraph Erdos601

-- Following a fresh neighbour at each step gives an infinite path.
private theorem finite_relative_degree {V : Type} (G : SimpleGraph V)
    (noPath : ¬ ∃ f : ℕ → V, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1)))
    (s : Set V) (hs : s.Nonempty) :
    ∃ x ∈ s, {y | y ∈ s ∧ G.Adj x y}.Finite := by
  classical
  by_contra! h
  obtain ⟨x, hx⟩ := hs
  have extend (v : s) (t : Finset V) : ∃ w : s, G.Adj v.val w.val ∧ w.val ∉ t := by
    obtain ⟨w, ⟨hws, haw⟩, hw⟩ := (h v.val v.property).exists_notMem_finset t
    exact ⟨⟨w, hws⟩, haw, hw⟩
  choose next nextAdj nextNew using extend
  let step (p : s × Finset V) : s × Finset V :=
    (next p.1 p.2, insert (next p.1 p.2).val p.2)
  let walk : ℕ → s × Finset V := Nat.rec (⟨x, hx⟩, {x}) (fun _ p => step p)
  have mem (n : ℕ) : (walk n).1.val ∈ (walk n).2 := by
    cases n <;> simp [walk, step]
  have mono : Monotone (fun n => (walk n).2) := by
    apply monotone_nat_of_le_succ
    intro n
    exact Finset.subset_insert _ _
  have distinct {i j : ℕ} (hij : i < j) : (walk i).1.val ≠ (walk j).1.val := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    intro heq
    have hold := mono (show i ≤ j by omega) (mem i)
    exact nextNew (walk j).1 (walk j).2 (heq ▸ hold)
  apply noPath
  refine ⟨fun n => (walk n).1.val, ?_, fun n => nextAdj (walk n).1 (walk n).2⟩
  intro i j hij
  rcases lt_trichotomy i j with hlt | hEq | hgt
  · exact (distinct hlt hij).elim
  · exact hEq
  · exact (distinct hgt hij.symm).elim

-- Extend a partial orientation at a vertex with finitely many remaining neighbours.
theorem finiteOrientation (V : Type) (G : SimpleGraph V)
    (noPath : ¬ ∃ f : ℕ → V, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))) :
    ∃ F : V → Finset V, (∀ x, x ∉ F x) ∧
      ∀ x y, G.Adj x y → y ∈ F x ∨ x ∈ F y := by
  classical
  let good : Set (Set (V × Finset V)) := {D |
    (∀ x A B, (x, A) ∈ D → (x, B) ∈ D → A = B) ∧
    (∀ x A, (x, A) ∈ D → x ∉ A) ∧
    ∀ x A, (x, A) ∈ D → ∀ y, G.Adj x y → y ∈ A ∨ ∃ B, (y, B) ∈ D ∧ x ∈ B}
  obtain ⟨D, hD⟩ := zorn_subset good (by
    intro c hc chain
    refine ⟨⋃₀ c, ?_, fun t ht => Set.subset_sUnion_of_mem ht⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro x A B ⟨t, ht, hA⟩ ⟨u, hu, hB⟩
      rcases chain.total ht hu with h | h
      · exact (hc hu).1 x A B (h hA) hB
      · exact (hc ht).1 x A B hA (h hB)
    · rintro x A ⟨t, ht, hA⟩
      exact (hc ht).2.1 x A hA
    · rintro x A ⟨t, ht, hA⟩ y hadj
      rcases (hc ht).2.2 x A hA y hadj with h | ⟨B, hB, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨B, ⟨t, ht, hB⟩, h⟩)
  let rest : Set V := {x | ¬ ∃ A, (x, A) ∈ D}
  have total (x : V) : ∃ A, (x, A) ∈ D := by
    by_contra hx
    obtain ⟨v, hv, hfin⟩ := finite_relative_degree G noPath rest ⟨x, hx⟩
    let N := hfin.toFinset
    have hN (y : V) : y ∈ N ↔ y ∈ rest ∧ G.Adj v y := Set.Finite.mem_toFinset _
    have added : insert (v, N) D ∈ good := by
      refine ⟨?_, ?_, ?_⟩
      · intro a A B hA hB
        rcases hA with hA | hA <;> rcases hB with hB | hB
        · exact congrArg Prod.snd (hA.trans hB.symm)
        · cases hA
          exact (hv ⟨B, hB⟩).elim
        · cases hB
          exact (hv ⟨A, hA⟩).elim
        · exact hD.1.1 a A B hA hB
      · rintro a A (h | h)
        · cases h
          exact fun ha => (hN _ |>.mp ha).2.ne rfl
        · exact hD.1.2.1 a A h
      · rintro a A (h | h) y hadj
        · cases h
          by_cases hy : y ∈ rest
          · exact Or.inl ((hN y).mpr ⟨hy, hadj⟩)
          have hy' : ∃ B, (y, B) ∈ D := Classical.not_not.mp hy
          obtain ⟨B, hB⟩ := hy'
          rcases hD.1.2.2 y B hB v hadj.symm with h | ⟨C, hC, _⟩
          · exact Or.inr ⟨B, Or.inr hB, h⟩
          · exact (hv ⟨C, hC⟩).elim
        · rcases hD.1.2.2 a A h y hadj with hy | ⟨B, hB, hy⟩
          · exact Or.inl hy
          · exact Or.inr ⟨B, Or.inr hB, hy⟩
    have back := hD.2 added (Set.subset_insert _ _)
    exact hv ⟨N, back (Set.mem_insert _ _)⟩
  choose F hF using total
  refine ⟨F, fun x => hD.1.2.1 x (F x) (hF x), ?_⟩
  intro x y hadj
  rcases hD.1.2.2 x (F x) (hF x) y hadj with h | ⟨B, hB, h⟩
  · exact Or.inl h
  · exact Or.inr ((hD.1.1 y B (F y) hB (hF y)) ▸ h)

-- Theorem 5 for a multiple of the first uncountable ordinal.
def H1 : Prop :=
  ∀ (γ : Ordinal.{0}), ω_ 1 * γ < ω_ 1 ^ (ω + 2) →
    ∀ F : (ω_ 1 * γ).ToType → Finset (ω_ 1 * γ).ToType, (∀ x, x ∉ F x) →
    ∃ s : Set (ω_ 1 * γ).ToType, typeLT s = ω_ 1 * γ ∧
      s.Pairwise (fun x y => y ∉ F x)

-- The countable limit ordinal case of Theorem 7.
def H2 : Prop :=
  ∀ β : Ordinal.{0}, β < ω_ 1 → Order.IsSuccLimit β → HasPathOrIndepSetOfType β

-- Attach a countable limit tail, assuming the graph theorem separately on each part.
def H3 : Prop :=
  ∀ γ β : Ordinal.{0}, γ ≠ 0 → β < ω_ 1 → Order.IsSuccLimit β →
    ω_ 1 * γ + β < ω_ 1 ^ (ω + 2) →
    HasPathOrIndepSetOfType (ω_ 1 * γ) → HasPathOrIndepSetOfType β →
    HasPathOrIndepSetOfType (ω_ 1 * γ + β)

theorem fullBlock (free : H1) (γ : Ordinal.{0})
    (bound : ω_ 1 * γ < ω_ 1 ^ (ω + 2)) : HasPathOrIndepSetOfType (ω_ 1 * γ) := by
  intro G
  by_cases hp : ∃ f : ℕ → _, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))
  · exact Or.inl hp
  obtain ⟨F, noSelf, cover⟩ := finiteOrientation _ G hp
  obtain ⟨s, htype, hfree⟩ := free γ bound F noSelf
  refine Or.inr ⟨s, (isIndepSet_iff G).2 ?_, htype⟩
  intro x hx y hy hxy hadj
  rcases cover x y hadj with h | h
  · exact hfree hx hy hxy h
  · exact hfree hy hx hxy.symm h

theorem main : H1 → H2 → H3 → type_of% @Erdos601.erdos_601.variants.erdos_hajnal_milner_1970 := by
  intro free countable append α hlim hbound
  let γ := α / ω_ 1
  let β := α % ω_ 1
  have split : ω_ 1 * γ + β = α := Ordinal.div_add_mod _ _
  have small : β < ω_ 1 := Ordinal.mod_lt _ (omega_pos 1).ne'
  rw [← split] at hlim hbound ⊢
  by_cases hg : γ = 0
  · simpa [hg] using countable β small (by simpa [hg] using hlim)
  have hb : ω_ 1 * γ < ω_ 1 ^ (ω + 2) := (le_self_add).trans_lt hbound
  have hblock := fullBlock free γ hb
  by_cases hz : β = 0
  · simpa [hz] using hblock
  have htail : Order.IsSuccLimit β :=
    (Ordinal.isSuccLimit_add_iff.mp hlim).resolve_right (fun h => hz h.1)
  exact append γ β hg small htail hbound hblock (countable β small htail)

end OMA.R_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1
