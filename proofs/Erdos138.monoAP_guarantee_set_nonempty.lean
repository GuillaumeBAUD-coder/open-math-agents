import FormalConjectures.ErdosProblems.«138»

-- Problem: Erdős Problem 138
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Van der Waerden's theorem (finitary form), deduced from Mathlib's Hales-Jewett theorem.

open Combinatorics

namespace OMA

/-- The value of a point of the cube: one plus the sum of its coordinates. -/
def val {ι : Type} [Fintype ι] {k : ℕ} (v : ι → Fin k) : ℕ := 1 + ∑ i, (v i : ℕ)

theorem val_mem {ι : Type} [Fintype ι] {k : ℕ} (v : ι → Fin k) :
    val v ∈ ((Finset.Icc 1 (1 + Fintype.card ι * k) : Finset ℕ) : Set ℕ) := by
  have h : ∑ i, (v i : ℕ) ≤ ∑ _i : ι, k :=
    Finset.sum_le_sum (fun i _ => (v i).2.le)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  simp only [Finset.coe_Icc, Set.mem_Icc, val]
  omega

theorem val_line {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} (l : Line (Fin k) ι) (x : Fin k) :
    val (l x) = (1 + ∑ i ∈ (Finset.univ.filter (fun i => l.idxFun i = none))ᶜ,
        ((l.idxFun i).map (fun y : Fin k => (y : ℕ))).getD 0)
      + (x : ℕ) • (Finset.univ.filter (fun i => l.idxFun i = none)).card := by
  unfold val
  rw [← Finset.sum_add_sum_compl (Finset.univ.filter (fun i => l.idxFun i = none))]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => l.idxFun i = none), ((l x i : Fin k) : ℕ)
      = (x : ℕ) • (Finset.univ.filter (fun i => l.idxFun i = none)).card := by
    rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [l.apply_none _ _ hi.2]
  have h2 : ∑ i ∈ (Finset.univ.filter (fun i => l.idxFun i = none))ᶜ, ((l x i : Fin k) : ℕ)
      = ∑ i ∈ (Finset.univ.filter (fun i => l.idxFun i = none))ᶜ,
        ((l.idxFun i).map (fun y : Fin k => (y : ℕ))).getD 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.2
    rw [Line.apply_some hy.symm, ← hy]
    rfl
  rw [h1, h2]
  ring

end OMA

theorem OMA.solution : type_of% @Erdos138.monoAP_guarantee_set_nonempty := by
  intro r k
  classical
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine ⟨1, fun coloring => ?_⟩
    exact (coloring ⟨1, by simp⟩).elim0
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨0, fun coloring => ⟨⟨0, hr⟩, ∅, ?_, ?_⟩⟩
    · simp
    · intro m hm
      exact absurd hm (Set.notMem_empty m)
  obtain ⟨ι, _inst, hι⟩ := Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨1 + Fintype.card ι * k, fun coloring => ?_⟩
  obtain ⟨l, c, hl⟩ := hι (fun v => coloring ⟨OMA.val v, OMA.val_mem v⟩)
  set s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none) with hs
  have hspos : 0 < s.card := Finset.card_pos.mpr ⟨l.proper.choose, by
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  set A : ℕ := 1 + ∑ i ∈ sᶜ, ((l.idxFun i).map (fun y : Fin k => (y : ℕ))).getD 0 with hA
  have hval : ∀ x : Fin k, OMA.val (l x) = A + (x : ℕ) • s.card := fun x => OMA.val_line l x
  refine ⟨c, {m | ∃ x : Fin k, m.1 = OMA.val (l x)}, ?_, ?_⟩
  · have himg : ((·.1) '' {m : ((Finset.Icc 1 (1 + Fintype.card ι * k) : Finset ℕ) : Set ℕ) |
        ∃ x : Fin k, m.1 = OMA.val (l x)}) =
        {y | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), A + n • s.card = y} := by
      ext y
      constructor
      · rintro ⟨m, ⟨x, hx⟩, rfl⟩
        exact ⟨x, by exact_mod_cast x.2, ((hval x).symm.trans hx.symm)⟩
      · rintro ⟨n, hn, rfl⟩
        have hn' : n < k := by exact_mod_cast hn
        exact ⟨⟨OMA.val (l ⟨n, hn'⟩), OMA.val_mem _⟩, ⟨⟨n, hn'⟩, rfl⟩, hval ⟨n, hn'⟩⟩
    refine ⟨A, s.card, ?_, himg⟩
    rw [himg]
    have hfin : {y | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), A + n • s.card = y} =
        (((Finset.range k).image (fun n => A + n • s.card) : Finset ℕ) : Set ℕ) := by
      ext y
      simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
        Set.mem_Iio, Nat.cast_lt, exists_prop]
    rw [hfin, ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective, Finset.card_range]
    intro n1 n2 h
    simp only [smul_eq_mul] at h
    have : n1 * s.card = n2 * s.card := by omega
    exact Nat.eq_of_mul_eq_mul_right hspos this
  · rintro m ⟨x, hx⟩
    rw [← hl x]
    congr 1
    exact Subtype.ext hx
