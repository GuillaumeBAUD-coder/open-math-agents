import FormalConjectures.Wikipedia.TotalColoringConjecture

/-! Total coloring using vertex doubles and edge sums modulo the least odd integer at least n.
Credit: @Deldor14. -/
open SimpleGraph

theorem OMA.solution : type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.complete_graph := by
  classical
  intro n
  let q := 2 * (n / 2) + 1
  have hn : n ≤ q := by dsimp [q]; omega
  have : NeZero q := ⟨by dsimp [q]; omega⟩
  let f (v : Fin n) : ZMod q := v.val
  have hf : Function.Injective f := by
    intro u v h
    have hmod := (ZMod.natCast_eq_natCast_iff' u.val v.val q).mp h
    rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le u.isLt hn),
      Nat.mod_eq_of_lt (lt_of_lt_of_le v.isLt hn), ← Fin.ext_iff] at hmod
  have hunit : IsUnit (2 : ZMod q) := by
    apply (ZMod.isUnit_iff_coprime 2 q).2
    apply Nat.prime_two.coprime_iff_not_dvd.2
    dsimp [q]
    omega
  let edgeSum : Sym2 (Fin n) → ZMod q :=
    Sym2.lift ⟨fun u v => f u + f v, fun u v => add_comm _ _⟩
  have heq {v : Fin n} {e : Sym2 (Fin n)} (h : v ∈ e) :
      edgeSum e = f v + f (Sym2.Mem.other h) :=
    congrArg edgeSum (Sym2.other_spec h).symm
  let colors : ZMod q ≃ Fin q := Fintype.equivFinOfCardEq (ZMod.card q)
  have hc : (completeGraph (Fin n)).TotalColorable q := by
    refine ⟨Sum.elim (fun v => colors (2 * f v)) (fun e => colors (edgeSum e.val)), ?_, ?_, ?_⟩
    · intro u v huv h
      exact huv.ne (hf (hunit.mul_right_inj.mp (colors.injective h)))
    · rintro e d hne ⟨v, he, hd⟩ h
      have H : edgeSum e.val = edgeSum d.val := colors.injective h
      rw [heq he, heq hd] at H
      have ho := hf (add_left_cancel H)
      exact hne (Subtype.ext ((Sym2.other_spec he).symm.trans
        ((congrArg (fun x : Fin n => s(v, x)) ho).trans (Sym2.other_spec hd))))
    · intro v e he h
      have H : 2 * f v = edgeSum e.val := colors.injective h
      rw [two_mul, heq he] at H
      have ho := hf (add_left_cancel H)
      have hadj : (completeGraph (Fin n)).Adj v (Sym2.Mem.other he) := by
        apply (completeGraph (Fin n)).mem_edgeSet.mp
        rw [Sym2.other_spec he]
        exact e.property
      exact hadj.ne ho
  apply (Nat.sInf_le hc).trans
  change q ≤ (⊤ : SimpleGraph (Fin n)).maxDegree + 2
  simp only [maxDegree_top, Fintype.card_fin]
  dsimp [q]
  omega
