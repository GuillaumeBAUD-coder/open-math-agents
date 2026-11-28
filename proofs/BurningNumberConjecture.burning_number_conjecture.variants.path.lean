import FormalConjectures.Paper.BurningNumberConjecture

open SimpleGraph BurningNumberConjecture

theorem OMA.solution : type_of% @BurningNumberConjecture.burning_number_conjecture.variants.path := by
  intro n hn
  have hreach := pathGraph_preconnected n
  have hwalk : ∀ {a b : Fin n} (p : (pathGraph n).Walk a b),
      a.1 ≤ b.1 + p.length ∧ b.1 ≤ a.1 + p.length := by
    intro a b p; induction p with
    | nil => simp
    | @cons u v w h _ ih => have := pathGraph_adj.mp h; simp; omega
  have hdl (a b : Fin n) :
      a.1 ≤ b.1 + (pathGraph n).dist a b ∧ b.1 ≤ a.1 + (pathGraph n).dist a b := by
    obtain ⟨p, hp⟩ := (hreach a b).exists_walk_length_eq_dist; rw [← hp]; exact hwalk p
  have hdi : ∀ (d : ℕ) (a b : Fin n), b.1 = a.1 + d → (pathGraph n).dist a b ≤ d := by
    intro d; induction d with
    | zero => intro a b h; simp [Fin.ext (by omega : a.1 = b.1)]
    | succ d ih =>
      intro a b h
      let u : Fin n := ⟨a.1 + d, by omega⟩
      have hadj : (pathGraph n).Adj u b := pathGraph_adj.mpr (.inl (by dsimp [u]; omega))
      have := hadj.reachable.dist_triangle_right a
      have := dist_eq_one_iff_adj.mpr hadj
      have := ih a u rfl; omega
  have hdu (a b : Fin n) (r : ℕ) (ha : a.1 ≤ b.1 + r) (hb : b.1 ≤ a.1 + r) :
      (pathGraph n).dist a b ≤ r := by
    by_cases h : a.1 ≤ b.1
    · exact (hdi (b.1 - a.1) a b (by omega)).trans (by omega)
    · rw [SimpleGraph.dist_comm]; exact (hdi (a.1 - b.1) b a (by omega)).trans (by omega)
  let k := ⌈Real.sqrt n⌉₊
  have hceil (t : ℕ) : k ≤ t ↔ n ≤ t ^ 2 := by
    rw [Nat.ceil_le, Real.sqrt_le_left (by positivity), ← Nat.cast_pow, Nat.cast_le]
  have hcover : ∃ x : Fin k → Fin n, IsBurningSequence (pathGraph n) x := by
    let c (i : Fin k) : Fin n :=
      ⟨min (i.rev.1 ^ 2 + i.rev.1) (n - 1), (min_le_right _ _).trans_lt (by omega)⟩
    refine ⟨c, fun v => ?_⟩
    let r : Fin k := ⟨Nat.sqrt v.1, Nat.sqrt_lt'.mpr (v.2.trans_le ((hceil k).1 le_rfl))⟩
    refine ⟨r.rev, hreach _ _, ?_⟩
    have hrlo : r.1 ^ 2 ≤ v.1 := Nat.sqrt_le' _
    have hrhi : v.1 < (r.1 + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hhi : v.1 ≤ r.1 ^ 2 + 2 * r.1 := by nlinarith
    have : (c r.rev).1 = min (r.1 ^ 2 + r.1) (n - 1) := by simp [c]
    have := v.2; have := hdu (c r.rev) v r.1 (by omega) (by omega)
    have := Fin.val_rev r; omega
  refine le_antisymm (Nat.sInf_le hcover) ((hceil _).2 ?_)
  let m := burningNumber (pathGraph n)
  obtain ⟨x, hx⟩ : ∃ x : Fin m → Fin n, IsBurningSequence (pathGraph n) x :=
    Nat.sInf_mem (s := {j | ∃ y : Fin j → Fin n, IsBurningSequence (pathGraph n) y}) ⟨k, hcover⟩
  let I (r : Fin m) := Finset.Icc ((x r.rev).1 - r.1) ((x r.rev).1 + r.1)
  have hcard : n ≤ (Finset.univ.biUnion I).card := by
    simpa using Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
      (f := Fin.val) (t := Finset.univ.biUnion I)
      (fun v _ => by
        obtain ⟨i, _, hi⟩ := hx v
        have := hdl (x i) v; have := Fin.val_rev i
        exact Finset.mem_biUnion.mpr ⟨i.rev, Finset.mem_univ _, by simp [I]; omega⟩)
      Fin.val_injective.injOn
  have hsum : ∀ t : ℕ, ∑ j ∈ Finset.range t, (2 * j + 1) = t ^ 2 := fun t => by
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, ih]; ring
  exact hcard.trans <| Finset.card_biUnion_le.trans <|
    (Finset.sum_le_sum fun r _ => by simp only [I, Nat.card_Icc]; omega).trans
      ((Fin.sum_univ_eq_sum_range (fun j => 2 * j + 1) m).trans (hsum m)).le
