import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1
import Mathlib.Data.Nat.Factors
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! A finite certificate for the consecutive cubic residues bound.
The witness entries identify forbidden prime-label assignments if no pair has zero sums.
CaDiCaL produced the RUP refutation. Lean checks the entries and the refutation in the
kernel before applying the soundness lemmas. -/

namespace CubicCover

private abbrev Literal := ℕ × Bool
private abbrev Clause := List Literal
private abbrev Entry := ℕ × List (ℕ × Fin 3)

private def opposite (l : Literal) : Literal := (l.1, !l.2)

private def remaining (known : Clause) (c : Clause) : Clause :=
  c.filter (fun l => !known.contains (opposite l))

private def checkRup (formula : List Clause) : List ℕ → Clause → Bool
  | [], _ => false
  | index :: hints, known =>
    match formula[index]? with
    | none => false
    | some c =>
      match remaining known c with
      | [] => true
      | [l] => checkRup formula hints (l :: known)
      | _ => false

private def checkProof : List Clause → List (Clause × List ℕ) → Bool
  | _, [] => false
  | formula, (c, hints) :: rest =>
    if checkRup formula hints (c.map opposite) then
      if c.isEmpty then true else checkProof (formula ++ [c]) rest
    else false

private def holds (a : ℕ → Bool) (l : Literal) : Prop := a l.1 = l.2
private def clauseTrue (a : ℕ → Bool) (c : Clause) : Prop := ∃ l ∈ c, holds a l

private theorem opposite_true {a : ℕ → Bool} {l : Literal} (h : ¬ holds a l) :
    holds a (opposite l) := by
  rcases l with ⟨p, b⟩
  cases b <;> cases hb : a p <;> simp_all [holds, opposite]

private theorem true_and_opposite_impossible {a : ℕ → Bool} {l : Literal}
    (h : holds a l) (ho : holds a (opposite l)) : False := by
  rcases l with ⟨p, b⟩
  cases b <;> simp [holds, opposite] at h ho <;> simp_all

private theorem residual_true {a : ℕ → Bool} {known c : Clause}
    (hk : ∀ l ∈ known, holds a l) (hc : clauseTrue a c) :
    clauseTrue a (remaining known c) := by
  obtain ⟨l, hl, htrue⟩ := hc
  refine ⟨l, ?_, htrue⟩
  apply List.mem_filter.mpr
  refine ⟨hl, ?_⟩
  have hnot : opposite l ∉ known := fun h =>
    true_and_opposite_impossible htrue (hk _ h)
  simpa using hnot

private theorem rup_sound (a : ℕ → Bool) (formula : List Clause)
    (hf : ∀ c ∈ formula, clauseTrue a c) (hints : List ℕ) (known : Clause)
    (hk : ∀ l ∈ known, holds a l) (hcheck : checkRup formula hints known = true) : False := by
  induction hints generalizing known with
  | nil => simp [checkRup] at hcheck
  | cons index hints ih =>
    cases hcl : formula[index]? with
    | none => simp [checkRup, hcl] at hcheck
    | some c =>
      have hmem : c ∈ formula := List.mem_of_getElem? hcl
      have hres := residual_true hk (hf c hmem)
      cases hr : remaining known c with
      | nil => simp [hr, clauseTrue] at hres
      | cons l rest =>
        cases rest with
        | nil =>
          have hl : holds a l := by simpa [hr, clauseTrue] using hres
          apply ih (l :: known) _ (by simpa [checkRup, hcl, hr] using hcheck)
          intro v hv
          rcases List.mem_cons.mp hv with rfl | h
          · exact hl
          · exact hk v h
        | cons l' tail => simp [checkRup, hcl, hr] at hcheck

private theorem proof_sound (a : ℕ → Bool) (formula : List Clause)
    (hf : ∀ c ∈ formula, clauseTrue a c) (steps : List (Clause × List ℕ))
    (hcheck : checkProof formula steps = true) : False := by
  induction steps generalizing formula with
  | nil => simp [checkProof] at hcheck
  | cons step rest ih =>
    rcases step with ⟨c, hints⟩
    by_cases hr : checkRup formula hints (c.map opposite) = true
    · have hc : clauseTrue a c := by
        classical
        by_contra hn
        apply rup_sound a formula hf hints (c.map opposite) _ hr
        intro l hl
        obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
        exact opposite_true (fun ht => hn ⟨l', hl', ht⟩)
      cases c with
      | nil => simp [clauseTrue] at hc
      | cons l ls =>
        change (if checkRup formula hints ((l :: ls).map opposite) = true then
          checkProof (formula ++ [l :: ls]) rest else false) = true at hcheck
        rw [if_pos hr] at hcheck
        apply ih (formula ++ [l :: ls]) _ hcheck
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hf d hd
        · simpa using (show d = l :: ls from List.mem_singleton.mp hd) ▸ hc
    · simp [checkProof, hr] at hcheck

private def bits (entry : ℕ × Fin 3) : Clause :=
  if entry.2 = 2 then [(2 * entry.1 + 1, false)]
  else [(2 * entry.1, !entry.2.val.testBit 0), (2 * entry.1 + 1, !entry.2.val.testBit 1)]

private def assignment (w : ℕ → ZMod 3) (index : ℕ) : Bool :=
  (w (index / 2)).val.testBit (index % 2)

private def label (e : Entry) (p : ℕ) : Fin 3 := (e.2.lookup p).getD 0

private def validEntry (e : Entry) : Bool :=
  decide (e.1 ∈ Finset.Icc 1 77) &&
    (e.1.primeFactorsList ++ (e.1 + 1).primeFactorsList).all
      (fun p => decide ((p, label e p) ∈ e.2)) &&
    decide ((e.1.primeFactorsList.map (fun p => ((label e p).val : ZMod 3))).sum = 0) &&
    decide (((e.1 + 1).primeFactorsList.map (fun p => ((label e p).val : ZMod 3))).sum = 0)

private theorem eq_of_fin3_bits (a b : Fin 3)
    (h0 : b ≠ 2 → a.val.testBit 0 = b.val.testBit 0)
    (h1 : a.val.testBit 1 = b.val.testBit 1) : a = b := by
  have h : ∀ a b : Fin 3, (b ≠ 2 → a.val.testBit 0 = b.val.testBit 0) →
      a.val.testBit 1 = b.val.testBit 1 → a = b := by decide
  exact h a b h0 h1

private theorem match_label {e : Entry} {w : ℕ → ZMod 3} {p : ℕ} {v : Fin 3}
    (hp : (p, v) ∈ e.2) (h : ¬ clauseTrue (assignment w) (e.2.flatMap bits)) :
    w p = (v.val : ZMod 3) := by
  have h0 (hv : v ≠ 2) : ¬ (w p).val.testBit 0 = !v.val.testBit 0 := by
    intro he
    apply h
    refine ⟨(2*p, !v.val.testBit 0), List.mem_flatMap.mpr ⟨(p,v), hp, by simp [bits, hv]⟩, ?_⟩
    have hdiv : 2*p/2 = p := by omega
    have hmod : 2*p%2 = 0 := by omega
    simpa [holds, assignment, hdiv, hmod] using he
  have h1 : ¬ (w p).val.testBit 1 = !v.val.testBit 1 := by
    intro he
    apply h
    have hm : (2*p+1, !v.val.testBit 1) ∈ bits (p,v) := by
      by_cases hv : v = 2
      · subst v
        have ht : (2 : ℕ).testBit 1 = true := by decide
        simp [bits, ht]
      · simp [bits, hv]
    refine ⟨(2*p+1, !v.val.testBit 1), List.mem_flatMap.mpr ⟨(p,v), hp, hm⟩, ?_⟩
    have hdiv : (2*p+1)/2 = p := by omega
    have hmod : (2*p+1)%2 = 1 := by omega
    simpa [holds, assignment, hdiv, hmod] using he
  have hb (a b : Bool) : (¬ a = !b) → a = b := by
    cases a <;> cases b <;> decide
  have he := eq_of_fin3_bits ⟨(w p).val, ZMod.val_lt _⟩ v
    (fun hv => hb _ _ (h0 hv)) (hb _ _ h1)
  have hv : (w p).val = v.val := congrArg Fin.val he
  calc
    w p = ((w p).val : ZMod 3) := (ZMod.natCast_zmod_val (w p)).symm
    _ = (v.val : ZMod 3) := by rw [hv]

private theorem entry_true (w : ℕ → ZMod 3)
    (hnot : ¬ ∃ n ∈ Finset.Icc 1 77,
      (n.primeFactorsList.map w).sum = 0 ∧ ((n+1).primeFactorsList.map w).sum = 0)
    (e : Entry) (he : validEntry e = true) : clauseTrue (assignment w) (e.2.flatMap bits) := by
  classical
  simp only [validEntry, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨⟨⟨hn, hall⟩, hz₁⟩, hz₂⟩ := he
  by_contra hc
  have hmap (p : ℕ) (hp : p ∈ e.1.primeFactorsList ++ (e.1+1).primeFactorsList) :
      w p = ((label e p).val : ZMod 3) :=
    match_label (of_decide_eq_true (List.all_eq_true.mp hall p hp)) hc
  have h₁ : e.1.primeFactorsList.map w =
      e.1.primeFactorsList.map (fun p => ((label e p).val : ZMod 3)) :=
    List.map_congr_left fun p hp => hmap p (List.mem_append.mpr (Or.inl hp))
  have h₂ : (e.1+1).primeFactorsList.map w =
      (e.1+1).primeFactorsList.map (fun p => ((label e p).val : ZMod 3)) :=
    List.map_congr_left fun p hp => hmap p (List.mem_append.mpr (Or.inr hp))
  exact hnot ⟨e.1, hn, h₁ ▸ hz₁, h₂ ▸ hz₂⟩

private def entries : List Entry := [
  (1, [(2, 0)]),
  (6, [(2, 1), (3, 2), (7, 0)]),
  (7, [(2, 1), (7, 0)]),
  (7, [(2, 2), (7, 0)]),
  (8, [(2, 1), (3, 0)]),
  (8, [(2, 2), (3, 0)]),
  (11, [(2, 1), (3, 1), (11, 0)]),
  (11, [(2, 2), (3, 2), (11, 0)]),
  (12, [(2, 1), (3, 1), (13, 0)]),
  (12, [(2, 2), (3, 2), (13, 0)]),
  (21, [(2, 1), (3, 1), (7, 2), (11, 2)]),
  (21, [(2, 2), (3, 2), (7, 1), (11, 1)]),
  (26, [(2, 1), (3, 1), (13, 2)]),
  (26, [(2, 1), (3, 2), (13, 2)]),
  (26, [(2, 2), (3, 2), (13, 1)]),
  (27, [(2, 1), (3, 1), (7, 1)]),
  (27, [(2, 1), (3, 2), (7, 1)]),
  (27, [(2, 2), (3, 1), (7, 2)]),
  (27, [(2, 2), (3, 2), (7, 2)]),
  (63, [(2, 1), (3, 2), (7, 2)]),
  (63, [(2, 2), (3, 1), (7, 1)]),
  (77, [(2, 1), (3, 1), (7, 2), (11, 1), (13, 1)]),
  (77, [(2, 2), (3, 2), (7, 1), (11, 2), (13, 2)]),
]

private def derivation : List (Clause × List ℕ) := [
  ([(7, false), (15, false), (27, false)], [18, 0, 13]),
  ([(5, false), (7, true), (15, false)], [5, 17]),
  ([(5, true), (7, true), (27, false)], [0, 4, 12]),
  ([(5, true), (7, false), (27, false)], [0, 13]),
  ([(5, false), (7, false), (27, true)], [9, 14]),
  ([(4, false), (15, true), (7, false), (5, true)], [16, 1]),
  ([(5, false), (7, true)], [5, 24, 3, 20]),
  ([(14, false), (23, true), (5, false), (7, false), (15, true)], [11, 7]),
  ([(14, false), (15, true), (27, false), (5, false), (7, false)], [22, 30]),
  ([(27, false), (7, false)], [23, 26, 3, 31]),
  ([(15, true), (7, true)], [29, 0, 4, 2, 15]),
  ([(6, false), (27, true), (4, false), (7, true), (5, true)], [8, 33, 10, 6, 21]),
  ([(5, true), (7, true), (4, false)], [4, 25, 34]),
  ([(7, true)], [29, 0, 35]),
  ([(27, false)], [36, 32]),
  ([(5, false)], [37, 36, 27]),
  ([(4, true)], [38, 0]),
  ([(15, false)], [39, 36, 38, 19]),
  ([], [39, 40, 36, 38, 28]),
]

set_option maxRecDepth 15000 in
set_option maxHeartbeats 10000000 in
private theorem entries_valid : entries.all validEntry = true := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 10000000 in
private theorem refutation_valid :
    checkProof (entries.map fun e => e.2.flatMap bits) derivation = true := by decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 10000000 in
theorem checked_cover (w : ℕ → ZMod 3) :
    ∃ n ∈ Finset.Icc 1 77, (n.primeFactorsList.map w).sum = 0 ∧
      ((n+1).primeFactorsList.map w).sum = 0 := by
  classical
  by_contra h
  refine proof_sound (assignment w) (entries.map fun e => e.2.flatMap bits) ?_
    derivation refutation_valid
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  exact entry_true w h e (List.all_eq_true.mp entries_valid e he)

end CubicCover

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 :=
  CubicCover.checked_cover
