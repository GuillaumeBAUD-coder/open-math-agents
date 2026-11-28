import OMAReductions.R_opg_black_and_white_cycle_conjecture_R1

-- Step opg-black-and-white-cycle-conjecture.R1.H1: hypothesis H1 of reduction opg-black-and-white-cycle-conjecture.R1
-- Credit: @nnkostov

/-!
We prove Tutte's cut-parity characterization of nowhere-zero 4-flows for any
finite multigraph (and both `hole = none` and `hole = some e`):
1. Any even-degree edge subset `C` decomposes into edge-disjoint closed trails
   carrying a conservative `{±1}`-valued circulation supported on `C`
   (`exists_unit_circulation`).
2. Forward (`HasNZ4Flow → cut-parity`): given a nowhere-zero 4-flow `f`, let `A`
   be its odd support and subtract a unit circulation `g` on `A`. Then `h = (f - g)/2`
   is conservative, its odd support `B` has even degrees everywhere, and `B` covers
   `E \ A` (where `|f e| = 2`, `g e = 0`, `|h e| = 1`), forcing every cut avoiding
   `A` to meet `B` (and `E`) in an even number of edges.
3. Backward (`cut-parity → HasNZ4Flow`): starting from `B₀ = E \ A`, repeatedly
   pair odd-degree vertices of `B` within a connected component of `(V, A)` and
   toggle along an `A`-walk in `ZMod 2` until all vertices have even degree in `B`
   while preserving `E \ A ⊆ B`. Summing unit circulations `gA + 2 gB` yields a
   nowhere-zero 4-flow.
-/

open OMA.S_opg_black_and_white_cycle_conjecture

private lemma zmod2_cast_int_eq_ite {P : Prop} [Decidable P] (z : ℤ)
    (hz : P ↔ Odd z) : ((z : ℤ) : ZMod 2) = if P then 1 else 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  by_cases hp : P
  · obtain ⟨k, rfl⟩ := hz.mp hp
    push_cast
    rw [h2, zero_mul, zero_add]
    simp [hp]
  · have hev : Even z := Int.not_odd_iff_even.mp (fun h => hp (hz.mpr h))
    obtain ⟨k, rfl⟩ := hev
    push_cast
    rw [← two_mul, h2, zero_mul]
    simp [hp]

private lemma even_degIn_of_conservative {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (f : E → ℤ) (hf : IsConservative src tgt f)
    (C : Finset E) (hC : ∀ e, e ∈ C ↔ Odd (f e)) (v : V) :
    Even (degIn src tgt C v) := by
  have hcons := congrArg (Int.cast : ℤ → ZMod 2) (hf v)
  push_cast at hcons
  have hcast : ∀ p : E → Prop, ∀ [DecidablePred p],
      ∑ e ∈ Finset.univ.filter p, ((f e : ℤ) : ZMod 2) = ((C.filter p).card : ZMod 2) := by
    intro p _
    calc
      ∑ e ∈ Finset.univ.filter p, ((f e : ℤ) : ZMod 2)
          = ∑ e ∈ Finset.univ.filter p, (if e ∈ C then (1 : ZMod 2) else 0) := by
        refine Finset.sum_congr rfl fun e _ => zmod2_cast_int_eq_ite (f e) (hC e)
      _ = ∑ _e ∈ (Finset.univ.filter p).filter (· ∈ C), (1 : ZMod 2) := by
        rw [← Finset.sum_filter]
      _ = (((Finset.univ.filter p).filter (· ∈ C)).card : ZMod 2) := by simp
      _ = ((C.filter p).card : ZMod 2) := by
        congr 2
        ext e
        simp [and_comm]
  rw [hcast (fun e => tgt e = v), hcast (fun e => src e = v)] at hcons
  have hzero : ((C.filter (fun e => src e = v)).card : ZMod 2) +
      ((C.filter (fun e => tgt e = v)).card : ZMod 2) = 0 := by
    rw [hcons]
    have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
    exact h2 _
  rw [← Nat.cast_add] at hzero
  exact (ZMod.natCast_eq_zero_iff_even).mp hzero

private lemma sum_degIn_zmod2 {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (B : Finset E) (S : Finset V) :
    ((∑ v ∈ S, degIn src tgt B v : ℕ) : ZMod 2) =
      (((B.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card : ℕ) : ZMod 2) := by
  have hfib : ∀ φ : E → V, ∑ v ∈ S, (B.filter fun e => φ e = v).card =
      (B.filter fun e => φ e ∈ S).card := by
    intro φ
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : φ e ∈ S <;> simp [h]
  unfold degIn
  rw [Finset.sum_add_distrib, hfib src, hfib tgt, Nat.cast_add]
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hs : src e ∈ S <;> by_cases ht : tgt e ∈ S
  · simp only [hs, ht, decide_true, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    decide
  · simp [hs, ht]
  · simp [hs, ht]
  · simp [hs, ht]

private def epStart {V E : Type*} (src tgt : E → V) (p : E × Bool) : V :=
  if p.2 then tgt p.1 else src p.1

private def epEnd {V E : Type*} (src tgt : E → V) (p : E × Bool) : V :=
  if p.2 then src p.1 else tgt p.1

private def stepSign (b : Bool) : ℤ :=
  if b then -1 else 1

private def trailVerts {V E : Type*} (src tgt : E → V) : List (E × Bool) → List V
  | [] => []
  | p :: ps => epStart src tgt p :: (p :: ps).map (epEnd src tgt)

private def IsSimpleTrail {V E : Type*} (src tgt : E → V) (C : Finset E)
    (L : List (E × Bool)) : Prop :=
  L ≠ [] ∧
  (∀ p ∈ L, p.1 ∈ C) ∧
  (∀ i : ℕ, (hi : i + 1 < L.length) →
    epEnd src tgt L[i] = epStart src tgt L[i + 1]) ∧
  (trailVerts src tgt L).Nodup

private lemma trailVerts_length {V E : Type*} (src tgt : E → V) (L : List (E × Bool))
    (hne : L ≠ []) : (trailVerts src tgt L).length = L.length + 1 := by
  cases L with
  | nil => exact absurd rfl hne
  | cons p ps => simp [trailVerts]

private lemma trailVerts_getElem_zero {V E : Type*} (src tgt : E → V)
    (L : List (E × Bool)) (hne : L ≠ []) :
    (trailVerts src tgt L)[0]'(by rw [trailVerts_length src tgt L hne]; exact Nat.succ_pos _) =
      epStart src tgt (L[0]'(List.length_pos_of_ne_nil hne)) := by
  cases L with
  | nil => exact absurd rfl hne
  | cons p ps => rfl

private lemma trailVerts_getElem_succ {V E : Type*} (src tgt : E → V)
    (L : List (E × Bool)) (j : ℕ) (hj : j < L.length) :
    have hne : L ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hj)
    (trailVerts src tgt L)[j + 1]'(by rw [trailVerts_length src tgt L hne]; exact Nat.succ_lt_succ hj) =
      epEnd src tgt L[j] := by
  cases L with
  | nil => simp at hj
  | cons p ps =>
    simp only [trailVerts, List.getElem_cons_succ, List.getElem_map]

private lemma trailVerts_getElem_eq_epStart {V E : Type*} (src tgt : E → V)
    (C : Finset E) (L : List (E × Bool)) (hL : IsSimpleTrail src tgt C L)
    (j : ℕ) (hj : j < L.length) :
    (trailVerts src tgt L)[j]'(by rw [trailVerts_length src tgt L hL.1]; omega) =
      epStart src tgt L[j] := by
  cases j with
  | zero => exact trailVerts_getElem_zero src tgt L hL.1
  | succ k =>
    rw [trailVerts_getElem_succ src tgt L k (by omega)]
    exact hL.2.2.1 k hj

private lemma extend_to_max_trail {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (C : Finset E) (k : ℕ) :
    ∀ L : List (E × Bool), IsSimpleTrail src tgt C L → Fintype.card V - L.length ≤ k →
      ∃ L' : List (E × Bool), IsSimpleTrail src tgt C L' ∧
        ∀ e' b', ¬ IsSimpleTrail src tgt C (L' ++ [(e', b')]) := by
  induction k with
  | zero =>
    intro L hL hle
    exfalso
    have hcard : L.length + 1 ≤ Fintype.card V := by
      have hlen : (trailVerts src tgt L).toFinset.card = L.length + 1 := by
        rw [List.toFinset_card_of_nodup hL.2.2.2, trailVerts_length src tgt L hL.1]
      rw [← hlen]
      exact Finset.card_le_univ _
    omega
  | succ k ih =>
    intro L hL hle
    by_cases hmax : ∀ e' b', ¬ IsSimpleTrail src tgt C (L ++ [(e', b')])
    · exact ⟨L, hL, hmax⟩
    · push Not at hmax
      obtain ⟨e', b', hnext⟩ := hmax
      refine ih (L ++ [(e', b')]) hnext ?_
      simp only [List.length_append, List.length_singleton]
      omega

private lemma isConservative_closed_chain {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (W : List (E × Bool)) (hne : W ≠ [])
    (hchain : ∀ j : ℕ, (hj : j + 1 < W.length) →
      epEnd src tgt W[j] = epStart src tgt W[j + 1])
    (hclosed : epEnd src tgt (W.getLast hne) = epStart src tgt (W.head hne)) :
    IsConservative src tgt (fun e => (W.map fun p => if p.1 = e then stepSign p.2 else 0).sum) := by
  have hdiff : ∀ (L : List (E × Bool)) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => tgt e = v),
          (L.map fun p => if p.1 = e then stepSign p.2 else 0).sum) -
        (∑ e ∈ Finset.univ.filter (fun e => src e = v),
          (L.map fun p => if p.1 = e then stepSign p.2 else 0).sum) =
        (L.map fun p =>
          (if epEnd src tgt p = v then (1 : ℤ) else 0) -
          (if epStart src tgt p = v then (1 : ℤ) else 0)).sum := by
    intro L v
    induction L with
    | nil => simp
    | cons p ps ih =>
      rcases p with ⟨e₀, b₀⟩
      simp only [List.map_cons, List.sum_cons]
      have hsum_add : ∀ s : Finset E, ∀ f g : E → ℤ,
          ∑ e ∈ s, (f e + g e) = (∑ e ∈ s, f e) + ∑ e ∈ s, g e :=
        fun s f g => Finset.sum_add_distrib
      rw [hsum_add, hsum_add]
      have hterm : ∀ φ : E → V,
          ∑ e ∈ Finset.univ.filter (fun e => φ e = v),
              (if e₀ = e then stepSign b₀ else 0) =
            if φ e₀ = v then stepSign b₀ else 0 := by
        intro φ
        by_cases hφ : φ e₀ = v
        · rw [if_pos hφ]
          rw [Finset.sum_eq_single e₀]
          · simp
          · intro e _ hne_e
            rw [if_neg hne_e.symm]
          · intro hmem
            exfalso
            exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ⟩)
        · rw [if_neg hφ]
          refine Finset.sum_eq_zero fun e he => ?_
          have hev : φ e = v := (Finset.mem_filter.mp he).2
          have hne_e : e₀ ≠ e := fun h => hφ (h ▸ hev)
          exact if_neg hne_e
      rw [hterm tgt, hterm src]
      have hsingle : (if tgt e₀ = v then stepSign b₀ else 0) -
          (if src e₀ = v then stepSign b₀ else 0) =
          (if epEnd src tgt (e₀, b₀) = v then (1 : ℤ) else 0) -
          (if epStart src tgt (e₀, b₀) = v then (1 : ℤ) else 0) := by
        cases b₀ <;> by_cases hs : src e₀ = v <;> by_cases ht : tgt e₀ = v <;>
          simp [stepSign, epStart, epEnd, hs, ht]
      linarith
  have htele : ∀ (f : V → ℤ) (L : List (E × Bool)) (hL : L ≠ []),
      (∀ j : ℕ, (hj : j + 1 < L.length) → epEnd src tgt L[j] = epStart src tgt L[j + 1]) →
      (L.map fun p => f (epEnd src tgt p) - f (epStart src tgt p)).sum =
        f (epEnd src tgt (L.getLast hL)) - f (epStart src tgt (L.head hL)) := by
    intro f L
    induction L with
    | nil => intro hL; exact absurd rfl hL
    | cons p ps ih =>
      intro _ hch
      cases ps with
      | nil => simp
      | cons q qs =>
        have hqs : q :: qs ≠ [] := List.cons_ne_nil _ _
        have hch' : ∀ j : ℕ, (hj : j + 1 < (q :: qs).length) →
            epEnd src tgt (q :: qs)[j] = epStart src tgt (q :: qs)[j + 1] := by
          intro j hj
          exact hch (j + 1) (by simpa using hj)
        have ih' := ih hqs hch'
        have hjoin : epEnd src tgt p = epStart src tgt q := by
          have := hch 0 (by simp)
          simpa using this
        have hlast : (p :: q :: qs).getLast (List.cons_ne_nil _ _) =
            (q :: qs).getLast hqs := List.getLast_cons hqs
        rw [List.map_cons, List.sum_cons, ih', hjoin, hlast]
        simp only [List.head_cons]
        ring
  intro v
  have h0 := hdiff W v
  rw [htele (fun u => if u = v then (1 : ℤ) else 0) W hne hchain, hclosed, sub_self] at h0
  exact eq_of_sub_eq_zero h0

private lemma degIn_erase_of_nonloop {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (C : Finset E) (e : E) (he : e ∈ C) (_hne : src e ≠ tgt e) (v : V) :
    degIn src tgt C v = degIn src tgt (C.erase e) v +
      (if src e = v then 1 else 0) + (if tgt e = v then 1 else 0) := by
  have hpart : ∀ φ : E → V, (C.filter fun d => φ d = v).card =
      ((C.erase e).filter fun d => φ d = v).card + (if φ e = v then 1 else 0) := by
    intro φ
    by_cases hφ : φ e = v
    · rw [if_pos hφ]
      have hmem : e ∈ C.filter fun d => φ d = v := Finset.mem_filter.mpr ⟨he, hφ⟩
      have heq : (C.erase e).filter (fun d => φ d = v) = (C.filter fun d => φ d = v).erase e := by
        ext d
        simp [and_comm, and_left_comm]
      rw [heq, Finset.card_erase_of_mem hmem]
      have hpos : 0 < (C.filter fun d => φ d = v).card := Finset.card_pos.mpr ⟨e, hmem⟩
      omega
    · rw [if_neg hφ, add_zero]
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hd, hdφ⟩
        exact ⟨⟨fun h => hφ (h ▸ hdφ), hd⟩, hdφ⟩
      · rintro ⟨⟨_, hd⟩, hdφ⟩
        exact ⟨hd, hdφ⟩
  unfold degIn
  rw [hpart src, hpart tgt]
  omega

private lemma degIn_erase_loop {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (C : Finset E) (e : E) (he : e ∈ C) (hloop : src e = tgt e) (v : V) :
    degIn src tgt C v = degIn src tgt (C.erase e) v + (if src e = v then 2 else 0) := by
  have hpart : ∀ φ : E → V, (C.filter fun d => φ d = v).card =
      ((C.erase e).filter fun d => φ d = v).card + (if φ e = v then 1 else 0) := by
    intro φ
    by_cases hφ : φ e = v
    · rw [if_pos hφ]
      have hmem : e ∈ C.filter fun d => φ d = v := Finset.mem_filter.mpr ⟨he, hφ⟩
      have heq : (C.erase e).filter (fun d => φ d = v) = (C.filter fun d => φ d = v).erase e := by
        ext d
        simp [and_comm, and_left_comm]
      rw [heq, Finset.card_erase_of_mem hmem]
      have hpos : 0 < (C.filter fun d => φ d = v).card := Finset.card_pos.mpr ⟨e, hmem⟩
      omega
    · rw [if_neg hφ, add_zero]
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hd, hdφ⟩
        exact ⟨⟨fun h => hφ (h ▸ hdφ), hd⟩, hdφ⟩
      · rintro ⟨⟨_, hd⟩, hdφ⟩
        exact ⟨hd, hdφ⟩
  unfold degIn
  rw [hpart src, hpart tgt, ← hloop]
  split_ifs <;> omega

private lemma exists_unit_circulation {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (C : Finset E)
    (hC : ∀ v, Even (degIn src tgt C v)) :
    ∃ g : E → ℤ, (∀ e, e ∈ C → |g e| = 1) ∧ (∀ e, e ∉ C → g e = 0) ∧
      IsConservative src tgt g := by
  classical
  suffices h : ∀ n : ℕ, ∀ C : Finset E, C.card = n → (∀ v, Even (degIn src tgt C v)) →
      ∃ g : E → ℤ, (∀ e, e ∈ C → |g e| = 1) ∧ (∀ e, e ∉ C → g e = 0) ∧
        IsConservative src tgt g from h C.card C rfl hC
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro C hn hC_even
    by_cases hEmpty : C = ∅
    · subst hEmpty
      refine ⟨fun _ => 0, fun _ h => absurd h (by simp), fun _ _ => rfl, ?_⟩
      intro v
      simp
    · have hne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      by_cases hloop : ∃ e₀ ∈ C, src e₀ = tgt e₀
      · obtain ⟨e₀, he₀, hsrc_tgt⟩ := hloop
        set C' := C.erase e₀
        have hlt : C'.card < n := by
          rw [← hn]
          exact Finset.card_erase_lt_of_mem he₀
        have hC'_even : ∀ v, Even (degIn src tgt C' v) := by
          intro v
          have heq := degIn_erase_loop src tgt C e₀ he₀ hsrc_tgt v
          have hv := hC_even v
          rw [heq, Nat.even_add] at hv
          have hif : Even (if src e₀ = v then 2 else 0) := by
            split_ifs
            · exact ⟨1, rfl⟩
            · exact ⟨0, rfl⟩
          exact hv.mpr hif
        obtain ⟨g', hg'1, hg'0, hg'_cons⟩ := ih C'.card hlt C' rfl hC'_even
        refine ⟨fun e => if e = e₀ then 1 else g' e, ?_, ?_, ?_⟩
        · intro e he
          dsimp only
          by_cases hee₀ : e = e₀
          · simp [hee₀]
          · rw [if_neg hee₀]
            exact hg'1 e (Finset.mem_erase.mpr ⟨hee₀, he⟩)
        · intro e he
          dsimp only
          have hee₀ : e ≠ e₀ := fun h => he (h ▸ he₀)
          rw [if_neg hee₀]
          exact hg'0 e (fun h => he (Finset.mem_erase.mp h).2)
        · intro v
          have heq_sums : ∀ φ : E → V, φ e₀ = src e₀ →
              ∑ e ∈ Finset.univ.filter (fun e => φ e = v), (if e = e₀ then (1 : ℤ) else g' e) =
                (if src e₀ = v then 1 else 0) +
                  ∑ e ∈ Finset.univ.filter (fun e => φ e = v), g' e := by
            intro φ hφ
            have he₀_g' : g' e₀ = 0 := hg'0 e₀ (Finset.notMem_erase e₀ C)
            have hstep : ∀ e : E, (if e = e₀ then (1 : ℤ) else g' e) =
                (if e = e₀ then 1 else 0) + g' e := by
              intro e
              by_cases hee : e = e₀
              · subst hee; simp [he₀_g']
              · simp [hee]
            simp_rw [hstep, Finset.sum_add_distrib]
            congr 1
            by_cases hsv : src e₀ = v
            · rw [if_pos hsv]
              have hmem : e₀ ∈ Finset.univ.filter (fun e => φ e = v) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ.trans hsv⟩
              rw [Finset.sum_eq_single e₀]
              · simp
              · intro e _ hee₀; rw [if_neg hee₀]
              · intro h; exact absurd hmem h
            · rw [if_neg hsv]
              refine Finset.sum_eq_zero fun e he => ?_
              have hne_e : e ≠ e₀ := fun h => hsv (hφ.symm.trans (h ▸ (Finset.mem_filter.mp he).2))
              exact if_neg hne_e
          rw [heq_sums tgt hsrc_tgt.symm, heq_sums src rfl, hg'_cons v]
      · push Not at hloop
        obtain ⟨e₀, he₀⟩ := hne
        have hinit : IsSimpleTrail src tgt C [(e₀, false)] := by
          refine ⟨by simp, ?_, ?_, ?_⟩
          · intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            exact he₀
          · intro i hi; simp at hi
          · simp [trailVerts, epStart, epEnd, hloop e₀ he₀]
        obtain ⟨L, hL, hmax⟩ := extend_to_max_trail src tgt C (Fintype.card V - 1) [(e₀, false)] hinit le_rfl
        have hL_ne : L ≠ [] := hL.1
        set p_last := L.getLast hL_ne
        set e_last := p_last.1
        set v_last := epEnd src tgt p_last
        have he_last_mem : e_last ∈ C := hL.2.1 p_last (List.getLast_mem hL_ne)
        have hlast_nonloop : src e_last ≠ tgt e_last := hloop e_last he_last_mem
        have hv_inc : src e_last = v_last ∨ tgt e_last = v_last := by
          dsimp [v_last, e_last, epEnd]
          cases p_last.2 <;> simp
        have hdeg_last : degIn src tgt C v_last = degIn src tgt (C.erase e_last) v_last + 1 := by
          have heq := degIn_erase_of_nonloop src tgt C e_last he_last_mem hlast_nonloop v_last
          rcases hv_inc with h1 | h2
          · have h2' : tgt e_last ≠ v_last := fun h => hlast_nonloop (h1.trans h.symm)
            rw [if_pos h1, if_neg h2'] at heq
            exact heq
          · have h1' : src e_last ≠ v_last := fun h => hlast_nonloop (h.trans h2.symm)
            rw [if_neg h1', if_pos h2] at heq
            exact heq
        have hdeg_pos : 0 < degIn src tgt (C.erase e_last) v_last := by
          have heven := hC_even v_last
          rw [hdeg_last] at heven
          rcases heven with ⟨k, hk⟩
          omega
        have hex_next : ∃ e' ∈ C.erase e_last, src e' = v_last ∨ tgt e' = v_last := by
          by_contra hnone
          push Not at hnone
          have h0 : degIn src tgt (C.erase e_last) v_last = 0 := by
            unfold degIn
            have hs0 : ((C.erase e_last).filter (fun e => src e = v_last)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro e he hs
              exact (hnone e he).1 hs
            have ht0 : ((C.erase e_last).filter (fun e => tgt e = v_last)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro e he ht
              exact (hnone e he).2 ht
            rw [hs0, ht0]
          omega
        obtain ⟨e', he'_mem, he'_inc⟩ := hex_next
        have he'_C : e' ∈ C := (Finset.mem_erase.mp he'_mem).2
        have he'_ne_last : e' ≠ e_last := (Finset.mem_erase.mp he'_mem).1
        let b' : Bool := decide (src e' ≠ v_last)
        have hb'_start : epStart src tgt (e', b') = v_last := by
          dsimp [epStart, b']
          by_cases h : src e' = v_last
          · simp [h]
          · simp [h]
            exact he'_inc.resolve_left h
        let w : V := epEnd src tgt (e', b')
        have hw_ne_vlast : w ≠ v_last := by
          dsimp [w, epEnd, b']
          by_cases h : src e' = v_last
          · simp only [h, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
            intro ht
            exact hloop e' he'_C (h.trans ht.symm)
          · simp only [h, not_false_eq_true, decide_true, ↓reduceIte]
        have hw_in_L : w ∈ trailVerts src tgt L := by
          by_contra hw_nmem
          apply hmax e' b'
          refine ⟨by simp, ?_, ?_, ?_⟩
          · intro p hp
            simp only [List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · exact hL.2.1 p hp
            · exact he'_C
          · intro j hj
            rw [List.length_append, List.length_singleton] at hj
            by_cases hj1 : j + 1 < L.length
            · rw [List.getElem_append_left (by omega), List.getElem_append_left hj1]
              exact hL.2.2.1 j hj1
            · have hj_eq : j + 1 = L.length := by omega
              have hj_lt : j < L.length := by omega
              rw [List.getElem_append_left hj_lt]
              have hr : j + 1 - L.length = 0 := by omega
              have hget_last : L[j] = p_last := by
                dsimp [p_last]
                rw [List.getLast_eq_getElem]
                congr 1
                omega
              have hge : L.length ≤ j + 1 := by omega
              simp only [List.getElem_append_right hge, hr, List.getElem_singleton]
              rw [hget_last]
              exact hb'_start.symm
          · have htv : trailVerts src tgt (L ++ [(e', b')]) = trailVerts src tgt L ++ [w] := by
              cases L with
              | nil => exact absurd rfl hL_ne
              | cons q qs => simp [trailVerts, w]
            rw [htv, List.nodup_append]
            refine ⟨hL.2.2.2, List.nodup_singleton w, ?_⟩
            intro x hx y hy hxy
            simp only [List.mem_singleton] at hy
            subst y
            subst x
            exact hw_nmem hx
        obtain ⟨i, hi_len, hi_eq⟩ := List.mem_iff_getElem.mp hw_in_L
        rw [trailVerts_length src tgt L hL_ne] at hi_len
        have hi_lt : i < L.length := by
          by_contra hnot
          have hi_eq_len : i = L.length := by omega
          have hlast_vert : (trailVerts src tgt L)[L.length]'(by rw [trailVerts_length src tgt L hL_ne]; omega) = v_last := by
            have h1 : L.length - 1 < L.length := Nat.sub_lt (List.length_pos_of_ne_nil hL_ne) Nat.one_pos
            have h2 := trailVerts_getElem_succ src tgt L (L.length - 1) h1
            have hidx : L.length - 1 + 1 = L.length := by omega
            have hgl : p_last = L[L.length - 1] := List.getLast_eq_getElem hL_ne
            rw [show v_last = epEnd src tgt L[L.length - 1] by dsimp [v_last]; rw [hgl]]
            simpa [hidx] using h2
          have hi_eq' : (trailVerts src tgt L)[L.length]'(by rw [trailVerts_length src tgt L hL_ne]; omega) = w := by
            simpa [hi_eq_len] using hi_eq
          exact hw_ne_vlast (hi_eq'.symm.trans hlast_vert)
        have hL_nodup_edges : (L.map Prod.fst).Nodup := by
          rw [List.nodup_iff_getElem?_ne_getElem?]
          intro j₁ j₂ hj₁₂ hj₂_len hsome
          have hj₂' : j₂ < L.length := by simpa using hj₂_len
          have hj₁' : j₁ < L.length := lt_trans hj₁₂ hj₂'
          have hj₁_len : j₁ < (L.map Prod.fst).length := by simpa using hj₁'
          simp only [List.getElem?_eq_getElem hj₁_len, List.getElem?_eq_getElem hj₂_len,
            List.getElem_map, Option.some.injEq] at hsome
          have hv2_mem : (trailVerts src tgt L)[j₂ + 1]'(by rw [trailVerts_length src tgt L hL_ne]; omega) =
              epStart src tgt L[j₁] ∨
              (trailVerts src tgt L)[j₂ + 1]'(by rw [trailVerts_length src tgt L hL_ne]; omega) =
              epEnd src tgt L[j₁] := by
            rw [trailVerts_getElem_succ src tgt L j₂ hj₂']
            dsimp [epStart, epEnd]
            rw [hsome]
            cases L[j₂].2 <;> cases L[j₁].2 <;> simp
          have ht1 := trailVerts_getElem_eq_epStart src tgt C L hL j₁ hj₁'
          have ht2 := trailVerts_getElem_succ src tgt L j₁ hj₁'
          rw [← ht1, ← ht2] at hv2_mem
          have hinj := hL.2.2.2.getElem_inj_iff (i := j₂ + 1) (j := j₁)
            (hi := by rw [trailVerts_length src tgt L hL_ne]; omega)
            (hj := by rw [trailVerts_length src tgt L hL_ne]; omega)
          have hinj2 := hL.2.2.2.getElem_inj_iff (i := j₂ + 1) (j := j₁ + 1)
            (hi := by rw [trailVerts_length src tgt L hL_ne]; omega)
            (hj := by rw [trailVerts_length src tgt L hL_ne]; omega)
          rcases hv2_mem with h | h
          · have := hinj.mp h; omega
          · have := hinj2.mp h; omega
        have he'_nmem_L : e' ∉ L.map Prod.fst := by
          intro hmem
          obtain ⟨j, hj_len, hj_eq⟩ := List.mem_iff_getElem.mp hmem
          have hj' : j < L.length := by simpa using hj_len
          simp only [List.getElem_map] at hj_eq
          have hj_ne_last : j ≠ L.length - 1 := by
            intro h
            have he_eq : e_last = e' := by
              dsimp [e_last, p_last]
              rw [List.getLast_eq_getElem]
              simp only [← h, hj_eq]
            exact he'_ne_last he_eq.symm
          have hj1 : j + 1 < L.length := by omega
          have hvlast_mem : (trailVerts src tgt L)[L.length]'(by rw [trailVerts_length src tgt L hL_ne]; omega) =
              epStart src tgt L[j] ∨
              (trailVerts src tgt L)[L.length]'(by rw [trailVerts_length src tgt L hL_ne]; omega) =
              epEnd src tgt L[j] := by
            have h1 : L.length - 1 < L.length := Nat.sub_lt (List.length_pos_of_ne_nil hL_ne) Nat.one_pos
            have h2 := trailVerts_getElem_succ src tgt L (L.length - 1) h1
            have hidx : L.length - 1 + 1 = L.length := by omega
            have hgl : p_last = L[L.length - 1] := List.getLast_eq_getElem hL_ne
            have hv_eq : (trailVerts src tgt L)[L.length]'(by rw [trailVerts_length src tgt L hL_ne]; omega) = v_last := by
              dsimp [v_last]; rw [hgl]; simpa [hidx] using h2
            rw [hv_eq, ← hb'_start]
            dsimp [epStart, epEnd]
            rw [hj_eq]
            cases b' <;> cases L[j].2 <;> simp
          have ht1 := trailVerts_getElem_eq_epStart src tgt C L hL j hj'
          have ht2 := trailVerts_getElem_succ src tgt L j hj'
          rw [← ht1, ← ht2] at hvlast_mem
          have hinj1 := hL.2.2.2.getElem_inj_iff (i := L.length) (j := j)
            (hi := by rw [trailVerts_length src tgt L hL_ne]; omega)
            (hj := by rw [trailVerts_length src tgt L hL_ne]; omega)
          have hinj2 := hL.2.2.2.getElem_inj_iff (i := L.length) (j := j + 1)
            (hi := by rw [trailVerts_length src tgt L hL_ne]; omega)
            (hj := by rw [trailVerts_length src tgt L hL_ne]; omega)
          rcases hvlast_mem with h | h
          · have := hinj1.mp h; omega
          · have := hinj2.mp h; omega
        set W := L.drop i ++ [(e', b')]
        have hW_ne : W ≠ [] := by simp [W]
        have hdrop_len : (L.drop i).length = L.length - i := List.length_drop
        have hW_len : W.length = L.length - i + 1 := by simp [W, hdrop_len]
        have hW_nodup : (W.map Prod.fst).Nodup := by
          have hsub : (L.drop i).map Prod.fst ⊆ L.map Prod.fst :=
            fun x hx => List.mem_map.mpr (let ⟨p, hp, hpe⟩ := List.mem_map.mp hx; ⟨p, List.mem_of_mem_drop hp, hpe⟩)
          have hnd_drop : ((L.drop i).map Prod.fst).Nodup :=
            (List.Sublist.map Prod.fst (List.drop_sublist i L)).nodup hL_nodup_edges
          have he'_drop : e' ∉ (L.drop i).map Prod.fst := fun h => he'_nmem_L (hsub h)
          dsimp [W]
          rw [List.map_append, List.map_singleton, List.nodup_append]
          refine ⟨hnd_drop, List.nodup_singleton e', ?_⟩
          intro x hx1 y hy hxy
          simp only [List.mem_singleton] at hy
          subst y
          subst x
          exact he'_drop hx1
        have hW_chain : ∀ j : ℕ, (hj : j + 1 < W.length) →
            epEnd src tgt W[j] = epStart src tgt W[j + 1] := by
          intro j hj
          dsimp [W]
          by_cases hj1 : j + 1 < (L.drop i).length
          · rw [List.getElem_append_left (by omega), List.getElem_append_left hj1,
              List.getElem_drop, List.getElem_drop]
            have := hL.2.2.1 (i + j) (by rw [hdrop_len] at hj1; omega)
            simpa [add_assoc] using this
          · have hj_last : j = L.length - i - 1 := by rw [hdrop_len] at hj1; rw [hW_len] at hj; omega
            rw [List.getElem_append_left (by rw [hdrop_len]; omega),
              List.getElem_append_right (by rw [hdrop_len]; omega),
              List.getElem_drop]
            have hidx_last : i + j = L.length - 1 := by omega
            have hidx_zero : j + 1 - (L.drop i).length = 0 := by rw [hdrop_len]; omega
            simp only [hidx_last, hidx_zero, List.getElem_singleton]
            have hgl : L[L.length - 1] = p_last := (List.getLast_eq_getElem hL_ne).symm
            rw [hgl]
            exact hb'_start.symm
        have hW_closed : epEnd src tgt (W.getLast hW_ne) = epStart src tgt (W.head hW_ne) := by
          have hlast : W.getLast hW_ne = (e', b') := by
            simp [W]
          have hhead : W.head hW_ne = L[i] := by
            have hne_drop : L.drop i ≠ [] := by
              rw [← List.length_pos_iff_ne_nil, hdrop_len]; omega
            dsimp [W]
            simp only [List.head_append_of_ne_nil hne_drop, List.head_eq_getElem hne_drop,
              List.getElem_drop, add_zero]
          rw [hlast, hhead]
          have hstart_i := trailVerts_getElem_eq_epStart src tgt C L hL i hi_lt
          rw [← hstart_i]
          exact hi_eq.symm
        let c : E → ℤ := fun e => (W.map fun p => if p.1 = e then stepSign p.2 else 0).sum
        let W_set : Finset E := (W.map Prod.fst).toFinset
        have hW_sub_C : W_set ⊆ C := by
          intro e he
          have he' : e ∈ W.map Prod.fst := List.mem_toFinset.mp he
          obtain ⟨p, hpW, rfl⟩ := List.mem_map.mp he'
          dsimp [W] at hpW
          rw [List.mem_append, List.mem_singleton] at hpW
          rcases hpW with hp | rfl
          · exact hL.2.1 p (List.mem_of_mem_drop hp)
          · exact he'_C
        have he'_in_W : e' ∈ W_set := by
          rw [List.mem_toFinset, List.mem_map]
          exact ⟨(e', b'), by simp [W], rfl⟩
        have hc_on : ∀ e ∈ W_set, |c e| = 1 := by
          intro e he
          have he_map : e ∈ W.map Prod.fst := List.mem_toFinset.mp he
          obtain ⟨⟨e₁, b₁⟩, hpW, heq⟩ := List.mem_map.mp he_map
          dsimp only at heq
          subst heq
          have hsum_single : c e₁ = stepSign b₁ := by
            dsimp [c]
            have hcalc : ∀ (M : List (E × Bool)), (M.map Prod.fst).Nodup →
                (∃ b, (e₁, b) ∈ M) → ∀ b, (e₁, b) ∈ M →
                (M.map fun p => if p.1 = e₁ then stepSign p.2 else 0).sum = stepSign b := by
              intro M
              induction M with
              | nil => intro _ _ b hb; simp at hb
              | cons q qs ihM =>
                intro hnd _ b hb
                rw [List.map_cons, List.nodup_cons] at hnd
                rw [List.map_cons, List.sum_cons]
                rcases List.mem_cons.mp hb with rfl | hb_tail
                · simp only [↓reduceIte]
                  have htail0 : (qs.map fun p => if p.1 = e₁ then stepSign p.2 else 0).sum = 0 := by
                    refine List.sum_eq_zero fun x hx => ?_
                    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
                    split_ifs with hpe
                    · exfalso
                      exact hnd.1 (List.mem_map.mpr ⟨p, hp, hpe⟩)
                    · rfl
                  omega
                · have hne_q : q.1 ≠ e₁ := fun h => hnd.1 (List.mem_map.mpr ⟨(e₁, b), hb_tail, h.symm⟩)
                  rw [if_neg hne_q, zero_add]
                  exact ihM hnd.2 ⟨b, hb_tail⟩ b hb_tail
            exact hcalc W hW_nodup ⟨b₁, hpW⟩ b₁ hpW
          rw [hsum_single]
          cases b₁ <;> simp [stepSign]
        have hc_off : ∀ e ∉ W_set, c e = 0 := by
          intro e he
          dsimp [c]
          refine List.sum_eq_zero fun x hx => ?_
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
          split_ifs with hpe
          · exfalso
            exact he (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, hpe⟩))
          · rfl
        have hc_cons : IsConservative src tgt c :=
          isConservative_closed_chain src tgt W hW_ne hW_chain hW_closed
        have hc_odd : ∀ e, e ∈ W_set ↔ Odd (c e) := by
          intro e
          by_cases he : e ∈ W_set
          · have h1 := hc_on e he
            have ho : Odd (c e) := by
              rcases eq_or_eq_neg_of_abs_eq h1 with hpos | hneg
              · rw [hpos]; exact ⟨0, by ring⟩
              · rw [hneg]; exact ⟨-1, by ring⟩
            exact ⟨fun _ => ho, fun _ => he⟩
          · have h0 := hc_off e he
            rw [h0]
            exact ⟨fun h => absurd h he, fun ho => by obtain ⟨k, hk⟩ := ho; omega⟩
        have hW_even : ∀ v, Even (degIn src tgt W_set v) :=
          even_degIn_of_conservative src tgt c hc_cons W_set hc_odd
        set C' := C \ W_set
        have hC'_lt : C'.card < n := by
          rw [← hn]
          have hsub : C' ⊂ C := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨Finset.sdiff_subset, ?_⟩
            intro heq
            have : e' ∈ C' := heq ▸ he'_C
            exact (Finset.mem_sdiff.mp this).2 he'_in_W
          exact Finset.card_lt_card hsub
        have hC'_even : ∀ v, Even (degIn src tgt C' v) := by
          intro v
          have hpart : ∀ φ : E → V, (C.filter fun e => φ e = v).card =
              (C'.filter fun e => φ e = v).card + (W_set.filter fun e => φ e = v).card := by
            intro φ
            rw [← Finset.card_union_of_disjoint]
            · congr 1
              ext e
              simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, C']
              constructor
              · rintro ⟨heC, hφ⟩
                by_cases heW : e ∈ W_set
                · exact Or.inr ⟨heW, hφ⟩
                · exact Or.inl ⟨⟨heC, heW⟩, hφ⟩
              · rintro (⟨⟨heC, _⟩, hφ⟩ | ⟨heW, hφ⟩)
                · exact ⟨heC, hφ⟩
                · exact ⟨hW_sub_C heW, hφ⟩
            · rw [Finset.disjoint_left]
              intro e he1 he2
              exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he1).1).2 (Finset.mem_filter.mp he2).1
          have hdeg_split : degIn src tgt C v = degIn src tgt C' v + degIn src tgt W_set v := by
            unfold degIn
            rw [hpart src, hpart tgt]
            omega
          have hvC := hC_even v
          have hvW := hW_even v
          rw [hdeg_split] at hvC
          rcases hvC with ⟨a, ha⟩
          rcases hvW with ⟨b, hb⟩
          exact ⟨a - b, by omega⟩
        obtain ⟨g', hg'1, hg'0, hg'_cons⟩ := ih C'.card hC'_lt C' rfl hC'_even
        refine ⟨fun e => c e + g' e, ?_, ?_, ?_⟩
        · intro e he
          dsimp only
          by_cases heW : e ∈ W_set
          · have hg'e : g' e = 0 := hg'0 e (fun h => (Finset.mem_sdiff.mp h).2 heW)
            rw [hg'e, add_zero]
            exact hc_on e heW
          · have hce : c e = 0 := hc_off e heW
            rw [hce, zero_add]
            exact hg'1 e (Finset.mem_sdiff.mpr ⟨he, heW⟩)
        · intro e he
          dsimp only
          have hce : c e = 0 := hc_off e (fun h => he (hW_sub_C h))
          have hg'e : g' e = 0 := hg'0 e (fun h => he (Finset.mem_sdiff.mp h).1)
          rw [hce, hg'e, add_zero]
        · intro v
          dsimp [IsConservative] at hc_cons hg'_cons ⊢
          simp_rw [Finset.sum_add_distrib]
          rw [hc_cons v, hg'_cons v]

private lemma degMod2_symmDiff_singleton {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (B : Finset E) (e : E) (v : V) :
    ((degIn src tgt (symmDiff B {e}) v : ℕ) : ZMod 2) =
      ((degIn src tgt B v : ℕ) : ZMod 2) +
        (if v = src e then 1 else 0) + (if v = tgt e then 1 else 0) := by
  have hpart : ∀ φ : E → V, (((symmDiff B {e}).filter fun d => φ d = v).card : ZMod 2) =
      ((B.filter fun d => φ d = v).card : ZMod 2) + (if v = φ e then 1 else 0) := by
    intro φ
    by_cases hφ : v = φ e
    · rw [if_pos hφ]
      by_cases heB : e ∈ B
      · have hmem : e ∈ B.filter fun d => φ d = v := Finset.mem_filter.mpr ⟨heB, hφ.symm⟩
        have hfilt : (symmDiff B {e}).filter (fun d => φ d = v) =
            (B.filter fun d => φ d = v).erase e := by
          ext d
          simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
          constructor
          · rintro ⟨(⟨hdB, hne⟩ | ⟨rfl, hnB⟩), hdφ⟩
            · exact ⟨hne, hdB, hdφ⟩
            · exact absurd heB hnB
          · rintro ⟨hne, hdB, hdφ⟩
            exact ⟨Or.inl ⟨hdB, hne⟩, hdφ⟩
        rw [hfilt, Finset.card_erase_of_mem hmem]
        have hpos : 0 < (B.filter fun d => φ d = v).card := Finset.card_pos.mpr ⟨e, hmem⟩
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [hk]
        push_cast
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        calc
          (k : ZMod 2) = (k : ZMod 2) + (1 + 1) := by rw [h2, add_zero]
          _ = ((k : ZMod 2) + 1) + 1 := by ring
      · have hnmem : e ∉ B.filter fun d => φ d = v := fun h => heB (Finset.mem_filter.mp h).1
        have hfilt : (symmDiff B {e}).filter (fun d => φ d = v) =
            insert e (B.filter fun d => φ d = v) := by
          ext d
          simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
          constructor
          · rintro ⟨(⟨hdB, _⟩ | ⟨rfl, _⟩), hdφ⟩
            · exact Or.inr ⟨hdB, hdφ⟩
            · exact Or.inl rfl
          · rintro (rfl | ⟨hdB, hdφ⟩)
            · exact ⟨Or.inr ⟨rfl, heB⟩, hφ.symm⟩
            · exact ⟨Or.inl ⟨hdB, fun h => heB (h ▸ hdB)⟩, hdφ⟩
        rw [hfilt, Finset.card_insert_of_notMem hnmem, Nat.cast_add, Nat.cast_one]
    · rw [if_neg hφ, add_zero]
      congr 2
      ext d
      simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton]
      constructor
      · rintro ⟨(⟨hdB, _⟩ | ⟨rfl, _⟩), hdφ⟩
        · exact ⟨hdB, hdφ⟩
        · exact absurd hdφ.symm hφ
      · rintro ⟨hdB, hdφ⟩
        have hde : d ≠ e := fun h => hφ (h ▸ hdφ).symm
        exact ⟨Or.inl ⟨hdB, hde⟩, hdφ⟩
  unfold degIn
  rw [Nat.cast_add, Nat.cast_add, hpart src, hpart tgt]
  ring

private lemma toggle_walk {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (A : Finset E)
    {u w : V} (p : (SimpleGraph.fromRel fun a b => ∃ e ∈ A, src e = a ∧ tgt e = b).Walk u w) :
    ∀ B : Finset E, (∀ d, d ∉ A → d ∈ B) →
      ∃ B' : Finset E, (∀ d, d ∉ A → d ∈ B') ∧
        ∀ v, ((degIn src tgt B' v : ℕ) : ZMod 2) =
          ((degIn src tgt B v : ℕ) : ZMod 2) +
            (if v = u then 1 else 0) + (if v = w then 1 else 0) := by
  induction p with
  | nil =>
    intro B hB
    refine ⟨B, hB, fun v => ?_⟩
    split_ifs
    · have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [add_assoc, h2, add_zero]
    · simp
  | @cons u x w h p' ih =>
    intro B hB
    obtain ⟨_, hrel⟩ := h
    have hex : ∃ e ∈ A, (src e = u ∧ tgt e = x) ∨ (src e = x ∧ tgt e = u) := by
      rcases hrel with ⟨e, he, hs, ht⟩ | ⟨e, he, hs, ht⟩
      · exact ⟨e, he, Or.inl ⟨hs, ht⟩⟩
      · exact ⟨e, he, Or.inr ⟨hs, ht⟩⟩
    obtain ⟨e, heA, hst⟩ := hex
    set B₁ := symmDiff B {e}
    have hB₁ : ∀ d, d ∉ A → d ∈ B₁ := by
      intro d hd
      rw [Finset.mem_symmDiff, Finset.mem_singleton]
      exact Or.inl ⟨hB d hd, fun hde => hd (hde ▸ heA)⟩
    obtain ⟨B', hB', hdeg'⟩ := ih B₁ hB₁
    refine ⟨B', hB', fun v => ?_⟩
    rw [hdeg' v, degMod2_symmDiff_singleton src tgt B e v]
    have hx2 : (if v = x then (1 : ZMod 2) else 0) + (if v = x then (1 : ZMod 2) else 0) = 0 := by
      by_cases hvx : v = x
      · simp only [hvx, ↓reduceIte]
        decide
      · simp [hvx]
    rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · calc
        (((degIn src tgt B v : ℕ) : ZMod 2) + (if v = src e then 1 else 0) + (if v = tgt e then 1 else 0)) +
            (if v = tgt e then 1 else 0) + (if v = w then 1 else 0)
            = ((degIn src tgt B v : ℕ) : ZMod 2) + (if v = src e then 1 else 0) +
                ((if v = tgt e then 1 else 0) + (if v = tgt e then 1 else 0)) + (if v = w then 1 else 0) := by ring
        _ = ((degIn src tgt B v : ℕ) : ZMod 2) + (if v = src e then 1 else 0) + (if v = w then 1 else 0) := by
          rw [hx2, add_zero]
    · calc
        (((degIn src tgt B v : ℕ) : ZMod 2) + (if v = src e then 1 else 0) + (if v = tgt e then 1 else 0)) +
            (if v = src e then 1 else 0) + (if v = w then 1 else 0)
            = ((degIn src tgt B v : ℕ) : ZMod 2) + (if v = tgt e then 1 else 0) +
                ((if v = src e then 1 else 0) + (if v = src e then 1 else 0)) + (if v = w then 1 else 0) := by ring
        _ = ((degIn src tgt B v : ℕ) : ZMod 2) + (if v = tgt e then 1 else 0) + (if v = w then 1 else 0) := by
          rw [hx2, add_zero]

private lemma odd_deg_filter_card_zmod2 {V E : Type*} [DecidableEq V]
    (src tgt : E → V) (B : Finset E) (S : Finset V) :
    (((S.filter fun v => Odd (degIn src tgt B v)).card : ℕ) : ZMod 2) =
      ∑ v ∈ S, ((degIn src tgt B v : ℕ) : ZMod 2) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases ho : Odd (degIn src tgt B v)
  · simp only [ho, ↓reduceIte, Nat.cast_one]
    obtain ⟨k, hk⟩ := ho
    rw [hk]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  · simp only [ho, ↓reduceIte, Nat.cast_zero]
    have hev : Even (degIn src tgt B v) := Nat.not_odd_iff_even.mp ho
    exact ((ZMod.natCast_eq_zero_iff_even).mpr hev).symm

private lemma walk_mem_iff_of_closed {V E : Type*} (src tgt : E → V) (A : Finset E)
    (S : Finset V) (hS : ∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) {u w : V}
    (p : (SimpleGraph.fromRel fun a b => ∃ e ∈ A, src e = a ∧ tgt e = b).Walk u w) :
    u ∈ S ↔ w ∈ S := by
  induction p with
  | nil => exact Iff.rfl
  | @cons u x w h _ ih =>
    obtain ⟨_, hrel⟩ := h
    have hux : u ∈ S ↔ x ∈ S := by
      rcases hrel with ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
      · exact hS e he
      · exact (hS e he).symm
    exact hux.trans ih

private lemma exists_even_cover {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (A : Finset E)
    (hCut : ∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
      Even ((Finset.univ.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card)) :
    ∃ B : Finset E, (∀ e, e ∉ A → e ∈ B) ∧ ∀ v, Even (degIn src tgt B v) := by
  classical
  suffices h : ∀ k : ℕ, ∀ B : Finset E,
      (Finset.univ.filter fun v => Odd (degIn src tgt B v)).card = k →
      (∀ d, d ∉ A → d ∈ B) →
      (∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
        Even ((S.filter fun v => Odd (degIn src tgt B v)).card)) →
      ∃ B' : Finset E, (∀ e, e ∉ A → e ∈ B') ∧ ∀ v, Even (degIn src tgt B' v) by
    set B₀ := Finset.univ \ A
    refine h (Finset.univ.filter fun v => Odd (degIn src tgt B₀ v)).card B₀ rfl ?_ ?_
    · intro d hd
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ d, hd⟩
    · intro S hS
      rw [← ZMod.natCast_eq_zero_iff_even, odd_deg_filter_card_zmod2, ← Nat.cast_sum,
        sum_degIn_zmod2]
      have hfilt : (B₀.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)) =
          Finset.univ.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, B₀]
        constructor
        · rintro ⟨_, hcross⟩; exact hcross
        · intro hcross
          refine ⟨fun heA => ?_, hcross⟩
          have hiff := hS e heA
          by_cases hs : src e ∈ S
          · simp [hs, hiff.mp hs] at hcross
          · simp [hs, mt hiff.mpr hs] at hcross
      rw [hfilt]
      exact (ZMod.natCast_eq_zero_iff_even).mpr (hCut S hS)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro B hk hcov hinv
    set O := Finset.univ.filter fun v => Odd (degIn src tgt B v)
    by_cases hO : O = ∅
    · refine ⟨B, hcov, fun v => Nat.not_odd_iff_even.mp ?_⟩
      intro ho
      have hv : v ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ v, ho⟩
      rw [hO] at hv
      exact Finset.notMem_empty v hv
    · obtain ⟨u, huO⟩ := Finset.nonempty_iff_ne_empty.mpr hO
      let G := SimpleGraph.fromRel fun a b : V => ∃ e ∈ A, src e = a ∧ tgt e = b
      let S := Finset.univ.filter fun w => G.Reachable u w
      have hS_closed : ∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S := by
        intro e heA
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hst : src e = tgt e
        · rw [hst]
        · have hadj : G.Adj (src e) (tgt e) := ⟨hst, Or.inl ⟨e, heA, rfl, rfl⟩⟩
          exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
      have heven_SO := hinv S hS_closed
      have hu_in_SO : u ∈ S.filter fun v => Odd (degIn src tgt B v) := by
        refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp huO).2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, SimpleGraph.Reachable.refl u⟩
      have hcard_ge2 : 2 ≤ (S.filter fun v => Odd (degIn src tgt B v)).card := by
        have hpos : 0 < (S.filter fun v => Odd (degIn src tgt B v)).card :=
          Finset.card_pos.mpr ⟨u, hu_in_SO⟩
        rcases heven_SO with ⟨m, hm⟩
        omega
      have hex_w : ∃ w ∈ S.filter (fun v => Odd (degIn src tgt B v)), w ≠ u := by
        by_contra hnone
        push Not at hnone
        have hsub : S.filter (fun v => Odd (degIn src tgt B v)) ⊆ {u} := by
          intro v hv
          exact Finset.mem_singleton.mpr (hnone v hv)
        have hle := Finset.card_le_card hsub
        simp at hle
        omega
      obtain ⟨w, hw_in_SO, hwu⟩ := hex_w
      have hwS : w ∈ S := (Finset.mem_filter.mp hw_in_SO).1
      have hw_odd : Odd (degIn src tgt B w) := (Finset.mem_filter.mp hw_in_SO).2
      have hw_reach : G.Reachable u w := (Finset.mem_filter.mp hwS).2
      obtain ⟨p⟩ := hw_reach
      obtain ⟨B₁, hcov₁, hdeg₁⟩ := toggle_walk src tgt A p B hcov
      set O₁ := Finset.univ.filter fun v => Odd (degIn src tgt B₁ v)
      have hO₁_eq : O₁ = (O.erase u).erase w := by
        ext v
        have hodd_iff : ∀ d : ℕ, Odd d ↔ (d : ZMod 2) = 1 := by
          intro d
          constructor
          · intro ho
            obtain ⟨m, rfl⟩ := ho
            push_cast
            have h2 : (2 : ZMod 2) = 0 := by decide
            rw [h2, zero_mul, zero_add]
          · intro hz
            rw [← not_not (a := Odd d), Nat.not_odd_iff_even, ← ZMod.natCast_eq_zero_iff_even]
            rw [hz]
            decide
        simp only [O₁, O, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hodd_iff]
        rw [hdeg₁ v]
        by_cases hvu : v = u <;> by_cases hvw : v = w
        · exfalso; exact hwu (hvw.symm.trans hvu)
        · have hu1 : ((degIn src tgt B u : ℕ) : ZMod 2) = 1 :=
            (hodd_iff _).mp (Finset.mem_filter.mp huO).2
          subst hvu
          simp [hvw, hu1]
        · have hw1 : ((degIn src tgt B w : ℕ) : ZMod 2) = 1 := (hodd_iff _).mp hw_odd
          subst hvw
          simp [hvu, hw1]
        · simp [hvu, hvw]
      have hO₁_lt : O₁.card < k := by
        rw [hO₁_eq, ← hk]
        have hw_in_erase : w ∈ O.erase u :=
          Finset.mem_erase.mpr ⟨hwu, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw_odd⟩⟩
        rw [Finset.card_erase_of_mem hw_in_erase, Finset.card_erase_of_mem huO]
        have hpos : 2 ≤ O.card :=
          Finset.one_lt_card.mpr ⟨u, huO, w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw_odd⟩, hwu.symm⟩
        omega
      have hinv₁ : ∀ S' : Finset V, (∀ e ∈ A, src e ∈ S' ↔ tgt e ∈ S') →
          Even ((S'.filter fun v => Odd (degIn src tgt B₁ v)).card) := by
        intro S' hS'
        rw [← ZMod.natCast_eq_zero_iff_even, odd_deg_filter_card_zmod2]
        simp_rw [hdeg₁, add_assoc, Finset.sum_add_distrib]
        have hzeroB : ∑ v ∈ S', ((degIn src tgt B v : ℕ) : ZMod 2) = 0 := by
          rw [← odd_deg_filter_card_zmod2, ZMod.natCast_eq_zero_iff_even]
          exact hinv S' hS'
        have huw_eq : (if u ∈ S' then (1 : ZMod 2) else 0) + (if w ∈ S' then 1 else 0) = 0 := by
          have hiff := walk_mem_iff_of_closed src tgt A S' hS' p
          by_cases huS' : u ∈ S' <;> simp [huS', hiff.mp]
          · decide
          · simp [mt hiff.mpr huS']
        have hsum_single : ∀ x : V, ∑ v ∈ S', (if v = x then (1 : ZMod 2) else 0) =
            if x ∈ S' then 1 else 0 := by
          intro x
          by_cases hx : x ∈ S'
          · rw [if_pos hx, Finset.sum_eq_single x]
            · simp
            · intro v _ hvx; rw [if_neg hvx]
            · intro h; exact absurd hx h
          · rw [if_neg hx]
            refine Finset.sum_eq_zero fun v hv => ?_
            have hvx : v ≠ x := fun h => hx (h ▸ hv)
            exact if_neg hvx
        rw [hzeroB, zero_add, hsum_single u, hsum_single w, huw_eq]
      exact ih O₁.card hO₁_lt B₁ rfl hcov₁ hinv₁

private theorem hasNZ4Flow_iff_cutParity
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V) :
    HasNZ4Flow src tgt ↔
      ∃ A : Finset E, (∀ v, Even (degIn src tgt A v)) ∧
        ∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
          Even ((Finset.univ.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card) := by
  classical
  constructor
  · rintro ⟨f, hf_bnd, hf_cons⟩
    set A := Finset.univ.filter fun e => Odd (f e)
    have hA_even : ∀ v, Even (degIn src tgt A v) :=
      even_degIn_of_conservative src tgt f hf_cons A (fun e => by simp [A])
    obtain ⟨g, hg_on, hg_off, hg_cons⟩ := exists_unit_circulation src tgt A hA_even
    have heven_diff : ∀ e : E, 2 ∣ f e - g e := by
      intro e
      by_cases he : e ∈ A
      · have hfo : Odd (f e) := (Finset.mem_filter.mp he).2
        have hgo : Odd (g e) := by
          rcases eq_or_eq_neg_of_abs_eq (hg_on e he) with h | h <;> rw [h]
          · exact ⟨0, by ring⟩
          · exact ⟨-1, by ring⟩
        obtain ⟨a, ha⟩ := hfo
        obtain ⟨b, hb⟩ := hgo
        exact ⟨a - b, by omega⟩
      · have hfe : Even (f e) := Int.not_odd_iff_even.mp fun h => he (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩)
        have hge : g e = 0 := hg_off e he
        obtain ⟨a, ha⟩ := hfe
        exact ⟨a, by omega⟩
    let h : E → ℤ := fun e => (f e - g e) / 2
    have hh2 : ∀ e, 2 * h e = f e - g e := fun e => Int.mul_ediv_cancel' (heven_diff e)
    have hh_cons : IsConservative src tgt h := by
      intro v
      have h2eq : 2 * ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), h e =
          2 * ∑ e ∈ Finset.univ.filter (fun e => src e = v), h e := by
        rw [Finset.mul_sum, Finset.mul_sum]
        simp_rw [hh2, Finset.sum_sub_distrib]
        rw [hf_cons v, hg_cons v]
      omega
    set B := Finset.univ.filter fun e => Odd (h e)
    have hB_even : ∀ v, Even (degIn src tgt B v) :=
      even_degIn_of_conservative src tgt h hh_cons B (fun e => by simp [B])
    have hcov_B : ∀ e, e ∉ A → e ∈ B := by
      intro e heA
      have hne_odd : ¬ Odd (f e) := fun h => heA (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩)
      have hge0 : g e = 0 := hg_off e heA
      obtain ⟨hb1, hb2⟩ := hf_bnd e
      have hf2 : f e = 2 ∨ f e = -2 := by
        have hev : Even (f e) := Int.not_odd_iff_even.mp hne_odd
        obtain ⟨a, ha⟩ := hev
        rw [ha] at hb1 hb2 ⊢
        rcases le_or_gt 0 a with ha0 | ha0
        · rw [abs_of_nonneg (by omega : 0 ≤ a + a)] at hb1 hb2
          omega
        · rw [abs_of_neg (by omega : a + a < 0)] at hb1 hb2
          omega
      have hh1 : h e = 1 ∨ h e = -1 := by
        have := hh2 e
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_⟩
      rcases hh1 with hh | hh <;> rw [hh]
      · exact ⟨0, by ring⟩
      · exact ⟨-1, by ring⟩
    refine ⟨A, hA_even, fun S hS => ?_⟩
    have hfilt : (Finset.univ.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)) =
        B.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hcross
        refine ⟨hcov_B e (fun heA => ?_), hcross⟩
        have hiff := hS e heA
        by_cases hs : src e ∈ S
        · simp [hs, hiff.mp hs] at hcross
        · simp [hs, mt hiff.mpr hs] at hcross
      · rintro ⟨_, hcross⟩
        exact hcross
    rw [hfilt, ← ZMod.natCast_eq_zero_iff_even, ← sum_degIn_zmod2]
    rw [Nat.cast_sum, ← odd_deg_filter_card_zmod2, ZMod.natCast_eq_zero_iff_even]
    have hzero : S.filter (fun v => Odd (degIn src tgt B v)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v _
      exact Nat.not_odd_iff_even.mpr (hB_even v)
    rw [hzero]
    simp
  · rintro ⟨A, hA_even, hCut⟩
    obtain ⟨B, hB_cov, hB_even⟩ := exists_even_cover src tgt A hCut
    obtain ⟨gA, hgA_on, hgA_off, hgA_cons⟩ := exists_unit_circulation src tgt A hA_even
    obtain ⟨gB, hgB_on, hgB_off, hgB_cons⟩ := exists_unit_circulation src tgt B hB_even
    refine ⟨fun e => gA e + 2 * gB e, ?_, ?_⟩
    · intro e
      by_cases heA : e ∈ A <;> by_cases heB : e ∈ B
      · rcases eq_or_eq_neg_of_abs_eq (hgA_on e heA) with ha | ha <;>
          rcases eq_or_eq_neg_of_abs_eq (hgB_on e heB) with hb | hb <;>
          simp [ha, hb]
      · rcases eq_or_eq_neg_of_abs_eq (hgA_on e heA) with ha | ha <;>
          simp [ha, hgB_off e heB]
      · rcases eq_or_eq_neg_of_abs_eq (hgB_on e heB) with hb | hb <;>
          simp [hgA_off e heA, hb]
      · exact absurd (hB_cov e heA) heB
    · intro v
      dsimp [IsConservative] at hgA_cons hgB_cons ⊢
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hgA_cons v, hgB_cons v]

theorem OMA.solution : OMA.R_opg_black_and_white_cycle_conjecture_R1.H1 := by
  intro V E _ _ _ _ src tgt hole
  cases hole with
  | none =>
    dsimp only
    rw [hasNZ4Flow_iff_cutParity src tgt]
    constructor
    · rintro ⟨A, hA, hCut⟩
      exact ⟨A, Finset.subset_univ A, hA, hCut⟩
    · rintro ⟨A, _, hA, hCut⟩
      exact ⟨A, hA, hCut⟩
  | some e₀ =>
    classical
    dsimp only [IsWhite]
    let E' := {d : E // d ≠ e₀}
    let src' : E' → V := fun d => src d.1
    let tgt' : E' → V := fun d => tgt d.1
    rw [hasNZ4Flow_iff_cutParity src' tgt']
    have hdeg_map : ∀ (A' : Finset E') (v : V),
        degIn src tgt (A'.map ⟨Subtype.val, Subtype.val_injective⟩) v = degIn src' tgt' A' v := by
      intro A' v
      have hpart : ∀ (φ : E → V) (φ' : E' → V), (∀ d : E', φ d.1 = φ' d) →
          ((A'.map ⟨Subtype.val, Subtype.val_injective⟩).filter fun e => φ e = v).card =
            (A'.filter fun d => φ' d = v).card := by
        intro φ φ' hφ
        rw [Finset.filter_map, Finset.card_map]
        congr 1
        ext d
        simp [Function.comp_apply, hφ d]
      unfold degIn
      rw [hpart src src' (fun _ => rfl), hpart tgt tgt' (fun _ => rfl)]
    have hcut_eq : ∀ S : Finset V,
        ((Finset.univ.erase e₀).filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card =
          (Finset.univ.filter fun d : E' => decide (src' d ∈ S) != decide (tgt' d ∈ S)).card := by
      intro S
      refine Finset.card_bij (fun e _ => ⟨e, ?_⟩) ?_ ?_ ?_
      · exact (Finset.mem_erase.mp (Finset.mem_filter.mp ‹_›).1).1
      · intro e he
        have he' := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'.2⟩
      · intro e₁ _ e₂ _ heq
        simpa using congrArg Subtype.val heq
      · intro d hd
        refine ⟨d.1, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨d.2, Finset.mem_univ _⟩,
          (Finset.mem_filter.mp hd).2⟩, rfl⟩
    constructor
    · rintro ⟨A', hA', hCut'⟩
      set A := A'.map ⟨Subtype.val, Subtype.val_injective⟩
      refine ⟨A, ?_, fun v => (hdeg_map A' v).symm ▸ hA' v, fun S hS => ?_⟩
      · intro e he
        obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp he
        exact Finset.mem_erase.mpr ⟨d.2, Finset.mem_univ _⟩
      · rw [hcut_eq S]
        refine hCut' S fun d hd => hS d.1 ?_
        exact Finset.mem_map.mpr ⟨d, hd, rfl⟩
    · rintro ⟨A, hA_sub, hA_even, hCut⟩
      set A' : Finset E' := Finset.univ.filter fun d => d.1 ∈ A
      have hA_map : A'.map ⟨Subtype.val, Subtype.val_injective⟩ = A := by
        ext e
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk, A']
        constructor
        · rintro ⟨d, hd, rfl⟩; exact hd
        · intro heA
          have hne : e ≠ e₀ := (Finset.mem_erase.mp (hA_sub heA)).1
          exact ⟨⟨e, hne⟩, heA, rfl⟩
      refine ⟨A', fun v => ?_, fun S hS' => ?_⟩
      · rw [← hdeg_map A' v, hA_map]
        exact hA_even v
      · rw [← hcut_eq S]
        refine hCut S fun e he => ?_
        have hne : e ≠ e₀ := (Finset.mem_erase.mp (hA_sub he)).1
        exact hS' ⟨e, hne⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
