import OMAReductions.R_opg_forcing_a_2_regular_minor_R1
import Mathlib

/-!
Proof of `opg-forcing-a-2-regular-minor.R1.H1` (Erdos-Gallai theorem on longest cycles, 1959):
Every nonempty finite simple graph `G` on `n` vertices with `k >= 3` and
`(k - 1) * n <= 2 * |E(G)|` contains a cycle of length at least `k`.

We prove the sharper bound `(k - 1) * (n - 1) < 2 * |E(G)|` by strong induction on `n`:
1. Vertices of degree `<= (k - 1) / 2` are deleted by induction.
2. Disconnected graphs and graphs with a cut-vertex split while preserving the edge-density
   hypothesis on at least one side.
3. For a 2-connected graph `G` with `n >= k` and `2 * delta(G) >= k`, we prove Kopylov/Dirac's
   longest-path cycle bound: taking a longest simple path `P = v_0 ... v_L`, `G` contains a cycle
   of length at least `min n (deg v_0 + deg v_L) >= k`, via:
   - a Hamiltonian cycle when `N(v_0)` and `N(v_L)` have an adjacent crossing (`A ∩ B ≠ ∅`),
   - a minimal-gap crossing cycle when `b < a`, and
   - a minimal covering vine of internally-`P`-disjoint bridges stitched into two vertex-disjoint
     paths closed by degree-preserving detours at both ends when `a <= b`.
-/

namespace OMAP2RegH1

open SimpleGraph Finset

/- ### Section 1: List helpers, slices, simple paths, and cycles -/

private def slice {V : Type*} (l : List V) (a b : ℕ) : List V :=
  (l.drop a).take (b - a)

private lemma slice_length {V : Type*} (l : List V) (a b : ℕ) :
    (slice l a b).length = min (b - a) (l.length - a) := by
  simp [slice]

private lemma slice_length_of_le {V : Type*} {l : List V} {a b : ℕ} (hb : b ≤ l.length) :
    (slice l a b).length = b - a := by
  rw [slice_length]; omega

private lemma slice_getElem {V : Type*} {l : List V} {a b i : ℕ}
    (hi : i < (slice l a b).length) :
    (slice l a b)[i]'hi = l[a + i]'(by rw [slice_length] at hi; omega) := by
  simp [slice]

private lemma slice_sublist {V : Type*} (l : List V) (a b : ℕ) :
    List.Sublist (slice l a b) l :=
  (List.take_sublist _ _).trans (List.drop_sublist _ _)

private lemma nodup_getElem_eq {V : Type*} {l : List V} (hnd : l.Nodup)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (h : l[i] = l[j]) : i = j :=
  congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h)

private lemma getLast_tail_eq {V : Type*} {l : List V} (hl : l ≠ []) (ht : l.tail ≠ []) :
    l.tail.getLast ht = l.getLast hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => exact (List.getLast_cons ht).symm

private lemma getLast_append_tail_eq {V : Type*} {l₁ l₂ : List V}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h12 : l₁ ++ l₂.tail ≠ [])
    (hmatch : l₁.getLast h₁ = l₂.head h₂) :
    (l₁ ++ l₂.tail).getLast h12 = l₂.getLast h₂ := by
  cases l₂ with
  | nil => exact absurd rfl h₂
  | cons a t =>
    cases t with
    | nil => simpa using hmatch
    | cons b t' => simp [List.getLast_append_of_ne_nil]

private lemma head_not_mem_tail {V : Type*} {l : List V} (hl : l ≠ []) (hnd : l.Nodup) :
    l.head hl ∉ l.tail := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => exact (List.nodup_cons.mp hnd).1

private lemma getElem_mem_eraseIdx {α : Type*} (l : List α) (idx j : ℕ)
    (hidx : idx < l.length) (hj : j < l.length) (hne : j ≠ idx) :
    l[j] ∈ l.eraseIdx idx := by
  by_cases hlt : j < idx
  · have h1 : j < (l.eraseIdx idx).length := by rw [List.length_eraseIdx_of_lt hidx]; omega
    have : (l.eraseIdx idx)[j]'h1 = l[j] := List.getElem_eraseIdx_of_lt h1 hlt
    rw [← this]; exact List.getElem_mem h1
  · have h1 : j - 1 < (l.eraseIdx idx).length := by rw [List.length_eraseIdx_of_lt hidx]; omega
    have : (l.eraseIdx idx)[j - 1]'h1 = l[j] := by
      rw [List.getElem_eraseIdx_of_ge h1 (by omega)]; congr 1; omega
    rw [← this]; exact List.getElem_mem h1

private def IsAdjList {V : Type*} (G : SimpleGraph V) (l : List V) : Prop :=
  ∀ i (hi : i + 1 < l.length), G.Adj l[i] l[i + 1]

private lemma isAdjList_nil {V : Type*} (G : SimpleGraph V) : IsAdjList G [] := by
  intro i hi; simp at hi

private lemma isAdjList_singleton {V : Type*} (G : SimpleGraph V) (a : V) :
    IsAdjList G [a] := by
  intro i hi; simp at hi

private lemma isAdjList_cons {V : Type*} {G : SimpleGraph V} {a : V} {l : List V}
    (hl : IsAdjList G l) (ha : ∀ h : l ≠ [], G.Adj a (l.head h)) :
    IsAdjList G (a :: l) := by
  intro i hi
  cases i with
  | zero =>
    cases l with
    | nil => simp at hi
    | cons b t => exact ha (by simp)
  | succ i =>
    exact hl i (by simpa using hi)

private lemma isAdjList_tail {V : Type*} {G : SimpleGraph V} {l : List V}
    (hl : IsAdjList G l) : IsAdjList G l.tail := by
  cases l with
  | nil => exact isAdjList_nil G
  | cons a t =>
    intro i hi
    exact hl (i + 1) (by simpa using hi)

private lemma isAdjList_reverse {V : Type*} {G : SimpleGraph V} {l : List V}
    (hl : IsAdjList G l) : IsAdjList G l.reverse := by
  intro i hi
  rw [List.length_reverse] at hi
  rw [List.getElem_reverse, List.getElem_reverse]
  have hlt : l.length - 1 - (i + 1) + 1 < l.length := by omega
  have hadj := hl (l.length - 1 - (i + 1)) hlt
  have heq : l[l.length - 1 - (i + 1) + 1] = l[l.length - 1 - i] := by congr 1; omega
  rw [heq] at hadj
  exact hadj.symm

private lemma isAdjList_take {V : Type*} {G : SimpleGraph V} {l : List V}
    (hl : IsAdjList G l) (n : ℕ) : IsAdjList G (l.take n) := by
  intro i hi
  have hi' : i + 1 < l.length := lt_of_lt_of_le hi (by simp)
  rw [List.getElem_take, List.getElem_take]
  exact hl i hi'

private lemma isAdjList_drop {V : Type*} {G : SimpleGraph V} {l : List V}
    (hl : IsAdjList G l) (n : ℕ) : IsAdjList G (l.drop n) := by
  intro i hi
  have hi' : n + i + 1 < l.length := by simp at hi; omega
  rw [List.getElem_drop, List.getElem_drop]
  have heq : n + (i + 1) = n + i + 1 := by omega
  simpa [heq] using hl (n + i) hi'

private lemma isAdjList_slice {V : Type*} {G : SimpleGraph V} {l : List V}
    (hl : IsAdjList G l) (a b : ℕ) : IsAdjList G (slice l a b) :=
  isAdjList_take (isAdjList_drop hl a) (b - a)

private lemma isAdjList_append {V : Type*} {G : SimpleGraph V} {l₁ l₂ : List V}
    (h₁ : IsAdjList G l₁) (h₂ : IsAdjList G l₂)
    (hjoin : ∀ (hne₁ : l₁ ≠ []) (hne₂ : l₂ ≠ []), G.Adj (l₁.getLast hne₁) (l₂.head hne₂)) :
    IsAdjList G (l₁ ++ l₂) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hlt : i + 1 < l₁.length
  · rw [List.getElem_append_left (by omega), List.getElem_append_left hlt]
    exact h₁ i hlt
  · by_cases heq : i + 1 = l₁.length
    · have hne₁ : l₁ ≠ [] := by intro h; subst h; simp at heq
      have hne₂ : l₂ ≠ [] := by intro h; subst h; simp at hi; omega
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      have h1 : l₁[i] = l₁.getLast hne₁ := by
        rw [List.getLast_eq_getElem]; congr 1; omega
      have h2 : l₂[i + 1 - l₁.length] = l₂.head hne₂ := by
        rw [List.head_eq_getElem_zero]; congr 1; omega
      rw [h1, h2]
      exact hjoin hne₁ hne₂
    · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      have hidx : i + 1 - l₁.length = (i - l₁.length) + 1 := by omega
      have hlt2 : (i - l₁.length) + 1 < l₂.length := by omega
      simpa [hidx] using h₂ (i - l₁.length) hlt2

private lemma isAdjList_append_tail {V : Type*} {G : SimpleGraph V} {l₁ l₂ : List V}
    (h₁ : IsAdjList G l₁) (h₂ : IsAdjList G l₂)
    (hne₁ : l₁ ≠ []) (hne₂ : l₂ ≠ [])
    (hmatch : l₁.getLast hne₁ = l₂.head hne₂) :
    IsAdjList G (l₁ ++ l₂.tail) := by
  cases l₂ with
  | nil => exact absurd rfl hne₂
  | cons b t =>
    simp only [List.tail_cons]
    refine isAdjList_append h₁ (isAdjList_tail h₂) ?_
    intro _ ht
    cases t with
    | nil => exact absurd rfl ht
    | cons c t' =>
      simp only [List.head_cons] at hmatch ⊢
      rw [hmatch]
      exact h₂ 0 (by simp)

private lemma isAdjList_rotate {V : Type*} {G : SimpleGraph V} {l : List V}
    (hl : IsAdjList G l) (hne : l ≠ [])
    (hclose : G.Adj (l.getLast hne) (l.head hne)) (k : ℕ) :
    IsAdjList G (l.rotate k) := by
  have hstep : ∀ (m : List V) (hm : m ≠ []), IsAdjList G m →
      G.Adj (m.getLast hm) (m.head hm) →
      IsAdjList G (m.rotate 1) ∧
      ∀ h' : m.rotate 1 ≠ [], G.Adj ((m.rotate 1).getLast h') ((m.rotate 1).head h') := by
    intro m hm hadj hc
    cases m with
    | nil => exact absurd rfl hm
    | cons a t =>
      cases t with
      | nil =>
        simp only [List.rotate_singleton]
        exact ⟨isAdjList_singleton G a, fun _ => hc⟩
      | cons b t' =>
        have hrot : (a :: b :: t').rotate 1 = (b :: t') ++ [a] := by
          simp [List.rotate_cons_succ]
        rw [hrot]
        refine ⟨?_, ?_⟩
        · refine isAdjList_append (isAdjList_tail hadj) (isAdjList_singleton G a) ?_
          intro _ _
          simpa using hc
        · intro _
          rw [List.getLast_append_singleton, List.head_append_of_ne_nil (by simp), List.head_cons]
          exact hadj 0 (by simp)
  have hcl : ∀ n, IsAdjList G (l.rotate n) ∧
      ∀ h' : l.rotate n ≠ [], G.Adj ((l.rotate n).getLast h') ((l.rotate n).head h') := by
    intro n
    induction n with
    | zero => simpa using ⟨hl, fun _ => hclose⟩
    | succ n ihn =>
      rw [← List.rotate_rotate]
      have hne_n : l.rotate n ≠ [] := by simpa using hne
      exact hstep (l.rotate n) hne_n ihn.1 (ihn.2 hne_n)
  exact (hcl k).1

private def listLast {V : Type*} : V → List V → V
  | a, [] => a
  | _, b :: t => listLast b t

private lemma listLast_eq_getLast {V : Type*} :
    ∀ (a : V) (t : List V), listLast a t = (a :: t).getLast (by simp)
  | _, [] => rfl
  | _, b :: t => by simp [listLast, listLast_eq_getLast b t]

private def walkOfAdjListAux {V : Type*} (G : SimpleGraph V) :
    ∀ (a : V) (t : List V), IsAdjList G (a :: t) → G.Walk a (listLast a t)
  | _, [], _ => Walk.nil
  | a, b :: t, hadj =>
    Walk.cons (show G.Adj a b from hadj 0 (by simp))
      (walkOfAdjListAux G b t (isAdjList_tail hadj))

private lemma walkOfAdjListAux_support {V : Type*} (G : SimpleGraph V) :
    ∀ (a : V) (t : List V) (hadj : IsAdjList G (a :: t)),
      (walkOfAdjListAux G a t hadj).support = a :: t
  | _, [], _ => rfl
  | a, b :: t, hadj => by
    change a :: (walkOfAdjListAux G b t (isAdjList_tail hadj)).support = a :: b :: t
    rw [walkOfAdjListAux_support G b t (isAdjList_tail hadj)]

private def walkOfAdjList {V : Type*} (G : SimpleGraph V) :
    ∀ (l : List V) (hl : l ≠ []), IsAdjList G l → G.Walk (l.head hl) (l.getLast hl)
  | [], hl, _ => absurd rfl hl
  | a :: t, _, hadj => (walkOfAdjListAux G a t hadj).copy rfl (listLast_eq_getLast a t)

private lemma walkOfAdjList_support {V : Type*} (G : SimpleGraph V) :
    ∀ (l : List V) (hl : l ≠ []) (hadj : IsAdjList G l),
      (walkOfAdjList G l hl hadj).support = l
  | [], hl, _ => absurd rfl hl
  | a :: t, _, hadj =>
    (Walk.support_copy (walkOfAdjListAux G a t hadj) rfl (listLast_eq_getLast a t)).trans
      (walkOfAdjListAux_support G a t hadj)

private lemma walkOfAdjList_length {V : Type*} (G : SimpleGraph V)
    (l : List V) (hl : l ≠ []) (hadj : IsAdjList G l) :
    (walkOfAdjList G l hl hadj).length = l.length - 1 := by
  have h := Walk.length_support (walkOfAdjList G l hl hadj)
  rw [walkOfAdjList_support] at h
  omega

private lemma isAdjList_support {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) : IsAdjList G w.support := by
  induction w with
  | nil => exact isAdjList_singleton G _
  | @cons a b c hadj p ih =>
    rw [Walk.support_cons]
    refine isAdjList_cons ih ?_
    intro _
    rw [Walk.head_support]
    exact hadj

private lemma exists_cycle_of_adjList {V : Type*} {G : SimpleGraph V} (l : List V)
    (hlen : 3 ≤ l.length) (hnodup : l.Nodup) (hadj : IsAdjList G l)
    (hclose : ∀ h : l ≠ [], G.Adj (l.getLast h) (l.head h)) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = l.length := by
  have hl : l ≠ [] := List.ne_nil_of_length_pos (by omega)
  let w : G.Walk (l.head hl) (l.getLast hl) := walkOfAdjList G l hl hadj
  let c : G.Walk (l.getLast hl) (l.getLast hl) := Walk.cons (hclose hl) w
  refine ⟨l.getLast hl, c, ?_, ?_⟩
  · rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, ?_⟩
    · have hwpath : w.IsPath := by
        rw [Walk.isPath_def, walkOfAdjList_support]; exact hnodup
      simpa [c] using hwpath
    · simp only [c, Walk.length_cons, w, walkOfAdjList_length]
      omega
  · simp only [c, Walk.length_cons, w, walkOfAdjList_length]
    omega

private lemma nodup_shorten {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (l : List V) (hl : l ≠ []) (hadj : IsAdjList G l) :
    ∃ l' : List V, ∃ hl' : l' ≠ [],
      l'.Nodup ∧ IsAdjList G l' ∧
      l'.head hl' = l.head hl ∧
      l'.getLast hl' = l.getLast hl ∧
      ∀ x ∈ l', x ∈ l := by
  let w := (walkOfAdjList G l hl hadj).bypass
  refine ⟨w.support, Walk.support_ne_nil w, ?_, isAdjList_support w, ?_, ?_, ?_⟩
  · exact (Walk.bypass_isPath _).support_nodup
  · exact Walk.head_support w
  · exact Walk.getLast_support w
  · intro x hx
    have hsub := Walk.support_bypass_subset_support (walkOfAdjList G l hl hadj) hx
    rwa [walkOfAdjList_support] at hsub

private lemma glue4_cycle {V : Type*} {G : SimpleGraph V}
    (W1 W2 W3 W4 : List V)
    (h1 : W1 ≠ []) (h2 : W2 ≠ []) (h3 : W3 ≠ []) (h4 : W4 ≠ [])
    (nd1 : W1.Nodup) (nd2 : W2.Nodup) (nd3 : W3.Nodup) (nd4 : W4.Nodup)
    (adj1 : IsAdjList G W1) (adj2 : IsAdjList G W2)
    (adj3 : IsAdjList G W3) (adj4 : IsAdjList G W4)
    (j12 : W1.getLast h1 = W2.head h2)
    (j23 : W2.getLast h2 = W3.head h3)
    (j34 : W3.getLast h3 = W4.head h4)
    (j41 : W4.getLast h4 = W1.head h1)
    (d12 : ∀ x ∈ W1, x ∈ W2.tail → False)
    (d123 : ∀ x ∈ W1 ++ W2.tail, x ∈ W3.tail → False)
    (d1234 : ∀ x ∈ (W1 ++ W2.tail) ++ W3.tail, x ∈ W4.tail.dropLast → False)
    (hlen3 : 3 ≤ (W1 ++ W2.tail ++ W3.tail ++ W4.tail.dropLast).length) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧
      c.length = (W1 ++ W2.tail ++ W3.tail ++ W4.tail.dropLast).length := by
  let C := W1 ++ W2.tail ++ W3.tail ++ W4.tail.dropLast
  have hnd12 : (W1 ++ W2.tail).Nodup := by
    rw [List.nodup_append]; exact ⟨nd1, nd2.tail, fun x hx y hy hxy => d12 x hx (hxy ▸ hy)⟩
  have hnd123 : (W1 ++ W2.tail ++ W3.tail).Nodup := by
    rw [List.nodup_append]; exact ⟨hnd12, nd3.tail, fun x hx y hy hxy => d123 x hx (hxy ▸ hy)⟩
  have hndC : C.Nodup := by
    rw [List.nodup_append]
    exact ⟨hnd123, nd4.tail.sublist (List.dropLast_sublist _),
      fun x hx y hy hxy => d1234 x hx (hxy ▸ hy)⟩
  have hadj12 : IsAdjList G (W1 ++ W2.tail) := isAdjList_append_tail adj1 adj2 h1 h2 j12
  have hne12 : W1 ++ W2.tail ≠ [] := List.append_ne_nil_of_left_ne_nil h1 _
  have hgl12 : (W1 ++ W2.tail).getLast hne12 = W2.getLast h2 :=
    getLast_append_tail_eq h1 h2 hne12 j12
  have hadj123 : IsAdjList G (W1 ++ W2.tail ++ W3.tail) :=
    isAdjList_append_tail hadj12 adj3 hne12 h3 (hgl12.trans j23)
  have hne123 : W1 ++ W2.tail ++ W3.tail ≠ [] := List.append_ne_nil_of_left_ne_nil hne12 _
  have hgl123 : (W1 ++ W2.tail ++ W3.tail).getLast hne123 = W3.getLast h3 :=
    getLast_append_tail_eq hne12 h3 hne123 (hgl12.trans j23)
  have hW4_cases : IsAdjList G C ∧ ∀ hC : C ≠ [], G.Adj (C.getLast hC) (C.head hC) := by
    cases hW4 : W4 with
    | nil => exact absurd hW4 h4
    | cons a t =>
      cases t with
      | nil =>
        exfalso
        have ha1 : W3.getLast h3 = W1.head h1 := by
          simp [hW4] at j34 j41; exact j34.trans j41
        have hhd_eq : (W1 ++ W2.tail ++ W3.tail).head hne123 = W1.head h1 := by
          rw [List.head_append_of_ne_nil hne12, List.head_append_of_ne_nil h1]
        have hgl_eq : (W1 ++ W2.tail ++ W3.tail).getLast hne123 = W1.head h1 :=
          hgl123.trans ha1
        have hlen123 : 2 ≤ (W1 ++ W2.tail ++ W3.tail).length := by
          have : (W1 ++ W2.tail ++ W3.tail ++ W4.tail.dropLast).length =
              (W1 ++ W2.tail ++ W3.tail).length := by simp [hW4]
          omega
        have h0 : (W1 ++ W2.tail ++ W3.tail)[0]'(by omega) =
            (W1 ++ W2.tail ++ W3.tail)[(W1 ++ W2.tail ++ W3.tail).length - 1]'(by omega) := by
          rw [← List.head_eq_getElem_zero hne123, ← List.getLast_eq_getElem hne123, hhd_eq, hgl_eq]
        have := nodup_getElem_eq hnd123 (by omega) (by omega) h0
        omega
      | cons b t' =>
        cases t' with
        | nil =>
          have hCeq : C = W1 ++ W2.tail ++ W3.tail := by simp [C, hW4]
          rw [hCeq]
          refine ⟨hadj123, fun _ => ?_⟩
          rw [hgl123, List.head_append_of_ne_nil hne12, List.head_append_of_ne_nil h1]
          have ha : W3.getLast h3 = a := by simpa [hW4] using j34
          have hb : b = W1.head h1 := by simpa [hW4] using j41
          rw [ha, ← hb]
          have := adj4; rw [hW4] at this; exact this 0 (by simp)
        | cons c t'' =>
          have hdrop_ne : (b :: c :: t'').dropLast ≠ [] := by simp
          have hW4_adj' : IsAdjList G (a :: b :: c :: t'') := by rwa [← hW4]
          have hW4_drop : IsAdjList G ((a :: b :: c :: t'').dropLast) := by
            rw [List.dropLast_eq_take]; exact isAdjList_take hW4_adj' _
          have hCeq : C = (W1 ++ W2.tail ++ W3.tail) ++ (a :: b :: c :: t'').dropLast.tail := by
            simp [C, hW4]
          have hadjC : IsAdjList G C := by
            rw [hCeq]
            refine isAdjList_append_tail hadj123 hW4_drop hne123 (by simp) ?_
            rw [hgl123]
            simpa [hW4] using j34
          refine ⟨hadjC, fun hC => ?_⟩
          have hheadC : C.head hC = W1.head h1 := by
            simp only [C, List.append_assoc]
            rw [List.head_append_of_ne_nil h1]
          have hlastC : C.getLast hC = (b :: c :: t'').dropLast.getLast hdrop_ne := by
            simp only [C, hW4, List.tail_cons]
            rw [List.getLast_append_of_ne_nil _ hdrop_ne]
          rw [hheadC, hlastC]
          have hgl4 : (b :: c :: t'').getLast (by simp) = W1.head h1 := by
            simpa [hW4] using j41
          rw [← hgl4]
          have h1' : (b :: c :: t'').dropLast.getLast hdrop_ne =
              (a :: b :: c :: t'')[t''.length + 1]'(by simp) := by
            rw [List.getLast_eq_getElem, List.getElem_dropLast]
            simp
          have h2' : (b :: c :: t'').getLast (by simp) =
              (a :: b :: c :: t'')[t''.length + 2]'(by simp) := by
            rw [List.getLast_eq_getElem]
            simp
          rw [h1', h2']
          exact hW4_adj' (t''.length + 1) (by simp)
  exact exists_cycle_of_adjList C hlen3 hndC hW4_cases.1 hW4_cases.2

/- ### Section 2: Bridges and bridge chains along a path `P` -/

private structure PBridge {V : Type*} (G : SimpleGraph V) (P : List V) where
  s : ℕ
  t : ℕ
  hs : s < P.length
  ht : t < P.length
  hst : s < t
  verts : List V
  hne : verts ≠ []
  hlen : 2 ≤ verts.length
  hnodup : verts.Nodup
  hadj : IsAdjList G verts
  hhead : verts.head hne = P[s]
  hlast : verts.getLast hne = P[t]
  hint : ∀ x ∈ verts, x ∈ P → x = P[s] ∨ x = P[t]

private lemma pbridge_merge {V : Type*} [DecidableEq V] {G : SimpleGraph V} {P : List V}
    (hPnd : P.Nodup) (q₁ q₂ : PBridge G P)
    (_hs : q₁.s < q₂.s) (ht : q₁.t < q₂.t)
    (z : V) (hzP : z ∉ P) (hz₁ : z ∈ q₁.verts) (hz₂ : z ∈ q₂.verts) :
    ∃ q : PBridge G P, q.s = q₁.s ∧ q.t = q₂.t := by
  let i₁ := q₁.verts.idxOf z
  let i₂ := q₂.verts.idxOf z
  have hi₁_lt : i₁ < q₁.verts.length := List.idxOf_lt_length_of_mem hz₁
  have hi₂_lt : i₂ < q₂.verts.length := List.idxOf_lt_length_of_mem hz₂
  have hi₁_get : q₁.verts[i₁] = z := List.getElem_idxOf hi₁_lt
  have hi₂_get : q₂.verts[i₂] = z := List.getElem_idxOf hi₂_lt
  have hi₁_pos : 0 < i₁ := by
    by_contra h0
    have hi0 : i₁ = 0 := by omega
    have : q₁.verts[0]'(by omega) = z := by simpa [hi0] using hi₁_get
    have hhead : q₁.verts[0]'(by omega) = P[q₁.s]'(q₁.hs) := by
      rw [← List.head_eq_getElem_zero q₁.hne, q₁.hhead]
    exact hzP (this ▸ hhead ▸ List.getElem_mem _)
  have hi₁_last : i₁ < q₁.verts.length - 1 := by
    by_contra hlast
    have hil : i₁ = q₁.verts.length - 1 := by omega
    have : q₁.verts[q₁.verts.length - 1]'(by omega) = z := by simpa [hil] using hi₁_get
    have hgl : q₁.verts[q₁.verts.length - 1]'(by omega) = P[q₁.t]'(q₁.ht) := by
      rw [← List.getLast_eq_getElem q₁.hne, q₁.hlast]
    exact hzP (this ▸ hgl ▸ List.getElem_mem _)
  have hi₂_pos : 0 < i₂ := by
    by_contra h0
    have hi0 : i₂ = 0 := by omega
    have : q₂.verts[0]'(by omega) = z := by simpa [hi0] using hi₂_get
    have hhead : q₂.verts[0]'(by omega) = P[q₂.s]'(q₂.hs) := by
      rw [← List.head_eq_getElem_zero q₂.hne, q₂.hhead]
    exact hzP (this ▸ hhead ▸ List.getElem_mem _)
  have hi₂_last : i₂ < q₂.verts.length - 1 := by
    by_contra hlast
    have hil : i₂ = q₂.verts.length - 1 := by omega
    have : q₂.verts[q₂.verts.length - 1]'(by omega) = z := by simpa [hil] using hi₂_get
    have hgl : q₂.verts[q₂.verts.length - 1]'(by omega) = P[q₂.t]'(q₂.ht) := by
      rw [← List.getLast_eq_getElem q₂.hne, q₂.hlast]
    exact hzP (this ▸ hgl ▸ List.getElem_mem _)
  let pref := q₁.verts.take i₁
  let suff := q₂.verts.drop i₂
  have hpref_len : pref.length = i₁ := by simp [pref]; omega
  have hsuff_len : suff.length = q₂.verts.length - i₂ := by simp [suff]
  have hpref_ne : pref ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hsuff_ne : suff ≠ [] := List.ne_nil_of_length_pos (by omega)
  let raw := pref ++ suff
  have hraw_ne : raw ≠ [] := List.append_ne_nil_of_left_ne_nil hpref_ne _
  have hraw_adj : IsAdjList G raw := by
    refine isAdjList_append (isAdjList_take q₁.hadj i₁) (isAdjList_drop q₂.hadj i₂) ?_
    intro _ _
    have h1 : pref.getLast hpref_ne = q₁.verts[i₁ - 1]'(by omega) := by
      rw [List.getLast_eq_getElem]
      simp only [pref, List.getElem_take]
      congr 1
      simpa [pref] using congrArg (· - 1) hpref_len
    have h2 : suff.head hsuff_ne = q₂.verts[i₂] := by
      rw [List.head_eq_getElem_zero]; simp [suff]
    have hadj : G.Adj (q₁.verts[i₁ - 1]'(by omega)) (q₁.verts[i₁]'hi₁_lt) := by
      have := q₁.hadj (i₁ - 1) (by omega)
      have heq : i₁ - 1 + 1 = i₁ := by omega
      simpa [heq] using this
    rw [h1, h2, hi₂_get]
    rwa [hi₁_get] at hadj
  have hraw_head : raw.head hraw_ne = P[q₁.s]'(q₁.hs) := by
    rw [List.head_append_of_ne_nil hpref_ne, List.head_eq_getElem_zero]
    simp only [pref, List.getElem_take, ← List.head_eq_getElem_zero q₁.hne, q₁.hhead]
  have hraw_last : raw.getLast hraw_ne = P[q₂.t]'(q₂.ht) := by
    rw [List.getLast_append_of_ne_nil _ hsuff_ne, List.getLast_eq_getElem]
    simp only [suff, List.getElem_drop]
    have hidx : i₂ + (suff.length - 1) = q₂.verts.length - 1 := by omega
    rw [← q₂.hlast, List.getLast_eq_getElem]
    congr 1
  have hraw_int : ∀ x ∈ raw, x ∈ P → x = P[q₁.s]'(q₁.hs) ∨ x = P[q₂.t]'(q₂.ht) := by
    intro x hx hxP
    rcases List.mem_append.mp hx with hx1 | hx2
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx1
      have hj_lt : j < i₁ := by omega
      have hj_lt1 : j < q₁.verts.length := lt_trans hj_lt hi₁_lt
      have hmem1 : q₁.verts[j]'hj_lt1 ∈ q₁.verts := List.getElem_mem _
      have hget : pref[j]'hj = q₁.verts[j]'hj_lt1 := List.getElem_take
      rw [hget] at hxP ⊢
      rcases q₁.hint _ hmem1 hxP with heq | heq
      · exact Or.inl heq
      · exfalso
        have hgl : q₁.verts[q₁.verts.length - 1]'(by omega) = P[q₁.t]'(q₁.ht) := by
          rw [← List.getLast_eq_getElem q₁.hne, q₁.hlast]
        have huniq := nodup_getElem_eq q₁.hnodup hj_lt1 (by omega) (heq.trans hgl.symm)
        omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx2
      have hj_lt2 : i₂ + j < q₂.verts.length := by omega
      have hget : suff[j]'hj = q₂.verts[i₂ + j]'hj_lt2 := List.getElem_drop
      have hmem2 : q₂.verts[i₂ + j]'hj_lt2 ∈ q₂.verts := List.getElem_mem _
      rw [hget] at hxP ⊢
      rcases q₂.hint _ hmem2 hxP with heq | heq
      · exfalso
        have hhd : q₂.verts[0]'(by omega) = P[q₂.s]'(q₂.hs) := by
          rw [← List.head_eq_getElem_zero q₂.hne, q₂.hhead]
        have huniq := nodup_getElem_eq q₂.hnodup hj_lt2 (by omega) (heq.trans hhd.symm)
        omega
      · exact Or.inr heq
  obtain ⟨l', hl', hnd', hadj', hhd', hgl', hsub'⟩ := nodup_shorten raw hraw_ne hraw_adj
  have hst' : q₁.s < q₂.t := lt_trans q₁.hst ht
  have hne_end : P[q₁.s]'(q₁.hs) ≠ P[q₂.t]'(q₂.ht) := by
    intro h; have := nodup_getElem_eq hPnd q₁.hs q₂.ht h; omega
  have hlen' : 2 ≤ l'.length := by
    by_contra hlt
    have hl1 : l'.length = 1 := by have := List.length_pos_iff.mpr hl'; omega
    have heq : l'.head hl' = l'.getLast hl' := by
      rw [List.head_eq_getElem_zero, List.getLast_eq_getElem]; congr 1; omega
    rw [hhd', hraw_head, hgl', hraw_last] at heq
    exact hne_end heq
  refine ⟨⟨q₁.s, q₂.t, q₁.hs, q₂.ht, hst', l', hl', hlen', hnd', hadj',
    hhd'.trans hraw_head, hgl'.trans hraw_last, ?_⟩, rfl, rfl⟩
  intro x hx hxP
  exact hraw_int x (hsub' x hx) hxP

private lemma exists_bridge_covering {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (P : List V) (hPnd : P.Nodup) (x : ℕ) (hx0 : 0 < x) (hxL : x + 1 < P.length)
    (h2conn : (G.induce {w : V | w ≠ P[x]}).Connected) :
    ∃ q : PBridge G P, q.s < x ∧ x < q.t := by
  classical
  have h0ne : P[0]'(by omega) ≠ P[x] := by
    intro h; have := nodup_getElem_eq hPnd (by omega) (by omega) h; omega
  have hLne : P[P.length - 1]'(by omega) ≠ P[x] := by
    intro h; have := nodup_getElem_eq hPnd (by omega) (by omega) h; omega
  obtain ⟨w⟩ := h2conn ⟨P[0]'(by omega), h0ne⟩ ⟨P[P.length - 1]'(by omega), hLne⟩
  let l : List V := w.support.map Subtype.val
  have hl_ne : l ≠ [] := List.ne_nil_of_length_pos (by simp [l])
  have hl_adj : IsAdjList G l := by
    intro i hi
    have hi' : i + 1 < w.support.length := by simpa [l] using hi
    have hadj := isAdjList_support w i hi'
    simpa [l] using hadj
  have hl_no_x : P[x] ∉ l := by
    intro hmem
    obtain ⟨⟨u, hu⟩, _, rfl⟩ := List.mem_map.mp hmem
    exact hu rfl
  have hl_head : l[0]'(List.length_pos_iff.mpr hl_ne) = P[0]'(by omega) := by
    have : w.support.head (Walk.support_ne_nil w) = ⟨P[0]'(by omega), h0ne⟩ := Walk.head_support w
    rw [List.head_eq_getElem_zero] at this
    simp [l, this]
  have hl_last : l[l.length - 1]'(by have := List.length_pos_iff.mpr hl_ne; omega) =
      P[P.length - 1]'(by omega) := by
    have : w.support.getLast (Walk.support_ne_nil w) = ⟨P[P.length - 1]'(by omega), hLne⟩ :=
      Walk.getLast_support w
    rw [List.getLast_eq_getElem] at this
    simp [l]
  let leftIdx : Finset (Fin l.length) :=
    Finset.univ.filter fun i : Fin l.length => ∃ s < x, ∃ hs : s < P.length, l[i.val] = P[s]
  have hleft_ne : leftIdx.Nonempty := by
    refine ⟨⟨0, List.length_pos_iff.mpr hl_ne⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨0, hx0, by omega, hl_head⟩
  let iL := leftIdx.max' hleft_ne
  obtain ⟨s, hsx, hsP, hiL_eq⟩ := (Finset.mem_filter.mp (Finset.max'_mem leftIdx hleft_ne)).2
  have hiL_lt_last : iL.val < l.length - 1 := by
    by_contra hge
    have heq : iL.val = l.length - 1 := by omega
    have h1 : l[iL.val]'iL.isLt = l[l.length - 1]'(by have := List.length_pos_iff.mpr hl_ne; omega) := by
      congr 1
    have hPs : P[P.length - 1]'(by omega) = P[s]'hsP := hl_last.symm.trans (h1.symm.trans hiL_eq)
    have := nodup_getElem_eq hPnd (by omega) hsP hPs
    omega
  let rightIdx : Finset (Fin l.length) :=
    Finset.univ.filter fun i : Fin l.length =>
      iL.val < i.val ∧ ∃ t, x < t ∧ ∃ ht : t < P.length, l[i.val] = P[t]
  have hright_ne : rightIdx.Nonempty := by
    refine ⟨⟨l.length - 1, by have := List.length_pos_iff.mpr hl_ne; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiL_lt_last, P.length - 1, by omega, by omega, hl_last⟩⟩
  let iR := rightIdx.min' hright_ne
  obtain ⟨hiLR, t, hxt, htP, hiR_eq⟩ := (Finset.mem_filter.mp (Finset.min'_mem rightIdx hright_ne)).2
  let raw := slice l iL.val (iR.val + 1)
  have hraw_len : raw.length = iR.val + 1 - iL.val := slice_length_of_le (by have := iR.isLt; omega)
  have hraw_ne : raw ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hraw_head : raw.head hraw_ne = P[s] := by
    rw [List.head_eq_getElem_zero, slice_getElem]; simpa using hiL_eq
  have hraw_last : raw.getLast hraw_ne = P[t] := by
    rw [List.getLast_eq_getElem, slice_getElem]
    have hidx : iL.val + (raw.length - 1) = iR.val := by omega
    simpa [hidx] using hiR_eq
  have hraw_int : ∀ y ∈ raw, y ∈ P → y = P[s] ∨ y = P[t] := by
    intro y hy hyP
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    have hget : raw[j]'hj = l[iL.val + j]'(by have := iR.isLt; omega) := slice_getElem hj
    rw [hget] at hyP ⊢
    obtain ⟨k, hkP, hk_eq⟩ := List.mem_iff_getElem.mp hyP
    by_cases hj0 : j = 0
    · left; subst hj0; simpa using hiL_eq
    · by_cases hjend : iL.val + j = iR.val
      · right; simpa [hjend] using hiR_eq
      · exfalso
        have hlt_l : iL.val + j < l.length := by have := iR.isLt; omega
        by_cases hkx : k < x
        · have hmem : (⟨iL.val + j, hlt_l⟩ : Fin l.length) ∈ leftIdx :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hkx, hkP, hk_eq.symm⟩
          have hle : iL.val + j ≤ iL.val :=
            Fin.le_iff_val_le_val.mp (Finset.le_max' leftIdx ⟨iL.val + j, hlt_l⟩ hmem)
          omega
        · by_cases hkx' : k = x
          · subst hkx'; exact hl_no_x (hk_eq ▸ List.getElem_mem hlt_l)
          · have hmem : (⟨iL.val + j, hlt_l⟩ : Fin l.length) ∈ rightIdx :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, k, by omega, hkP, hk_eq.symm⟩
            have hle : iR.val ≤ iL.val + j := by
              simpa using Fin.le_iff_val_le_val.mp (Finset.min'_le rightIdx ⟨iL.val + j, hlt_l⟩ hmem)
            omega
  obtain ⟨l', hl', hnd', hadj', hhd', hgl', hsub'⟩ :=
    nodup_shorten raw hraw_ne (isAdjList_slice hl_adj _ _)
  have hst : s < t := lt_trans hsx hxt
  have hne_st : P[s] ≠ P[t] := by
    intro h; have := nodup_getElem_eq hPnd hsP htP h; omega
  have hlen' : 2 ≤ l'.length := by
    by_contra hlt
    have hl1 : l'.length = 1 := by have := List.length_pos_iff.mpr hl'; omega
    have heq : l'.head hl' = l'.getLast hl' := by
      rw [List.head_eq_getElem_zero, List.getLast_eq_getElem]; congr 1; omega
    rw [hhd', hraw_head, hgl', hraw_last] at heq
    exact hne_st heq
  exact ⟨⟨s, t, hsP, htP, hst, l', hl', hlen', hnd', hadj',
    hhd'.trans hraw_head, hgl'.trans hraw_last,
    fun y hy hyP => hraw_int y (hsub' y hy) hyP⟩, hsx, hxt⟩

/- Stitching a chain of monotonically non-overlapping bridges along `P` -/

private def stitchChain {V : Type*} {G : SimpleGraph V} (P : List V) :
    ℕ → ℕ → List (PBridge G P) → List V
  | startIdx, endIdx, [] => slice P startIdx (endIdx + 1)
  | startIdx, endIdx, q :: rest =>
    slice P startIdx (q.s + 1) ++ q.verts.tail ++ (stitchChain P q.t endIdx rest).tail

private def BridgeChainOK {V : Type*} {G : SimpleGraph V} {P : List V} :
    ℕ → ℕ → List (PBridge G P) → Prop
  | startIdx, endIdx, [] => startIdx ≤ endIdx ∧ endIdx < P.length
  | startIdx, endIdx, q :: rest =>
    startIdx ≤ q.s ∧ BridgeChainOK q.t endIdx rest

private def ChainDisj {V : Type*} {G : SimpleGraph V} {P : List V} :
    List (PBridge G P) → Prop
  | [] => True
  | q :: rest =>
    (∀ q' ∈ rest, ∀ x ∈ q.verts, x ∈ q'.verts → x ∈ P) ∧ ChainDisj rest

private lemma bridgeChainOK_le {V : Type*} {G : SimpleGraph V} {P : List V}
    {s e : ℕ} {bs : List (PBridge G P)} (hok : BridgeChainOK s e bs) :
    s ≤ e ∧ e < P.length := by
  induction bs generalizing s with
  | nil => exact hok
  | cons q rest ih =>
    have ⟨h1, h2⟩ := ih hok.2
    exact ⟨le_trans hok.1 (le_trans (le_of_lt q.hst) h1), h2⟩

private lemma stitchChain_ne_nil {V : Type*} {G : SimpleGraph V} {P : List V}
    (s e : ℕ) (bs : List (PBridge G P)) (hok : BridgeChainOK s e bs) :
    stitchChain P s e bs ≠ [] := by
  cases bs with
  | nil =>
    have hlen : (stitchChain P s e ([] : List (PBridge G P))).length = e + 1 - s :=
      slice_length_of_le (by have := hok.2; omega)
    have := hok.1
    exact List.ne_nil_of_length_pos (by omega)
  | cons q rest =>
    have hlen : (slice P s (q.s + 1)).length = q.s + 1 - s :=
      slice_length_of_le (by have := q.hs; omega)
    have := hok.1
    exact List.append_ne_nil_of_left_ne_nil
      (List.append_ne_nil_of_left_ne_nil (List.ne_nil_of_length_pos (by omega)) _) _

private lemma stitchChain_head {V : Type*} {G : SimpleGraph V} {P : List V}
    (s e : ℕ) (bs : List (PBridge G P)) (hok : BridgeChainOK s e bs) :
    (stitchChain P s e bs).head (stitchChain_ne_nil s e bs hok) =
      P[s]'(by have := bridgeChainOK_le hok; omega) := by
  cases bs with
  | nil =>
    simp only [stitchChain]
    generalize_proofs h1 h2
    rw [List.head_eq_getElem_zero, slice_getElem]
    simp
  | cons q rest =>
    have hlen1 : (slice P s (q.s + 1)).length = q.s + 1 - s :=
      slice_length_of_le (by have := q.hs; omega)
    have := hok.1
    have hne1 : slice P s (q.s + 1) ≠ [] := List.ne_nil_of_length_pos (by omega)
    simp only [stitchChain]
    generalize_proofs h1 h2
    rw [List.head_append_of_ne_nil (List.append_ne_nil_of_left_ne_nil hne1 _),
        List.head_append_of_ne_nil hne1, List.head_eq_getElem_zero, slice_getElem]
    simp

private lemma stitchChain_last {V : Type*} {G : SimpleGraph V} {P : List V}
    (s e : ℕ) (bs : List (PBridge G P)) (hok : BridgeChainOK s e bs) :
    (stitchChain P s e bs).getLast (stitchChain_ne_nil s e bs hok) =
      P[e]'(bridgeChainOK_le hok).2 := by
  induction bs generalizing s with
  | nil =>
    simp only [stitchChain]
    generalize_proofs h1 h2
    rw [List.getLast_eq_getElem, slice_getElem]
    have hlen : (slice P s (e + 1)).length = e + 1 - s :=
      slice_length_of_le (by have := hok.2; omega)
    have := hok.1
    congr 1; omega
  | cons q rest ih =>
    simp only [stitchChain]
    generalize_proofs h1 h2
    by_cases htail : (stitchChain P q.t e rest).tail = []
    · have hqt_ne : stitchChain P q.t e rest ≠ [] := stitchChain_ne_nil q.t e rest hok.2
      have hqt_len1 : (stitchChain P q.t e rest).length = 1 := by
        have hpos := List.length_pos_iff.mpr hqt_ne
        have := congrArg List.length htail
        simp at this; omega
      have hqt_eq : (stitchChain P q.t e rest).head hqt_ne =
          (stitchChain P q.t e rest).getLast hqt_ne := by
        rw [List.head_eq_getElem_zero, List.getLast_eq_getElem]; congr 1; omega
      rw [stitchChain_head q.t e rest hok.2, ih q.t hok.2] at hqt_eq
      have hqtail_ne : q.verts.tail ≠ [] := by
        have := q.hlen; exact List.ne_nil_of_length_pos (by simp; omega)
      have hsub : slice P s (q.s + 1) ++ q.verts.tail ++ (stitchChain P q.t e rest).tail =
          slice P s (q.s + 1) ++ q.verts.tail := by rw [htail, List.append_nil]
      simp only [hsub]
      rw [List.getLast_append_of_ne_nil _ hqtail_ne, getLast_tail_eq q.hne hqtail_ne, q.hlast, hqt_eq]
    · have hqt_ne : stitchChain P q.t e rest ≠ [] := stitchChain_ne_nil q.t e rest hok.2
      rw [List.getLast_append_of_ne_nil _ htail, getLast_tail_eq hqt_ne htail]
      exact ih q.t hok.2

private lemma stitchChain_isAdj {V : Type*} {G : SimpleGraph V} {P : List V}
    (hPadj : IsAdjList G P) (s e : ℕ) (bs : List (PBridge G P)) (hok : BridgeChainOK s e bs) :
    IsAdjList G (stitchChain P s e bs) := by
  induction bs generalizing s with
  | nil => exact isAdjList_slice hPadj s (e + 1)
  | cons q rest ih =>
    simp only [stitchChain]
    have hlen1 : (slice P s (q.s + 1)).length = q.s + 1 - s :=
      slice_length_of_le (by have := q.hs; omega)
    have := hok.1
    have hne1 : slice P s (q.s + 1) ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hgl1 : (slice P s (q.s + 1)).getLast hne1 = P[q.s]'(q.hs) := by
      rw [List.getLast_eq_getElem, slice_getElem]; congr 1; omega
    have hpart1 : IsAdjList G (slice P s (q.s + 1) ++ q.verts.tail) :=
      isAdjList_append_tail (isAdjList_slice hPadj s (q.s + 1)) q.hadj hne1 q.hne
        (hgl1.trans q.hhead.symm)
    have hqtail_ne : q.verts.tail ≠ [] :=
      List.ne_nil_of_length_pos (by simp; have := q.hlen; omega)
    have hne12 : slice P s (q.s + 1) ++ q.verts.tail ≠ [] :=
      List.append_ne_nil_of_left_ne_nil hne1 _
    have hgl12 : (slice P s (q.s + 1) ++ q.verts.tail).getLast hne12 = P[q.t]'(q.ht) := by
      rw [List.getLast_append_of_ne_nil _ hqtail_ne, getLast_tail_eq q.hne hqtail_ne, q.hlast]
    exact isAdjList_append_tail hpart1 (ih q.t hok.2) hne12
      (stitchChain_ne_nil q.t e rest hok.2)
      (hgl12.trans (stitchChain_head q.t e rest hok.2).symm)

private lemma stitchChain_mem_P_ge {V : Type*} {G : SimpleGraph V} {P : List V}
    (hPnd : P.Nodup) (s e : ℕ) (bs : List (PBridge G P)) (hok : BridgeChainOK s e bs)
    {k : ℕ} (hk : k < P.length) (hmem : P[k] ∈ stitchChain P s e bs) :
    s ≤ k ∧ k ≤ e := by
  induction bs generalizing s with
  | nil =>
    have hmem' : P[k] ∈ slice P s (e + 1) := hmem
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem'
    rw [slice_getElem] at heq
    have hlen : (slice P s (e + 1)).length = e + 1 - s :=
      slice_length_of_le (by have := hok.2; omega)
    have hidx := nodup_getElem_eq hPnd (by have := hok.2; omega) hk heq
    have := hok.1; omega
  | cons q rest ih =>
    simp only [stitchChain, List.mem_append] at hmem
    have hqe : q.t ≤ e := (bridgeChainOK_le hok.2).1
    rcases hmem with (h1 | h2) | h3
    · obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp h1
      rw [slice_getElem] at heq
      have hlen : (slice P s (q.s + 1)).length = q.s + 1 - s :=
        slice_length_of_le (by have := q.hs; omega)
      have hidx := nodup_getElem_eq hPnd (by have := q.hs; omega) hk heq
      have := q.hst; have := hok.1; omega
    · rcases q.hint _ (List.mem_of_mem_tail h2) (List.getElem_mem hk) with heq | heq
      · have hidx := nodup_getElem_eq hPnd hk q.hs heq
        have := q.hst; have := hok.1; omega
      · have hidx := nodup_getElem_eq hPnd hk q.ht heq
        have := q.hst; have := hok.1; omega
    · have ⟨hlo, hhi⟩ := ih q.t hok.2 (List.mem_of_mem_tail h3)
      have := q.hst; have := hok.1; omega

private lemma stitchChain_mem_notP {V : Type*} {G : SimpleGraph V} {P : List V}
    (s e : ℕ) (bs : List (PBridge G P)) {x : V} (hxP : x ∉ P)
    (hmem : x ∈ stitchChain P s e bs) :
    ∃ q ∈ bs, x ∈ q.verts := by
  induction bs generalizing s with
  | nil =>
    exfalso
    exact hxP ((slice_sublist P s (e + 1)).subset hmem)
  | cons q rest ih =>
    simp only [stitchChain, List.mem_append] at hmem
    rcases hmem with (h1 | h2) | h3
    · exfalso; exact hxP ((slice_sublist P s (q.s + 1)).subset h1)
    · exact ⟨q, List.mem_cons_self, List.mem_of_mem_tail h2⟩
    · obtain ⟨q', hq', hx'⟩ := ih q.t (List.mem_of_mem_tail h3)
      exact ⟨q', List.mem_cons_of_mem q hq', hx'⟩

private lemma stitchChain_nodup {V : Type*} {G : SimpleGraph V} {P : List V}
    (hPnd : P.Nodup) (s e : ℕ) (bs : List (PBridge G P))
    (hok : BridgeChainOK s e bs) (hdisj : ChainDisj bs) :
    (stitchChain P s e bs).Nodup := by
  induction bs generalizing s with
  | nil => exact hPnd.sublist (slice_sublist P s (e + 1))
  | cons q rest ih =>
    simp only [stitchChain]
    have hnd1 : (slice P s (q.s + 1)).Nodup := hPnd.sublist (slice_sublist P s (q.s + 1))
    have hnd2 : q.verts.tail.Nodup := q.hnodup.tail
    have hnd3 : (stitchChain P q.t e rest).tail.Nodup := (ih q.t hok.2 hdisj.2).tail
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hnd1, hnd2, ?_⟩, hnd3, ?_⟩
    · intro x hx1 y hy2 hxy; subst hxy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx1
      have hlen : (slice P s (q.s + 1)).length = q.s + 1 - s :=
        slice_length_of_le (by have := q.hs; omega)
      have hget : (slice P s (q.s + 1))[j]'hj = P[s + j]'(by have := q.hs; omega) :=
        slice_getElem hj
      rw [hget] at hy2
      rcases q.hint _ (List.mem_of_mem_tail hy2) (List.getElem_mem _) with heq | heq
      · have hnot : q.verts.head q.hne ∉ q.verts.tail := head_not_mem_tail q.hne q.hnodup
        rw [q.hhead] at hnot
        exact hnot (heq ▸ hy2)
      · have hidx := nodup_getElem_eq hPnd (by have := q.hs; omega) q.ht heq
        have := q.hst; omega
    · intro x hx12 y hy3 hxy; subst hxy
      have hsc_ne : stitchChain P q.t e rest ≠ [] := stitchChain_ne_nil q.t e rest hok.2
      have hnot_hd : x ≠ P[q.t]'(q.ht) := by
        intro heq
        have hnot := head_not_mem_tail hsc_ne (ih q.t hok.2 hdisj.2)
        rw [stitchChain_head q.t e rest hok.2] at hnot
        exact hnot (heq ▸ hy3)
      have hy3' : x ∈ stitchChain P q.t e rest := List.mem_of_mem_tail hy3
      rcases List.mem_append.mp hx12 with hx1 | hx2
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx1
        have hlen : (slice P s (q.s + 1)).length = q.s + 1 - s :=
          slice_length_of_le (by have := q.hs; omega)
        have hget : (slice P s (q.s + 1))[j]'hj = P[s + j]'(by have := q.hs; omega) :=
          slice_getElem hj
        rw [hget] at hy3'
        have ⟨hlo, _⟩ := stitchChain_mem_P_ge hPnd q.t e rest hok.2 (by have := q.hs; omega) hy3'
        have := q.hst; omega
      · by_cases hxP : x ∈ P
        · rcases q.hint x (List.mem_of_mem_tail hx2) hxP with rfl | rfl
          · have ⟨hlo, _⟩ := stitchChain_mem_P_ge hPnd q.t e rest hok.2 q.hs hy3'
            have := q.hst; omega
          · exact hnot_hd rfl
        · obtain ⟨q', hq', hxq'⟩ := stitchChain_mem_notP q.t e rest hxP hy3'
          exact hxP (hdisj.1 q' hq' x (List.mem_of_mem_tail hx2) hxq')

private lemma stitchChain_mem_P_interval {V : Type*} {G : SimpleGraph V} {P : List V}
    (hPnd : P.Nodup) (s e : ℕ) (bs : List (PBridge G P)) (hok : BridgeChainOK s e bs)
    {k : ℕ} (hk : k < P.length) (hmem : P[k] ∈ stitchChain P s e bs) :
    (bs = [] ∧ s ≤ k ∧ k ≤ e) ∨
    (∃ q : PBridge G P, bs.head? = some q ∧ s ≤ k ∧ k ≤ q.s) ∨
    (∃ i : ℕ, ∃ hi : i + 1 < bs.length, bs[i].t ≤ k ∧ k ≤ bs[i + 1].s) ∨
    (∃ q : PBridge G P, bs.getLast? = some q ∧ q.t ≤ k ∧ k ≤ e) := by
  induction bs generalizing s with
  | nil =>
    left
    exact ⟨rfl, stitchChain_mem_P_ge hPnd s e [] hok hk hmem⟩
  | cons q rest ih =>
    simp only [stitchChain, List.mem_append] at hmem
    rcases hmem with (h1 | h2) | h3
    · right; left
      refine ⟨q, rfl, ?_⟩
      obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp h1
      rw [slice_getElem] at heq
      have hlen : (slice P s (q.s + 1)).length = q.s + 1 - s :=
        slice_length_of_le (by have := q.hs; omega)
      have hidx := nodup_getElem_eq hPnd (by have := q.hs; omega) hk heq
      have := hok.1; omega
    · rcases q.hint _ (List.mem_of_mem_tail h2) (List.getElem_mem hk) with heq | heq
      · right; left
        have hidx := nodup_getElem_eq hPnd hk q.hs heq
        exact ⟨q, rfl, by have := hok.1; omega, by omega⟩
      · have hidx := nodup_getElem_eq hPnd hk q.ht heq
        cases rest with
        | nil =>
          right; right; right
          exact ⟨q, rfl, by omega, by have := hok.2.1; omega⟩
        | cons q' rest' =>
          right; right; left
          exact ⟨0, by simp, by simp [hidx], by simpa [hidx] using hok.2.1⟩
    · have h3' : P[k] ∈ stitchChain P q.t e rest := List.mem_of_mem_tail h3
      rcases ih q.t hok.2 h3' with ⟨rfl, hlo, hhi⟩ | ⟨q', hhd, hlo, hhi⟩ | ⟨i, hi, hlo, hhi⟩ | ⟨q', hgl, hlo, hhi⟩
      · right; right; right
        exact ⟨q, rfl, hlo, hhi⟩
      · cases rest with
        | nil => simp at hhd
        | cons q'' rest' =>
          simp at hhd; subst hhd
          right; right; left
          exact ⟨0, by simp, hlo, hhi⟩
      · right; right; left
        exact ⟨i + 1, by simpa using hi, hlo, hhi⟩
      · right; right; right
        cases rest with
        | nil => simp at hgl
        | cons q'' rest' =>
          exact ⟨q', by simpa using hgl, hlo, hhi⟩

private lemma mk_bridgeChainOK {V : Type*} {G : SimpleGraph V} {P : List V}
    (bs : List (PBridge G P)) (s e : ℕ)
    (h0 : bs = [] → s ≤ e ∧ e < P.length)
    (hne : ∀ h : bs ≠ [], s ≤ (bs.head h).s ∧ (bs.getLast h).t ≤ e ∧ e < P.length)
    (hstep : ∀ r (hr : r + 1 < bs.length), bs[r].t ≤ bs[r + 1].s) :
    BridgeChainOK s e bs := by
  induction bs generalizing s with
  | nil => exact h0 rfl
  | cons q rest ih =>
    refine ⟨(hne (by simp)).1, ih q.t ?_ ?_ ?_⟩
    · intro hnil; subst hnil
      exact ⟨(hne (by simp)).2.1, (hne (by simp)).2.2⟩
    · intro hrest
      have h01 : q.t ≤ (rest.head hrest).s := by
        cases rest with
        | nil => exact absurd rfl hrest
        | cons r0 _ => simpa using hstep 0 (by simp)
      have hgl : rest.getLast hrest = (q :: rest).getLast (by simp) := by
        simp [List.getLast_cons hrest]
      exact ⟨h01, hgl ▸ (hne (by simp)).2.1, (hne (by simp)).2.2⟩
    · intro r hr
      exact hstep (r + 1) (by simpa using hr)

private lemma mk_chainDisj {V : Type*} {G : SimpleGraph V} {P : List V}
    (bs : List (PBridge G P))
    (h : ∀ i j (hi : i < bs.length) (hj : j < bs.length), i < j →
      ∀ x ∈ bs[i].verts, x ∈ bs[j].verts → x ∈ P) :
    ChainDisj bs := by
  induction bs with
  | nil => trivial
  | cons q rest ih =>
    refine ⟨?_, ih ?_⟩
    · intro q' hq' x hxq hxq'
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq'
      exact h 0 (j + 1) (by simp) (by simpa using hj) (by omega) x hxq hxq'
    · intro i j hi hj hij
      exact h (i + 1) (j + 1) (by simpa using hi) (by simpa using hj) (by omega)

/- ### Section 3: Modular pieces of Kopylov/Dirac's longest-path theorem -/

private lemma degree_ge_two_of_two_connected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (h2conn : ∀ v : V, (G.induce {w : V | w ≠ v}).Connected) :
    ∀ v : V, 2 ≤ G.degree v := by
  intro v
  by_contra hlt
  by_cases h0 : G.degree v = 0
  · have hne : (Finset.univ.erase v).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]; omega)
    obtain ⟨w, hw⟩ := hne
    have hwv : w ≠ v := Finset.ne_of_mem_erase hw
    obtain ⟨p⟩ := hconn v w
    cases p with
    | nil => exact hwv rfl
    | @cons _ b _ hadj _ =>
      have : b ∈ G.neighborFinset v := (mem_neighborFinset G v b).mpr hadj
      have hpos : 0 < (G.neighborFinset v).card := Finset.card_pos.mpr ⟨b, this⟩
      rw [card_neighborFinset_eq_degree] at hpos
      omega
  · have h1 : (G.neighborFinset v).card = 1 := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
    have hvw : v ≠ w := by
      intro h; subst h
      have : v ∈ G.neighborFinset v := by rw [hw]; simp
      exact ((mem_neighborFinset G v v).mp this).ne rfl
    have hlt2 : ({v, w} : Finset V).card < (Finset.univ : Finset V).card := by
      rw [Finset.card_pair hvw, Finset.card_univ]; omega
    obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
    have ⟨hzv, hzw⟩ : z ≠ v ∧ z ≠ w := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz; exact hz
    obtain ⟨p⟩ := h2conn w ⟨v, hvw⟩ ⟨z, hzw⟩
    cases p with
    | nil => exact hzv rfl
    | @cons _ b _ hadj _ =>
      have hb : b.val ∈ G.neighborFinset v := (mem_neighborFinset G v b.val).mpr hadj
      rw [hw, Finset.mem_singleton] at hb
      exact b.property hb

private lemma kopylov_case_inter {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (P : List V) (hPnd : P.Nodup) (hPadj : IsAdjList G P) (hP3 : 3 ≤ P.length)
    (hPmax : ∀ Q : List V, Q.Nodup → IsAdjList G Q → Q.length ≤ P.length)
    (r : ℕ) (hr : r + 1 < P.length)
    (hrA : G.Adj (P[0]'(by omega)) (P[r + 1]'hr))
    (hrB : G.Adj (P[P.length - 1]'(by omega)) (P[r]'(by omega))) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = Fintype.card V := by
  let p1 := slice P 0 (r + 1)
  let p2 := (slice P (r + 1) P.length).reverse
  let C := p1 ++ p2
  have hp1_len : p1.length = r + 1 := by
    dsimp only [p1]; rw [slice_length_of_le (by omega)]; omega
  have hp2_len : p2.length = P.length - (r + 1) := by
    dsimp only [p2]; rw [List.length_reverse, slice_length_of_le (le_refl P.length)]
  have hClen : C.length = P.length := by simp [C, hp1_len, hp2_len]; omega
  have hp1_ne : p1 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hp2_ne : p2 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hCne : C ≠ [] := List.append_ne_nil_of_left_ne_nil hp1_ne _
  have hCnd : C.Nodup := by
    rw [List.nodup_append]
    refine ⟨hPnd.sublist (slice_sublist _ _ _),
      List.nodup_reverse.mpr (hPnd.sublist (slice_sublist _ _ _)), ?_⟩
    intro x hx y hy hxy; subst hxy
    obtain ⟨j₁, hj₁, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.mem_reverse] at hy
    obtain ⟨j₂, hj₂, heq⟩ := List.mem_iff_getElem.mp hy
    rw [slice_getElem hj₁, slice_getElem hj₂] at heq
    have hlen2 : (slice P (r + 1) P.length).length = P.length - (r + 1) :=
      slice_length_of_le (le_refl P.length)
    have hidx := nodup_getElem_eq hPnd (by omega) (by omega) heq
    omega
  have hCadj : IsAdjList G C := by
    refine isAdjList_append (isAdjList_slice hPadj _ _)
      (isAdjList_reverse (isAdjList_slice hPadj _ _)) ?_
    intro _ _
    have h1 : p1.getLast hp1_ne = P[r]'(by omega) := by
      rw [List.getLast_eq_getElem, slice_getElem]; congr 1; omega
    have h2 : p2.head hp2_ne = P[P.length - 1]'(by omega) := by
      rw [List.head_eq_getElem_zero]
      simp only [p2, List.getElem_reverse, slice_getElem]
      have hlen2 : (slice P (r + 1) P.length).length = P.length - (r + 1) :=
        slice_length_of_le (le_refl P.length)
      congr 1; omega
    rw [h1, h2]
    exact hrB.symm
  have hCclose : ∀ h : C ≠ [], G.Adj (C.getLast h) (C.head h) := by
    intro _
    have h1 : C.getLast hCne = P[r + 1]'hr := by
      rw [List.getLast_append_of_ne_nil _ hp2_ne, List.getLast_eq_getElem]
      simp only [p2, List.getElem_reverse, slice_getElem]
      have hlen2 : (slice P (r + 1) P.length).length = P.length - (r + 1) :=
        slice_length_of_le (le_refl P.length)
      have hrev2 : (slice P (r + 1) P.length).reverse.length = P.length - (r + 1) := by
        rw [List.length_reverse, hlen2]
      congr 1; omega
    have h2 : C.head hCne = P[0]'(by omega) := by
      rw [List.head_append_of_ne_nil hp1_ne, List.head_eq_getElem_zero, slice_getElem]
    rw [h1, h2]
    exact hrA.symm
  have hPfull : P.length = Fintype.card V := by
    by_contra hne_full
    have hPlt : P.length < Fintype.card V := by
      have hle : P.length ≤ Fintype.card V := by
        have := Finset.card_le_univ P.toFinset
        rwa [List.toFinset_card_of_nodup hPnd] at this
      omega
    have hltC : C.toFinset.card < (Finset.univ : Finset V).card := by
      rw [List.toFinset_card_of_nodup hCnd, hClen, Finset.card_univ]; exact hPlt
    obtain ⟨w₀, _, hw₀'⟩ := Finset.exists_mem_notMem_of_card_lt_card hltC
    have hw₀ : w₀ ∉ C := by simpa using hw₀'
    obtain ⟨walk⟩ := hconn w₀ (C.head hCne)
    let sl := walk.support
    have hsl_adj : IsAdjList G sl := isAdjList_support walk
    have hsl_ne : sl ≠ [] := Walk.support_ne_nil walk
    let outIdx : Finset (Fin sl.length) :=
      Finset.univ.filter fun i : Fin sl.length => sl[i.val] ∉ C
    have hout_ne : outIdx.Nonempty := by
      refine ⟨⟨0, List.length_pos_iff.mpr hsl_ne⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      have : sl[0]'(List.length_pos_iff.mpr hsl_ne) = w₀ := by
        rw [← List.head_eq_getElem_zero hsl_ne]; exact Walk.head_support walk
      rwa [this]
    let io := outIdx.max' hout_ne
    have hio_out : sl[io.val] ∉ C := (Finset.mem_filter.mp (Finset.max'_mem outIdx hout_ne)).2
    have hio_lt : io.val + 1 < sl.length := by
      by_contra hge
      have heq : io.val = sl.length - 1 := by omega
      have h1 : sl[io.val]'io.isLt = sl[sl.length - 1]'(by have := List.length_pos_iff.mpr hsl_ne; omega) := by
        congr 1
      have hgl : sl[sl.length - 1]'(by have := List.length_pos_iff.mpr hsl_ne; omega) = C.head hCne := by
        rw [← List.getLast_eq_getElem hsl_ne]; exact Walk.getLast_support walk
      exact hio_out (by rw [h1, hgl]; exact List.head_mem hCne)
    have hnext_in : sl[io.val + 1] ∈ C := by
      by_contra hnot
      have hmem : (⟨io.val + 1, hio_lt⟩ : Fin sl.length) ∈ outIdx :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
      have hle : io.val + 1 ≤ io.val :=
        Fin.le_iff_val_le_val.mp (Finset.le_max' outIdx ⟨io.val + 1, hio_lt⟩ hmem)
      omega
    have hadj_w : G.Adj sl[io.val] sl[io.val + 1] := hsl_adj io.val hio_lt
    let C' := C.rotate (C.idxOf sl[io.val + 1])
    have hC'nd : C'.Nodup := List.nodup_rotate.mpr hCnd
    have hC'adj : IsAdjList G C' := isAdjList_rotate hCadj hCne (hCclose hCne) _
    have hC'ne : C' ≠ [] := by simpa [C'] using hCne
    have hC'head : C'.head hC'ne = sl[io.val + 1] := by
      rw [List.head_eq_getElem_zero]
      have hlt : C.idxOf sl[io.val + 1] < C.length := List.idxOf_lt_length_of_mem hnext_in
      simp only [C', List.getElem_rotate, Nat.zero_add, Nat.mod_eq_of_lt hlt]
      exact List.getElem_idxOf hlt
    have hnot_C' : sl[io.val] ∉ C' := by simpa [C', List.mem_rotate] using hio_out
    have hlong := hPmax (sl[io.val] :: C') (List.nodup_cons.mpr ⟨hnot_C', hC'nd⟩)
      (isAdjList_cons hC'adj (fun _ => by rw [hC'head]; exact hadj_w))
    simp [C', hClen] at hlong
  obtain ⟨u, c, hc, hclen⟩ := exists_cycle_of_adjList C (by omega) hCnd hCadj hCclose
  exact ⟨u, c, hc, by omega⟩

private lemma kopylov_case_crossing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : List V) (hPnd : P.Nodup) (hPadj : IsAdjList G P) (hP3 : 3 ≤ P.length)
    (A B : Finset (Fin (P.length - 1)))
    (hAdef : ∀ r : Fin (P.length - 1), r ∈ A ↔ G.Adj (P[0]'(by omega)) (P[r.val + 1]'(by omega)))
    (hBdef : ∀ r : Fin (P.length - 1), r ∈ B ↔ G.Adj (P[P.length - 1]'(by omega)) (P[r.val]'(by omega)))
    (hAcard : A.card = G.degree (P[0]'(by omega)))
    (hBcard : B.card = G.degree (P[P.length - 1]'(by omega)))
    (hd0 : 2 ≤ G.degree (P[0]'(by omega)))
    (hdL : 2 ≤ G.degree (P[P.length - 1]'(by omega)))
    (hdisjAB : Disjoint A B)
    (i0 j0 : Fin (P.length - 1)) (hi0 : i0 ∈ B) (hj0 : j0 ∈ A) (hcross : i0.val < j0.val + 1) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧
      G.degree (P[0]'(by omega)) + G.degree (P[P.length - 1]'(by omega)) ≤ c.length := by
  let L := P.length - 1
  let S : Finset (Fin L × Fin L) := (B ×ˢ A).filter (fun p => p.1.val < p.2.val + 1)
  have hSne : S.Nonempty := ⟨(i0, j0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi0, hj0⟩, hcross⟩⟩
  obtain ⟨⟨i, j'⟩, hmemS, hminS⟩ :=
    Finset.exists_min_image S (fun p => p.2.val + 1 - p.1.val) hSne
  have hiB : i ∈ B := (Finset.mem_product.mp (Finset.mem_filter.mp hmemS).1).1
  have hjA : j' ∈ A := (Finset.mem_product.mp (Finset.mem_filter.mp hmemS).1).2
  have hij' : i.val < j'.val + 1 := (Finset.mem_filter.mp hmemS).2
  have hij_ne : i ≠ j' := fun heq => Finset.disjoint_left.mp hdisjAB (heq ▸ hjA) hiB
  have hij_lt : i.val < j'.val := by
    have : i.val ≠ j'.val := fun h => hij_ne (Fin.ext h)
    omega
  let j : ℕ := j'.val + 1
  let I : Finset (Fin L) := Finset.univ.filter (fun r : Fin L => i.val < r.val ∧ r.val < j'.val)
  have hAB_disj_I : Disjoint (A ∪ B) I := by
    rw [Finset.disjoint_left]
    intro r hrAB hrI
    obtain ⟨hri, hrj⟩ := (Finset.mem_filter.mp hrI).2
    rcases Finset.mem_union.mp hrAB with hrA | hrB
    · have hmem' : (i, r) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hiB, hrA⟩, by dsimp only; omega⟩
      have hle := hminS (i, r) hmem'; dsimp only at hle; omega
    · have hmem' : (r, j') ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hrB, hjA⟩, by dsimp only; omega⟩
      have hle := hminS (r, j') hmem'; dsimp only at hle; omega
  have hIcard : I.card = j - i.val - 2 := by
    have hbij : I.card = (Finset.Ioo i.val j'.val).card := by
      refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
      · intro r hr
        obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hr).2
        exact Finset.mem_Ioo.mpr ⟨h1, h2⟩
      · intro r₁ _ r₂ _ h; exact Fin.ext h
      · intro k hk
        obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hk
        exact ⟨⟨k, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩, rfl⟩
    rw [hbij, Nat.card_Ioo]; omega
  have hsum_le : G.degree (P[0]'(by omega)) + G.degree (P[P.length - 1]'(by omega)) ≤
      L + 2 - (j - i.val) := by
    have hcard_le : (A ∪ B).card + I.card ≤ (Finset.univ : Finset (Fin L)).card := by
      rw [← Finset.card_union_of_disjoint hAB_disj_I]
      exact Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisjAB, hAcard, hBcard, hIcard, Finset.card_univ,
      Fintype.card_fin] at hcard_le
    omega
  let p1 := slice P 0 (i.val + 1)
  let p2 := (slice P j P.length).reverse
  let C := p1 ++ p2
  have hp1_len : p1.length = i.val + 1 := by
    dsimp only [p1]; rw [slice_length_of_le (by omega)]; omega
  have hp2_len : p2.length = P.length - j := by
    dsimp only [p2]; rw [List.length_reverse, slice_length_of_le (le_refl P.length)]
  have hClen : C.length = L + 2 - (j - i.val) := by simp [C, hp1_len, hp2_len]; omega
  have hp1_ne : p1 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hp2_ne : p2 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hCne : C ≠ [] := List.append_ne_nil_of_left_ne_nil hp1_ne _
  have hCnd : C.Nodup := by
    rw [List.nodup_append]
    refine ⟨hPnd.sublist (slice_sublist _ _ _),
      List.nodup_reverse.mpr (hPnd.sublist (slice_sublist _ _ _)), ?_⟩
    intro x hx y hy hxy; subst hxy
    obtain ⟨k₁, hk₁, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.mem_reverse] at hy
    obtain ⟨k₂, hk₂, heq⟩ := List.mem_iff_getElem.mp hy
    rw [slice_getElem hk₁, slice_getElem hk₂] at heq
    have hlen2 : (slice P j P.length).length = P.length - j :=
      slice_length_of_le (le_refl P.length)
    have hidx := nodup_getElem_eq hPnd (by omega) (by omega) heq
    omega
  have hCadj : IsAdjList G C := by
    refine isAdjList_append (isAdjList_slice hPadj _ _)
      (isAdjList_reverse (isAdjList_slice hPadj _ _)) ?_
    intro _ _
    have h1 : p1.getLast hp1_ne = P[i.val]'(by omega) := by
      rw [List.getLast_eq_getElem, slice_getElem]; congr 1; omega
    have h2 : p2.head hp2_ne = P[P.length - 1]'(by omega) := by
      rw [List.head_eq_getElem_zero]
      simp only [p2, List.getElem_reverse, slice_getElem]
      have hlen2 : (slice P j P.length).length = P.length - j :=
        slice_length_of_le (le_refl P.length)
      congr 1; omega
    rw [h1, h2]
    exact ((hBdef i).mp hiB).symm
  have hCclose : ∀ h : C ≠ [], G.Adj (C.getLast h) (C.head h) := by
    intro _
    have h1 : C.getLast hCne = P[j]'(by omega) := by
      rw [List.getLast_append_of_ne_nil _ hp2_ne, List.getLast_eq_getElem]
      simp only [p2, List.getElem_reverse, slice_getElem]
      have hlen2 : (slice P j P.length).length = P.length - j :=
        slice_length_of_le (le_refl P.length)
      have hrev2 : (slice P j P.length).reverse.length = P.length - j := by
        rw [List.length_reverse, hlen2]
      congr 1; omega
    have h2 : C.head hCne = P[0]'(by omega) := by
      rw [List.head_append_of_ne_nil hp1_ne, List.head_eq_getElem_zero, slice_getElem]
    rw [h1, h2]
    exact ((hAdef j').mp hjA).symm
  obtain ⟨u, c, hc, hclen⟩ := exists_cycle_of_adjList C (by omega) hCnd hCadj hCclose
  exact ⟨u, c, hc, by omega⟩

/- Structure holding a sorted minimal covering vine on `[a, b]` -/

private structure VineData {V : Type*} (G : SimpleGraph V) (P : List V) (a b : ℕ) where
  m : ℕ
  qs : List (PBridge G P)
  hlen : qs.length = m
  hm_pos : 1 ≤ m
  hs_strict : ∀ i j (hi : i < m) (hj : j < m), i < j → (qs[i]'(by omega)).s < (qs[j]'(by omega)).s
  ht_strict : ∀ i j (hi : i < m) (hj : j < m), i < j → (qs[i]'(by omega)).t < (qs[j]'(by omega)).t
  hs0_lt_a : (qs[0]'(by omega)).s < a
  hb_lt_tm : b < (qs[m - 1]'(by omega)).t
  ha_le_si : ∀ i (hi : i < m), 1 ≤ i → a ≤ (qs[i]'(by omega)).s
  hti_le_b : ∀ i (hi : i + 1 < m), (qs[i]'(by omega)).t ≤ b
  hstep_overlap : ∀ i (hi : i + 1 < m), (qs[i + 1]'(by omega)).s < (qs[i]'(by omega)).t
  hskip_disj : ∀ i (hi : i + 2 < m), (qs[i]'(by omega)).t ≤ (qs[i + 2]'(by omega)).s
  hpair_disj : ∀ i j (hi : i < m) (hj : j < m), i < j →
    ∀ x ∈ (qs[i]'(by omega)).verts, x ∈ (qs[j]'(by omega)).verts → x ∈ P

private lemma exists_vineData {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (P : List V) (hPnd : P.Nodup) (a b : ℕ)
    (ha0 : 0 < a) (hab : a ≤ b) (hbL : b + 1 < P.length)
    (h2conn : ∀ v : V, (G.induce {w : V | w ≠ v}).Connected) :
    Nonempty (VineData G P a b) := by
  let Covers (qs : List (PBridge G P)) : Prop :=
    ∀ x, a ≤ x → x ≤ b → ∃ q ∈ qs, q.s < x ∧ x < q.t
  have hex_cov : ∃ m : ℕ, ∃ qs : List (PBridge G P), qs.length = m ∧ Covers qs := by
    have hbuild : ∀ n : ℕ, a + n ≤ b + 1 →
        ∃ qs : List (PBridge G P), ∀ x, a ≤ x → x < a + n → ∃ q ∈ qs, q.s < x ∧ x < q.t := by
      intro n
      induction n with
      | zero => intro _; exact ⟨[], fun x h1 h2 => by omega⟩
      | succ n ih =>
        intro hle
        obtain ⟨qs, hqs⟩ := ih (by omega)
        obtain ⟨q, hqs', hqt'⟩ := exists_bridge_covering P hPnd (a + n) (by omega) (by omega)
          (h2conn (P[a + n]'(by omega)))
        refine ⟨q :: qs, fun x h1 h2 => ?_⟩
        by_cases heq : x = a + n
        · subst heq; exact ⟨q, List.mem_cons_self, hqs', hqt'⟩
        · obtain ⟨q', hq', h1', h2'⟩ := hqs x h1 (by omega)
          exact ⟨q', List.mem_cons_of_mem q hq', h1', h2'⟩
    obtain ⟨qs, hqs⟩ := hbuild (b + 1 - a) (by omega)
    exact ⟨qs.length, qs, rfl, fun x h1 h2 => hqs x h1 (by omega)⟩
  classical
  let m := Nat.find hex_cov
  obtain ⟨qs₀, hqs₀_len, hqs₀_cov⟩ := Nat.find_spec hex_cov
  have hmin_cov : ∀ qs' : List (PBridge G P), Covers qs' → m ≤ qs'.length :=
    fun qs' hcov' => Nat.find_min' hex_cov ⟨qs', rfl, hcov'⟩
  let qs := qs₀.mergeSort (fun q₁ q₂ => decide (q₁.s ≤ q₂.s))
  have hqs_perm : qs.Perm qs₀ := List.mergeSort_perm qs₀ _
  have hqs_len : qs.length = m := hqs_perm.length_eq.trans hqs₀_len
  have hqs_cov : Covers qs := by
    intro x h1 h2
    obtain ⟨q, hq, h3, h4⟩ := hqs₀_cov x h1 h2
    exact ⟨q, hqs_perm.mem_iff.mpr hq, h3, h4⟩
  have hqs_sorted : ∀ i j (hi : i < m) (hj : j < m), i ≤ j →
      (qs[i]'(by omega)).s ≤ (qs[j]'(by omega)).s := by
    have hpair : qs.Pairwise (fun q₁ q₂ => decide (q₁.s ≤ q₂.s) = true) :=
      List.pairwise_mergeSort (l := qs₀) (le := fun q₁ q₂ => decide (q₁.s ≤ q₂.s))
        (by intro x y z hxy hyz; simp only [decide_eq_true_eq] at hxy hyz ⊢; omega)
        (by intro x y; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    intro i j hi hj hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · have := List.pairwise_iff_getElem.mp hpair i j (by omega) (by omega) hlt
      simpa using this
  have hm_pos : 1 ≤ m := by
    obtain ⟨q, hq, _, _⟩ := hqs_cov a le_rfl hab
    have := List.length_pos_iff.mpr (List.ne_nil_of_mem hq)
    omega
  have hneed : ∀ idx (hidx : idx < m),
      ∃ x, a ≤ x ∧ x ≤ b ∧ (qs[idx]'(by omega)).s < x ∧ x < (qs[idx]'(by omega)).t ∧
        ∀ j (hj : j < m), j ≠ idx → ¬ ((qs[j]'(by omega)).s < x ∧ x < (qs[j]'(by omega)).t) := by
    intro idx hidx
    by_contra hall
    push Not at hall
    have hcov' : Covers (qs.eraseIdx idx) := by
      intro x h1 h2
      obtain ⟨q, hq, hsx, hxt⟩ := hqs_cov x h1 h2
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      by_cases hji : j = idx
      · subst hji
        obtain ⟨j', hj', hne', hs', ht'⟩ := hall x h1 h2 hsx hxt
        exact ⟨qs[j']'(by omega), getElem_mem_eraseIdx qs j j' (by omega) (by omega) hne', hs', ht'⟩
      · exact ⟨qs[j], getElem_mem_eraseIdx qs idx j (by omega) hj hji, hsx, hxt⟩
    have hle := hmin_cov (qs.eraseIdx idx) hcov'
    rw [List.length_eraseIdx_of_lt (by omega)] at hle
    omega
  have hs_strict : ∀ i j (hi : i < m) (hj : j < m), i < j →
      (qs[i]'(by omega)).s < (qs[j]'(by omega)).s := by
    intro i j hi hj hij
    have hle := hqs_sorted i j hi hj (le_of_lt hij)
    by_contra hge
    by_cases ht : (qs[i]'(by omega)).t ≤ (qs[j]'(by omega)).t
    · obtain ⟨x, _, _, hsx, hxt, hnot⟩ := hneed i hi
      exact hnot j hj (by omega) ⟨by omega, by omega⟩
    · obtain ⟨x, _, _, hsx, hxt, hnot⟩ := hneed j hj
      exact hnot i hi (by omega) ⟨by omega, by omega⟩
  have ht_strict : ∀ i j (hi : i < m) (hj : j < m), i < j →
      (qs[i]'(by omega)).t < (qs[j]'(by omega)).t := by
    intro i j hi hj hij
    have hlt_s := hs_strict i j hi hj hij
    by_contra hge
    obtain ⟨x, _, _, hsx, hxt, hnot⟩ := hneed j hj
    exact hnot i hi (by omega) ⟨by omega, by omega⟩
  have hs0_lt_a : (qs[0]'(by omega)).s < a := by
    obtain ⟨q, hq, hsx, _⟩ := hqs_cov a le_rfl hab
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
    have := hqs_sorted 0 j (by omega) (by omega) (Nat.zero_le j)
    omega
  have hb_lt_tm : b < (qs[m - 1]'(by omega)).t := by
    obtain ⟨q, hq, _, hxt⟩ := hqs_cov b hab le_rfl
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
    by_cases hjm : j = m - 1
    · subst hjm; exact hxt
    · have := ht_strict j (m - 1) (by omega) (by omega) (by omega); omega
  have ha_le_si : ∀ i (hi : i < m), 1 ≤ i → a ≤ (qs[i]'(by omega)).s := by
    intro i hi hi1
    by_contra hlt
    have ht0i := ht_strict 0 i (by omega) hi (by omega)
    obtain ⟨x, hx1, _, hsx, hxt, hnot⟩ := hneed 0 (by omega)
    exact hnot i hi (by omega) ⟨by omega, by omega⟩
  have hti_le_b : ∀ i (hi : i + 1 < m), (qs[i]'(by omega)).t ≤ b := by
    intro i hi
    by_contra hgt
    have hsim := hs_strict i (m - 1) (by omega) (by omega) (by omega)
    obtain ⟨x, _, hx2, hsx, hxt, hnot⟩ := hneed (m - 1) (by omega)
    exact hnot i (by omega) (by omega) ⟨by omega, by omega⟩
  have hstep_overlap : ∀ i (hi : i + 1 < m),
      (qs[i + 1]'(by omega)).s < (qs[i]'(by omega)).t := by
    intro i hi
    by_contra hge
    have hti_ge_a : a < (qs[i]'(by omega)).t := by
      obtain ⟨q, hq, hsx, hxt⟩ := hqs_cov a le_rfl hab
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      have hj0 : j = 0 := by
        by_contra hne0; have := ha_le_si j (by omega) (by omega); omega
      subst hj0
      by_cases hi0 : i = 0
      · subst hi0; exact hxt
      · have := ht_strict 0 i (by omega) (by omega) (by omega); omega
    obtain ⟨q, hq, hsx, hxt⟩ := hqs_cov (qs[i]'(by omega)).t (by omega) (hti_le_b i hi)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
    by_cases hji : j ≤ i
    · rcases eq_or_lt_of_le hji with rfl | hlt
      · omega
      · have := ht_strict j i (by omega) (by omega) hlt; omega
    · have := hqs_sorted (i + 1) j (by omega) (by omega) (by omega); omega
  have hskip_disj : ∀ i (hi : i + 2 < m),
      (qs[i]'(by omega)).t ≤ (qs[i + 2]'(by omega)).s := by
    intro i hi
    by_contra hgt
    obtain ⟨x, _, _, hsx, hxt, hnot⟩ := hneed (i + 1) (by omega)
    have hs01 := hs_strict i (i + 1) (by omega) (by omega) (by omega)
    have ht12 := ht_strict (i + 1) (i + 2) (by omega) (by omega) (by omega)
    by_cases hxt' : x < (qs[i]'(by omega)).t
    · exact hnot i (by omega) (by omega) ⟨by omega, hxt'⟩
    · exact hnot (i + 2) (by omega) (by omega) ⟨by omega, by omega⟩
  have hpair_disj : ∀ i j (hi : i < m) (hj : j < m), i < j →
      ∀ x ∈ (qs[i]'(by omega)).verts, x ∈ (qs[j]'(by omega)).verts → x ∈ P := by
    intro i j hi hj hij x hxi hxj
    by_contra hxP
    obtain ⟨q', hq's, hq't⟩ := pbridge_merge hPnd (qs[i]'(by omega)) (qs[j]'(by omega))
      (hs_strict i j hi hj hij) (ht_strict i j hi hj hij) x hxP hxi hxj
    let qs' := q' :: (qs.eraseIdx j).eraseIdx i
    have her_len : (qs.eraseIdx j).length = m - 1 := by
      rw [List.length_eraseIdx_of_lt (by omega)]; omega
    have hlen' : qs'.length = m - 1 := by
      simp only [qs', List.length_cons]
      rw [List.length_eraseIdx_of_lt (by omega), her_len]; omega
    have hcov' : Covers qs' := by
      intro y hy1 hy2
      obtain ⟨q, hq, hsy, hyt⟩ := hqs_cov y hy1 hy2
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hq
      by_cases h1 : idx = i
      · subst h1
        have htij := ht_strict idx j (by omega) hj hij
        exact ⟨q', List.mem_cons_self, by omega, by omega⟩
      · by_cases h2 : idx = j
        · subst h2
          have hsij := hs_strict i idx hi (by omega) hij
          exact ⟨q', List.mem_cons_self, by omega, by omega⟩
        · refine ⟨qs[idx], List.mem_cons_of_mem q' ?_, hsy, hyt⟩
          by_cases hlt : idx < j
          · have hk_lt : idx < (qs.eraseIdx j).length := by omega
            have hk_eq : (qs.eraseIdx j)[idx]'hk_lt = qs[idx] :=
              List.getElem_eraseIdx_of_lt hk_lt hlt
            rw [← hk_eq]
            exact getElem_mem_eraseIdx (qs.eraseIdx j) i idx (by omega) hk_lt h1
          · have hk_lt : idx - 1 < (qs.eraseIdx j).length := by omega
            have hk_eq : (qs.eraseIdx j)[idx - 1]'hk_lt = qs[idx] := by
              rw [List.getElem_eraseIdx_of_ge hk_lt (by omega)]; congr 1; omega
            rw [← hk_eq]
            exact getElem_mem_eraseIdx (qs.eraseIdx j) i (idx - 1) (by omega) hk_lt (by omega)
    have hle := hmin_cov qs' hcov'
    omega
  exact ⟨⟨m, qs, hqs_len, hm_pos, hs_strict, ht_strict, hs0_lt_a, hb_lt_tm,
    ha_le_si, hti_le_b, hstep_overlap, hskip_disj, hpair_disj⟩⟩

/- Endpoint detours RL (from P[s0] to P[a]) and RR (from P[b] to P[tm]) -/

private structure DetourLeft {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : List V) (s0 a : ℕ) where
  verts : List V
  hne : verts ≠ []
  hnd : verts.Nodup
  hadj : IsAdjList G verts
  hhead : ∀ hs : s0 < P.length, verts.head hne = P[s0]'hs
  hlast : ∀ ha : a < P.length, verts.getLast hne = P[a]'ha
  hlen : ∀ h0 : 0 < P.length, G.degree (P[0]'h0) + 1 ≤ verts.length
  hmem : ∀ x ∈ verts, ∃ k ≤ a, ∃ hk : k < P.length, x = P[k]'hk

private lemma build_detourLeft {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : List V) (hPnd : P.Nodup) (hPadj : IsAdjList G P) (hP3 : 3 ≤ P.length)
    (hP0_mem : ∀ w : V, G.Adj (P[0]'(by omega)) w → w ∈ P)
    (s0 a : ℕ) (hs0a : s0 < a) (haL : a < P.length - 1)
    (hmaxA : ∀ j (_hj0 : 0 < j) (hj : j < P.length), G.Adj (P[0]'(by omega)) (P[j]'hj) → j ≤ a)
    (haAdj : G.Adj (P[0]'(by omega)) (P[a]'(by omega))) :
    Nonempty (DetourLeft G P s0 a) := by
  let Ahi : Finset (Fin P.length) :=
    Finset.univ.filter fun j : Fin P.length => s0 < j.val ∧ G.Adj (P[0]'(by omega)) P[j.val]
  have hAhi_ne : Ahi.Nonempty :=
    ⟨⟨a, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0a, haAdj⟩⟩
  let rLFin := Ahi.min' hAhi_ne
  let rL := rLFin.val
  have hrL_gt : s0 < rL := (Finset.mem_filter.mp (Finset.min'_mem Ahi hAhi_ne)).2.1
  have hrL_adj : G.Adj (P[0]'(by omega)) (P[rL]'rLFin.isLt) :=
    (Finset.mem_filter.mp (Finset.min'_mem Ahi hAhi_ne)).2.2
  have hrL_le_a : rL ≤ a := hmaxA rL (by omega) rLFin.isLt hrL_adj
  let RL := (slice P 0 (s0 + 1)).reverse ++ slice P rL (a + 1)
  have h1_len : (slice P 0 (s0 + 1)).reverse.length = s0 + 1 := by
    rw [List.length_reverse, slice_length_of_le (by omega)]; omega
  have h2_len : (slice P rL (a + 1)).length = a + 1 - rL := slice_length_of_le (by omega)
  have h1_ne : (slice P 0 (s0 + 1)).reverse ≠ [] := List.ne_nil_of_length_pos (by omega)
  have h2_ne : slice P rL (a + 1) ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hRL_ne : RL ≠ [] := List.append_ne_nil_of_left_ne_nil h1_ne _
  have hRL_nd : RL.Nodup := by
    rw [List.nodup_append]
    refine ⟨List.nodup_reverse.mpr (hPnd.sublist (slice_sublist _ _ _)),
      hPnd.sublist (slice_sublist _ _ _), ?_⟩
    intro x hx y hy hxy; subst hxy
    rw [List.mem_reverse] at hx
    obtain ⟨j₁, hj₁, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j₂, hj₂, heq⟩ := List.mem_iff_getElem.mp hy
    rw [slice_getElem hj₁, slice_getElem hj₂] at heq
    have := slice_length_of_le (l := P) (a := 0) (b := s0 + 1) (by omega)
    have hidx := nodup_getElem_eq hPnd (by omega) (by omega) heq
    omega
  have hRL_adj : IsAdjList G RL := by
    refine isAdjList_append (isAdjList_reverse (isAdjList_slice hPadj _ _))
      (isAdjList_slice hPadj _ _) ?_
    intro _ _
    have h1 : (slice P 0 (s0 + 1)).reverse.getLast h1_ne = P[0]'(by omega) := by
      rw [List.getLast_eq_getElem, List.getElem_reverse, slice_getElem]
      have := slice_length_of_le (l := P) (a := 0) (b := s0 + 1) (by omega)
      congr 1; omega
    have h2 : (slice P rL (a + 1)).head h2_ne = P[rL]'rLFin.isLt := by
      rw [List.head_eq_getElem_zero, slice_getElem]; simp
    rw [h1, h2]; exact hrL_adj
  have hRL_head : ∀ hs : s0 < P.length, RL.head hRL_ne = P[s0]'hs := by
    intro hs
    rw [List.head_append_of_ne_nil h1_ne, List.head_eq_getElem_zero, List.getElem_reverse, slice_getElem]
    have := slice_length_of_le (l := P) (a := 0) (b := s0 + 1) (by omega)
    congr 1; omega
  have hRL_last : ∀ ha : a < P.length, RL.getLast hRL_ne = P[a]'ha := by
    intro ha
    rw [List.getLast_append_of_ne_nil _ h2_ne, List.getLast_eq_getElem, slice_getElem]
    congr 1; omega
  have hRL_len : ∀ h0 : 0 < P.length, G.degree (P[0]'h0) + 1 ≤ RL.length := by
    intro h0
    have hsub : insert (P[0]'h0) (G.neighborFinset (P[0]'h0)) ⊆ RL.toFinset := by
      intro w hw
      simp only [Finset.mem_insert, mem_neighborFinset, List.mem_toFinset] at hw ⊢
      rcases hw with rfl | hadj
      · apply List.mem_append_left
        rw [List.mem_reverse]
        have hlt : 0 < (slice P 0 (s0 + 1)).length := by
          rw [slice_length_of_le (by omega)]; omega
        have heq : (slice P 0 (s0 + 1))[0]'hlt = P[0]'h0 := by rw [slice_getElem]
        rw [← heq]; exact List.getElem_mem hlt
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (hP0_mem w hadj)
        have hj0 : 0 < j := by
          by_contra h
          have hj_eq : j = 0 := by omega
          subst hj_eq
          exact hadj.ne rfl
        have hja : j ≤ a := hmaxA j hj0 hj hadj
        by_cases hjs0 : j ≤ s0
        · apply List.mem_append_left
          rw [List.mem_reverse]
          have hlt : j < (slice P 0 (s0 + 1)).length := by
            rw [slice_length_of_le (by omega)]; omega
          have heq : (slice P 0 (s0 + 1))[j]'hlt = P[j]'hj := by rw [slice_getElem]; simp
          rw [← heq]; exact List.getElem_mem hlt
        · apply List.mem_append_right
          have hmemAhi : (⟨j, hj⟩ : Fin P.length) ∈ Ahi :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, hadj⟩
          have hrL_le_j : rL ≤ j := by
            simpa [rL] using Fin.le_iff_val_le_val.mp (Finset.min'_le Ahi ⟨j, hj⟩ hmemAhi)
          have hlt : j - rL < (slice P rL (a + 1)).length := by
            rw [slice_length_of_le (by omega)]; omega
          have heq : (slice P rL (a + 1))[j - rL]'hlt = P[j]'hj := by
            rw [slice_getElem]; congr 1; omega
          rw [← heq]; exact List.getElem_mem hlt
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree,
      List.toFinset_card_of_nodup hRL_nd] at hc
    exact hc
  have hRL_mem : ∀ x ∈ RL, ∃ k ≤ a, ∃ hk : k < P.length, x = P[k]'hk := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · rw [List.mem_reverse] at h1
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h1
      have := slice_length_of_le (l := P) (a := 0) (b := s0 + 1) (by omega)
      exact ⟨j, by omega, by omega, by rw [slice_getElem]; simp⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h2
      exact ⟨rL + j, by omega, by omega, slice_getElem hj⟩
  exact ⟨⟨RL, hRL_ne, hRL_nd, hRL_adj, hRL_head, hRL_last, hRL_len, hRL_mem⟩⟩

private structure DetourRight {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : List V) (b tm : ℕ) where
  verts : List V
  hne : verts ≠ []
  hnd : verts.Nodup
  hadj : IsAdjList G verts
  hhead : ∀ hb : b < P.length, verts.head hne = P[b]'hb
  hlast : ∀ htm : tm < P.length, verts.getLast hne = P[tm]'htm
  hlen : ∀ hL : P.length - 1 < P.length, G.degree (P[P.length - 1]'hL) + 1 ≤ verts.length
  hmem : ∀ x ∈ verts, ∃ k ≥ b, ∃ hk : k < P.length, x = P[k]'hk

private lemma build_detourRight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : List V) (hPnd : P.Nodup) (hPadj : IsAdjList G P) (hP3 : 3 ≤ P.length)
    (hPL_mem : ∀ w : V, G.Adj (P[P.length - 1]'(by omega)) w → w ∈ P)
    (b tm : ℕ) (_hb0 : 0 < b) (hbtm : b < tm) (htmP : tm < P.length)
    (hminB : ∀ j (hj : j < P.length - 1), G.Adj (P[P.length - 1]'(by omega)) (P[j]'(by omega)) → b ≤ j)
    (hbAdj : G.Adj (P[P.length - 1]'(by omega)) (P[b]'(by omega))) :
    Nonempty (DetourRight G P b tm) := by
  let Blo : Finset (Fin P.length) :=
    Finset.univ.filter fun j : Fin P.length => j.val < tm ∧ G.Adj (P[P.length - 1]'(by omega)) P[j.val]
  have hBlo_ne : Blo.Nonempty :=
    ⟨⟨b, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbtm, hbAdj⟩⟩
  let rRFin := Blo.max' hBlo_ne
  let rR := rRFin.val
  have hrR_lt : rR < tm := (Finset.mem_filter.mp (Finset.max'_mem Blo hBlo_ne)).2.1
  have hrR_adj : G.Adj (P[P.length - 1]'(by omega)) (P[rR]'rRFin.isLt) :=
    (Finset.mem_filter.mp (Finset.max'_mem Blo hBlo_ne)).2.2
  have hb_le_rR : b ≤ rR := hminB rR (by omega) hrR_adj
  let RR := slice P b (rR + 1) ++ (slice P tm P.length).reverse
  have h1_len : (slice P b (rR + 1)).length = rR + 1 - b := slice_length_of_le (by omega)
  have h2_len : (slice P tm P.length).reverse.length = P.length - tm := by
    rw [List.length_reverse, slice_length_of_le (le_refl P.length)]
  have h1_ne : slice P b (rR + 1) ≠ [] := List.ne_nil_of_length_pos (by omega)
  have h2_ne : (slice P tm P.length).reverse ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hRR_ne : RR ≠ [] := List.append_ne_nil_of_left_ne_nil h1_ne _
  have hRR_nd : RR.Nodup := by
    rw [List.nodup_append]
    refine ⟨hPnd.sublist (slice_sublist _ _ _),
      List.nodup_reverse.mpr (hPnd.sublist (slice_sublist _ _ _)), ?_⟩
    intro x hx y hy hxy; subst hxy
    rw [List.mem_reverse] at hy
    obtain ⟨j₁, hj₁, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j₂, hj₂, heq⟩ := List.mem_iff_getElem.mp hy
    rw [slice_getElem hj₁, slice_getElem hj₂] at heq
    have := slice_length_of_le (l := P) (a := tm) (b := P.length) (le_refl P.length)
    have hidx := nodup_getElem_eq hPnd (by omega) (by omega) heq
    omega
  have hRR_adj : IsAdjList G RR := by
    refine isAdjList_append (isAdjList_slice hPadj _ _)
      (isAdjList_reverse (isAdjList_slice hPadj _ _)) ?_
    intro _ _
    have h1 : (slice P b (rR + 1)).getLast h1_ne = P[rR]'rRFin.isLt := by
      rw [List.getLast_eq_getElem, slice_getElem]; congr 1; omega
    have h2 : (slice P tm P.length).reverse.head h2_ne = P[P.length - 1]'(by omega) := by
      rw [List.head_eq_getElem_zero, List.getElem_reverse, slice_getElem]
      have := slice_length_of_le (l := P) (a := tm) (b := P.length) (le_refl P.length)
      congr 1; omega
    rw [h1, h2]; exact hrR_adj.symm
  have hRR_head : ∀ hb : b < P.length, RR.head hRR_ne = P[b]'hb := by
    intro hb
    rw [List.head_append_of_ne_nil h1_ne, List.head_eq_getElem_zero, slice_getElem]; simp
  have hRR_last : ∀ htm : tm < P.length, RR.getLast hRR_ne = P[tm]'htm := by
    intro htm
    rw [List.getLast_append_of_ne_nil _ h2_ne, List.getLast_eq_getElem,
      List.getElem_reverse, slice_getElem]
    have := slice_length_of_le (l := P) (a := tm) (b := P.length) (le_refl P.length)
    congr 1; omega
  have hRR_len : ∀ hL : P.length - 1 < P.length, G.degree (P[P.length - 1]'hL) + 1 ≤ RR.length := by
    intro hL
    have hsub : insert (P[P.length - 1]'hL) (G.neighborFinset (P[P.length - 1]'hL)) ⊆ RR.toFinset := by
      intro w hw
      simp only [Finset.mem_insert, mem_neighborFinset, List.mem_toFinset] at hw ⊢
      rcases hw with rfl | hadj
      · apply List.mem_append_right
        rw [List.mem_reverse]
        have hlt : P.length - 1 - tm < (slice P tm P.length).length := by
          rw [slice_length_of_le (le_refl P.length)]; omega
        have heq : (slice P tm P.length)[P.length - 1 - tm]'hlt = P[P.length - 1]'hL := by
          rw [slice_getElem]; congr 1; omega
        rw [← heq]; exact List.getElem_mem hlt
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (hPL_mem w hadj)
        have hjL : j < P.length - 1 := by
          by_contra h
          have hj_eq : j = P.length - 1 := by omega
          subst hj_eq
          exact hadj.ne rfl
        have hbj : b ≤ j := hminB j hjL hadj
        by_cases hjtm : tm ≤ j
        · apply List.mem_append_right
          rw [List.mem_reverse]
          have hlt : j - tm < (slice P tm P.length).length := by
            rw [slice_length_of_le (le_refl P.length)]; omega
          have heq : (slice P tm P.length)[j - tm]'hlt = P[j]'hj := by
            rw [slice_getElem]; congr 1; omega
          rw [← heq]; exact List.getElem_mem hlt
        · apply List.mem_append_left
          have hmemBlo : (⟨j, hj⟩ : Fin P.length) ∈ Blo :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, hadj⟩
          have hj_le_rR : j ≤ rR := by
            simpa [rR] using Fin.le_iff_val_le_val.mp (Finset.le_max' Blo ⟨j, hj⟩ hmemBlo)
          have hlt : j - b < (slice P b (rR + 1)).length := by
            rw [slice_length_of_le (by omega)]; omega
          have heq : (slice P b (rR + 1))[j - b]'hlt = P[j]'hj := by
            rw [slice_getElem]; congr 1; omega
          rw [← heq]; exact List.getElem_mem hlt
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree,
      List.toFinset_card_of_nodup hRR_nd] at hc
    exact hc
  have hRR_mem : ∀ x ∈ RR, ∃ k ≥ b, ∃ hk : k < P.length, x = P[k]'hk := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h2
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h1
      exact ⟨b + j, by omega, by omega, slice_getElem hj⟩
    · rw [List.mem_reverse] at h2
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h2
      have := slice_length_of_le (l := P) (a := tm) (b := P.length) (le_refl P.length)
      exact ⟨tm + j, by omega, by omega, slice_getElem hj⟩
  exact ⟨⟨RR, hRR_ne, hRR_nd, hRR_adj, hRR_head, hRR_last, hRR_len, hRR_mem⟩⟩

/- Closing the vine when `m` is odd vs even -/

private lemma kopylov_case_vine {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : List V) (hPnd : P.Nodup) (hPadj : IsAdjList G P) (hP3 : 3 ≤ P.length)
    (a b : ℕ) (_ha0 : 0 < a) (hab : a ≤ b) (hbL : b + 1 < P.length)
    (hd0 : 2 ≤ G.degree (P[0]'(by omega)))
    (hdL : 2 ≤ G.degree (P[P.length - 1]'(by omega)))
    (Vdata : VineData G P a b)
    (dL : DetourLeft G P (Vdata.qs[0]'(by have := Vdata.hlen; have := Vdata.hm_pos; omega)).s a)
    (dR : DetourRight G P b (Vdata.qs[Vdata.m - 1]'(by have := Vdata.hlen; have := Vdata.hm_pos; omega)).t) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧
      G.degree (P[0]'(by omega)) + G.degree (P[P.length - 1]'(by omega)) ≤ c.length := by
  rcases Vdata with ⟨m, qs, hqs_len, hm_pos, hs_strict, ht_strict, hs0_lt_a, hb_lt_tm,
    ha_le_si, hti_le_b, hstep_overlap, hskip_disj, hpair_disj⟩
  let s0 := (qs[0]'(by omega)).s
  let tm := (qs[m - 1]'(by omega)).t
  have hs0_lt_P : s0 < P.length := (qs[0]'(by omega)).hs
  have htm_lt_P : tm < P.length := (qs[m - 1]'(by omega)).ht
  have hqs_idx : ∀ {i j : ℕ} (hi : i < qs.length) (hj : j < qs.length), i = j → qs[i] = qs[j] := by
    intro i j hi hj h; subst h; rfl
  have hqs_sorted : ∀ i j (hi : i < m) (hj : j < m), i ≤ j →
      (qs[i]'(by omega)).s ≤ (qs[j]'(by omega)).s := by
    intro i j hi hj hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (hs_strict i j hi hj hlt)
  let oddList : List (PBridge G P) :=
    (List.range ((m + 1) / 2)).attach.map fun ⟨r, hr⟩ =>
      qs[2 * r]'(by simp only [List.mem_range] at hr; omega)
  let evenList : List (PBridge G P) :=
    (List.range (m / 2)).attach.map fun ⟨r, hr⟩ =>
      qs[2 * r + 1]'(by simp only [List.mem_range] at hr; omega)
  have hodd_len : oddList.length = (m + 1) / 2 := by simp [oddList]
  have heven_len : evenList.length = m / 2 := by simp [evenList]
  have hodd_get : ∀ r (hr : r < (m + 1) / 2), oddList[r]'(by omega) = qs[2 * r]'(by omega) := by
    intro r hr; simp [oddList]
  have heven_get : ∀ r (hr : r < m / 2), evenList[r]'(by omega) = qs[2 * r + 1]'(by omega) := by
    intro r hr; simp [evenList]
  have hodd_disj : ChainDisj oddList := mk_chainDisj oddList fun i j hi hj hij => by
    rw [hodd_get i (by omega), hodd_get j (by omega)]
    exact hpair_disj (2 * i) (2 * j) (by omega) (by omega) (by omega)
  have heven_disj : ChainDisj evenList := mk_chainDisj evenList fun i j hi hj hij => by
    rw [heven_get i (by omega), heven_get j (by omega)]
    exact hpair_disj (2 * i + 1) (2 * j + 1) (by omega) (by omega) (by omega)
  have hdL_int : ∀ x ∈ dL.verts.tail.dropLast,
      ∃ k, k < a ∧ k ≠ s0 ∧ ∃ hk : k < P.length, x = P[k]'hk := by
    intro x hxl
    have hxl_t : x ∈ dL.verts.tail := List.mem_of_mem_dropLast hxl
    obtain ⟨k, hka, hkP, rfl⟩ := dL.hmem x (List.mem_of_mem_tail hxl_t)
    have hk_ne_s0 : k ≠ s0 := by
      intro hks
      have hnot := head_not_mem_tail dL.hne dL.hnd
      rw [dL.hhead hs0_lt_P] at hnot
      have hPeq : P[k]'hkP = P[s0]'hs0_lt_P := by congr 1
      exact hnot (hPeq ▸ hxl_t)
    have hk_ne_a : k ≠ a := by
      intro hka_eq
      have ht_ne : dL.verts.tail ≠ [] := List.ne_nil_of_mem hxl_t
      have ht_nd : dL.verts.tail.Nodup := dL.hnd.tail
      have hgl : dL.verts.tail.getLast ht_ne = P[a]'(by omega) := by
        rw [getLast_tail_eq dL.hne ht_ne, dL.hlast (by omega)]
      have hdrop : dL.verts.tail.dropLast ++ [P[a]'(by omega)] = dL.verts.tail := by
        rw [← hgl]; exact List.dropLast_append_getLast ht_ne
      rw [← hdrop, List.nodup_append] at ht_nd
      have hPeq : P[k]'hkP = P[a]'(by omega) := by congr 1
      exact ht_nd.2.2 _ hxl _ (List.mem_singleton_self _) hPeq
    exact ⟨k, by omega, hk_ne_s0, hkP, rfl⟩
  have hodd_ne : oddList ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hodd_hd_eq : ∀ q, oddList.head? = some q → q = qs[0]'(by omega) := by
    intro q hhd
    rw [List.head?_eq_some_head hodd_ne] at hhd
    rw [← Option.some.inj hhd, List.head_eq_getElem_zero]; exact hodd_get 0 (by omega)
  have heven_hd_eq : ∀ q, evenList.head? = some q → ∃ _hm2 : 2 ≤ m, q = qs[1]'(by omega) := by
    intro q hhd
    have hne : evenList ≠ [] := by intro h; rw [h] at hhd; simp at hhd
    have hpos := List.length_pos_iff.mpr hne
    rw [heven_len] at hpos
    have hm2 : 2 ≤ m := by omega
    refine ⟨hm2, ?_⟩
    rw [List.head?_eq_some_head hne] at hhd
    rw [← Option.some.inj hhd, List.head_eq_getElem_zero]; exact heven_get 0 (by omega)
  have hnotP_disj : ∀ (se1 ee1 se2 ee2 : ℕ) {x : V}, x ∉ P →
      x ∈ stitchChain P se1 ee1 evenList → x ∈ stitchChain P se2 ee2 oddList → False := by
    intro se1 ee1 se2 ee2 x hxP hxe hxo
    obtain ⟨q₁, hq₁, hx₁⟩ := stitchChain_mem_notP se1 ee1 evenList hxP hxe
    obtain ⟨q₂, hq₂, hx₂⟩ := stitchChain_mem_notP se2 ee2 oddList hxP hxo
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hq₁
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hq₂
    have hp' : p < m / 2 := by omega
    have hr' : r < (m + 1) / 2 := by omega
    rw [heven_get p hp'] at hx₁
    rw [hodd_get r hr'] at hx₂
    by_cases hlt : 2 * p + 1 < 2 * r
    · exact hxP (hpair_disj (2 * p + 1) (2 * r) (by omega) (by omega) hlt x hx₁ hx₂)
    · exact hxP (hpair_disj (2 * r) (2 * p + 1) (by omega) (by omega) (by omega) x hx₂ hx₁)
  by_cases hm_odd : m % 2 = 1
  · have hodd_gl_eq : ∀ q, oddList.getLast? = some q → q = qs[m - 1]'(by omega) := by
      intro q hgl
      rw [List.getLast?_eq_some_getLast hodd_ne] at hgl
      rw [← Option.some.inj hgl, List.getLast_eq_getElem]
      have hidx : 2 * (oddList.length - 1) = m - 1 := by omega
      simpa [hidx] using hodd_get (oddList.length - 1) (by omega)
    have heven_gl_eq : ∀ q, evenList.getLast? = some q → 2 ≤ m ∧ q = qs[m - 2]'(by omega) := by
      intro q hgl
      have hne : evenList ≠ [] := by intro h; rw [h] at hgl; simp at hgl
      have hm2 : 2 ≤ m := by have := List.length_pos_iff.mpr hne; omega
      refine ⟨hm2, ?_⟩
      rw [List.getLast?_eq_some_getLast hne] at hgl
      rw [← Option.some.inj hgl, List.getLast_eq_getElem]
      have hidx : 2 * (evenList.length - 1) + 1 = m - 2 := by omega
      simpa [hidx] using heven_get (evenList.length - 1) (by omega)
    have hodd_ok : BridgeChainOK s0 tm oddList :=
      mk_bridgeChainOK oddList s0 tm (fun h => absurd h hodd_ne)
        (fun hne => by
          have h1 := hodd_hd_eq _ (List.head?_eq_some_head hne)
          have h2 := hodd_gl_eq _ (List.getLast?_eq_some_getLast hne)
          rw [h1, h2]; exact ⟨le_rfl, le_rfl, htm_lt_P⟩)
        (fun r hr => by
          rw [hodd_get r (by omega), hodd_get (r + 1) (by omega)]
          rw [hqs_idx (by omega) (by omega) (show 2 * (r + 1) = 2 * r + 2 by omega)]
          exact hskip_disj (2 * r) (by omega))
    have heven_ok : BridgeChainOK a b evenList :=
      mk_bridgeChainOK evenList a b (fun _ => ⟨hab, by omega⟩)
        (fun hne => by
          have ⟨hm2, h1⟩ := heven_hd_eq _ (List.head?_eq_some_head hne)
          have ⟨_, h2⟩ := heven_gl_eq _ (List.getLast?_eq_some_getLast hne)
          rw [h1, h2]
          exact ⟨ha_le_si 1 (by omega) le_rfl, hti_le_b (m - 2) (by omega), by omega⟩)
        (fun r hr => by
          rw [heven_get r (by omega), heven_get (r + 1) (by omega)]
          rw [hqs_idx (by omega) (by omega) (show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega)]
          exact hskip_disj (2 * r + 1) (by omega))
    let Weven := stitchChain P a b evenList
    let Wodd := stitchChain P s0 tm oddList
    have hWeven_ne : Weven ≠ [] := stitchChain_ne_nil a b evenList heven_ok
    have hWodd_ne : Wodd ≠ [] := stitchChain_ne_nil s0 tm oddList hodd_ok
    have hWodd_rev_ne : Wodd.reverse ≠ [] := by simpa using hWodd_ne
    have hWeven_nd : Weven.Nodup := stitchChain_nodup hPnd a b evenList heven_ok heven_disj
    have hWodd_nd : Wodd.Nodup := stitchChain_nodup hPnd s0 tm oddList hodd_ok hodd_disj
    have hWeven_hd : Weven.head hWeven_ne = P[a]'(by omega) := stitchChain_head a b evenList heven_ok
    have hWeven_gl : Weven.getLast hWeven_ne = P[b]'(by omega) := stitchChain_last a b evenList heven_ok
    have hWodd_hd : Wodd.head hWodd_ne = P[s0]'hs0_lt_P := stitchChain_head s0 tm oddList hodd_ok
    have hWodd_gl : Wodd.getLast hWodd_ne = P[tm]'htm_lt_P := stitchChain_last s0 tm oddList hodd_ok
    have hWodd_rev_hd : Wodd.reverse.head hWodd_rev_ne = P[tm]'htm_lt_P := by
      rw [List.head_reverse]; exact hWodd_gl
    have hWodd_rev_gl : Wodd.reverse.getLast hWodd_rev_ne = P[s0]'hs0_lt_P := by
      rw [List.getLast_reverse]; exact hWodd_hd
    have hdisj_eo : ∀ x ∈ Weven, x ∉ Wodd := by
      intro x hxe hxo
      by_cases hxP : x ∈ P
      · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hxP
        have ⟨hka, hkb⟩ := stitchChain_mem_P_ge hPnd a b evenList heven_ok hk hxe
        have h1 := stitchChain_mem_P_interval hPnd s0 tm oddList hodd_ok hk hxo
        have h2 := stitchChain_mem_P_interval hPnd a b evenList heven_ok hk hxe
        rcases h1 with ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi⟩ | ⟨r, hr, hlo_o, hhi_o⟩ | ⟨q, hgl, hlo, _⟩
        · exact absurd hnil hodd_ne
        · have := hodd_hd_eq q hhd; subst this; omega
        · rw [hodd_get r (by omega)] at hlo_o
          rw [hodd_get (r + 1) (by omega)] at hhi_o
          have hhi_o' : k ≤ (qs[2 * r + 2]'(by omega)).s := by
            rw [← hqs_idx (by omega) (by omega) (show 2 * (r + 1) = 2 * r + 2 by omega)]
            exact hhi_o
          rcases h2 with ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi_e⟩ | ⟨p, hp, hlo_e, hhi_e⟩ | ⟨q, hgl, hlo_e, _⟩
          · have : m / 2 = 0 := by rw [← heven_len, hnil]; rfl
            omega
          · have ⟨hm2, hq⟩ := heven_hd_eq q hhd; subst hq
            have h01 := hstep_overlap 0 (by omega)
            simp only [Nat.zero_add] at h01
            by_cases hr0 : r = 0
            · have hq0 : qs[2 * r]'(by omega) = qs[0]'(by omega) := hqs_idx (by omega) (by omega) (by omega)
              rw [hq0] at hlo_o; omega
            · have := ht_strict 0 (2 * r) (by omega) (by omega) (by omega); omega
          · rw [heven_get p (by omega)] at hlo_e
            rw [heven_get (p + 1) (by omega)] at hhi_e
            have hhi_e' : k ≤ (qs[2 * p + 3]'(by omega)).s := by
              rw [← hqs_idx (by omega) (by omega) (show 2 * (p + 1) + 1 = 2 * p + 3 by omega)]
              exact hhi_e
            by_cases hpr : 2 * p + 1 < 2 * r
            · have hsort := hqs_sorted (2 * p + 3) (2 * r + 1) (by omega) (by omega) (by omega)
              have hov := hstep_overlap (2 * r) (by omega); omega
            · have hsort := hqs_sorted (2 * r + 2) (2 * p + 2) (by omega) (by omega) (by omega)
              have hov := hstep_overlap (2 * p + 1) (by omega)
              have hqeq : qs[2 * p + 1 + 1]'(by omega) = qs[2 * p + 2]'(by omega) :=
                hqs_idx (by omega) (by omega) (by omega)
              rw [hqeq] at hov; omega
          · have ⟨hm2, hq⟩ := heven_gl_eq q hgl; subst hq
            by_cases heq : 2 * r + 2 = m - 1
            · have h1 := hstep_overlap (m - 2) (by omega)
              have hqeq : qs[m - 2 + 1]'(by omega) = qs[2 * r + 2]'(by omega) :=
                hqs_idx (by omega) (by omega) (by omega)
              rw [hqeq] at h1; omega
            · have := hqs_sorted (2 * r + 2) (m - 2) (by omega) (by omega) (by omega)
              have := (qs[m - 2]'(by omega)).hst; omega
        · have := hodd_gl_eq q hgl; subst this; omega
      · exact hnotP_disj a b s0 tm hxP hxe hxo
    have hd12 : ∀ x ∈ Weven, x ∈ dR.verts.tail → False := by
      intro x hxe hxr
      obtain ⟨k, hkb, hkP, rfl⟩ := dR.hmem x (List.mem_of_mem_tail hxr)
      have ⟨_, hkb'⟩ := stitchChain_mem_P_ge hPnd a b evenList heven_ok hkP hxe
      have hnot := head_not_mem_tail dR.hne dR.hnd
      rw [dR.hhead (by omega)] at hnot
      have hPeq : P[k]'hkP = P[b]'(by omega) := by congr 1; omega
      exact hnot (hPeq ▸ hxr)
    have hd123 : ∀ x ∈ Weven ++ dR.verts.tail, x ∈ Wodd.reverse.tail → False := by
      intro x hx12 hxo
      have hxo' : x ∈ Wodd := List.mem_reverse.mp (List.mem_of_mem_tail hxo)
      rcases List.mem_append.mp hx12 with hxe | hxr
      · exact hdisj_eo x hxe hxo'
      · obtain ⟨k, hkb, hkP, rfl⟩ := dR.hmem x (List.mem_of_mem_tail hxr)
        have hnot_tm : k ≠ tm := by
          intro hktm
          have hnot := head_not_mem_tail hWodd_rev_ne (List.nodup_reverse.mpr hWodd_nd)
          rw [hWodd_rev_hd] at hnot
          have hPeq : P[k]'hkP = P[tm]'htm_lt_P := by congr 1
          exact hnot (hPeq ▸ hxo)
        rcases stitchChain_mem_P_interval hPnd s0 tm oddList hodd_ok hkP hxo' with
          ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi⟩ | ⟨r, hr, _, hhi⟩ | ⟨q, hgl, hlo, hhi⟩
        · exact absurd hnil hodd_ne
        · have := hodd_hd_eq q hhd; subst this; omega
        · rw [hodd_get (r + 1) (by omega)] at hhi
          have := hti_le_b (2 * r + 1) (by omega)
          have h3 := hstep_overlap (2 * r + 1) (by omega)
          have hqeq : qs[2 * r + 1 + 1]'(by omega) = qs[2 * (r + 1)]'(by omega) :=
            hqs_idx (by omega) (by omega) (by omega)
          rw [hqeq] at h3; omega
        · have := hodd_gl_eq q hgl; subst this; omega
    have hd1234 : ∀ x ∈ (Weven ++ dR.verts.tail) ++ Wodd.reverse.tail,
        x ∈ dL.verts.tail.dropLast → False := by
      intro x hx123 hxl
      obtain ⟨k, hka, hks0, hkP, rfl⟩ := hdL_int x hxl
      rcases List.mem_append.mp hx123 with hx12 | hxo
      · rcases List.mem_append.mp hx12 with hxe | hxr
        · have ⟨hlo, _⟩ := stitchChain_mem_P_ge hPnd a b evenList heven_ok hkP hxe; omega
        · obtain ⟨k', hk'b, hk'P, heq⟩ := dR.hmem _ (List.mem_of_mem_tail hxr)
          have := nodup_getElem_eq hPnd hkP hk'P heq; omega
      · have hxo' : P[k] ∈ Wodd := List.mem_reverse.mp (List.mem_of_mem_tail hxo)
        rcases stitchChain_mem_P_interval hPnd s0 tm oddList hodd_ok hkP hxo' with
          ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi⟩ | ⟨r, hr, hlo, _⟩ | ⟨q, hgl, hlo, _⟩
        · exact absurd hnil hodd_ne
        · have := hodd_hd_eq q hhd; subst this; omega
        · rw [hodd_get r (by omega)] at hlo
          have h01 := hstep_overlap 0 (by omega)
          simp only [Nat.zero_add] at h01
          have := ha_le_si 1 (by omega) le_rfl
          by_cases hr0 : r = 0
          · have hq0 : qs[2 * r]'(by omega) = qs[0]'(by omega) := hqs_idx (by omega) (by omega) (by omega)
            rw [hq0] at hlo; omega
          · have := ht_strict 0 (2 * r) (by omega) (by omega) (by omega); omega
        · have := hodd_gl_eq q hgl; subst this; omega
    have hWodd_len2 : 2 ≤ Wodd.length := by
      by_contra hlt
      have hlen1 : Wodd.length = 1 := by have := List.length_pos_iff.mpr hWodd_ne; omega
      have heq : Wodd.head hWodd_ne = Wodd.getLast hWodd_ne := by
        rw [List.head_eq_getElem_zero, List.getLast_eq_getElem]; congr 1; omega
      rw [hWodd_hd, hWodd_gl] at heq
      have := nodup_getElem_eq hPnd hs0_lt_P htm_lt_P heq; omega
    have hlen_bound : G.degree (P[0]'(by omega)) + G.degree (P[P.length - 1]'(by omega)) ≤
        (Weven ++ dR.verts.tail ++ Wodd.reverse.tail ++ dL.verts.tail.dropLast).length := by
      simp only [List.length_append, List.length_tail, List.length_dropLast, List.length_reverse]
      have h1 : 1 ≤ Weven.length := List.length_pos_iff.mpr hWeven_ne
      have := dL.hlen (by omega); have := dR.hlen (by omega); omega
    obtain ⟨u, c, hc, hclen⟩ := glue4_cycle Weven dR.verts Wodd.reverse dL.verts
      hWeven_ne dR.hne hWodd_rev_ne dL.hne
      hWeven_nd dR.hnd (List.nodup_reverse.mpr hWodd_nd) dL.hnd
      (stitchChain_isAdj hPadj a b evenList heven_ok) dR.hadj
      (isAdjList_reverse (stitchChain_isAdj hPadj s0 tm oddList hodd_ok)) dL.hadj
      (hWeven_gl.trans (dR.hhead (by omega)).symm)
      ((dR.hlast htm_lt_P).trans hWodd_rev_hd.symm)
      (hWodd_rev_gl.trans (dL.hhead hs0_lt_P).symm)
      ((dL.hlast (by omega)).trans hWeven_hd.symm)
      hd12 hd123 hd1234 (by omega)
    exact ⟨u, c, hc, by omega⟩
  · have hm2 : 2 ≤ m := by omega
    have heven_ne : evenList ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hodd_gl_eq : ∀ q, oddList.getLast? = some q → q = qs[m - 2]'(by omega) := by
      intro q hgl
      rw [List.getLast?_eq_some_getLast hodd_ne] at hgl
      rw [← Option.some.inj hgl, List.getLast_eq_getElem]
      have hidx : 2 * (oddList.length - 1) = m - 2 := by omega
      simpa [hidx] using hodd_get (oddList.length - 1) (by omega)
    have heven_gl_eq : ∀ q, evenList.getLast? = some q → q = qs[m - 1]'(by omega) := by
      intro q hgl
      rw [List.getLast?_eq_some_getLast heven_ne] at hgl
      rw [← Option.some.inj hgl, List.getLast_eq_getElem]
      have hidx : 2 * (evenList.length - 1) + 1 = m - 1 := by omega
      simpa [hidx] using heven_get (evenList.length - 1) (by omega)
    have hodd_ok : BridgeChainOK s0 b oddList :=
      mk_bridgeChainOK oddList s0 b (fun h => absurd h hodd_ne)
        (fun hne => by
          have h1 := hodd_hd_eq _ (List.head?_eq_some_head hne)
          have h2 := hodd_gl_eq _ (List.getLast?_eq_some_getLast hne)
          rw [h1, h2]; exact ⟨le_rfl, hti_le_b (m - 2) (by omega), by omega⟩)
        (fun r hr => by
          rw [hodd_get r (by omega), hodd_get (r + 1) (by omega)]
          rw [hqs_idx (by omega) (by omega) (show 2 * (r + 1) = 2 * r + 2 by omega)]
          exact hskip_disj (2 * r) (by omega))
    have heven_ok : BridgeChainOK a tm evenList :=
      mk_bridgeChainOK evenList a tm (fun h => absurd h heven_ne)
        (fun hne => by
          have ⟨_, h1⟩ := heven_hd_eq _ (List.head?_eq_some_head hne)
          have h2 := heven_gl_eq _ (List.getLast?_eq_some_getLast hne)
          rw [h1, h2]; exact ⟨ha_le_si 1 (by omega) le_rfl, le_rfl, htm_lt_P⟩)
        (fun r hr => by
          rw [heven_get r (by omega), heven_get (r + 1) (by omega)]
          rw [hqs_idx (by omega) (by omega) (show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega)]
          exact hskip_disj (2 * r + 1) (by omega))
    let Weven := stitchChain P a tm evenList
    let Wodd := stitchChain P s0 b oddList
    have hWeven_ne : Weven ≠ [] := stitchChain_ne_nil a tm evenList heven_ok
    have hWodd_ne : Wodd ≠ [] := stitchChain_ne_nil s0 b oddList hodd_ok
    have hWodd_rev_ne : Wodd.reverse ≠ [] := by simpa using hWodd_ne
    have hRR_rev_ne : dR.verts.reverse ≠ [] := by simpa using dR.hne
    have hWeven_nd : Weven.Nodup := stitchChain_nodup hPnd a tm evenList heven_ok heven_disj
    have hWodd_nd : Wodd.Nodup := stitchChain_nodup hPnd s0 b oddList hodd_ok hodd_disj
    have hWeven_hd : Weven.head hWeven_ne = P[a]'(by omega) := stitchChain_head a tm evenList heven_ok
    have hWeven_gl : Weven.getLast hWeven_ne = P[tm]'htm_lt_P := stitchChain_last a tm evenList heven_ok
    have hWodd_hd : Wodd.head hWodd_ne = P[s0]'hs0_lt_P := stitchChain_head s0 b oddList hodd_ok
    have hWodd_gl : Wodd.getLast hWodd_ne = P[b]'(by omega) := stitchChain_last s0 b oddList hodd_ok
    have hRR_rev_hd : dR.verts.reverse.head hRR_rev_ne = P[tm]'htm_lt_P := by
      rw [List.head_reverse]; exact dR.hlast htm_lt_P
    have hRR_rev_gl : dR.verts.reverse.getLast hRR_rev_ne = P[b]'(by omega) := by
      rw [List.getLast_reverse]; exact dR.hhead (by omega)
    have hWodd_rev_hd : Wodd.reverse.head hWodd_rev_ne = P[b]'(by omega) := by
      rw [List.head_reverse]; exact hWodd_gl
    have hWodd_rev_gl : Wodd.reverse.getLast hWodd_rev_ne = P[s0]'hs0_lt_P := by
      rw [List.getLast_reverse]; exact hWodd_hd
    have hdisj_eo : ∀ x ∈ Weven, x ∉ Wodd := by
      intro x hxe hxo
      by_cases hxP : x ∈ P
      · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hxP
        have ⟨hka, _⟩ := stitchChain_mem_P_ge hPnd a tm evenList heven_ok hk hxe
        have ⟨_, hkb⟩ := stitchChain_mem_P_ge hPnd s0 b oddList hodd_ok hk hxo
        have h1 := stitchChain_mem_P_interval hPnd s0 b oddList hodd_ok hk hxo
        have h2 := stitchChain_mem_P_interval hPnd a tm evenList heven_ok hk hxe
        rcases h1 with ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi⟩ | ⟨r, hr, hlo_o, hhi_o⟩ | ⟨q, hgl, hlo_o, _⟩
        · exact absurd hnil hodd_ne
        · have := hodd_hd_eq q hhd; subst this; omega
        · rw [hodd_get r (by omega)] at hlo_o
          rw [hodd_get (r + 1) (by omega)] at hhi_o
          have hhi_o' : k ≤ (qs[2 * r + 2]'(by omega)).s := by
            rw [← hqs_idx (by omega) (by omega) (show 2 * (r + 1) = 2 * r + 2 by omega)]
            exact hhi_o
          rcases h2 with ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi_e⟩ | ⟨p, hp, hlo_e, hhi_e⟩ | ⟨q, hgl, hlo_e, _⟩
          · exact absurd hnil heven_ne
          · have ⟨_, hq⟩ := heven_hd_eq q hhd; subst hq
            have h01 := hstep_overlap 0 (by omega)
            simp only [Nat.zero_add] at h01
            by_cases hr0 : r = 0
            · have hq0 : qs[2 * r]'(by omega) = qs[0]'(by omega) := hqs_idx (by omega) (by omega) (by omega)
              rw [hq0] at hlo_o; omega
            · have := ht_strict 0 (2 * r) (by omega) (by omega) (by omega); omega
          · rw [heven_get p (by omega)] at hlo_e
            rw [heven_get (p + 1) (by omega)] at hhi_e
            have hhi_e' : k ≤ (qs[2 * p + 3]'(by omega)).s := by
              rw [← hqs_idx (by omega) (by omega) (show 2 * (p + 1) + 1 = 2 * p + 3 by omega)]
              exact hhi_e
            by_cases hpr : 2 * p + 1 < 2 * r
            · have hsort := hqs_sorted (2 * p + 3) (2 * r + 1) (by omega) (by omega) (by omega)
              have hov := hstep_overlap (2 * r) (by omega); omega
            · have hsort := hqs_sorted (2 * r + 2) (2 * p + 2) (by omega) (by omega) (by omega)
              have hov := hstep_overlap (2 * p + 1) (by omega)
              have hqeq : qs[2 * p + 1 + 1]'(by omega) = qs[2 * p + 2]'(by omega) :=
                hqs_idx (by omega) (by omega) (by omega)
              rw [hqeq] at hov; omega
          · have := heven_gl_eq q hgl; subst this; omega
        · have := hodd_gl_eq q hgl; subst this
          rcases h2 with ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi_e⟩ | ⟨p, hp, _, hhi_e⟩ | ⟨q, hgl', hlo_e, _⟩
          · exact absurd hnil heven_ne
          · have ⟨_, hq⟩ := heven_hd_eq q hhd; subst hq
            have h01 := hstep_overlap 0 (by omega)
            simp only [Nat.zero_add] at h01
            by_cases hm2' : m = 2
            · have hq0 : qs[m - 2]'(by omega) = qs[0]'(by omega) := hqs_idx (by omega) (by omega) (by omega)
              rw [hq0] at hlo_o; omega
            · have := ht_strict 0 (m - 2) (by omega) (by omega) (by omega); omega
          · rw [heven_get (p + 1) (by omega)] at hhi_e
            have hhi_e' : k ≤ (qs[2 * p + 3]'(by omega)).s := by
              rw [← hqs_idx (by omega) (by omega) (show 2 * (p + 1) + 1 = 2 * p + 3 by omega)]
              exact hhi_e
            have := hqs_sorted (2 * p + 3) (m - 1) (by omega) (by omega) (by omega)
            have h2 := hstep_overlap (m - 2) (by omega)
            have hqeq : qs[m - 2 + 1]'(by omega) = qs[m - 1]'(by omega) :=
              hqs_idx (by omega) (by omega) (by omega)
            rw [hqeq] at h2; omega
          · have := heven_gl_eq q hgl'; subst this; omega
      · exact hnotP_disj a tm s0 b hxP hxe hxo
    have hd12 : ∀ x ∈ Weven, x ∈ dR.verts.reverse.tail → False := by
      intro x hxe hxr
      obtain ⟨k, hkb, hkP, rfl⟩ := dR.hmem x (List.mem_reverse.mp (List.mem_of_mem_tail hxr))
      have hnot_tm : k ≠ tm := by
        intro hktm
        have hnot := head_not_mem_tail hRR_rev_ne (List.nodup_reverse.mpr dR.hnd)
        rw [hRR_rev_hd] at hnot
        have hPeq : P[k]'hkP = P[tm]'htm_lt_P := by congr 1
        exact hnot (hPeq ▸ hxr)
      rcases stitchChain_mem_P_interval hPnd a tm evenList heven_ok hkP hxe with
        ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi⟩ | ⟨p, hp, _, hhi⟩ | ⟨q, hgl, hlo, hhi⟩
      · exact absurd hnil heven_ne
      · have ⟨_, hq⟩ := heven_hd_eq q hhd; subst hq
        have h01 := hstep_overlap 0 (by omega)
        simp only [Nat.zero_add] at h01
        have := hti_le_b 0 (by omega); omega
      · rw [heven_get (p + 1) (by omega)] at hhi
        have := hti_le_b (2 * p + 2) (by omega)
        have h3 := hstep_overlap (2 * p + 2) (by omega)
        have hqeq : qs[2 * p + 2 + 1]'(by omega) = qs[2 * (p + 1) + 1]'(by omega) :=
          hqs_idx (by omega) (by omega) (by omega)
        rw [hqeq] at h3; omega
      · have := heven_gl_eq q hgl; subst this; omega
    have hd123 : ∀ x ∈ Weven ++ dR.verts.reverse.tail, x ∈ Wodd.reverse.tail → False := by
      intro x hx12 hxo
      have hxo' : x ∈ Wodd := List.mem_reverse.mp (List.mem_of_mem_tail hxo)
      rcases List.mem_append.mp hx12 with hxe | hxr
      · exact hdisj_eo x hxe hxo'
      · obtain ⟨k, hkb, hkP, rfl⟩ := dR.hmem x (List.mem_reverse.mp (List.mem_of_mem_tail hxr))
        have ⟨_, hkb'⟩ := stitchChain_mem_P_ge hPnd s0 b oddList hodd_ok hkP hxo'
        have hnot := head_not_mem_tail hWodd_rev_ne (List.nodup_reverse.mpr hWodd_nd)
        rw [hWodd_rev_hd] at hnot
        have hPeq : P[k]'hkP = P[b]'(by omega) := by congr 1; omega
        exact hnot (hPeq ▸ hxo)
    have hd1234 : ∀ x ∈ (Weven ++ dR.verts.reverse.tail) ++ Wodd.reverse.tail,
        x ∈ dL.verts.tail.dropLast → False := by
      intro x hx123 hxl
      obtain ⟨k, hka, hks0, hkP, rfl⟩ := hdL_int x hxl
      rcases List.mem_append.mp hx123 with hx12 | hxo
      · rcases List.mem_append.mp hx12 with hxe | hxr
        · have ⟨hlo, _⟩ := stitchChain_mem_P_ge hPnd a tm evenList heven_ok hkP hxe; omega
        · obtain ⟨k', hk'b, hk'P, heq⟩ := dR.hmem _ (List.mem_reverse.mp (List.mem_of_mem_tail hxr))
          have := nodup_getElem_eq hPnd hkP hk'P heq; omega
      · have hxo' : P[k] ∈ Wodd := List.mem_reverse.mp (List.mem_of_mem_tail hxo)
        rcases stitchChain_mem_P_interval hPnd s0 b oddList hodd_ok hkP hxo' with
          ⟨hnil, _, _⟩ | ⟨q, hhd, _, hhi⟩ | ⟨r, hr, hlo, _⟩ | ⟨q, hgl, hlo, _⟩
        · exact absurd hnil hodd_ne
        · have := hodd_hd_eq q hhd; subst this; omega
        · rw [hodd_get r (by omega)] at hlo
          have h01 := hstep_overlap 0 (by omega)
          simp only [Nat.zero_add] at h01
          have := ha_le_si 1 (by omega) le_rfl
          by_cases hr0 : r = 0
          · have hq0 : qs[2 * r]'(by omega) = qs[0]'(by omega) := hqs_idx (by omega) (by omega) (by omega)
            rw [hq0] at hlo; omega
          · have := ht_strict 0 (2 * r) (by omega) (by omega) (by omega); omega
        · have := hodd_gl_eq q hgl; subst this
          have h01 := hstep_overlap 0 (by omega)
          simp only [Nat.zero_add] at h01
          have := ha_le_si 1 (by omega) le_rfl
          by_cases hm2' : m = 2
          · have hq0 : qs[m - 2]'(by omega) = qs[0]'(by omega) := hqs_idx (by omega) (by omega) (by omega)
            rw [hq0] at hlo; omega
          · have := ht_strict 0 (m - 2) (by omega) (by omega) (by omega); omega
    have hWeven_len2 : 2 ≤ Weven.length := by
      by_contra hlt
      have hlen1 : Weven.length = 1 := by have := List.length_pos_iff.mpr hWeven_ne; omega
      have heq : Weven.head hWeven_ne = Weven.getLast hWeven_ne := by
        rw [List.head_eq_getElem_zero, List.getLast_eq_getElem]; congr 1; omega
      rw [hWeven_hd, hWeven_gl] at heq
      have := nodup_getElem_eq hPnd (by omega) htm_lt_P heq; omega
    have hWodd_len2 : 2 ≤ Wodd.length := by
      by_contra hlt
      have hlen1 : Wodd.length = 1 := by have := List.length_pos_iff.mpr hWodd_ne; omega
      have heq : Wodd.head hWodd_ne = Wodd.getLast hWodd_ne := by
        rw [List.head_eq_getElem_zero, List.getLast_eq_getElem]; congr 1; omega
      rw [hWodd_hd, hWodd_gl] at heq
      have := nodup_getElem_eq hPnd hs0_lt_P (by omega) heq; omega
    have hlen_bound : G.degree (P[0]'(by omega)) + G.degree (P[P.length - 1]'(by omega)) ≤
        (Weven ++ dR.verts.reverse.tail ++ Wodd.reverse.tail ++ dL.verts.tail.dropLast).length := by
      simp only [List.length_append, List.length_tail, List.length_dropLast, List.length_reverse]
      have := dL.hlen (by omega); have := dR.hlen (by omega); omega
    obtain ⟨u, c, hc, hclen⟩ := glue4_cycle Weven dR.verts.reverse Wodd.reverse dL.verts
      hWeven_ne hRR_rev_ne hWodd_rev_ne dL.hne
      hWeven_nd (List.nodup_reverse.mpr dR.hnd) (List.nodup_reverse.mpr hWodd_nd) dL.hnd
      (stitchChain_isAdj hPadj a tm evenList heven_ok) (isAdjList_reverse dR.hadj)
      (isAdjList_reverse (stitchChain_isAdj hPadj s0 b oddList hodd_ok)) dL.hadj
      (hWeven_gl.trans hRR_rev_hd.symm)
      (hRR_rev_gl.trans hWodd_rev_hd.symm)
      (hWodd_rev_gl.trans (dL.hhead hs0_lt_P).symm)
      ((dL.hlast (by omega)).trans hWeven_hd.symm)
      hd12 hd123 hd1234 (by omega)
    exact ⟨u, c, hc, by omega⟩

private theorem kopylov_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (h2conn : ∀ v : V, (G.induce {w : V | w ≠ v}).Connected) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧
      ∃ (x y : V), min (Fintype.card V) (G.degree x + G.degree y) ≤ c.length := by
  classical
  have hdeg2 := degree_ge_two_of_two_connected G hn hconn h2conn
  let PPred (m : ℕ) : Prop := ∃ l : List V, l.length = m ∧ l.Nodup ∧ IsAdjList G l
  let M := Nat.findGreatest PPred (Fintype.card V)
  have hM_spec : PPred M := by
    obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact Nat.findGreatest_spec (m := 1) (by omega)
      ⟨[v₀], rfl, List.nodup_singleton v₀, isAdjList_singleton G v₀⟩
  obtain ⟨P, hPlen, hPnd, hPadj⟩ := hM_spec
  have hPmax : ∀ Q : List V, Q.Nodup → IsAdjList G Q → Q.length ≤ P.length := by
    intro Q hQnd hQadj
    have hQle : Q.length ≤ Fintype.card V := by
      have := Finset.card_le_univ Q.toFinset
      rwa [List.toFinset_card_of_nodup hQnd] at this
    rw [hPlen]
    exact Nat.le_findGreatest hQle ⟨Q, rfl, hQnd, hQadj⟩
  have hPne : P ≠ [] := by
    obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    have h1 : 1 ≤ P.length := hPmax [v₀] (List.nodup_singleton v₀) (isAdjList_singleton G v₀)
    exact List.ne_nil_of_length_pos (by omega)
  have hP0_mem : ∀ w : V, G.Adj (P[0]'(List.length_pos_iff.mpr hPne)) w → w ∈ P := by
    intro w hadj
    by_contra hnot
    have hnd' : (w :: P).Nodup := List.nodup_cons.mpr ⟨hnot, hPnd⟩
    have hadj' : IsAdjList G (w :: P) := isAdjList_cons hPadj (fun _ => by
      rw [List.head_eq_getElem_zero]; exact hadj.symm)
    have := hPmax (w :: P) hnd' hadj'
    simp at this
  have hPL_mem : ∀ w : V, G.Adj (P[P.length - 1]'(by have := List.length_pos_iff.mpr hPne; omega)) w → w ∈ P := by
    intro w hadj
    by_contra hnot
    have hnd' : (P ++ [w]).Nodup := by
      rw [List.nodup_append]
      exact ⟨hPnd, List.nodup_singleton w, fun x hx y hy hxy => by
        simp at hy; subst hy; subst hxy; exact hnot hx⟩
    have hadj' : IsAdjList G (P ++ [w]) :=
      isAdjList_append hPadj (isAdjList_singleton G w) (fun _ _ => by
        rw [List.getLast_eq_getElem, List.head_cons]; exact hadj)
    have := hPmax (P ++ [w]) hnd' hadj'
    simp at this
  have hP3 : 3 ≤ P.length := by
    let u₀ := P[0]'(List.length_pos_iff.mpr hPne)
    have hsub : insert u₀ (G.neighborFinset u₀) ⊆ P.toFinset := by
      intro w hw
      simp only [Finset.mem_insert, mem_neighborFinset, List.mem_toFinset] at hw ⊢
      rcases hw with rfl | hadj
      · exact List.getElem_mem _
      · exact hP0_mem w hadj
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree,
      List.toFinset_card_of_nodup hPnd] at hcard
    have := hdeg2 u₀; omega
  let L := P.length - 1
  let v0 : V := P[0]'(by omega)
  let vL : V := P[L]'(by omega)
  let A : Finset (Fin L) :=
    Finset.univ.filter fun r : Fin L => G.Adj v0 (P[r.val + 1]'(by omega))
  let B : Finset (Fin L) :=
    Finset.univ.filter fun r : Fin L => G.Adj vL (P[r.val]'(by omega))
  have hAcard : A.card = G.degree v0 := by
    rw [← card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun r _ => P[r.val + 1]'(by omega)) ?_ ?_ ?_
    · intro r hr; exact (mem_neighborFinset G v0 _).mpr (Finset.mem_filter.mp hr).2
    · intro r₁ _ r₂ _ heq
      have := nodup_getElem_eq hPnd (by omega) (by omega) heq; exact Fin.ext (by omega)
    · intro w hw
      have hadj : G.Adj v0 w := (mem_neighborFinset G v0 w).mp hw
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (hP0_mem w hadj)
      have hj0 : 0 < j := by
        by_contra h
        have hj_eq : j = 0 := by omega
        subst hj_eq
        exact hadj.ne rfl
      refine ⟨⟨j - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · dsimp only
        have heq : j - 1 + 1 = j := by omega
        simpa [heq] using hadj
      · dsimp only; congr 1; omega
  have hBcard : B.card = G.degree vL := by
    rw [← card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun r _ => P[r.val]'(by omega)) ?_ ?_ ?_
    · intro r hr; exact (mem_neighborFinset G vL _).mpr (Finset.mem_filter.mp hr).2
    · intro r₁ _ r₂ _ heq
      exact Fin.ext (nodup_getElem_eq hPnd (by omega) (by omega) heq)
    · intro w hw
      have hadj : G.Adj vL w := (mem_neighborFinset G vL w).mp hw
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (hPL_mem w hadj)
      have hjL : j < L := by
        by_contra h
        have hj_eq : j = L := by omega
        subst hj_eq
        exact hadj.ne rfl
      exact ⟨⟨j, hjL⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, rfl⟩
  have h0A : (⟨0, by omega⟩ : Fin L) ∈ A :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPadj 0 (by omega)⟩
  have hLB : (⟨L - 1, by omega⟩ : Fin L) ∈ B := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hadj := hPadj (L - 1) (by omega)
    have heq : L - 1 + 1 = L := by omega
    have hadj' : G.Adj (P[L - 1]'(by omega)) vL := by simpa [vL, heq] using hadj
    exact hadj'.symm
  by_cases hAB : (A ∩ B).Nonempty
  · obtain ⟨r, hr⟩ := hAB
    have hrA : G.Adj v0 (P[r.val + 1]'(by omega)) :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hr).1).2
    have hrB : G.Adj vL (P[r.val]'(by omega)) :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hr).2).2
    obtain ⟨u, c, hc, hclen⟩ :=
      kopylov_case_inter G hconn P hPnd hPadj hP3 hPmax r.val (by omega) hrA hrB
    exact ⟨u, c, hc, v0, vL, by rw [hclen]; exact Nat.min_le_left _ _⟩
  · have hdisjAB : Disjoint A B :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hAB)
    have hAne : A.Nonempty := ⟨⟨0, by omega⟩, h0A⟩
    have hBne : B.Nonempty := ⟨⟨L - 1, by omega⟩, hLB⟩
    let aMax := A.max' hAne
    let bMin := B.min' hBne
    let a : ℕ := aMax.val + 1
    let b : ℕ := bMin.val
    have ha_lt_L : a < L := by
      by_contra hge
      have haL : aMax.val = L - 1 := by omega
      have : (⟨L - 1, by omega⟩ : Fin L) ∈ A := by
        have hm := Finset.max'_mem A hAne
        have heq : aMax = ⟨L - 1, by omega⟩ := Fin.ext haL
        rwa [← heq]
      exact Finset.disjoint_left.mp hdisjAB this hLB
    have hb_pos : 0 < b := by
      by_contra h0
      have hb0 : bMin.val = 0 := by omega
      have : (⟨0, by omega⟩ : Fin L) ∈ B := by
        have hm := Finset.min'_mem B hBne
        have heq : bMin = ⟨0, by omega⟩ := Fin.ext hb0
        rwa [← heq]
      exact Finset.disjoint_left.mp hdisjAB h0A this
    by_cases hba : b < a
    · obtain ⟨u, c, hc, hclen⟩ := kopylov_case_crossing G P hPnd hPadj hP3 A B
        (fun r => by simp [A, v0]) (fun r => by simp [B, vL, L])
        hAcard hBcard (hdeg2 v0) (hdeg2 vL) hdisjAB
        bMin aMax (Finset.min'_mem B hBne) (Finset.max'_mem A hAne) hba
      exact ⟨u, c, hc, v0, vL, le_trans (Nat.min_le_right _ _) hclen⟩
    · have hab : a ≤ b := by omega
      obtain ⟨Vdata⟩ := exists_vineData P hPnd a b (by omega) hab (by omega) h2conn
      have hmaxA : ∀ j (hj0 : 0 < j) (hj : j < P.length), G.Adj (P[0]'(by omega)) (P[j]'hj) → j ≤ a := by
        intro j hj0 hjP hadj
        have hjL : j - 1 < L := by
          by_contra hge
          have hjeq : j = L := by omega
          subst hjeq
          have hmemA : (⟨L - 1, by omega⟩ : Fin L) ∈ A :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              dsimp only
              have heq : L - 1 + 1 = L := by omega
              simpa [heq] using hadj⟩
          exact Finset.disjoint_left.mp hdisjAB hmemA hLB
        have hmemA : (⟨j - 1, hjL⟩ : Fin L) ∈ A :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            dsimp only
            have heq : j - 1 + 1 = j := by omega
            simpa [heq] using hadj⟩
        have hle : j - 1 ≤ aMax.val :=
          Fin.le_iff_val_le_val.mp (Finset.le_max' A ⟨j - 1, hjL⟩ hmemA)
        omega
      have hminB : ∀ j (hj : j < P.length - 1), G.Adj (P[P.length - 1]'(by omega)) (P[j]'(by omega)) → b ≤ j := by
        intro j hjL hadj
        have hmemB : (⟨j, hjL⟩ : Fin L) ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
        exact Fin.le_iff_val_le_val.mp (Finset.min'_le B ⟨j, hjL⟩ hmemB)
      obtain ⟨dL⟩ := build_detourLeft G P hPnd hPadj hP3 hP0_mem
        (Vdata.qs[0]'(by have := Vdata.hlen; have := Vdata.hm_pos; omega)).s a
        Vdata.hs0_lt_a ha_lt_L hmaxA (Finset.mem_filter.mp (Finset.max'_mem A hAne)).2
      obtain ⟨dR⟩ := build_detourRight G P hPnd hPadj hP3 hPL_mem
        b (Vdata.qs[Vdata.m - 1]'(by have := Vdata.hlen; have := Vdata.hm_pos; omega)).t
        hb_pos Vdata.hb_lt_tm (Vdata.qs[Vdata.m - 1]'(by have := Vdata.hlen; have := Vdata.hm_pos; omega)).ht
        hminB (Finset.mem_filter.mp (Finset.min'_mem B hBne)).2
      obtain ⟨u, c, hc, hclen⟩ := kopylov_case_vine G P hPnd hPadj hP3 a b
        (by omega) hab (by omega) (hdeg2 v0) (hdeg2 vL) Vdata dL dR
      exact ⟨u, c, hc, v0, vL, le_trans (Nat.min_le_right _ _) hclen⟩

/- ### Section 4: Strong induction reduction to 2-connected graphs -/

private lemma lift_cycle_induce {V : Type*} {G : SimpleGraph V} {S : Set V} {k : ℕ}
    (h : ∃ (u : S) (c : (G.induce S).Walk u u), c.IsCycle ∧ k ≤ c.length) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  obtain ⟨u, c, hc, hlen⟩ := h
  let f : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  refine ⟨f.toHom u, c.map f.toHom, hc.map f.injective, ?_⟩
  rw [Walk.length_map]; exact hlen

private lemma degree_induce_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)]
    (u : S) :
    (G.induce S).degree u = ((G.neighborFinset u.val).filter (· ∈ S)).card := by
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun w _ => w.val) ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_filter.mpr ⟨(mem_neighborFinset G u.val w.val).mpr
      ((mem_neighborFinset (G.induce S) u w).mp hw), w.property⟩
  · intro w₁ _ w₂ _ heq; exact Subtype.ext heq
  · intro w hw
    obtain ⟨hadj, hwS⟩ := Finset.mem_filter.mp hw
    exact ⟨⟨w, hwS⟩, (mem_neighborFinset (G.induce S) u ⟨w, hwS⟩).mpr
      ((mem_neighborFinset G u.val w).mp hadj), rfl⟩

private theorem erdos_gallai_aux : ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    Fintype.card V = n → 3 ≤ k → (k - 1) * (n - 1) < 2 * G.edgeFinset.card →
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    intro V _ _ G _ k hcard hk hedge
    have h2e_le : 2 * G.edgeFinset.card ≤ n * (n - 1) := by
      rw [← G.sum_degrees_eq_twice_card_edges]
      calc ∑ v : V, G.degree v ≤ ∑ _v : V, (n - 1) := by
            refine Finset.sum_le_sum fun v _ => ?_
            have hle := G.degree_lt_card_verts v
            omega
        _ = n * (n - 1) := by rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
    have hkn : k ≤ n := by
      have hlt : (k - 1) * (n - 1) < n * (n - 1) := lt_of_lt_of_le hedge h2e_le
      have hn1 : 0 < n - 1 := by
        by_contra h0; have : n - 1 = 0 := by omega
        rw [this] at hlt; simp at hlt
      have : k - 1 < n := (Nat.mul_lt_mul_right hn1).mp hlt
      omega
    have hn3 : 3 ≤ n := by omega
    by_cases hlow : ∃ v : V, 2 * G.degree v ≤ k - 1
    · obtain ⟨v, hv⟩ := hlow
      let S : Set V := {w | w ≠ v}
      let G' := G.induce S
      have hcard' : Fintype.card S = n - 1 := by
        rw [Fintype.card_of_subtype (Finset.univ.erase v) (by intro x; simp [S]),
          Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
      have hedge' : 2 * G'.edgeFinset.card + 2 * G.degree v = 2 * G.edgeFinset.card := by
        rw [← G'.sum_degrees_eq_twice_card_edges, ← G.sum_degrees_eq_twice_card_edges]
        have hsum1 : ∑ u : S, G'.degree u =
            ∑ u ∈ Finset.univ.erase v, ((G.neighborFinset u).filter (· ≠ v)).card := by
          refine Finset.sum_bij (fun (u : S) _ => u.val) ?_ ?_ ?_ ?_
          · intro u _; exact Finset.mem_erase.mpr ⟨u.property, Finset.mem_univ _⟩
          · intro u₁ _ u₂ _ h; exact Subtype.ext h
          · intro u hu; exact ⟨⟨u, (Finset.mem_erase.mp hu).1⟩, Finset.mem_univ _, rfl⟩
          · intro u _; exact degree_induce_eq G S u
        have hsum2 : ∑ u ∈ Finset.univ.erase v,
            (((G.neighborFinset u).filter (· ≠ v)).card + if G.Adj u v then 1 else 0) =
            ∑ u ∈ Finset.univ.erase v, G.degree u := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← card_neighborFinset_eq_degree]
          by_cases hadj : G.Adj u v
          · have hmem : v ∈ G.neighborFinset u := (mem_neighborFinset G u v).mpr hadj
            have hfilt : (G.neighborFinset u).filter (· ≠ v) = (G.neighborFinset u).erase v := by
              ext w; simp [and_comm]
            rw [if_pos hadj, hfilt, Finset.card_erase_add_one hmem]
          · have hnot : v ∉ G.neighborFinset u := by simpa [mem_neighborFinset] using hadj
            have hfilt : (G.neighborFinset u).filter (· ≠ v) = G.neighborFinset u := by
              ext w; simp only [Finset.mem_filter, and_iff_left_iff_imp]
              intro hw heq; subst heq; exact hnot hw
            rw [if_neg hadj, hfilt, Nat.add_zero]
        have hsum3 : ∑ u ∈ Finset.univ.erase v, (if G.Adj u v then 1 else 0) = G.degree v := by
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
            ← card_neighborFinset_eq_degree]
          congr 1; ext u
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
            mem_neighborFinset]
          exact ⟨fun h => h.2.symm, fun h => ⟨G.ne_of_adj h.symm, h.symm⟩⟩
        have hsum4 : G.degree v + ∑ u ∈ Finset.univ.erase v, G.degree u = ∑ u : V, G.degree u :=
          Finset.add_sum_erase Finset.univ (fun u => G.degree u) (Finset.mem_univ v)
        rw [Finset.sum_add_distrib, hsum3] at hsum2
        omega
      have hedge_lt' : (k - 1) * (n - 1 - 1) < 2 * G'.edgeFinset.card := by
        have hmul : (k - 1) * (n - 1) = (k - 1) * (n - 1 - 1) + (k - 1) := by
          have : n - 1 = (n - 1 - 1) + 1 := by omega
          conv_lhs => rw [this]
          rw [Nat.mul_add, Nat.mul_one]
        omega
      exact lift_cycle_induce (ih (n - 1) (by omega) S G' k hcard' hk hedge_lt')
    push Not at hlow
    by_cases hconn : G.Connected
    · by_cases h2conn : ∀ v : V, (G.induce {w : V | w ≠ v}).Connected
      · obtain ⟨u, c, hc, x, y, hlen⟩ := kopylov_cycle G (by omega) hconn h2conn
        have hx : k ≤ 2 * G.degree x := by have := hlow x; omega
        have hy : k ≤ 2 * G.degree y := by have := hlow y; omega
        have hxy : k ≤ G.degree x + G.degree y := by omega
        exact ⟨u, c, hc, le_trans (le_min (by omega) hxy) hlen⟩
      · push Not at h2conn
        obtain ⟨v, hv_disc⟩ := h2conn
        let S := {w : V | w ≠ v}
        let Gv := G.induce S
        have hSne : Nonempty S := by
          have hcardS : Fintype.card S = n - 1 := by
            rw [Fintype.card_of_subtype (Finset.univ.erase v) (by intro x; simp [S]),
              Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
          exact Fintype.card_pos_iff.mp (by omega)
        obtain ⟨u₀⟩ := hSne
        have hex_unreach : ∃ w₀ : S, ¬ Gv.Reachable u₀ w₀ := by
          by_contra hall; push Not at hall
          apply hv_disc
          have : Nonempty S := ⟨u₀⟩
          exact Connected.mk fun a b => (hall a).symm.trans (hall b)
        obtain ⟨w₀, hw₀⟩ := hex_unreach
        let A : Set V := {w | w = v ∨ ∃ h : w ≠ v, Gv.Reachable u₀ ⟨w, h⟩}
        let B : Set V := {w | w = v ∨ ∃ h : w ≠ v, ¬ Gv.Reachable u₀ ⟨w, h⟩}
        have hAcard_ge : 2 ≤ Fintype.card A := by
          have hne : (⟨v, Or.inl rfl⟩ : A) ≠ ⟨u₀.val, Or.inr ⟨u₀.property, Reachable.refl _⟩⟩ := by
            intro h; exact u₀.property (congrArg Subtype.val h).symm
          have hle := Finset.card_le_univ ({⟨v, Or.inl rfl⟩,
            ⟨u₀.val, Or.inr ⟨u₀.property, Reachable.refl _⟩⟩} : Finset A)
          rw [Finset.card_pair hne] at hle; exact hle
        have hBcard_ge : 2 ≤ Fintype.card B := by
          have hne : (⟨v, Or.inl rfl⟩ : B) ≠ ⟨w₀.val, Or.inr ⟨w₀.property, hw₀⟩⟩ := by
            intro h; exact w₀.property (congrArg Subtype.val h).symm
          have hle := Finset.card_le_univ ({⟨v, Or.inl rfl⟩,
            ⟨w₀.val, Or.inr ⟨w₀.property, hw₀⟩⟩} : Finset B)
          rw [Finset.card_pair hne] at hle; exact hle
        have hAB_sum : Fintype.card A + Fintype.card B = n + 1 := by
          let fA : Finset V := Finset.univ.filter (· ∈ A)
          let fB : Finset V := Finset.univ.filter (· ∈ B)
          have h1 : Fintype.card A = fA.card :=
            Fintype.card_of_subtype fA (by intro x; simp [fA])
          have h2 : Fintype.card B = fB.card :=
            Fintype.card_of_subtype fB (by intro x; simp [fB])
          have hunion : fA ∪ fB = Finset.univ := by
            ext x
            simp only [fA, fB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
              iff_true]
            by_cases hxv : x = v
            · left; exact Or.inl hxv
            · by_cases hr : Gv.Reachable u₀ ⟨x, hxv⟩
              · left; exact Or.inr ⟨hxv, hr⟩
              · right; exact Or.inr ⟨hxv, hr⟩
          have hinter : fA ∩ fB = {v} := by
            ext x
            simp only [fA, fB, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_singleton]
            constructor
            · rintro ⟨hA, hB⟩
              rcases hA with rfl | ⟨_, hr⟩
              · rfl
              · rcases hB with rfl | ⟨_, hnr⟩
                · rfl
                · exact absurd hr hnr
            · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
          have hcu := Finset.card_union_add_card_inter fA fB
          rw [hunion, hinter, Finset.card_univ, hcard, Finset.card_singleton] at hcu
          omega
        have hAlt : Fintype.card A < n := by omega
        have hBlt : Fintype.card B < n := by omega
        have hedge_split : 2 * (G.induce A).edgeFinset.card + 2 * (G.induce B).edgeFinset.card =
            2 * G.edgeFinset.card := by
          rw [← (G.induce A).sum_degrees_eq_twice_card_edges,
              ← (G.induce B).sum_degrees_eq_twice_card_edges,
              ← G.sum_degrees_eq_twice_card_edges]
          have hdegA_ne : ∀ u : A, u.val ≠ v → (G.induce A).degree u = G.degree u.val := by
            intro u huv
            rw [degree_induce_eq, ← card_neighborFinset_eq_degree]
            congr 1; ext w
            simp only [Finset.mem_filter, and_iff_left_iff_imp, mem_neighborFinset]
            intro hadj
            by_cases hwv : w = v
            · exact Or.inl hwv
            · right; refine ⟨hwv, ?_⟩
              rcases u.property with h | ⟨_, hr⟩
              · exact absurd h huv
              · exact hr.trans (Adj.reachable (show Gv.Adj ⟨u.val, huv⟩ ⟨w, hwv⟩ from hadj))
          have hdegB_ne : ∀ u : B, u.val ≠ v → (G.induce B).degree u = G.degree u.val := by
            intro u huv
            rw [degree_induce_eq, ← card_neighborFinset_eq_degree]
            congr 1; ext w
            simp only [Finset.mem_filter, and_iff_left_iff_imp, mem_neighborFinset]
            intro hadj
            by_cases hwv : w = v
            · exact Or.inl hwv
            · right; refine ⟨hwv, ?_⟩
              rcases u.property with h | ⟨_, hnr⟩
              · exact absurd h huv
              · intro hr
                exact hnr (hr.trans (Adj.reachable (show Gv.Adj ⟨w, hwv⟩ ⟨u.val, huv⟩ from hadj.symm)))
          let vA : A := ⟨v, Or.inl rfl⟩
          let vB : B := ⟨v, Or.inl rfl⟩
          have hdegv : (G.induce A).degree vA + (G.induce B).degree vB =
              G.degree v := by
            rw [degree_induce_eq, degree_induce_eq, ← card_neighborFinset_eq_degree]
            have hdisj : Disjoint ((G.neighborFinset v).filter (· ∈ A))
                ((G.neighborFinset v).filter (· ∈ B)) := by
              rw [Finset.disjoint_left]
              intro w hwA hwB
              obtain ⟨hadj, hA⟩ := Finset.mem_filter.mp hwA
              obtain ⟨_, hB⟩ := Finset.mem_filter.mp hwB
              have hwv : w ≠ v := (G.ne_of_adj ((mem_neighborFinset G v w).mp hadj)).symm
              rcases hA with rfl | ⟨_, hr⟩
              · exact hwv rfl
              · rcases hB with rfl | ⟨_, hnr⟩
                · exact hwv rfl
                · exact hnr hr
            rw [← Finset.card_union_of_disjoint hdisj]
            congr 1; ext w
            simp only [Finset.mem_union, Finset.mem_filter, mem_neighborFinset]
            constructor
            · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
            · intro h
              have hwv : w ≠ v := (G.ne_of_adj h).symm
              by_cases hr : Gv.Reachable u₀ ⟨w, hwv⟩
              · left; exact ⟨h, Or.inr ⟨hwv, hr⟩⟩
              · right; exact ⟨h, Or.inr ⟨hwv, hr⟩⟩
          have hsumA := (Finset.add_sum_erase Finset.univ (fun u => (G.induce A).degree u) (Finset.mem_univ vA)).symm
          have hsumB := (Finset.add_sum_erase Finset.univ (fun u => (G.induce B).degree u) (Finset.mem_univ vB)).symm
          have hsumV := (Finset.add_sum_erase Finset.univ (fun u => G.degree u) (Finset.mem_univ v)).symm
          let sA : Finset V := (Finset.univ.erase v).filter (fun w => ∃ h : w ≠ v, Gv.Reachable u₀ ⟨w, h⟩)
          let sB : Finset V := (Finset.univ.erase v).filter (fun w => ∃ h : w ≠ v, ¬ Gv.Reachable u₀ ⟨w, h⟩)
          have hEA : ∑ u ∈ Finset.univ.erase vA, (G.induce A).degree u = ∑ w ∈ sA, G.degree w := by
            refine Finset.sum_bij (fun u _ => u.val) ?_ ?_ ?_ ?_
            · intro u hu
              have huv : u.val ≠ v := fun h => (Finset.ne_of_mem_erase hu) (Subtype.ext h)
              rcases u.property with h | h
              · exact absurd h huv
              · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨huv, Finset.mem_univ _⟩, h⟩
            · intro u₁ _ u₂ _ h; exact Subtype.ext h
            · intro w hw
              obtain ⟨hwv, hr⟩ := Finset.mem_filter.mp hw
              exact ⟨⟨w, Or.inr hr⟩, Finset.mem_erase.mpr
                ⟨fun h => (Finset.ne_of_mem_erase hwv) (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩
            · intro u hu
              exact hdegA_ne u (fun h => (Finset.ne_of_mem_erase hu) (Subtype.ext h))
          have hEB : ∑ u ∈ Finset.univ.erase vB, (G.induce B).degree u = ∑ w ∈ sB, G.degree w := by
            refine Finset.sum_bij (fun u _ => u.val) ?_ ?_ ?_ ?_
            · intro u hu
              have huv : u.val ≠ v := fun h => (Finset.ne_of_mem_erase hu) (Subtype.ext h)
              rcases u.property with h | h
              · exact absurd h huv
              · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨huv, Finset.mem_univ _⟩, h⟩
            · intro u₁ _ u₂ _ h; exact Subtype.ext h
            · intro w hw
              obtain ⟨hwv, hnr⟩ := Finset.mem_filter.mp hw
              exact ⟨⟨w, Or.inr hnr⟩, Finset.mem_erase.mpr
                ⟨fun h => (Finset.ne_of_mem_erase hwv) (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩
            · intro u hu
              exact hdegB_ne u (fun h => (Finset.ne_of_mem_erase hu) (Subtype.ext h))
          have hsAB_disj : Disjoint sA sB := by
            rw [Finset.disjoint_left]
            intro w hwA hwB
            obtain ⟨_, ⟨_, hr⟩⟩ := Finset.mem_filter.mp hwA
            obtain ⟨_, ⟨_, hnr⟩⟩ := Finset.mem_filter.mp hwB
            exact hnr hr
          have hsAB_union : sA ∪ sB = Finset.univ.erase v := by
            ext w
            simp only [Finset.mem_union, sA, sB, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
              and_true]
            constructor
            · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
            · intro hwv
              by_cases hr : Gv.Reachable u₀ ⟨w, hwv⟩
              · left; exact ⟨hwv, hwv, hr⟩
              · right; exact ⟨hwv, hwv, hr⟩
          have hsum_er : ∑ w ∈ sA, G.degree w + ∑ w ∈ sB, G.degree w =
              ∑ w ∈ Finset.univ.erase v, G.degree w := by
            rw [← Finset.sum_union hsAB_disj, hsAB_union]
          omega
        have hmul_sum : (k - 1) * (Fintype.card A - 1) + (k - 1) * (Fintype.card B - 1) =
            (k - 1) * (n - 1) := by
          rw [← Nat.mul_add]; congr 1; omega
        by_cases hA_good : (k - 1) * (Fintype.card A - 1) < 2 * (G.induce A).edgeFinset.card
        · exact lift_cycle_induce (ih (Fintype.card A) hAlt A (G.induce A) k rfl hk hA_good)
        · have hB_good : (k - 1) * (Fintype.card B - 1) < 2 * (G.induce B).edgeFinset.card := by omega
          exact lift_cycle_induce (ih (Fintype.card B) hBlt B (G.induce B) k rfl hk hB_good)
    · obtain ⟨u₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      have hex_unreach : ∃ w₀ : V, ¬ G.Reachable u₀ w₀ := by
        by_contra hall; push Not at hall
        have : Nonempty V := ⟨u₀⟩
        exact hconn (Connected.mk fun a b => (hall a).symm.trans (hall b))
      obtain ⟨w₀, hw₀⟩ := hex_unreach
      let A : Set V := {w | G.Reachable u₀ w}
      let B : Set V := {w | ¬ G.Reachable u₀ w}
      have hApos : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr ⟨⟨u₀, Reachable.refl u₀⟩⟩
      have hBpos : 1 ≤ Fintype.card B := Fintype.card_pos_iff.mpr ⟨⟨w₀, hw₀⟩⟩
      have hAB_sum : Fintype.card A + Fintype.card B = n := by
        let fA : Finset V := Finset.univ.filter (· ∈ A)
        let fB : Finset V := Finset.univ.filter (· ∈ B)
        have h1 : Fintype.card A = fA.card := Fintype.card_of_subtype fA (by intro x; simp [fA])
        have h2 : Fintype.card B = fB.card := Fintype.card_of_subtype fB (by intro x; simp [fB])
        have hdisj : Disjoint fA fB := by
          rw [Finset.disjoint_left]
          intro w hwA hwB
          exact (Finset.mem_filter.mp hwB).2 (Finset.mem_filter.mp hwA).2
        have hunion : fA ∪ fB = Finset.univ := by
          ext w
          simp only [fA, fB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact em (G.Reachable u₀ w)
        rw [h1, h2, ← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, hcard]
      have hAlt : Fintype.card A < n := by omega
      have hBlt : Fintype.card B < n := by omega
      have hedge_split : 2 * (G.induce A).edgeFinset.card + 2 * (G.induce B).edgeFinset.card =
          2 * G.edgeFinset.card := by
        rw [← (G.induce A).sum_degrees_eq_twice_card_edges,
            ← (G.induce B).sum_degrees_eq_twice_card_edges,
            ← G.sum_degrees_eq_twice_card_edges]
        let sA : Finset V := Finset.univ.filter (· ∈ A)
        let sB : Finset V := Finset.univ.filter (· ∈ B)
        have hEA : ∑ u : A, (G.induce A).degree u = ∑ w ∈ sA, G.degree w := by
          refine Finset.sum_bij (fun u _ => u.val) ?_ ?_ ?_ ?_
          · intro u _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.property⟩
          · intro u₁ _ u₂ _ h; exact Subtype.ext h
          · intro w hw; exact ⟨⟨w, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, rfl⟩
          · intro u _
            rw [degree_induce_eq, ← card_neighborFinset_eq_degree]
            congr 1; ext w
            simp only [Finset.mem_filter, and_iff_left_iff_imp, mem_neighborFinset]
            intro hadj; exact u.property.trans (Adj.reachable hadj)
        have hEB : ∑ u : B, (G.induce B).degree u = ∑ w ∈ sB, G.degree w := by
          refine Finset.sum_bij (fun u _ => u.val) ?_ ?_ ?_ ?_
          · intro u _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.property⟩
          · intro u₁ _ u₂ _ h; exact Subtype.ext h
          · intro w hw; exact ⟨⟨w, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, rfl⟩
          · intro u _
            rw [degree_induce_eq, ← card_neighborFinset_eq_degree]
            congr 1; ext w
            simp only [Finset.mem_filter, and_iff_left_iff_imp, mem_neighborFinset]
            intro hadj hr; exact u.property (hr.trans (Adj.reachable hadj.symm))
        have hdisj : Disjoint sA sB := by
          rw [Finset.disjoint_left]
          intro w hwA hwB
          exact (Finset.mem_filter.mp hwB).2 (Finset.mem_filter.mp hwA).2
        have hunion : sA ∪ sB = Finset.univ := by
          ext w
          simp only [Finset.mem_union, sA, sB, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact em (G.Reachable u₀ w)
        rw [hEA, hEB, ← Finset.sum_union hdisj, hunion]
      have hmul_le : (k - 1) * (Fintype.card A - 1) + (k - 1) * (Fintype.card B - 1) ≤
          (k - 1) * (n - 1) := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left (k - 1) (by omega)
      by_cases hA_good : (k - 1) * (Fintype.card A - 1) < 2 * (G.induce A).edgeFinset.card
      · exact lift_cycle_induce (ih (Fintype.card A) hAlt A (G.induce A) k rfl hk hA_good)
      · have hB_good : (k - 1) * (Fintype.card B - 1) < 2 * (G.induce B).edgeFinset.card := by omega
        exact lift_cycle_induce (ih (Fintype.card B) hBlt B (G.induce B) k rfl hk hB_good)

end OMAP2RegH1

theorem OMA.solution : OMA.R_opg_forcing_a_2_regular_minor_R1.H1 := by
  classical
  intro V _ _ G _ k hk hedge
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos
  have hlt : (k - 1) * (Fintype.card V - 1) < 2 * G.edgeFinset.card := by
    have hmul : (k - 1) * Fintype.card V = (k - 1) * (Fintype.card V - 1) + (k - 1) := by
      have : Fintype.card V = (Fintype.card V - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [Nat.mul_add, Nat.mul_one]
    omega
  exact OMAP2RegH1.erdos_gallai_aux (Fintype.card V) V G k rfl hk hlt
