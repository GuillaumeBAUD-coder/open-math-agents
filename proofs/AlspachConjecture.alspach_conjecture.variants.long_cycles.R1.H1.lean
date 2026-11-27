import OMAReductions.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1

/-!
# Walecki Hamilton Cycle Decomposition for Odd Complete Graphs

For odd order at least five, we decompose the complete graph into Hamilton cycles via
Walecki's rotational zigzag construction with one hub vertex and circle vertices.
-/

namespace OMA.WaleckiLong

open SimpleGraph AlspachConjecture

private abbrev K (n : ℕ) := completeGraph (Fin n)

private def chain {n : ℕ} (a b : Fin n) : List (Fin n) → Prop
  | [] => a ≠ b
  | x :: xs => a ≠ x ∧ chain x b xs

private def trail {n : ℕ} (a b : Fin n) : (l : List (Fin n)) → chain a b l → (K n).Walk a b
  | [], h => .cons (by simpa [chain] using h) .nil
  | x :: xs, h => .cons (by simpa [chain] using h.1) (trail x b xs h.2)

private def arcs {n : ℕ} (a b : Fin n) : List (Fin n) → List (Sym2 (Fin n))
  | [] => [s(a, b)]
  | x :: xs => s(a, x) :: arcs x b xs

private lemma trail_length {n : ℕ} (a b : Fin n) (l : List (Fin n)) (h : chain a b l) :
    (trail a b l h).length = l.length + 1 := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail, ih]

private lemma trail_support {n : ℕ} (a b : Fin n) (l : List (Fin n)) (h : chain a b l) :
    (trail a b l h).support = a :: (l ++ [b]) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail, ih]

private lemma trail_edges {n : ℕ} (a b : Fin n) (l : List (Fin n)) (h : chain a b l) :
    (trail a b l h).edges = arcs a b l := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [trail, arcs, ih]

private lemma chain_of_nodup {n : ℕ} (a b : Fin n) (l : List (Fin n))
    (hnodup : (a :: l).Nodup) (hb : b ∉ l) (hne : l = [] → a ≠ b) : chain a b l := by
  induction l generalizing a with
  | nil => exact hne rfl
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    have hx_ne : a ≠ x := fun h => hnodup.1 (by simp [h])
    have hb_xs : b ∉ xs := fun h => hb (List.mem_cons_of_mem x h)
    have hxb : xs = [] → x ≠ b := fun _ h => hb (by simp [h])
    exact ⟨hx_ne, ih x hnodup.2 hb_xs hxb⟩

private lemma nodup_append_singleton_of_cons {α : Type*} (a : α) (l : List α)
    (h : (a :: l).Nodup) : (l ++ [a]).Nodup := by
  rw [List.nodup_cons] at h
  rw [List.nodup_append]
  refine ⟨h.2, List.nodup_singleton a, ?_⟩
  intro x hx y hy hxy
  rw [List.mem_singleton] at hy
  subst hy
  subst hxy
  exact h.1 hx

private def mkCycle {n : ℕ} (a : Fin n) (l : List (Fin n))
    (hnodup : (a :: l).Nodup) (hlen : 2 ≤ l.length) : Cycle (K n) :=
  have hne : l = [] → a ≠ a := fun h => by simp [h] at hlen
  have hch : chain a a l := chain_of_nodup a a l hnodup (List.nodup_cons.mp hnodup).1 hne
  ⟨a, trail a a l hch, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by
    rw [Walk.isPath_def,
      Walk.support_tail_of_not_nil _ (by simp [← Walk.length_eq_zero_iff, trail_length]),
      trail_support]
    exact nodup_append_singleton_of_cons a l hnodup,
    by rw [trail_length]; omega⟩⟩

private lemma mkCycle_length {n : ℕ} (a : Fin n) (l : List (Fin n))
    (hnodup : (a :: l).Nodup) (hlen : 2 ≤ l.length) :
    (mkCycle a l hnodup hlen).length = l.length + 1 :=
  trail_length ..

private lemma mkCycle_edges {n : ℕ} (a : Fin n) (l : List (Fin n))
    (hnodup : (a :: l).Nodup) (hlen : 2 ≤ l.length) :
    (mkCycle a l hnodup hlen).edges = arcs a a l :=
  trail_edges ..

private lemma mem_arcs_ofFn {n m : ℕ} (a b : Fin n) (f : Fin (m + 1) → Fin n) (e : Sym2 (Fin n)) :
    e ∈ arcs a b (List.ofFn f) ↔
      e = s(a, f ⟨0, Nat.zero_lt_succ m⟩) ∨
      e = s(f ⟨m, Nat.lt_succ_self m⟩, b) ∨
      ∃ t : Fin m, e = s(f ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩, f ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩) := by
  induction m generalizing a with
  | zero =>
    simp [List.ofFn_succ, arcs]
  | succ m ih =>
    rw [List.ofFn_succ, arcs, List.mem_cons, ih (f 0) (fun i => f i.succ)]
    constructor
    · rintro (h0 | h1 | hlast | ⟨t, ht⟩)
      · exact Or.inl h0
      · exact Or.inr (Or.inr ⟨⟨0, Nat.zero_lt_succ m⟩, h1⟩)
      · exact Or.inr (Or.inl hlast)
      · exact Or.inr (Or.inr ⟨t.succ, ht⟩)
    · rintro (h0 | hlast | ⟨t, ht⟩)
      · exact Or.inl h0
      · exact Or.inr (Or.inr (Or.inl hlast))
      · revert ht
        refine Fin.cases ?_ ?_ t
        · intro ht
          exact Or.inr (Or.inl ht)
        · intro t' ht
          exact Or.inr (Or.inr (Or.inr ⟨t', ht⟩))

private def step (k t : ℕ) : ℕ :=
  if t = 0 then 0 else if t % 2 = 1 then t / 2 + 1 else 2 * k - t / 2

private def wrap (M u : ℕ) : ℕ :=
  if u < M then u else u - M

private def z (k r t : ℕ) : ℕ :=
  wrap (2 * k) (r + step k t)

private lemma z_lt {k r t : ℕ} (_hk : 2 ≤ k) (hr : r < k) (ht : t < 2 * k) :
    z k r t < 2 * k := by
  dsimp [z, wrap, step]
  split_ifs <;> omega

private lemma z_inj {k r t₁ t₂ : ℕ} (hk : 2 ≤ k) (hr : r < k)
    (ht₁ : t₁ < 2 * k) (ht₂ : t₂ < 2 * k) (heq : z k r t₁ = z k r t₂) :
    t₁ = t₂ := by
  dsimp [z, wrap, step] at heq
  split_ifs at heq <;> omega

private lemma z_zero {k r : ℕ} (hk : 2 ≤ k) (hr : r < k) :
    z k r 0 = r := by
  simp only [z, wrap, step, ↓reduceIte, add_zero]
  split_ifs <;> omega

private lemma z_last {k r : ℕ} (hk : 2 ≤ k) (hr : r < k) :
    z k r (2 * k - 1) = r + k := by
  dsimp [z, wrap, step]
  split_ifs <;> omega

private lemma z_even_pair {k r m : ℕ} (hk : 2 ≤ k) (hr : r < k) (hm : m < k) :
    z k r (2 * m) = wrap (2 * k) (2 * k + r - m) ∧ z k r (2 * m + 1) = r + m + 1 := by
  dsimp [z, wrap, step]
  split_ifs <;> omega

private lemma z_odd_pair {k r m : ℕ} (hk : 2 ≤ k) (hr : r < k) (hm : m + 1 < k) :
    z k r (2 * m + 1) = r + m + 1 ∧ z k r (2 * m + 2) = wrap (2 * k) (2 * k + r - (m + 1)) := by
  dsimp [z, wrap, step]
  split_ifs <;> omega

private lemma circle_edge_forward {k r t x y : ℕ} (hk : 2 ≤ k) (hr : r < k)
    (ht : t < 2 * k - 1)
    (hxy : (z k r t = x ∧ z k r (t + 1) = y) ∨ (z k r t = y ∧ z k r (t + 1) = x)) :
    r = wrap (2 * k) (x + y) / 2 := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · dsimp [z, wrap, step]
    split_ifs <;> omega

private lemma circle_edge_backward_odd {k r x y : ℕ} (hk : 2 ≤ k) (hx : x < 2 * k) (hy : y < 2 * k)
    (_hne : x ≠ y) (hodd : wrap (2 * k) (x + y) % 2 = 1) (hr : r = wrap (2 * k) (x + y) / 2) :
    ∃ t < 2 * k - 1, (z k r t = x ∧ z k r (t + 1) = y) ∨ (z k r t = y ∧ z k r (t + 1) = x) := by
  have hr_lt : r < k := by
    subst hr; dsimp [wrap]; split_ifs <;> omega
  let d1 := wrap (2 * k) (2 * k + r - x)
  let d2 := wrap (2 * k) (2 * k + r - y)
  let m := if d1 < k then d1 else d2
  have hm_prop : m < k ∧ ((wrap (2 * k) (2 * k + r - m) = x ∧ r + m + 1 = y) ∨
      (wrap (2 * k) (2 * k + r - m) = y ∧ r + m + 1 = x)) := by
    subst hr
    dsimp [m, d1, d2, wrap] at hodd ⊢
    split_ifs at hodd ⊢ <;> omega
  obtain ⟨hm, hpair⟩ := hm_prop
  obtain ⟨hz0, hz1⟩ := z_even_pair hk hr_lt hm
  refine ⟨2 * m, by omega, ?_⟩
  rw [hz0, hz1]
  exact hpair

private lemma circle_edge_backward_even {k r x y : ℕ} (hk : 2 ≤ k) (hx : x < 2 * k) (hy : y < 2 * k)
    (hne : x ≠ y) (heven : wrap (2 * k) (x + y) % 2 ≠ 1) (hr : r = wrap (2 * k) (x + y) / 2) :
    ∃ t < 2 * k - 1, (z k r t = x ∧ z k r (t + 1) = y) ∨ (z k r t = y ∧ z k r (t + 1) = x) := by
  have hr_lt : r < k := by
    subst hr; dsimp [wrap]; split_ifs <;> omega
  let u1 := wrap (2 * k) (2 * k + x - r)
  let u2 := wrap (2 * k) (2 * k + y - r)
  let u := if 1 ≤ u1 ∧ u1 < k then u1 else u2
  let m := u - 1
  have hm_prop : m + 1 < k ∧ ((r + m + 1 = x ∧ wrap (2 * k) (2 * k + r - (m + 1)) = y) ∨
      (r + m + 1 = y ∧ wrap (2 * k) (2 * k + r - (m + 1)) = x)) := by
    subst hr
    dsimp [m, u, u1, u2, wrap] at heven ⊢
    split_ifs at heven ⊢ <;> omega
  obtain ⟨hm, hpair⟩ := hm_prop
  obtain ⟨hz1, hz2⟩ := z_odd_pair hk hr_lt hm
  refine ⟨2 * m + 1, by omega, ?_⟩
  have h2m : 2 * m + 1 + 1 = 2 * m + 2 := by omega
  rw [h2m, hz1, hz2]
  exact hpair

private lemma circle_edge_iff {k r x y : ℕ} (hk : 2 ≤ k) (hr : r < k)
    (hx : x < 2 * k) (hy : y < 2 * k) (hne : x ≠ y) :
    (∃ t < 2 * k - 1, (z k r t = x ∧ z k r (t + 1) = y) ∨ (z k r t = y ∧ z k r (t + 1) = x)) ↔
      r = wrap (2 * k) (x + y) / 2 := by
  constructor
  · rintro ⟨t, ht, hxy⟩
    exact circle_edge_forward hk hr ht hxy
  · intro hr_eq
    by_cases hodd : wrap (2 * k) (x + y) % 2 = 1
    · exact circle_edge_backward_odd hk hx hy hne hodd hr_eq
    · exact circle_edge_backward_even hk hx hy hne hodd hr_eq

private def hub (k : ℕ) : Fin (2 * k + 1) := ⟨2 * k, by omega⟩

private def cVert {k : ℕ} (hk : 2 ≤ k) (r : Fin k) (i : Fin (2 * k)) : Fin (2 * k + 1) :=
  ⟨z k r.val i.val, Nat.lt_succ_of_lt (z_lt hk r.isLt i.isLt)⟩

private lemma cVert_inj {k : ℕ} (hk : 2 ≤ k) (r : Fin k) : Function.Injective (cVert hk r) := by
  intro i j hij
  ext
  exact z_inj hk r.isLt i.isLt j.isLt (congrArg Fin.val hij)

private lemma nodup_hub_cVert {k : ℕ} (hk : 2 ≤ k) (r : Fin k) :
    (hub k :: List.ofFn (cVert hk r)).Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, List.nodup_ofFn.mpr (cVert_inj hk r)⟩
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  have hlt : (cVert hk r i).val < 2 * k := z_lt hk r.isLt i.isLt
  rw [hi] at hlt
  exact Nat.lt_irrefl (2 * k) hlt

private def wCycle {k : ℕ} (hk : 2 ≤ k) (r : Fin k) : Cycle (K (2 * k + 1)) :=
  mkCycle (hub k) (List.ofFn (cVert hk r)) (nodup_hub_cVert hk r) (by simp; omega)

private lemma wCycle_length {k : ℕ} (hk : 2 ≤ k) (r : Fin k) :
    (wCycle hk r).length = 2 * k + 1 := by
  rw [wCycle, mkCycle_length]
  simp

private def edgeOwner {k : ℕ} (_hk : 2 ≤ k) (a b : Fin (2 * k + 1)) (hab : a ≠ b) : Fin k :=
  if ha : a.val = 2 * k then
    ⟨wrap k b.val, by
      have hb : b.val < 2 * k := by have := b.isLt; have := Fin.val_ne_of_ne hab; omega
      dsimp [wrap]; split_ifs <;> omega⟩
  else if hb : b.val = 2 * k then
    ⟨wrap k a.val, by
      have ha' : a.val < 2 * k := by have := a.isLt; omega
      dsimp [wrap]; split_ifs <;> omega⟩
  else
    ⟨wrap (2 * k) (a.val + b.val) / 2, by
      have ha' : a.val < 2 * k := by have := a.isLt; omega
      have hb' : b.val < 2 * k := by have := b.isLt; omega
      dsimp [wrap]; split_ifs <;> omega⟩

private lemma mem_wCycle_edges_pair {k : ℕ} (hk : 2 ≤ k) (r : Fin k)
    (a b : Fin (2 * k + 1)) (hab : a ≠ b) :
    s(a, b) ∈ (wCycle hk r).edges ↔ r = edgeOwner hk a b hab := by
  have hm : 2 * k - 1 + 1 = 2 * k := by omega
  let f : Fin (2 * k - 1 + 1) → Fin (2 * k + 1) := fun i => cVert hk r ⟨i.val, by omega⟩
  have hofFn : List.ofFn (cVert hk r) = List.ofFn f := by
    apply List.ext_getElem
    · simp [hm]
    · intro i hi₁ hi₂
      rw [List.getElem_ofFn, List.getElem_ofFn]
  rw [wCycle, mkCycle_edges, hofFn, mem_arcs_ofFn]
  have hf0 : (f ⟨0, Nat.zero_lt_succ _⟩).val = r.val := z_zero hk r.isLt
  have hflast : (f ⟨2 * k - 1, Nat.lt_succ_self _⟩).val = r.val + k := z_last hk r.isLt
  have hflt : ∀ i : Fin (2 * k - 1 + 1), (f i).val < 2 * k := fun i => z_lt hk r.isLt (by omega)
  have hval_ne : a.val ≠ b.val := Fin.val_ne_of_ne hab
  by_cases ha : a.val = 2 * k
  · have hb_lt : b.val < 2 * k := by have := b.isLt; omega
    have howner : (edgeOwner hk a b hab).val = wrap k b.val := by simp [edgeOwner, ha]
    rw [Fin.ext_iff, howner]
    constructor
    · rintro (h0 | hlast | ⟨t, ht⟩)
      · rw [Sym2.eq_iff] at h0
        rcases h0 with ⟨_, hbf⟩ | ⟨haf, _⟩
        · have : b.val = r.val := (congrArg Fin.val hbf).trans hf0
          have hr : r.val < k := r.isLt
          dsimp [wrap]; split_ifs <;> omega
        · have := hflt ⟨0, Nat.zero_lt_succ _⟩
          have : a.val = (f ⟨0, Nat.zero_lt_succ _⟩).val := congrArg Fin.val haf
          omega
      · rw [Sym2.eq_iff] at hlast
        rcases hlast with ⟨haf, _⟩ | ⟨_, hbf⟩
        · have := hflt ⟨2 * k - 1, Nat.lt_succ_self _⟩
          have : a.val = (f ⟨2 * k - 1, Nat.lt_succ_self _⟩).val := congrArg Fin.val haf
          omega
        · have : b.val = r.val + k := (congrArg Fin.val hbf).trans hflast
          have hr : r.val < k := r.isLt
          dsimp [wrap]; split_ifs <;> omega
      · rw [Sym2.eq_iff] at ht
        rcases ht with ⟨haf, _⟩ | ⟨haf, _⟩
        · have := hflt ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩
          have : a.val = (f ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩).val := congrArg Fin.val haf
          omega
        · have := hflt ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩
          have : a.val = (f ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩).val := congrArg Fin.val haf
          omega
    · intro hr_eq
      have ha_hub : a = hub k := Fin.ext ha
      by_cases hbk : b.val < k
      · left
        rw [ha_hub, Sym2.eq_iff]
        left
        refine ⟨rfl, Fin.ext ?_⟩
        rw [hf0]
        dsimp [wrap] at hr_eq
        split_ifs at hr_eq <;> omega
      · right; left
        rw [ha_hub, Sym2.eq_iff]
        right
        refine ⟨rfl, Fin.ext ?_⟩
        rw [hflast]
        dsimp [wrap] at hr_eq
        split_ifs at hr_eq <;> omega
  · by_cases hb : b.val = 2 * k
    · have ha_lt : a.val < 2 * k := by have := a.isLt; omega
      have howner : (edgeOwner hk a b hab).val = wrap k a.val := by simp [edgeOwner, ha, hb]
      rw [Fin.ext_iff, howner]
      constructor
      · rintro (h0 | hlast | ⟨t, ht⟩)
        · rw [Sym2.eq_iff] at h0
          rcases h0 with ⟨_, hbf⟩ | ⟨haf, _⟩
          · have := hflt ⟨0, Nat.zero_lt_succ _⟩
            have : b.val = (f ⟨0, Nat.zero_lt_succ _⟩).val := congrArg Fin.val hbf
            omega
          · have : a.val = r.val := (congrArg Fin.val haf).trans hf0
            have hr : r.val < k := r.isLt
            dsimp [wrap]; split_ifs <;> omega
        · rw [Sym2.eq_iff] at hlast
          rcases hlast with ⟨haf, _⟩ | ⟨_, hbf⟩
          · have : a.val = r.val + k := (congrArg Fin.val haf).trans hflast
            have hr : r.val < k := r.isLt
            dsimp [wrap]; split_ifs <;> omega
          · have := hflt ⟨2 * k - 1, Nat.lt_succ_self _⟩
            have : b.val = (f ⟨2 * k - 1, Nat.lt_succ_self _⟩).val := congrArg Fin.val hbf
            omega
        · rw [Sym2.eq_iff] at ht
          rcases ht with ⟨_, hbf⟩ | ⟨_, hbf⟩
          · have := hflt ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩
            have : b.val = (f ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩).val := congrArg Fin.val hbf
            omega
          · have := hflt ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩
            have : b.val = (f ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩).val := congrArg Fin.val hbf
            omega
      · intro hr_eq
        have hb_hub : b = hub k := Fin.ext hb
        by_cases hak : a.val < k
        · left
          rw [hb_hub, Sym2.eq_iff]
          right
          refine ⟨Fin.ext ?_, rfl⟩
          rw [hf0]
          dsimp [wrap] at hr_eq
          split_ifs at hr_eq <;> omega
        · right; left
          rw [hb_hub, Sym2.eq_iff]
          left
          refine ⟨Fin.ext ?_, rfl⟩
          rw [hflast]
          dsimp [wrap] at hr_eq
          split_ifs at hr_eq <;> omega
    · have ha_lt : a.val < 2 * k := by have := a.isLt; omega
      have hb_lt : b.val < 2 * k := by have := b.isLt; omega
      have howner : (edgeOwner hk a b hab).val = wrap (2 * k) (a.val + b.val) / 2 := by
        simp [edgeOwner, ha, hb]
      rw [Fin.ext_iff, howner, ← circle_edge_iff hk r.isLt ha_lt hb_lt hval_ne]
      constructor
      · rintro (h0 | hlast | ⟨t, ht⟩)
        · rw [Sym2.eq_iff] at h0
          rcases h0 with ⟨hah, _⟩ | ⟨_, hbh⟩
          · exact False.elim (ha (congrArg Fin.val hah))
          · exact False.elim (hb (congrArg Fin.val hbh))
        · rw [Sym2.eq_iff] at hlast
          rcases hlast with ⟨_, hbh⟩ | ⟨hah, _⟩
          · exact False.elim (hb (congrArg Fin.val hbh))
          · exact False.elim (ha (congrArg Fin.val hah))
        · refine ⟨t.val, t.isLt, ?_⟩
          rw [Sym2.eq_iff] at ht
          rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨(congrArg Fin.val h1).symm, (congrArg Fin.val h2).symm⟩
          · exact Or.inr ⟨(congrArg Fin.val h2).symm, (congrArg Fin.val h1).symm⟩
      · rintro ⟨t, ht, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · right; right
          refine ⟨⟨t, ht⟩, ?_⟩
          rw [Sym2.eq_iff]
          exact Or.inl ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩
        · right; right
          refine ⟨⟨t, ht⟩, ?_⟩
          rw [Sym2.eq_iff]
          exact Or.inr ⟨Fin.ext h2.symm, Fin.ext h1.symm⟩

end OMA.WaleckiLong

theorem OMA.solution : OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1.H1 := by
  intro n hn h5 m hm hsum
  rcases hn with ⟨k, rfl⟩
  have hk : 2 ≤ k := by omega
  have hm_rep : m = Multiset.replicate m.card (2 * k + 1) := by
    rw [Multiset.eq_replicate]
    exact ⟨rfl, fun x hx => hm x hx⟩
  have hchoose : (2 * k + 1).choose 2 = (2 * k + 1) * k := by
    rw [Nat.choose_two_right]
    have hmul : (2 * k + 1) * (2 * k + 1 - 1) = (2 * k + 1) * k * 2 := by
      have hsub : 2 * k + 1 - 1 = 2 * k := by omega
      rw [hsub]
      ring
    rw [hmul, Nat.mul_div_cancel _ (by omega)]
  have hcard : m.card = k := by
    have hsum' := hsum
    rw [hm_rep, Multiset.sum_replicate, smul_eq_mul, hchoose] at hsum'
    nlinarith
  let C : Multiset (SimpleGraph.Cycle (SimpleGraph.completeGraph (Fin (2 * k + 1)))) :=
    (Finset.univ : Finset (Fin k)).val.map (OMA.WaleckiLong.wCycle hk)
  refine ⟨C, ?_, ?_⟩
  · intro e he
    have he' : e ∈ (SimpleGraph.completeGraph (Fin (2 * k + 1))).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp he
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := by
        rwa [SimpleGraph.mem_edgeSet, SimpleGraph.completeGraph_eq_top, SimpleGraph.top_adj] at he'
      dsimp only [C]
      rw [Multiset.filter_map, Multiset.card_map]
      change ((Finset.univ : Finset (Fin k)).filter
        (fun r => s(a, b) ∈ (OMA.WaleckiLong.wCycle hk r).edges)).card = 1
      have hfilt : (Finset.univ : Finset (Fin k)).filter
          (fun r => s(a, b) ∈ (OMA.WaleckiLong.wCycle hk r).edges) =
          {OMA.WaleckiLong.edgeOwner hk a b hab} := by
        ext r
        simp [OMA.WaleckiLong.mem_wCycle_edges_pair hk r a b hab]
      rw [hfilt, Finset.card_singleton]
  · rw [hm_rep, hcard]
    dsimp [AlspachConjecture.lengths, C]
    rw [Multiset.map_map]
    have hconst : (SimpleGraph.Cycle.length ∘ OMA.WaleckiLong.wCycle hk) =
        Function.const (Fin k) (2 * k + 1) := by
      funext r
      exact OMA.WaleckiLong.wCycle_length hk r
    rw [hconst, Multiset.map_const]
    simp
