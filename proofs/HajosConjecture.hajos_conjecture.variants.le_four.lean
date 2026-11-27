import FormalConjectures.Wikipedia.HajosConjecture

-- Problem: Hajós' conjecture for k ≤ 4 (Dirac 1952)
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/HajosConjecture.lean (declaration HajosConjecture.hajos_conjecture.variants.le_four)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Reference: G. A. Dirac, A property of 4-chromatic graphs and some remarks on critical graphs (1952).

/-!
# Hajós' conjecture for `k ≤ 4`

A graph that is not `(k - 1)`-colourable contains a nonempty vertex set `S` in which every vertex
has at least `k - 1` neighbours (otherwise greedy colouring works).  For `k = 3` a longest path in
`S` together with a second neighbour of its first vertex gives a cycle.  For `k = 4` we take a
longest path `p 0, …, p M` in `S` for which the second neighbour index `b` of `p 0` is minimal.
Flipping the path along the chord `p 0 p b` shows that `p (b - 1)` has a neighbour `p j` with
`j > b`; with a third neighbour `p c` (`c > b`) of `p 0` this yields a subdivided `K₄` with branch
vertices `p 0`, `p (b - 1)`, `p b`, `p (min j c)`.
-/

open SimpleGraph


namespace HajosFleet
open HajosConjecture
variable {V : Type} {G : SimpleGraph V}

/-- A walk along the list `(range n).map (p ∘ g)` starting from `u`. -/
lemma exists_walk_map (p : ℕ → V) : ∀ (n : ℕ) (g : ℕ → ℕ) (u : V),
    (0 < n → G.Adj u (p (g 0))) → (∀ t, t + 1 < n → G.Adj (p (g t)) (p (g (t + 1)))) →
    ∃ q : G.Walk u (if n = 0 then u else p (g (n - 1))),
      q.support = u :: (List.range n).map (fun t => p (g t))
  | 0, g, u, _, _ => ⟨Walk.nil, by simp⟩
  | n + 1, g, u, h0, hs => by
    obtain ⟨q, hq⟩ := exists_walk_map p n (fun t => g (t + 1)) (p (g 0))
      (fun hn => hs 0 (by omega)) (fun t ht => hs (t + 1) (by omega))
    refine ⟨Walk.cons (h0 (by omega)) (q.copy rfl ?_), ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [if_neg (by omega)]
        congr 2; omega
    · simp only [Walk.support_cons, Walk.support_copy, hq, List.range_succ_eq_map,
        List.map_cons, List.map_map]
      rfl

lemma mem_dropLast_map (p : ℕ → V) (n : ℕ) (g : ℕ → ℕ) (x : V)
    (hx : x ∈ ((List.range n).map (fun t => p (g t))).dropLast) :
    ∃ t, t + 1 < n ∧ p (g t) = x := by
  rcases n with _ | n
  · simp at hx
  rw [List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat] at hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, by omega, rfl⟩

lemma mem_rev_dropLast {l : List V} {x : V} :
    x ∈ l.reverse.tail.dropLast ↔ x ∈ l.tail.dropLast := by
  rw [List.tail_reverse, List.dropLast_reverse, List.mem_reverse]
  rcases l with _ | ⟨a, l⟩
  · simp
  · simp only [List.tail_cons]
    rcases l.eq_nil_or_concat with rfl | ⟨l', b, rfl⟩
    · simp
    · rw [List.concat_eq_append, ← List.cons_append, List.dropLast_concat, List.dropLast_concat,
        List.tail_cons]

/-- Build a subdivision of `K_k` from index data along a path `p`. -/
lemma tk_of_indices (k m : ℕ) (p : ℕ → V) (hinj : Set.InjOn p (Set.Iic m))
    (h : Fin k → ℕ) (N : Fin k → Fin k → ℕ) (Gf : Fin k → Fin k → ℕ → ℕ)
    (hh : Function.Injective h) (hhm : ∀ i, h i ≤ m)
    (hN : ∀ i j, i < j → 1 ≤ N i j)
    (hlast : ∀ i j, i < j → Gf i j (N i j - 1) = h j)
    (hbd : ∀ i j, i < j → ∀ t < N i j, Gf i j t ≤ m)
    (hne : ∀ i j, i < j → ∀ t < N i j, Gf i j t ≠ h i)
    (hgi : ∀ i j, i < j → ∀ t < N i j, ∀ t' < N i j, Gf i j t = Gf i j t' → t = t')
    (hadj0 : ∀ i j, i < j → G.Adj (p (h i)) (p (Gf i j 0)))
    (hadjs : ∀ i j, i < j → ∀ t, t + 1 < N i j → G.Adj (p (Gf i j t)) (p (Gf i j (t + 1))))
    (havoid : ∀ i j, i < j → ∀ t, t + 1 < N i j → ∀ l, Gf i j t ≠ h l)
    (hdisj : ∀ i j i' j', i < j → i' < j' → (i, j) ≠ (i', j') →
      ∀ t, t + 1 < N i j → ∀ t', t' + 1 < N i' j' → Gf i j t ≠ Gf i' j' t') :
    ContainsSubdivision (completeGraph (Fin k)) G := by
  have key : ∀ i j, i < j → ∃ q : G.Walk (p (h i)) (p (h j)),
      q.support = p (h i) :: (List.range (N i j)).map (fun t => p (Gf i j t)) := by
    intro i j hij
    obtain ⟨q, hq⟩ := exists_walk_map (G := G) p (N i j) (Gf i j) (p (h i))
      (fun _ => hadj0 i j hij) (hadjs i j hij)
    refine ⟨q.copy rfl ?_, by rw [Walk.support_copy, hq]⟩
    rw [if_neg (by have := hN i j hij; omega), hlast i j hij]
  choose W hW using key
  -- interior membership
  have hint : ∀ i j (hij : i < j) x, x ∈ (W i j hij).support.tail.dropLast →
      ∃ t, t + 1 < N i j ∧ p (Gf i j t) = x := by
    intro i j hij x hx
    rw [hW, List.tail_cons] at hx
    exact mem_dropLast_map p _ _ x hx
  let P : ∀ w w', (completeGraph (Fin k)).Adj w w' → G.Walk (p (h w)) (p (h w')) :=
    fun w w' hw => if hlt : w < w' then W w w' hlt
      else (W w' w (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hw))).reverse
  -- interior of P in terms of the ordered pair
  have hPint : ∀ w w' hw x, x ∈ (P w w' hw).support.tail.dropLast →
      ∃ i j, ∃ hij : i < j, s(w, w') = s(i, j) ∧ x ∈ (W i j hij).support.tail.dropLast := by
    intro w w' hw x hx
    by_cases hlt : w < w'
    · refine ⟨w, w', hlt, rfl, ?_⟩
      simpa [P, hlt] using hx
    · have h2 : w' < w := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hw)
      refine ⟨w', w, h2, Sym2.eq_swap, ?_⟩
      simp only [P, hlt, ↓reduceDIte, Walk.support_reverse] at hx
      exact mem_rev_dropLast.mp hx
  refine ⟨fun i => p (h i), P, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    exact hh (hinj (hhm i) (hhm j) hij)
  · intro w w' hw
    have hpath : ∀ i j (hij : i < j), (W i j hij).IsPath := by
      intro i j hij
      rw [Walk.isPath_def, hW, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_map, List.mem_range, not_exists, not_and]
        intro t ht he
        exact hne i j hij t ht (hinj (hbd i j hij t ht) (hhm i) he)
      · refine List.Nodup.map_on ?_ List.nodup_range
        intro t ht t' ht' he
        simp only [List.mem_range] at ht ht'
        exact hgi i j hij t ht t' ht' (hinj (hbd i j hij t ht) (hbd i j hij t' ht') he)
    by_cases hlt : w < w'
    · simpa [P, hlt] using hpath w w' hlt
    · simp only [P, hlt, ↓reduceDIte]
      exact (hpath _ _ _).reverse
  · intro w w' hw x hx
    obtain ⟨i, j, hij, -, hx⟩ := hPint w w' hw x hx
    obtain ⟨t, ht, rfl⟩ := hint i j hij x hx
    rintro ⟨l, hl⟩
    exact havoid i j hij t ht l (hinj (hbd i j hij t (by omega)) (hhm l) hl.symm)
  · intro w₁ w₁' h₁ w₂ w₂' h₂ hs x hx1 hx2
    obtain ⟨i, j, hij, hs1, hx1⟩ := hPint _ _ h₁ x hx1
    obtain ⟨i', j', hij', hs2, hx2⟩ := hPint _ _ h₂ x hx2
    obtain ⟨t, ht, rfl⟩ := hint i j hij _ hx1
    obtain ⟨t', ht', he⟩ := hint i' j' hij' _ hx2
    have hpair : (i, j) ≠ (i', j') := by
      rintro ⟨⟩; exact hs (hs1.trans hs2.symm)
    exact hdisj i j i' j' hij hij' hpair t ht t' ht'
      (hinj (hbd i j hij t (by omega)) (hbd i' j' hij' t' (by omega)) he.symm)


section Color
variable [Fintype V]
open Classical in
lemma color_of_sparse (r : ℕ) (hr : 0 < r) : ∀ S : Finset V,
    (∀ T ⊆ S, T.Nonempty → ∃ v ∈ T, (T.filter (G.Adj v)).card < r) →
    ∃ c : V → Fin r, ∀ u ∈ S, ∀ w ∈ S, G.Adj u w → c u ≠ c w := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => ⟨0, hr⟩, by simp⟩
    obtain ⟨v, hvS, hv⟩ := hS S subset_rfl hne
    obtain ⟨c, hc⟩ := ih (S.erase v) (Finset.erase_ssubset hvS)
      (fun T hT hTne => hS T (hT.trans (Finset.erase_subset _ _)) hTne)
    have hlt : ((S.filter (G.Adj v)).image c).card < (Finset.univ : Finset (Fin r)).card := by
      calc _ ≤ (S.filter (G.Adj v)).card := Finset.card_image_le
        _ < r := hv
        _ = _ := by simp
    obtain ⟨col, -, hcol⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨Function.update c v col, ?_⟩
    intro u hu w hw huw
    by_cases huv : u = v
    · subst huv
      have hwv : w ≠ u := (G.ne_of_adj huw).symm
      rw [Function.update_self, Function.update_of_ne hwv]
      intro h; apply hcol; rw [h]
      exact Finset.mem_image_of_mem _ (by simp [hw, huw])
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self, Function.update_of_ne huv]
      intro h; apply hcol; rw [← h]
      exact Finset.mem_image_of_mem _ (by simp [hu, huw.symm])
    rw [Function.update_of_ne huv, Function.update_of_ne hwv]
    exact hc u (by simp [hu, huv]) w (by simp [hw, hwv]) huw

open Classical in
lemma exists_dense (r : ℕ) (h : ¬ G.Colorable r) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, r ≤ (S.filter (G.Adj v)).card := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨Finset.univ, ?_, by simp⟩
    by_contra hne
    rw [Finset.univ_nonempty_iff, not_nonempty_iff] at hne
    exact h ⟨Coloring.mk (fun v => isEmptyElim v) (fun {v} => isEmptyElim v)⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := color_of_sparse (G := G) r hr Finset.univ
    (fun T _ hT => by
      obtain ⟨v, hv, hlt⟩ := hcon T hT
      exact ⟨v, hv, hlt⟩)
  exact h ⟨Coloring.mk c (fun {u w} huw => hc u (by simp) w (by simp) huw)⟩

lemma not_colorable_of_le {k r : ℕ} (h : (k : ℕ∞) ≤ G.chromaticNumber) (hr : r < k) :
    ¬ G.Colorable r := by
  intro hc
  have := hc.chromaticNumber_le
  have : (k : ℕ∞) ≤ r := h.trans this
  exact absurd (by exact_mod_cast this) (not_le.mpr hr)


end Color

section Paths
variable [Fintype V]
open Classical

/-- `p 0, …, p m` is a path of `G` inside `S`. -/
def IsPathIn (G : SimpleGraph V) (S : Finset V) (p : ℕ → V) (m : ℕ) : Prop :=
  Set.InjOn p (Set.Iic m) ∧ (∀ t < m, G.Adj (p t) (p (t + 1))) ∧ ∀ t ≤ m, p t ∈ S

lemma IsPathIn.le_card {S : Finset V} {p : ℕ → V} {m : ℕ} (hp : IsPathIn G S p m) :
    m ≤ Fintype.card V := by
  have h1 : ((Finset.range (m + 1)).image p).card = m + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    exact hp.1 (by simp only [Set.mem_Iic]; omega) (by simp only [Set.mem_Iic]; omega) hab
  have h2 := Finset.card_le_univ ((Finset.range (m + 1)).image p)
  omega

lemma IsPathIn.extend {S : Finset V} {p : ℕ → V} {m : ℕ} {u : V} (hp : IsPathIn G S p m)
    (hu : u ∈ S) (hadj : G.Adj u (p 0)) (hnot : ∀ t ≤ m, p t ≠ u) :
    IsPathIn G S (fun t => if t = 0 then u else p (t - 1)) (m + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_Iic] at ha hb
    simp only at hab
    split_ifs at hab with h1 h2 h2
    · omega
    · exact absurd hab.symm (hnot _ (by omega))
    · exact absurd hab (hnot _ (by omega))
    · have := hp.1 (show a - 1 ∈ Set.Iic m by simp only [Set.mem_Iic]; omega)
        (show b - 1 ∈ Set.Iic m by simp only [Set.mem_Iic]; omega) hab
      omega
  · intro t ht
    rcases t with _ | t
    · simpa using hadj
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact hp.2.1 t (by omega)
  · intro t ht
    simp only
    split_ifs with h
    · exact hu
    · exact hp.2.2 _ (by omega)

lemma exists_longest (S : Finset V) (hS : S.Nonempty) :
    ∃ M p, IsPathIn G S p M ∧ ∀ m q, IsPathIn G S q m → m ≤ M := by
  obtain ⟨v, hv⟩ := hS
  let P : ℕ → Prop := fun m => ∃ p, IsPathIn G S p m
  have h0 : P 0 := ⟨fun _ => v, by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb _
      simp only [Set.mem_Iic] at ha hb
      omega
    · intro t ht; omega
    · intro t _; exact hv⟩
  obtain ⟨p, hp⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le (Fintype.card V)) h0
  exact ⟨_, p, hp, fun m q hq => Nat.le_findGreatest hq.le_card ⟨q, hq⟩⟩

lemma nbr_mem {S : Finset V} {p : ℕ → V} {M : ℕ} (hp : IsPathIn G S p M)
    (hmax : ∀ m q, IsPathIn G S q m → m ≤ M) {u : V} (hu : u ∈ S) (hadj : G.Adj (p 0) u) :
    ∃ t ≤ M, p t = u := by
  by_contra hcon
  push Not at hcon
  have := hmax _ _ (hp.extend hu hadj.symm (fun t ht => hcon t ht))
  omega

lemma IsPathIn.flip {S : Finset V} {p : ℕ → V} {m b : ℕ} (hp : IsPathIn G S p m)
    (hb1 : 1 ≤ b) (hbm : b ≤ m) (hadj : G.Adj (p 0) (p b)) :
    IsPathIn G S (fun i => if i < b then p (b - 1 - i) else p i) m := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Iic] at hx hy
    simp only at hxy
    split_ifs at hxy with h1 h2 h2
    · have := hp.1 (show b - 1 - x ∈ Set.Iic m by simp only [Set.mem_Iic]; omega)
        (show b - 1 - y ∈ Set.Iic m by simp only [Set.mem_Iic]; omega) hxy
      omega
    · have := hp.1 (show b - 1 - x ∈ Set.Iic m by simp only [Set.mem_Iic]; omega)
        (show y ∈ Set.Iic m by simp only [Set.mem_Iic]; omega) hxy
      omega
    · have := hp.1 (show x ∈ Set.Iic m by simp only [Set.mem_Iic]; omega)
        (show b - 1 - y ∈ Set.Iic m by simp only [Set.mem_Iic]; omega) hxy
      omega
    · exact hp.1 (show x ∈ Set.Iic m by simp only [Set.mem_Iic]; omega)
        (show y ∈ Set.Iic m by simp only [Set.mem_Iic]; omega) hxy
  · intro t ht
    simp only
    by_cases h1 : t + 1 < b
    · rw [if_pos (by omega), if_pos h1]
      have := hp.2.1 (b - 1 - (t + 1)) (by omega)
      rw [show b - 1 - (t + 1) + 1 = b - 1 - t by omega] at this
      exact this.symm
    · by_cases h2 : t + 1 = b
      · rw [if_pos (by omega), if_neg (by omega), show b - 1 - t = 0 by omega, h2]
        exact hadj
      · rw [if_neg (by omega), if_neg (by omega)]
        exact hp.2.1 t ht
  · intro t ht
    simp only
    split_ifs
    · exact hp.2.2 _ (by omega)
    · exact hp.2.2 _ ht

lemma exists_nbr_not_mem {S : Finset V} {v : V} {r : ℕ}
    (hdeg : r ≤ (S.filter (G.Adj v)).card) (E : Finset V) (hE : E.card < r) :
    ∃ u ∈ S, G.Adj v u ∧ u ∉ E := by
  have : 0 < ((S.filter (G.Adj v)) \ E).card := by
    have := Finset.le_card_sdiff E (S.filter (G.Adj v))
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp this
  simp only [Finset.mem_sdiff, Finset.mem_filter] at hu
  exact ⟨u, hu.1.1, hu.1.2, hu.2⟩

lemma tk3 {S : Finset V} (hS : S.Nonempty) (hdeg : ∀ v ∈ S, 2 ≤ (S.filter (G.Adj v)).card) :
    ContainsSubdivision (completeGraph (Fin 3)) G := by
  obtain ⟨M, p, hp, hmax⟩ := exists_longest (G := G) S hS
  obtain ⟨u, huS, hadj, hu1⟩ :=
    exists_nbr_not_mem (hdeg (p 0) (hp.2.2 0 (Nat.zero_le _))) {p 1} (by simp)
  obtain ⟨c, hcM, rfl⟩ := nbr_mem hp hmax huS hadj
  have hc0 : c ≠ 0 := by rintro rfl; exact G.irrefl hadj
  have hc1 : c ≠ 1 := by rintro rfl; simp at hu1
  have hstep : ∀ s t, s + 1 ≤ M → t = s + 1 → G.Adj (p s) (p t) := by
    rintro s t hs rfl; exact hp.2.1 s (by omega)
  refine tk_of_indices 3 M p hp.1 ![0, 1, c] ![![0, 1, 1], ![0, 0, c - 1], ![0, 0, 0]]
    ![![fun _ => 0, fun t => 1 + t, fun _ => c], ![fun _ => 0, fun _ => 0, fun t => 2 + t],
      ![fun _ => 0, fun _ => 0, fun _ => 0]] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht) <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht) <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht t' ht' h) <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      first | exact hadj | exact hstep _ _ (by omega) (by omega)
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht) <;> first | omega | exact hstep _ _ (by omega) (by omega)
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht l) <;> (try fin_cases l) <;> simp <;> omega
  · intro i j i' j' hij hij' hne; fin_cases i <;> fin_cases j <;> fin_cases i' <;>
      fin_cases j' <;> (try simp at hij) <;> (try simp at hij') <;> (try simp at hne) <;>
      simp <;> (try intro t ht t' ht') <;> omega

set_option maxHeartbeats 2000000 in
lemma tk4 {S : Finset V} (hS : S.Nonempty) (hdeg : ∀ v ∈ S, 3 ≤ (S.filter (G.Adj v)).card) :
    ContainsSubdivision (completeGraph (Fin 4)) G := by
  obtain ⟨M, p₀, hp₀, hmax⟩ := exists_longest (G := G) S hS
  let B : ℕ → Prop := fun n => ∃ q, IsPathIn G S q M ∧ 2 ≤ n ∧ n ≤ M ∧ G.Adj (q 0) (q n)
  have hB : ∃ n, B n := by
    obtain ⟨u, huS, hadj, hu1⟩ :=
      exists_nbr_not_mem (hdeg (p₀ 0) (hp₀.2.2 0 (Nat.zero_le _))) {p₀ 1} (by simp)
    obtain ⟨c, hcM, rfl⟩ := nbr_mem hp₀ hmax huS hadj
    have hc0 : c ≠ 0 := by rintro rfl; exact G.irrefl hadj
    have hc1 : c ≠ 1 := by rintro rfl; simp at hu1
    exact ⟨c, p₀, hp₀, by omega, hcM, hadj⟩
  have hmin : ∀ n, B n → Nat.find hB ≤ n := fun n hn => Nat.find_min' hB hn
  obtain ⟨p, hp, hb2, hbM, hpb⟩ := Nat.find_spec hB
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.find hB := ⟨_, rfl⟩
  rw [← hb] at hb2 hbM hpb hmin
  -- a third neighbour of `p 0`
  obtain ⟨u, huS, hpc, huE⟩ := exists_nbr_not_mem (hdeg (p 0) (hp.2.2 0 (Nat.zero_le _)))
    {p 1, p b} ((Finset.card_le_two).trans_lt (by norm_num))
  obtain ⟨c, hcM, rfl⟩ := nbr_mem hp hmax huS hpc
  have hc0 : c ≠ 0 := by rintro rfl; exact G.irrefl hpc
  have hc1 : c ≠ 1 := by rintro rfl; simp at huE
  have hcb : c ≠ b := by rintro rfl; simp at huE
  have hbc : b < c := lt_of_le_of_ne (hmin c ⟨p, hp, by omega, hcM, hpc⟩) (Ne.symm hcb)
  -- the flipped path starting at `p (b - 1)`
  have hq := hp.flip (b := b) (by omega) hbM hpb
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ → V, q = fun i => if i < b then p (b - 1 - i) else p i :=
    ⟨_, rfl⟩
  rw [← hqdef] at hq
  have hq0 : q 0 = p (b - 1) := by rw [hqdef]; simp only [if_pos (show 0 < b by omega)]; rfl
  have hq1 : q 1 = p (b - 2) := by
    rw [hqdef]; simp only [if_pos (show 1 < b by omega)]; congr 1
  have hqge : ∀ i, b ≤ i → q i = p i := by
    intro i hi; rw [hqdef]; simp only [if_neg (show ¬ i < b by omega)]
  obtain ⟨u, huS, hqa, huE⟩ := exists_nbr_not_mem (hdeg (q 0) (hq.2.2 0 (Nat.zero_le _)))
    {q 1, q b} ((Finset.card_le_two).trans_lt (by norm_num))
  obtain ⟨s, hsM, rfl⟩ := nbr_mem hq hmax huS hqa
  have hs0 : s ≠ 0 := by rintro rfl; exact G.irrefl hqa
  have hs1 : s ≠ 1 := by rintro rfl; simp at huE
  have hsb' : s ≠ b := by rintro rfl; simp at huE
  have hsb : b < s := by
    by_contra hcon
    have := hmin s ⟨q, hq, by omega, hsM, hqa⟩
    omega
  have hpj : G.Adj (p (b - 1)) (p s) := by rw [← hq0, ← hqge s hsb.le]; exact hqa
  obtain ⟨d, hd⟩ : ∃ d, d = min s c := ⟨_, rfl⟩
  have hstep : ∀ x y, x + 1 ≤ M → y = x + 1 → G.Adj (p x) (p y) := by
    rintro x y hx rfl; exact hp.2.1 x (by omega)
  have hstep' : ∀ x y, y + 1 ≤ M → x = y + 1 → G.Adj (p x) (p y) := by
    rintro x y hy rfl; exact (hp.2.1 y (by omega)).symm
  refine tk_of_indices 4 M p hp.1 ![0, b - 1, b, d]
    ![![0, b - 1, 1, c - d + 1], ![0, 0, 1, s - d + 1], ![0, 0, 0, d - b], ![0, 0, 0, 0]]
    ![![fun _ => 0, fun t => 1 + t, fun _ => b, fun t => c - t],
      ![fun _ => 0, fun _ => 0, fun _ => b, fun t => s - t],
      ![fun _ => 0, fun _ => 0, fun _ => 0, fun t => b + 1 + t],
      ![fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0]] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;> omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht) <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht) <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht t' ht' h) <;> omega
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      first | exact hpb | exact hpc | exact hpj | exact hstep _ _ (by omega) (by omega)
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht) <;>
      first | omega | exact hstep _ _ (by omega) (by omega) | exact hstep' _ _ (by omega) (by omega)
  · intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
      (try intro t ht l) <;> (try fin_cases l) <;> simp <;> omega
  · intro i j i' j' hij hij' hne
    fin_cases i <;> fin_cases j <;> (try simp at hij) <;> fin_cases i' <;> fin_cases j' <;>
      (try simp at hij') <;> (try simp at hne) <;>
      simp <;> (try intro t ht t' ht') <;> omega

theorem le_four (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4)
    (h : (k : ℕ∞) ≤ G.chromaticNumber) : ContainsSubdivision (completeGraph (Fin k)) G := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · refine ⟨Fin.elim0, fun w => w.elim0, ⟨fun w => w.elim0, fun w => w.elim0,
      fun w => w.elim0, fun w => w.elim0⟩⟩
  obtain ⟨S, hS, hdeg⟩ := exists_dense (G := G) (k - 1) (not_colorable_of_le h (by omega))
  interval_cases k
  · obtain ⟨v, hv⟩ := hS
    refine tk_of_indices 1 0 (fun _ => v) (by intro a ha b hb _; simp only [Set.mem_Iic] at ha hb; omega) ![0]
      (fun _ _ => 1) (fun _ _ _ => 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first
      | (intro x y _; exact Subsingleton.elim x y)
      | (intro i; fin_cases i; simp)
      | (intro i j hij; exact absurd hij (by fin_cases i; fin_cases j; simp))
      | (intro i j i' j' hij; exact absurd hij (by fin_cases i; fin_cases j; simp))
  · obtain ⟨v, hv⟩ := hS
    obtain ⟨u, huS, hvu, -⟩ := exists_nbr_not_mem (hdeg v hv) ∅ (by simp)
    have hvu' : v ≠ u := G.ne_of_adj hvu
    refine tk_of_indices 2 1 (fun t => if t = 0 then v else u) ?_ ![0, 1]
      (fun _ _ => 1) (fun _ _ _ => 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro a ha b hb hab
      simp only [Set.mem_Iic] at ha hb
      interval_cases a <;> interval_cases b <;> simp_all
    · intro x y hxy; fin_cases x <;> fin_cases y <;> simp at hxy ⊢
    · intro i; fin_cases i <;> simp
    all_goals first
      | (intro i j hij; fin_cases i <;> fin_cases j <;> (try simp at hij) <;> simp <;>
          (try intro t ht) <;> (try intro t' ht' h) <;> first | omega | exact hvu)
      | (intro i j hij t ht l; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega)
      | (intro i j i' j' hij hij' hne; fin_cases i <;> fin_cases j <;> fin_cases i' <;>
          fin_cases j' <;> simp at hij hij' hne ⊢)
  · exact tk3 hS hdeg
  · exact tk4 hS hdeg

end Paths

end HajosFleet

theorem OMA.solution : type_of% @HajosConjecture.hajos_conjecture.variants.le_four := by
  intro V _ G k hk h
  exact HajosFleet.le_four G k hk h
