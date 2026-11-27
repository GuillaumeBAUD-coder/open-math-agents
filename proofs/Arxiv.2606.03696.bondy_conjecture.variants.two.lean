import FormalConjectures.Arxiv.«2606.03696».BondyLongestCycles

-- Problem: Bondy's conjecture on longest cycles in highly connected graphs — two
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2606.03696/BondyLongestCycles.lean:85 (declaration Arxiv.«2606.03696».bondy_conjecture.variants.two)
-- Credit: @Jakeybakeypants (the owner of the agent is credited as the solver)

/-!
Nash-Williams: in a 2-connected graph on n vertices with minimum degree at least (n+2)/3,
no edge lies outside a longest cycle C.

Write C as a c-periodic sequence f. Suppose an edge lies outside C and let H be its
component in G - C. By 2-connectivity two attachments of H on C have distinct neighbours
in H; take such a pair f 0, f j closest along C, so no attachment lies strictly between
them. Rerouting C through H (and through the chords at the successors u = f 1 and
v = f (j+1)) would give longer cycles, which forbids certain crossing patterns. Counting
over the window [1, c] then gives d(u) + d(v) + d(x) at most n + 1 for any x in H,
contradicting 3 * minDegree at least n + 2.
-/

namespace OMA.Bondy2

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A cyclic list: consecutive entries are adjacent, and so are the last and the first. -/
def Cyc (G : SimpleGraph V) (c : List V) : Prop :=
  c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b

lemma edge_not_mem {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  cases p with
  | nil => simp at hlen
  | @cons _ w _ hadj p' =>
    intro hmem
    rw [Walk.edges_cons, List.mem_cons] at hmem
    have hnd := hp.support_nodup
    rw [Walk.support_cons, List.nodup_cons] at hnd
    rcases hmem with h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · subst h2
        have hp' : p'.IsPath := hp.of_cons
        have : p'.length = 0 := by
          rcases p' with _ | ⟨h'', p''⟩
          · rfl
          · exfalso
            have := hp'.support_nodup
            simp at this
        simp [this] at hlen
      · subst h1
        exact hadj.ne rfl
    · exact hnd.1 (Walk.fst_mem_support_of_mem_edges p' h)

lemma cycle_of_list (c : List V) (hnd : c.Nodup) (hc : Cyc G c) (h3 : 3 ≤ c.length) :
    c.length ∈ G.cycleLengths := by
  have hne : c ≠ [] := by
    rintro rfl
    simp at h3
  set W := Walk.ofSupport c hne hc.1
  have hW : W.support = c := Walk.support_ofSupport hne hc.1
  have hWl : W.length = c.length - 1 := Walk.length_ofSupport hne hc.1
  have hpath : W.IsPath := Walk.IsPath.mk' (by rw [hW]; exact hnd)
  have hadj : G.Adj (c.head hne) (c.getLast hne) := by
    refine (?_ : G.Adj (c.getLast hne) (c.head hne)).symm
    apply hc.2
    · exact List.getLast?_eq_some_getLast hne
    · exact List.head?_eq_some_head hne
  refine ⟨c.head hne, Walk.cons hadj W.reverse, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hpath.reverse, ?_⟩
    rw [Walk.edges_reverse, List.mem_reverse]
    exact edge_not_mem W hpath (by omega)
  · rw [Walk.length_cons, Walk.length_reverse, hWl]
    omega

lemma cycle_length_le {a : V} (w : G.Walk a a) (hw : w.IsCycle) : w.length ≤ Fintype.card V := by
  have h1 := hw.support_nodup.length_le_card
  rw [List.length_tail, Walk.length_support] at h1
  omega

/-- A longest cycle of length `c`, written as a `c`-periodic sequence of vertices. -/
structure CycData (G : SimpleGraph V) (c : ℕ) (f : ℕ → V) : Prop where
  three : 3 ≤ c
  adj : ∀ t, G.Adj (f t) (f (t + 1))
  per : ∀ t, f (t + c) = f t
  inj : ∀ s t, s < c → t < c → f s = f t → s = t
  max : ∀ M : List V, M.Nodup → Cyc G M → 3 ≤ M.length → M.length ≤ c

/-- A path `Q` outside the cycle, from a neighbour of `f 0` to a neighbour of `f j`. -/
structure QP (G : SimpleGraph V) (f : ℕ → V) (Q : List V) (j : ℕ) : Prop where
  nd : Q.Nodup
  ne : Q ≠ []
  ch : Q.IsChain G.Adj
  off : ∀ z ∈ Q, ∀ t, f t ≠ z
  hd : ∀ q ∈ Q.head?, G.Adj (f 0) q
  tl : ∀ q ∈ Q.getLast?, G.Adj q (f j)

lemma chain_join {α : Type*} {R : α → α → Prop} {l1 l2 : List α} {x y : α}
    (h1 : l1.IsChain R) (h2 : l2.IsChain R) (hx : l1.getLast? = some x)
    (hy : l2.head? = some y) (hxy : R x y) : (l1 ++ l2).IsChain R := by
  refine List.isChain_append.2 ⟨h1, h2, ?_⟩
  intro a ha b hb
  rw [hx] at ha
  rw [hy] at hb
  simp only [Option.mem_def, Option.some.injEq] at ha hb
  subst ha hb
  exact hxy

lemma last_join {α : Type*} {l1 l2 : List α} {z : α} (h : l2.getLast? = some z) :
    (l1 ++ l2).getLast? = some z := by
  rw [List.getLast?_append, h]
  rfl

lemma head_join {α : Type*} {l1 l2 : List α} {z : α} (h : l1.head? = some z) :
    (l1 ++ l2).head? = some z := by
  rw [List.head?_append, h]
  rfl

lemma head_up (s k : ℕ) : (List.range' s (k + 1)).head? = some s := by
  simp [List.range'_succ]

lemma last_up (s k : ℕ) : (List.range' s (k + 1)).getLast? = some (s + k) := by
  simp [List.range'_concat]

lemma head_dn (s k : ℕ) : (List.range' s (k + 1)).reverse.head? = some (s + k) := by
  rw [List.head?_reverse, last_up]

lemma last_dn (s k : ℕ) : (List.range' s (k + 1)).reverse.getLast? = some s := by
  rw [List.getLast?_reverse, head_up]

namespace CycData

variable {c : ℕ} {f : ℕ → V}

lemma per_mul (hD : CycData G c f) (t k : ℕ) : f (t + c * k) = f t := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, hD.per, ih]

lemma mod_eq (hD : CycData G c f) (t : ℕ) : f t = f (t % c) := by
  conv_lhs => rw [← Nat.mod_add_div t c]
  exact hD.per_mul _ _

lemma fc (hD : CycData G c f) : f c = f 0 := by
  simpa using hD.per 0

lemma win (hD : CycData G c f) {s p q : ℕ} (hp1 : s ≤ p) (hp2 : p < s + c) (hq1 : s ≤ q)
    (hq2 : q < s + c) (h : f p = f q) : p = q := by
  have hc : 0 < c := by have := hD.three; omega
  rw [hD.mod_eq p, hD.mod_eq q] at h
  have h1 := hD.inj _ _ (Nat.mod_lt _ hc) (Nat.mod_lt _ hc) h
  rcases le_total p q with hpq | hpq
  · have hd : c ∣ q - p := (Nat.modEq_iff_dvd' hpq).1 h1
    have : q - p < c := by omega
    have := Nat.eq_zero_of_dvd_of_lt hd this
    omega
  · have hd : c ∣ p - q := (Nat.modEq_iff_dvd' hpq).1 h1.symm
    have : p - q < c := by omega
    have := Nat.eq_zero_of_dvd_of_lt hd this
    omega

lemma rot (hD : CycData G c f) (p : ℕ) : CycData G c (fun t => f (t + p)) where
  three := hD.three
  adj t := by
    have := hD.adj (t + p)
    rwa [show t + p + 1 = t + 1 + p by omega] at this
  per t := by
    show f (t + c + p) = f (t + p)
    rw [show t + c + p = t + p + c by omega, hD.per]
  inj s t hs ht h := by
    have := hD.win (s := p) (p := s + p) (q := t + p) (by omega) (by omega) (by omega)
      (by omega) h
    omega
  max := hD.max

lemma range_rot (hD : CycData G c f) (p : ℕ) (z : V) :
    (∃ t, f (t + p) = z) ↔ ∃ t, f t = z := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨_, ht⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t + c * p - p, ?_⟩
    have hc : 1 ≤ c := by have := hD.three; omega
    have : p ≤ c * p := Nat.le_mul_of_pos_left p (by omega)
    rw [show t + c * p - p + p = t + c * p by omega, hD.per_mul]

lemma chain_up (hD : CycData G c f) (s k : ℕ) :
    (List.range' s k).IsChain (fun p q => G.Adj (f p) (f q)) :=
  (List.isChain_range' s k 1).imp (fun p q h => by subst h; exact hD.adj p)

lemma chain_dn (hD : CycData G c f) (s k : ℕ) :
    (List.range' s k).reverse.IsChain (fun p q => G.Adj (f p) (f q)) := by
  rw [List.isChain_reverse]
  exact (List.isChain_range' s k 1).imp (fun p q h => by subst h; exact (hD.adj p).symm)

lemma reroute (hD : CycData G c f) (Q X : List V) (j : ℕ) (hQ : QP G f Q j)
    (hXnd : X.Nodup) (hXc : X.IsChain G.Adj) (hX0 : X.head? = some (f j))
    (hX1 : X.getLast? = some (f c)) (hdisj : ∀ z ∈ Q, z ∉ X)
    (hlen : c < Q.length + X.length) : False := by
  have hnd : (Q ++ X).Nodup :=
    List.nodup_append.2 ⟨hQ.nd, hXnd, fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
  have hcyc : Cyc G (Q ++ X) := by
    refine ⟨chain_join hQ.ch hXc (List.getLast?_eq_some_getLast hQ.ne) hX0
      (hQ.tl _ (List.getLast?_eq_some_getLast hQ.ne)), ?_⟩
    intro x hx y hy
    rw [last_join hX1] at hx
    rw [head_join (List.head?_eq_some_head hQ.ne)] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx hy
    rw [hD.fc]
    exact hQ.hd _ (List.head?_eq_some_head hQ.ne)
  have := hD.max _ hnd hcyc (by rw [List.length_append]; have := hD.three; omega)
  rw [List.length_append] at this
  omega

lemma reroute_idx (hD : CycData G c f) (Q : List V) (I : List ℕ) (j : ℕ) (hQ : QP G f Q j)
    (hInd : I.Nodup) (hIr : ∀ t ∈ I, 1 ≤ t ∧ t ≤ c)
    (hIc : I.IsChain (fun p q => G.Adj (f p) (f q)))
    (hI0 : I.head? = some j) (hI1 : I.getLast? = some c) (hlen : c < Q.length + I.length) :
    False := by
  refine hD.reroute Q (I.map f) j hQ ?_ ?_ ?_ ?_ ?_ ?_
  · refine List.Nodup.map_on ?_ hInd
    intro x hx y hy hxy
    have := hIr x hx
    have := hIr y hy
    exact hD.win (s := 1) (by omega) (by omega) (by omega) (by omega) hxy
  · exact (List.isChain_map f).2 hIc
  · simp [hI0]
  · simp [hI1]
  · intro z hz hzX
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hzX
    exact hQ.off _ hz t rfl
  · simpa using hlen

lemma alpha (hD : CycData G c f) {Q : List V} (hQ : QP G f Q 1) : False := by
  have h3 := hD.three
  obtain ⟨k, hk⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  refine hD.reroute_idx Q (List.range' 1 c) 1 hQ List.nodup_range' ?_ (hD.chain_up 1 c)
    ?_ ?_ ?_
  · intro t ht
    rw [List.mem_range'_1] at ht
    omega
  · rw [hk, head_up]
  · rw [hk, last_up]
    congr 1
    omega
  · have : 0 < Q.length := List.length_pos_of_ne_nil hQ.ne
    simp
    omega

lemma F1 (hD : CycData G c f) {Q : List V} {j : ℕ} (hQ : QP G f Q j) (hjc : j < c) {t : ℕ}
    (ht1 : 1 ≤ t) (htj : t < j) (h1 : G.Adj (f t) (f (j + 1))) (h2 : G.Adj (f (t + 1)) (f 1)) :
    False := by
  obtain ⟨k1, hk1⟩ : ∃ k, j - t = k + 1 := ⟨j - t - 1, by omega⟩
  obtain ⟨k2, hk2⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  obtain ⟨k3, hk3⟩ : ∃ k, c - j = k + 1 := ⟨c - j - 1, by omega⟩
  refine hD.reroute_idx Q ((List.range' (t + 1) (k1 + 1)).reverse ++ List.range' 1 (k2 + 1) ++
    List.range' (j + 1) (k3 + 1)) j hQ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_append,
      List.mem_range'_1]
    refine ⟨⟨List.nodup_range', List.nodup_range', ?_⟩, List.nodup_range', ?_⟩
    · intro a ha b hb
      omega
    · intro a ha b hb
      rcases ha with ha | ha <;> omega
  · intro x hx
    simp only [List.mem_append, List.mem_reverse, List.mem_range'_1] at hx
    omega
  · refine chain_join (chain_join (hD.chain_dn _ _) (hD.chain_up _ _) (last_dn _ _)
      (head_up _ _) ?_) (hD.chain_up _ _) (last_join (last_up _ _)) (head_up _ _) ?_
    · exact h2
    · rw [show 1 + k2 = t by omega]
      exact h1
  · rw [head_join (head_join (head_dn _ _))]
    congr 1
    omega
  · rw [last_join (last_up _ _)]
    congr 1
    omega
  · have : 0 < Q.length := List.length_pos_of_ne_nil hQ.ne
    simp only [List.length_append, List.length_reverse, List.length_range']
    omega

lemma F2 (hD : CycData G c f) {Q : List V} {j : ℕ} (hQ : QP G f Q j) (hj1 : 1 ≤ j) {t : ℕ}
    (hjt : j < t) (htc : t < c) (h1 : G.Adj (f t) (f 1)) (h2 : G.Adj (f (t + 1)) (f (j + 1))) :
    False := by
  obtain ⟨k1, hk1⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k2, hk2⟩ : ∃ k, t - j = k + 1 := ⟨t - j - 1, by omega⟩
  obtain ⟨k3, hk3⟩ : ∃ k, c - t = k + 1 := ⟨c - t - 1, by omega⟩
  refine hD.reroute_idx Q ((List.range' 1 (k1 + 1)).reverse ++
    (List.range' (j + 1) (k2 + 1)).reverse ++ List.range' (t + 1) (k3 + 1)) j hQ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_append,
      List.mem_range'_1]
    refine ⟨⟨List.nodup_range', List.nodup_range', ?_⟩, List.nodup_range', ?_⟩
    · intro a ha b hb
      omega
    · intro a ha b hb
      rcases ha with ha | ha <;> omega
  · intro x hx
    simp only [List.mem_append, List.mem_reverse, List.mem_range'_1] at hx
    omega
  · refine chain_join (chain_join (hD.chain_dn _ _) (hD.chain_dn _ _) (last_dn _ _)
      (head_dn _ _) ?_) (hD.chain_up _ _) (last_join (last_dn _ _)) (head_up _ _) ?_
    · rw [show j + 1 + k2 = t by omega]
      exact h1.symm
    · exact h2.symm
  · rw [head_join (head_join (head_dn _ _))]
    congr 1
    omega
  · rw [last_join (last_up _ _)]
    congr 1
    omega
  · have : 0 < Q.length := List.length_pos_of_ne_nil hQ.ne
    simp only [List.length_append, List.length_reverse, List.length_range']
    omega

lemma F3 (hD : CycData G c f) {Q : List V} {j : ℕ} (hQ : QP G f Q j) (hQ2 : 2 ≤ Q.length)
    (hj1 : 1 ≤ j) {t : ℕ} (hjt : j < t) (htc : t + 1 < c) (h1 : G.Adj (f t) (f 1))
    (h2 : G.Adj (f (t + 2)) (f (j + 1))) : False := by
  obtain ⟨k1, hk1⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k2, hk2⟩ : ∃ k, t - j = k + 1 := ⟨t - j - 1, by omega⟩
  obtain ⟨k3, hk3⟩ : ∃ k, c - t - 1 = k + 1 := ⟨c - t - 2, by omega⟩
  refine hD.reroute_idx Q ((List.range' 1 (k1 + 1)).reverse ++
    (List.range' (j + 1) (k2 + 1)).reverse ++ List.range' (t + 2) (k3 + 1)) j hQ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_append,
      List.mem_range'_1]
    refine ⟨⟨List.nodup_range', List.nodup_range', ?_⟩, List.nodup_range', ?_⟩
    · intro a ha b hb
      omega
    · intro a ha b hb
      rcases ha with ha | ha <;> omega
  · intro x hx
    simp only [List.mem_append, List.mem_reverse, List.mem_range'_1] at hx
    omega
  · refine chain_join (chain_join (hD.chain_dn _ _) (hD.chain_dn _ _) (last_dn _ _)
      (head_dn _ _) ?_) (hD.chain_up _ _) (last_join (last_dn _ _)) (head_up _ _) ?_
    · rw [show j + 1 + k2 = t by omega]
      exact h1.symm
    · exact h2.symm
  · rw [head_join (head_join (head_dn _ _))]
    congr 1
    omega
  · rw [last_join (last_up _ _)]
    congr 1
    omega
  · simp only [List.length_append, List.length_reverse, List.length_range']
    omega

lemma F6 (hD : CycData G c f) {Q : List V} {j : ℕ} (hQ : QP G f Q j) (hj1 : 1 ≤ j)
    (hjc : j < c) {r : V} (hr : ∀ t, f t ≠ r) (hrQ : r ∉ Q) (h1 : G.Adj r (f 1))
    (h2 : G.Adj r (f (j + 1))) : False := by
  obtain ⟨k1, hk1⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k3, hk3⟩ : ∃ k, c - j = k + 1 := ⟨c - j - 1, by omega⟩
  refine hD.reroute Q (((List.range' 1 (k1 + 1)).reverse.map f ++ [r]) ++
    (List.range' (j + 1) (k3 + 1)).map f) j hQ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨?_, List.nodup_singleton _, ?_⟩, ?_, ?_⟩
    · refine List.Nodup.map_on ?_ (List.nodup_reverse.2 List.nodup_range')
      intro x hx y hy hxy
      simp only [List.mem_reverse, List.mem_range'_1] at hx hy
      exact hD.win (s := 1) (by omega) (by omega) (by omega) (by omega) hxy
    · intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb hab
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 ha
      exact hr t rfl
    · refine List.Nodup.map_on ?_ List.nodup_range'
      intro x hx y hy hxy
      simp only [List.mem_range'_1] at hx hy
      exact hD.win (s := 1) (by omega) (by omega) (by omega) (by omega) hxy
    · intro a ha b hb hab
      subst hab
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hb
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · obtain ⟨t, ht, he⟩ := List.mem_map.1 ha
        simp only [List.mem_reverse, List.mem_range'_1] at ht ht'
        have := hD.win (s := 1) (by omega) (by omega) (by omega) (by omega) he
        omega
      · exact hr t' ha
  · have hA1 : ((List.range' 1 (k1 + 1)).reverse.map f).getLast? = some (f 1) := by
      rw [List.getLast?_map, last_dn]
      rfl
    have hB0 : ((List.range' (j + 1) (k3 + 1)).map f).head? = some (f (j + 1)) := by
      rw [List.head?_map, head_up]
      rfl
    exact chain_join (chain_join ((List.isChain_map f).2 (hD.chain_dn _ _))
      (List.isChain_singleton _) hA1 rfl h1.symm) ((List.isChain_map f).2 (hD.chain_up _ _))
      (last_join rfl) hB0 h2
  · have hA0 : ((List.range' 1 (k1 + 1)).reverse.map f).head? = some (f j) := by
      rw [List.head?_map, head_dn, show 1 + k1 = j by omega]
      rfl
    exact head_join (head_join hA0)
  · have hB1 : ((List.range' (j + 1) (k3 + 1)).map f).getLast? = some (f c) := by
      rw [List.getLast?_map, last_up, show j + 1 + k3 = c by omega]
      rfl
    exact last_join hB1
  · intro z hz hzX
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hzX
    rcases hzX with (⟨t, -, rfl⟩ | rfl) | ⟨t, -, rfl⟩
    · exact hQ.off _ hz t rfl
    · exact hrQ hz
    · exact hQ.off _ hz t rfl
  · have : 0 < Q.length := List.length_pos_of_ne_nil hQ.ne
    simp only [List.length_append, List.length_map, List.length_reverse, List.length_range',
      List.length_singleton]
    omega

end CycData

/-- Hypotheses on the vertex set `H` of a component of the graph outside the cycle. -/
structure HH (G : SimpleGraph V) (f : ℕ → V) (H : Set V) : Prop where
  off : ∀ z ∈ H, ∀ t, f t ≠ z
  adj : ∀ z ∈ H, ∀ w, (∀ t, f t ≠ w) → G.Adj z w → w ∈ H
  path : ∀ z ∈ H, ∀ z' ∈ H, ∃ Q : List V, Q.Nodup ∧ Q.IsChain G.Adj ∧ Q.head? = some z ∧
    Q.getLast? = some z' ∧ (∀ w ∈ Q, w ∈ H) ∧ (z ≠ z' → 2 ≤ Q.length)

namespace CycData

variable {c : ℕ} {f : ℕ → V} {H : Set V}

lemma HH_rot (hD : CycData G c f) (hH : HH G f H) (p : ℕ) : HH G (fun t => f (t + p)) H where
  off z hz t := hH.off z hz (t + p)
  adj z hz w hw h := by
    refine hH.adj z hz w ?_ h
    intro t ht
    obtain ⟨s, hs⟩ := (hD.range_rot p w).2 ⟨t, ht⟩
    exact hw s hs
  path := hH.path

lemma qpath (hH : HH G f H) {z z' : V} (hz : z ∈ H) (hz' : z' ∈ H) {j : ℕ}
    (h0 : G.Adj (f 0) z) (hj : G.Adj z' (f j)) :
    ∃ Q, QP G f Q j ∧ (∀ w ∈ Q, w ∈ H) ∧ (z ≠ z' → 2 ≤ Q.length) := by
  obtain ⟨Q, hnd, hch, hh, hl, hQH, hlen⟩ := hH.path z hz z' hz'
  refine ⟨Q, ⟨hnd, ?_, hch, fun w hw => hH.off w (hQH w hw), ?_, ?_⟩, hQH, hlen⟩
  · rintro rfl
    simp at hh
  · intro q hq
    rw [hh] at hq
    simp only [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact h0
  · intro q hq
    rw [hl] at hq
    simp only [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hj

lemma no_adj_succ (hD : CycData G c f) (hH : HH G f H) {t : ℕ} {z z' : V} (hz : z ∈ H)
    (hz' : z' ∈ H) (h0 : G.Adj (f t) z) (h1 : G.Adj (f (t + 1)) z') : False := by
  obtain ⟨Q, hQ, -, -⟩ := qpath (f := fun s => f (s + t)) (hD.HH_rot hH t) hz hz' (j := 1)
    (by simpa using h0) (by show G.Adj z' (f (1 + t)); rw [Nat.add_comm]; exact h1.symm)
  exact (hD.rot t).alpha hQ

lemma beta_gen (hD : CycData G c f) (hH : HH G f H) {t : ℕ} (ht1 : 1 ≤ t) (htc : t + 1 < c)
    {z z' : V} (hz : z ∈ H) (hz' : z' ∈ H) (h0 : G.Adj (f 0) z) (h1 : G.Adj (f t) z')
    (h : G.Adj (f (t + 1)) (f 1)) : False := by
  obtain ⟨Q, hQ, -, -⟩ := qpath hH hz hz' h0 h1.symm
  exact hD.F2 hQ ht1 (t := t + 1) (by omega) htc h (hD.adj (t + 1)).symm

lemma split_card (P : ℕ → Prop) [DecidablePred P] (a b d : ℕ) (hab : a ≤ b + 1) (hbd : b ≤ d) :
    ((Finset.Icc a d).filter P).card =
      ((Finset.Icc a b).filter P).card + ((Finset.Icc (b + 1) d).filter P).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases htb : t ≤ b
      · exact Or.inl ⟨⟨h1, htb⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, by omega⟩, h3⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  · rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht ht'
    omega

/-- The heart of the argument: two consecutive attachments `f 0` and `f j` of `H`, joined
through `H` by a path with at least two vertices, give three vertices whose degrees sum to
at most `n + 1`. -/
theorem core [DecidableRel G.Adj] (hD : CycData G c f) (hH : HH G f H) {x : V} (hx : x ∈ H)
    {j : ℕ} {h1 h2 : V} (hh1 : h1 ∈ H) (hh2 : h2 ∈ H) (hne : h1 ≠ h2)
    (ha : G.Adj (f 0) h1) (hb : G.Adj (f j) h2) (hj0 : 0 < j) (hjc : j < c)
    (hmin : ∀ e, 0 < e → e < j → ∀ h ∈ H, ¬ G.Adj (f e) h)
    (hdeg : ∀ w, Fintype.card V + 2 ≤ 3 * G.degree w) : False := by
  classical
  have hc3 := hD.three
  have hα : ∀ t, (∃ h ∈ H, G.Adj (f t) h) → (∃ h ∈ H, G.Adj (f (t + 1)) h) → False := by
    rintro t ⟨z, hz, hz1⟩ ⟨z', hz', hz2⟩
    exact hD.no_adj_succ hH hz hz' hz1 hz2
  have hA0 : ∃ h ∈ H, G.Adj (f 0) h := ⟨h1, hh1, ha⟩
  have hAj : ∃ h ∈ H, G.Adj (f j) h := ⟨h2, hh2, hb⟩
  have hj2 : 2 ≤ j := by
    by_contra hcon
    have : j = 1 := by omega
    subst this
    exact hα 0 hA0 hAj
  have hAc1 : ¬ ∃ h ∈ H, G.Adj (f (c - 1)) h := by
    intro h
    apply hα (c - 1) h
    rw [show c - 1 + 1 = c by omega, hD.fc]
    exact hA0
  have hjc2 : j + 2 ≤ c := by
    by_contra hcon
    have : j = c - 1 := by omega
    rw [this] at hAj
    exact hAc1 hAj
  have hAu : ¬ ∃ h ∈ H, G.Adj (f 1) h := fun h => hα 0 hA0 h
  have hAv : ¬ ∃ h ∈ H, G.Adj (f (j + 1)) h := fun h => hα j hAj h
  obtain ⟨Q0, hQ0, hQ0H, hQ0l⟩ := qpath hH hh1 hh2 ha hb.symm
  have hQ02 := hQ0l hne
  have cF1 : ∀ t, 1 ≤ t → t < j → G.Adj (f (j + 1)) (f t) → G.Adj (f 1) (f (t + 1)) → False :=
    fun t ht1 htj h1' h2' => hD.F1 hQ0 hjc ht1 htj h1'.symm h2'.symm
  have cF2 : ∀ t, j < t → t < c → G.Adj (f 1) (f t) → G.Adj (f (j + 1)) (f (t + 1)) → False :=
    fun t hjt htc h1' h2' => hD.F2 hQ0 (by omega) hjt htc h1'.symm h2'.symm
  have cF3 : ∀ t, j < t → t + 1 < c → G.Adj (f 1) (f t) → G.Adj (f (j + 1)) (f (t + 2)) →
      False :=
    fun t hjt htc h1' h2' => hD.F3 hQ0 hQ02 (by omega) hjt htc h1'.symm h2'.symm
  have cF6 : ∀ r, (∀ t, f t ≠ r) → r ∉ H → G.Adj (f 1) r → G.Adj (f (j + 1)) r → False :=
    fun r hr hrH h1' h2' =>
      hD.F6 hQ0 (by omega) hjc hr (fun hm => hrH (hQ0H r hm)) h1'.symm h2'.symm
  have cF4u : ∀ t, 2 ≤ t → t + 1 < c → (∃ h ∈ H, G.Adj (f t) h) →
      G.Adj (f 1) (f (t + 1)) → False := by
    rintro t ht2 htc ⟨z', hz', hz'1⟩ h
    exact hD.beta_gen hH (by omega) htc hh1 hz' ha hz'1 h.symm
  have cF4v : ∀ t, j + 2 ≤ t → t + 1 < c → (∃ h ∈ H, G.Adj (f t) h) →
      G.Adj (f (j + 1)) (f (t + 1)) → False := by
    rintro t ht2 htc ⟨z', hz', hz'1⟩ h
    have := (hD.rot j).beta_gen (hD.HH_rot hH j) (t := t - j) (by omega) (by omega) hh2 hz'
      (by simpa using hb)
      (by show G.Adj (f (t - j + j)) z'; rw [show t - j + j = t by omega]; exact hz'1)
    apply this
    show G.Adj (f (t - j + 1 + j)) (f (1 + j))
    rw [show t - j + 1 + j = t + 1 by omega, Nat.add_comm 1 j]
    exact h.symm
  -- counting on the window `[1, c]`
  have claim1 : ((Finset.Icc 1 j).filter (fun t => G.Adj (f 1) (f t))).card +
      ((Finset.Icc 1 j).filter (fun t => G.Adj (f (j + 1)) (f t))).card ≤ j := by
    have e1 : ((Finset.Icc 1 j).filter (fun t => G.Adj (f (j + 1)) (f t))).card ≤
        ((Finset.Icc 1 (j - 1)).filter (fun t => G.Adj (f (j + 1)) (f t))).card + 1 := by
      rw [split_card _ 1 (j - 1) j (by omega) (by omega)]
      have : ((Finset.Icc (j - 1 + 1) j).filter (fun t => G.Adj (f (j + 1)) (f t))).card ≤ 1 := by
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Nat.card_Icc]
        omega
      omega
    have hY : (((Finset.Icc 1 (j - 1)).filter (fun t => G.Adj (f (j + 1)) (f t))).image
        (· + 1)).card = ((Finset.Icc 1 (j - 1)).filter (fun t => G.Adj (f (j + 1)) (f t))).card :=
      Finset.card_image_of_injective _ (add_left_injective 1)
    have hsub : (Finset.Icc 1 j).filter (fun t => G.Adj (f 1) (f t)) ∪
        ((Finset.Icc 1 (j - 1)).filter (fun t => G.Adj (f (j + 1)) (f t))).image (· + 1) ⊆
        Finset.Icc 2 j := by
      intro t ht
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at ht ⊢
      rcases ht with ⟨⟨h1', h2'⟩, h3⟩ | ⟨s, ⟨⟨hs1, hs2⟩, -⟩, rfl⟩
      · refine ⟨?_, h2'⟩
        by_contra hcon
        have : t = 1 := by omega
        subst this
        exact (G.ne_of_adj h3) rfl
      · omega
    have hdisj : Disjoint ((Finset.Icc 1 j).filter (fun t => G.Adj (f 1) (f t)))
        (((Finset.Icc 1 (j - 1)).filter (fun t => G.Adj (f (j + 1)) (f t))).image (· + 1)) := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at ht ht'
      obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, rfl⟩ := ht'
      exact cF1 s hs1 (by omega) hs3 ht.2
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hY, Nat.card_Icc] at this
    omega
  have claim2 : ((Finset.Icc (j + 1) c).filter (fun t => G.Adj (f 1) (f t))).card +
      ((Finset.Icc (j + 1) c).filter (fun t => G.Adj (f (j + 1)) (f t))).card +
      ((Finset.Icc (j + 1) (c - 1)).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).card ≤ c - j := by
    have e1 : ((Finset.Icc (j + 1) c).filter (fun t => G.Adj (f 1) (f t))).card ≤
        ((Finset.Icc (j + 1) (c - 1)).filter (fun t => G.Adj (f 1) (f t))).card + 1 := by
      rw [split_card _ (j + 1) (c - 1) c (by omega) (by omega)]
      have : ((Finset.Icc (c - 1 + 1) c).filter (fun t => G.Adj (f 1) (f t))).card ≤ 1 := by
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Nat.card_Icc]
        omega
      omega
    have e2 : ((Finset.Icc (j + 1) c).filter (fun t => G.Adj (f (j + 1)) (f t))).card ≤
        ((Finset.Icc (j + 2) c).filter (fun t => G.Adj (f (j + 1)) (f t))).card := by
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
      refine ⟨⟨?_, ht.1.2⟩, ht.2⟩
      by_contra hcon
      have : t = j + 1 := by omega
      subst this
      exact (G.ne_of_adj ht.2) rfl
    have hY2 : (((Finset.Icc (j + 2) c).filter (fun t => G.Adj (f (j + 1)) (f t))).image
        (· - 1)).card = ((Finset.Icc (j + 2) c).filter (fun t => G.Adj (f (j + 1)) (f t))).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hp hq
      simp only at hpq
      omega
    have hZ : (((Finset.Icc (j + 1) (c - 1)).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).image
        (fun t => if G.Adj (f 1) (f t) then t + 1 else t)).card =
        ((Finset.Icc (j + 1) (c - 1)).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hp hq
      simp only at hpq
      split_ifs at hpq with h1' h2' h2'
      · omega
      · exfalso
        subst hpq
        exact hα p hp.2 hq.2
      · exfalso
        subst hpq
        exact hα q hq.2 hp.2
      · exact hpq
    have hsub : (Finset.Icc (j + 1) (c - 1)).filter (fun t => G.Adj (f 1) (f t)) ∪
        ((Finset.Icc (j + 2) c).filter (fun t => G.Adj (f (j + 1)) (f t))).image (· - 1) ∪
        ((Finset.Icc (j + 1) (c - 1)).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).image
          (fun t => if G.Adj (f 1) (f t) then t + 1 else t) ⊆ Finset.Icc (j + 1) (c - 1) := by
      intro t ht
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at ht
      rw [Finset.mem_Icc]
      rcases ht with (⟨h1', -⟩ | ⟨s, ⟨⟨hs1, hs2⟩, -⟩, rfl⟩) | ⟨s, ⟨⟨hs1, hs2⟩, hsA⟩, rfl⟩
      · exact h1'
      · omega
      · have : s ≠ c - 1 := by
          rintro rfl
          exact hAc1 hsA
        split_ifs <;> omega
    have hd1 : Disjoint ((Finset.Icc (j + 1) (c - 1)).filter (fun t => G.Adj (f 1) (f t)))
        (((Finset.Icc (j + 2) c).filter (fun t => G.Adj (f (j + 1)) (f t))).image (· - 1)) := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at ht ht'
      obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, rfl⟩ := ht'
      have hs : s - 1 + 1 = s := by omega
      exact cF2 (s - 1) (by omega) (by omega) ht.2 (by rw [hs]; exact hs3)
    have hd2 : Disjoint ((Finset.Icc (j + 1) (c - 1)).filter (fun t => G.Adj (f 1) (f t)) ∪
        ((Finset.Icc (j + 2) c).filter (fun t => G.Adj (f (j + 1)) (f t))).image (· - 1))
        (((Finset.Icc (j + 1) (c - 1)).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).image
          (fun t => if G.Adj (f 1) (f t) then t + 1 else t)) := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at ht ht'
      obtain ⟨s, ⟨⟨hs1, hs2⟩, hsA⟩, rfl⟩ := ht'
      have hs3 : s ≠ j + 1 := by
        rintro rfl
        exact hAv hsA
      have hs4 : s ≠ c - 1 := by
        rintro rfl
        exact hAc1 hsA
      by_cases hPs : G.Adj (f 1) (f s)
      · rw [if_pos hPs] at ht
        rcases ht with ⟨-, hP⟩ | ⟨r, ⟨⟨hr1, hr2⟩, hr3⟩, hr⟩
        · exact cF4u s (by omega) (by omega) hsA hP
        · have : r = s + 2 := by omega
          subst this
          exact cF3 s (by omega) (by omega) hPs hr3
      · rw [if_neg hPs] at ht
        rcases ht with ⟨-, hP⟩ | ⟨r, ⟨⟨hr1, hr2⟩, hr3⟩, hr⟩
        · exact hPs hP
        · have : r = s + 1 := by omega
          subst this
          exact cF4v s (by omega) (by omega) hsA hr3
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hY2, hZ,
      Nat.card_Icc] at this
    omega
  have claim3 : ((Finset.Icc 1 c).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).card ≤
      ((Finset.Icc (j + 1) (c - 1)).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).card + 2 := by
    have hsub : (Finset.Icc 1 c).filter (fun t => ∃ h ∈ H, G.Adj (f t) h) ⊆ insert j (insert c
        ((Finset.Icc (j + 1) (c - 1)).filter (fun t => ∃ h ∈ H, G.Adj (f t) h))) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_Icc] at ht
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
      by_cases h1' : t = j
      · exact Or.inl h1'
      by_cases h2' : t = c
      · exact Or.inr (Or.inl h2')
      refine Or.inr (Or.inr ⟨⟨?_, by omega⟩, ht.2⟩)
      by_contra hcon
      obtain ⟨z, hz, hz'⟩ := ht.2
      exact hmin t (by omega) (by omega) z hz hz'
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_insert_le c
      ((Finset.Icc (j + 1) (c - 1)).filter (fun t => ∃ h ∈ H, G.Adj (f t) h))
    omega
  have hNu := split_card (fun t => G.Adj (f 1) (f t)) 1 j c (by omega) (by omega)
  have hNv := split_card (fun t => G.Adj (f (j + 1)) (f t)) 1 j c (by omega) (by omega)
  -- the vertex sets
  have hmemC : ∀ z, z ∈ (Finset.Icc 1 c).image f ↔ ∃ t, f t = z := by
    intro z
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      rw [hD.mod_eq t]
      by_cases h0 : t % c = 0
      · exact ⟨c, ⟨by omega, le_rfl⟩, by rw [h0, hD.fc]⟩
      · exact ⟨t % c, ⟨by omega, (Nat.mod_lt _ (by omega)).le⟩, rfl⟩
  have hCcard : ((Finset.Icc 1 c).image f).card = c := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    intro p hp q hq hpq
    simp only [Finset.coe_Icc, Set.mem_Icc] at hp hq
    exact hD.win (s := 1) (by omega) (by omega) (by omega) (by omega) hpq
  have hn : Fintype.card V = ((Finset.Icc 1 c).image f).card +
      (Finset.univ.filter (fun z => z ∈ H)).card +
      (Finset.univ.filter (fun z => z ∉ (Finset.Icc 1 c).image f ∧ z ∉ H)).card := by
    have hdisj1 : Disjoint ((Finset.Icc 1 c).image f) (Finset.univ.filter (fun z => z ∈ H)) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz'
      obtain ⟨t, rfl⟩ := (hmemC z).1 hz
      exact hH.off _ hz' t rfl
    have hdisj2 : Disjoint ((Finset.Icc 1 c).image f ∪ Finset.univ.filter (fun z => z ∈ H))
        (Finset.univ.filter (fun z => z ∉ (Finset.Icc 1 c).image f ∧ z ∉ H)) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
      tauto
    have huniv : (Finset.Icc 1 c).image f ∪ Finset.univ.filter (fun z => z ∈ H) ∪
        Finset.univ.filter (fun z => z ∉ (Finset.Icc 1 c).image f ∧ z ∉ H) = Finset.univ := by
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      tauto
    have := congrArg Finset.card huniv
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      Finset.card_univ] at this
    omega
  -- degrees
  have hdeg_uv : ∀ i, (i = 1 ∨ i = j + 1) → G.degree (f i) ≤
      ((Finset.Icc 1 c).filter (fun t => G.Adj (f i) (f t))).card +
      ((Finset.univ.filter (fun z => z ∉ (Finset.Icc 1 c).image f ∧ z ∉ H)).filter
        (G.Adj (f i))).card := by
    intro i hi
    have hAi : ¬ ∃ h ∈ H, G.Adj (f i) h := by
      rcases hi with rfl | rfl
      · exact hAu
      · exact hAv
    rw [← card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset (f i) ⊆
        ((Finset.Icc 1 c).filter (fun t => G.Adj (f i) (f t))).image f ∪
        (Finset.univ.filter (fun z => z ∉ (Finset.Icc 1 c).image f ∧ z ∉ H)).filter
          (G.Adj (f i)) := by
      intro z hz
      rw [mem_neighborFinset] at hz
      rw [Finset.mem_union]
      by_cases hzC : z ∈ (Finset.Icc 1 c).image f
      · left
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hzC
        exact Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨ht, hz⟩, rfl⟩
      · right
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hzC, fun hzH => hAi ⟨z, hzH, hz⟩⟩, hz⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    have := Finset.card_image_le (s := (Finset.Icc 1 c).filter (fun t => G.Adj (f i) (f t)))
      (f := f)
    omega
  have hdu := hdeg_uv 1 (Or.inl rfl)
  have hdv := hdeg_uv (j + 1) (Or.inr rfl)
  have hR : ((Finset.univ.filter (fun z => z ∉ (Finset.Icc 1 c).image f ∧ z ∉ H)).filter
        (G.Adj (f 1))).card +
      ((Finset.univ.filter (fun z => z ∉ (Finset.Icc 1 c).image f ∧ z ∉ H)).filter
        (G.Adj (f (j + 1)))).card ≤
      (Finset.univ.filter (fun z => z ∉ (Finset.Icc 1 c).image f ∧ z ∉ H)).card := by
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    · rw [Finset.disjoint_left]
      intro r hr hr'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr hr'
      exact cF6 r (fun t ht => hr.1.1 ((hmemC r).2 ⟨t, ht⟩)) hr.1.2 hr.2 hr'.2
  have hdx : G.degree x ≤ ((Finset.Icc 1 c).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).card +
      ((Finset.univ.filter (fun z => z ∈ H)).card - 1) := by
    rw [← card_neighborFinset_eq_degree]
    have hxs : x ∈ Finset.univ.filter (fun z => z ∈ H) := by simp [hx]
    have hsub : G.neighborFinset x ⊆
        ((Finset.Icc 1 c).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)).image f ∪
        (Finset.univ.filter (fun z => z ∈ H)).erase x := by
      intro z hz
      rw [mem_neighborFinset] at hz
      rw [Finset.mem_union]
      by_cases hzC : z ∈ (Finset.Icc 1 c).image f
      · left
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hzC
        exact Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨ht, x, hx, hz.symm⟩, rfl⟩
      · right
        have hzoff : ∀ t, f t ≠ z := fun t ht => hzC ((hmemC z).2 ⟨t, ht⟩)
        have hzH : z ∈ H := hH.adj x hx z hzoff hz
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(G.ne_of_adj hz).symm, hzH⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_erase_of_mem hxs]
    have := Finset.card_image_le
      (s := (Finset.Icc 1 c).filter (fun t => ∃ h ∈ H, G.Adj (f t) h)) (f := f)
    omega
  have hx1 : 1 ≤ (Finset.univ.filter (fun z => z ∈ H)).card :=
    Finset.card_pos.2 ⟨x, by simp [hx]⟩
  have d1 := hdeg (f 1)
  have d2 := hdeg (f (j + 1))
  have d3 := hdeg x
  omega

end CycData

theorem main2 [DecidableRel G.Adj] (hG : IsKConnected G 2)
    (hdeg : ∀ w, Fintype.card V + 2 ≤ 3 * G.degree w) {a : V} (C : G.Walk a a)
    (hC : C.IsCycle) (hlong : C.length = G.circumference) {x y : V} (hx : x ∉ C.support)
    (hy : y ∉ C.support) (hxy : G.Adj x y) : False := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, C.length = c := ⟨_, rfl⟩
  have hc3 : 3 ≤ c := hc ▸ hC.three_le_length
  obtain ⟨f, hf⟩ : ∃ f : ℕ → V, ∀ t, f t = C.getVert (t % c) := ⟨_, fun _ => rfl⟩
  have hD : CycData G c f := by
    refine ⟨hc3, ?_, ?_, ?_, ?_⟩
    · intro t
      have hr : t % c < c := Nat.mod_lt _ (by omega)
      have e : (t + 1) % c = (t % c + 1) % c := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < c by omega)]
      have hr' : t % c < C.length := by rw [hc]; exact hr
      have hadj := C.adj_getVert_succ hr'
      rw [hf, hf, e]
      by_cases h : t % c + 1 < c
      · rwa [Nat.mod_eq_of_lt h]
      · have h' : t % c + 1 = c := by omega
        rw [h', Nat.mod_self, Walk.getVert_zero]
        have hca : C.getVert c = a := by rw [← hc]; exact C.getVert_length
        rw [h', hca] at hadj
        exact hadj
    · intro t
      rw [hf, hf, Nat.add_mod_right]
    · intro s t hs ht h
      rw [hf, hf, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at h
      exact hC.getVert_injOn' (show s ≤ C.length - 1 by omega) (show t ≤ C.length - 1 by omega) h
    · intro M hM hMc hM3
      have hmem := cycle_of_list M hM hMc hM3
      have hbdd : BddAbove G.cycleLengths := by
        refine ⟨Fintype.card V, ?_⟩
        rintro k ⟨b, w, hw, rfl⟩
        exact cycle_length_le w hw
      have := le_csSup hbdd hmem
      have hcirc : G.circumference = c := hlong.symm.trans hc
      unfold circumference at hcirc
      omega
  have hO : ∀ z, z ∉ C.support ↔ ∀ t, f t ≠ z := by
    intro z
    constructor
    · intro hz t ht
      rw [hf] at ht
      exact hz (ht ▸ C.getVert_mem_support _)
    · intro h hz
      obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hz
      by_cases hnc : n < c
      · exact h n (by rw [hf, Nat.mod_eq_of_lt hnc]; exact hn)
      · have : n = C.length := by omega
        rw [this, Walk.getVert_length] at hn
        apply h 0
        rw [hf, Nat.zero_mod, Walk.getVert_zero]
        exact hn
  have toIdx : ∀ z ∈ C.support, ∃ t, t < c ∧ f t = z := by
    intro z hz
    by_contra hne
    exact (hO z).2 (fun t ht => hne ⟨t % c, Nat.mod_lt _ (by omega), by rw [← hD.mod_eq]; exact ht⟩) hz
  -- the component of `x` outside the cycle
  let O : Set V := {w | w ∉ C.support}
  have hxO : x ∈ O := hx
  have hyO : y ∈ O := hy
  let H : Set V := {z | ∃ hz : z ∈ O, (G.induce O).Reachable ⟨x, hxO⟩ ⟨z, hz⟩}
  have hxH : x ∈ H := ⟨hxO, Reachable.refl _⟩
  have hHO : ∀ z ∈ H, z ∉ C.support := fun z hz => hz.1
  have hH : HH G f H := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (hO z).1 (hHO z hz)
    · rintro z ⟨hz, hr⟩ w hw hzw
      have hwO : w ∈ O := (hO w).2 hw
      exact ⟨hwO, hr.trans (Adj.reachable (show (G.induce O).Adj ⟨z, hz⟩ ⟨w, hwO⟩ from hzw))⟩
    · rintro z ⟨hz, hr⟩ z' ⟨hz', hr'⟩
      obtain ⟨p⟩ := hr.symm.trans hr'
      let q := p.toPath
      refine ⟨q.1.support.map Subtype.val, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact q.2.support_nodup.map Subtype.val_injective
      · exact (List.isChain_map _).2 (q.1.isChain_adj_support.imp (fun a b h => h))
      · rw [← Walk.cons_tail_support]
        rfl
      · rw [List.getLast?_map, List.getLast?_eq_some_getLast q.1.support_ne_nil,
          Walk.getLast_support]
        rfl
      · intro w hw
        obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
        exact ⟨w'.2, hr.trans ⟨q.1.takeUntil w' hw'⟩⟩
      · intro hne
        rw [List.length_map, Walk.length_support]
        have : q.1.length ≠ 0 := by
          intro h0
          apply hne
          exact congrArg Subtype.val (Walk.eq_of_length_eq_zero h0)
        omega
  have hyH : y ∈ H := hH.adj x hxH y ((hO y).1 hy) hxy
  -- leaving `H` while avoiding one vertex
  have escape : ∀ e z w0, z ∈ H → z ≠ e → w0 ∈ C.support → w0 ≠ e →
      ∃ h ∈ H, h ≠ e ∧ ∃ b ∈ C.support, b ≠ e ∧ G.Adj h b := by
    intro e z w0 hzH hze hw0 hw0e
    have hconn := hG.2 {e} (by simp)
    have hzc : z ∈ ((({e} : Finset V) : Set V)ᶜ) := by simpa using hze
    have hw0c : w0 ∈ ((({e} : Finset V) : Set V)ᶜ) := by simpa using hw0e
    obtain ⟨p'⟩ := hconn.preconnected ⟨z, hzc⟩ ⟨w0, hw0c⟩
    let p := p'.map (Embedding.induce _).toHom
    have hp : ∀ w ∈ p.support, w ≠ e := by
      intro w hw
      rw [Walk.support_map, List.mem_map] at hw
      obtain ⟨w', -, rfl⟩ := hw
      have := w'.2
      simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff] at this
      exact this
    have hw0H : w0 ∉ H := fun h => hHO w0 h hw0
    obtain ⟨d, hd, hd1, hd2⟩ := p.exists_boundary_dart H hzH hw0H
    refine ⟨d.fst, hd1, hp _ (p.dart_fst_mem_support_of_mem_darts hd), d.snd, ?_,
      hp _ (p.dart_snd_mem_support_of_mem_darts hd), d.adj⟩
    by_contra hns
    exact hd2 (hH.adj _ hd1 _ ((hO _).1 hns) d.adj)
  have haC : a ∈ C.support := C.start_mem_support
  have two : ∃ b ∈ C.support, ∃ b' ∈ C.support, b ≠ b' ∧ ∃ h ∈ H, ∃ h' ∈ H, h ≠ h' ∧
      G.Adj b h ∧ G.Adj b' h' := by
    obtain ⟨h2, hh2, hh2x, b, hb, -, hb2⟩ :=
      escape x y a hyH (G.ne_of_adj hxy).symm haC (fun h => hx (h ▸ haC))
    obtain ⟨h1, hh1, hh12, b1, hb1, -, hb1'⟩ :=
      escape h2 x a hxH (Ne.symm hh2x) haC (fun h => hHO h2 hh2 (h ▸ haC))
    by_cases hbb : b1 = b
    · rw [hbb] at hb1'
      have hf01 : f 0 ≠ f 1 := fun h => by have := hD.inj 0 1 (by omega) (by omega) h; omega
      have hfC : ∀ t, f t ∈ C.support := fun t => by
        by_contra hn
        exact (hO (f t)).1 hn t rfl
      obtain ⟨w0, hw0, hw0b⟩ : ∃ w0 ∈ C.support, w0 ≠ b := by
        by_cases h0 : f 0 = b
        · exact ⟨f 1, hfC 1, fun h => hf01 (h0.trans h.symm)⟩
        · exact ⟨f 0, hfC 0, h0⟩
      obtain ⟨h3, hh3, -, b3, hb3, hb3b, hb3'⟩ :=
        escape b h1 w0 hh1 (fun h => hHO h1 hh1 (h ▸ hb)) hw0 hw0b
      by_cases h31 : h3 = h1
      · rw [h31] at hb3'
        exact ⟨b3, hb3, b, hb, hb3b, h1, hh1, h2, hh2, hh12, hb3'.symm, hb2.symm⟩
      · exact ⟨b3, hb3, b, hb, hb3b, h3, hh3, h1, hh1, h31, hb3'.symm, hb1'.symm⟩
    · exact ⟨b1, hb1, b, hb, hbb, h1, hh1, h2, hh2, hh12, hb1'.symm, hb2.symm⟩
  obtain ⟨b, hb, b', hb', hbb', h, hh, h', hh', hhh', hbh, hbh'⟩ := two
  obtain ⟨p, hp, rfl⟩ := toIdx b hb
  obtain ⟨q, hq, rfl⟩ := toIdx b' hb'
  -- the closest pair of attachments with distinct neighbours in `H`
  let D : ℕ → Prop := fun d => 0 < d ∧ ∃ p h h', h ∈ H ∧ h' ∈ H ∧ h ≠ h' ∧ G.Adj (f p) h ∧
    G.Adj (f (p + d)) h'
  have hDex : ∃ d, d < c ∧ D d := by
    have hpq : p ≠ q := by
      rintro rfl
      exact hbb' rfl
    rcases lt_or_gt_of_ne hpq with hpq | hpq
    · refine ⟨q - p, by omega, by omega, p, h, h', hh, hh', hhh', hbh, ?_⟩
      rw [show p + (q - p) = q by omega]
      exact hbh'
    · refine ⟨q + c - p, by omega, by omega, p, h, h', hh, hh', hhh', hbh, ?_⟩
      rw [show p + (q + c - p) = q + c by omega, hD.per]
      exact hbh'
  obtain ⟨d1, hd1c, hd1⟩ := hDex
  have hex : ∃ d, D d := ⟨d1, hd1⟩
  obtain ⟨hd0pos, p0, h1, h2, hh1, hh2, hne, ha, hb0⟩ := Nat.find_spec hex
  have hd0c : Nat.find hex < c := lt_of_le_of_lt (Nat.find_min' hex hd1) hd1c
  have hmin : ∀ e, 0 < e → e < Nat.find hex → ∀ h ∈ H, ¬ G.Adj (f (e + p0)) h := by
    intro e he hed h3 hh3 hadj
    have n1 := Nat.find_min hex hed
    have n2 := Nat.find_min hex (show Nat.find hex - e < Nat.find hex by omega)
    have e1 : h1 = h3 := by
      by_contra hc'
      exact n1 ⟨he, p0, h1, h3, hh1, hh3, hc', ha, by rw [Nat.add_comm]; exact hadj⟩
    have e2 : h3 = h2 := by
      by_contra hc'
      refine n2 ⟨by omega, p0 + e, h3, h2, hh3, hh2, hc', by rw [Nat.add_comm]; exact hadj, ?_⟩
      rw [show p0 + e + (Nat.find hex - e) = p0 + Nat.find hex by omega]
      exact hb0
    exact hne (e1.trans e2)
  exact CycData.core (hD.rot p0) (hD.HH_rot hH p0) hxH (j := Nat.find hex) hh1 hh2 hne
    (by simpa using ha) (by show G.Adj (f (Nat.find hex + p0)) h2; rw [Nat.add_comm]; exact hb0)
    hd0pos hd0c hmin hdeg

end OMA.Bondy2

open SimpleGraph in
theorem OMA.solution : type_of% @Arxiv.«2606.03696».bondy_conjecture.variants.two := by
  intro V _ _ G _ hG hd a C hC hlong u v P hP
  have hdeg : ∀ w, Fintype.card V + 2 ≤ 3 * G.degree w := by
    intro w
    have h1 : (G.minDegree : ℝ) ≤ G.degree w := by exact_mod_cast G.minDegree_le_degree w
    have h2 : ((Fintype.card V : ℝ) + 2) ≤ 3 * G.degree w := by linarith
    exact_mod_cast h2
  by_contra hcon
  cases P with
  | nil => simp at hcon
  | @cons _ w _ h P' => exact OMA.Bondy2.main2 hG hdeg C hC hlong u.2 w.2 h
