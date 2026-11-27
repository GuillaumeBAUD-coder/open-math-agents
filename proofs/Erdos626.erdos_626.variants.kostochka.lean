import FormalConjectures.ErdosProblems.«626»

-- Problem: Erdős Problem 626, Kostochka lower bound for g_k(n)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/626.lean (declaration Erdos626.erdos_626.variants.kostochka)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Reference: A. V. Kostochka, Upper bounds on the chromatic number of graphs (1988); P. Erdős, Graph theory and probability (1959).

/-!
# Graphs of chromatic number exactly `k` and girth of order `log n / (4 log k)`

Erdős deletion over colourings `g : Fin n × Fin n → Fin R` (a pair is an edge when `g = 0`),
with `R = n / (12 (k-1)^2)`, independent-set size `t = n / (2 (k-1)) + 1` and
`m = ⌊log n / (4 log k)⌋`. Counting short cycles and independent `t`-sets gives a graph on `Fin n`
with girth `> m` and chromatic number `> k - 1`, because `24 (k-1)^2 < k^4`. Removing the
vertices one at a time lowers the chromatic number by at most one each step, so some induced
subgraph has chromatic number exactly `k`, and its girth is still `> m`. Hence `m ≤ g k n`.
-/

open SimpleGraph Finset
namespace OMA626

variable {n R : ℕ}

def key (u v : Fin n) : Fin n × Fin n := (min u v, max u v)

lemma key_comm (u v : Fin n) : key u v = key v u := by simp [key, min_comm, max_comm]

lemma key_eq {a b c d : Fin n} (h : key a b = key c d) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  simp only [key, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · rw [min_eq_left hab, min_eq_left hcd] at h1; rw [max_eq_right hab, max_eq_right hcd] at h2
    exact Or.inl ⟨h1, h2⟩
  · rw [min_eq_left hab, min_eq_right hcd] at h1; rw [max_eq_right hab, max_eq_left hcd] at h2
    exact Or.inr ⟨h1, h2⟩
  · rw [min_eq_right hab, min_eq_left hcd] at h1; rw [max_eq_left hab, max_eq_right hcd] at h2
    exact Or.inr ⟨h2, h1⟩
  · rw [min_eq_right hab, min_eq_right hcd] at h1; rw [max_eq_left hab, max_eq_left hcd] at h2
    exact Or.inl ⟨h2, h1⟩

lemma key_of_lt {a b : Fin n} (h : a < b) : key a b = (a, b) := by
  simp [key, min_eq_left h.le, max_eq_right h.le]

/-- The graph whose edge `{u, v}` is present when `g` takes the value `0` at `key u v`. -/
def Gr (g : Fin n × Fin n → Fin R) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => (g (key u v)).val = 0

lemma Gr_adj {g : Fin n × Fin n → Fin R} {u v : Fin n} :
    (Gr g).Adj u v ↔ u ≠ v ∧ (g (key u v)).val = 0 := by
  simp only [Gr, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, by rw [key_comm]; exact h'⟩
  · rintro ⟨h, h'⟩; exact ⟨h, Or.inl h'⟩

/-- Number of maps `g` with prescribed values (in `A`) on a set `E` of keys. -/
lemma card_constrained (E : Finset (Fin n × Fin n)) (A : Finset (Fin R)) :
    (univ.filter (fun g : Fin n × Fin n → Fin R => ∀ p ∈ E, g p ∈ A)).card * R ^ E.card =
      A.card ^ E.card * R ^ (n * n) := by
  classical
  have hE : E.card ≤ n * n := by
    have := Finset.card_le_univ E; simpa using this
  have hset : univ.filter (fun g : Fin n × Fin n → Fin R => ∀ p ∈ E, g p ∈ A) =
      Fintype.piFinset (fun p => if p ∈ E then A else univ) := by
    ext g
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h p; split_ifs with hp
      · exact h p hp
      · exact mem_univ _
    · intro h p hp; have := h p; rwa [if_pos hp] at this
  rw [hset, Fintype.card_piFinset]
  have : ∀ p : Fin n × Fin n, ((if p ∈ E then A else univ) : Finset (Fin R)).card =
      if p ∈ E then A.card else R := by
    intro p; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n × Fin n)))
    (fun p => p ∈ E)
  have h2 : (univ.filter (fun p : Fin n × Fin n => p ∈ E)) = E := by ext; simp
  rw [h2] at h1 ⊢
  rw [card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  rw [mul_assoc, ← pow_add]
  congr 2
  omega


lemma succ_succ_ne {j : ℕ} (k k' : Fin (j + 3)) (h1 : k = k' + 1) (h2 : k + 1 = k') : False := by
  have e1 := congrArg Fin.val h1
  have e2 := congrArg Fin.val h2
  rw [Fin.val_add_one] at e1 e2
  have hk := k.isLt; have hk' := k'.isLt
  split_ifs at e1 e2 with c1 c2 c2 <;>
    simp only [Fin.ext_iff, Fin.val_last] at c1 c2 <;> omega

open scoped Classical in
/-- Cycle tuples of length `j + 3` in `Gr g`. -/
noncomputable def T (g : Fin n × Fin n → Fin R) (j : ℕ) : Finset (Fin (j + 3) → Fin n) :=
  univ.filter (fun x => Function.Injective x ∧ ∀ k, (Gr g).Adj (x k) (x (k + 1)))

lemma keys_inj {j : ℕ} {x : Fin (j + 3) → Fin n} (hx : Function.Injective x) :
    Function.Injective (fun k => key (x k) (x (k + 1))) := by
  intro k k' h
  rcases key_eq h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hx h1
  · exact (succ_succ_ne k k' (hx h1) (hx h2)).elim

lemma sum_card_T (j : ℕ) :
    (∑ g : Fin n × Fin n → Fin R, (T g j).card) * R ^ (j + 3) ≤ n ^ (j + 3) * R ^ (n * n) := by
  classical
  have hswap : ∑ g : Fin n × Fin n → Fin R, (T g j).card =
      ∑ x : Fin (j + 3) → Fin n, (univ.filter (fun g : Fin n × Fin n → Fin R =>
        Function.Injective x ∧ ∀ k, (Gr g).Adj (x k) (x (k + 1)))).card := by
    simp only [T, Finset.card_filter]
    convert Finset.sum_comm
  rw [hswap, Finset.sum_mul]
  have hb : ∀ x : Fin (j + 3) → Fin n, (univ.filter (fun g : Fin n × Fin n → Fin R =>
        Function.Injective x ∧ ∀ k, (Gr g).Adj (x k) (x (k + 1)))).card * R ^ (j + 3) ≤
      R ^ (n * n) := by
    intro x
    by_cases hx : Function.Injective x
    · set E := univ.image (fun k => key (x k) (x (k + 1))) with hEdef
      have hEc : E.card = j + 3 := by
        rw [card_image_of_injective _ (keys_inj hx)]; simp
      have hsub : univ.filter (fun g : Fin n × Fin n → Fin R =>
          Function.Injective x ∧ ∀ k, (Gr g).Adj (x k) (x (k + 1))) ⊆
          univ.filter (fun g : Fin n × Fin n → Fin R =>
            ∀ p ∈ E, g p ∈ univ.filter (fun r : Fin R => r.val = 0)) := by
        intro g hg
        simp only [mem_filter, mem_univ, true_and] at hg ⊢
        intro p hp
        obtain ⟨k, -, rfl⟩ := mem_image.1 hp
        exact (Gr_adj.1 (hg.2 k)).2
      have hc := card_constrained (R := R) E (univ.filter (fun r : Fin R => r.val = 0))
      have hA : (univ.filter (fun r : Fin R => r.val = 0)).card ≤ 1 := by
        apply Finset.card_le_one.2
        intro a ha b hb
        simp only [mem_filter] at ha hb
        exact Fin.ext (ha.2.trans hb.2.symm)
      rw [hEc] at hc
      calc _ ≤ (univ.filter (fun g : Fin n × Fin n → Fin R =>
            ∀ p ∈ E, g p ∈ univ.filter (fun r : Fin R => r.val = 0))).card * R ^ (j + 3) :=
            Nat.mul_le_mul_right _ (card_le_card hsub)
        _ = _ := hc
        _ ≤ 1 ^ (j + 3) * R ^ (n * n) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hA _)
        _ = R ^ (n * n) := by simp
    · have : univ.filter (fun g : Fin n × Fin n → Fin R =>
          Function.Injective x ∧ ∀ k, (Gr g).Adj (x k) (x (k + 1))) = ∅ := by
        ext g; simp [hx]
      rw [this]; simp
  calc ∑ x : Fin (j + 3) → Fin n, (univ.filter (fun g : Fin n × Fin n → Fin R =>
        Function.Injective x ∧ ∀ k, (Gr g).Adj (x k) (x (k + 1)))).card * R ^ (j + 3)
        ≤ ∑ _x : Fin (j + 3) → Fin n, R ^ (n * n) :=
        Finset.sum_le_sum fun x _ => hb x
    _ = n ^ (j + 3) * R ^ (n * n) := by simp


open scoped Classical in
/-- Vertices that start a cycle of length at most `m`. -/
noncomputable def D (g : Fin n × Fin n → Fin R) (m : ℕ) : Finset (Fin n) :=
  univ.filter (fun v => ∃ w : (Gr g).Walk v v, w.IsCycle ∧ w.length ≤ m)

lemma card_D_le (g : Fin n × Fin n → Fin R) (m : ℕ) :
    (D g m).card ≤ ∑ j ∈ range (m - 2), (T g j).card := by
  classical
  have hsub : D g m ⊆ (range (m - 2)).biUnion (fun j => (T g j).image (fun x => x 0)) := by
    intro v hv
    simp only [D, mem_filter, mem_univ, true_and] at hv
    obtain ⟨w, hc, hl⟩ := hv
    have hL3 : 3 ≤ w.length := hc.three_le_length
    set j := w.length - 3 with hj
    have hjL : j + 3 = w.length := by omega
    let x : Fin (j + 3) → Fin n := fun k => w.getVert k.val
    have hxT : x ∈ T g j := by
      simp only [T, mem_filter, mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro a b hab
        apply Fin.ext
        have ha := a.isLt; have hb := b.isLt
        exact hc.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
          (by simp only [Set.mem_setOf_eq]; omega) hab
      · intro k
        by_cases hk : k = Fin.last (j + 2)
        · have h1 : (k + 1 : Fin (j + 3)) = 0 := by rw [hk]; exact Fin.last_add_one _
          have h2 : x (k + 1) = w.getVert w.length := by
            simp only [x, h1, Fin.val_zero, Walk.getVert_zero, Walk.getVert_length]
          have h3 : (k : ℕ) = w.length - 1 := by rw [hk]; simp; omega
          have := w.adj_getVert_succ (i := w.length - 1) (by omega)
          rw [show w.length - 1 + 1 = w.length by omega] at this
          rw [h2]; simp only [x, h3]; exact this
        · have h1 : ((k + 1 : Fin (j + 3)) : ℕ) = k + 1 := by
            rw [Fin.val_add_one, if_neg hk]
          have := w.adj_getVert_succ (i := k) (by have := k.isLt; omega)
          simp only [x, h1]; exact this
    refine mem_biUnion.2 ⟨j, mem_range.2 (by omega), mem_image.2 ⟨x, hxT, ?_⟩⟩
    simp [x]
  calc (D g m).card ≤ _ := card_le_card hsub
    _ ≤ ∑ j ∈ range (m - 2), ((T g j).image (fun x => x 0)).card := card_biUnion_le
    _ ≤ _ := sum_le_sum fun j _ => card_image_le


/-- Ordered pairs `a < b` of a set. -/
def I (S : Finset (Fin n)) : Finset (Fin n × Fin n) := (S ×ˢ S).filter (fun p => p.1 < p.2)

lemma two_mul_card_I (S : Finset (Fin n)) : 2 * (I S).card = S.card * S.card - S.card := by
  classical
  rw [← Finset.offDiag_card]
  have hsplit : S.offDiag = I S ∪ (S ×ˢ S).filter (fun p => p.2 < p.1) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_offDiag, I, mem_union, mem_filter, mem_product]
    constructor
    · rintro ⟨ha, hb, hab⟩
      rcases lt_or_gt_of_ne hab with h | h
      · exact Or.inl ⟨⟨ha, hb⟩, h⟩
      · exact Or.inr ⟨⟨ha, hb⟩, h⟩
    · rintro (⟨⟨ha, hb⟩, h⟩ | ⟨⟨ha, hb⟩, h⟩)
      · exact ⟨ha, hb, h.ne⟩
      · exact ⟨ha, hb, h.ne'⟩
  have hdisj : Disjoint (I S) ((S ×ˢ S).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [I, mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hswap : ((S ×ˢ S).filter (fun p => p.2 < p.1)).card = (I S).card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · rintro ⟨a, b⟩ h; simp only [I, mem_filter, mem_product] at h ⊢; exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h; simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.2, h.1⟩
    · rintro ⟨a, b⟩ h
      refine ⟨(b, a), ?_, rfl⟩
      simp only [I, mem_filter, mem_product] at h ⊢; exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
  rw [hsplit, card_union_of_disjoint hdisj, hswap]; ring

lemma nonzero_of_indep {g : Fin n × Fin n → Fin R} {S : Finset (Fin n)}
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ (Gr g).Adj u v) :
    ∀ p ∈ I S, g p ∈ univ.filter (fun r : Fin R => r.val ≠ 0) := by
  rintro ⟨a, b⟩ hp
  simp only [I, mem_filter, mem_product] at hp
  have := hS a hp.1.1 b hp.1.2
  rw [Gr_adj, key_of_lt hp.2] at this
  simp only [mem_filter, mem_univ, true_and]
  exact fun h => this ⟨hp.2.ne, h⟩

lemma card_nonzero (hR : 0 < R) : (univ.filter (fun r : Fin R => r.val ≠ 0)).card = R - 1 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin R)))
    (fun r : Fin R => r.val = 0)
  have h2 : (univ.filter (fun r : Fin R => r.val = 0)) = {⟨0, hR⟩} := by
    ext r; simp [Fin.ext_iff]
  rw [h2, card_singleton, card_univ, Fintype.card_fin] at h1
  simp only [ne_eq]
  omega

lemma exists_good (hn : 0 < n) (hR : 0 < R) (m t : ℕ) (hm : 1 ≤ m)
    (hcyc : ∀ j ∈ range (m - 2), 4 * m * n ^ (j + 3) ≤ n * R ^ (j + 3))
    (hind : 4 * n.choose t * (R - 1) ^ ((t * t - t) / 2) < R ^ ((t * t - t) / 2)) :
    ∃ g : Fin n × Fin n → Fin R, n > 2 * (D g m).card ∧
      ∀ S : Finset (Fin n), S.card = t → ¬ ∀ p ∈ I S, g p ∈ univ.filter (fun r : Fin R => r.val ≠ 0) := by
  classical
  set N := n * n
  set e := (t * t - t) / 2 with he
  -- cycles
  have hX : ∀ j ∈ range (m - 2), 4 * m * ∑ g : Fin n × Fin n → Fin R, (T g j).card ≤ n * R ^ N := by
    intro j hj
    have h1 := sum_card_T (n := n) (R := R) j
    have h2 := hcyc j hj
    have hpos : 0 < R ^ (j + 3) := pow_pos hR _
    have : 4 * m * (∑ g : Fin n × Fin n → Fin R, (T g j).card) * R ^ (j + 3) ≤
        n * R ^ N * R ^ (j + 3) := by
      calc 4 * m * (∑ g : Fin n × Fin n → Fin R, (T g j).card) * R ^ (j + 3)
          = 4 * m * ((∑ g : Fin n × Fin n → Fin R, (T g j).card) * R ^ (j + 3)) := by ring
        _ ≤ 4 * m * (n ^ (j + 3) * R ^ N) := Nat.mul_le_mul_left _ h1
        _ = (4 * m * n ^ (j + 3)) * R ^ N := by ring
        _ ≤ (n * R ^ (j + 3)) * R ^ N := Nat.mul_le_mul_right _ h2
        _ = n * R ^ N * R ^ (j + 3) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hsumD : 4 * ∑ g : Fin n × Fin n → Fin R, (D g m).card ≤ n * R ^ N := by
    have h1 : ∑ g : Fin n × Fin n → Fin R, (D g m).card ≤
        ∑ j ∈ range (m - 2), ∑ g : Fin n × Fin n → Fin R, (T g j).card := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun g _ => card_D_le g m
    have h2 : m * (4 * ∑ j ∈ range (m - 2), ∑ g : Fin n × Fin n → Fin R, (T g j).card) ≤
        m * (n * R ^ N) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      calc ∑ j ∈ range (m - 2), m * (4 * ∑ g : Fin n × Fin n → Fin R, (T g j).card)
          ≤ ∑ _j ∈ range (m - 2), n * R ^ N :=
            Finset.sum_le_sum fun j hj => by have := hX j hj; linarith
        _ = (m - 2) * (n * R ^ N) := by simp
        _ ≤ m * (n * R ^ N) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have h3 := Nat.le_of_mul_le_mul_left h2 (by omega)
    omega
  set bad1 := univ.filter (fun g : Fin n × Fin n → Fin R => n ≤ 2 * (D g m).card)
  have hb1 : 2 * bad1.card ≤ R ^ N := by
    have h1 : n * bad1.card ≤ ∑ g ∈ bad1, 2 * (D g m).card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun g hg => (mem_filter.1 hg).2
    have h2 : ∑ g ∈ bad1, 2 * (D g m).card ≤ ∑ g : Fin n × Fin n → Fin R, 2 * (D g m).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2' : ∑ g : Fin n × Fin n → Fin R, 2 * (D g m).card =
        2 * ∑ g : Fin n × Fin n → Fin R, (D g m).card := by rw [Finset.mul_sum]
    have h3 : n * (2 * bad1.card) ≤ n * R ^ N := by
      have : n * (2 * bad1.card) = 2 * (n * bad1.card) := by ring
      omega
    exact Nat.le_of_mul_le_mul_left h3 hn
  set bad2 := univ.filter (fun g : Fin n × Fin n → Fin R => ∃ S ∈ powersetCard t (univ : Finset (Fin n)),
    ∀ p ∈ I S, g p ∈ univ.filter (fun r : Fin R => r.val ≠ 0))
  have hb2 : 4 * bad2.card < R ^ N := by
    have hsub : bad2 ⊆ (powersetCard t (univ : Finset (Fin n))).biUnion (fun S =>
        univ.filter (fun g : Fin n × Fin n → Fin R =>
          ∀ p ∈ I S, g p ∈ univ.filter (fun r : Fin R => r.val ≠ 0))) := by
      intro g hg
      obtain ⟨S, hS, hp⟩ := (mem_filter.1 hg).2
      exact mem_biUnion.2 ⟨S, hS, mem_filter.2 ⟨mem_univ _, hp⟩⟩
    have heach : ∀ S ∈ powersetCard t (univ : Finset (Fin n)),
        (univ.filter (fun g : Fin n × Fin n → Fin R =>
          ∀ p ∈ I S, g p ∈ univ.filter (fun r : Fin R => r.val ≠ 0))).card * R ^ e =
        (R - 1) ^ e * R ^ N := by
      intro S hS
      have hSc : S.card = t := (mem_powersetCard.1 hS).2
      have hIc : (I S).card = e := by
        have := two_mul_card_I S; rw [hSc] at this; rw [he]; omega
      have := card_constrained (R := R) (I S) (univ.filter (fun r : Fin R => r.val ≠ 0))
      rwa [card_nonzero hR, hIc] at this
    have h1 : bad2.card * R ^ e ≤ n.choose t * ((R - 1) ^ e * R ^ N) := by
      calc bad2.card * R ^ e ≤ (∑ S ∈ powersetCard t (univ : Finset (Fin n)),
            (univ.filter (fun g : Fin n × Fin n → Fin R =>
              ∀ p ∈ I S, g p ∈ univ.filter (fun r : Fin R => r.val ≠ 0))).card) * R ^ e :=
            Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
        _ = ∑ S ∈ powersetCard t (univ : Finset (Fin n)), (R - 1) ^ e * R ^ N := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl heach
        _ = n.choose t * ((R - 1) ^ e * R ^ N) := by simp
    have hpos : 0 < R ^ e := pow_pos hR _
    have h2 : 4 * bad2.card * R ^ e < R ^ N * R ^ e := by
      calc 4 * bad2.card * R ^ e = 4 * (bad2.card * R ^ e) := by ring
        _ ≤ 4 * (n.choose t * ((R - 1) ^ e * R ^ N)) := Nat.mul_le_mul_left _ h1
        _ = (4 * n.choose t * (R - 1) ^ e) * R ^ N := by ring
        _ < R ^ e * R ^ N := Nat.mul_lt_mul_of_pos_right hind (pow_pos hR _)
        _ = R ^ N * R ^ e := by ring
    exact Nat.lt_of_mul_lt_mul_right h2
  have hlt : (bad1 ∪ bad2).card < (univ : Finset (Fin n × Fin n → Fin R)).card := by
    rw [card_univ, Fintype.card_fun, Fintype.card_prod]
    simp only [Fintype.card_fin]
    change _ < R ^ N
    have := card_union_le bad1 bad2
    omega
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨g, ?_, ?_⟩
  · by_contra h
    exact hg (mem_union_left _ (mem_filter.2 ⟨mem_univ _, by omega⟩))
  · intro S hS hp
    exact hg (mem_union_right _ (mem_filter.2 ⟨mem_univ _, S, mem_powersetCard.2
      ⟨subset_univ _, hS⟩, hp⟩))


lemma big (hn : 0 < n) (hR : 0 < R) (m t : ℕ) (hm : 1 ≤ m)
    (hcyc : ∀ j ∈ range (m - 2), 4 * m * n ^ (j + 3) ≤ n * R ^ (j + 3))
    (hind : 4 * n.choose t * (R - 1) ^ ((t * t - t) / 2) < R ^ ((t * t - t) / 2)) :
    ∃ c : ℕ, (∃ G : SimpleGraph (Fin n), (m : ℕ∞) < G.egirth ∧ G.chromaticNumber = c) ∧
      n < 2 * (c * (t - 1)) := by
  classical
  obtain ⟨g, hD, hI⟩ := exists_good hn hR m t hm hcyc hind
  set Dg := D g m with hDg
  let G' : SimpleGraph (Fin n) :=
    SimpleGraph.fromRel fun u v => (Gr g).Adj u v ∧ u ∉ Dg ∧ v ∉ Dg
  have hG' : ∀ u v, G'.Adj u v ↔ (Gr g).Adj u v ∧ u ∉ Dg ∧ v ∉ Dg := by
    intro u v
    simp only [G', SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, h | h⟩
      · exact h
      · exact ⟨h.1.symm, h.2.2, h.2.1⟩
    · intro h; exact ⟨h.1.ne, Or.inl h⟩
  have hle : G' ≤ Gr g := fun u v h => ((hG' u v).1 h).1
  have hgirth : (m : ℕ∞) < G'.egirth := by
    rw [← ENat.add_one_le_iff (ENat.coe_ne_top m), SimpleGraph.le_egirth]
    intro a w hw
    by_contra hlt
    have hL : w.length ≤ m := by
      by_contra h
      exact hlt (by exact_mod_cast (show m + 1 ≤ w.length by omega))
    have h3 : 3 ≤ w.length := hw.three_le_length
    have hadj := w.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero] at hadj
    have ha : a ∉ Dg := ((hG' _ _).1 hadj).2.1
    apply ha
    rw [hDg]
    simp only [D, mem_filter, mem_univ, true_and]
    exact ⟨w.mapLe hle, hw.mapLe hle, by rw [Walk.length_mapLe]; exact hL⟩
  have hfin : G'.chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) SimpleGraph.chromaticNumber_le_card
  set c := G'.chromaticNumber.toNat with hcdef
  refine ⟨c, ⟨G', hgirth, (ENat.coe_toNat hfin).symm⟩, ?_⟩
  obtain ⟨C⟩ := G'.colorable_chromaticNumber_of_fintype
  set K := (univ : Finset (Fin n)) \ Dg
  have hKc : K.card = n - Dg.card := by
    rw [card_sdiff, inter_univ, card_univ, Fintype.card_fin]
  have hclass : ∀ i : Fin c, (K.filter (fun v => C v = i)).card ≤ t - 1 := by
    intro i
    by_contra hcon
    obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (show t ≤ (K.filter (fun v => C v = i)).card by omega)
    apply hI S hSc
    apply nonzero_of_indep
    intro u hu v hv hadj
    have hu' := hS hu; have hv' := hS hv
    simp only [K, mem_filter, mem_sdiff, mem_univ, true_and] at hu' hv'
    have : G'.Adj u v := (hG' u v).2 ⟨hadj, hu'.1, hv'.1⟩
    exact C.valid this (hu'.2.trans hv'.2.symm)
  have hKle : K.card ≤ c * (t - 1) := by
    rw [card_eq_sum_card_fiberwise (f := fun v => C v) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
    calc ∑ i : Fin c, (K.filter (fun v => C v = i)).card ≤ ∑ _i : Fin c, (t - 1) :=
          sum_le_sum fun i _ => hclass i
      _ = c * (t - 1) := by simp
  omega



lemma numB2 (n R t : ℕ) (hR : 1 ≤ R) (ht1 : 1 ≤ t)
    (ht : R * (2 * n + 6) ≤ (t - 1) ^ 2) :
    4 * n.choose t * (R - 1) ^ ((t * t - t) / 2) < R ^ ((t * t - t) / 2) := by
  set e := (t * t - t) / 2 with he
  have he2 : 2 * e = t * t - t := by
    rw [he]; apply Nat.two_mul_div_two_of_even
    have := Nat.even_mul_pred_self t
    rwa [Nat.mul_sub_one] at this
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := by linarith
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have heR : 2 * (e : ℝ) = t * t - t := by
    have : t ≤ t * t := Nat.le_mul_self t
    have h := congrArg (fun k : ℕ => (k : ℝ)) he2
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    rw [h, Nat.cast_sub this]; push_cast; ring
  have htR' : (R : ℝ) * (2 * n + 6) ≤ ((t : ℝ) - 1) ^ 2 := by
    have h := (Nat.cast_le (α := ℝ)).2 ht
    push_cast [Nat.cast_sub ht1] at h
    exact h
  have heR2 : (n : ℝ) + 3 ≤ e / R := by
    rw [le_div_iff₀ hRpos]; nlinarith
  have hcast : ((R - 1 : ℕ) : ℝ) = R - 1 := by rw [Nat.cast_sub hR]; simp
  suffices h : 4 * (n.choose t : ℝ) * ((R : ℝ) - 1) ^ e < (R : ℝ) ^ e by
    rw [← hcast] at h; exact_mod_cast h
  have hch : (n.choose t : ℝ) ≤ Real.exp n := by
    have h1 : (n.choose t : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.choose_le_two_pow n t
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (n.choose t : ℝ) ≤ (2 : ℝ) ^ n := h1
      _ ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) h2 n
      _ = Real.exp n := by rw [← Real.exp_nat_mul]; simp
  have hb0 : 0 ≤ 1 - 1 / (R : ℝ) := by
    rw [sub_nonneg, div_le_one hRpos]; exact hRR
  have hb1 : 1 - 1 / (R : ℝ) ≤ Real.exp (-(1 / (R : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (R : ℝ))); linarith
  have hpow : (1 - 1 / (R : ℝ)) ^ e ≤ Real.exp (-(e / (R : ℝ))) := by
    calc (1 - 1 / (R : ℝ)) ^ e ≤ Real.exp (-(1 / (R : ℝ))) ^ e := pow_le_pow_left₀ hb0 hb1 e
      _ = Real.exp (-(e / (R : ℝ))) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hfac : (R : ℝ) - 1 = R * (1 - 1 / R) := by field_simp
  have h3 : Real.exp n * Real.exp (-(e / (R : ℝ))) ≤ Real.exp (-3) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  have h4 : 4 * Real.exp (-3) < 1 := by
    have := Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)
    rw [Real.exp_neg]
    have hp : 0 < Real.exp 3 := Real.exp_pos 3
    rw [mul_inv_lt_iff₀ hp]; linarith
  have hRe : 0 < (R : ℝ) ^ e := pow_pos hRpos e
  rw [hfac, mul_pow]
  calc 4 * (n.choose t : ℝ) * ((R : ℝ) ^ e * (1 - 1 / (R : ℝ)) ^ e)
      ≤ 4 * Real.exp n * ((R : ℝ) ^ e * Real.exp (-(e / (R : ℝ)))) := by gcongr
    _ = (R : ℝ) ^ e * (4 * (Real.exp n * Real.exp (-(e / (R : ℝ))))) := by ring
    _ ≤ (R : ℝ) ^ e * (4 * Real.exp (-3)) := by gcongr
    _ < (R : ℝ) ^ e * 1 := mul_lt_mul_of_pos_left h4 hRe
    _ = (R : ℝ) ^ e := mul_one _

/-- The subgraph of `G` keeping only edges between vertices of index at least `i`. -/
def Hs (G : SimpleGraph (Fin n)) (i : ℕ) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ i ≤ u.val ∧ i ≤ v.val
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma Hs_adj {G : SimpleGraph (Fin n)} {i : ℕ} {u v : Fin n} :
    (Hs G i).Adj u v ↔ G.Adj u v ∧ i ≤ u.val ∧ i ≤ v.val := Iff.rfl

lemma Hs_le (G : SimpleGraph (Fin n)) (i : ℕ) : Hs G i ≤ G := fun _ _ h => (Hs_adj.1 h).1

lemma Hs_zero (G : SimpleGraph (Fin n)) : Hs G 0 = G := by
  ext u v; simp [Hs_adj]

lemma Hs_step (G : SimpleGraph (Fin n)) (i : ℕ) :
    (Hs G i).chromaticNumber ≤ (Hs G (i + 1)).chromaticNumber + 1 := by
  have hfin : (Hs G (i + 1)).chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) SimpleGraph.chromaticNumber_le_card
  set a := (Hs G (i + 1)).chromaticNumber.toNat with ha
  obtain ⟨C⟩ := (Hs G (i + 1)).colorable_chromaticNumber_of_fintype
  let C' : (Hs G i).Coloring (Fin (a + 1)) :=
    SimpleGraph.Coloring.mk (fun v => if v.val = i then Fin.last a else (C v).castSucc) (by
      intro u v huv
      have hne : u ≠ v := (Hs G i).ne_of_adj huv
      by_cases hu : u.val = i <;> by_cases hv : v.val = i
      · exact absurd (Fin.ext (hu.trans hv.symm)) hne
      · simp only [hu, hv, if_true, if_false]
        exact (Fin.castSucc_lt_last _).ne'
      · simp only [hu, hv, if_true, if_false]
        exact (Fin.castSucc_lt_last _).ne
      · simp only [hu, hv, if_false]
        intro heq
        have huv' := Hs_adj.1 huv
        have h2 : (Hs G (i + 1)).Adj u v := Hs_adj.2 ⟨huv'.1, by have := huv'.2.1; omega,
          by have := huv'.2.2; omega⟩
        exact C.valid h2 (Fin.castSucc_injective _ heq))
  have h1 : (Hs G i).chromaticNumber ≤ ((a + 1 : ℕ) : ℕ∞) :=
    SimpleGraph.Colorable.chromaticNumber_le ⟨C'⟩
  rw [← ENat.coe_toNat hfin, ← ha]
  simpa using h1

lemma Hs_last (G : SimpleGraph (Fin n)) : (Hs G n).chromaticNumber ≤ 1 := by
  apply SimpleGraph.Colorable.chromaticNumber_le
  refine ⟨SimpleGraph.Coloring.mk (fun _ => 0) ?_⟩
  intro u v h
  exfalso
  have := (Hs_adj.1 h).2.1; have := u.isLt; omega

lemma ivt (f : ℕ → ℕ∞) (k : ℕ) (hstep : ∀ i, f i ≤ f (i + 1) + 1) :
    ∀ N, (k : ℕ∞) ≤ f 0 → f N < k → ∃ i, f i = k := by
  intro N
  induction N with
  | zero => intro h1 h2; exact absurd h1 (not_le.2 h2)
  | succ N ih =>
    intro h1 h2
    by_cases hN : f N < k
    · exact ih h1 hN
    · push_neg at hN
      refine ⟨N, le_antisymm ?_ hN⟩
      calc f N ≤ f (N + 1) + 1 := hstep N
        _ ≤ k := Order.add_one_le_of_lt h2

lemma exists_sub_chi (G : SimpleGraph (Fin n)) (k : ℕ) (hk : 2 ≤ k)
    (hG : (k : ℕ∞) ≤ G.chromaticNumber) :
    ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.chromaticNumber = k := by
  obtain ⟨i, hi⟩ := ivt (fun i => (Hs G i).chromaticNumber) k (Hs_step G) n
    (by simpa [Hs_zero] using hG)
    (lt_of_le_of_lt (Hs_last G) (by exact_mod_cast (show 1 < k by omega)))
  exact ⟨Hs G i, Hs_le G i, hi⟩

lemma cycle_len_le {G : SimpleGraph (Fin n)} {a : Fin n} (w : G.Walk a a) (hw : w.IsCycle) :
    w.length ≤ n := by
  cases w with
  | nil => exact absurd hw SimpleGraph.Walk.IsCycle.not_of_nil
  | cons h p =>
    have hp := ((SimpleGraph.Walk.cons_isCycle_iff p h).1 hw).1
    have := hp.length_lt
    simp only [Fintype.card_fin] at this
    simp only [SimpleGraph.Walk.length_cons]
    omega


lemma bdd (k n : ℕ) (hk : 3 ≤ k) :
    BddAbove {m : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ (m : ℕ∞) < G.egirth} := by
  refine ⟨n, ?_⟩
  rintro m ⟨G, hχ, hm⟩
  have hac : ¬ G.IsAcyclic := by
    intro hA
    have := hA.chromaticNumber_le_two
    rw [hχ] at this
    have : k ≤ 2 := by exact_mod_cast this
    omega
  obtain ⟨a, w, hw, hl⟩ := SimpleGraph.exists_egirth_eq_length.2 hac
  rw [hl] at hm
  have h1 : m < w.length := by exact_mod_cast hm
  have := cycle_len_le w hw
  omega

lemma core (k n m : ℕ) (hk : 4 ≤ k) (hn : 12 * k ≤ n) (hn2 : 12 * (k - 1) ^ 2 ≤ n)
    (hm : 1 ≤ m) (hE : 4 * m * (24 * (k - 1) ^ 2) ^ m ≤ n) : m ≤ Erdos626.g k n := by
  set q := 2 * (k - 1) with hq
  have hq1 : 6 ≤ q := by omega
  set s := n / q with hs
  set R := n / (3 * q ^ 2) with hRdef
  have hQ : 0 < 3 * q ^ 2 := by positivity
  have hnQ : 3 * q ^ 2 ≤ n := by
    have : 3 * q ^ 2 = 12 * (k - 1) ^ 2 := by rw [hq]; ring
    omega
  have hR : 0 < R := Nat.div_pos hnQ hQ
  have h1 : 3 * q ^ 2 * R ≤ n := Nat.mul_div_le n (3 * q ^ 2)
  have h1' : n < 3 * q ^ 2 * R + 3 * q ^ 2 := by
    have e1 : 3 * q ^ 2 * R + n % (3 * q ^ 2) = n := Nat.div_add_mod n _
    have e2 := Nat.mod_lt n hQ
    linarith
  have hE6 : n ≤ 24 * (k - 1) ^ 2 * R := by
    have : 24 * (k - 1) ^ 2 = 6 * q ^ 2 := by rw [hq]; ring
    rw [this]; nlinarith
  have h2 : q * s ≤ n := Nat.mul_div_le n q
  have h2' : n < q * s + q := by
    have e1 : q * s + n % q = n := Nat.div_add_mod n _
    have e2 := Nat.mod_lt n (show 0 < q by omega)
    linarith
  have hcyc : ∀ j ∈ range (m - 2), 4 * m * n ^ (j + 3) ≤ n * R ^ (j + 3) := by
    intro j hj
    rw [mem_range] at hj
    have hj3 : j + 3 ≤ m := by omega
    have hEpos : 1 ≤ 24 * (k - 1) ^ 2 := by
      have : 1 ≤ (k - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    calc 4 * m * n ^ (j + 3) ≤ 4 * m * (24 * (k - 1) ^ 2 * R) ^ (j + 3) := by
          gcongr
      _ = 4 * m * (24 * (k - 1) ^ 2) ^ (j + 3) * R ^ (j + 3) := by ring
      _ ≤ 4 * m * (24 * (k - 1) ^ 2) ^ m * R ^ (j + 3) := by
          gcongr
          all_goals omega
      _ ≤ n * R ^ (j + 3) := by gcongr
  have hsq : R * (2 * n + 6) ≤ s ^ 2 := by
    have h3 : n * (2 * n + 6) ≤ 3 * (q * s) ^ 2 := by
      have hz : ((n : ℤ) - q) ≤ (q : ℤ) * s := by push_cast at h2' ⊢; linarith
      have hz0 : (0 : ℤ) ≤ (n : ℤ) - q := by
        have : q ≤ n := by omega
        have : (q : ℤ) ≤ n := by exact_mod_cast this
        linarith
      have hn' : (12 : ℤ) * k ≤ n := by exact_mod_cast hn
      have hq' : (q : ℤ) = 2 * ((k : ℤ) - 1) := by
        have : q + 2 = 2 * k := by omega
        have : (q : ℤ) + 2 = 2 * k := by exact_mod_cast this
        linarith
      have : ((n : ℤ) - q) ^ 2 ≤ ((q : ℤ) * s) ^ 2 := pow_le_pow_left₀ hz0 hz 2
      have key : (n : ℤ) * (2 * n + 6) ≤ 3 * ((q : ℤ) * s) ^ 2 := by nlinarith
      exact_mod_cast key
    have h4 : 3 * q ^ 2 * (R * (2 * n + 6)) ≤ 3 * q ^ 2 * s ^ 2 := by
      calc 3 * q ^ 2 * (R * (2 * n + 6)) = (3 * q ^ 2 * R) * (2 * n + 6) := by ring
        _ ≤ n * (2 * n + 6) := by gcongr
        _ ≤ 3 * (q * s) ^ 2 := h3
        _ = 3 * q ^ 2 * s ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_left h4 hQ
  have hind := numB2 n R (s + 1) hR (Nat.le_add_left 1 s) (by simpa using hsq)
  obtain ⟨c, ⟨G, hgirth, hχ⟩, hcn⟩ := big (n := n) (R := R) (by omega) hR m (s + 1) hm hcyc hind
  simp only [Nat.add_sub_cancel] at hcn
  have hck : k ≤ c := by
    have : (k - 1) * s < c * s := by
      have : 2 * ((k - 1) * s) < 2 * (c * s) := by
        calc 2 * ((k - 1) * s) = q * s := by rw [hq]; ring
          _ < 2 * (c * s) := by omega
      omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  have hkG : (k : ℕ∞) ≤ G.chromaticNumber := by rw [hχ]; exact_mod_cast hck
  obtain ⟨H, hHG, hHχ⟩ := exists_sub_chi G k (by omega) hkG
  have hHg : (m : ℕ∞) < H.egirth := lt_of_lt_of_le hgirth (SimpleGraph.egirth_anti hHG)
  exact le_csSup (bdd k n (by omega)) ⟨H, hHχ, hHg⟩

end OMA626

namespace OMA626

lemma E_lt (k : ℕ) (hk : 4 ≤ k) : 24 * (k - 1) ^ 2 < k ^ 4 := by
  rcases Nat.eq_or_lt_of_le hk with h | h
  · subst h; norm_num
  · have h1 : (k - 1) ^ 2 < k ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    have h2 : 25 ≤ k ^ 2 := by nlinarith
    calc 24 * (k - 1) ^ 2 < 24 * k ^ 2 := by omega
      _ < k ^ 2 * k ^ 2 := by nlinarith
      _ = k ^ 4 := by ring

end OMA626

open Filter in
theorem OMA.solution : type_of% @Erdos626.erdos_626.variants.kostochka := by
  intro k hk ε hε
  set Eₙ : ℕ := 24 * (k - 1) ^ 2 with hEₙ
  have hE1 : 1 ≤ Eₙ := by
    have : 1 ≤ (k - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  set E : ℝ := (Eₙ : ℝ) with hEdef
  have hE1r : (1 : ℝ) ≤ E := by rw [hEdef]; exact_mod_cast hE1
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  set L := Real.log k with hL
  have hL0 : 0 < L := Real.log_pos hk1
  have hEk : Real.log E < 4 * L := by
    have h : E < (k : ℝ) ^ 4 := by
      have h0 : Eₙ < k ^ 4 := OMA626.E_lt k hk
      rw [hEdef]; exact_mod_cast h0
    have := Real.log_lt_log (by linarith) h
    rwa [Real.log_pow] at this
  set θ := Real.log E / (4 * L) with hθ
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; exact hEk
  have hθ0 : 0 ≤ θ := div_nonneg (Real.log_nonneg hE1r) (by linarith)
  have hr : 0 < 1 - θ := by linarith
  have hB : ∀ᶠ x : ℝ in atTop, Real.log x ≤ L * x ^ (1 - θ) := by
    have := (isLittleO_log_rpow_atTop hr).bound hL0
    filter_upwards [this, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    exact hx
  have hC : ∀ᶠ x : ℝ in atTop, 1 / ε ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hB' := tendsto_natCast_atTop_atTop.eventually hB
  have hC' := tendsto_natCast_atTop_atTop.eventually hC
  filter_upwards [hB', hC', eventually_ge_atTop (12 * k + 12 * (k - 1) ^ 2 + k ^ 4)] with n hBn hCn hn
  have hn0 : 0 < n := by have := Nat.one_le_pow 4 k (by omega); omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  set x := Real.log n / (4 * L) with hx
  have hk4 : (k : ℝ) ^ 4 ≤ n := by exact_mod_cast (show k ^ 4 ≤ n by omega)
  have hlogn : 4 * L ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hk4
    rwa [Real.log_pow] at this
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ (by linarith)]; linarith
  set m := ⌊x⌋₊ with hm
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hx1)
  have hmx : (m : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  have hEm : 4 * m * Eₙ ^ m ≤ n := by
    have hpow : E ^ m ≤ (n : ℝ) ^ θ := by
      rw [← Real.rpow_natCast]
      calc E ^ (m : ℝ) ≤ E ^ x := Real.rpow_le_rpow_of_exponent_le hE1r hmx
        _ = (n : ℝ) ^ θ := by
          rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hnr, hx, hθ]
          congr 1; ring
    have h4m : 4 * (m : ℝ) ≤ Real.log n / L := by
      have : 4 * x = Real.log n / L := by rw [hx]; field_simp
      linarith
    have hlog : Real.log n / L ≤ (n : ℝ) ^ (1 - θ) := by
      rw [div_le_iff₀ hL0]; linarith
    have hfin : (4 * m * Eₙ ^ m : ℝ) ≤ n := by
      have hE0 : (0 : ℝ) ≤ E ^ m := by positivity
      calc (4 * m * Eₙ ^ m : ℝ) = 4 * (m : ℝ) * E ^ m := by rw [hEdef]
        _ ≤ (n : ℝ) ^ (1 - θ) * (n : ℝ) ^ θ := by
          apply mul_le_mul (h4m.trans hlog) hpow hE0 (by positivity)
        _ = n := by rw [← Real.rpow_add hnr]; simp
    exact_mod_cast hfin
  have hg := OMA626.core k n m hk (by omega) (by omega) hm1 hEm
  have hgr : (m : ℝ) ≤ (Erdos626.g k n : ℝ) := by exact_mod_cast hg
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hεl : 1 ≤ ε * Real.log n := by
    rw [div_le_iff₀ hε] at hCn; linarith
  calc (1 / (4 * Real.log k) - ε) * Real.log n = x - ε * Real.log n := by
        rw [hx, ← hL]; ring
    _ ≤ m := by linarith
    _ ≤ Erdos626.g k n := hgr
