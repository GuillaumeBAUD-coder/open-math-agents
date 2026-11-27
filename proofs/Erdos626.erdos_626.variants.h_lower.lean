import FormalConjectures.ErdosProblems.«626»

-- Problem: Erdős Problem 626 — lower bound for h^(m)(n)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/626.lean:137 (declaration Erdos626.erdos_626.variants.h_lower)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Erdős 626: graphs of large girth and polynomially large chromatic number

Erdős's deletion argument, done by counting instead of probability. A map
`g : Fin n × Fin n → Fin R` defines the graph where `u < v` are adjacent when `g (u, v) = 0`
(edge density `1/R`, with `R = ⌈n^(1 - 3/(4m))⌉`). Summing over all `R^(n²)` maps:
* a fixed cycle of length `ℓ ≥ 3` needs `ℓ` distinct values equal to `0`, so the total number of
  cycle tuples of length at most `m` is at most `R^(n²) · Σ (n/R)^ℓ ≤ R^(n²) · n/4`;
* a fixed `t`-set is independent for `(R-1)^(t(t-1)/2) R^(n² - t(t-1)/2)` maps, and with
  `t = ⌈2R(log n + 1)⌉ + 1` the union over all `t`-sets is below `R^(n²)/4`.
So some map has fewer than `n/2` vertices starting a short cycle and no independent `t`-set.
Deleting the edges at those vertices leaves girth `> m`, and the other `> n/2` vertices force
`χ ≥ n / (2(t-1)) ≥ n^(1/(2m))` for large `n`. Hence the statement holds with `c = 1/2`.
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



lemma numA (m n R : ℕ) (hm : 1 ≤ m) (hx1 : (1 : ℝ) ≤ n)
    (hR : ((n : ℝ) ^ (1 - 3 / (4 * (m : ℝ)))) ≤ R) (h1 : 4 * (m : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ)) :
    ∀ j ∈ Finset.range (m - 2), 4 * m * n ^ (j + 3) ≤ n * R ^ (j + 3) := by
  intro j hj
  have hjm : j + 3 ≤ m := by have := Finset.mem_range.1 hj; omega
  set x : ℝ := (n : ℝ) with hxdef
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set θ : ℝ := 3 / (4 * (m : ℝ)) with hθ
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by positivity)]; linarith
  have hx0 : 0 < x := by linarith
  set a := x ^ (1 - θ)
  set b := x ^ θ
  have hb1 : 1 ≤ b := Real.one_le_rpow hx1 (by positivity)
  have ha0 : 0 ≤ a := by positivity
  have hab : b * a = x := by
    rw [← Real.rpow_add hx0]; simp
  have hbm : b ^ m = x ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; rw [hθ]; field_simp
  have hx34 : x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have key : 4 * (m : ℝ) * (x : ℝ) ^ (j + 3) ≤ x * (R : ℝ) ^ (j + 3) := by
    have e1 : x ^ (j + 3) = b ^ (j + 3) * a ^ (j + 3) := by rw [← mul_pow, hab]
    have e2 : b ^ (j + 3) ≤ b ^ m := pow_le_pow_right₀ hb1 hjm
    have e3 : a ^ (j + 3) ≤ (R : ℝ) ^ (j + 3) := pow_le_pow_left₀ ha0 hR _
    have e4 : 4 * (m : ℝ) * b ^ m ≤ x := by
      rw [hbm]; nlinarith [Real.rpow_nonneg hx0.le (3 / 4 : ℝ)]
    have hapos : 0 ≤ a ^ (j + 3) := pow_nonneg ha0 _
    calc 4 * (m : ℝ) * x ^ (j + 3) = 4 * (m : ℝ) * b ^ (j + 3) * a ^ (j + 3) := by rw [e1]; ring
      _ ≤ 4 * (m : ℝ) * b ^ m * a ^ (j + 3) := by gcongr
      _ ≤ x * a ^ (j + 3) := by gcongr
      _ ≤ x * (R : ℝ) ^ (j + 3) := by gcongr
  have key' : ((4 * m * n ^ (j + 3) : ℕ) : ℝ) ≤ ((n * R ^ (j + 3) : ℕ) : ℝ) := by
    push_cast; exact key
  exact_mod_cast key'

lemma numB (n R t : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) (ht3 : 3 ≤ t)
    (ht : 2 * (R : ℝ) * (Real.log n + 1) ≤ (t : ℝ) - 1) :
    4 * n.choose t * (R - 1) ^ ((t * t - t) / 2) < R ^ ((t * t - t) / 2) := by
  set e := (t * t - t) / 2 with he
  have he2 : 2 * e = t * t - t := by
    rw [he]; apply Nat.two_mul_div_two_of_even
    have := Nat.even_mul_pred_self t
    rwa [Nat.mul_sub_one] at this
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := by linarith
  have hxR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht3
  have heR : 2 * (e : ℝ) = t * t - t := by
    have : t ≤ t * t := Nat.le_mul_self t
    have h := congrArg (fun k : ℕ => (k : ℝ)) he2
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    rw [h, Nat.cast_sub this]; push_cast; ring
  set L := Real.log n
  have hL0 : 0 ≤ L := Real.log_nonneg hxR
  have heR2 : (t : ℝ) * (L + 1) ≤ e / R := by
    rw [le_div_iff₀ hRpos]; nlinarith
  have hcast : ((R - 1 : ℕ) : ℝ) = R - 1 := by rw [Nat.cast_sub hR]; simp
  suffices h : 4 * (n.choose t : ℝ) * ((R : ℝ) - 1) ^ e < (R : ℝ) ^ e by
    rw [← hcast] at h; exact_mod_cast h
  have hch : (n.choose t : ℝ) ≤ (n : ℝ) ^ t := by exact_mod_cast Nat.choose_le_pow n t
  have hxt : (n : ℝ) ^ t = Real.exp (t * L) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hb0 : 0 ≤ 1 - 1 / (R : ℝ) := by
    rw [sub_nonneg, div_le_one hRpos]; exact hRR
  have hb1 : 1 - 1 / (R : ℝ) ≤ Real.exp (-(1 / (R : ℝ))) := by
    have := Real.add_one_le_exp (-(1 / (R : ℝ))); linarith
  have hpow : (1 - 1 / (R : ℝ)) ^ e ≤ Real.exp (-(e / (R : ℝ))) := by
    calc (1 - 1 / (R : ℝ)) ^ e ≤ Real.exp (-(1 / (R : ℝ))) ^ e := pow_le_pow_left₀ hb0 hb1 e
      _ = Real.exp (-(e / (R : ℝ))) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hfac : (R : ℝ) - 1 = R * (1 - 1 / R) := by field_simp
  have h3 : Real.exp (t * L) * Real.exp (-(e / (R : ℝ))) ≤ Real.exp (-3) := by
    rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
  have h4 : 4 * Real.exp (-3) < 1 := by
    have := Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)
    rw [Real.exp_neg]
    have hp : 0 < Real.exp 3 := Real.exp_pos 3
    rw [mul_inv_lt_iff₀ hp]; linarith
  have hRe : 0 < (R : ℝ) ^ e := pow_pos hRpos e
  rw [hfac, mul_pow]
  calc 4 * (n.choose t : ℝ) * ((R : ℝ) ^ e * (1 - 1 / (R : ℝ)) ^ e)
      ≤ 4 * Real.exp (t * L) * ((R : ℝ) ^ e * Real.exp (-(e / (R : ℝ)))) := by
        rw [← hxt]; gcongr
    _ = (R : ℝ) ^ e * (4 * (Real.exp (t * L) * Real.exp (-(e / (R : ℝ))))) := by ring
    _ ≤ (R : ℝ) ^ e * (4 * Real.exp (-3)) := by gcongr
    _ < (R : ℝ) ^ e * 1 := mul_lt_mul_of_pos_left h4 hRe
    _ = (R : ℝ) ^ e := mul_one _


lemma numC (m n R t c : ℕ) (hm : 1 ≤ m) (hx1 : (1 : ℝ) ≤ n) (ht1 : 1 ≤ t)
    (hRa : (R : ℝ) < (n : ℝ) ^ (1 - 3 / (4 * (m : ℝ))) + 1)
    (ht : (t : ℝ) - 1 < 2 * R * (Real.log n + 1) + 1)
    (h2 : 10 * (Real.log n + 1) ≤ (n : ℝ) ^ (1 / (4 * (m : ℝ))))
    (hc : n < 2 * (c * (t - 1))) :
    (n : ℝ) ^ (1 / (2 * (m : ℝ))) ≤ c := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < n := by linarith
  have hθ1 : 3 / (4 * (m : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  set a := (n : ℝ) ^ (1 - 3 / (4 * (m : ℝ)))
  set p := (n : ℝ) ^ (1 / (2 * (m : ℝ)))
  set q := (n : ℝ) ^ (1 / (4 * (m : ℝ)))
  have ha1 : 1 ≤ a := Real.one_le_rpow hx1 (by linarith)
  have hp0 : 0 ≤ p := by positivity
  have hpaq : p * a * q = n := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    have : 1 / (2 * (m : ℝ)) + (1 - 3 / (4 * (m : ℝ))) + 1 / (4 * (m : ℝ)) = 1 := by
      field_simp; ring
    rw [this, Real.rpow_one]
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hx1
  have hcast : ((t - 1 : ℕ) : ℝ) = t - 1 := by rw [Nat.cast_sub ht1]; simp
  have hcR : (n : ℝ) < 2 * (c * ((t : ℝ) - 1)) := by
    rw [← hcast]; exact_mod_cast hc
  have ht0 : (0 : ℝ) ≤ (t : ℝ) - 1 := by rw [← hcast]; positivity
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have htb : (t : ℝ) - 1 ≤ 5 * a * (Real.log n + 1) := by
    have : 2 * (R : ℝ) * (Real.log n + 1) ≤ 2 * (a + 1) * (Real.log n + 1) := by
      gcongr
    nlinarith
  by_contra hlt
  push_neg at hlt
  have h3 : 2 * ((c : ℝ) * ((t : ℝ) - 1)) ≤ 2 * (p * ((t : ℝ) - 1)) := by
    gcongr
  have h4 : 2 * (p * ((t : ℝ) - 1)) ≤ 2 * (p * (5 * a * (Real.log n + 1))) := by gcongr
  have h5 : 2 * (p * (5 * a * (Real.log n + 1))) = p * a * (10 * (Real.log n + 1)) := by ring
  have h6 : p * a * (10 * (Real.log n + 1)) ≤ p * a * q := by
    apply mul_le_mul_of_nonneg_left h2; positivity
  linarith


open Filter in
theorem main : ∃ c > (0 : ℝ), ∀ m : ℕ, 1 ≤ m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (c / (m : ℝ) - ε) ≤ (Erdos626.h m n : ℝ) := by
  refine ⟨1 / 2, by norm_num, fun m hm ε hε => ?_⟩
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : (0 : ℝ) < 1 / (4 * (m : ℝ)) := by positivity
  have ev1 : ∀ᶠ n : ℕ in atTop, 4 * (m : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev2 : ∀ᶠ n : ℕ in atTop, (20 : ℝ) ≤ (n : ℝ) ^ (1 / (4 * (m : ℝ))) :=
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have ev3 : ∀ᶠ n : ℕ in atTop, ‖Real.log n‖ ≤ (1 / 20) * ‖(n : ℝ) ^ (1 / (4 * (m : ℝ)))‖ :=
    tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_atTop hr).bound (by norm_num))
  filter_upwards [ev1, ev2, ev3, eventually_ge_atTop 1] with n h1 h2a h2b hn
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hx1
  have hq0 : 0 ≤ (n : ℝ) ^ (1 / (4 * (m : ℝ))) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0, abs_of_nonneg hq0] at h2b
  have h2 : 10 * (Real.log n + 1) ≤ (n : ℝ) ^ (1 / (4 * (m : ℝ))) := by linarith
  have hθ1 : 3 / (4 * (m : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  set a := (n : ℝ) ^ (1 - 3 / (4 * (m : ℝ))) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow hx1 (by linarith)
  set R := ⌈a⌉₊ with hRdef
  have hR : 0 < R := Nat.ceil_pos.2 (by linarith)
  have hRa : a ≤ R := Nat.le_ceil a
  have hRa2 : (R : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  set t := ⌈2 * (R : ℝ) * (Real.log n + 1)⌉₊ + 1 with htdef
  have htc : ((t : ℝ) - 1) = (⌈2 * (R : ℝ) * (Real.log n + 1)⌉₊ : ℝ) := by
    rw [htdef]; push_cast; ring
  have htlo : 2 * (R : ℝ) * (Real.log n + 1) ≤ (t : ℝ) - 1 := by rw [htc]; exact Nat.le_ceil _
  have hthi : (t : ℝ) - 1 < 2 * R * (Real.log n + 1) + 1 := by
    rw [htc]; exact Nat.ceil_lt_add_one (by positivity)
  have ht3 : 3 ≤ t := by
    have : 1 < ⌈2 * (R : ℝ) * (Real.log n + 1)⌉₊ := Nat.lt_ceil.2 (by push_cast; nlinarith)
    omega
  obtain ⟨c, ⟨G, hg, hχ⟩, hc⟩ := big (n := n) (R := R) (by omega) hR m t hm
    (numA m n R hm hx1 hRa h1) (numB n R t hn hR ht3 htlo)
  have hpc := numC m n R t c hm hx1 (by omega) hRa2 hthi h2 hc
  have hbdd : BddAbove {c : ℕ | ∃ G : SimpleGraph (Fin n), (m : ℕ∞) < G.egirth ∧
      G.chromaticNumber = c} := by
    refine ⟨n, ?_⟩
    rintro c' ⟨G', -, hG'⟩
    have := G'.chromaticNumber_le_card
    rw [hG', Fintype.card_fin] at this
    exact_mod_cast this
  have hch : c ≤ Erdos626.h m n := le_csSup hbdd ⟨G, hg, hχ⟩
  have hexp : (n : ℝ) ^ ((1 / 2 : ℝ) / (m : ℝ) - ε) ≤ (n : ℝ) ^ (1 / (2 * (m : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have : (1 / 2 : ℝ) / (m : ℝ) = 1 / (2 * (m : ℝ)) := by field_simp
    linarith
  calc (n : ℝ) ^ ((1 / 2 : ℝ) / (m : ℝ) - ε) ≤ (n : ℝ) ^ (1 / (2 * (m : ℝ))) := hexp
    _ ≤ c := hpc
    _ ≤ (Erdos626.h m n : ℝ) := by exact_mod_cast hch

end OMA626

theorem OMA.solution : type_of% @Erdos626.erdos_626.variants.h_lower := by
  exact OMA626.main
