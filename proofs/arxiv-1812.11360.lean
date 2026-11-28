import OMAStatements.S_arxiv_1812_11360

/-!
# Proof of arxiv-1812.11360: Signatures of the odd prisms P(2n+1, 1) up to switching

Every signature on the odd prism `C_{2n+1} □ K_2` (`n ≥ 1`) is switching-equivalent to a
signature with at most `n + 1` negative edges.

## Proof outline
Working in `ZMod 2`, any signature `S` determines outer-cycle edge signs `sigA`, inner-cycle
edge signs `sigB`, and spoke signs `sigR`, along with the `2n + 1` square face parities
`q i = sigA i + sigB i + sigR i + sigR (i + 1)` and the two cycle parities
`cOut = ∑ sigA`, `cIn = ∑ sigB`, which satisfy `∑ q = cOut + cIn`.

For any zero-sum vector `d : Fin (2n + 1) → ZMod 2`, the prefix sum `r0` and its complement
`r0 + 1` both satisfy `r i + r (i + 1) = d i` and have weights summing to `2n + 1`, so one
of them has weight at most `n`. Using this, we construct target signs `tauA, tauB, tauR`
matching `q`, `cOut`, and `cIn` with total weight at most `n + 1`:
* `(cOut, cIn) = (0, 0)`: `tauA = tauB = 0`, `wt tauR ≤ n`.
* `(cOut, cIn) = (1, 0)` or `(0, 1)`: one cycle edge set to `1`, `wt tauR ≤ n`.
* `(cOut, cIn) = (1, 1)`: take `r` with `r i + r (i + 1) = q i` and `wt r ≤ n`. If
  `wt r ≤ n - 1`, set `tauA 0 = tauB 0 = 1`; otherwise `wt r = n ≥ 1`, pick `k` with `r k = 1`,
  flip `r k` to `0`, and set `tauA (k - 1) = 1` and `tauB k = 1`, giving total weight `n + 1`.

Finally, since `∑ (sigA + tauA) = 0`, prefix sums define a vertex switching set `X` realizing
`tauA, tauB, tauR`, so `switch (prism (2n + 1)) S X` has cardinality at most `n + 1`.
-/

namespace OMA.P_arxiv_1812_11360

open OMA.S_arxiv_1812_11360 SimpleGraph

/-- Indicator in `ZMod 2` of a proposition (classical). -/
private noncomputable def ind (P : Prop) : ZMod 2 :=
  @ite _ P (Classical.propDecidable P) 1 0

private lemma ind_eq_one_iff (P : Prop) : ind P = 1 ↔ P := by
  unfold ind
  split_ifs with h
  · simp [h]
  · simp [h]

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma zmod2_add_eq_one_iff (a b c : ZMod 2) :
    a + b + c = 1 ↔ (a = 1 ↔ (b = 1 ↔ c = 1)) := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;> decide

private lemma ind_zmod2_eq_one (a : ZMod 2) : ind (a = 1) = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · unfold ind; rw [if_neg (by decide)]
  · unfold ind; rw [if_pos rfl]

/-- Hamming weight of a `ZMod 2`-valued vector on `Fin N`. -/
private def wt {N : ℕ} (f : Fin N → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i : Fin N => f i = 1).card

/-- Prefix sum `∑_{j < i} d j` in `ZMod 2`. -/
private def prefixSum {N : ℕ} (d : Fin N → ZMod 2) (i : Fin N) : ZMod 2 :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j

/-- If `∑ j, d j = 0`, then `prefixSum d i + prefixSum d (i + 1) = d i` for all `i : Fin N`. -/
private lemma prefixSum_add_succ {N : ℕ} (hN : 1 < N) [NeZero N] (d : Fin N → ZMod 2)
    (hsum : ∑ j : Fin N, d j = 0) (i : Fin N) :
    prefixSum d i + prefixSum d (i + 1) = d i := by
  unfold prefixSum
  have hone : (1 : Fin N).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt hN
  by_cases hi : i.val + 1 < N
  · have hval : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, hone]
      exact Nat.mod_eq_of_lt hi
    have hset :
        (Finset.univ.filter fun j : Fin N => j.val < (i + 1).val) =
          insert i (Finset.univ.filter fun j : Fin N => j.val < i.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hval]
      constructor
      · intro hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact Or.inr h
        · exact Or.inl (Fin.ext h)
      · rintro (rfl | h)
        · omega
        · omega
    have hnotmem : i ∉ Finset.univ.filter (fun j : Fin N => j.val < i.val) := by
      simp
    rw [hset, Finset.sum_insert hnotmem]
    have hself := zmod2_add_self (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j)
    calc
      (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j) +
          (d i + ∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j)
        = d i + ((∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j) +
            ∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j) := by ring
      _ = d i := by rw [hself, add_zero]
  · have hlast : i.val + 1 = N := by omega
    have hzero : i + 1 = 0 := by
      apply Fin.ext
      rw [Fin.val_add, hone, hlast, Nat.mod_self, Fin.val_zero]
    have hempty : (Finset.univ.filter fun j : Fin N => j.val < (i + 1).val) = ∅ := by
      rw [hzero]
      ext j
      simp
    have huniv :
        (Finset.univ : Finset (Fin N)) =
          insert i (Finset.univ.filter fun j : Fin N => j.val < i.val) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff]
      have hj : j.val < N := j.isLt
      by_cases hjeq : j.val = i.val
      · exact Or.inl (Fin.ext hjeq)
      · exact Or.inr (by omega)
    have hnotmem : i ∉ Finset.univ.filter (fun j : Fin N => j.val < i.val) := by
      simp
    rw [hempty, Finset.sum_empty, add_zero]
    have hsum' : d i + ∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j = 0 := by
      rw [← Finset.sum_insert hnotmem, ← huniv]
      exact hsum
    have hself := zmod2_add_self (d i)
    calc
      (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j)
        = (d i + d i) + ∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j := by
          rw [hself, zero_add]
      _ = d i + (d i + ∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < i.val), d j) := by ring
      _ = d i := by rw [hsum', add_zero]

/-- For odd `N = 2 * n + 1` with `n ≥ 1`, any zero-sum `d : Fin N → ZMod 2` has a discrete
antiderivative `r` with `r i + r (i + 1) = d i` and weight `wt r ≤ n`. -/
private lemma exists_antideriv_le (n : ℕ) (hn : 1 ≤ n) (d : Fin (2 * n + 1) → ZMod 2)
    (hsum : ∑ j : Fin (2 * n + 1), d j = 0) :
    ∃ r : Fin (2 * n + 1) → ZMod 2,
      (∀ i, r i + r (i + 1) = d i) ∧ wt r ≤ n := by
  let r0 : Fin (2 * n + 1) → ZMod 2 := prefixSum d
  let r1 : Fin (2 * n + 1) → ZMod 2 := fun i => r0 i + 1
  have hr0 : ∀ i, r0 i + r0 (i + 1) = d i := prefixSum_add_succ (by omega) d hsum
  have hr1 : ∀ i, r1 i + r1 (i + 1) = d i := fun i => by
    dsimp only [r1]
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    calc
      r0 i + 1 + (r0 (i + 1) + 1) = (r0 i + r0 (i + 1)) + (1 + 1) := by ring
      _ = d i := by rw [hr0 i, h11, add_zero]
  have hdisj : Disjoint (Finset.univ.filter fun i => r0 i = 1)
      (Finset.univ.filter fun i => r1 i = 1) := by
    rw [Finset.disjoint_filter]
    intro i _ h0 h1
    dsimp only [r1] at h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hunion : (Finset.univ.filter fun i => r0 i = 1) ∪
      (Finset.univ.filter fun i => r1 i = 1) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    dsimp only [r1]
    rcases zmod2_eq_zero_or_one (r0 i) with h | h <;> rw [h] <;> decide
  have hcard : wt r0 + wt r1 = 2 * n + 1 := by
    unfold wt
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  by_cases h : wt r0 ≤ n
  · exact ⟨r0, hr0, h⟩
  · exact ⟨r1, hr1, by omega⟩

/-- Weight of the indicator vector `fun i => if i = k then 1 else 0` is `1`. -/
private lemma wt_single {N : ℕ} (k : Fin N) :
    wt (fun i : Fin N => if i = k then (1 : ZMod 2) else 0) = 1 := by
  unfold wt
  have : (Finset.univ.filter fun i : Fin N => (if i = k then (1 : ZMod 2) else 0) = 1) = {k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    split_ifs with h
    · simp [h]
    · simp [h]
  rw [this, Finset.card_singleton]

private lemma wt_zero {N : ℕ} : wt (fun _ : Fin N => (0 : ZMod 2)) = 0 := by
  unfold wt
  simp

private lemma sum_single {N : ℕ} (k : Fin N) :
    ∑ i : Fin N, (if i = k then (1 : ZMod 2) else 0) = 1 := by
  simp

/-- Core combinatorial step: given face parities `q`, `cOut`, `cIn` with `∑ q = cOut + cIn`,
there exist target edge parities `tauA, tauB, tauR` achieving the same face parities
with total weight `≤ n + 1`. -/
private lemma exists_low_weight_target (n : ℕ) (hn : 1 ≤ n)
    (q : Fin (2 * n + 1) → ZMod 2) (cOut cIn : ZMod 2)
    (hbal : ∑ i : Fin (2 * n + 1), q i = cOut + cIn) :
    ∃ tauA tauB tauR : Fin (2 * n + 1) → ZMod 2,
      (∑ i, tauA i = cOut) ∧
      (∀ i, tauA i + tauB i + tauR i + tauR (i + 1) = q i) ∧
      wt tauA + wt tauB + wt tauR ≤ n + 1 := by
  rcases zmod2_eq_zero_or_one cOut with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one cIn with rfl | rfl
  · have hq : ∑ i, q i = 0 := by simpa using hbal
    obtain ⟨r, hr, hwt⟩ := exists_antideriv_le n hn q hq
    refine ⟨fun _ => 0, fun _ => 0, r, by simp, ?_, ?_⟩
    · intro i; simpa using hr i
    · rw [wt_zero]; omega
  · let tauB : Fin (2 * n + 1) → ZMod 2 := fun i => if i = 0 then 1 else 0
    let d : Fin (2 * n + 1) → ZMod 2 := fun i => q i + tauB i
    have hd : ∑ i, d i = 0 := by
      dsimp only [d, tauB]
      rw [Finset.sum_add_distrib, hbal, sum_single]
      decide
    obtain ⟨r, hr, hwt⟩ := exists_antideriv_le n hn d hd
    refine ⟨fun _ => 0, tauB, r, by simp, ?_, ?_⟩
    · intro i
      have hri := hr i
      dsimp only [d] at hri
      have hb := zmod2_add_self (tauB i)
      calc
        (0 : ZMod 2) + tauB i + r i + r (i + 1)
          = tauB i + (r i + r (i + 1)) := by ring
        _ = tauB i + (q i + tauB i) := by rw [hri]
        _ = q i + (tauB i + tauB i) := by ring
        _ = q i := by rw [hb, add_zero]
    · rw [wt_zero, wt_single]; omega
  · let tauA : Fin (2 * n + 1) → ZMod 2 := fun i => if i = 0 then 1 else 0
    let d : Fin (2 * n + 1) → ZMod 2 := fun i => q i + tauA i
    have hd : ∑ i, d i = 0 := by
      dsimp only [d, tauA]
      rw [Finset.sum_add_distrib, hbal, sum_single]
      decide
    obtain ⟨r, hr, hwt⟩ := exists_antideriv_le n hn d hd
    refine ⟨tauA, fun _ => 0, r, sum_single 0, ?_, ?_⟩
    · intro i
      have hri := hr i
      dsimp only [d] at hri
      have ha := zmod2_add_self (tauA i)
      calc
        tauA i + (0 : ZMod 2) + r i + r (i + 1)
          = tauA i + (r i + r (i + 1)) := by ring
        _ = tauA i + (q i + tauA i) := by rw [hri]
        _ = q i + (tauA i + tauA i) := by ring
        _ = q i := by rw [ha, add_zero]
    · rw [wt_zero, wt_single]; omega
  · have hq : ∑ i, q i = 0 := by
      rw [hbal]; decide
    obtain ⟨r, hr, hwt⟩ := exists_antideriv_le n hn q hq
    by_cases hlt : wt r ≤ n - 1
    · let tauA : Fin (2 * n + 1) → ZMod 2 := fun i => if i = 0 then 1 else 0
      refine ⟨tauA, tauA, r, sum_single 0, ?_, ?_⟩
      · intro i
        have ha := zmod2_add_self (tauA i)
        calc
          tauA i + tauA i + r i + r (i + 1)
            = (tauA i + tauA i) + (r i + r (i + 1)) := by ring
          _ = q i := by rw [ha, zero_add, hr i]
      · rw [wt_single]; omega
    · have hpos : 0 < wt r := by omega
      obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
      have hrk : r k = 1 := (Finset.mem_filter.mp hk).2
      let tauA : Fin (2 * n + 1) → ZMod 2 := fun i => if i = k - 1 then 1 else 0
      let tauB : Fin (2 * n + 1) → ZMod 2 := fun i => if i = k then 1 else 0
      let r' : Fin (2 * n + 1) → ZMod 2 := fun i => r i + if i = k then 1 else 0
      have hwtr' : wt r' = wt r - 1 := by
        unfold wt
        have hset :
            (Finset.univ.filter fun i : Fin (2 * n + 1) => r' i = 1) =
              (Finset.univ.filter fun i : Fin (2 * n + 1) => r i = 1).erase k := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, r']
          by_cases hik : i = k
          · subst hik
            simp [hrk]
          · simp [hik]
        rw [hset, Finset.card_erase_of_mem hk]
      refine ⟨tauA, tauB, r', sum_single (k - 1), ?_, ?_⟩
      · intro i
        have heq : (i + 1 = k) ↔ (i = k - 1) := by
          constructor
          · intro h; rw [← h, add_sub_cancel_right]
          · intro h; rw [h, sub_add_cancel]
        dsimp only [tauA, tauB, r']
        have hdelta :
            (if i = k - 1 then (1 : ZMod 2) else 0) + (if i + 1 = k then (1 : ZMod 2) else 0) = 0 := by
          by_cases h : i = k - 1
          · rw [if_pos h, if_pos (heq.mpr h)]; decide
          · rw [if_neg h, if_neg (mt heq.mp h)]; decide
        have hdelta2 :
            (if i = k then (1 : ZMod 2) else 0) + (if i = k then (1 : ZMod 2) else 0) = 0 :=
          zmod2_add_self _
        calc
          (if i = k - 1 then (1 : ZMod 2) else 0) + (if i = k then 1 else 0) +
              (r i + if i = k then 1 else 0) + (r (i + 1) + if i + 1 = k then 1 else 0)
            = (r i + r (i + 1)) +
              ((if i = k - 1 then (1 : ZMod 2) else 0) + (if i + 1 = k then 1 else 0)) +
              ((if i = k then (1 : ZMod 2) else 0) + (if i = k then 1 else 0)) := by ring
          _ = q i := by rw [hr i, hdelta, hdelta2, add_zero, add_zero]
      · rw [wt_single, wt_single, hwtr']; omega

private def edgeA {N : ℕ} [NeZero N] (i : Fin N) : Sym2 (Fin N × Fin 2) := s((i, 0), (i + 1, 0))
private def edgeB {N : ℕ} [NeZero N] (i : Fin N) : Sym2 (Fin N × Fin 2) := s((i, 1), (i + 1, 1))
private def edgeR {N : ℕ} (i : Fin N) : Sym2 (Fin N × Fin 2) := s((i, 0), (i, 1))

/-- Every edge of `prism (2 * n + 1)` is an outer cycle edge, inner cycle edge, or spoke. -/
private lemma mem_prism_edgeSet (n : ℕ) (hn : 1 ≤ n) (e : Sym2 (Fin (2 * n + 1) × Fin 2))
    (he : e ∈ (prism (2 * n + 1)).edgeSet) :
    (∃ i, e = edgeA i) ∨ (∃ i, e = edgeB i) ∨ (∃ i, e = edgeR i) := by
  induction e using Sym2.ind with
  | _ u v =>
    rcases u with ⟨i, bi⟩
    rcases v with ⟨j, bj⟩
    rw [mem_edgeSet] at he
    change (cycleGraph (2 * n + 1) □ (⊤ : SimpleGraph (Fin 2))).Adj (i, bi) (j, bj) at he
    rw [boxProd_adj] at he
    rcases he with ⟨hadj, hbeq⟩ | ⟨hbadj, hieq⟩
    · change bi = bj at hbeq
      subst hbeq
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hadj' : (cycleGraph ((2 * m + 1) + 2)).Adj i j := hadj
      rw [cycleGraph_adj] at hadj'
      have hij : j = i + 1 ∨ i = j + 1 := by
        rcases hadj' with h | h
        · right; rw [← h, add_sub_cancel]
        · left; rw [← h, add_sub_cancel]
      fin_cases bi
      · left
        rcases hij with rfl | rfl
        · exact ⟨i, rfl⟩
        · exact ⟨j, Sym2.eq_swap⟩
      · right; left
        rcases hij with rfl | rfl
        · exact ⟨i, rfl⟩
        · exact ⟨j, Sym2.eq_swap⟩
    · change i = j at hieq
      subst hieq
      have hne : bi ≠ bj := hbadj
      right; right
      fin_cases bi <;> fin_cases bj
      · exact absurd rfl hne
      · exact ⟨i, rfl⟩
      · exact ⟨i, Sym2.eq_swap⟩
      · exact absurd rfl hne

/-- If `s(u, v) ∈ switch G S X`, then `ind (s(u, v) ∈ S) + ind (u ∈ X) + ind (v ∈ X) = 1`. -/
private lemma switch_ind_eq_one {V : Type*} (G : SimpleGraph V) (S : Set (Sym2 V)) (X : Set V)
    {u v : V} (h : s(u, v) ∈ switch G S X) :
    ind (s(u, v) ∈ S) + ind (u ∈ X) + ind (v ∈ X) = 1 := by
  rcases h with ⟨_, u', v', heq, hiff⟩
  rw [zmod2_add_eq_one_iff, ind_eq_one_iff, ind_eq_one_iff, ind_eq_one_iff]
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hiff
  · simpa [Sym2.eq_swap] using hiff.trans iff_comm

private theorem main_proof : ∀ n ≥ 1, ∀ S ⊆ (prism (2 * n + 1)).edgeSet,
    ∃ X : Set (Fin (2 * n + 1) × Fin 2), (switch (prism (2 * n + 1)) S X).ncard ≤ n + 1 := by
  intro n hn S _hS
  let N := 2 * n + 1
  let sigA : Fin N → ZMod 2 := fun i => ind (edgeA i ∈ S)
  let sigB : Fin N → ZMod 2 := fun i => ind (edgeB i ∈ S)
  let sigR : Fin N → ZMod 2 := fun i => ind (edgeR i ∈ S)
  let q : Fin N → ZMod 2 := fun i => sigA i + sigB i + sigR i + sigR (i + 1)
  let cOut : ZMod 2 := ∑ i : Fin N, sigA i
  let cIn : ZMod 2 := ∑ i : Fin N, sigB i
  have hRsum : ∑ i : Fin N, (sigR i + sigR (i + 1)) = 0 := by
    rw [Finset.sum_add_distrib]
    have hshift : ∑ i : Fin N, sigR (i + 1) = ∑ i : Fin N, sigR i :=
      Fintype.sum_equiv (Equiv.addRight (1 : Fin N)) _ _ (fun _ => rfl)
    rw [hshift, zmod2_add_self]
  have hbal : ∑ i : Fin N, q i = cOut + cIn := by
    dsimp only [q, cOut, cIn]
    have hsplit :
        (∑ i : Fin N, (sigA i + sigB i + sigR i + sigR (i + 1))) =
          (∑ i : Fin N, sigA i) + (∑ i : Fin N, sigB i) +
            ∑ i : Fin N, (sigR i + sigR (i + 1)) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit, hRsum, add_zero]
  obtain ⟨tauA, tauB, tauR, htauA_sum, htau_face, htau_wt⟩ :=
    exists_low_weight_target n hn q cOut cIn hbal
  let dA : Fin N → ZMod 2 := fun i => sigA i + tauA i
  let dR : Fin N → ZMod 2 := fun i => sigR i + tauR i
  have hdA_sum : ∑ i : Fin N, dA i = 0 := by
    dsimp only [dA]
    rw [Finset.sum_add_distrib, htauA_sum]
    exact zmod2_add_self cOut
  let x0 : Fin N → ZMod 2 := prefixSum dA
  let x1 : Fin N → ZMod 2 := fun i => x0 i + dR i
  have hx0_step : ∀ i : Fin N, x0 i + x0 (i + 1) = dA i :=
    prefixSum_add_succ (by omega) dA hdA_sum
  have hxA : ∀ i : Fin N, sigA i + x0 i + x0 (i + 1) = tauA i := fun i => by
    have hs := zmod2_add_self (sigA i)
    calc
      sigA i + x0 i + x0 (i + 1) = sigA i + (x0 i + x0 (i + 1)) := by ring
      _ = sigA i + (sigA i + tauA i) := by rw [hx0_step i]
      _ = (sigA i + sigA i) + tauA i := by ring
      _ = tauA i := by rw [hs, zero_add]
  have hxR : ∀ i : Fin N, sigR i + x0 i + x1 i = tauR i := fun i => by
    dsimp only [x1, dR]
    have hx := zmod2_add_self (x0 i)
    have hr := zmod2_add_self (sigR i)
    calc
      sigR i + x0 i + (x0 i + (sigR i + tauR i))
        = (sigR i + sigR i) + (x0 i + x0 i) + tauR i := by ring
      _ = tauR i := by rw [hr, hx, zero_add, zero_add]
  have hxB : ∀ i : Fin N, sigB i + x1 i + x1 (i + 1) = tauB i := fun i => by
    have hface : sigA i + sigB i + sigR i + sigR (i + 1) =
        tauA i + tauB i + tauR i + tauR (i + 1) := (htau_face i).symm
    have hxa := hxA i
    have hxr0 := hxR i
    have hxr1 := hxR (i + 1)
    have h2 : (2 : ZMod 2) = 0 := rfl
    linear_combination hface - hxa + hxr0 + hxr1 +
      (tauR i + tauR (i + 1) - sigR i - sigR (i + 1)) * h2
  let X : Set (Fin N × Fin 2) := {v | (if v.2 = 0 then x0 v.1 else x1 v.1) = 1}
  have hindX0 : ∀ i : Fin N, ind ((i, (0 : Fin 2)) ∈ X) = x0 i := fun i => by
    change ind (x0 i = 1) = x0 i
    exact ind_zmod2_eq_one (x0 i)
  have hindX1 : ∀ i : Fin N, ind ((i, (1 : Fin 2)) ∈ X) = x1 i := fun i => by
    change ind (x1 i = 1) = x1 i
    exact ind_zmod2_eq_one (x1 i)
  let FA : Finset (Sym2 (Fin N × Fin 2)) :=
    (Finset.univ.filter fun i : Fin N => tauA i = 1).image edgeA
  let FB : Finset (Sym2 (Fin N × Fin 2)) :=
    (Finset.univ.filter fun i : Fin N => tauB i = 1).image edgeB
  let FR : Finset (Sym2 (Fin N × Fin 2)) :=
    (Finset.univ.filter fun i : Fin N => tauR i = 1).image edgeR
  have hsub : switch (prism N) S X ⊆ ↑(FA ∪ FB ∪ FR) := by
    intro e he
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    rcases mem_prism_edgeSet n hn e he.1 with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · left; left
      refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have h1 := switch_ind_eq_one (prism N) S X
        (show s((i, 0), (i + 1, 0)) ∈ switch (prism N) S X from he)
      rw [hindX0 i, hindX0 (i + 1)] at h1
      rw [← hxA i]; exact h1
    · left; right
      refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have h1 := switch_ind_eq_one (prism N) S X
        (show s((i, 1), (i + 1, 1)) ∈ switch (prism N) S X from he)
      rw [hindX1 i, hindX1 (i + 1)] at h1
      rw [← hxB i]; exact h1
    · right
      refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have h1 := switch_ind_eq_one (prism N) S X
        (show s((i, 0), (i, 1)) ∈ switch (prism N) S X from he)
      rw [hindX0 i, hindX1 i] at h1
      rw [← hxR i]; exact h1
  refine ⟨X, ?_⟩
  calc
    (switch (prism N) S X).ncard ≤ (↑(FA ∪ FB ∪ FR) : Set _).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (FA ∪ FB ∪ FR).card := Set.ncard_coe_finset _
    _ ≤ (FA ∪ FB).card + FR.card := Finset.card_union_le _ _
    _ ≤ FA.card + FB.card + FR.card := by
      have := Finset.card_union_le FA FB; omega
    _ ≤ wt tauA + wt tauB + wt tauR := by
      have hA : FA.card ≤ wt tauA := Finset.card_image_le
      have hB : FB.card ≤ wt tauB := Finset.card_image_le
      have hR : FR.card ≤ wt tauR := Finset.card_image_le
      omega
    _ ≤ n + 1 := htau_wt

end OMA.P_arxiv_1812_11360

theorem OMA.solution : type_of% @OMA.S_arxiv_1812_11360.main :=
  OMA.P_arxiv_1812_11360.main_proof
