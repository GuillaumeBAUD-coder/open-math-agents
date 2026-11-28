import OMAStatements.S_oeis_a250392
import Mathlib

/-!
# Nine-letter arrays avoiding tied middle entries in four-letter windows

This proves both conjectures in https://oeis.org/A250392. The threshold-set
construction is adapted from the eight-position proof of A250391 (#26543)
and the ten-position proof of A250393 (#27307), after @Salofe's A250064
proof (#23285). The kernel verifies each of the six windows for the native
predicate on nine positions.

For any transfer that includes its diagonal and whose other edges strictly
decrease a finite rank, the counts are binomial polynomials of degree bounded
by the rank. Applying this to the nine-position threshold sets shows that ten
sample counts suffice. The finite transfer certificate, binomial interpolation,
and formal power-series identity give the conjectured numerator and recurrence.
-/

/-!
A250392, the nine-position row of Hardin's four-entry window problem.
The threshold-chain proof and four-entry window equivalence are adapted from
@rodolfoquint's A250391 proof, PR #26543, commit 49dfd8336, which credits
@Salofe's A250064 proof, PR #23285, commit bd4969a8ddc52c3bd7f8d30008570b9868fd00b6.
Conjectures by Colin Barker (2017). Statement by @clementtrecourt, PR #18788.
-/

namespace Median392

open OMA.S_oeis_a250392 Finset

/-! ### The window condition -/

/-- The condition of the statement on 4 values (without the bound on `v`). -/
def Cy (y : Fin 4 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 4)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 4 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
  obtain ⟨S, hS, v, h1, ⟨s, hs, hsv⟩, h3, ⟨t0, ht0, ht0v⟩⟩ := h
  have hc : S.card = 2 := (Finset.mem_powersetCard.1 hS).2
  by_cases hw : w < v
  · have hsub : univ.filter (fun t => y t ≤ w) ⊆ S.erase s := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have htS : t ∈ S := by
        by_contra hn
        have := h3 t hn
        omega
      refine Finset.mem_erase.2 ⟨?_, htS⟩
      rintro rfl
      omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hs, hc] at h1'
    omega
  · have hsub : insert t0 S ⊆ univ.filter (fun t => y t ≤ w) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · have := h1 t ht'
        omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ht0, hc] at h1'
    omega

theorem cy_of (y : Fin 4 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 4)) y Finset.univ_nonempty
    refine ⟨m, ?_⟩
    rw [hU, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : univ.filter (fun t => y t ≤ y m) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      exact hm t (Finset.mem_univ t)
    rw [this]
    simp
  obtain ⟨s, hsU, hmin⟩ := Finset.exists_min_image U y hUne
  have hs2 : 2 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    rw [hU, Finset.mem_filter] at hsU
    exact hsU.2
  have hs3 : 3 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    have := h (y s)
    omega
  set L := univ.filter (fun t => y t < y s) with hL
  set E := univ.filter (fun t => y t = y s) with hE
  have hLc : L.card ≤ 1 := by
    by_cases hLne : L.Nonempty
    · obtain ⟨l, hl, hlmax⟩ := Finset.exists_max_image L y hLne
      have hyl : y l < y s := by
        rw [hL, Finset.mem_filter] at hl
        exact hl.2
      have hlU : l ∉ U := by
        intro hlU
        have := hmin l hlU
        omega
      have hcl : (univ.filter (fun t => y t ≤ y l)).card ≤ 1 := by
        rw [hU, Finset.mem_filter] at hlU
        have : ¬ 2 ≤ (univ.filter (fun t => y t ≤ y l)).card :=
          fun h2 => hlU ⟨Finset.mem_univ _, h2⟩
        omega
      have hsub : L ⊆ univ.filter (fun t => y t ≤ y l) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlmax t ht
      exact le_trans (Finset.card_le_card hsub) hcl
    · rw [Finset.not_nonempty_iff_eq_empty.mp hLne]
      simp
  have hsplit : (univ.filter (fun t => y t ≤ y s)) ⊆ L ∪ E := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [Finset.mem_union, hL, hE, Finset.mem_filter, Finset.mem_filter]
    rcases Nat.lt_or_ge (y t) (y s) with h' | h'
    · exact Or.inl ⟨Finset.mem_univ _, h'⟩
    · exact Or.inr ⟨Finset.mem_univ _, by omega⟩
  have hcard := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le L E)
  have hsE : s ∈ E := by
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hnotL : ∀ t, ¬ y t < y s → t ∉ L := by
    intro t ht htL
    rw [hL, Finset.mem_filter] at htL
    exact ht htL.2
  rcases Nat.lt_or_ge 0 L.card with hpos | hzero
  · -- one value below `y s`
    obtain ⟨l, hLl⟩ := Finset.card_eq_one.1 (by omega : L.card = 1)
    have hlL : l ∈ L := by rw [hLl]; exact Finset.mem_singleton_self l
    have hyl : y l < y s := by
      rw [hL, Finset.mem_filter] at hlL
      exact hlL.2
    have hE1 : 1 ≤ (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < (E.erase s).card)
    have hes : e ≠ s := (Finset.mem_erase.1 he).1
    have hye : y e = y s := by
      have := (Finset.mem_erase.1 he).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hls : l ≠ s := by
      rintro rfl
      omega
    refine ⟨{l, s}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e, ?_, hye⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair hls⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · rw [Finset.mem_singleton.1 ht']
    · intro t ht
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLl, Finset.mem_singleton] at htL
      apply ht
      rw [htL]
      exact Finset.mem_insert_self l {s}
    · intro he'
      rcases Finset.mem_insert.1 he' with rfl | he''
      · omega
      · exact hes (Finset.mem_singleton.1 he'')
  · -- no value below `y s`
    have hL0 : L.card = 0 := by omega
    have hE3 : 3 ≤ E.card := by omega
    have hE2 : 1 < (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.1 hE2
    have he1s : e1 ≠ s := (Finset.mem_erase.1 he1).1
    have he2s : e2 ≠ s := (Finset.mem_erase.1 he2).1
    have hye1 : y e1 = y s := by
      have := (Finset.mem_erase.1 he1).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hye2 : y e2 = y s := by
      have := (Finset.mem_erase.1 he2).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hLempty : L = ∅ := Finset.card_eq_zero.1 hL0
    refine ⟨{s, e1}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e2, ?_, hye2⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair he1s.symm⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · exact le_rfl
      · rw [Finset.mem_singleton.1 ht', hye1]
    · intro t _
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLempty] at htL
      exact Finset.notMem_empty t htL
    · intro he'
      rcases Finset.mem_insert.1 he' with h' | h'
      · exact he2s h'
      · exact he12 (Finset.mem_singleton.1 h').symm

theorem window_iff (y : Fin 4 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 4 → ℕ) :
    ¬ Cy y ↔ ∀ v : ℕ, ¬ ((univ.filter (fun t => y t < v)).card ≤ 1 ∧
      3 ≤ (univ.filter (fun t => y t < v + 1)).card) := by
  rw [window_iff, not_forall]
  simp only [ne_eq, not_not]
  constructor
  · rintro ⟨w, hw⟩ v ⟨h1, h3⟩
    rcases Nat.lt_or_ge w v with h | h
    · have hsub : univ.filter (fun t => y t ≤ w) ⊆ univ.filter (fun t => y t < v) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        omega
      have := Finset.card_le_card hsub
      omega
    · have hsub : univ.filter (fun t => y t < v + 1) ⊆ univ.filter (fun t => y t ≤ w) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        omega
      have := Finset.card_le_card hsub
      omega
  · intro h
    by_contra hne
    simp only [not_exists] at hne
    have key : ∀ v, (univ.filter (fun t => y t < v)).card ≤ 1 := by
      intro v
      induction v with
      | zero => simp
      | succ v ih =>
        have h1 := h v
        have h2 := hne v
        have e : univ.filter (fun t => y t < v + 1) = univ.filter (fun t => y t ≤ v) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [e] at h1 ⊢
        by_contra hc
        exact h1 ⟨ih, by omega⟩
    have hall : univ.filter (fun t => y t < univ.sup y + 1) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      have := Finset.le_sup (f := y) (Finset.mem_univ t)
      omega
    have := key (univ.sup y + 1)
    rw [hall] at this
    simp at this

/-! ### Strict threshold sets -/

/-- Entry `k` of a set of positions (`false` past the end). -/
def fget (f : Fin 9 → Bool) (k : ℕ) : Bool := if h : k < 9 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 9 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 4 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 9 → Bool) : Prop := ∀ i < (6 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 9 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 9 → Fin (n + 1)) (v : ℕ) : Fin 9 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a250392.get x k ≤ n := by
  unfold OMA.S_oeis_a250392.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (6 : ℕ), cntW (fun _ => true) i = 4 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 9 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (6 : ℕ), ¬ Cy (fun t : Fin 4 => OMA.S_oeis_a250392.get x (i + t)) := by
    unfold good
    rw [decide_eq_true_iff]
    refine forall_congr' fun i => imp_congr_right fun _ => not_congr ?_
    constructor
    · rintro ⟨S, hS, v, _, h1, h2, h3, h4⟩
      exact ⟨S, hS, v, h1, h2, h3, h4⟩
    · rintro ⟨S, hS, v, h1, ⟨t, ht, htv⟩, h3, h4⟩
      refine ⟨S, hS, v, ?_, h1, ⟨t, ht, htv⟩, h3, h4⟩
      rw [← htv]
      exact Nat.lt_succ_of_le (get_le x _)
  have step2 : ∀ i < (6 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 4 => OMA.S_oeis_a250392.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 9 := by have := t.isLt; omega
    unfold OMA.S_oeis_a250392.get fget Lt
    rw [dif_pos ht, dif_pos ht, decide_eq_true_iff]
  have hfull : ∀ w, n < w → Lt x w = fun _ => true := by
    intro w hw
    funext p
    unfold Lt
    have := (x p).isLt
    simp only [decide_eq_true_iff]
    omega
  rw [step1]
  constructor
  · intro h v _ i hi
    have := (not_cy_iff _).1 (h i hi) v
    simp only [step2 i hi v, step2 i hi (v + 1)] at this
    exact this
  · intro h i hi
    rw [not_cy_iff]
    intro v
    simp only [step2 i hi v, step2 i hi (v + 1)]
    by_cases hv : v ≤ n
    · exact h v hv i hi
    · rw [hfull v (by omega), cnt_univ i hi]
      omega

/-! ### Chains of strict threshold sets -/

/-- Arrays with entries in `0..n` whose consecutive strict threshold sets are compatible, with
`Lt x n ⊆ T` and `Lt x n` compatible with `T`. -/
noncomputable def M (n : ℕ) (T : Fin 9 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 9 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 9 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
  classical
  unfold M
  split_ifs with h
  · rw [Finset.filter_true_of_mem]
    · simp
    · intro x _
      refine ⟨fun p hp => ?_, fun v hv => absurd hv (Nat.not_lt_zero _), ?_⟩
      · rw [Lt_zero] at hp
        exact absurd hp (by simp)
      · rw [Lt_zero]
        exact h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply h
    rw [← Lt_zero x]
    exact hx.2.2

/-- Restriction of an array with entries in `0..n+1` to entries in `0..n`. -/
def lower {n : ℕ} (x : Fin 9 → Fin (n + 2)) : Fin 9 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 9 → Bool) (x : Fin 9 → Fin (n + 1)) : Fin 9 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 9 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 9 → Bool) (x : Fin 9 → Fin (n + 1)) (p : Fin 9) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 9 → Bool) :
    M (n + 1) T = ∑ S : Fin 9 → Bool,
      if Comp S T ∧ (∀ p, S p = true → T p = true) then M n S else 0 := by
  classical
  unfold M
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => Lt x (n + 1)) (t := univ)
    (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hS
  · apply Finset.card_bij' (fun x _ => lower x) (fun x _ => raise S x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨⟨_, h2, _⟩, h3⟩ := hx
      refine ⟨fun p hp => ?_, fun v hv => ?_, ?_⟩
      · rw [Lt_lower x n le_rfl] at hp
        rw [← h3]
        have hp' : (x p : ℕ) < n := of_decide_eq_true hp
        exact decide_eq_true (by omega)
      · rw [Lt_lower x v (by omega), Lt_lower x (v + 1) (by omega)]
        exact h2 v (by omega)
      · rw [Lt_lower x n le_rfl, ← h3]
        exact h2 n (by omega)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2, h3⟩ := hx
      have hTS : Lt (raise S x) (n + 1) = S := by
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) < n + 1) = S p
        rw [raise_val]
        by_cases hp : S p = true
        · rw [if_pos hp, hp]
          have := (x p).isLt
          exact decide_eq_true (by omega)
        · rw [if_neg hp]
          simp only [Bool.not_eq_true] at hp
          rw [hp]
          exact decide_eq_false (by omega)
      have hlow : ∀ v ≤ n, Lt (raise S x) v = Lt x v := by
        intro v hv
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) < v) = decide ((x p : ℕ) < v)
        rw [raise_val]
        split_ifs with hp
        · rfl
        · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p (decide_eq_true h))
          rw [decide_eq_decide]
          omega
      refine ⟨⟨?_, fun v hv => ?_, ?_⟩, hTS⟩
      · rw [hTS]
        exact hS.2
      · rcases Nat.lt_or_ge v n with hv' | hv'
        · rw [hlow v (by omega), hlow (v + 1) (by omega)]
          exact h2 v hv'
        · obtain rfl : v = n := by omega
          rw [hlow v le_rfl, hTS]
          exact h3
      · rw [hTS]
        exact hS.1
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨_, h3⟩ := hx
      funext p
      apply Fin.ext
      rw [raise_val]
      have hiff : S p = true ↔ (x p : ℕ) < n + 1 := by
        rw [← h3]
        exact decide_eq_true_iff
      split_ifs with hp
      · show min (x p : ℕ) n = x p
        have := hiff.1 hp
        omega
      · have : ¬ (x p : ℕ) < n + 1 := fun h => hp (hiff.2 h)
        have := (x p).isLt
        omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨h1, _⟩ := hx
      funext p
      apply Fin.ext
      show min ((raise S x p : Fin (n + 2)) : ℕ) n = x p
      rw [raise_val]
      split_ifs with hp
      · have := (x p).isLt
        omega
      · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p (decide_eq_true h))
        have := (x p).isLt
        omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    rintro ⟨⟨h1, _, h3⟩, h4⟩
    apply hS
    rw [← h4]
    exact ⟨h3, h1⟩

/-! ### Codes -/

/-- The set of positions with code `u`: position `p` is in it iff bit `p` of `u` is set. -/
def row (u : Fin 512) : Fin 9 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 9 → Bool) : ℕ := ∑ p : Fin 9, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 512, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 9 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2 + m / 256 % 2

theorem cnt_row : ∀ u : Fin 512, cntW (row u) 0 = pcb (u.val &&& 15) ∧
    cntW (row u) 1 = pcb (u.val &&& 30) ∧
    cntW (row u) 2 = pcb (u.val &&& 60) ∧
    cntW (row u) 3 = pcb (u.val &&& 120) ∧
    cntW (row u) 4 = pcb (u.val &&& 240) ∧
    cntW (row u) 5 = pcb (u.val &&& 480) := by
  decide +kernel

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 15) ≤ 1 ∧ 3 ≤ pcb (t &&& 15)) ∧
    ¬ (pcb (s &&& 30) ≤ 1 ∧ 3 ≤ pcb (t &&& 30)) ∧
    ¬ (pcb (s &&& 60) ≤ 1 ∧ 3 ≤ pcb (t &&& 60)) ∧
    ¬ (pcb (s &&& 120) ≤ 1 ∧ 3 ≤ pcb (t &&& 120)) ∧
    ¬ (pcb (s &&& 240) ≤ 1 ∧ 3 ≤ pcb (t &&& 240)) ∧
    ¬ (pcb (s &&& 480) ≤ 1 ∧ 3 ≤ pcb (t &&& 480)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (6 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 512) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5]

theorem sub_iff (w u : Fin 512) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 9
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (512 : ℕ) ≤ 2 ^ i := by
          calc (512 : ℕ) = 2 ^ 9 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := w.isLt
        omega
      simp [hw]
  · intro h p hp
    unfold row at hp ⊢
    rw [← h, Nat.testBit_land] at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.2

/-- The codes of the subsets of the set with code `u`. -/
def subs (u : Fin 512) : Finset (Fin 512) :=
  univ.filter (fun w : Fin 512 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 512 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 512, M n (row u) = G n u := by
  induction n with
  | zero =>
    intro u
    rw [M_zero, ← row_zero, G]
    exact if_congr (compc_iff 0 u) rfl rfl
  | succ n ih =>
    intro u
    rw [M_succ, ← row_bijective.sum_comp]
    simp only [G, subs]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih w]
    by_cases h1 : (w.val &&& u.val == w.val) = true
    · rw [if_pos h1]
      exact if_congr ((and_iff_left ((sub_iff w u).2 h1)).trans (compc_iff w u)) rfl rfl
    · rw [if_neg h1, if_neg (fun h => h1 ((sub_iff w u).1 h.2))]

theorem row_full : ∀ p, row 511 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 511 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 9 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 511 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 511)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 511 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 511 := by
      rw [hr]
      funext p
      unfold Lt
      have := (x p).isLt
      simp only [decide_eq_true_iff]
      omega
    constructor
    · intro h
      refine ⟨fun p _ => row_full p, fun v hv => h v (by omega), ?_⟩
      rw [← hn]
      exact h n le_rfl
    · rintro ⟨_, h2, h3⟩ v hv
      rcases Nat.lt_or_ge v n with h | h
      · exact h2 v h
      · obtain rfl : v = n := by omega
        rw [hn]
        exact h3
  unfold a
  rw [h1, ← M_eq_G]
  unfold M
  congr 2

/-! ### The recurrence -/

theorem G_succ (n : ℕ) (u : Fin 512) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl

end Median392

namespace Median392
open Finset

/-- Repeated strict transitions produce the coefficients of the binomial
expansion. A chain arriving at a state cannot have more steps than its rank. -/
theorem binomial_transfer {ι : Type*} (pred : ι → Finset ι) (rank : ι → ℕ)
    (d : ℕ) (hr : ∀ x, ∀ y ∈ pred x, rank y < rank x)
    (M : ℕ → ι → ℕ)
    (step : ∀ n x, M (n+1) x = M n x + ∑ y ∈ pred x, M n y)
    (x : ι) (hx : rank x ≤ d) :
    ∃ c : Fin (d+1) → ℤ, ∀ n : ℕ, (M n x : ℤ) = ∑ j, c j * (n.choose j.val : ℤ) := by
  classical
  let C : ℕ → ι → ℕ := Nat.rec (M 0) (fun _ prev z => ∑ y ∈ pred z, prev y)
  have cstep (k : ℕ) (z : ι) : C (k+1) z = ∑ y ∈ pred z, C k y := rfl
  have vanish (k : ℕ) (z : ι) (hk : rank z < k) : C k z = 0 := by
    induction k generalizing z with
    | zero => omega
    | succ k ih =>
      rw [cstep]
      exact sum_eq_zero (fun y hy => ih y (by have := hr z y hy; omega))
  have expand (n : ℕ) (z : ι) :
      M n z = ∑ j ∈ range (n+1), C j z * n.choose j := by
    induction n generalizing z with
    | zero => simp [C]
    | succ n ih =>
      have shift : (∑ j ∈ range (n+1), C (j+1) z * n.choose (j+1)) + C 0 z =
          ∑ j ∈ range (n+1), C j z * n.choose j := by
        calc
          _ = ∑ j ∈ range (n+1+1), C j z * n.choose j := by
            rw [sum_range_succ' (fun j => C j z * n.choose j)]; simp
          _ = _ := by rw [sum_range_succ]; simp
      rw [step,ih,sum_range_succ' (fun j => C j z * (n+1).choose j)]
      simp only [Nat.choose_succ_succ,Nat.choose_zero_right,mul_one,mul_add,sum_add_distrib]
      have sub (k : ℕ) : (∑ y ∈ pred z, C k y * n.choose k) = C (k+1) z * n.choose k := by
        rw [cstep,sum_mul]
      calc
        _ = (∑ j ∈ range (n+1), C j z * n.choose j) +
            ∑ k ∈ range (n+1), C (k+1) z * n.choose k := by
              simp_rw [ih]
              rw [sum_comm (s := pred z),show (∑ k ∈ range (n+1), ∑ y ∈ pred z, C k y * n.choose k) =
                  ∑ k ∈ range (n+1), C (k+1) z * n.choose k from sum_congr rfl (fun k _ => sub k)]
        _ = _ := by rw [← shift]; ac_rfl
  refine ⟨fun j => Int.ofNat (C j.val x),?_⟩
  intro n
  rw [Fin.sum_univ_eq_sum_range (fun j => Int.ofNat (C j x) * (n.choose j : ℤ))]
  suffices h : M n x = ∑ j ∈ range (d+1), C j x * n.choose j by
    rw [h,Nat.cast_sum]
    simp only [Nat.cast_mul]
    rfl
  rw [expand]
  rcases le_total n d with hn | hd
  · apply sum_subset (range_mono (by omega))
    intro j hj hnj
    simp only [mem_range] at hnj
    simp [Nat.choose_eq_zero_of_lt (show n < j by omega)]
  · symm
    apply sum_subset (range_mono (by omega))
    intro j hj hdj
    simp only [mem_range] at hdj
    simp [vanish j x (by omega)]

end Median392

namespace Median392
open Finset
open scoped Classical

/-- Transfers between increasing threshold sets have degree at most the number of positions. -/
theorem threshold_polynomial {d : ℕ}
    (edge : (Fin d → Bool) → (Fin d → Bool) → Prop) [DecidableRel edge]
    (refl : ∀ T, edge T T)
    (incl : ∀ {S T}, edge S T → ∀ p, S p = true → T p = true)
    (A : ℕ → (Fin d → Bool) → ℕ)
    (advance : ∀ n T, A (n+1) T = ∑ S, if edge S T then A n S else 0)
    (T : Fin d → Bool) :
    ∃ c : Fin (d+1) → ℤ, ∀ n : ℕ, (A n T : ℤ) = ∑ j, c j * (n.choose j.val : ℤ) := by
  let members (U : Fin d → Bool) := univ.filter (fun p => U p = true)
  let allowed (U : Fin d → Bool) := univ.filter (fun V => edge V U)
  let pred (U : Fin d → Bool) := (allowed U).erase U
  have ident : Function.Injective members := by
    intro U V huv
    funext p
    have e : p ∈ members U ↔ p ∈ members V := by rw [huv]
    apply Bool.eq_iff_iff.mpr
    simpa only [members,mem_filter,mem_univ,true_and] using e
  refine binomial_transfer pred (fun U => (members U).card) d ?_ A ?_ T ?_
  · intro U V hv
    obtain ⟨hne, he⟩ : V ≠ U ∧ edge V U := by
      simpa only [pred,allowed,mem_erase,mem_filter,mem_univ,true_and] using hv
    apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun e => hne (ident e)⟩)
    intro p hp
    simpa only [members,mem_filter,mem_univ,true_and] using incl he p
      (by simpa only [members,mem_filter,mem_univ,true_and] using hp)
  · intro n U
    have hu : U ∈ allowed U := by simp [allowed,refl]
    have h := Finset.add_sum_erase (allowed U) (A n) hu
    rw [advance]
    simpa only [pred,allowed,sum_filter] using h.symm
  · simpa [members] using (Finset.card_filter_le (s:=univ) (fun p => T p=true))

end Median392

namespace Median392
open OMA.S_oeis_a250392
open scoped Classical

theorem count_shape : ∃ c : Fin 10 → ℤ, ∀ n : ℕ,
    a (n+1) = ∑ j, c j * (n.choose j.val : ℤ) := by
  let edge (S T : Fin 9 → Bool) := Comp S T ∧ ∀ p, S p = true → T p = true
  let : DecidableRel edge := fun S T => inferInstanceAs
    (Decidable (Comp S T ∧ ∀ p, S p = true → T p = true))
  have refl (T : Fin 9 → Bool) : edge T T := by
    refine ⟨?_, fun p hp => hp⟩
    intro i hi bad
    omega
  have next (n : ℕ) (T : Fin 9 → Bool) :
      M (n+1+1) T = ∑ S, if edge S T then M (n+1) S else 0 := by
    exact M_succ (n+1) T
  obtain ⟨c,hc⟩ := threshold_polynomial (d := 9) edge refl (fun h => h.2)
    (fun n => M (n+1)) next (row 511)
  refine ⟨c,fun n => ?_⟩
  rw [a_eq_G,←M_eq_G]
  exact hc n
end Median392

namespace Median392

open OMA.S_oeis_a250392 Finset

/- The packed certificate follows the method used for A249849, which credits
@Salofe's A250064 threshold-chain proof in project PR #23285. Each word stores
512 entries, indexed by the nine-bit subset mask, in radix 2^32. -/
def tb (T w : ℕ) : ℕ := (T >>> (32 * w)) % 2 ^ 32

def tabT : ℕ → ℕ
  | 0 => 0x100000001000000000000000000000001000000010000000100000001000000010000000100000000000000000000000000000001000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000001000000010000000100000001000000000000000000000000000000010000000000000001000000010000000100000000000000010000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000010000000100000000000000000000000000000000000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000010000000100000000000000000000000100000001000000010000000100000001000000010000000000000000000000000000000100000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000001000000010000000000000000000000010000000100000001000000010000000100000001000000000000000000000000000000010000000000000001000000010000000100000000000000010000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000010000000100000001000000010000000000000000000000000000000100000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000000000000000000000000000000000000000000000001000000010000000100000000000000010000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000100000001000000000000000000000001000000010000000100000001000000010000000100000000000000000000000000000001000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001
  | 1 => 0x600000003000000030000000300000003000000030000000600000003000000030000000300000006000000030000000C0000000600000006000000030000000300000003000000030000000300000005000000060000000600000003000000090000000C0000000C000000060000000C000000060000000600000003000000030000000100000003000000030000000300000003000000060000000300000005000000050000000C000000060000000C0000000600000006000000030000000900000009000000090000000C000000090000000C0000000C00000006000000090000000C0000000C000000060000000C0000000600000006000000030000000300000001000000010000000100000003000000030000000600000003000000030000000300000006000000030000000C00000006000000060000000300000005000000050000000500000005000000090000000C0000000C00000006000000090000000C0000000C000000060000000C0000000600000006000000030000000C000000040000000C0000000C0000000C0000000C00000020000000100000000C0000000C0000002000000010000000200000001000000010000000080000000C0000000C0000000C000000100000000C0000001000000010000000080000000C000000100000001000000008000000100000000800000008000000040000000300000001000000010000000100000001000000010000000200000001000000030000000300000006000000030000000C0000000600000006000000030000000300000003000000030000000300000005000000060000000600000003000000090000000C0000000C000000060000000C0000000600000006000000030000000600000002000000060000000600000006000000060000000C000000060000000C0000000C0000002000000010000000200000001000000010000000080000000C0000000C0000000C000000100000000C0000001000000010000000080000000C000000100000001000000008000000100000000800000008000000040000000600000002000000020000000200000006000000060000000C0000000600000006000000060000000C0000000600000020000000100000001000000008000000060000000600000006000000060000000C0000001000000010000000080000000C000000100000001000000008000000100000000800000008000000040000000600000002000000060000000600000006000000060000001000000008000000060000000600000010000000080000001000000008000000080000000400000006000000060000000600000008000000060000000800000008000000040000000600000008000000080000000400000008000000040000000400000002000000030000000300000001000000010000000100000001000000020000000100000001000000010000000200000001000000040000000200000002000000010000000300000003000000030000000300000005000000060000000600000003000000090000000C0000000C000000060000000C000000060000000600000003000000030000000100000003000000030000000300000003000000060000000300000005000000050000000C000000060000000C0000000600000006000000030000000C0000000C0000000C000000100000000C0000001000000010000000080000000C000000100000001000000008000000100000000800000008000000040000000300000001000000010000000100000003000000030000000600000003000000030000000300000006000000030000000C000000060000000600000003000000060000000600000006000000060000000C0000001000000010000000080000000C0000001000000010000000080000001000000008000000080000000400000006000000020000000600000006000000060000000600000010000000080000000600000006000000100000000800000010000000080000000800000004000000060000000600000006000000080000000600000008000000080000000400000006000000080000000800000004000000080000000400000004000000020000000300000001000000010000000100000001000000010000000200000001000000030000000300000006000000030000000C00000006000000060000000300000003000000030000000300000003000000050000000600000006000000030000000C00000010000000100000000800000010000000080000000800000004000000030000000100000003000000030000000300000003000000060000000300000006000000060000001000000008000000100000000800000008000000040000000600000006000000060000000800000006000000080000000800000004000000060000000800000008000000040000000800000004000000040000000200000003000000010000000100000001000000030000000300000006000000030000000300000003000000060000000300000010000000080000000800000004000000030000000300000003000000030000000600000008000000080000000400000006000000080000000800000004000000080000000400000004000000020000000300000001000000030000000300000003000000030000000800000004000000030000000300000008000000040000000800000004000000040000000200000003000000030000000300000004000000030000000400000004000000020000000300000004000000040000000200000004000000020000000200000001
  | 2 => 0x3C60000015300000163000000B50000016D000000BC000001200000006000000177000000C20000012C00000064000001CB0000009900000099000000330000016F000000C7000000C700000067000001120000009F0000009F0000003500000195000000F3000000F300000051000000F300000051000000510000001B000001770000007F000000D10000006C000000D10000006C000000A800000038000001250000009600000105000000570000010500000057000000570000001D00000195000000E1000000E100000087000000E100000087000000870000002D000000E100000087000000870000002D000000870000002D0000002D0000000F0000016D0000006E0000008600000043000000D10000006C000000A800000038000000D10000006C000000A8000000380000010500000057000000570000001D0000011200000096000000960000004D000000E100000087000000870000002D000000E100000087000000870000002D000000870000002D0000002D0000000F000001CB0000009900000105000000870000010500000087000000F3000000510000010500000087000000F300000051000000F300000051000000510000001B000000F30000008700000087000000510000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B00000009000001630000006A000000740000003A00000086000000440000006600000022000000D10000006C000000A8000000380000010500000057000000570000001D000000C70000006C0000006C000000380000009600000057000000570000001D000000E100000087000000870000002D000000870000002D0000002D0000000F0000012C00000066000000A800000057000000A800000057000000870000002D0000010500000087000000F300000051000000F300000051000000510000001B000000F30000008700000087000000510000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B0000000900000120000000570000006600000033000000A800000057000000870000002D000000A800000057000000870000002D000000F300000051000000510000001B0000009F00000057000000570000002D0000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B000000090000009900000033000000570000002D000000570000002D000000510000001B000000570000002D000000510000001B000000510000001B0000001B00000009000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B000000090000000900000003000001530000008C0000006A000000370000006E0000003A000000570000001D0000007F00000043000000660000002200000099000000330000003300000011000000C70000006C0000006C000000380000009600000057000000570000001D000000E100000087000000870000002D000000870000002D0000002D0000000F000000C2000000430000006C000000380000006C00000038000000570000001D000000960000004D000000870000002D000000870000002D0000002D0000000F000000F30000008700000087000000510000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B00000009000000BC0000003A00000044000000220000006C00000038000000570000001D0000006C00000038000000570000001D000000870000002D0000002D0000000F0000009F00000057000000570000002D0000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B000000090000009900000033000000570000002D000000570000002D000000510000001B000000570000002D000000510000001B000000510000001B0000001B00000009000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B000000090000000900000003000000B5000000370000003A0000001D000000430000002200000033000000110000006C00000038000000570000001D000000870000002D0000002D0000000F0000006700000038000000380000001D0000004D0000002D0000002D0000000F0000008700000051000000510000001B000000510000001B0000001B000000090000006400000022000000380000001D000000380000001D0000002D0000000F000000570000002D000000510000001B000000510000001B0000001B00000009000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B000000090000000900000003000000600000001D0000002200000011000000380000001D0000002D0000000F000000380000001D0000002D0000000F000000510000001B0000001B00000009000000350000001D0000001D0000000F0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B00000009000000090000000300000033000000110000001D0000000F0000001D0000000F0000001B000000090000001D0000000F0000001B000000090000001B0000000900000009000000030000001B0000000F0000000F000000090000000F0000000900000009000000030000000F00000009000000090000000300000009000000030000000300000001
  | 3 => 0x67D200001B9A00001D09000009DA00001E0F00000A5500000E080000038200001F1B00000AB700000EBC000003AF0000140000000500000005000000014000001EB000000B1600000B16000003D200000E01000005400000054000000150000012B40000072000000720000001C800000720000001C8000001C80000007200001F1B0000086F00000BA40000040200000BA400000402000005880000016200000EDA00000515000007A0000001E8000007A0000001E8000001E80000007A000012B4000006E4000006E4000002A0000006E4000002A0000002A0000000A8000006E4000002A0000002A0000000A8000002A0000000A8000000A80000002A00001E0F00000773000008BA000002EE00000BA400000402000005880000016200000BA4000004020000058800000162000007A0000001E8000001E80000007A00000E010000051500000515000001BE000006E4000002A0000002A0000000A8000006E4000002A0000002A0000000A8000002A0000000A8000000A80000002A0000140000000560000007A0000002A0000007A0000002A00000040000000100000007A0000002A000000400000001000000040000000100000001000000004000000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001000001D090000072A000007B600000296000008BA000002FA000004000000010000000BA4000004020000058800000162000007A0000001E8000001E80000007A00000B1600000402000004020000016200000515000001E8000001E80000007A000006E4000002A0000002A0000000A8000002A0000000A8000000A80000002A00000EBC0000040000000588000001E800000588000001E8000002A0000000A8000007A0000002A000000400000001000000040000000100000001000000004000000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001000000E0800000378000004000000015800000588000001E8000002A0000000A800000588000001E8000002A0000000A80000040000000100000001000000004000000540000001E8000001E8000000A8000002A0000001000000010000000040000002A0000001000000010000000040000001000000004000000040000000100000050000000158000001E8000000A8000001E8000000A80000010000000040000001E8000000A8000001000000004000000100000000400000004000000010000001C8000000A8000000A800000040000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400001B9A000007BC0000072A00000272000007730000029600000378000000DE0000086F000002EE00000400000001000000056000000158000001580000005600000B1600000402000004020000016200000515000001E8000001E80000007A000006E4000002A0000002A0000000A8000002A0000000A8000000A80000002A00000AB7000002EE00000402000001620000040200000162000001E80000007A00000515000001BE000002A0000000A8000002A0000000A8000000A80000002A00000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001000000A5500000296000002FA000001000000040200000162000001E80000007A0000040200000162000001E80000007A000002A0000000A8000000A80000002A00000540000001E8000001E8000000A8000002A0000001000000010000000040000002A0000001000000010000000040000001000000004000000040000000100000050000000158000001E8000000A8000001E8000000A80000010000000040000001E8000000A8000001000000004000000100000000400000004000000010000001C8000000A8000000A800000040000000A8000000400000004000000010000000A800000040000000400000001000000040000000100000001000000004000009DA0000027200000296000000DE000002EE0000010000000158000000560000040200000162000001E80000007A000002A0000000A8000000A80000002A000003D200000162000001620000007A000001BE000000A8000000A80000002A000002A000000100000001000000004000000100000000400000004000000010000003AF00000100000001620000007A000001620000007A000000A80000002A000001E8000000A8000001000000004000000100000000400000004000000010000001C8000000A8000000A800000040000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400000382000000DE0000010000000056000001620000007A000000A80000002A000001620000007A000000A80000002A00000100000000400000004000000010000001500000007A0000007A0000002A000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400000140000000560000007A0000002A0000007A0000002A00000040000000100000007A0000002A000000400000001000000040000000100000001000000004000000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001
  | 4 => 0x4B8CC000100D200010D7A00004465000116E0000047AB00005AFA000012320001208D00004A3F00005F6900001315000079180000183800001838000004D800011E1400004CCB00004CCB000013C400005C41000019640000196400000514000074040000203A0000203A000006720000203A00000672000006720000014A0001208D00003F2C0000502E000014A00000502E000014A000001A9000000550000060E6000018D30000222E000006D60000222E000006D6000006D60000015E0000740400001FA400001FA4000008CA00001FA4000008CA000008CA000001C200001FA4000008CA000008CA000001C2000008CA000001C2000001C20000005A000116E000003902000040BD000010540000502E000014A000001A90000005500000502E000014A000001A90000005500000222E000006D6000006D60000015E00005C41000018D3000018D30000065E00001FA4000008CA000008CA000001C200001FA4000008CA000008CA000001C2000008CA000001C2000001C20000005A0000791800001A5E0000222E000008CA0000222E000008CA00000C35000002710000222E000008CA00000C350000027100000C3500000271000002710000007D0000203A000008CA000008CA00000271000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D0000001900010D7A000036EE00003A7000000EBA000040BD00001090000014E60000042E0000502E000014A000001A90000005500000222E000006D6000006D60000015E00004CCB000014A0000014A000000550000018D3000006D6000006D60000015E00001FA4000008CA000008CA000001C2000008CA000001C2000001C20000005A00005F69000014E600001A90000006D600001A90000006D6000008CA000001C20000222E000008CA00000C350000027100000C3500000271000002710000007D0000203A000008CA000008CA00000271000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D0000001900005AFA0000128E000014E60000054600001A90000006D6000008CA000001C200001A90000006D6000008CA000001C200000C3500000271000002710000007D00001964000006D6000006D6000001C2000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D000000190000183800000546000006D6000001C2000006D6000001C2000002710000007D000006D6000001C2000002710000007D000002710000007D0000007D0000001900000672000001C2000001C20000007D000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D000000190000001900000005000100D2000037CE000036EE00000DFA0000390200000EBA0000128E000003B600003F2C00001054000014E60000042E00001A5E00000546000005460000010E00004CCB000014A0000014A000000550000018D3000006D6000006D60000015E00001FA4000008CA000008CA000001C2000008CA000001C2000001C20000005A00004A3F00001054000014A000000550000014A000000550000006D60000015E000018D30000065E000008CA000001C2000008CA000001C2000001C20000005A0000203A000008CA000008CA00000271000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D00000019000047AB00000EBA000010900000042E000014A000000550000006D60000015E000014A000000550000006D60000015E000008CA000001C2000001C20000005A00001964000006D6000006D6000001C2000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D000000190000183800000546000006D6000001C2000006D6000001C2000002710000007D000006D6000001C2000002710000007D000002710000007D0000007D0000001900000672000001C2000001C20000007D000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D0000001900000019000000050000446500000DFA00000EBA000003B6000010540000042E000005460000010E000014A000000550000006D60000015E000008CA000001C2000001C20000005A000013C400000550000005500000015E0000065E000001C2000001C20000005A000008CA00000271000002710000007D000002710000007D0000007D00000019000013150000042E000005500000015E000005500000015E000001C20000005A000006D6000001C2000002710000007D000002710000007D0000007D0000001900000672000001C2000001C20000007D000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D00000019000000190000000500001232000003B60000042E0000010E000005500000015E000001C20000005A000005500000015E000001C20000005A000002710000007D0000007D00000019000005140000015E0000015E0000005A000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D000000190000001900000005000004D80000010E0000015E0000005A0000015E0000005A0000007D000000190000015E0000005A0000007D000000190000007D0000001900000019000000050000014A0000005A0000005A000000190000005A0000001900000019000000050000005A00000019000000190000000500000019000000050000000500000001
  | 5 => 0x20F6200005D0550006136200013B23000645FA0001491A00019026000042B100067A120001540C0001A220000045B00001FC5C000054BA000054BA00000E1F0006706700015EDB00015EDB000047F9000197F00000587A0000587A00000EBF0001ED1100006B9400006B94000011EE00006B94000011EE000011EE000002FD00067A1200012D8800016C5700004AB500016C5700004AB500005BFE00000F550001A947000056F400007134000012DE00007134000012DE000012DE000003250001ED1100006A5900006A590000173400006A590000173400001734000003DE00006A590000173400001734000003DE00001734000003DE000003DE000000A5000645FA000114940001335100003E0300016C5700004AB500005BFE00000F5500016C5700004AB500005BFE00000F5500007134000012DE000012DE00000325000197F0000056F4000056F4000011CB00006A590000173400001734000003DE00006A590000173400001734000003DE00001734000003DE000003DE000000A50001FC5C00005C1C0000713400001734000071340000173400001E6000000510000071340000173400001E600000051000001E600000051000000510000000D800006B94000017340000173400000510000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D8000000240006136200010B53000119EF000038DB0001335100003ECB00004C0E00000CAD00016C5700004AB500005BFE00000F5500007134000012DE000012DE0000032500015EDB00004AB500004AB500000F55000056F4000012DE000012DE0000032500006A590000173400001734000003DE00001734000003DE000003DE000000A50001A22000004C0E00005BFE000012DE00005BFE000012DE00001734000003DE000071340000173400001E600000051000001E600000051000000510000000D800006B94000017340000173400000510000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D80000002400019026000044CA00004C0E00000F5A00005BFE000012DE00001734000003DE00005BFE000012DE00001734000003DE00001E600000051000000510000000D80000587A000012DE000012DE000003DE000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D800000024000054BA00000F5A000012DE000003DE000012DE000003DE00000510000000D8000012DE000003DE00000510000000D800000510000000D8000000D800000024000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D80000002400000024000000060005D0550001099300010B530000363B00011494000038DB000044CA00000B7700012D8800003E0300004C0E00000CAD00005C1C00000F5A00000F5A0000028F00015EDB00004AB500004AB500000F55000056F4000012DE000012DE0000032500006A590000173400001734000003DE00001734000003DE000003DE000000A50001540C00003E0300004AB500000F5500004AB500000F55000012DE00000325000056F4000011CB00001734000003DE00001734000003DE000003DE000000A500006B94000017340000173400000510000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D8000000240001491A000038DB00003ECB00000CAD00004AB500000F55000012DE0000032500004AB500000F55000012DE0000032500001734000003DE000003DE000000A50000587A000012DE000012DE000003DE000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D800000024000054BA00000F5A000012DE000003DE000012DE000003DE00000510000000D8000012DE000003DE00000510000000D800000510000000D8000000D800000024000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D800000024000000240000000600013B230000363B000038DB00000B7700003E0300000CAD00000F5A0000028F00004AB500000F55000012DE0000032500001734000003DE000003DE000000A5000047F900000F5500000F5500000325000011CB000003DE000003DE000000A5000017340000051000000510000000D800000510000000D8000000D800000024000045B000000CAD00000F550000032500000F5500000325000003DE000000A5000012DE000003DE00000510000000D800000510000000D8000000D800000024000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D8000000240000002400000006000042B100000B7700000CAD0000028F00000F5500000325000003DE000000A500000F5500000325000003DE000000A500000510000000D8000000D80000002400000EBF0000032500000325000000A5000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D800000024000000240000000600000E1F0000028F00000325000000A500000325000000A5000000D80000002400000325000000A5000000D800000024000000D8000000240000002400000006000002FD000000A5000000A500000024000000A5000000240000002400000006000000A500000024000000240000000600000024000000060000000600000001
  | 6 => 0xA41C560018B4B10019B725000455AA001A7BA3000482890005526E0000C2A2001B45A00004A59700058A210000CA97000689770000EF110000EF1100002227001B28570004C8120004C8120000D09B00056F010000F8A30000F8A300002385000662CD0001256D0001256D000029EB0001256D000029EB000029EB000005FD001B45A0000439B10004F1630000D7940004F1630000D79400010140000024C00005A1EB0000F523000132D300002BD5000132D300002BD500002BD500000643000662CD000123210001232100003441000123210000344100003441000007770001232100003441000034410000077700003441000007770000077700000111001A7BA30003EC5600044A970000B8A70004F1630000D79400010140000024C00004F1630000D79400010140000024C0000132D300002BD500002BD50000064300056F010000F5230000F523000029B30001232100003441000034410000077700012321000034410000344100000777000034410000077700000777000001110006897700010297000132D300003441000132D300003441000041A700000961000132D300003441000041A700000961000041A70000096100000961000001570001256D0000344100003441000009610000344100000961000009610000015700003441000009610000096100000157000009610000015700000157000000310019B7250003CDC40003FC240000AB6400044A970000BAB40000DBBC00001F640004F1630000D79400010140000024C0000132D300002BD500002BD5000006430004C8120000D7940000D794000024C00000F52300002BD500002BD500000643000123210000344100003441000007770000344100000777000007770000011100058A210000DBBC0001014000002BD50001014000002BD50000344100000777000132D300003441000041A700000961000041A70000096100000961000001570001256D0000344100003441000009610000344100000961000009610000015700003441000009610000096100000157000009610000015700000157000000310005526E0000C98D0000DBBC000024F10001014000002BD500003441000007770001014000002BD50000344100000777000041A70000096100000961000001570000F8A300002BD500002BD5000007770000344100000961000009610000015700003441000009610000096100000157000009610000015700000157000000310000EF11000024F100002BD50000077700002BD500000777000009610000015700002BD500000777000009610000015700000961000001570000015700000031000029EB0000077700000777000001570000077700000157000001570000003100000777000001570000015700000031000001570000003100000031000000070018B4B10003BE9E0003CDC40000A4410003EC560000AB640000C98D00001CCB000439B10000B8A70000DBBC00001F6400010297000024F1000024F1000005470004C8120000D7940000D794000024C00000F52300002BD500002BD50000064300012321000034410000344100000777000034410000077700000777000001110004A5970000B8A70000D794000024C00000D794000024C000002BD5000006430000F523000029B30000344100000777000034410000077700000777000001110001256D000034410000344100000961000034410000096100000961000001570000344100000961000009610000015700000961000001570000015700000031000482890000AB640000BAB400001F640000D794000024C000002BD5000006430000D794000024C000002BD500000643000034410000077700000777000001110000F8A300002BD500002BD5000007770000344100000961000009610000015700003441000009610000096100000157000009610000015700000157000000310000EF11000024F100002BD50000077700002BD500000777000009610000015700002BD500000777000009610000015700000961000001570000015700000031000029EB000007770000077700000157000007770000015700000157000000310000077700000157000001570000003100000157000000310000003100000007000455AA0000A4410000AB6400001CCB0000B8A700001F64000024F1000005470000D794000024C000002BD500000643000034410000077700000777000001110000D09B000024C0000024C000000643000029B300000777000007770000011100003441000009610000096100000157000009610000015700000157000000310000CA9700001F64000024C000000643000024C000000643000007770000011100002BD500000777000009610000015700000961000001570000015700000031000029EB0000077700000777000001570000077700000157000001570000003100000777000001570000015700000031000001570000003100000031000000070000C2A200001CCB00001F6400000547000024C0000006430000077700000111000024C0000006430000077700000111000009610000015700000157000000310000238500000643000006430000011100000777000001570000015700000031000007770000015700000157000000310000015700000031000000310000000700002227000005470000064300000111000006430000011100000157000000310000064300000111000001570000003100000157000000310000003100000007000005FD000001110000011100000031000001110000003100000031000000070000011100000031000000310000000700000031000000070000000700000001
  | 7 => 0x2834ACC005465640057877E000CA13C0059EBAA000D1866000F1E200001E3C4005C5FB2000D7542000FAE100001F5C200121A00000243400002434000004868005C1528000DD034000DD03400020344000F6F1E000258400002584000004B080011C3D00002B5000002B500000056A00002B500000056A0000056A000000AD4005C5FB2000C719A000E3A3000021294000E3A300002129400026AA000004D54000FEDD4000251160002D10000005A200002D10000005A2000005A2000000B440011C3D00002B1100002B110000069000002B110000069000000690000000D200002B110000069000000690000000D200000690000000D2000000D20000001A40059EBAA000BA972000C9B8C0001D0BC000E3A300002129400026AA000004D54000E3A300002129400026AA000004D540002D10000005A2000005A2000000B44000F6F1E00025116000251160000564C0002B110000069000000690000000D200002B110000069000000690000000D200000690000000D2000000D20000001A400121A0000026F000002D100000069000002D1000000690000008000000010000002D100000069000000800000001000000080000000100000001000000002000002B5000000690000006900000010000000690000001000000010000000020000006900000010000000100000000200000010000000020000000200000000400057877E000B56B4000BD0FC0001B36C000C9B8C0001D55400021CC000004398000E3A300002129400026AA000004D540002D10000005A2000005A2000000B44000DD034000212940002129400004D540002511600005A2000005A2000000B440002B110000069000000690000000D200000690000000D2000000D20000001A4000FAE1000021CC000026AA000005A2000026AA000005A200000690000000D200002D100000069000000800000001000000080000000100000001000000002000002B500000069000000690000001000000069000000100000001000000002000000690000001000000010000000020000001000000002000000020000000040000F1E200001F56000021CC000004DE000026AA000005A200000690000000D2000026AA000005A200000690000000D20000080000000100000001000000002000002584000005A2000005A2000000D200000690000001000000010000000020000006900000010000000100000000200000010000000020000000200000000400002434000004DE000005A2000000D2000005A2000000D20000010000000020000005A2000000D20000010000000020000001000000002000000020000000040000056A000000D2000000D200000020000000D2000000200000002000000004000000D200000020000000200000000400000020000000040000000400000000800546564000B1ED0000B56B40001A304000BA9720001B36C0001F56000003EAC000C719A0001D0BC00021CC00000439800026F0000004DE000004DE0000009BC000DD034000212940002129400004D540002511600005A2000005A2000000B440002B110000069000000690000000D200000690000000D2000000D20000001A4000D75420001D0BC0002129400004D540002129400004D5400005A2000000B44000251160000564C0000690000000D200000690000000D2000000D20000001A40002B500000069000000690000001000000069000000100000001000000002000000690000001000000010000000020000001000000002000000020000000040000D18660001B36C0001D554000043980002129400004D5400005A2000000B440002129400004D5400005A2000000B440000690000000D2000000D20000001A40002584000005A2000005A2000000D200000690000001000000010000000020000006900000010000000100000000200000010000000020000000200000000400002434000004DE000005A2000000D2000005A2000000D20000010000000020000005A2000000D20000010000000020000001000000002000000020000000040000056A000000D2000000D200000020000000D2000000200000002000000004000000D2000000200000002000000004000000200000000400000004000000008000CA13C0001A3040001B36C00003EAC0001D0BC0000439800004DE0000009BC0002129400004D5400005A2000000B440000690000000D2000000D20000001A40002034400004D5400004D5400000B440000564C00000D2000000D20000001A400006900000010000000100000000200000010000000020000000200000000400001F5C20000439800004D5400000B4400004D5400000B4400000D20000001A400005A2000000D20000010000000020000001000000002000000020000000040000056A000000D2000000D200000020000000D2000000200000002000000004000000D20000002000000020000000040000002000000004000000040000000080001E3C400003EAC00004398000009BC00004D5400000B4400000D20000001A400004D5400000B4400000D20000001A40000100000000200000002000000004000004B0800000B4400000B44000001A400000D2000000200000002000000004000000D200000020000000200000000400000020000000040000000400000000800004868000009BC00000B44000001A400000B44000001A4000002000000004000000B44000001A400000200000000400000020000000040000000400000000800000AD4000001A4000001A400000040000001A4000000400000004000000008000001A400000040000000400000000800000040000000080000000800000001
  | 8 => 0x83ED9E800F5432400FD92B4001FFB4E0103EDE000210F420025875C00042B7C010A6FEE0021E5DA0026CDAE00044FBE002C0CB80004E4F80004E4F800008B380109C8C00022B7320022B73200046AD0002649F600050E5000050E5000008FD0002B5E100005BD640005BD640000A3440005BD640000A3440000A34400001224010A6FEE001FB7980023A63C000489000023A63C00048900000531C0000093C00027615C000500E20005F28C0000A92C0005F28C0000A92C0000A92C000012CC002B5E100005B7100005B7100000C1A40005B7100000C1A40000C1A4000015840005B7100000C1A40000C1A4000015840000C1A40000158400001584000002640103EDE0001DF124002013F600040A100023A63C00048900000531C0000093C00023A63C00048900000531C0000093C00005F28C0000A92C0000A92C000012CC002649F6000500E2000500E20000A2CC0005B7100000C1A40000C1A4000015840005B7100000C1A40000C1A4000015840000C1A4000015840000158400000264002C0CB800053C4C0005F28C0000C1A40005F28C0000C1A40000E6A9000019A10005F28C0000C1A40000E6A9000019A10000E6A9000019A1000019A1000002D90005BD640000C1A40000C1A4000019A10000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D90000005100FD92B4001D2EE4001E48C00003CFFC002013F60004134000049E84000083640023A63C00048900000531C0000093C00005F28C0000A92C0000A92C000012CC0022B7320004890000048900000093C0000500E20000A92C0000A92C000012CC0005B7100000C1A40000C1A4000015840000C1A40000158400001584000002640026CDAE00049E84000531C00000A92C000531C00000A92C0000C1A4000015840005F28C0000C1A40000E6A9000019A10000E6A9000019A1000019A1000002D90005BD640000C1A40000C1A4000019A10000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D9000000510025875C000451BC00049E84000094EC000531C00000A92C0000C1A400001584000531C00000A92C0000C1A4000015840000E6A9000019A1000019A1000002D900050E500000A92C0000A92C000015840000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D9000000510004E4F8000094EC0000A92C000015840000A92C00001584000019A1000002D90000A92C00001584000019A1000002D9000019A1000002D9000002D9000000510000A3440000158400001584000002D900001584000002D9000002D90000005100001584000002D9000002D900000051000002D900000051000000510000000900F54324001C94F4001D2EE40003AE84001DF1240003CFFC000451BC00007ADC001FB79800040A1000049E840000836400053C4C000094EC000094EC0000108C0022B7320004890000048900000093C0000500E20000A92C0000A92C000012CC0005B7100000C1A40000C1A4000015840000C1A40000158400001584000002640021E5DA00040A1000048900000093C000048900000093C00000A92C000012CC000500E20000A2CC0000C1A4000015840000C1A40000158400001584000002640005BD640000C1A40000C1A4000019A10000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D90000005100210F420003CFFC000413400000836400048900000093C00000A92C000012CC00048900000093C00000A92C000012CC0000C1A400001584000015840000026400050E500000A92C0000A92C000015840000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D9000000510004E4F8000094EC0000A92C000015840000A92C00001584000019A1000002D90000A92C00001584000019A1000002D9000019A1000002D9000002D9000000510000A3440000158400001584000002D900001584000002D9000002D90000005100001584000002D9000002D900000051000002D9000000510000005100000009001FFB4E0003AE840003CFFC00007ADC00040A1000008364000094EC0000108C00048900000093C00000A92C000012CC0000C1A400001584000015840000026400046AD0000093C0000093C0000012CC0000A2CC0000158400001584000002640000C1A4000019A1000019A1000002D9000019A1000002D9000002D90000005100044FBE00008364000093C0000012CC000093C0000012CC00001584000002640000A92C00001584000019A1000002D9000019A1000002D9000002D9000000510000A3440000158400001584000002D900001584000002D9000002D90000005100001584000002D9000002D900000051000002D900000051000000510000000900042B7C00007ADC000083640000108C000093C0000012CC0000158400000264000093C0000012CC0000158400000264000019A1000002D9000002D90000005100008FD0000012CC000012CC0000026400001584000002D9000002D90000005100001584000002D9000002D900000051000002D900000051000000510000000900008B380000108C000012CC00000264000012CC00000264000002D900000051000012CC00000264000002D900000051000002D900000051000000510000000900001224000002640000026400000051000002640000005100000051000000090000026400000051000000510000000900000051000000090000000900000001
  | 9 => 0x17964192027562D70288F56D0048B1630297F1F5004AF1BD0053F3D60008652F02A74325004CB129005691EA0008A8310060FA2C0009B29E0009B29E0000F84302A5EE93004E6423004E64230008D9FF005593A70009FD9E0009FD9E0000FFC3005FB1C1000B313C000B313C00011E86000B313C00011E8600011E8600001CA702A74325004864E300504D23000910D700504D23000910D7000A3CE6000106170057C5490009E61F000B8EFC000127E6000B8EFC000127E6000127E600001D97005FB1C1000B2791000B279100014DFC000B279100014DFC00014DFC00002166000B279100014DFC00014DFC0000216600014DFC0000216600002166000003570297F1F50044BE4B00491E7100082E1500504D23000910D7000A3CE60001061700504D23000910D7000A3CE600010617000B8EFC000127E6000127E600001D97005593A70009E61F0009E61F00011DE1000B279100014DFC00014DFC00002166000B279100014DFC00014DFC0000216600014DFC0000216600002166000003570060FA2C000A5294000B8EFC00014DFC000B8EFC00014DFC000186A000002710000B8EFC00014DFC000186A000002710000186A00000271000002710000003E8000B313C00014DFC00014DFC0000271000014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E8000000640288F56D0043246500456F2D0007C42500491E7100083EF5000939EA0000EC3100504D23000910D7000A3CE600010617000B8EFC000127E6000127E600001D97004E6423000910D7000910D7000106170009E61F000127E6000127E600001D97000B279100014DFC00014DFC0000216600014DFC000021660000216600000357005691EA000939EA000A3CE6000127E6000A3CE6000127E600014DFC00002166000B8EFC00014DFC000186A000002710000186A00000271000002710000003E8000B313C00014DFC00014DFC0000271000014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E8000000640053F3D60008AFA2000939EA00010842000A3CE6000127E600014DFC00002166000A3CE6000127E600014DFC00002166000186A00000271000002710000003E80009FD9E000127E6000127E60000216600014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E8000000640009B29E00010842000127E600002166000127E60000216600002710000003E8000127E60000216600002710000003E800002710000003E8000003E80000006400011E860000216600002166000003E800002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A027562D70041BE1B00432465000785B50044BE4B0007C4250008AFA20000DE5D004864E300082E15000939EA0000EC31000A5294000108420001084200001A6D004E6423000910D7000910D7000106170009E61F000127E6000127E600001D97000B279100014DFC00014DFC0000216600014DFC000021660000216600000357004CB12900082E15000910D700010617000910D700010617000127E600001D970009E61F00011DE100014DFC0000216600014DFC000021660000216600000357000B313C00014DFC00014DFC0000271000014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E800000064004AF1BD0007C42500083EF50000EC31000910D700010617000127E600001D97000910D700010617000127E600001D9700014DFC0000216600002166000003570009FD9E000127E6000127E60000216600014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E8000000640009B29E00010842000127E600002166000127E60000216600002710000003E8000127E60000216600002710000003E800002710000003E8000003E80000006400011E860000216600002166000003E800002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A0048B163000785B50007C4250000DE5D00082E150000EC310001084200001A6D000910D700010617000127E600001D9700014DFC0000216600002166000003570008D9FF000106170001061700001D9700011DE100002166000021660000035700014DFC0000271000002710000003E800002710000003E8000003E8000000640008A8310000EC310001061700001D970001061700001D970000216600000357000127E60000216600002710000003E800002710000003E8000003E80000006400011E860000216600002166000003E800002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A0008652F0000DE5D0000EC3100001A6D0001061700001D9700002166000003570001061700001D97000021660000035700002710000003E8000003E8000000640000FFC300001D9700001D970000035700002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A0000F84300001A6D00001D970000035700001D9700000357000003E80000006400001D9700000357000003E800000064000003E800000064000000640000000A00001CA70000035700000357000000640000035700000064000000640000000A0000035700000064000000640000000A000000640000000A0000000A00000001
  | 10 => 0x3C80C40605B778DF05E177A70097A9EB0601A481009C007200ACE1A4000FB76C062279B5009F5D4800B1DAFA00102B2E00C51A6B0011EB210011EB210001A103061FF67700A29FB100A29FB1001080E700B00EF400126ABF00126ABF0001AC9D00C2D50D00146937001469370001DB05001469370001DB050001DB0500002B2F062279B5009775AB00A63E450010DE5C00A63E450010DE5C0012D5180001B64800B42861001243DC001505310001E933001505310001E9330001E93300002C7900C2D50D00145B0900145B09000221EB00145B09000221EB000221EB000031A100145B09000221EB000221EB000031A1000221EB000031A1000031A1000004830601A481009083260098D04C000F610300A63E450010DE5C0012D5180001B64800A63E450010DE5C0012D5180001B648001505310001E9330001E93300002C7900B00EF4001243DC001243DC0001DA2900145B09000221EB000221EB000031A100145B09000221EB000221EB000031A1000221EB000031A1000031A10000048300C51A6B0012FD4500150531000221EB00150531000221EB0002751B0000393100150531000221EB0002751B000039310002751B00003931000039310000053300146937000221EB000221EB00003931000221EB000039310000393100000533000221EB0000393100003931000005330000393100000533000005330000007905E177A7008D67060091CEF4000EABE60098D04C000F7E04001126FA00018F2E00A63E450010DE5C0012D5180001B648001505310001E9330001E93300002C7900A29FB10010DE5C0010DE5C0001B648001243DC0001E9330001E93300002C7900145B09000221EB000221EB000031A1000221EB000031A1000031A10000048300B1DAFA001126FA0012D5180001E9330012D5180001E933000221EB000031A100150531000221EB0002751B000039310002751B00003931000039310000053300146937000221EB000221EB00003931000221EB000039310000393100000533000221EB0000393100003931000005330000393100000533000005330000007900ACE1A400103D03001126FA0001B9EF0012D5180001E933000221EB000031A10012D5180001E933000221EB000031A10002751B00003931000039310000053300126ABF0001E9330001E933000031A1000221EB000039310000393100000533000221EB000039310000393100000533000039310000053300000533000000790011EB210001B9EF0001E933000031A10001E933000031A100003931000005330001E933000031A10000393100000533000039310000053300000533000000790001DB05000031A1000031A100000533000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B05B778DF008A7F68008D6706000E3F3B00908326000EABE600103D03000179E9009775AB000F6103001126FA00018F2E0012FD450001B9EF0001B9EF0000282D00A29FB10010DE5C0010DE5C0001B648001243DC0001E9330001E93300002C7900145B09000221EB000221EB000031A1000221EB000031A1000031A100000483009F5D48000F61030010DE5C0001B6480010DE5C0001B6480001E93300002C79001243DC0001DA29000221EB000031A1000221EB000031A1000031A10000048300146937000221EB000221EB00003931000221EB000039310000393100000533000221EB00003931000039310000053300003931000005330000053300000079009C0072000EABE6000F7E0400018F2E0010DE5C0001B6480001E93300002C790010DE5C0001B6480001E93300002C79000221EB000031A1000031A10000048300126ABF0001E9330001E933000031A1000221EB000039310000393100000533000221EB000039310000393100000533000039310000053300000533000000790011EB210001B9EF0001E933000031A10001E933000031A100003931000005330001E933000031A10000393100000533000039310000053300000533000000790001DB05000031A1000031A100000533000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B0097A9EB000E3F3B000EABE6000179E9000F610300018F2E0001B9EF0000282D0010DE5C0001B6480001E93300002C79000221EB000031A1000031A100000483001080E70001B6480001B64800002C790001DA29000031A1000031A100000483000221EB0000393100003931000005330000393100000533000005330000007900102B2E00018F2E0001B64800002C790001B64800002C79000031A1000004830001E933000031A10000393100000533000039310000053300000533000000790001DB05000031A1000031A100000533000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B000FB76C000179E900018F2E0000282D0001B64800002C79000031A1000004830001B64800002C79000031A100000483000039310000053300000533000000790001AC9D00002C7900002C7900000483000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B0001A1030000282D00002C790000048300002C7900000483000005330000007900002C790000048300000533000000790000053300000079000000790000000B00002B2F0000048300000483000000790000048300000079000000790000000B0000048300000079000000790000000B000000790000000B0000000B00000001
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem base_T : ∀ u : Fin 512, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_0 : ∀ u : Fin 512, u.val / 16 = 0 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_1 : ∀ u : Fin 512, u.val / 16 = 1 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_2 : ∀ u : Fin 512, u.val / 16 = 2 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_3 : ∀ u : Fin 512, u.val / 16 = 3 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_4 : ∀ u : Fin 512, u.val / 16 = 4 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_5 : ∀ u : Fin 512, u.val / 16 = 5 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_6 : ∀ u : Fin 512, u.val / 16 = 6 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_7 : ∀ u : Fin 512, u.val / 16 = 7 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_8 : ∀ u : Fin 512, u.val / 16 = 8 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_9 : ∀ u : Fin 512, u.val / 16 = 9 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_10 : ∀ u : Fin 512, u.val / 16 = 10 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_11 : ∀ u : Fin 512, u.val / 16 = 11 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_12 : ∀ u : Fin 512, u.val / 16 = 12 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_13 : ∀ u : Fin 512, u.val / 16 = 13 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_14 : ∀ u : Fin 512, u.val / 16 = 14 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_15 : ∀ u : Fin 512, u.val / 16 = 15 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_16 : ∀ u : Fin 512, u.val / 16 = 16 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_17 : ∀ u : Fin 512, u.val / 16 = 17 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_18 : ∀ u : Fin 512, u.val / 16 = 18 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_19 : ∀ u : Fin 512, u.val / 16 = 19 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_20 : ∀ u : Fin 512, u.val / 16 = 20 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_21 : ∀ u : Fin 512, u.val / 16 = 21 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_22 : ∀ u : Fin 512, u.val / 16 = 22 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_23 : ∀ u : Fin 512, u.val / 16 = 23 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_24 : ∀ u : Fin 512, u.val / 16 = 24 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_25 : ∀ u : Fin 512, u.val / 16 = 25 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_26 : ∀ u : Fin 512, u.val / 16 = 26 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_27 : ∀ u : Fin 512, u.val / 16 = 27 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_28 : ∀ u : Fin 512, u.val / 16 = 28 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_29 : ∀ u : Fin 512, u.val / 16 = 29 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_30 : ∀ u : Fin 512, u.val / 16 = 30 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_31 : ∀ u : Fin 512, u.val / 16 = 31 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

theorem step_all (n : ℕ) (hn : n < 10) (u : Fin 512) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  have hu := u.isLt
  obtain ⟨c, hc⟩ : ∃ c, u.val / 16 = c := ⟨_, rfl⟩
  have hc2 : c < 32 := by omega
  interval_cases c
  · exact chunk_0 u hc n hn
  · exact chunk_1 u hc n hn
  · exact chunk_2 u hc n hn
  · exact chunk_3 u hc n hn
  · exact chunk_4 u hc n hn
  · exact chunk_5 u hc n hn
  · exact chunk_6 u hc n hn
  · exact chunk_7 u hc n hn
  · exact chunk_8 u hc n hn
  · exact chunk_9 u hc n hn
  · exact chunk_10 u hc n hn
  · exact chunk_11 u hc n hn
  · exact chunk_12 u hc n hn
  · exact chunk_13 u hc n hn
  · exact chunk_14 u hc n hn
  · exact chunk_15 u hc n hn
  · exact chunk_16 u hc n hn
  · exact chunk_17 u hc n hn
  · exact chunk_18 u hc n hn
  · exact chunk_19 u hc n hn
  · exact chunk_20 u hc n hn
  · exact chunk_21 u hc n hn
  · exact chunk_22 u hc n hn
  · exact chunk_23 u hc n hn
  · exact chunk_24 u hc n hn
  · exact chunk_25 u hc n hn
  · exact chunk_26 u hc n hn
  · exact chunk_27 u hc n hn
  · exact chunk_28 u hc n hn
  · exact chunk_29 u hc n hn
  · exact chunk_30 u hc n hn
  · exact chunk_31 u hc n hn

theorem G_eq_T (n : ℕ) (hn : n ≤ 10) : ∀ u : Fin 512, G n u = tb (tabT n) u.val := by
  induction n with
  | zero => exact base_T
  | succ n ih =>
    intro u
    rw [G_succ]
    have ih' := ih (by omega)
    simp only [ih']
    exact step_all n (by omega) u

/-- The full-mask counts after one through ten levels. -/
def samples : Fin 10 → ℤ := ![6, 966, 26578, 309452, 2160160, 10755158, 42158796, 138336744, 395723154, 1015071750]

theorem samples_valid (n : Fin 10) : a (n.val + 1) = samples n := by
  rw [a_eq_G, G_eq_T (n.val + 1) (by omega)]
  have check : ∀ i : Fin 10, (tb (tabT (i.val + 1)) 511 : ℤ) = samples i := by
    decide +kernel
  exact check n

end Median392

namespace Median392
open PowerSeries
open OMA.S_oeis_a250392

def observations : Fin 10 → ℤ := ![6, 966, 26578, 309452, 2160160, 10755158, 42158796, 138336744, 395723154, 1015071750]
def weights : Fin 10 → ℤ := ![6, 960, 24652, 232610, 1077962, 2787922, 4234088, 3757328, 1804992, 362880]

/-- The square matrix of binomial coefficients is unit lower triangular. -/
theorem binomial_unique {D : ℕ} {c t : Fin D → ℤ}
    (h : ∀ n : Fin D, ∑ d, c d * ((n.val.choose d.val : ℕ):ℤ) =
      ∑ d, t d * ((n.val.choose d.val : ℕ):ℤ)) : c=t := by
  funext i
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | h k ih =>
    have hz : ∑ d : Fin D, (c d-t d) * ((i.val.choose d.val : ℕ):ℤ) = 0 := by
      simp only [sub_mul,Finset.sum_sub_distrib,h i,sub_self]
    rw [Finset.sum_eq_single i] at hz
    · simpa using sub_eq_zero.mp (by simpa using hz : c i-t i=0)
    · intro d _ hdi
      by_cases lt : d.val < i.val
      · have e := ih d.val (by omega) d rfl
        simp [e]
      · have hn : i.val < d.val := by
          have ne : d.val≠i.val := fun h => hdi (Fin.ext h)
          omega
        simp [Nat.choose_eq_zero_of_lt hn]
    · simp

theorem weights_observations (n : Fin 10) :
    ∑ d : Fin 10, weights d * ((n.val.choose d.val : ℕ):ℤ) = observations n := by
  revert n
  decide +kernel

/-- The explicit binomial-basis polynomial valid at every positive parameter. -/
theorem explicit_counts
    (shape : ∃ c : Fin 10 → ℤ, ∀ n : ℕ, a (n+1) = ∑ d, c d * ((n.choose d.val : ℕ):ℤ))
    (data : ∀ n : Fin 10, a (n.val+1)=observations n) (n : ℕ) :
    a (n+1)= ∑ d : Fin 10, weights d * ((n.choose d.val : ℕ):ℤ) := by
  obtain ⟨c,hc⟩ := shape
  have ht : c=weights := binomial_unique (fun i => by rw [← hc,data,weights_observations])
  simpa [ht] using hc n

noncomputable def binSeries (d : ℕ) : PowerSeries ℚ := mk fun n => (n.choose d : ℚ)

theorem binSeries_one_sub (d : ℕ) : binSeries d * (1-X)^(d+1) = X^d := by
  induction d with
  | zero =>
    ext n
    cases n with
    | zero => simp [binSeries]
    | succ n => simp [binSeries,mul_sub,coeff_succ_mul_X,coeff_one]
  | succ d ih =>
    have step : binSeries (d+1)*(1-X)=X*binSeries d := by
      ext n
      cases n with
      | zero => simp [binSeries,mul_sub]
      | succ n =>
        simp [binSeries,mul_sub,coeff_succ_mul_X,coeff_succ_X_mul,Nat.choose_succ_succ]
    calc
      _ = (binSeries (d+1)*(1-X))*(1-X)^(d+1) := by ring
      _ = X*(binSeries d*(1-X)^(d+1)) := by rw [step]; ring
      _ = X^(d+1) := by rw [ih,pow_succ]; ring

noncomputable def series : PowerSeries ℚ := mk fun n => if n < 1 then 0 else (a n:ℚ)

theorem rational_binomial_series {D : ℕ} (v : Fin (D+1) → ℤ) (b : ℕ → ℤ)
    (h : ∀ n : ℕ, b (n+1)= ∑ d : Fin (D+1), v d * ((n.choose d.val : ℕ):ℤ)) :
    mk (fun n => if n<1 then 0 else (b n : ℚ)) * (1-X)^(D+1) =
      X*∑ d : Fin (D+1), C ((v d:ℤ):ℚ)*(X^d.val*(1-X)^(D-d.val)) := by
  have rep : mk (fun n => if n<1 then 0 else (b n : ℚ)) =
      X * ∑ d : Fin (D+1), C ((v d:ℤ):ℚ)*binSeries d.val := by
    ext n
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_succ_X_mul]
      simp only [coeff_mk,if_neg (by omega : ¬n+1<1),map_sum,coeff_C_mul,binSeries]
      exact_mod_cast h n
  have reduce (d : Fin (D+1)) : binSeries d.val*(1-X)^(D+1) = X^d.val*(1-X)^(D-d.val) := by
    have add : D+1=d.val+1+(D-d.val) := by omega
    have ep := congrArg (fun e : ℕ => (1-X : PowerSeries ℚ)^e) add
    rw [pow_add _ (d.val+1) (D-d.val)] at ep
    rw [ep,← mul_assoc,binSeries_one_sub]
  rw [rep,mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,reduce]

theorem gf_of_explicit
    (h : ∀ n : ℕ, a (n+1)= ∑ d : Fin 10, weights d * ((n.choose d.val : ℕ):ℤ)) :
    series * (1-X)^10 = 2*X*(3+453*X+8594*X^2+43211*X^3+73495*X^4+45443*X^5+9692*X^6+549*X^7) := by
  have hf := rational_binomial_series (D:=9) weights a h
  change series*(1-X)^10 = _ at hf
  rw [hf]
  norm_num [weights,Fin.sum_univ_succ]
  ring

end Median392

namespace Median392
open PowerSeries
open OMA.S_oeis_a250392

/-- Read the tenth finite difference off the numerator. -/
theorem recurrence_of_gf
    (h : series * (1-X)^10 = 2*X*(3+453*X+8594*X^2+43211*X^3+73495*X^4+45443*X^5+9692*X^6+549*X^7))
    (n : ℕ) (hn : 11≤n) :
    (a n : ℚ) = 10*a (n-1) - 45*a (n-2) + 120*a (n-3) - 210*a (n-4) +
      252*a (n-5) - 210*a (n-6) + 120*a (n-7) - 45*a (n-8) + 10*a (n-9) - a (n-10) := by
  have eqn : series - C 10*(series*X^1) + C 45*(series*X^2) - C 120*(series*X^3) +
      C 210*(series*X^4) - C 252*(series*X^5) + C 210*(series*X^6) - C 120*(series*X^7) +
      C 45*(series*X^8) - C 10*(series*X^9) + series*X^10 =
      C 6*X^1+C 906*X^2+C 17188*X^3+C 86422*X^4+C 146990*X^5+
      C 90886*X^6+C 19384*X^7+C 1098*X^8 := by
    simp only [map_ofNat]
    linear_combination h
  have atn := congrArg (coeff n) eqn
  simp only [map_sub,map_add,coeff_C_mul,coeff_mul_X_pow',coeff_C,series,coeff_mk] at atn
  simp (disch := omega) only [if_pos, if_neg, add_zero] at atn
  linarith only [atn]

end Median392

open Median392 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250392.main := by
  have data (n : Fin 10) : OMA.S_oeis_a250392.a (n.val+1) = observations n := samples_valid n
  have gf := gf_of_explicit (explicit_counts count_shape data)
  exact ⟨gf, recurrence_of_gf gf⟩
