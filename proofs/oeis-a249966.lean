import OMAStatements.S_oeis_a249966

/-!
A249966: the generating function and recurrence for eleven-position arrays with
strict second/third order-statistic gaps in every length-six window.

Adapted with credit from @Salofe's A250064 threshold-chain proof, PR23285,
https://github.com/lefttosolve2/open-math-agents/pull/23285
(head bd4969a8ddc52c3bd7f8d30008570b9868fd00b6).
The exact six windows, 2048 subset states and all packed tables are regenerated
and kernel checked here. A state-vector finite-difference identity propagates by
linearity to every index, yielding the universal recurrence and generating function.
The conjectures are Colin Barker's; the formal statement is @clementtrecourt's.
-/

namespace OMA.Helpers

open OMA.S_oeis_a249966 Finset

/-! ### The window condition -/

/-- The condition of the statement on 6 values (without the bound on `v`). -/
def Cy (y : Fin 6 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 6)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 6 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
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

theorem cy_of (y : Fin 6 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 6)) y Finset.univ_nonempty
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

theorem window_iff (y : Fin 6 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 6 → ℕ) :
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
def fget (f : Fin 11 → Bool) (k : ℕ) : Bool := if h : k < 11 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 11 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 6 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 11 → Bool) : Prop := ∀ i < (6 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 11 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 11 → Fin (n + 1)) (v : ℕ) : Fin 11 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 11 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a249966.get x k ≤ n := by
  unfold OMA.S_oeis_a249966.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (6 : ℕ), cntW (fun _ => true) i = 6 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 11 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (6 : ℕ), ¬ Cy (fun t : Fin 6 => OMA.S_oeis_a249966.get x (i + t)) := by
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
      (univ.filter (fun t : Fin 6 => OMA.S_oeis_a249966.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 11 := by have := t.isLt; omega
    unfold OMA.S_oeis_a249966.get fget Lt
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
noncomputable def M (n : ℕ) (T : Fin 11 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 11 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 11 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 11 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 11 → Fin (n + 2)) : Fin 11 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 11 → Bool) (x : Fin 11 → Fin (n + 1)) : Fin 11 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 11 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 11 → Bool) (x : Fin 11 → Fin (n + 1)) (p : Fin 11) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 11 → Bool) :
    M (n + 1) T = ∑ S : Fin 11 → Bool,
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
def row (u : Fin 2048) : Fin 11 → Bool := fun p => Nat.testBit u.val p.val

def idIndex (k : Fin 64) (i : Fin 32) : Fin 2048 := ⟨32 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · exact congrFun h ⟨i, hi⟩
  · have hp : 2048 ≤ 2 ^ i := by
      change 2 ^ 11 ≤ 2 ^ i
      exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hp)]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 11 bits. -/
def pcb (m : ℕ) : ℕ :=
  m / 1 % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2 + m / 256 % 2 + m / 512 % 2 + m / 1024 % 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_0 : ∀ i : Fin 32, cntW (row (idIndex 0 i)) 0 = pcb ((idIndex 0 i).val &&& 63) ∧ cntW (row (idIndex 0 i)) 1 = pcb ((idIndex 0 i).val &&& 126) ∧ cntW (row (idIndex 0 i)) 2 = pcb ((idIndex 0 i).val &&& 252) ∧ cntW (row (idIndex 0 i)) 3 = pcb ((idIndex 0 i).val &&& 504) ∧ cntW (row (idIndex 0 i)) 4 = pcb ((idIndex 0 i).val &&& 1008) ∧ cntW (row (idIndex 0 i)) 5 = pcb ((idIndex 0 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_1 : ∀ i : Fin 32, cntW (row (idIndex 1 i)) 0 = pcb ((idIndex 1 i).val &&& 63) ∧ cntW (row (idIndex 1 i)) 1 = pcb ((idIndex 1 i).val &&& 126) ∧ cntW (row (idIndex 1 i)) 2 = pcb ((idIndex 1 i).val &&& 252) ∧ cntW (row (idIndex 1 i)) 3 = pcb ((idIndex 1 i).val &&& 504) ∧ cntW (row (idIndex 1 i)) 4 = pcb ((idIndex 1 i).val &&& 1008) ∧ cntW (row (idIndex 1 i)) 5 = pcb ((idIndex 1 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_2 : ∀ i : Fin 32, cntW (row (idIndex 2 i)) 0 = pcb ((idIndex 2 i).val &&& 63) ∧ cntW (row (idIndex 2 i)) 1 = pcb ((idIndex 2 i).val &&& 126) ∧ cntW (row (idIndex 2 i)) 2 = pcb ((idIndex 2 i).val &&& 252) ∧ cntW (row (idIndex 2 i)) 3 = pcb ((idIndex 2 i).val &&& 504) ∧ cntW (row (idIndex 2 i)) 4 = pcb ((idIndex 2 i).val &&& 1008) ∧ cntW (row (idIndex 2 i)) 5 = pcb ((idIndex 2 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_3 : ∀ i : Fin 32, cntW (row (idIndex 3 i)) 0 = pcb ((idIndex 3 i).val &&& 63) ∧ cntW (row (idIndex 3 i)) 1 = pcb ((idIndex 3 i).val &&& 126) ∧ cntW (row (idIndex 3 i)) 2 = pcb ((idIndex 3 i).val &&& 252) ∧ cntW (row (idIndex 3 i)) 3 = pcb ((idIndex 3 i).val &&& 504) ∧ cntW (row (idIndex 3 i)) 4 = pcb ((idIndex 3 i).val &&& 1008) ∧ cntW (row (idIndex 3 i)) 5 = pcb ((idIndex 3 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_4 : ∀ i : Fin 32, cntW (row (idIndex 4 i)) 0 = pcb ((idIndex 4 i).val &&& 63) ∧ cntW (row (idIndex 4 i)) 1 = pcb ((idIndex 4 i).val &&& 126) ∧ cntW (row (idIndex 4 i)) 2 = pcb ((idIndex 4 i).val &&& 252) ∧ cntW (row (idIndex 4 i)) 3 = pcb ((idIndex 4 i).val &&& 504) ∧ cntW (row (idIndex 4 i)) 4 = pcb ((idIndex 4 i).val &&& 1008) ∧ cntW (row (idIndex 4 i)) 5 = pcb ((idIndex 4 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_5 : ∀ i : Fin 32, cntW (row (idIndex 5 i)) 0 = pcb ((idIndex 5 i).val &&& 63) ∧ cntW (row (idIndex 5 i)) 1 = pcb ((idIndex 5 i).val &&& 126) ∧ cntW (row (idIndex 5 i)) 2 = pcb ((idIndex 5 i).val &&& 252) ∧ cntW (row (idIndex 5 i)) 3 = pcb ((idIndex 5 i).val &&& 504) ∧ cntW (row (idIndex 5 i)) 4 = pcb ((idIndex 5 i).val &&& 1008) ∧ cntW (row (idIndex 5 i)) 5 = pcb ((idIndex 5 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_6 : ∀ i : Fin 32, cntW (row (idIndex 6 i)) 0 = pcb ((idIndex 6 i).val &&& 63) ∧ cntW (row (idIndex 6 i)) 1 = pcb ((idIndex 6 i).val &&& 126) ∧ cntW (row (idIndex 6 i)) 2 = pcb ((idIndex 6 i).val &&& 252) ∧ cntW (row (idIndex 6 i)) 3 = pcb ((idIndex 6 i).val &&& 504) ∧ cntW (row (idIndex 6 i)) 4 = pcb ((idIndex 6 i).val &&& 1008) ∧ cntW (row (idIndex 6 i)) 5 = pcb ((idIndex 6 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_7 : ∀ i : Fin 32, cntW (row (idIndex 7 i)) 0 = pcb ((idIndex 7 i).val &&& 63) ∧ cntW (row (idIndex 7 i)) 1 = pcb ((idIndex 7 i).val &&& 126) ∧ cntW (row (idIndex 7 i)) 2 = pcb ((idIndex 7 i).val &&& 252) ∧ cntW (row (idIndex 7 i)) 3 = pcb ((idIndex 7 i).val &&& 504) ∧ cntW (row (idIndex 7 i)) 4 = pcb ((idIndex 7 i).val &&& 1008) ∧ cntW (row (idIndex 7 i)) 5 = pcb ((idIndex 7 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_8 : ∀ i : Fin 32, cntW (row (idIndex 8 i)) 0 = pcb ((idIndex 8 i).val &&& 63) ∧ cntW (row (idIndex 8 i)) 1 = pcb ((idIndex 8 i).val &&& 126) ∧ cntW (row (idIndex 8 i)) 2 = pcb ((idIndex 8 i).val &&& 252) ∧ cntW (row (idIndex 8 i)) 3 = pcb ((idIndex 8 i).val &&& 504) ∧ cntW (row (idIndex 8 i)) 4 = pcb ((idIndex 8 i).val &&& 1008) ∧ cntW (row (idIndex 8 i)) 5 = pcb ((idIndex 8 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_9 : ∀ i : Fin 32, cntW (row (idIndex 9 i)) 0 = pcb ((idIndex 9 i).val &&& 63) ∧ cntW (row (idIndex 9 i)) 1 = pcb ((idIndex 9 i).val &&& 126) ∧ cntW (row (idIndex 9 i)) 2 = pcb ((idIndex 9 i).val &&& 252) ∧ cntW (row (idIndex 9 i)) 3 = pcb ((idIndex 9 i).val &&& 504) ∧ cntW (row (idIndex 9 i)) 4 = pcb ((idIndex 9 i).val &&& 1008) ∧ cntW (row (idIndex 9 i)) 5 = pcb ((idIndex 9 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_10 : ∀ i : Fin 32, cntW (row (idIndex 10 i)) 0 = pcb ((idIndex 10 i).val &&& 63) ∧ cntW (row (idIndex 10 i)) 1 = pcb ((idIndex 10 i).val &&& 126) ∧ cntW (row (idIndex 10 i)) 2 = pcb ((idIndex 10 i).val &&& 252) ∧ cntW (row (idIndex 10 i)) 3 = pcb ((idIndex 10 i).val &&& 504) ∧ cntW (row (idIndex 10 i)) 4 = pcb ((idIndex 10 i).val &&& 1008) ∧ cntW (row (idIndex 10 i)) 5 = pcb ((idIndex 10 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_11 : ∀ i : Fin 32, cntW (row (idIndex 11 i)) 0 = pcb ((idIndex 11 i).val &&& 63) ∧ cntW (row (idIndex 11 i)) 1 = pcb ((idIndex 11 i).val &&& 126) ∧ cntW (row (idIndex 11 i)) 2 = pcb ((idIndex 11 i).val &&& 252) ∧ cntW (row (idIndex 11 i)) 3 = pcb ((idIndex 11 i).val &&& 504) ∧ cntW (row (idIndex 11 i)) 4 = pcb ((idIndex 11 i).val &&& 1008) ∧ cntW (row (idIndex 11 i)) 5 = pcb ((idIndex 11 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_12 : ∀ i : Fin 32, cntW (row (idIndex 12 i)) 0 = pcb ((idIndex 12 i).val &&& 63) ∧ cntW (row (idIndex 12 i)) 1 = pcb ((idIndex 12 i).val &&& 126) ∧ cntW (row (idIndex 12 i)) 2 = pcb ((idIndex 12 i).val &&& 252) ∧ cntW (row (idIndex 12 i)) 3 = pcb ((idIndex 12 i).val &&& 504) ∧ cntW (row (idIndex 12 i)) 4 = pcb ((idIndex 12 i).val &&& 1008) ∧ cntW (row (idIndex 12 i)) 5 = pcb ((idIndex 12 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_13 : ∀ i : Fin 32, cntW (row (idIndex 13 i)) 0 = pcb ((idIndex 13 i).val &&& 63) ∧ cntW (row (idIndex 13 i)) 1 = pcb ((idIndex 13 i).val &&& 126) ∧ cntW (row (idIndex 13 i)) 2 = pcb ((idIndex 13 i).val &&& 252) ∧ cntW (row (idIndex 13 i)) 3 = pcb ((idIndex 13 i).val &&& 504) ∧ cntW (row (idIndex 13 i)) 4 = pcb ((idIndex 13 i).val &&& 1008) ∧ cntW (row (idIndex 13 i)) 5 = pcb ((idIndex 13 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_14 : ∀ i : Fin 32, cntW (row (idIndex 14 i)) 0 = pcb ((idIndex 14 i).val &&& 63) ∧ cntW (row (idIndex 14 i)) 1 = pcb ((idIndex 14 i).val &&& 126) ∧ cntW (row (idIndex 14 i)) 2 = pcb ((idIndex 14 i).val &&& 252) ∧ cntW (row (idIndex 14 i)) 3 = pcb ((idIndex 14 i).val &&& 504) ∧ cntW (row (idIndex 14 i)) 4 = pcb ((idIndex 14 i).val &&& 1008) ∧ cntW (row (idIndex 14 i)) 5 = pcb ((idIndex 14 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_15 : ∀ i : Fin 32, cntW (row (idIndex 15 i)) 0 = pcb ((idIndex 15 i).val &&& 63) ∧ cntW (row (idIndex 15 i)) 1 = pcb ((idIndex 15 i).val &&& 126) ∧ cntW (row (idIndex 15 i)) 2 = pcb ((idIndex 15 i).val &&& 252) ∧ cntW (row (idIndex 15 i)) 3 = pcb ((idIndex 15 i).val &&& 504) ∧ cntW (row (idIndex 15 i)) 4 = pcb ((idIndex 15 i).val &&& 1008) ∧ cntW (row (idIndex 15 i)) 5 = pcb ((idIndex 15 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_16 : ∀ i : Fin 32, cntW (row (idIndex 16 i)) 0 = pcb ((idIndex 16 i).val &&& 63) ∧ cntW (row (idIndex 16 i)) 1 = pcb ((idIndex 16 i).val &&& 126) ∧ cntW (row (idIndex 16 i)) 2 = pcb ((idIndex 16 i).val &&& 252) ∧ cntW (row (idIndex 16 i)) 3 = pcb ((idIndex 16 i).val &&& 504) ∧ cntW (row (idIndex 16 i)) 4 = pcb ((idIndex 16 i).val &&& 1008) ∧ cntW (row (idIndex 16 i)) 5 = pcb ((idIndex 16 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_17 : ∀ i : Fin 32, cntW (row (idIndex 17 i)) 0 = pcb ((idIndex 17 i).val &&& 63) ∧ cntW (row (idIndex 17 i)) 1 = pcb ((idIndex 17 i).val &&& 126) ∧ cntW (row (idIndex 17 i)) 2 = pcb ((idIndex 17 i).val &&& 252) ∧ cntW (row (idIndex 17 i)) 3 = pcb ((idIndex 17 i).val &&& 504) ∧ cntW (row (idIndex 17 i)) 4 = pcb ((idIndex 17 i).val &&& 1008) ∧ cntW (row (idIndex 17 i)) 5 = pcb ((idIndex 17 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_18 : ∀ i : Fin 32, cntW (row (idIndex 18 i)) 0 = pcb ((idIndex 18 i).val &&& 63) ∧ cntW (row (idIndex 18 i)) 1 = pcb ((idIndex 18 i).val &&& 126) ∧ cntW (row (idIndex 18 i)) 2 = pcb ((idIndex 18 i).val &&& 252) ∧ cntW (row (idIndex 18 i)) 3 = pcb ((idIndex 18 i).val &&& 504) ∧ cntW (row (idIndex 18 i)) 4 = pcb ((idIndex 18 i).val &&& 1008) ∧ cntW (row (idIndex 18 i)) 5 = pcb ((idIndex 18 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_19 : ∀ i : Fin 32, cntW (row (idIndex 19 i)) 0 = pcb ((idIndex 19 i).val &&& 63) ∧ cntW (row (idIndex 19 i)) 1 = pcb ((idIndex 19 i).val &&& 126) ∧ cntW (row (idIndex 19 i)) 2 = pcb ((idIndex 19 i).val &&& 252) ∧ cntW (row (idIndex 19 i)) 3 = pcb ((idIndex 19 i).val &&& 504) ∧ cntW (row (idIndex 19 i)) 4 = pcb ((idIndex 19 i).val &&& 1008) ∧ cntW (row (idIndex 19 i)) 5 = pcb ((idIndex 19 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_20 : ∀ i : Fin 32, cntW (row (idIndex 20 i)) 0 = pcb ((idIndex 20 i).val &&& 63) ∧ cntW (row (idIndex 20 i)) 1 = pcb ((idIndex 20 i).val &&& 126) ∧ cntW (row (idIndex 20 i)) 2 = pcb ((idIndex 20 i).val &&& 252) ∧ cntW (row (idIndex 20 i)) 3 = pcb ((idIndex 20 i).val &&& 504) ∧ cntW (row (idIndex 20 i)) 4 = pcb ((idIndex 20 i).val &&& 1008) ∧ cntW (row (idIndex 20 i)) 5 = pcb ((idIndex 20 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_21 : ∀ i : Fin 32, cntW (row (idIndex 21 i)) 0 = pcb ((idIndex 21 i).val &&& 63) ∧ cntW (row (idIndex 21 i)) 1 = pcb ((idIndex 21 i).val &&& 126) ∧ cntW (row (idIndex 21 i)) 2 = pcb ((idIndex 21 i).val &&& 252) ∧ cntW (row (idIndex 21 i)) 3 = pcb ((idIndex 21 i).val &&& 504) ∧ cntW (row (idIndex 21 i)) 4 = pcb ((idIndex 21 i).val &&& 1008) ∧ cntW (row (idIndex 21 i)) 5 = pcb ((idIndex 21 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_22 : ∀ i : Fin 32, cntW (row (idIndex 22 i)) 0 = pcb ((idIndex 22 i).val &&& 63) ∧ cntW (row (idIndex 22 i)) 1 = pcb ((idIndex 22 i).val &&& 126) ∧ cntW (row (idIndex 22 i)) 2 = pcb ((idIndex 22 i).val &&& 252) ∧ cntW (row (idIndex 22 i)) 3 = pcb ((idIndex 22 i).val &&& 504) ∧ cntW (row (idIndex 22 i)) 4 = pcb ((idIndex 22 i).val &&& 1008) ∧ cntW (row (idIndex 22 i)) 5 = pcb ((idIndex 22 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_23 : ∀ i : Fin 32, cntW (row (idIndex 23 i)) 0 = pcb ((idIndex 23 i).val &&& 63) ∧ cntW (row (idIndex 23 i)) 1 = pcb ((idIndex 23 i).val &&& 126) ∧ cntW (row (idIndex 23 i)) 2 = pcb ((idIndex 23 i).val &&& 252) ∧ cntW (row (idIndex 23 i)) 3 = pcb ((idIndex 23 i).val &&& 504) ∧ cntW (row (idIndex 23 i)) 4 = pcb ((idIndex 23 i).val &&& 1008) ∧ cntW (row (idIndex 23 i)) 5 = pcb ((idIndex 23 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_24 : ∀ i : Fin 32, cntW (row (idIndex 24 i)) 0 = pcb ((idIndex 24 i).val &&& 63) ∧ cntW (row (idIndex 24 i)) 1 = pcb ((idIndex 24 i).val &&& 126) ∧ cntW (row (idIndex 24 i)) 2 = pcb ((idIndex 24 i).val &&& 252) ∧ cntW (row (idIndex 24 i)) 3 = pcb ((idIndex 24 i).val &&& 504) ∧ cntW (row (idIndex 24 i)) 4 = pcb ((idIndex 24 i).val &&& 1008) ∧ cntW (row (idIndex 24 i)) 5 = pcb ((idIndex 24 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_25 : ∀ i : Fin 32, cntW (row (idIndex 25 i)) 0 = pcb ((idIndex 25 i).val &&& 63) ∧ cntW (row (idIndex 25 i)) 1 = pcb ((idIndex 25 i).val &&& 126) ∧ cntW (row (idIndex 25 i)) 2 = pcb ((idIndex 25 i).val &&& 252) ∧ cntW (row (idIndex 25 i)) 3 = pcb ((idIndex 25 i).val &&& 504) ∧ cntW (row (idIndex 25 i)) 4 = pcb ((idIndex 25 i).val &&& 1008) ∧ cntW (row (idIndex 25 i)) 5 = pcb ((idIndex 25 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_26 : ∀ i : Fin 32, cntW (row (idIndex 26 i)) 0 = pcb ((idIndex 26 i).val &&& 63) ∧ cntW (row (idIndex 26 i)) 1 = pcb ((idIndex 26 i).val &&& 126) ∧ cntW (row (idIndex 26 i)) 2 = pcb ((idIndex 26 i).val &&& 252) ∧ cntW (row (idIndex 26 i)) 3 = pcb ((idIndex 26 i).val &&& 504) ∧ cntW (row (idIndex 26 i)) 4 = pcb ((idIndex 26 i).val &&& 1008) ∧ cntW (row (idIndex 26 i)) 5 = pcb ((idIndex 26 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_27 : ∀ i : Fin 32, cntW (row (idIndex 27 i)) 0 = pcb ((idIndex 27 i).val &&& 63) ∧ cntW (row (idIndex 27 i)) 1 = pcb ((idIndex 27 i).val &&& 126) ∧ cntW (row (idIndex 27 i)) 2 = pcb ((idIndex 27 i).val &&& 252) ∧ cntW (row (idIndex 27 i)) 3 = pcb ((idIndex 27 i).val &&& 504) ∧ cntW (row (idIndex 27 i)) 4 = pcb ((idIndex 27 i).val &&& 1008) ∧ cntW (row (idIndex 27 i)) 5 = pcb ((idIndex 27 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_28 : ∀ i : Fin 32, cntW (row (idIndex 28 i)) 0 = pcb ((idIndex 28 i).val &&& 63) ∧ cntW (row (idIndex 28 i)) 1 = pcb ((idIndex 28 i).val &&& 126) ∧ cntW (row (idIndex 28 i)) 2 = pcb ((idIndex 28 i).val &&& 252) ∧ cntW (row (idIndex 28 i)) 3 = pcb ((idIndex 28 i).val &&& 504) ∧ cntW (row (idIndex 28 i)) 4 = pcb ((idIndex 28 i).val &&& 1008) ∧ cntW (row (idIndex 28 i)) 5 = pcb ((idIndex 28 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_29 : ∀ i : Fin 32, cntW (row (idIndex 29 i)) 0 = pcb ((idIndex 29 i).val &&& 63) ∧ cntW (row (idIndex 29 i)) 1 = pcb ((idIndex 29 i).val &&& 126) ∧ cntW (row (idIndex 29 i)) 2 = pcb ((idIndex 29 i).val &&& 252) ∧ cntW (row (idIndex 29 i)) 3 = pcb ((idIndex 29 i).val &&& 504) ∧ cntW (row (idIndex 29 i)) 4 = pcb ((idIndex 29 i).val &&& 1008) ∧ cntW (row (idIndex 29 i)) 5 = pcb ((idIndex 29 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_30 : ∀ i : Fin 32, cntW (row (idIndex 30 i)) 0 = pcb ((idIndex 30 i).val &&& 63) ∧ cntW (row (idIndex 30 i)) 1 = pcb ((idIndex 30 i).val &&& 126) ∧ cntW (row (idIndex 30 i)) 2 = pcb ((idIndex 30 i).val &&& 252) ∧ cntW (row (idIndex 30 i)) 3 = pcb ((idIndex 30 i).val &&& 504) ∧ cntW (row (idIndex 30 i)) 4 = pcb ((idIndex 30 i).val &&& 1008) ∧ cntW (row (idIndex 30 i)) 5 = pcb ((idIndex 30 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_31 : ∀ i : Fin 32, cntW (row (idIndex 31 i)) 0 = pcb ((idIndex 31 i).val &&& 63) ∧ cntW (row (idIndex 31 i)) 1 = pcb ((idIndex 31 i).val &&& 126) ∧ cntW (row (idIndex 31 i)) 2 = pcb ((idIndex 31 i).val &&& 252) ∧ cntW (row (idIndex 31 i)) 3 = pcb ((idIndex 31 i).val &&& 504) ∧ cntW (row (idIndex 31 i)) 4 = pcb ((idIndex 31 i).val &&& 1008) ∧ cntW (row (idIndex 31 i)) 5 = pcb ((idIndex 31 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_32 : ∀ i : Fin 32, cntW (row (idIndex 32 i)) 0 = pcb ((idIndex 32 i).val &&& 63) ∧ cntW (row (idIndex 32 i)) 1 = pcb ((idIndex 32 i).val &&& 126) ∧ cntW (row (idIndex 32 i)) 2 = pcb ((idIndex 32 i).val &&& 252) ∧ cntW (row (idIndex 32 i)) 3 = pcb ((idIndex 32 i).val &&& 504) ∧ cntW (row (idIndex 32 i)) 4 = pcb ((idIndex 32 i).val &&& 1008) ∧ cntW (row (idIndex 32 i)) 5 = pcb ((idIndex 32 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_33 : ∀ i : Fin 32, cntW (row (idIndex 33 i)) 0 = pcb ((idIndex 33 i).val &&& 63) ∧ cntW (row (idIndex 33 i)) 1 = pcb ((idIndex 33 i).val &&& 126) ∧ cntW (row (idIndex 33 i)) 2 = pcb ((idIndex 33 i).val &&& 252) ∧ cntW (row (idIndex 33 i)) 3 = pcb ((idIndex 33 i).val &&& 504) ∧ cntW (row (idIndex 33 i)) 4 = pcb ((idIndex 33 i).val &&& 1008) ∧ cntW (row (idIndex 33 i)) 5 = pcb ((idIndex 33 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_34 : ∀ i : Fin 32, cntW (row (idIndex 34 i)) 0 = pcb ((idIndex 34 i).val &&& 63) ∧ cntW (row (idIndex 34 i)) 1 = pcb ((idIndex 34 i).val &&& 126) ∧ cntW (row (idIndex 34 i)) 2 = pcb ((idIndex 34 i).val &&& 252) ∧ cntW (row (idIndex 34 i)) 3 = pcb ((idIndex 34 i).val &&& 504) ∧ cntW (row (idIndex 34 i)) 4 = pcb ((idIndex 34 i).val &&& 1008) ∧ cntW (row (idIndex 34 i)) 5 = pcb ((idIndex 34 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_35 : ∀ i : Fin 32, cntW (row (idIndex 35 i)) 0 = pcb ((idIndex 35 i).val &&& 63) ∧ cntW (row (idIndex 35 i)) 1 = pcb ((idIndex 35 i).val &&& 126) ∧ cntW (row (idIndex 35 i)) 2 = pcb ((idIndex 35 i).val &&& 252) ∧ cntW (row (idIndex 35 i)) 3 = pcb ((idIndex 35 i).val &&& 504) ∧ cntW (row (idIndex 35 i)) 4 = pcb ((idIndex 35 i).val &&& 1008) ∧ cntW (row (idIndex 35 i)) 5 = pcb ((idIndex 35 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_36 : ∀ i : Fin 32, cntW (row (idIndex 36 i)) 0 = pcb ((idIndex 36 i).val &&& 63) ∧ cntW (row (idIndex 36 i)) 1 = pcb ((idIndex 36 i).val &&& 126) ∧ cntW (row (idIndex 36 i)) 2 = pcb ((idIndex 36 i).val &&& 252) ∧ cntW (row (idIndex 36 i)) 3 = pcb ((idIndex 36 i).val &&& 504) ∧ cntW (row (idIndex 36 i)) 4 = pcb ((idIndex 36 i).val &&& 1008) ∧ cntW (row (idIndex 36 i)) 5 = pcb ((idIndex 36 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_37 : ∀ i : Fin 32, cntW (row (idIndex 37 i)) 0 = pcb ((idIndex 37 i).val &&& 63) ∧ cntW (row (idIndex 37 i)) 1 = pcb ((idIndex 37 i).val &&& 126) ∧ cntW (row (idIndex 37 i)) 2 = pcb ((idIndex 37 i).val &&& 252) ∧ cntW (row (idIndex 37 i)) 3 = pcb ((idIndex 37 i).val &&& 504) ∧ cntW (row (idIndex 37 i)) 4 = pcb ((idIndex 37 i).val &&& 1008) ∧ cntW (row (idIndex 37 i)) 5 = pcb ((idIndex 37 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_38 : ∀ i : Fin 32, cntW (row (idIndex 38 i)) 0 = pcb ((idIndex 38 i).val &&& 63) ∧ cntW (row (idIndex 38 i)) 1 = pcb ((idIndex 38 i).val &&& 126) ∧ cntW (row (idIndex 38 i)) 2 = pcb ((idIndex 38 i).val &&& 252) ∧ cntW (row (idIndex 38 i)) 3 = pcb ((idIndex 38 i).val &&& 504) ∧ cntW (row (idIndex 38 i)) 4 = pcb ((idIndex 38 i).val &&& 1008) ∧ cntW (row (idIndex 38 i)) 5 = pcb ((idIndex 38 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_39 : ∀ i : Fin 32, cntW (row (idIndex 39 i)) 0 = pcb ((idIndex 39 i).val &&& 63) ∧ cntW (row (idIndex 39 i)) 1 = pcb ((idIndex 39 i).val &&& 126) ∧ cntW (row (idIndex 39 i)) 2 = pcb ((idIndex 39 i).val &&& 252) ∧ cntW (row (idIndex 39 i)) 3 = pcb ((idIndex 39 i).val &&& 504) ∧ cntW (row (idIndex 39 i)) 4 = pcb ((idIndex 39 i).val &&& 1008) ∧ cntW (row (idIndex 39 i)) 5 = pcb ((idIndex 39 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_40 : ∀ i : Fin 32, cntW (row (idIndex 40 i)) 0 = pcb ((idIndex 40 i).val &&& 63) ∧ cntW (row (idIndex 40 i)) 1 = pcb ((idIndex 40 i).val &&& 126) ∧ cntW (row (idIndex 40 i)) 2 = pcb ((idIndex 40 i).val &&& 252) ∧ cntW (row (idIndex 40 i)) 3 = pcb ((idIndex 40 i).val &&& 504) ∧ cntW (row (idIndex 40 i)) 4 = pcb ((idIndex 40 i).val &&& 1008) ∧ cntW (row (idIndex 40 i)) 5 = pcb ((idIndex 40 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_41 : ∀ i : Fin 32, cntW (row (idIndex 41 i)) 0 = pcb ((idIndex 41 i).val &&& 63) ∧ cntW (row (idIndex 41 i)) 1 = pcb ((idIndex 41 i).val &&& 126) ∧ cntW (row (idIndex 41 i)) 2 = pcb ((idIndex 41 i).val &&& 252) ∧ cntW (row (idIndex 41 i)) 3 = pcb ((idIndex 41 i).val &&& 504) ∧ cntW (row (idIndex 41 i)) 4 = pcb ((idIndex 41 i).val &&& 1008) ∧ cntW (row (idIndex 41 i)) 5 = pcb ((idIndex 41 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_42 : ∀ i : Fin 32, cntW (row (idIndex 42 i)) 0 = pcb ((idIndex 42 i).val &&& 63) ∧ cntW (row (idIndex 42 i)) 1 = pcb ((idIndex 42 i).val &&& 126) ∧ cntW (row (idIndex 42 i)) 2 = pcb ((idIndex 42 i).val &&& 252) ∧ cntW (row (idIndex 42 i)) 3 = pcb ((idIndex 42 i).val &&& 504) ∧ cntW (row (idIndex 42 i)) 4 = pcb ((idIndex 42 i).val &&& 1008) ∧ cntW (row (idIndex 42 i)) 5 = pcb ((idIndex 42 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_43 : ∀ i : Fin 32, cntW (row (idIndex 43 i)) 0 = pcb ((idIndex 43 i).val &&& 63) ∧ cntW (row (idIndex 43 i)) 1 = pcb ((idIndex 43 i).val &&& 126) ∧ cntW (row (idIndex 43 i)) 2 = pcb ((idIndex 43 i).val &&& 252) ∧ cntW (row (idIndex 43 i)) 3 = pcb ((idIndex 43 i).val &&& 504) ∧ cntW (row (idIndex 43 i)) 4 = pcb ((idIndex 43 i).val &&& 1008) ∧ cntW (row (idIndex 43 i)) 5 = pcb ((idIndex 43 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_44 : ∀ i : Fin 32, cntW (row (idIndex 44 i)) 0 = pcb ((idIndex 44 i).val &&& 63) ∧ cntW (row (idIndex 44 i)) 1 = pcb ((idIndex 44 i).val &&& 126) ∧ cntW (row (idIndex 44 i)) 2 = pcb ((idIndex 44 i).val &&& 252) ∧ cntW (row (idIndex 44 i)) 3 = pcb ((idIndex 44 i).val &&& 504) ∧ cntW (row (idIndex 44 i)) 4 = pcb ((idIndex 44 i).val &&& 1008) ∧ cntW (row (idIndex 44 i)) 5 = pcb ((idIndex 44 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_45 : ∀ i : Fin 32, cntW (row (idIndex 45 i)) 0 = pcb ((idIndex 45 i).val &&& 63) ∧ cntW (row (idIndex 45 i)) 1 = pcb ((idIndex 45 i).val &&& 126) ∧ cntW (row (idIndex 45 i)) 2 = pcb ((idIndex 45 i).val &&& 252) ∧ cntW (row (idIndex 45 i)) 3 = pcb ((idIndex 45 i).val &&& 504) ∧ cntW (row (idIndex 45 i)) 4 = pcb ((idIndex 45 i).val &&& 1008) ∧ cntW (row (idIndex 45 i)) 5 = pcb ((idIndex 45 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_46 : ∀ i : Fin 32, cntW (row (idIndex 46 i)) 0 = pcb ((idIndex 46 i).val &&& 63) ∧ cntW (row (idIndex 46 i)) 1 = pcb ((idIndex 46 i).val &&& 126) ∧ cntW (row (idIndex 46 i)) 2 = pcb ((idIndex 46 i).val &&& 252) ∧ cntW (row (idIndex 46 i)) 3 = pcb ((idIndex 46 i).val &&& 504) ∧ cntW (row (idIndex 46 i)) 4 = pcb ((idIndex 46 i).val &&& 1008) ∧ cntW (row (idIndex 46 i)) 5 = pcb ((idIndex 46 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_47 : ∀ i : Fin 32, cntW (row (idIndex 47 i)) 0 = pcb ((idIndex 47 i).val &&& 63) ∧ cntW (row (idIndex 47 i)) 1 = pcb ((idIndex 47 i).val &&& 126) ∧ cntW (row (idIndex 47 i)) 2 = pcb ((idIndex 47 i).val &&& 252) ∧ cntW (row (idIndex 47 i)) 3 = pcb ((idIndex 47 i).val &&& 504) ∧ cntW (row (idIndex 47 i)) 4 = pcb ((idIndex 47 i).val &&& 1008) ∧ cntW (row (idIndex 47 i)) 5 = pcb ((idIndex 47 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_48 : ∀ i : Fin 32, cntW (row (idIndex 48 i)) 0 = pcb ((idIndex 48 i).val &&& 63) ∧ cntW (row (idIndex 48 i)) 1 = pcb ((idIndex 48 i).val &&& 126) ∧ cntW (row (idIndex 48 i)) 2 = pcb ((idIndex 48 i).val &&& 252) ∧ cntW (row (idIndex 48 i)) 3 = pcb ((idIndex 48 i).val &&& 504) ∧ cntW (row (idIndex 48 i)) 4 = pcb ((idIndex 48 i).val &&& 1008) ∧ cntW (row (idIndex 48 i)) 5 = pcb ((idIndex 48 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_49 : ∀ i : Fin 32, cntW (row (idIndex 49 i)) 0 = pcb ((idIndex 49 i).val &&& 63) ∧ cntW (row (idIndex 49 i)) 1 = pcb ((idIndex 49 i).val &&& 126) ∧ cntW (row (idIndex 49 i)) 2 = pcb ((idIndex 49 i).val &&& 252) ∧ cntW (row (idIndex 49 i)) 3 = pcb ((idIndex 49 i).val &&& 504) ∧ cntW (row (idIndex 49 i)) 4 = pcb ((idIndex 49 i).val &&& 1008) ∧ cntW (row (idIndex 49 i)) 5 = pcb ((idIndex 49 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_50 : ∀ i : Fin 32, cntW (row (idIndex 50 i)) 0 = pcb ((idIndex 50 i).val &&& 63) ∧ cntW (row (idIndex 50 i)) 1 = pcb ((idIndex 50 i).val &&& 126) ∧ cntW (row (idIndex 50 i)) 2 = pcb ((idIndex 50 i).val &&& 252) ∧ cntW (row (idIndex 50 i)) 3 = pcb ((idIndex 50 i).val &&& 504) ∧ cntW (row (idIndex 50 i)) 4 = pcb ((idIndex 50 i).val &&& 1008) ∧ cntW (row (idIndex 50 i)) 5 = pcb ((idIndex 50 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_51 : ∀ i : Fin 32, cntW (row (idIndex 51 i)) 0 = pcb ((idIndex 51 i).val &&& 63) ∧ cntW (row (idIndex 51 i)) 1 = pcb ((idIndex 51 i).val &&& 126) ∧ cntW (row (idIndex 51 i)) 2 = pcb ((idIndex 51 i).val &&& 252) ∧ cntW (row (idIndex 51 i)) 3 = pcb ((idIndex 51 i).val &&& 504) ∧ cntW (row (idIndex 51 i)) 4 = pcb ((idIndex 51 i).val &&& 1008) ∧ cntW (row (idIndex 51 i)) 5 = pcb ((idIndex 51 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_52 : ∀ i : Fin 32, cntW (row (idIndex 52 i)) 0 = pcb ((idIndex 52 i).val &&& 63) ∧ cntW (row (idIndex 52 i)) 1 = pcb ((idIndex 52 i).val &&& 126) ∧ cntW (row (idIndex 52 i)) 2 = pcb ((idIndex 52 i).val &&& 252) ∧ cntW (row (idIndex 52 i)) 3 = pcb ((idIndex 52 i).val &&& 504) ∧ cntW (row (idIndex 52 i)) 4 = pcb ((idIndex 52 i).val &&& 1008) ∧ cntW (row (idIndex 52 i)) 5 = pcb ((idIndex 52 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_53 : ∀ i : Fin 32, cntW (row (idIndex 53 i)) 0 = pcb ((idIndex 53 i).val &&& 63) ∧ cntW (row (idIndex 53 i)) 1 = pcb ((idIndex 53 i).val &&& 126) ∧ cntW (row (idIndex 53 i)) 2 = pcb ((idIndex 53 i).val &&& 252) ∧ cntW (row (idIndex 53 i)) 3 = pcb ((idIndex 53 i).val &&& 504) ∧ cntW (row (idIndex 53 i)) 4 = pcb ((idIndex 53 i).val &&& 1008) ∧ cntW (row (idIndex 53 i)) 5 = pcb ((idIndex 53 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_54 : ∀ i : Fin 32, cntW (row (idIndex 54 i)) 0 = pcb ((idIndex 54 i).val &&& 63) ∧ cntW (row (idIndex 54 i)) 1 = pcb ((idIndex 54 i).val &&& 126) ∧ cntW (row (idIndex 54 i)) 2 = pcb ((idIndex 54 i).val &&& 252) ∧ cntW (row (idIndex 54 i)) 3 = pcb ((idIndex 54 i).val &&& 504) ∧ cntW (row (idIndex 54 i)) 4 = pcb ((idIndex 54 i).val &&& 1008) ∧ cntW (row (idIndex 54 i)) 5 = pcb ((idIndex 54 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_55 : ∀ i : Fin 32, cntW (row (idIndex 55 i)) 0 = pcb ((idIndex 55 i).val &&& 63) ∧ cntW (row (idIndex 55 i)) 1 = pcb ((idIndex 55 i).val &&& 126) ∧ cntW (row (idIndex 55 i)) 2 = pcb ((idIndex 55 i).val &&& 252) ∧ cntW (row (idIndex 55 i)) 3 = pcb ((idIndex 55 i).val &&& 504) ∧ cntW (row (idIndex 55 i)) 4 = pcb ((idIndex 55 i).val &&& 1008) ∧ cntW (row (idIndex 55 i)) 5 = pcb ((idIndex 55 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_56 : ∀ i : Fin 32, cntW (row (idIndex 56 i)) 0 = pcb ((idIndex 56 i).val &&& 63) ∧ cntW (row (idIndex 56 i)) 1 = pcb ((idIndex 56 i).val &&& 126) ∧ cntW (row (idIndex 56 i)) 2 = pcb ((idIndex 56 i).val &&& 252) ∧ cntW (row (idIndex 56 i)) 3 = pcb ((idIndex 56 i).val &&& 504) ∧ cntW (row (idIndex 56 i)) 4 = pcb ((idIndex 56 i).val &&& 1008) ∧ cntW (row (idIndex 56 i)) 5 = pcb ((idIndex 56 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_57 : ∀ i : Fin 32, cntW (row (idIndex 57 i)) 0 = pcb ((idIndex 57 i).val &&& 63) ∧ cntW (row (idIndex 57 i)) 1 = pcb ((idIndex 57 i).val &&& 126) ∧ cntW (row (idIndex 57 i)) 2 = pcb ((idIndex 57 i).val &&& 252) ∧ cntW (row (idIndex 57 i)) 3 = pcb ((idIndex 57 i).val &&& 504) ∧ cntW (row (idIndex 57 i)) 4 = pcb ((idIndex 57 i).val &&& 1008) ∧ cntW (row (idIndex 57 i)) 5 = pcb ((idIndex 57 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_58 : ∀ i : Fin 32, cntW (row (idIndex 58 i)) 0 = pcb ((idIndex 58 i).val &&& 63) ∧ cntW (row (idIndex 58 i)) 1 = pcb ((idIndex 58 i).val &&& 126) ∧ cntW (row (idIndex 58 i)) 2 = pcb ((idIndex 58 i).val &&& 252) ∧ cntW (row (idIndex 58 i)) 3 = pcb ((idIndex 58 i).val &&& 504) ∧ cntW (row (idIndex 58 i)) 4 = pcb ((idIndex 58 i).val &&& 1008) ∧ cntW (row (idIndex 58 i)) 5 = pcb ((idIndex 58 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_59 : ∀ i : Fin 32, cntW (row (idIndex 59 i)) 0 = pcb ((idIndex 59 i).val &&& 63) ∧ cntW (row (idIndex 59 i)) 1 = pcb ((idIndex 59 i).val &&& 126) ∧ cntW (row (idIndex 59 i)) 2 = pcb ((idIndex 59 i).val &&& 252) ∧ cntW (row (idIndex 59 i)) 3 = pcb ((idIndex 59 i).val &&& 504) ∧ cntW (row (idIndex 59 i)) 4 = pcb ((idIndex 59 i).val &&& 1008) ∧ cntW (row (idIndex 59 i)) 5 = pcb ((idIndex 59 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_60 : ∀ i : Fin 32, cntW (row (idIndex 60 i)) 0 = pcb ((idIndex 60 i).val &&& 63) ∧ cntW (row (idIndex 60 i)) 1 = pcb ((idIndex 60 i).val &&& 126) ∧ cntW (row (idIndex 60 i)) 2 = pcb ((idIndex 60 i).val &&& 252) ∧ cntW (row (idIndex 60 i)) 3 = pcb ((idIndex 60 i).val &&& 504) ∧ cntW (row (idIndex 60 i)) 4 = pcb ((idIndex 60 i).val &&& 1008) ∧ cntW (row (idIndex 60 i)) 5 = pcb ((idIndex 60 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_61 : ∀ i : Fin 32, cntW (row (idIndex 61 i)) 0 = pcb ((idIndex 61 i).val &&& 63) ∧ cntW (row (idIndex 61 i)) 1 = pcb ((idIndex 61 i).val &&& 126) ∧ cntW (row (idIndex 61 i)) 2 = pcb ((idIndex 61 i).val &&& 252) ∧ cntW (row (idIndex 61 i)) 3 = pcb ((idIndex 61 i).val &&& 504) ∧ cntW (row (idIndex 61 i)) 4 = pcb ((idIndex 61 i).val &&& 1008) ∧ cntW (row (idIndex 61 i)) 5 = pcb ((idIndex 61 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_62 : ∀ i : Fin 32, cntW (row (idIndex 62 i)) 0 = pcb ((idIndex 62 i).val &&& 63) ∧ cntW (row (idIndex 62 i)) 1 = pcb ((idIndex 62 i).val &&& 126) ∧ cntW (row (idIndex 62 i)) 2 = pcb ((idIndex 62 i).val &&& 252) ∧ cntW (row (idIndex 62 i)) 3 = pcb ((idIndex 62 i).val &&& 504) ∧ cntW (row (idIndex 62 i)) 4 = pcb ((idIndex 62 i).val &&& 1008) ∧ cntW (row (idIndex 62 i)) 5 = pcb ((idIndex 62 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_63 : ∀ i : Fin 32, cntW (row (idIndex 63 i)) 0 = pcb ((idIndex 63 i).val &&& 63) ∧ cntW (row (idIndex 63 i)) 1 = pcb ((idIndex 63 i).val &&& 126) ∧ cntW (row (idIndex 63 i)) 2 = pcb ((idIndex 63 i).val &&& 252) ∧ cntW (row (idIndex 63 i)) 3 = pcb ((idIndex 63 i).val &&& 504) ∧ cntW (row (idIndex 63 i)) 4 = pcb ((idIndex 63 i).val &&& 1008) ∧ cntW (row (idIndex 63 i)) 5 = pcb ((idIndex 63 i).val &&& 2016) := by
  decide +kernel

theorem cnt_row (u : Fin 2048) : cntW (row u) 0 = pcb (u.val &&& 63) ∧ cntW (row u) 1 = pcb (u.val &&& 126) ∧ cntW (row u) 2 = pcb (u.val &&& 252) ∧ cntW (row u) 3 = pcb (u.val &&& 504) ∧ cntW (row u) 4 = pcb (u.val &&& 1008) ∧ cntW (row u) 5 = pcb (u.val &&& 2016) := by
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, cntW (row (idIndex k i)) 0 = pcb ((idIndex k i).val &&& 63) ∧ cntW (row (idIndex k i)) 1 = pcb ((idIndex k i).val &&& 126) ∧ cntW (row (idIndex k i)) 2 = pcb ((idIndex k i).val &&& 252) ∧ cntW (row (idIndex k i)) 3 = pcb ((idIndex k i).val &&& 504) ∧ cntW (row (idIndex k i)) 4 = pcb ((idIndex k i).val &&& 1008) ∧ cntW (row (idIndex k i)) 5 = pcb ((idIndex k i).val &&& 2016) := by
    intro k
    fin_cases k
    · exact cnt_row_chunk_0
    · exact cnt_row_chunk_1
    · exact cnt_row_chunk_2
    · exact cnt_row_chunk_3
    · exact cnt_row_chunk_4
    · exact cnt_row_chunk_5
    · exact cnt_row_chunk_6
    · exact cnt_row_chunk_7
    · exact cnt_row_chunk_8
    · exact cnt_row_chunk_9
    · exact cnt_row_chunk_10
    · exact cnt_row_chunk_11
    · exact cnt_row_chunk_12
    · exact cnt_row_chunk_13
    · exact cnt_row_chunk_14
    · exact cnt_row_chunk_15
    · exact cnt_row_chunk_16
    · exact cnt_row_chunk_17
    · exact cnt_row_chunk_18
    · exact cnt_row_chunk_19
    · exact cnt_row_chunk_20
    · exact cnt_row_chunk_21
    · exact cnt_row_chunk_22
    · exact cnt_row_chunk_23
    · exact cnt_row_chunk_24
    · exact cnt_row_chunk_25
    · exact cnt_row_chunk_26
    · exact cnt_row_chunk_27
    · exact cnt_row_chunk_28
    · exact cnt_row_chunk_29
    · exact cnt_row_chunk_30
    · exact cnt_row_chunk_31
    · exact cnt_row_chunk_32
    · exact cnt_row_chunk_33
    · exact cnt_row_chunk_34
    · exact cnt_row_chunk_35
    · exact cnt_row_chunk_36
    · exact cnt_row_chunk_37
    · exact cnt_row_chunk_38
    · exact cnt_row_chunk_39
    · exact cnt_row_chunk_40
    · exact cnt_row_chunk_41
    · exact cnt_row_chunk_42
    · exact cnt_row_chunk_43
    · exact cnt_row_chunk_44
    · exact cnt_row_chunk_45
    · exact cnt_row_chunk_46
    · exact cnt_row_chunk_47
    · exact cnt_row_chunk_48
    · exact cnt_row_chunk_49
    · exact cnt_row_chunk_50
    · exact cnt_row_chunk_51
    · exact cnt_row_chunk_52
    · exact cnt_row_chunk_53
    · exact cnt_row_chunk_54
    · exact cnt_row_chunk_55
    · exact cnt_row_chunk_56
    · exact cnt_row_chunk_57
    · exact cnt_row_chunk_58
    · exact cnt_row_chunk_59
    · exact cnt_row_chunk_60
    · exact cnt_row_chunk_61
    · exact cnt_row_chunk_62
    · exact cnt_row_chunk_63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

/-- Compatibility on bit codes, enforcing all six windows. -/
def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 63) ≤ 1 ∧ 3 ≤ pcb (t &&& 63)) ∧
    ¬ (pcb (s &&& 126) ≤ 1 ∧ 3 ≤ pcb (t &&& 126)) ∧
    ¬ (pcb (s &&& 252) ≤ 1 ∧ 3 ≤ pcb (t &&& 252)) ∧
    ¬ (pcb (s &&& 504) ≤ 1 ∧ 3 ≤ pcb (t &&& 504)) ∧
    ¬ (pcb (s &&& 1008) ≤ 1 ∧ 3 ≤ pcb (t &&& 1008)) ∧
    ¬ (pcb (s &&& 2016) ≤ 1 ∧ 3 ≤ pcb (t &&& 2016)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (6 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 2048) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5]

theorem sub_iff (w u : Fin 2048) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 11
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (2048 : ℕ) ≤ 2 ^ i := by
          calc (2048 : ℕ) = 2 ^ 11 := by norm_num
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
def subs (u : Fin 2048) : Finset (Fin 2048) :=
  univ.filter (fun w : Fin 2048 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 2048 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 2048, M n (row u) = G n u := by
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

theorem row_full : ∀ p, row 2047 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 2047 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 11 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 2047 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 2047)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 2047 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 2047 := by
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

theorem G_succ (n : ℕ) (u : Fin 2048) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 := rfl

/-- Packed state vectors, certified by the chain recursion, with the per-table entry width in the low six bits. -/
def tb (T w : ℕ) : ℕ := (T >>> (6 + (T % 64) * w)) % 2 ^ (T % 64)

def tabT : ℕ → ℕ
  | 0 => 0x45C5DFC00000000000000000000000000000000000000000000000000000000005C5DFC000000000000000000000000001C1DFC00000000000C0CFC0004045C045C5DFC0000000000000000000000000000000000000000000000000000000000005DFC00000000000000000000000000001DFC0000000000000CFC0000045C045C5DFC000000000000000000000000000001FC00000000000000FC0000005C005C5DFC000000000000003C0000001C001C1DFC0000000C000C0CFC0004045C045C5DFC1
  | 1 => 0x1EA5194630D4630CC318D4630CC318CC318C6330D4630CC318CC318C6330CC318C6330C6330D8630D4A318C618CC618C6318CC618C6318C6318CA630CC618C6318C6318CA630C6318CA630D2C6198630D46518C330CC330C6118CC330C6118C6118C6330CC330C6118C6118C6330C6118C6330CA56198630CC63186318C6318C6318C6318C6318CA5298A630C6318C6318CA5298A630D294B12C6192C6198630D4630D4630CC3184C318CC3184C318C610846330CC3184C318C610846330C610846330C6330D8630CC618CC618C630846318C630846318C6318CA630C630846318C6318CA630CA52952C6192C6198630CC330CC330C611846118C611846118C6118C6330C611846118C6118C6330CA1294A5618A56198630C6318C6318C6318C6318CA5294A5298A5298A630D8C6318C6418C641908218C6419082190822084114630CC31854630CC318CC318461084C318C6330CC318461084C318C6330C61084211046330D8630CC618C63084C618C6318C63084210846318CA630C63084210846318CA630C6318CA630D2C6198630CC330C61184C330C6118C61184200846118C6330C61184200846118C6330C6118C6330CA56198630C6318C210846318C6318C6318C6318CA5298A630CC6318C63198C641908218C641908219082208410C3184C3184C3184C318C6108061084610846330C6108061084610846330C610846330C6330D8630C6308463084630846318C630846318C6318CA630CC6108C6318C631990820C63199082190822084106118461184611846118C611846118C6118C6330CC2308C2318C2318C6820C2318C6820C682208410C6318C6318C6318C6320C6318C6320C6320C8410C6318C6320C6320C8410C6320C8410C8411042094630CC3184C3184610854630CC318CC318C6330CC3184610846108421104C318C6330C6330D8630CC618C630846308421084C618C6318C6318CA630C630842108421084221046318CA630D2C6198630CC330C611846118420084C330C6118C6118C6330C611842008420084211046118C6330CA56198630C6318C2108421084210846318C6318CA5298A630C6318C6318CA5298A630D8C641908219082208410C3184C31846108061084C3184C318C610846330C61080610842000021104610846330C6330D8630C63084630842100021084630846318C6318CA630C630846318C6318CA630CC631990821908220841061184611842008020084611846118C6118C6330C611846118C6118C6330CC2318C6820C6822084106318C6318C6318C6318CC6318C6320C6320C8410C6318C6320C6320C8410C6320C8410C841104208C318461080C318461084C318461084C318C6330C6108020000610842110461084211046330D8630C6308421000630842108463084210846318CA630C63084210846318CA630C6318CA630D90822084106118420080611842008461184200846118C6330C61184200846118C6330C6118C6330CC6822084106318C210846318C6318C6318C6318CC6320C84106318C6318CC6320C8410C6320C8410C841104208610806108061080610846108061084610846330C6108061084610846330C610846330C6330E084106308463084630846318C630846318C6318CC8410630846318C6318CC84106318CC8410C8411042086118461184611846118C611846118C6118C63410611846118C6118C634106118C6341063411042086318C6318C6318C631906318C6319063190642086318C631906319064208631906420864208821045
  | 2 => 0x270E7D74150C490F033F1B0046D1843611C604BC7581430A6029D20837D1D584EC7AA1540AF82C47EE1620BA82F43020C5094818D0E63451B6849872213C0A1028C76614A0AC02BC2BC0B4088816C7A21550B282D82E60BF09181842FA0C5097819439609904C80CD2084A51C087387421E409E828C7861F80A882BC2A60B405A016C7C42090AE82D82CE0BF05F81842DE0C5062819421409904C80CC7A22020AC82D42BE0BC05E01802CE0C2061019021009904C80CC2DE0C7063819C22409F04F80D432A0F307981441E6051028806D184384252873871615A0F2028C74E1680FC02BC2A607305A016C78617310482D82CA07A05F81842D207C062819418A06504C80CC76616F10102D42BA07805E01802C207A061019018406404C80CC2CE07B063819C18E06704F80D422208C07981441E6051028806C7EE20910484482CA0B705B81802D20BB05D819017606403200CC2DE0BF05F819C17E06703380D420208C0460144118051028806C2FA0C706381B018E06C03600E022209604B015C12C05702B807432A0E1070821C1C208704380B41C208704380B410E02D016803D0F03531C6853C94A1CE0F2028C71614E0B781D43F00AF05A016C7421560BD81E44120B605F81842CA06E041010418A06504C80CC7221520BA81E04040B505E01802BA06C03F00FC18406404C80CC2BE06B040010018E06704F80D418E06704F80D41E6051028806C7AA1F80BE830C41211205B81802CA0B903E00FC17606403200CC2CE0BB03E810017E06703380D417E06703380D4118051028806C2E60C2041010C18E06C03600E018E06C03600E012C05702B807422409604B01341C208704380B41C208704380B410E02D016803C7581710FC030C3F00C308901802A607D05C80FC17203F03200CC2A607C05D810017604003380D417604003380D40CE035028806C2BC081061010C18404303600E018404303600E00D803802B807421005404B013412C04D04380B412C04D04380B410E02D016803C3020C5062819C18A06703380E018A06703380E00CE03801C007421408C046013411804D02680B411804D02680B409A02D016803C3960F3079821C1E608704381441E6087043814410E051028806C1E6087043814410E051028806C10E051028806C0A201B00D802505432F1AB84C871A1500B181B494A1CE0F2028C3F00AF05A016C7021480AE81A02FA07A04101044120B605F818418A06504C80CC6DA1420AA81982EA07803F00FC4040B505E018018406404C80CC2B206903800E0104042031808418E06704F80D41E6051028806C7561E40AE82CC2F60C503E00FC41211205B818017606403200CC2BA0B703680E00FA042021008417E06703380D4118051028806C2CA0BC03800E8100044022008818E06C03600E012C05702B807418E06C03600E012C05702B80741C208704380B410E02D016803C71815F0F202CC2DE08706280FC3F00C3089018017203F03200CC2A207805B80E00F8028021008417604003380D40CE035028806C2B007B05E00E80FC028022008818404303600E00D803802B807418404303600E00D803802B807412C04D04380B410E02D016803C2EA0BF05F8190104042021008818A06703380E00CE03801C007418A06703380E00CE03801C007411804D02680B409A02D016803C25E09F04F815C13E05702B80B41E6087043814410E051028806C1E6087043814410E051028806C10E051028806C0A201B00D80246C01430B181EC3C80B306280FC3C80B306280FC22406003200CC27A06803E008816E038021008416E03802100840CE035028806C28406A03F008817803A022008817803A02200880D803802B807417803A02200880D803802B80740D803802B807410E02D016803C2BE0B4041010817E064021008817E06402100880CE03801C007417E06402100880CE03801C00740CE03801C007409A02D016803C24609903180CC13E05702B80B413E05702B80B410E051028806C13E05702B80B410E051028806C10E051028806C0A201B00D802429807A05A0108168042032008816804203200880C802201C007416804203200880C802201C00740C802201C007407001D016803C22206304C80CC13203302B80B413203302B80B40AE02D028806C13203302B80B40AE02D028806C0AE02D028806C0A201B00D802425209904C814413205102880B413205102880B40A202D016806C13205102880B40A202D016806C0A202D016806C05A01B00D802413205102880B40A202D016806C0A202D016806C05A01B00D80240A202D016806C05A01B00D802405A01B00D8024036009004800CFAE30C19784846A61360A1817870814D0AF81AC2E207603D00F494A1CE0F2028C3F00AF05A016C4120B605F818418A06504C80CC68A1330A1017C2A406903500D42DE07603D80F810204203180844040B505E018018406404C80CC18E06704F80D41E6051028806C6FA1CE0A402A42AC0B303400D42E60C303C00F80F8042021008441211205B818017606403200CC17E06703380D4118051028806C2AA0B503480DC0D603A01D00740F604302180880A8033019804418E06C03600E012C05702B80741C208704380B410E02D016803C6C214D0E702A429C07705980D42D008406180F80FA02802100843F00C3089018017203F03200CC17604003380D40CE035028806C29407605A80DC0D801F01D00740F40260218088086022019804418404303600E00D803802B807412C04D04380B410E02D016803C2C40B605B01800DC03801C00740F80400200088080022011004418A06703380E00CE03801C007411804D02680B409A02D016803C18A06703380E00CE03801C007411804D02680B409A02D016803C1E6087043814410E051028806C10E051028806C0A201B00D802467E1360A801C839C0A905980D42B4077043809C18603E02100843C80B306280FC22406003200CC16E03802100840CE035028806C27806903C007C16A03701D00740F001F0140050086022019804417803A02200880D803802B80740D803802B807410E02D016803C2A80AF03D00F816C06001C00740F403F0140050080022011004417E06402100880CE03801C00740CE03801C007409A02D016803C17E06402100880CE03801C00740CE03801C007409A02D016803C13E05702B80B410E051028806C10E051028806C0A201B00D802428607605780F815E03E03000740E602801F805007E014011004416804203200880C802201C00740C802201C007407001D016803C16804203200880C802201C00740C802201C007407001D016803C13203302B80B40AE02D028806C0AE02D028806C0A201B00D802418A06503280D40CA03501A80740CA03501A807406A01D00E803C13205102880B40A202D016806C0A202D016806C05A01B00D802413205102880B40A202D016806C0A202D016806C05A01B00D80240A202D016806C05A01B00D802405A01B00D8024036009004800C624121099018829E07203D808039C0A905980D418603E021008439C0A905980D418603E021008422406003200CC0CE035028806C24C05F03300540F001F011004416A03701D0074086022019804416A03701D007408602201980440D803802B807410E02D016803C2760A303400D40F203F011004416C06001C0074080022011004416C06001C007408002201100440CE03801C007409A02D016803C16C06001C007408002201100440CE03801C007409A02D016803C0CE03801C007409A02D016803C10E051028806C0A201B00D802425E06B05180D40EA02701F804415E03E030007407E014011004415E03E030007407E01401100440C802201C007407001D016803C15E03E030007407E01401100440C802201C007407001D016803C0C802201C007407001D016803C0AE02D028806C0A201B00D802417A06103080CC08202101080440CA03501A807406A01D00E803C0CA03501A807406A01D00E803C0A202D016806C05A01B00D80240CA03501A807406A01D00E803C0A202D016806C05A01B00D80240A202D016806C05A01B00D802405A01B00D8024036009004800C23605E036808014603501F804414603501F80440C001D011004414603501F80440C001D01100440C001D011004407001D016803C14603501F80440C001D01100440C001D011004407001D016803C0C001D011004407001D016803C07001D016803C0A201B00D802416205B02080840C203301080440C2033010804406A01D00E803C0C2033010804406A01D00E803C06A01D00E803C05A01B00D80240C2033010804406A01D00E803C06A01D00E803C05A01B00D802406A01D00E803C05A01B00D802405A01B00D8024036009004800C14E03D02D80840B602101980440B6021019804406601100E803C0B6021019804406601100E803C06601100E803C03A00F00D80240B6021019804406601100E803C06601100E803C03A00F00D802406601100E803C03A00F00D802403A00F00D8024036009004800C0C6033019806C06601B00D803C06601B00D803C03600F007802406601B00D803C03600F007802403600F007802401E009004800C06601B00D803C03600F007802403600F007802401E009004800C03600F007802401E009004800C01E009004800C0120030018004D
  | 3 => 0x2097E12F3C272C815BECA16C85B240BCBC05F60A5C785E1C0C49A064C4329681A90036E2024D0A9550604A0C99A067A8344F01B9E039480268835B581C7A03C04028980F6900A8C01C5000E289FCC05ABD0BDC406110313E019E6035740240032EE01AF503896026580E79009EE01AC000D60346C81BCF03A8E027B80F3580A7301C5000E280F9F00AC201D8000EC009F0004F8009F0004F8A955075800C20E085E43202822FE034940240033A38244F0375A026580DF9009EE013DC00D6035220256E0391E027B80EA880A73014E600E280EFA00AC20158400EC006A7804F8009F0004F8346C825080387C027680E7080A55014AA00E080EDC80AB70156E00EBC06AC8050000A00005000F5800B160162C00F4807008054000A8000540095A0072000E40007200390001C800390001C8A5C78617C0EB00085E4310601C0D045FC02400325101D070489E026580DE20077F013DC00D6033A381DD504ADC027B80E7A007DA014E600E280E9D807F30158400EC00561003B0009F0004F832EE01D8204A10027680E3D007BD014AA00E080E7B007E90156E00EBC055B803AF00A00005000EDC808190162C00F48058B003D200A800054006F1004C100E40007200390001C800390001C835B58256E04ADC034E00E6B00A0E0141C00E080E9D80A4D0149A00EBC0526803AF0075E005000EFA00A9A0153400F48054D003D2007A4005400685004C100982007200260801C800390001C80F9F00B160162C01008058B00402008040058806F10051500A2A007A0028A801E8003D0001E8095A006E400DC800A800372002A000540002A00372002A000540002A00150000A800150000A8A16C85D120C4B806CF83AC002179045FC02400310601B4803B1601DEC122780996013DC00D60320281BD803CB201EC812B7009EE014E600E280E6B007380109000B200561003B0009F0004F8313E01B7903BD801E641284009DA014AA00E080E3D007250105600AFC055B803AF00A00005000E7080733010B200B34058B003D200A8000540058B003D200A80005400390001C800390001C8344F0244F03CEA02A0C12B700D380141C00E080E7A00A2200FFE00AFC0526803AF0075E005000EA880A4D0103600B34054D003D2007A400540054D003D2007A4005400260801C800390001C80F3580AB7010E400BB8058B004020080400588058B004020080400588028A801E8003D0001E807008051500A2A006F80372002A000540002A00372002A000540002A00150000A800150000A8329681DA50489E02A0C122780A8301A7000E080DE2007E90144400AFC0511002BF0075E005000DF9007EE0149A00B340526802CD007A4005400526802CD007A40054001E90015000390001C80E79008410156E00BB8055B802EE0080400588055B802EE0080400588020100162003D0001E806AC8038700A2A006F8028A801BE00540002A0028A801BE00540002A00150000A800150000A80F6900AC20158400F480561003D2007A4005880561003D2007A40058801E900162002C4001E806A7804C100982006F80260801BE0037C002A00260801BE0037C002A000DF000A800150000A809F00072000E4000A800390002A000540004000390002A0005400040001500010000200001000390002A000540004000150001000020000100015000100002000010000800004000080000409CB2059CE0BAD806570312E01B5C0396601C583AC002179045FC02400122780996013DC00D60308381ADE038B001BB40F3A807C80106E00B0012B7009EE014E600E280561003B0009F0004F82F7101A480376801B000EF6007A50101400AC41284009DA014AA00E08055B803AF00A00005000E1F0070A00EF400A080439002E2007C0003E0058B003D200A80005400390001C800390001C83266822FE038B0027080F2C80A9E00FCA00AC412B700D380141C00E080526803AF0075E005000E4780A0E00E8C00A08040D802E2005C4003E0054D003D2007A4005400260801C800390001C80EA380A5500EF400A58042C802FA005F400400058B004020080400588028A801E8003D0001E8058B004020080400588028A801E8003D0001E80372002A000540002A00150000A800150000A8312681C76045FC027080EC58085D0153C00AC4122780A8301A7000E080511002BF0075E005000DD6807BC0141C00A0803FF80221005C4003E00526802CD007A40054001E90015000390001C80E25807EC014AA00A5804158022A005F400400055B802EE0080400588020100162003D0001E8055B802EE0080400588020100162003D0001E8028A801BE00540002A00150000A800150000A80F0100A73014E600EBC0424002E2005C4004000561003D2007A40058801E900162002C4001E80561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A807600054000A80007A002A0001E8003D0002A00390002A0005400040001500010000200001000390002A000540004000150001000020000100015000100002000010000800004000080000402F2F01AA20396601F08117F009C20153C00AC4117F009C20153C00AC4069C003820075E005000D25006F800FCA00780050700282005C4003E0050700282005C4003E001E90015000390001C80D5D007170101400798052A80296005F400400052A80296005F400400020100162003D0001E8052A80296005F400400020100162003D0001E8020100162003D0001E80150000A800150000A80E52009EE0106E00B4C0539803AF005C4004000539803AF005C40040001E900162002C4001E80539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A8071400500007C00056002A0001E8003D0002A002A0001E8003D0002A0015000100002000010002A0001E8003D0002A00150001000020000100015000100002000010000800004000080000400DB8807D6013DC00B4C04F7002D30075E0040004F7002D30075E0040001D780100002C4001E804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A806B0003C800A0000560028000158003D0002A0028000158003D0002A000F4000A80020000100028000158003D0002A000F4000A8002000010000F4000A8002000010000800004000080000400714004F8009F000720027C001C800390002A0027C001C800390002A000E4000A80015000100027C001C800390002A000E4000A8001500010000E4000A800150001000054000400008000040027C001C800390002A000E4000A8001500010000E4000A80015000100005400040000800004000E4000A80015000100005400040000800004000540004000080000400020000100002000010979E056A80B39C060E42E89019A503544019A030BE01B24038EC01C180ED28078E00FAC00A783AC002179045FC02400122780996013DC00D6012B7009EE014E600E280561003B0009F0004F82D5E8191003490019640DBC806E200E2E0097C0EC10078A00FD800AB00420802D300790003C81284009DA014AA00E08055B803AF00A0000500058B003D200A80005400390001C800390001C8302502179035BC025080DEC009C200DF00097C0EEA80A8300F7800AB003F7002D3005A6003C812B700D380141C00E080526803AF0075E00500054D003D2007A4005400260801C800390001C80DE7809DA00E14009C80399802960052C00378040C802EE005DC0040001C380158002B000158058B004020080400588028A801E8003D0001E80372002A000540002A00150000A800150000A82F0E01B24042F2025080DA400798013840097C0E83808380150600AB003F480218005A6003C8122780A8301A7000E080511002BF0075E005000526802CD007A40054001E90015000390001C80D7A8078A013B4009C80392801D30052C0037803F480216005DC00400017700100002B000158055B802EE0080400588020100162003D0001E8028A801BE00540002A00150000A800150000A80E3D009EE013DC00E08039C00282005040037803F9802CD0059A0040001668010000200001580561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A80561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A80390002A000540004000150001000020000100015000100002000010000800004000080000402D92019A5036B801D4010BC80942013840097C0E0680798010BA008240541802AC005A6003C8117F009C20153C00AC4069C003820075E00500050700282005C4003E001E90015000390001C80CF3006E200F4A0072004ED002720052C0037803DE801D300454002E8017700100002B000158052A80296005F400400020100162003D0001E8020100162003D0001E80150000A800150000A80DCF0099600F9000AB004F700382005040037803ED002BF00442002E801668010000200001580539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A80539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A802A0001E8003D0002A00150001000020000100015000100002000010000800004000080000400D480078E0132C00AB004CB002AC007040037803BF802180057E002E8015F800BA002000015804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A8028000158003D0002A000F4000A8002000010000F4000A8002000010000800004000080000400546003B0007600054001D800150002A0001E801D800150002A0001E800A80007A000F4000A8027C001C800390002A000E4000A8001500010000E4000A800150001000054000400008000040027C001C800390002A000E4000A8001500010000E4000A80015000100005400040000800004000E4000A800150001000054000400008000040005400040000800004000200001000020000102B7D81839032B801A480D9F0075000F840073010BC80942013840097C0541802AC005A6003C810BC80942013840097C0541802AC005A6003C8069C003820075E0050001E90015000390001C80C220065900D80005D003CC801C8003CC0028804ED002720052C00378017700100002B00015804ED002720052C00378017700100002B000158020100162003D0001E80150000A800150000A80CF50090000DDA0097C03D9002B1003C00028804F7003820050400378016680100002000015804F7003820050400378016680100002000015801E900162002C4001E800DF000A800150000A804F7003820050400378016680100002000015801E900162002C4001E800DF000A800150000A801E900162002C4001E800DF000A800150000A8015000100002000010000800004000080000400C9880706012000097C03BD80209005620028804CB002AC0070400378015F800BA002000015804CB002AC0070400378015F800BA002000015801D780100002C4001E800B10007A00150000A804CB002AC0070400378015F800BA002000015801D780100002C4001E800B10007A00150000A801D780100002C4001E800B10007A00150000A800F4000A80020000100008000040000800004005130038A00714005000164000F8001F00015801D800150002A0001E800A80007A000F4000A801D800150002A0001E800A80007A000F4000A800E4000A80015000100005400040000800004001D800150002A0001E800A80007A000F4000A800E4000A80015000100005400040000800004000E4000A800150001000054000400008000040005400040000800004000200001000020000100BEC0066800E2C0073004800025F005620028804800025F005620028801C1000DE002000015804800025F005620028801C1000DE002000015801C1000DE002000015800B10007A00150000A804800025F005620028801C1000DE002000015801C1000DE002000015800B10007A00150000A801C1000DE002000015800B10007A00150000A800B10007A00150000A8008000040000800004004D10035800580003C801C500140001F00015801C500140001F00015800A80007A000F4000A801C500140001F00015800A80007A000F4000A800A80007A000F4000A8005400040000800004001C500140001F00015800A80007A000F4000A800A80007A000F4000A8005400040000800004000A80007A000F4000A8005400040000800004000540004000080000400020000100002000010049A0029E006B0003C801AC000F2002800015801AC000F2002800015800A000056000F4000A801AC000F2002800015800A000056000F4000A800A000056000F4000A8003D0002A000800004001AC000F2002800015800A000056000F4000A800A000056000F4000A8003D0002A000800004000A000056000F4000A8003D0002A0008000040003D0002A0008000040002000010000200001001C50013E0027C001C8009F00072000E4000A8009F00072000E4000A800390002A0005400040009F00072000E4000A800390002A000540004000390002A00054000400015000100002000010009F00072000E4000A800390002A000540004000390002A0005400040001500010000200001000390002A00054000400015000100002000010001500010000200001000080000400008000053
  | 4 => 0x27BA2C1212CD25228210466098220843A8808B494038EC89B6668456AE09008A03B86C24D8C00F8810200860101B09E044846AAE092EFE03CDB025DF90100670212D8010BA026A9A0106920226C001171808CDD00483400B5A40048A896ACC04348808BDF4039AC02418000F39001F74800FDD02525800FBF0020F9A010B9C086EF00454200AEB00045E0261620102B1021F3C0113AC08CAB00484600B7480049500903A804A3500BE64004C2803C0F00180600300C0013389E0448525F408EA78049BDC2490001328901EFD400FDD0258F0013C5802051E010B9C082A1004542008A840045E0267B20144A70213040113AC087EE00484600908C00495008AAF004A3500946A004C2802BBC80180600300C001338261620141DE020E0E011194086828047AB008F560048C808A77004A3F00947E004C5402C0480183800307000136008F0A004CCB009996004F1002E208019640032C800145003A0200203A0040740019C80101D000672000CE40005289B666847A250A4BE8049BDC23FBF01042502651200FDD024BFF010B960278B0010B9C0819400386D008A840045E0258F00111D502894E0113AC08614003A9700908C0049500873B003B4200946A004C280251A80130A00300C00133825258010F3B0283BC0111940846D8039E9008F560048C8086C8003B3900947E004C540251F80131500307000136008A77003CC9009996004F10026658013C40032C800145002DB000176B0040740019C80101D000672000CE400052826A9A0144A702894E0156F8085648045F7008BEE0048C80873B0047A2008F44004C54023D100131500262A00136008AAF0049BA009374004F10024DD0013C400278800145002B3100176B002ED60019C800BB5800672000CE40005280903A804CCB009996005280026658014A000294000154002DB00018D30031A6001B5800C698006D6000DAC00057803A02001FA4003F4800232800FD20008CA00119400070800FD20008CA001194000708004650001C200038400016898220844F440905D603F6C4292FA0126F702651200FDD023FBF00FE7D021F6400DFC809E2C0042E7008A840045E0249000102B6022B6600E5180A2538044EB00908C004950085648036D7007AAC003DE80251A80130A00300C0013382418000FF9A0224E400E2640A0EF004465008F560048C80846D8036840079DC003D8C0251F8013150030700013600868280372E007C8C003ECC026658013C40032C8001450026658013C40032C80014500101D000672000CE400052825DF9013C58022CFC0120A80A2538055BE008BEE0048C808614004670007764003D8C023D100131500262A001360087EE0047A200792C003ECC024DD0013C4002788001450024DD0013C400278800145000BB5800672000CE400052808CAB004A3F007DBA004150026658014A0002940001540026658014A000294000154000C698006D6000DAC00057802E208018D30031A600197800FD20008CA00119400070800FD20008CA001194000708004650001C200038400016824D8C0110360278B00120A809E2C00482A00AB7C0048C808194003AC1008CE0003D8C02338000F6300262A001360082A1003B21008F44003ECC023D1000FB3002788001450023D1000FB3002788001450009E2000514000CE4000528086EF003D4500947E0041500251F8010540029400015400251F80105400294000154000A50000550000DAC00057802C048013010031A600197800C6980065E00119400070800C6980065E001194000708004650001C200038400016808CDD004A3500946A004F100251A8013C40027880015400251A8013C4002788001540009E2000550000AA000057802BBC80176B002ED600197800BB580065E000CBC00070800BB580065E000CBC0007080032F0001C200038400016803C0F00203A0040740023280101D0008CA0011940009C40101D0008CA0011940009C4004650002710004E20001F40101D0008CA0011940009C4004650002710004E20001F4004650002710004E20001F40013880007D0000FA000064948A0842FE708A60803BE342417580FEC902122200D648292FA0126F702651200FDD009E2C0042E7008A840045E023A9E00FB47020D6600D3A008B3F0039E1007958003D000A2538044EB00908C0049500251A80130A00300C00133822F7D00F63D02030800CED4089390038FD007766003C040A0EF004465008F560048C80251F801315003070001360083838035F00071E000396801F6E8010180028A0001040026658013C40032C80014500101D000672000CE400052824BBF813289020D66010F5008AD98048CC00756A003C040A2538055BE008BEE0048C8023D100131500262A001360084C10045F7006F2400396801E4B001018002030001040024DD0013C400278800145000BB5800672000CE4000528087CF0047AB0071E0003AE801F230010900021200010B8026658014A000294000154000C698006D6000DAC000578026658014A000294000154000C698006D6000DAC00057800FD20008CA001194000708004650001C200038400016824022810768026512010F50087D9003D20009198003C0409E2C00482A00AB7C0048C802338000F6300262A001360081478039DD008BEE00396801DD9000CED002030001040023D1000FB3002788001450009E2000514000CE4000528083E6803B18008F56003AE801E77000D2A0021200010B80251F80105400294000154000A50000550000DAC0005780251F80105400294000154000A50000550000DAC00057800C6980065E001194000708004650001C2000384000168089B000484600908C004C5401EAB0010180020300010B80251A8013C4002788001540009E2000550000AA00005780251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C200038400016802F990019640032C8001B5800CB20006D6000DAC0007080101D0008CA0011940009C4004650002710004E20001F40101D0008CA0011940009C4004650002710004E20001F4004650002710004E20001F40013880007D0000FA00006422D2500F98B02122200E600099448043D4009198003C04099448043D4009198003C0402ADF00123200262A00136007BF500356100756A002EC0022FB800E5A002030001040022FB800E5A002030001040009E2000514000CE400052807DD2003630007766002F68023D5800EBA0021200010B8023D5800EBA0021200010B800A50000550000DAC000578023D5800EBA0021200010B800A50000550000DAC00057800A50000550000DAC000578004650001C2000384000168084B6004542007958003ECC024230013150020300010B8024230013150020300010B8009E2000550000AA0000578024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C200038400016802DD20018380028A000151800CB20006D6000DAC00070800CB20006D6000DAC000708004650002710004E20001F400CB20006D6000DAC000708004650002710004E20001F4004650002710004E20001F40013880007D0000FA00006408021803A6C008A84003ECC022A1000FB300262A0010B8022A1000FB300262A0010B80098A80042E000AA0000578022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E00038400016802BAC0013BA00307000151800C1C000546000DAC00070800C1C000546000DAC0007080036B0001C20004E20001F400C1C000546000DAC0007080036B0001C20004E20001F40036B0001C20004E20001F40013880007D0000FA00006402D6900180600300C0019C800C03000672000CE400070800C03000672000CE4000708003390001C20003840001F400C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA00006400C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA000064003390001C20003840001F4000E100007D0000FA000064000E100007D0000FA0000640003E8000190000320000149096684114A085FCE039BC0227A200F1D601F31600C68823D1280FD1E020ED000D5400881B0038720074D8003A98292FA0126F702651200FDD009E2C0042E7008A840045E00A2538044EB00908C0049500251A80130A00300C00133821A4400EC6001EC7A00C4B007FCD003474006C6000366C0879D80385C007630003BC801EA2800FB3002774000FC80A0EF004465008F560048C80251F801315003070001360026658013C40032C80014500101D000672000CE4000528235570126F701F68E0103700815B0043D4006AC200366C088EA80482A0073BA003BC801D90800FB3001F66000FC80A2538055BE008BEE0048C8023D100131500262A001360024DD0013C400278800145000BB5800672000CE400052808158804465006BE00037E801B97000EBA001D74000ED801E648010540020A80010B800980800546000A8C000438026658014A000294000154000C698006D6000DAC00057800FD20008CA001194000708004650001C200038400016822B5700FD1E024DEE01037007F3E8038A20087A800366C085CB003C48009054003BC801D60800CAA001F66000FC809E2C00482A00AB7C0048C802338000F6300262A001360023D1000FB3002788001450009E2000514000CE400052807DF800385C0088CA0037E801B42000B8F001D74000ED801D9C800CCA0020A80010B80082A00042E000A8C0004380251F80105400294000154000A50000550000DAC00057800C6980065E001194000708004650001C2000384000168083490044EB0089D60048C801B6B800E5A001CB4000ED801DA1000FB3001F660010B8007D980042E00085C0004380251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C20003840001680251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C20003840001680101D0008CA0011940009C4004650002710004E20001F4004650002710004E20001F40013880007D0000FA00006421D4400F1D601FD9200DB640937B8040DC0087A800366C082128038A2007A4000314402415000EF2001F66000FC8099448043D4009198003C0402ADF00123200262A001360022FB800E5A002030001040009E2000514000CE4000528079C80034740071FA002CF002232800DFA001D74000ED801CF4800B8F001A54000D480082A00042E000A8C000438023D5800EBA0021200010B800A50000550000DAC00057800A50000550000DAC000578004650001C2000384000168080338042E70073C2003BC802275801232001CB4000ED801D4B800F630019DA000D48007D980042E00085C000438024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C2000384000168024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C200038400016800CB20006D6000DAC000708004650002710004E20001F4004650002710004E20001F40013880007D0000FA00006407C408038720085CE003BC802173800EF2002464000ED801C36800CAA001EC6000D48007B180035200085C000438022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E000384000168022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E00038400016800C1C000546000DAC0007080036B0001C20004E20001F40036B0001C20004E20001F40013880007D0000FA0000640241A00130A00261400145000985000514000A2800057800985000514000A280005780028A00015E0002BC00016800C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA00006400C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA000064003390001C20003840001F4000E100007D0000FA000064000E100007D0000FA0000640003E800019000032000014208CC00E6F001DF1A00CA0807ED88036D9007300002CF00937B8040DC0087A800366C02415000EF2001F66000FC80937B8040DC0087A800366C02415000EF2001F66000FC802ADF00123200262A001360009E2000514000CE40005280735800312C00676A00271801C4C800B3C0017B4000BE002232800DFA001D74000ED80082A00042E000A8C00043802232800DFA001D74000ED80082A00042E000A8C00043800A50000550000DAC000578004650001C2000384000168079B6003F740069D000366C01CA3000F01001760000BE002275801232001CB4000ED8007D980042E00085C00043802275801232001CB4000ED8007D980042E00085C000438009E2000550000AA00005780032F0001C200038400016802275801232001CB4000ED8007D980042E00085C000438009E2000550000AA00005780032F0001C2000384000168009E2000550000AA00005780032F0001C2000384000168004650002710004E20001F40013880007D0000FA0000640770D803550007EE800366C01BF9000C51001E02000BE002173800EF2002464000ED8007B180035200085C00043802173800EF2002464000ED8007B180035200085C0004380098A80042E000AA0000578002A800015E00038400016802173800EF2002464000ED8007B180035200085C0004380098A80042E000AA0000578002A800015E0003840001680098A80042E000AA0000578002A800015E0003840001680036B0001C20004E20001F40013880007D0000FA000064022E30012540024A8001360007BD00041000082000043800985000514000A280005780028A00015E0002BC00016800985000514000A280005780028A00015E0002BC000168003390001C20003840001F4000E100007D0000FA00006400985000514000A280005780028A00015E0002BC000168003390001C20003840001F4000E100007D0000FA000064003390001C20003840001F4000E100007D0000FA000064000E100007D0000FA0000640003E800019000032000014071D90031A2006B24002CF001FBA000D9B001E02000BE001FBA000D9B001E02000BE0009190003B600085C00043801FBA000D9B001E02000BE0009190003B600085C000438009190003B600085C000438002A800015E00038400016801FBA000D9B001E02000BE0009190003B600085C000438009190003B600085C000438002A800015E000384000168009190003B600085C000438002A800015E000384000168002A800015E0003840001680013880007D0000FA00006402174001178001E80000FC80092A0004D80008200004380092A0004D80008200004380028A00015E0002BC0001680092A0004D80008200004380028A00015E0002BC0001680028A00015E0002BC000168000E100007D0000FA0000640092A0004D80008200004380028A00015E0002BC0001680028A00015E0002BC000168000E100007D0000FA0000640028A00015E0002BC000168000E100007D0000FA000064000E100007D0000FA0000640003E80001900003200001402036000EA60022F0000FC8008BC0003F20009B0000438008BC0003F20009B00004380026C00010E0002BC000168008BC0003F20009B00004380026C00010E0002BC0001680026C00010E0002BC000168000AF00005A0000FA000064008BC0003F20009B00004380026C00010E0002BC0001680026C00010E0002BC000168000AF00005A0000FA0000640026C00010E0002BC000168000AF00005A0000FA000064000AF00005A0000FA0000640003E800019000032000014009150004CE00099C0005280026700014A0002940001680026700014A000294000168000A500005A0000B40000640026700014A000294000168000A500005A0000B4000064000A500005A0000B40000640002D0000190000320000140026700014A000294000168000A500005A0000B4000064000A500005A0000B40000640002D000019000032000014000A500005A0000B40000640002D0000190000320000140002D0000190000320000140000C80000500000A0000057
  | 5 => 0x34A26152740EC8A0A1D40740E5CA3DD73077E6D81EB772014FFCCA6C8D707A7E981F9957015CD202033F301696F405CEEA004AB6CA91D4807C50E8202153016344C20F6DD01730B405FBEF004D2A421856E017A45C062B0D004FE84064AD5005260C018D9E0010914A28E7207756BC1ED9300153EDC1FB1E50163DC405BC310049F4C207C30016E37005F7D0004D5AC0618C1004FE2401826A001019C21318A0176908061E78004F54C0651160052D380192960010C6406766B0054D0C01A0B200115CC01F82400150180054060003804A91D4808CD5681F62AF019E45C200B6B01AC4C005A9070049F4C20C88601B805C05DCEC004D5AC05EC3B004FE24013F89001019C21788A01C1E4805FF30004F54C06202C0052D38014B4E0010C64063D3D0054D0C01534300115CC0183E20015018005406000380421318A01BEA5805F305004EC8C0613C8005246801491A0010AC4063EDA005503001540C00116C00186C000152E80054BA000387C0670670057B6C015EDB0011FE40197F000161E800587A0003AFC01ED11001AE50006B9400047B8006B9400047B80011EE0000BF4A6C8D707E01D023355A019E45C1FA0D401780B806B1300049F4C202EEE01810C806E017004D5AC05DFCD0043FE8013F89001019C20C8860188AE8070792004F54C060B7900462C4014B4E0010C6406178A0046EB001534300115CC01534300115CC0054060003804207C3001856DC06FA96004EC8C05FC5F004581001491A0010AC40616710046FF001540C00116C001540C00116C00054BA000387C063EDA0048CF0015EDB0011FE4015EDB0011FE400587A0003AFC01942B0014AA0006B9400047B8006B9400047B80011EE0000BF421856E01C1E48070792005E988060369005091C0142470010AC406178A00525B001496C00116C001496C00116C00045B0000387C063D3D00549940152650011FE40152650011FE40047F90003AFC0180AF0014AA00052A800047B80052A800047B80011EE0000BF406766B0057B6C015EDB0012AD4015EDB0012AD4004AB50003D5401942B0015BD00056F40004B780056F40004B780012DE0000C9401ED11001A964006A590005CD0006A590005CD00017340000F78006A590005CD00017340000F780017340000F780003DE0000294A3DD7307A04781FB5A0016FF9C23355A019E45C06B1300049F4C1FA0D401715840618C0004347006E017004D5AC013F89001019C200B6B017667C06356C00449FC070792004F54C014B4E0010C64060369004282C012425000EBE401534300115CC00540600038041FB1E501726F80625910043E9006FA96004EC8C01491A0010AC405FC5F0042438012324000EB3801540C00116C00054BA000387C0613C80043210012922000EFC0015EDB0011FE400587A0003AFC015EDB0011FE400587A0003AFC006B9400047B80011EE0000BF420F6DD01B805C0639400052698070792005E9880142470010AC4060B7900510F4011DC8000EB3801496C00116C00045B0000387C06202C00525B00121F0000EFC00152650011FE40047F90003AFC0152650011FE40047F90003AFC0052A800047B80011EE0000BF40651160055030012B81000F80C015EDB0012AD4004AB50003D54015EDB0012AD4004AB50003D540056F40004B780012DE0000C940197F00015BD00056F4000472C006A590005CD00017340000F78006A590005CD00017340000F780017340000F780003DE00002942033F3018698806E017005269806E0170052698017A620010AC405DFCD004642001443D000EB3801443D000EB380045B0000387C05EC3B0046CC401496C000EFC001496C000EFC00047F90003AFC01496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF40618C1004908001540C000F80C01540C000F80C004AB50003D5401540C000F80C004AB50003D54004AB50003D540012DE0000C940186C000119B80056F4000472C0056F4000472C0017340000F780056F4000472C0017340000F780017340000F780003DE0000294064AD50054D0C0153430011FE40153430011FE40047F90003D540153430011FE40047F90003D540047F90003D54000F550000C940183E20014AA00052A8000472C0052A8000472C0011CB0000F780052A8000472C0011CB0000F780011CB0000F780003DE000029401F824001AE50006B940005CD0006B940005CD00017340001440006B940005CD0001734000144000173400014400005100000360006B940005CD00017340001440001734000144000051000003600017340001440000510000036000051000003600000D80000090A0A1D40771D501E9922015EE8C1FB5A0017172C05F7E80040E5C23355A019E45C06B1300049F4C06E017004D5AC013F89001019C1F62AF016D69C05EDA300406A8063940004546C0120D4000E854070792004F54C014B4E0010C6401534300115CC00540600038041ED9300166E6405D39B003F27C06259100445B0011D21000E55006FA96004EC8C01491A0010AC401540C00116C00054BA000387C05F3050041B2C0113C3000DE7C012B81000F4EC004A2E0003174015EDB0011FE400587A0003AFC006B9400047B80011EE0000BF420215301AC4C005EDA3004E36406356C00530A40118E8000E550070792005E9880142470010AC401496C00116C00045B0000387C05FF30005091C010DFF000DE7C0121F0000F4EC003D3B00031740152650011FE40047F90003AFC0052A800047B80011EE0000BF4061E7800524680113C3000E36C012922000FB2C003ECB00032B4015EDB0012AD4004AB50003D540056F40004B780012DE0000C94015EDB0012AD4004AB50003D540056F40004B780012DE0000C94006A590005CD00017340000F780017340000F780003DE00002941F9957017C13406B130004E3640618C000485B8014C29000E55006E0170052698017A620010AC401443D000EB380045B0000387C05DCEC004572C014247000DE7C011DC8000CE3C003D3B000317401496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF405F7D00046BB401491A000E36C012324000D1D8003ECB00032B401540C000F80C004AB50003D54004AB50003D540012DE0000C9401540C000F80C004AB50003D54004AB50003D540012DE0000C940056F4000472C0017340000F780017340000F780003DE0000294062B0D0052D38014B4E00116C0012425000F4EC003D3B00032B40153430011FE40047F90003D540047F90003D54000F550000C940153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE000029401A0B200161E800587A0004B7800587A0004B780012DE0000F78006B940005CD0001734000144000173400014400005100000360006B940005CD00017340001440001734000144000051000003600017340001440000510000036000051000003600000D800000901EB772016B3B405F7E80044C1C06B130004E364014C29000E55006B130004E364014C29000E550017A620010AC40045B0000387C05A90700410BC0118E8000BDE0014247000DE7C003D3B0003174014247000DE7C003D3B00031740047F90003AFC0011EE0000BF405BC310041E70011D21000C06801491A000E36C003ECB00032B401491A000E36C003ECB00032B4004AB50003D540012DE0000C9401491A000E36C003ECB00032B4004AB50003D540012DE0000C94004AB50003D540012DE0000C940017340000F780003DE000029405FBEF004FE240120D4000EEF8014B4E00116C0003D3B00032B4014B4E00116C0003D3B00032B40047F90003D54000F550000C94014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE000029401929600152E8004A2E0003D6800587A0004B780012DE0000F7800587A0004B780012DE0000F780017340001440000510000036000587A0004B780012DE0000F78001734000144000051000003600017340001440000510000036000051000003600000D8000009005CEEA0045F7C013F89000EEF8013F89000EEF80045B000032B4013F89000EEF80045B000032B40045B000032B4000F550000C94013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE000029401826A00120480054BA0003D680054BA0003D680012DE0000F780054BA0003D680012DE0000F780012DE0000F7800051000003600054BA0003D680012DE0000F780012DE0000F7800051000003600012DE0000F78000510000036000051000003600000D80000090018D9E001501800540600047B800540600047B80011EE0000F7800540600047B80011EE0000F780011EE0000F780003DE000036000540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D8000009000540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D800000900011EE0000F780003DE00003600003DE00003600000D800000900003DE00003600000D800000900000D8000009000002400000189D03B20743FB81DC75401546401E811E0161C0005ACED003D0941F8074016F6EC05F04D0040B4C061A620043CDC0117DF000E09C23355A019E45C06B1300049F4C06E017004D5AC013F89001019C070792004F54C014B4E0010C6401534300115CC00540600038041DD5AF015A88C059B99003C8F805C9BE003FDEC01079C000D3D80615B70043BBC011AED000E4C4012420000EEF8004812000300C06FA96004EC8C01491A0010AC401540C00116C00054BA000387C015EDB0011FE400587A0003AFC006B9400047B80011EE0000BF41F143A019E45C05B5A7004B46405D99F004E36401042F000D3D80622BA00526980115CB000E4C4011B31000EEF8003BBE000300C070792005E9880142470010AC401496C00116C00045B0000387C0152650011FE40047F90003AFC0052A800047B80011EE0000BF405DA42004EC8C0106CB000D8EC010C84000E36C0038DB0002DDC01233C000F80C003E0300032B400466E0003D68000F5A0000A3C015EDB0012AD4004AB50003D540056F40004B780012DE0000C94006A590005CD00017340000F780017340000F780003DE00002941E9FA6016F6EC067917004B46405C5610043F540138D9000D3D806043200478740149A6000E4C4011908000CA10003BBE000300C06E0170052698017A620010AC401443D000EB380045B0000387C01496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF405B8DC0043BBC013B23000D8EC01090E000BCE40038DB0002DDC011BFC000CCE8003E0300032B4003E0300032B4000F5A0000A3C01540C000F80C004AB50003D54004AB50003D540012DE0000C940056F4000472C0017340000F780017340000F780003DE000029405E917004F54C013D530010AC4010A0B000DE7C00379F0002DDC011BAC000EFC0003BF000032B4003BF000032B4000CAD0000A3C0153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE00002940153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE0000294006B940005CD00017340001440001734000144000051000003600017340001440000510000036000051000003600000D800000901DF9B60161C0005C5CB00421EC067917004B4640138D9000D3D805E02E0043F5401216E000C4EC0149A6000E4C4003BBE000300C06B130004E364014C29000E550017A620010AC40045B0000387C014247000DE7C003D3B00031740047F90003AFC0011EE0000BF4058F71003FDEC01116C000B7B0013B23000D8EC0038DB0002DDC011604000BCE40034760002A58003E0300032B4000F5A0000A3C01491A000E36C003ECB00032B4004AB50003D540012DE0000C94004AB50003D540012DE0000C940017340000F780003DE000029405CC2D004D5AC01151B000E4C4013D530010AC400379F0002DDC0118B1000EB3800338F0002A58003BF000032B4000CAD0000A3C014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE0000294014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE000029400587A0004B780012DE0000F78001734000144000051000003600017340001440000510000036000051000003600000D8000009005A5BD0043CDC01356B000E4C401356B000E4C40042B10002DDC010FFA000CA10003ACE0002A58003ACE0002A58000CAD0000A3C013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE0000294013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE00002940054BA0003D680012DE0000F780012DE0000F7800051000003600012DE0000F78000510000036000051000003600000D8000009001498300115CC0045730003AFC0045730003AFC000EBF0000C940045730003AFC000EBF0000C94000EBF0000C94000325000029400540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D8000009000540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D800000900011EE0000F780003DE00003600003DE00003600000D800000900003DE00003600000D800000900000D8000009000002400000181D03970154640057BA3003DD8C05BFE700421EC011307000B710067917004B4640138D9000D3D80149A6000E4C4003BBE000300C067917004B4640138D9000D3D80149A6000E4C4003BBE000300C017A620010AC40045B0000387C0047F90003AFC0011EE0000BF4054FB7003C8F800FC9F000A530010FA4000B7B000301A0002698013B23000D8EC0038DB0002DDC003E0300032B4000F5A0000A3C013B23000D8EC0038DB0002DDC003E0300032B4000F5A0000A3C004AB50003D540012DE0000C940017340000F780003DE0000294058D130049F4C0101AA000D3D801127F000E550002F780002698013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C0047F90003D54000F550000C940011CB0000F780003DE0000294013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C0047F90003D54000F550000C940011CB0000F780003DE00002940047F90003D54000F550000C940011CB0000F780003DE00002940017340001440000510000036000051000003600000D800000900573480040B4C0127D3000D3D8010D1C000C4EC003954000269801356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C01356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C0045B000032B4000F550000C94000F550000C940003DE000029401356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C0045B000032B4000F550000C94000F550000C940003DE00002940045B000032B4000F550000C94000F550000C940003DE00002940012DE0000F78000510000036000051000003600000D80000090013FA10010C64004319000387C003AF90003174000C5D0000A3C0045730003AFC000EBF0000C94000EBF0000C9400032500002940045730003AFC000EBF0000C94000EBF0000C9400032500002940011EE0000F780003DE00003600003DE00003600000D800000900045730003AFC000EBF0000C94000EBF0000C9400032500002940011EE0000F780003DE00003600003DE00003600000D800000900011EE0000F780003DE00003600003DE00003600000D800000900003DE00003600000D800000900000D800000900000240000018053FF3003D094010397000B7100127D3000D3D800395400026980127D3000D3D800395400026980042B10002DDC000CAD0000A3C0127D3000D3D800395400026980042B10002DDC000CAD0000A3C0042B10002DDC000CAD0000A3C000F550000C940003DE00002940127D3000D3D800395400026980042B10002DDC000CAD0000A3C0042B10002DDC000CAD0000A3C000F550000C940003DE00002940042B10002DDC000CAD0000A3C000F550000C940003DE0000294000F550000C940003DE000029400051000003600000D800000900134A9001019C003A15000300C004319000387C000C5D0000A3C004319000387C000C5D0000A3C000EBF0000C940003250000294004319000387C000C5D0000A3C000EBF0000C940003250000294000EBF0000C9400032500002940003DE00003600000D80000090004319000387C000C5D0000A3C000EBF0000C940003250000294000EBF0000C9400032500002940003DE00003600000D80000090000EBF0000C9400032500002940003DE00003600000D800000900003DE00003600000D800000900000D800000900000240000018012ADB000E09C004067000300C004067000300C000E1F0000A3C004067000300C000E1F0000A3C000E1F0000A3C0003250000294004067000300C000E1F0000A3C000E1F0000A3C0003250000294000E1F0000A3C000325000029400032500002940000D80000090004067000300C000E1F0000A3C000E1F0000A3C0003250000294000E1F0000A3C000325000029400032500002940000D80000090000E1F0000A3C000325000029400032500002940000D8000009000032500002940000D800000900000D8000009000002400000180042450003804000E010000BF4000E010000BF40002FD0000294000E010000BF40002FD00002940002FD00002940000A50000090000E010000BF40002FD00002940002FD00002940000A500000900002FD00002940000A500000900000A500000900000240000018000E010000BF40002FD00002940002FD00002940000A500000900002FD00002940000A500000900000A5000009000002400000180002FD00002940000A500000900000A5000009000002400000180000A50000090000024000001800002400000180000060000005A
  | 6 => 0x2E76D5123AA3E7E1DE7735824B582079AD6EE09707F704D1FBC005A75647B87FB2099D3FB04F0915805D6AD8141405001812C800C59168010895C7D029F209BC8FF0502D9F005EE5E4147D8580189FA900CABF7801101E414C7C2401906AA00D006E801185CC034EF660048075002A3918003041478E065E09677D304D76D6805B71B813D3810017C77C00C3C4100106B9C144144E0185FF400CA973801111F8033A770004653200294D48002F33C14A3D5C018DAD600CF07D80117254035444600488EF002ACC180030E940366204004A202002C2628003274C00CF822000ED270007693800087847D029F20AD11DD04EA826806BDB2414042D601BC2E300C182C80106B9C1469F6001C6BD800C76E8001111F803256D6004653200232990002F33C14C8F1C01CF94400CB5CF80117254033D32200488EF002447780030E94034B306004A20200251010003274C00A5F92000ED2700076938000878414A3D5C01CCAE400C9F83001156A80337F300048289002414480030A88034D002004A59700252CB80032A5C00A735E000EF1100077888000889C03650AE004C81200264090003426C00ADE02000F8A30007C5180008E1400CC59A001256D00092B68000A7AC0024ADA00029EB00014F5800017F47B87FB209DD08505688EE806BDB2413CC0B6018EDC100DE17180106B9C14174FE019707C00E35EC001111F8031F13A003D94E00232990002F33C1469F60019DFFE00E7CA2001172540332F66003F459002447780030E940338C7A003FE5400251010003274C0094404000C9D3000769380008784144144E019AF9200E6572001156A8032C578003EC33002414480030A88033937A004002900252CB80032A5C0094B2E000CA9700077888000889C034D002004188600264090003426C0099024000D09B0007C5180008E1400AC5F2000EA7900092B68000A7AC0024ADA00029EB00014F5800017F414C7C2401CF94400E7CA2001435E0032EDF00046D8200236C100030A880338C7A004848F002424780032A5C009091E000CA97000654B8000889C034B306004A16100250B08003426C00942C2000D09B000684D80008E1400A5026000EA79000753C8000A7AC001D4F200029EB00014F5800017F40366204004C812002640900035E500099024000D7940006BCA0000930000AC5F2000F5230007A918000AF54001EA460002BD500015EA8000190C00CC59A001232100091908000D104002464200034410001A2080001DDC002464200034410001A2080001DDC0006882000077700003BB8000044479AD6EE0997F1304F5CCA0061D74015A23BA01AF6C900DE17180106B9C13CC0B60188DDB00CDE78800F3A04038D7B0004447E00232990002F33C14042D6018D6EC00D1207000F7D2C039F2880045C95002447780030E94032EDF0003C80D0020C660002C15C0094404000C9D300076938000878413D38100189B2000CF500800F58DC03995C800455AA002414480030A88032C578003C59E0020B710002C0600094B2E000CA9700077888000889C0337F30003D1F300215500002CCF40099024000D09B0007C5180008E140099024000D09B0007C5180008E140024ADA00029EB00014F5800017F4147D85801C6BD800D190A8012051C039F2880050D7800236C100030A880332F6600473C500202C60002C060009091E000CA97000654B8000889C033D322004848F00209D08002CCF400942C2000D09B000684D80008E1400942C2000D09B000684D80008E14001D4F200029EB00014F5800017F40354446004A59700218FD8002E29C0099024000D7940006BCA000093000099024000D7940006BCA00009300001EA460002BD500015EA8000190C00ADE02000F5230007A918000A6CC002464200034410001A2080001DDC002464200034410001A2080001DDC0006882000077700003BB800004441414050019C0AF00E35EC0012051C038D7B0004814700286BC00030A88031F13A003F4EC00239E28002C060008E78A000B018000654B8000889C03256D6003FCFD00242478002CCF4009091E000B33D000684D80008E14009091E000B33D000684D80008E14001A136000238500014F5800017F4033A770004193C00252CB8002E29C0094B2E000B8A70006BCA000093000094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C00A735E000CDFB0007A918000A6CC001EA4600029B30001A2080001DDC001EA4600029B30001A2080001DDC0006882000077700003BB80000444034EF66004A20200251010003426C0094404000D09B000684D800093000094404000D09B000684D80009300001A13600024C000012600000190C00A5F92000EA79000753C8000A6CC001D4F200029B300014D980001DDC001D4F200029B300014D980001DDC0005366000077700003BB8000044400CF822001256D00092B68000D1040024ADA00034410001A20800025840024ADA00034410001A20800025840006882000096100004B08000055C0024ADA00034410001A20800025840006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C4779DCD60965BEA04CF665805DF7D413D73280188CA700CA1DD000EC41C15A23BA01AF6C900DE17180106B9C038D7B0004447E00232990002F33C13AA09A018545B00C90CD000EB248034642A003E7B7002069A0002B714039F2880045C95002447780030E940094404000C9D3000769380008784135DB5A017F19F00C604E800E724C033D402003DC1F00201108002AF8803995C800455AA002414480030A880094B2E000CA9700077888000889C0327E0C003BEA5001F4640002A0A800863F6000B69A0006B7980007AD40099024000D09B0007C5180008E140024ADA00029EB00014F5800017F4140B67C01BC2E300C90CD00113A1C034481C00488FD001FA4F8002AF88039F2880050D7800236C100030A88009091E000CA97000654B8000889C032D73E0046D82001EB378002A0A80082742000B69A0005B4D00007AD400942C2000D09B000684D80008E14001D4F200029EB00014F5800017F4033C1F60048289001F4640002AD900085540000BAB40005D5A00007D900099024000D7940006BCA00009300001EA460002BD500015EA8000190C0099024000D7940006BCA00009300001EA460002BD500015EA8000190C002464200034410001A2080001DDC0006882000077700003BB8000044413C2456019291700DE17180113A1C03379E20040C69002447E8002AF88038D7B0004814700286BC00030A88008E78A000B018000654B8000889C031DBA0003EB7D00236C10002A0A80080B180009E830005B4D00007AD4009091E000B33D000684D80008E14001A136000238500014F5800017F4032A5CE003FBBB00241448002AD900082DC4000A10E0005D5A00007D900094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C0094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C001EA4600029B30001A2080001DDC0006882000077700003BB8000044403401BA00488EF002447780032A5C0083198000B69A0005B4D00007D900094404000D09B000684D80009300001A13600024C000012600000190C0094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB8000044400B098A000F8A30007C518000AF54001F1460002BD500015EA80001DDC0024ADA00034410001A20800025840006882000096100004B08000055C0024ADA00034410001A20800025840006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C41347EF0018336000CA1DD000F80AC03785C60044E87002447E8002AF8803785C60044E87002447E8002AF8800A1AF0000C2A2000654B8000889C03060B2003B5C9001FA4F80024F48008DB04000A82A0005B4D00007AD4008DB04000A82A0005B4D00007AD4001A136000238500014F5800017F4030F104003C0C00020110800256800090512000AB640005D5A00007D900090512000AB640005D5A00007D90001AF2800024C000015EA8000190C0090512000AB640005D5A00007D90001AF2800024C000015EA8000190C001AF2800024C000015EA8000190C0006882000077700003BB80000444032AFDE0046532002069A0002C9AC00911DE000CA970005B4D00007D9000911DE000CA970005B4D00007D90001A13600024C000012600000190C00911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB8000044400AB306000EF110006B79800093C4001F1460002BD500015EA80001DDC001F1460002BD500015EA80001DDC0006882000096100004B08000055C001F1460002BD500015EA80001DDC0006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C4031645A003F19600232990002C9AC008CA64000B26B000654B80007D90008CA64000B26B000654B80007D90001952E0001F6400012600000190C008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB8000044400A5352000D1350007788800093C4001DE2200024F100015EA80001DDC001DE2200024F100015EA80001DDC00057AA000077700004B08000055C001DE2200024F100015EA80001DDC00057AA000077700004B08000055C00057AA000077700004B08000055C00012C2000015700000AB800000C400A8E46000ED2700076938000A7AC001DA4E00029EB00014F580001DDC001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C4001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C400053D6000077700003BB8000055C0000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C7547CFC0933BC204B2DF5005B8D8C132FE26017A7CA00C19B0000E077013BA10A0186F6300C948B800EBCAC033815E003D534001F8CB0002A32C15A23BA01AF6C900DE17180106B9C038D7B0004447E00232990002F33C039F2880045C95002447780030E940094404000C9D300076938000878412CEFA601739B300BF8CF800DF0240313640003A529001E060000283580335F24003D47E001FDDD8002AE700083278000B26B000689A8000778C03995C800455AA002414480030A880094B2E000CA9700077888000889C0099024000D09B0007C5180008E140024ADA00029EB00014F5800017F413791FE01AF6C900C2A2D8010A9F4031ADD80044E87001DAE480028358033BFFC0048147001F5BE8002AE70007F9FA000B26B00059358000778C039F2880050D7800236C100030A88009091E000CA97000654B8000889C00942C2000D09B000684D80008E14001D4F200029EB00014F5800017F4031B5AC00455AA001DF5280029104007A3E6000AB6400055B20000732C008310C000B8A70005C5380007D900019BF600024F100012788000151C0099024000D7940006BCA00009300001EA460002BD500015EA8000190C002464200034410001A2080001DDC0006882000077700003BB80000444133A7F60186F6300D7B648010A9F40311BB6003D6D1002274380028358032E0F8004024400240A38002AE70007E9D80009B7A00059358000778C038D7B0004814700286BC00030A88008E78A000B018000654B8000889C009091E000B33D000684D80008E14001A136000238500014F5800017F4030BFE8003D47E0022AD5000291040078B3C000937000055B20000732C00800520009DD40005C5380007D90001714E0001F6400012788000151C0094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C001EA4600029B30001A2080001DDC0006882000077700003BB800004440320D540045C950022E4A80030A88007901A000A82A00054150000732C007FCA8000B33D000599E80007D90001667A0001F640000FB20000151C0094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB800004440094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB800004440024ADA00034410001A20800025840006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C412E0FEE017A7CA00C4653800EFEBC035ED920042A7D002274380028358031DB82003D6D1002063480025F78009028E000AB9C00059358000778C03785C60044E87002447E8002AF8800A1AF0000C2A2000654B8000889C008DB04000A82A0005B4D00007AD4001A136000238500014F5800017F402F8EF8003A529001EE0F80023E8C008AB54000A44100055B20000732C007D8660009370000508700006C48001714E0001F6400012788000151C0090512000AB640005D5A00007D90001AF2800024C000015EA8000190C001AF2800024C000015EA8000190C0006882000077700003BB800004440313F52004447E001F3DB8002AE70008B92A000C2A200054150000732C007E8B2000B0180004F4180006C48001667A0001F640000FB20000151C00911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB8000044400911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB80000444001F1460002BD500015EA80001DDC0006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C40302590003D534002223F0002AE7000888FC000AB9C00061510000732C007B29C0009B7A000580C00006C4800160300001B120000FB20000151C008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB80000444008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB80000444001DE2200024F100015EA80001DDC00057AA000077700004B08000055C00057AA000077700004B08000055C00012C2000015700000AB800000C400900EA000C9D300064E980008E1400193A6000238500011C28000190C00193A6000238500011C28000190C000470A0000643000032180000444001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C4001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C400053D6000077700003BB8000055C0000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C125AC10016E36300BBEFA800E2D80030EBA0003BFAF001F01580023BD0035ED920042A7D002274380028358009028E000AB9C00059358000778C035ED920042A7D002274380028358009028E000AB9C00059358000778C00A1AF0000C2A2000654B8000889C001A136000238500014F5800017F402DB8DC0037C09001CE4980020F4C007AC6E0008FA30004AD000006414008AB54000A44100055B20000732C001714E0001F6400012788000151C008AB54000A44100055B20000732C001714E0001F6400012788000151C001AF2800024C000015EA8000190C0006882000077700003BB8000044402F72F20041AE7001D64900028358007BE96000ABE200049E900006414008B92A000C2A200054150000732C001667A0001F640000FB20000151C008B92A000C2A200054150000732C001667A0001F640000FB20000151C001A13600024C000012600000190C0005366000077700003BB80000444008B92A000C2A200054150000732C001667A0001F640000FB20000151C001A13600024C000012600000190C0005366000077700003BB80000444001A13600024C000012600000190C0005366000077700003BB800004440006882000096100004B08000055C00012C2000015700000AB800000C402EB56C003AF2B0020D73800283580079D0200097DE00055F10000641400888FC000AB9C00061510000732C00160300001B120000FB20000151C00888FC000AB9C00061510000732C00160300001B120000FB20000151C001952E0001F6400012600000190C0004980000064300003BB8000044400888FC000AB9C00061510000732C00160300001B120000FB20000151C001952E0001F6400012600000190C0004980000064300003BB80000444001952E0001F6400012600000190C0004980000064300003BB8000044400057AA000077700004B08000055C00012C2000015700000AB800000C4008C2E6000C3A500061D28000889C00160AE0001EB50000F5A8000151C00193A6000238500011C28000190C000470A000064300003218000044400193A6000238500011C28000190C000470A000064300003218000044400053D6000077700003BB8000055C0000EEE000015700000AB800000C400193A6000238500011C28000190C000470A000064300003218000044400053D6000077700003BB8000055C0000EEE000015700000AB800000C400053D6000077700003BB8000055C0000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C02D3AB200381DC001D88380023BD000835CE000A0D600055F10000641400835CE000A0D600055F10000641400185440001CCB0000FB20000151C00835CE000A0D600055F10000641400185440001CCB0000FB20000151C00185440001CCB0000FB20000151C0004980000064300003BB8000044400835CE000A0D600055F10000641400185440001CCB0000FB20000151C00185440001CCB0000FB20000151C0004980000064300003BB8000044400185440001CCB0000FB20000151C0004980000064300003BB800004440004980000064300003BB8000044400012C2000015700000AB800000C400880F2000BCCF00056E28000778C001874A00022270000F5A8000151C001874A00022270000F5A8000151C000470A0000643000032180000444001874A00022270000F5A8000151C000470A0000643000032180000444000470A00006430000321800004440000EEE000015700000AB800000C4001874A00022270000F5A8000151C000470A0000643000032180000444000470A00006430000321800004440000EEE000015700000AB800000C4000470A00006430000321800004440000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C00844AE000A8CB0005E678000778C001799E0001DE300011138000151C001799E0001DE300011138000151C000444E0000547000032180000444001799E0001DE300011138000151C000444E0000547000032180000444000444E00005470000321800004440000C86000011100000AB800000C4001799E0001DE300011138000151C000444E0000547000032180000444000444E00005470000321800004440000C86000011100000AB800000C4000444E00005470000321800004440000C86000011100000AB800000C40000C86000011100000AB800000C400002AE000003100000188000001C001820A00021E100010F0800017F400043C200005FD00002FE8000044400043C200005FD00002FE800004440000BFA00001110000088800000C400043C200005FD00002FE800004440000BFA00001110000088800000C40000BFA00001110000088800000C40000222000003100000188000001C00043C200005FD00002FE800004440000BFA00001110000088800000C40000BFA00001110000088800000C40000222000003100000188000001C0000BFA00001110000088800000C40000222000003100000188000001C0000222000003100000188000001C00000620000007000000380000005D
  | 7 => 0x3D74D0D010CA9CE0222C05D0091C00488ABF3D302559E3804C19238013844A08C98043025F4BE804DC13AC01412F1813B5E5B0052724000A8C6BC003069808E117E002660F7404EBDEEC0145A5B014115200054193C00ACAC200031A090144FC43005547FC00B091680032EFB002CD97A000D0D30001DF64000077D9089FBD080253DB5604C6F2B8013B73401381FAE0051A06C00A79EA800302B6013E10B800536A6E00ACBA740031D6D002BF862000CCCFC001D6F8000075BE014367490054DB5A00B00E440032CD9002D2D49000D2842001E5F40000797D002E09C2000D6A0C001F3D800007CF60008FB8000023EE000047DC000011F708E117E002A08AF004D7CA14016B627813AC5EB005D391400A5E6F800302B601404037005F2CFA00AA531C0031D6D002AF73E000CCCFC001999F800075BE01455E740060CD6C00AD45240032CD9002C13B3000D2842001A5084000797D002CC15C000D6A0C001AD4180007CF60007650900023EE000047DC000011F7014367490060446000AC39B8003284F002BD833000D1866001A30CC00078F1002CDFAF000D7542001AEA840007D70800772A70002434000048680000121A002E0A94000DD034001BA06800080D10007B78F000258400004B08000012C20008E1E80002B50000056A0000015A800015A80000056A00000AD4000002B508C98043026D9BB0054115E0016B6278137CD4800550E6600BA722800302B6013BCE1A0056933A00BE59F40031D6D002AA57C000B6F42001999F800075BE014040370057E04600C19AD80032CD9002B92D4000BB56C001A5084000797D002BDB51000BD0D2001AD4180007CF60006B5060001F3D800047DC000011F7013E10B800574D5C00C088C0003284F002B45C6000BA096001A30CC00078F1002BE816000BD70E001AEA840007D708006BAA10001F5C200048680000121A002CDFAF000C198E001BA06800080D10006E81A000203440004B08000012C20007A7BA00023A1E00056A0000015A800015A80000056A00000AD4000002B50144FC430060CD6C00C19AD80039A24002B5E7E000CE2340019C46800078F1002BDB51000D1F9E001A3F3C0007D7080068FCF0001F5C20003EB84000121A002CC15C000D6C04001AD80800080D10006B602000203440004068800012C200075CEA00023A1E0004743C00015A800011D0F000056A00000AD4000002B5002E09C2000DD034001BA06800084A50006E81A000212940004252800013550007A7BA000251160004A22C00016880001288B00005A200000B44000002D10008E1E80002B110000562200001A4000015888000069000000D200000034800015888000069000000D20000003480000348000000D2000001A40000006908ABF3D3025EA8C404E194A0014E8DD01504578005AD89E00BA722800302B60137CD480053F42000AEF5D4002D3F0802F967D000C75B4001999F800075BE013AC5EB0054CCB800B1570C002DEDD003066B6000CB364001A5084000797D002B5E7E000B44E000182B900006F660006B5060001F3D800047DC000011F701381FAE005415EE00AFFAB0002D8E380302230000CA13C001A30CC00078F1002B45C6000B3FAE001825C40006F548006BAA10001F5C200048680000121A002BD833000B62920018904C00071298006E81A000203440004B08000012C20006E81A000203440004B08000012C200015A80000056A00000AD4000002B501411520005F2CFA00B1AB7C00343F0803066B6000E68900019C46800078F1002B92D4000CF2D40017C9740006F5480068FCF0001F5C20003EB84000121A002C13B3000D1F9E001816E400071298006B602000203440004068800012C20006B602000203440004068800012C200011D0F000056A00000AD4000002B5002D2D49000D75420018B678000742F0006E81A000212940004252800013550006E81A000212940004252800013550001288B00005A200000B44000002D10007B78F000251160004A22C000159300015888000069000000D200000034800015888000069000000D20000003480000348000000D2000001A400000069013B5E5B0057815600BE59F400343F0802F967D000D0FC2001CD12000078F1002AA57C000BB63E0019E5A80006F548006796A0001BD520003EB84000121A002AF73E000BCDB4001A3F3C000712980068FCF0001C4A60004068800012C200068FCF0001C4A60004068800012C2000101A200004B080000AD4000002B5002BF862000C17CE001AEA84000742F0006BAA10001D0BC0004252800013550006BAA10001D0BC0004252800013550001094A00004D540000B44000002D1000772A70001FF620004A22C00015930001288B0000564C0000D20000003480001288B0000564C0000D20000003480000348000000D2000001A400000069002CD97A000D6A0C001AD41800080D10006B506000203440004068800013550006B50600020344000406880001355000101A200004D5400009AA800002D10007650900023A1E0004743C000159300011D0F0000564C0000AC98000034800011D0F0000564C0000AC98000034800002B2600000D2000001A4000000690008FB800002B50000056A000001A4000015A80000069000000D200000040000015A80000069000000D2000000400000034800000100000002000000008000015A80000069000000D2000000400000034800000100000002000000008000003480000010000000200000000800000080000000200000004000000010088B01740253CBD404C068F00143068013865280053EA8000AC1C14002C0D701504578005AD89E00BA722800302B6002F967D000C75B4001999F800075BE0135F2850053485400AB5F30002BEA3802C6ADF000B91E00017EAB40006DDE003066B6000CB364001A5084000797D0006B5060001F3D800047DC000011F70131BCAE0052198000A912C0002B420002BFEAC000B73860017B2980006CD780302230000CA13C001A30CC00078F10006BAA10001F5C200048680000121A002B0E6E000B2D9400173CE80006B0D00062D9E0001CC240004248000010920006E81A000203440004B08000012C200015A80000056A00000AD4000002B5013AF7BB005D391400AB5F3000323A9002C55C3000D239C00176B2C0006CD7803066B6000E68900019C46800078F100068FCF0001F5C20003EB84000121A002B5149000CE2340016DC380006B0D000605B90001CC240003984800010920006B602000203440004068800012C200011D0F000056A00000AD4000002B5002C0391000D186600173CE80006CDB000624130001D5540003AAA800010E60006E81A000212940004252800013550001288B00005A200000B44000002D10006E81A000212940004252800013550001288B00005A200000B44000002D100015888000069000000D20000003480000348000000D2000001A400000069013704EB0055C0BC00BA722800323A9002BBD75000BEE3E001A47380006CD7802F967D000D0FC2001CD12000078F10006796A0001BD520003EB84000121A002A94C7000B9EC80019C4680006B0D0005F25D0001980600039848000109200068FCF0001C4A60004068800012C2000101A200004B080000AD4000002B5002B2E9D000BC970001A30CC0006CDB0006097100019DFC0003AAA800010E60006BAA10001D0BC0004252800013550001094A00004D540000B44000002D10006BAA10001D0BC0004252800013550001094A00004D540000B44000002D10001288B0000564C0000D20000003480000348000000D2000001A400000069002C245A000D2842001A50840007D7080060AE40001CC240003984800010E60006B50600020344000406880001355000101A200004D5400009AA800002D10006B50600020344000406880001355000101A200004D5400009AA800002D100011D0F0000564C0000AC98000034800002B2600000D2000001A4000000690007CF60000258400004B080000168800012C2000005A200000B440000034800015A80000069000000D2000000400000034800000100000002000000008000015A80000069000000D20000004000000348000001000000020000000080000034800000100000002000000008000000800000002000000040000000100130648E0052E30400AC1C14002DF15002E9C8A000C8EA4001A47380006CD7802E9C8A000C8EA4001A47380006CD7800734480001E3C40003EB84000121A002979BE000B153000176B2C00060080006711A0001AC340003984800010920006711A0001AC34000398480001092000101A200004B080000AD4000002B50029E7AA000B323A0017B298000611900068C330001B36C0003AAA800010E600068C330001B36C0003AAA800010E60001094A00004D540000B44000002D100068C330001B36C0003AAA800010E60001094A00004D540000B44000002D10001094A00004D540000B44000002D10000348000000D2000001A400000069002B2B08000CCCFC0017EAB40007096800694210001F5C20003984800010E6000694210001F5C20003984800010E6000101A200004D5400009AA800002D1000694210001F5C20003984800010E6000101A200004D5400009AA800002D1000101A200004D5400009AA800002D100002B2600000D2000001A400000069000797D00002434000042480000137800012C2000005A200000B440000034800012C2000005A200000B4400000348000034800000100000002000000008000012C2000005A200000B4400000348000034800000100000002000000008000003480000010000000200000000800000080000000200000004000000010002A31AF000BADFC001999F800070968006667E0001C25A0003EB8400010E60006667E0001C25A0003EB8400010E60000FAE10000439800009AA800002D10006667E0001C25A0003EB8400010E60000FAE10000439800009AA800002D10000FAE10000439800009AA800002D1000026AA00000B4400001A40000006900075BE000020520000486800001378000121A000004DE00000B4400000348000121A000004DE00000B440000034800002D1000000D20000020000000080000121A000004DE00000B440000034800002D1000000D2000002000000008000002D1000000D20000020000000080000008000000020000000400000001000077D9000023EE000047DC000015A800011F70000056A00000AD40000034800011F70000056A00000AD40000034800002B5000000D2000001A40000008000011F70000056A00000AD40000034800002B5000000D2000001A40000008000002B5000000D2000001A400000080000006900000020000000400000001000011F70000056A00000AD40000034800002B5000000D2000001A40000008000002B5000000D2000001A400000080000006900000020000000400000001000002B5000000D2000001A40000008000000690000002000000040000000100000069000000200000004000000010000001000000004000000080000000208654E700248E48004A797A8013BC29812F546200513EFE00A5C608002A2920136CDD80053936000AB8178002BFDB002BC0AB000B616C00175BF80006B1B01504578005AD89E00BA722800302B6002F967D000C75B4001999F800075BE003066B6000CB364001A5084000797D0006B5060001F3D800047DC000011F70129EDAB004FECB800A433000029EDD802A0AF7000AE6440016647400066CC802BA6AE000B5FE4001792E00006CB800060BE70001C25A00040A40000102900302230000CA13C001A30CC00078F10006BAA10001F5C200048680000121A0006E81A000203440004B08000012C200015A80000056A00000AD4000002B5013307BA005AD89E00A690A80030C79002A665C000C8EA400162A6000066CC802BF023000D0FC200173D900006CB80005E6DA0001C25A000384B40001029003066B6000E68900019C46800078F100068FCF0001F5C20003EB84000121A0006B602000203440004068800012C200011D0F000056A00000AD4000002B5002A6DAD000CA13C00165B2800068C10005B1490001B36C000366D80000FAB00060CC70001D0BC0003A17800010E60000FFB100004DE000009BC0000026F0006E81A000212940004252800013550001288B00005A200000B44000002D100015888000069000000D20000003480000348000000D2000001A400000069012FA5F40053936000B5B13C0030C790029FA10000B650800191D4800066CC802B499D000BD428001A1F840006CB80005DB1F000190C0000384B40001029002F967D000D0FC2001CD12000078F10006796A0001BD520003EB84000121A00068FCF0001C4A60004068800012C2000101A200004B080000AD4000002B50029B537000B5FE40019427800068C100059FD700017FA2000366D80000FAB0005EB87000196C40003A17800010E60000E85E0000439800009BC0000026F0006BAA10001D0BC0004252800013550001094A00004D540000B44000002D10001288B0000564C0000D20000003480000348000000D2000001A400000069002AA3FE000CB364001966C800078F10005A2700001AC34000358680000FAB0005E8690001C4A60003894C00010E60000E2530000439800008730000026F0006B50600020344000406880001355000101A200004D5400009AA800002D100011D0F0000564C0000AC98000034800002B2600000D2000001A4000000690006B50600020344000406880001355000101A200004D5400009AA800002D100011D0F0000564C0000AC98000034800002B2600000D2000001A40000006900015A80000069000000D2000000400000034800000100000002000000008000003480000010000000200000000800000080000000200000004000000010012ACF1C00513EFE00A7D500002CA1C002D6C4F000C31E400191D4800066CC802A8733000B65080017DC7C0006211800687E10001B2E0000384B40001029002E9C8A000C8EA4001A47380006CD7800734480001E3C40003EB84000121A0006711A0001AC34000398480001092000101A200004B080000AD4000002B50028D036000AE6440016E70C0005DA00006509E0001A304000366D80000FAB0005D04B00017FA200033BF80000EE70000E85E0000439800009BC0000026F00068C330001B36C0003AAA800010E60001094A00004D540000B44000002D10001094A00004D540000B44000002D10000348000000D2000001A400000069002A0C9E000C75B4001723C00006CB8000659B20001E3C4000358680000FAB0005DAB60001BD520003300C0000EE70000E2530000439800008730000026F000694210001F5C20003984800010E6000101A200004D5400009AA800002D1000101A200004D5400009AA800002D100002B2600000D2000001A400000069000694210001F5C20003984800010E6000101A200004D5400009AA800002D1000101A200004D5400009AA800002D100002B2600000D2000001A40000006900012C2000005A200000B440000034800003480000010000000200000000800000348000001000000020000000080000008000000020000000400000001000293920000B616C0018EB680006CB800063ADA0001B2E00003C7880000FAB0005B7A1000190C000037AA40000EE70000DEA900003B9C00008730000026F0006667E0001C25A0003EB8400010E60000FAE10000439800009AA800002D10000FAE10000439800009AA800002D1000026AA00000B4400001A4000000690006667E0001C25A0003EB8400010E60000FAE10000439800009AA800002D10000FAE10000439800009AA800002D1000026AA00000B4400001A400000069000121A000004DE00000B440000034800002D1000000D2000002000000008000002D1000000D200000200000000800000080000000200000004000000010000686980001F3D80003E7B000012C20000F9EC00004B080000961000002D10000F9EC00004B080000961000002D10000258400000B4400001688000006900011F70000056A00000AD40000034800002B5000000D2000001A40000008000002B5000000D2000001A400000080000006900000020000000400000001000011F70000056A00000AD40000034800002B5000000D2000001A40000008000002B5000000D2000001A400000080000006900000020000000400000001000002B5000000D2000001A40000008000000690000002000000040000000100000069000000200000004000000010000001000000004000000080000000201238009004EF0A600A18340002A8810029D1BA000B28700016F8A80005D22002D6C4F000C31E400191D4800066CC800687E10001B2E0000384B40001029002D6C4F000C31E400191D4800066CC800687E10001B2E0000384B40001029000734480001E3C40003EB84000121A000101A200004B080000AD4000002B500276E68000A7B760015A100000571E0005B1C700017680000308C80000DEB0006509E0001A304000366D80000FAB0000E85E0000439800009BC0000026F0006509E0001A304000366D80000FAB0000E85E0000439800009BC0000026F0001094A00004D540000B44000002D10000348000000D2000001A4000000690028B4B6000C0AD80015F51C00066CC8005BDBA0001B35E000300400000DEB000659B20001E3C4000358680000FAB0000E2530000439800008730000026F000659B20001E3C4000358680000FAB0000E2530000439800008730000026F000101A200004D5400009AA800002D100002B2600000D2000001A400000069000659B20001E3C4000358680000FAB0000E2530000439800008730000026F000101A200004D5400009AA800002D100002B2600000D2000001A400000069000101A200004D5400009AA800002D100002B2600000D2000001A40000006900003480000010000000200000000800000080000000200000004000000010002825E3000AFF6C001815B000066CC8005A7E100018846000366BC0000DEB00063ADA0001B2E00003C7880000FAB0000DEA900003B9C00008730000026F00063ADA0001B2E00003C7880000FAB0000DEA900003B9C00008730000026F0000FAE10000439800009AA800002D1000026AA00000B4400001A40000006900063ADA0001B2E00003C7880000FAB0000DEA900003B9C00008730000026F0000FAE10000439800009AA800002D1000026AA00000B4400001A4000000690000FAE10000439800009AA800002D1000026AA00000B4400001A40000006900002D1000000D20000020000000080000008000000020000000400000001000065DF60001E5F40003CBE8000121A0000DECC0000424800008490000026F0000F9EC00004B080000961000002D10000258400000B440000168800000690000F9EC00004B080000961000002D10000258400000B4400001688000006900002B5000000D2000001A40000008000000690000002000000040000000100000F9EC00004B080000961000002D10000258400000B4400001688000006900002B5000000D2000001A400000080000006900000020000000400000001000002B5000000D2000001A40000008000000690000002000000040000000100000069000000200000004000000010000001000000004000000080000000200270894000A8A48001606B80005D220006056C00019B32000366BC0000DEB0006056C00019B32000366BC0000DEB0000F1E200003EAC00008730000026F0006056C00019B32000366BC0000DEB0000F1E200003EAC00008730000026F0000F1E200003EAC00008730000026F000026AA00000B4400001A4000000690006056C00019B32000366BC0000DEB0000F1E200003EAC00008730000026F0000F1E200003EAC00008730000026F000026AA00000B4400001A4000000690000F1E200003EAC00008730000026F000026AA00000B4400001A400000069000026AA00000B4400001A4000000690000080000000200000004000000010000634120001D6F800036EF000010290000F2FA0000486800008490000026F0000F2FA0000486800008490000026F0000258400000B440000168800000690000F2FA0000486800008490000026F0000258400000B440000168800000690000258400000B4400001688000006900000690000002000000040000000100000F2FA0000486800008490000026F0000258400000B440000168800000690000258400000B4400001688000006900000690000002000000040000000100000258400000B4400001688000006900000690000002000000040000000100000069000000200000004000000010000001000000004000000080000000200060D300001AC6C0003ADF000010290000EB7C000040A4000090D0000026F0000EB7C000040A4000090D0000026F00002434000009BC0000168800000690000EB7C000040A4000090D0000026F00002434000009BC00001688000006900002434000009BC000016880000069000005A2000001A40000040000000100000EB7C000040A4000090D0000026F00002434000009BC00001688000006900002434000009BC000016880000069000005A2000001A400000400000001000002434000009BC000016880000069000005A2000001A4000004000000010000005A2000001A400000400000001000000100000000400000008000000020000EFB2000047DC00008FB800002B5000023EE00000AD4000015A80000069000023EE00000AD4000015A800000690000056A000001A4000003480000010000023EE00000AD4000015A800000690000056A000001A40000034800000100000056A000001A4000003480000010000000D200000040000000800000002000023EE00000AD4000015A800000690000056A000001A40000034800000100000056A000001A4000003480000010000000D2000000400000008000000020000056A000001A4000003480000010000000D200000040000000800000002000000D20000004000000080000000200000020000000080000001000000005F
  | 8 => 0x20C388C480FC7B76F8401C0DF601E3310E040F7AE2E01EDF9DA007D8C734003930F9041BC3C4A01F5153F007FFBB5E003AA37480818F4C0003C06FD800F548E20007B144042594B2201FA0C9700816E84A003B5D460083A8BB0003D1902800FA56300007DD6600850F6A4003DD9FD000FF514800080C6700103073400083B14000252EC400010869040A9C80801ECCFE4007E17A6C0039BCAC00807060C003B87A0000F3FB580007AA0C00829E678003CB016000FA945E0007E676800FEC9C40008193300024A3F80001048E008493C0C003D9EC1800FEE0BC0008093E80105047400084C8D00025ADC000010BF00010990CE0008725380026A8C4000112E90002BBCFC0001370700004DC1C0000228F042594B2202244324007FA95E00041568480816AE900042DE49800F1BCCC0007AA0C00836B22400441E40000F770CA0007E676800F9867C000819330002064CC0001048E008549FE8004527BE800FB3ED40008093E800FF42D800084C8D00021323400010BF000102DBE40008725380021C94E000112E900024D1460001370700004DC1C0000228F008493C0C0044CFD9000F9E4D20007FED3800FE1B5E000843D0800210F4200010ADF00103983C0008797680021E5DA000113EF8002511960001393E00004E4F8000022CE00109C8C00008ADCC80022B73200011AB40002649F600014394000050E50000023F40002B5E1000016F5900005BD64000028D100005BD64000028D100000A34400000489041BC3C4A01FFE319808910C9000415684808058A74003DBD278010B79260007AA0C0081CBA54003EB6FB0011079000007E676800F7C9E0000757698002064CC0001048E00836B224003F8D9D801149EFA0008093E800FC912000077F5C80021323400010BF0000FE135400078FA500021C94E000112E900021C94E000112E900004DC1C0000228F00829E678003F2DAC801133F640007FED3800FB0AD2000773A1800210F4200010ADF000FE70D8000793C980021E5DA000113EF80021E5DA000113EF80004E4F8000022CE00103983C0007BAFF80022B73200011AB400022B73200011AB4000050E50000023F40002601480001351080005BD64000028D100005BD64000028D100000A3440000048900850F6A4004527BE801149EFA0008F955000FB761E0008252280020948A00010ADF000FE1354000848C700021231C000113EF80021231C000113EF800044FBE000022CE00102DBE4000874E900021D3A400011AB400021D3A400011AB4000046AD0000023F400024B2440001351080004D442000028D100004D442000028D100000A344000004890010990CE0008ADCC80022B7320001224000022B73200012240000048900000024F0000260148000140388000500E200002A4B0000500E200002A4B00000A92C000004B30002B5E1000016DC400005B7100000306900005B7100000306900000C1A40000056100005B7100000306900000C1A40000056100000C1A40000056100000158400000099040F7AE2E01F4EB2400808F632003CD0E1808910C90004156848010B79260007AA0C008058A74003D0939800FD3824000744030011079000007E6768002064CC0001048E00816AE90003D94190010042F200075CF3001149EFA0008093E80021323400010BF0000FB761E0007405C8001EDC140000F8C100021C94E000112E900004DC1C0000228F00807060C003D1C1F000FE7F9C00074F35801133F640007FED3800210F4200010ADF000FB0AD200073DDC0001ED8CC0000F8B680021E5DA000113EF80004E4F8000022CE000FE1B5E000752F10001F557C0000FC7C80022B73200011AB4000050E50000023F400022B73200011AB4000050E50000023F400005BD64000028D100000A344000004890083A8BB000441E4000100B0B400083CA3001149EFA0008F95500020948A00010ADF000FC912000082EC60001E6DD40000F8B680021231C000113EF800044FBE000022CE000FF42D8000848C70001EC9B40000FC7C80021D3A400011AB4000046AD0000023F400021D3A400011AB4000046AD0000023F400004D442000028D100000A34400000489001050474000879768001F80F60001028400022B73200012240000048900000024F000022B73200012240000048900000024F00000500E200002A4B00000A92C000004B30002649F6000140388000500E2000028B300005B7100000306900000C1A40000056100005B7100000306900000C1A40000056100000C1A4000005610000015840000009900818F4C0003F4FE300110790000083CA300110790000083CA300023E55400010ADF000F7C9E000077F9B80020BB180000F8B680020BB180000F8B6800044FBE000022CE000F9867C00078E0B80021231C0000FC7C80021231C0000FC7C800046AD0000023F400021231C0000FC7C800046AD0000023F4000046AD0000023F400000A34400000489000FEC9C40007B88980021E5DA0001028400021E5DA00010284000048900000024F000021E5DA00010284000048900000024F0000048900000024F000000A92C000004B3000251196000119718000500E2000028B30000500E2000028B300000C1A4000005610000500E2000028B300000C1A40000056100000C1A400000561000001584000000990010307340008725380021C94E00011AB400021C94E00011AB4000046AD0000024F000021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300024D1460001351080004D442000028B300004D442000028B300000A2CC0000056100004D442000028B300000A2CC0000056100000A2CC00000561000001584000000990002BBCFC00016F5900005BD640000306900005BD640000306900000C1A40000066840005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D9000000144401C0DF601ECF0EE807D85BD0003AF66380808F632003D0009800F985FE00071889008910C90004156848010B79260007AA0C0011079000007E6768002064CC0001048E007FA95E0003C9A84800F8A14A000714AE00100B0B4000769F38001E8E500000F58E001149EFA0008093E80021323400010BF000021C94E000112E900004DC1C0000228F007E17A6C003BD361800F5A1500006FC85800FE7F9C0007588F8001E4F7A0000F38B801133F640007FED3800210F4200010ADF00021E5DA000113EF80004E4F8000022CE000F9E4D2000733860001DD5400000F0630001F80F6000100380000489D80000204600022B73200011AB4000050E50000023F400005BD64000028D100000A3440000048900816E84A0042DE49800F8A14A0007F4340010042F2000847E00001DFD1E0000F38B801149EFA0008F95500020948A00010ADF00021231C000113EF800044FBE000022CE000FB3ED4000825228001D66040000F0630001EC9B4000100380000400E00000204600021D3A400011AB4000046AD0000023F400004D442000028D100000A34400000489000FEE0BC000843D08001DD5400000F3FF0001F557C000104D0000041340000020D900022B73200012240000048900000024F00000500E200002A4B00000A92C000004B300022B73200012240000048900000024F00000500E200002A4B00000A92C000004B300005B7100000306900000C1A40000056100000C1A40000056100000158400000099007FFBB5E003E30B20010B79260007F434000FD382400079D58000211F800000F38B80110790000083CA300023E55400010ADF00020BB180000F8B6800044FBE000022CE000F770CA000772A580020948A0000F0630001E6DD40000E6CB8000400E00000204600021231C0000FC7C800046AD0000023F4000046AD0000023F400000A34400000489000FA945E00078B22000210F420000F3FF0001ED8CC0000E9DF000041340000020D900021E5DA00010284000048900000024F0000048900000024F000000A92C000004B300021E5DA00010284000048900000024F0000048900000024F000000A92C000004B30000500E2000028B300000C1A40000056100000C1A40000056100000158400000099000FF514800084C8D000213234000113EF8001EDC14000100380000400E0000020D900021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900026A8C400014394000050E5000002A4B000050E5000002A4B00000A92C0000056100005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014407D8C734003C57CA800F985FE00075CDE0010B79260007F434000211F800000F38B8010B79260007F434000211F800000F38B80023E55400010ADF000044FBE000022CE000F1BCCC0007250B8001DFD1E0000DADC00020948A0000F0630000400E00000204600020948A0000F0630000400E000002046000046AD0000023F400000A34400000489000F3FB58000735D20001E4F7A0000DD13000210F420000F3FF000041340000020D9000210F420000F3FF000041340000020D9000048900000024F000000A92C000004B3000210F420000F3FF000041340000020D9000048900000024F000000A92C000004B3000048900000024F000000A92C000004B300000C1A40000056100000158400000099000FA5630000819330001E8E500000FB2C800213234000113EF8000400E0000020D9000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC000005610000015840000009900025ADC00001393E0000489D80000253B000050E5000002A4B00000A92C00000561000050E5000002A4B00000A92C0000056100000C1A4000006684000019A1000000B6400050E5000002A4B00000A92C0000056100000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014400F548E200077B0E0002064CC0000FB2C8002064CC0000FB2C800044FBE000020D90002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B30002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900024A3F800011BD100004E4F80000253B00004E4F80000253B00000A92C0000056100004E4F80000253B00000A92C0000056100000A92C000005610000019A1000000B640004E4F80000253B00000A92C0000056100000A92C000005610000019A1000000B640000A92C000005610000019A1000000B64000019A1000000B64000002D900000014400252EC40001370700004DC1C000028D100004DC1C000028D100000A3440000056100004DC1C000028D100000A3440000056100000A34400000561000001584000000B640004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440000A34400000561000001584000000B6400001584000000B64000002D900000014400001584000000B64000002D9000000144000002D9000000144000000510000000243F1EDDBE01E4E27F007B3C3BA0039C8AC007D3AC90003B4747000F15F2A0006D41F007FF8C66003CC7FB000F8C2C8000716A6000FD3F8C00074E2F0001DEC380000F00F008910C90004156848010B79260007AA0C0011079000007E6768002064CC0001048E001149EFA0008093E80021323400010BF000021C94E000112E900004DC1C0000228F007B33F90003A68C6000EF4D860006CBD6000F4707C000708B40001CD7480000E7A6800FCB6B200074D720001E2C880000F3570001EE2260000FB2C800046F4400001F89001133F640007FED3800210F4200010ADF00021E5DA000113EF80004E4F8000022CE00022B73200011AB4000050E50000023F400005BD64000028D100000A34400000489007E8325C00415684800F26A120007BFB4000F650640007F4340001C942E0000E7A6800FE367600083CA30001DCA960000F3570001E382E0000FB2C80003ECB200001F89001149EFA0008F95500020948A00010ADF00021231C000113EF800044FBE000022CE00021D3A400011AB4000046AD0000023F400004D442000028D100000A34400000489000F67B060007FED38001CCE180000EBA10001D4BC40000F3FF00003CFFC00001EB70001EEBFE00010284000040A10000020D90000465C60000253B0000094EC0000042300022B73200012240000048900000024F00000500E200002A4B00000A92C000004B300005B7100000306900000C1A40000056100000C1A40000056100000158400000099007D454FC003CC7FB001055A120007BFB4000F424E600074FFD0001FD0D00000E7A6800FADBEC00078E9400020F28C0000F3570001DFE6E0000E2FB00003ECB200001F8900110790000083CA300023E55400010ADF00020BB180000F8B6800044FBE000022CE00021231C0000FC7C800046AD0000023F4000046AD0000023F400000A34400000489000F2C05800074D720001FFB4E0000EBA10001CF7700000DABC80003CFFC00001EB70001E4F260000E643000040A10000020D9000040A10000020D90000094EC0000042300021E5DA00010284000048900000024F0000048900000024F000000A92C000004B30000500E2000028B300000C1A40000056100000C1A40000056100000158400000099000F767F40008093E8002024FA00010ADF0001D01720000F06300003C18C00001EB70001E3E940000FC7C80003F1F2000020D900003F1F2000020D90000083640000042300021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014407B7E768003B4747000F4002600072D3F801055A120007BFB40001FD0D00000E7A6800F6F49E00074FFD0001E75600000DE9780020F28C0000F35700003ECB200001F890010B79260007F434000211F800000F38B80023E55400010ADF000044FBE000022CE00020948A0000F0630000400E000002046000046AD0000023F400000A34400000489000EE1E80000708B40001D623E0000D5F00001FFB4E0000EBA100003CFFC00001EB70001DCE860000DABC80003A77C00001D73000040A10000020D90000094EC00000423000210F420000F3FF000041340000020D9000048900000024F000000A92C000004B3000048900000024F000000A92C000004B300000C1A40000056100000158400000099000F4640A0007E6768001DA7CE0000F3570002024FA00010ADF00003C18C00001EB70001DFD720000F8B6800039B2E00001D7300003F1F2000020D900000836400000423000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000050E5000002A4B00000A92C0000056100000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014400F01BF600074E2F0001F99DA0000F3570001F99DA0000F357000042B7C00001EB70001D5DA60000E2FB00003E2DA00001D7300003E2DA00001D73000008364000004230002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B3000001584000000990002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900004E4F80000253B00000A92C0000056100000A92C000005610000019A1000000B640000A92C000005610000019A1000000B64000019A1000000B64000002D90000001440020EC50000112E9000044BA4000023F4000044BA4000023F4000008FD0000004B3000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440000A34400000561000001584000000B6400001584000000B64000002D900000014400001584000000B64000002D9000000144000002D900000014400000051000000024078CC4380039C8AC000EBD98E0006E13F000F3438600072D3F8001D73780000D4CA001055A120007BFB40001FD0D00000E7A680020F28C0000F35700003ECB200001F89001055A120007BFB40001FD0D00000E7A680020F28C0000F35700003ECB200001F8900023E55400010ADF000044FBE000022CE000046AD0000023F400000A34400000489000E6F2B00006CBD60001BF2160000C90F0001D3CD60000D5F000003744C00001BBA0001FFB4E0000EBA100003CFFC00001EB7000040A10000020D90000094EC000004230001FFB4E0000EBA100003CFFC00001EB7000040A10000020D90000094EC00000423000048900000024F000000A92C000004B300000C1A40000056100000158400000099000ED75180007AA0C0001C52B80000E7A68001D73CC0000F38B800036B7000001BBA0002024FA00010ADF00003C18C00001EB700003F1F2000020D9000008364000004230002024FA00010ADF00003C18C00001EB700003F1F2000020D900000836400000423000046AD0000024F00000093C0000004B300000A2CC00000561000001584000000990002024FA00010ADF00003C18C00001EB700003F1F2000020D900000836400000423000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000046AD0000024F00000093C0000004B300000A2CC000005610000015840000009900000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014400EA8DD2000716A60001EA8300000E7A68001D100C0000DE9780003CE2E00001BBA0001F99DA0000F357000042B7C00001EB700003E2DA00001D73000008364000004230001F99DA0000F357000042B7C00001EB700003E2DA00001D7300000836400000423000044FBE000020D90000093C0000004B30000093C0000004B3000001584000000990001F99DA0000F357000042B7C00001EB700003E2DA00001D7300000836400000423000044FBE000020D90000093C0000004B30000093C0000004B300000158400000099000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900000A92C000005610000019A1000000B64000019A1000000B64000002D90000001440020319C00010BF0000042FC0000022CE00003E3040000204600000811800000423000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC00000099000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900000A34400000561000001584000000B6400001584000000B64000002D900000014400044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900000A34400000561000001584000000B6400001584000000B64000002D90000001440000A34400000561000001584000000B6400001584000000B64000002D900000014400001584000000B64000002D9000000144000002D90000001440000005100000002400E4C3E40006D41F0001C62240000D4CA0001EA8300000E7A680003CE2E00001BBA0001EA8300000E7A680003CE2E00001BBA000042B7C00001EB7000008364000004230001EA8300000E7A680003CE2E00001BBA000042B7C00001EB700000836400000423000042B7C00001EB7000008364000004230000093C0000004B3000001584000000990001EA8300000E7A680003CE2E00001BBA000042B7C00001EB700000836400000423000042B7C00001EB7000008364000004230000093C0000004B300000158400000099000042B7C00001EB7000008364000004230000093C0000004B3000001584000000990000093C0000004B3000001584000000990000019A1000000B64000002D9000000144001F75980001048E00003D63800001F89000042FC0000022CE00000811800000423000042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000008FD0000004B30000012CC00000099000001584000000B64000002D900000014400042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000008FD0000004B30000012CC00000099000001584000000B64000002D900000014400008FD0000004B30000012CC00000099000001584000000B64000002D900000014400001584000000B64000002D9000000144000002D900000014400000051000000024001EC5100000F00F00004123800001F8900004123800001F89000008B380000042300004123800001F89000008B3800000423000008B38000004230000012CC0000009900004123800001F89000008B3800000423000008B38000004230000012CC00000099000008B38000004230000012CC000000990000012CC000000990000002D90000001440004123800001F89000008B3800000423000008B38000004230000012CC00000099000008B38000004230000012CC000000990000012CC000000990000002D900000014400008B38000004230000012CC000000990000012CC000000990000002D9000000144000012CC000000990000002D9000000144000002D900000014400000051000000024000421A40000228F000008A3C00000489000008A3C0000048900000122400000099000008A3C00000489000001224000000990000012240000009900000026400000014400008A3C0000048900000122400000099000001224000000990000002640000001440000122400000099000000264000000144000002640000001440000005100000002400008A3C0000048900000122400000099000001224000000990000002640000001440000122400000099000000264000000144000002640000001440000005100000002400001224000000990000002640000001440000026400000014400000051000000024000002640000001440000005100000002400000051000000024000000090000000062
  | 9 => 0x3B23B5BBD8CBA425B219D0C47EC0571DC01068813E44016377D8602D197D0C0093C1DAC699D83AE01681164602DE3365800971CA240B991E9A0026946CF004EB099A00118B12C6A80D461016B4884602E5B24280098CC64C0BC49B2E002732FC7005026DA60011E5E7C0BE119990027A141B005193E8E001245CFC014AA58B8004A9B3B000A65FCC00021465C6814B50D0162C9CFC02D49EB0400951420C0B83123200264EC1F004E5B75E00117ECAC0BB026450026FA171005042A420011FAC0C0146055780049944F000A44FFC00020DCCC0BD8A381002783F5500517FF62001241F4C014D33BE8004B380D000A8816C00021B37C015289B18004C71C3000AC85DC00022812C00302B0E00009A23600013446C00003DA7C6A80D46101863D1FA02DCD768800A661EB00B9773DA002A7A052004DB45B600117ECAC0BC0B0A1002B31574004F590420011FAC0C013FE2D180049944F00093289E00020DCCC0BE73F97002BC8F36005071F02001241F4C01467FA08004B380D00096701A00021B37C014ABBE78004C71C300098E38600022812C0029454180009A23600013446C00003DA7C0BD8A381002B966B600500DEEE00122C58C014534A48004AF1BD00095E37A0002194BC014BB05E8004CB12900099625200022A0C40029893380009B29E00013653C00003E10C0152F7498004E64230009CC8460002367FC002AC9D380009FD9E00013FB3C00003FF0C002FD8E08000B313C000166278000047A180005989E000011E86000023D0C00000729C699D83AE016F366C2030C7A3F400A661EB00B819A210027946650054F40A400117ECAC0B9F4267002823F45005662AE80011FAC0C013DCDC780043763700093289E00020DCCC0BC0B0A100289F91D005791E6C001241F4C01434EB380044BFD100096701A00021B37C01451752800454ABB00098E38600022812C002638E180008A04B00013446C00003DA7C0BB02645002867B0B00572CD6C00122C58C014192AD800445FE300095E37A0002194BC01459ABF80045708300099625200022A0C40026589480008A83100013653C00003E10C014BB05E80046BC630009CC8460002367FC0027321180008D9FF00013FB3C00003FF0C002A7E888000995F7000166278000047A180005989E000011E86000023D0C00000729C0BE11999002BC8F36005791E6C0014239380141FD0F80049F5DB00093EBB60002194BC014517528004B203100096406200022A0C40025901880008A83100011506200003E10C014ABBE78004C901700099202E0002367FC0026480B80008D9FF00011B3FE00003FF0C002929CC8000995F7000132BEE000047A180004CAFB800011E86000023D0C00000729C015289B18004E64230009CC84600024435C002732118000910D70001221AE00004185C002A7E8880009E61F00013CC3E000049F980004F30F8000127E6000024FCC00000765C002FD8E08000B2791000164F220000537F0000593C8800014DFC000029BF8000008598000593C8800014DFC000029BF80000085980000A6FE0000021660000042CC000000D5C68813E4401681F57E02E17CDD4009C2CEEC0C31E8FD0029987AC0054F40A400117ECAC0B819A2100272DA770050F78E20010B336C01598ABA00047EB0300093289E00020DCCC0B9773DA00277D5830051D66620010E6BF4015E479B0004907D300096701A00021B37C0141FD0F80042BF3D0008D20820001F9524002638E180008A04B00013446C00003DA7C0B831232002737365005153C2E0010CA34C015CB35B00048B16300095E37A0002194BC014192AD80042AD670008D1D160001F95FC0026589480008A83100013653C00003E10C014534A480043630B0008F29FE00020076C0027321180008D9FF00013FB3C00003FF0C0027321180008D9FF00013FB3C00003FF0C0005989E000011E86000023D0C00000729C0BC49B2E002B315740051F64320012AA0F4015E479B000508E4E00093EBB60002194BC01434EB38004A46870008B5E460001F95FC0025901880008A83100011506200003E10C01467FA08004B20310008CE50600020076C0026480B80008D9FF00011B3FE00003FF0C0026480B80008D9FF00011B3FE00003FF0C0004CAFB800011E86000023D0C00000729C014D33BE8004CB1290008FDD6200020B854002732118000910D70001221AE00004185C002732118000910D70001221AE00004185C0004F30F8000127E6000024FCC00000765C002AC9D380009E61F00013CC3E000047784000593C8800014DFC000029BF8000008598000593C8800014DFC000029BF80000085980000A6FE0000021660000042CC000000D5C0B991E9A00287BD3D005662AE80012AA0F401598ABA0004AA83D000A11C9C0002194BC013DCDC780044C0BB000948D0E0001F95FC0025234380007E57F00011506200003E10C013FE2D1800453EC100096406200020076C002590188000801DB00011B3FE00003FF0C002590188000801DB00011B3FE00003FF0C00046CFF80000FFC3000023D0C00000729C01460557800469F0B00099625200020B85400265894800082E150001221AE00004185C00265894800082E150001221AE00004185C0004886B800010617000024FCC00000765C0029893380008D45F00013CC3E0000477840004F30F800011DE1000029BF80000085980004F30F800011DE1000029BF80000085980000A6FE0000021660000042CC000000D5C014AA58B8004C71C300098E3860002367FC002638E180008D9FF00011B3FE00004185C002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C002945418000995F7000132BEE0000477840004CAFB800011DE1000023BC20000085980004CAFB800011DE1000023BC200000859800008EF08000021660000042CC000000D5C00302B0E0000B313C0001662780000537F00005989E000014DFC000029BF8000009C400005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D0000000190674311FB0162F5D2A02D1CC6BC0097E972C0B85F37500272701B004FE5DA20010598F40C31E8FD0029987AC0054F40A400117ECAC01598ABA00047EB0300093289E00020DCCC0B735DA20026EDE9B004FA75760010536FC0147D90C8004407BD0008BD3760001F3404015E479B0004907D300096701A00021B37C002638E180008A04B00013446C00003DA7C0B527AC1002679627004EC7E9600102149401454F0B8004377930008AD3620001EF9CC015CB35B00048B16300095E37A0002194BC0026589480008A83100013653C00003E10C014037BB8004257D50008900CA0001EA6740023F758800081D350001228D400003A1C40027321180008D9FF00013FB3C00003FF0C0005989E000011E86000023D0C00000729C0B96C90A002A7A052004FA75760012165FC014759988004B048F000897C960001EF9CC015E479B000508E4E00093EBB60002194BC0025901880008A83100011506200003E10C0141C7C080049F5DB00087329A0001EA67400233941800081D35000103A6A00003A1C40026480B80008D9FF00011B3FE00003FF0C0004CAFB800011E86000023D0C00000729C0145FFD88004AF1BD0008900CA0001F10940023CA7F800083EF5000107DEA00003B0C4002732118000910D70001221AE00004185C0004F30F8000127E6000024FCC00000765C002732118000910D70001221AE00004185C0004F30F8000127E6000024FCC00000765C000593C8800014DFC000029BF80000085980000A6FE0000021660000042CC000000D5C0B78CD960027D73F70054F40A40012165FC0143DE3880045A82700096091E0001EF9CC01598ABA0004AA83D000A11C9C0002194BC0025234380007E57F00011506200003E10C013D641080044582D00093EBB60001EA6740022D7918000765D2000103A6A00003A1C4002590188000801DB00011B3FE00003FF0C00046CFF80000FFC3000023D0C00000729C01410A9080045236100095E37A0001F109400234745800077CF4000107DEA00003B0C400265894800082E150001221AE00004185C0004886B800010617000024FCC00000765C00265894800082E150001221AE00004185C0004886B800010617000024FCC00000765C0004F30F800011DE1000029BF80000085980000A6FE0000021660000042CC000000D5C01464FA38004B380D00096701A00022A0C400234820800081D35000103A6A00003B0C4002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C0004CAFB800011DE1000023BC200000859800008EF08000021660000042CC000000D5C002B217700009FD9E00013FB3C000049F980004FECF0000127E6000024FCC0000085980005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D00000001900B465F430026C6D57004FE5DA20010E5AB40153D02900048597F00096091E0001EF9CC0153D02900048597F00096091E0001EF9CC0028472700008652F00011506200003E10C0136D16D80041DCA5000897C960001C38C00024FAED80007A99D000103A6A00003A1C40024FAED80007A99D000103A6A00003A1C400046CFF80000FFC3000023D0C00000729C01396DD780042688B0008AD3620001C7BB0002578DE80007C425000107DEA00003B0C4002578DE80007C425000107DEA00003B0C40004886B800010617000024FCC00000765C002578DE80007C425000107DEA00003B0C40004886B800010617000024FCC00000765C0004886B800010617000024FCC00000765C0000A6FE0000021660000042CC000000D5C01409B6980049944F0008BD3760001FDD3C00259C0680008A831000103A6A00003B0C400259C0680008A831000103A6A00003B0C400046CFF800010617000020C2E00000765C00259C0680008A831000103A6A00003B0C400046CFF800010617000020C2E00000765C00046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C002A205B00009B29E0001228D40000421080004FECF0000127E6000024FCC0000085980004FECF0000127E6000024FCC0000085980000A6FE000002710000004E20000000FA00004FECF0000127E6000024FCC0000085980000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D0000000190013AC266800449C0D00093289E0001FDD3C0024CA2780007F74F00011506200003B0C40024CA2780007F74F00011506200003B0C40004541880000EC31000020C2E00000765C0024CA2780007F74F00011506200003B0C40004541880000EC31000020C2E00000765C0004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C002913FF00008E33200013653C0000421080004D94F000010842000024FCC0000085980004D94F000010842000024FCC000008598000093F3000002166000004E20000000FA00004D94F000010842000024FCC000008598000093F3000002166000004E20000000FA0000093F3000002166000004E20000000FA0000013880000003E80000007D0000000190002997F300009A23600013446C000047A180004D11B000011E86000023D0C0000085980004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA00004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA000008F430000021660000042CC000000FA0000010B30000003E80000007D00000001900004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA000008F430000021660000042CC000000FA0000010B30000003E80000007D000000019000008F430000021660000042CC000000FA0000010B30000003E80000007D0000000190000010B30000003E80000007D0000000190000001F40000000640000000C800000002865D212D9015DB86A602C5EBA5400952E1A40B40FABF002628F39004D8DAAE000FCD4040B79B361002706BEB004FAE7EE0010563540143DE9E80043217D00089381A0001E92F40C31E8FD0029987AC0054F40A400117ECAC01598ABA00047EB0300093289E00020DCCC015E479B0004907D300096701A00021B37C002638E180008A04B00013446C00003DA7C0B164E7E0025A6C8B004CF2C4E000FBC6DC0139B9B280040E85500084D1160001DA03C01433D85800431C3D0008A46C20001EF4A400234F8580007F74F00011C664000038E14015CB35B00048B16300095E37A0002194BC0026589480008A83100013653C00003E10C0027321180008D9FF00013FB3C00003FF0C0005989E000011E86000023D0C00000729C0B5A44230029987AC004DDBD360011AA8FC013BEAC180048597F00083B94A0001DA03C0144FC8E8004AA83D00088B05A0001EF4A400229F6080007F74F0000FEE9E000038E14015E479B000508E4E00093EBB60002194BC0025901880008A83100011506200003E10C0026480B80008D9FF00011B3FE00003FF0C0004CAFB800011E86000023D0C00000729C013C1FAA80048B16300084AFAA0001E16D40021B18580007C4250000F884A00003797400235E31800082E15000105C2A00003B0C400046A2F8000108420000210840000069B4002732118000910D70001221AE00004185C0004F30F8000127E6000024FCC00000765C000593C8800014DFC000029BF80000085980000A6FE0000021660000042CC000000D5C0B408B23002706BEB005330F580011AA8FC01396D3B800432EC100090B2FE0001DA03C01411FA2800452ED100095507A0001EF4A40022605D8000748C80000FEE9E000038E1401598ABA0004AA83D000A11C9C0002194BC0025234380007E57F00011506200003E10C002590188000801DB00011B3FE00003FF0C00046CFF80000FFC3000023D0C00000729C0137D0B8800431C3D0009162C60001E16D4002156B3800070DEE0000F884A0000379740022B84180007626C000105C2A00003B0C40004170A80000EC310000210840000069B400265894800082E150001221AE00004185C0004886B800010617000024FCC00000765C0004F30F800011DE1000029BF80000085980000A6FE0000021660000042CC000000D5C013D0A0D8004907D3000920FA60002194BC00215F9E80007A99D0000F533A0000379740022A55D8000801DB0001003B600003B0C4000400ED80000EC3100001D8620000069B4002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C0004CAFB800011DE1000023BC200000859800008EF08000021660000042CC000000D5C002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C0004CAFB800011DE1000023BC200000859800008EF08000021660000042CC000000D5C0005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D00000001900B1BBEC3002628F39004E4E036001083A74014CC3D600046AA3F00090B2FE0001DA03C013CA332800432EC10008B504E0001C9EA80025541E80007BD290000FEE9E000038E140153D02900048597F00096091E0001EF9CC0028472700008652F00011506200003E10C0024FAED80007A99D000103A6A00003A1C400046CFF80000FFC3000023D0C00000729C0132760F80040E85500086EF260001BA560002458B18000785B50000F884A00003797400222FF1800070DEE0000EF9E80000359D00004170A80000EC310000210840000069B4002578DE80007C425000107DEA00003B0C40004886B800010617000024FCC00000765C0004886B800010617000024FCC00000765C0000A6FE0000021660000042CC000000D5C013997E380047EB03000880F7A0001EF4A4002483E980008652F0000F533A00003797400225FE880007E57F0000ECBA40000359D0000400ED80000EC3100001D8620000069B400259C0680008A831000103A6A00003B0C400046CFF800010617000020C2E00000765C00046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C00259C0680008A831000103A6A00003B0C400046CFF800010617000020C2E00000765C00046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C0004FECF0000127E6000024FCC0000085980000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D00000001900134A36780043217D0008FD6060001EF4A40023F58180007BD2900010CA5E0000379740021BB1B8000748C80000FCAFE0000359D00003F2BF80000D67400001D8620000069B40024CA2780007F74F00011506200003B0C40004541880000EC31000020C2E00000765C0004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C0024CA2780007F74F00011506200003B0C40004541880000EC31000020C2E00000765C0004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C0004D94F000010842000024FCC000008598000093F3000002166000004E20000000FA0000093F3000002166000004E20000000FA0000013880000003E80000007D000000019000254D9D80008A04B00011409600003FF0C0004502580000FFC300001FF8600000765C0004502580000FFC300001FF8600000765C00007FE1800001D97000003B2E000000D5C0004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA000008F430000021660000042CC000000FA0000010B30000003E80000007D00000001900004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA000008F430000021660000042CC000000FA0000010B30000003E80000007D000000019000008F430000021660000042CC000000FA0000010B30000003E80000007D0000000190000010B30000003E80000007D0000000190000001F40000000640000000C80000000280AE3B80200254B869004BF4B96000FE7B94013859DD800420E9D000872D5A0001B7FE0014CC3D600046AA3F00090B2FE0001DA03C0025541E80007BD290000FEE9E000038E14014CC3D600046AA3F00090B2FE0001DA03C0025541E80007BD290000FEE9E000038E140028472700008652F00011506200003E10C00046CFF80000FFC3000023D0C00000729C012A28418003EF1B7000810A4A0001A2DA00021946980006E9580000E3DD8000032CD0002458B18000785B50000F884A0000379740004170A80000EC310000210840000069B4002458B18000785B50000F884A0000379740004170A80000EC310000210840000069B40004886B800010617000024FCC00000765C0000A6FE0000021660000042CC000000D5C013198C980045FB2B000829B7E0001DA03C0021CD7E80007BE730000E1C60000032CD0002483E980008652F0000F533A000037974000400ED80000EC3100001D8620000069B4002483E980008652F0000F533A000037974000400ED80000EC3100001D8620000069B400046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C002483E980008652F0000F533A000037974000400ED80000EC3100001D8620000069B400046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C00046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C0000A6FE000002710000004E20000000FA0000013880000003E80000007D0000000190012E39448004158D50008BF6560001DA03C0021666D8000727AA0000F7CE6000032CD00023F58180007BD2900010CA5E0000379740003F2BF80000D67400001D8620000069B40023F58180007BD2900010CA5E0000379740003F2BF80000D67400001D8620000069B40004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C0023F58180007BD2900010CA5E0000379740003F2BF80000D67400001D8620000069B40004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C0004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C000093F3000002166000004E20000000FA0000013880000003E80000007D000000019000248B9F800086CDF00010D9BE00003E10C0003F2A480000E87100001D0E20000069B40004502580000FFC300001FF8600000765C00007FE1800001D97000003B2E000000D5C0004502580000FFC300001FF8600000765C00007FE1800001D97000003B2E000000D5C00008F430000021660000042CC000000FA0000010B30000003E80000007D00000001900004502580000FFC300001FF8600000765C00007FE1800001D97000003B2E000000D5C00008F430000021660000042CC000000FA0000010B30000003E80000007D000000019000008F430000021660000042CC000000FA0000010B30000003E80000007D0000000190000010B30000003E80000007D0000000190000001F40000000640000000C8000000028012783B58003F350100082CC7A0001B7FE00022FD9580007680F0000F7CE6000032CD00022FD9580007680F0000F7CE6000032CD00004329780000DE5D00001D8620000069B40022FD9580007680F0000F7CE6000032CD00004329780000DE5D00001D8620000069B40004329780000DE5D00001D8620000069B40000830B800001D970000042CC000000D5C0022FD9580007680F0000F7CE6000032CD00004329780000DE5D00001D8620000069B40004329780000DE5D00001D8620000069B40000830B800001D970000042CC000000D5C0004329780000DE5D00001D8620000069B40000830B800001D970000042CC000000D5C0000830B800001D970000042CC000000D5C000013880000003E80000007D00000001900023CBCF8000837330000F9A02000038E140004366F80000F84300001D0E20000069B40004366F80000F84300001D0E20000069B400007FE1800001D97000003B2E000000D5C0004366F80000F84300001D0E20000069B400007FE1800001D97000003B2E000000D5C00007FE1800001D97000003B2E000000D5C000010B30000003E80000007D00000001900004366F80000F84300001D0E20000069B400007FE1800001D97000003B2E000000D5C00007FE1800001D97000003B2E000000D5C000010B30000003E80000007D000000019000007FE1800001D97000003B2E000000D5C000010B30000003E80000007D0000000190000010B30000003E80000007D0000000190000001F40000000640000000C80000000280023162580007A4BD000106E66000038E1400041B9980000E38500001F0860000069B400041B9980000E38500001F0860000069B400007C21800001A6D000003B2E000000D5C00041B9980000E38500001F0860000069B400007C21800001A6D000003B2E000000D5C00007C21800001A6D000003B2E000000D5C00000ECB8000003570000007D000000019000041B9980000E38500001F0860000069B400007C21800001A6D000003B2E000000D5C00007C21800001A6D000003B2E000000D5C00000ECB8000003570000007D000000019000007C21800001A6D000003B2E000000D5C00000ECB8000003570000007D000000019000000ECB8000003570000007D0000000190000001F40000000640000000C8000000028000428CB80000F69F00001ED3E00000729C00007B4F800001CA700000394E000000D5C00007B4F800001CA700000394E000000D5C00000E538000003570000006AE00000019000007B4F800001CA700000394E000000D5C00000E538000003570000006AE00000019000000E538000003570000006AE000000190000001AB8000000640000000C800000002800007B4F800001CA700000394E000000D5C00000E538000003570000006AE00000019000000E538000003570000006AE000000190000001AB8000000640000000C800000002800000E538000003570000006AE000000190000001AB8000000640000000C8000000028000001AB8000000640000000C80000000280000003200000000A0000000140000000063
  | 10 => 0x2EBDE6A8F6245CF1DF9126A8DC4C00E106B7784A786CAA403948CE3701D0864DC001597E69C4B3068660039F5314501D7E817F001609A6040772648C80059D86D9002DBF2C500024B4B7C4BC39F86C03A6DC21101DC4B482801642F9BC078BDACE6005B281BA002E8539B8002561C64079C4A98A005C0F3CA002F44CDE800261746400BF6348A0009B462D00055AC6E80003E4EDC4A346950603931B12901D265FBE8015C64E1807660834E00594BF1C002D96EC100024A140C078062526005AB62FE002E980ED000258CD4400BD0E87400099691800054C10C80003DA3AC07980B5E6005BD98E3002F3F7888002613E4000C0D80C60009C840F00056B86D80003F11C400C3B26E60009EDDCB00058A035800040748400187C4EE00011CEC500008E76280000679BC4BC39F86C03E551D7D01D742658801808B2000772071BA0061FE3C6002D3E2EA80024A140C078A117AA00637F2A8002E1C059800258CD4400B9CB1A60009969180004CB48C00003DA3AC07A08BEF40064BC9F3002EB04188002613E4000BD47E860009C840F0004E420780003F11C400BF8D56E0009EDDCB0004F6EE58000407484001548A1800011CEC500008E76280000679BC07980B5E60064521AE002E7B5D380025EA7AC00BC9D23A0009C00720004E003900003EDDB000C0196560009F5D480004FAEA4000040ACB800156999400011EB2100008F590800006840C00C3FECEE000A29FB1000514FD8800042039C001601DE8000126ABF00009355F800006B27400185AA1A0001469370000A349B8000076C1400028D26E00001DB0500000ED82800000ACBC4B306866003B05970A01F2A8EBE801808B200076565D96005BFA7FC0030FF1E300024A140C077696E6E005D289F80031BF954000258CD4400B8A941E0008DECF50004CB48C00003DA3AC078A117AA005E2D3F500325E4F98002613E4000BB8FEB20009061E40004E420780003F11C400BC85BE20009172240004F6EE580004074840013DBB96000101D2100008E76280000679BC078062526005DB64C90032290D700025EA7AC00BAA7FBE0008FAC220004E003900003EDDB000BCD4A2200091BF7C0004FAEA4000040ACB80013EBA90000102B2E00008F590800006840C00C01965600094452D000514FD8800042039C001453F620001080E700009355F800006B2740015DDDB200011BC820000A349B8000076C1400028D26E00001DB0500000ED82800000ACBC079C4A98A0064BC9F300325E4F98002996D1800BAD918E0009A21D10004D10E880003EDDB000BC85BE20009C61830004E30C1800040ACB800138C306000102B2E000081597000006840C00BF8D56E0009F24F30004F9279800042039C0013E49E60001080E7000084073800006B27400153D2CA00011BC8200008DE410000076C1400023790400001DB0500000ED82800000ACBC00C3B26E6000A29FB1000514FD88000437970001453F6200010DE5C000086F2E000006D9200015DDDB20001243DC0000921EE000007A4CC0002487B800001E93300000F499800000B1E400185AA1A000145B090000A2D8480000887AC00028B6120000221EB0000110F5800000C68400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C4A786CAA4039FC3EBB01D9F9C5F8016B5DBF407CAA3AFA006022C800030FF1E300024A140C076565D96005B235AC002EF19E98002326EF400C6FE5500009633510004CB48C00003DA3AC0772071BA005BCAEAA002F667B280023896B400C9793E6000984F900004E420780003F11C400BAD918E0008C9B1800049F01F00003B89B40013DBB96000101D2100008E76280000679BC07660834E005B35396002F214A68002352AA800C8A435C00097A9EB0004E003900003EDDB000BAA7FBE0008C7D3000049F22F00003B8DD40013EBA90000102B2E00008F590800006840C00BC9D23A0008DE36B0004AF08400003C5458001453F620001080E700009355F800006B274001453F620001080E700009355F800006B27400028D26E00001DB0500000ED82800000ACBC078BDACE600637F2A8002F7766680026D7AAC00C9793E6000A65B460004D10E880003EDDB000BB8FEB20009ABD89000491B0A00003B8DD400138C306000102B2E000081597000006840C00BD47E860009C618300049D9E280003C54580013E49E60001080E7000084073800006B2740013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC00C0D80C60009F5D480004B461C00003D840C001453F6200010DE5C000086F2E000006D920001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E4001601DE80001243DC0000921EE00000768A400028B6120000221EB0000110F5800000C68400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C0772648C8005DE1A4D0031BF95400026D7AAC00C6FE5500009B5EAB000532DA300003EDDB000B8A941E0009062470004D5EC480003B8DD4001357B120000EE375000081597000006840C00B9CB1A6000915D420004E30C180003C545800138C3060000F1516000084073800006B27400138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC00BD0E87400093FFD30004FAEA400003D840C0013EBA900000F6103000086F2E000006D9200013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E4001569994000107BF60000921EE00000768A40002487B800001DA290000110F5800000C6840002487B800001DA290000110F5800000C6840000443D60000031A10000018D0800000120C00BF6348A0009EDDCB0004F6EE5800042039C0013DBB960001080E7000084073800006D9200013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E4001548A1800011BC8200008DE4100000768A400023790400001DA2900000ED14800000C68400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C00187C4EE0001469370000A349B80000887AC00028D26E0000221EB0000110F5800000E4C400028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC00028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E449AA371300393AD61901D0CF84B80162630F00767E717E005B13082002E60D56800227BE0407CAA3AFA006022C800030FF1E300024A140C00C6FE5500009633510004CB48C00003DA3AC075D09962005A9D04A002E414ED8002272F3000BDDD99A0008EF768000494CAB00003ADE8400C9793E6000984F900004E420780003F11C40013DBB96000101D2100008E76280000679BC074997EFA0059A4260002DCA8768002212C9000BC8529A0008DE34A00048D3A000003A7B8400C8A435C00097A9EB0004E003900003EDDB00013EBA90000102B2E00008F590800006840C00B9ED74E0008BD959000480350000039F9100012D18700000F44020000873958000062584001453F620001080E700009355F800006B27400028D26E00001DB0500000ED82800000ACBC07712D20A0061FE3C6002E414ED80025C074C00BD99ECA0009C0E3D000482F0300003A7B8400C9793E6000A65B460004D10E880003EDDB000138C306000102B2E000081597000006840C00BAC10620009A21D10004725A8800039F91000127678A0000F440200007A20100000625840013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC00BCFDE220009C007200048035000003AAF980012BC2100000F7E0400007BF020000063CB8001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E4001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C075FA05FC005C87FF70030FF1E300025C074C00BBC67A60009206830004E071E80003A7B8400C6FE5500009B5EAB000532DA300003EDDB0001357B120000EE375000081597000006840C00B8701660008F9E360004D10E8800039F910001246C280000E0D4200007A201000006258400138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC00BA603B40009123A30004E003900003AAF9800127C8BC0000E35BC00007BF020000063CB80013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E40013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E40002487B800001DA290000110F5800000C6840000443D60000031A10000018D0800000120C00BD1337A0009C840F0004E4207800040ACB800127C07C0000F440200007A2010000063CB80013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E40013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C0016280D6000126ABF00009355F800007A4CC00024D57E00001E93300000F499800000C68400028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC00028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E4074219370005A498B1002E60D56800238600C00C3FC78C0009701D30004E071E80003A7B8400C3FC78C0009701D30004E071E80003A7B840014CB68C0000FB76C000081597000006840C00B4F8BAA0008AE8AE000482F03000035DAC80013443A20000E7E4400007A20100000625840013443A20000E7E4400007A20100000625840002101CE00001AC9D00000ED82800000ACBC00B65BB040008BF5D600048D3A000003650580013800E40000EABE600007BF020000063CB80013800E40000EABE600007BF020000063CB800021BCB800001B64800000F499800000B1E40013800E40000EABE600007BF020000063CB800021BCB800001B64800000F499800000B1E400021BCB800001B64800000F499800000B1E40000443D60000031A10000018D0800000120C00BA14E6E000996918000494CAB00003C070000139081E000102B2E00007A2010000063CB800139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E400139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C0015AE1B600011EB21000087395800006E7BC00024D57E00001E93300000F499800000C68400024D57E00001E93300000F499800000C6840000443D6000003931000001C9880000014CC00024D57E00001E93300000F499800000C6840000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E400B6FCB14000901D920004CB48C00003C070000132D2300000F01C00000815970000063CB800132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00153043200010921700008F590800006E7BC00023D64200001B9EF00000F499800000C68400023D64200001B9EF00000F499800000C68400003D2660000031A1000001C9880000014CC00023D64200001B9EF00000F499800000C68400003D2660000031A1000001C9880000014CC00003D2660000031A1000001C9880000014CC00000726200000053300000029980000001E400156B1BA00011CEC500008E7628000076C14000239D8A00001DB0500000ED82800000C684000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C48B9E3BF203875AD8001C9D6B0C8015C98AB4073F87D760058FAF16002D24C5880021715480760B2E14005ACF069002E43FFB800227644C00BBC349A0008D3E4A000480EC9000039CA2407CAA3AFA006022C800030FF1E300024A140C00C6FE5500009633510004CB48C00003DA3AC00C9793E6000984F900004E420780003F11C40013DBB96000101D2100008E76280000679BC0726362520057E50FB002CD21300002151A6C00B66A72C00089067100045FAEB0000382EAC00BB6C9920008D35860004891D180003A73C800127FFA60000F01C000008490B800006069400C8A435C00097A9EB0004E003900003EDDB00013EBA90000102B2E00008F590800006840C001453F620001080E700009355F800006B27400028D26E00001DB0500000ED82800000ACBC074DB8422006022C80002D4E82500024F36E400B795D540009701D30004574570000382EAC00BC5A7EA0009B5EAB00047CF1B00003A73C800122BA840000F01C00000780E0000006069400C9793E6000A65B460004D10E880003EDDB000138C306000102B2E000081597000006840C0013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC00B7B31C600097A9EB00045ECAC800038FCEC0011BC6D60000EABE60000755F3000005E7A4001288A5A0000F610300007B0818000063CB800020F7EC00001B9EF00000DCF7800000A0B4001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C073EA628A005ACF06900301164000024F36E400B646B580008D551B0004B80E98000382EAC00BA513F0000911FA40004DAF5580003A73C800120C48E0000DD9F40000780E0000006069400C6FE5500009B5EAB000532DA300003EDDB0001357B120000EE375000081597000006840C00138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC00B56C5FC0008D35860004BD4F5800038FCEC00118FA600000D77150000755F3000005E7A4001237EF80000E081A00007B0818000063CB80001EC206000018F2E00000DCF7800000A0B40013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E40002487B800001DA290000110F5800000C6840000443D60000031A10000018D0800000120C00B81E794000984F900004C27C800003EDDB00011936300000E7E44000073F22000005E7A400122E4480000F1516000078A8B0000063CB80001E2A2C000018F2E00000C797000000A0B40013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C0013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C00028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E4072919C6E0058FAF16002D8984100022CB40000C04590000093CDB90004B80E98000382EAC00B7F4FF80008D551B0004903418000367F4400136BD560000E9CF20000780E0000006069400C3FC78C0009701D30004E071E80003A7B840014CB68C0000FB76C000081597000006840C0013443A20000E7E4400007A20100000625840002101CE00001AC9D00000ED82800000ACBC00B297E3800089067100046F1A5000034D97C0012F53D60000E3F3B0000755F3000005E7A40011F58440000D7715000071ADE000005B8600001EC206000018F2E00000DCF7800000A0B40013800E40000EABE600007BF020000063CB800021BCB800001B64800000F499800000B1E400021BCB800001B64800000F499800000B1E40000443D60000031A10000018D0800000120C00B650374000963351000477BB400003A73C8001309F200000FB76C000073F22000005E7A400120C3C80000EE3750000706A1000005B8600001E2A2C000018F2E00000C797000000A0B400139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C00139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C00024D57E00001E93300000F499800000C6840000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E400B3B0DB20008D3E4A0004B19A880003A73C80012C66A20000E9CF200007DBB6000005E7A40011BD9EA0000DD9F40000771BA800005B8600001DC6EA000016E1800000C797000000A0B400132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00023D64200001B9EF00000F499800000C68400003D2660000031A1000001C9880000014CC00003D2660000031A1000001C9880000014CC00000726200000053300000029980000001E4001368C5A000101D21000080E90800006B274000203A4200001AC9D00000D64E800000B1E4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C070835BBC0057262AD002C4C61E00021A2F5800B5AEDFA0008B2D00000470C0180003493E000C04590000093CDB90004B80E98000382EAC00136BD560000E9CF20000780E0000006069400C04590000093CDB90004B80E98000382EAC00136BD560000E9CF20000780E000000606940014CB68C0000FB76C000081597000006840C0002101CE00001AC9D00000ED82800000ACBC00AE3270C00085469B00044259200003257040011A95540000D365F00006CA0B00000572C40012F53D60000E3F3B0000755F3000005E7A40001EC206000018F2E00000DCF7800000A0B40012F53D60000E3F3B0000755F3000005E7A40001EC206000018F2E00000DCF7800000A0B400021BCB800001B64800000F499800000B1E40000443D60000031A10000018D0800000120C00B217CDE00092850300044E5E60000382EAC0011C4B5A0000E9EE100006BB5900000572C4001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B4001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C0002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E400B04D30200089D9130004942818000382EAC00119377A0000D9FD1000074F7080000572C40012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B40012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C0012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00003D2660000031A1000001C9880000014CC00000726200000053300000029980000001E400130BA320000FC47100007E238800006840C0001DC4DA00001896100000C4B0800000A0B4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C00ACBF34E00085C55200044F7C080003493E0001250A060000E0BAB000074F7080000572C4001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B4001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B40001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B40001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C0001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C000036C90000002C790000018D0800000120C00000726200000053300000029980000001E40012B0E320000F68EB000075BD080000606940001F88E200001A10300000C4B0800000A0B40001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C0001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C00003593A000002C7900000163C800000120C00000634200000053300000029980000001E40001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C00003593A000002C7900000163C800000120C00000634200000053300000029980000001E400003593A000002C7900000163C800000120C00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C00125A5BE0000E728900007B47580000606940001ED1D60000181A500000D081800000A0B40001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C0001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C00003420600000282D00000163C800000120C0000058F200000048300000029980000001E40001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C00003420600000282D00000163C800000120C0000058F200000048300000029980000001E400003420600000282D00000163C800000120C0000058F200000048300000029980000001E40000058F200000048300000029980000001E4000000A6600000007900000003C800000002C0001F276E000019E6F00000CF37800000ACBC000033CDE000002B2F000001597800000120C000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E4000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E400000565E00000048300000024180000001E400000090600000007900000003C800000002C000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E400000565E00000048300000024180000001E400000090600000007900000003C800000002C00000565E00000048300000024180000001E400000090600000007900000003C800000002C00000090600000007900000003C800000002C0000000F200000000B00000000580000000065
  | 11 => 0x2128EAEA5E05E1C378AC0BE73F5D3802135B5D143017161BB808710371C0111814F14002E90DA403083E589A808884818401157D5DD6002F710FBC0460057C5800C119A8000188C900E000479C51030DB026F9008989092E0117DB9756002FE251D8046DC3D27000C3AECFA0018EE0E4800048D2198047687544800C57261600194BBC2C0004A1544800665465300012D93AC000293E95000006DFC382FEFF69740086E2A99B01128FDD9C002EEEF91004599767C000C0106D200187AAC5C000477F3A00467CB756000C2D901B0018F8FA9A00049240A800653A74B00012A5FEA00028DAF0000006CF28004748ABF9800C515F5100194B2BE20004A14EC80067164F280012FE7DD00029B94D000006F4378006880D3100013422CE0002A92C400000718760000BA915000001F183800003E307000000A5D6830DB026F90091E44B9001153527D2003355DC7C046019171800D0FC94200184EE14C000477F3A0046D06B66800D3ED8E10018BBC6A600049240A800639D94700012A5FEA000254BFD400006CF28004791CE36000D65910A00190490D20004A14EC8006553D2780012FE7DD00025FCFBA00006F437800667518E00013422CE000268459C0000718760000A41F1480001F183800003E307000000A5D6804748ABF9800D587E080018EA887400049CA7580065016DF80012EFF9300025DFF2600006EEF980066BE2D7800135106100026A20C2000071E564000A50E5F80001F46A000003E8D4000000A6CE00068AD9F400013AEDAA000275DB5400007414D8000A94D7B80002014E000004029C000000AB1A0000B9BE2A0000233D600000467AC000000BBF20000119EB0000002EFC8000005DF90000000FA983083E589A808AD9152C0123C89720003355DC7C04595AB4E000C553F4B001A1F9284000477F3A004628E6C3000C7A40C9001A7DB1C200049240A800630BC760001160F89000254BFD400006CF280046D06B66800C9A38B3001ACB22140004A14EC800647832600011A76A600025FCFBA00006F43780064F2EE280011C694D000268459C00007187600009A116700001C61D800003E307000000A5D680467CB756000C8B829E001AB0FC1000049CA7580064072A300011932CB00025DFF2600006EEF9800651D5F100011CFB4F00026A20C2000071E5640009A883080001C795900003E8D4000000A6CE00066BE2D7800121923F000275DB5400007414D80009D76D500001D053600004029C000000AB1A0000A84AEB00001EFDF70000467AC000000BBF20000119EB0000002EFC8000005DF90000000FA98047687544800D65910A001ACB221400050433A000641C91900012BA8E200025751C400006EEF980064F2EE280012FB9E300025F73C6000071E56400097DCF180001C7959000038F2B200000A6CE000667518E000134B53E0002696A7C00007414D80009A5A9F00001D053600003A0A6C00000AB1A0000A3D62F00001EFDF700003DFBEE00000BBF200000F7EFB800002EFC8000005DF90000000FA98006880D3100013AEDAA000275DB5400007671D80009D76D500001D9C7600003B38EC00000AEA58000A84AEB00001FD76300003FAEC600000C11A00000FEBB1800003046800000608D00000010178000B9BE2A0000232944000046528800000D57800001194A200000355E0000006ABC00000011CA00001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B83017161BB80889CD7E60116ABF4180030C56C48048F225C8000CD5771F001A1F9284000477F3A004595AB4E000C3B015800192296BA00044E7B140069F6C70800124902A000254BFD400006CF280046019171800C4F842000195BB02E0004598698006B2C88500012853B200025FCFBA00006F437800641C919000113C2E80002418B00000069A6400009A116700001C61D800003E307000000A5D6804599767C000C3CF6BF00193996E80004535DFC006AC3F0400012729D600025DFF2600006EEF980064072A3000113932B000241AEAA000069B0640009A883080001C795900003E8D4000000A6CE00065016DF800116260D000248E46E00006AF8AC0009D76D500001D053600004029C000000AB1A00009D76D500001D053600004029C000000AB1A0000119EB0000002EFC8000005DF90000000FA98046DC3D27000D3ED8E10019640B560004B6F9B4006B2C8850001410CE800025751C400006EEF9800647832600012CC29600023B9D42000069B06400097DCF180001C7959000038F2B200000A6CE0006553D2780012FB9E30002410F2A00006AF8AC0009A5A9F00001D053600003A0A6C00000AB1A00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA980067164F2800135106100024B4A1C00006CE7280009D76D500001D9C7600003B38EC00000AEA580009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D00000010178000A94D7B80001FD76300003FAEC600000BBAA80001194A200000355E0000006ABC00000011CA00001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B80460057C5800C90EDF3001A7DB1C20004B6F9B40069F6C7080012DBE6D00028219D000006EEF9800630BC7600011A75BF000259852C000069B06400096614B00001A6C19000038F2B200000A6CE000639D94700011C46E200025F73C600006AF8AC00097DCF180001ABE2B00003A0A6C00000AB1A000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA9800653A74B00012102E700026A20C200006CE7280009A883080001B39CA00003B38EC00000AEA580009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D00000010178000A50E5F80001D033100003FAEC600000BBAA80000FEBB1800002EEAA000006ABC00000011CA00000FEBB1800002EEAA000006ABC00000011CA000001AAF000000047280000008E5000000017B800665465300013422CE000268459C00007414D80009A116700001D053600003A0A6C00000AEA580009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C0000010178000A41F1480001EFDF700003DFBEE00000BBAA80000F7EFB800002EEAA000005DD540000011CA00000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B8000BA91500000233D600000467AC000000D5780000119EB000000355E0000006ABC00000014400000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B00000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D8000000002402F9CFD74E0086FB4A320111BC0D48002FABB530045AAFD06000C38C52C0018DB580A00043B5248048F225C8000CD5771F001A1F9284000477F3A00069F6C70800124902A000254BFD400006CF2800454D49F4800C2A88D20018CC734000043A924C0065902D5800117DCB800023CDCF200006889A0006B2C88500012853B200025FCFBA00006F43780009A116700001C61D800003E307000000A5D68044A3F767000C0BAE38001891BF8800042FC2400064E65BA000115EC630002397F6C000067E99C006AC3F0400012729D600025DFF2600006EEF980009A883080001C795900003E8D4000000A6CE00063AA21D0001126C9E000233FD5C00006725D800092D28700001B0A8600003B5C80000009E4C00009D76D500001D053600004029C000000AB1A0000119EB0000002EFC8000005DF90000000FA98045F6E5D5800D0FC9420018CC7340000497F01800656EC0B80012EF83A000234DD66000067E99C006B2C8850001410CE800025751C400006EEF9800097DCF180001C7959000038F2B200000A6CE000641243480012BA8E200022DC20400006725D80009043CA80001B0A86000036150C000009E4C00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA9800652CAF880012EFF93000233FD5C0000684F8800092391B80001B690E000036D21C00000A07200009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D000000101780009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D000000101780001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B80455F5775800C66A9F2001A1F9284000497F01800648A5AE80011D477300025DF074000067E99C0069F6C7080012DBE6D00028219D000006EEF9800096614B00001A6C19000038F2B200000A6CE00062EF1A98001191B3400025751C400006725D80008EE75080001915CF000036150C000009E4C000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA980063E3EA680011BD76C00025DFF260000684F88000906BAA80001958B6000036D21C00000A07200009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D000000101780009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D000000101780000FEBB1800002EEAA000006ABC00000011CA000001AAF000000047280000008E5000000017B800652EF0B00012FE7DD00025FCFBA000071E5640009062C000001B0A86000036150C00000A07200009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B8000AA4B1000002014E000004029C000000C11A0000100A70000003046800000608D00000011CA0000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B00000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D8000000002400446053C5000C2030660018DB580A000459055800687E4A1000125FC0600025DF074000067E99C00687E4A1000125FC0600025DF074000067E99C000A0867400001BBBE6000038F2B200000A6CE000613B853000110B538000234DD66000060820000095D471000019C976000036150C000009E4C000095D471000019C976000036150C000009E4C00000E829B000002AC68000005DF90000000FA980061EAB170001129AB90002397F6C00006144E8000977FC980001A13E2000036D21C00000A0720000977FC980001A13E2000036D21C00000A07200000ECE3B000002BA9600000608D00000010178000977FC980001A13E2000036D21C00000A07200000ECE3B000002BA9600000608D000000101780000ECE3B000002BA9600000608D0000001017800001AAF000000047280000008E5000000017B80063B839200012A5FEA00023CDCF200006A745400097F3EE80001C7959000036150C00000A072000097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C000001017800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B8000A6E53400001F46A000003B5C8000000B0160000100A70000003046800000608D00000011CA0000100A70000003046800000608D00000011CA000001AAF00000005100000000A2000000001B00000100A70000003046800000608D00000011CA000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D800000000240006232403800119FC72000254BFD400006A7454000952FF500001A9D15000038F2B200000A0720000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C0000010178000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B8000A36BC000001D230800003E8D4000000B01600000FA350000002C05800000608D00000011CA00000FA350000002C05800000608D00000011CA00000182340000004728000000A2000000001B000000FA350000002C05800000608D00000011CA00000182340000004728000000A2000000001B000000182340000004728000000A2000000001B0000000288000000006C00000000D800000000240000A4FA5400001F183800003E307000000BBF200000F8C1C000002EFC8000005DF900000011CA00000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000000239400000006C00000000D8000000002400000003600000000090000000012000000000302F0E1BC560085501848010DF69464002EF506DC0444E6BF3000BF6F5DB00184060CC00041D92800456C8A96000C306D740018CD53E400043AC3480064876F9800114C39A000233F8E4000066C7A8048F225C8000CD5771F001A1F9284000477F3A00069F6C70800124902A000254BFD400006CF280006B2C88500012853B200025FCFBA00006F43780009A116700001C61D800003E307000000A5D680437154CD800BD486580018175C7000041A101C0061E7B5F80010D3D660002253572000064306400645C14F000114B5AE000237AED8000067DE7000090817380001A9D1500003A4610000009B658006AC3F0400012729D600025DFF2600006EEF980009A883080001C795900003E8D4000000A6CE00009D76D500001D053600004029C000000AB1A0000119EB0000002EFC8000005DF90000000FA98044C48497000CD5771F00185511A4000481091800627C210000125FC060002216A7000006430640064D1C5980012DBE6D0002323668000067DE700008E237100001A9D150000353A2A000009B658006B2C8850001410CE800025751C400006EEF9800097DCF180001C7959000038F2B200000A6CE00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA9800628AFA880012729D6000224D93C00006583D80008B130680001A13E200003427C400000989A800090C91F80001B39CA000036739400000A07200000E8198800002C05800000580B0000000EAC80009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D000000101780001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B80444240C2000C306D740019AAEE3E00048109180061D80AC000114E8D000024BF80C00006430640063D206480011BAA9000025B7CDA000067DE700008D3ADF800018C0580000353A2A000009B6580069F6C7080012DBE6D00028219D000006EEF9800096614B00001A6C19000038F2B200000A6CE000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA9800616C80D800114B5AE00024E53AC00006583D800089C995800018222D00003427C400000989A80008E7DA78000190E4A000036739400000A07200000D9CE500000281C800000580B0000000EAC80009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D000000101780000FEBB1800002EEAA000006ABC00000011CA000001AAF000000047280000008E5000000017B80062B930B00012853B2000250A76400006EEF9800089E174000019C97600003392EC00000989A80008E34A680001ABE2B0000357C5600000A07200000D5F1580000281C80000050390000000EAC80009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B80009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B8000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D800000000240043881B8E000BF6F5DB0018718A5800044420400066ABB8F800120424600024BF80C00006430640062A9FA5800114E8D000023A8EE60000617FDC00096DF36800019F79C0000353A2A000009B65800687E4A1000125FC0600025DF074000067E99C000A0867400001BBBE6000038F2B200000A6CE000095D471000019C976000036150C000009E4C00000E829B000002AC68000005DF90000000FA9800600836900010D3D6600022BD8C600005ED9200009394EB00001960F600003427C400000989A80008C9965800018222D000032B16C00000945980000D9CE500000281C800000580B0000000EAC8000977FC980001A13E2000036D21C00000A07200000ECE3B000002BA9600000608D000000101780000ECE3B000002BA9600000608D0000001017800001AAF000000047280000008E5000000017B80061D767D000124902A00022FB970000067DE700009429D900001BBBE600003392EC00000989A80008D3B5300001A6C190000322B9E00000945980000D5F1580000281C80000050390000000EAC800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B8000100A70000003046800000608D00000011CA000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D80000000024000608CD40000114C39A0002492054000067DE70000924815000019F79C00003777CC00000989A80008B07C4800018C058000034D83200000945980000D360C80000251660000050390000000EAC8000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B8000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000FA350000002C05800000608D00000011CA00000182340000004728000000A2000000001B000000182340000004728000000A2000000001B0000000288000000006C00000000D80000000024000096C9D600001C61D8000038C3B000000AB1A00000E30EC000002AC6800000558D000000101780000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000000239400000006C00000000D8000000002400000003600000000090000000012000000000300426B6BA2800BBD41B70017D5DA980004230D5800618AD89000111081000022C82AC00005E60D00066ABB8F800120424600024BF80C000064306400096DF36800019F79C0000353A2A000009B6580066ABB8F800120424600024BF80C000064306400096DF36800019F79C0000353A2A000009B658000A0867400001BBBE6000038F2B200000A6CE00000E829B000002AC68000005DF90000000FA98005DDDF220001068407000217E12000005AC6300008A6BBF800017B648000030A274000008DE780009394EB00001960F600003427C400000989A80000D9CE500000281C800000580B0000000EAC80009394EB00001960F600003427C400000989A80000D9CE500000281C800000580B0000000EAC80000ECE3B000002BA9600000608D0000001017800001AAF000000047280000008E5000000017B8005FC4A3B00011DFCE800021D492600006430640008B30D3000019FA670000304100000008DE780009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B80009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B800001AAF00000005100000000A2000000001B0000000288000000006C00000000D800000000240005EE21F780010EB0D200023BF9D0000064306400089CF628000185FF7000033F4CE000008DE78000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC8000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B8000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000182340000004728000000A2000000001B0000000288000000006C00000000D800000000240000942A8900001BD0DE000037A1BC00000A6CE00000D34C80000027930000004F260000000EAC80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000000239400000006C00000000D800000000240000000360000000009000000001200000000030005D21B4800010764A000021DA92400005E60D00008EFE740000190C19000033F4CE000008DE780008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B80008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B8000015D4B000000405E0000008E5000000017B800000288000000006C00000000D80000000024000091A43300001B3CA000003444D0000009B6580000DE86F0000029B38000004F260000000EAC80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B8000015634000000405E00000080BC00000017B800000239400000006C00000000D8000000002400000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B8000015634000000405E00000080BC00000017B800000239400000006C00000000D800000000240000015634000000405E00000080BC00000017B800000239400000006C00000000D80000000024000000239400000006C00000000D8000000002400000003600000000090000000012000000000300008F38A2000019B1EA0000367940000009B6580000D9E500000026D960000053670000000EAC80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B8000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D8000000002400000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B8000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D800000000240000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D80000000024000000202F00000005EE0000000D8000000002400000003600000000090000000012000000000300000DBF87000002975A0000052EB4000000FA98000014BAD0000003EA60000007D4C00000017B8000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000001F5300000005EE0000000BDC00000002400000002F7000000009000000001200000000030000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000001F5300000005EE0000000BDC00000002400000002F7000000009000000001200000000030000001F5300000005EE0000000BDC00000002400000002F70000000090000000012000000000300000002F7000000009000000001200000000030000000048000000000C000000001800000000067
  | 12 => 0x2B03E3D0D80381953F64C38B6DFDCBC048CCB7640393D08CA1C049EC9C40004AC72B838005DEAE6D839B47A361C04AA88DE2804BC891E2C005F8B33D404C6A32760006116BD3C0062A2617400083D86B03A1425B82C04B2C27CA804C618D2C400605DF0D004D482538800624975A400640C143000085E72C004DD43A1A00063198FD8006565BE60000880A5080066778AB80008A484500009635C580000B8DFB83913198440049D7806A004B0DE8018005E9DD80004C05987F00060A02B40006265EBF000083AF15004CEAAC7600061EA5E20006439AECC000867962400657B05C800088F7B7800094F2A000000B7520004DB82DF000062F3C73C006569EA680008811B7400673343A80008B4F16800097DE9500000BAEA90006885C36C0008D1D76C0009ABFA580000BE75B8000A84E1680000CF25080000CF250800000FEF283A1425B82C04F5C3A55004BBA098300066B62E0404C6F26780006865C7DC0061C324D800083AF15004D3F449500069C113E0006356368400086796240063FAE27800088F7B7800088F7B780000B7520004E01CD730006ADE3B24006463B0D80008811B740065905F100008B4F1680008B4F1680000BAEA9000669F07080008D1D76C0008D1D76C0000BE75B8000958E41C0000CF25080000CF250800000FEF2804DB82DF00006A7D604800640319040008792A2C0065452DEC0008AED7940008AED7940000BA68F80066E5E6280008D85A440008D85A440000BF0B6C000965BD1C0000D047800000D0478000001005800068B4BF10000900659400090065940000C2751000099F57FC0000D545900000D5459000001067D0000A7AEA900000E884F80000E884F8000011E2D80000E884F8000011E2D8000011E2D8000001603839B47A361C04BD940E4C04F5C3A5500066B62E0404C033E9C800630F76AC006865C7DC00083AF15004C96CCF48006420F9480069C113E000086796240063713E60000806ADAC00088F7B780000B7520004D3F4495000650D878C006ADE3B240008811B740064C25AE0000824A6840008B4F1680000BAEA900065358C2800083227180008D1D76C0000BE75B80008D1D76C0000BE75B80000CF250800000FEF2804CEAAC76000649FE354006A7D60480008792A2C00645A57D400081C145C0008AED7940000BA68F800655F9960000836319C0008D85A440000BF0B6C0008D85A440000BF0B6C0000D0478000001005800066E5E628000855D2FC00090065940000C2751000090065940000C275100000D5459000001067D000099194600000CE92940000E884F8000011E2D80000E884F8000011E2D8000011E2D8000001603804DD43A1A0006ADE3B24006ADE3B24000926ED8800646C217C0008982F240008982F240000BA68F80065358C280008B411F80008B411F80000BF0B6C0008B411F80000BF0B6C0000BF0B6C000010058000669F07080008D624F80008D624F80000C275100008D624F80000C275100000C2751000001067D000095568980000CE92940000CE9294000011E2D80000CE9294000011E2D8000011E2D80000016038006885C36C000900659400090065940000C61F8000090065940000C61F800000C61F80000010B84000099194600000D3CF340000D3CF3400001257080000D3CF34000012570800001257080000016928000A7AEA900000E816100000E816100000141D380000E816100000141D380000141D380000018C180000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E78393D08CA1C04AB8C1B9004C187CA94006204B33C04F5C3A5500066B62E04006865C7DC00083AF15004C033E9C800624E30AC0064CC6D580007F59D780069C113E0000867962400088F7B780000B7520004C6F267800062E5B7A800659EF4B40008086EC8006ADE3B240008811B740008B4F1680000BAEA9000646C217C0007F7678400084FDCE80000B255F80008D1D76C0000BE75B80000CF250800000FEF2804C05987F000625B389800652049380007FDEA5C006A7D60480008792A2C0008AED7940000BA68F800645A57D40007F642D00008508FA80000B26A140008D85A440000BF0B6C0000D0478000001005800065452DEC000808274800086959480000B4707400090065940000C275100000D5459000001067D000090065940000C275100000D5459000001067D00000E884F8000011E2D8000011E2D8000001603804D48253880069C113E00065BE0DC80008A59DD8006ADE3B24000926ED880008982F240000BA68F80064C25AE000089FBBE000083BC9D80000B26A140008B411F80000BF0B6C0000BF0B6C00001005800065905F100008B411F800084E9B280000B470740008D624F80000C275100000C2751000001067D00008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D8000001603800673343A80008D85A44000871826C0000B7735000090065940000C61F800000C61F80000010B84000090065940000C61F800000C61F80000010B8400000D3CF3400001257080000125708000001692800099F57FC0000D3CF340000D3CF34000011DD280000E816100000141D380000141D380000018C180000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E7804C6A327600064C8B1080069C113E00008A59DD80069C113E00008A59DD8000926ED880000BA68F80063713E60000824991C00089FBBE00000B26A1400089FBBE00000B26A140000BF0B6C00001005800063FAE2780008314E5C0008B411F80000B470740008B411F80000B470740000C2751000001067D00008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D8000001603800657B05C8000851998C0008D85A440000B773500008D85A440000B773500000C61F80000010B8400008D85A440000B773500000C61F80000010B8400000C61F80000010B84000001257080000016928000965BD1C0000C286BC0000D3CF34000011DD280000D3CF34000011DD280000141D380000018C180000D3CF34000011DD280000141D380000018C180000141D380000018C180000018C180000001E780066778AB80008D1D76C0008D1D76C0000C275100008D1D76C0000C275100000C27510000010B8400008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B8400000016928000958E41C0000CE92940000CE9294000011DD280000CE9294000011DD28000011DD280000018C180000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E78000A84E1680000E884F80000E884F80000141D380000E884F80000141D380000141D38000001BE440000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A438B6DFDCBC049E60882404ADA1D810005FFBEA8C04C187CA9400623C35DC0063C4341C0007D501D804F5C3A5500066B62E04006865C7DC00083AF1500069C113E0000867962400088F7B780000B7520004BBA098300061D45D4400638EE0140007D415000065BE0DC8000812955C00083FA5700000B092A0006ADE3B240008811B740008B4F1680000BAEA900008D1D76C0000BE75B80000CF250800000FEF2804B0DE80180060EDFF2C0062B455900007C19F4C00652049380008055A0C00083441940000AF9A9C006A7D60480008792A2C0008AED7940000BA68F80008D85A440000BF0B6C0000D04780000010058000640319040007EE67E00008226CC00000AE7ED8000871826C0000B64C600000C69FE000000F476000090065940000C275100000D5459000001067D00000E884F8000011E2D8000011E2D8000001603804C618D2C4006865C7DC00638EE014000871205000659EF4B40008ADF1700008246C6C0000AF9A9C006ADE3B24000926ED880008982F240000BA68F80008B411F80000BF0B6C0000BF0B6C0000100580006463B0D80008982F2400080D25580000AE7ED800084E9B280000B64C600000B64C6000000F47600008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D80000016038006569EA680008AED7940008226CC00000B04F9800086959480000B89A400000B89A4000000F788800090065940000C61F800000C61F80000010B8400000D3CF3400001257080000125708000001692800090065940000C61F800000C61F80000010B8400000D3CF340000125708000012570800000169280000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E7804BC891E2C006390BC00006865C7DC00087120500064CC6D5800083717C00008ADF1700000AF9A9C0069C113E00008A59DD8000926ED880000BA68F800089FBBE00000B26A140000BF0B6C0000100580006356368400081B7C6C0008982F240000AE7ED800083BC9D80000AA348C0000B64C6000000F47600008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D80000016038006439AECC00082E27C00008AED7940000B04F980008508FA80000ABDAD80000B89A4000000F78880008D85A440000B773500000C61F80000010B8400000C61F80000010B840000012570800000169280008D85A440000B773500000C61F80000010B8400000C61F80000010B840000012570800000169280000D3CF34000011DD280000141D380000018C180000141D380000018C180000018C180000001E78006565BE600008B4F1680008B4F1680000BF0B6C00084FDCE80000B64C600000B64C6000000F78880008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E780009ABFA580000D545900000D5459000001257080000D54590000012570800001257080000018C180000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A404AC72B8380061872C740063C4341C0008076720006865C7DC00087120500008ADF1700000AF9A9C006865C7DC00087120500008ADF1700000AF9A9C000926ED880000BA68F80000BF0B6C00001005800061C324D80007E28B5C0008246C6C0000A43A000008982F240000AE7ED80000B64C6000000F47600008982F240000AE7ED80000B64C6000000F47600000C2751000001067D0000011E2D80000016038006265EBF00007EF85E000083441940000A56E580008AED7940000B04F980000B89A4000000F78880008AED7940000B04F980000B89A4000000F78880000C61F80000010B840000012570800000169280008AED7940000B04F980000B89A4000000F78880000C61F80000010B840000012570800000169280000C61F80000010B840000012570800000169280000141D380000018C180000018C180000001E7800640C143000088F7B7800083FA5700000B399F40008B4F1680000BF0B6C0000B64C6000000F78880008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E7800097DE9500000D047800000C69FE0000010DAC80000D54590000012570800001257080000018C180000D54590000012570800001257080000018C180000141D38000001BE44000001BE4400000022540000D54590000012570800001257080000018C180000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A40062A26174000821699000088F7B780000B399F400088F7B780000B399F40000BF0B6C00000F788800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B840000001692800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800094F2A000000C338780000D04780000010DAC80000D04780000010DAC800001257080000018C180000D04780000010DAC800001257080000018C1800001257080000018C18000001BE4400000022540000D04780000010DAC800001257080000018C1800001257080000018C18000001BE44000000225400001257080000018C18000001BE440000002254000001BE440000002254000000225400000002A40009635C580000CF25080000CF2508000011E2D80000CF2508000011E2D8000011E2D80000018C180000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C1800000022540000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A40000000034381953F64C0490DC5958049E608824005EA898C004AB8C1B90006054E1880061872C740007A2863804BD940E4C0061FE75A8006390BC000007D426E00064C8B1080007FD6F7800082169900000ADD50804F5C3A5500066B62E04006865C7DC00083AF1500069C113E0000867962400088F7B780000B75200006ADE3B240008811B740008B4F1680000BAEA900008D1D76C0000BE75B80000CF250800000FEF28049D7806A0005F53E0200060EDFF2C00079C9B5000625B38980007CA69500007EF85E00000A9D37400649FE3540007FD1A9000082E27C00000AF8AF8000851998C0000B399F40000C3387800000F0458006A7D60480008792A2C0008AED7940000BA68F80008D85A440000BF0B6C0000D04780000010058000090065940000C275100000D5459000001067D00000E884F8000011E2D8000011E2D8000001603804B2C27CA80066B62E040061D45D4400084A3BF00062E5B7A800087120500007E28B5C0000A9D37400650D878C0008A59DD800081B7C6C0000AF8AF80008314E5C0000B399F40000B399F400000F0458006ADE3B24000926ED880008982F240000BA68F80008B411F80000BF0B6C0000BF0B6C00001005800008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D800000160380062F3C73C0008792A2C0007EE67E00000ABE97800080827480000B04F980000B04F9800000EC5C8000855D2FC0000B773500000B7735000000F78880000C286BC000010DAC8000010DAC80000014BE800090065940000C61F800000C61F80000010B8400000D3CF340000125708000012570800000169280000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E7804AA88DE280061FE75A80066B62E0400084A3BF000624E30AC0007FE57D800087120500000A9D374006420F94800082C21600008A59DD80000AF8AF8000824991C0000A815980000B399F400000F04580069C113E00008A59DD8000926ED880000BA68F800089FBBE00000B26A140000BF0B6C00001005800008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D800000160380061EA5E200007FD1A900008792A2C0000ABE9780007F642D00000A449A40000B04F9800000EC5C8000836319C0000AA0A180000B7735000000F78880000B7735000000F7888000010DAC80000014BE80008D85A440000B773500000C61F80000010B8400000C61F80000010B840000012570800000169280000D3CF34000011DD280000141D380000018C180000141D380000018C180000018C180000001E780063198FD80008811B740008811B740000BA68F80007F767840000AE7ED80000AE7ED800000EC5C800083227180000B470740000B4707400000F78880000B4707400000F788800000F78880000014BE80008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E780008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E780000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A4049EC9C400006054E18800623C35DC0007E3DEFC0066B62E0400084A3BF000087120500000A9D37400630F76AC0007FE57D800083717C00000A5B39C0008A59DD80000AF8AF80000B399F400000F0458006865C7DC00087120500008ADF1700000AF9A9C000926ED880000BA68F80000BF0B6C00001005800008982F240000AE7ED80000B64C6000000F47600000C2751000001067D0000011E2D800000160380060A02B400007CA69500008055A0C0000A19BB00008792A2C0000ABE9780000B04F9800000EC5C800081C145C0000A449A40000ABDAD800000E66B80000B7735000000F7888000010DAC80000014BE80008AED7940000B04F980000B89A4000000F78880000C61F80000010B840000012570800000169280000C61F80000010B840000012570800000169280000141D380000018C180000018C180000001E7800624975A40008679624000812955C0000AF8AF80008811B740000BA68F80000AE7ED800000EC5C8000824A6840000B26A140000AA348C00000E66B80000B4707400000F788800000F78880000014BE80008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000D54590000012570800001257080000018C180000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A4006116BD3C0007FD6F7800086796240000AF8AF800086796240000AF8AF80000BA68F800000EC5C8000806ADAC0000A815980000B26A1400000E66B80000B26A1400000E66B800000F78880000014BE800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E780000D04780000010DAC800001257080000018C1800001257080000018C18000001BE44000000225400001257080000018C18000001BE440000002254000001BE440000002254000000225400000002A40008A484500000BE75B80000BE75B800001067D00000BE75B800001067D000001067D000000169280000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A40000000034048CCB7640005EA898C0005FFBEA8C0007ABBDB8006204B33C0007E3DEFC00080767200000A0D7100066B62E0400084A3BF000087120500000A9D3740008A59DD80000AF8AF80000B399F400000F04580066B62E0400084A3BF000087120500000A9D3740008A59DD80000AF8AF80000B399F400000F0458000926ED880000BA68F80000BF0B6C00001005800000C2751000001067D0000011E2D80000016038005E9DD80000079C9B500007C19F4C00009B45880007FDEA5C0000A19BB00000A56E5800000DD3400008792A2C0000ABE9780000B04F9800000EC5C80000B7735000000F7888000010DAC80000014BE80008792A2C0000ABE9780000B04F9800000EC5C80000B7735000000F7888000010DAC80000014BE80000C61F80000010B840000012570800000169280000141D380000018C180000018C180000001E7800605DF0D000083AF1500007D415000000A9D3740008086EC80000AF9A9C0000A43A0000000DD3400008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A4005F8B33D40007D426E000083AF1500000A9D3740007F59D780000A5B39C0000AF9A9C00000DD34000086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE800086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE80000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE80000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E780000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800001257080000018C18000001BE440000002254000001BE440000002254000000225400000002A4000880A5080000BAEA900000BAEA9000001005800000B255F800000F476000000F47600000014BE80000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E78000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E78000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A40000000034005DEAE6D80007A286380007D501D80000A0D71000083AF1500000A9D3740000AF9A9C00000DD34000083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE800083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE80000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E7800083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE80000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E780000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E78000010B84000000169280000018C180000001E78000001BE440000002254000000225400000002A400085E72C00000B752000000B092A000000F04580000BAEA90000010058000000F47600000014BE80000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E780000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E7800001067D0000001692800000169280000001E780000018C180000002254000000225400000002A40000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E7800001067D0000001692800000169280000001E780000018C180000002254000000225400000002A400001067D0000001692800000169280000001E780000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A4000000003400083D86B00000ADD5080000B7520000000F04580000B7520000000F045800001005800000014BE80000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E780000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E7800001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A40000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E7800001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A400001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A400000169280000001E78000000225400000002A4000000225400000002A400000002A400000000340000B8DFB800000FEF2800000FEF28000001603800000FEF28000001603800000160380000001E7800000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000160380000001E780000001E7800000002A40000001E7800000002A400000002A4000000003400000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000160380000001E780000001E7800000002A40000001E7800000002A400000002A4000000003400000160380000001E780000001E7800000002A40000001E7800000002A400000002A400000000340000001E7800000002A400000002A4000000003400000002A40000000034000000003400000000068
  | _ => 0

def BaseTab (u : Fin 2048) : Prop :=
    G 0 u = tb (tabT 0) u.val

instance (u : Fin 2048) : Decidable (BaseTab u) := by
  unfold BaseTab
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_0 : ∀ i : Fin 32, BaseTab (idIndex 0 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_1 : ∀ i : Fin 32, BaseTab (idIndex 1 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_2 : ∀ i : Fin 32, BaseTab (idIndex 2 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_3 : ∀ i : Fin 32, BaseTab (idIndex 3 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_4 : ∀ i : Fin 32, BaseTab (idIndex 4 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_5 : ∀ i : Fin 32, BaseTab (idIndex 5 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_6 : ∀ i : Fin 32, BaseTab (idIndex 6 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_7 : ∀ i : Fin 32, BaseTab (idIndex 7 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_8 : ∀ i : Fin 32, BaseTab (idIndex 8 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_9 : ∀ i : Fin 32, BaseTab (idIndex 9 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_10 : ∀ i : Fin 32, BaseTab (idIndex 10 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_11 : ∀ i : Fin 32, BaseTab (idIndex 11 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_12 : ∀ i : Fin 32, BaseTab (idIndex 12 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_13 : ∀ i : Fin 32, BaseTab (idIndex 13 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_14 : ∀ i : Fin 32, BaseTab (idIndex 14 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_15 : ∀ i : Fin 32, BaseTab (idIndex 15 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_16 : ∀ i : Fin 32, BaseTab (idIndex 16 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_17 : ∀ i : Fin 32, BaseTab (idIndex 17 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_18 : ∀ i : Fin 32, BaseTab (idIndex 18 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_19 : ∀ i : Fin 32, BaseTab (idIndex 19 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_20 : ∀ i : Fin 32, BaseTab (idIndex 20 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_21 : ∀ i : Fin 32, BaseTab (idIndex 21 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_22 : ∀ i : Fin 32, BaseTab (idIndex 22 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_23 : ∀ i : Fin 32, BaseTab (idIndex 23 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_24 : ∀ i : Fin 32, BaseTab (idIndex 24 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_25 : ∀ i : Fin 32, BaseTab (idIndex 25 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_26 : ∀ i : Fin 32, BaseTab (idIndex 26 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_27 : ∀ i : Fin 32, BaseTab (idIndex 27 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_28 : ∀ i : Fin 32, BaseTab (idIndex 28 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_29 : ∀ i : Fin 32, BaseTab (idIndex 29 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_30 : ∀ i : Fin 32, BaseTab (idIndex 30 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_31 : ∀ i : Fin 32, BaseTab (idIndex 31 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_32 : ∀ i : Fin 32, BaseTab (idIndex 32 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_33 : ∀ i : Fin 32, BaseTab (idIndex 33 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_34 : ∀ i : Fin 32, BaseTab (idIndex 34 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_35 : ∀ i : Fin 32, BaseTab (idIndex 35 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_36 : ∀ i : Fin 32, BaseTab (idIndex 36 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_37 : ∀ i : Fin 32, BaseTab (idIndex 37 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_38 : ∀ i : Fin 32, BaseTab (idIndex 38 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_39 : ∀ i : Fin 32, BaseTab (idIndex 39 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_40 : ∀ i : Fin 32, BaseTab (idIndex 40 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_41 : ∀ i : Fin 32, BaseTab (idIndex 41 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_42 : ∀ i : Fin 32, BaseTab (idIndex 42 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_43 : ∀ i : Fin 32, BaseTab (idIndex 43 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_44 : ∀ i : Fin 32, BaseTab (idIndex 44 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_45 : ∀ i : Fin 32, BaseTab (idIndex 45 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_46 : ∀ i : Fin 32, BaseTab (idIndex 46 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_47 : ∀ i : Fin 32, BaseTab (idIndex 47 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_48 : ∀ i : Fin 32, BaseTab (idIndex 48 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_49 : ∀ i : Fin 32, BaseTab (idIndex 49 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_50 : ∀ i : Fin 32, BaseTab (idIndex 50 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_51 : ∀ i : Fin 32, BaseTab (idIndex 51 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_52 : ∀ i : Fin 32, BaseTab (idIndex 52 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_53 : ∀ i : Fin 32, BaseTab (idIndex 53 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_54 : ∀ i : Fin 32, BaseTab (idIndex 54 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_55 : ∀ i : Fin 32, BaseTab (idIndex 55 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_56 : ∀ i : Fin 32, BaseTab (idIndex 56 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_57 : ∀ i : Fin 32, BaseTab (idIndex 57 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_58 : ∀ i : Fin 32, BaseTab (idIndex 58 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_59 : ∀ i : Fin 32, BaseTab (idIndex 59 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_60 : ∀ i : Fin 32, BaseTab (idIndex 60 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_61 : ∀ i : Fin 32, BaseTab (idIndex 61 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_62 : ∀ i : Fin 32, BaseTab (idIndex 62 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_63 : ∀ i : Fin 32, BaseTab (idIndex 63 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T (u : Fin 2048) : G 0 u = tb (tabT 0) u.val := by
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, BaseTab (idIndex k i) := by
    intro k
    fin_cases k
    · exact base_T_chunk_0
    · exact base_T_chunk_1
    · exact base_T_chunk_2
    · exact base_T_chunk_3
    · exact base_T_chunk_4
    · exact base_T_chunk_5
    · exact base_T_chunk_6
    · exact base_T_chunk_7
    · exact base_T_chunk_8
    · exact base_T_chunk_9
    · exact base_T_chunk_10
    · exact base_T_chunk_11
    · exact base_T_chunk_12
    · exact base_T_chunk_13
    · exact base_T_chunk_14
    · exact base_T_chunk_15
    · exact base_T_chunk_16
    · exact base_T_chunk_17
    · exact base_T_chunk_18
    · exact base_T_chunk_19
    · exact base_T_chunk_20
    · exact base_T_chunk_21
    · exact base_T_chunk_22
    · exact base_T_chunk_23
    · exact base_T_chunk_24
    · exact base_T_chunk_25
    · exact base_T_chunk_26
    · exact base_T_chunk_27
    · exact base_T_chunk_28
    · exact base_T_chunk_29
    · exact base_T_chunk_30
    · exact base_T_chunk_31
    · exact base_T_chunk_32
    · exact base_T_chunk_33
    · exact base_T_chunk_34
    · exact base_T_chunk_35
    · exact base_T_chunk_36
    · exact base_T_chunk_37
    · exact base_T_chunk_38
    · exact base_T_chunk_39
    · exact base_T_chunk_40
    · exact base_T_chunk_41
    · exact base_T_chunk_42
    · exact base_T_chunk_43
    · exact base_T_chunk_44
    · exact base_T_chunk_45
    · exact base_T_chunk_46
    · exact base_T_chunk_47
    · exact base_T_chunk_48
    · exact base_T_chunk_49
    · exact base_T_chunk_50
    · exact base_T_chunk_51
    · exact base_T_chunk_52
    · exact base_T_chunk_53
    · exact base_T_chunk_54
    · exact base_T_chunk_55
    · exact base_T_chunk_56
    · exact base_T_chunk_57
    · exact base_T_chunk_58
    · exact base_T_chunk_59
    · exact base_T_chunk_60
    · exact base_T_chunk_61
    · exact base_T_chunk_62
    · exact base_T_chunk_63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he, BaseTab] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

def StepTab (u : Fin 2048) : Prop :=
    ∀ n < (12 : ℕ), (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) = tb (tabT (n + 1)) u.val

instance (u : Fin 2048) : Decidable (StepTab u) := by
  unfold StepTab
  infer_instance

set_option maxRecDepth 20000 in
abbrev s2047 : StepTab 2047 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2046 : StepTab 2046 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2045 : StepTab 2045 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2043 : StepTab 2043 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2039 : StepTab 2039 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2031 : StepTab 2031 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2015 : StepTab 2015 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1983 : StepTab 1983 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1919 : StepTab 1919 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1791 : StepTab 1791 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1535 : StepTab 1535 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1023 : StepTab 1023 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2044 : StepTab 2044 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2042 : StepTab 2042 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2041 : StepTab 2041 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2038 : StepTab 2038 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2037 : StepTab 2037 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2035 : StepTab 2035 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2030 : StepTab 2030 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2029 : StepTab 2029 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2027 : StepTab 2027 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2023 : StepTab 2023 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2014 : StepTab 2014 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2013 : StepTab 2013 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2011 : StepTab 2011 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2007 : StepTab 2007 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1999 : StepTab 1999 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1982 : StepTab 1982 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1981 : StepTab 1981 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1979 : StepTab 1979 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1975 : StepTab 1975 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1967 : StepTab 1967 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1951 : StepTab 1951 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1918 : StepTab 1918 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1917 : StepTab 1917 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1915 : StepTab 1915 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1911 : StepTab 1911 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1903 : StepTab 1903 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1887 : StepTab 1887 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1855 : StepTab 1855 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1790 : StepTab 1790 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1789 : StepTab 1789 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1787 : StepTab 1787 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1783 : StepTab 1783 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1775 : StepTab 1775 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1759 : StepTab 1759 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1727 : StepTab 1727 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1663 : StepTab 1663 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1534 : StepTab 1534 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1533 : StepTab 1533 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1531 : StepTab 1531 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1527 : StepTab 1527 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1519 : StepTab 1519 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1503 : StepTab 1503 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1471 : StepTab 1471 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1407 : StepTab 1407 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1279 : StepTab 1279 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1022 : StepTab 1022 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1021 : StepTab 1021 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1019 : StepTab 1019 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1015 : StepTab 1015 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1007 : StepTab 1007 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s991 : StepTab 991 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s959 : StepTab 959 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s895 : StepTab 895 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s767 : StepTab 767 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s511 : StepTab 511 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2040 : StepTab 2040 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2036 : StepTab 2036 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2034 : StepTab 2034 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2033 : StepTab 2033 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2028 : StepTab 2028 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2026 : StepTab 2026 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2025 : StepTab 2025 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2022 : StepTab 2022 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2021 : StepTab 2021 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2019 : StepTab 2019 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2012 : StepTab 2012 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2010 : StepTab 2010 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2009 : StepTab 2009 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2006 : StepTab 2006 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2005 : StepTab 2005 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2003 : StepTab 2003 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1998 : StepTab 1998 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1997 : StepTab 1997 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1995 : StepTab 1995 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1991 : StepTab 1991 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1980 : StepTab 1980 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1978 : StepTab 1978 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1977 : StepTab 1977 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1974 : StepTab 1974 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1973 : StepTab 1973 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1971 : StepTab 1971 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1966 : StepTab 1966 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1965 : StepTab 1965 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1963 : StepTab 1963 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1959 : StepTab 1959 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1950 : StepTab 1950 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1949 : StepTab 1949 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1947 : StepTab 1947 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1943 : StepTab 1943 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1935 : StepTab 1935 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1916 : StepTab 1916 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1914 : StepTab 1914 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1913 : StepTab 1913 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1910 : StepTab 1910 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1909 : StepTab 1909 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1907 : StepTab 1907 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1902 : StepTab 1902 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1901 : StepTab 1901 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1899 : StepTab 1899 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1895 : StepTab 1895 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1886 : StepTab 1886 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1885 : StepTab 1885 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1883 : StepTab 1883 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1879 : StepTab 1879 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1871 : StepTab 1871 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1854 : StepTab 1854 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1853 : StepTab 1853 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1851 : StepTab 1851 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1847 : StepTab 1847 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1839 : StepTab 1839 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1823 : StepTab 1823 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1788 : StepTab 1788 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1786 : StepTab 1786 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1785 : StepTab 1785 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1782 : StepTab 1782 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1781 : StepTab 1781 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1779 : StepTab 1779 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1774 : StepTab 1774 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1773 : StepTab 1773 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1771 : StepTab 1771 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1767 : StepTab 1767 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1758 : StepTab 1758 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1757 : StepTab 1757 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1755 : StepTab 1755 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1751 : StepTab 1751 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1743 : StepTab 1743 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1726 : StepTab 1726 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1725 : StepTab 1725 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1723 : StepTab 1723 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1719 : StepTab 1719 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1711 : StepTab 1711 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1695 : StepTab 1695 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1662 : StepTab 1662 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1661 : StepTab 1661 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1659 : StepTab 1659 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1655 : StepTab 1655 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1647 : StepTab 1647 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1631 : StepTab 1631 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1599 : StepTab 1599 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1532 : StepTab 1532 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1530 : StepTab 1530 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1529 : StepTab 1529 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1526 : StepTab 1526 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1525 : StepTab 1525 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1523 : StepTab 1523 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1518 : StepTab 1518 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1517 : StepTab 1517 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1515 : StepTab 1515 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1511 : StepTab 1511 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1502 : StepTab 1502 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1501 : StepTab 1501 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1499 : StepTab 1499 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1495 : StepTab 1495 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1487 : StepTab 1487 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1470 : StepTab 1470 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1469 : StepTab 1469 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1467 : StepTab 1467 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1463 : StepTab 1463 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1455 : StepTab 1455 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1439 : StepTab 1439 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1406 : StepTab 1406 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1405 : StepTab 1405 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1403 : StepTab 1403 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1399 : StepTab 1399 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1391 : StepTab 1391 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1375 : StepTab 1375 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1343 : StepTab 1343 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1278 : StepTab 1278 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1277 : StepTab 1277 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1275 : StepTab 1275 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1271 : StepTab 1271 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1263 : StepTab 1263 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1247 : StepTab 1247 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1215 : StepTab 1215 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1151 : StepTab 1151 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1020 : StepTab 1020 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1018 : StepTab 1018 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1017 : StepTab 1017 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1014 : StepTab 1014 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1013 : StepTab 1013 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1011 : StepTab 1011 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1006 : StepTab 1006 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1005 : StepTab 1005 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1003 : StepTab 1003 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s999 : StepTab 999 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s990 : StepTab 990 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s989 : StepTab 989 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s987 : StepTab 987 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s983 : StepTab 983 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s975 : StepTab 975 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s958 : StepTab 958 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s957 : StepTab 957 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s955 : StepTab 955 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s951 : StepTab 951 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s943 : StepTab 943 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s927 : StepTab 927 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s894 : StepTab 894 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s893 : StepTab 893 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s891 : StepTab 891 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s887 : StepTab 887 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s879 : StepTab 879 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s863 : StepTab 863 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s831 : StepTab 831 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s766 : StepTab 766 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s765 : StepTab 765 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s763 : StepTab 763 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s759 : StepTab 759 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s751 : StepTab 751 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s735 : StepTab 735 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s703 : StepTab 703 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s639 : StepTab 639 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s510 : StepTab 510 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s509 : StepTab 509 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s507 : StepTab 507 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s503 : StepTab 503 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s495 : StepTab 495 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s479 : StepTab 479 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s447 : StepTab 447 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s383 : StepTab 383 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s255 : StepTab 255 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2032 : StepTab 2032 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2024 : StepTab 2024 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2020 : StepTab 2020 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2018 : StepTab 2018 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2017 : StepTab 2017 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2008 : StepTab 2008 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2004 : StepTab 2004 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2002 : StepTab 2002 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2001 : StepTab 2001 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1996 : StepTab 1996 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1994 : StepTab 1994 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1993 : StepTab 1993 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1990 : StepTab 1990 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1989 : StepTab 1989 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1987 : StepTab 1987 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1976 : StepTab 1976 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1972 : StepTab 1972 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1970 : StepTab 1970 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1969 : StepTab 1969 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1964 : StepTab 1964 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1962 : StepTab 1962 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1961 : StepTab 1961 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1958 : StepTab 1958 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1957 : StepTab 1957 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1955 : StepTab 1955 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1948 : StepTab 1948 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1946 : StepTab 1946 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1945 : StepTab 1945 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1942 : StepTab 1942 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1941 : StepTab 1941 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1939 : StepTab 1939 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1934 : StepTab 1934 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1933 : StepTab 1933 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1931 : StepTab 1931 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1927 : StepTab 1927 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1912 : StepTab 1912 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1908 : StepTab 1908 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1906 : StepTab 1906 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1905 : StepTab 1905 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1900 : StepTab 1900 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1898 : StepTab 1898 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1897 : StepTab 1897 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1894 : StepTab 1894 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1893 : StepTab 1893 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1891 : StepTab 1891 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1884 : StepTab 1884 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1882 : StepTab 1882 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1881 : StepTab 1881 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1878 : StepTab 1878 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1877 : StepTab 1877 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1875 : StepTab 1875 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1870 : StepTab 1870 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1869 : StepTab 1869 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1867 : StepTab 1867 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1863 : StepTab 1863 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1852 : StepTab 1852 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1850 : StepTab 1850 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1849 : StepTab 1849 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1846 : StepTab 1846 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1845 : StepTab 1845 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1843 : StepTab 1843 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1838 : StepTab 1838 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1837 : StepTab 1837 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1835 : StepTab 1835 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1831 : StepTab 1831 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1822 : StepTab 1822 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1821 : StepTab 1821 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1819 : StepTab 1819 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1815 : StepTab 1815 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1807 : StepTab 1807 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1784 : StepTab 1784 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1780 : StepTab 1780 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1778 : StepTab 1778 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1777 : StepTab 1777 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1772 : StepTab 1772 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1770 : StepTab 1770 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1769 : StepTab 1769 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1766 : StepTab 1766 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1765 : StepTab 1765 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1763 : StepTab 1763 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1756 : StepTab 1756 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1754 : StepTab 1754 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1753 : StepTab 1753 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1750 : StepTab 1750 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1749 : StepTab 1749 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1747 : StepTab 1747 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1742 : StepTab 1742 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1741 : StepTab 1741 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1739 : StepTab 1739 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1735 : StepTab 1735 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1724 : StepTab 1724 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1722 : StepTab 1722 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1721 : StepTab 1721 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1718 : StepTab 1718 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1717 : StepTab 1717 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1715 : StepTab 1715 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1710 : StepTab 1710 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1709 : StepTab 1709 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1707 : StepTab 1707 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1703 : StepTab 1703 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1694 : StepTab 1694 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1693 : StepTab 1693 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1691 : StepTab 1691 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1687 : StepTab 1687 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1679 : StepTab 1679 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1660 : StepTab 1660 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1658 : StepTab 1658 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1657 : StepTab 1657 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1654 : StepTab 1654 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1653 : StepTab 1653 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1651 : StepTab 1651 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1646 : StepTab 1646 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1645 : StepTab 1645 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1643 : StepTab 1643 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1639 : StepTab 1639 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1630 : StepTab 1630 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1629 : StepTab 1629 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1627 : StepTab 1627 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1623 : StepTab 1623 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1615 : StepTab 1615 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1598 : StepTab 1598 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1597 : StepTab 1597 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1595 : StepTab 1595 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1591 : StepTab 1591 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1583 : StepTab 1583 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1567 : StepTab 1567 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1528 : StepTab 1528 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1524 : StepTab 1524 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1522 : StepTab 1522 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1521 : StepTab 1521 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1516 : StepTab 1516 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1514 : StepTab 1514 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1513 : StepTab 1513 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1510 : StepTab 1510 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1509 : StepTab 1509 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1507 : StepTab 1507 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1500 : StepTab 1500 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1498 : StepTab 1498 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1497 : StepTab 1497 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1494 : StepTab 1494 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1493 : StepTab 1493 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1491 : StepTab 1491 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1486 : StepTab 1486 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1485 : StepTab 1485 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1483 : StepTab 1483 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1479 : StepTab 1479 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1468 : StepTab 1468 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1466 : StepTab 1466 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1465 : StepTab 1465 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1462 : StepTab 1462 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1461 : StepTab 1461 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1459 : StepTab 1459 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1454 : StepTab 1454 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1453 : StepTab 1453 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1451 : StepTab 1451 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1447 : StepTab 1447 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1438 : StepTab 1438 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1437 : StepTab 1437 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1435 : StepTab 1435 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1431 : StepTab 1431 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1423 : StepTab 1423 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1404 : StepTab 1404 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1402 : StepTab 1402 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1401 : StepTab 1401 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1398 : StepTab 1398 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1397 : StepTab 1397 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1395 : StepTab 1395 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1390 : StepTab 1390 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1389 : StepTab 1389 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1387 : StepTab 1387 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1383 : StepTab 1383 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1374 : StepTab 1374 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1373 : StepTab 1373 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1371 : StepTab 1371 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1367 : StepTab 1367 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1359 : StepTab 1359 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1342 : StepTab 1342 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1341 : StepTab 1341 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1339 : StepTab 1339 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1335 : StepTab 1335 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1327 : StepTab 1327 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1311 : StepTab 1311 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1276 : StepTab 1276 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1274 : StepTab 1274 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1273 : StepTab 1273 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1270 : StepTab 1270 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1269 : StepTab 1269 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1267 : StepTab 1267 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1262 : StepTab 1262 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1261 : StepTab 1261 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1259 : StepTab 1259 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1255 : StepTab 1255 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1246 : StepTab 1246 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1245 : StepTab 1245 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1243 : StepTab 1243 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1239 : StepTab 1239 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1231 : StepTab 1231 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1214 : StepTab 1214 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1213 : StepTab 1213 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1211 : StepTab 1211 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1207 : StepTab 1207 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1199 : StepTab 1199 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1183 : StepTab 1183 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1150 : StepTab 1150 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1149 : StepTab 1149 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1147 : StepTab 1147 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1143 : StepTab 1143 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1135 : StepTab 1135 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1119 : StepTab 1119 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1087 : StepTab 1087 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1016 : StepTab 1016 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1012 : StepTab 1012 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1010 : StepTab 1010 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1009 : StepTab 1009 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1004 : StepTab 1004 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1002 : StepTab 1002 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1001 : StepTab 1001 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s998 : StepTab 998 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s997 : StepTab 997 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s995 : StepTab 995 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s988 : StepTab 988 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s986 : StepTab 986 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s985 : StepTab 985 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s982 : StepTab 982 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s981 : StepTab 981 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s979 : StepTab 979 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s974 : StepTab 974 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s973 : StepTab 973 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s971 : StepTab 971 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s967 : StepTab 967 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s956 : StepTab 956 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s954 : StepTab 954 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s953 : StepTab 953 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s950 : StepTab 950 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s949 : StepTab 949 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s947 : StepTab 947 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s942 : StepTab 942 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s941 : StepTab 941 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s939 : StepTab 939 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s935 : StepTab 935 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s926 : StepTab 926 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s925 : StepTab 925 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s923 : StepTab 923 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s919 : StepTab 919 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s911 : StepTab 911 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s892 : StepTab 892 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s890 : StepTab 890 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s889 : StepTab 889 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s886 : StepTab 886 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s885 : StepTab 885 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s883 : StepTab 883 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s878 : StepTab 878 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s877 : StepTab 877 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s875 : StepTab 875 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s871 : StepTab 871 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s862 : StepTab 862 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s861 : StepTab 861 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s859 : StepTab 859 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s855 : StepTab 855 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s847 : StepTab 847 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s830 : StepTab 830 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s829 : StepTab 829 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s827 : StepTab 827 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s823 : StepTab 823 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s815 : StepTab 815 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s799 : StepTab 799 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s764 : StepTab 764 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s762 : StepTab 762 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s761 : StepTab 761 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s758 : StepTab 758 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s757 : StepTab 757 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s755 : StepTab 755 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s750 : StepTab 750 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s749 : StepTab 749 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s747 : StepTab 747 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s743 : StepTab 743 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s734 : StepTab 734 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s733 : StepTab 733 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s731 : StepTab 731 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s727 : StepTab 727 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s719 : StepTab 719 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s702 : StepTab 702 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s701 : StepTab 701 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s699 : StepTab 699 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s695 : StepTab 695 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s687 : StepTab 687 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s671 : StepTab 671 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s638 : StepTab 638 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s637 : StepTab 637 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s635 : StepTab 635 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s631 : StepTab 631 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s623 : StepTab 623 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s607 : StepTab 607 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s575 : StepTab 575 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s508 : StepTab 508 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s506 : StepTab 506 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s505 : StepTab 505 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s502 : StepTab 502 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s501 : StepTab 501 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s499 : StepTab 499 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s494 : StepTab 494 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s493 : StepTab 493 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s491 : StepTab 491 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s487 : StepTab 487 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s478 : StepTab 478 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s477 : StepTab 477 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s475 : StepTab 475 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s471 : StepTab 471 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s463 : StepTab 463 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s446 : StepTab 446 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s445 : StepTab 445 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s443 : StepTab 443 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s439 : StepTab 439 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s431 : StepTab 431 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s415 : StepTab 415 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s382 : StepTab 382 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s381 : StepTab 381 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s379 : StepTab 379 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s375 : StepTab 375 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s367 : StepTab 367 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s351 : StepTab 351 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s319 : StepTab 319 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s254 : StepTab 254 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s253 : StepTab 253 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s251 : StepTab 251 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s247 : StepTab 247 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s239 : StepTab 239 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s223 : StepTab 223 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s191 : StepTab 191 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s127 : StepTab 127 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2016 : StepTab 2016 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2000 : StepTab 2000 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1992 : StepTab 1992 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1988 : StepTab 1988 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1986 : StepTab 1986 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1985 : StepTab 1985 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1968 : StepTab 1968 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1960 : StepTab 1960 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1956 : StepTab 1956 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1954 : StepTab 1954 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1953 : StepTab 1953 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1944 : StepTab 1944 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1940 : StepTab 1940 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1938 : StepTab 1938 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1937 : StepTab 1937 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1932 : StepTab 1932 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1930 : StepTab 1930 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1929 : StepTab 1929 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1926 : StepTab 1926 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1925 : StepTab 1925 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1923 : StepTab 1923 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1904 : StepTab 1904 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1896 : StepTab 1896 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1892 : StepTab 1892 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1890 : StepTab 1890 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1889 : StepTab 1889 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1880 : StepTab 1880 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1876 : StepTab 1876 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1874 : StepTab 1874 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1873 : StepTab 1873 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1868 : StepTab 1868 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1866 : StepTab 1866 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1865 : StepTab 1865 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1862 : StepTab 1862 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1861 : StepTab 1861 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1859 : StepTab 1859 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1848 : StepTab 1848 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1844 : StepTab 1844 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1842 : StepTab 1842 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1841 : StepTab 1841 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1836 : StepTab 1836 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1834 : StepTab 1834 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1833 : StepTab 1833 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1830 : StepTab 1830 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1829 : StepTab 1829 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1827 : StepTab 1827 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1820 : StepTab 1820 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1818 : StepTab 1818 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1817 : StepTab 1817 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1814 : StepTab 1814 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1813 : StepTab 1813 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1811 : StepTab 1811 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1806 : StepTab 1806 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1805 : StepTab 1805 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1803 : StepTab 1803 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1799 : StepTab 1799 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1776 : StepTab 1776 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1768 : StepTab 1768 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1764 : StepTab 1764 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1762 : StepTab 1762 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1761 : StepTab 1761 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1752 : StepTab 1752 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1748 : StepTab 1748 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1746 : StepTab 1746 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1745 : StepTab 1745 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1740 : StepTab 1740 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1738 : StepTab 1738 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1737 : StepTab 1737 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1734 : StepTab 1734 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1733 : StepTab 1733 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1731 : StepTab 1731 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1720 : StepTab 1720 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1716 : StepTab 1716 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1714 : StepTab 1714 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1713 : StepTab 1713 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1708 : StepTab 1708 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1706 : StepTab 1706 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1705 : StepTab 1705 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1702 : StepTab 1702 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1701 : StepTab 1701 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1699 : StepTab 1699 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1692 : StepTab 1692 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1690 : StepTab 1690 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1689 : StepTab 1689 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1686 : StepTab 1686 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1685 : StepTab 1685 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1683 : StepTab 1683 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1678 : StepTab 1678 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1677 : StepTab 1677 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1675 : StepTab 1675 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1671 : StepTab 1671 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1656 : StepTab 1656 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1652 : StepTab 1652 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1650 : StepTab 1650 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1649 : StepTab 1649 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1644 : StepTab 1644 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1642 : StepTab 1642 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1641 : StepTab 1641 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1638 : StepTab 1638 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1637 : StepTab 1637 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1635 : StepTab 1635 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1628 : StepTab 1628 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1626 : StepTab 1626 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1625 : StepTab 1625 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1622 : StepTab 1622 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1621 : StepTab 1621 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1619 : StepTab 1619 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1614 : StepTab 1614 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1613 : StepTab 1613 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1611 : StepTab 1611 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1607 : StepTab 1607 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1596 : StepTab 1596 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1594 : StepTab 1594 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1593 : StepTab 1593 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1590 : StepTab 1590 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1589 : StepTab 1589 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1587 : StepTab 1587 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1582 : StepTab 1582 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1581 : StepTab 1581 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1579 : StepTab 1579 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1575 : StepTab 1575 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1566 : StepTab 1566 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1565 : StepTab 1565 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1563 : StepTab 1563 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1559 : StepTab 1559 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1551 : StepTab 1551 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1520 : StepTab 1520 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1512 : StepTab 1512 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1508 : StepTab 1508 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1506 : StepTab 1506 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1505 : StepTab 1505 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1496 : StepTab 1496 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1492 : StepTab 1492 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1490 : StepTab 1490 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1489 : StepTab 1489 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1484 : StepTab 1484 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1482 : StepTab 1482 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1481 : StepTab 1481 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1478 : StepTab 1478 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1477 : StepTab 1477 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1475 : StepTab 1475 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1464 : StepTab 1464 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1460 : StepTab 1460 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1458 : StepTab 1458 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1457 : StepTab 1457 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1452 : StepTab 1452 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1450 : StepTab 1450 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1449 : StepTab 1449 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1446 : StepTab 1446 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1445 : StepTab 1445 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1443 : StepTab 1443 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1436 : StepTab 1436 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1434 : StepTab 1434 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1433 : StepTab 1433 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1430 : StepTab 1430 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1429 : StepTab 1429 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1427 : StepTab 1427 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1422 : StepTab 1422 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1421 : StepTab 1421 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1419 : StepTab 1419 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1415 : StepTab 1415 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1400 : StepTab 1400 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1396 : StepTab 1396 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1394 : StepTab 1394 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1393 : StepTab 1393 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1388 : StepTab 1388 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1386 : StepTab 1386 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1385 : StepTab 1385 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1382 : StepTab 1382 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1381 : StepTab 1381 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1379 : StepTab 1379 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1372 : StepTab 1372 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1370 : StepTab 1370 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1369 : StepTab 1369 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1366 : StepTab 1366 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1365 : StepTab 1365 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1363 : StepTab 1363 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1358 : StepTab 1358 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1357 : StepTab 1357 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1355 : StepTab 1355 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1351 : StepTab 1351 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1340 : StepTab 1340 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1338 : StepTab 1338 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1337 : StepTab 1337 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1334 : StepTab 1334 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1333 : StepTab 1333 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1331 : StepTab 1331 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1326 : StepTab 1326 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1325 : StepTab 1325 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1323 : StepTab 1323 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1319 : StepTab 1319 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1310 : StepTab 1310 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1309 : StepTab 1309 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1307 : StepTab 1307 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1303 : StepTab 1303 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1295 : StepTab 1295 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1272 : StepTab 1272 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1268 : StepTab 1268 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1266 : StepTab 1266 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1265 : StepTab 1265 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1260 : StepTab 1260 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1258 : StepTab 1258 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1257 : StepTab 1257 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1254 : StepTab 1254 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1253 : StepTab 1253 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1251 : StepTab 1251 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1244 : StepTab 1244 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1242 : StepTab 1242 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1241 : StepTab 1241 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1238 : StepTab 1238 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1237 : StepTab 1237 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1235 : StepTab 1235 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1230 : StepTab 1230 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1229 : StepTab 1229 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1227 : StepTab 1227 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1223 : StepTab 1223 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1212 : StepTab 1212 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1210 : StepTab 1210 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1209 : StepTab 1209 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1206 : StepTab 1206 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1205 : StepTab 1205 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1203 : StepTab 1203 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1198 : StepTab 1198 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1197 : StepTab 1197 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1195 : StepTab 1195 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1191 : StepTab 1191 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1182 : StepTab 1182 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1181 : StepTab 1181 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1179 : StepTab 1179 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1175 : StepTab 1175 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1167 : StepTab 1167 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1148 : StepTab 1148 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1146 : StepTab 1146 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1145 : StepTab 1145 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1142 : StepTab 1142 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1141 : StepTab 1141 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1139 : StepTab 1139 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1134 : StepTab 1134 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1133 : StepTab 1133 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1131 : StepTab 1131 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1127 : StepTab 1127 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1118 : StepTab 1118 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1117 : StepTab 1117 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1115 : StepTab 1115 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1111 : StepTab 1111 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1103 : StepTab 1103 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1086 : StepTab 1086 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1085 : StepTab 1085 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1083 : StepTab 1083 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1079 : StepTab 1079 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1071 : StepTab 1071 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1055 : StepTab 1055 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1008 : StepTab 1008 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1000 : StepTab 1000 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s996 : StepTab 996 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s994 : StepTab 994 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s993 : StepTab 993 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s984 : StepTab 984 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s980 : StepTab 980 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s978 : StepTab 978 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s977 : StepTab 977 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s972 : StepTab 972 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s970 : StepTab 970 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s969 : StepTab 969 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s966 : StepTab 966 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s965 : StepTab 965 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s963 : StepTab 963 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s952 : StepTab 952 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s948 : StepTab 948 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s946 : StepTab 946 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s945 : StepTab 945 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s940 : StepTab 940 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s938 : StepTab 938 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s937 : StepTab 937 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s934 : StepTab 934 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s933 : StepTab 933 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s931 : StepTab 931 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s924 : StepTab 924 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s922 : StepTab 922 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s921 : StepTab 921 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s918 : StepTab 918 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s917 : StepTab 917 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s915 : StepTab 915 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s910 : StepTab 910 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s909 : StepTab 909 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s907 : StepTab 907 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s903 : StepTab 903 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s888 : StepTab 888 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s884 : StepTab 884 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s882 : StepTab 882 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s881 : StepTab 881 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s876 : StepTab 876 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s874 : StepTab 874 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s873 : StepTab 873 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s870 : StepTab 870 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s869 : StepTab 869 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s867 : StepTab 867 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s860 : StepTab 860 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s858 : StepTab 858 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s857 : StepTab 857 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s854 : StepTab 854 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s853 : StepTab 853 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s851 : StepTab 851 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s846 : StepTab 846 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s845 : StepTab 845 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s843 : StepTab 843 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s839 : StepTab 839 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s828 : StepTab 828 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s826 : StepTab 826 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s825 : StepTab 825 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s822 : StepTab 822 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s821 : StepTab 821 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s819 : StepTab 819 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s814 : StepTab 814 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s813 : StepTab 813 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s811 : StepTab 811 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s807 : StepTab 807 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s798 : StepTab 798 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s797 : StepTab 797 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s795 : StepTab 795 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s791 : StepTab 791 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s783 : StepTab 783 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s760 : StepTab 760 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s756 : StepTab 756 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s754 : StepTab 754 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s753 : StepTab 753 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s748 : StepTab 748 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s746 : StepTab 746 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s745 : StepTab 745 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s742 : StepTab 742 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s741 : StepTab 741 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s739 : StepTab 739 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s732 : StepTab 732 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s730 : StepTab 730 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s729 : StepTab 729 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s726 : StepTab 726 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s725 : StepTab 725 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s723 : StepTab 723 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s718 : StepTab 718 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s717 : StepTab 717 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s715 : StepTab 715 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s711 : StepTab 711 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s700 : StepTab 700 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s698 : StepTab 698 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s697 : StepTab 697 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s694 : StepTab 694 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s693 : StepTab 693 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s691 : StepTab 691 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s686 : StepTab 686 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s685 : StepTab 685 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s683 : StepTab 683 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s679 : StepTab 679 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s670 : StepTab 670 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s669 : StepTab 669 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s667 : StepTab 667 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s663 : StepTab 663 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s655 : StepTab 655 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s636 : StepTab 636 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s634 : StepTab 634 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s633 : StepTab 633 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s630 : StepTab 630 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s629 : StepTab 629 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s627 : StepTab 627 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s622 : StepTab 622 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s621 : StepTab 621 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s619 : StepTab 619 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s615 : StepTab 615 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s606 : StepTab 606 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s605 : StepTab 605 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s603 : StepTab 603 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s599 : StepTab 599 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s591 : StepTab 591 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s574 : StepTab 574 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s573 : StepTab 573 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s571 : StepTab 571 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s567 : StepTab 567 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s559 : StepTab 559 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s543 : StepTab 543 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s504 : StepTab 504 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s500 : StepTab 500 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s498 : StepTab 498 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s497 : StepTab 497 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s492 : StepTab 492 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s490 : StepTab 490 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s489 : StepTab 489 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s486 : StepTab 486 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s485 : StepTab 485 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s483 : StepTab 483 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s476 : StepTab 476 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s474 : StepTab 474 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s473 : StepTab 473 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s470 : StepTab 470 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s469 : StepTab 469 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s467 : StepTab 467 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s462 : StepTab 462 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s461 : StepTab 461 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s459 : StepTab 459 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s455 : StepTab 455 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s444 : StepTab 444 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s442 : StepTab 442 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s441 : StepTab 441 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s438 : StepTab 438 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s437 : StepTab 437 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s435 : StepTab 435 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s430 : StepTab 430 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s429 : StepTab 429 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s427 : StepTab 427 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s423 : StepTab 423 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s414 : StepTab 414 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s413 : StepTab 413 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s411 : StepTab 411 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s407 : StepTab 407 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s399 : StepTab 399 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s380 : StepTab 380 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s378 : StepTab 378 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s377 : StepTab 377 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s374 : StepTab 374 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s373 : StepTab 373 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s371 : StepTab 371 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s366 : StepTab 366 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s365 : StepTab 365 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s363 : StepTab 363 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s359 : StepTab 359 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s350 : StepTab 350 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s349 : StepTab 349 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s347 : StepTab 347 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s343 : StepTab 343 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s335 : StepTab 335 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s318 : StepTab 318 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s317 : StepTab 317 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s315 : StepTab 315 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s311 : StepTab 311 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s303 : StepTab 303 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s287 : StepTab 287 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s252 : StepTab 252 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s250 : StepTab 250 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s249 : StepTab 249 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s246 : StepTab 246 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s245 : StepTab 245 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s243 : StepTab 243 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s238 : StepTab 238 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s237 : StepTab 237 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s235 : StepTab 235 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s231 : StepTab 231 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s222 : StepTab 222 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s221 : StepTab 221 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s219 : StepTab 219 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s215 : StepTab 215 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s207 : StepTab 207 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s190 : StepTab 190 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s189 : StepTab 189 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s187 : StepTab 187 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s183 : StepTab 183 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s175 : StepTab 175 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s159 : StepTab 159 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s126 : StepTab 126 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s125 : StepTab 125 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s123 : StepTab 123 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s119 : StepTab 119 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s111 : StepTab 111 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s95 : StepTab 95 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s63 : StepTab 63 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1984 : StepTab 1984 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1952 : StepTab 1952 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1936 : StepTab 1936 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1928 : StepTab 1928 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1924 : StepTab 1924 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1922 : StepTab 1922 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1921 : StepTab 1921 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1888 : StepTab 1888 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1872 : StepTab 1872 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1864 : StepTab 1864 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1860 : StepTab 1860 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1858 : StepTab 1858 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1857 : StepTab 1857 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1840 : StepTab 1840 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1832 : StepTab 1832 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1828 : StepTab 1828 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1826 : StepTab 1826 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1825 : StepTab 1825 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1816 : StepTab 1816 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1812 : StepTab 1812 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1810 : StepTab 1810 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1809 : StepTab 1809 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1804 : StepTab 1804 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1802 : StepTab 1802 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1801 : StepTab 1801 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1798 : StepTab 1798 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1797 : StepTab 1797 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1795 : StepTab 1795 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1760 : StepTab 1760 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1744 : StepTab 1744 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1736 : StepTab 1736 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1732 : StepTab 1732 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1730 : StepTab 1730 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1729 : StepTab 1729 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1712 : StepTab 1712 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1704 : StepTab 1704 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1700 : StepTab 1700 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1698 : StepTab 1698 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1697 : StepTab 1697 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1688 : StepTab 1688 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1684 : StepTab 1684 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1682 : StepTab 1682 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1681 : StepTab 1681 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1676 : StepTab 1676 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1674 : StepTab 1674 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1673 : StepTab 1673 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1670 : StepTab 1670 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1669 : StepTab 1669 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1667 : StepTab 1667 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1648 : StepTab 1648 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1640 : StepTab 1640 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1636 : StepTab 1636 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1634 : StepTab 1634 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1633 : StepTab 1633 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1624 : StepTab 1624 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1620 : StepTab 1620 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1618 : StepTab 1618 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1617 : StepTab 1617 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1612 : StepTab 1612 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1610 : StepTab 1610 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1609 : StepTab 1609 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1606 : StepTab 1606 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1605 : StepTab 1605 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1603 : StepTab 1603 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1592 : StepTab 1592 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1588 : StepTab 1588 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1586 : StepTab 1586 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1585 : StepTab 1585 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1580 : StepTab 1580 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1578 : StepTab 1578 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1577 : StepTab 1577 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1574 : StepTab 1574 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1573 : StepTab 1573 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1571 : StepTab 1571 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1564 : StepTab 1564 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1562 : StepTab 1562 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1561 : StepTab 1561 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1558 : StepTab 1558 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1557 : StepTab 1557 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1555 : StepTab 1555 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1550 : StepTab 1550 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1549 : StepTab 1549 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1547 : StepTab 1547 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1543 : StepTab 1543 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1504 : StepTab 1504 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1488 : StepTab 1488 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1480 : StepTab 1480 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1476 : StepTab 1476 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1474 : StepTab 1474 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1473 : StepTab 1473 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1456 : StepTab 1456 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1448 : StepTab 1448 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1444 : StepTab 1444 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1442 : StepTab 1442 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1441 : StepTab 1441 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1432 : StepTab 1432 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1428 : StepTab 1428 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1426 : StepTab 1426 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1425 : StepTab 1425 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1420 : StepTab 1420 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1418 : StepTab 1418 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1417 : StepTab 1417 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1414 : StepTab 1414 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1413 : StepTab 1413 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1411 : StepTab 1411 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1392 : StepTab 1392 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1384 : StepTab 1384 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1380 : StepTab 1380 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1378 : StepTab 1378 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1377 : StepTab 1377 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1368 : StepTab 1368 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1364 : StepTab 1364 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1362 : StepTab 1362 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1361 : StepTab 1361 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1356 : StepTab 1356 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1354 : StepTab 1354 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1353 : StepTab 1353 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1350 : StepTab 1350 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1349 : StepTab 1349 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1347 : StepTab 1347 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1336 : StepTab 1336 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1332 : StepTab 1332 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1330 : StepTab 1330 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1329 : StepTab 1329 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1324 : StepTab 1324 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1322 : StepTab 1322 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1321 : StepTab 1321 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1318 : StepTab 1318 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1317 : StepTab 1317 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1315 : StepTab 1315 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1308 : StepTab 1308 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1306 : StepTab 1306 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1305 : StepTab 1305 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1302 : StepTab 1302 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1301 : StepTab 1301 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1299 : StepTab 1299 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1294 : StepTab 1294 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1293 : StepTab 1293 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1291 : StepTab 1291 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1287 : StepTab 1287 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1264 : StepTab 1264 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1256 : StepTab 1256 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1252 : StepTab 1252 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1250 : StepTab 1250 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1249 : StepTab 1249 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1240 : StepTab 1240 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1236 : StepTab 1236 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1234 : StepTab 1234 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1233 : StepTab 1233 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1228 : StepTab 1228 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1226 : StepTab 1226 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1225 : StepTab 1225 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1222 : StepTab 1222 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1221 : StepTab 1221 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1219 : StepTab 1219 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1208 : StepTab 1208 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1204 : StepTab 1204 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1202 : StepTab 1202 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1201 : StepTab 1201 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1196 : StepTab 1196 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1194 : StepTab 1194 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1193 : StepTab 1193 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1190 : StepTab 1190 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1189 : StepTab 1189 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1187 : StepTab 1187 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1180 : StepTab 1180 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1178 : StepTab 1178 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1177 : StepTab 1177 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1174 : StepTab 1174 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1173 : StepTab 1173 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1171 : StepTab 1171 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1166 : StepTab 1166 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1165 : StepTab 1165 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1163 : StepTab 1163 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1159 : StepTab 1159 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1144 : StepTab 1144 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1140 : StepTab 1140 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1138 : StepTab 1138 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1137 : StepTab 1137 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1132 : StepTab 1132 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1130 : StepTab 1130 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1129 : StepTab 1129 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1126 : StepTab 1126 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1125 : StepTab 1125 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1123 : StepTab 1123 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1116 : StepTab 1116 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1114 : StepTab 1114 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1113 : StepTab 1113 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1110 : StepTab 1110 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1109 : StepTab 1109 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1107 : StepTab 1107 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1102 : StepTab 1102 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1101 : StepTab 1101 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1099 : StepTab 1099 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1095 : StepTab 1095 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1084 : StepTab 1084 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1082 : StepTab 1082 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1081 : StepTab 1081 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1078 : StepTab 1078 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1077 : StepTab 1077 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1075 : StepTab 1075 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1070 : StepTab 1070 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1069 : StepTab 1069 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1067 : StepTab 1067 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1063 : StepTab 1063 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1054 : StepTab 1054 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1053 : StepTab 1053 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1051 : StepTab 1051 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1047 : StepTab 1047 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1039 : StepTab 1039 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s992 : StepTab 992 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s976 : StepTab 976 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s968 : StepTab 968 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s964 : StepTab 964 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s962 : StepTab 962 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s961 : StepTab 961 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s944 : StepTab 944 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s936 : StepTab 936 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s932 : StepTab 932 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s930 : StepTab 930 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s929 : StepTab 929 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s920 : StepTab 920 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s916 : StepTab 916 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s914 : StepTab 914 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s913 : StepTab 913 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s908 : StepTab 908 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s906 : StepTab 906 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s905 : StepTab 905 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s902 : StepTab 902 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s901 : StepTab 901 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s899 : StepTab 899 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s880 : StepTab 880 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s872 : StepTab 872 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s868 : StepTab 868 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s866 : StepTab 866 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s865 : StepTab 865 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s856 : StepTab 856 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s852 : StepTab 852 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s850 : StepTab 850 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s849 : StepTab 849 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s844 : StepTab 844 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s842 : StepTab 842 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s841 : StepTab 841 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s838 : StepTab 838 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s837 : StepTab 837 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s835 : StepTab 835 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s824 : StepTab 824 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s820 : StepTab 820 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s818 : StepTab 818 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s817 : StepTab 817 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s812 : StepTab 812 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s810 : StepTab 810 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s809 : StepTab 809 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s806 : StepTab 806 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s805 : StepTab 805 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s803 : StepTab 803 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s796 : StepTab 796 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s794 : StepTab 794 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s793 : StepTab 793 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s790 : StepTab 790 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s789 : StepTab 789 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s787 : StepTab 787 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s782 : StepTab 782 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s781 : StepTab 781 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s779 : StepTab 779 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s775 : StepTab 775 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s752 : StepTab 752 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s744 : StepTab 744 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s740 : StepTab 740 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s738 : StepTab 738 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s737 : StepTab 737 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s728 : StepTab 728 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s724 : StepTab 724 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s722 : StepTab 722 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s721 : StepTab 721 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s716 : StepTab 716 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s714 : StepTab 714 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s713 : StepTab 713 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s710 : StepTab 710 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s709 : StepTab 709 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s707 : StepTab 707 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s696 : StepTab 696 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s692 : StepTab 692 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s690 : StepTab 690 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s689 : StepTab 689 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s684 : StepTab 684 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s682 : StepTab 682 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s681 : StepTab 681 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s678 : StepTab 678 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s677 : StepTab 677 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s675 : StepTab 675 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s668 : StepTab 668 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s666 : StepTab 666 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s665 : StepTab 665 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s662 : StepTab 662 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s661 : StepTab 661 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s659 : StepTab 659 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s654 : StepTab 654 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s653 : StepTab 653 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s651 : StepTab 651 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s647 : StepTab 647 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s632 : StepTab 632 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s628 : StepTab 628 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s626 : StepTab 626 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s625 : StepTab 625 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s620 : StepTab 620 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s618 : StepTab 618 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s617 : StepTab 617 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s614 : StepTab 614 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s613 : StepTab 613 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s611 : StepTab 611 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s604 : StepTab 604 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s602 : StepTab 602 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s601 : StepTab 601 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s598 : StepTab 598 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s597 : StepTab 597 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s595 : StepTab 595 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s590 : StepTab 590 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s589 : StepTab 589 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s587 : StepTab 587 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s583 : StepTab 583 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s572 : StepTab 572 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s570 : StepTab 570 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s569 : StepTab 569 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s566 : StepTab 566 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s565 : StepTab 565 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s563 : StepTab 563 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s558 : StepTab 558 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s557 : StepTab 557 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s555 : StepTab 555 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s551 : StepTab 551 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s542 : StepTab 542 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s541 : StepTab 541 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s539 : StepTab 539 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s535 : StepTab 535 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s527 : StepTab 527 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s496 : StepTab 496 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s488 : StepTab 488 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s484 : StepTab 484 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s482 : StepTab 482 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s481 : StepTab 481 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s472 : StepTab 472 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s468 : StepTab 468 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s466 : StepTab 466 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s465 : StepTab 465 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s460 : StepTab 460 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s458 : StepTab 458 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s457 : StepTab 457 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s454 : StepTab 454 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s453 : StepTab 453 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s451 : StepTab 451 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s440 : StepTab 440 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s436 : StepTab 436 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s434 : StepTab 434 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s433 : StepTab 433 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s428 : StepTab 428 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s426 : StepTab 426 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s425 : StepTab 425 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s422 : StepTab 422 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s421 : StepTab 421 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s419 : StepTab 419 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s412 : StepTab 412 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s410 : StepTab 410 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s409 : StepTab 409 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s406 : StepTab 406 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s405 : StepTab 405 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s403 : StepTab 403 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s398 : StepTab 398 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s397 : StepTab 397 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s395 : StepTab 395 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s391 : StepTab 391 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s376 : StepTab 376 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s372 : StepTab 372 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s370 : StepTab 370 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s369 : StepTab 369 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s364 : StepTab 364 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s362 : StepTab 362 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s361 : StepTab 361 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s358 : StepTab 358 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s357 : StepTab 357 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s355 : StepTab 355 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s348 : StepTab 348 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s346 : StepTab 346 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s345 : StepTab 345 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s342 : StepTab 342 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s341 : StepTab 341 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s339 : StepTab 339 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s334 : StepTab 334 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s333 : StepTab 333 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s331 : StepTab 331 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s327 : StepTab 327 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s316 : StepTab 316 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s314 : StepTab 314 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s313 : StepTab 313 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s310 : StepTab 310 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s309 : StepTab 309 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s307 : StepTab 307 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s302 : StepTab 302 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s301 : StepTab 301 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s299 : StepTab 299 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s295 : StepTab 295 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s286 : StepTab 286 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s285 : StepTab 285 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s283 : StepTab 283 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s279 : StepTab 279 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s271 : StepTab 271 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s248 : StepTab 248 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s244 : StepTab 244 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s242 : StepTab 242 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s241 : StepTab 241 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s236 : StepTab 236 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s234 : StepTab 234 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s233 : StepTab 233 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s230 : StepTab 230 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s229 : StepTab 229 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s227 : StepTab 227 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s220 : StepTab 220 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s218 : StepTab 218 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s217 : StepTab 217 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s214 : StepTab 214 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s213 : StepTab 213 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s211 : StepTab 211 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s206 : StepTab 206 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s205 : StepTab 205 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s203 : StepTab 203 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s199 : StepTab 199 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s188 : StepTab 188 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s186 : StepTab 186 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s185 : StepTab 185 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s182 : StepTab 182 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s181 : StepTab 181 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s179 : StepTab 179 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s174 : StepTab 174 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s173 : StepTab 173 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s171 : StepTab 171 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s167 : StepTab 167 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s158 : StepTab 158 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s157 : StepTab 157 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s155 : StepTab 155 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s151 : StepTab 151 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s143 : StepTab 143 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s124 : StepTab 124 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s122 : StepTab 122 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s121 : StepTab 121 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s118 : StepTab 118 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s117 : StepTab 117 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s115 : StepTab 115 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s110 : StepTab 110 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s109 : StepTab 109 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s107 : StepTab 107 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s103 : StepTab 103 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s94 : StepTab 94 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s93 : StepTab 93 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s91 : StepTab 91 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s87 : StepTab 87 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s79 : StepTab 79 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s62 : StepTab 62 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s61 : StepTab 61 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s59 : StepTab 59 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s55 : StepTab 55 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s47 : StepTab 47 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s31 : StepTab 31 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1920 : StepTab 1920 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1856 : StepTab 1856 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1824 : StepTab 1824 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1808 : StepTab 1808 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1800 : StepTab 1800 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1796 : StepTab 1796 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1794 : StepTab 1794 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1793 : StepTab 1793 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1728 : StepTab 1728 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1696 : StepTab 1696 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1680 : StepTab 1680 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1672 : StepTab 1672 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1668 : StepTab 1668 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1666 : StepTab 1666 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1665 : StepTab 1665 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1632 : StepTab 1632 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1616 : StepTab 1616 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1608 : StepTab 1608 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1604 : StepTab 1604 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1602 : StepTab 1602 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1601 : StepTab 1601 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1584 : StepTab 1584 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1576 : StepTab 1576 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1572 : StepTab 1572 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1570 : StepTab 1570 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1569 : StepTab 1569 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1560 : StepTab 1560 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1556 : StepTab 1556 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1554 : StepTab 1554 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1553 : StepTab 1553 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1548 : StepTab 1548 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1546 : StepTab 1546 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1545 : StepTab 1545 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1542 : StepTab 1542 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1541 : StepTab 1541 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1539 : StepTab 1539 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1472 : StepTab 1472 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1440 : StepTab 1440 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1424 : StepTab 1424 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1416 : StepTab 1416 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1412 : StepTab 1412 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1410 : StepTab 1410 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1409 : StepTab 1409 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1376 : StepTab 1376 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1360 : StepTab 1360 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1352 : StepTab 1352 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1348 : StepTab 1348 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1346 : StepTab 1346 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1345 : StepTab 1345 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1328 : StepTab 1328 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1320 : StepTab 1320 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1316 : StepTab 1316 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1314 : StepTab 1314 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1313 : StepTab 1313 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1304 : StepTab 1304 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1300 : StepTab 1300 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1298 : StepTab 1298 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1297 : StepTab 1297 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1292 : StepTab 1292 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1290 : StepTab 1290 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1289 : StepTab 1289 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1286 : StepTab 1286 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1285 : StepTab 1285 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1283 : StepTab 1283 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1248 : StepTab 1248 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1232 : StepTab 1232 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1224 : StepTab 1224 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1220 : StepTab 1220 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1218 : StepTab 1218 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1217 : StepTab 1217 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1200 : StepTab 1200 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1192 : StepTab 1192 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1188 : StepTab 1188 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1186 : StepTab 1186 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1185 : StepTab 1185 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1176 : StepTab 1176 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1172 : StepTab 1172 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1170 : StepTab 1170 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1169 : StepTab 1169 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1164 : StepTab 1164 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1162 : StepTab 1162 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1161 : StepTab 1161 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1158 : StepTab 1158 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1157 : StepTab 1157 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1155 : StepTab 1155 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1136 : StepTab 1136 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1128 : StepTab 1128 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1124 : StepTab 1124 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1122 : StepTab 1122 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1121 : StepTab 1121 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1112 : StepTab 1112 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1108 : StepTab 1108 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1106 : StepTab 1106 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1105 : StepTab 1105 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1100 : StepTab 1100 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1098 : StepTab 1098 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1097 : StepTab 1097 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1094 : StepTab 1094 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1093 : StepTab 1093 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1091 : StepTab 1091 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1080 : StepTab 1080 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1076 : StepTab 1076 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1074 : StepTab 1074 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1073 : StepTab 1073 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1068 : StepTab 1068 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1066 : StepTab 1066 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1065 : StepTab 1065 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1062 : StepTab 1062 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1061 : StepTab 1061 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1059 : StepTab 1059 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1052 : StepTab 1052 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1050 : StepTab 1050 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1049 : StepTab 1049 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1046 : StepTab 1046 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1045 : StepTab 1045 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1043 : StepTab 1043 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1038 : StepTab 1038 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1037 : StepTab 1037 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1035 : StepTab 1035 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1031 : StepTab 1031 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s960 : StepTab 960 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s928 : StepTab 928 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s912 : StepTab 912 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s904 : StepTab 904 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s900 : StepTab 900 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s898 : StepTab 898 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s897 : StepTab 897 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s864 : StepTab 864 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s848 : StepTab 848 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s840 : StepTab 840 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s836 : StepTab 836 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s834 : StepTab 834 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s833 : StepTab 833 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s816 : StepTab 816 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s808 : StepTab 808 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s804 : StepTab 804 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s802 : StepTab 802 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s801 : StepTab 801 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s792 : StepTab 792 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s788 : StepTab 788 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s786 : StepTab 786 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s785 : StepTab 785 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s780 : StepTab 780 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s778 : StepTab 778 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s777 : StepTab 777 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s774 : StepTab 774 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s773 : StepTab 773 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s771 : StepTab 771 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s736 : StepTab 736 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s720 : StepTab 720 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s712 : StepTab 712 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s708 : StepTab 708 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s706 : StepTab 706 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s705 : StepTab 705 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s688 : StepTab 688 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s680 : StepTab 680 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s676 : StepTab 676 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s674 : StepTab 674 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s673 : StepTab 673 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s664 : StepTab 664 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s660 : StepTab 660 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s658 : StepTab 658 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s657 : StepTab 657 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s652 : StepTab 652 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s650 : StepTab 650 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s649 : StepTab 649 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s646 : StepTab 646 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s645 : StepTab 645 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s643 : StepTab 643 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s624 : StepTab 624 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s616 : StepTab 616 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s612 : StepTab 612 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s610 : StepTab 610 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s609 : StepTab 609 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s600 : StepTab 600 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s596 : StepTab 596 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s594 : StepTab 594 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s593 : StepTab 593 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s588 : StepTab 588 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s586 : StepTab 586 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s585 : StepTab 585 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s582 : StepTab 582 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s581 : StepTab 581 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s579 : StepTab 579 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s568 : StepTab 568 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s564 : StepTab 564 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s562 : StepTab 562 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s561 : StepTab 561 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s556 : StepTab 556 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s554 : StepTab 554 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s553 : StepTab 553 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s550 : StepTab 550 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s549 : StepTab 549 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s547 : StepTab 547 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s540 : StepTab 540 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s538 : StepTab 538 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s537 : StepTab 537 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s534 : StepTab 534 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s533 : StepTab 533 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s531 : StepTab 531 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s526 : StepTab 526 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s525 : StepTab 525 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s523 : StepTab 523 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s519 : StepTab 519 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s480 : StepTab 480 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s464 : StepTab 464 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s456 : StepTab 456 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s452 : StepTab 452 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s450 : StepTab 450 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s449 : StepTab 449 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s432 : StepTab 432 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s424 : StepTab 424 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s420 : StepTab 420 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s418 : StepTab 418 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s417 : StepTab 417 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s408 : StepTab 408 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s404 : StepTab 404 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s402 : StepTab 402 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s401 : StepTab 401 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s396 : StepTab 396 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s394 : StepTab 394 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s393 : StepTab 393 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s390 : StepTab 390 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s389 : StepTab 389 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s387 : StepTab 387 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s368 : StepTab 368 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s360 : StepTab 360 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s356 : StepTab 356 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s354 : StepTab 354 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s353 : StepTab 353 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s344 : StepTab 344 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s340 : StepTab 340 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s338 : StepTab 338 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s337 : StepTab 337 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s332 : StepTab 332 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s330 : StepTab 330 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s329 : StepTab 329 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s326 : StepTab 326 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s325 : StepTab 325 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s323 : StepTab 323 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s312 : StepTab 312 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s308 : StepTab 308 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s306 : StepTab 306 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s305 : StepTab 305 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s300 : StepTab 300 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s298 : StepTab 298 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s297 : StepTab 297 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s294 : StepTab 294 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s293 : StepTab 293 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s291 : StepTab 291 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s284 : StepTab 284 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s282 : StepTab 282 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s281 : StepTab 281 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s278 : StepTab 278 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s277 : StepTab 277 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s275 : StepTab 275 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s270 : StepTab 270 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s269 : StepTab 269 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s267 : StepTab 267 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s263 : StepTab 263 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s240 : StepTab 240 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s232 : StepTab 232 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s228 : StepTab 228 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s226 : StepTab 226 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s225 : StepTab 225 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s216 : StepTab 216 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s212 : StepTab 212 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s210 : StepTab 210 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s209 : StepTab 209 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s204 : StepTab 204 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s202 : StepTab 202 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s201 : StepTab 201 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s198 : StepTab 198 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s197 : StepTab 197 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s195 : StepTab 195 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s184 : StepTab 184 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s180 : StepTab 180 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s178 : StepTab 178 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s177 : StepTab 177 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s172 : StepTab 172 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s170 : StepTab 170 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s169 : StepTab 169 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s166 : StepTab 166 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s165 : StepTab 165 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s163 : StepTab 163 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s156 : StepTab 156 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s154 : StepTab 154 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s153 : StepTab 153 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s150 : StepTab 150 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s149 : StepTab 149 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s147 : StepTab 147 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s142 : StepTab 142 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s141 : StepTab 141 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s139 : StepTab 139 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s135 : StepTab 135 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s120 : StepTab 120 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s116 : StepTab 116 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s114 : StepTab 114 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s113 : StepTab 113 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s108 : StepTab 108 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s106 : StepTab 106 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s105 : StepTab 105 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s102 : StepTab 102 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s101 : StepTab 101 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s99 : StepTab 99 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s92 : StepTab 92 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s90 : StepTab 90 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s89 : StepTab 89 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s86 : StepTab 86 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s85 : StepTab 85 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s83 : StepTab 83 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s78 : StepTab 78 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s77 : StepTab 77 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s75 : StepTab 75 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s71 : StepTab 71 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s60 : StepTab 60 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s58 : StepTab 58 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s57 : StepTab 57 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s54 : StepTab 54 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s53 : StepTab 53 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s51 : StepTab 51 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s46 : StepTab 46 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s45 : StepTab 45 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s43 : StepTab 43 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s39 : StepTab 39 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s30 : StepTab 30 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s29 : StepTab 29 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s27 : StepTab 27 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s23 : StepTab 23 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s15 : StepTab 15 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1792 : StepTab 1792 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1664 : StepTab 1664 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1600 : StepTab 1600 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1568 : StepTab 1568 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1552 : StepTab 1552 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1544 : StepTab 1544 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1540 : StepTab 1540 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1538 : StepTab 1538 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1537 : StepTab 1537 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1408 : StepTab 1408 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1344 : StepTab 1344 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1312 : StepTab 1312 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1296 : StepTab 1296 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1288 : StepTab 1288 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1284 : StepTab 1284 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1282 : StepTab 1282 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1281 : StepTab 1281 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1216 : StepTab 1216 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1184 : StepTab 1184 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1168 : StepTab 1168 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1160 : StepTab 1160 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1156 : StepTab 1156 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1154 : StepTab 1154 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1153 : StepTab 1153 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1120 : StepTab 1120 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1104 : StepTab 1104 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1096 : StepTab 1096 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1092 : StepTab 1092 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1090 : StepTab 1090 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1089 : StepTab 1089 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1072 : StepTab 1072 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1064 : StepTab 1064 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1060 : StepTab 1060 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1058 : StepTab 1058 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1057 : StepTab 1057 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1048 : StepTab 1048 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1044 : StepTab 1044 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1042 : StepTab 1042 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1041 : StepTab 1041 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1036 : StepTab 1036 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1034 : StepTab 1034 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1033 : StepTab 1033 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1030 : StepTab 1030 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1029 : StepTab 1029 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1027 : StepTab 1027 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s896 : StepTab 896 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s832 : StepTab 832 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s800 : StepTab 800 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s784 : StepTab 784 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s776 : StepTab 776 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s772 : StepTab 772 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s770 : StepTab 770 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s769 : StepTab 769 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s704 : StepTab 704 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s672 : StepTab 672 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s656 : StepTab 656 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s648 : StepTab 648 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s644 : StepTab 644 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s642 : StepTab 642 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s641 : StepTab 641 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s608 : StepTab 608 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s592 : StepTab 592 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s584 : StepTab 584 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s580 : StepTab 580 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s578 : StepTab 578 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s577 : StepTab 577 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s560 : StepTab 560 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s552 : StepTab 552 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s548 : StepTab 548 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s546 : StepTab 546 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s545 : StepTab 545 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s536 : StepTab 536 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s532 : StepTab 532 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s530 : StepTab 530 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s529 : StepTab 529 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s524 : StepTab 524 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s522 : StepTab 522 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s521 : StepTab 521 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s518 : StepTab 518 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s517 : StepTab 517 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s515 : StepTab 515 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s448 : StepTab 448 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s416 : StepTab 416 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s400 : StepTab 400 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s392 : StepTab 392 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s388 : StepTab 388 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s386 : StepTab 386 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s385 : StepTab 385 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s352 : StepTab 352 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s336 : StepTab 336 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s328 : StepTab 328 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s324 : StepTab 324 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s322 : StepTab 322 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s321 : StepTab 321 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s304 : StepTab 304 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s296 : StepTab 296 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s292 : StepTab 292 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s290 : StepTab 290 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s289 : StepTab 289 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s280 : StepTab 280 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s276 : StepTab 276 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s274 : StepTab 274 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s273 : StepTab 273 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s268 : StepTab 268 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s266 : StepTab 266 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s265 : StepTab 265 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s262 : StepTab 262 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s261 : StepTab 261 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s259 : StepTab 259 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s224 : StepTab 224 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s208 : StepTab 208 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s200 : StepTab 200 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s196 : StepTab 196 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s194 : StepTab 194 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s193 : StepTab 193 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s176 : StepTab 176 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s168 : StepTab 168 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s164 : StepTab 164 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s162 : StepTab 162 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s161 : StepTab 161 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s152 : StepTab 152 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s148 : StepTab 148 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s146 : StepTab 146 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s145 : StepTab 145 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s140 : StepTab 140 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s138 : StepTab 138 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s137 : StepTab 137 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s134 : StepTab 134 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s133 : StepTab 133 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s131 : StepTab 131 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s112 : StepTab 112 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s104 : StepTab 104 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s100 : StepTab 100 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s98 : StepTab 98 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s97 : StepTab 97 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s88 : StepTab 88 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s84 : StepTab 84 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s82 : StepTab 82 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s81 : StepTab 81 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s76 : StepTab 76 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s74 : StepTab 74 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s73 : StepTab 73 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s70 : StepTab 70 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s69 : StepTab 69 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s67 : StepTab 67 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s56 : StepTab 56 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s52 : StepTab 52 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s50 : StepTab 50 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s49 : StepTab 49 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s44 : StepTab 44 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s42 : StepTab 42 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s41 : StepTab 41 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s38 : StepTab 38 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s37 : StepTab 37 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s35 : StepTab 35 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s28 : StepTab 28 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s26 : StepTab 26 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s25 : StepTab 25 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s22 : StepTab 22 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s21 : StepTab 21 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s19 : StepTab 19 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s14 : StepTab 14 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s13 : StepTab 13 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s11 : StepTab 11 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s7 : StepTab 7 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1536 : StepTab 1536 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1280 : StepTab 1280 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1152 : StepTab 1152 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1088 : StepTab 1088 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1056 : StepTab 1056 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1040 : StepTab 1040 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1032 : StepTab 1032 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1028 : StepTab 1028 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1026 : StepTab 1026 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1025 : StepTab 1025 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s768 : StepTab 768 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s640 : StepTab 640 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s576 : StepTab 576 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s544 : StepTab 544 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s528 : StepTab 528 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s520 : StepTab 520 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s516 : StepTab 516 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s514 : StepTab 514 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s513 : StepTab 513 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s384 : StepTab 384 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s320 : StepTab 320 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s288 : StepTab 288 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s272 : StepTab 272 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s264 : StepTab 264 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s260 : StepTab 260 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s258 : StepTab 258 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s257 : StepTab 257 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s192 : StepTab 192 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s160 : StepTab 160 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s144 : StepTab 144 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s136 : StepTab 136 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s132 : StepTab 132 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s130 : StepTab 130 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s129 : StepTab 129 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s96 : StepTab 96 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s80 : StepTab 80 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s72 : StepTab 72 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s68 : StepTab 68 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s66 : StepTab 66 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s65 : StepTab 65 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s48 : StepTab 48 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s40 : StepTab 40 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s36 : StepTab 36 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s34 : StepTab 34 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s33 : StepTab 33 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s24 : StepTab 24 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s20 : StepTab 20 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s18 : StepTab 18 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s17 : StepTab 17 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s12 : StepTab 12 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s10 : StepTab 10 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s9 : StepTab 9 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s6 : StepTab 6 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s5 : StepTab 5 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s3 : StepTab 3 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1024 : StepTab 1024 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s512 : StepTab 512 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s256 : StepTab 256 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s128 : StepTab 128 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s64 : StepTab 64 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s32 : StepTab 32 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s16 : StepTab 16 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s8 : StepTab 8 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s4 : StepTab 4 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s2 : StepTab 2 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s1 : StepTab 1 := by decide +kernel
set_option maxRecDepth 20000 in
abbrev s0 : StepTab 0 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg0 : ∀ i : Fin 32, StepTab (idIndex 0 i) := by
  intro i
  fin_cases i
  · exact s0
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact s5
  · exact s6
  · exact s7
  · exact s8
  · exact s9
  · exact s10
  · exact s11
  · exact s12
  · exact s13
  · exact s14
  · exact s15
  · exact s16
  · exact s17
  · exact s18
  · exact s19
  · exact s20
  · exact s21
  · exact s22
  · exact s23
  · exact s24
  · exact s25
  · exact s26
  · exact s27
  · exact s28
  · exact s29
  · exact s30
  · exact s31

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg1 : ∀ i : Fin 32, StepTab (idIndex 1 i) := by
  intro i
  fin_cases i
  · exact s32
  · exact s33
  · exact s34
  · exact s35
  · exact s36
  · exact s37
  · exact s38
  · exact s39
  · exact s40
  · exact s41
  · exact s42
  · exact s43
  · exact s44
  · exact s45
  · exact s46
  · exact s47
  · exact s48
  · exact s49
  · exact s50
  · exact s51
  · exact s52
  · exact s53
  · exact s54
  · exact s55
  · exact s56
  · exact s57
  · exact s58
  · exact s59
  · exact s60
  · exact s61
  · exact s62
  · exact s63

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg2 : ∀ i : Fin 32, StepTab (idIndex 2 i) := by
  intro i
  fin_cases i
  · exact s64
  · exact s65
  · exact s66
  · exact s67
  · exact s68
  · exact s69
  · exact s70
  · exact s71
  · exact s72
  · exact s73
  · exact s74
  · exact s75
  · exact s76
  · exact s77
  · exact s78
  · exact s79
  · exact s80
  · exact s81
  · exact s82
  · exact s83
  · exact s84
  · exact s85
  · exact s86
  · exact s87
  · exact s88
  · exact s89
  · exact s90
  · exact s91
  · exact s92
  · exact s93
  · exact s94
  · exact s95

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg3 : ∀ i : Fin 32, StepTab (idIndex 3 i) := by
  intro i
  fin_cases i
  · exact s96
  · exact s97
  · exact s98
  · exact s99
  · exact s100
  · exact s101
  · exact s102
  · exact s103
  · exact s104
  · exact s105
  · exact s106
  · exact s107
  · exact s108
  · exact s109
  · exact s110
  · exact s111
  · exact s112
  · exact s113
  · exact s114
  · exact s115
  · exact s116
  · exact s117
  · exact s118
  · exact s119
  · exact s120
  · exact s121
  · exact s122
  · exact s123
  · exact s124
  · exact s125
  · exact s126
  · exact s127

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg4 : ∀ i : Fin 32, StepTab (idIndex 4 i) := by
  intro i
  fin_cases i
  · exact s128
  · exact s129
  · exact s130
  · exact s131
  · exact s132
  · exact s133
  · exact s134
  · exact s135
  · exact s136
  · exact s137
  · exact s138
  · exact s139
  · exact s140
  · exact s141
  · exact s142
  · exact s143
  · exact s144
  · exact s145
  · exact s146
  · exact s147
  · exact s148
  · exact s149
  · exact s150
  · exact s151
  · exact s152
  · exact s153
  · exact s154
  · exact s155
  · exact s156
  · exact s157
  · exact s158
  · exact s159

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg5 : ∀ i : Fin 32, StepTab (idIndex 5 i) := by
  intro i
  fin_cases i
  · exact s160
  · exact s161
  · exact s162
  · exact s163
  · exact s164
  · exact s165
  · exact s166
  · exact s167
  · exact s168
  · exact s169
  · exact s170
  · exact s171
  · exact s172
  · exact s173
  · exact s174
  · exact s175
  · exact s176
  · exact s177
  · exact s178
  · exact s179
  · exact s180
  · exact s181
  · exact s182
  · exact s183
  · exact s184
  · exact s185
  · exact s186
  · exact s187
  · exact s188
  · exact s189
  · exact s190
  · exact s191

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg6 : ∀ i : Fin 32, StepTab (idIndex 6 i) := by
  intro i
  fin_cases i
  · exact s192
  · exact s193
  · exact s194
  · exact s195
  · exact s196
  · exact s197
  · exact s198
  · exact s199
  · exact s200
  · exact s201
  · exact s202
  · exact s203
  · exact s204
  · exact s205
  · exact s206
  · exact s207
  · exact s208
  · exact s209
  · exact s210
  · exact s211
  · exact s212
  · exact s213
  · exact s214
  · exact s215
  · exact s216
  · exact s217
  · exact s218
  · exact s219
  · exact s220
  · exact s221
  · exact s222
  · exact s223

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg7 : ∀ i : Fin 32, StepTab (idIndex 7 i) := by
  intro i
  fin_cases i
  · exact s224
  · exact s225
  · exact s226
  · exact s227
  · exact s228
  · exact s229
  · exact s230
  · exact s231
  · exact s232
  · exact s233
  · exact s234
  · exact s235
  · exact s236
  · exact s237
  · exact s238
  · exact s239
  · exact s240
  · exact s241
  · exact s242
  · exact s243
  · exact s244
  · exact s245
  · exact s246
  · exact s247
  · exact s248
  · exact s249
  · exact s250
  · exact s251
  · exact s252
  · exact s253
  · exact s254
  · exact s255

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg8 : ∀ i : Fin 32, StepTab (idIndex 8 i) := by
  intro i
  fin_cases i
  · exact s256
  · exact s257
  · exact s258
  · exact s259
  · exact s260
  · exact s261
  · exact s262
  · exact s263
  · exact s264
  · exact s265
  · exact s266
  · exact s267
  · exact s268
  · exact s269
  · exact s270
  · exact s271
  · exact s272
  · exact s273
  · exact s274
  · exact s275
  · exact s276
  · exact s277
  · exact s278
  · exact s279
  · exact s280
  · exact s281
  · exact s282
  · exact s283
  · exact s284
  · exact s285
  · exact s286
  · exact s287

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg9 : ∀ i : Fin 32, StepTab (idIndex 9 i) := by
  intro i
  fin_cases i
  · exact s288
  · exact s289
  · exact s290
  · exact s291
  · exact s292
  · exact s293
  · exact s294
  · exact s295
  · exact s296
  · exact s297
  · exact s298
  · exact s299
  · exact s300
  · exact s301
  · exact s302
  · exact s303
  · exact s304
  · exact s305
  · exact s306
  · exact s307
  · exact s308
  · exact s309
  · exact s310
  · exact s311
  · exact s312
  · exact s313
  · exact s314
  · exact s315
  · exact s316
  · exact s317
  · exact s318
  · exact s319

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg10 : ∀ i : Fin 32, StepTab (idIndex 10 i) := by
  intro i
  fin_cases i
  · exact s320
  · exact s321
  · exact s322
  · exact s323
  · exact s324
  · exact s325
  · exact s326
  · exact s327
  · exact s328
  · exact s329
  · exact s330
  · exact s331
  · exact s332
  · exact s333
  · exact s334
  · exact s335
  · exact s336
  · exact s337
  · exact s338
  · exact s339
  · exact s340
  · exact s341
  · exact s342
  · exact s343
  · exact s344
  · exact s345
  · exact s346
  · exact s347
  · exact s348
  · exact s349
  · exact s350
  · exact s351

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg11 : ∀ i : Fin 32, StepTab (idIndex 11 i) := by
  intro i
  fin_cases i
  · exact s352
  · exact s353
  · exact s354
  · exact s355
  · exact s356
  · exact s357
  · exact s358
  · exact s359
  · exact s360
  · exact s361
  · exact s362
  · exact s363
  · exact s364
  · exact s365
  · exact s366
  · exact s367
  · exact s368
  · exact s369
  · exact s370
  · exact s371
  · exact s372
  · exact s373
  · exact s374
  · exact s375
  · exact s376
  · exact s377
  · exact s378
  · exact s379
  · exact s380
  · exact s381
  · exact s382
  · exact s383

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg12 : ∀ i : Fin 32, StepTab (idIndex 12 i) := by
  intro i
  fin_cases i
  · exact s384
  · exact s385
  · exact s386
  · exact s387
  · exact s388
  · exact s389
  · exact s390
  · exact s391
  · exact s392
  · exact s393
  · exact s394
  · exact s395
  · exact s396
  · exact s397
  · exact s398
  · exact s399
  · exact s400
  · exact s401
  · exact s402
  · exact s403
  · exact s404
  · exact s405
  · exact s406
  · exact s407
  · exact s408
  · exact s409
  · exact s410
  · exact s411
  · exact s412
  · exact s413
  · exact s414
  · exact s415

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg13 : ∀ i : Fin 32, StepTab (idIndex 13 i) := by
  intro i
  fin_cases i
  · exact s416
  · exact s417
  · exact s418
  · exact s419
  · exact s420
  · exact s421
  · exact s422
  · exact s423
  · exact s424
  · exact s425
  · exact s426
  · exact s427
  · exact s428
  · exact s429
  · exact s430
  · exact s431
  · exact s432
  · exact s433
  · exact s434
  · exact s435
  · exact s436
  · exact s437
  · exact s438
  · exact s439
  · exact s440
  · exact s441
  · exact s442
  · exact s443
  · exact s444
  · exact s445
  · exact s446
  · exact s447

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg14 : ∀ i : Fin 32, StepTab (idIndex 14 i) := by
  intro i
  fin_cases i
  · exact s448
  · exact s449
  · exact s450
  · exact s451
  · exact s452
  · exact s453
  · exact s454
  · exact s455
  · exact s456
  · exact s457
  · exact s458
  · exact s459
  · exact s460
  · exact s461
  · exact s462
  · exact s463
  · exact s464
  · exact s465
  · exact s466
  · exact s467
  · exact s468
  · exact s469
  · exact s470
  · exact s471
  · exact s472
  · exact s473
  · exact s474
  · exact s475
  · exact s476
  · exact s477
  · exact s478
  · exact s479

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg15 : ∀ i : Fin 32, StepTab (idIndex 15 i) := by
  intro i
  fin_cases i
  · exact s480
  · exact s481
  · exact s482
  · exact s483
  · exact s484
  · exact s485
  · exact s486
  · exact s487
  · exact s488
  · exact s489
  · exact s490
  · exact s491
  · exact s492
  · exact s493
  · exact s494
  · exact s495
  · exact s496
  · exact s497
  · exact s498
  · exact s499
  · exact s500
  · exact s501
  · exact s502
  · exact s503
  · exact s504
  · exact s505
  · exact s506
  · exact s507
  · exact s508
  · exact s509
  · exact s510
  · exact s511

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg16 : ∀ i : Fin 32, StepTab (idIndex 16 i) := by
  intro i
  fin_cases i
  · exact s512
  · exact s513
  · exact s514
  · exact s515
  · exact s516
  · exact s517
  · exact s518
  · exact s519
  · exact s520
  · exact s521
  · exact s522
  · exact s523
  · exact s524
  · exact s525
  · exact s526
  · exact s527
  · exact s528
  · exact s529
  · exact s530
  · exact s531
  · exact s532
  · exact s533
  · exact s534
  · exact s535
  · exact s536
  · exact s537
  · exact s538
  · exact s539
  · exact s540
  · exact s541
  · exact s542
  · exact s543

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg17 : ∀ i : Fin 32, StepTab (idIndex 17 i) := by
  intro i
  fin_cases i
  · exact s544
  · exact s545
  · exact s546
  · exact s547
  · exact s548
  · exact s549
  · exact s550
  · exact s551
  · exact s552
  · exact s553
  · exact s554
  · exact s555
  · exact s556
  · exact s557
  · exact s558
  · exact s559
  · exact s560
  · exact s561
  · exact s562
  · exact s563
  · exact s564
  · exact s565
  · exact s566
  · exact s567
  · exact s568
  · exact s569
  · exact s570
  · exact s571
  · exact s572
  · exact s573
  · exact s574
  · exact s575

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg18 : ∀ i : Fin 32, StepTab (idIndex 18 i) := by
  intro i
  fin_cases i
  · exact s576
  · exact s577
  · exact s578
  · exact s579
  · exact s580
  · exact s581
  · exact s582
  · exact s583
  · exact s584
  · exact s585
  · exact s586
  · exact s587
  · exact s588
  · exact s589
  · exact s590
  · exact s591
  · exact s592
  · exact s593
  · exact s594
  · exact s595
  · exact s596
  · exact s597
  · exact s598
  · exact s599
  · exact s600
  · exact s601
  · exact s602
  · exact s603
  · exact s604
  · exact s605
  · exact s606
  · exact s607

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg19 : ∀ i : Fin 32, StepTab (idIndex 19 i) := by
  intro i
  fin_cases i
  · exact s608
  · exact s609
  · exact s610
  · exact s611
  · exact s612
  · exact s613
  · exact s614
  · exact s615
  · exact s616
  · exact s617
  · exact s618
  · exact s619
  · exact s620
  · exact s621
  · exact s622
  · exact s623
  · exact s624
  · exact s625
  · exact s626
  · exact s627
  · exact s628
  · exact s629
  · exact s630
  · exact s631
  · exact s632
  · exact s633
  · exact s634
  · exact s635
  · exact s636
  · exact s637
  · exact s638
  · exact s639

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg20 : ∀ i : Fin 32, StepTab (idIndex 20 i) := by
  intro i
  fin_cases i
  · exact s640
  · exact s641
  · exact s642
  · exact s643
  · exact s644
  · exact s645
  · exact s646
  · exact s647
  · exact s648
  · exact s649
  · exact s650
  · exact s651
  · exact s652
  · exact s653
  · exact s654
  · exact s655
  · exact s656
  · exact s657
  · exact s658
  · exact s659
  · exact s660
  · exact s661
  · exact s662
  · exact s663
  · exact s664
  · exact s665
  · exact s666
  · exact s667
  · exact s668
  · exact s669
  · exact s670
  · exact s671

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg21 : ∀ i : Fin 32, StepTab (idIndex 21 i) := by
  intro i
  fin_cases i
  · exact s672
  · exact s673
  · exact s674
  · exact s675
  · exact s676
  · exact s677
  · exact s678
  · exact s679
  · exact s680
  · exact s681
  · exact s682
  · exact s683
  · exact s684
  · exact s685
  · exact s686
  · exact s687
  · exact s688
  · exact s689
  · exact s690
  · exact s691
  · exact s692
  · exact s693
  · exact s694
  · exact s695
  · exact s696
  · exact s697
  · exact s698
  · exact s699
  · exact s700
  · exact s701
  · exact s702
  · exact s703

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg22 : ∀ i : Fin 32, StepTab (idIndex 22 i) := by
  intro i
  fin_cases i
  · exact s704
  · exact s705
  · exact s706
  · exact s707
  · exact s708
  · exact s709
  · exact s710
  · exact s711
  · exact s712
  · exact s713
  · exact s714
  · exact s715
  · exact s716
  · exact s717
  · exact s718
  · exact s719
  · exact s720
  · exact s721
  · exact s722
  · exact s723
  · exact s724
  · exact s725
  · exact s726
  · exact s727
  · exact s728
  · exact s729
  · exact s730
  · exact s731
  · exact s732
  · exact s733
  · exact s734
  · exact s735

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg23 : ∀ i : Fin 32, StepTab (idIndex 23 i) := by
  intro i
  fin_cases i
  · exact s736
  · exact s737
  · exact s738
  · exact s739
  · exact s740
  · exact s741
  · exact s742
  · exact s743
  · exact s744
  · exact s745
  · exact s746
  · exact s747
  · exact s748
  · exact s749
  · exact s750
  · exact s751
  · exact s752
  · exact s753
  · exact s754
  · exact s755
  · exact s756
  · exact s757
  · exact s758
  · exact s759
  · exact s760
  · exact s761
  · exact s762
  · exact s763
  · exact s764
  · exact s765
  · exact s766
  · exact s767

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg24 : ∀ i : Fin 32, StepTab (idIndex 24 i) := by
  intro i
  fin_cases i
  · exact s768
  · exact s769
  · exact s770
  · exact s771
  · exact s772
  · exact s773
  · exact s774
  · exact s775
  · exact s776
  · exact s777
  · exact s778
  · exact s779
  · exact s780
  · exact s781
  · exact s782
  · exact s783
  · exact s784
  · exact s785
  · exact s786
  · exact s787
  · exact s788
  · exact s789
  · exact s790
  · exact s791
  · exact s792
  · exact s793
  · exact s794
  · exact s795
  · exact s796
  · exact s797
  · exact s798
  · exact s799

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg25 : ∀ i : Fin 32, StepTab (idIndex 25 i) := by
  intro i
  fin_cases i
  · exact s800
  · exact s801
  · exact s802
  · exact s803
  · exact s804
  · exact s805
  · exact s806
  · exact s807
  · exact s808
  · exact s809
  · exact s810
  · exact s811
  · exact s812
  · exact s813
  · exact s814
  · exact s815
  · exact s816
  · exact s817
  · exact s818
  · exact s819
  · exact s820
  · exact s821
  · exact s822
  · exact s823
  · exact s824
  · exact s825
  · exact s826
  · exact s827
  · exact s828
  · exact s829
  · exact s830
  · exact s831

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg26 : ∀ i : Fin 32, StepTab (idIndex 26 i) := by
  intro i
  fin_cases i
  · exact s832
  · exact s833
  · exact s834
  · exact s835
  · exact s836
  · exact s837
  · exact s838
  · exact s839
  · exact s840
  · exact s841
  · exact s842
  · exact s843
  · exact s844
  · exact s845
  · exact s846
  · exact s847
  · exact s848
  · exact s849
  · exact s850
  · exact s851
  · exact s852
  · exact s853
  · exact s854
  · exact s855
  · exact s856
  · exact s857
  · exact s858
  · exact s859
  · exact s860
  · exact s861
  · exact s862
  · exact s863

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg27 : ∀ i : Fin 32, StepTab (idIndex 27 i) := by
  intro i
  fin_cases i
  · exact s864
  · exact s865
  · exact s866
  · exact s867
  · exact s868
  · exact s869
  · exact s870
  · exact s871
  · exact s872
  · exact s873
  · exact s874
  · exact s875
  · exact s876
  · exact s877
  · exact s878
  · exact s879
  · exact s880
  · exact s881
  · exact s882
  · exact s883
  · exact s884
  · exact s885
  · exact s886
  · exact s887
  · exact s888
  · exact s889
  · exact s890
  · exact s891
  · exact s892
  · exact s893
  · exact s894
  · exact s895

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg28 : ∀ i : Fin 32, StepTab (idIndex 28 i) := by
  intro i
  fin_cases i
  · exact s896
  · exact s897
  · exact s898
  · exact s899
  · exact s900
  · exact s901
  · exact s902
  · exact s903
  · exact s904
  · exact s905
  · exact s906
  · exact s907
  · exact s908
  · exact s909
  · exact s910
  · exact s911
  · exact s912
  · exact s913
  · exact s914
  · exact s915
  · exact s916
  · exact s917
  · exact s918
  · exact s919
  · exact s920
  · exact s921
  · exact s922
  · exact s923
  · exact s924
  · exact s925
  · exact s926
  · exact s927

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg29 : ∀ i : Fin 32, StepTab (idIndex 29 i) := by
  intro i
  fin_cases i
  · exact s928
  · exact s929
  · exact s930
  · exact s931
  · exact s932
  · exact s933
  · exact s934
  · exact s935
  · exact s936
  · exact s937
  · exact s938
  · exact s939
  · exact s940
  · exact s941
  · exact s942
  · exact s943
  · exact s944
  · exact s945
  · exact s946
  · exact s947
  · exact s948
  · exact s949
  · exact s950
  · exact s951
  · exact s952
  · exact s953
  · exact s954
  · exact s955
  · exact s956
  · exact s957
  · exact s958
  · exact s959

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg30 : ∀ i : Fin 32, StepTab (idIndex 30 i) := by
  intro i
  fin_cases i
  · exact s960
  · exact s961
  · exact s962
  · exact s963
  · exact s964
  · exact s965
  · exact s966
  · exact s967
  · exact s968
  · exact s969
  · exact s970
  · exact s971
  · exact s972
  · exact s973
  · exact s974
  · exact s975
  · exact s976
  · exact s977
  · exact s978
  · exact s979
  · exact s980
  · exact s981
  · exact s982
  · exact s983
  · exact s984
  · exact s985
  · exact s986
  · exact s987
  · exact s988
  · exact s989
  · exact s990
  · exact s991

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg31 : ∀ i : Fin 32, StepTab (idIndex 31 i) := by
  intro i
  fin_cases i
  · exact s992
  · exact s993
  · exact s994
  · exact s995
  · exact s996
  · exact s997
  · exact s998
  · exact s999
  · exact s1000
  · exact s1001
  · exact s1002
  · exact s1003
  · exact s1004
  · exact s1005
  · exact s1006
  · exact s1007
  · exact s1008
  · exact s1009
  · exact s1010
  · exact s1011
  · exact s1012
  · exact s1013
  · exact s1014
  · exact s1015
  · exact s1016
  · exact s1017
  · exact s1018
  · exact s1019
  · exact s1020
  · exact s1021
  · exact s1022
  · exact s1023

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg32 : ∀ i : Fin 32, StepTab (idIndex 32 i) := by
  intro i
  fin_cases i
  · exact s1024
  · exact s1025
  · exact s1026
  · exact s1027
  · exact s1028
  · exact s1029
  · exact s1030
  · exact s1031
  · exact s1032
  · exact s1033
  · exact s1034
  · exact s1035
  · exact s1036
  · exact s1037
  · exact s1038
  · exact s1039
  · exact s1040
  · exact s1041
  · exact s1042
  · exact s1043
  · exact s1044
  · exact s1045
  · exact s1046
  · exact s1047
  · exact s1048
  · exact s1049
  · exact s1050
  · exact s1051
  · exact s1052
  · exact s1053
  · exact s1054
  · exact s1055

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg33 : ∀ i : Fin 32, StepTab (idIndex 33 i) := by
  intro i
  fin_cases i
  · exact s1056
  · exact s1057
  · exact s1058
  · exact s1059
  · exact s1060
  · exact s1061
  · exact s1062
  · exact s1063
  · exact s1064
  · exact s1065
  · exact s1066
  · exact s1067
  · exact s1068
  · exact s1069
  · exact s1070
  · exact s1071
  · exact s1072
  · exact s1073
  · exact s1074
  · exact s1075
  · exact s1076
  · exact s1077
  · exact s1078
  · exact s1079
  · exact s1080
  · exact s1081
  · exact s1082
  · exact s1083
  · exact s1084
  · exact s1085
  · exact s1086
  · exact s1087

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg34 : ∀ i : Fin 32, StepTab (idIndex 34 i) := by
  intro i
  fin_cases i
  · exact s1088
  · exact s1089
  · exact s1090
  · exact s1091
  · exact s1092
  · exact s1093
  · exact s1094
  · exact s1095
  · exact s1096
  · exact s1097
  · exact s1098
  · exact s1099
  · exact s1100
  · exact s1101
  · exact s1102
  · exact s1103
  · exact s1104
  · exact s1105
  · exact s1106
  · exact s1107
  · exact s1108
  · exact s1109
  · exact s1110
  · exact s1111
  · exact s1112
  · exact s1113
  · exact s1114
  · exact s1115
  · exact s1116
  · exact s1117
  · exact s1118
  · exact s1119

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg35 : ∀ i : Fin 32, StepTab (idIndex 35 i) := by
  intro i
  fin_cases i
  · exact s1120
  · exact s1121
  · exact s1122
  · exact s1123
  · exact s1124
  · exact s1125
  · exact s1126
  · exact s1127
  · exact s1128
  · exact s1129
  · exact s1130
  · exact s1131
  · exact s1132
  · exact s1133
  · exact s1134
  · exact s1135
  · exact s1136
  · exact s1137
  · exact s1138
  · exact s1139
  · exact s1140
  · exact s1141
  · exact s1142
  · exact s1143
  · exact s1144
  · exact s1145
  · exact s1146
  · exact s1147
  · exact s1148
  · exact s1149
  · exact s1150
  · exact s1151

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg36 : ∀ i : Fin 32, StepTab (idIndex 36 i) := by
  intro i
  fin_cases i
  · exact s1152
  · exact s1153
  · exact s1154
  · exact s1155
  · exact s1156
  · exact s1157
  · exact s1158
  · exact s1159
  · exact s1160
  · exact s1161
  · exact s1162
  · exact s1163
  · exact s1164
  · exact s1165
  · exact s1166
  · exact s1167
  · exact s1168
  · exact s1169
  · exact s1170
  · exact s1171
  · exact s1172
  · exact s1173
  · exact s1174
  · exact s1175
  · exact s1176
  · exact s1177
  · exact s1178
  · exact s1179
  · exact s1180
  · exact s1181
  · exact s1182
  · exact s1183

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg37 : ∀ i : Fin 32, StepTab (idIndex 37 i) := by
  intro i
  fin_cases i
  · exact s1184
  · exact s1185
  · exact s1186
  · exact s1187
  · exact s1188
  · exact s1189
  · exact s1190
  · exact s1191
  · exact s1192
  · exact s1193
  · exact s1194
  · exact s1195
  · exact s1196
  · exact s1197
  · exact s1198
  · exact s1199
  · exact s1200
  · exact s1201
  · exact s1202
  · exact s1203
  · exact s1204
  · exact s1205
  · exact s1206
  · exact s1207
  · exact s1208
  · exact s1209
  · exact s1210
  · exact s1211
  · exact s1212
  · exact s1213
  · exact s1214
  · exact s1215

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg38 : ∀ i : Fin 32, StepTab (idIndex 38 i) := by
  intro i
  fin_cases i
  · exact s1216
  · exact s1217
  · exact s1218
  · exact s1219
  · exact s1220
  · exact s1221
  · exact s1222
  · exact s1223
  · exact s1224
  · exact s1225
  · exact s1226
  · exact s1227
  · exact s1228
  · exact s1229
  · exact s1230
  · exact s1231
  · exact s1232
  · exact s1233
  · exact s1234
  · exact s1235
  · exact s1236
  · exact s1237
  · exact s1238
  · exact s1239
  · exact s1240
  · exact s1241
  · exact s1242
  · exact s1243
  · exact s1244
  · exact s1245
  · exact s1246
  · exact s1247

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg39 : ∀ i : Fin 32, StepTab (idIndex 39 i) := by
  intro i
  fin_cases i
  · exact s1248
  · exact s1249
  · exact s1250
  · exact s1251
  · exact s1252
  · exact s1253
  · exact s1254
  · exact s1255
  · exact s1256
  · exact s1257
  · exact s1258
  · exact s1259
  · exact s1260
  · exact s1261
  · exact s1262
  · exact s1263
  · exact s1264
  · exact s1265
  · exact s1266
  · exact s1267
  · exact s1268
  · exact s1269
  · exact s1270
  · exact s1271
  · exact s1272
  · exact s1273
  · exact s1274
  · exact s1275
  · exact s1276
  · exact s1277
  · exact s1278
  · exact s1279

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg40 : ∀ i : Fin 32, StepTab (idIndex 40 i) := by
  intro i
  fin_cases i
  · exact s1280
  · exact s1281
  · exact s1282
  · exact s1283
  · exact s1284
  · exact s1285
  · exact s1286
  · exact s1287
  · exact s1288
  · exact s1289
  · exact s1290
  · exact s1291
  · exact s1292
  · exact s1293
  · exact s1294
  · exact s1295
  · exact s1296
  · exact s1297
  · exact s1298
  · exact s1299
  · exact s1300
  · exact s1301
  · exact s1302
  · exact s1303
  · exact s1304
  · exact s1305
  · exact s1306
  · exact s1307
  · exact s1308
  · exact s1309
  · exact s1310
  · exact s1311

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg41 : ∀ i : Fin 32, StepTab (idIndex 41 i) := by
  intro i
  fin_cases i
  · exact s1312
  · exact s1313
  · exact s1314
  · exact s1315
  · exact s1316
  · exact s1317
  · exact s1318
  · exact s1319
  · exact s1320
  · exact s1321
  · exact s1322
  · exact s1323
  · exact s1324
  · exact s1325
  · exact s1326
  · exact s1327
  · exact s1328
  · exact s1329
  · exact s1330
  · exact s1331
  · exact s1332
  · exact s1333
  · exact s1334
  · exact s1335
  · exact s1336
  · exact s1337
  · exact s1338
  · exact s1339
  · exact s1340
  · exact s1341
  · exact s1342
  · exact s1343

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg42 : ∀ i : Fin 32, StepTab (idIndex 42 i) := by
  intro i
  fin_cases i
  · exact s1344
  · exact s1345
  · exact s1346
  · exact s1347
  · exact s1348
  · exact s1349
  · exact s1350
  · exact s1351
  · exact s1352
  · exact s1353
  · exact s1354
  · exact s1355
  · exact s1356
  · exact s1357
  · exact s1358
  · exact s1359
  · exact s1360
  · exact s1361
  · exact s1362
  · exact s1363
  · exact s1364
  · exact s1365
  · exact s1366
  · exact s1367
  · exact s1368
  · exact s1369
  · exact s1370
  · exact s1371
  · exact s1372
  · exact s1373
  · exact s1374
  · exact s1375

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg43 : ∀ i : Fin 32, StepTab (idIndex 43 i) := by
  intro i
  fin_cases i
  · exact s1376
  · exact s1377
  · exact s1378
  · exact s1379
  · exact s1380
  · exact s1381
  · exact s1382
  · exact s1383
  · exact s1384
  · exact s1385
  · exact s1386
  · exact s1387
  · exact s1388
  · exact s1389
  · exact s1390
  · exact s1391
  · exact s1392
  · exact s1393
  · exact s1394
  · exact s1395
  · exact s1396
  · exact s1397
  · exact s1398
  · exact s1399
  · exact s1400
  · exact s1401
  · exact s1402
  · exact s1403
  · exact s1404
  · exact s1405
  · exact s1406
  · exact s1407

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg44 : ∀ i : Fin 32, StepTab (idIndex 44 i) := by
  intro i
  fin_cases i
  · exact s1408
  · exact s1409
  · exact s1410
  · exact s1411
  · exact s1412
  · exact s1413
  · exact s1414
  · exact s1415
  · exact s1416
  · exact s1417
  · exact s1418
  · exact s1419
  · exact s1420
  · exact s1421
  · exact s1422
  · exact s1423
  · exact s1424
  · exact s1425
  · exact s1426
  · exact s1427
  · exact s1428
  · exact s1429
  · exact s1430
  · exact s1431
  · exact s1432
  · exact s1433
  · exact s1434
  · exact s1435
  · exact s1436
  · exact s1437
  · exact s1438
  · exact s1439

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg45 : ∀ i : Fin 32, StepTab (idIndex 45 i) := by
  intro i
  fin_cases i
  · exact s1440
  · exact s1441
  · exact s1442
  · exact s1443
  · exact s1444
  · exact s1445
  · exact s1446
  · exact s1447
  · exact s1448
  · exact s1449
  · exact s1450
  · exact s1451
  · exact s1452
  · exact s1453
  · exact s1454
  · exact s1455
  · exact s1456
  · exact s1457
  · exact s1458
  · exact s1459
  · exact s1460
  · exact s1461
  · exact s1462
  · exact s1463
  · exact s1464
  · exact s1465
  · exact s1466
  · exact s1467
  · exact s1468
  · exact s1469
  · exact s1470
  · exact s1471

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg46 : ∀ i : Fin 32, StepTab (idIndex 46 i) := by
  intro i
  fin_cases i
  · exact s1472
  · exact s1473
  · exact s1474
  · exact s1475
  · exact s1476
  · exact s1477
  · exact s1478
  · exact s1479
  · exact s1480
  · exact s1481
  · exact s1482
  · exact s1483
  · exact s1484
  · exact s1485
  · exact s1486
  · exact s1487
  · exact s1488
  · exact s1489
  · exact s1490
  · exact s1491
  · exact s1492
  · exact s1493
  · exact s1494
  · exact s1495
  · exact s1496
  · exact s1497
  · exact s1498
  · exact s1499
  · exact s1500
  · exact s1501
  · exact s1502
  · exact s1503

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg47 : ∀ i : Fin 32, StepTab (idIndex 47 i) := by
  intro i
  fin_cases i
  · exact s1504
  · exact s1505
  · exact s1506
  · exact s1507
  · exact s1508
  · exact s1509
  · exact s1510
  · exact s1511
  · exact s1512
  · exact s1513
  · exact s1514
  · exact s1515
  · exact s1516
  · exact s1517
  · exact s1518
  · exact s1519
  · exact s1520
  · exact s1521
  · exact s1522
  · exact s1523
  · exact s1524
  · exact s1525
  · exact s1526
  · exact s1527
  · exact s1528
  · exact s1529
  · exact s1530
  · exact s1531
  · exact s1532
  · exact s1533
  · exact s1534
  · exact s1535

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg48 : ∀ i : Fin 32, StepTab (idIndex 48 i) := by
  intro i
  fin_cases i
  · exact s1536
  · exact s1537
  · exact s1538
  · exact s1539
  · exact s1540
  · exact s1541
  · exact s1542
  · exact s1543
  · exact s1544
  · exact s1545
  · exact s1546
  · exact s1547
  · exact s1548
  · exact s1549
  · exact s1550
  · exact s1551
  · exact s1552
  · exact s1553
  · exact s1554
  · exact s1555
  · exact s1556
  · exact s1557
  · exact s1558
  · exact s1559
  · exact s1560
  · exact s1561
  · exact s1562
  · exact s1563
  · exact s1564
  · exact s1565
  · exact s1566
  · exact s1567

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg49 : ∀ i : Fin 32, StepTab (idIndex 49 i) := by
  intro i
  fin_cases i
  · exact s1568
  · exact s1569
  · exact s1570
  · exact s1571
  · exact s1572
  · exact s1573
  · exact s1574
  · exact s1575
  · exact s1576
  · exact s1577
  · exact s1578
  · exact s1579
  · exact s1580
  · exact s1581
  · exact s1582
  · exact s1583
  · exact s1584
  · exact s1585
  · exact s1586
  · exact s1587
  · exact s1588
  · exact s1589
  · exact s1590
  · exact s1591
  · exact s1592
  · exact s1593
  · exact s1594
  · exact s1595
  · exact s1596
  · exact s1597
  · exact s1598
  · exact s1599

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg50 : ∀ i : Fin 32, StepTab (idIndex 50 i) := by
  intro i
  fin_cases i
  · exact s1600
  · exact s1601
  · exact s1602
  · exact s1603
  · exact s1604
  · exact s1605
  · exact s1606
  · exact s1607
  · exact s1608
  · exact s1609
  · exact s1610
  · exact s1611
  · exact s1612
  · exact s1613
  · exact s1614
  · exact s1615
  · exact s1616
  · exact s1617
  · exact s1618
  · exact s1619
  · exact s1620
  · exact s1621
  · exact s1622
  · exact s1623
  · exact s1624
  · exact s1625
  · exact s1626
  · exact s1627
  · exact s1628
  · exact s1629
  · exact s1630
  · exact s1631

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg51 : ∀ i : Fin 32, StepTab (idIndex 51 i) := by
  intro i
  fin_cases i
  · exact s1632
  · exact s1633
  · exact s1634
  · exact s1635
  · exact s1636
  · exact s1637
  · exact s1638
  · exact s1639
  · exact s1640
  · exact s1641
  · exact s1642
  · exact s1643
  · exact s1644
  · exact s1645
  · exact s1646
  · exact s1647
  · exact s1648
  · exact s1649
  · exact s1650
  · exact s1651
  · exact s1652
  · exact s1653
  · exact s1654
  · exact s1655
  · exact s1656
  · exact s1657
  · exact s1658
  · exact s1659
  · exact s1660
  · exact s1661
  · exact s1662
  · exact s1663

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg52 : ∀ i : Fin 32, StepTab (idIndex 52 i) := by
  intro i
  fin_cases i
  · exact s1664
  · exact s1665
  · exact s1666
  · exact s1667
  · exact s1668
  · exact s1669
  · exact s1670
  · exact s1671
  · exact s1672
  · exact s1673
  · exact s1674
  · exact s1675
  · exact s1676
  · exact s1677
  · exact s1678
  · exact s1679
  · exact s1680
  · exact s1681
  · exact s1682
  · exact s1683
  · exact s1684
  · exact s1685
  · exact s1686
  · exact s1687
  · exact s1688
  · exact s1689
  · exact s1690
  · exact s1691
  · exact s1692
  · exact s1693
  · exact s1694
  · exact s1695

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg53 : ∀ i : Fin 32, StepTab (idIndex 53 i) := by
  intro i
  fin_cases i
  · exact s1696
  · exact s1697
  · exact s1698
  · exact s1699
  · exact s1700
  · exact s1701
  · exact s1702
  · exact s1703
  · exact s1704
  · exact s1705
  · exact s1706
  · exact s1707
  · exact s1708
  · exact s1709
  · exact s1710
  · exact s1711
  · exact s1712
  · exact s1713
  · exact s1714
  · exact s1715
  · exact s1716
  · exact s1717
  · exact s1718
  · exact s1719
  · exact s1720
  · exact s1721
  · exact s1722
  · exact s1723
  · exact s1724
  · exact s1725
  · exact s1726
  · exact s1727

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg54 : ∀ i : Fin 32, StepTab (idIndex 54 i) := by
  intro i
  fin_cases i
  · exact s1728
  · exact s1729
  · exact s1730
  · exact s1731
  · exact s1732
  · exact s1733
  · exact s1734
  · exact s1735
  · exact s1736
  · exact s1737
  · exact s1738
  · exact s1739
  · exact s1740
  · exact s1741
  · exact s1742
  · exact s1743
  · exact s1744
  · exact s1745
  · exact s1746
  · exact s1747
  · exact s1748
  · exact s1749
  · exact s1750
  · exact s1751
  · exact s1752
  · exact s1753
  · exact s1754
  · exact s1755
  · exact s1756
  · exact s1757
  · exact s1758
  · exact s1759

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg55 : ∀ i : Fin 32, StepTab (idIndex 55 i) := by
  intro i
  fin_cases i
  · exact s1760
  · exact s1761
  · exact s1762
  · exact s1763
  · exact s1764
  · exact s1765
  · exact s1766
  · exact s1767
  · exact s1768
  · exact s1769
  · exact s1770
  · exact s1771
  · exact s1772
  · exact s1773
  · exact s1774
  · exact s1775
  · exact s1776
  · exact s1777
  · exact s1778
  · exact s1779
  · exact s1780
  · exact s1781
  · exact s1782
  · exact s1783
  · exact s1784
  · exact s1785
  · exact s1786
  · exact s1787
  · exact s1788
  · exact s1789
  · exact s1790
  · exact s1791

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg56 : ∀ i : Fin 32, StepTab (idIndex 56 i) := by
  intro i
  fin_cases i
  · exact s1792
  · exact s1793
  · exact s1794
  · exact s1795
  · exact s1796
  · exact s1797
  · exact s1798
  · exact s1799
  · exact s1800
  · exact s1801
  · exact s1802
  · exact s1803
  · exact s1804
  · exact s1805
  · exact s1806
  · exact s1807
  · exact s1808
  · exact s1809
  · exact s1810
  · exact s1811
  · exact s1812
  · exact s1813
  · exact s1814
  · exact s1815
  · exact s1816
  · exact s1817
  · exact s1818
  · exact s1819
  · exact s1820
  · exact s1821
  · exact s1822
  · exact s1823

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg57 : ∀ i : Fin 32, StepTab (idIndex 57 i) := by
  intro i
  fin_cases i
  · exact s1824
  · exact s1825
  · exact s1826
  · exact s1827
  · exact s1828
  · exact s1829
  · exact s1830
  · exact s1831
  · exact s1832
  · exact s1833
  · exact s1834
  · exact s1835
  · exact s1836
  · exact s1837
  · exact s1838
  · exact s1839
  · exact s1840
  · exact s1841
  · exact s1842
  · exact s1843
  · exact s1844
  · exact s1845
  · exact s1846
  · exact s1847
  · exact s1848
  · exact s1849
  · exact s1850
  · exact s1851
  · exact s1852
  · exact s1853
  · exact s1854
  · exact s1855

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg58 : ∀ i : Fin 32, StepTab (idIndex 58 i) := by
  intro i
  fin_cases i
  · exact s1856
  · exact s1857
  · exact s1858
  · exact s1859
  · exact s1860
  · exact s1861
  · exact s1862
  · exact s1863
  · exact s1864
  · exact s1865
  · exact s1866
  · exact s1867
  · exact s1868
  · exact s1869
  · exact s1870
  · exact s1871
  · exact s1872
  · exact s1873
  · exact s1874
  · exact s1875
  · exact s1876
  · exact s1877
  · exact s1878
  · exact s1879
  · exact s1880
  · exact s1881
  · exact s1882
  · exact s1883
  · exact s1884
  · exact s1885
  · exact s1886
  · exact s1887

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg59 : ∀ i : Fin 32, StepTab (idIndex 59 i) := by
  intro i
  fin_cases i
  · exact s1888
  · exact s1889
  · exact s1890
  · exact s1891
  · exact s1892
  · exact s1893
  · exact s1894
  · exact s1895
  · exact s1896
  · exact s1897
  · exact s1898
  · exact s1899
  · exact s1900
  · exact s1901
  · exact s1902
  · exact s1903
  · exact s1904
  · exact s1905
  · exact s1906
  · exact s1907
  · exact s1908
  · exact s1909
  · exact s1910
  · exact s1911
  · exact s1912
  · exact s1913
  · exact s1914
  · exact s1915
  · exact s1916
  · exact s1917
  · exact s1918
  · exact s1919

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg60 : ∀ i : Fin 32, StepTab (idIndex 60 i) := by
  intro i
  fin_cases i
  · exact s1920
  · exact s1921
  · exact s1922
  · exact s1923
  · exact s1924
  · exact s1925
  · exact s1926
  · exact s1927
  · exact s1928
  · exact s1929
  · exact s1930
  · exact s1931
  · exact s1932
  · exact s1933
  · exact s1934
  · exact s1935
  · exact s1936
  · exact s1937
  · exact s1938
  · exact s1939
  · exact s1940
  · exact s1941
  · exact s1942
  · exact s1943
  · exact s1944
  · exact s1945
  · exact s1946
  · exact s1947
  · exact s1948
  · exact s1949
  · exact s1950
  · exact s1951

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg61 : ∀ i : Fin 32, StepTab (idIndex 61 i) := by
  intro i
  fin_cases i
  · exact s1952
  · exact s1953
  · exact s1954
  · exact s1955
  · exact s1956
  · exact s1957
  · exact s1958
  · exact s1959
  · exact s1960
  · exact s1961
  · exact s1962
  · exact s1963
  · exact s1964
  · exact s1965
  · exact s1966
  · exact s1967
  · exact s1968
  · exact s1969
  · exact s1970
  · exact s1971
  · exact s1972
  · exact s1973
  · exact s1974
  · exact s1975
  · exact s1976
  · exact s1977
  · exact s1978
  · exact s1979
  · exact s1980
  · exact s1981
  · exact s1982
  · exact s1983

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg62 : ∀ i : Fin 32, StepTab (idIndex 62 i) := by
  intro i
  fin_cases i
  · exact s1984
  · exact s1985
  · exact s1986
  · exact s1987
  · exact s1988
  · exact s1989
  · exact s1990
  · exact s1991
  · exact s1992
  · exact s1993
  · exact s1994
  · exact s1995
  · exact s1996
  · exact s1997
  · exact s1998
  · exact s1999
  · exact s2000
  · exact s2001
  · exact s2002
  · exact s2003
  · exact s2004
  · exact s2005
  · exact s2006
  · exact s2007
  · exact s2008
  · exact s2009
  · exact s2010
  · exact s2011
  · exact s2012
  · exact s2013
  · exact s2014
  · exact s2015

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev sg63 : ∀ i : Fin 32, StepTab (idIndex 63 i) := by
  intro i
  fin_cases i
  · exact s2016
  · exact s2017
  · exact s2018
  · exact s2019
  · exact s2020
  · exact s2021
  · exact s2022
  · exact s2023
  · exact s2024
  · exact s2025
  · exact s2026
  · exact s2027
  · exact s2028
  · exact s2029
  · exact s2030
  · exact s2031
  · exact s2032
  · exact s2033
  · exact s2034
  · exact s2035
  · exact s2036
  · exact s2037
  · exact s2038
  · exact s2039
  · exact s2040
  · exact s2041
  · exact s2042
  · exact s2043
  · exact s2044
  · exact s2045
  · exact s2046
  · exact s2047

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev step_T (u : Fin 2048) : StepTab u := by
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, StepTab (idIndex k i) := by
    intro k
    fin_cases k
    · exact sg0
    · exact sg1
    · exact sg2
    · exact sg3
    · exact sg4
    · exact sg5
    · exact sg6
    · exact sg7
    · exact sg8
    · exact sg9
    · exact sg10
    · exact sg11
    · exact sg12
    · exact sg13
    · exact sg14
    · exact sg15
    · exact sg16
    · exact sg17
    · exact sg18
    · exact sg19
    · exact sg20
    · exact sg21
    · exact sg22
    · exact sg23
    · exact sg24
    · exact sg25
    · exact sg26
    · exact sg27
    · exact sg28
    · exact sg29
    · exact sg30
    · exact sg31
    · exact sg32
    · exact sg33
    · exact sg34
    · exact sg35
    · exact sg36
    · exact sg37
    · exact sg38
    · exact sg39
    · exact sg40
    · exact sg41
    · exact sg42
    · exact sg43
    · exact sg44
    · exact sg45
    · exact sg46
    · exact sg47
    · exact sg48
    · exact sg49
    · exact sg50
    · exact sg51
    · exact sg52
    · exact sg53
    · exact sg54
    · exact sg55
    · exact sg56
    · exact sg57
    · exact sg58
    · exact sg59
    · exact sg60
    · exact sg61
    · exact sg62
    · exact sg63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

theorem step_all (n : ℕ) (hn : n < 12) (u : Fin 2048) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := step_T u n hn

theorem G_eq_T (n : ℕ) (hn : n ≤ 12) : ∀ u : Fin 2048, G n u = tb (tabT n) u.val := by
  induction n with
  | zero => exact base_T
  | succ n ih =>
    intro u
    rw [G_succ]
    have ih' := ih (by omega)
    simp only [ih']
    exact step_all n (by omega) u

def DiffTab (u : Fin 2048) : Prop :=
    tb (tabT 12) u.val + 66 * tb (tabT 10) u.val + 495 * tb (tabT 8) u.val + 924 * tb (tabT 6) u.val + 495 * tb (tabT 4) u.val + 66 * tb (tabT 2) u.val + tb (tabT 0) u.val =
      12 * tb (tabT 11) u.val + 220 * tb (tabT 9) u.val + 792 * tb (tabT 7) u.val + 792 * tb (tabT 5) u.val + 220 * tb (tabT 3) u.val + 12 * tb (tabT 1) u.val

instance (u : Fin 2048) : Decidable (DiffTab u) := by
  unfold DiffTab
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_0 : ∀ i : Fin 32, DiffTab (idIndex 0 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_1 : ∀ i : Fin 32, DiffTab (idIndex 1 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_2 : ∀ i : Fin 32, DiffTab (idIndex 2 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_3 : ∀ i : Fin 32, DiffTab (idIndex 3 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_4 : ∀ i : Fin 32, DiffTab (idIndex 4 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_5 : ∀ i : Fin 32, DiffTab (idIndex 5 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_6 : ∀ i : Fin 32, DiffTab (idIndex 6 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_7 : ∀ i : Fin 32, DiffTab (idIndex 7 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_8 : ∀ i : Fin 32, DiffTab (idIndex 8 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_9 : ∀ i : Fin 32, DiffTab (idIndex 9 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_10 : ∀ i : Fin 32, DiffTab (idIndex 10 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_11 : ∀ i : Fin 32, DiffTab (idIndex 11 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_12 : ∀ i : Fin 32, DiffTab (idIndex 12 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_13 : ∀ i : Fin 32, DiffTab (idIndex 13 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_14 : ∀ i : Fin 32, DiffTab (idIndex 14 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_15 : ∀ i : Fin 32, DiffTab (idIndex 15 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_16 : ∀ i : Fin 32, DiffTab (idIndex 16 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_17 : ∀ i : Fin 32, DiffTab (idIndex 17 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_18 : ∀ i : Fin 32, DiffTab (idIndex 18 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_19 : ∀ i : Fin 32, DiffTab (idIndex 19 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_20 : ∀ i : Fin 32, DiffTab (idIndex 20 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_21 : ∀ i : Fin 32, DiffTab (idIndex 21 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_22 : ∀ i : Fin 32, DiffTab (idIndex 22 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_23 : ∀ i : Fin 32, DiffTab (idIndex 23 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_24 : ∀ i : Fin 32, DiffTab (idIndex 24 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_25 : ∀ i : Fin 32, DiffTab (idIndex 25 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_26 : ∀ i : Fin 32, DiffTab (idIndex 26 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_27 : ∀ i : Fin 32, DiffTab (idIndex 27 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_28 : ∀ i : Fin 32, DiffTab (idIndex 28 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_29 : ∀ i : Fin 32, DiffTab (idIndex 29 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_30 : ∀ i : Fin 32, DiffTab (idIndex 30 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_31 : ∀ i : Fin 32, DiffTab (idIndex 31 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_32 : ∀ i : Fin 32, DiffTab (idIndex 32 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_33 : ∀ i : Fin 32, DiffTab (idIndex 33 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_34 : ∀ i : Fin 32, DiffTab (idIndex 34 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_35 : ∀ i : Fin 32, DiffTab (idIndex 35 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_36 : ∀ i : Fin 32, DiffTab (idIndex 36 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_37 : ∀ i : Fin 32, DiffTab (idIndex 37 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_38 : ∀ i : Fin 32, DiffTab (idIndex 38 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_39 : ∀ i : Fin 32, DiffTab (idIndex 39 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_40 : ∀ i : Fin 32, DiffTab (idIndex 40 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_41 : ∀ i : Fin 32, DiffTab (idIndex 41 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_42 : ∀ i : Fin 32, DiffTab (idIndex 42 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_43 : ∀ i : Fin 32, DiffTab (idIndex 43 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_44 : ∀ i : Fin 32, DiffTab (idIndex 44 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_45 : ∀ i : Fin 32, DiffTab (idIndex 45 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_46 : ∀ i : Fin 32, DiffTab (idIndex 46 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_47 : ∀ i : Fin 32, DiffTab (idIndex 47 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_48 : ∀ i : Fin 32, DiffTab (idIndex 48 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_49 : ∀ i : Fin 32, DiffTab (idIndex 49 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_50 : ∀ i : Fin 32, DiffTab (idIndex 50 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_51 : ∀ i : Fin 32, DiffTab (idIndex 51 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_52 : ∀ i : Fin 32, DiffTab (idIndex 52 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_53 : ∀ i : Fin 32, DiffTab (idIndex 53 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_54 : ∀ i : Fin 32, DiffTab (idIndex 54 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_55 : ∀ i : Fin 32, DiffTab (idIndex 55 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_56 : ∀ i : Fin 32, DiffTab (idIndex 56 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_57 : ∀ i : Fin 32, DiffTab (idIndex 57 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_58 : ∀ i : Fin 32, DiffTab (idIndex 58 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_59 : ∀ i : Fin 32, DiffTab (idIndex 59 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_60 : ∀ i : Fin 32, DiffTab (idIndex 60 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_61 : ∀ i : Fin 32, DiffTab (idIndex 61 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_62 : ∀ i : Fin 32, DiffTab (idIndex 62 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_63 : ∀ i : Fin 32, DiffTab (idIndex 63 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base (u : Fin 2048) : tb (tabT 12) u.val + 66 * tb (tabT 10) u.val + 495 * tb (tabT 8) u.val + 924 * tb (tabT 6) u.val + 495 * tb (tabT 4) u.val + 66 * tb (tabT 2) u.val + tb (tabT 0) u.val =
      12 * tb (tabT 11) u.val + 220 * tb (tabT 9) u.val + 792 * tb (tabT 7) u.val + 792 * tb (tabT 5) u.val + 220 * tb (tabT 3) u.val + 12 * tb (tabT 1) u.val := by
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, DiffTab (idIndex k i) := by
    intro k
    fin_cases k
    · exact tab_base_chunk_0
    · exact tab_base_chunk_1
    · exact tab_base_chunk_2
    · exact tab_base_chunk_3
    · exact tab_base_chunk_4
    · exact tab_base_chunk_5
    · exact tab_base_chunk_6
    · exact tab_base_chunk_7
    · exact tab_base_chunk_8
    · exact tab_base_chunk_9
    · exact tab_base_chunk_10
    · exact tab_base_chunk_11
    · exact tab_base_chunk_12
    · exact tab_base_chunk_13
    · exact tab_base_chunk_14
    · exact tab_base_chunk_15
    · exact tab_base_chunk_16
    · exact tab_base_chunk_17
    · exact tab_base_chunk_18
    · exact tab_base_chunk_19
    · exact tab_base_chunk_20
    · exact tab_base_chunk_21
    · exact tab_base_chunk_22
    · exact tab_base_chunk_23
    · exact tab_base_chunk_24
    · exact tab_base_chunk_25
    · exact tab_base_chunk_26
    · exact tab_base_chunk_27
    · exact tab_base_chunk_28
    · exact tab_base_chunk_29
    · exact tab_base_chunk_30
    · exact tab_base_chunk_31
    · exact tab_base_chunk_32
    · exact tab_base_chunk_33
    · exact tab_base_chunk_34
    · exact tab_base_chunk_35
    · exact tab_base_chunk_36
    · exact tab_base_chunk_37
    · exact tab_base_chunk_38
    · exact tab_base_chunk_39
    · exact tab_base_chunk_40
    · exact tab_base_chunk_41
    · exact tab_base_chunk_42
    · exact tab_base_chunk_43
    · exact tab_base_chunk_44
    · exact tab_base_chunk_45
    · exact tab_base_chunk_46
    · exact tab_base_chunk_47
    · exact tab_base_chunk_48
    · exact tab_base_chunk_49
    · exact tab_base_chunk_50
    · exact tab_base_chunk_51
    · exact tab_base_chunk_52
    · exact tab_base_chunk_53
    · exact tab_base_chunk_54
    · exact tab_base_chunk_55
    · exact tab_base_chunk_56
    · exact tab_base_chunk_57
    · exact tab_base_chunk_58
    · exact tab_base_chunk_59
    · exact tab_base_chunk_60
    · exact tab_base_chunk_61
    · exact tab_base_chunk_62
    · exact tab_base_chunk_63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he, DiffTab] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

theorem G_base : ∀ u : Fin 2048,
    G 12 u + 66 * G 10 u + 495 * G 8 u + 924 * G 6 u + 495 * G 4 u + 66 * G 2 u + G 0 u =
      12 * G 11 u + 220 * G 9 u + 792 * G 7 u + 792 * G 5 u + 220 * G 3 u + 12 * G 1 u := by
  intro u
  rw [G_eq_T 12 (by norm_num) u, G_eq_T 11 (by norm_num) u, G_eq_T 10 (by norm_num) u, G_eq_T 9 (by norm_num) u, G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 2048,
    G (m + 12) u + 66 * G (m + 10) u + 495 * G (m + 8) u + 924 * G (m + 6) u + 495 * G (m + 4) u + 66 * G (m + 2) u + G m u =
      12 * G (m + 11) u + 220 * G (m + 9) u + 792 * G (m + 7) u + 792 * G (m + 5) u + 220 * G (m + 3) u + 12 * G (m + 1) u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 9 = (m + 9) + 1 by omega, show m + 1 + 10 = (m + 10) + 1 by omega, show m + 1 + 11 = (m + 11) + 1 by omega, show m + 1 + 12 = (m + 12) + 1 by omega]
    rw [G_succ (m + 12), G_succ (m + 10), G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m, G_succ (m + 11), G_succ (m + 9), G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 12) + 66 * a (m + 10) + 495 * a (m + 8) + 924 * a (m + 6) + 495 * a (m + 4) + 66 * a (m + 2) + a m =
      12 * a (m + 11) + 220 * a (m + 9) + 792 * a (m + 7) + 792 * a (m + 5) + 220 * a (m + 3) + 12 * a (m + 1) := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 2047

theorem G_vals : G 1 2047 = 15 ∧ G 2 2047 = 4999 ∧ G 3 2047 = 267004 ∧ G 4 2047 = 5207128 ∧ G 5 2047 = 55191061 ∧ G 6 2047 = 389769865 ∧ G 7 2047 = 2062131616 ∧ G 8 2047 = 8794967112 ∧ G 9 2047 = 31750272891 ∧ G 10 2047 = 100377252987 ∧ G 11 2047 = 284840809660 ∧ G 12 2047 = 738995422048 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num), G_eq_T 10 (by norm_num), G_eq_T 11 (by norm_num), G_eq_T 12 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 15 ∧ a 2 = 4999 ∧ a 3 = 267004 ∧ a 4 = 5207128 ∧ a 5 = 55191061 ∧ a 6 = 389769865 ∧ a 7 = 2062131616 ∧ a 8 = 8794967112 ∧ a 9 = 31750272891 ∧ a 10 = 100377252987 ∧ a 11 = 284840809660 ∧ a 12 = 738995422048 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  norm_num

theorem recurrence (n : ℕ) (hn : 13 ≤ n) :
    (a n : ℚ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 12) + 66 * a (m + 10) + 495 * a (m + 8) + 924 * a (m + 6) + 495 * a (m + 4) + 66 * a (m + 2) + a m : ℤ) : ℚ) =
      ((12 * a (m + 11) + 220 * a (m + 9) + 792 * a (m + 7) + 792 * a (m + 5) + 220 * a (m + 3) + 12 * a (m + 1) : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 12 - 1 = (m + 11) by omega, show m + 12 - 2 = (m + 10) by omega, show m + 12 - 3 = (m + 9) by omega, show m + 12 - 4 = (m + 8) by omega, show m + 12 - 5 = (m + 7) by omega, show m + 12 - 6 = (m + 6) by omega, show m + 12 - 7 = (m + 5) by omega, show m + 12 - 8 = (m + 4) by omega, show m + 12 - 9 = (m + 3) by omega, show m + 12 - 10 = (m + 2) by omega, show m + 12 - 11 = (m + 1) by omega, show m + 12 - 12 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 12 : PowerSeries ℚ) =
      X * (15 + 4819 * X + 208006 * X ^ 2 + 2329714 * X ^ 3 + 9235434 * X ^ 4 + 14869326 * X ^ 5 + 10156734 * X ^ 6 + 2833778 * X ^ 7 + 273635 * X ^ 8 + 5339 * X ^ 9) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 12 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 12 * (PowerSeries.mk F * X ^ 1) + C 66 * (PowerSeries.mk F * X ^ 2) - C 220 * (PowerSeries.mk F * X ^ 3) + C 495 * (PowerSeries.mk F * X ^ 4) - C 792 * (PowerSeries.mk F * X ^ 5) + C 924 * (PowerSeries.mk F * X ^ 6) - C 792 * (PowerSeries.mk F * X ^ 7) + C 495 * (PowerSeries.mk F * X ^ 8) - C 220 * (PowerSeries.mk F * X ^ 9) + C 66 * (PowerSeries.mk F * X ^ 10) - C 12 * (PowerSeries.mk F * X ^ 11) + C 1 * (PowerSeries.mk F * X ^ 12) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X * (15 + 4819 * X + 208006 * X ^ 2 + 2329714 * X ^ 3 + 9235434 * X ^ 4 + 14869326 * X ^ 5 + 10156734 * X ^ 6 + 2833778 * X ^ 7 + 273635 * X ^ 8 + 5339 * X ^ 9) : ℚ⟦X⟧) =
      C 15 * X ^ 1 + C 4819 * X ^ 2 + C 208006 * X ^ 3 + C 2329714 * X ^ 4 + C 9235434 * X ^ 5 + C 14869326 * X ^ 6 + C 10156734 * X ^ 7 + C 2833778 * X ^ 8 + C 273635 * X ^ 9 + C 5339 * X ^ 10 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 13
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 13 := ⟨k - 13, by omega⟩
    have hr := recurrence (j + 13) (by omega)
    simp only [show j + 13 - 1 = j + 12 by omega, show j + 13 - 2 = j + 11 by omega, show j + 13 - 3 = j + 10 by omega, show j + 13 - 4 = j + 9 by omega, show j + 13 - 5 = j + 8 by omega, show j + 13 - 6 = j + 7 by omega, show j + 13 - 7 = j + 6 by omega, show j + 13 - 8 = j + 5 by omega, show j + 13 - 9 = j + 4 by omega, show j + 13 - 10 = j + 3 by omega, show j + 13 - 11 = j + 2 by omega, show j + 13 - 12 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 13 by omega,
      show 1 ≤ j + 13 by omega,
      show 2 ≤ j + 13 by omega,
      show 3 ≤ j + 13 by omega,
      show 4 ≤ j + 13 by omega,
      show 5 ≤ j + 13 by omega,
      show 6 ≤ j + 13 by omega,
      show 7 ≤ j + 13 by omega,
      show 8 ≤ j + 13 by omega,
      show 9 ≤ j + 13 by omega,
      show 10 ≤ j + 13 by omega,
      show 11 ≤ j + 13 by omega,
      show 12 ≤ j + 13 by omega,
      show j + 13 - 0 = j + 13 by omega,
      show j + 13 - 1 = j + 12 by omega,
      show j + 13 - 2 = j + 11 by omega,
      show j + 13 - 3 = j + 10 by omega,
      show j + 13 - 4 = j + 9 by omega,
      show j + 13 - 5 = j + 8 by omega,
      show j + 13 - 6 = j + 7 by omega,
      show j + 13 - 7 = j + 6 by omega,
      show j + 13 - 8 = j + 5 by omega,
      show j + 13 - 9 = j + 4 by omega,
      show j + 13 - 10 = j + 3 by omega,
      show j + 13 - 11 = j + 2 by omega,
      show j + 13 - 12 = j + 1 by omega,
      show ¬ (j + 13 = 1) by omega,
      show ¬ (j + 13 = 2) by omega,
      show ¬ (j + 13 = 3) by omega,
      show ¬ (j + 13 = 4) by omega,
      show ¬ (j + 13 = 5) by omega,
      show ¬ (j + 13 = 6) by omega,
      show ¬ (j + 13 = 7) by omega,
      show ¬ (j + 13 = 8) by omega,
      show ¬ (j + 13 = 9) by omega,
      show ¬ (j + 13 = 10) by omega,
      show ¬ (j + 13 < 1) by omega,
      show ¬ (j + 12 < 1) by omega,
      show ¬ (j + 11 < 1) by omega,
      show ¬ (j + 10 < 1) by omega,
      show ¬ (j + 9 < 1) by omega,
      show ¬ (j + 8 < 1) by omega,
      show ¬ (j + 7 < 1) by omega,
      show ¬ (j + 6 < 1) by omega,
      show ¬ (j + 5 < 1) by omega,
      show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega,
      show ¬ (j + 2 < 1) by omega,
      show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a249966.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
