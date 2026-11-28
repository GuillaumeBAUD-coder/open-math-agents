import OMAStatements.S_oeis_a250390

/-!
A250390: exact seven-position/four-window adaptation of the threshold-chain proof
by @Salofe for A250064, PR #23285, commit bd4969a8ddc52c3bd7f8d30008570b9868fd00b6.
Conjecture: Colin Barker (2017); registered statement: @clementtrecourt, PR #19430.
The finite tables certify a recurrence on every subset state; linearity then proves
it for all levels. All computations are kernel checked.
-/

namespace OMA.A250390

open OMA.S_oeis_a250390 Finset

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
def fget (f : Fin 7 → Bool) (k : ℕ) : Bool := if h : k < 7 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 7 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 4 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 7 → Bool) : Prop := ∀ i < (4 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 7 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 7 → Fin (n + 1)) (v : ℕ) : Fin 7 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 7 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a250390.get x k ≤ n := by
  unfold OMA.S_oeis_a250390.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (4 : ℕ), cntW (fun _ => true) i = 4 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 7 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (4 : ℕ), ¬ Cy (fun t : Fin 4 => OMA.S_oeis_a250390.get x (i + t)) := by
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
  have step2 : ∀ i < (4 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 4 => OMA.S_oeis_a250390.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 7 := by have := t.isLt; omega
    unfold OMA.S_oeis_a250390.get fget Lt
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
noncomputable def M (n : ℕ) (T : Fin 7 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 7 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 7 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 7 → Fin (n + 2)) : Fin 7 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 7 → Bool) (x : Fin 7 → Fin (n + 1)) : Fin 7 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 7 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 7 → Bool) (x : Fin 7 → Fin (n + 1)) (p : Fin 7) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 7 → Bool) :
    M (n + 1) T = ∑ S : Fin 7 → Bool,
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
def row (u : Fin 128) : Fin 7 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 7 → Bool) : ℕ := ∑ p : Fin 7, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 128, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 7 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2

theorem cnt_row : ∀ u : Fin 128, cntW (row u) 0 = pcb (u.val &&& 15) ∧
    cntW (row u) 1 = pcb (u.val &&& 30) ∧
    cntW (row u) 2 = pcb (u.val &&& 60) ∧
    cntW (row u) 3 = pcb (u.val &&& 120) := by
  decide +kernel

/-- `Comp` on codes. -/
def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 15) ≤ 1 ∧ 3 ≤ pcb (t &&& 15)) ∧
    ¬ (pcb (s &&& 30) ≤ 1 ∧ 3 ≤ pcb (t &&& 30)) ∧
    ¬ (pcb (s &&& 60) ≤ 1 ∧ 3 ≤ pcb (t &&& 60)) ∧
    ¬ (pcb (s &&& 120) ≤ 1 ∧ 3 ≤ pcb (t &&& 120)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (4 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 128) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, b0, b1, b2, b3]

theorem sub_iff (w u : Fin 128) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 7
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (128 : ℕ) ≤ 2 ^ i := by
          calc (128 : ℕ) = 2 ^ 7 := by norm_num
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
def subs (u : Fin 128) : Finset (Fin 128) :=
  univ.filter (fun w : Fin 128 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 128 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 128, M n (row u) = G n u := by
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

theorem row_full : ∀ p, row 127 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 127 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 7 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 127 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 127)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 127 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 127 := by
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

theorem G_succ (n : ℕ) (u : Fin 128) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl

/-! ### Packed tables, with 24-bit slots, certified by the chain recursion. -/
def tb (T w : ℕ) : ℕ := (T >>> (24 * w)) % 2 ^ 24

def tabT : ℕ → ℕ
  | 0 => 0x1000001000001000001000001000001000001000000000000000000000000000000000000000000000000000000000000000001000001000001000001000001000001000000000000000000000001000000000001000001000001000000000001000001000001000001000001000001000001000000000000000000000000000000000000000000000000000000000000000000000000000001000001000001000001000000000000000000000000000000000001000001000001000000000001000001000001000001000001000001000001000000000000000000000000000000000000000001000001000000000000000001000001000001000001000001000001000000000000000000000001000000000001000001000001000000000001000001000001000001000001000001000001
  | 1 => 0x600000300000300000300000300000300000600000300000300000300000600000300000C00000600000600000300000300000300000300000300000500000600000600000300000C000010000010000008000010000008000008000004000003000001000003000003000003000003000006000003000006000006000010000008000010000008000008000004000006000006000006000008000006000008000008000004000006000008000008000004000008000004000004000002000003000001000001000001000003000003000006000003000003000003000006000003000010000008000008000004000003000003000003000003000006000008000008000004000006000008000008000004000008000004000004000002000003000001000003000003000003000003000008000004000003000003000008000004000008000004000004000002000003000003000003000004000003000004000004000002000003000004000004000002000004000002000002000001
  | 2 => 0x11200006000006400003300006700003500005100001B00006C00003800005700001D00008700002D00002D00000F00006700003800003800001D00004D00002D00002D00000F00008700005100005100001B00005100001B00001B00000900006400002200003800001D00003800001D00002D00000F00005700002D00005100001B00005100001B00001B00000900005100002D00002D00001B00002D00001B00001B00000900002D00001B00001B00000900001B00000900000900000300006000001D00002200001100003800001D00002D00000F00003800001D00002D00000F00005100001B00001B00000900003500001D00001D00000F00002D00001B00001B00000900002D00001B00001B00000900001B00000900000900000300003300001100001D00000F00001D00000F00001B00000900001D00000F00001B00000900001B00000900000900000300001B00000F00000F00000900000F00000900000900000300000F000009000009000003000009000003000003000001
  | 3 => 0xD380003820003AF0001400003D20001500001C80000720004020001620001E800007A0002A00000A80000A800002A0003D200016200016200007A0001BE0000A80000A800002A0002A00001000001000000400001000000400000400000100003AF00010000016200007A00016200007A0000A800002A0001E80000A80001000000400001000000400000400000100001C80000A80000A80000400000A80000400000400000100000A80000400000400000100000400000100000100000040003820000DE00010000005600016200007A0000A800002A00016200007A0000A800002A00010000004000004000001000015000007A00007A00002A0000A80000400000400000100000A800004000004000001000004000001000001000000400014000005600007A00002A00007A00002A00004000001000007A00002A00004000001000004000001000001000000400007200002A00002A00001000002A00001000001000000400002A000010000010000004000010000004000004000001
  | 4 => 0x55BE0012320013150004D80013C400051400067200014A0014A00005500006D600015E0008CA0001C20001C200005A0013C400055000055000015E00065E0001C20001C200005A0008CA00027100027100007D00027100007D00007D00001900131500042E00055000015E00055000015E0001C200005A0006D60001C200027100007D00027100007D00007D0000190006720001C20001C200007D0001C200007D00007D0000190001C200007D00007D00001900007D0000190000190000050012320003B600042E00010E00055000015E0001C200005A00055000015E0001C200005A00027100007D00007D00001900051400015E00015E00005A0001C200007D00007D0000190001C200007D00007D00001900007D0000190000190000050004D800010E00015E00005A00015E00005A00007D00001900015E00005A00007D00001900007D00001900001900000500014A00005A00005A00001900005A00001900001900000500005A000019000019000005000019000005000005000001
  | 5 => 0x17A620042B10045B0000E1F0047F9000EBF0011EE0002FD004AB5000F550012DE0003250017340003DE0003DE0000A50047F9000F55000F550003250011CB0003DE0003DE0000A50017340005100005100000D80005100000D80000D80000240045B0000CAD000F55000325000F550003250003DE0000A50012DE0003DE0005100000D80005100000D80000D80000240011EE0003DE0003DE0000D80003DE0000D80000D80000240003DE0000D80000D80000240000D80000240000240000060042B1000B77000CAD00028F000F550003250003DE0000A5000F550003250003DE0000A50005100000D80000D8000024000EBF0003250003250000A50003DE0000D80000D80000240003DE0000D80000D80000240000D8000024000024000006000E1F00028F0003250000A50003250000A50000D80000240003250000A50000D80000240000D80000240000240000060002FD0000A50000A50000240000A50000240000240000060000A5000024000024000006000024000006000006000001
  | 6 => 0x50D7800C2A200CA9700222700D09B0023850029EB0005FD00D7940024C0002BD500064300344100077700077700011100D09B0024C00024C00006430029B300077700077700011100344100096100096100015700096100015700015700003100CA97001F640024C00006430024C0000643000777000111002BD50007770009610001570009610001570001570000310029EB00077700077700015700077700015700015700003100077700015700015700003100015700003100003100000700C2A2001CCB001F640005470024C00006430007770001110024C00006430007770001110009610001570001570000310023850006430006430001110007770001570001570000310007770001570001570000310001570000310000310000070022270005470006430001110006430001110001570000310006430001110001570000310001570000310000310000070005FD000111000111000031000111000031000031000007000111000031000031000007000031000007000007000001
  | 7 => 0xE689001E3C401F5C2004868020344004B080056A0000AD4021294004D54005A20000B44006900000D20000D200001A4020344004D54004D54000B4400564C000D20000D200001A400690000100000100000020000100000020000020000004001F5C2004398004D54000B44004D54000B44000D200001A4005A20000D200010000002000010000002000002000000400056A0000D20000D20000200000D20000200000200000040000D2000020000020000004000020000004000004000000801E3C4003EAC0043980009BC004D54000B44000D200001A4004D54000B44000D200001A4001000000200000200000040004B08000B44000B440001A4000D20000200000200000040000D200002000002000000400002000000400000400000080048680009BC000B440001A4000B440001A4000200000040000B440001A4000200000040000200000040000040000008000AD40001A40001A40000400001A40000400000400000080001A4000040000040000008000040000008000008000001
  | 8 => 0x23E554042B7C044FBE008B38046AD0008FD000A3440012240489000093C000A92C0012CC00C1A4001584001584000264046AD00093C00093C00012CC00A2CC00158400158400026400C1A40019A10019A10002D90019A10002D90002D9000051044FBE0083640093C00012CC0093C00012CC00158400026400A92C0015840019A10002D90019A10002D90002D900005100A3440015840015840002D90015840002D90002D90000510015840002D90002D90000510002D9000051000051000009042B7C007ADC00836400108C0093C00012CC0015840002640093C00012CC0015840002640019A10002D90002D9000051008FD00012CC0012CC0002640015840002D90002D90000510015840002D90002D90000510002D9000051000051000009008B3800108C0012CC0002640012CC0002640002D90000510012CC0002640002D90000510002D9000051000051000009001224000264000264000051000264000051000051000009000264000051000051000009000051000009000009000001
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def base_T : ∀ u : Fin 128, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_0 : ∀ u : Fin 128, u.val / 16 = 0 → ∀ n < (8 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_1 : ∀ u : Fin 128, u.val / 16 = 1 → ∀ n < (8 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_2 : ∀ u : Fin 128, u.val / 16 = 2 → ∀ n < (8 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_3 : ∀ u : Fin 128, u.val / 16 = 3 → ∀ n < (8 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_4 : ∀ u : Fin 128, u.val / 16 = 4 → ∀ n < (8 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_5 : ∀ u : Fin 128, u.val / 16 = 5 → ∀ n < (8 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_6 : ∀ u : Fin 128, u.val / 16 = 6 → ∀ n < (8 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_7 : ∀ u : Fin 128, u.val / 16 = 7 → ∀ n < (8 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

theorem step_all (n : ℕ) (hn : n < 8) (u : Fin 128) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  have hu := u.isLt
  obtain ⟨c, hc⟩ : ∃ c, u.val / 16 = c := ⟨_, rfl⟩
  have hc2 : c < 8 := by omega
  interval_cases c
  · exact chunk_0 u hc n hn
  · exact chunk_1 u hc n hn
  · exact chunk_2 u hc n hn
  · exact chunk_3 u hc n hn
  · exact chunk_4 u hc n hn
  · exact chunk_5 u hc n hn
  · exact chunk_6 u hc n hn
  · exact chunk_7 u hc n hn

theorem G_eq_T (n : ℕ) (hn : n ≤ 8) : ∀ u : Fin 128, G n u = tb (tabT n) u.val := by
  induction n with
  | zero => exact base_T
  | succ n ih =>
    intro u
    rw [G_succ]
    have ih' := ih (by omega)
    simp only [ih']
    exact step_all n (by omega) u

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def tab_base : ∀ u : Fin 128,
    tb (tabT 8) u.val + 28 * tb (tabT 6) u.val + 70 * tb (tabT 4) u.val + 28 * tb (tabT 2) u.val + tb (tabT 0) u.val =
      8 * tb (tabT 7) u.val + 56 * tb (tabT 5) u.val + 56 * tb (tabT 3) u.val + 8 * tb (tabT 1) u.val := by
  decide +kernel

theorem G_base : ∀ u : Fin 128,
    G 8 u + 28 * G 6 u + 70 * G 4 u + 28 * G 2 u + G 0 u =
      8 * G 7 u + 56 * G 5 u + 56 * G 3 u + 8 * G 1 u := by
  intro u
  rw [G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 128,
    G (m + 8) u + 28 * G (m + 6) u + 70 * G (m + 4) u + 28 * G (m + 2) u + G m u =
      8 * G (m + 7) u + 56 * G (m + 5) u + 56 * G (m + 3) u + 8 * G (m + 1) u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega]
    rw [G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m, G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 8) + 28 * a (m + 6) + 70 * a (m + 4) + 28 * a (m + 2) + a m =
      8 * a (m + 7) + 56 * a (m + 5) + 56 * a (m + 3) + 8 * a (m + 1) := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 127

theorem G_vals : G 1 127 = 6 ∧ G 2 127 = 274 ∧ G 3 127 = 3384 ∧ G 4 127 = 21950 ∧ G 5 127 = 96866 ∧ G 6 127 = 331128 ∧ G 7 127 = 944272 ∧ G 8 127 = 2352468 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 6 ∧ a 2 = 274 ∧ a 3 = 3384 ∧ a 4 = 21950 ∧ a 5 = 96866 ∧ a 6 = 331128 ∧ a 7 = 944272 ∧ a 8 = 2352468 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num

theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 8) + 28 * a (m + 6) + 70 * a (m + 4) + 28 * a (m + 2) + a m : ℤ) : ℚ) =
      ((8 * a (m + 7) + 56 * a (m + 5) + 56 * a (m + 3) + 8 * a (m + 1) : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 8 - 1 = (m + 7) by omega, show m + 8 - 2 = (m + 6) by omega, show m + 8 - 3 = (m + 5) by omega, show m + 8 - 4 = (m + 4) by omega, show m + 8 - 5 = (m + 3) by omega, show m + 8 - 6 = (m + 2) by omega, show m + 8 - 7 = (m + 1) by omega, show m + 8 - 8 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) =
      2 * X * (3 + 113 * X + 680 * X ^ 2 + 1107 * X ^ 3 + 547 * X ^ 4 + 70 * X ^ 5) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 8 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 8 * (PowerSeries.mk F * X ^ 1) + C 28 * (PowerSeries.mk F * X ^ 2) - C 56 * (PowerSeries.mk F * X ^ 3) + C 70 * (PowerSeries.mk F * X ^ 4) - C 56 * (PowerSeries.mk F * X ^ 5) + C 28 * (PowerSeries.mk F * X ^ 6) - C 8 * (PowerSeries.mk F * X ^ 7) + C 1 * (PowerSeries.mk F * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (3 + 113 * X + 680 * X ^ 2 + 1107 * X ^ 3 + 547 * X ^ 4 + 70 * X ^ 5) : ℚ⟦X⟧) =
      C 6 * X ^ 1 + C 226 * X ^ 2 + C 1360 * X ^ 3 + C 2214 * X ^ 4 + C 1094 * X ^ 5 + C 140 * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 9
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have hr := recurrence (j + 9) (by omega)
    simp only [show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega, show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega, show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega, show j + 9 - 8 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 9 by omega,
      show 1 ≤ j + 9 by omega,
      show 2 ≤ j + 9 by omega,
      show 3 ≤ j + 9 by omega,
      show 4 ≤ j + 9 by omega,
      show 5 ≤ j + 9 by omega,
      show 6 ≤ j + 9 by omega,
      show 7 ≤ j + 9 by omega,
      show 8 ≤ j + 9 by omega,
      show j + 9 - 0 = j + 9 by omega,
      show j + 9 - 1 = j + 8 by omega,
      show j + 9 - 2 = j + 7 by omega,
      show j + 9 - 3 = j + 6 by omega,
      show j + 9 - 4 = j + 5 by omega,
      show j + 9 - 5 = j + 4 by omega,
      show j + 9 - 6 = j + 3 by omega,
      show j + 9 - 7 = j + 2 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show ¬ (j + 9 = 1) by omega,
      show ¬ (j + 9 = 2) by omega,
      show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega,
      show ¬ (j + 9 = 5) by omega,
      show ¬ (j + 9 = 6) by omega,
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

end OMA.A250390

theorem OMA.solution : type_of% @OMA.S_oeis_a250390.main :=
  ⟨OMA.A250390.gen_fun, OMA.A250390.recurrence⟩
