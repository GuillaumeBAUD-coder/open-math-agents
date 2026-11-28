import OMAStatements.S_oeis_a250391

/-!
A250391: exact eight-position/five-window adaptation of the threshold-chain proof
by @Salofe for A250064, PR #23285, commit bd4969a8ddc52c3bd7f8d30008570b9868fd00b6.
Conjecture: Colin Barker (2017); registered statement: @clementtrecourt, PR #19870.
The finite tables certify a recurrence on every subset state; linearity then proves
it for all levels. All computations are kernel checked.
-/

namespace OMA.A250391

open OMA.S_oeis_a250391 Finset

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
def fget (f : Fin 8 → Bool) (k : ℕ) : Bool := if h : k < 8 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 8 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 4 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 8 → Bool) : Prop := ∀ i < (5 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 8 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 8 → Fin (n + 1)) (v : ℕ) : Fin 8 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 8 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a250391.get x k ≤ n := by
  unfold OMA.S_oeis_a250391.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (5 : ℕ), cntW (fun _ => true) i = 4 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 8 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (5 : ℕ), ¬ Cy (fun t : Fin 4 => OMA.S_oeis_a250391.get x (i + t)) := by
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
  have step2 : ∀ i < (5 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 4 => OMA.S_oeis_a250391.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 8 := by have := t.isLt; omega
    unfold OMA.S_oeis_a250391.get fget Lt
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
noncomputable def M (n : ℕ) (T : Fin 8 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 8 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 8 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 8 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 8 → Fin (n + 2)) : Fin 8 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 8 → Bool) (x : Fin 8 → Fin (n + 1)) : Fin 8 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 8 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 8 → Bool) (x : Fin 8 → Fin (n + 1)) (p : Fin 8) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 8 → Bool) :
    M (n + 1) T = ∑ S : Fin 8 → Bool,
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
def row (u : Fin 256) : Fin 8 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 8 → Bool) : ℕ := ∑ p : Fin 8, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 256, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 8 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2

theorem cnt_row : ∀ u : Fin 256, cntW (row u) 0 = pcb (u.val &&& 15) ∧
    cntW (row u) 1 = pcb (u.val &&& 30) ∧
    cntW (row u) 2 = pcb (u.val &&& 60) ∧
    cntW (row u) 3 = pcb (u.val &&& 120) ∧
    cntW (row u) 4 = pcb (u.val &&& 240) := by
  decide +kernel

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 15) ≤ 1 ∧ 3 ≤ pcb (t &&& 15)) ∧
    ¬ (pcb (s &&& 30) ≤ 1 ∧ 3 ≤ pcb (t &&& 30)) ∧
    ¬ (pcb (s &&& 60) ≤ 1 ∧ 3 ≤ pcb (t &&& 60)) ∧
    ¬ (pcb (s &&& 120) ≤ 1 ∧ 3 ≤ pcb (t &&& 120)) ∧
    ¬ (pcb (s &&& 240) ≤ 1 ∧ 3 ≤ pcb (t &&& 240)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (5 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 256) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4]

theorem sub_iff (w u : Fin 256) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 8
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (256 : ℕ) ≤ 2 ^ i := by
          calc (256 : ℕ) = 2 ^ 8 := by norm_num
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
def subs (u : Fin 256) : Finset (Fin 256) :=
  univ.filter (fun w : Fin 256 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 256 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 256, M n (row u) = G n u := by
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

theorem row_full : ∀ p, row 255 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 255 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 8 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 255 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 255)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 255 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 255 := by
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

theorem G_succ (n : ℕ) (u : Fin 256) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl


/-! Packed tables certify the recursion on every state. -/
def tb (T w : ℕ) : ℕ := (T >>> (32 * w)) % 2 ^ 32

def tabT : ℕ → ℕ
  | 0 => 0x1000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000001000000010000000000000000000000010000000100000001000000010000000100000001000000000000000000000000000000010000000000000001000000010000000100000000000000010000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000010000000100000001000000010000000000000000000000000000000100000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000000000000000000000000000000000000000000000001000000010000000100000000000000010000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000100000001000000000000000000000001000000010000000100000001000000010000000100000000000000000000000000000001000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001
  | 1 => 0x600000003000000030000000300000003000000030000000600000003000000030000000300000006000000030000000C0000000600000006000000030000000300000003000000030000000300000005000000060000000600000003000000090000000C0000000C000000060000000C000000060000000600000003000000030000000100000003000000030000000300000003000000060000000300000005000000050000000C000000060000000C0000000600000006000000030000000C0000000C0000000C000000100000000C0000001000000010000000080000000C000000100000001000000008000000100000000800000008000000040000000300000001000000010000000100000003000000030000000600000003000000030000000300000006000000030000000C000000060000000600000003000000060000000600000006000000060000000C0000001000000010000000080000000C0000001000000010000000080000001000000008000000080000000400000006000000020000000600000006000000060000000600000010000000080000000600000006000000100000000800000010000000080000000800000004000000060000000600000006000000080000000600000008000000080000000400000006000000080000000800000004000000080000000400000004000000020000000300000001000000010000000100000001000000010000000200000001000000030000000300000006000000030000000C00000006000000060000000300000003000000030000000300000003000000050000000600000006000000030000000C00000010000000100000000800000010000000080000000800000004000000030000000100000003000000030000000300000003000000060000000300000006000000060000001000000008000000100000000800000008000000040000000600000006000000060000000800000006000000080000000800000004000000060000000800000008000000040000000800000004000000040000000200000003000000010000000100000001000000030000000300000006000000030000000300000003000000060000000300000010000000080000000800000004000000030000000300000003000000030000000600000008000000080000000400000006000000080000000800000004000000080000000400000004000000020000000300000001000000030000000300000003000000030000000800000004000000030000000300000008000000040000000800000004000000040000000200000003000000030000000300000004000000030000000400000004000000020000000300000004000000040000000200000004000000020000000200000001
  | 2 => 0x202000000B5000000BC00000060000000C2000000640000009900000033000000C7000000670000009F00000035000000F300000051000000510000001B000000C70000006C0000006C000000380000009600000057000000570000001D000000E100000087000000870000002D000000870000002D0000002D0000000F000000C2000000430000006C000000380000006C00000038000000570000001D000000960000004D000000870000002D000000870000002D0000002D0000000F000000F30000008700000087000000510000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B00000009000000BC0000003A00000044000000220000006C00000038000000570000001D0000006C00000038000000570000001D000000870000002D0000002D0000000F0000009F00000057000000570000002D0000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B000000090000009900000033000000570000002D000000570000002D000000510000001B000000570000002D000000510000001B000000510000001B0000001B00000009000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B000000090000000900000003000000B5000000370000003A0000001D000000430000002200000033000000110000006C00000038000000570000001D000000870000002D0000002D0000000F0000006700000038000000380000001D0000004D0000002D0000002D0000000F0000008700000051000000510000001B000000510000001B0000001B000000090000006400000022000000380000001D000000380000001D0000002D0000000F000000570000002D000000510000001B000000510000001B0000001B00000009000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B000000090000000900000003000000600000001D0000002200000011000000380000001D0000002D0000000F000000380000001D0000002D0000000F000000510000001B0000001B00000009000000350000001D0000001D0000000F0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B00000009000000090000000300000033000000110000001D0000000F0000001D0000000F0000001B000000090000001D0000000F0000001B000000090000001B0000000900000009000000030000001B0000000F0000000F000000090000000F0000000900000009000000030000000F00000009000000090000000300000009000000030000000300000001
  | 3 => 0x2508000009DA00000A550000038200000AB7000003AF000005000000014000000B16000003D2000005400000015000000720000001C8000001C80000007200000B1600000402000004020000016200000515000001E8000001E80000007A000006E4000002A0000002A0000000A8000002A0000000A8000000A80000002A00000AB7000002EE00000402000001620000040200000162000001E80000007A00000515000001BE000002A0000000A8000002A0000000A8000000A80000002A00000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001000000A5500000296000002FA000001000000040200000162000001E80000007A0000040200000162000001E80000007A000002A0000000A8000000A80000002A00000540000001E8000001E8000000A8000002A0000001000000010000000040000002A0000001000000010000000040000001000000004000000040000000100000050000000158000001E8000000A8000001E8000000A80000010000000040000001E8000000A8000001000000004000000100000000400000004000000010000001C8000000A8000000A800000040000000A8000000400000004000000010000000A800000040000000400000001000000040000000100000001000000004000009DA0000027200000296000000DE000002EE0000010000000158000000560000040200000162000001E80000007A000002A0000000A8000000A80000002A000003D200000162000001620000007A000001BE000000A8000000A80000002A000002A000000100000001000000004000000100000000400000004000000010000003AF00000100000001620000007A000001620000007A000000A80000002A000001E8000000A8000001000000004000000100000000400000004000000010000001C8000000A8000000A800000040000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400000382000000DE0000010000000056000001620000007A000000A80000002A000001620000007A000000A80000002A00000100000000400000004000000010000001500000007A0000007A0000002A000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400000140000000560000007A0000002A0000007A0000002A00000040000000100000007A0000002A000000400000001000000040000000100000001000000004000000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001
  | 4 => 0x141DE00004465000047AB0000123200004A3F0000131500001838000004D800004CCB000013C400001964000005140000203A00000672000006720000014A00004CCB000014A0000014A000000550000018D3000006D6000006D60000015E00001FA4000008CA000008CA000001C2000008CA000001C2000001C20000005A00004A3F00001054000014A000000550000014A000000550000006D60000015E000018D30000065E000008CA000001C2000008CA000001C2000001C20000005A0000203A000008CA000008CA00000271000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D00000019000047AB00000EBA000010900000042E000014A000000550000006D60000015E000014A000000550000006D60000015E000008CA000001C2000001C20000005A00001964000006D6000006D6000001C2000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D000000190000183800000546000006D6000001C2000006D6000001C2000002710000007D000006D6000001C2000002710000007D000002710000007D0000007D0000001900000672000001C2000001C20000007D000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D0000001900000019000000050000446500000DFA00000EBA000003B6000010540000042E000005460000010E000014A000000550000006D60000015E000008CA000001C2000001C20000005A000013C400000550000005500000015E0000065E000001C2000001C20000005A000008CA00000271000002710000007D000002710000007D0000007D00000019000013150000042E000005500000015E000005500000015E000001C20000005A000006D6000001C2000002710000007D000002710000007D0000007D0000001900000672000001C2000001C20000007D000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D00000019000000190000000500001232000003B60000042E0000010E000005500000015E000001C20000005A000005500000015E000001C20000005A000002710000007D0000007D00000019000005140000015E0000015E0000005A000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D000000190000001900000005000004D80000010E0000015E0000005A0000015E0000005A0000007D000000190000015E0000005A0000007D000000190000007D0000001900000019000000050000014A0000005A0000005A000000190000005A0000001900000019000000050000005A00000019000000190000000500000019000000050000000500000001
  | 5 => 0x6FA9600013B230001491A000042B10001540C000045B0000054BA00000E1F00015EDB000047F90000587A00000EBF00006B94000011EE000011EE000002FD00015EDB00004AB500004AB500000F55000056F4000012DE000012DE0000032500006A590000173400001734000003DE00001734000003DE000003DE000000A50001540C00003E0300004AB500000F5500004AB500000F55000012DE00000325000056F4000011CB00001734000003DE00001734000003DE000003DE000000A500006B94000017340000173400000510000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D8000000240001491A000038DB00003ECB00000CAD00004AB500000F55000012DE0000032500004AB500000F55000012DE0000032500001734000003DE000003DE000000A50000587A000012DE000012DE000003DE000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D800000024000054BA00000F5A000012DE000003DE000012DE000003DE00000510000000D8000012DE000003DE00000510000000D800000510000000D8000000D800000024000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D800000024000000240000000600013B230000363B000038DB00000B7700003E0300000CAD00000F5A0000028F00004AB500000F55000012DE0000032500001734000003DE000003DE000000A5000047F900000F5500000F5500000325000011CB000003DE000003DE000000A5000017340000051000000510000000D800000510000000D8000000D800000024000045B000000CAD00000F550000032500000F5500000325000003DE000000A5000012DE000003DE00000510000000D800000510000000D8000000D800000024000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D8000000240000002400000006000042B100000B7700000CAD0000028F00000F5500000325000003DE000000A500000F5500000325000003DE000000A500000510000000D8000000D80000002400000EBF0000032500000325000000A5000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D800000024000000240000000600000E1F0000028F00000325000000A500000325000000A5000000D80000002400000325000000A5000000D800000024000000D8000000240000002400000006000002FD000000A5000000A500000024000000A5000000240000002400000006000000A500000024000000240000000600000024000000060000000600000001
  | 6 => 0x1CCAE4000455AA000482890000C2A20004A5970000CA970000EF11000022270004C8120000D09B0000F8A3000023850001256D000029EB000029EB000005FD0004C8120000D7940000D794000024C00000F52300002BD500002BD50000064300012321000034410000344100000777000034410000077700000777000001110004A5970000B8A70000D794000024C00000D794000024C000002BD5000006430000F523000029B30000344100000777000034410000077700000777000001110001256D000034410000344100000961000034410000096100000961000001570000344100000961000009610000015700000961000001570000015700000031000482890000AB640000BAB400001F640000D794000024C000002BD5000006430000D794000024C000002BD500000643000034410000077700000777000001110000F8A300002BD500002BD5000007770000344100000961000009610000015700003441000009610000096100000157000009610000015700000157000000310000EF11000024F100002BD50000077700002BD500000777000009610000015700002BD500000777000009610000015700000961000001570000015700000031000029EB000007770000077700000157000007770000015700000157000000310000077700000157000001570000003100000157000000310000003100000007000455AA0000A4410000AB6400001CCB0000B8A700001F64000024F1000005470000D794000024C000002BD500000643000034410000077700000777000001110000D09B000024C0000024C000000643000029B300000777000007770000011100003441000009610000096100000157000009610000015700000157000000310000CA9700001F64000024C000000643000024C000000643000007770000011100002BD500000777000009610000015700000961000001570000015700000031000029EB0000077700000777000001570000077700000157000001570000003100000777000001570000015700000031000001570000003100000031000000070000C2A200001CCB00001F6400000547000024C0000006430000077700000111000024C0000006430000077700000111000009610000015700000157000000310000238500000643000006430000011100000777000001570000015700000031000007770000015700000157000000310000015700000031000000310000000700002227000005470000064300000111000006430000011100000157000000310000064300000111000001570000003100000157000000310000003100000007000005FD000001110000011100000031000001110000003100000031000000070000011100000031000000310000000700000031000000070000000700000001
  | 7 => 0x604460000CA13C000D18660001E3C4000D75420001F5C20002434000004868000DD034000203440002584000004B080002B500000056A0000056A000000AD4000DD034000212940002129400004D540002511600005A2000005A2000000B440002B110000069000000690000000D200000690000000D2000000D20000001A4000D75420001D0BC0002129400004D540002129400004D5400005A2000000B44000251160000564C0000690000000D200000690000000D2000000D20000001A40002B500000069000000690000001000000069000000100000001000000002000000690000001000000010000000020000001000000002000000020000000040000D18660001B36C0001D554000043980002129400004D5400005A2000000B440002129400004D5400005A2000000B440000690000000D2000000D20000001A40002584000005A2000005A2000000D200000690000001000000010000000020000006900000010000000100000000200000010000000020000000200000000400002434000004DE000005A2000000D2000005A2000000D20000010000000020000005A2000000D20000010000000020000001000000002000000020000000040000056A000000D2000000D200000020000000D2000000200000002000000004000000D2000000200000002000000004000000200000000400000004000000008000CA13C0001A3040001B36C00003EAC0001D0BC0000439800004DE0000009BC0002129400004D5400005A2000000B440000690000000D2000000D20000001A40002034400004D5400004D5400000B440000564C00000D2000000D20000001A400006900000010000000100000000200000010000000020000000200000000400001F5C20000439800004D5400000B4400004D5400000B4400000D20000001A400005A2000000D20000010000000020000001000000002000000020000000040000056A000000D2000000D200000020000000D2000000200000002000000004000000D20000002000000020000000040000002000000004000000040000000080001E3C400003EAC00004398000009BC00004D5400000B4400000D20000001A400004D5400000B4400000D20000001A40000100000000200000002000000004000004B0800000B4400000B44000001A400000D2000000200000002000000004000000D200000020000000200000000400000020000000040000000400000000800004868000009BC00000B44000001A400000B44000001A4000002000000004000000B44000001A400000200000000400000020000000040000000400000000800000AD4000001A4000001A400000040000001A4000000400000004000000008000001A400000040000000400000000800000040000000080000000800000001
  | 8 => 0x1133F64001FFB4E00210F4200042B7C0021E5DA00044FBE0004E4F800008B380022B73200046AD000050E5000008FD00005BD640000A3440000A344000012240022B7320004890000048900000093C0000500E20000A92C0000A92C000012CC0005B7100000C1A40000C1A4000015840000C1A40000158400001584000002640021E5DA00040A1000048900000093C000048900000093C00000A92C000012CC000500E20000A2CC0000C1A4000015840000C1A40000158400001584000002640005BD640000C1A40000C1A4000019A10000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D90000005100210F420003CFFC000413400000836400048900000093C00000A92C000012CC00048900000093C00000A92C000012CC0000C1A400001584000015840000026400050E500000A92C0000A92C000015840000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D9000000510004E4F8000094EC0000A92C000015840000A92C00001584000019A1000002D90000A92C00001584000019A1000002D9000019A1000002D9000002D9000000510000A3440000158400001584000002D900001584000002D9000002D90000005100001584000002D9000002D900000051000002D9000000510000005100000009001FFB4E0003AE840003CFFC00007ADC00040A1000008364000094EC0000108C00048900000093C00000A92C000012CC0000C1A400001584000015840000026400046AD0000093C0000093C0000012CC0000A2CC0000158400001584000002640000C1A4000019A1000019A1000002D9000019A1000002D9000002D90000005100044FBE00008364000093C0000012CC000093C0000012CC00001584000002640000A92C00001584000019A1000002D9000019A1000002D9000002D9000000510000A3440000158400001584000002D900001584000002D9000002D90000005100001584000002D9000002D900000051000002D900000051000000510000000900042B7C00007ADC000083640000108C000093C0000012CC0000158400000264000093C0000012CC0000158400000264000019A1000002D9000002D90000005100008FD0000012CC000012CC0000026400001584000002D9000002D90000005100001584000002D9000002D900000051000002D900000051000000510000000900008B380000108C000012CC00000264000012CC00000264000002D900000051000012CC00000264000002D900000051000002D900000051000000510000000900001224000002640000026400000051000002640000005100000051000000090000026400000051000000510000000900000051000000090000000900000001
  | 9 => 0x2B966B60048B163004AF1BD0008652F004CB1290008A8310009B29E0000F843004E64230008D9FF0009FD9E0000FFC3000B313C00011E8600011E8600001CA7004E6423000910D7000910D7000106170009E61F000127E6000127E600001D97000B279100014DFC00014DFC0000216600014DFC000021660000216600000357004CB12900082E15000910D700010617000910D700010617000127E600001D970009E61F00011DE100014DFC0000216600014DFC000021660000216600000357000B313C00014DFC00014DFC0000271000014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E800000064004AF1BD0007C42500083EF50000EC31000910D700010617000127E600001D97000910D700010617000127E600001D9700014DFC0000216600002166000003570009FD9E000127E6000127E60000216600014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E8000000640009B29E00010842000127E600002166000127E60000216600002710000003E8000127E60000216600002710000003E800002710000003E8000003E80000006400011E860000216600002166000003E800002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A0048B163000785B50007C4250000DE5D00082E150000EC310001084200001A6D000910D700010617000127E600001D9700014DFC0000216600002166000003570008D9FF000106170001061700001D9700011DE100002166000021660000035700014DFC0000271000002710000003E800002710000003E8000003E8000000640008A8310000EC310001061700001D970001061700001D970000216600000357000127E60000216600002710000003E800002710000003E8000003E80000006400011E860000216600002166000003E800002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A0008652F0000DE5D0000EC3100001A6D0001061700001D9700002166000003570001061700001D97000021660000035700002710000003E8000003E8000000640000FFC300001D9700001D970000035700002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A0000F84300001A6D00001D970000035700001D9700000357000003E80000006400001D9700000357000003E800000064000003E800000064000000640000000A00001CA70000035700000357000000640000035700000064000000640000000A0000035700000064000000640000000A000000640000000A0000000A00000001
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def base_T : ∀ u : Fin 256, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_0 : ∀ u : Fin 256, u.val / 16 = 0 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_1 : ∀ u : Fin 256, u.val / 16 = 1 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_2 : ∀ u : Fin 256, u.val / 16 = 2 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_3 : ∀ u : Fin 256, u.val / 16 = 3 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_4 : ∀ u : Fin 256, u.val / 16 = 4 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_5 : ∀ u : Fin 256, u.val / 16 = 5 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_6 : ∀ u : Fin 256, u.val / 16 = 6 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_7 : ∀ u : Fin 256, u.val / 16 = 7 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_8 : ∀ u : Fin 256, u.val / 16 = 8 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_9 : ∀ u : Fin 256, u.val / 16 = 9 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_10 : ∀ u : Fin 256, u.val / 16 = 10 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_11 : ∀ u : Fin 256, u.val / 16 = 11 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_12 : ∀ u : Fin 256, u.val / 16 = 12 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_13 : ∀ u : Fin 256, u.val / 16 = 13 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_14 : ∀ u : Fin 256, u.val / 16 = 14 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_15 : ∀ u : Fin 256, u.val / 16 = 15 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

theorem step_all (n : ℕ) (hn : n < 9) (u : Fin 256) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  have hu := u.isLt
  obtain ⟨c, hc⟩ : ∃ c, u.val / 16 = c := ⟨_, rfl⟩
  have hc2 : c < 16 := by omega
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

theorem G_eq_T (n : ℕ) (hn : n ≤ 9) : ∀ u : Fin 256, G n u = tb (tabT n) u.val := by
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
def tab_base : ∀ u : Fin 256,
    tb (tabT 9) u.val + 36 * tb (tabT 7) u.val + 126 * tb (tabT 5) u.val + 84 * tb (tabT 3) u.val + 9 * tb (tabT 1) u.val =
      9 * tb (tabT 8) u.val + 84 * tb (tabT 6) u.val + 126 * tb (tabT 4) u.val + 36 * tb (tabT 2) u.val + tb (tabT 0) u.val := by
  decide +kernel

theorem G_base : ∀ u : Fin 256,
    G 9 u + 36 * G 7 u + 126 * G 5 u + 84 * G 3 u + 9 * G 1 u =
      9 * G 8 u + 84 * G 6 u + 126 * G 4 u + 36 * G 2 u + G 0 u := by
  intro u
  rw [G_eq_T 9 (by norm_num) u, G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 256,
    G (m + 9) u + 36 * G (m + 7) u + 126 * G (m + 5) u + 84 * G (m + 3) u + 9 * G (m + 1) u =
      9 * G (m + 8) u + 84 * G (m + 6) u + 126 * G (m + 4) u + 36 * G (m + 2) u + G m u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 9 = (m + 9) + 1 by omega]
    rw [G_succ (m + 9), G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1), G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 9) + 36 * a (m + 7) + 126 * a (m + 5) + 84 * a (m + 3) + 9 * a (m + 1) =
      9 * a (m + 8) + 84 * a (m + 6) + 126 * a (m + 4) + 36 * a (m + 2) + a m := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 255

theorem G_vals : G 1 255 = 6 ∧ G 2 255 = 514 ∧ G 3 255 = 9480 ∧ G 4 255 = 82398 ∧ G 5 255 = 457366 ∧ G 6 255 = 1886948 ∧ G 7 255 = 6308960 ∧ G 8 255 = 18038628 ∧ G 9 255 = 45704886 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 6 ∧ a 2 = 514 ∧ a 3 = 9480 ∧ a 4 = 82398 ∧ a 5 = 457366 ∧ a 6 = 1886948 ∧ a 7 = 6308960 ∧ a 8 = 18038628 ∧ a 9 = 45704886 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num

theorem recurrence (n : ℕ) (hn : 10 ≤ n) :
    (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 9) + 36 * a (m + 7) + 126 * a (m + 5) + 84 * a (m + 3) + 9 * a (m + 1) : ℤ) : ℚ) =
      ((9 * a (m + 8) + 84 * a (m + 6) + 126 * a (m + 4) + 36 * a (m + 2) + a m : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 9 - 1 = (m + 8) by omega, show m + 9 - 2 = (m + 7) by omega, show m + 9 - 3 = (m + 6) by omega, show m + 9 - 4 = (m + 5) by omega, show m + 9 - 5 = (m + 4) by omega, show m + 9 - 6 = (m + 3) by omega, show m + 9 - 7 = (m + 2) by omega, show m + 9 - 8 = (m + 1) by omega, show m + 9 - 9 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 9 : PowerSeries ℚ) =
      2 * X * (3 + 230 * X + 2535 * X ^ 2 + 7539 * X ^ 3 + 7322 * X ^ 4 + 2335 * X ^ 5 + 196 * X ^ 6) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 9 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 9 * (PowerSeries.mk F * X ^ 1) + C 36 * (PowerSeries.mk F * X ^ 2) - C 84 * (PowerSeries.mk F * X ^ 3) + C 126 * (PowerSeries.mk F * X ^ 4) - C 126 * (PowerSeries.mk F * X ^ 5) + C 84 * (PowerSeries.mk F * X ^ 6) - C 36 * (PowerSeries.mk F * X ^ 7) + C 9 * (PowerSeries.mk F * X ^ 8) - C 1 * (PowerSeries.mk F * X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (3 + 230 * X + 2535 * X ^ 2 + 7539 * X ^ 3 + 7322 * X ^ 4 + 2335 * X ^ 5 + 196 * X ^ 6) : ℚ⟦X⟧) =
      C 6 * X ^ 1 + C 460 * X ^ 2 + C 5070 * X ^ 3 + C 15078 * X ^ 4 + C 14644 * X ^ 5 + C 4670 * X ^ 6 + C 392 * X ^ 7 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    have hr := recurrence (j + 10) (by omega)
    simp only [show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega, show j + 10 - 8 = j + 2 by omega, show j + 10 - 9 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 10 by omega,
      show 1 ≤ j + 10 by omega,
      show 2 ≤ j + 10 by omega,
      show 3 ≤ j + 10 by omega,
      show 4 ≤ j + 10 by omega,
      show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega,
      show 7 ≤ j + 10 by omega,
      show 8 ≤ j + 10 by omega,
      show 9 ≤ j + 10 by omega,
      show j + 10 - 0 = j + 10 by omega,
      show j + 10 - 1 = j + 9 by omega,
      show j + 10 - 2 = j + 8 by omega,
      show j + 10 - 3 = j + 7 by omega,
      show j + 10 - 4 = j + 6 by omega,
      show j + 10 - 5 = j + 5 by omega,
      show j + 10 - 6 = j + 4 by omega,
      show j + 10 - 7 = j + 3 by omega,
      show j + 10 - 8 = j + 2 by omega,
      show j + 10 - 9 = j + 1 by omega,
      show ¬ (j + 10 = 1) by omega,
      show ¬ (j + 10 = 2) by omega,
      show ¬ (j + 10 = 3) by omega,
      show ¬ (j + 10 = 4) by omega,
      show ¬ (j + 10 = 5) by omega,
      show ¬ (j + 10 = 6) by omega,
      show ¬ (j + 10 = 7) by omega,
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

end OMA.A250391

theorem OMA.solution : type_of% @OMA.S_oeis_a250391.main :=
  ⟨OMA.A250391.gen_fun, OMA.A250391.recurrence⟩
