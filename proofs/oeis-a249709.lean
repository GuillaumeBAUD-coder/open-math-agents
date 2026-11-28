import OMAStatements.S_oeis_a249709

/-!
Proof of the g.f. and the recurrence for A249709 (arrays of length 6 with entries in 0..n in
which every 4 consecutive entries have the maximum of some two of them equal to the minimum of
the other two).

* Window condition. For four values `y`, the max/min condition holds iff no threshold `w` has
  exactly two values `≤ w` (`window_iff`), i.e. iff no strict threshold set `{t | y t < v + 1}`
  has exactly two elements (`cy_iff_lt`).
* Strict threshold sets. With `Lt x v` the set of positions where `x < v`, `x` is good iff for
  every `v ≤ n` the set `Lt x (v+1)` meets no window in exactly two positions (`good_iff`).
* Chains. Counting arrays by the top set `Lt x n` gives a linear recursion `G` on 6-bit codes
  (`M_succ`, `M_eq_G`), whose matrix is unitriangular on the admissible codes; `(1-x)^6`
  annihilates it entrywise at `m = 0` by a finite computation, hence for every `m`. The
  recurrence and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a249709 Finset

/-! ### The window condition -/

/-- The condition of the statement on 4 values (without the bound on `v`). -/
def Cy4 (y : Fin 4 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 4)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy4_to (y : Fin 4 → ℕ) (h : Cy4 y) (w : ℕ) :
    (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
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

theorem cy4_of (y : Fin 4 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy4 y := by
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
    Cy4 y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy4_to y, cy4_of y⟩

/-- The window condition in terms of strict threshold counts. -/
theorem cy_iff_lt (y : Fin 4 → ℕ) :
    Cy4 y ↔ ∀ v : ℕ, (univ.filter (fun t => y t < v + 1)).card ≠ 2 := by
  rw [window_iff]
  simp only [Nat.lt_add_one_iff]

/-! ### Strict threshold sets -/

/-- Entry `k` of a set of positions (`false` past the end). -/
def fget (f : Fin 6 → Bool) (k : ℕ) : Bool := if h : k < 6 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 6 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 4 => fget f (i + t) = true)).card

/-- The admissibility of a strict threshold set `T` (the next one after `S` in a chain): no
window meets `T` in exactly two positions. -/
def Comp (_S T : Fin 6 → Bool) : Prop := ∀ i < (3 : ℕ), cntW T i ≠ 2

instance decComp (S T : Fin 6 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 6 → Fin (n + 1)) (v : ℕ) : Fin 6 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a249709.get x k ≤ n := by
  unfold OMA.S_oeis_a249709.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (3 : ℕ), cntW (fun _ => true) i = 4 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 6 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (3 : ℕ), Cy4 (fun t : Fin 4 => OMA.S_oeis_a249709.get x (i + t)) := by
    unfold good
    rw [decide_eq_true_iff]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    constructor
    · rintro ⟨S, hS, v, _, h1, h2, h3, h4⟩
      exact ⟨S, hS, v, h1, h2, h3, h4⟩
    · rintro ⟨S, hS, v, h1, ⟨t, ht, htv⟩, h3, h4⟩
      refine ⟨S, hS, v, ?_, h1, ⟨t, ht, htv⟩, h3, h4⟩
      rw [← htv]
      exact Nat.lt_succ_of_le (get_le x _)
  have step2 : ∀ i < (3 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 4 => OMA.S_oeis_a249709.get x (i + t) < v)).card =
        cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 6 := by have := t.isLt; omega
    unfold OMA.S_oeis_a249709.get fget Lt
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
    have := (cy_iff_lt _).1 (h i hi) v
    rw [step2 i hi (v + 1)] at this
    exact this
  · intro h i hi
    rw [cy_iff_lt]
    intro v
    rw [step2 i hi (v + 1)]
    by_cases hv : v ≤ n
    · exact h v hv i hi
    · rw [hfull (v + 1) (by omega), cnt_univ i hi]
      omega

/-! ### Chains of strict threshold sets -/

/-- Arrays with entries in `0..n` whose strict threshold sets `Lt x 1, ..., Lt x n` are
admissible, with `Lt x n ⊆ T` and `T` admissible. -/
noncomputable def M (n : ℕ) (T : Fin 6 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 6 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 6 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 6 → Fin (n + 2)) : Fin 6 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 6 → Bool) (x : Fin 6 → Fin (n + 1)) : Fin 6 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 6 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 6 → Bool) (x : Fin 6 → Fin (n + 1)) (p : Fin 6) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 6 → Bool) :
    M (n + 1) T = ∑ S : Fin 6 → Bool,
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
def row (u : Fin 64) : Fin 6 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 6 → Bool) : ℕ := ∑ p : Fin 6, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 64, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 6 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2

theorem cnt_row : ∀ u : Fin 64, cntW (row u) 0 = pcb (u.val &&& 15) ∧
    cntW (row u) 1 = pcb (u.val &&& 30) ∧
    cntW (row u) 2 = pcb (u.val &&& 60) := by
  decide +kernel

/-- Admissibility on codes: no window meets the set in exactly two positions. -/
def okc (t : ℕ) : Bool :=
  decide (pcb (t &&& 15) ≠ 2 ∧ pcb (t &&& 30) ≠ 2 ∧ pcb (t &&& 60) ≠ 2)

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (3 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)⟩
  · rintro ⟨h0, h1, h2⟩ i hi
    interval_cases i <;> assumption

theorem okc_iff (s t : Fin 64) : Comp (row s) (row t) ↔ okc t.val = true := by
  obtain ⟨b0, b1, b2⟩ := cnt_row t
  unfold Comp okc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, b0, b1, b2]

theorem sub_iff (w u : Fin 64) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 6
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (64 : ℕ) ≤ 2 ^ i := by
          calc (64 : ℕ) = 2 ^ 6 := by norm_num
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
def subs (u : Fin 64) : Finset (Fin 64) :=
  univ.filter (fun w : Fin 64 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 64 → ℕ
  | 0, u => if okc u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if okc u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 64, M n (row u) = G n u := by
  induction n with
  | zero =>
    intro u
    rw [M_zero, ← row_zero, G]
    exact if_congr (okc_iff 0 u) rfl rfl
  | succ n ih =>
    intro u
    rw [M_succ, ← row_bijective.sum_comp]
    simp only [G, subs]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih w]
    by_cases h1 : (w.val &&& u.val == w.val) = true
    · rw [if_pos h1]
      exact if_congr ((and_iff_left ((sub_iff w u).2 h1)).trans (okc_iff w u)) rfl rfl
    · rw [if_neg h1, if_neg (fun h => h1 ((sub_iff w u).1 h.2))]

theorem row_full : ∀ p, row 63 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 63 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 6 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 63 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 63)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 63 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 63 := by
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

theorem G_succ (n : ℕ) (u : Fin 64) :
    G (n + 1) u = ∑ w ∈ subs u, if okc u.val = true then G n w else 0 :=
  rfl

theorem G_base : ∀ u : Fin 64,
    G 6 u + 15 * G 4 u + 15 * G 2 u + G 0 u = 6 * G 5 u + 20 * G 3 u + 6 * G 1 u := by
  decide +kernel

theorem G_rec (m : ℕ) : ∀ u : Fin 64,
    G (m + 6) u + 15 * G (m + 4) u + 15 * G (m + 2) u + G m u =
      6 * G (m + 5) u + 20 * G (m + 3) u + 6 * G (m + 1) u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega,
      show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega,
      show m + 1 + 6 = (m + 6) + 1 by omega]
    rw [G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m, G_succ (m + 5),
      G_succ (m + 3), G_succ (m + 1)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 6) + 15 * a (m + 4) + 15 * a (m + 2) + a m =
      6 * a (m + 5) + 20 * a (m + 3) + 6 * a (m + 1) := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 63

theorem G_vals : G 1 63 = 20 ∧ G 2 63 = 125 ∧ G 3 63 = 440 ∧ G 4 63 = 1153 ∧ G 5 63 = 2524 ∧
    G 6 63 = 4893 := by
  decide +kernel

theorem a_vals : a 1 = 20 ∧ a 2 = 125 ∧ a 3 = 440 ∧ a 4 = 1153 ∧ a 5 = 2524 ∧ a 6 = 4893 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6]
  norm_num

theorem recurrence (n : ℕ) (hn : 6 < n) :
    a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h := a_rec m
  rw [show m + 6 - 1 = (m + 5) by omega, show m + 6 - 2 = (m + 4) by omega,
    show m + 6 - 3 = (m + 3) by omega, show m + 6 - 4 = (m + 2) by omega,
    show m + 6 - 5 = (m + 1) by omega, show m + 6 - 6 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (20 + 5 * X - 10 * X ^ 2 - 12 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 6 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 6 * (PowerSeries.mk F * X ^ 1) +
        C 15 * (PowerSeries.mk F * X ^ 2) - C 20 * (PowerSeries.mk F * X ^ 3) +
        C 15 * (PowerSeries.mk F * X ^ 4) - C 6 * (PowerSeries.mk F * X ^ 5) +
        C 1 * (PowerSeries.mk F * X ^ 6) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X * (20 + 5 * X - 10 * X ^ 2 - 12 * X ^ 3 + 6 * X ^ 4 - X ^ 5) : ℚ⟦X⟧) =
      C 20 * X ^ 1 + C 5 * X ^ 2 - C 10 * X ^ 3 - C 12 * X ^ 4 + C 6 * X ^ 5 - C 1 * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    have hr := recurrence (j + 7) (by omega)
    simp only [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
      show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega] at hr
    have hq : ((a (j + 7) : ℤ) : ℚ) = ((6 * a (j + 6) - 15 * a (j + 5) + 20 * a (j + 4) -
        15 * a (j + 3) + 6 * a (j + 2) - a (j + 1) : ℤ) : ℚ) := by
      rw [hr]
    push_cast at hq
    simp only [show 0 ≤ j + 7 by omega,
      show 1 ≤ j + 7 by omega,
      show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega,
      show 4 ≤ j + 7 by omega,
      show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega,
      show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega,
      show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 1) by omega,
      show ¬ (j + 7 = 2) by omega,
      show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega,
      show ¬ (j + 7 = 5) by omega,
      show ¬ (j + 7 = 6) by omega,
      show ¬ (j + 7 = 0) by omega,
      show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega,
      if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a249709.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
