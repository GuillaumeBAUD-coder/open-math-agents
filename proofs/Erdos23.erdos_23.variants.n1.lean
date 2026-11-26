import FormalConjectures.ErdosProblems.«23»

/-!
Every triangle-free graph on five vertices becomes bipartite after deleting at most one edge.
-/

namespace N1

open SimpleGraph

def bit (m k : Nat) : Bool := m.testBit k

def eidxNat (i j : Nat) : Nat :=
  let a := min i j
  let c := max i j
  if a == 0 then c - 1 else if a == 1 then c + 2 else if a == 2 then c + 4 else c + 5

def hasEdgeFin (m : Nat) (i j : Fin 5) : Bool :=
  if i = j then false else bit m (eidxNat i.val j.val)

def tri (m : Nat) (a b c : Fin 5) : Bool :=
  hasEdgeFin m a b && hasEdgeFin m a c && hasEdgeFin m b c

def hasTri (m : Nat) : Bool :=
  tri m 0 1 2 || tri m 0 1 3 || tri m 0 1 4 || tri m 0 2 3 || tri m 0 2 4 ||
    tri m 0 3 4 || tri m 1 2 3 || tri m 1 2 4 || tri m 1 3 4 || tri m 2 3 4

def pairOk (m mask : Nat) (i j : Fin 5) : Bool :=
  !(hasEdgeFin m i j) || (bit mask i.val != bit mask j.val)

def allPairs (m mask : Nat) : List (Fin 5 × Fin 5) → Bool
  | [] => true
  | p :: rest => pairOk m mask p.1 p.2 && allPairs m mask rest

def verts : List (Fin 5 × Fin 5) :=
  [(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (0, 4), (4, 0),
   (1, 2), (2, 1), (1, 3), (3, 1), (1, 4), (4, 1),
   (2, 3), (3, 2), (2, 4), (4, 2), (3, 4), (4, 3)]

def colorsOk (m mask : Nat) : Bool := allPairs m mask verts

def anyMask (m : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => colorsOk m n || anyMask m n

def someColor (m : Nat) : Bool := anyMask m 32

def clearBit (m k : Nat) : Nat := m &&& (1023 - (1 <<< k))

def anyClear (m : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => someColor (clearBit m n) || anyClear m n

def someDel (m : Nat) : Bool := anyClear m 10

def good (m : Nat) : Bool := someColor m || someDel m

def claim (m : Nat) : Bool := hasTri m || good m

def checkFrom (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => claim (lo + n) && checkFrom lo n

def searchColor (m : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => if colorsOk m fuel = true then fuel else searchColor m fuel

def searchDel (m : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => if someColor (clearBit m fuel) = true then fuel else searchDel m fuel

def keptMask (m : Nat) : Nat :=
  if someColor m = true then m else clearBit m (searchDel m 10)

def colorMask (m : Nat) : Nat := searchColor (keptMask m) 32

def ends1 : Fin 10 → Fin 5
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1
  | 5 => 1 | 6 => 1 | 7 => 2 | 8 => 2 | 9 => 3

def ends2 : Fin 10 → Fin 5
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 2
  | 5 => 3 | 6 => 4 | 7 => 3 | 8 => 4 | 9 => 4

def edgesOf (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : Fin 10 → Bool :=
  fun k => decide (G.Adj (ends1 k) (ends2 k))

def toNat (b : Fin 10 → Bool) : Nat :=
  (if b 0 then 1 else 0) ||| (if b 1 then 2 else 0) ||| (if b 2 then 4 else 0) |||
    (if b 3 then 8 else 0) ||| (if b 4 then 16 else 0) ||| (if b 5 then 32 else 0) |||
    (if b 6 then 64 else 0) ||| (if b 7 then 128 else 0) ||| (if b 8 then 256 else 0) |||
    (if b 9 then 512 else 0)

theorem bit_if_pow (c : Bool) {p i n : Nat} (hn : n = 2 ^ p) :
    bit (if c then n else 0) i = (c && decide (p = i)) := by
  cases c <;> simp [bit, hn, Nat.testBit_two_pow]

theorem bit_or (m n i : Nat) : bit (m ||| n) i = (bit m i || bit n i) := by
  simp [bit, Nat.testBit_or]

theorem bit_toNat_fold (b : Fin 10 → Bool) (i : Nat) :
    bit (toNat b) i =
      ((b 0 && decide ((0 : Nat) = i)) || (b 1 && decide ((1 : Nat) = i)) ||
        (b 2 && decide ((2 : Nat) = i)) || (b 3 && decide ((3 : Nat) = i)) ||
        (b 4 && decide ((4 : Nat) = i)) || (b 5 && decide ((5 : Nat) = i)) ||
        (b 6 && decide ((6 : Nat) = i)) || (b 7 && decide ((7 : Nat) = i)) ||
        (b 8 && decide ((8 : Nat) = i)) || (b 9 && decide ((9 : Nat) = i))) := by
  simp only [toNat, bit_or]
  rw [bit_if_pow (hn := (by decide : (1 : Nat) = 2 ^ 0))]
  rw [bit_if_pow (hn := (by decide : (2 : Nat) = 2 ^ 1))]
  rw [bit_if_pow (hn := (by decide : (4 : Nat) = 2 ^ 2))]
  rw [bit_if_pow (hn := (by decide : (8 : Nat) = 2 ^ 3))]
  rw [bit_if_pow (hn := (by decide : (16 : Nat) = 2 ^ 4))]
  rw [bit_if_pow (hn := (by decide : (32 : Nat) = 2 ^ 5))]
  rw [bit_if_pow (hn := (by decide : (64 : Nat) = 2 ^ 6))]
  rw [bit_if_pow (hn := (by decide : (128 : Nat) = 2 ^ 7))]
  rw [bit_if_pow (hn := (by decide : (256 : Nat) = 2 ^ 8))]
  rw [bit_if_pow (hn := (by decide : (512 : Nat) = 2 ^ 9))]

theorem bit_toNat (b : Fin 10 → Bool) (k : Fin 10) : bit (toNat b) k.val = b k := by
  rw [bit_toNat_fold]
  fin_cases k <;> simp

theorem decide_eq_false_of_lt {p i : Nat} (hp : p < i) : decide (p = i) = false := by
  have : p ≠ i := Nat.ne_of_lt hp
  simp [this]

theorem bit_high (b : Fin 10 → Bool) {i : Nat} (hi : 10 ≤ i) : bit (toNat b) i = false := by
  rw [bit_toNat_fold]
  simp [decide_eq_false_of_lt (show (0 : Nat) < i by omega),
    decide_eq_false_of_lt (show (1 : Nat) < i by omega),
    decide_eq_false_of_lt (show (2 : Nat) < i by omega),
    decide_eq_false_of_lt (show (3 : Nat) < i by omega),
    decide_eq_false_of_lt (show (4 : Nat) < i by omega),
    decide_eq_false_of_lt (show (5 : Nat) < i by omega),
    decide_eq_false_of_lt (show (6 : Nat) < i by omega),
    decide_eq_false_of_lt (show (7 : Nat) < i by omega),
    decide_eq_false_of_lt (show (8 : Nat) < i by omega),
    decide_eq_false_of_lt (show (9 : Nat) < i by omega)]

theorem testBit_1023_low : ∀ i : Fin 10, bit 1023 i.val = true := by
  decide

theorem testBit_1023_high {i : Nat} (hi : 10 ≤ i) : bit 1023 i = false := by
  have hlt : (1023 : Nat) < 2 ^ i := by
    have h10 : (1023 : Nat) < 2 ^ 10 := by decide
    exact Nat.lt_of_lt_of_le h10 (Nat.pow_le_pow_right (by decide) hi)
  simpa [bit] using Nat.testBit_lt_two_pow hlt

theorem toNat_mask (b : Fin 10 → Bool) : toNat b = toNat b &&& 1023 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  by_cases hi : i < 10
  · have h1023 : (1023).testBit i = true := by simpa [bit] using testBit_1023_low ⟨i, hi⟩
    simp only [h1023, Bool.and_true]
  · have hhi : 10 ≤ i := by omega
    have hL : (toNat b).testBit i = false := by simpa [bit] using bit_high b hhi
    have hR : (1023).testBit i = false := by simpa [bit] using testBit_1023_high hhi
    simp only [hL, hR, Bool.false_and]

theorem toNat_lt (b : Fin 10 → Bool) : toNat b < 1024 := by
  rw [toNat_mask b]
  have hle : toNat b &&& 1023 ≤ 1023 := Nat.and_le_right
  omega

theorem eidx_lt : ∀ i j : Fin 5, i ≠ j → eidxNat i.val j.val < 10 := by
  decide

theorem ends_spec : ∀ i j : Fin 5, ∀ k : Fin 10, i ≠ j → eidxNat i.val j.val = k.val →
    (ends1 k = i ∧ ends2 k = j) ∨ (ends1 k = j ∧ ends2 k = i) := by
  decide

theorem maskBit : ∀ k i : Fin 10,
    bit (1023 - (1 <<< k.val)) i.val = decide (i.val ≠ k.val) := by
  decide

theorem hasEdge_symm (m : Nat) (i j : Fin 5) : hasEdgeFin m i j = hasEdgeFin m j i := by
  fin_cases i <;> fin_cases j <;> rfl

def graphOf (m : Nat) : SimpleGraph (Fin 5) where
  Adj i j := hasEdgeFin m i j = true
  symm := ⟨fun i j h => by simpa [hasEdge_symm m i j] using h⟩
  loopless := ⟨fun i h => by simp [hasEdgeFin] at h⟩

theorem encode_adj {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj] (i j : Fin 5) :
    G.Adj i j ↔ hasEdgeFin (toNat (edgesOf G)) i j = true := by
  by_cases hij : i = j
  · subst hij
    constructor
    · intro h
      exact False.elim (G.irrefl h)
    · intro h
      simp [hasEdgeFin] at h
  · rw [hasEdgeFin, if_neg hij]
    have hlt : eidxNat i.val j.val < 10 := eidx_lt i j hij
    rw [bit_toNat (edgesOf G) ⟨eidxNat i.val j.val, hlt⟩]
    simp only [edgesOf, decide_eq_true_iff]
    rcases ends_spec i j ⟨eidxNat i.val j.val, hlt⟩ hij rfl with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · rw [hi, hj]
    · rw [hi, hj, adj_comm]

theorem tri_false {G : SimpleGraph (Fin 5)} {m : Nat} (hFree : G.CliqueFree 3)
    (henc : ∀ i j : Fin 5, G.Adj i j ↔ hasEdgeFin m i j = true) (a b c : Fin 5) :
    tri m a b c = false := by
  cases ht : tri m a b c with
  | false => rfl
  | true =>
    exfalso
    rw [tri, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at ht
    rcases ht with ⟨⟨hab, hac⟩, hbc⟩
    exact hFree {a, b, c}
      (is3Clique_triple_iff.2 ⟨(henc a b).2 hab, (henc a c).2 hac, (henc b c).2 hbc⟩)

theorem no_hasTri {G : SimpleGraph (Fin 5)} {m : Nat} (hFree : G.CliqueFree 3)
    (henc : ∀ i j : Fin 5, G.Adj i j ↔ hasEdgeFin m i j = true) : hasTri m = false := by
  have h012 := tri_false hFree henc 0 1 2
  have h013 := tri_false hFree henc 0 1 3
  have h014 := tri_false hFree henc 0 1 4
  have h023 := tri_false hFree henc 0 2 3
  have h024 := tri_false hFree henc 0 2 4
  have h034 := tri_false hFree henc 0 3 4
  have h123 := tri_false hFree henc 1 2 3
  have h124 := tri_false hFree henc 1 2 4
  have h134 := tri_false hFree henc 1 3 4
  have h234 := tri_false hFree henc 2 3 4
  simp [hasTri, h012, h013, h014, h023, h024, h034, h123, h124, h134, h234]

theorem allPairs_succ (m mask : Nat) (p : Fin 5 × Fin 5) (rest : List (Fin 5 × Fin 5)) :
    allPairs m mask (p :: rest) = (pairOk m mask p.1 p.2 && allPairs m mask rest) := rfl

theorem allPairs_mem {m mask : Nat} {l : List (Fin 5 × Fin 5)} {i j : Fin 5}
    (h : allPairs m mask l = true) (hm : (i, j) ∈ l) : pairOk m mask i j = true := by
  induction l with
  | nil => simp at hm
  | cons p rest ih =>
    rw [allPairs_succ, Bool.and_eq_true_iff] at h
    rcases h with ⟨hp, hr⟩
    simp [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact hp
    · exact ih hr hm

theorem mem_verts : ∀ i j : Fin 5, i ≠ j → (i, j) ∈ verts := by
  decide

theorem colorsOk_pair {m mask : Nat} {i j : Fin 5} (h : colorsOk m mask = true) (hne : i ≠ j) :
    pairOk m mask i j = true :=
  allPairs_mem h (mem_verts i j hne)

theorem bits_differ {m mask : Nat} {i j : Fin 5} (hp : pairOk m mask i j = true)
    (he : hasEdgeFin m i j = true) : bit mask i.val ≠ bit mask j.val := by
  rw [pairOk, Bool.or_eq_true_iff] at hp
  rcases hp with hn | hb
  · rw [Bool.not_eq_true'] at hn
    simp [hn] at he
  · cases hbi : bit mask i.val <;> cases hbj : bit mask j.val
    · simp [hbi, hbj] at hb
    · simp [hbi, hbj]
    · simp [hbi, hbj]
    · simp [hbi, hbj] at hb

def col (mask : Nat) (i : Fin 5) : Fin 2 :=
  if bit mask i.val then 1 else 0

theorem col_ne {mask : Nat} {i j : Fin 5} (h : bit mask i.val ≠ bit mask j.val) :
    col mask i ≠ col mask j := by
  cases hbi : bit mask i.val <;> cases hbj : bit mask j.val
  · simp [col, hbi, hbj] at h
  · simp [col, hbi, hbj]
  · simp [col, hbi, hbj]
  · simp [col, hbi, hbj] at h

theorem bip_of_colors {m mask : Nat} (hok : colorsOk m mask = true) : (graphOf m).IsBipartite := by
  refine ⟨Coloring.mk (col mask) ?_⟩
  intro i j hij
  have he : hasEdgeFin m i j = true := by simpa [graphOf] using hij
  have hne : i ≠ j := by
    intro h
    simp [hasEdgeFin, h] at he
  exact col_ne (bits_differ (colorsOk_pair hok hne) he)

theorem bit_clear_idx (m : Nat) (k i : Fin 10) :
    bit (clearBit m k.val) i.val = (bit m i.val && decide (i.val ≠ k.val)) := by
  have hm : bit (1023 - (1 <<< k.val)) i.val = decide (i.val ≠ k.val) := maskBit k i
  simp only [bit] at hm
  simp only [clearBit, bit, Nat.testBit_and, hm]

theorem hasEdge_clear_le {m k : Nat} {i j : Fin 5} (hk : k < 10)
    (h : hasEdgeFin (clearBit m k) i j = true) : hasEdgeFin m i j = true := by
  by_cases hij : i = j
  · simp [hasEdgeFin, hij] at h
  · rw [hasEdgeFin, if_neg hij] at h ⊢
    have hlt : eidxNat i.val j.val < 10 := eidx_lt i j hij
    have hbit := bit_clear_idx m ⟨k, hk⟩ ⟨eidxNat i.val j.val, hlt⟩
    rw [hbit, Bool.and_eq_true_iff] at h
    exact h.1

theorem kept_le {m k : Nat} (hk : k < 10) : graphOf (clearBit m k) ≤ graphOf m := by
  intro a b hab
  have h : hasEdgeFin (clearBit m k) a b = true := by simpa [graphOf] using hab
  simpa [graphOf] using hasEdge_clear_le hk h

theorem only_one_bit {m k : Nat} {i j : Fin 5} (hk : k < 10)
    (hG : hasEdgeFin m i j = true) (hH : hasEdgeFin (clearBit m k) i j = false) :
    eidxNat i.val j.val = k := by
  have hne : i ≠ j := by
    intro h
    simp [hasEdgeFin, h] at hG
  rw [hasEdgeFin, if_neg hne] at hG hH
  have hlt : eidxNat i.val j.val < 10 := eidx_lt i j hne
  have hbit := bit_clear_idx m ⟨k, hk⟩ ⟨eidxNat i.val j.val, hlt⟩
  rw [hbit, hG, Bool.true_and] at hH
  by_contra hneidx
  have : decide (eidxNat i.val j.val ≠ k) = true := by simp [hneidx]
  simp [this] at hH

theorem edge_is_cleared {m k : Nat} (hk : k < 10) {e : Sym2 (Fin 5)}
    (he : e ∈ (graphOf m).edgeSet) (hn : e ∉ (graphOf (clearBit m k)).edgeSet) :
    e = s(ends1 ⟨k, hk⟩, ends2 ⟨k, hk⟩) := by
  induction e using Sym2.ind with
  | h x y =>
    have hG : hasEdgeFin m x y = true := by simpa [graphOf, mem_edgeSet] using he
    have hNot : ¬ hasEdgeFin (clearBit m k) x y = true := by
      simpa [graphOf, mem_edgeSet] using hn
    have hH : hasEdgeFin (clearBit m k) x y = false := by
      cases hbit : hasEdgeFin (clearBit m k) x y
      · rfl
      · exact absurd hbit hNot
    have hidx : eidxNat x.val y.val = k := only_one_bit hk hG hH
    have hne : x ≠ y := by
      intro h
      simp [hasEdgeFin, h] at hG
    rcases ends_spec x y ⟨k, hk⟩ hne hidx with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · simp [hx, hy]
    · simp [hx, hy, Sym2.eq_swap]

theorem del_card {m k : Nat} (hk : k < 10) [DecidableRel (graphOf m).Adj]
    [DecidableRel (graphOf (clearBit m k)).Adj] :
    ((graphOf m).edgeFinset \ (graphOf (clearBit m k)).edgeFinset).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e1 he1 e2 he2
  simp only [Finset.mem_sdiff, mem_edgeFinset] at he1 he2
  rw [edge_is_cleared hk he1.1 he1.2, edge_is_cleared hk he2.1 he2.2]

theorem nodel_card (m : Nat) [DecidableRel (graphOf m).Adj] :
    ((graphOf m).edgeFinset \ (graphOf m).edgeFinset).card ≤ 1 := by
  rw [Finset.sdiff_self]
  simp

theorem anyMask_succ (m n : Nat) : anyMask m (n + 1) = (colorsOk m n || anyMask m n) := rfl

theorem anyMask_spec {m n : Nat} (h : anyMask m n = true) : ∃ k, k < n ∧ colorsOk m k = true := by
  induction n with
  | zero => simp [anyMask] at h
  | succ n ih =>
    rw [anyMask_succ, Bool.or_eq_true_iff] at h
    rcases h with hc | hr
    · exact ⟨n, by omega, hc⟩
    · obtain ⟨k, hk, hok⟩ := ih hr
      exact ⟨k, by omega, hok⟩

theorem searchColor_succ (m fuel : Nat) :
    searchColor m (fuel + 1) = (if colorsOk m fuel = true then fuel else searchColor m fuel) := rfl

theorem searchColor_spec {m fuel : Nat} (h : ∃ k, k < fuel ∧ colorsOk m k = true) :
    colorsOk m (searchColor m fuel) = true := by
  induction fuel with
  | zero =>
    rcases h with ⟨k, hk, _⟩
    omega
  | succ fuel ih =>
    rw [searchColor_succ]
    by_cases hc : colorsOk m fuel = true
    · rw [if_pos hc]
      exact hc
    · rw [if_neg hc]
      refine ih ?_
      rcases h with ⟨k, hk1, hk2⟩
      have hne : k ≠ fuel := by
        intro heq
        apply hc
        simpa [heq] using hk2
      exact ⟨k, by omega, hk2⟩

theorem anyClear_succ (m n : Nat) :
    anyClear m (n + 1) = (someColor (clearBit m n) || anyClear m n) := rfl

theorem anyClear_spec {m n : Nat} (h : anyClear m n = true) :
    ∃ k, k < n ∧ someColor (clearBit m k) = true := by
  induction n with
  | zero => simp [anyClear] at h
  | succ n ih =>
    rw [anyClear_succ, Bool.or_eq_true_iff] at h
    rcases h with hc | hr
    · exact ⟨n, by omega, hc⟩
    · obtain ⟨k, hk, hok⟩ := ih hr
      exact ⟨k, by omega, hok⟩

theorem searchDel_succ (m fuel : Nat) :
    searchDel m (fuel + 1) =
      (if someColor (clearBit m fuel) = true then fuel else searchDel m fuel) := rfl

theorem searchDel_spec {m fuel : Nat} (h : ∃ k, k < fuel ∧ someColor (clearBit m k) = true) :
    searchDel m fuel < fuel ∧ someColor (clearBit m (searchDel m fuel)) = true := by
  induction fuel with
  | zero =>
    rcases h with ⟨k, hk, _⟩
    omega
  | succ fuel ih =>
    rw [searchDel_succ]
    by_cases hc : someColor (clearBit m fuel) = true
    · rw [if_pos hc]
      exact ⟨by omega, hc⟩
    · rw [if_neg hc]
      rcases h with ⟨k, hk1, hk2⟩
      have hne : k ≠ fuel := by
        intro heq
        apply hc
        simpa [heq] using hk2
      have hs := ih ⟨k, by omega, hk2⟩
      exact ⟨by omega, hs.2⟩

theorem kept_spec {m : Nat} (hg : good m = true) : someColor (keptMask m) = true := by
  rw [good, Bool.or_eq_true_iff] at hg
  rw [keptMask]
  by_cases hc : someColor m = true
  · rw [if_pos hc]
    exact hc
  · rw [if_neg hc]
    rcases hg with h1 | h2
    · exact absurd h1 hc
    · have hs := searchDel_spec (m := m) (fuel := 10) (anyClear_spec (by simpa [someDel] using h2))
      exact hs.2

theorem color_spec {m : Nat} (hg : good m = true) :
    colorsOk (keptMask m) (colorMask m) = true := by
  have hs : someColor (keptMask m) = true := kept_spec hg
  rw [someColor] at hs
  exact searchColor_spec (m := keptMask m) (fuel := 32) (anyMask_spec hs)

theorem checkFrom_succ (lo n : Nat) :
    checkFrom lo (n + 1) = (claim (lo + n) && checkFrom lo n) := rfl

theorem claim_in_range {lo n m : Nat} (h : checkFrom lo n = true) (hmlo : lo ≤ m)
    (hmn : m < lo + n) : claim m = true := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
    rw [checkFrom_succ, Bool.and_eq_true_iff] at h
    rcases h with ⟨hc, hr⟩
    by_cases hlast : m = lo + n
    · rw [hlast]
      exact hc
    · exact ih hr hmlo (by omega)

set_option maxHeartbeats 2000000000 in
set_option maxRecDepth 100000 in
theorem check0 : checkFrom 0 256 = true := by
  decide

set_option maxHeartbeats 2000000000 in
set_option maxRecDepth 100000 in
theorem check1 : checkFrom 256 256 = true := by
  decide

set_option maxHeartbeats 2000000000 in
set_option maxRecDepth 100000 in
theorem check2 : checkFrom 512 256 = true := by
  decide

set_option maxHeartbeats 2000000000 in
set_option maxRecDepth 100000 in
theorem check3 : checkFrom 768 256 = true := by
  decide

theorem claim_lt {m : Nat} (hm : m < 1024) : claim m = true := by
  by_cases h0 : m < 256
  · exact claim_in_range check0 (by omega) (by omega)
  by_cases h1 : m < 512
  · exact claim_in_range check1 (by omega) (by omega)
  by_cases h2 : m < 768
  · exact claim_in_range check2 (by omega) (by omega)
  · exact claim_in_range check3 (by omega) (by omega)

end N1

open N1 SimpleGraph

theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n1 := by
  classical
  intro G hFree
  haveI : DecidableRel G.Adj := fun a b => Classical.propDecidable (G.Adj a b)
  let m : Nat := toNat (edgesOf G)
  have henc : ∀ i j : Fin 5, G.Adj i j ↔ hasEdgeFin m i j = true := by
    intro i j
    simpa [m] using encode_adj (G := G) i j
  have hno : hasTri m = false := no_hasTri hFree henc
  have hgood : good m = true := by
    have hclaim : claim m = true := claim_lt (by simpa [m] using toNat_lt (edgesOf G))
    rw [claim, Bool.or_eq_true_iff] at hclaim
    rcases hclaim with htri | hg
    · simp [hno] at htri
    · exact hg
  have hcol : colorsOk (keptMask m) (colorMask m) = true := color_spec hgood
  have hGeq : G = graphOf m := by
    ext a b
    simpa [graphOf] using henc a b
  refine ⟨graphOf (keptMask m), ?_, bip_of_colors hcol, ?_⟩
  · by_cases hc : someColor m = true
    · rw [keptMask, if_pos hc, hGeq]
    · have hsome : someDel m = true := by
        rw [good, Bool.or_eq_true_iff] at hgood
        rcases hgood with h1 | h2
        · exact absurd h1 hc
        · exact h2
      have hs :=
        searchDel_spec (m := m) (fuel := 10) (anyClear_spec (by simpa [someDel] using hsome))
      rw [keptMask, if_neg hc, hGeq]
      exact kept_le hs.1
  · rw [hGeq]
    by_cases hc : someColor m = true
    · rw [keptMask, if_pos hc]
      exact nodel_card m
    · have hsome : someDel m = true := by
        rw [good, Bool.or_eq_true_iff] at hgood
        rcases hgood with h1 | h2
        · exact absurd h1 hc
        · exact h2
      have hs :=
        searchDel_spec (m := m) (fuel := 10) (anyClear_spec (by simpa [someDel] using hsome))
      rw [keptMask, if_neg hc]
      exact del_card hs.1
