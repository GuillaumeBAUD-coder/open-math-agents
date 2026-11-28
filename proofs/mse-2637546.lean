import OMAStatements.S_mse_2637546

namespace MSE2637546

def nextIdx {len : ℕ} (h : 0 < len) (i : Fin len) : Fin len :=
  ⟨(i.val + 1) % len, Nat.mod_lt _ h⟩

/-- A Hamiltonian cycle on the integer interval `[L, R]` (`len = R - L + 1 ≥ 2`). -/
structure IntervalCycle (L R : ℕ) where
  len : ℕ
  hlen : len = R - L + 1
  hpos : 2 ≤ len
  seq : Fin len → ℕ
  hinj : Function.Injective seq
  hmem : ∀ i : Fin len, L ≤ seq i ∧ seq i ≤ R
  hadj : ∀ i : Fin len, IsSquare (seq i + seq (nextIdx (by omega : 0 < len) i))

/-- Undirected edge membership in an `IntervalCycle`. -/
def HasEdge {L R : ℕ} (c : IntervalCycle L R) (u v : ℕ) : Prop :=
  ∃ i : Fin c.len,
    (c.seq i = u ∧ c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) i) = v) ∨
    (c.seq i = v ∧ c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) i) = u)

/-- Number of edges in `c` whose endpoint sum equals `sq`. -/
noncomputable def edgeCount {L R : ℕ} (c : IntervalCycle L R) (sq : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin c.len)).filter
    (fun i => c.seq i + c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) i) = sq)).card

/-- Whether `c` contains at least one edge of sum `s * s` in mod-5 class `cls`:
    `cls = 0` means `s % 5 = 0`; `cls = 1` means `s % 5 = 1 ∨ s % 5 = 4`;
    `cls = 2` means `s % 5 = 2 ∨ s % 5 = 3`. -/
def HasMod5Class {L R : ℕ} (c : IntervalCycle L R) (cls : ℕ) : Prop :=
  ∃ i : Fin c.len, ∃ s : ℕ,
    c.seq i + c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) i) = s * s ∧
    (if cls = 0 then s % 5 = 0
     else if cls = 1 then s % 5 = 1 ∨ s % 5 = 4
     else s % 5 = 2 ∨ s % 5 = 3)

/-- Self-sustaining mod-5 invariant for `n ≥ 54` (used for all `n ≥ 19857`). -/
def InvMod5 (n : ℕ) : Prop :=
  ∃ c : IntervalCycle 1 n,
    HasMod5Class c 0 ∧ HasMod5Class c 1 ∧ HasMod5Class c 2

/-- Small-edge multiplicity invariant for `n ∈ [54, 19856]`. -/
def InvSmall (k4 k5 k6 k7 n : ℕ) : Prop :=
  ∃ c : IntervalCycle 1 n,
    k4 ≤ edgeCount c 16 ∧
    k5 ≤ edgeCount c 25 ∧
    k6 ≤ edgeCount c 36 ∧
    k7 ≤ edgeCount c 49

/-- Target Hamiltonian path property matching `OMA.S_mse_2637546.main`. -/
def HasHamPath (n : ℕ) : Prop :=
  ∃ p : Equiv.Perm (Fin n),
    ∀ i j : Fin n, j.val = i.val + 1 → IsSquare ((p i).val + 1 + ((p j).val + 1))

/-- Piecewise reflection matching evaluator on `ℕ`. Each triple `(lo, hi, sq)` maps
    `x ∈ [lo, hi]` to `sq - x`. -/
def evalMatching : List (ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], x => x
  | (lo, hi, sq) :: rest, x =>
      if lo ≤ x ∧ x ≤ hi then sq - x else evalMatching rest x

end MSE2637546

namespace MSE2637546.S1

open MSE2637546

/-- Mod-5 residue class predicate matching `HasMod5Class`. -/
def mod5Pred (cls s : ℕ) : Prop :=
  if cls = 0 then s % 5 = 0
  else if cls = 1 then s % 5 = 1 ∨ s % 5 = 4
  else s % 5 = 2 ∨ s % 5 = 3

private lemma sq_eq_sq_nat {a b : ℕ} (h : a * a = b * b) : a = b := by
  nlinarith only [h]

private lemma exists_of_edgeCount_pos {L R sq : ℕ} {c : IntervalCycle L R}
    (h : 1 ≤ edgeCount c sq) :
    ∃ i : Fin c.len,
      c.seq i + c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) i) = sq := by
  unfold edgeCount at h
  have hpos : 0 < ((Finset.univ : Finset (Fin c.len)).filter
      (fun i => c.seq i + c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) i) = sq)).card := by
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.2⟩

/-! ### 1-3: Basic Conversions -/

theorem intervalCycle_to_hasHamPath {n : ℕ} (hn : 2 ≤ n) (c : IntervalCycle 1 n) : HasHamPath n := by
  have hlen : c.len = n := by have := c.hlen; omega
  let f : Fin n → Fin n := fun i =>
    ⟨c.seq ⟨i.val, by omega⟩ - 1, by
      have hm := c.hmem ⟨i.val, by omega⟩
      omega⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    have hv : (f i).val = (f j).val := congrArg Fin.val hij
    simp only [f] at hv
    have hmi := c.hmem ⟨i.val, by omega⟩
    have hmj := c.hmem ⟨j.val, by omega⟩
    have hseq : c.seq ⟨i.val, by omega⟩ = c.seq ⟨j.val, by omega⟩ := by omega
    have hidx := c.hinj hseq
    exact Fin.ext (Fin.mk.inj hidx)
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  refine ⟨Equiv.ofBijective f hfbij, ?_⟩
  intro i j hij
  have hmi := c.hmem ⟨i.val, by omega⟩
  have hmj := c.hmem ⟨j.val, by omega⟩
  have hpi : (Equiv.ofBijective f hfbij i).val + 1 = c.seq ⟨i.val, by omega⟩ := by
    simp only [Equiv.ofBijective_apply, f]; omega
  have hpj : (Equiv.ofBijective f hfbij j).val + 1 = c.seq ⟨j.val, by omega⟩ := by
    simp only [Equiv.ofBijective_apply, f]; omega
  rw [hpi, hpj]
  have hnext : nextIdx (by omega : 0 < c.len) ⟨i.val, by omega⟩ = ⟨j.val, by omega⟩ := by
    apply Fin.ext
    simp only [nextIdx]
    have hlt : i.val + 1 < c.len := by omega
    rw [Nat.mod_eq_of_lt hlt]
    exact hij.symm
  rw [← hnext]
  exact c.hadj ⟨i.val, by omega⟩

theorem invSmall_to_invMod5 {n : ℕ} (h : InvSmall 1 1 1 1 n) : InvMod5 n := by
  rcases h with ⟨c, h16, h25, _, h49⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := exists_of_edgeCount_pos h25
    exact ⟨i, 5, hi, by decide⟩
  · obtain ⟨i, hi⟩ := exists_of_edgeCount_pos h16
    exact ⟨i, 4, hi, by decide⟩
  · obtain ⟨i, hi⟩ := exists_of_edgeCount_pos h49
    exact ⟨i, 7, hi, by decide⟩

theorem invMod5_to_hasHamPath {n : ℕ} (hn : 2 ≤ n) (h : InvMod5 n) : HasHamPath n := by
  rcases h with ⟨c, _⟩
  exact intervalCycle_to_hasHamPath hn c

/-! ### 4: Core 1-Edge Cycle Splicing -/

private lemma mod_add_eq {n r k : ℕ} (hr : r < n) (hk : k < n) :
    (r + k) % n = if r + k < n then r + k else r + k - n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

private def rotIdx {len : ℕ} (h : 0 < len) (i0 k : Fin len) : Fin len :=
  ⟨((i0.val + 1) % len + k.val) % len, Nat.mod_lt _ h⟩

private lemma rotIdx_zero {len : ℕ} (h : 0 < len) (i0 : Fin len) :
    rotIdx h i0 ⟨0, h⟩ = nextIdx h i0 := by
  apply Fin.ext
  simp only [rotIdx, nextIdx, Nat.add_zero]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ h)

private lemma rotIdx_last {len : ℕ} (h : 0 < len) (i0 : Fin len) :
    rotIdx h i0 ⟨len - 1, by omega⟩ = i0 := by
  apply Fin.ext
  simp only [rotIdx]
  have hr : (i0.val + 1) % len < len := Nat.mod_lt _ h
  rw [mod_add_eq hr (by omega)]
  by_cases hi : i0.val + 1 < len
  · have hmod : (i0.val + 1) % len = i0.val + 1 := Nat.mod_eq_of_lt hi
    rw [hmod]
    split_ifs <;> omega
  · have heq : i0.val + 1 = len := by omega
    have hmod : (i0.val + 1) % len = 0 := by rw [heq, Nat.mod_self]
    rw [hmod]
    split_ifs <;> omega

private lemma rotIdx_succ {len : ℕ} (h : 0 < len) (i0 : Fin len) {k : ℕ} (hk : k + 1 < len) :
    rotIdx h i0 ⟨k + 1, hk⟩ = nextIdx h (rotIdx h i0 ⟨k, by omega⟩) := by
  apply Fin.ext
  simp only [rotIdx, nextIdx]
  symm
  rw [Nat.mod_add_mod, Nat.add_assoc]

private lemma rotIdx_inj {len : ℕ} (h : 0 < len) (i0 : Fin len) :
    Function.Injective (rotIdx h i0) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  simp only [rotIdx] at hv
  have hr : (i0.val + 1) % len < len := Nat.mod_lt _ h
  rw [mod_add_eq hr a.isLt, mod_add_eq hr b.isLt] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

private def unrotVal {len : ℕ} (i0 j : Fin len) : ℕ :=
  if (i0.val + 1) % len ≤ j.val then j.val - (i0.val + 1) % len
  else j.val + len - (i0.val + 1) % len

private lemma unrotVal_lt {len : ℕ} (h : 2 ≤ len) {i0 j : Fin len} (hne : j ≠ i0) :
    unrotVal i0 j < len - 1 := by
  have hval : j.val ≠ i0.val := fun heq => hne (Fin.ext heq)
  unfold unrotVal
  by_cases hi : i0.val + 1 < len
  · have hmod : (i0.val + 1) % len = i0.val + 1 := Nat.mod_eq_of_lt hi
    rw [hmod]
    split_ifs <;> omega
  · have heq : i0.val + 1 = len := by omega
    have hmod : (i0.val + 1) % len = 0 := by rw [heq, Nat.mod_self]
    rw [hmod]
    split_ifs <;> omega

private lemma rotIdx_unrotVal {len : ℕ} (h : 2 ≤ len) {i0 j : Fin len} (hne : j ≠ i0) :
    rotIdx (by omega : 0 < len) i0 ⟨unrotVal i0 j, by have := unrotVal_lt h hne; omega⟩ = j := by
  apply Fin.ext
  simp only [rotIdx]
  have hr : (i0.val + 1) % len < len := Nat.mod_lt _ (by omega)
  have hu : unrotVal i0 j < len - 1 := unrotVal_lt h hne
  rw [mod_add_eq hr (by omega)]
  unfold unrotVal
  split_ifs <;> omega

private def revIdx {len : ℕ} (h : 2 ≤ len) (j : Fin len) : Fin len :=
  if hj : j.val + 1 < len then ⟨len - 2 - j.val, by omega⟩
  else ⟨len - 1, by omega⟩

private lemma revIdx_inj {len : ℕ} (h : 2 ≤ len) : Function.Injective (revIdx h) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  simp only [revIdx] at hv
  apply Fin.ext
  split_ifs at hv <;> simp only [] at hv <;> omega

private def reverseCycle {L R : ℕ} (c : IntervalCycle L R) : IntervalCycle L R where
  len := c.len
  hlen := c.hlen
  hpos := c.hpos
  seq := fun k => c.seq ⟨c.len - 1 - k.val, by omega⟩
  hinj := by
    intro a b hab
    have h := c.hinj hab
    have hv : c.len - 1 - a.val = c.len - 1 - b.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  hmem := fun k => c.hmem ⟨c.len - 1 - k.val, by omega⟩
  hadj := by
    intro k
    have hlen := c.hpos
    by_cases hk : k.val + 1 < c.len
    · have hnext : (nextIdx (by omega : 0 < c.len) k).val = k.val + 1 := by
        simp only [nextIdx]; exact Nat.mod_eq_of_lt hk
      have h1 : (⟨c.len - 1 - (nextIdx (by omega : 0 < c.len) k).val, by omega⟩ : Fin c.len) =
                ⟨c.len - 2 - k.val, by omega⟩ := by
        apply Fin.ext; dsimp only; omega
      have h2 : nextIdx (by omega : 0 < c.len) ⟨c.len - 2 - k.val, by omega⟩ =
                ⟨c.len - 1 - k.val, by omega⟩ := by
        apply Fin.ext
        simp only [nextIdx]
        have hlt : c.len - 2 - k.val + 1 < c.len := by omega
        rw [Nat.mod_eq_of_lt hlt]; omega
      rw [h1, Nat.add_comm, ← h2]
      exact c.hadj ⟨c.len - 2 - k.val, by omega⟩
    · have hk_eq : k.val = c.len - 1 := by omega
      have hnext : (nextIdx (by omega : 0 < c.len) k).val = 0 := by
        simp only [nextIdx]
        have heq : k.val + 1 = c.len := by omega
        rw [heq, Nat.mod_self]
      have h1 : (⟨c.len - 1 - k.val, by omega⟩ : Fin c.len) =
                nextIdx (by omega : 0 < c.len) ⟨c.len - 1, by omega⟩ := by
        apply Fin.ext
        simp only [nextIdx]
        have heq : c.len - 1 + 1 = c.len := by omega
        rw [heq, Nat.mod_self]; omega
      have h2 : (⟨c.len - 1 - (nextIdx (by omega : 0 < c.len) k).val, by omega⟩ : Fin c.len) =
                ⟨c.len - 1, by omega⟩ := by
        apply Fin.ext; dsimp only; omega
      rw [h1, h2, Nat.add_comm]
      exact c.hadj ⟨c.len - 1, by omega⟩

private lemma reverseCycle_seq_revIdx {L R : ℕ} (c : IntervalCycle L R) (j : Fin c.len) :
    (reverseCycle c).seq (revIdx c.hpos j) =
      c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) j) := by
  have hlen := c.hpos
  by_cases hj : j.val + 1 < c.len
  · change c.seq ⟨c.len - 1 - (revIdx c.hpos j).val, _⟩ = _
    congr 1
    apply Fin.ext
    simp only [revIdx, hj, ↓reduceDIte, nextIdx]
    rw [Nat.mod_eq_of_lt hj]; omega
  · change c.seq ⟨c.len - 1 - (revIdx c.hpos j).val, _⟩ = _
    congr 1
    apply Fin.ext
    simp only [revIdx, hj, ↓reduceDIte, nextIdx]
    have heq : j.val + 1 = c.len := by omega
    rw [heq, Nat.mod_self]; omega

private lemma reverseCycle_seq_next_revIdx {L R : ℕ} (c : IntervalCycle L R) (j : Fin c.len) :
    (reverseCycle c).seq
      (nextIdx (by have := (reverseCycle c).hpos; omega : 0 < (reverseCycle c).len) (revIdx c.hpos j)) =
      c.seq j := by
  have hlen := c.hpos
  by_cases hj : j.val + 1 < c.len
  · change c.seq ⟨c.len - 1 - ((revIdx c.hpos j).val + 1) % c.len, _⟩ = c.seq j
    congr 1
    apply Fin.ext
    simp only [revIdx, hj, ↓reduceDIte]
    have hlt : c.len - 2 - j.val + 1 < c.len := by omega
    rw [Nat.mod_eq_of_lt hlt]; omega
  · change c.seq ⟨c.len - 1 - ((revIdx c.hpos j).val + 1) % c.len, _⟩ = c.seq j
    congr 1
    apply Fin.ext
    simp only [revIdx, hj, ↓reduceDIte]
    have heq : c.len - 1 + 1 = c.len := by omega
    rw [heq, Nat.mod_self]; omega

private lemma splice_cycles_fwd {L R : ℕ} (hL : 3 ≤ L) (hLR : L + 1 ≤ R)
    (c1 : IntervalCycle 1 (L - 1)) (c2 : IntervalCycle L R)
    (i1 : Fin c1.len) (i2 : Fin c2.len)
    (h12 : IsSquare (c1.seq i1 + c2.seq (nextIdx (by have := c2.hpos; omega : 0 < c2.len) i2)))
    (h21 : IsSquare (c1.seq (nextIdx (by have := c1.hpos; omega : 0 < c1.len) i1) + c2.seq i2)) :
    ∃ c : IntervalCycle 1 R,
      (∀ sq : ℕ, c1.seq i1 + c1.seq (nextIdx (by have := c1.hpos; omega : 0 < c1.len) i1) ≠ sq →
        edgeCount c1 sq ≤ edgeCount c sq) ∧
      (∀ sq : ℕ, edgeCount c1 sq - 1 ≤ edgeCount c sq) ∧
      (∀ cls : ℕ,
        (∃ j : Fin c1.len, j ≠ i1 ∧ ∃ s : ℕ,
          c1.seq j + c1.seq (nextIdx (by have := c1.hpos; omega : 0 < c1.len) j) = s * s ∧
          mod5Pred cls s) →
        HasMod5Class c cls) ∧
      (∀ cls : ℕ,
        (∃ j : Fin c2.len, j ≠ i2 ∧ ∃ s : ℕ,
          c2.seq j + c2.seq (nextIdx (by have := c2.hpos; omega : 0 < c2.len) j) = s * s ∧
          mod5Pred cls s) →
        HasMod5Class c cls) := by
  have hlen1 : c1.len = L - 1 := by have := c1.hlen; omega
  have hlen2 : c2.len = R - L + 1 := by have := c2.hlen; omega
  have hp1 : 2 ≤ c1.len := c1.hpos
  have hp2 : 2 ≤ c2.len := c2.hpos
  let N : ℕ := c1.len + c2.len
  have hN : N = R - 1 + 1 := by omega
  let sseq : Fin N → ℕ := fun idx =>
    if h : idx.val < c1.len then
      c1.seq (rotIdx (by omega : 0 < c1.len) i1 ⟨idx.val, h⟩)
    else
      c2.seq (rotIdx (by omega : 0 < c2.len) i2 ⟨idx.val - c1.len, by omega⟩)
  have hmem : ∀ idx : Fin N, 1 ≤ sseq idx ∧ sseq idx ≤ R := by
    intro idx
    simp only [sseq]
    split_ifs with h
    · have hm := c1.hmem (rotIdx (by omega : 0 < c1.len) i1 ⟨idx.val, h⟩)
      omega
    · have hm := c2.hmem (rotIdx (by omega : 0 < c2.len) i2 ⟨idx.val - c1.len, by omega⟩)
      omega
  have hinj : Function.Injective sseq := by
    intro a b hab
    simp only [sseq] at hab
    split_ifs at hab with ha hb hb
    · have hrot := c1.hinj hab
      have hk := rotIdx_inj (by omega : 0 < c1.len) i1 hrot
      exact Fin.ext (Fin.mk.inj hk)
    · have hm1 := c1.hmem (rotIdx (by omega : 0 < c1.len) i1 ⟨a.val, ha⟩)
      have hm2 := c2.hmem (rotIdx (by omega : 0 < c2.len) i2 ⟨b.val - c1.len, by omega⟩)
      omega
    · have hm1 := c1.hmem (rotIdx (by omega : 0 < c1.len) i1 ⟨b.val, hb⟩)
      have hm2 := c2.hmem (rotIdx (by omega : 0 < c2.len) i2 ⟨a.val - c1.len, by omega⟩)
      omega
    · have hrot := c2.hinj hab
      have hk := rotIdx_inj (by omega : 0 < c2.len) i2 hrot
      have hv : a.val - c1.len = b.val - c1.len := congrArg Fin.val hk
      exact Fin.ext (by omega)
  have hadj : ∀ idx : Fin N, IsSquare (sseq idx + sseq (nextIdx (by omega : 0 < N) idx)) := by
    intro idx
    by_cases h1 : idx.val + 1 < c1.len
    · have hnext : (nextIdx (by omega : 0 < N) idx).val = idx.val + 1 := by
        simp only [nextIdx]; exact Nat.mod_eq_of_lt (by omega)
      have hs1 : sseq idx = c1.seq (rotIdx (by omega : 0 < c1.len) i1 ⟨idx.val, by omega⟩) := by
        simp only [sseq, show idx.val < c1.len by omega, ↓reduceDIte]
      have hs2 : sseq (nextIdx (by omega : 0 < N) idx) =
          c1.seq (nextIdx (by omega : 0 < c1.len) (rotIdx (by omega : 0 < c1.len) i1 ⟨idx.val, by omega⟩)) := by
        simp only [sseq, show (nextIdx (by omega : 0 < N) idx).val < c1.len by omega, ↓reduceDIte]
        congr 1
        have hidx : (⟨(nextIdx (by omega : 0 < N) idx).val, by omega⟩ : Fin c1.len) = ⟨idx.val + 1, h1⟩ :=
          Fin.ext hnext
        rw [hidx, rotIdx_succ (by omega : 0 < c1.len) i1 h1]
      rw [hs1, hs2]
      exact c1.hadj _
    · by_cases h2 : idx.val + 1 = c1.len
      · have hnext : (nextIdx (by omega : 0 < N) idx).val = c1.len := by
          simp only [nextIdx]; rw [Nat.mod_eq_of_lt (by omega)]; exact h2
        have hs1 : sseq idx = c1.seq i1 := by
          simp only [sseq, show idx.val < c1.len by omega, ↓reduceDIte]
          have hidx : (⟨idx.val, by omega⟩ : Fin c1.len) = ⟨c1.len - 1, by omega⟩ := by
            apply Fin.ext; dsimp only; omega
          rw [hidx, rotIdx_last]
        have hs2 : sseq (nextIdx (by omega : 0 < N) idx) = c2.seq (nextIdx (by omega : 0 < c2.len) i2) := by
          simp only [sseq, show ¬((nextIdx (by omega : 0 < N) idx).val < c1.len) by omega, ↓reduceDIte]
          have hidx : (⟨(nextIdx (by omega : 0 < N) idx).val - c1.len, by omega⟩ : Fin c2.len) =
                      ⟨0, by omega⟩ := by
            apply Fin.ext; dsimp only; omega
          rw [hidx, rotIdx_zero]
        rw [hs1, hs2]
        exact h12
      · by_cases h3 : idx.val + 1 < N
        · have hnext : (nextIdx (by omega : 0 < N) idx).val = idx.val + 1 := by
            simp only [nextIdx]; exact Nat.mod_eq_of_lt h3
          have hs1 : sseq idx = c2.seq (rotIdx (by omega : 0 < c2.len) i2 ⟨idx.val - c1.len, by omega⟩) := by
            simp only [sseq, show ¬(idx.val < c1.len) by omega, ↓reduceDIte]
          have hs2 : sseq (nextIdx (by omega : 0 < N) idx) =
              c2.seq (nextIdx (by omega : 0 < c2.len) (rotIdx (by omega : 0 < c2.len) i2 ⟨idx.val - c1.len, by omega⟩)) := by
            simp only [sseq, show ¬((nextIdx (by omega : 0 < N) idx).val < c1.len) by omega, ↓reduceDIte]
            congr 1
            have hidx : (⟨(nextIdx (by omega : 0 < N) idx).val - c1.len, by omega⟩ : Fin c2.len) =
                        ⟨(idx.val - c1.len) + 1, by omega⟩ := by
              apply Fin.ext; dsimp only; omega
            rw [hidx, rotIdx_succ (by omega : 0 < c2.len) i2 (by omega)]
          rw [hs1, hs2]
          exact c2.hadj _
        · have hnext : (nextIdx (by omega : 0 < N) idx).val = 0 := by
            simp only [nextIdx]
            have heq : idx.val + 1 = N := by omega
            rw [heq, Nat.mod_self]
          have hs1 : sseq idx = c2.seq i2 := by
            simp only [sseq, show ¬(idx.val < c1.len) by omega, ↓reduceDIte]
            have hidx : (⟨idx.val - c1.len, by omega⟩ : Fin c2.len) = ⟨c2.len - 1, by omega⟩ := by
              apply Fin.ext; dsimp only; omega
            rw [hidx, rotIdx_last]
          have hs2 : sseq (nextIdx (by omega : 0 < N) idx) = c1.seq (nextIdx (by omega : 0 < c1.len) i1) := by
            simp only [sseq, show (nextIdx (by omega : 0 < N) idx).val < c1.len by omega, ↓reduceDIte]
            have hidx : (⟨(nextIdx (by omega : 0 < N) idx).val, by omega⟩ : Fin c1.len) =
                        ⟨0, by omega⟩ := Fin.ext hnext
            rw [hidx, rotIdx_zero]
          rw [hs1, hs2, Nat.add_comm]
          exact h21
  let c : IntervalCycle 1 R :=
    { len := N
      hlen := hN
      hpos := by omega
      seq := sseq
      hinj := hinj
      hmem := hmem
      hadj := hadj }
  have hc_len : c.len = N := rfl
  have hc1_edge : ∀ j : Fin c1.len, j ≠ i1 →
      ∃ idx : Fin c.len,
        idx.val = unrotVal i1 j ∧
        c.seq idx + c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) idx) =
          c1.seq j + c1.seq (nextIdx (by omega : 0 < c1.len) j) := by
    intro j hne
    have hu : unrotVal i1 j < c1.len - 1 := unrotVal_lt hp1 hne
    let idx : Fin c.len := ⟨unrotVal i1 j, by omega⟩
    refine ⟨idx, rfl, ?_⟩
    have hnext : (nextIdx (by omega : 0 < c.len) idx).val = unrotVal i1 j + 1 := by
      simp only [nextIdx, idx]; exact Nat.mod_eq_of_lt (by omega)
    have hs1 : c.seq idx = c1.seq j := by
      change sseq idx = c1.seq j
      simp only [sseq, idx, show unrotVal i1 j < c1.len by omega, ↓reduceDIte]
      rw [rotIdx_unrotVal hp1 hne]
    have hs2 : c.seq (nextIdx (by omega : 0 < c.len) idx) = c1.seq (nextIdx (by omega : 0 < c1.len) j) := by
      change sseq (nextIdx (by omega : 0 < N) idx) = c1.seq (nextIdx (by omega : 0 < c1.len) j)
      simp only [sseq, show (nextIdx (by omega : 0 < N) idx).val < c1.len by omega, ↓reduceDIte]
      have hfin : (⟨(nextIdx (by omega : 0 < N) idx).val, by omega⟩ : Fin c1.len) =
                  ⟨unrotVal i1 j + 1, by omega⟩ := Fin.ext hnext
      rw [hfin, rotIdx_succ (by omega : 0 < c1.len) i1 (by omega), rotIdx_unrotVal hp1 hne]
    rw [hs1, hs2]
  have hc2_edge : ∀ j : Fin c2.len, j ≠ i2 →
      ∃ idx : Fin c.len,
        c.seq idx + c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) idx) =
          c2.seq j + c2.seq (nextIdx (by omega : 0 < c2.len) j) := by
    intro j hne
    have hu : unrotVal i2 j < c2.len - 1 := unrotVal_lt hp2 hne
    let idx : Fin c.len := ⟨c1.len + unrotVal i2 j, by omega⟩
    refine ⟨idx, ?_⟩
    have hnext : (nextIdx (by omega : 0 < c.len) idx).val = c1.len + unrotVal i2 j + 1 := by
      simp only [nextIdx, idx]; exact Nat.mod_eq_of_lt (by omega)
    have hs1 : c.seq idx = c2.seq j := by
      change sseq idx = c2.seq j
      simp only [sseq, idx, show ¬(c1.len + unrotVal i2 j < c1.len) by omega, ↓reduceDIte]
      have hfin : (⟨c1.len + unrotVal i2 j - c1.len, by omega⟩ : Fin c2.len) =
                  ⟨unrotVal i2 j, by omega⟩ := by
        apply Fin.ext; dsimp only; omega
      rw [hfin, rotIdx_unrotVal hp2 hne]
    have hs2 : c.seq (nextIdx (by omega : 0 < c.len) idx) = c2.seq (nextIdx (by omega : 0 < c2.len) j) := by
      change sseq (nextIdx (by omega : 0 < N) idx) = c2.seq (nextIdx (by omega : 0 < c2.len) j)
      simp only [sseq, show ¬((nextIdx (by omega : 0 < N) idx).val < c1.len) by omega, ↓reduceDIte]
      have hfin : (⟨(nextIdx (by omega : 0 < N) idx).val - c1.len, by omega⟩ : Fin c2.len) =
                  ⟨unrotVal i2 j + 1, by omega⟩ := by
        apply Fin.ext; dsimp only; omega
      rw [hfin, rotIdx_succ (by omega : 0 < c2.len) i2 (by omega), rotIdx_unrotVal hp2 hne]
    rw [hs1, hs2]
  have herase : ∀ sq : ℕ,
      (((Finset.univ : Finset (Fin c1.len)).filter
        (fun j => c1.seq j + c1.seq (nextIdx (by omega : 0 < c1.len) j) = sq)).erase i1).card ≤
      edgeCount c sq := by
    intro sq
    unfold edgeCount
    let S1 := (Finset.univ : Finset (Fin c1.len)).filter
      (fun j => c1.seq j + c1.seq (nextIdx (by omega : 0 < c1.len) j) = sq)
    let Sc := (Finset.univ : Finset (Fin c.len)).filter
      (fun idx => c.seq idx + c.seq (nextIdx (by omega : 0 < c.len) idx) = sq)
    let φ : Fin c1.len → Fin c.len := fun j =>
      if hne : j ≠ i1 then ⟨unrotVal i1 j, by have := unrotVal_lt hp1 hne; omega⟩
      else ⟨0, by omega⟩
    have hmap : ∀ j ∈ S1.erase i1, φ j ∈ Sc := by
      intro j hj
      rw [Finset.mem_erase, Finset.mem_filter] at hj
      rcases hj with ⟨hne, _, hsq⟩
      obtain ⟨idx, hidx_val, hidx_sum⟩ := hc1_edge j hne
      have hφ : φ j = idx := by
        apply Fin.ext
        dsimp only [φ]
        rw [dif_pos hne]
        exact hidx_val.symm
      rw [hφ, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hidx_sum, hsq]⟩
    have hinjOn : Set.InjOn φ (S1.erase i1 : Set (Fin c1.len)) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_erase] at ha hb
      have hv := congrArg Fin.val hab
      dsimp only [φ] at hv
      rw [dif_pos ha.1, dif_pos hb.1] at hv
      have hu1 := rotIdx_unrotVal hp1 ha.1
      have hu2 := rotIdx_unrotVal hp1 hb.1
      rw [← hu1, ← hu2]
      congr 1
      exact Fin.ext hv
    exact Finset.card_le_card_of_injOn φ hmap hinjOn
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro sq hne
    have hle := herase sq
    have hnotmem : i1 ∉ (Finset.univ : Finset (Fin c1.len)).filter
        (fun j => c1.seq j + c1.seq (nextIdx (by omega : 0 < c1.len) j) = sq) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hne
    rw [Finset.erase_eq_of_notMem hnotmem] at hle
    exact hle
  · intro sq
    have hle := herase sq
    have hcard : edgeCount c1 sq - 1 ≤
        (((Finset.univ : Finset (Fin c1.len)).filter
          (fun j => c1.seq j + c1.seq (nextIdx (by omega : 0 < c1.len) j) = sq)).erase i1).card := by
      unfold edgeCount
      by_cases hm : i1 ∈ (Finset.univ : Finset (Fin c1.len)).filter
          (fun j => c1.seq j + c1.seq (nextIdx (by omega : 0 < c1.len) j) = sq)
      · rw [Finset.card_erase_of_mem hm]
      · rw [Finset.erase_eq_of_notMem hm]; omega
    omega
  · intro cls ⟨j, hne, s, hsum, hpred⟩
    obtain ⟨idx, _, hidx_sum⟩ := hc1_edge j hne
    exact ⟨idx, s, by rw [hidx_sum, hsum], hpred⟩
  · intro cls ⟨j, hne, s, hsum, hpred⟩
    obtain ⟨idx, hidx_sum⟩ := hc2_edge j hne
    exact ⟨idx, s, by rw [hidx_sum, hsum], hpred⟩

theorem splice_cycles {L R : ℕ} (hL : 3 ≤ L) (hLR : L + 1 ≤ R)
    (c1 : IntervalCycle 1 (L - 1)) (c2 : IntervalCycle L R)
    (i1 : Fin c1.len) (i2 : Fin c2.len)
    (hcross :
      (IsSquare (c1.seq i1 + c2.seq i2) ∧
       IsSquare (c1.seq (nextIdx (by have := c1.hpos; omega : 0 < c1.len) i1) +
                 c2.seq (nextIdx (by have := c2.hpos; omega : 0 < c2.len) i2))) ∨
      (IsSquare (c1.seq i1 + c2.seq (nextIdx (by have := c2.hpos; omega : 0 < c2.len) i2)) ∧
       IsSquare (c1.seq (nextIdx (by have := c1.hpos; omega : 0 < c1.len) i1) + c2.seq i2))) :
    ∃ c : IntervalCycle 1 R,
      (∀ sq : ℕ, c1.seq i1 + c1.seq (nextIdx (by have := c1.hpos; omega : 0 < c1.len) i1) ≠ sq →
        edgeCount c1 sq ≤ edgeCount c sq) ∧
      (∀ sq : ℕ, edgeCount c1 sq - 1 ≤ edgeCount c sq) ∧
      (∀ cls : ℕ,
        (∃ j : Fin c1.len, j ≠ i1 ∧ ∃ s : ℕ,
          c1.seq j + c1.seq (nextIdx (by have := c1.hpos; omega : 0 < c1.len) j) = s * s ∧
          mod5Pred cls s) →
        HasMod5Class c cls) ∧
      (∀ cls : ℕ,
        (∃ j : Fin c2.len, j ≠ i2 ∧ ∃ s : ℕ,
          c2.seq j + c2.seq (nextIdx (by have := c2.hpos; omega : 0 < c2.len) j) = s * s ∧
          mod5Pred cls s) →
        HasMod5Class c cls) := by
  rcases hcross with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
  · let c2r := reverseCycle c2
    let i2r : Fin c2r.len := revIdx c2.hpos i2
    have h12 : IsSquare (c1.seq i1 + c2r.seq (nextIdx (by have := c2r.hpos; omega : 0 < c2r.len) i2r)) := by
      rw [reverseCycle_seq_next_revIdx]; exact hxu
    have h21 : IsSquare (c1.seq (nextIdx (by have := c1.hpos; omega : 0 < c1.len) i1) + c2r.seq i2r) := by
      rw [reverseCycle_seq_revIdx]; exact hyv
    obtain ⟨c, h1, h2, h3, h4⟩ := splice_cycles_fwd hL hLR c1 c2r i1 i2r h12 h21
    refine ⟨c, h1, h2, h3, ?_⟩
    intro cls ⟨j, hne, s, hsum, hpred⟩
    apply h4 cls
    refine ⟨revIdx c2.hpos j, ?_, s, ?_, hpred⟩
    · intro heq
      exact hne (revIdx_inj c2.hpos heq)
    · rw [reverseCycle_seq_revIdx, reverseCycle_seq_next_revIdx, Nat.add_comm]
      exact hsum
  · exact splice_cycles_fwd hL hLR c1 c2 i1 i2 hxv hyu

/-! ### 5: Brahmagupta Self-Sustaining Mod-5 Merge -/

private lemma mod5Pred_disjoint {c1 c2 s : ℕ} (hc1 : c1 ≤ 2) (hc2 : c2 ≤ 2)
    (hne : c1 ≠ c2) (h1 : mod5Pred c1 s) (h2 : mod5Pred c2 s) : False := by
  unfold mod5Pred at h1 h2
  split_ifs at h1 h2 <;> omega

theorem brahmagupta_merge {L R b : ℕ}
    (hL : 33 ≤ L) (hb_odd : b % 2 = 1) (h18 : 18 * L ≤ b * b) (hR : R = b * b - L)
    (h1 : InvMod5 (L - 1))
    (c2 : IntervalCycle L R)
    (hrefl : ∀ u, L ≤ u → u ≤ R → HasEdge c2 u (b * b - u))
    (hrepl : b % 5 = 0 ∨
             ((b % 5 = 1 ∨ b % 5 = 4) ∧ HasMod5Class c2 2) ∨
             ((b % 5 = 2 ∨ b % 5 = 3) ∧ HasMod5Class c2 1)) :
    InvMod5 R := by
  rcases h1 with ⟨c1, hc1_0, hc1_1, hc1_2⟩
  have _ := hb_odd
  have hLR : L + 1 ≤ R := by omega
  have hp1 : 2 ≤ c1.len := c1.hpos
  have hp2 : 2 ≤ c2.len := c2.hpos
  -- Choose the mod-5 class `burned` to consume from `c1`, and witness `(i1, s)`
  have hpick : ∃ burned : ℕ, burned ≤ 2 ∧
      (∃ i1 : Fin c1.len, ∃ s : ℕ,
        c1.seq i1 + c1.seq (nextIdx (by omega : 0 < c1.len) i1) = s * s ∧
        mod5Pred burned s ∧
        ((4 * b - 3 * s) % 5 = 0 ∨ (4 * b + 3 * s) % 5 = 0)) ∧
      ((burned = 0 ∧ b % 5 = 0) ∨
       (burned = 2 ∧ (b % 5 = 1 ∨ b % 5 = 4) ∧ HasMod5Class c2 2) ∨
       (burned = 1 ∧ (b % 5 = 2 ∨ b % 5 = 3) ∧ HasMod5Class c2 1)) := by
    rcases hrepl with hb0 | ⟨hb14, hcls2⟩ | ⟨hb23, hcls1⟩
    · rcases hc1_0 with ⟨i1, s, hsum, hs⟩
      refine ⟨0, by omega, ⟨i1, s, hsum, hs, ?_⟩, Or.inl ⟨rfl, hb0⟩⟩
      left; simp only [↓reduceIte] at hs; omega
    · rcases hc1_2 with ⟨i1, s, hsum, hs⟩
      refine ⟨2, by omega, ⟨i1, s, hsum, hs, ?_⟩, Or.inr (Or.inl ⟨rfl, hb14, hcls2⟩)⟩
      simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte] at hs
      have hss : s * s < 2 * L := by
        have hx := c1.hmem i1
        have hy := c1.hmem (nextIdx (by omega : 0 < c1.len) i1)
        omega
      have h3s : 3 * s < b := by nlinarith only [hss, h18]
      omega
    · rcases hc1_1 with ⟨i1, s, hsum, hs⟩
      refine ⟨1, by omega, ⟨i1, s, hsum, hs, ?_⟩, Or.inr (Or.inr ⟨rfl, hb23, hcls1⟩)⟩
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] at hs
      have hss : s * s < 2 * L := by
        have hx := c1.hmem i1
        have hy := c1.hmem (nextIdx (by omega : 0 < c1.len) i1)
        omega
      have h3s : 3 * s < b := by nlinarith only [hss, h18]
      omega
  rcases hpick with ⟨burned, hburned_le, ⟨i1, s, hxy, hs_pred, hdiv5⟩, hrepl_case⟩
  let x := c1.seq i1
  let y := c1.seq (nextIdx (by omega : 0 < c1.len) i1)
  have hx_mem : 1 ≤ x ∧ x ≤ L - 1 := c1.hmem i1
  have hy_mem : 1 ≤ y ∧ y ≤ L - 1 := c1.hmem (nextIdx (by omega : 0 < c1.len) i1)
  have hss : s * s < 2 * L := by omega
  have h3s : 3 * s < b := by nlinarith only [hss, h18]
  have h4s : 4 * s < 3 * b := by omega
  -- Construct `(u, v)` with `L ≤ u ≤ R`, `u + v = b * b`, `IsSquare (x + u)`, `IsSquare (y + v)`
  have huv : ∃ u v : ℕ, L ≤ u ∧ u ≤ R ∧ u + v = b * b ∧ IsSquare (x + u) ∧ IsSquare (y + v) := by
    rcases hdiv5 with hminus | hplus
    · let p := (4 * b - 3 * s) / 5
      let q := (3 * b + 4 * s) / 5
      have hp5 : 5 * p = 4 * b - 3 * s := by omega
      have hq5 : 5 * q = 3 * b + 4 * s := by omega
      have hpq_sq : p * p + q * q = b * b + s * s := by
        have h25 : 25 * (p * p + q * q) = 25 * (b * b + s * s) := by
          have : (5 * p) * (5 * p) + (5 * q) * (5 * q) = 25 * (p * p + q * q) := by ring
          rw [← this, hp5, hq5]
          have hsub : 3 * s ≤ 4 * b := by omega
          zify [hsub]; ring
        omega
      have h5p_lo : 3 * b < 5 * p := by omega
      have h5p_hi : 5 * p ≤ 4 * b := by omega
      have h5q_lo : 3 * b ≤ 5 * q := by omega
      have hp_lo : 2 * L < p * p := by nlinarith only [h5p_lo, h18, hL]
      have hp_hi : p * p + L ≤ b * b := by nlinarith only [h5p_hi, h18]
      have hq_lo : 2 * L < q * q := by nlinarith only [h5q_lo, h18, hL]
      refine ⟨p * p - x, q * q - y, by omega, by omega, by omega,
        ⟨p, by omega⟩, ⟨q, by omega⟩⟩
    · let p := (4 * b + 3 * s) / 5
      let q := (3 * b - 4 * s) / 5
      have hp5 : 5 * p = 4 * b + 3 * s := by omega
      have hq5 : 5 * q = 3 * b - 4 * s := by omega
      have hpq_sq : p * p + q * q = b * b + s * s := by
        have h25 : 25 * (p * p + q * q) = 25 * (b * b + s * s) := by
          have : (5 * p) * (5 * p) + (5 * q) * (5 * q) = 25 * (p * p + q * q) := by ring
          rw [← this, hp5, hq5]
          have hsub : 4 * s ≤ 3 * b := by omega
          zify [hsub]; ring
        omega
      have h3q_lo : b < 3 * q := by omega
      have h5q_hi : 5 * q ≤ 3 * b := by omega
      have h5p_lo : 4 * b ≤ 5 * p := by omega
      have hq_lo : 2 * L < q * q := by nlinarith only [h3q_lo, h18, hL]
      have hq_hi : q * q + L ≤ b * b := by nlinarith only [h5q_hi, h18]
      have hp_lo : 2 * L < p * p := by nlinarith only [h5p_lo, h18, hL]
      refine ⟨q * q - x, p * p - y, by omega, by omega, by omega,
        ⟨q, by omega⟩, ⟨p, by omega⟩⟩
  rcases huv with ⟨u, v, hu_lo, hu_hi, huv_sum, hxu_sq, hyv_sq⟩
  have hedge : HasEdge c2 u v := by
    have hv_eq : v = b * b - u := by omega
    rw [hv_eq]
    exact hrefl u hu_lo hu_hi
  rcases hedge with ⟨i2, hi2_pair⟩
  have hcross :
      (IsSquare (c1.seq i1 + c2.seq i2) ∧
       IsSquare (c1.seq (nextIdx (by omega : 0 < c1.len) i1) +
                 c2.seq (nextIdx (by omega : 0 < c2.len) i2))) ∨
      (IsSquare (c1.seq i1 + c2.seq (nextIdx (by omega : 0 < c2.len) i2)) ∧
       IsSquare (c1.seq (nextIdx (by omega : 0 < c1.len) i1) + c2.seq i2)) := by
    rcases hi2_pair with ⟨hi2u, hi2v⟩ | ⟨hi2v, hi2u⟩
    · exact Or.inl ⟨by rw [hi2u]; exact hxu_sq, by rw [hi2v]; exact hyv_sq⟩
    · exact Or.inr ⟨by rw [hi2u]; exact hxu_sq, by rw [hi2v]; exact hyv_sq⟩
  obtain ⟨c, _, _, hc1_keep, hc2_keep⟩ := splice_cycles (by omega) hLR c1 c2 i1 i2 hcross
  have hi2_sum : c2.seq i2 + c2.seq (nextIdx (by omega : 0 < c2.len) i2) = b * b := by
    rcases hi2_pair with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hsurvive : ∀ cls : ℕ, cls ≤ 2 → cls ≠ burned → HasMod5Class c1 cls → HasMod5Class c cls := by
    intro cls hcls_le hne ⟨j, s', hj_sum, hj_pred⟩
    apply hc1_keep cls
    refine ⟨j, ?_, s', hj_sum, hj_pred⟩
    intro heq
    subst heq
    have hs_eq : s' = s := sq_eq_sq_nat (by omega)
    subst hs_eq
    exact mod5Pred_disjoint hcls_le hburned_le hne hj_pred hs_pred
  have hburned_ok : HasMod5Class c burned := by
    rcases hrepl_case with ⟨rfl, hb0⟩ | ⟨rfl, hb14, ⟨j, z, hz_sum, hz_pred⟩⟩ | ⟨rfl, hb23, ⟨j, z, hz_sum, hz_pred⟩⟩
    · have hu' : ∃ u' : ℕ, L ≤ u' ∧ u' ≤ R ∧ u' ≠ u ∧ u' ≠ v := by
        by_cases hL1 : L ≠ u ∧ L ≠ v
        · exact ⟨L, le_refl _, by omega, hL1.1, hL1.2⟩
        · by_cases hL2 : L + 1 ≠ u ∧ L + 1 ≠ v
          · exact ⟨L + 1, by omega, by omega, hL2.1, hL2.2⟩
          · exact ⟨L + 2, by omega, by omega, by omega, by omega⟩
      rcases hu' with ⟨u', hu'_lo, hu'_hi, hneu, hnev⟩
      obtain ⟨j, hj⟩ := hrefl u' hu'_lo hu'_hi
      apply hc2_keep 0
      refine ⟨j, ?_, b, ?_, by simp [mod5Pred, hb0]⟩
      · intro heq
        subst heq
        rcases hi2_pair with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          (rcases hj with ⟨h3, _⟩ | ⟨_, h4⟩ <;> omega)
      · rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · apply hc2_keep 2
      refine ⟨j, ?_, z, hz_sum, hz_pred⟩
      intro heq
      subst heq
      have hzb : z = b := sq_eq_sq_nat (by omega)
      subst hzb
      simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte] at hz_pred
      omega
    · apply hc2_keep 1
      refine ⟨j, ?_, z, hz_sum, hz_pred⟩
      intro heq
      subst heq
      have hzb : z = b := sq_eq_sq_nat (by omega)
      subst hzb
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] at hz_pred
      omega
  refine ⟨c, ?_, ?_, ?_⟩
  · by_cases h0 : burned = 0
    · subst h0; exact hburned_ok
    · exact hsurvive 0 (by omega) (Ne.symm h0) hc1_0
  · by_cases h1 : burned = 1
    · subst h1; exact hburned_ok
    · exact hsurvive 1 (by omega) (Ne.symm h1) hc1_1
  · by_cases h2 : burned = 2
    · subst h2; exact hburned_ok
    · exact hsurvive 2 (by omega) (Ne.symm h2) hc1_2

/-! ### 6: Small-Edge Merge -/

theorem small_edge_merge {k4 k5 k6 k7 L R z lo hi p q s : ℕ}
    (hL : 3 ≤ L) (hLR : L + 1 ≤ R)
    (hs : s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7)
    (hpq : p * p + q * q = z * z + s * s)
    (hpleq : p ≤ q)
    (hlo1 : L ≤ lo) (hhi1 : hi ≤ R) (hlohi : lo + hi = z * z)
    (hbound : lo + s * s ≤ p * p + 1)
    (h1 : InvSmall (if s = 4 then k4 + 1 else k4)
                   (if s = 5 then k5 + 1 else k5)
                   (if s = 6 then k6 + 1 else k6)
                   (if s = 7 then k7 + 1 else k7) (L - 1))
    (c2 : IntervalCycle L R)
    (hrefl : ∀ u, lo ≤ u → u ≤ hi → HasEdge c2 u (z * z - u)) :
    InvSmall k4 k5 k6 k7 R := by
  rcases h1 with ⟨c1, hc16, hc25, hc36, hc49⟩
  have _ := hhi1
  have hp1 : 2 ≤ c1.len := c1.hpos
  have hp2 : 2 ≤ c2.len := c2.hpos
  have hpos_s : 1 ≤ edgeCount c1 (s * s) := by
    rcases hs with rfl | rfl | rfl | rfl
    · change 1 ≤ edgeCount c1 16; simp only [↓reduceIte] at hc16; omega
    · change 1 ≤ edgeCount c1 25; simp only [↓reduceIte] at hc25; omega
    · change 1 ≤ edgeCount c1 36; simp only [↓reduceIte] at hc36; omega
    · change 1 ≤ edgeCount c1 49; simp only [↓reduceIte] at hc49; omega
  obtain ⟨i1, hxy⟩ := exists_of_edgeCount_pos hpos_s
  let x := c1.seq i1
  let y := c1.seq (nextIdx (by omega : 0 < c1.len) i1)
  have hx_mem : 1 ≤ x ∧ x ≤ L - 1 := c1.hmem i1
  have hy_mem : 1 ≤ y ∧ y ≤ L - 1 := c1.hmem (nextIdx (by omega : 0 < c1.len) i1)
  have hpq_le : p * p ≤ q * q := Nat.mul_le_mul hpleq hpleq
  let u := p * p - x
  let v := q * q - y
  have hu_lo : lo ≤ u := by omega
  have hu_hi : u ≤ hi := by omega
  have huv_sum : u + v = z * z := by omega
  have hv_eq : v = z * z - u := by omega
  have hedge : HasEdge c2 u v := by
    rw [hv_eq]
    exact hrefl u hu_lo hu_hi
  have hxu_sq : IsSquare (x + u) := ⟨p, by omega⟩
  have hyv_sq : IsSquare (y + v) := ⟨q, by omega⟩
  have hcross : ∃ i2 : Fin c2.len,
      (IsSquare (c1.seq i1 + c2.seq i2) ∧
       IsSquare (c1.seq (nextIdx (by omega : 0 < c1.len) i1) +
                 c2.seq (nextIdx (by omega : 0 < c2.len) i2))) ∨
      (IsSquare (c1.seq i1 + c2.seq (nextIdx (by omega : 0 < c2.len) i2)) ∧
       IsSquare (c1.seq (nextIdx (by omega : 0 < c1.len) i1) + c2.seq i2)) := by
    rcases hedge with ⟨i2, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨i2, Or.inl ⟨by rw [h1]; exact hxu_sq, by rw [h2]; exact hyv_sq⟩⟩
    · exact ⟨i2, Or.inr ⟨by rw [h2]; exact hxu_sq, by rw [h1]; exact hyv_sq⟩⟩
  rcases hcross with ⟨i2, hcr⟩
  obtain ⟨c, hkeep_ne, hkeep_sub, _, _⟩ := splice_cycles hL hLR c1 c2 i1 i2 hcr
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · rcases hs with rfl | rfl | rfl | rfl
    · simp only [↓reduceIte] at hc16; have := hkeep_sub 16; omega
    · simp only [show (5 : ℕ) ≠ 4 by decide, ↓reduceIte] at hc16
      have := hkeep_ne 16 (by omega); omega
    · simp only [show (6 : ℕ) ≠ 4 by decide, ↓reduceIte] at hc16
      have := hkeep_ne 16 (by omega); omega
    · simp only [show (7 : ℕ) ≠ 4 by decide, ↓reduceIte] at hc16
      have := hkeep_ne 16 (by omega); omega
  · rcases hs with rfl | rfl | rfl | rfl
    · simp only [show (4 : ℕ) ≠ 5 by decide, ↓reduceIte] at hc25
      have := hkeep_ne 25 (by omega); omega
    · simp only [↓reduceIte] at hc25; have := hkeep_sub 25; omega
    · simp only [show (6 : ℕ) ≠ 5 by decide, ↓reduceIte] at hc25
      have := hkeep_ne 25 (by omega); omega
    · simp only [show (7 : ℕ) ≠ 5 by decide, ↓reduceIte] at hc25
      have := hkeep_ne 25 (by omega); omega
  · rcases hs with rfl | rfl | rfl | rfl
    · simp only [show (4 : ℕ) ≠ 6 by decide, ↓reduceIte] at hc36
      have := hkeep_ne 36 (by omega); omega
    · simp only [show (5 : ℕ) ≠ 6 by decide, ↓reduceIte] at hc36
      have := hkeep_ne 36 (by omega); omega
    · simp only [↓reduceIte] at hc36; have := hkeep_sub 36; omega
    · simp only [show (7 : ℕ) ≠ 6 by decide, ↓reduceIte] at hc36
      have := hkeep_ne 36 (by omega); omega
  · rcases hs with rfl | rfl | rfl | rfl
    · simp only [show (4 : ℕ) ≠ 7 by decide, ↓reduceIte] at hc49
      have := hkeep_ne 49 (by omega); omega
    · simp only [show (5 : ℕ) ≠ 7 by decide, ↓reduceIte] at hc49
      have := hkeep_ne 49 (by omega); omega
    · simp only [show (6 : ℕ) ≠ 7 by decide, ↓reduceIte] at hc49
      have := hkeep_ne 49 (by omega); omega
    · simp only [↓reduceIte] at hc49; have := hkeep_sub 49; omega

/-! ### 7: Cycle of Two Involutions & Computable Two-Matching Checker -/

theorem cycle_of_involutions {L R : ℕ} {g1 g2 : ℕ → ℕ}
    (hLR : L + 1 ≤ R)
    (heven : (R - L + 1) % 2 = 0)
    (hg1_mem : ∀ x, L ≤ x → x ≤ R → L ≤ g1 x ∧ g1 x ≤ R)
    (hg2_mem : ∀ x, L ≤ x → x ≤ R → L ≤ g2 x ∧ g2 x ≤ R)
    (hg1_inv : ∀ x, L ≤ x → x ≤ R → g1 (g1 x) = x)
    (hg2_inv : ∀ x, L ≤ x → x ≤ R → g2 (g2 x) = x)
    (hg1_ne : ∀ x, L ≤ x → x ≤ R → g1 x ≠ x)
    (hg2_ne : ∀ x, L ≤ x → x ≤ R → g2 x ≠ x)
    (hg1_sq : ∀ x, L ≤ x → x ≤ R → IsSquare (x + g1 x))
    (hg2_sq : ∀ x, L ≤ x → x ≤ R → IsSquare (x + g2 x))
    (hperiod : (g2 ∘ g1)^[(R - L + 1) / 2] L = L)
    (hmin : ∀ k, 0 < k → k < (R - L + 1) / 2 → (g2 ∘ g1)^[k] L ≠ L) :
    ∃ c : IntervalCycle L R,
      (∀ u, L ≤ u → u ≤ R → HasEdge c u (g1 u)) ∧
      (∀ u, L ≤ u → u ≤ R → HasEdge c u (g2 u)) := by
  let half : ℕ := (R - L + 1) / 2
  let N : ℕ := R - L + 1
  have hN_eq : N = 2 * half := by omega
  have hhalf_pos : 1 ≤ half := by omega
  let f : ℕ → ℕ := g2 ∘ g1
  have hf_mem : ∀ x, L ≤ x → x ≤ R → L ≤ f x ∧ f x ≤ R := by
    intro x hlo hhi
    have h1 := hg1_mem x hlo hhi
    exact hg2_mem (g1 x) h1.1 h1.2
  have hf_iter_mem : ∀ k x, L ≤ x → x ≤ R → L ≤ f^[k] x ∧ f^[k] x ≤ R := by
    intro k
    induction k with
    | zero => intro x hlo hhi; exact ⟨hlo, hhi⟩
    | succ k ih =>
      intro x hlo hhi
      rw [Function.iterate_succ_apply']
      have hk := ih x hlo hhi
      exact hf_mem (f^[k] x) hk.1 hk.2
  have hf_inj : ∀ x y, L ≤ x → x ≤ R → L ≤ y → y ≤ R → f x = f y → x = y := by
    intro x y hx1 hx2 hy1 hy2 hxy
    have hgx := hg1_mem x hx1 hx2
    have hgy := hg1_mem y hy1 hy2
    have h1 : g1 x = g1 y := by
      have := congrArg g2 hxy
      simpa only [f, Function.comp_apply, hg2_inv _ hgx.1 hgx.2, hg2_inv _ hgy.1 hgy.2] using this
    have := congrArg g1 h1
    simpa only [hg1_inv x hx1 hx2, hg1_inv y hy1 hy2] using this
  have hf_iter_inj : ∀ k x y, L ≤ x → x ≤ R → L ≤ y → y ≤ R → f^[k] x = f^[k] y → x = y := by
    intro k
    induction k with
    | zero => intro x y _ _ _ _ h; exact h
    | succ k ih =>
      intro x y hx1 hx2 hy1 hy2 h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
      have hkx := hf_iter_mem k x hx1 hx2
      have hky := hf_iter_mem k y hy1 hy2
      exact ih x y hx1 hx2 hy1 hy2 (hf_inj _ _ hkx.1 hkx.2 hky.1 hky.2 h)
  have hdihedral_step : ∀ x, L ≤ x → x ≤ R → f (g1 (f x)) = g1 x := by
    intro x hx1 hx2
    have h1 := hg1_mem x hx1 hx2
    have h2 := hg2_mem (g1 x) h1.1 h1.2
    simp only [f, Function.comp_apply]
    rw [hg1_inv (g2 (g1 x)) h2.1 h2.2, hg2_inv (g1 x) h1.1 h1.2]
  have hdihedral : ∀ m x, L ≤ x → x ≤ R → f^[m] (g1 (f^[m] x)) = g1 x := by
    intro m
    induction m with
    | zero => intro x _ _; rfl
    | succ m ih =>
      intro x hx1 hx2
      have hm := hf_iter_mem m x hx1 hx2
      calc f^[m + 1] (g1 (f^[m + 1] x))
          = f^[m] (f (g1 (f (f^[m] x)))) := by
              rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
        _ = f^[m] (g1 (f^[m] x)) := by rw [hdihedral_step (f^[m] x) hm.1 hm.2]
        _ = g1 x := ih x hx1 hx2
  have hno_cross : ∀ k, ∀ x, L ≤ x → x ≤ R → g1 x ≠ f^[k] x := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hx1 hx2 heq
      match k with
      | 0 => exact hg1_ne x hx1 hx2 heq
      | 1 =>
        have h1 := hg1_mem x hx1 hx2
        exact hg2_ne (g1 x) h1.1 h1.2 heq.symm
      | k' + 2 =>
        have hfx := hf_mem x hx1 hx2
        have hgfx := hg1_mem (f x) hfx.1 hfx.2
        have hkfx := hf_iter_mem k' (f x) hfx.1 hfx.2
        have hstep : f (g1 (f x)) = f (f^[k'] (f x)) := by
          rw [hdihedral_step x hx1 hx2, heq]
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply]
        have hcancel := hf_inj (g1 (f x)) (f^[k'] (f x)) hgfx.1 hgfx.2 hkfx.1 hkfx.2 hstep
        exact ih k' (by omega) (f x) hfx.1 hfx.2 hcancel
  let sseq : Fin N → ℕ := fun i =>
    if i.val % 2 = 0 then f^[i.val / 2] L else g1 (f^[i.val / 2] L)
  have hL_mem : L ≤ L ∧ L ≤ R := ⟨le_refl _, by omega⟩
  have hmem : ∀ i : Fin N, L ≤ sseq i ∧ sseq i ≤ R := by
    intro i
    simp only [sseq]
    have hk := hf_iter_mem (i.val / 2) L hL_mem.1 hL_mem.2
    split_ifs
    · exact hk
    · exact hg1_mem _ hk.1 hk.2
  have hsame_half : ∀ a b, a < half → b < half → f^[a] L = f^[b] L → a = b := by
    intro a b ha hb hab
    by_cases hle : a ≤ b
    · have hd : b = a + (b - a) := by omega
      rw [hd, Function.iterate_add_apply] at hab
      have hbd := hf_iter_mem (b - a) L hL_mem.1 hL_mem.2
      have heq := hf_iter_inj a L (f^[b - a] L) hL_mem.1 hL_mem.2 hbd.1 hbd.2 hab
      by_cases h0 : b - a = 0
      · omega
      · exfalso
        exact hmin (b - a) (by omega) (by omega) heq.symm
    · have hd : a = b + (a - b) := by omega
      rw [hd, Function.iterate_add_apply] at hab
      have had := hf_iter_mem (a - b) L hL_mem.1 hL_mem.2
      have heq := hf_iter_inj b (f^[a - b] L) L had.1 had.2 hL_mem.1 hL_mem.2 hab
      by_cases h0 : a - b = 0
      · omega
      · exfalso
        exact hmin (a - b) (by omega) (by omega) heq
  have hinj : Function.Injective sseq := by
    intro i j hij
    simp only [sseq] at hij
    split_ifs at hij with hi hj hj
    · have hdiv := hsame_half (i.val / 2) (j.val / 2) (by omega) (by omega) hij
      exact Fin.ext (by omega)
    · exfalso
      have h1 := congrArg (f^[j.val / 2]) hij.symm
      rw [hdihedral (j.val / 2) L hL_mem.1 hL_mem.2, ← Function.iterate_add_apply] at h1
      exact hno_cross (j.val / 2 + i.val / 2) L hL_mem.1 hL_mem.2 h1
    · exfalso
      have h1 := congrArg (f^[i.val / 2]) hij
      rw [hdihedral (i.val / 2) L hL_mem.1 hL_mem.2, ← Function.iterate_add_apply] at h1
      exact hno_cross (i.val / 2 + j.val / 2) L hL_mem.1 hL_mem.2 h1
    · have hki := hf_iter_mem (i.val / 2) L hL_mem.1 hL_mem.2
      have hkj := hf_iter_mem (j.val / 2) L hL_mem.1 hL_mem.2
      have h1 : f^[i.val / 2] L = f^[j.val / 2] L := by
        have := congrArg g1 hij
        simpa only [hg1_inv _ hki.1 hki.2, hg1_inv _ hkj.1 hkj.2] using this
      have hdiv := hsame_half (i.val / 2) (j.val / 2) (by omega) (by omega) h1
      exact Fin.ext (by omega)
  have hadj : ∀ i : Fin N, IsSquare (sseq i + sseq (nextIdx (by omega : 0 < N) i)) := by
    intro i
    by_cases hev : i.val % 2 = 0
    · have hlt : i.val + 1 < N := by omega
      have hnext : (nextIdx (by omega : 0 < N) i).val = i.val + 1 := by
        simp only [nextIdx]; exact Nat.mod_eq_of_lt hlt
      have hs1 : sseq i = f^[i.val / 2] L := by simp only [sseq, hev, ↓reduceIte]
      have hs2 : sseq (nextIdx (by omega : 0 < N) i) = g1 (f^[i.val / 2] L) := by
        simp only [sseq, hnext, show (i.val + 1) % 2 ≠ 0 by omega, ↓reduceIte,
          show (i.val + 1) / 2 = i.val / 2 by omega]
      rw [hs1, hs2]
      have hk := hf_iter_mem (i.val / 2) L hL_mem.1 hL_mem.2
      exact hg1_sq _ hk.1 hk.2
    · have hs1 : sseq i = g1 (f^[i.val / 2] L) := by simp only [sseq, hev, ↓reduceIte]
      have hk := hf_iter_mem (i.val / 2) L hL_mem.1 hL_mem.2
      have hgk := hg1_mem _ hk.1 hk.2
      by_cases hlt : i.val + 1 < N
      · have hnext : (nextIdx (by omega : 0 < N) i).val = i.val + 1 := by
          simp only [nextIdx]; exact Nat.mod_eq_of_lt hlt
        have hs2 : sseq (nextIdx (by omega : 0 < N) i) = g2 (g1 (f^[i.val / 2] L)) := by
          simp only [sseq, hnext, show (i.val + 1) % 2 = 0 by omega, ↓reduceIte,
            show (i.val + 1) / 2 = i.val / 2 + 1 by omega]
          rw [Function.iterate_succ_apply']
          rfl
        rw [hs1, hs2]
        exact hg2_sq _ hgk.1 hgk.2
      · have hnext : (nextIdx (by omega : 0 < N) i).val = 0 := by
          simp only [nextIdx]
          have heq : i.val + 1 = N := by omega
          rw [heq, Nat.mod_self]
        have hdiv : i.val / 2 + 1 = half := by omega
        have hs2 : sseq (nextIdx (by omega : 0 < N) i) = g2 (g1 (f^[i.val / 2] L)) := by
          simp only [sseq, hnext, Nat.zero_mod, ↓reduceIte, Nat.zero_div, Function.iterate_zero_apply]
          have : g2 (g1 (f^[i.val / 2] L)) = f^[i.val / 2 + 1] L := by
            rw [Function.iterate_succ_apply']; rfl
          rw [this, hdiv]
          exact hperiod.symm
        rw [hs1, hs2]
        exact hg2_sq _ hgk.1 hgk.2
  let c : IntervalCycle L R :=
    { len := N
      hlen := rfl
      hpos := by omega
      seq := sseq
      hinj := hinj
      hmem := hmem
      hadj := hadj }
  have hsurj : ∀ u, L ≤ u → u ≤ R → ∃ i : Fin N, sseq i = u := by
    let φ : Fin N → Fin N := fun i => ⟨sseq i - L, by have := hmem i; omega⟩
    have hφ_inj : Function.Injective φ := by
      intro a b hab
      have hv := congrArg Fin.val hab
      simp only [φ] at hv
      have ha := hmem a
      have hb := hmem b
      exact hinj (by omega)
    have hφ_surj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφ_inj
    intro u hlo hhi
    obtain ⟨i, hi⟩ := hφ_surj ⟨u - L, by omega⟩
    have hv := congrArg Fin.val hi
    simp only [φ] at hv
    have hm := hmem i
    exact ⟨i, by omega⟩
  refine ⟨c, ?_, ?_⟩
  · intro u hlo hhi
    obtain ⟨i, hi⟩ := hsurj u hlo hhi
    by_cases hev : i.val % 2 = 0
    · refine ⟨i, Or.inl ⟨hi, ?_⟩⟩
      have hlt : i.val + 1 < N := by omega
      have hnext : (nextIdx (by omega : 0 < N) i).val = i.val + 1 := by
        simp only [nextIdx]; exact Nat.mod_eq_of_lt hlt
      change sseq (nextIdx (by omega : 0 < N) i) = g1 u
      rw [← hi]
      simp only [sseq, hev, hnext, ↓reduceIte,
        show (i.val + 1) % 2 ≠ 0 by omega, show (i.val + 1) / 2 = i.val / 2 by omega]
    · let j : Fin N := ⟨i.val - 1, by omega⟩
      have hnext : nextIdx (by omega : 0 < N) j = i := by
        apply Fin.ext
        simp only [nextIdx, j]
        have hlt : i.val - 1 + 1 < N := by omega
        rw [Nat.mod_eq_of_lt hlt]; omega
      refine ⟨j, Or.inr ⟨?_, by rw [hnext]; exact hi⟩⟩
      change sseq j = g1 u
      rw [← hi]
      have hk := hf_iter_mem (i.val / 2) L hL_mem.1 hL_mem.2
      simp only [sseq, j, hev, ↓reduceIte,
        show (i.val - 1) % 2 = 0 by omega, show (i.val - 1) / 2 = i.val / 2 by omega]
      exact (hg1_inv _ hk.1 hk.2).symm
  · intro u hlo hhi
    obtain ⟨i, hi⟩ := hsurj u hlo hhi
    by_cases hev : i.val % 2 = 0
    · by_cases hi0 : i.val = 0
      · let j : Fin N := ⟨N - 1, by omega⟩
        have hnext : nextIdx (by omega : 0 < N) j = i := by
          apply Fin.ext
          simp only [nextIdx, j]
          have heq : N - 1 + 1 = N := by omega
          rw [heq, Nat.mod_self]; omega
        refine ⟨j, Or.inr ⟨?_, by rw [hnext]; exact hi⟩⟩
        change sseq j = g2 u
        have hu_eq : u = L := by
          rw [← hi]; simp only [sseq, hi0, Nat.zero_mod, ↓reduceIte, Nat.zero_div, Function.iterate_zero_apply]
        have hdiv : (N - 1) / 2 + 1 = half := by omega
        have hk := hf_iter_mem ((N - 1) / 2) L hL_mem.1 hL_mem.2
        have hgk := hg1_mem _ hk.1 hk.2
        have hstep : g2 (g1 (f^[(N - 1) / 2] L)) = L := by
          have : g2 (g1 (f^[(N - 1) / 2] L)) = f^[(N - 1) / 2 + 1] L := by
            rw [Function.iterate_succ_apply']; rfl
          rw [this, hdiv]; exact hperiod
        have hg2L : g2 L = g1 (f^[(N - 1) / 2] L) :=
          calc g2 L = g2 (g2 (g1 (f^[(N - 1) / 2] L))) := congrArg g2 hstep.symm
            _ = g1 (f^[(N - 1) / 2] L) := hg2_inv _ hgk.1 hgk.2
        simp only [sseq, j, show (N - 1) % 2 ≠ 0 by omega, ↓reduceIte, hu_eq, hg2L]
      · let j : Fin N := ⟨i.val - 1, by omega⟩
        have hnext : nextIdx (by omega : 0 < N) j = i := by
          apply Fin.ext
          simp only [nextIdx, j]
          have hlt : i.val - 1 + 1 < N := by omega
          rw [Nat.mod_eq_of_lt hlt]; omega
        refine ⟨j, Or.inr ⟨?_, by rw [hnext]; exact hi⟩⟩
        change sseq j = g2 u
        have hdiv : (i.val - 1) / 2 + 1 = i.val / 2 := by omega
        have hk := hf_iter_mem ((i.val - 1) / 2) L hL_mem.1 hL_mem.2
        have hgk := hg1_mem _ hk.1 hk.2
        have hu_eq : u = g2 (g1 (f^[(i.val - 1) / 2] L)) := by
          rw [← hi]
          simp only [sseq, hev, ↓reduceIte]
          rw [← hdiv, Function.iterate_succ_apply']; rfl
        simp only [sseq, j, show (i.val - 1) % 2 ≠ 0 by omega, ↓reduceIte, hu_eq]
        rw [hg2_inv _ hgk.1 hgk.2]
    · refine ⟨i, Or.inl ⟨hi, ?_⟩⟩
      change sseq (nextIdx (by omega : 0 < N) i) = g2 u
      have hu_eq : u = g1 (f^[i.val / 2] L) := by
        rw [← hi]; simp only [sseq, hev, ↓reduceIte]
      rw [hu_eq]
      by_cases hlt : i.val + 1 < N
      · have hnext : (nextIdx (by omega : 0 < N) i).val = i.val + 1 := by
          simp only [nextIdx]; exact Nat.mod_eq_of_lt hlt
        simp only [sseq, hnext, show (i.val + 1) % 2 = 0 by omega, ↓reduceIte,
          show (i.val + 1) / 2 = i.val / 2 + 1 by omega]
        rw [Function.iterate_succ_apply']; rfl
      · have hnext : (nextIdx (by omega : 0 < N) i).val = 0 := by
          simp only [nextIdx]
          have heq : i.val + 1 = N := by omega
          rw [heq, Nat.mod_self]
        have hdiv : i.val / 2 + 1 = half := by omega
        simp only [sseq, hnext, Nat.zero_mod, ↓reduceIte, Nat.zero_div, Function.iterate_zero_apply]
        have : g2 (g1 (f^[i.val / 2] L)) = f^[i.val / 2 + 1] L := by
          rw [Function.iterate_succ_apply']; rfl
        rw [this, hdiv]
        exact hperiod.symm

/-- Piecewise reflection matching evaluator using square roots `(lo, hi, r)` with sum `r * r`. -/
def evalRootMatching : List (ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], x => x
  | (lo, hi, r) :: rest, x =>
      if lo ≤ x ∧ x ≤ hi then r * r - x else evalRootMatching rest x

/-- Check that `m` partitions `[cur, R]` contiguously from left to right. -/
def checkCovers (cur R : ℕ) : List (ℕ × ℕ × ℕ) → Bool
  | [] => false
  | [(lo, hi, _)] => (lo == cur) && Nat.ble lo hi && (hi == R)
  | (lo, hi, _) :: rest =>
      (lo == cur) && Nat.ble lo hi && Nat.blt hi R && checkCovers (hi + 1) R rest

/-- Check that a single piece `(lo, hi, r)` is either an odd-root self-reflection
    or paired with a disjoint partner piece in `m` of the same root `r`. -/
def checkTriple (m : List (ℕ × ℕ × ℕ)) (t : ℕ × ℕ × ℕ) : Bool :=
  let (lo, hi, r) := t
  ((lo + hi == r * r) && (r % 2 == 1)) ||
  m.any (fun (lo', hi', r') =>
    (r' == r) && (lo + hi' == r * r) && (hi + lo' == r * r) && (Nat.blt hi lo' || Nat.blt hi' lo))

/-- Check that `m` defines a fixed-point-free square-sum involution on `[L, R]`. -/
def checkRootMatching (L R : ℕ) (m : List (ℕ × ℕ × ℕ)) : Bool :=
  checkCovers L R m && m.all (checkTriple m)

/-- Fast structurally recursive walk checker for `(evalRootMatching m2 ∘ evalRootMatching m1)`. -/
def checkWalkGo (L steps : ℕ) (m1 m2 : List (ℕ × ℕ × ℕ)) : ℕ → ℕ → Bool
  | 0, cur => cur == L
  | k + 1, cur =>
      if Nat.blt (k + 1) steps && (cur == L) then false
      else checkWalkGo L steps m1 m2 k (evalRootMatching m2 (evalRootMatching m1 cur))

/-- Check that `L` has exact period `steps` under `evalRootMatching m2 ∘ evalRootMatching m1`. -/
def checkWalk (L steps : ℕ) (m1 m2 : List (ℕ × ℕ × ℕ)) : Bool :=
  checkWalkGo L steps m1 m2 steps L

/-- Full computable certificate checker for two matchings forming a Hamiltonian cycle on `[L, R]`. -/
def checkTwoMatchings (L R : ℕ) (m1 m2 : List (ℕ × ℕ × ℕ)) : Bool :=
  Nat.ble (L + 1) R &&
  ((R - L + 1) % 2 == 0) &&
  checkRootMatching L R m1 &&
  checkRootMatching L R m2 &&
  checkWalk L ((R - L + 1) / 2) m1 m2

private lemma checkCovers_bounds {cur R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hc : checkCovers cur R m = true) :
    ∀ lo hi r, (lo, hi, r) ∈ m → cur ≤ lo ∧ lo ≤ hi ∧ hi ≤ R := by
  induction m generalizing cur with
  | nil => simp [checkCovers] at hc
  | cons hd tl ih =>
    rcases hd with ⟨lo0, hi0, r0⟩
    cases tl with
    | nil =>
      simp only [checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hc
      intro lo hi r hmem
      simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      omega
    | cons hd2 tl2 =>
      simp only [checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hc
      intro lo hi r hmem
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem_tl
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        omega
      · have htl := ih hc.2 lo hi r hmem_tl
        omega

private lemma checkCovers_exists {cur R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hc : checkCovers cur R m = true) {x : ℕ} (hlo : cur ≤ x) (hhi : x ≤ R) :
    ∃ lo hi r, (lo, hi, r) ∈ m ∧ lo ≤ x ∧ x ≤ hi := by
  induction m generalizing cur with
  | nil => simp [checkCovers] at hc
  | cons hd tl ih =>
    rcases hd with ⟨lo0, hi0, r0⟩
    cases tl with
    | nil =>
      simp only [checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hc
      exact ⟨lo0, hi0, r0, List.mem_singleton_self _, by omega, by omega⟩
    | cons hd2 tl2 =>
      simp only [checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hc
      by_cases hx : x ≤ hi0
      · exact ⟨lo0, hi0, r0, List.mem_cons_self, by omega, hx⟩
      · obtain ⟨lo, hi, r, hmem, h1, h2⟩ := ih hc.2 (by omega)
        exact ⟨lo, hi, r, List.mem_cons_of_mem _ hmem, h1, h2⟩

private lemma checkCovers_eval_mem {cur R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hc : checkCovers cur R m = true) {lo hi r x : ℕ}
    (hmem : (lo, hi, r) ∈ m) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    evalRootMatching m x = r * r - x := by
  induction m generalizing cur with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨lo0, hi0, r0⟩
    cases tl with
    | nil =>
      simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      simp only [evalRootMatching, hlo, hhi, and_self, ↓reduceIte]
    | cons hd2 tl2 =>
      simp only [checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hc
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem_tl
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        simp only [evalRootMatching, hlo, hhi, and_self, ↓reduceIte]
      · have hb := checkCovers_bounds hc.2 lo hi r hmem_tl
        have hnot : ¬ (lo0 ≤ x ∧ x ≤ hi0) := by omega
        simp only [evalRootMatching, hnot, ↓reduceIte]
        exact ih hc.2 hmem_tl

private lemma checkRootMatching_sound {L R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hc : checkRootMatching L R m = true) :
    (∀ x, L ≤ x → x ≤ R → L ≤ evalRootMatching m x ∧ evalRootMatching m x ≤ R) ∧
    (∀ x, L ≤ x → x ≤ R → evalRootMatching m (evalRootMatching m x) = x) ∧
    (∀ x, L ≤ x → x ≤ R → evalRootMatching m x ≠ x) ∧
    (∀ x, L ≤ x → x ≤ R → IsSquare (x + evalRootMatching m x)) := by
  simp only [checkRootMatching, Bool.and_eq_true, List.all_eq_true] at hc
  rcases hc with ⟨hcov, hall⟩
  have hpoint : ∀ x, L ≤ x → x ≤ R →
      (L ≤ evalRootMatching m x ∧ evalRootMatching m x ≤ R) ∧
      evalRootMatching m (evalRootMatching m x) = x ∧
      evalRootMatching m x ≠ x ∧
      IsSquare (x + evalRootMatching m x) := by
    intro x hx1 hx2
    obtain ⟨lo, hi, r, hmem, hlo, hhi⟩ := checkCovers_exists hcov hx1 hx2
    have hb := checkCovers_bounds hcov lo hi r hmem
    have heval : evalRootMatching m x = r * r - x := checkCovers_eval_mem hcov hmem hlo hhi
    have ht := hall (lo, hi, r) hmem
    simp only [checkTriple, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      List.any_eq_true, Nat.blt_eq] at ht
    rcases ht with ⟨hsum, hodd⟩ | ⟨⟨lo', hi', r'⟩, hmem', ⟨⟨⟨hr_eq, h1⟩, h2⟩, hdisj⟩⟩
    · have hy_lo : lo ≤ r * r - x := by omega
      have hy_hi : r * r - x ≤ hi := by omega
      have heval2 : evalRootMatching m (r * r - x) = r * r - (r * r - x) :=
        checkCovers_eval_mem hcov hmem hy_lo hy_hi
      rw [heval]
      refine ⟨⟨by omega, by omega⟩, by rw [heval2]; omega, ?_, ⟨r, by omega⟩⟩
      intro heq
      have h2x : 2 * x = r * r := by omega
      have hmod : (r * r) % 2 = 1 := by rw [Nat.mul_mod, hodd]
      omega
    · dsimp only at hr_eq h1 h2 hdisj
      subst hr_eq
      have hb' := checkCovers_bounds hcov lo' hi' r' hmem'
      have hy_lo : lo' ≤ r' * r' - x := by omega
      have hy_hi : r' * r' - x ≤ hi' := by omega
      have heval2 : evalRootMatching m (r' * r' - x) = r' * r' - (r' * r' - x) :=
        checkCovers_eval_mem hcov hmem' hy_lo hy_hi
      rw [heval]
      refine ⟨⟨by omega, by omega⟩, by rw [heval2]; omega, by omega, ⟨r', by omega⟩⟩
  exact ⟨fun x h1 h2 => (hpoint x h1 h2).1,
         fun x h1 h2 => (hpoint x h1 h2).2.1,
         fun x h1 h2 => (hpoint x h1 h2).2.2.1,
         fun x h1 h2 => (hpoint x h1 h2).2.2.2⟩

private lemma checkWalkGo_sound {L steps : ℕ} {m1 m2 : List (ℕ × ℕ × ℕ)} :
    ∀ k cur : ℕ, checkWalkGo L steps m1 m2 k cur = true →
      (evalRootMatching m2 ∘ evalRootMatching m1)^[k] cur = L ∧
      (∀ j, j < k → k - j < steps → (evalRootMatching m2 ∘ evalRootMatching m1)^[j] cur ≠ L) := by
  intro k
  induction k with
  | zero =>
    intro cur h
    simp only [checkWalkGo, beq_iff_eq] at h
    exact ⟨h, fun j hj => by omega⟩
  | succ k ih =>
    intro cur h
    simp only [checkWalkGo] at h
    by_cases hbad : (Nat.blt (k + 1) steps && (cur == L)) = true
    · rw [hbad] at h; simp at h
    · simp only [Bool.not_eq_true] at hbad
      rw [hbad] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hper, hmin⟩ := ih (evalRootMatching m2 (evalRootMatching m1 cur)) h
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply]; exact hper
      · intro j hj hdiff
        cases j with
        | zero =>
          simp only [Function.iterate_zero_apply]
          intro heq
          have htrue : (Nat.blt (k + 1) steps && (cur == L)) = true := by
            simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq]
            exact ⟨by omega, heq⟩
          rw [htrue] at hbad; cases hbad
        | succ j' =>
          rw [Function.iterate_succ_apply]
          exact hmin j' (by omega) (by omega)

theorem cycle_of_two_matchings_both (L R : ℕ) (m1 m2 : List (ℕ × ℕ × ℕ))
    (hcheck : checkTwoMatchings L R m1 m2 = true) :
    ∃ c : IntervalCycle L R,
      (∀ u, L ≤ u → u ≤ R → HasEdge c u (evalRootMatching m1 u)) ∧
      (∀ u, L ≤ u → u ≤ R → HasEdge c u (evalRootMatching m2 u)) := by
  simp only [checkTwoMatchings, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hLR, heven⟩, hm1⟩, hm2⟩, hwalk⟩
  obtain ⟨hg1_mem, hg1_inv, hg1_ne, hg1_sq⟩ := checkRootMatching_sound hm1
  obtain ⟨hg2_mem, hg2_inv, hg2_ne, hg2_sq⟩ := checkRootMatching_sound hm2
  obtain ⟨hper, hmin⟩ := checkWalkGo_sound ((R - L + 1) / 2) L hwalk
  exact cycle_of_involutions hLR heven
    hg1_mem hg2_mem hg1_inv hg2_inv hg1_ne hg2_ne hg1_sq hg2_sq
    hper (fun k hk1 hk2 => hmin k hk2 (by omega))

theorem cycle_of_two_matchings (L R : ℕ) (m1 m2 : List (ℕ × ℕ × ℕ))
    (hcheck : checkTwoMatchings L R m1 m2 = true) :
    ∃ c : IntervalCycle L R,
      ∀ u, L ≤ u → u ≤ R → HasEdge c u (evalRootMatching m1 u) := by
  obtain ⟨c, h1, _⟩ := cycle_of_two_matchings_both L R m1 m2 hcheck
  exact ⟨c, h1⟩

/-! ### Self-test: Instant `by decide` verification on `[1, 32]` -/

private theorem test_cycle_1_32 :
    ∃ c : IntervalCycle 1 32,
      ∀ u, 1 ≤ u → u ≤ 32 →
        HasEdge c u (evalRootMatching
          [(1, 1, 3), (2, 3, 4), (4, 6, 6), (7, 7, 5), (8, 8, 3),
           (9, 10, 5), (11, 12, 6), (13, 14, 4), (15, 16, 5), (17, 17, 6),
           (18, 18, 5), (19, 19, 6), (20, 23, 7), (24, 25, 6), (26, 29, 7), (30, 32, 6)] u) :=
  cycle_of_two_matchings 1 32
    [(1, 1, 3), (2, 3, 4), (4, 6, 6), (7, 7, 5), (8, 8, 3),
     (9, 10, 5), (11, 12, 6), (13, 14, 4), (15, 16, 5), (17, 17, 6),
     (18, 18, 5), (19, 19, 6), (20, 23, 7), (24, 25, 6), (26, 29, 7), (30, 32, 6)]
    [(1, 1, 4), (2, 2, 5), (3, 3, 3), (4, 4, 5), (5, 5, 4),
     (6, 6, 3), (7, 10, 6), (11, 11, 4), (12, 13, 5), (14, 14, 6),
     (15, 15, 4), (16, 16, 6), (17, 19, 7), (20, 20, 6), (21, 21, 5),
     (22, 22, 6), (23, 23, 5), (24, 25, 7), (26, 29, 6), (30, 32, 7)]
    (by decide)

end MSE2637546.S1

namespace MSE2637546.S2

open MSE2637546

/-! ## Part 1: Master Involution Single-Cycle Theorem -/

lemma isUnit_intCast_zmod_of_coprime {D : ℕ} {z : ℤ}
    (hcop : Nat.Coprime D z.natAbs) : IsUnit (z : ZMod D) := by
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz, Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime z.natAbs D).mpr hcop.symm
  · rw [hz, Int.cast_neg, Int.cast_natCast]
    exact ((ZMod.isUnit_iff_coprime z.natAbs D).mpr hcop.symm).neg

/-- Master Contraction Single-Cycle Theorem for two fixed-point-free square-sum involutions
    on `[L, R]` with a contracted core `B` of cardinality `2 * D`. -/
theorem master_involution_cycle
    {L R D : ℕ} (hLR : 2 ≤ R - L + 1) (hD : 1 ≤ D)
    {m1 m2 : ℕ → ℕ}
    (hm1_mem : ∀ x, L ≤ x → x ≤ R → L ≤ m1 x ∧ m1 x ≤ R)
    (hm1_inv : ∀ x, L ≤ x → x ≤ R → m1 (m1 x) = x)
    (hm1_fpf : ∀ x, L ≤ x → x ≤ R → m1 x ≠ x)
    (hm1_sq : ∀ x, L ≤ x → x ≤ R → IsSquare (x + m1 x))
    (hm2_mem : ∀ x, L ≤ x → x ≤ R → L ≤ m2 x ∧ m2 x ≤ R)
    (hm2_inv : ∀ x, L ≤ x → x ≤ R → m2 (m2 x) = x)
    (hm2_fpf : ∀ x, L ≤ x → x ≤ R → m2 x ≠ x)
    (hm2_sq : ∀ x, L ≤ x → x ≤ R → IsSquare (x + m2 x))
    (B : ℕ → Prop) [DecidablePred B]
    (hB_card : ((Finset.Icc L R).filter B).card = 2 * D)
    (hB_m2 : ∀ x, L ≤ x → x ≤ R → B x → B (m2 x))
    (S : ZMod D) (hS : IsUnit S)
    (hmod_out : ∀ x, L ≤ x → x ≤ R → ¬ B (m1 x) →
      ((m2 (m1 x) : ℕ) : ZMod D) = (x : ZMod D))
    (hmod_in : ∀ x, L ≤ x → x ≤ R → B (m1 x) →
      ((m2 (m1 x) : ℕ) : ZMod D) = (x : ZMod D) + S)
    (hmono : (∀ x, L ≤ x → x ≤ R → ¬ B (m1 x) → m2 (m1 x) < x) ∨
             (∀ x, L ≤ x → x ≤ R → ¬ B (m1 x) → x < m2 (m1 x))) :
    ∃ c : IntervalCycle L R,
      ∀ u, L ≤ u → u ≤ R → HasEdge c u (m1 u) ∧ HasEdge c u (m2 u) := by
  classical
  have : NeZero D := ⟨by omega⟩
  let V : Finset ℕ := Finset.Icc L R
  let f : ℕ → ℕ := fun x => m2 (m1 x)
  let g : ℕ → ℕ := fun x => m1 (m2 x)
  let Bset : Finset ℕ := V.filter B
  let A : Finset ℕ := V.filter (fun x => B (m1 x))
  have hmemV : ∀ {x}, x ∈ V ↔ L ≤ x ∧ x ≤ R := fun {x} => Finset.mem_Icc
  have hm1V : ∀ {x}, x ∈ V → m1 x ∈ V := fun hx =>
    hmemV.mpr (hm1_mem _ (hmemV.mp hx).1 (hmemV.mp hx).2)
  have hm2V : ∀ {x}, x ∈ V → m2 x ∈ V := fun hx =>
    hmemV.mpr (hm2_mem _ (hmemV.mp hx).1 (hmemV.mp hx).2)
  have hfV : ∀ {x}, x ∈ V → f x ∈ V := fun hx => hm2V (hm1V hx)
  have hgV : ∀ {x}, x ∈ V → g x ∈ V := fun hx => hm1V (hm2V hx)
  have hf_iterV : ∀ {x}, x ∈ V → ∀ k, f^[k] x ∈ V := by
    intro x hx k
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hfV ih
  have hg_iterV : ∀ {x}, x ∈ V → ∀ k, g^[k] x ∈ V := by
    intro x hx k
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hgV ih
  have hgf : ∀ {x}, x ∈ V → g (f x) = x := by
    intro x hx
    have h1 := hm1V hx
    change m1 (m2 (m2 (m1 x))) = x
    rw [hm2_inv _ (hmemV.mp h1).1 (hmemV.mp h1).2]
    exact hm1_inv _ (hmemV.mp hx).1 (hmemV.mp hx).2
  have hfg : ∀ {x}, x ∈ V → f (g x) = x := by
    intro x hx
    have h2 := hm2V hx
    change m2 (m1 (m1 (m2 x))) = x
    rw [hm1_inv _ (hmemV.mp h2).1 (hmemV.mp h2).2]
    exact hm2_inv _ (hmemV.mp hx).1 (hmemV.mp hx).2
  have hg_iter_f_iter : ∀ {x}, x ∈ V → ∀ k, g^[k] (f^[k] x) = x := by
    intro x hx k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
      rw [hgf (hf_iterV hx k)]
      exact ih
  have hf_inj : ∀ {x y}, x ∈ V → y ∈ V → f x = f y → x = y := by
    intro x y hx hy h
    rw [← hgf hx, ← hgf hy, h]
  have hf_iter_inj : ∀ {x y}, x ∈ V → y ∈ V → ∀ k, f^[k] x = f^[k] y → x = y := by
    intro x y hx hy k h
    rw [← hg_iter_f_iter hx k, ← hg_iter_f_iter hy k, h]
  -- Step 1: A.card = 2 * D
  have hA_card : A.card = 2 * D := by
    have hbij : A.card = Bset.card := by
      apply Finset.card_bij (fun x _ => m1 x)
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hm1V hx.1, hx.2⟩
      · intro x1 hx1 x2 hx2 hEq
        rw [Finset.mem_filter] at hx1 hx2
        have := congrArg m1 hEq
        rw [hm1_inv _ (hmemV.mp hx1.1).1 (hmemV.mp hx1.1).2,
            hm1_inv _ (hmemV.mp hx2.1).1 (hmemV.mp hx2.1).2] at this
        exact this
      · intro y hy
        rw [Finset.mem_filter] at hy
        refine ⟨m1 y, ?_, hm1_inv _ (hmemV.mp hy.1).1 (hmemV.mp hy.1).2⟩
        rw [Finset.mem_filter]
        refine ⟨hm1V hy.1, ?_⟩
        rw [hm1_inv _ (hmemV.mp hy.1).1 (hmemV.mp hy.1).2]
        exact hy.2
    rw [hbij]
    exact hB_card
  -- Step 2: Every x ∈ V hits A under forward iteration of f
  have hhit : ∀ x, x ∈ V → ∃ k : ℕ, f^[k] x ∈ A := by
    intro x hx
    by_contra hno
    push Not at hno
    have hnotB : ∀ k, ¬ B (m1 (f^[k] x)) := by
      intro k hB
      exact hno k (Finset.mem_filter.mpr ⟨hf_iterV hx k, hB⟩)
    rcases hmono with hdec | hinc
    · have hle : ∀ k, f^[k] x + k ≤ x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hfk := hf_iterV hx k
          have hlt : f (f^[k] x) < f^[k] x :=
            hdec _ (hmemV.mp hfk).1 (hmemV.mp hfk).2 (hnotB k)
          rw [Function.iterate_succ_apply']
          omega
      have := hle (x + 1)
      omega
    · have hge : ∀ k, x + k ≤ f^[k] x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hfk := hf_iterV hx k
          have hlt : f^[k] x < f (f^[k] x) :=
            hinc _ (hmemV.mp hfk).1 (hmemV.mp hfk).2 (hnotB k)
          rw [Function.iterate_succ_apply']
          omega
      have h1 := hge (R + 1)
      have h2 := (hmemV.mp (hf_iterV hx (R + 1))).2
      omega
  -- Step 3: First-return map F on A
  have hret : ∀ x, x ∈ A → ∃ k : ℕ, f^[k + 1] x ∈ A := by
    intro x hx
    have hxV : x ∈ V := (Finset.mem_filter.mp hx).1
    obtain ⟨k, hk⟩ := hhit (f x) (hfV hxV)
    refine ⟨k, ?_⟩
    rw [Function.iterate_succ_apply]
    exact hk
  let retStep : ℕ → ℕ := fun x =>
    if hx : x ∈ A then Nat.find (hret x hx) + 1 else 0
  let F : ℕ → ℕ := fun x => f^[retStep x] x
  have hF_mem : ∀ {x}, x ∈ A → F x ∈ A := by
    intro x hx
    change f^[retStep x] x ∈ A
    simp only [retStep, dif_pos hx]
    exact Nat.find_spec (hret x hx)
  have hF_mod : ∀ {x}, x ∈ A → (F x : ZMod D) = (x : ZMod D) + S := by
    intro x hx
    have hxV : x ∈ V := (Finset.mem_filter.mp hx).1
    have hxB : B (m1 x) := (Finset.mem_filter.mp hx).2
    let r := Nat.find (hret x hx)
    have hstep : ∀ j, j ≤ r → (f^[j + 1] x : ZMod D) = (x : ZMod D) + S := by
      intro j
      induction j with
      | zero =>
        intro _
        simpa [Function.iterate_one] using hmod_in x (hmemV.mp hxV).1 (hmemV.mp hxV).2 hxB
      | succ j ih =>
        intro hj
        have hlt : j < r := by omega
        have hnotA : f^[j + 1] x ∉ A := Nat.find_min (hret x hx) hlt
        have hfjV : f^[j + 1] x ∈ V := hf_iterV hxV (j + 1)
        have hnotB : ¬ B (m1 (f^[j + 1] x)) := by
          intro hB
          exact hnotA (Finset.mem_filter.mpr ⟨hfjV, hB⟩)
        have hout := hmod_out _ (hmemV.mp hfjV).1 (hmemV.mp hfjV).2 hnotB
        change (f (f^[j + 1] x) : ZMod D) = (f^[j + 1] x : ZMod D) at hout
        rw [show f^[j + 1 + 1] x = f (f^[j + 1] x) from Function.iterate_succ_apply' f (j + 1) x]
        rw [hout, ih (by omega)]
    have hFr : F x = f^[r + 1] x := by
      simp only [F, retStep, dif_pos hx, r]
    rw [hFr]
    exact hstep r le_rfl
  have hF_iter : ∀ {x}, x ∈ A → ∀ m : ℕ,
      F^[m] x ∈ A ∧ (∃ N : ℕ, F^[m] x = f^[N] x) ∧
      (F^[m] x : ZMod D) = (x : ZMod D) + (m : ZMod D) * S := by
    intro x hx m
    induction m with
    | zero =>
      refine ⟨hx, ⟨0, rfl⟩, ?_⟩
      simp
    | succ m ih =>
      rcases ih with ⟨hmA, ⟨N, hN⟩, hmod⟩
      rw [Function.iterate_succ_apply']
      refine ⟨hF_mem hmA, ?_, ?_⟩
      · refine ⟨retStep (F^[m] x) + N, ?_⟩
        change f^[retStep (F^[m] x)] (F^[m] x) = f^[retStep (F^[m] x) + N] x
        rw [hN, Function.iterate_add_apply]
      · rw [hF_mod hmA, hmod]
        push_cast
        ring
  -- Step 4: Pick x0 ∈ A and find its minimal positive f-period p
  have hA_nonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x0, hx0A⟩ := hA_nonempty
  have hx0V : x0 ∈ V := (Finset.mem_filter.mp hx0A).1
  have hex_per : ∃ k : ℕ, 0 < k ∧ f^[k] x0 = x0 := by
    have hcard_lt : V.card < (Finset.range (V.card + 1)).card := by
      rw [Finset.card_range]
      omega
    have hmaps : ∀ k ∈ Finset.range (V.card + 1), f^[k] x0 ∈ V := fun k _ => hf_iterV hx0V k
    obtain ⟨i, hi, j, hj, hij, hEq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt hmaps
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · refine ⟨j - i, by omega, ?_⟩
      apply hf_iter_inj (hf_iterV hx0V (j - i)) hx0V i
      rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
      exact hEq.symm
    · refine ⟨i - j, by omega, ?_⟩
      apply hf_iter_inj (hf_iterV hx0V (i - j)) hx0V j
      rw [← Function.iterate_add_apply, show j + (i - j) = i by omega]
      exact hEq
  let p : ℕ := Nat.find hex_per
  have hp_spec : 0 < p ∧ f^[p] x0 = x0 := Nat.find_spec hex_per
  have hp_pos : 0 < p := hp_spec.1
  have hp_eq : f^[p] x0 = x0 := hp_spec.2
  have hp_min : ∀ k, 0 < k → k < p → f^[k] x0 ≠ x0 := by
    intro k hk0 hkp hEq
    exact Nat.find_min hex_per hkp ⟨hk0, hEq⟩
  have hf_iter_mul : ∀ q : ℕ, f^[p * q] x0 = x0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, ih, hp_eq]
  have hf_iter_mod : ∀ n : ℕ, f^[n] x0 = f^[n % p] x0 := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n p]
    rw [add_comm, Function.iterate_add_apply, hf_iter_mul]
  have hf_iter_inj_lt : ∀ a b, a < p → b < p → f^[a] x0 = f^[b] x0 → a = b := by
    intro a b ha hb hEq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : f^[b - a] x0 = x0 := by
        apply hf_iter_inj (hf_iterV hx0V (b - a)) hx0V a
        rw [← Function.iterate_add_apply, show a + (b - a) = b by omega]
        exact hEq.symm
      exact hp_min (b - a) (by omega) (by omega) this
    · have : f^[a - b] x0 = x0 := by
        apply hf_iter_inj (hf_iterV hx0V (a - b)) hx0V b
        rw [← Function.iterate_add_apply, show b + (a - b) = a by omega]
        exact hEq
      exact hp_min (a - b) (by omega) (by omega) this
  -- Step 5: Orbit O and mirror orbit O'
  let O : Finset ℕ := (Finset.range p).image (fun k => f^[k] x0)
  let O' : Finset ℕ := O.image m1
  have hO_sub : O ⊆ V := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
    exact hf_iterV hx0V k
  have hO'_sub : O' ⊆ V := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact hm1V (hO_sub hz)
  have hO_card : O.card = p := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range p
    · intro a ha b hb hEq
      exact hf_iter_inj_lt a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hEq
  have hO'_card : O'.card = p := by
    rw [Finset.card_image_of_injOn]
    · exact hO_card
    · intro a ha b hb hEq
      have haV := hO_sub ha
      have hbV := hO_sub hb
      have := congrArg m1 hEq
      rw [hm1_inv _ (hmemV.mp haV).1 (hmemV.mp haV).2,
          hm1_inv _ (hmemV.mp hbV).1 (hmemV.mp hbV).2] at this
      exact this
  have hO_mem_iter : ∀ n : ℕ, f^[n] x0 ∈ O := by
    intro n
    rw [hf_iter_mod n]
    exact Finset.mem_image.mpr ⟨n % p, Finset.mem_range.mpr (Nat.mod_lt n hp_pos), rfl⟩
  have hO_f : ∀ {y}, y ∈ O → f y ∈ O := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
    rw [← Function.iterate_succ_apply' f k x0]
    exact hO_mem_iter (k + 1)
  have hO_g : ∀ {y}, y ∈ O → g y ∈ O := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
    have hkp : f^[k + p] x0 = f^[k] x0 := by
      rw [Function.iterate_add_apply, hp_eq]
    have h1 : f^[k + p] x0 = f (f^[k + p - 1] x0) := by
      have : k + p = (k + p - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [Function.iterate_succ_apply']
    rw [← hkp, h1, hgf (hf_iterV hx0V (k + p - 1))]
    exact hO_mem_iter (k + p - 1)
  have hO'_g : ∀ {y}, y ∈ O' → g y ∈ O' := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    have : g (m1 z) = m1 (f z) := rfl
    rw [this]
    exact Finset.mem_image.mpr ⟨f z, hO_f hz, rfl⟩
  -- Step 6: O and O' are disjoint
  have hno_m1_orbit : ∀ k : ℕ, ∀ z, z ∈ V → m1 z ≠ f^[k] z := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro z hz hEq
      match k with
      | 0 => exact hm1_fpf z (hmemV.mp hz).1 (hmemV.mp hz).2 hEq
      | 1 =>
        have hm1z := hm1V hz
        exact hm2_fpf (m1 z) (hmemV.mp hm1z).1 (hmemV.mp hm1z).2 hEq.symm
      | k' + 2 =>
        have hfz : f z ∈ V := hfV hz
        have hfk1 : f^[k' + 1] z ∈ V := hf_iterV hz (k' + 1)
        have hm1_fk1 := hm1V hfk1
        have hstep : m1 (f z) = f^[k'] (f z) := by
          change m1 (m2 (m1 z)) = f^[k'] (f z)
          rw [hEq]
          rw [show f^[k' + 2] z = m2 (m1 (f^[k' + 1] z)) from Function.iterate_succ_apply' f (k' + 1) z]
          rw [hm2_inv _ (hmemV.mp hm1_fk1).1 (hmemV.mp hm1_fk1).2]
          rw [hm1_inv _ (hmemV.mp hfk1).1 (hmemV.mp hfk1).2]
          rw [Function.iterate_succ_apply]
        exact ih k' (by omega) (f z) hfz hstep
  have hdisj : Disjoint O O' := by
    rw [Finset.disjoint_left]
    intro y hyO hyO'
    rcases Finset.mem_image.mp hyO with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hyO' with ⟨z, hzO, hmz⟩
    rcases Finset.mem_image.mp hzO with ⟨b, hb, rfl⟩
    have ha' : a < p := Finset.mem_range.mp ha
    have hb' : b < p := Finset.mem_range.mp hb
    have hzV : f^[b] x0 ∈ V := hf_iterV hx0V b
    by_cases hba : b ≤ a
    · have hEq : m1 (f^[b] x0) = f^[a - b] (f^[b] x0) := by
        rw [← Function.iterate_add_apply, show a - b + b = a by omega]
        exact hmz
      exact hno_m1_orbit (a - b) (f^[b] x0) hzV hEq
    · have hEq : m1 (f^[b] x0) = f^[a + p - b] (f^[b] x0) := by
        rw [← Function.iterate_add_apply, show a + p - b + b = a + p by omega]
        rw [Function.iterate_add_apply, hp_eq]
        exact hmz
      exact hno_m1_orbit (a + p - b) (f^[b] x0) hzV hEq
  -- Step 7: D ≤ (O ∩ A).card and D ≤ (O' ∩ A).card
  have hOA_card : D ≤ (O ∩ A).card := by
    let phi : Fin D → ℕ := fun m => F^[m.val] x0
    have hphi_mem : ∀ m : Fin D, phi m ∈ O ∩ A := by
      intro m
      rcases hF_iter hx0A m.val with ⟨hmA, ⟨N, hN⟩, _⟩
      refine Finset.mem_inter.mpr ⟨?_, hmA⟩
      change F^[m.val] x0 ∈ O
      rw [hN]
      exact hO_mem_iter N
    have hphi_inj : Function.Injective phi := by
      intro m1 m2 hEq
      have h1 := (hF_iter hx0A m1.val).2.2
      have h2 := (hF_iter hx0A m2.val).2.2
      have hz : ((m1.val : ZMod D) * S) = ((m2.val : ZMod D) * S) := by
        apply add_left_cancel (a := (x0 : ZMod D))
        rw [← h1, ← h2]
        exact congrArg (fun n : ℕ => (n : ZMod D)) hEq
      have hmod : (m1.val : ZMod D) = (m2.val : ZMod D) := hS.mul_right_cancel hz
      have hval := congrArg ZMod.val hmod
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt m1.isLt, Nat.mod_eq_of_lt m2.isLt] at hval
      exact Fin.ext hval
    have hsub : Finset.univ.image phi ⊆ O ∩ A := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨m, _, rfl⟩
      exact hphi_mem m
    have hcard_img : (Finset.univ.image phi).card = D := by
      rw [Finset.card_image_of_injective _ hphi_inj, Finset.card_univ, Fintype.card_fin]
    calc D = (Finset.univ.image phi).card := hcard_img.symm
      _ ≤ (O ∩ A).card := Finset.card_le_card hsub
  have hO'A_card : D ≤ (O' ∩ A).card := by
    let psi : ℕ → ℕ := fun y => m1 (f y)
    have hsub : (O ∩ A).image psi ⊆ O' ∩ A := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨y, hy, rfl⟩
      rcases Finset.mem_inter.mp hy with ⟨hyO, hyA⟩
      have hyV : y ∈ V := hO_sub hyO
      have hyB : B (m1 y) := (Finset.mem_filter.mp hyA).2
      have hfyO : f y ∈ O := hO_f hyO
      have hfyV : f y ∈ V := hfV hyV
      have hm1yV : m1 y ∈ V := hm1V hyV
      refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨f y, hfyO, rfl⟩, ?_⟩
      refine Finset.mem_filter.mpr ⟨hm1V hfyV, ?_⟩
      change B (m1 (m1 (f y)))
      rw [hm1_inv _ (hmemV.mp hfyV).1 (hmemV.mp hfyV).2]
      exact hB_m2 (m1 y) (hmemV.mp hm1yV).1 (hmemV.mp hm1yV).2 hyB
    have hcard_img : ((O ∩ A).image psi).card = (O ∩ A).card := by
      apply Finset.card_image_of_injOn
      intro y1 hy1 y2 hy2 hEq
      have hy1V : y1 ∈ V := hO_sub (Finset.mem_inter.mp (Finset.mem_coe.mp hy1)).1
      have hy2V : y2 ∈ V := hO_sub (Finset.mem_inter.mp (Finset.mem_coe.mp hy2)).1
      have hfy1V : f y1 ∈ V := hfV hy1V
      have hfy2V : f y2 ∈ V := hfV hy2V
      have h1 := congrArg m1 hEq
      change m1 (m1 (f y1)) = m1 (m1 (f y2)) at h1
      rw [hm1_inv _ (hmemV.mp hfy1V).1 (hmemV.mp hfy1V).2,
          hm1_inv _ (hmemV.mp hfy2V).1 (hmemV.mp hfy2V).2] at h1
      exact hf_inj hy1V hy2V h1
    calc D ≤ (O ∩ A).card := hOA_card
      _ = ((O ∩ A).image psi).card := hcard_img.symm
      _ ≤ (O' ∩ A).card := Finset.card_le_card hsub
  -- Step 8: A ⊆ O ∪ O', hence O ∪ O' = V, hence V.card = 2 * p
  have hA_sub_union : A ⊆ O ∪ O' := by
    have hdisjA : Disjoint (O ∩ A) (O' ∩ A) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hdisj)
    have hsubA : (O ∩ A) ∪ (O' ∩ A) ⊆ A :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hcard_ge : A.card ≤ ((O ∩ A) ∪ (O' ∩ A)).card := by
      rw [Finset.card_union_of_disjoint hdisjA, hA_card]
      omega
    have hEqA : (O ∩ A) ∪ (O' ∩ A) = A := Finset.eq_of_subset_of_card_le hsubA hcard_ge
    intro a ha
    rw [← hEqA] at ha
    rcases Finset.mem_union.mp ha with h | h
    · exact Finset.mem_union_left O' (Finset.mem_inter.mp h).1
    · exact Finset.mem_union_right O (Finset.mem_inter.mp h).1
  have hUnion_g : ∀ k : ℕ, ∀ y, y ∈ O ∪ O' → g^[k] y ∈ O ∪ O' := by
    intro k
    induction k with
    | zero => intro y hy; exact hy
    | succ k ih =>
      intro y hy
      rw [Function.iterate_succ_apply']
      rcases Finset.mem_union.mp (ih y hy) with h | h
      · exact Finset.mem_union_left O' (hO_g h)
      · exact Finset.mem_union_right O (hO'_g h)
  have hV_eq_union : O ∪ O' = V := by
    apply Finset.Subset.antisymm (Finset.union_subset hO_sub hO'_sub)
    intro v hv
    obtain ⟨k, hkA⟩ := hhit v hv
    have hkU : f^[k] v ∈ O ∪ O' := hA_sub_union hkA
    have := hUnion_g k (f^[k] v) hkU
    rwa [hg_iter_f_iter hv k] at this
  have hV_card : V.card = 2 * p := by
    rw [← hV_eq_union, Finset.card_union_of_disjoint hdisj, hO_card, hO'_card]
    omega
  have h2p_eq : 2 * p = R - L + 1 := by
    have hIcc : V.card = R + 1 - L := Nat.card_Icc L R
    omega
  -- Step 9: Construct IntervalCycle L R
  let seq : Fin (2 * p) → ℕ := fun i =>
    if i.val % 2 = 0 then f^[i.val / 2] x0 else m1 (f^[i.val / 2] x0)
  have hseq_mem : ∀ i : Fin (2 * p), L ≤ seq i ∧ seq i ≤ R := by
    intro i
    dsimp only [seq]
    split_ifs
    · exact hmemV.mp (hf_iterV hx0V (i.val / 2))
    · exact hmemV.mp (hm1V (hf_iterV hx0V (i.val / 2)))
  have hseq_inj : Function.Injective seq := by
    intro i j hEq
    have hi_lt := i.isLt
    have hj_lt := j.isLt
    dsimp only [seq] at hEq
    split_ifs at hEq with hi hj hj
    · have hk : i.val / 2 = j.val / 2 :=
        hf_iter_inj_lt (i.val / 2) (j.val / 2) (by omega) (by omega) hEq
      exact Fin.ext (by omega)
    · exfalso
      have h1 : f^[i.val / 2] x0 ∈ O := hO_mem_iter (i.val / 2)
      have h2 : m1 (f^[j.val / 2] x0) ∈ O' :=
        Finset.mem_image.mpr ⟨f^[j.val / 2] x0, hO_mem_iter (j.val / 2), rfl⟩
      rw [hEq] at h1
      exact Finset.disjoint_left.mp hdisj h1 h2
    · exfalso
      have h1 : m1 (f^[i.val / 2] x0) ∈ O' :=
        Finset.mem_image.mpr ⟨f^[i.val / 2] x0, hO_mem_iter (i.val / 2), rfl⟩
      have h2 : f^[j.val / 2] x0 ∈ O := hO_mem_iter (j.val / 2)
      rw [← hEq] at h2
      exact Finset.disjoint_left.mp hdisj h2 h1
    · have h1 := congrArg m1 hEq
      have hiV := hf_iterV hx0V (i.val / 2)
      have hjV := hf_iterV hx0V (j.val / 2)
      rw [hm1_inv _ (hmemV.mp hiV).1 (hmemV.mp hiV).2,
          hm1_inv _ (hmemV.mp hjV).1 (hmemV.mp hjV).2] at h1
      have hk : i.val / 2 = j.val / 2 :=
        hf_iter_inj_lt (i.val / 2) (j.val / 2) (by omega) (by omega) h1
      exact Fin.ext (by omega)
  have hnext_even : ∀ (k : ℕ) (hk : 2 * k < 2 * p),
      seq ⟨2 * k, hk⟩ = f^[k] x0 ∧
      seq (nextIdx (by omega : 0 < 2 * p) ⟨2 * k, hk⟩) = m1 (f^[k] x0) := by
    intro k hk
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k) / 2 = k := by omega
    have h3 : (2 * k + 1) % (2 * p) = 2 * k + 1 := Nat.mod_eq_of_lt (by omega)
    have h4 : (2 * k + 1) % 2 ≠ 0 := by omega
    have h5 : (2 * k + 1) / 2 = k := by omega
    constructor
    · simp only [seq, h1, ↓reduceIte, h2]
    · simp only [seq, nextIdx, h3, h4, ↓reduceIte, h5]
  have hnext_odd : ∀ (k : ℕ) (hk : 2 * k + 1 < 2 * p),
      seq ⟨2 * k + 1, hk⟩ = m1 (f^[k] x0) ∧
      seq (nextIdx (by omega : 0 < 2 * p) ⟨2 * k + 1, hk⟩) = m2 (m1 (f^[k] x0)) := by
    intro k hk
    have h1 : (2 * k + 1) % 2 ≠ 0 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    have hmod_eq : (2 * k + 1 + 1) % (2 * p) = 2 * ((k + 1) % p) := by
      by_cases hkp : k + 1 < p
      · rw [Nat.mod_eq_of_lt (by omega : 2 * k + 1 + 1 < 2 * p), Nat.mod_eq_of_lt hkp]
        omega
      · have hkeq : k + 1 = p := by omega
        rw [show 2 * k + 1 + 1 = 2 * p by omega, hkeq, Nat.mod_self, Nat.mod_self]
    have h3 : (2 * ((k + 1) % p)) % 2 = 0 := by omega
    have h4 : (2 * ((k + 1) % p)) / 2 = (k + 1) % p := by omega
    constructor
    · simp only [seq, h1, ↓reduceIte, h2]
    · simp only [seq, nextIdx, hmod_eq, h3, ↓reduceIte, h4]
      rw [← hf_iter_mod (k + 1), Function.iterate_succ_apply']
  have hseq_adj : ∀ i : Fin (2 * p),
      IsSquare (seq i + seq (nextIdx (by omega : 0 < 2 * p) i)) := by
    intro i
    have hi_lt := i.isLt
    by_cases hev : i.val % 2 = 0
    · let k := i.val / 2
      have hk_lt : 2 * k < 2 * p := by omega
      have hi_eq : i = ⟨2 * k, hk_lt⟩ := Fin.ext (by dsimp; omega)
      rw [hi_eq]
      rcases hnext_even k hk_lt with ⟨hs1, hs2⟩
      rw [hs1, hs2]
      have hkV := hf_iterV hx0V k
      exact hm1_sq _ (hmemV.mp hkV).1 (hmemV.mp hkV).2
    · let k := i.val / 2
      have hk_lt : 2 * k + 1 < 2 * p := by omega
      have hi_eq : i = ⟨2 * k + 1, hk_lt⟩ := Fin.ext (by dsimp; omega)
      rw [hi_eq]
      rcases hnext_odd k hk_lt with ⟨hs1, hs2⟩
      rw [hs1, hs2]
      have hm1kV := hm1V (hf_iterV hx0V k)
      exact hm2_sq _ (hmemV.mp hm1kV).1 (hmemV.mp hm1kV).2
  let cyc : IntervalCycle L R := {
    len := 2 * p
    hlen := h2p_eq
    hpos := h2p_eq.symm ▸ hLR
    seq := seq
    hinj := hseq_inj
    hmem := hseq_mem
    hadj := hseq_adj
  }
  refine ⟨cyc, ?_⟩
  intro u huL huR
  have huV : u ∈ V := hmemV.mpr ⟨huL, huR⟩
  have huU : u ∈ O ∪ O' := by rwa [hV_eq_union]
  constructor
  · -- HasEdge cyc u (m1 u)
    rcases Finset.mem_union.mp huU with huO | huO'
    · rcases Finset.mem_image.mp huO with ⟨k, hk, rfl⟩
      have hklt : k < p := Finset.mem_range.mp hk
      refine ⟨⟨2 * k, show 2 * k < 2 * p by omega⟩, Or.inl ?_⟩
      exact hnext_even k (by omega)
    · rcases Finset.mem_image.mp huO' with ⟨z, hzO, rfl⟩
      rcases Finset.mem_image.mp hzO with ⟨k, hk, rfl⟩
      have hklt : k < p := Finset.mem_range.mp hk
      have hkV := hf_iterV hx0V k
      refine ⟨⟨2 * k, show 2 * k < 2 * p by omega⟩, Or.inr ?_⟩
      rcases hnext_even k (by omega) with ⟨hs1, hs2⟩
      refine ⟨?_, hs2⟩
      change seq ⟨2 * k, _⟩ = m1 (m1 (f^[k] x0))
      rw [hs1, hm1_inv _ (hmemV.mp hkV).1 (hmemV.mp hkV).2]
  · -- HasEdge cyc u (m2 u)
    rcases Finset.mem_union.mp huU with huO | huO'
    · have hguO : g u ∈ O := hO_g huO
      rcases Finset.mem_image.mp hguO with ⟨k, hk, hkeq⟩
      have hklt : k < p := Finset.mem_range.mp hk
      have hm2uV := hm2V huV
      have hm1k : m1 (f^[k] x0) = m2 u := by
        rw [hkeq]
        change m1 (m1 (m2 u)) = m2 u
        exact hm1_inv _ (hmemV.mp hm2uV).1 (hmemV.mp hm2uV).2
      have hm2m1k : m2 (m1 (f^[k] x0)) = u := by
        rw [hm1k]
        exact hm2_inv _ huL huR
      refine ⟨⟨2 * k + 1, show 2 * k + 1 < 2 * p by omega⟩, Or.inr ?_⟩
      rcases hnext_odd k (by omega) with ⟨hs1, hs2⟩
      exact ⟨hs1.trans hm1k, hs2.trans hm2m1k⟩
    · rcases Finset.mem_image.mp huO' with ⟨z, hzO, rfl⟩
      rcases Finset.mem_image.mp hzO with ⟨k, hk, rfl⟩
      have hklt : k < p := Finset.mem_range.mp hk
      refine ⟨⟨2 * k + 1, show 2 * k + 1 < 2 * p by omega⟩, Or.inl ?_⟩
      exact hnext_odd k (by omega)

/-! ## Part 2: The Four 4-Square Single-Cycle Theorems -/

lemma isSquare_of_add_sub {x s : ℕ} (h : x ≤ s * s) : IsSquare (x + (s * s - x)) := by
  refine ⟨s, ?_⟩
  omega

lemma odd_sq_ne_double {s x : ℕ} (hs : s % 2 = 1) : s * s - x ≠ x := by
  have hodd : (s * s) % 2 = 1 := by
    rw [Nat.mul_mod, hs]
  omega

lemma zmod_sub_eq {D x y : ℕ} (hy : y ≤ x) :
    ((x - y : ℕ) : ZMod D) = (x : ZMod D) - (y : ZMod D) := by
  rw [Nat.cast_sub hy]

lemma zmod_sq_refl_comp {D x s1 s2 : ℕ} (h1 : x ≤ s1 * s1) (h2 : s1 * s1 - x ≤ s2 * s2) :
    ((s2 * s2 - (s1 * s1 - x) : ℕ) : ZMod D) =
    (x : ZMod D) + (((s2 : ℤ) * s2 - (s1 : ℤ) * s1 : ℤ) : ZMod D) := by
  have hEq : ((s2 * s2 - (s1 * s1 - x) : ℕ) : ℤ) =
      (x : ℤ) + ((s2 : ℤ) * s2 - (s1 : ℤ) * s1) := by
    have h1z : (x : ℤ) ≤ (s1 : ℤ) * s1 := by exact_mod_cast h1
    have h2z : (s1 : ℤ) * s1 - (x : ℤ) ≤ (s2 : ℤ) * s2 := by
      have : ((s1 * s1 - x : ℕ) : ℤ) ≤ ((s2 * s2 : ℕ) : ℤ) := by exact_mod_cast h2
      rw [Nat.cast_sub h1] at this
      push_cast at this
      exact this
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
    push_cast
    omega
  have := congrArg (fun z : ℤ => (z : ZMod D)) hEq
  simpa using this

lemma zmod_sq_diff_add {D s1 s2 s3 : ℕ} (h : s2 * s2 = s1 * s1 + D) :
    (((s2 : ℤ) * s2 - (s3 : ℤ) * s3 : ℤ) : ZMod D) =
    (((s1 : ℤ) * s1 - (s3 : ℤ) * s3 : ℤ) : ZMod D) := by
  have hEq : (s2 : ℤ) * s2 - (s3 : ℤ) * s3 = ((s1 : ℤ) * s1 - (s3 : ℤ) * s3) + (D : ℤ) := by
    have : (s2 : ℤ) * s2 = (s1 : ℤ) * s1 + (D : ℤ) := by exact_mod_cast h
    omega
  rw [hEq, Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero]

lemma zmod_sq_diff_sub2 {D s1 s2 s3 : ℕ} (h : s3 * s3 = s2 * s2 + 2 * D) :
    (((s1 : ℤ) * s1 - (s3 : ℤ) * s3 : ℤ) : ZMod D) =
    (((s1 : ℤ) * s1 - (s2 : ℤ) * s2 : ℤ) : ZMod D) := by
  have hEq : (s1 : ℤ) * s1 - (s3 : ℤ) * s3 = ((s1 : ℤ) * s1 - (s2 : ℤ) * s2) - 2 * (D : ℤ) := by
    have : (s3 : ℤ) * s3 = (s2 : ℤ) * s2 + 2 * (D : ℤ) := by exact_mod_cast h
    omega
  rw [hEq, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      ZMod.natCast_self, mul_zero, sub_zero]

/-- 1. Left 4-square single-cycle theorem `(a, b, e1, e2)`. -/
theorem left_4sq_cycle {a b e1 e2 w1 L R : ℕ}
    (ha_odd : a % 2 = 1) (hb_odd : b % 2 = 1) (hab : a < b) (he : e1 < e2)
    (hdioph : b * b - a * a = 2 * (e2 * e2 - e1 * e1))
    (hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((e1 : ℤ) * e1 - (b : ℤ) * b)))
    (hw1_lo : 1 ≤ w1) (hw1_hi : w1 < e2 * e2 - e1 * e1)
    (hL : 2 * L + e2 * e2 = a * a + b * b + w1 + 1)
    (hL_pos : 1 ≤ L) (hL_hi : 2 * L + 3 ≤ a * a)
    (hR : R = b * b - L) :
    ∃ c : IntervalCycle L R,
      (∀ u, L ≤ u → u ≤ R → HasEdge c u (b * b - u)) ∧
      (∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c u (a * a - u)) ∧
      (∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c u (e1 * e1 - u)) ∧
      (∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c u (e2 * e2 - u)) := by
  let D : ℕ := e2 * e2 - e1 * e1
  have hD_pos : 1 ≤ D := by
    have : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    omega
  have ha2_lt_b2 : a * a < b * b := Nat.mul_lt_mul'' hab hab
  have hb2_eq : b * b = a * a + 2 * D := by omega
  have he2_eq : e2 * e2 = e1 * e1 + D := by
    have : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    omega
  let M : ℕ := a * a - L
  have hM_gt : L + 3 ≤ M := by omega
  have hR_eq : R = M + 2 * D := by omega
  have he1_sum : e1 * e1 = 2 * M + D + w1 + 1 := by omega
  have he2_sum : e2 * e2 = 2 * M + 2 * D + w1 + 1 := by omega
  let m1 : ℕ → ℕ := fun x => b * b - x
  let m2 : ℕ → ℕ := fun x =>
    if x ≤ M then a * a - x
    else if x ≤ M + w1 then e1 * e1 - x
    else if x ≤ M + D then e2 * e2 - x
    else if x ≤ M + D + w1 then e1 * e1 - x
    else e2 * e2 - x
  let B : ℕ → Prop := fun x => M + 1 ≤ x
  let S : ZMod D := (((e1 : ℤ) * e1 - (b : ℤ) * b : ℤ) : ZMod D)
  have hS : IsUnit S := isUnit_intCast_zmod_of_coprime hcop
  have hB_card : ((Finset.Icc L R).filter B).card = 2 * D := by
    have hfilt : (Finset.Icc L R).filter B = Finset.Icc (M + 1) R := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc, B]
      omega
    rw [hfilt, Nat.card_Icc]
    omega
  have hz_e2 : (((e2 : ℤ) * e2 - (b : ℤ) * b : ℤ) : ZMod D) = S :=
    zmod_sq_diff_add he2_eq
  obtain ⟨c, hc⟩ := master_involution_cycle (L := L) (R := R) (D := D)
    (by omega) hD_pos (m1 := m1) (m2 := m2)
    (fun x hxL hxR => by dsimp only [m1]; omega)
    (fun x hxL hxR => by dsimp only [m1]; omega)
    (fun x hxL hxR => by dsimp only [m1]; exact odd_sq_ne_double hb_odd)
    (fun x hxL hxR => by dsimp only [m1]; exact isSquare_of_add_sub (by omega))
    (fun x hxL hxR => by dsimp only [m2]; split_ifs <;> omega)
    (fun x hxL hxR => by
      dsimp only [m2]
      by_cases h1 : x ≤ M
      · rw [if_pos h1, if_pos (by omega)]; omega
      · rw [if_neg h1]
        by_cases h2 : x ≤ M + w1
        · rw [if_pos h2, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
        · rw [if_neg h2]
          by_cases h3 : x ≤ M + D
          · rw [if_pos h3, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega
          · rw [if_neg h3]
            by_cases h4 : x ≤ M + D + w1
            · rw [if_pos h4, if_neg (by omega), if_pos (by omega)]; omega
            · rw [if_neg h4, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega)
    (fun x hxL hxR => by
      dsimp only [m2]
      split_ifs with h1
      · exact odd_sq_ne_double ha_odd
      · omega
      · omega
      · omega
      · omega)
    (fun x hxL hxR => by
      dsimp only [m2]
      split_ifs <;> exact isSquare_of_add_sub (by omega))
    B hB_card
    (fun x hxL hxR hBx => by dsimp only [B, m2] at hBx ⊢; split_ifs <;> omega)
    S hS
    (fun x hxL hxR hnotB => by
      dsimp only [B, m1, m2] at hnotB ⊢
      have hle : b * b - x ≤ M := by omega
      rw [if_pos hle]
      have hEq : a * a - (b * b - x) = x - 2 * D := by omega
      rw [hEq, zmod_sub_eq (by omega)]
      simp)
    (fun x hxL hxR hBx => by
      dsimp only [B, m1, m2] at hBx ⊢
      have hgt : ¬ (b * b - x ≤ M) := by omega
      rw [if_neg hgt]
      split_ifs
      · exact zmod_sq_refl_comp (by omega) (by omega)
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e2]
      · exact zmod_sq_refl_comp (by omega) (by omega)
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e2])
    (Or.inl (fun x hxL hxR hnotB => by
      dsimp only [B, m1, m2] at hnotB ⊢
      have hle : b * b - x ≤ M := by omega
      rw [if_pos hle]
      omega))
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro u huL huR
    exact (hc u huL huR).1
  · refine ⟨L, le_rfl, by omega, ?_⟩
    have h := (hc L le_rfl (by omega)).2
    have hm2L : m2 L = a * a - L := by dsimp only [m2]; rw [if_pos (by omega)]
    rwa [hm2L] at h
  · refine ⟨M + 1, by omega, by omega, ?_⟩
    have h := (hc (M + 1) (by omega) (by omega)).2
    have hm2e1 : m2 (M + 1) = e1 * e1 - (M + 1) := by
      dsimp only [m2]
      rw [if_neg (by omega), if_pos (by omega)]
    rwa [hm2e1] at h
  · refine ⟨M + w1 + 1, by omega, by omega, ?_⟩
    have h := (hc (M + w1 + 1) (by omega) (by omega)).2
    have hm2e2 : m2 (M + w1 + 1) = e2 * e2 - (M + w1 + 1) := by
      dsimp only [m2]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rwa [hm2e2] at h

/-- 2. Mirror 4-square single-cycle theorem `(e1, e2, b, c)`. -/
theorem mirror_4sq_cycle {e1 e2 b c w1 L R : ℕ}
    (hb_odd : b % 2 = 1) (hc_odd : c % 2 = 1) (hbc : b < c) (he : e1 < e2)
    (hdioph : c * c - b * b = 2 * (e2 * e2 - e1 * e1))
    (hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2)))
    (hw1_lo : 1 ≤ w1) (hw1_hi : w1 < e2 * e2 - e1 * e1)
    (hL : 2 * L + w1 + e2 * e2 = 2 * e1 * e1 + 1)
    (hL_pos : 1 ≤ L) (hL_hi : 2 * L + c * c + 3 ≤ 2 * b * b)
    (hR : R = b * b - L) :
    ∃ c_cyc : IntervalCycle L R,
      (∀ u, L ≤ u → u ≤ R → HasEdge c_cyc u (b * b - u)) ∧
      (∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c_cyc u (c * c - u)) ∧
      (∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c_cyc u (e1 * e1 - u)) ∧
      (∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c_cyc u (e2 * e2 - u)) := by
  let D : ℕ := e2 * e2 - e1 * e1
  have hD_pos : 1 ≤ D := by
    have : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    omega
  have hb2_lt_c2 : b * b < c * c := Nat.mul_lt_mul'' hbc hbc
  have hc2_eq : c * c = b * b + 2 * D := by omega
  have he2_eq : e2 * e2 = e1 * e1 + D := by
    have : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    omega
  have h2b2 : 2 * b * b = 2 * (b * b) := by ring
  have h2e12 : 2 * e1 * e1 = 2 * (e1 * e1) := by ring
  have hR_ge : L + 2 * D + 3 ≤ R := by omega
  have he1_sum : e1 * e1 = 2 * L + w1 + D - 1 := by omega
  have he2_sum : e2 * e2 = 2 * L + w1 + 2 * D - 1 := by omega
  let m1 : ℕ → ℕ := fun x => b * b - x
  let m2 : ℕ → ℕ := fun x =>
    if x ≤ L + w1 - 1 then e1 * e1 - x
    else if x ≤ L + D - 1 then e2 * e2 - x
    else if x ≤ L + D + w1 - 1 then e1 * e1 - x
    else if x ≤ L + 2 * D - 1 then e2 * e2 - x
    else c * c - x
  let B : ℕ → Prop := fun x => x ≤ L + 2 * D - 1
  let S : ZMod D := (((e2 : ℤ) * e2 - (b : ℤ) * b : ℤ) : ZMod D)
  have hS : IsUnit S := by
    have hcop' : Nat.Coprime D (Int.natAbs ((e2 : ℤ) * e2 - (b : ℤ) * b)) := by
      have : Int.natAbs ((e2 : ℤ) * e2 - (b : ℤ) * b) =
             Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2) := by
        rw [← Int.natAbs_neg, neg_sub]
      rw [this]
      exact hcop
    exact isUnit_intCast_zmod_of_coprime hcop'
  have hB_card : ((Finset.Icc L R).filter B).card = 2 * D := by
    have hfilt : (Finset.Icc L R).filter B = Finset.Icc L (L + 2 * D - 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc, B]
      omega
    rw [hfilt, Nat.card_Icc]
    omega
  have hz_e1 : (((e1 : ℤ) * e1 - (b : ℤ) * b : ℤ) : ZMod D) = S :=
    (zmod_sq_diff_add he2_eq).symm
  obtain ⟨cyc, hcyc⟩ := master_involution_cycle (L := L) (R := R) (D := D)
    (by omega) hD_pos (m1 := m1) (m2 := m2)
    (fun x hxL hxR => by dsimp only [m1]; omega)
    (fun x hxL hxR => by dsimp only [m1]; omega)
    (fun x hxL hxR => by dsimp only [m1]; exact odd_sq_ne_double hb_odd)
    (fun x hxL hxR => by dsimp only [m1]; exact isSquare_of_add_sub (by omega))
    (fun x hxL hxR => by dsimp only [m2]; split_ifs <;> omega)
    (fun x hxL hxR => by
      dsimp only [m2]
      by_cases h1 : x ≤ L + w1 - 1
      · rw [if_pos h1, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h1]
        by_cases h2 : x ≤ L + D - 1
        · rw [if_pos h2, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
        · rw [if_neg h2]
          by_cases h3 : x ≤ L + D + w1 - 1
          · rw [if_pos h3, if_pos (by omega)]; omega
          · rw [if_neg h3]
            by_cases h4 : x ≤ L + 2 * D - 1
            · rw [if_pos h4, if_neg (by omega), if_pos (by omega)]; omega
            · rw [if_neg h4, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega)
    (fun x hxL hxR => by
      dsimp only [m2]
      split_ifs
      · omega
      · omega
      · omega
      · omega
      · exact odd_sq_ne_double hc_odd)
    (fun x hxL hxR => by
      dsimp only [m2]
      split_ifs <;> exact isSquare_of_add_sub (by omega))
    B hB_card
    (fun x hxL hxR hBx => by dsimp only [B, m2] at hBx ⊢; split_ifs <;> omega)
    S hS
    (fun x hxL hxR hnotB => by
      dsimp only [B, m1, m2] at hnotB ⊢
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hEq : c * c - (b * b - x) = x + 2 * D := by omega
      rw [hEq]
      simp)
    (fun x hxL hxR hBx => by
      dsimp only [B, m1, m2] at hBx ⊢
      split_ifs
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e1]
      · exact zmod_sq_refl_comp (by omega) (by omega)
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e1]
      · exact zmod_sq_refl_comp (by omega) (by omega))
    (Or.inr (fun x hxL hxR hnotB => by
      dsimp only [B, m1, m2] at hnotB ⊢
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      omega))
  refine ⟨cyc, ?_, ?_, ?_, ?_⟩
  · intro u huL huR
    exact (hcyc u huL huR).1
  · refine ⟨R, by omega, le_rfl, ?_⟩
    have h := (hcyc R (by omega) le_rfl).2
    have hm2R : m2 R = c * c - R := by
      dsimp only [m2]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rwa [hm2R] at h
  · refine ⟨L, le_rfl, by omega, ?_⟩
    have h := (hcyc L le_rfl (by omega)).2
    have hm2L : m2 L = e1 * e1 - L := by
      dsimp only [m2]
      rw [if_pos (by omega)]
    rwa [hm2L] at h
  · refine ⟨L + w1, by omega, by omega, ?_⟩
    have h := (hcyc (L + w1) (by omega) (by omega)).2
    have hm2e2 : m2 (L + w1) = e2 * e2 - (L + w1) := by
      dsimp only [m2]
      rw [if_neg (by omega), if_pos (by omega)]
    rwa [hm2e2] at h

/-- 3. 3-Cross 4-square single-cycle theorem `(e1, e2, b, e3)`. -/
theorem three_cross_cycle {e1 e2 b e3 w1 L R : ℕ}
    (hb_odd : b % 2 = 1) (he12 : e1 < e2) (_he23 : e2 < e3)
    (hdioph : b * b + e2 * e2 = e1 * e1 + e3 * e3)
    (hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2)))
    (hw1_lo : 1 ≤ w1) (hw1_hi : w1 < e2 * e2 - e1 * e1)
    (hw3 : e2 * e2 + 1 ≤ b * b + w1)
    (hL : 2 * L + b * b + 2 * w1 = 2 * e1 * e1 + 1)
    (hL_pos : 1 ≤ L) (hR : R = b * b - L) :
    ∃ c_cyc : IntervalCycle L R,
      ∀ u, L ≤ u → u ≤ R → HasEdge c_cyc u (b * b - u) := by
  obtain ⟨D, hD_def⟩ : ∃ D : ℕ, D = e2 * e2 - e1 * e1 := ⟨_, rfl⟩
  have hD_pos : 1 ≤ D := by
    have : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he12 he12
    omega
  have he2_eq : e2 * e2 = e1 * e1 + D := by
    have : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he12 he12
    omega
  have he3_eq : e3 * e3 = b * b + D := by omega
  have h2e12 : 2 * e1 * e1 = 2 * (e1 * e1) := by ring
  obtain ⟨W, hW_def⟩ : ∃ W : ℕ, W = D + (b * b + w1 - e2 * e2) := ⟨_, rfl⟩
  have hW_gt : D + 1 ≤ W := by omega
  have hR_eq : R = L + 2 * W - 1 := by omega
  have hb2_sum : b * b = 2 * L + 2 * W - 1 := by omega
  have he1_sum : e1 * e1 = 2 * L + W + w1 - 1 := by omega
  have he2_sum : e2 * e2 = 2 * L + W + w1 + D - 1 := by omega
  have he3_sum : e3 * e3 = 2 * L + 2 * W + D - 1 := by omega
  have hw1_hi' : w1 < D := by omega
  have hcopD : Nat.Coprime D (Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2)) := by
    rwa [hD_def]
  clear hD_def hW_def hdioph hw3 hL hR hcop he12 _he23 h2e12 hw1_hi
  let m1 : ℕ → ℕ := fun x => b * b - x
  let m2 : ℕ → ℕ := fun x =>
    if x ≤ L + w1 - 1 then e1 * e1 - x
    else if x ≤ L + D - 1 then e2 * e2 - x
    else if x ≤ L + W - 1 then e3 * e3 - x
    else if x ≤ L + W + w1 - 1 then e1 * e1 - x
    else if x ≤ L + W + D - 1 then e2 * e2 - x
    else e3 * e3 - x
  have hm2_I1 : ∀ x, x ≤ L + w1 - 1 → m2 x = e1 * e1 - x := fun x h => by
    dsimp only [m2]; rw [if_pos h]
  have hm2_I2 : ∀ x, L + w1 ≤ x → x ≤ L + D - 1 → m2 x = e2 * e2 - x := fun x _ h2 => by
    clear hcopD hb_odd hb2_sum he2_eq he3_eq he1_sum he2_sum he3_sum hR_eq
    dsimp only [m2]; rw [if_neg (by omega), if_pos h2]
  have hm2_I3 : ∀ x, L + D ≤ x → x ≤ L + W - 1 → m2 x = e3 * e3 - x := fun x _ h2 => by
    clear hcopD hb_odd hb2_sum he2_eq he3_eq he1_sum he2_sum he3_sum hR_eq
    dsimp only [m2]; rw [if_neg (by omega), if_neg (by omega), if_pos h2]
  have hm2_I4 : ∀ x, L + W ≤ x → x ≤ L + W + w1 - 1 → m2 x = e1 * e1 - x := fun x _ h2 => by
    clear hcopD hb_odd hb2_sum he2_eq he3_eq he1_sum he2_sum he3_sum hR_eq
    dsimp only [m2]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]
  have hm2_I5 : ∀ x, L + W + w1 ≤ x → x ≤ L + W + D - 1 → m2 x = e2 * e2 - x := fun x _ h2 => by
    clear hcopD hb_odd hb2_sum he2_eq he3_eq he1_sum he2_sum he3_sum hR_eq
    dsimp only [m2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]
  have hm2_I6 : ∀ x, L + W + D ≤ x → m2 x = e3 * e3 - x := fun x _ => by
    clear hcopD hb_odd hb2_sum he2_eq he3_eq he1_sum he2_sum he3_sum hR_eq
    dsimp only [m2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hm2_all : ∀ x, L ≤ x → x ≤ R →
      (L ≤ m2 x ∧ m2 x ≤ R) ∧ m2 (m2 x) = x ∧ m2 x ≠ x ∧ IsSquare (x + m2 x) := by
    clear hcopD hb_odd hb2_sum he2_eq he3_eq m1
    intro x hxL hxR
    by_cases h1 : x ≤ L + w1 - 1
    · rw [hm2_I1 x h1]
      exact ⟨by omega, by rw [hm2_I4 _ (by omega) (by omega)]; omega,
             by omega, isSquare_of_add_sub (by omega)⟩
    · by_cases h2 : x ≤ L + D - 1
      · rw [hm2_I2 x (by omega) h2]
        exact ⟨by omega, by rw [hm2_I5 _ (by omega) (by omega)]; omega,
               by omega, isSquare_of_add_sub (by omega)⟩
      · by_cases h3 : x ≤ L + W - 1
        · rw [hm2_I3 x (by omega) h3]
          exact ⟨by omega, by rw [hm2_I6 _ (by omega)]; omega,
                 by omega, isSquare_of_add_sub (by omega)⟩
        · by_cases h4 : x ≤ L + W + w1 - 1
          · rw [hm2_I4 x (by omega) h4]
            exact ⟨by omega, by rw [hm2_I1 _ (by omega)]; omega,
                   by omega, isSquare_of_add_sub (by omega)⟩
          · by_cases h5 : x ≤ L + W + D - 1
            · rw [hm2_I5 x (by omega) h5]
              exact ⟨by omega, by rw [hm2_I2 _ (by omega) (by omega)]; omega,
                     by omega, isSquare_of_add_sub (by omega)⟩
            · rw [hm2_I6 x (by omega)]
              exact ⟨by omega, by rw [hm2_I3 _ (by omega) (by omega)]; omega,
                     by omega, isSquare_of_add_sub (by omega)⟩
  let B : ℕ → Prop := fun x =>
    x ≤ L + D - 1 ∨ (L + W ≤ x ∧ x ≤ L + W + D - 1)
  let S : ZMod D := (((e2 : ℤ) * e2 - (b : ℤ) * b : ℤ) : ZMod D)
  have hS : IsUnit S := by
    have hcop' : Nat.Coprime D (Int.natAbs ((e2 : ℤ) * e2 - (b : ℤ) * b)) := by
      have : Int.natAbs ((e2 : ℤ) * e2 - (b : ℤ) * b) =
             Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2) := by
        rw [← Int.natAbs_neg, neg_sub]
      rw [this]
      exact hcopD
    exact isUnit_intCast_zmod_of_coprime hcop'
  have hB_card : ((Finset.Icc L R).filter B).card = 2 * D := by
    have hfilt : (Finset.Icc L R).filter B =
        Finset.Icc L (L + D - 1) ∪ Finset.Icc (L + W) (L + W + D - 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, B]
      omega
    have hdisj : Disjoint (Finset.Icc L (L + D - 1)) (Finset.Icc (L + W) (L + W + D - 1)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1 hx2
      omega
    rw [hfilt, Finset.card_union_of_disjoint hdisj, Nat.card_Icc, Nat.card_Icc]
    omega
  have hz_e1 : (((e1 : ℤ) * e1 - (b : ℤ) * b : ℤ) : ZMod D) = S :=
    (zmod_sq_diff_add he2_eq).symm
  have hB_m2 : ∀ x, L ≤ x → x ≤ R → B x → B (m2 x) := by
    intro x hxL hxR hBx
    dsimp only [B] at hBx ⊢
    rcases hBx with hBx | ⟨hBx1, hBx2⟩
    · by_cases h1 : x ≤ L + w1 - 1
      · rw [hm2_I1 x h1]; right; omega
      · rw [hm2_I2 x (by omega) hBx]; right; omega
    · by_cases h4 : x ≤ L + W + w1 - 1
      · rw [hm2_I4 x hBx1 h4]; left; omega
      · rw [hm2_I5 x (by omega) hBx2]; left; omega
  have hmod_out : ∀ x, L ≤ x → x ≤ R → ¬ B (m1 x) → ((m2 (m1 x) : ℕ) : ZMod D) = (x : ZMod D) := by
    intro x hxL hxR hnotB
    dsimp only [B, m1] at hnotB ⊢
    by_cases h3 : b * b - x ≤ L + W - 1
    · rw [hm2_I3 (b * b - x) (by omega) h3]
      have hEq : e3 * e3 - (b * b - x) = x + D := by omega
      rw [hEq]
      simp
    · rw [hm2_I6 (b * b - x) (by omega)]
      have hEq : e3 * e3 - (b * b - x) = x + D := by omega
      rw [hEq]
      simp
  have hmod_in : ∀ x, L ≤ x → x ≤ R → B (m1 x) → ((m2 (m1 x) : ℕ) : ZMod D) = (x : ZMod D) + S := by
    intro x hxL hxR hBx
    dsimp only [B, m1] at hBx ⊢
    rcases hBx with hBx | ⟨hBx1, hBx2⟩
    · by_cases h1 : b * b - x ≤ L + w1 - 1
      · rw [hm2_I1 _ h1, zmod_sq_refl_comp (by omega) (by omega), hz_e1]
      · rw [hm2_I2 _ (by omega) hBx]
        exact zmod_sq_refl_comp (by omega) (by omega)
    · by_cases h4 : b * b - x ≤ L + W + w1 - 1
      · rw [hm2_I4 _ hBx1 h4, zmod_sq_refl_comp (by omega) (by omega), hz_e1]
      · rw [hm2_I5 _ (by omega) hBx2]
        exact zmod_sq_refl_comp (by omega) (by omega)
  have hmono : ∀ x, L ≤ x → x ≤ R → ¬ B (m1 x) → x < m2 (m1 x) := by
    intro x hxL hxR hnotB
    dsimp only [B, m1] at hnotB ⊢
    by_cases h3 : b * b - x ≤ L + W - 1
    · rw [hm2_I3 _ (by omega) h3]; omega
    · rw [hm2_I6 _ (by omega)]; omega
  obtain ⟨cyc, hcyc⟩ := master_involution_cycle (L := L) (R := R) (D := D)
    (by omega) hD_pos (m1 := m1) (m2 := m2)
    (fun x hxL hxR => by dsimp only [m1]; omega)
    (fun x hxL hxR => by dsimp only [m1]; omega)
    (fun x hxL hxR => by dsimp only [m1]; exact odd_sq_ne_double hb_odd)
    (fun x hxL hxR => by dsimp only [m1]; exact isSquare_of_add_sub (by omega))
    (fun x hxL hxR => (hm2_all x hxL hxR).1)
    (fun x hxL hxR => (hm2_all x hxL hxR).2.1)
    (fun x hxL hxR => (hm2_all x hxL hxR).2.2.1)
    (fun x hxL hxR => (hm2_all x hxL hxR).2.2.2)
    B hB_card hB_m2 S hS hmod_out hmod_in (Or.inr hmono)
  exact ⟨cyc, fun u huL huR => (hcyc u huL huR).1⟩

/-- 4. Split-M1 2-Cross single-cycle theorem `(b1, b2, e1, e2)`. -/
theorem split_m1_2cross_cycle {b1 b2 e1 e2 w1 L R : ℕ}
    (hb1_odd : b1 % 2 = 1) (hb2_odd : b2 % 2 = 1) (hb12 : b1 < b2) (he : e1 < e2)
    (hdioph : b2 * b2 - b1 * b1 = 2 * (e2 * e2 - e1 * e1))
    (hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((b1 : ℤ) * b1 - (e1 : ℤ) * e1)))
    (hw1_lo : 1 ≤ w1) (hw1_hi : w1 < e2 * e2 - e1 * e1)
    (hL : 2 * L + w1 + e2 * e2 = 2 * e1 * e1 + 1)
    (hL_pos : 1 ≤ L) (hR : R = L + 2 * (e2 * e2 - e1 * e1) - 1)
    (hJ1 : 2 * L + 3 ≤ b1 * b1) (hJ2 : b2 * b2 + 3 ≤ 2 * R) :
    ∃ c_cyc : IntervalCycle L R,
      (∀ u, L ≤ u → u ≤ b1 * b1 - L → HasEdge c_cyc u (b1 * b1 - u)) ∧
      (∀ u, b2 * b2 - R ≤ u → u ≤ R → HasEdge c_cyc u (b2 * b2 - u)) := by
  let D : ℕ := e2 * e2 - e1 * e1
  have hD_pos : 1 ≤ D := by
    have : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    omega
  have hb12_sq : b1 * b1 < b2 * b2 := Nat.mul_lt_mul'' hb12 hb12
  have hb2_eq : b2 * b2 = b1 * b1 + 2 * D := by omega
  have he2_eq : e2 * e2 = e1 * e1 + D := by
    have : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    omega
  have h2e12 : 2 * e1 * e1 = 2 * (e1 * e1) := by ring
  let M1 : ℕ := b1 * b1 - L
  have hM1_lo : L + 3 ≤ M1 := by omega
  have hM1_hi : M1 + 4 ≤ R := by omega
  have hsplit : b2 * b2 - R = M1 + 1 := by omega
  have he1_sum : e1 * e1 = 2 * L + w1 + D - 1 := by omega
  have he2_sum : e2 * e2 = 2 * L + w1 + 2 * D - 1 := by omega
  let m1 : ℕ → ℕ := fun x => if x ≤ M1 then b1 * b1 - x else b2 * b2 - x
  let m2 : ℕ → ℕ := fun x =>
    if x ≤ L + w1 - 1 then e1 * e1 - x
    else if x ≤ L + D - 1 then e2 * e2 - x
    else if x ≤ L + D + w1 - 1 then e1 * e1 - x
    else e2 * e2 - x
  let B : ℕ → Prop := fun _ => True
  let S : ZMod D := (((e1 : ℤ) * e1 - (b1 : ℤ) * b1 : ℤ) : ZMod D)
  have hS : IsUnit S := by
    have hcop' : Nat.Coprime D (Int.natAbs ((e1 : ℤ) * e1 - (b1 : ℤ) * b1)) := by
      have : Int.natAbs ((e1 : ℤ) * e1 - (b1 : ℤ) * b1) =
             Int.natAbs ((b1 : ℤ) * b1 - (e1 : ℤ) * e1) := by
        rw [← Int.natAbs_neg, neg_sub]
      rw [this]
      exact hcop
    exact isUnit_intCast_zmod_of_coprime hcop'
  have hB_card : ((Finset.Icc L R).filter B).card = 2 * D := by
    have hfilt : (Finset.Icc L R).filter B = Finset.Icc L R := by
      ext x
      simp [B]
    rw [hfilt, Nat.card_Icc]
    omega
  have hz_e1_b2 : (((e1 : ℤ) * e1 - (b2 : ℤ) * b2 : ℤ) : ZMod D) = S :=
    zmod_sq_diff_sub2 hb2_eq
  have hz_e2_b1 : (((e2 : ℤ) * e2 - (b1 : ℤ) * b1 : ℤ) : ZMod D) = S :=
    zmod_sq_diff_add he2_eq
  have hz_e2_b2 : (((e2 : ℤ) * e2 - (b2 : ℤ) * b2 : ℤ) : ZMod D) = S :=
    (zmod_sq_diff_add he2_eq).trans hz_e1_b2
  obtain ⟨cyc, hcyc⟩ := master_involution_cycle (L := L) (R := R) (D := D)
    (by omega) hD_pos (m1 := m1) (m2 := m2)
    (fun x hxL hxR => by dsimp only [m1]; split_ifs <;> omega)
    (fun x hxL hxR => by
      dsimp only [m1]
      by_cases h1 : x ≤ M1
      · rw [if_pos h1, if_pos (by omega)]; omega
      · rw [if_neg h1, if_neg (by omega)]; omega)
    (fun x hxL hxR => by
      dsimp only [m1]
      split_ifs
      · exact odd_sq_ne_double hb1_odd
      · exact odd_sq_ne_double hb2_odd)
    (fun x hxL hxR => by
      dsimp only [m1]
      split_ifs <;> exact isSquare_of_add_sub (by omega))
    (fun x hxL hxR => by dsimp only [m2]; split_ifs <;> omega)
    (fun x hxL hxR => by
      dsimp only [m2]
      by_cases h1 : x ≤ L + w1 - 1
      · rw [if_pos h1, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
      · rw [if_neg h1]
        by_cases h2 : x ≤ L + D - 1
        · rw [if_pos h2, if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega
        · rw [if_neg h2]
          by_cases h3 : x ≤ L + D + w1 - 1
          · rw [if_pos h3, if_pos (by omega)]; omega
          · rw [if_neg h3, if_neg (by omega), if_pos (by omega)]; omega)
    (fun x hxL hxR => by dsimp only [m2]; split_ifs <;> omega)
    (fun x hxL hxR => by
      dsimp only [m2]
      split_ifs <;> exact isSquare_of_add_sub (by omega))
    B hB_card
    (fun _ _ _ _ => trivial)
    S hS
    (fun _ _ _ hnotB => False.elim (hnotB trivial))
    (fun x hxL hxR _ => by
      dsimp only [m1, m2]
      split_ifs
      · exact zmod_sq_refl_comp (by omega) (by omega)
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e2_b1]
      · exact zmod_sq_refl_comp (by omega) (by omega)
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e2_b1]
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e1_b2]
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e2_b2]
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e1_b2]
      · rw [zmod_sq_refl_comp (by omega) (by omega), hz_e2_b2])
    (Or.inl (fun _ _ _ hnotB => False.elim (hnotB trivial)))
  refine ⟨cyc, ?_, ?_⟩
  · intro u huL huM
    have h := (hcyc u huL (by omega)).1
    have hm1u : m1 u = b1 * b1 - u := by dsimp only [m1]; rw [if_pos huM]
    rwa [hm1u] at h
  · intro u huM huR
    have h := (hcyc u (by omega) huR).1
    have hm1u : m1 u = b2 * b2 - u := by dsimp only [m1]; rw [if_neg (by omega)]
    rwa [hm1u] at h

/-! ## Part 3: Closed-Form Infinite Mirror Coverage for ALL `n ≥ 461457` -/

lemma hasMod5Class_of_hasEdge {L R : ℕ} (hL : 1 ≤ L) {c : IntervalCycle L R} {u z cls : ℕ}
    (he : HasEdge c u (z * z - u))
    (hcls : if cls = 0 then z % 5 = 0
            else if cls = 1 then z % 5 = 1 ∨ z % 5 = 4
            else z % 5 = 2 ∨ z % 5 = 3) :
    HasMod5Class c cls := by
  rcases he with ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · have hge : L ≤ z * z - u := by
      rw [← h2]
      exact (c.hmem _).1
    refine ⟨i, z, ?_, hcls⟩
    rw [h1, h2]
    omega
  · have hge : L ≤ z * z - u := by
      rw [← h1]
      exact (c.hmem _).1
    refine ⟨i, z, ?_, hcls⟩
    rw [h1, h2]
    omega

/-- Geometric scale sequence `24, 36, 48, 72, 96, 144, ...`. -/
def Mseq (k : ℕ) : ℕ :=
  if k % 2 = 0 then 24 * 2 ^ (k / 2) else 36 * 2 ^ (k / 2)

lemma Mseq_ge_24 (k : ℕ) : 24 ≤ Mseq k := by
  unfold Mseq
  have h1 : 1 ≤ 2 ^ (k / 2) := Nat.one_le_two_pow
  split_ifs <;> omega

lemma Mseq_ge_36 {k : ℕ} (hk : 1 ≤ k) : 36 ≤ Mseq k := by
  unfold Mseq
  split_ifs with hev
  · have hk2 : 1 ≤ k / 2 := by omega
    have h2 : 2 ≤ 2 ^ (k / 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k / 2) := Nat.pow_le_pow_right (by omega) hk2
    omega
  · have h1 : 1 ≤ 2 ^ (k / 2) := Nat.one_le_two_pow
    omega

lemma Mseq_even (k : ℕ) : Mseq k % 2 = 0 := by
  unfold Mseq
  split_ifs <;> omega

lemma Mseq_div3 (k : ℕ) : Mseq k % 3 = 0 := by
  unfold Mseq
  split_ifs <;> omega

lemma pow2_mod5_ne_zero (r : ℕ) : 2 ^ r % 5 ≠ 0 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [pow_succ]
    omega

lemma Mseq_not_div5 (k : ℕ) : Mseq k % 5 ≠ 0 := by
  unfold Mseq
  have h := pow2_mod5_ne_zero (k / 2)
  split_ifs <;> omega

lemma Mseq_prime_factors (k : ℕ) {p : ℕ} (hp : Nat.Prime p) (hd : p ∣ Mseq k) :
    p = 2 ∨ p = 3 := by
  unfold Mseq at hd
  split_ifs at hd
  · rcases hp.dvd_mul.mp hd with h24 | hpow
    · have h24' : p ∣ 3 * 2 ^ 3 := by simpa using h24
      rcases hp.dvd_mul.mp h24' with h3 | h2
      · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpow)
  · rcases hp.dvd_mul.mp hd with h36 | hpow
    · have h36' : p ∣ 3 ^ 2 * 2 ^ 2 := by simpa using h36
      rcases hp.dvd_mul.mp h36' with h3 | h2
      · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)
      · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpow)

lemma Mseq_step (k : ℕ) : 2 * Mseq (k + 1) ≤ 3 * Mseq k := by
  unfold Mseq
  by_cases h : k % 2 = 0
  · have h1 : (k + 1) % 2 ≠ 0 := by omega
    have h2 : (k + 1) / 2 = k / 2 := by omega
    simp only [h, h1, ↓reduceIte, h2]
    omega
  · have h1 : (k + 1) % 2 = 0 := by omega
    have h2 : (k + 1) / 2 = k / 2 + 1 := by omega
    simp only [h, h1, ↓reduceIte, h2, pow_succ]
    omega

lemma Mseq_unbounded (n : ℕ) : ∃ k : ℕ, n ≤ 1850 * (Mseq k) ^ 2 := by
  refine ⟨2 * n, ?_⟩
  have hM : Mseq (2 * n) = 24 * 2 ^ n := by
    unfold Mseq
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp only [h1, ↓reduceIte, h2]
  have hpow : n < 2 ^ n := Nat.lt_two_pow_self
  have hle : n ≤ Mseq (2 * n) := by omega
  nlinarith

lemma exists_coprime_42_gap (x : ℕ) : ∃ d : ℕ, d ≤ 5 ∧ Nat.Coprime (x + d) 42 := by
  have hmod : ∀ r : Fin 42, ∃ d : Fin 6, Nat.Coprime (r.val + d.val) 42 := by decide
  obtain ⟨d, hd⟩ := hmod ⟨x % 42, Nat.mod_lt x (by omega)⟩
  refine ⟨d.val, by omega, ?_⟩
  have hEq : (x + d.val) % 42 = (x % 42 + d.val) % 42 := by omega
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec, hEq, ← Nat.gcd_rec, Nat.gcd_comm]
  exact (Nat.coprime_iff_gcd_eq_one).mp hd

lemma mirror_coprime {m t : ℕ}
    (hm_even : m % 2 = 0) (hm_div3 : m % 3 = 0)
    (hm_pf : ∀ p, Nat.Prime p → p ∣ m → p = 2 ∨ p = 3)
    (ht_lo : 11 * m ≤ t) (ht_cop : Nat.Coprime t 42) :
    Nat.Coprime ((2 * t + 3 * m) * (2 * t + 3 * m) - (2 * t - 3 * m) * (2 * t - 3 * m))
      (Int.natAbs (((3 * t - 4 * m : ℕ) : ℤ) * (3 * t - 4 * m : ℕ) -
        ((2 * t + 3 * m : ℕ) : ℤ) * (2 * t + 3 * m : ℕ))) := by
  have hD : (2 * t + 3 * m) * (2 * t + 3 * m) - (2 * t - 3 * m) * (2 * t - 3 * m) = 24 * t * m := by
    have h3m : 3 * m ≤ 2 * t := by omega
    have hle : (2 * t - 3 * m) * (2 * t - 3 * m) ≤ (2 * t + 3 * m) * (2 * t + 3 * m) :=
      Nat.mul_le_mul (by omega) (by omega)
    zify [h3m, hle]
    ring
  have he2_le_b : 2 * t + 3 * m ≤ 3 * t - 4 * m := by omega
  have hsq_le : (2 * t + 3 * m) * (2 * t + 3 * m) ≤ (3 * t - 4 * m) * (3 * t - 4 * m) :=
    Nat.mul_le_mul he2_le_b he2_le_b
  have hK_abs :
      Int.natAbs (((3 * t - 4 * m : ℕ) : ℤ) * (3 * t - 4 * m : ℕ) -
        ((2 * t + 3 * m : ℕ) : ℤ) * (2 * t + 3 * m : ℕ)) =
      (3 * t - 4 * m) * (3 * t - 4 * m) - (2 * t + 3 * m) * (2 * t + 3 * m) := by
    have hEq : (((3 * t - 4 * m : ℕ) : ℤ) * (3 * t - 4 * m : ℕ) -
        ((2 * t + 3 * m : ℕ) : ℤ) * (2 * t + 3 * m : ℕ)) =
        (((3 * t - 4 * m) * (3 * t - 4 * m) - (2 * t + 3 * m) * (2 * t + 3 * m) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hsq_le]
      push_cast
      rfl
    rw [hEq, Int.natAbs_natCast]
  rw [hD, hK_abs]
  set K : ℕ := (3 * t - 4 * m) * (3 * t - 4 * m) - (2 * t + 3 * m) * (2 * t + 3 * m)
  have hK_eq : K + 36 * (t * m) = 5 * (t * t) + 7 * (m * m) := by
    have h4m : 4 * m ≤ 3 * t := by omega
    dsimp only [K]
    zify [h4m, hsq_le]
    ring
  have ht_odd : t % 2 = 1 := by
    by_contra h
    have h2t : 2 ∣ t := by omega
    have h2g : 2 ∣ Nat.gcd t 42 := Nat.dvd_gcd h2t (by decide)
    rw [ht_cop.gcd_eq_one] at h2g
    omega
  have ht_not3 : t % 3 ≠ 0 := by
    intro h
    have h3t : 3 ∣ t := by omega
    have h3g : 3 ∣ Nat.gcd t 42 := Nat.dvd_gcd h3t (by decide)
    rw [ht_cop.gcd_eq_one] at h3g
    omega
  have ht_not7 : ¬ 7 ∣ t := by
    intro h7t
    have h7g : 7 ∣ Nat.gcd t 42 := Nat.dvd_gcd h7t (by decide)
    rw [ht_cop.gcd_eq_one] at h7g
    omega
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp1 : p ∣ 24 * t * m := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hp2 : p ∣ K := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  by_cases hp2eq : p = 2
  · subst hp2eq
    have ht2 : (t * t) % 2 = 1 := by rw [Nat.mul_mod, ht_odd]
    have hm2 : (m * m) % 2 = 0 := by rw [Nat.mul_mod, hm_even]
    have hK_even : K % 2 = 0 := by omega
    omega
  · by_cases hp3eq : p = 3
    · subst hp3eq
      have ht2 : (t * t) % 3 = 1 := by
        rw [Nat.mul_mod]
        have : t % 3 = 1 ∨ t % 3 = 2 := by omega
        rcases this with h | h <;> simp [h]
      have hm2 : (m * m) % 3 = 0 := by rw [Nat.mul_mod, hm_div3]
      have hK_div3 : K % 3 = 0 := by omega
      omega
    · have hpt : p ∣ t := by
        rcases hp.dvd_mul.mp hp1 with h24t | hm
        · rcases hp.dvd_mul.mp h24t with h24 | ht
          · exfalso
            have h24' : p ∣ 3 * 2 ^ 3 := by simpa using h24
            rcases hp.dvd_mul.mp h24' with h3 | h2
            · exact hp3eq ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
            · exact hp2eq ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
          · exact ht
        · exfalso
          rcases hm_pf p hp hm with rfl | rfl
          · exact hp2eq rfl
          · exact hp3eq rfl
      have hp7m2 : p ∣ 7 * (m * m) := by
        have hsum : p ∣ K + 36 * (t * m) :=
          dvd_add hp2 (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpt m) 36)
        rw [hK_eq] at hsum
        have h5t2 : p ∣ 5 * (t * t) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpt t) 5
        exact (Nat.dvd_add_right h5t2).mp hsum
      have hp7 : p ∣ 7 := by
        rcases hp.dvd_mul.mp hp7m2 with h7 | hm2
        · exact h7
        · exfalso
          have hm : p ∣ m := by
            rcases hp.dvd_mul.mp hm2 with h | h <;> exact h
          rcases hm_pf p hp hm with rfl | rfl
          · exact hp2eq rfl
          · exact hp3eq rfl
      have hp7eq : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp7
      subst hp7eq
      exact ht_not7 hpt

lemma mirror_mod5_replenish (t m : ℕ) (hm5 : m % 5 ≠ 0) (ht_lo : 11 * m ≤ t) :
    let b := 3 * t - 4 * m
    let c := 3 * t + 4 * m
    let e1 := 2 * t - 3 * m
    let e2 := 2 * t + 3 * m
    b % 5 = 0 ∨
    ((b % 5 = 1 ∨ b % 5 = 4) ∧
      ((c % 5 = 2 ∨ c % 5 = 3) ∨ (e1 % 5 = 2 ∨ e1 % 5 = 3) ∨ (e2 % 5 = 2 ∨ e2 % 5 = 3))) ∨
    ((b % 5 = 2 ∨ b % 5 = 3) ∧
      ((c % 5 = 1 ∨ c % 5 = 4) ∨ (e1 % 5 = 1 ∨ e1 % 5 = 4) ∨ (e2 % 5 = 1 ∨ e2 % 5 = 4))) := by
  dsimp only
  have hfin : ∀ r s : Fin 5, s.val ≠ 0 →
      let b := (3 * r.val + s.val) % 5
      let c := (3 * r.val + 4 * s.val) % 5
      let e1 := (2 * r.val + 2 * s.val) % 5
      let e2 := (2 * r.val + 3 * s.val) % 5
      b = 0 ∨
      ((b = 1 ∨ b = 4) ∧
        ((c = 2 ∨ c = 3) ∨ (e1 = 2 ∨ e1 = 3) ∨ (e2 = 2 ∨ e2 = 3))) ∨
      ((b = 2 ∨ b = 3) ∧
        ((c = 1 ∨ c = 4) ∨ (e1 = 1 ∨ e1 = 4) ∨ (e2 = 1 ∨ e2 = 4))) := by decide
  have hb : (3 * t - 4 * m) % 5 = (3 * (t % 5) + m % 5) % 5 := by omega
  have hc : (3 * t + 4 * m) % 5 = (3 * (t % 5) + 4 * (m % 5)) % 5 := by omega
  have he1 : (2 * t - 3 * m) % 5 = (2 * (t % 5) + 2 * (m % 5)) % 5 := by omega
  have he2 : (2 * t + 3 * m) % 5 = (2 * (t % 5) + 3 * (m % 5)) % 5 := by omega
  rw [hb, hc, he1, he2]
  exact hfin ⟨t % 5, Nat.mod_lt t (by omega)⟩ ⟨m % 5, Nat.mod_lt m (by omega)⟩ hm5

def nLo (m t : ℕ) : ℕ :=
  (3 * t - 4 * m) ^ 2 - (3 * t - 4 * m) ^ 2 / 18

def nHi (m t : ℕ) : ℕ :=
  (3 * t - 4 * m) ^ 2 - max 55 ((4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2)

lemma mirror_step_for_t {m t n : ℕ}
    (hm24 : 24 ≤ m) (hm_even : m % 2 = 0) (hm_div3 : m % 3 = 0) (hm_not5 : m % 5 ≠ 0)
    (hm_pf : ∀ p, Nat.Prime p → p ∣ m → p = 2 ∨ p = 3)
    (ht_lo : 11 * m ≤ t) (ht_hi : t ≤ 16 * m) (ht_cop : Nat.Coprime t 42)
    (hn_lo : nLo m t ≤ n) (hn_hi : n ≤ nHi m t) :
    ∃ L b : ℕ, 55 ≤ L ∧ L < n ∧ b % 2 = 1 ∧ 18 * L ≤ b * b ∧ n = b * b - L ∧
      ∃ c2 : IntervalCycle L n,
        (∀ u, L ≤ u → u ≤ n → HasEdge c2 u (b * b - u)) ∧
        (b % 5 = 0 ∨
         ((b % 5 = 1 ∨ b % 5 = 4) ∧ HasMod5Class c2 2) ∨
         ((b % 5 = 2 ∨ b % 5 = 3) ∧ HasMod5Class c2 1)) := by
  let b : ℕ := 3 * t - 4 * m
  let c : ℕ := 3 * t + 4 * m
  let e1 : ℕ := 2 * t - 3 * m
  let e2 : ℕ := 2 * t + 3 * m
  have h4m : 4 * m ≤ 3 * t := by omega
  have h3m : 3 * m ≤ 2 * t := by omega
  have hb_z : (b : ℤ) = 3 * (t : ℤ) - 4 * (m : ℤ) := by dsimp only [b]; omega
  have hc_z : (c : ℤ) = 3 * (t : ℤ) + 4 * (m : ℤ) := by dsimp only [c]; omega
  have he1_z : (e1 : ℤ) = 2 * (t : ℤ) - 3 * (m : ℤ) := by dsimp only [e1]; omega
  have he2_z : (e2 : ℤ) = 2 * (t : ℤ) + 3 * (m : ℤ) := by dsimp only [e2]; omega
  have hb_ge : 29 * m ≤ b := by omega
  have hb2_eq_pow : b * b = (3 * t - 4 * m) ^ 2 := by dsimp only [b]; ring
  let L : ℕ := b * b - n
  have hL_ge_55 : 55 ≤ L := by
    dsimp only [nHi] at hn_hi
    have hmax : 55 ≤ max 55 ((4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2) := le_max_left _ _
    have hb2_big : 55 ≤ b * b := by nlinarith
    omega
  have h18L : 18 * L ≤ b * b := by
    dsimp only [nLo] at hn_lo
    have hL_le : L ≤ b * b / 18 := by omega
    omega
  have hn_eq : n = b * b - L := by omega
  have hL_lt_n : L < n := by omega
  have ht_odd : t % 2 = 1 := by
    by_contra h
    have h2t : 2 ∣ t := by omega
    have h2g : 2 ∣ Nat.gcd t 42 := Nat.dvd_gcd h2t (by decide)
    rw [ht_cop.gcd_eq_one] at h2g
    omega
  have hb_odd : b % 2 = 1 := by omega
  have hc_odd : c % 2 = 1 := by omega
  have hbc : b < c := by omega
  have he : e1 < e2 := by omega
  have hdioph : c * c - b * b = 2 * (e2 * e2 - e1 * e1) := by
    have hle1 : b * b ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
    have hle2 : e1 * e1 ≤ e2 * e2 := Nat.mul_le_mul (by omega) (by omega)
    zify [hle1, hle2]
    rw [hb_z, hc_z, he1_z, he2_z]
    ring
  have hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2)) :=
    mirror_coprime hm_even hm_div3 hm_pf ht_lo ht_cop
  have hD_eq : e2 * e2 - e1 * e1 = 24 * t * m := by
    have hle : e1 * e1 ≤ e2 * e2 := Nat.mul_le_mul (by omega) (by omega)
    zify [hle]
    rw [he1_z, he2_z]
    ring
  have ht_lo_z : 11 * (m : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht_lo
  have hm24_z : (24 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm24
  have h2e1_ge_e2 : e2 * e2 ≤ 2 * (e1 * e1) := by
    zify
    rw [he1_z, he2_z]
    nlinarith only [ht_lo_z, hm24_z]
  have hcond1 : 2 * L + e2 * e2 ≤ 2 * (e1 * e1) := by
    have hmul : b * b + 9 * (e2 * e2) ≤ 18 * (e1 * e1) := by
      zify
      rw [hb_z, he1_z, he2_z]
      nlinarith only [ht_lo_z, hm24_z]
    omega
  have hcond2 : 4 * t * t + 9 * m * m + 2 ≤ 60 * t * m + 2 * L := by
    dsimp only [nHi] at hn_hi
    have hmax : (4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2 ≤
        max 55 ((4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2) := le_max_right _ _
    have hle_b2 : max 55 ((4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2) ≤ b * b := by
      apply max_le
      · nlinarith only [hb_ge, hm24]
      · have hsub : 4 * t * t + 9 * m * m + 3 - 60 * t * m ≤ 2 * (b * b) := by
          by_cases hneg : 60 * t * m ≤ 4 * t * t + 9 * m * m + 3
          · zify [hneg]
            rw [hb_z]
            nlinarith only [ht_lo_z, hm24_z]
          · omega
        omega
    have hL_ge : (4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2 ≤ L := by omega
    omega
  have hcond2' : 2 * (e1 * e1) + 1 < 2 * L + e2 * e2 + (e2 * e2 - e1 * e1) := by
    have hle : e1 * e1 ≤ e2 * e2 := Nat.mul_le_mul (by omega) (by omega)
    zify [hle]
    rw [he1_z, he2_z]
    have hcond2_z : 4 * (t : ℤ) * t + 9 * (m : ℤ) * m + 2 ≤ 60 * (t : ℤ) * m + 2 * (L : ℤ) := by
      exact_mod_cast hcond2
    linarith
  let w1 : ℕ := 2 * (e1 * e1) + 1 - e2 * e2 - 2 * L
  have h2e12 : 2 * e1 * e1 = 2 * (e1 * e1) := by ring
  have hw1_lo : 1 ≤ w1 := by omega
  have hw1_hi : w1 < e2 * e2 - e1 * e1 := by omega
  have hL_eq : 2 * L + w1 + e2 * e2 = 2 * e1 * e1 + 1 := by omega
  have hL_hi : 2 * L + c * c + 3 ≤ 2 * b * b := by
    have h2b2 : 2 * b * b = 2 * (b * b) := by ring
    have hmul : 9 * (c * c) + 27 ≤ 17 * (b * b) := by
      zify
      rw [hb_z, hc_z]
      nlinarith only [ht_lo_z, hm24_z]
    omega
  obtain ⟨cyc, hbm, hcm, he1m, he2m⟩ := mirror_4sq_cycle
    hb_odd hc_odd hbc he hdioph hcop hw1_lo hw1_hi hL_eq (by omega) hL_hi hn_eq
  refine ⟨L, b, hL_ge_55, hL_lt_n, hb_odd, h18L, hn_eq, cyc, hbm, ?_⟩
  have hmod5 := mirror_mod5_replenish t m hm_not5 ht_lo
  rcases hmod5 with hb0 | ⟨hb14, hhit2⟩ | ⟨hb23, hhit1⟩
  · exact Or.inl hb0
  · refine Or.inr (Or.inl ⟨hb14, ?_⟩)
    rcases hhit2 with hc2 | he12 | he22
    · rcases hcm with ⟨u, _, _, hu⟩
      exact hasMod5Class_of_hasEdge (by omega) hu (by simpa using hc2)
    · rcases he1m with ⟨u, _, _, hu⟩
      exact hasMod5Class_of_hasEdge (by omega) hu (by simpa using he12)
    · rcases he2m with ⟨u, _, _, hu⟩
      exact hasMod5Class_of_hasEdge (by omega) hu (by simpa using he22)
  · refine Or.inr (Or.inr ⟨hb23, ?_⟩)
    rcases hhit1 with hc1 | he11 | he21
    · rcases hcm with ⟨u, _, _, hu⟩
      exact hasMod5Class_of_hasEdge (by omega) hu (by simpa using hc1)
    · rcases he1m with ⟨u, _, _, hu⟩
      exact hasMod5Class_of_hasEdge (by omega) hu (by simpa using he11)
    · rcases he2m with ⟨u, _, _, hu⟩
      exact hasMod5Class_of_hasEdge (by omega) hu (by simpa using he21)

lemma mirror_overlap {m t1 t2 : ℕ}
    (hm24 : 24 ≤ m) (ht1_lo : 11 * m ≤ t1) (ht12 : t1 ≤ t2) (ht2_hi : t2 ≤ 16 * m)
    (hstep : t2 ≤ t1 + 6) :
    nLo m t2 ≤ nHi m t1 + 1 := by
  dsimp only [nLo, nHi]
  have ht1_hi : t1 ≤ 16 * m := by omega
  have h4m1 : 4 * m ≤ 3 * t1 := by omega
  have h4m2 : 4 * m ≤ 3 * t2 := by omega
  have hmain : 17 * (3 * t2 - 4 * m) ^ 2 + 17 +
      18 * max 55 ((4 * t1 * t1 + 9 * m * m + 3 - 60 * t1 * m) / 2) ≤
      18 * (3 * t1 - 4 * m) ^ 2 := by
    have hb2_le : 3 * t2 - 4 * m ≤ (3 * t1 - 4 * m) + 18 := by omega
    have hb2sq : (3 * t2 - 4 * m) ^ 2 ≤ ((3 * t1 - 4 * m) + 18) ^ 2 :=
      Nat.pow_le_pow_left hb2_le 2
    by_cases hcase : (4 * t1 * t1 + 9 * m * m + 3 - 60 * t1 * m) / 2 ≤ 55
    · rw [max_eq_left hcase]
      have hquad : 17 * ((3 * t1 - 4 * m) + 18) ^ 2 + 17 + 18 * 55 ≤
          18 * (3 * t1 - 4 * m) ^ 2 := by
        zify [h4m1]
        nlinarith
      omega
    · rw [max_eq_right (by omega : 55 ≤ (4 * t1 * t1 + 9 * m * m + 3 - 60 * t1 * m) / 2)]
      have hpos : 60 * t1 * m ≤ 4 * t1 * t1 + 9 * m * m + 3 := by omega
      have hdiv2 : 2 * ((4 * t1 * t1 + 9 * m * m + 3 - 60 * t1 * m) / 2) ≤
          4 * t1 * t1 + 9 * m * m + 3 - 60 * t1 * m := Nat.mul_div_le _ 2
      have hquad : 17 * ((3 * t1 - 4 * m) + 18) ^ 2 + 17 +
          9 * (4 * t1 * t1 + 9 * m * m + 3 - 60 * t1 * m) ≤
          18 * (3 * t1 - 4 * m) ^ 2 := by
        zify [h4m1, hpos]
        have h1 : (0 : ℤ) ≤ (16 * (m : ℤ) - t1) * ((t1 : ℤ) - 11 * m) :=
          mul_nonneg (by omega) (by omega)
        have h2 : (0 : ℤ) ≤ (m : ℤ) * (16 * (m : ℤ) - t1) :=
          mul_nonneg (by omega) (by omega)
        have h3 : (0 : ℤ) ≤ ((m : ℤ) - 24) * (m : ℤ) :=
          mul_nonneg (by omega) (by omega)
        nlinarith
      omega
  omega

lemma mirror_upper_endpoint {m t : ℕ}
    (hm24 : 24 ≤ m) (ht_lo : 16 * m - 5 ≤ t) (ht_hi : t ≤ 16 * m) :
    1850 * m ^ 2 ≤ nHi m t := by
  dsimp only [nHi]
  have h4m : 4 * m ≤ 3 * t := by omega
  have h1 : 1850 * m ^ 2 + max 55 ((4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2) ≤
      (3 * t - 4 * m) ^ 2 := by
    by_cases hcase : (4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2 ≤ 55
    · rw [max_eq_left hcase]
      zify [h4m]
      have h3 : (0 : ℤ) ≤ ((m : ℤ) - 24) * (m : ℤ) := mul_nonneg (by omega) (by omega)
      have h4 : (0 : ℤ) ≤ ((t : ℤ) - (16 * m - 5)) * ((t : ℤ) + (16 * m - 5)) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    · rw [max_eq_right (by omega : 55 ≤ (4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2)]
      have hpos : 60 * t * m ≤ 4 * t * t + 9 * m * m + 3 := by omega
      have hdiv2 : 2 * ((4 * t * t + 9 * m * m + 3 - 60 * t * m) / 2) ≤
          4 * t * t + 9 * m * m + 3 - 60 * t * m := Nat.mul_div_le _ 2
      have hquad : 3700 * m ^ 2 + (4 * t * t + 9 * m * m + 3 - 60 * t * m) ≤
          2 * (3 * t - 4 * m) ^ 2 := by
        zify [h4m, hpos]
        have h3 : (0 : ℤ) ≤ ((m : ℤ) - 24) * (m : ℤ) := mul_nonneg (by omega) (by omega)
        have h4 : (0 : ℤ) ≤ ((t : ℤ) - (16 * m - 5)) * ((t : ℤ) + (16 * m - 5)) :=
          mul_nonneg (by omega) (by omega)
        have h5 : (0 : ℤ) ≤ (m : ℤ) * ((t : ℤ) - (16 * m - 5)) :=
          mul_nonneg (by omega) (by omega)
        nlinarith
      omega
  omega

lemma mirror_lower_endpoint {m t : ℕ}
    (hm36 : 36 ≤ m) (ht_lo : 11 * m ≤ t) (ht_hi : t ≤ 11 * m + 5) :
    nLo m t ≤ 820 * m ^ 2 := by
  dsimp only [nLo]
  have hb_hi : 3 * t - 4 * m ≤ 29 * m + 15 := by omega
  have hquad : 17 * (3 * t - 4 * m) ^ 2 + 17 ≤ 18 * (820 * m ^ 2) := by
    have hb2 : (3 * t - 4 * m) ^ 2 ≤ (29 * m + 15) ^ 2 := Nat.pow_le_pow_left hb_hi 2
    nlinarith
  omega

lemma exists_good_t {m n t_start t_end : ℕ}
    (hm24 : 24 ≤ m)
    (hts_lo : 11 * m ≤ t_start) (hts_le : t_start ≤ t_end) (hte_hi : t_end ≤ 16 * m)
    (hts_cop : Nat.Coprime t_start 42) (hte_cop : Nat.Coprime t_end 42)
    (hn_lo : nLo m t_start ≤ n) (hn_hi : n ≤ nHi m t_end) :
    ∃ t : ℕ, 11 * m ≤ t ∧ t ≤ 16 * m ∧ Nat.Coprime t 42 ∧ nLo m t ≤ n ∧ n ≤ nHi m t := by
  classical
  have hex : ∃ t : ℕ, t_start ≤ t ∧ Nat.Coprime t 42 ∧ n ≤ nHi m t :=
    ⟨t_end, hts_le, hte_cop, hn_hi⟩
  let t : ℕ := Nat.find hex
  have ht_spec : t_start ≤ t ∧ Nat.Coprime t 42 ∧ n ≤ nHi m t := Nat.find_spec hex
  have ht_le_end : t ≤ t_end := Nat.find_min' hex ⟨hts_le, hte_cop, hn_hi⟩
  refine ⟨t, by omega, by omega, ht_spec.2.1, ?_, ht_spec.2.2⟩
  by_cases heq : t = t_start
  · rw [heq]
    exact hn_lo
  · have hlt : t_start < t := by omega
    have hex_prev : ∃ t1 : ℕ, t_start ≤ t1 ∧ t1 < t ∧ t ≤ t1 + 6 ∧ Nat.Coprime t1 42 := by
      by_cases hclose : t ≤ t_start + 6
      · exact ⟨t_start, le_rfl, hlt, hclose, hts_cop⟩
      · obtain ⟨d, hd5, hdcop⟩ := exists_coprime_42_gap (t - 6)
        refine ⟨t - 6 + d, by omega, by omega, by omega, hdcop⟩
    obtain ⟨t1, ht1_ge, ht1_lt, ht1_step, ht1_cop⟩ := hex_prev
    have hnotP : ¬ (t_start ≤ t1 ∧ Nat.Coprime t1 42 ∧ n ≤ nHi m t1) :=
      Nat.find_min hex ht1_lt
    have hn_gt : nHi m t1 + 1 ≤ n := by
      have : ¬ (n ≤ nHi m t1) := fun h => hnotP ⟨ht1_ge, ht1_cop, h⟩
      omega
    have hov : nLo m t ≤ nHi m t1 + 1 :=
      mirror_overlap hm24 (by omega) (by omega) (by omega) ht1_step
    omega

/-- Closed-form infinite mirror coverage for every `n ≥ 461457`. -/
theorem infinite_mirror_step (n : ℕ) (hn : 461457 ≤ n) :
    ∃ L b : ℕ, 55 ≤ L ∧ L < n ∧ b % 2 = 1 ∧ 18 * L ≤ b * b ∧ n = b * b - L ∧
      ∃ c2 : IntervalCycle L n,
        (∀ u, L ≤ u → u ≤ n → HasEdge c2 u (b * b - u)) ∧
        (b % 5 = 0 ∨
         ((b % 5 = 1 ∨ b % 5 = 4) ∧ HasMod5Class c2 2) ∨
         ((b % 5 = 2 ∨ b % 5 = 3) ∧ HasMod5Class c2 1)) := by
  classical
  let k : ℕ := Nat.find (Mseq_unbounded n)
  let m : ℕ := Mseq k
  have hk_ub : n ≤ 1850 * m ^ 2 := Nat.find_spec (Mseq_unbounded n)
  by_cases hk0 : k = 0
  · have hm24 : m = 24 := by
      dsimp only [m]
      rw [hk0]
      decide
    have hn_hi : n ≤ nHi m 379 := by
      have : 1850 * 24 ^ 2 ≤ nHi 24 379 := by decide
      rw [hm24] at hk_ub ⊢
      omega
    have hn_lo : nLo m 265 ≤ n := by
      have : nLo 24 265 = 461457 := by decide
      rw [hm24]
      omega
    obtain ⟨t, ht_lo, ht_hi, ht_cop, htn_lo, htn_hi⟩ :=
      exists_good_t (m := m) (n := n) (t_start := 265) (t_end := 379)
        (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) hn_lo hn_hi
    exact mirror_step_for_t (Mseq_ge_24 k) (Mseq_even k) (Mseq_div3 k) (Mseq_not_div5 k)
      (fun p hp hd => Mseq_prime_factors k hp hd) ht_lo ht_hi ht_cop htn_lo htn_hi
  · have hk_ge1 : 1 ≤ k := by omega
    have hm36 : 36 ≤ m := Mseq_ge_36 hk_ge1
    have hprev : 1850 * (Mseq (k - 1)) ^ 2 < n := by
      have hnot := Nat.find_min (Mseq_unbounded n) (show k - 1 < k by omega)
      omega
    have hstep : 2 * m ≤ 3 * Mseq (k - 1) := by
      have hEq : k - 1 + 1 = k := by omega
      have h := Mseq_step (k - 1)
      rwa [hEq] at h
    have hn_lb : 820 * m ^ 2 < n := by
      nlinarith
    obtain ⟨d1, hd1, hcop1⟩ := exists_coprime_42_gap (11 * m)
    obtain ⟨d2, hd2, hcop2⟩ := exists_coprime_42_gap (16 * m - 5)
    let t_start := 11 * m + d1
    let t_end := 16 * m - 5 + d2
    have hts_lo : nLo m t_start ≤ n := by
      have h := mirror_lower_endpoint hm36 (t := t_start) (by omega) (by omega)
      omega
    have hte_hi : n ≤ nHi m t_end := by
      have h := mirror_upper_endpoint (by omega : 24 ≤ m) (t := t_end) (by omega) (by omega)
      omega
    obtain ⟨t, ht_lo, ht_hi, ht_cop, htn_lo, htn_hi⟩ :=
      exists_good_t (m := m) (n := n) (t_start := t_start) (t_end := t_end)
        (by omega) (by omega) (by omega) (by omega) hcop1 hcop2 hts_lo hte_hi
    exact mirror_step_for_t (Mseq_ge_24 k) (Mseq_even k) (Mseq_div3 k) (Mseq_not_div5 k)
      (fun p hp hd => Mseq_prime_factors k hp hd) ht_lo ht_hi ht_cop htn_lo htn_hi

end MSE2637546.S2

namespace MSE2637546.S3

open MSE2637546

/-! ### Part 1: Fast Bitmask Verifiers for Base Paths and Base Cycles -/

private lemma nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
private lemma nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
private lemma nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
private lemma nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl
private lemma nat_mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

private lemma nat_beq_true {a b : ℕ} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

private lemma nat_beq_false {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := by
  intro heq; subst heq; simp at h

private lemma nat_ble_false {a b : ℕ} (h : Nat.ble a b = false) : ¬ a ≤ b := by
  intro hle; rw [Nat.ble_eq.mpr hle] at h; cases h

private lemma nat_blt_false {a b : ℕ} (h : Nat.blt a b = false) : ¬ a < b := by
  intro hlt; rw [Nat.blt_eq.mpr hlt] at h; cases h

private lemma div_two_pow_add_eq {m e k : ℕ} (h0 : (m / 2 ^ e) % 2 = 0) :
    ((m + 2 ^ e) / 2 ^ k) % 2 = if k = e then 1 else (m / 2 ^ k) % 2 := by
  have hpe : 0 < 2 ^ e := Nat.pos_of_ne_zero (by positivity)
  have hpk : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
  by_cases hke : k = e
  · subst hke
    rw [if_pos rfl, Nat.add_div_right _ hpe]
    omega
  · rw [if_neg hke]
    by_cases hlt : k < e
    · have hpow : 2 ^ e = 2 ^ k * 2 ^ (e - k) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlt)]
      have heven : 2 ^ (e - k) % 2 = 0 := by
        have h1 : e - k = (e - k - 1) + 1 := by omega
        rw [h1, Nat.pow_succ]; omega
      rw [hpow, Nat.add_mul_div_left _ _ hpk]
      omega
    · have hgt : e < k := by omega
      have hpe1 : 0 < 2 ^ (e + 1) := Nat.pos_of_ne_zero (by positivity)
      have hdiv : m % 2 ^ (e + 1) < 2 ^ e := by
        have h1 : m = 2 ^ (e + 1) * (m / 2 ^ (e + 1)) + m % 2 ^ (e + 1) :=
          (Nat.div_add_mod m (2 ^ (e + 1))).symm
        have h2 : 2 ^ (e + 1) = 2 ^ e * 2 := Nat.pow_succ 2 e
        have h3 : m / 2 ^ e = 2 * (m / 2 ^ (e + 1)) + (m % 2 ^ (e + 1)) / 2 ^ e := by
          have hrew : 2 ^ (e + 1) * (m / 2 ^ (e + 1)) + m % 2 ^ (e + 1) =
              2 ^ e * (2 * (m / 2 ^ (e + 1))) + m % 2 ^ (e + 1) := by
            rw [h2]; ring
          calc m / 2 ^ e = (2 ^ e * (2 * (m / 2 ^ (e + 1))) + m % 2 ^ (e + 1)) / 2 ^ e := by
                rw [← hrew, ← h1]
            _ = 2 * (m / 2 ^ (e + 1)) + (m % 2 ^ (e + 1)) / 2 ^ e := Nat.mul_add_div hpe _ _
        have h4 : (m % 2 ^ (e + 1)) / 2 ^ e < 2 := by
          have hm_lt : m % 2 ^ (e + 1) < 2 ^ e * 2 := by rw [← h2]; exact Nat.mod_lt m hpe1
          exact Nat.div_lt_of_lt_mul (by linarith)
        rw [h3, Nat.mul_add_mod] at h0
        have h5 : (m % 2 ^ (e + 1)) / 2 ^ e = 0 := by
          generalize (m % 2 ^ (e + 1)) / 2 ^ e = q at h4 h0 ⊢
          omega
        have h6 := Nat.div_add_mod (m % 2 ^ (e + 1)) (2 ^ e)
        rw [h5, Nat.mul_zero, Nat.zero_add] at h6
        have h7 := Nat.mod_lt (m % 2 ^ (e + 1)) hpe
        omega
      have hsplit : 2 ^ k = 2 ^ (e + 1) * 2 ^ (k - (e + 1)) := by
        rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
      have hmod_lt : m % 2 ^ k + 2 ^ e < 2 ^ k := by
        have hm_lt : m % 2 ^ k < 2 ^ (e + 1) * 2 ^ (k - (e + 1)) := by
          rw [← hsplit]; exact Nat.mod_lt m hpk
        have hq_lt : (m % 2 ^ k) / 2 ^ (e + 1) < 2 ^ (k - (e + 1)) :=
          Nat.div_lt_of_lt_mul hm_lt
        have hrem_eq : (m % 2 ^ k) % 2 ^ (e + 1) = m % 2 ^ (e + 1) := by
          rw [hsplit, Nat.mod_mul_right_mod]
        have hdecomp := Nat.div_add_mod (m % 2 ^ k) (2 ^ (e + 1))
        rw [hrem_eq] at hdecomp
        have hq_le : (m % 2 ^ k) / 2 ^ (e + 1) + 1 ≤ 2 ^ (k - (e + 1)) := by omega
        have hmul : 2 ^ (e + 1) * ((m % 2 ^ k) / 2 ^ (e + 1) + 1) ≤ 2 ^ (e + 1) * 2 ^ (k - (e + 1)) :=
          Nat.mul_le_mul_left _ hq_le
        rw [← hsplit] at hmul
        have hpow2 : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by rw [Nat.pow_succ]; omega
        linarith
      have heq_div : (m + 2 ^ e) / 2 ^ k = m / 2 ^ k := by
        have h1 : m + 2 ^ e = 2 ^ k * (m / 2 ^ k) + (m % 2 ^ k + 2 ^ e) := by
          have := Nat.div_add_mod m (2 ^ k); omega
        rw [h1, Nat.mul_add_div hpk, Nat.div_eq_of_lt hmod_lt, Nat.add_zero]
      rw [heq_div]

/-- Exact 5-step binary search square checker for `m ≤ 1088`. -/
def isSq32 (m : ℕ) : Bool :=
  let r :=
    match Nat.ble 1024 m with
    | true => 32
    | false =>
      let r := match Nat.ble 256 m with | true => 16 | false => 0
      let r := match Nat.ble (Nat.mul (Nat.add r 8) (Nat.add r 8)) m with | true => Nat.add r 8 | false => r
      let r := match Nat.ble (Nat.mul (Nat.add r 4) (Nat.add r 4)) m with | true => Nat.add r 4 | false => r
      let r := match Nat.ble (Nat.mul (Nat.add r 2) (Nat.add r 2)) m with | true => Nat.add r 2 | false => r
      match Nat.ble (Nat.mul (Nat.add r 1) (Nat.add r 1)) m with | true => Nat.add r 1 | false => r
  Nat.beq (Nat.mul r r) m

private lemma isSq32_sound {m : ℕ} (h : isSq32 m = true) : IsSquare m := by
  unfold isSq32 at h
  dsimp only at h
  exact ⟨_, (nat_beq_true h).symm⟩

/-- Single-pass Hamiltonian path checker for `n ≤ 255` using a 256-bit `Nat` mask. -/
def checkPathGo (n : ℕ) (mask len : ℕ) : List ℕ → Bool
  | [] => false
  | [last] =>
      let p := Nat.pow 2 last
      match Nat.ble 1 last, Nat.ble last n, Nat.beq (Nat.mod (Nat.div mask p) 2) 0, Nat.beq (Nat.add len 1) n with
      | true, true, true, true => true
      | _, _, _, _ => false
  | a :: b :: rest =>
      let p := Nat.pow 2 a
      match Nat.ble 1 a, Nat.ble a n, Nat.beq (Nat.mod (Nat.div mask p) 2) 0, isSq32 (Nat.add a b) with
      | true, true, true, true => checkPathGo n (Nat.add mask p) (Nat.add len 1) (b :: rest)
      | _, _, _, _ => false

def checkHamPath (n : ℕ) (seq : List ℕ) : Bool :=
  match Nat.ble 1 n, Nat.ble n 255 with
  | true, true => checkPathGo n 0 0 seq
  | _, _ => false

private lemma checkPathGo_sound {n : ℕ} :
    ∀ (seq : List ℕ) (mask len : ℕ),
      checkPathGo n mask len seq = true →
      seq.Nodup ∧
      len + seq.length = n ∧
      (∀ x ∈ seq, 1 ≤ x ∧ x ≤ n ∧ (mask / 2 ^ x) % 2 = 0) ∧
      (∀ i (hi : i + 1 < seq.length), IsSquare (seq[i] + seq[i + 1])) := by
  intro seq
  induction seq with
  | nil => intro mask len h; simp [checkPathGo] at h
  | cons a tl ih =>
    intro mask len h
    cases tl with
    | nil =>
      simp only [checkPathGo] at h
      split at h <;> try cases h
      rename_i h1 h2 h3 h4
      have h1' : 1 ≤ a := Nat.ble_eq.mp h1
      have h2' : a ≤ n := Nat.ble_eq.mp h2
      have h3' : (mask / 2 ^ a) % 2 = 0 := nat_beq_true h3
      have h4' : len + 1 = n := nat_beq_true h4
      refine ⟨List.nodup_singleton a, by simp; omega, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨h1', h2', h3'⟩
      · intro i hi; simp at hi
    | cons b rest =>
      simp only [checkPathGo] at h
      split at h <;> try cases h
      rename_i h1 h2 h3 hsq
      have h1' : 1 ≤ a := Nat.ble_eq.mp h1
      have h2' : a ≤ n := Nat.ble_eq.mp h2
      have h3' : (mask / 2 ^ a) % 2 = 0 := nat_beq_true h3
      obtain ⟨hnodup, hlen, hmem, hadj⟩ := ih (mask + 2 ^ a) (len + 1) h
      have hnotmem : a ∉ b :: rest := by
        intro ha
        have hma := hmem a ha
        have hbit := div_two_pow_add_eq (m := mask) (e := a) (k := a) h3'
        rw [if_pos rfl] at hbit
        omega
      refine ⟨List.nodup_cons.mpr ⟨hnotmem, hnodup⟩, ?_, ?_, ?_⟩
      · simp only [List.length_cons] at hlen ⊢; omega
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx_tl
        · exact ⟨h1', h2', h3'⟩
        · have hne : x ≠ a := fun heq => hnotmem (heq ▸ hx_tl)
          have hmx := hmem x hx_tl
          have hbit := div_two_pow_add_eq (m := mask) (e := a) (k := x) h3'
          rw [if_neg hne] at hbit
          exact ⟨hmx.1, hmx.2.1, by omega⟩
      · intro i hi
        cases i with
        | zero => exact isSq32_sound hsq
        | succ i' =>
          simp only [List.getElem_cons_succ]
          exact hadj i' (by simp only [List.length_cons] at hi ⊢; omega)

theorem checkHamPath_sound {n : ℕ} {seq : List ℕ} (h : checkHamPath n seq = true) :
    HasHamPath n := by
  unfold checkHamPath at h
  split at h <;> try cases h
  obtain ⟨hnodup, hlen, hmem, hadj⟩ := checkPathGo_sound seq 0 0 h
  have hlen' : seq.length = n := by omega
  let f : Fin n → Fin n := fun i =>
    ⟨seq[i.val]'(by omega) - 1, by
      have hm := hmem (seq[i.val]'(by omega)) (List.getElem_mem _)
      omega⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    have hv : (f i).val = (f j).val := congrArg Fin.val hij
    simp only [f] at hv
    have hmi := hmem (seq[i.val]'(by omega)) (List.getElem_mem _)
    have hmj := hmem (seq[j.val]'(by omega)) (List.getElem_mem _)
    have hseq : seq[i.val]'(by omega) = seq[j.val]'(by omega) := by omega
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp hseq)
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  refine ⟨Equiv.ofBijective f hfbij, ?_⟩
  intro i j hij
  have hmi := hmem (seq[i.val]'(by omega)) (List.getElem_mem _)
  have hmj := hmem (seq[j.val]'(by omega)) (List.getElem_mem _)
  have hpi : (Equiv.ofBijective f hfbij i).val + 1 = seq[i.val]'(by omega) := by
    simp only [Equiv.ofBijective_apply, f]; omega
  have hpj : (Equiv.ofBijective f hfbij j).val + 1 = seq[j.val]'(by omega) := by
    simp only [Equiv.ofBijective_apply, f]; omega
  rw [hpi, hpj]
  have hjeq : seq[j.val]'(by omega) = seq[i.val + 1]'(by omega) := by congr 1
  rw [hjeq]
  exact hadj i.val (by omega)

/-- 3-bucket 256-bit mask predicate (for `x ≤ 767`, all exponents `< 256`). -/
def bit3 (m0 m1 m2 x : ℕ) : ℕ :=
  if x ≤ 255 then (m0 / 2 ^ x) % 2
  else if x ≤ 511 then (m1 / 2 ^ (x - 256)) % 2
  else (m2 / 2 ^ (x - 512)) % 2

/-- Pure specification of cyclic edge-sum count along a non-empty list. -/
def countCyclic (first sq : ℕ) : List ℕ → ℕ
  | [] => 0
  | [last] => if last + first = sq then 1 else 0
  | a :: b :: rest => (if a + b = sq then 1 else 0) + countCyclic first sq (b :: rest)

/-- Fast single-pass base-cycle verifier using 3 buckets of `< 256`-bit GMP masks. -/
def checkCycleFastGo (n first : ℕ) (m0 m1 m2 c16 c25 c36 c49 len : ℕ) : List ℕ → Bool
  | [] => false
  | [last] =>
      let okBit :=
        match Nat.ble last 255 with
        | true => Nat.beq (Nat.mod (Nat.div m0 (Nat.pow 2 last)) 2) 0
        | false =>
          match Nat.ble last 511 with
          | true => Nat.beq (Nat.mod (Nat.div m1 (Nat.pow 2 (Nat.sub last 256))) 2) 0
          | false => Nat.beq (Nat.mod (Nat.div m2 (Nat.pow 2 (Nat.sub last 512))) 2) 0
      match Nat.ble 1 last, Nat.ble last n, okBit with
      | true, true, true =>
        let s := Nat.add last first
        match isSq32 s, Nat.beq (Nat.add len 1) n with
        | true, true =>
          Nat.ble 2 (match Nat.beq s 16 with | true => Nat.add c16 1 | false => c16) &&
          Nat.ble 4 (match Nat.beq s 25 with | true => Nat.add c25 1 | false => c25) &&
          Nat.ble 3 (match Nat.beq s 36 with | true => Nat.add c36 1 | false => c36) &&
          Nat.ble 5 (match Nat.beq s 49 with | true => Nat.add c49 1 | false => c49)
        | _, _ => false
      | _, _, _ => false
  | a :: b :: rest =>
      match Nat.ble 1 a, Nat.ble a n with
      | true, true =>
        let s := Nat.add a b
        match isSq32 s with
        | true =>
          let c16' := match Nat.beq s 16 with | true => Nat.add c16 1 | false => c16
          let c25' := match Nat.beq s 25 with | true => Nat.add c25 1 | false => c25
          let c36' := match Nat.beq s 36 with | true => Nat.add c36 1 | false => c36
          let c49' := match Nat.beq s 49 with | true => Nat.add c49 1 | false => c49
          match Nat.ble a 255 with
          | true =>
            let p := Nat.pow 2 a
            match Nat.beq (Nat.mod (Nat.div m0 p) 2) 0 with
            | true => checkCycleFastGo n first (Nat.add m0 p) m1 m2 c16' c25' c36' c49' (Nat.add len 1) (b :: rest)
            | false => false
          | false =>
            match Nat.ble a 511 with
            | true =>
              let p := Nat.pow 2 (Nat.sub a 256)
              match Nat.beq (Nat.mod (Nat.div m1 p) 2) 0 with
              | true => checkCycleFastGo n first m0 (Nat.add m1 p) m2 c16' c25' c36' c49' (Nat.add len 1) (b :: rest)
              | false => false
            | false =>
              let p := Nat.pow 2 (Nat.sub a 512)
              match Nat.beq (Nat.mod (Nat.div m2 p) 2) 0 with
              | true => checkCycleFastGo n first m0 m1 (Nat.add m2 p) c16' c25' c36' c49' (Nat.add len 1) (b :: rest)
              | false => false
        | false => false
      | _, _ => false

def checkBaseCycle (n : ℕ) (seq : List ℕ) : Bool :=
  match Nat.ble 2 n, Nat.ble n 767, seq with
  | true, true, a :: rest => checkCycleFastGo n a 0 0 0 0 0 0 0 0 (a :: rest)
  | _, _, _ => false

private lemma checkCycleFastGo_sound {n first : ℕ} :
    ∀ (seq : List ℕ) (m0 m1 m2 c16 c25 c36 c49 len : ℕ),
      checkCycleFastGo n first m0 m1 m2 c16 c25 c36 c49 len seq = true →
      seq.Nodup ∧
      len + seq.length = n ∧
      (∀ x ∈ seq, 1 ≤ x ∧ x ≤ n ∧ bit3 m0 m1 m2 x = 0) ∧
      (∀ i (hi : i < seq.length),
        IsSquare (seq[i] + if hlt : i + 1 < seq.length then seq[i + 1] else first)) ∧
      2 ≤ c16 + countCyclic first 16 seq ∧
      4 ≤ c25 + countCyclic first 25 seq ∧
      3 ≤ c36 + countCyclic first 36 seq ∧
      5 ≤ c49 + countCyclic first 49 seq := by
  intro seq
  induction seq with
  | nil => intro m0 m1 m2 c16 c25 c36 c49 len h; simp [checkCycleFastGo] at h
  | cons a tl ih =>
    intro m0 m1 m2 c16 c25 c36 c49 len h
    cases tl with
    | nil =>
      simp only [checkCycleFastGo] at h
      split at h <;> try cases h
      rename_i h1 h2 hbit
      split at h <;> try cases h
      rename_i hsq hlen
      have h1' : 1 ≤ a := Nat.ble_eq.mp h1
      have h2' : a ≤ n := Nat.ble_eq.mp h2
      have hlen' : len + 1 = n := nat_beq_true hlen
      have hbit0 : bit3 m0 m1 m2 a = 0 := by
        unfold bit3
        split_ifs with ha1 ha2
        · have hb : Nat.ble a 255 = true := Nat.ble_eq.mpr ha1
          simp only [hb] at hbit; exact nat_beq_true hbit
        · have hb1 : Nat.ble a 255 = false := by
            cases h' : Nat.ble a 255 with | false => rfl | true => exfalso; exact ha1 (Nat.ble_eq.mp h')
          have hb2 : Nat.ble a 511 = true := Nat.ble_eq.mpr ha2
          simp only [hb1, hb2] at hbit; exact nat_beq_true hbit
        · have hb1 : Nat.ble a 255 = false := by
            cases h' : Nat.ble a 255 with | false => rfl | true => exfalso; exact ha1 (Nat.ble_eq.mp h')
          have hb2 : Nat.ble a 511 = false := by
            cases h' : Nat.ble a 511 with | false => rfl | true => exfalso; exact ha2 (Nat.ble_eq.mp h')
          simp only [hb1, hb2] at hbit; exact nat_beq_true hbit
      simp only [Bool.and_eq_true, Nat.ble_eq] at h
      have hcnt : ∀ (sq c k : ℕ),
          k ≤ (match Nat.beq (Nat.add a first) sq with | true => Nat.add c 1 | false => c) →
          k ≤ c + countCyclic first sq [a] := by
        intro sq c k hk
        simp only [countCyclic]
        cases hq : Nat.beq (Nat.add a first) sq with
        | true =>
          simp only [hq] at hk
          have heq : a + first = sq := nat_beq_true hq
          rw [if_pos heq]; exact hk
        | false =>
          simp only [hq] at hk
          have hne : a + first ≠ sq := nat_beq_false hq
          rw [if_neg hne]; omega
      refine ⟨List.nodup_singleton a, by simp; omega, ?_, ?_,
        hcnt 16 c16 2 h.1.1.1, hcnt 25 c25 4 h.1.1.2, hcnt 36 c36 3 h.1.2, hcnt 49 c49 5 h.2⟩
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact ⟨h1', h2', hbit0⟩
      · intro i hi
        have hi0 : i = 0 := by simp at hi; omega
        subst hi0
        simp only [List.length_singleton, Nat.zero_add, lt_self_iff_false, ↓reduceDIte,
          List.getElem_cons_zero]
        exact isSq32_sound hsq
    | cons b rest =>
      simp only [checkCycleFastGo] at h
      split at h <;> try cases h
      rename_i h1 h2
      split at h <;> try cases h
      rename_i hsq
      have h1' : 1 ≤ a := Nat.ble_eq.mp h1
      have h2' : a ≤ n := Nat.ble_eq.mp h2
      have hstep : ∃ m0' m1' m2',
          bit3 m0 m1 m2 a = 0 ∧
          bit3 m0' m1' m2' a = 1 ∧
          (∀ x, x ≠ a → bit3 m0' m1' m2' x = bit3 m0 m1 m2 x) ∧
          checkCycleFastGo n first m0' m1' m2'
            (match Nat.beq (Nat.add a b) 16 with | true => Nat.add c16 1 | false => c16)
            (match Nat.beq (Nat.add a b) 25 with | true => Nat.add c25 1 | false => c25)
            (match Nat.beq (Nat.add a b) 36 with | true => Nat.add c36 1 | false => c36)
            (match Nat.beq (Nat.add a b) 49 with | true => Nat.add c49 1 | false => c49)
            (len + 1) (b :: rest) = true := by
        split at h
        · rename_i ha1
          have ha1' : a ≤ 255 := Nat.ble_eq.mp ha1
          split at h <;> try cases h
          rename_i hb0
          have hb0' : (m0 / 2 ^ a) % 2 = 0 := nat_beq_true hb0
          refine ⟨m0 + 2 ^ a, m1, m2, ?_, ?_, ?_, h⟩
          · unfold bit3; rw [if_pos ha1']; exact hb0'
          · unfold bit3; rw [if_pos ha1']
            have := div_two_pow_add_eq (m := m0) (e := a) (k := a) hb0'
            rw [if_pos rfl] at this; exact this
          · intro x hne; unfold bit3
            split_ifs with hx1 hx2
            · have := div_two_pow_add_eq (m := m0) (e := a) (k := x) hb0'
              rw [if_neg hne] at this; exact this
            · rfl
            · rfl
        · rename_i ha1
          have ha1' : ¬ a ≤ 255 := nat_ble_false ha1
          split at h
          · rename_i ha2
            have ha2' : a ≤ 511 := Nat.ble_eq.mp ha2
            split at h <;> try cases h
            rename_i hb0
            have hb0' : (m1 / 2 ^ (a - 256)) % 2 = 0 := nat_beq_true hb0
            refine ⟨m0, m1 + 2 ^ (a - 256), m2, ?_, ?_, ?_, h⟩
            · unfold bit3; rw [if_neg ha1', if_pos ha2']; exact hb0'
            · unfold bit3; rw [if_neg ha1', if_pos ha2']
              have := div_two_pow_add_eq (m := m1) (e := a - 256) (k := a - 256) hb0'
              rw [if_pos rfl] at this; exact this
            · intro x hne; unfold bit3
              split_ifs with hx1 hx2
              · rfl
              · have hne' : x - 256 ≠ a - 256 := by omega
                have := div_two_pow_add_eq (m := m1) (e := a - 256) (k := x - 256) hb0'
                rw [if_neg hne'] at this; exact this
              · rfl
          · rename_i ha2
            have ha2' : ¬ a ≤ 511 := nat_ble_false ha2
            split at h <;> try cases h
            rename_i hb0
            have hb0' : (m2 / 2 ^ (a - 512)) % 2 = 0 := nat_beq_true hb0
            refine ⟨m0, m1, m2 + 2 ^ (a - 512), ?_, ?_, ?_, h⟩
            · unfold bit3; rw [if_neg ha1', if_neg ha2']; exact hb0'
            · unfold bit3; rw [if_neg ha1', if_neg ha2']
              have := div_two_pow_add_eq (m := m2) (e := a - 512) (k := a - 512) hb0'
              rw [if_pos rfl] at this; exact this
            · intro x hne; unfold bit3
              split_ifs with hx1 hx2
              · rfl
              · rfl
              · have hne' : x - 512 ≠ a - 512 := by omega
                have := div_two_pow_add_eq (m := m2) (e := a - 512) (k := x - 512) hb0'
                rw [if_neg hne'] at this; exact this
      rcases hstep with ⟨m0', m1', m2', hba0, hba1, hbother, hrec⟩
      obtain ⟨hnodup, hlen, hmem, hadj, hc16, hc25, hc36, hc49⟩ := ih _ _ _ _ _ _ _ _ hrec
      have hnotmem : a ∉ b :: rest := by
        intro ha; have := (hmem a ha).2.2; omega
      have hcnt_step : ∀ (sq c k : ℕ),
          k ≤ (match Nat.beq (Nat.add a b) sq with | true => Nat.add c 1 | false => c) +
              countCyclic first sq (b :: rest) →
          k ≤ c + countCyclic first sq (a :: b :: rest) := by
        intro sq c k hk
        simp only [countCyclic]
        cases hq : Nat.beq (Nat.add a b) sq with
        | true =>
          simp only [hq] at hk
          have heq : a + b = sq := nat_beq_true hq
          have hk' : k ≤ (c + 1) + countCyclic first sq (b :: rest) := hk
          rw [if_pos heq]; omega
        | false =>
          simp only [hq] at hk
          have hne : a + b ≠ sq := nat_beq_false hq
          rw [if_neg hne]; omega
      refine ⟨List.nodup_cons.mpr ⟨hnotmem, hnodup⟩, ?_, ?_, ?_,
        hcnt_step 16 c16 2 hc16, hcnt_step 25 c25 4 hc25,
        hcnt_step 36 c36 3 hc36, hcnt_step 49 c49 5 hc49⟩
      · simp only [List.length_cons] at hlen ⊢; omega
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx_tl
        · exact ⟨h1', h2', hba0⟩
        · have hne : x ≠ a := fun heq => hnotmem (heq ▸ hx_tl)
          have hmx := hmem x hx_tl
          exact ⟨hmx.1, hmx.2.1, by rw [← hbother x hne]; exact hmx.2.2⟩
      · intro i hi
        cases i with
        | zero =>
          simp only [List.length_cons, Nat.zero_add, List.getElem_cons_zero, List.getElem_cons_succ]
          rw [dif_pos (by omega)]
          exact isSq32_sound hsq
        | succ i' =>
          have hi' : i' < (b :: rest).length := by simp only [List.length_cons] at hi ⊢; omega
          have hsub := hadj i' hi'
          by_cases hlt : i' + 1 < (b :: rest).length
          · have hlt2 : i' + 1 + 1 < (a :: b :: rest).length := by simp only [List.length_cons] at hlt ⊢; omega
            simp only [hlt, ↓reduceDIte] at hsub
            simp only [hlt2, ↓reduceDIte, List.getElem_cons_succ]
            exact hsub
          · have hlt2 : ¬ (i' + 1 + 1 < (a :: b :: rest).length) := by simp only [List.length_cons] at hlt ⊢; omega
            simp only [hlt, ↓reduceDIte] at hsub
            simp only [hlt2, ↓reduceDIte, List.getElem_cons_succ]
            exact hsub

private lemma countCyclic_eq_card {first sq : ℕ} :
    ∀ (seq : List ℕ),
      countCyclic first sq seq =
      ((Finset.univ : Finset (Fin seq.length)).filter (fun i =>
        seq[i.val] + (if hlt : i.val + 1 < seq.length then seq[i.val + 1] else first) = sq)).card := by
  intro seq
  induction seq with
  | nil => simp [countCyclic]
  | cons a tl ih =>
    cases tl with
    | nil =>
      rw [Finset.card_filter]
      simp [countCyclic]
    | cons b rest =>
      rw [Finset.card_filter]
      simp only [List.length_cons, countCyclic]
      rw [Fin.sum_univ_succ, ih, Finset.card_filter]
      simp only [List.length_cons]
      have hhead : (if a + b = sq then 1 else 0) =
          (if (a :: b :: rest)[(0 : Fin (rest.length + 1 + 1)).val] +
              (if hlt : (0 : Fin (rest.length + 1 + 1)).val + 1 < rest.length + 1 + 1 then
                (a :: b :: rest)[(0 : Fin (rest.length + 1 + 1)).val + 1] else first) = sq then 1 else 0) := by
        simp only [Fin.val_zero, Nat.zero_add, List.getElem_cons_zero, List.getElem_cons_succ]
        rw [dif_pos (by omega)]
      rw [hhead]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [Fin.val_succ, List.getElem_cons_succ]
      by_cases hlt : i.val + 1 < rest.length + 1
      · have hlt2 : i.val + 1 + 1 < rest.length + 1 + 1 := by omega
        rw [dif_pos hlt2, dif_pos hlt]
      · have hlt2 : ¬ (i.val + 1 + 1 < rest.length + 1 + 1) := by omega
        rw [dif_neg hlt2, dif_neg hlt]

theorem checkBaseCycle_sound {n : ℕ} {seq : List ℕ} (h : checkBaseCycle n seq = true) :
    InvSmall 2 4 3 5 n := by
  unfold checkBaseCycle at h
  split at h <;> try cases h
  rename_i a rest hn2 hn767
  have hn2' : 2 ≤ n := Nat.ble_eq.mp hn2
  obtain ⟨hnodup, hlen, hmem, hadj, hc16, hc25, hc36, hc49⟩ :=
    checkCycleFastGo_sound (a :: rest) 0 0 0 0 0 0 0 0 h
  have hlen' : (a :: rest).length = n := by omega
  let c : IntervalCycle 1 n :=
    { len := (a :: rest).length
      hlen := by omega
      hpos := by omega
      seq := fun i => (a :: rest)[i.val]
      hinj := fun i j hij => Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp hij)
      hmem := fun i =>
        let hm := hmem (a :: rest)[i.val] (List.getElem_mem _)
        ⟨hm.1, hm.2.1⟩
      hadj := by
        intro i
        have hstep := hadj i.val i.isLt
        have hnext : (a :: rest)[(nextIdx (by omega : 0 < (a :: rest).length) i).val] =
            if hlt : i.val + 1 < (a :: rest).length then (a :: rest)[i.val + 1] else a := by
          simp only [nextIdx]
          by_cases hlt : i.val + 1 < (a :: rest).length
          · rw [dif_pos hlt]; congr 1; exact Nat.mod_eq_of_lt hlt
          · rw [dif_neg hlt]
            have heq : i.val + 1 = (a :: rest).length := by omega
            simp [heq]
        rw [hnext]
        exact hstep }
  have hedge_eq : ∀ sq, edgeCount c sq = countCyclic a sq (a :: rest) := by
    intro sq
    rw [countCyclic_eq_card]
    unfold edgeCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, c]
    have hi_lt : i.val < (a :: rest).length := i.isLt
    have hnext : (a :: rest)[(nextIdx (by omega : 0 < (a :: rest).length) i).val] =
        if hlt : i.val + 1 < (a :: rest).length then (a :: rest)[i.val + 1] else a := by
      simp only [nextIdx]
      by_cases hlt : i.val + 1 < (a :: rest).length
      · rw [dif_pos hlt]; congr 1; exact Nat.mod_eq_of_lt hlt
      · rw [dif_neg hlt]
        have heq : i.val + 1 = (a :: rest).length := by omega
        simp [heq]
    rw [hnext]
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · rw [hedge_eq]; omega
  · rw [hedge_eq]; omega
  · rw [hedge_eq]; omega
  · rw [hedge_eq]; omega

/-! ### Part 2: Matching Helpers & Rauzy Elimination Verifier -/

private lemma checkCovers_bounds {cur R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hc : S1.checkCovers cur R m = true) :
    ∀ a b r, (a, b, r) ∈ m → cur ≤ a ∧ a ≤ b ∧ b ≤ R := by
  induction m generalizing cur with
  | nil => simp [S1.checkCovers] at hc
  | cons hd tl ih =>
    rcases hd with ⟨lo0, hi0, r0⟩
    cases tl with
    | nil =>
      intro a b r hm
      simp only [S1.checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hc
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl, rfl⟩; omega
    | cons hd2 tl2 =>
      intro a b r hm
      simp only [S1.checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hc
      rw [List.mem_cons] at hm
      rcases hm with heq | hm_tl
      · simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, rfl, rfl⟩; omega
      · have htl := ih hc.2 a b r hm_tl; omega

private lemma checkCovers_exists {cur R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hc : S1.checkCovers cur R m = true) {x : ℕ} (h1 : cur ≤ x) (h2 : x ≤ R) :
    ∃ lo hi r, (lo, hi, r) ∈ m ∧ lo ≤ x ∧ x ≤ hi := by
  induction m generalizing cur with
  | nil => simp [S1.checkCovers] at hc
  | cons hd tl ih =>
    rcases hd with ⟨lo0, hi0, r0⟩
    cases tl with
    | nil =>
      simp only [S1.checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hc
      exact ⟨lo0, hi0, r0, List.mem_singleton_self _, by omega, by omega⟩
    | cons hd2 tl2 =>
      simp only [S1.checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hc
      by_cases hx : x ≤ hi0
      · exact ⟨lo0, hi0, r0, List.mem_cons_self, by omega, hx⟩
      · obtain ⟨lo, hi, r, hm, ha, hb⟩ := ih hc.2 (by omega)
        exact ⟨lo, hi, r, List.mem_cons_of_mem _ hm, ha, hb⟩

private lemma checkCovers_pairwise_disjoint {cur R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hc : S1.checkCovers cur R m = true) :
    m.Pairwise (fun t1 t2 => t1.2.1 < t2.1) := by
  induction m generalizing cur with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    rcases hd with ⟨lo0, hi0, r0⟩
    cases tl with
    | nil => exact List.pairwise_singleton _ _
    | cons hd2 tl2 =>
      simp only [S1.checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hc
      rw [List.pairwise_cons]
      refine ⟨?_, ih hc.2⟩
      intro t ht
      rcases t with ⟨a, b, r⟩
      have hb := checkCovers_bounds hc.2 a b r ht
      dsimp only; omega

theorem evalRootMatching_of_mem_checkCovers {cur R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hc : S1.checkCovers cur R m = true) {lo hi z x : ℕ}
    (hmem : (lo, hi, z) ∈ m) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    S1.evalRootMatching m x = z * z - x := by
  induction m generalizing cur with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨lo0, hi0, r0⟩
    cases tl with
    | nil =>
      simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      simp only [S1.evalRootMatching, hlo, hhi, and_self, ↓reduceIte]
    | cons hd2 tl2 =>
      simp only [S1.checkCovers, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hc
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem_tl
      · simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
        simp only [S1.evalRootMatching, hlo, hhi, and_self, ↓reduceIte]
      · have hb := checkCovers_bounds hc.2 lo hi z hmem_tl
        have hnot : ¬ (lo0 ≤ x ∧ x ≤ hi0) := by omega
        simp only [S1.evalRootMatching, hnot, ↓reduceIte]
        exact ih hc.2 hmem_tl

private lemma checkRootMatching_piece_bounds {L R : ℕ} {m : List (ℕ × ℕ × ℕ)}
    (hm : S1.checkRootMatching L R m = true) {lo hi r : ℕ} (hmem : (lo, hi, r) ∈ m) :
    L ≤ lo ∧ lo ≤ hi ∧ hi ≤ R ∧ hi + L ≤ r * r ∧ r * r ≤ lo + R := by
  simp only [S1.checkRootMatching, Bool.and_eq_true, List.all_eq_true] at hm
  have hb := checkCovers_bounds hm.1 lo hi r hmem
  have ht := hm.2 (lo, hi, r) hmem
  simp only [S1.checkTriple, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, Nat.blt_eq] at ht
  rcases ht with ⟨hsum, _⟩ | ⟨⟨lo', hi', r'⟩, hmem', ⟨⟨⟨hr, h1⟩, h2⟩, _⟩⟩
  · omega
  · dsimp only at hr h1 h2; subst hr
    have hb' := checkCovers_bounds hm.1 lo' hi' r' hmem'
    omega

/-- A translation piece: on `[lo, hi]`, `f^[cost] x = if pos then x + mag else x - mag`. -/
structure Piece where
  lo : ℕ
  hi : ℕ
  pos : Bool
  mag : ℕ
  cost : ℕ

def applyPiece (p : Piece) (x : ℕ) : ℕ :=
  if p.pos then x + p.mag else x - p.mag

def inDomain (pcs : List Piece) (x : ℕ) : Prop :=
  ∃ p ∈ pcs, p.lo ≤ x ∧ x ≤ p.hi

def DisjPieces (p q : Piece) : Prop :=
  p.hi < q.lo ∨ q.hi < p.lo

def ValidPiecesD (f : ℕ → ℕ) (L R : ℕ) (D : ℕ → Prop) (pcs : List Piece) : Prop :=
  pcs.Pairwise DisjPieces ∧
  ∀ p ∈ pcs,
    L ≤ p.lo ∧ p.lo ≤ p.hi ∧ p.hi ≤ R ∧ 1 ≤ p.cost ∧
    ∀ x, p.lo ≤ x → x ≤ p.hi →
      (p.pos = false → p.mag ≤ x) ∧
      L ≤ applyPiece p x ∧ applyPiece p x ≤ R ∧
      f^[p.cost] x = applyPiece p x ∧
      (∀ t, 0 < t → t < p.cost → ¬ D (f^[t] x))

def ValidPieces (f : ℕ → ℕ) (L R : ℕ) (pcs : List Piece) : Prop :=
  inDomain pcs L ∧ ValidPiecesD f L R (inDomain pcs) pcs

def addShift (p1 : Bool) (m1 : ℕ) (p2 : Bool) (m2 : ℕ) : Bool × ℕ :=
  match p1, p2 with
  | true, true => (true, Nat.add m1 m2)
  | false, false => (false, Nat.add m1 m2)
  | true, false =>
      match Nat.ble m2 m1 with
      | true => (true, Nat.sub m1 m2)
      | false => (false, Nat.sub m2 m1)
  | false, true =>
      match Nat.ble m1 m2 with
      | true => (true, Nat.sub m2 m1)
      | false => (false, Nat.sub m1 m2)

def natMax (a b : ℕ) : ℕ := match Nat.ble a b with | true => b | false => a
def natMin (a b : ℕ) : ℕ := match Nat.ble a b with | true => a | false => b

private lemma natMax_eq (a b : ℕ) : natMax a b = max a b := by
  unfold natMax
  cases h : Nat.ble a b with
  | true => dsimp only; have := Nat.ble_eq.mp h; omega
  | false => dsimp only; have := nat_ble_false h; omega

private lemma natMin_eq (a b : ℕ) : natMin a b = min a b := by
  unfold natMin
  cases h : Nat.ble a b with
  | true => dsimp only; have := Nat.ble_eq.mp h; omega
  | false => dsimp only; have := nat_ble_false h; omega

def buildPiecesFor (L a1 b1 s1 : ℕ) : List (ℕ × ℕ × ℕ) → List Piece
  | [] => []
  | (a2, b2, r2) :: rest =>
      let s2 := Nat.mul r2 r2
      let lo := natMax a1 (Nat.sub s1 b2)
      let hi := natMin b1 (Nat.sub s1 a2)
      let tl := buildPiecesFor L a1 b1 s1 rest
      match Nat.ble lo hi, Nat.ble a2 s1 with
      | true, true =>
          let (pos, mag) := match Nat.ble s1 s2 with
            | true => (true, Nat.sub s2 s1)
            | false => (false, Nat.sub s1 s2)
          match Nat.beq lo L, Nat.blt L hi with
          | true, true => ⟨L, L, pos, mag, 1⟩ :: ⟨Nat.add L 1, hi, pos, mag, 1⟩ :: tl
          | _, _ => ⟨lo, hi, pos, mag, 1⟩ :: tl
      | _, _ => tl

def buildPieces (L : ℕ) (m2 : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) → List Piece
  | [] => []
  | (a1, b1, r1) :: rest =>
      buildPiecesFor L a1 b1 (Nat.mul r1 r1) m2 ++ buildPieces L m2 rest

private lemma buildPiecesFor_mem {L a1 b1 s1 : ℕ} {m2 : List (ℕ × ℕ × ℕ)} {p : Piece}
    (hp : p ∈ buildPiecesFor L a1 b1 s1 m2) :
    ∃ a2 b2 r2, (a2, b2, r2) ∈ m2 ∧
      a1 ≤ p.lo ∧ p.lo ≤ p.hi ∧ p.hi ≤ b1 ∧
      a2 ≤ s1 ∧ s1 - b2 ≤ p.lo ∧ p.hi ≤ s1 - a2 ∧
      p.cost = 1 ∧
      (p.pos = true ∧ s1 ≤ r2 * r2 ∧ p.mag = r2 * r2 - s1 ∨
       p.pos = false ∧ r2 * r2 < s1 ∧ p.mag = s1 - r2 * r2) := by
  induction m2 with
  | nil => simp [buildPiecesFor] at hp
  | cons hd tl ih =>
    rcases hd with ⟨a2, b2, r2⟩
    simp only [buildPiecesFor, nat_mul_eq, nat_sub_eq, nat_add_eq] at hp
    split at hp
    · rename_i hle ha2
      have hle' : max a1 (s1 - b2) ≤ min b1 (s1 - a2) := by
        rw [← natMax_eq, ← natMin_eq]; exact Nat.ble_eq.mp hle
      have ha2' : a2 ≤ s1 := Nat.ble_eq.mp ha2
      have hpm : (match Nat.ble s1 (r2 * r2) with | true => (true, r2 * r2 - s1) | false => (false, s1 - r2 * r2)).1 = true ∧ s1 ≤ r2 * r2 ∧
                 (match Nat.ble s1 (r2 * r2) with | true => (true, r2 * r2 - s1) | false => (false, s1 - r2 * r2)).2 = r2 * r2 - s1 ∨
                 (match Nat.ble s1 (r2 * r2) with | true => (true, r2 * r2 - s1) | false => (false, s1 - r2 * r2)).1 = false ∧ r2 * r2 < s1 ∧
                 (match Nat.ble s1 (r2 * r2) with | true => (true, r2 * r2 - s1) | false => (false, s1 - r2 * r2)).2 = s1 - r2 * r2 := by
        cases hcmp : Nat.ble s1 (r2 * r2) with
        | true => left; exact ⟨rfl, Nat.ble_eq.mp hcmp, rfl⟩
        | false => right; have := nat_ble_false hcmp; exact ⟨rfl, by omega, rfl⟩
      split at hp
      · rename_i hloL hLhi
        have hloL' : max a1 (s1 - b2) = L := by rw [← natMax_eq]; exact nat_beq_true hloL
        have hLhi' : L < min b1 (s1 - a2) := by rw [← natMin_eq]; exact Nat.blt_eq.mp hLhi
        rw [List.mem_cons, List.mem_cons] at hp
        rcases hp with rfl | rfl | htl
        · exact ⟨a2, b2, r2, List.mem_cons_self, by dsimp only; omega, by dsimp only; omega,
            by dsimp only; omega, ha2', by dsimp only; omega, by dsimp only; omega, rfl, hpm⟩
        · exact ⟨a2, b2, r2, List.mem_cons_self, by dsimp only; omega, by dsimp only; rw [natMin_eq]; omega,
            by dsimp only; rw [natMin_eq]; omega, ha2', by dsimp only; omega, by dsimp only; rw [natMin_eq]; omega, rfl, hpm⟩
        · obtain ⟨a2', b2', r2', hm', hrest⟩ := ih htl
          exact ⟨a2', b2', r2', List.mem_cons_of_mem _ hm', hrest⟩
      · rw [List.mem_cons] at hp
        rcases hp with rfl | htl
        · exact ⟨a2, b2, r2, List.mem_cons_self, by dsimp only; rw [natMax_eq]; omega,
            by dsimp only; rw [natMax_eq, natMin_eq]; omega, by dsimp only; rw [natMin_eq]; omega,
            ha2', by dsimp only; rw [natMax_eq]; omega, by dsimp only; rw [natMin_eq]; omega, rfl, hpm⟩
        · obtain ⟨a2', b2', r2', hm', hrest⟩ := ih htl
          exact ⟨a2', b2', r2', List.mem_cons_of_mem _ hm', hrest⟩
    · obtain ⟨a2', b2', r2', hm', hrest⟩ := ih hp
      exact ⟨a2', b2', r2', List.mem_cons_of_mem _ hm', hrest⟩

private lemma buildPiecesFor_pairwise {L a1 b1 s1 : ℕ} {m2 : List (ℕ × ℕ × ℕ)}
    (hpw : m2.Pairwise (fun t1 t2 => t1.2.1 < t2.1)) :
    (buildPiecesFor L a1 b1 s1 m2).Pairwise DisjPieces := by
  induction m2 with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    rcases hd with ⟨a2, b2, r2⟩
    rw [List.pairwise_cons] at hpw
    have ihtl := ih hpw.2
    simp only [buildPiecesFor, nat_mul_eq, nat_sub_eq, nat_add_eq]
    split
    · rename_i hle ha2
      have hle' : max a1 (s1 - b2) ≤ min b1 (s1 - a2) := by
        rw [← natMax_eq, ← natMin_eq]; exact Nat.ble_eq.mp hle
      have ha2' : a2 ≤ s1 := Nat.ble_eq.mp ha2
      have hdisj_tl : ∀ q ∈ buildPiecesFor L a1 b1 s1 tl, q.hi < max a1 (s1 - b2) := by
        intro q hq
        obtain ⟨a2', b2', r2', hm', _, _, _, ha2p, _, hqhi, _, _⟩ := buildPiecesFor_mem hq
        have hlt := hpw.1 (a2', b2', r2') hm'
        dsimp only at hlt
        omega
      split
      · rename_i hloL hLhi
        have hloL' : max a1 (s1 - b2) = L := by rw [← natMax_eq]; exact nat_beq_true hloL
        have hLhi' : L < min b1 (s1 - a2) := by rw [← natMin_eq]; exact Nat.blt_eq.mp hLhi
        rw [List.pairwise_cons, List.pairwise_cons]
        refine ⟨?_, ?_, ihtl⟩
        · intro q hq
          rw [List.mem_cons] at hq
          rcases hq with rfl | hqtl
          · left; dsimp only; omega
          · right; have := hdisj_tl q hqtl; dsimp only; omega
        · intro q hqtl
          right; have := hdisj_tl q hqtl; dsimp only; omega
      · rw [List.pairwise_cons]
        refine ⟨?_, ihtl⟩
        intro q hqtl
        right; have := hdisj_tl q hqtl; dsimp only; rw [natMax_eq]; omega
    · exact ihtl

private lemma buildPiecesFor_covers {L a1 b1 s1 x : ℕ} {m2 : List (ℕ × ℕ × ℕ)} {a2 b2 r2 : ℕ}
    (hm2 : (a2, b2, r2) ∈ m2) (hx1 : a1 ≤ x) (hx2 : x ≤ b1)
    (ha2 : a2 ≤ s1 - x) (hb2 : s1 - x ≤ b2) (hxs1 : x ≤ s1) :
    inDomain (buildPiecesFor L a1 b1 s1 m2) x := by
  induction m2 with
  | nil => cases hm2
  | cons hd tl ih =>
    rcases hd with ⟨a2', b2', r2'⟩
    rw [List.mem_cons] at hm2
    simp only [buildPiecesFor, nat_mul_eq, nat_sub_eq, nat_add_eq]
    rcases hm2 with heq | htl
    · simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
      have h1 : Nat.ble (natMax a1 (s1 - b2)) (natMin b1 (s1 - a2)) = true := by
        rw [natMax_eq, natMin_eq, Nat.ble_eq]; omega
      have h2 : Nat.ble a2 s1 = true := Nat.ble_eq.mpr (by omega)
      simp only [h1, h2]
      split
      · rename_i hloL hLhi
        have hloL' : max a1 (s1 - b2) = L := by rw [← natMax_eq]; exact nat_beq_true hloL
        by_cases hxL : x = L
        · exact ⟨_, List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega, by dsimp only; rw [natMin_eq]; omega⟩
      · exact ⟨_, List.mem_cons_self, by dsimp only; rw [natMax_eq]; omega, by dsimp only; rw [natMin_eq]; omega⟩
    · obtain ⟨q, hq, hq1, hq2⟩ := ih htl
      split
      · split
        · exact ⟨q, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq), hq1, hq2⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq, hq1, hq2⟩
      · exact ⟨q, hq, hq1, hq2⟩

private lemma buildPieces_valid {L R : ℕ} {m1 m2 : List (ℕ × ℕ × ℕ)}
    (hLR : L ≤ R)
    (hm1 : S1.checkRootMatching L R m1 = true)
    (hm2 : S1.checkRootMatching L R m2 = true) :
    ValidPieces (S1.evalRootMatching m2 ∘ S1.evalRootMatching m1) L R (buildPieces L m2 m1) := by
  have hc1 : S1.checkCovers L R m1 = true := (Bool.and_eq_true _ _).mp hm1 |>.1
  have hc2 : S1.checkCovers L R m2 = true := (Bool.and_eq_true _ _).mp hm2 |>.1
  have hpw1 := checkCovers_pairwise_disjoint hc1
  have hpw2 := checkCovers_pairwise_disjoint hc2
  have hmem_bp : ∀ m1' : List (ℕ × ℕ × ℕ),
      (∀ t ∈ m1', t ∈ m1) →
      ∀ p ∈ buildPieces L m2 m1',
        ∃ a1 b1 r1 a2 b2 r2,
          (a1, b1, r1) ∈ m1' ∧ (a2, b2, r2) ∈ m2 ∧
          a1 ≤ p.lo ∧ p.lo ≤ p.hi ∧ p.hi ≤ b1 ∧
          a2 ≤ r1 * r1 ∧ r1 * r1 - b2 ≤ p.lo ∧ p.hi ≤ r1 * r1 - a2 ∧
          p.cost = 1 ∧
          (p.pos = true ∧ r1 * r1 ≤ r2 * r2 ∧ p.mag = r2 * r2 - r1 * r1 ∨
           p.pos = false ∧ r2 * r2 < r1 * r1 ∧ p.mag = r1 * r1 - r2 * r2) := by
    intro m1'
    induction m1' with
    | nil => intro _ p hp; simp [buildPieces] at hp
    | cons hd tl ih =>
      intro hsub p hp
      rcases hd with ⟨a1, b1, r1⟩
      simp only [buildPieces, List.mem_append, nat_mul_eq] at hp
      rcases hp with hfor | htl
      · obtain ⟨a2, b2, r2, hm2', hrest⟩ := buildPiecesFor_mem hfor
        exact ⟨a1, b1, r1, a2, b2, r2, List.mem_cons_self, hm2', hrest⟩
      · obtain ⟨a1', b1', r1', a2', b2', r2', hm1', hm2', hrest⟩ :=
          ih (fun t ht => hsub t (List.mem_cons_of_mem _ ht)) p htl
        exact ⟨a1', b1', r1', a2', b2', r2', List.mem_cons_of_mem _ hm1', hm2', hrest⟩
  have hpw_bp : ∀ m1' : List (ℕ × ℕ × ℕ),
      m1'.Pairwise (fun t1 t2 => t1.2.1 < t2.1) →
      (∀ t ∈ m1', t ∈ m1) →
      (buildPieces L m2 m1').Pairwise DisjPieces := by
    intro m1'
    induction m1' with
    | nil => intro _ _; exact List.Pairwise.nil
    | cons hd tl ih =>
      intro hpw hsub
      rcases hd with ⟨a1, b1, r1⟩
      rw [List.pairwise_cons] at hpw
      simp only [buildPieces]
      rw [List.pairwise_append]
      refine ⟨buildPiecesFor_pairwise hpw2, ih hpw.2 (fun t ht => hsub t (List.mem_cons_of_mem _ ht)), ?_⟩
      intro p hp q hq
      obtain ⟨_, _, _, _, _, _, hphi, _⟩ := buildPiecesFor_mem hp
      obtain ⟨a1', b1', r1', _, _, _, hm1', _, ha1', _, _, _⟩ :=
        hmem_bp tl (fun t ht => hsub t (List.mem_cons_of_mem _ ht)) q hq
      have hlt := hpw.1 (a1', b1', r1') hm1'
      dsimp only at hlt
      left; omega
  have hdomL : inDomain (buildPieces L m2 m1) L := by
    obtain ⟨a1, b1, r1, hm1L, ha1L, hb1L⟩ := checkCovers_exists hc1 (le_refl L) hLR
    have hpb1 := checkRootMatching_piece_bounds hm1 hm1L
    obtain ⟨a2, b2, r2, hm2L, ha2L, hb2L⟩ :=
      checkCovers_exists hc2 (x := r1 * r1 - L) (by omega) (by omega)
    have hcov : ∀ m1' : List (ℕ × ℕ × ℕ), (a1, b1, r1) ∈ m1' → inDomain (buildPieces L m2 m1') L := by
      intro m1' hm1'
      induction m1' with
      | nil => cases hm1'
      | cons hd tl ih =>
        rcases hd with ⟨a1', b1', r1'⟩
        rw [List.mem_cons] at hm1'
        simp only [buildPieces, nat_mul_eq]
        rcases hm1' with heq | htl
        · simp only [Prod.mk.injEq] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          obtain ⟨q, hq, hq1, hq2⟩ := buildPiecesFor_covers (L := L) hm2L ha1L hb1L ha2L hb2L (by omega)
          exact ⟨q, List.mem_append_left _ hq, hq1, hq2⟩
        · obtain ⟨q, hq, hq1, hq2⟩ := ih htl
          exact ⟨q, List.mem_append_right _ hq, hq1, hq2⟩
    exact hcov m1 hm1L
  refine ⟨hdomL, ⟨hpw_bp m1 hpw1 (fun _ h => h), ?_⟩⟩
  intro p hp
  obtain ⟨a1, b1, r1, a2, b2, r2, hm1p, hm2p, ha1, hlohi, hb1, ha2s1, hlo2, hhi2, hcost, hpm⟩ :=
    hmem_bp m1 (fun _ h => h) p hp
  have hpb1 := checkRootMatching_piece_bounds hm1 hm1p
  have hpb2 := checkRootMatching_piece_bounds hm2 hm2p
  refine ⟨by omega, hlohi, by omega, by omega, ?_⟩
  intro x hx1 hx2
  have hev1 : S1.evalRootMatching m1 x = r1 * r1 - x :=
    evalRootMatching_of_mem_checkCovers hc1 hm1p (by omega) (by omega)
  have hy1 : a2 ≤ r1 * r1 - x := by omega
  have hy2 : r1 * r1 - x ≤ b2 := by omega
  have hev2 : S1.evalRootMatching m2 (r1 * r1 - x) = r2 * r2 - (r1 * r1 - x) :=
    evalRootMatching_of_mem_checkCovers hc2 hm2p hy1 hy2
  have hstep : (S1.evalRootMatching m2 ∘ S1.evalRootMatching m1)^[p.cost] x =
      r2 * r2 - (r1 * r1 - x) := by
    rw [hcost, Function.iterate_one, Function.comp_apply, hev1, hev2]
  have happ : (p.pos = false → p.mag ≤ x) ∧
      applyPiece p x = r2 * r2 - (r1 * r1 - x) := by
    unfold applyPiece
    rcases hpm with ⟨hpos, hle, hmag⟩ | ⟨hpos, hlt, hmag⟩
    · rw [hpos, if_pos rfl]; exact ⟨fun h => Bool.noConfusion h, by omega⟩
    · rw [hpos, if_neg Bool.false_ne_true]; exact ⟨fun _ => by omega, by omega⟩
  refine ⟨happ.1, by rw [happ.2]; omega, by rw [happ.2]; omega, by rw [hstep, happ.2], ?_⟩
  intro t ht1 ht2; omega

def pickBestGo (L : ℕ) (idx : ℕ) (bestW bestIdx : ℕ) (hasBest : Bool) : List Piece → Option ℕ
  | [] => match hasBest with | true => some bestIdx | false => none
  | p :: rest =>
      let w := Nat.add (Nat.sub p.hi p.lo) 1
      let elig :=
        match Nat.beq p.mag 0, Nat.beq p.lo L, Nat.ble w p.mag with
        | false, false, true => true
        | _, _, _ => false
      match elig with
      | true =>
          match hasBest with
          | false => pickBestGo L (Nat.add idx 1) w idx true rest
          | true =>
              match Nat.blt bestW w with
              | true => pickBestGo L (Nat.add idx 1) w idx true rest
              | false => pickBestGo L (Nat.add idx 1) bestW bestIdx true rest
      | false => pickBestGo L (Nat.add idx 1) bestW bestIdx hasBest rest

def getPieceAt : ℕ → List Piece → Option Piece
  | _, [] => none
  | 0, p :: _ => some p
  | k + 1, _ :: rest => getPieceAt k rest

def routePiece (e : Piece) (q : Piece) : List Piece :=
  let valid := match q.pos with
    | true => Nat.ble q.mag e.hi
    | false => true
  match valid with
  | false => [q]
  | true =>
      let preLo := match q.pos with | true => Nat.sub e.lo q.mag | false => Nat.add e.lo q.mag
      let preHi := match q.pos with | true => Nat.sub e.hi q.mag | false => Nat.add e.hi q.mag
      let ilo := natMax q.lo preLo
      let ihi := natMin q.hi preHi
      match Nat.ble ilo ihi with
      | false => [q]
      | true =>
          let (npos, nmag) := addShift q.pos q.mag e.pos e.mag
          let ncost := Nat.add q.cost e.cost
          let mid : Piece := ⟨ilo, ihi, npos, nmag, ncost⟩
          let r1 := match Nat.blt ihi q.hi with
            | true => [mid, ⟨Nat.add ihi 1, q.hi, q.pos, q.mag, q.cost⟩]
            | false => [mid]
          match Nat.blt q.lo ilo with
          | true => ⟨q.lo, Nat.sub ilo 1, q.pos, q.mag, q.cost⟩ :: r1
          | false => r1

def routeAll (skipIdx : ℕ) (e : Piece) : ℕ → List Piece → List Piece
  | _, [] => []
  | idx, q :: rest =>
      match Nat.beq idx skipIdx with
      | true => routeAll skipIdx e (Nat.add idx 1) rest
      | false => routePiece e q ++ routeAll skipIdx e (Nat.add idx 1) rest

def mergeAdjGo (L : ℕ) (cur : Piece) : List Piece → List Piece
  | [] => [cur]
  | p2 :: rest =>
      match Nat.beq cur.lo L, Nat.beq (Nat.add cur.hi 1) p2.lo, cur.pos == p2.pos, Nat.beq cur.mag p2.mag, Nat.beq cur.cost p2.cost with
      | false, true, true, true, true =>
          mergeAdjGo L ⟨cur.lo, p2.hi, cur.pos, cur.mag, cur.cost⟩ rest
      | _, _, _, _, _ => cur :: mergeAdjGo L p2 rest

def mergeAdj (L : ℕ) : List Piece → List Piece
  | [] => []
  | p :: rest => mergeAdjGo L p rest

def hasDoneL (L : ℕ) : List Piece → Bool
  | [] => false
  | p :: rest =>
      match Nat.beq p.lo L, Nat.beq p.mag 0 with
      | true, true => true
      | _, _ => hasDoneL L rest

def rauzyLoop (L : ℕ) : ℕ → List Piece → List Piece
  | 0, pcs => pcs
  | fuel + 1, pcs =>
      match hasDoneL L pcs, Nat.ble pcs.length 20 with
      | false, true =>
          match pickBestGo L 0 0 0 false pcs with
          | none => pcs
          | some idx =>
              match getPieceAt idx pcs with
              | none => pcs
              | some e =>
                  rauzyLoop L fuel (mergeAdj L (routeAll idx e 0 pcs))
      | _, _ => pcs

private lemma getPieceAt_mem {k : ℕ} {pcs : List Piece} {e : Piece}
    (h : getPieceAt k pcs = some e) : e ∈ pcs := by
  induction pcs generalizing k with
  | nil => simp [getPieceAt] at h
  | cons p rest ih =>
    cases k with
    | zero => simp [getPieceAt] at h; subst h; exact List.mem_cons_self
    | succ k' => simp [getPieceAt] at h; exact List.mem_cons_of_mem _ (ih h)

private lemma pickBestGo_spec {L : ℕ} :
    ∀ (pcs : List Piece) (idx bestW bestIdx : ℕ) (hasBest : Bool) (out : ℕ),
      pickBestGo L idx bestW bestIdx hasBest pcs = some out →
      (hasBest = true ∧ out = bestIdx) ∨
      ∃ k p, out = idx + k ∧ getPieceAt k pcs = some p ∧
        p.mag ≠ 0 ∧ p.lo ≠ L ∧ p.hi - p.lo + 1 ≤ p.mag := by
  intro pcs
  induction pcs with
  | nil =>
    intro idx bestW bestIdx hasBest out h
    simp only [pickBestGo] at h
    cases hasBest with
    | false => cases h
    | true => simp at h; exact Or.inl ⟨rfl, h.symm⟩
  | cons p rest ih =>
    intro idx bestW bestIdx hasBest out h
    simp only [pickBestGo, nat_add_eq, nat_sub_eq] at h
    split at h
    · rename_i helig
      have hp_elig : p.mag ≠ 0 ∧ p.lo ≠ L ∧ p.hi - p.lo + 1 ≤ p.mag := by
        split at helig <;> try cases helig
        rename_i h1 h2 h3
        exact ⟨nat_beq_false h1, nat_beq_false h2, Nat.ble_eq.mp h3⟩
      cases hasBest with
      | false =>
        dsimp only at h
        rcases ih (idx + 1) _ idx true out h with ⟨_, rfl⟩ | ⟨k, q, hout, hget, hq⟩
        · exact Or.inr ⟨0, p, by omega, rfl, hp_elig⟩
        · exact Or.inr ⟨k + 1, q, by omega, hget, hq⟩
      | true =>
        dsimp only at h
        split at h
        · rcases ih (idx + 1) _ idx true out h with ⟨_, rfl⟩ | ⟨k, q, hout, hget, hq⟩
          · exact Or.inr ⟨0, p, by omega, rfl, hp_elig⟩
          · exact Or.inr ⟨k + 1, q, by omega, hget, hq⟩
        · rcases ih (idx + 1) bestW bestIdx true out h with ⟨hb, heq⟩ | ⟨k, q, hout, hget, hq⟩
          · exact Or.inl ⟨rfl, heq⟩
          · exact Or.inr ⟨k + 1, q, by omega, hget, hq⟩
    · rcases ih (idx + 1) bestW bestIdx hasBest out h with ⟨hb, heq⟩ | ⟨k, q, hout, hget, hq⟩
      · exact Or.inl ⟨hb, heq⟩
      · exact Or.inr ⟨k + 1, q, by omega, hget, hq⟩

private lemma addShift_apply {p1 p2 : Bool} {m1 m2 x : ℕ}
    (hx1 : p1 = false → m1 ≤ x)
    (hx2 : p2 = false → m2 ≤ (if p1 then x + m1 else x - m1)) :
    let res := addShift p1 m1 p2 m2
    (res.1 = false → res.2 ≤ x) ∧
    (if res.1 then x + res.2 else x - res.2) =
      (if p2 then (if p1 then x + m1 else x - m1) + m2 else (if p1 then x + m1 else x - m1) - m2) := by
  unfold addShift
  simp only [nat_add_eq, nat_sub_eq]
  cases p1 <;> cases p2
  · have h1 := hx1 rfl; have h2 := hx2 rfl
    simp only [Bool.false_eq_true, ↓reduceIte] at h2 ⊢
    exact ⟨fun _ => by omega, by omega⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases h : Nat.ble m1 m2 with
    | true => simp only [↓reduceIte]; have hle := Nat.ble_eq.mp h; have h1 := hx1 rfl; exact ⟨fun hc => Bool.noConfusion hc, by omega⟩
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; have hgt := nat_ble_false h; have h1 := hx1 rfl; exact ⟨fun _ => by omega, by omega⟩
  · have h2 := hx2 rfl
    simp only [Bool.false_eq_true, ↓reduceIte] at h2 ⊢
    cases h : Nat.ble m2 m1 with
    | true => simp only [↓reduceIte]; have hle := Nat.ble_eq.mp h; exact ⟨fun hc => Bool.noConfusion hc, by omega⟩
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; have hgt := nat_ble_false h; exact ⟨fun _ => by omega, by omega⟩
  · simp only [↓reduceIte]; exact ⟨fun hc => Bool.noConfusion hc, by omega⟩

private lemma routePiece_split_props {e q : Piece} {preLo preHi : ℕ}
    (hqlo : q.lo ≤ q.hi)
    (hpre_iff : ∀ x, q.lo ≤ x → x ≤ q.hi → ((e.lo ≤ applyPiece q x ∧ applyPiece q x ≤ e.hi) ↔ preLo ≤ x ∧ x ≤ preHi)) :
    let ilo := natMax q.lo preLo
    let ihi := natMin q.hi preHi
    let res : List Piece :=
      match Nat.ble ilo ihi with
      | false => [q]
      | true =>
          let (npos, nmag) := addShift q.pos q.mag e.pos e.mag
          let ncost := Nat.add q.cost e.cost
          let mid : Piece := ⟨ilo, ihi, npos, nmag, ncost⟩
          let r1 := match Nat.blt ihi q.hi with
            | true => [mid, ⟨Nat.add ihi 1, q.hi, q.pos, q.mag, q.cost⟩]
            | false => [mid]
          match Nat.blt q.lo ilo with
          | true => ⟨q.lo, Nat.sub ilo 1, q.pos, q.mag, q.cost⟩ :: r1
          | false => r1
    res.Pairwise DisjPieces ∧
    (∀ r ∈ res, q.lo ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ q.hi) ∧
    (∀ x, inDomain res x ↔ q.lo ≤ x ∧ x ≤ q.hi) ∧
    (∀ r ∈ res, ∀ x, r.lo ≤ x → x ≤ r.hi →
      (r.pos = q.pos ∧ r.mag = q.mag ∧ r.cost = q.cost ∧ ¬ (e.lo ≤ applyPiece q x ∧ applyPiece q x ≤ e.hi)) ∨
      ((r.pos, r.mag) = addShift q.pos q.mag e.pos e.mag ∧ r.cost = q.cost + e.cost ∧
       e.lo ≤ applyPiece q x ∧ applyPiece q x ≤ e.hi)) := by
  dsimp only
  simp only [nat_add_eq, nat_sub_eq]
  have hilo_eq : natMax q.lo preLo = max q.lo preLo := natMax_eq _ _
  have hihi_eq : natMin q.hi preHi = min q.hi preHi := natMin_eq _ _
  cases hle_b : Nat.ble (natMax q.lo preLo) (natMin q.hi preHi) with
  | false =>
    dsimp only
    have hgt := nat_ble_false hle_b
    have hno : ∀ x, q.lo ≤ x → x ≤ q.hi → ¬ (e.lo ≤ applyPiece q x ∧ applyPiece q x ≤ e.hi) := by
      intro x hx1 hx2 hm; rw [hpre_iff x hx1 hx2] at hm; omega
    refine ⟨List.pairwise_singleton _ _, ?_, ?_, ?_⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨le_refl _, hqlo, le_refl _⟩
    · intro x; simp [inDomain]
    · intro r hr x hx1 hx2; simp only [List.mem_singleton] at hr; subst hr
      exact Or.inl ⟨rfl, rfl, rfl, hno x hx1 hx2⟩
  | true =>
    dsimp only
    have hle' := Nat.ble_eq.mp hle_b
    set ilo := natMax q.lo preLo
    set ihi := natMin q.hi preHi
    have hq_lo_le : q.lo ≤ ilo := by omega
    have hihi_le : ihi ≤ q.hi := by omega
    set sh := addShift q.pos q.mag e.pos e.mag
    set mid : Piece := ⟨ilo, ihi, sh.1, sh.2, q.cost + e.cost⟩
    have hmid_spec : ∀ x, mid.lo ≤ x → x ≤ mid.hi →
        (mid.pos, mid.mag) = addShift q.pos q.mag e.pos e.mag ∧ mid.cost = q.cost + e.cost ∧
        e.lo ≤ applyPiece q x ∧ applyPiece q x ≤ e.hi := by
      intro x hx1 hx2
      dsimp only [mid] at hx1 hx2 ⊢
      refine ⟨rfl, rfl, ?_⟩
      rw [hpre_iff x (by omega) (by omega)]; omega
    cases hlt_hi : Nat.blt ihi q.hi with
    | true =>
      dsimp only
      have hlt_hi' := Nat.blt_eq.mp hlt_hi
      cases hlt_lo : Nat.blt q.lo ilo with
      | true =>
        dsimp only
        have hlt_lo' := Nat.blt_eq.mp hlt_lo
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons, List.pairwise_cons]
          refine ⟨by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (left; dsimp only [mid]; omega),
            by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; left; dsimp only [mid]; omega,
            List.pairwise_singleton _ _⟩
        · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> (dsimp only [mid]; omega)
        · intro x; constructor
          · rintro ⟨r, hr, hx1, hx2⟩; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> (dsimp only [mid] at hx1 hx2; omega)
          · rintro ⟨hx1, hx2⟩
            by_cases h1 : x < ilo
            · exact ⟨_, List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩
            · by_cases h2 : x ≤ ihi
              · exact ⟨mid, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only [mid]; omega, by dsimp only [mid]; omega⟩
              · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by dsimp only; omega, by dsimp only; omega⟩
        · intro r hr x hx1 hx2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · dsimp only at hx1 hx2 ⊢
            left; refine ⟨rfl, rfl, rfl, ?_⟩; rw [hpre_iff x (by omega) (by omega)]; omega
          · exact Or.inr (hmid_spec x hx1 hx2)
          · dsimp only at hx1 hx2 ⊢
            left; refine ⟨rfl, rfl, rfl, ?_⟩; rw [hpre_iff x (by omega) (by omega)]; omega
      | false =>
        dsimp only
        have hge_lo := nat_blt_false hlt_lo
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; left; dsimp only [mid]; omega,
            List.pairwise_singleton _ _⟩
        · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> (dsimp only [mid]; omega)
        · intro x; constructor
          · rintro ⟨r, hr, hx1, hx2⟩; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> (dsimp only [mid] at hx1 hx2; omega)
          · rintro ⟨hx1, hx2⟩
            by_cases h2 : x ≤ ihi
            · exact ⟨mid, List.mem_cons_self, by dsimp only [mid]; omega, by dsimp only [mid]; omega⟩
            · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩
        · intro r hr x hx1 hx2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Or.inr (hmid_spec x hx1 hx2)
          · dsimp only at hx1 hx2 ⊢
            left; refine ⟨rfl, rfl, rfl, ?_⟩; rw [hpre_iff x (by omega) (by omega)]; omega
    | false =>
      dsimp only
      have hge_hi := nat_blt_false hlt_hi
      cases hlt_lo : Nat.blt q.lo ilo with
      | true =>
        dsimp only
        have hlt_lo' := Nat.blt_eq.mp hlt_lo
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; left; dsimp only [mid]; omega,
            List.pairwise_singleton _ _⟩
        · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> (dsimp only [mid]; omega)
        · intro x; constructor
          · rintro ⟨r, hr, hx1, hx2⟩; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> (dsimp only [mid] at hx1 hx2; omega)
          · rintro ⟨hx1, hx2⟩
            by_cases h1 : x < ilo
            · exact ⟨_, List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩
            · exact ⟨mid, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only [mid]; omega, by dsimp only [mid]; omega⟩
        · intro r hr x hx1 hx2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · dsimp only at hx1 hx2 ⊢
            left; refine ⟨rfl, rfl, rfl, ?_⟩; rw [hpre_iff x (by omega) (by omega)]; omega
          · exact Or.inr (hmid_spec x hx1 hx2)
      | false =>
        dsimp only
        have hge_lo := nat_blt_false hlt_lo
        refine ⟨List.pairwise_singleton _ _, ?_, ?_, ?_⟩
        · intro r hr; simp only [List.mem_singleton] at hr; subst hr; dsimp only [mid]; omega
        · intro x; constructor
          · rintro ⟨r, hr, hx1, hx2⟩; simp only [List.mem_singleton] at hr; subst hr; dsimp only [mid] at hx1 hx2; omega
          · rintro ⟨hx1, hx2⟩; exact ⟨mid, List.mem_cons_self, by dsimp only [mid]; omega, by dsimp only [mid]; omega⟩
        · intro r hr x hx1 hx2; simp only [List.mem_singleton] at hr; subst hr
          exact Or.inr (hmid_spec x hx1 hx2)

private lemma routePiece_props {e q : Piece} (hqlo : q.lo ≤ q.hi)
    (hqsub : ∀ x, q.lo ≤ x → x ≤ q.hi → q.pos = false → q.mag ≤ x) :
    (routePiece e q).Pairwise DisjPieces ∧
    (∀ r ∈ routePiece e q, q.lo ≤ r.lo ∧ r.lo ≤ r.hi ∧ r.hi ≤ q.hi) ∧
    (∀ x, inDomain (routePiece e q) x ↔ q.lo ≤ x ∧ x ≤ q.hi) ∧
    (∀ r ∈ routePiece e q, ∀ x, r.lo ≤ x → x ≤ r.hi →
      (r.pos = q.pos ∧ r.mag = q.mag ∧ r.cost = q.cost ∧ ¬ (e.lo ≤ applyPiece q x ∧ applyPiece q x ≤ e.hi)) ∨
      ((r.pos, r.mag) = addShift q.pos q.mag e.pos e.mag ∧ r.cost = q.cost + e.cost ∧
       e.lo ≤ applyPiece q x ∧ applyPiece q x ≤ e.hi)) := by
  unfold routePiece
  cases hqpos : q.pos with
  | false =>
    dsimp only
    have hres := routePiece_split_props (e := e) (q := q) (preLo := Nat.add e.lo q.mag) (preHi := Nat.add e.hi q.mag) hqlo (by
      intro x hx1 hx2
      have hsub := hqsub x hx1 hx2 hqpos
      unfold applyPiece; rw [hqpos, if_neg Bool.false_ne_true]; simp only [nat_add_eq]; omega)
    simpa only [hqpos] using hres
  | true =>
    dsimp only
    cases hv : Nat.ble q.mag e.hi with
    | false =>
      dsimp only
      have hgt := nat_ble_false hv
      have hno : ∀ x, q.lo ≤ x → x ≤ q.hi → ¬ (e.lo ≤ applyPiece q x ∧ applyPiece q x ≤ e.hi) := by
        intro x _ _; unfold applyPiece; rw [hqpos, if_pos rfl]; omega
      refine ⟨List.pairwise_singleton _ _, ?_, ?_, ?_⟩
      · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨le_refl _, hqlo, le_refl _⟩
      · intro x; simp [inDomain]
      · intro r hr x hx1 hx2; simp only [List.mem_singleton] at hr; subst hr
        exact Or.inl ⟨hqpos, rfl, rfl, hno x hx1 hx2⟩
    | true =>
      dsimp only
      have hle := Nat.ble_eq.mp hv
      have hres := routePiece_split_props (e := e) (q := q) (preLo := Nat.sub e.lo q.mag) (preHi := Nat.sub e.hi q.mag) hqlo (by
        intro x _ _
        unfold applyPiece; rw [hqpos, if_pos rfl]; simp only [nat_sub_eq]; omega)
      simpa only [hqpos] using hres

private lemma routeAll_valid {f : ℕ → ℕ} {L R skipIdx : ℕ} {e : Piece} {pcs : List Piece}
    (hv : ValidPieces f L R pcs)
    (hget : getPieceAt skipIdx pcs = some e)
    (he_lo : e.lo ≠ L) :
    ValidPieces f L R (routeAll skipIdx e 0 pcs) := by
  rcases hv with ⟨hdomL, hpw, hall⟩
  have he_mem : e ∈ pcs := getPieceAt_mem hget
  have he_spec := hall e he_mem
  have hsub_all : ∀ (xs : List Piece) (idx : ℕ),
      (∀ q ∈ xs, q ∈ pcs) →
      xs.Pairwise DisjPieces →
      (∀ r ∈ routeAll skipIdx e idx xs, ∃ q ∈ xs, r ∈ routePiece e q ∧
        (getPieceAt (skipIdx - idx) xs = some e → idx ≤ skipIdx → DisjPieces q e)) := by
    intro xs
    induction xs with
    | nil => intro idx _ _ r hr; simp [routeAll] at hr
    | cons q rest ih =>
      intro idx hsub hpw_xs r hr
      rw [List.pairwise_cons] at hpw_xs
      simp only [routeAll, nat_add_eq] at hr
      split at hr
      · rename_i heq
        have hidx : idx = skipIdx := nat_beq_true heq
        obtain ⟨q', hq', hr', _⟩ := ih (idx + 1) (fun a ha => hsub a (List.mem_cons_of_mem _ ha)) hpw_xs.2 r hr
        refine ⟨q', List.mem_cons_of_mem _ hq', hr', ?_⟩
        intro hg _
        have hqe : q = e := by
          have : skipIdx - idx = 0 := by omega
          rw [this] at hg; simp [getPieceAt] at hg; exact hg
        subst hqe
        have := hpw_xs.1 q' hq'; rcases this with h1 | h2; exact Or.inr h1; exact Or.inl h2
      · rename_i hne
        have hne' : idx ≠ skipIdx := nat_beq_false hne
        rw [List.mem_append] at hr
        rcases hr with hrq | hrrest
        · refine ⟨q, List.mem_cons_self, hrq, ?_⟩
          intro hg hle
          have hsub_pos : skipIdx - idx = (skipIdx - (idx + 1)) + 1 := by omega
          rw [hsub_pos] at hg; simp only [getPieceAt] at hg
          have he_rest : e ∈ rest := getPieceAt_mem hg
          exact hpw_xs.1 e he_rest
        · obtain ⟨q', hq', hr', hdisj⟩ := ih (idx + 1) (fun a ha => hsub a (List.mem_cons_of_mem _ ha)) hpw_xs.2 r hrrest
          refine ⟨q', List.mem_cons_of_mem _ hq', hr', ?_⟩
          intro hg hle
          have hsub_pos : skipIdx - idx = (skipIdx - (idx + 1)) + 1 := by omega
          rw [hsub_pos] at hg; simp only [getPieceAt] at hg
          exact hdisj hg (by omega)
  have hnot_in_e : ∀ r ∈ routeAll skipIdx e 0 pcs, DisjPieces r e := by
    intro r hr
    obtain ⟨q, hq, hrq, hdisj⟩ := hsub_all pcs 0 (fun _ h => h) hpw r hr
    have hq_spec := hall q hq
    have hrp := routePiece_props (e := e) hq_spec.2.1 (fun x hx1 hx2 => (hq_spec.2.2.2.2 x hx1 hx2).1)
    have hrb := hrp.2.1 r hrq
    have hqe : DisjPieces q e := hdisj (by simpa using hget) (Nat.zero_le _)
    rcases hqe with h1 | h2
    · left; omega
    · right; omega
  have hdom_sub : ∀ x, inDomain (routeAll skipIdx e 0 pcs) x → inDomain pcs x ∧ ¬ (e.lo ≤ x ∧ x ≤ e.hi) := by
    rintro x ⟨r, hr, hx1, hx2⟩
    obtain ⟨q, hq, hrq, _⟩ := hsub_all pcs 0 (fun _ h => h) hpw r hr
    have hq_spec := hall q hq
    have hrp := routePiece_props (e := e) hq_spec.2.1 (fun y hy1 hy2 => (hq_spec.2.2.2.2 y hy1 hy2).1)
    have hrb := hrp.2.1 r hrq
    have hde := hnot_in_e r hr
    refine ⟨⟨q, hq, by omega, by omega⟩, ?_⟩
    rcases hde with h1 | h2 <;> omega
  have hpw_out : ∀ (xs : List Piece) (idx : ℕ),
      (∀ q ∈ xs, q ∈ pcs) → xs.Pairwise DisjPieces →
      (routeAll skipIdx e idx xs).Pairwise DisjPieces := by
    intro xs
    induction xs with
    | nil => intro _ _ _; exact List.Pairwise.nil
    | cons q rest ih =>
      intro idx hsub hpw_xs
      rw [List.pairwise_cons] at hpw_xs
      simp only [routeAll, nat_add_eq]
      split
      · exact ih (idx + 1) (fun a ha => hsub a (List.mem_cons_of_mem _ ha)) hpw_xs.2
      · rw [List.pairwise_append]
        have hq_spec := hall q (hsub q List.mem_cons_self)
        have hrp := routePiece_props (e := e) hq_spec.2.1 (fun y hy1 hy2 => (hq_spec.2.2.2.2 y hy1 hy2).1)
        refine ⟨hrp.1, ih (idx + 1) (fun a ha => hsub a (List.mem_cons_of_mem _ ha)) hpw_xs.2, ?_⟩
        intro r1 hr1 r2 hr2
        have hrb1 := hrp.2.1 r1 hr1
        obtain ⟨q2, hq2, hr2q, _⟩ := hsub_all rest (idx + 1) (fun a ha => hsub a (List.mem_cons_of_mem _ ha)) hpw_xs.2 r2 hr2
        have hq2_spec := hall q2 (hsub q2 (List.mem_cons_of_mem _ hq2))
        have hrp2 := routePiece_props (e := e) hq2_spec.2.1 (fun y hy1 hy2 => (hq2_spec.2.2.2.2 y hy1 hy2).1)
        have hrb2 := hrp2.2.1 r2 hr2q
        rcases hpw_xs.1 q2 hq2 with h1 | h2
        · left; omega
        · right; omega
  have hdomL' : inDomain (routeAll skipIdx e 0 pcs) L := by
    rcases hdomL with ⟨q, hq, hqL1, hqL2⟩
    have hq_spec0 := hall q hq
    have hqne : q ≠ e := by intro hqe; subst hqe; omega
    have hcov : ∀ (xs : List Piece) (idx : ℕ),
        (∀ a ∈ xs, a ∈ pcs) → q ∈ xs →
        (idx ≤ skipIdx → getPieceAt (skipIdx - idx) xs = some e) →
        inDomain (routeAll skipIdx e idx xs) L := by
      intro xs
      induction xs with
      | nil => intro _ _ hq' _; cases hq'
      | cons a rest ih =>
        intro idx hsub hqin hget_xs
        rw [List.mem_cons] at hqin
        simp only [routeAll, nat_add_eq]
        split
        · rename_i heq
          have hidx : idx = skipIdx := nat_beq_true heq
          rcases hqin with rfl | hrest
          · exfalso
            have hg := hget_xs (by omega)
            have h0 : skipIdx - idx = 0 := by omega
            rw [h0] at hg; simp [getPieceAt] at hg
            exact hqne hg
          · exact ih (idx + 1) (fun b hb => hsub b (List.mem_cons_of_mem _ hb)) hrest (fun hle => by omega)
        · rename_i hne_idx
          have hne_idx' : idx ≠ skipIdx := nat_beq_false hne_idx
          rcases hqin with rfl | hrest
          · have ha_spec := hall q (hsub q List.mem_cons_self)
            have hrp := routePiece_props (e := e) ha_spec.2.1 (fun y hy1 hy2 => (ha_spec.2.2.2.2 y hy1 hy2).1)
            obtain ⟨r, hr, h1, h2⟩ := (hrp.2.2.1 L).mpr ⟨hqL1, hqL2⟩
            exact ⟨r, List.mem_append_left _ hr, h1, h2⟩
          · obtain ⟨r, hr, h1, h2⟩ :=
              ih (idx + 1) (fun b hb => hsub b (List.mem_cons_of_mem _ hb)) hrest (fun hle => by
                have hg := hget_xs (by omega)
                have hsub_pos : skipIdx - idx = (skipIdx - (idx + 1)) + 1 := by omega
                rw [hsub_pos] at hg; exact hg)
            exact ⟨r, List.mem_append_right _ hr, h1, h2⟩
    exact hcov pcs 0 (fun _ h => h) hq (fun _ => by simpa using hget)
  refine ⟨hdomL', ⟨hpw_out pcs 0 (fun _ h => h) hpw, ?_⟩⟩
  intro r hr
  obtain ⟨q, hq, hrq, _⟩ := hsub_all pcs 0 (fun _ h => h) hpw r hr
  have hq_spec := hall q hq
  have hrp := routePiece_props (e := e) hq_spec.2.1 (fun y hy1 hy2 => (hq_spec.2.2.2.2 y hy1 hy2).1)
  have hrb := hrp.2.1 r hrq
  have hcost_pos : 1 ≤ r.cost := by
    rcases hrp.2.2.2 r hrq r.lo (le_refl _) hrb.2.1 with ⟨_, _, hc, _⟩ | ⟨_, hc, _⟩ <;> omega
  refine ⟨by omega, hrb.2.1, by omega, hcost_pos, ?_⟩
  intro x hx1 hx2
  have hqx := hq_spec.2.2.2.2 x (by omega) (by omega)
  rcases hrp.2.2.2 r hrq x hx1 hx2 with ⟨hpos, hmag, hcost, hnot_e⟩ | ⟨hpm, hcost, he1, he2⟩
  · have happ_eq : applyPiece r x = applyPiece q x := by unfold applyPiece; rw [hpos, hmag]
    refine ⟨by rw [hpos, hmag]; exact hqx.1, by rw [happ_eq]; exact hqx.2.1,
      by rw [happ_eq]; exact hqx.2.2.1, by rw [hcost, happ_eq]; exact hqx.2.2.2.1, ?_⟩
    intro t ht1 ht2 hdom
    rw [hcost] at ht2
    exact hqx.2.2.2.2 t ht1 ht2 (hdom_sub _ hdom).1
  · have hex := he_spec.2.2.2.2 (applyPiece q x) he1 he2
    have hsh := addShift_apply (x := x) hqx.1 (by exact hex.1)
    have hrpos : r.pos = (addShift q.pos q.mag e.pos e.mag).1 := congrArg Prod.fst hpm
    have hrmag : r.mag = (addShift q.pos q.mag e.pos e.mag).2 := congrArg Prod.snd hpm
    have happ_eq : applyPiece r x = applyPiece e (applyPiece q x) := by
      unfold applyPiece; rw [hrpos, hrmag]; exact hsh.2
    refine ⟨by rw [hrpos, hrmag]; exact hsh.1,
      by rw [happ_eq]; exact hex.2.1,
      by rw [happ_eq]; exact hex.2.2.1, ?_, ?_⟩
    · rw [hcost, Nat.add_comm q.cost e.cost, Function.iterate_add_apply, hqx.2.2.2.1, hex.2.2.2.1, happ_eq]
    · intro t ht1 ht2 hdom
      rw [hcost] at ht2
      by_cases hlt : t < q.cost
      · exact hqx.2.2.2.2 t ht1 hlt (hdom_sub _ hdom).1
      · by_cases heq : t = q.cost
        · subst heq
          rw [hqx.2.2.2.1] at hdom
          exact (hdom_sub _ hdom).2 ⟨he1, he2⟩
        · have hsub_t : t = (t - q.cost) + q.cost := by omega
          rw [hsub_t, Function.iterate_add_apply, hqx.2.2.2.1] at hdom
          exact hex.2.2.2.2 (t - q.cost) (by omega) (by omega) (hdom_sub _ hdom).1

private lemma mergeAdjGo_inDomain {L : ℕ} :
    ∀ (rest : List Piece) (cur : Piece),
      cur.lo ≤ cur.hi → (∀ q ∈ rest, q.lo ≤ q.hi) →
      (∀ x, inDomain (mergeAdjGo L cur rest) x ↔ inDomain (cur :: rest) x) := by
  intro rest
  induction rest with
  | nil => intro cur _ _ x; rfl
  | cons p2 tl ih =>
    intro cur hcur hrest x
    have hp2 : p2.lo ≤ p2.hi := hrest p2 List.mem_cons_self
    have htl : ∀ q ∈ tl, q.lo ≤ q.hi := fun q hq => hrest q (List.mem_cons_of_mem _ hq)
    simp only [mergeAdjGo, nat_add_eq]
    split
    · rename_i _ ha _ _ _
      have ha' : cur.hi + 1 = p2.lo := nat_beq_true ha
      rw [ih ⟨cur.lo, p2.hi, cur.pos, cur.mag, cur.cost⟩ (by dsimp only; omega) htl x]
      constructor
      · rintro ⟨w, hw, h1, h2⟩
        rw [List.mem_cons] at hw
        rcases hw with rfl | hwtl
        · dsimp only at h1 h2
          by_cases hx : x ≤ cur.hi
          · exact ⟨cur, List.mem_cons_self, h1, hx⟩
          · exact ⟨p2, List.mem_cons_of_mem _ List.mem_cons_self, by omega, h2⟩
        · exact ⟨w, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hwtl), h1, h2⟩
      · rintro ⟨w, hw, h1, h2⟩
        rw [List.mem_cons, List.mem_cons] at hw
        rcases hw with rfl | rfl | hwtl
        · exact ⟨_, List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩
        · exact ⟨_, List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩
        · exact ⟨w, List.mem_cons_of_mem _ hwtl, h1, h2⟩
    · constructor
      · rintro ⟨w, hw, h1, h2⟩
        rw [List.mem_cons] at hw
        rcases hw with hw_eq | hwtl
        · rw [hw_eq] at h1 h2; exact ⟨cur, List.mem_cons_self, h1, h2⟩
        · obtain ⟨w', hw', h1', h2'⟩ := (ih p2 hp2 htl x).mp ⟨w, hwtl, h1, h2⟩
          exact ⟨w', List.mem_cons_of_mem _ hw', h1', h2'⟩
      · rintro ⟨w, hw, h1, h2⟩
        rw [List.mem_cons] at hw
        rcases hw with hw_eq | hwtl
        · rw [hw_eq] at h1 h2; exact ⟨cur, List.mem_cons_self, h1, h2⟩
        · obtain ⟨w', hw', h1', h2'⟩ := (ih p2 hp2 htl x).mpr ⟨w, hwtl, h1, h2⟩
          exact ⟨w', List.mem_cons_of_mem _ hw', h1', h2'⟩

private lemma mergeAdjGo_validD {f : ℕ → ℕ} {L R : ℕ} {D : ℕ → Prop} :
    ∀ (rest : List Piece) (cur : Piece),
      ValidPiecesD f L R D (cur :: rest) →
      ValidPiecesD f L R D (mergeAdjGo L cur rest) := by
  intro rest
  induction rest with
  | nil => intro cur hv; exact hv
  | cons p2 tl ih =>
    intro cur hv
    rcases hv with ⟨hpw, hall⟩
    rw [List.pairwise_cons, List.pairwise_cons] at hpw
    have hcur := hall cur List.mem_cons_self
    have hp2 := hall p2 (List.mem_cons_of_mem _ List.mem_cons_self)
    rcases hcur with ⟨hcurL, hcur_lh, hcurR, hcur_c, hcur_x⟩
    rcases hp2 with ⟨hp2L, hp2_lh, hp2R, hp2_c, hp2_x⟩
    simp only [mergeAdjGo, nat_add_eq]
    split
    · rename_i _ hadj hpos hmag hcost
      have hadj' : cur.hi + 1 = p2.lo := nat_beq_true hadj
      have hpos' : cur.pos = p2.pos := beq_iff_eq.mp hpos
      have hmag' : cur.mag = p2.mag := nat_beq_true hmag
      have hcost' : cur.cost = p2.cost := nat_beq_true hcost
      let merged : Piece := ⟨cur.lo, p2.hi, cur.pos, cur.mag, cur.cost⟩
      apply ih merged
      refine ⟨?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hpw.2.2⟩
        intro q hq
        have hqs := hall q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
        have hd1 := hpw.1 q (List.mem_cons_of_mem _ hq)
        have hd2 := hpw.2.1 q hq
        dsimp only [DisjPieces, merged] at hd1 hd2 ⊢
        rcases hd1 with h1 | h1 <;> rcases hd2 with h2 | h2 <;> omega
      · intro q hq
        rw [List.mem_cons] at hq
        rcases hq with rfl | htl
        · refine ⟨hcurL, by dsimp only [merged]; omega, hp2R, hcur_c, ?_⟩
          intro x hx1 hx2
          dsimp only [merged] at hx1 hx2
          by_cases hx : x ≤ cur.hi
          · exact hcur_x x hx1 hx
          · have hpx := hp2_x x (by omega) hx2
            have happ : applyPiece merged x = applyPiece p2 x := by
              unfold applyPiece; dsimp only [merged]; rw [hpos', hmag']
            refine ⟨by dsimp only [merged]; rw [hpos', hmag']; exact hpx.1,
              by rw [happ]; exact hpx.2.1,
              by rw [happ]; exact hpx.2.2.1,
              by rw [happ]; dsimp only [merged]; rw [hcost']; exact hpx.2.2.2.1,
              by dsimp only [merged]; rw [hcost']; exact hpx.2.2.2.2⟩
        · exact hall q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htl))
    · have hv_tail : ValidPiecesD f L R D (p2 :: tl) :=
        ⟨List.pairwise_cons.mpr ⟨hpw.2.1, hpw.2.2⟩,
         fun q hq => hall q (List.mem_cons_of_mem _ hq)⟩
      have hres := ih p2 hv_tail
      have hdom_tail := mergeAdjGo_inDomain (L := L) tl p2 hp2_lh
        (fun q hq => (hall q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))).2.1)
      refine ⟨?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hres.1⟩
        intro q hq
        have hqs := hres.2 q hq
        have hq_lo_in : inDomain (p2 :: tl) q.lo := (hdom_tail q.lo).mp ⟨q, hq, le_refl _, hqs.2.1⟩
        rcases hq_lo_in with ⟨w1, hw1, hw1a, hw1b⟩
        have hd1 := hpw.1 w1 hw1
        dsimp only [DisjPieces] at hd1 ⊢
        by_cases h1 : cur.hi < q.lo
        · exact Or.inl h1
        · by_cases h2 : q.hi < cur.lo
          · exact Or.inr h2
          · exfalso
            have hcur_in : q.lo < cur.lo := by rcases hd1 with h | h <;> omega
            have hcur_mem : inDomain (p2 :: tl) cur.lo :=
              (hdom_tail cur.lo).mp ⟨q, hq, by omega, by omega⟩
            rcases hcur_mem with ⟨w, hw, hwa, hwb⟩
            have hdw := hpw.1 w hw
            dsimp only [DisjPieces] at hdw
            rcases hdw with h | h <;> omega
      · intro q hq
        rw [List.mem_cons] at hq
        rcases hq with rfl | hqtl
        · exact ⟨hcurL, hcur_lh, hcurR, hcur_c, hcur_x⟩
        · exact hres.2 q hqtl

private lemma mergeAdj_valid {f : ℕ → ℕ} {L R : ℕ} {pcs : List Piece}
    (hv : ValidPieces f L R pcs) :
    ValidPieces f L R (mergeAdj L pcs) := by
  cases pcs with
  | nil => exact hv
  | cons cur rest =>
    rcases hv with ⟨hdomL, hvD⟩
    have hdom_eq := mergeAdjGo_inDomain (L := L) rest cur
      (hvD.2 cur List.mem_cons_self).2.1
      (fun q hq => (hvD.2 q (List.mem_cons_of_mem _ hq)).2.1)
    have hvD' := mergeAdjGo_validD rest cur hvD
    refine ⟨(hdom_eq L).mpr hdomL, ⟨hvD'.1, ?_⟩⟩
    intro p hp
    have hps := hvD'.2 p hp
    refine ⟨hps.1, hps.2.1, hps.2.2.1, hps.2.2.2.1, ?_⟩
    intro x hx1 hx2
    have hpx := hps.2.2.2.2 x hx1 hx2
    refine ⟨hpx.1, hpx.2.1, hpx.2.2.1, hpx.2.2.2.1, ?_⟩
    intro t ht1 ht2 hdm
    exact hpx.2.2.2.2 t ht1 ht2 ((hdom_eq _).mp hdm)

private lemma rauzyLoop_valid {f : ℕ → ℕ} {L R : ℕ} :
    ∀ (fuel : ℕ) (pcs : List Piece),
      ValidPieces f L R pcs → ValidPieces f L R (rauzyLoop L fuel pcs) := by
  intro fuel
  induction fuel with
  | zero => intro pcs hv; exact hv
  | succ fuel ih =>
    intro pcs hv
    simp only [rauzyLoop]
    split
    · split
      · exact hv
      · rename_i idx hpick
        split
        · exact hv
        · rename_i e hget
          have hspec := pickBestGo_spec pcs 0 0 0 false idx hpick
          rcases hspec with ⟨hc, _⟩ | ⟨k, p, hidx, hget', _, hp_lo, _⟩
          · cases hc
          · have hk : idx = k := by omega
            subst hk
            rw [hget'] at hget
            have hpe : p = e := Option.some.inj hget
            subst hpe
            exact ih _ (mergeAdj_valid (routeAll_valid hv hget' hp_lo))
    · exact hv

def findPiece (x : ℕ) : List Piece → Option Piece
  | [] => none
  | p :: rest =>
      match Nat.ble p.lo x, Nat.ble x p.hi with
      | true, true => some p
      | _, _ => findPiece x rest

private lemma findPiece_sound {x : ℕ} {pcs : List Piece} {p : Piece}
    (h : findPiece x pcs = some p) : p ∈ pcs ∧ p.lo ≤ x ∧ x ≤ p.hi := by
  induction pcs with
  | nil => simp [findPiece] at h
  | cons q rest ih =>
    simp only [findPiece] at h
    split at h
    · rename_i h1 h2
      have hqp : q = p := Option.some.inj h
      subst hqp
      exact ⟨List.mem_cons_self, Nat.ble_eq.mp h1, Nat.ble_eq.mp h2⟩
    · obtain ⟨hm, h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, h1, h2⟩

def walkJumpGo (L steps : ℕ) (pcs : List Piece) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, cur, done =>
      match findPiece cur pcs with
      | none => false
      | some p =>
          match Nat.beq p.mag 0 with
          | true => Nat.beq cur L && Nat.beq (Nat.add done p.cost) steps
          | false =>
              match p.pos with
              | true =>
                  let k := Nat.add (Nat.div (Nat.sub p.hi cur) p.mag) 1
                  let cur' := Nat.add cur (Nat.mul k p.mag)
                  let done' := Nat.add done (Nat.mul k p.cost)
                  match Nat.beq done' steps with
                  | true => Nat.beq cur' L
                  | false =>
                      match Nat.blt done' steps, Nat.beq cur' L with
                      | true, false => walkJumpGo L steps pcs fuel cur' done'
                      | _, _ => false
              | false =>
                  let hitL := Nat.beq p.lo L && Nat.beq (Nat.mod (Nat.sub cur L) p.mag) 0
                  let k := match hitL with
                    | true => Nat.div (Nat.sub cur L) p.mag
                    | false => Nat.add (Nat.div (Nat.sub cur p.lo) p.mag) 1
                  let cur' := Nat.sub cur (Nat.mul k p.mag)
                  let done' := Nat.add done (Nat.mul k p.cost)
                  match Nat.beq done' steps with
                  | true => Nat.beq cur' L
                  | false =>
                      match Nat.blt done' steps, Nat.beq cur' L with
                      | true, false => walkJumpGo L steps pcs fuel cur' done'
                      | _, _ => false

def checkWalkRauzy (L R : ℕ) (m1 m2 : List (ℕ × ℕ × ℕ)) : Bool :=
  let steps := Nat.div (Nat.add (Nat.sub R L) 1) 2
  let pcs := rauzyLoop L 30 (buildPieces L m2 m1)
  walkJumpGo L steps pcs 600 L 0

private lemma walk_pos_jump {f : ℕ → ℕ} {L R : ℕ} {pcs : List Piece} {p : Piece} {cur : ℕ}
    (hv : ValidPieces f L R pcs) (hp : p ∈ pcs) (hpos : p.pos = true) (hmag : 0 < p.mag)
    (hcur1 : p.lo ≤ cur) (_hcur2 : cur ≤ p.hi) :
    ∀ k, (∀ j, j < k → cur + j * p.mag ≤ p.hi) →
      f^[k * p.cost] cur = cur + k * p.mag ∧
      (∀ t, 0 < t → t < k * p.cost → f^[t] cur ≠ L) := by
  have hps := hv.2.2 p hp
  have hstep : ∀ j, cur + j * p.mag ≤ p.hi →
      f^[p.cost] (cur + j * p.mag) = cur + (j + 1) * p.mag ∧
      (∀ r, 0 < r → r < p.cost → f^[r] (cur + j * p.mag) ≠ L) := by
    intro j hj
    have hx := hps.2.2.2.2 (cur + j * p.mag) (by omega) hj
    have happ : applyPiece p (cur + j * p.mag) = cur + (j + 1) * p.mag := by
      unfold applyPiece; rw [hpos, if_pos rfl]; ring
    refine ⟨by rw [hx.2.2.2.1, happ], ?_⟩
    intro r hr1 hr2 hL
    have hnot := hx.2.2.2.2 r hr1 hr2
    rw [hL] at hnot
    exact hnot hv.1
  intro k hk
  have hiter : ∀ j, j ≤ k → f^[j * p.cost] cur = cur + j * p.mag := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := (hstep j (hk j (by omega))).1
      rw [Nat.succ_mul, Nat.add_comm (j * p.cost) p.cost, Function.iterate_add_apply, h1, h2]
  refine ⟨hiter k (le_refl _), ?_⟩
  intro t ht1 ht2
  have hcpos : 0 < p.cost := by omega
  set q := t / p.cost
  set r := t % p.cost
  have hqr : t = r + q * p.cost := by
    have := Nat.div_add_mod t p.cost
    dsimp only [q, r]
    rw [Nat.mul_comm] at this
    omega
  have hq_lt : q < k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ht2)
  have hr_lt : r < p.cost := Nat.mod_lt t hcpos
  rw [hqr, Function.iterate_add_apply, hiter q (by omega)]
  by_cases hr0 : r = 0
  · rw [hr0, Function.iterate_zero_apply]
    have hq_pos : 0 < q := by
      have : r + q * p.cost = q * p.cost := by omega
      have hqp : 0 < q * p.cost := by omega
      exact Nat.pos_of_mul_pos_right hqp
    have hqm : 0 < q * p.mag := Nat.mul_pos hq_pos hmag
    have hpL : L ≤ p.lo := hps.1
    omega
  · exact (hstep q (hk q hq_lt)).2 r (by omega) hr_lt

private lemma walk_neg_jump {f : ℕ → ℕ} {L R : ℕ} {pcs : List Piece} {p : Piece} {cur : ℕ}
    (hv : ValidPieces f L R pcs) (hp : p ∈ pcs) (hpos : p.pos = false) (hmag : 0 < p.mag)
    (_hcur1 : p.lo ≤ cur) (hcur2 : cur ≤ p.hi) :
    ∀ k, (∀ j, j < k → p.lo + j * p.mag ≤ cur) →
      (∀ j, 0 < j → j < k → cur - j * p.mag ≠ L) →
      k * p.mag ≤ cur ∧
      f^[k * p.cost] cur = cur - k * p.mag ∧
      (∀ t, 0 < t → t < k * p.cost → f^[t] cur ≠ L) := by
  have hps := hv.2.2 p hp
  have hstep : ∀ j, p.lo + j * p.mag ≤ cur →
      (j + 1) * p.mag ≤ cur ∧
      f^[p.cost] (cur - j * p.mag) = cur - (j + 1) * p.mag ∧
      (∀ r, 0 < r → r < p.cost → f^[r] (cur - j * p.mag) ≠ L) := by
    intro j hj
    have hx := hps.2.2.2.2 (cur - j * p.mag) (by omega) (by omega)
    have hsub := hx.1 hpos
    have hle : (j + 1) * p.mag ≤ cur := by rw [Nat.add_mul, Nat.one_mul]; omega
    have happ : applyPiece p (cur - j * p.mag) = cur - (j + 1) * p.mag := by
      unfold applyPiece; rw [hpos, if_neg Bool.false_ne_true]; rw [Nat.add_mul, Nat.one_mul]; omega
    refine ⟨hle, by rw [hx.2.2.2.1, happ], ?_⟩
    intro r hr1 hr2 hL
    have hnot := hx.2.2.2.2 r hr1 hr2
    rw [hL] at hnot
    exact hnot hv.1
  intro k hk hneL
  have hiter : ∀ j, j ≤ k → j * p.mag ≤ cur ∧ f^[j * p.cost] cur = cur - j * p.mag := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j (hk j (by omega))
      refine ⟨h2.1, ?_⟩
      rw [Nat.succ_mul, Nat.add_comm (j * p.cost) p.cost, Function.iterate_add_apply, h1.2, h2.2.1]
  refine ⟨(hiter k (le_refl _)).1, (hiter k (le_refl _)).2, ?_⟩
  intro t ht1 ht2
  have hcpos : 0 < p.cost := by omega
  set q := t / p.cost
  set r := t % p.cost
  have hqr : t = r + q * p.cost := by
    have := Nat.div_add_mod t p.cost
    dsimp only [q, r]
    rw [Nat.mul_comm] at this
    omega
  have hq_lt : q < k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ht2)
  have hr_lt : r < p.cost := Nat.mod_lt t hcpos
  rw [hqr, Function.iterate_add_apply, (hiter q (by omega)).2]
  by_cases hr0 : r = 0
  · rw [hr0, Function.iterate_zero_apply]
    have hq_pos : 0 < q := by
      have : r + q * p.cost = q * p.cost := by omega
      have hqp : 0 < q * p.cost := by omega
      exact Nat.pos_of_mul_pos_right hqp
    exact hneL q hq_pos hq_lt
  · exact (hstep q (hk q hq_lt)).2.2 r (by omega) hr_lt

private lemma walkJumpGo_sound {f : ℕ → ℕ} {L R steps : ℕ} {pcs : List Piece}
    (hv : ValidPieces f L R pcs) :
    ∀ (fuel cur done : ℕ),
      f^[done] L = cur →
      (∀ t, 0 < t → t ≤ done → f^[t] L ≠ L) →
      walkJumpGo L steps pcs fuel cur done = true →
      f^[steps] L = L ∧ ∀ t, 0 < t → t < steps → f^[t] L ≠ L := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; simp [walkJumpGo] at h
  | succ fuel ih =>
    intro cur done hcur hprev h
    simp only [walkJumpGo, nat_add_eq, nat_sub_eq, nat_mul_eq, nat_div_eq, nat_mod_eq] at h
    cases hfind : findPiece cur pcs with
    | none => rw [hfind] at h; simp at h
    | some p =>
      rw [hfind] at h
      dsimp only at h
      obtain ⟨hp_mem, hp1, hp2⟩ := findPiece_sound hfind
      have hps := hv.2.2 p hp_mem
      cases hmag0 : Nat.beq p.mag 0 with
      | true =>
        rw [hmag0] at h
        dsimp only at h
        have hmag_eq : p.mag = 0 := nat_beq_true hmag0
        simp only [Bool.and_eq_true] at h
        have hcurL : cur = L := nat_beq_true h.1
        have hst : done + p.cost = steps := nat_beq_true h.2
        have hdone0 : done = 0 := by
          by_contra hd
          exact hprev done (by omega) (le_refl _) (by rw [hcur, hcurL])
        subst hdone0
        have hx := hps.2.2.2.2 cur hp1 hp2
        have happ : applyPiece p cur = cur := by unfold applyPiece; rw [hmag_eq]; split_ifs <;> omega
        refine ⟨?_, ?_⟩
        · have : steps = p.cost := by omega
          rw [this, ← hcurL, hx.2.2.2.1, happ]
        · intro t ht1 ht2 hL
          have hnot := hx.2.2.2.2 t ht1 (by omega)
          rw [hcurL, hL] at hnot
          exact hnot hv.1
      | false =>
        rw [hmag0] at h
        dsimp only at h
        have hmag_pos : 0 < p.mag := by have := nat_beq_false hmag0; omega
        cases hpos : p.pos with
        | true =>
          rw [hpos] at h
          dsimp only at h
          set k := (p.hi - cur) / p.mag + 1
          set cur' := cur + k * p.mag
          set done' := done + k * p.cost
          have hk_ok : ∀ j, j < k → cur + j * p.mag ≤ p.hi := by
            intro j hj
            have hjle : j ≤ (p.hi - cur) / p.mag := by omega
            have hmul : j * p.mag ≤ (p.hi - cur) / p.mag * p.mag := Nat.mul_le_mul_right _ hjle
            have hdm := Nat.div_mul_le_self (p.hi - cur) p.mag
            omega
          obtain ⟨hjump, hmid⟩ := walk_pos_jump hv hp_mem hpos hmag_pos hp1 hp2 k hk_ok
          have hcur' : f^[done'] L = cur' := by
            have : done' = k * p.cost + done := by omega
            rw [this, Function.iterate_add_apply, hcur, hjump]
          have hmid_all : ∀ t, 0 < t → t < done' → f^[t] L ≠ L := by
            intro t ht1 ht2
            by_cases hle : t ≤ done
            · exact hprev t ht1 hle
            · have hsub : t = (t - done) + done := by omega
              rw [hsub, Function.iterate_add_apply, hcur]
              exact hmid (t - done) (by omega) (by omega)
          cases hdone_eq : Nat.beq done' steps with
          | true =>
            rw [hdone_eq] at h
            dsimp only at h
            have hst : done' = steps := nat_beq_true hdone_eq
            have hcL : cur' = L := nat_beq_true h
            exact ⟨by rw [← hst, hcur', hcL], by rw [← hst]; exact hmid_all⟩
          | false =>
            rw [hdone_eq] at h
            dsimp only at h
            split at h <;> try cases h
            rename_i hlt_d hne_L
            have hne_L' : cur' ≠ L := nat_beq_false hne_L
            have hprev' : ∀ t, 0 < t → t ≤ done' → f^[t] L ≠ L := by
              intro t ht1 ht2
              by_cases hlt : t < done'
              · exact hmid_all t ht1 hlt
              · have heq : t = done' := by omega
                rw [heq, hcur']; exact hne_L'
            exact ih cur' done' hcur' hprev' h
        | false =>
          rw [hpos] at h
          dsimp only at h
          set hitL := Nat.beq p.lo L && Nat.beq ((cur - L) % p.mag) 0
          set k := match hitL with
            | true => (cur - L) / p.mag
            | false => (cur - p.lo) / p.mag + 1
          set cur' := cur - k * p.mag
          set done' := done + k * p.cost
          have hcur_gt_L : L < cur := by
            have hx := hps.2.2.2.2 cur hp1 hp2
            have hsub := hx.1 hpos
            have hge := hx.2.1
            unfold applyPiece at hge; rw [hpos, if_neg Bool.false_ne_true] at hge
            omega
          have hk_ok : ∀ j, j < k → p.lo + j * p.mag ≤ cur := by
            intro j hj
            cases hhit : hitL with
            | true =>
              have hhit' := hhit
              simp only [hitL, Bool.and_eq_true] at hhit'
              have hloL : p.lo = L := nat_beq_true hhit'.1
              have hk_eq : k = (cur - L) / p.mag := by simp only [k, hhit]
              have hjle : j ≤ (cur - L) / p.mag := by omega
              have hmul : j * p.mag ≤ (cur - L) / p.mag * p.mag := Nat.mul_le_mul_right _ hjle
              have hdm := Nat.div_mul_le_self (cur - L) p.mag
              omega
            | false =>
              have hk_eq : k = (cur - p.lo) / p.mag + 1 := by simp only [k, hhit]
              have hjle : j ≤ (cur - p.lo) / p.mag := by omega
              have hmul : j * p.mag ≤ (cur - p.lo) / p.mag * p.mag := Nat.mul_le_mul_right _ hjle
              have hdm := Nat.div_mul_le_self (cur - p.lo) p.mag
              omega
          have hne_mid : ∀ j, 0 < j → j < k → cur - j * p.mag ≠ L := by
            intro j hj1 hj2 heq
            cases hhit : hitL with
            | true =>
              have hhit' := hhit
              simp only [hitL, Bool.and_eq_true] at hhit'
              have hmod0 : (cur - L) % p.mag = 0 := nat_beq_true hhit'.2
              have hk_eq : k = (cur - L) / p.mag := by simp only [k, hhit]
              have hmul_eq : k * p.mag = cur - L := by
                have := Nat.div_add_mod (cur - L) p.mag
                rw [hmod0, Nat.add_zero, Nat.mul_comm] at this
                rw [hk_eq]; exact this
              have hjm_lt : j * p.mag < k * p.mag := Nat.mul_lt_mul_of_pos_right hj2 hmag_pos
              omega
            | false =>
              have hlo_le : p.lo + j * p.mag ≤ cur := hk_ok j hj2
              have hpL : L ≤ p.lo := hps.1
              have hloL : p.lo = L := by omega
              have hsub_eq : cur - L = j * p.mag := by omega
              have hmod0 : (cur - L) % p.mag = 0 := by rw [hsub_eq, Nat.mul_mod_left]
              have htrue : hitL = true := by
                simp only [hitL, Bool.and_eq_true]
                exact ⟨by rw [hloL]; simp, by rw [hmod0]; simp⟩
              rw [htrue] at hhit; cases hhit
          obtain ⟨_, hjump, hmid⟩ := walk_neg_jump hv hp_mem hpos hmag_pos hp1 hp2 k hk_ok hne_mid
          have hcur' : f^[done'] L = cur' := by
            have : done' = k * p.cost + done := by omega
            rw [this, Function.iterate_add_apply, hcur, hjump]
          have hmid_all : ∀ t, 0 < t → t < done' → f^[t] L ≠ L := by
            intro t ht1 ht2
            by_cases hle : t ≤ done
            · exact hprev t ht1 hle
            · have hsub : t = (t - done) + done := by omega
              rw [hsub, Function.iterate_add_apply, hcur]
              exact hmid (t - done) (by omega) (by omega)
          cases hdone_eq : Nat.beq done' steps with
          | true =>
            rw [hdone_eq] at h
            dsimp only at h
            have hst : done' = steps := nat_beq_true hdone_eq
            have hcL : cur' = L := nat_beq_true h
            exact ⟨by rw [← hst, hcur', hcL], by rw [← hst]; exact hmid_all⟩
          | false =>
            rw [hdone_eq] at h
            dsimp only at h
            split at h <;> try cases h
            rename_i hlt_d hne_L
            have hne_L' : cur' ≠ L := nat_beq_false hne_L
            have hprev' : ∀ t, 0 < t → t ≤ done' → f^[t] L ≠ L := by
              intro t ht1 ht2
              by_cases hlt : t < done'
              · exact hmid_all t ht1 hlt
              · have heq : t = done' := by omega
                rw [heq, hcur']; exact hne_L'
            exact ih cur' done' hcur' hprev' h

private lemma checkWalkGo_of_orbit {L steps : ℕ} {m1 m2 : List (ℕ × ℕ × ℕ)} :
    ∀ k cur, k ≤ steps →
      (S1.evalRootMatching m2 ∘ S1.evalRootMatching m1)^[k] cur = L →
      (∀ j, j < k → k - j < steps →
        (S1.evalRootMatching m2 ∘ S1.evalRootMatching m1)^[j] cur ≠ L) →
      S1.checkWalkGo L steps m1 m2 k cur = true := by
  intro k
  induction k with
  | zero =>
    intro cur _ hper _
    simp only [S1.checkWalkGo, beq_iff_eq]
    exact hper
  | succ k ih =>
    intro cur hk hper hmin
    simp only [S1.checkWalkGo]
    have hnot : ¬ (Nat.blt (k + 1) steps && (cur == L)) = true := by
      simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq]
      rintro ⟨hlt, rfl⟩
      exact hmin 0 (by omega) (by omega) rfl
    have hfalse : (Nat.blt (k + 1) steps && (cur == L)) = false := Bool.eq_false_iff.mpr hnot
    rw [hfalse]
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply ih (S1.evalRootMatching m2 (S1.evalRootMatching m1 cur)) (by omega)
    · rw [Function.iterate_succ_apply] at hper; exact hper
    · intro j hj hdiff
      have := hmin (j + 1) (by omega) (by omega)
      rw [Function.iterate_succ_apply] at this
      exact this

theorem checkWalkRauzy_implies_checkTwoMatchings {L R : ℕ} {m1 m2 : List (ℕ × ℕ × ℕ)}
    (hLR : L + 1 ≤ R)
    (heven : (R - L + 1) % 2 = 0)
    (hm1 : S1.checkRootMatching L R m1 = true)
    (hm2 : S1.checkRootMatching L R m2 = true)
    (hwalk : checkWalkRauzy L R m1 m2 = true) :
    S1.checkTwoMatchings L R m1 m2 = true := by
  unfold checkWalkRauzy at hwalk
  have hv0 := buildPieces_valid (by omega) hm1 hm2
  have hv := rauzyLoop_valid 30 (buildPieces L m2 m1) hv0
  obtain ⟨hper, hmin⟩ := walkJumpGo_sound hv 600 L 0 rfl (fun t ht1 ht2 => by omega) hwalk
  have hcw : S1.checkWalk L ((R - L + 1) / 2) m1 m2 = true := by
    unfold S1.checkWalk
    exact checkWalkGo_of_orbit ((R - L + 1) / 2) L (le_refl _) hper
      (fun j hj hdiff => hmin j (by omega) hj)
  simp only [S1.checkTwoMatchings, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨hLR, heven⟩, hm1⟩, hm2⟩, hcw⟩

/-! ### Part 3: Budget Step Functions & O(1) Interval Coverage -/

def req4 (n : ℕ) : ℕ :=
  if (54 ≤ n ∧ n ≤ 507 ∧ n ≠ 278 ∧ n ≠ 284 ∧ n ≠ 285 ∧ n ≠ 287) ∨ (695 ≤ n ∧ n ≤ 717) then 2 else 1

def req5 (n : ℕ) : ℕ :=
  if n ≤ 251 then 4 else if n ≤ 795 then 3 else if n ≤ 5098 then 2 else 1

def req6 (n : ℕ) : ℕ :=
  if n ≤ 288 ∧ n ≠ 230 then 3 else if n ≤ 1053 then 2 else 1

def req7 (n : ℕ) : ℕ :=
  if n ≤ 79 then 5 else if n ≤ 237 then 4 else if n ≤ 963 then 3 else if n ≤ 1800 then 2 else 1

def minReq4 (a b : ℕ) : ℕ :=
  if (54 ≤ a ∧ b ≤ 507 ∧ (b < 278 ∨ 287 < a ∨ (279 ≤ a ∧ b ≤ 283) ∨ (a = 286 ∧ b = 286))) ∨
     (695 ≤ a ∧ b ≤ 717) then 2 else 1

def maxReq4 (a b : ℕ) : ℕ :=
  if (a ≤ 507 ∧ 54 ≤ b) ∨ (a ≤ 717 ∧ 695 ≤ b) then 2 else 1

def minReq6 (a b : ℕ) : ℕ :=
  if b ≤ 288 ∧ (b < 230 ∨ 230 < a) then 3 else if b ≤ 1053 then 2 else 1

def maxReq6 (a b : ℕ) : ℕ :=
  if a ≤ 288 ∧ ¬ (a = 230 ∧ b = 230) then 3 else if a ≤ 1053 then 2 else 1

lemma req_bounds (n : ℕ) :
    (1 ≤ req4 n ∧ req4 n ≤ 2) ∧ (1 ≤ req5 n ∧ req5 n ≤ 4) ∧
    (1 ≤ req6 n ∧ req6 n ≤ 3) ∧ (1 ≤ req7 n ∧ req7 n ≤ 5) := by
  unfold req4 req5 req6 req7
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (split_ifs <;> omega)

lemma req4_between {a b x : ℕ} (h1 : a ≤ x) (h2 : x ≤ b) :
    minReq4 a b ≤ req4 x ∧ req4 x ≤ maxReq4 a b := by
  unfold req4 minReq4 maxReq4; split_ifs <;> omega

lemma req5_between {a b x : ℕ} (h1 : a ≤ x) (h2 : x ≤ b) :
    req5 b ≤ req5 x ∧ req5 x ≤ req5 a := by
  unfold req5; split_ifs <;> omega

lemma req6_between {a b x : ℕ} (h1 : a ≤ x) (h2 : x ≤ b) :
    minReq6 a b ≤ req6 x ∧ req6 x ≤ maxReq6 a b := by
  unfold req6 minReq6 maxReq6; split_ifs <;> omega

lemma req7_between {a b x : ℕ} (h1 : a ≤ x) (h2 : x ≤ b) :
    req7 b ≤ req7 x ∧ req7 x ≤ req7 a := by
  unfold req7; split_ifs <;> omega

def checkBudgetRange (nLo nHi pLo pHi s : ℕ) : Bool :=
  Nat.ble (maxReq4 nLo nHi + if s == 4 then 1 else 0) (minReq4 pLo pHi) &&
  Nat.ble (req5 nLo + if s == 5 then 1 else 0) (req5 pHi) &&
  Nat.ble (maxReq6 nLo nHi + if s == 6 then 1 else 0) (minReq6 pLo pHi) &&
  Nat.ble (req7 nLo + if s == 7 then 1 else 0) (req7 pHi)

theorem checkBudgetRange_sound {nLo nHi pLo pHi s n p : ℕ}
    (hb : checkBudgetRange nLo nHi pLo pHi s = true)
    (hn1 : nLo ≤ n) (hn2 : n ≤ nHi) (hp1 : pLo ≤ p) (hp2 : p ≤ pHi) :
    (if s = 4 then req4 n + 1 else req4 n) ≤ req4 p ∧
    (if s = 5 then req5 n + 1 else req5 n) ≤ req5 p ∧
    (if s = 6 then req6 n + 1 else req6 n) ≤ req6 p ∧
    (if s = 7 then req7 n + 1 else req7 n) ≤ req7 p := by
  simp only [checkBudgetRange, Bool.and_eq_true, Nat.ble_eq] at hb
  have h4 := req4_between hn1 hn2
  have h4p := req4_between hp1 hp2
  have h5 := req5_between hn1 hn2
  have h5p := req5_between hp1 hp2
  have h6 := req6_between hn1 hn2
  have h6p := req6_between hp1 hp2
  have h7 := req7_between hn1 hn2
  have h7p := req7_between hp1 hp2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hb.1.1.1; split_ifs at this ⊢ <;> simp_all <;> omega
  · have := hb.1.1.2; split_ifs at this ⊢ <;> simp_all <;> omega
  · have := hb.1.2; split_ifs at this ⊢ <;> simp_all <;> omega
  · have := hb.2; split_ifs at this ⊢ <;> simp_all <;> omega

def checkBudgetPoint (n p s : ℕ) : Bool :=
  Nat.ble (req4 n + if s == 4 then 1 else 0) (req4 p) &&
  Nat.ble (req5 n + if s == 5 then 1 else 0) (req5 p) &&
  Nat.ble (req6 n + if s == 6 then 1 else 0) (req6 p) &&
  Nat.ble (req7 n + if s == 7 then 1 else 0) (req7 p)

theorem checkBudgetPoint_sound {n p s : ℕ} (hb : checkBudgetPoint n p s = true) :
    (if s = 4 then req4 n + 1 else req4 n) ≤ req4 p ∧
    (if s = 5 then req5 n + 1 else req5 n) ≤ req5 p ∧
    (if s = 6 then req6 n + 1 else req6 n) ≤ req6 p ∧
    (if s = 7 then req7 n + 1 else req7 n) ≤ req7 p := by
  simp only [checkBudgetPoint, Bool.and_eq_true, Nat.ble_eq] at hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hb.1.1.1; split_ifs at this ⊢ <;> simp_all
  · have := hb.1.1.2; split_ifs at this ⊢ <;> simp_all
  · have := hb.1.2; split_ifs at this ⊢ <;> simp_all
  · have := hb.2; split_ifs at this ⊢ <;> simp_all

def checkIntervalCover (cur target : ℕ) : List (ℕ × ℕ) → Bool
  | [] => Nat.blt target cur
  | (lo, hi) :: rest =>
      Nat.ble lo cur && checkIntervalCover (natMax cur (Nat.add hi 1)) target rest

theorem checkIntervalCover_sound {cur target : ℕ} {ivs : List (ℕ × ℕ)}
    (hc : checkIntervalCover cur target ivs = true) :
    ∀ n, cur ≤ n → n ≤ target → ∃ p ∈ ivs, p.1 ≤ n ∧ n ≤ p.2 := by
  induction ivs generalizing cur with
  | nil =>
    intro n h1 h2
    simp only [checkIntervalCover, Nat.blt_eq] at hc
    omega
  | cons hd tl ih =>
    rcases hd with ⟨lo, hi⟩
    simp only [checkIntervalCover, Bool.and_eq_true, Nat.ble_eq, natMax_eq, nat_add_eq] at hc
    intro n h1 h2
    by_cases hle : n ≤ hi
    · exact ⟨(lo, hi), List.mem_cons_self, by omega, hle⟩
    · obtain ⟨p, hp, hlo, hhi⟩ := ih hc.2 n (by omega) h2
      exact ⟨p, List.mem_cons_of_mem _ hp, hlo, hhi⟩

def mergeSorted : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, _, _ => []
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      match Nat.ble x.1 y.1 with
      | true => x :: mergeSorted fuel xs (y :: ys)
      | false => y :: mergeSorted fuel (x :: xs) ys

theorem mem_mergeSorted : ∀ (fuel : ℕ) (xs ys : List (ℕ × ℕ)) (p : ℕ × ℕ),
    p ∈ mergeSorted fuel xs ys → p ∈ xs ∨ p ∈ ys := by
  intro fuel
  induction fuel with
  | zero => intro xs ys p hp; simp [mergeSorted] at hp
  | succ fuel ih =>
    intro xs ys p hp
    cases xs with
    | nil => simp only [mergeSorted] at hp; exact Or.inr hp
    | cons x xs =>
      cases ys with
      | nil => simp only [mergeSorted] at hp; exact Or.inl hp
      | cons y ys =>
        simp only [mergeSorted] at hp
        cases hcmp : Nat.ble x.1 y.1 with
        | true =>
          rw [hcmp] at hp; dsimp only at hp
          rw [List.mem_cons] at hp
          rcases hp with rfl | htl
          · exact Or.inl List.mem_cons_self
          · rcases ih xs (y :: ys) p htl with h1 | h2
            · exact Or.inl (List.mem_cons_of_mem _ h1)
            · exact Or.inr h2
        | false =>
          rw [hcmp] at hp; dsimp only at hp
          rw [List.mem_cons] at hp
          rcases hp with rfl | htl
          · exact Or.inr List.mem_cons_self
          · rcases ih (x :: xs) ys p htl with h1 | h2
            · exact Or.inl h1
            · exact Or.inr (List.mem_cons_of_mem _ h2)
/-! ### Part 4: Verified Base Paths (`n ∈ [25, 53]`) -/

def basePathList : List (ℕ × List ℕ) := [
(25,[18,7,9,16,20,5,4,21,15,10,6,19,17,8,1,3,22,14,11,25,24,12,13,23,2]),
(26,[22,14,2,23,26,10,15,21,4,12,13,3,6,19,17,8,1,24,25,11,5,20,16,9,7,18]),
(27,[18,7,2,14,22,27,9,16,20,5,11,25,24,12,4,21,15,10,26,23,13,3,6,19,17,8,1]),
(28,[18,7,2,23,26,10,6,19,17,8,28,21,15,1,3,13,12,4,5,20,16,9,27,22,14,11,25,24]),
(29,[18,7,29,20,16,9,27,22,14,2,23,26,10,6,19,17,8,28,21,15,1,3,13,12,4,5,11,25,24]),
(30,[18,7,29,20,16,9,27,22,14,2,23,26,10,15,21,28,8,17,19,30,6,3,13,12,4,5,11,25,24,1]),
(31,[30,19,17,8,28,21,15,1,24,25,11,14,22,27,9,16,20,29,7,2,23,26,10,6,3,13,12,4,5,31,18]),
(32,[29,20,16,9,27,22,14,2,7,18,31,5,11,25,24,12,4,32,17,19,30,6,10,26,23,13,3,1,8,28,21,15]),
(33,[19,30,6,10,26,23,13,12,24,25,11,14,2,7,29,20,5,4,32,17,8,28,21,15,1,3,22,27,9,16,33,31,18]),
(34,[20,29,7,18,31,5,11,25,24,12,13,23,26,10,6,19,30,34,2,14,22,27,9,16,33,3,1,15,21,4,32,17,8,28]),
(35,[22,27,9,16,33,31,18,7,29,20,5,11,25,24,12,4,32,17,8,28,21,15,1,35,14,2,34,30,19,6,10,26,23,13,3]),
(36,[31,18,7,9,27,22,14,35,29,20,16,33,3,6,10,26,23,2,34,30,19,17,32,4,5,11,25,24,12,13,36,28,21,15,1,8]),
(37,[8,17,32,4,21,28,36,13,12,37,27,22,3,33,31,18,7,9,16,20,5,11,25,24,1,15,34,30,19,6,10,26,23,2,14,35,29]),
(38,[34,30,19,6,10,15,21,28,36,13,23,26,38,11,25,24,12,37,27,9,16,20,29,35,1,8,17,32,4,5,31,33,3,22,14,2,7,18]),
(39,[32,17,8,28,36,13,23,26,38,11,25,39,10,15,21,4,12,24,1,35,29,20,5,31,18,7,9,16,33,3,6,19,30,34,2,14,22,27,37]),
(40,[30,19,6,10,39,25,11,38,26,23,2,34,15,21,28,36,13,3,33,31,18,7,29,35,14,22,27,37,12,4,32,17,8,1,24,40,9,16,20,5]),
(41,[21,28,36,13,12,37,27,22,3,33,16,20,29,35,14,2,34,30,6,19,17,32,4,5,31,18,7,9,40,24,25,39,10,15,1,8,41,23,26,38,11]),
(42,[42,39,25,11,38,26,10,15,34,30,6,19,17,32,4,21,28,36,13,23,2,14,35,29,7,18,31,5,20,16,33,3,22,27,37,12,24,1,8,41,40,9]),
(43,[38,26,10,39,25,11,5,31,18,7,42,22,14,2,23,41,40,9,27,37,12,24,1,35,29,20,16,33,3,13,36,28,8,17,32,4,21,43,6,19,30,34,15]),
(44,[25,39,42,22,27,37,44,20,29,35,14,11,38,43,21,28,36,13,12,24,40,41,8,1,15,34,2,23,26,10,6,30,19,17,32,4,5,31,18,7,9,16,33,3]),
(45,[16,33,31,18,7,29,35,14,2,34,30,19,17,32,4,45,36,28,21,43,6,10,15,1,8,41,23,26,38,11,25,39,42,22,3,13,12,24,40,9,27,37,44,5,20]),
(46,[25,39,42,22,27,37,44,20,29,35,14,11,5,31,18,46,3,33,16,9,7,2,34,30,6,10,26,38,43,21,15,1,24,40,41,23,13,12,4,32,17,8,28,36,45,19]),
(47,[46,18,31,33,16,20,29,35,14,22,42,7,9,27,37,44,5,11,25,39,10,26,38,43,6,30,19,45,36,28,21,4,32,17,8,41,40,24,12,13,3,1,15,34,47,2,23]),
(48,[26,38,43,21,28,36,45,4,32,17,19,30,6,10,15,34,47,2,23,13,12,37,27,9,40,41,8,1,24,25,39,42,22,3,46,18,7,29,35,14,11,5,31,33,48,16,20,44]),
(49,[29,20,44,37,27,9,40,41,23,26,38,43,21,28,36,45,4,12,13,3,22,42,39,25,24,1,8,17,32,49,15,10,6,19,30,34,47,2,7,18,46,35,14,11,5,31,33,48,16]),
(50,[46,18,31,50,14,35,29,20,44,5,11,25,39,42,22,27,37,12,24,40,9,7,2,47,34,30,19,17,32,49,15,10,6,43,38,26,23,41,8,28,21,4,45,36,13,3,1,48,16,33]),
(51,[51,49,32,17,47,34,30,19,45,36,28,8,41,40,24,25,39,42,22,27,37,44,20,29,7,9,16,48,33,31,50,14,2,23,13,12,4,5,11,38,26,10,15,21,43,6,3,1,35,46,18]),
(52,[50,31,18,46,35,29,52,48,33,16,20,44,37,27,9,7,42,39,25,11,5,4,12,24,40,41,23,26,38,43,21,28,8,1,15,10,6,3,22,14,2,47,34,30,19,45,36,13,51,49,32,17]),
(53,[39,42,22,27,37,44,20,29,52,48,16,9,40,41,23,26,38,43,21,28,53,47,2,7,18,46,35,14,50,31,33,3,13,36,45,19,6,10,15,34,30,51,49,32,17,8,1,24,25,11,5,4,12])
]

set_option maxRecDepth 4000 in
private theorem basePathList_check :
    basePathList.all (fun p => checkHamPath p.1 p.2) = true := rfl

private theorem basePathList_keys :
    (basePathList.map Prod.fst == List.range' 25 29) = true := rfl

theorem base_paths_25_53 : ∀ n, 25 ≤ n → n ≤ 53 → HasHamPath n := by
  intro n h1 h2
  have hmem_range : n ∈ List.range' 25 29 := by
    rw [List.mem_range']; exact ⟨n - 25, by omega, by omega⟩
  have hkeys : basePathList.map Prod.fst = List.range' 25 29 := beq_iff_eq.mp basePathList_keys
  rw [← hkeys, List.mem_map] at hmem_range
  rcases hmem_range with ⟨p, hp, rfl⟩
  have hall := List.all_eq_true.mp basePathList_check p hp
  exact checkHamPath_sound hall

/-! ### Part 5: Verified Base Cycles (`266` cycles in `[54, 531]`, base-532 packed) -/

def unpackChunk : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, v => Nat.mod v 532 :: unpackChunk k (Nat.div v 532)

def unpack532 : List ℕ → ℕ → List ℕ
  | [], _ => []
  | v :: vs, rem =>
      match Nat.ble rem 24 with
      | true => unpackChunk rem v
      | false => unpackChunk 24 v ++ unpack532 vs (Nat.sub rem 24)

set_option maxRecDepth 2000 in
private def baseCyclePacked1 : List (ℕ × List ℕ) := [
(54,[0x292598fd72adefce9fb51f8d07f12fceee988fcc1ccf4af7d79a71,0x7570f60d0e90240b4b1ac8578c71cc5e49609e336ca31a8899c6a,0x74829d329a48b]),
(55,[0x74920a827cabea684eae397d39416b191178527fbb61e52acc341,0x4e045df1c3c6cc440894649692b159973bd1c9853903fe638dcb6,0x286ee1e7a786a00]),
(56,[0x292598fd74d168d4e3d079e2d1a2e1654ab37d9b4bd2a4d8accef1,0x3a69c8a3765d6d1b80d2fa798aa2d47589b6a05611fe0d44641fa,0x9d54c6a2369f182e1]),
(57,[0x15be33f2ccde335f68adb666d7163051aa93e1166456ebfffd6647,0x9a8acf6a64754599e695c4dac72481b591a02e31537ae79ecdad6,0x11c172dfcad5c27aeedc]),
(58,[0x2b8493667326681cecedb7ee42741a1b1354bba2e5bcca25591eae,0x2ded6e2f7dbaa4ccf649204629d38bdec923482e075522d8630189,0x1c71806bbd1246dd90771f]),
(59,[0x18350ae4f23c1c2e9d12db1c27262fc6b69708b0664eb339110593,0x4014b14b3848135c3f247bf1f38a42b86046a2ec16468bdd963c81,0x14e8b1338fb2e8f3da99b33b0]),
(60,[0x3c6c6536f697dea4d47c485974ce17f35ab1d20483bb5cfc0a6ebc,0x16f90b278aa6318a6ecc2885f17d4369f56498edf1f328f5ea85e6,0x1e9234cef51db1cabb57a68ceee]),
(61,[0x304d849318efebd223ad02cf08901060e933b8192aa2309988ae81,0x353cdd85e3bc4d0087f72096ecf3bd4dddd4ebb4231aa33542d555,0x2c5ecadfdb1f932ef4b2fd9606721]),
(62,[0x87d89dd66cf47fd60c0fe1b798b6912b9a3671869978185ce5842,0x44db62ff36b30e7d63ec215963f7f33b3627468c984e0dac5410d2,0x31606767e1312e201165047e2f2e893]),
(63,[0x2cb03c65891327e73c897bf202d71f69e644f2f34b23ae98f27227,0x319fa085e21d300d150573f9eae69f19f919c11fb4820c21bf184c,0x7b84236456e00d70275aeed5d0b5d91ef]),
(64,[0x15be33f80d4d426d8aa10fbd0e85fc7132cb47879728f3fbf81d36,0xc1ac8d3e4592fc38650fd260ab76907daa5443d2c01910d1da116,0x21c6cf3d2e37fe7876375c273ef83bfdc122]),
(65,[0x13dbe1b8144d59c46034f160c022993385f8bfbdaf391b5e3a72a,0x3c6c653d05f0062087a1020c4c429f3f11e77efc92409f6db224d3,0x3ec6bc6988e1431f4814de02ebf1c6488936ca]),
(66,[0x3a03863d2b203f88c08c7dff6212e856352098015a91aa63a555a6,0xfcec4ab6c1712e55dc60c5294fa2597bc1cfbfdd8f43ba0ec5a68,0x48f00e11cbf9bb422aab34fd984ed0abdac312f4]),
(67,[0x4c0c0d611aacb43203ede718ef8b8830d2b2b3e0e15161f2e484ea,0x27233574173fa9f5c38c42f71a9cc04acf3bf48f509a4df13c751,0x97ef17b06592af33a20f4e0d18196711487491bc7f]),
(68,[0x44f29dad1e7f9078b1d4976313a1dba02b6638eb8a0c0c5ca14a7f,0x3b430078b710aeef1bb426b7c151aa04e9b5452423f9a967039cc3,0xd77c64a59bb7bdf6bdecc4df5bcc115102854ede0ce3]),
(69,[0x488fe08631cae783673a2c19440075bbf3ac291bd5fae7aca14a7f,0x2cc2e12d4ce9e6386555571515f7eebc9f626900eaf6329bfea318,0x1c4030461c773ac24f3f7f4d693fdacf860b7ca6039d1f0]),
(70,[0x12418065a24af4df4d3db4cfb6eb287e6d61c533813ead34d13647,0x306b33215dee31fdf513fa5a05bcdaf24eea0ed6dd90fc0e0d986e,0x86bfe7166754bf64112eab9c42f71447b6c38ef83520915cc]),
(71,[0x135bc729410d42e33336797e6061519a4eb502ae3df9c7b3415f66,0x2e02486aa2d4dc5ef3c86cb4e4861f99ebe64daed6028e4b340471,0x294b5632b27649af5664c25b7c01da3640c0947c9ddba05df636]),
(72,[0xfceca8c0b5bad286ac6a078cca4283be86372f6ad15fb7358717f,0x231589128cd511863b4e68d7addf7ab6362d5ad13e4eaaf88d1207,0x4020e816b8c1035c1ec14c15380cebe2b0c660af7c1af3c5ee98df]),
(73,[0x1bc45c854dae346ab5af28885c790df4ec0db152aec17cefce6574,0x614b343a4d370836f10a4819306a888bac9063a6c1f77f2ab3446,0x19696bb4cd428286a7aaab250a4aba162188d2969427d1c1efa873,0x4]),
(74,[0x2439b7c73acece5608a87b72370b4794bb5ae347361579173d25f0,0x2b8e73ce2996899b908b888e0d7765756c05a6b7f711c0aadd72d2,0x3fffca857c66dc46904b85fb109e0dde9218b60e38a75be1b8d334,0x1b48]),
(75,[0x43be304289da1d5e667a65854fc2baae5fea9eff48f0465e8e2f2f,0x38bc84d6facb696ead11c50b54124ccd7819a3b72871f6732c6c40,0x4878a0449c7a85afed2e65301436efa6a2c32b974f007f95c9aac5,0x6c4859]),
(76,[0x549c2bcd41ebdd2856d2384a8d04e1c8df76b79cc13670cea75225,0x353ce8b0e27e54e54d8d10ddcd007054d5ad6f4a8640bc6ab121c6,0x474432da09957bad9642ba5c7878fe7f46c64c949c0c81018377e8,0xf38bbe99]),
(77,[0x4aec85a49e82d5e92224d6f1f635a48b5e5b1926e4a655c6d5ea05,0x15d4e259efecad88f2e4e3fe8d454e02e0ea02e630293a364619df,0x4289c2dfc2c069afeef163e2338af9bb1390ae01bd9aa34d4568cb,0x46129465012]),
(78,[0xd55ae43144fb65d22718787f2f81ab1beb0dc47c0e83784178c37,0x1f8d2c6e109a11c211e5ad5cd1afc9ebfbe13dbf052f1c7be6dc8e,0x44db62ff394ae28f9963fd81e4c2f07ce5a507e5f885040328edb2,0xc617b3cc4054]),
(79,[0x3ed53bd6c7eb06be14adbff8603a9e65fc72a24e7ed9561f32a4e6,0x474f466e870cd83c70d6d3767f896b8ca4f0ce8e9bd021b664c181,0x5bd6bc28606ed57497fb96f61f16cff7791f66b6b819f8594280c5,0x124300e6f206288c]),
(80,[0x56f8cb995ebbc73bf4f1fbf28b16ff4434013ed76d81db8da804d4,0x5f8159e2e133cffd1d15472fefb3a1969cbd9a6e6cb19d5fa8120d,0x3c83ac393d84ae00fdabfe4fe88eac8bbced9053f8ac00b0dbc8a2,0x326d50c1f77faebbe3]),
(81,[0x1852adb4660327a53c3c10be4d841ed4d51ebe92dc434358d8d95a,0x1f822ddb93b4ffdf4cc04bc2e0aa0bd66cbea146605b33097a7a34,0x3a03948466bbfd265ecd1f1a5ce154e20f35c3ab434b46f651b1f2,0x2eb5fbe1efd6b3b5185]),
(82,[0x427d9c052a5c3288004c348112ce2902217a6acca5b7a44c326ec2,0x15cc356babf7786752ea2ae4aee9110a520374d0c1080703b4caca,0x56f8cb934f941dc4fe6018e58a2b44b70abfaed313db657f3e6cef,0x82126a1ccf5318367ad80d]),
(83,[0x52334bb47465e7454c88670fe055a011004247f56b2106f72e5aae,0x883ee9c40daa07b0e6b4b203c0996af1145f46e248838f50a7cbc,0x4c20fc009c366fde50ce412f613c65ba817e66cd5a9f5742edadea,0x1c9eedf1646e4e9d4b012d471]),
(84,[0x17095ae49cd6c1e7703cf40ce96dd4cf194babc6ff1fb8c5ad7ae8,0x195b7c205d94aa36e7dc5bf0fcacfe2f5ac57a4ca25fdbd506d166,0x15cc301eba95eed5438556b81eb95d00694479eb88e17f15a35640,0xc3dc8bc9c4420064f1dee8bd2b]),
(85,[0x10f2e82ea4aa93fdc376c8fc4016cbe79da893efe6d0b4af7c3a5c,0x290b6d570918a544a30b406e5ffc47e13769a6c63cad83cee296b7,0x2ded737eb9279229c04d014f381f8de13bcc05c915038ace423193,0x665ed9a515dd8a78fc6234043b57]),
(86,[0x34087b54d882f701297332849ebedc9f642134667d10e5090938f2,0x3c27ec5e6610cd7f45596625c15f79e5f14fec4e41890fa5a66e6,0x2a65102ac61277f94211016f95df8d29e22b5ff0084e10ca04370e,0x170d46e4046edf4780713281d9f28bd]),
(87,[0x56f8c7f4a18ce84195b397b02cfb7e9c13a8461f31ea63917759a9,0x142f980012d67c5a21aa04958502cbed0ff64361ca055c95b9501,0x5961aa91abe4f926ec3f3a6bed6a9426ac0395ebfd5b923973daf7,0x9d575e0bef72f5ddd0a20a9302ddf0177])
]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem baseCyclePacked1_ok :
    baseCyclePacked1.all (fun p => checkBaseCycle p.1 (unpack532 p.2 p.1)) = true := rfl

set_option maxRecDepth 2000 in
private def baseCyclePacked2 : List (ℕ × List ℕ) := [
(88,[0x2cb8f7e2733778d9712dda0cd4bc11063dc1bc936ef8f78575778b,0x38bc8fc0e734f9f2e4780c1858adc0e385f62556abdf3c7e4f2ba0,0x15e9d9e7e6f819cc9cdfe59a931c1b4b44b5b80dd69a6f3482bc85,0x80ff98d0930abf57c4e4c98d93676492037]),
(89,[0x30601b1902f407486b9bd7497582584932383c460f28f285faf4f1,0x3fffce2834bce8df77170947857a10a08fc8ce160f710256cb681c,0x3da0dcb510ba1efa6cfb8ef34fde99bc4c04297e084f5061b76d38,0x746fb3690558e6feaa48aeb111c80d0e2418a1]),
(90,[0x66ae8f642182e4e034b80d9bd18be77179b061d8a3465f67abbca4,0x4d61a7b5b359feec4b48870d2db241362c445af513b5884f657484,0x62b5f6dcd4fa14aa46e4622a771a000d18f549bec1e422ddf9444,0x155d91700af5702507b28fbc2f9d3538dde4b9503]),
(91,[0x135bc2f9fac91672b63eee4ef204066a88b42d7ad355c64354b9ff,0xc2140e1a6cec25046cb22f4a913697ea0a5f59737299c839357ad,0xd4f363327d87fddcd74b103750529a6e8896b112a5f13fa3e9702,0x491ecdf45aacb1bb1ceffd4c80f1cce0a85e7e76c5]),
(92,[0x883ea714e0502ea4efde78f5e9ce549c72446c3e13c58d88b07bf,0x3b430baff840ab0e7923fcf6595108b6434a06e6df26bf89881e5e,0xc4667c733f71c6c66688a03f96a6b9761c2d13ed37ff74d987938,0x19ef5fe9a878636e5b42e477c534e3b1e63fe158bd972]),
(93,[0x195b8e5289c4a99c10f145dd6b0c909a11abf27d90efbdfc754a1f,0x2ccdf1613eb2b5bbb6c14ec835e634ba17c4649c06ce2400f0ede3,0x367d903c182eca04a2322416c3f917130b13abd45625a191cd69bc,0x7ab0a0ed85ec0c00756c427a960562579371da92ce4c93f]),
(94,[0x4c3a96e2de7f48b770f9c039025602e52b2b154c9b7bfa56e27ed0,0x122ee7f12ab71cdca34556405efab365d4d6b45f1487c0de94e3b1,0x2b7bcf043ee8451a348574df51ca26132c4a76aba9b265bc34f451,0xa590f21a72f3ce2aaf84dcaa7883a65888db0e4a35b988250]),
(95,[0x32d402b79990c70a3fc2d7aa76f7dc9d89a9841931be3934604744,0xae126335141f57b662c4dbfc20d11e6fabb7d2805621c0fa4f39b,0x5367caac516e09cfd57e46c3cbbb70d0762084860f5d3104c67608,0x1ee2514dca386a20dbe0628cc8f16a3899aeaa95304aa8f10783]),
(96,[0x2315a0da49f1743b5dd88ebf50da0fe33d61e0c6fb8f1d16904744,0x42972bbeb42d380a02e93684c7df35eb34781caeaf70043c445674,0x3527eee4c06e49ce51252d1ba16c4cb687cbbb62a03a1250e8ab0d,0xfc61853f1f2f249725f29c6f0e562433cdafa8c5144bcb278b63c]),
(97,[0x72bacc5887b22c47b0f681d8007348a333ca77f63512c5066f8ddc,0x3fffc4ebe47d05c8a61e0a1312b4d8faac94de8475e15500bc7021,0xeaf428d6b5b9b60fe81bd420bc1478d37b7a3c03a91bb79c9fe4f,0x1e58d7a19e6e88575f3b528e9575de51dd99a11fbf3929e098ce88,0x18]),
(98,[0x32bf141e681744d2424c9df9dda8edabc22b5622d9cc229ef61cea,0x2a2fca30b421afe6a0e05da0bf9b7a13b607b1822ac0ee4b60ff6,0x6b9c2a8064ec97702628cca8858ef2965a5446f155dacbe1a7553f,0x2de4a9c7e5f8baff8ff669765172271d27f43e64ec45222627b170,0xca3]),
(99,[0x4fb333ae1b8a805898bbc1bd0cd4b1e4753e5dca6f51a51a2232db,0x402e50f28e81741baf1b3ae9f79ca4f35379b325497274bf433d6b,0x15cc356bb00b77b60df9a604c9e63df0d17cef9d26c5e6484e4737,0x1e58d7a789ad2c30f9bd901fceb7c96005dee20ba674507176562e,0x8ee7b0]),
(100,[0x2cb906260f2fba4a6ec8e0e85a89884b504d3c12e49f6d327f1839,0x632d2cc0c1f9f3a4bd1fd432350e674a114c19646df96bff19602c,0x1ac7c3bf815774535241b7101100791aa6ffff182615aeb71b566a,0x6a59384fd1ca06ab3785eb5768a6288c43191a5ef0de293480481b,0x3f20ba1d]),
(101,[0x4d6f044448b140029485fdd8af13d889d284737f86a2cc53552215,0x5846c9837326425f91afdbf7f0ef134bc95b7c361ae01a9acd7cf5,0x6df68080be928c7363095dceb13f335f3cfb00584b78ca996bcef4,0x510c4c74f3a9213d409d7620caea332f881e6a9022288a35d695c6,0x416b3e7edee]),
(102,[0x754f3ce3d956378ecd8342655476a450d7e153e8be320749153c6c,0x6f2ae80307bc260f3ec19f76fc4af12d15146ad5c448237e39f45b,0x67e2f3ce589da4aa2e839030647ba7c9d2cd0b1c63c1fcd1717929,0x4d61a7befb8017a53c82cb75e6cecf59403bdfaea2dcea863e08eb,0x87c41eb9d44e8]),
(103,[0x354922daaa6c88afa5120e31fdede5104947fc66afa697151b3461,0x12274ee124986828c466f789f893ab31b7b9caec72bccf3fad0078,0x2de4b73833e9b3bc6b4046571cbaf0d6edc848f88509afd966a07a,0x66bbf019c6091de3573a65a7221eca71e1cf81398a336eeec63803,0xb032d7292bbfda4]),
(104,[0x78ce532a487d97e8486a2dba3cfa3f50748bc9e421dccf843260f9,0x7b5566d6fc3a71838416e94b123743805cd225adebea4ea7c30384,0x75177a681abe37802853d1de24cba2a5673e100173351df1cfa7c6,0x3a038a73fcb831780cee50bd1b8cbb84ebdfbd7970a1df0e86b68b,0x1999a094c54504e54d]),
(105,[0x741ad67bdc7dbc4de0c1226bc9bef8f279cd29a8a9bd7a199ad633,0x3dabe67c62dad3286fd395bcc3cdb06369ee3a3fe9589cab23c8f9,0x5989b54d975eb21b04be8cbf949054e34b4a9b616eab36908d359d,0x413434dab7c3508f2b077ef0fe6234c9cb69cf3118b5534e853807,0x482fbbc5fe4d800921e6]),
(106,[0x4c2d2e0d9fbdad930e899794ede47431ff20c55f9c44e69257bdd8,0x4d556967f8e495c73c3cd6955f3c44db1386a93e25766d88f0bb52,0x290b6d55001722f72664bdc60a47635efd7c7eb967b7d5f6d591b5,0x9bff5576c143829c75b168cdb8691f42be71f6b30f71ca3f6d45f,0x5a72650cbb6a62642f8878]),
(107,[0x3eec86ff7a192519469b7ec450309618f1e9cb7563cb579071cc2b,0x56f8dfbb4a7d5e99c40cabad10fc67b4c35f7729c456651cd85900,0x31b930397c7eebfae6de813489150e269ad1bd53e0c4cfbae8ad2d,0x489d4eb23389fea2ebf2a275893af06b90dea3a20ef28f09552883,0xdf73f8d38ddcb88796bf770d]),
(108,[0x511ad25eb01b93128a3f63c83ea346f456d4c35bcc872d88980312,0x64619a22b6abb3e1375407db90b1bb0fdafc9f800754653768b75e,0x6f115bab83e355d08faf77f2e7a6acf99d42769a2531a8a129102d,0x88b87f8d6adceb2d71211cdb7f412c3be9b73eb2710790a9cb43d,0x387f79b9653a4ea92349b2add85]),
(109,[0x14b56c804e1b1321c97fb21f907467d8274b0c36df32ed2bb45ece,0x4af8bb52796150dd8ce5b7c7401ad11941368dbe9e677418713c6c,0x33ead25841a11a319eb3fd0847dea59259d82d02506b8007619123,0x6df67549e3429b11789c469bd77f52a987f7b01b2e641c9b5b3745,0x293571812b5826beb65601e3c30a6]),
(110,[0x463460a1a74df814278ba921e130334ddd5b435759e08ab6320609,0x55c4725a6acb29fbbf870b5e39d9e897f1f8dd7e1731ebe8b2c54b,0x2e1bef9a21d93cd5ad0e9503f3f627cd0aa5cb898cd97663cd7275,0x30601b1a81a5ac997f5824286fe3cfad2319a9007fe39a9434b0d7,0xfa4a2cac275b1a12ecce3fad88956cd]),
(111,[0x4eb1f79878114c8414c214c17f8c44c0d8241b6859c41176c2ceac,0x67d6c37834ff3d2d176aa68dceb4d891d82b360258eb0cb280b733,0x8398c439206a88c2fc2fd8613f8450fdbf59ac7069a14eb8398127,0x718667efe4b334767e17d3fcc47b97f998f1db9550b06faa375a30,0x17f98ced55401d53901bdd3a4a0355cc1e]),
(112,[0x8751f823a9d7a88287d34a833ded39206d7cff1a743b6482440316,0x80176e3685711c8ea6c34b98a69924c32e743feca434378bef9944,0x813d46d05a6c6842b9090e2582cb76a1955b64cf322623199352c2,0x5f815fc13248450ed3e35785236f0c305e0128395da01ed6ed9e1a,0x9d067800eb7e3908731a7d90f2529a14d62]),
(113,[0x828ff7321f128f9a263f2683b81f245322bf3429f0decaec5988e4,0x2ded6e372a0eaa1fc1c4f437cc350b931a091b48f417cc8c014128,0x9c8b50a572751de1bd429e468f058d472b85c7797bfc54edad70f,0x15cc3021d57b4311a1d4af45bd3784ab8b41f0119960935f125e0d,0x1f7ee008cd0c2676af04b2e58223c9f93d32db]),
(114,[0x3d7788fbcd77f263039948f149c59eb4a4d2fb9cd5a2aa22cd6a7,0x2cda11ce6a55f9da63b3882b34939f410ad80dbbeb085f6655b27d,0x122edb5674ba4b706c575aa3a134c4a775d3fe70772eb5f509305c,0x7b45b236778bf61150705450c13908f1d75e2e3fa2dd0b7073aa41,0x45a668c94d06e6e96555ad1465090f2cd37df7b6]),
(115,[0x863e0f68b3aee562ea379600b4f7a06b30e798e064806c29033ae7,0x5a961cc0284bfc6b48a1d03bae1a89f7363f756cb3ebd38ce3f052,0x49d1aeafd409ece9554ef5f5f18d930946051ba1b1aad3cef5ae3a,0x7b371faa7667e8232a3f8687bb5900fa11c2c4a517fc8f4303012b,0x6830532cd14ad9f33b24f696271485c6fa0ad148b6]),
(116,[0x705f4b4e5fcd6cd784722d1fed72244ec7e75c5a03f6cafede04cc,0x740b21d56d173f1722de6193a453625a806df1a2d44332e958e6eb,0x570512e6c88fc60db6b94aa34f8ace4f7bca1ccb62c3eb5497ac78,0x2cda2cae32f77cd78c4353359d4289701cc747e4c36a7d40e5476d,0x4fd2448c5ef8740c9783e5a9bbdcbf9cbff74f8199a5f]),
(117,[0x10fa7fe00fd82be00807c3de759796a207d97da80768f69cab3eaa,0x2bb30d45b7e290208ace8c33a2f01cf30371ca9bd2fe984e5274f2,0x450e8c744ebbc85e705d0b4f9023162c8b3a2d51da9a4cd6c367c1,0x620866901871a99d29cc5831b9828fc5533f6c15aeadfd641d0b83,0x47e9da2cbdc25b18c0c9412a02783cb46b810895c1b7a7]),
(118,[0x49ad0da4b2b4492d55f4e169c7cd0e76f75bdeff26069315caccff,0x2bb31cef38f5a43f3117008f7633082c86c5ecca05eb2badc121a7,0x55ec796f0d7aa6e4e79ccd00748f039d32e365f9de40b2aa0d48e4,0x5cf3eaad319ee53740be9f62ea32997a5a9cc5496de569f3e1c83a,0xb806fc5e8482408705232d3e47bf6528f2938a113356a7f3c]),
(119,[0x2925a5559cb24f08de3108087b102cf586e010d9a20b76e5679770,0x183dc8519e046d185ff0e1357c5d7a43735c74601a955d7435ce2a,0x4eb1f79b90927ec91e5ee194580e4aa9e91edde95135a02e0b0260,0x5bd6ade1292aed393f29fe786d63f8c3a8a7b205d8215efcf9ae8c,0x282ff6f304524571b0527025fb2cc0307fb286e8eb03100c9cb1]),
(120,[0x3a28358ab43d0bb258220e07b7e10be1df7460e5753526e714aace,0x305639555b716f1c3ea7d08cf1a0fcfc1ea8b90ba5d5a5bdefe779,0x5cfeee92838eeb9ed9676a4d7b77861a297f0bd9011ea8a53bcaa9,0x9115e7f3f5c3d54e70761c391668a1c425506c9138ea1aea9a3d58,0x2856b70333d61dd9b42f7d48ffd424883723a1a6bc16a3f473e00]),
(121,[0x48abdcbf76d37eb6fab9c0d2d87fd02ac232c9bb1491c1ee417bf3,0x84f8cafe99a22e5c7a2507e8e53a2bd40d40baaed07b7888b58469,0x1bfc164f1daf198967ca810bfd5ca72805573e886c9bb8bc87a083,0x1e58ca3b00865232a3bbaa3fca27fbcc5ff7603c616ba1a450124d,0x1aa68ef490e432bcde7192ed3cebf2aa2f2b1d473d268caa9f9b1c,0xe])
]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem baseCyclePacked2_ok :
    baseCyclePacked2.all (fun p => checkBaseCycle p.1 (unpack532 p.2 p.1)) = true := rfl

set_option maxRecDepth 2000 in
private def baseCyclePacked3 : List (ℕ × List ℕ) := [
(122,[0x1bfc229f373e907bb046cefcfcfb47d774f8ca9b9933437c315e51,0x7d9ffa73830e0d9e62d5f7e46e17f85751bb9400ffa05a2b78bc3d,0x72e669116c7ae51c78dc470e6377dac6b217554af297a4d61392d0,0x27fc42d2b43a0572458494004159fd1fa1ecfbf686e6fb515cc8b2,0x88961a2fb4945432eb449c0075b2f7a42e31ec9e56d6d6ae445c70,0xaf00]),
(123,[0x9484154ab8d0d4981f2b97a18efc160300426d4c704618acd824cf,0x82645149ec4c448f0b8288e269d9bf01891f2fef9b60b7803f9fc2,0x657a274fa3c58558e6117b68b746d6b3df46004b512bff7e54dd9c,0x6f396662bb2daa8236ea8ad2ef48cc6d5a52f289745d537ce76e34,0x7ef2af01744daaa1e26cacdd7fb75d4546d758438597cd8a96b239,0x705d8f]),
(124,[0x1a8fe62aa88fef24cfc02b998603df11bb6f06d5d604c378d57742,0x860ef83bc39e079306bea54ecd2aec2ba6d1b44e807d7d6097c42f,0x6f1d9277293f01e5bdcb135eaf48c07a08066697c2f047ef010b25,0x5730950f60a3fb839f5c865d61ccfd0222a02b72aad2fd78862cd8,0x7b5566ce82799d832db9a954d83c792d32c76f0dccf5f4cb39c5bd,0x3f2096f3]),
(125,[0x816c52d71fc2f883548ab807aadfb9531d3a32ee6d12b446141861,0xfeff34df46c54cfbd99ba0d08a3fb46e79894e9bda6676c781496,0x2a7ea76c98c930331e085571648199b147c07849f955457559be87,0x46347b77e9233937762cc48a6218a282594233d6a8858ba898161a,0x26d3fb250ba51d4a52443fa00a7a8bd3a2a33bd41c2647546c5953,0xce081e8bf4]),
(126,[0x1f6f8b9e1fba3242b742f2c7d23f10d6449172bc51d9a80102cdc8,0x740b36d29bb055dffe4000571aacbacd886adab1e973d33f04ea86,0x3a36b3eeb93e7a8a3613ea661fe4e4def2e0f8c1dd39f65766cf98,0x19722a87814b7ff707ac677cd4addde156094eafb33775a2c75c94,0x9a8c4b7f0b0a1c58d3edd01127db409caa2bcc030a0a12c65de40,0x160d529521160]),
(127,[0x95d6cd816ec5f53fb2f9904e91db15e7172190dee3fef5e0a2458c,0x83b4aff61b3780a20fede5cb61d91a168ac06aefa55c106f2e4cf1,0x5e3f919acb18c72c333597a35fb6e1447dd891a1f232d45119fbfb,0xfb810fc326cbca4fb52b94e8da2c3070f66b89978fb05261e054f,0x10fa7fdcb4ad4a3f0c66e9ab15fbec84fb94425a99d6f46c261314,0x1060a747f08695e2]),
(128,[0x258864256375e1abd078728683f95f14a4a08504a885e2045924e6,0x94b337ac9eeb7858eabde5520bc2e7be4518a33896784bbb3c9091,0xe7e893eac7952cef8dba7c774efa4e4d70e63fb1ea170bf5af549,0xfe3b6f84c0db03278c824860fb5b524e71b165ceb6302e560e0ed,0xd871884e6891d7e93c52c6fd4fb00e285237d587323d3bcb6d797,0xe66bff6ecb8259c45]),
(129,[0x525eef1cb3c23196150e3a3a68d7fd489205108dcadea972a4b09e,0xe83a92c0dbe05a02c618ec4004bb742d04f6581ad9fa2e508e1f1,0x4777673a8513b1d83b849576531631a5cea0de4343fdb28d863f71,0x5c024a9e611c8b05ad2a2558c494facad8df77cb6be6ff0cc64026,0x50f2a4fe05dd9e301552109d9033d73556d29085eb72f91d6ffbfd,0x7fe989ecc831b926dfd2]),
(130,[0x1aa68ef9cbd60dab29bff0a922c33a3bf8911e6570ebc8536250d3,0x2b8e79b066d22f73990c4d2712f478453a45aec7a917f2ba018af2,0x1f6f8b955c62ccfcca8a0c30dc037c88c58200c056cbfb1819c2c0,0x62087d3ad509bcab206164068bb524e530879027f95ecc604525e3,0x58396ea437a5b33ad93c407af183ac5eef91a646d8d1c76d0541e7,0x822c6647a29eff4129ac40]),
(131,[0x632d3b4bc8415f246ec0fe85ee2213f0f614bac82610e3d15ceb18,0x7ef2a195b60b0316407e50ad9a9312475a2b70f2330c4e1968b2ae,0x390237f8725c90977595c1ccf67adf645fef55fd78b866f2519f64,0x7045bb9d72f12f80d7c6ec2ef565ff4c4659bd6941d3ad4a002562,0x94b33027729c28b916d63a833845c7c3a4acd7f1c56bf724878ef7,0x2ff59e62c3c39dcd0295c719]),
(132,[0x9bcd2bd9b2563c8205cc7aef1b9bc774746b927b499bfba7b1ae2b,0x83a621a4d100b1814047e602c5ad2c8f13cef985bdf4321eca07c4,0x937eca4e93c62fa1ac210b4353dace3b849b4300e559918c112360,0x9aa883176a4e7bc40d7df2ca63a9499187e8d7c6e52ff75a9f88e6,0x7b55768578be9cdd36962f6641e2f8044b21398d96edfd13703b99,0x3ddbd0a71f65364ead7cd2b5af3]),
(133,[0x5e5b85b9b318e65588a8f8d915391bb85ed47d9cc19d6a520df179,0x71c2e40d102ec949916a071b129b4925747dfb3569abfaa2e855a2,0x73ef39cb92cb2dbb1f6e5174be9bf9e080f1ad5af849fd375d31d2,0x27e73eaff333105a0488c13dbb25cd29150038bd3614667b5a17b8,0x2722871a8bb01ab2d611442b9c02c1bb5fca7b15460eae636e094,0x7099684211f6ac567ffc39967af0b]),
(134,[0x2e0e8b7d9e6b8f9e7ac9b9e59f4fe93cf3e6c48e8f04e882fd6225,0x88a6dcc4f137da6ee54cf09d232e42f280c67170c05b523dbf10fa,0x861d8ac2872af999c681b5c245f771ca8d1d410d87d1b3de20f927,0x21d0dcf9e5dd6d0e7997bc18f3e5930c435c8c842de45d40a97ee5,0x27deaaa3dedb767098d0d676c9bfed1300a654c8899329b569c098,0x1a2cc4db105620f1105cec8922224380]),
(135,[0x740b284958a6927bafbbaf48eaa0e1779ee1c59c5d572b28988cb8,0x49d1aeb5c2f6e0c2dff8a1d3fe5c85251e12405369cb129a52a018,0x3b9d260d7c4abd1c91b038d9ce5c97891d3d1e9a9695d00f51488,0x4ff61d009bdbf17da00a02e74a7a9e376dd59387808ffeb05889ad,0x6babe85f00da08d7c20077e9f6559e687affb1b209dabd9dfc917b,0x1807bfbe5522e985881f6e6f6cd4052634]),
(136,[0x87727cd29ea2a20379dcc6eab0e013ca6250cdd19dadc6bdfe954d,0x94a26012d38481a989aabec6c2c78eb9f179c4f9cfae6d398b32a4,0x112460b973886e5d97ce9b3e4433e6ea8d114b86a641698aff8701,0x983fa84a7cf8499cef3ab3cceb35598e9cec21a2d2f608f86364bf,0x21e12da1035d2793e83a73f8f65a5d7b3a0d5a378b0639ad9fbe0e,0x238cc96a92d344761510e68a6f1b9ed34f75]),
(137,[0x4b06297b4031ea6f4199f6066decdcdaf1c23731852b940a5481f6,0x1a9df74424a2d1577d26a667d53482aa9826c0932c1cfdf79047b2,0xb2b93552bc27d440a5952f309c66be337ddee8c29a7c4223f357b,0x66aea0f77bd6c681f362e766f8558e2662f17065b673ff4a047e7b,0x7dcf193d313261efac50792bafb671a0d6c531e849d8ea1c0ba314,0x4fbc4ace74e5af54136a15fca9267eb6acb370]),
(138,[0x937eca561c2e88964c2bf5fd52ee3c6457ef43c8fd3a4326d4220b,0x64714858a2a1aef09caed615610edf5f015d7514b102a99367d946,0x7dcf11aba439672014c0fa987ffa1c11c9bd5eca1ff7d7685d478e,0x4ea359109777085253798ca57dbdfce724517fb6317b1cffd57590,0x15cc356ec4fd77e7c6078f628a2c79ab639b922b824bfe291d434b,0x18836f73811651e6c6caec4b46a95773ff35d6b8b]),
(139,[0x18350aee40dd03f519ed19b399358d3d3e0f0ac9b384c8624c0acf,0x136c60eb87de5afba60bbe2ccd9d0653a14fdd2e99c92b3558041,0x53839838d55ee9b30fec7501777be5ae99e75c92ff69024a06f4b7,0x9b1f39d3160f1250925fb1a09fdf40ba60cf3cc203a58fedc85e3,0x64532a54a35e11258040e3fa2bd7c700d0ac70b7a80fd3d3cdecc0,0x3ed9f703c732e4085e4dd97849812b23bddd0b39071]),
(140,[0x67f07282315bff18d760e233faa166cc3dc574ba60715d19459fbc,0x71c2d350018b6e098d07c1f48a2c0c39345201e3a8e0158d47fe1a,0x9bffc90576b87687ebf80072546f02d1d9d72e0c0bf49ea2f09433,0x378814fb210ca2548c084506c9a223f017001fb7469bfdf5686df0,0x88b7cc358db5f4e96fe077bbfeab5cbc0c1dd426d4df61345a227,0x371bf22f1ca70b66e6066e8a9ddbedd1464735a90033e]),
(141,[0x9e56a2decbc9991f015fc382628f94f2e757d2cc05e27177312a3c,0x65a5c5650514307bc5cfa27cbe8586a1e0317a8c433246092c692d,0x6e258b226fc94a0d2cd853f9a74eacbcf136bf0d01f7e4ce94f279,0x9d115ddc8e82abac35ecfa61a0366bc6a71810e8a4c5391724ed35,0xc15b4e46a32cc4783b9c480f44d250e8ee268e94de8571f071e26,0x81aaf18cf0e07166f1cc3c3782a8388fb4f8ab408b0b813]),
(142,[0x477758b02fc26d0686077d28b46982fbba56840f402d5efcc1880c,0x801761e209b3f814712581226efe95a01445430b06d99086edea21,0x195b7c205cbe5635df4eba9c655f7350bcbc6a0c692f15ead82af6,0xa7e929012faf1b27cb24a641ed3fd1e92886ab6bdd06c09f93608c,0x464301fa0dc439a48a3da7b2934bc1fd7933ac84f1052ffcc9fe2a,0x4c499d8224bddc3e5ea29ec98b283f33b44f0e517c75f722]),
(143,[0x20e9c2cded67c30c0f10242a88a68751d3cb030eb7d1f3098a4e38,0x631ebcf01e1319ec9d7da2c473b295329efefc94bd2930747266a1,0x9bdce97480fe2d6e5e846b77a92e28a09c66593f2ffe6a4af974ce,0x537519cd2323c632726ef6b9040488d05f3a21a8458af9e0d67257,0x9d221aa426410ec6aef2eb57e2cee374ad461423d3e51a6a2fe224,0x10495b17fbea7b476bde0abd98bed762cd9addc3d26ba7d23b1a]),
(144,[0x54c7c9e5bfb1b59e7ebd529f4a09e4ab2441edc154388bb85b903f,0x1d195317ea1d1f309f08f801a249c2b0f9284689ac2c46bc549196,0x94a24ccb512833aeefd6a456b0eedfbe63660039486e3eb9035f59,0x2336c99d42e03269d33d78507cd101c4592cc69bca44b9afe0285e,0x5d36aa91ea4cf76dea8b258ca693229f49649f8651bda0521d77cf,0x83b4a4c77de76072521cf487df9ababbe68a824f949b68d8aa800c]),
(145,[0x6f4920e9c75543801b1e560b11318e852baafb8c16ac1586a33d91,0xa5a324828a1b3bed958173f598ac6ab807b21e0e70867125c2ae8d,0x4e6b66d32a430203bc661cb9c4f4b7ad1580c05d4489f8e7c236c,0x488fe5e015204bb1dc5ff83357d85c170b94778397bc9be8981040,0x367d89491d372bd79dd016cecd703a4d8ca4c99b15339d2ee518a8,0x8c23a7d17e383dab49f1d219d742a0cfcb8e489225f06725b5883b,0x50]),
(146,[0x89ed580a8c23675447f97204afc8a72dbad829e9eba6d4f62e2ce7,0x597b4a3b96da8a75379a44f26816debf3f9ae663e3a38cd570130e,0x32d41b5462a27d6ccefa02e058cda1565b15bfaf92e79dbd69df33,0xa1f3e370b2dac241c46ccdbdafe1a2f123e8a58802c961acd1967b,0x16f2a15752271b07386415de3f7b527895049f6c7563759c5823a2,0xa6c5a096e86812137d17c99b99d2098598269f1cafbeea5ae294e1,0x2587]),
(147,[0x32d422e793c291f50b22004d0bac5dccd7001e73517c39050db1c5,0x9e569b48832089222628e0fc4ce8d7e35955987f400840280cac93,0x8008d53c91b4ea60a02d4316ddb451f232a1482ad9a7e823ca09ad,0x815b7c5cbb92fa6d99e4f3c3b6419eea558e634833024aaeb8ce53,0x8e9c29dc60b3c63c5800aca6de0159b634a8f9f3e5b805a26bee05,0x937eca4e8d8d96d6aacab001e680a37b5ad1a1ccecc0534c31bc17,0x410e47]),
(148,[0x1103455775b2f88938bf0688641675e1e3fb2d9e44dfdbd6083fc4,0x633cdaf6abcb8ce4ab880f5fcfec0cac7abae3c5e2890238b54072,0x9996e62bc27cbe5b963e75fb0ec15a80014b39bbaafe89de7fe34f,0x54c7d2969bdd9e844f46746c3cf1b9f43047154a688728f65580d2,0x256e22a4b375a23300ff6c0904077ada719652e142da3a895029f7,0x8b21df6b025611f1d63e15c6fb0829992d54e987779002a23168ae,0x41b5d8386]),
(149,[0x6943164c0f205180a467336426729787c6c7538c45be7ba787e407,0xfc61853f82b8b0fe0e1fe7b01f48310b85a10e61aaec61857cac2,0x403cd6e8aed895e0f7e6562d3bd59f59b4d62e139e022877253744,0x614d0aa816af01c7fa091b1fca0c417fdaf10f8692034dbcdbe70,0x54c7c9e5be5327960b3a634e4434749c97bd606c80ca7b1765ac30,0x7ee2fa5b8ccf8b82ae2bf7977393f2e0e97429cd76f6c561e980fa,0x3f2483e145b]),
(150,[0x596ddc0abef1d840efc377389639c1492f3efeb9b4d7efb0cc0d3e,0x2a7eb82d0b684fb09c064ed6b26de10abab22976e5abd9cf8f8d92,0x94c529081d04174f967ef47631c886b5350c0cdd0edcb205cd98a1,0x2575be3c9ddfdf395fe50b4706ccbd712fce963089ee343dbfdeb5,0x693366597f7c4e7f448828a55a303806a7a1e921b138c38117e9aa,0x614ab6fa41a993fd9aa12934f46324ab2f2b6f612545dfc95aa72,0x150f7e12d6661c]),
(151,[0x5383b553d5f025fdb6d2f014de22a941d3ba384404ba0a06026562,0x3b5c881b475df107453e5e64eff3dd82caf387f13c8b0a6d211874,0x996461077bc7896762d231e203e529eadc06896e0adc619ac646f7,0x34220b0f72e1998e26b797035e4c05c0e06f611a77b30ddad74e8e,0xa3285870e0f1394410e1925245d851a2cc3e6dba9ee1a77697ca86,0x95c70dab486512ac5294ba043c8fb453c7f11d01213811b094aa6e,0x6faf6995f5dcdcc]),
(152,[0x2824531ef04243c9920e6be3ed12cf50570373be6d2de6ac06219e,0xa7d971ce69ada26d0fccb7f125f1a4f2a2792cbee37f965f405487,0xb681191682ecd5c5784d839b3be35e5f777b996b7ab552570e80f1,0x195b93a67d21dafd9cbc9cc747ab1fdea5a0a5354cbaaa72c00af6,0x4c2d2e05f2b3371ee59f6a79b7279aaf620a1c21ae4e0c46b604c3,0x91050a7bd0ef64b55e94aa802f6e841059c2f05a3c39a77bb56b86,0xf11e8cf0bd644a90d]),
(153,[0x934fab8d7dcfa9771d1d245c2627c50949f9fb0c62ec26a36d039d,0x277633ed6c6d00168a562c77dad5a2ef54a9cfa073e0cf3d34e7e,0x7ec70b9c4e7f6210f6132cad32adcf351cb7ef9ef91cfe0fe5056a,0x707da6a7299bacc8672a7edfaab660126fbd4d1e1b61da93022d9f,0x9e56a2decbc998668178a3e4375063630ec137cf17f0b7460ee5eb,0x38cf2729fd5dc9894d8debc8633567979c7d3b630965d505e0b20d,0x2a68e81000f2c8f8d5c1]),
(154,[0x2b8e79b06a2fde6b93a997f1113d4b1df6e84b0bc450ee3fadf028,0x88b904a5e07867af5f8573c624583db311dba5a42d0e66afc11201,0x73e303d10e8903585cf8b1b0d9146d8a67f5f8ca147034d427d500,0x2a2fcad2263d6187563ef7d4932a8b7aedf4c1f21b15f72621789,0x8c23b42b45162976637c530b62f49ff7c3e0ac0425e5ac804d2eea,0x31abdaad1d270ab8b0c69376cb97ed2108915ed51d75e8a4cc1170,0x302adcfb63e36b6e5e788]),
(155,[0xaba94783e9a452ecbf5dda8dbb8abd97a2c6e36a3f2849b8748fc4,0x8c23a7d6e3e29befcd0d34732d2a6c8103c46ba03ce879031b7f57,0x1bd26bb8bc2880b622e38c97610484915b00002f75fea9e089a74c,0x5d1885017484e5a1496d5e3f6aef381cc5e2d7bb59bf5b8aa802e5,0x877275d92ec10437cd23eb4dadbfc67030c931a4d3e37087a355ff,0x1274aac184ef0ed58f6380fb70a8af957aaacebcd8b369817da2e5,0xaaf38d5c8dd5a6008e42e9dd])
]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem baseCyclePacked3_ok :
    baseCyclePacked3.all (fun p => checkBaseCycle p.1 (unpack532 p.2 p.1)) = true := rfl

set_option maxRecDepth 2000 in
private def baseCyclePacked4 : List (ℕ × List ℕ) := [
(156,[0x7a43d20d5c4c34d9b8b0377c49567c7b7b76b806399b15745aa7c3,0x6e259be32aa46aa90232c3bd8daf1c1e7fd935afb6fc046c53ef63,0x3c628257f60eb0f8931aa1efe567785f640a0c05fc938955e31c06,0x525823d3d1cccfe179a87fef65801453655b55649225bb0dd420a,0x4e89d6d68facdcf79bbddfca49a225f7ee2b5712dee8e543c6bb10,0xa5a31720c195ed24d49f5ac3dc49ae70c2ca4585ac9ed34f11ec07,0x40e6d39bd7878b80140c82c89b0]),
(157,[0xae255c515560214706146c8e53deb659fa56bad3fd0c2b0def11f3,0x2575d6dce479a19908cad062e8511575b9c51de3b92895795c975d,0x9d342e55f730edaf87f011bfa80a1dbe2bf16f96fe1ee38a688b01,0x13636dec8fb93f05f764cb46d0c369efb90e76dc0582d554e22387,0xbb65feda22eba41ad87b0dc8e1a0d809bba920f18591b0ed664224,0x1489c49a60faf17177634cfa0bce067c945b94c636289b1404ed21,0x7fa918557d6aabe8870e7c9cc394]),
(158,[0xa7fa0e07219c45e37e4c22065666a207fae9e21118bb2871893266,0xa0d17ea9b7998483f590ba2c7b9f29e1513344b139e4b75db29439,0x8d582181cabb472b278da7170e9cdaee97a17b955369badccbd008,0x13dbb13fefa3490ea565800fb64938c36f376670876e4b3475f98,0x43be2af41ec8bd2644fbf3128dd75f5d628d194f07159300273a6b,0x9d34366d126f601a00df675f255bb194e47e430a6ae20426128230,0x13ef0ea3eea669a005419d7dd18d57a]),
(159,[0x7193d616044732404122a1b7b58aa11e816f3328e5f0305eea5eae,0x5bd6d7071a3596d1ab2faaf6a17d9d177341d17b85e65d24dd26b3,0x3b7ae2888e7e43a996eab1e71c148e5627929ebb0f3885fef693fd,0x4fd7cbcd81d8093237c24553e6a45370950becea9e88dc42774a17,0xbb40cf5764dfbbbb48f923839bde0357cf20764ab8376cfccc186f,0xa46ec6cb8eb1981a6c2c60d354370d0a0b406cbcf64d7f40d3cfd5,0x231a981819153f3a726b23262938bbb20c]),
(160,[0x7dcf193d3132617997e523819897d0ce175114ddb5f6365c537201,0xc001a99f1341a242744e51d733fd438850202c0af59f540840b2fc,0x37a5c9e71c9bfa94a21763e49e44bae68b9b59dd4b08d6238223de,0x27e7424649b6b6eeecc1edc7eeacfb7336b9cf5c1166283de251e7,0x5383bdfe3d6729cf0deab2d3b96f386ca96083248623ec5c832d0b,0x2912f437f83d6793baeda67b8a0be9a7e5f25c3f91742a2b00f313,0x50e45a8c3a48e401fd8d4090225303b6efce]),
(161,[0x7ef2beaaf701db0b7f2e82c3c8eb9232ea79b071ec522de5d153d9,0x741aeed4c0bb3111222c61c0d9df6a6bd6d7f3a6c5b4b834ca1d4b,0x972e137d7d275aaab0bd226c0f21f6449058698764f9e785ac8274,0x596df4ad2e829ecdc4119f60e55fb5b1a0859d1d02472e0f72d54f,0xbb52d59b92481166cccd0462baf9c0b1221558dc7a72729bdb5de7,0x6a4bcaf5bff0c55db2c8bd8291a4ce2d406ff78914745b2a02ebce,0x6ec86fcbd88736b2cf47fbe48fa7d721fc8738]),
(162,[0x402e50fca7c568d47c0068dd4bdab71b2571fa2b9d930b79ee64e1,0xb2c10189dd4b6278af9308159ebcd843d3fc2167918ef730a8f3c8,0x3430a1c8b3ddd9a0a8ffd8902ae7207a8f35142a25f72a883279b9,0xb08e17c831b42402ffae0038ae463b0d3cffa4e9795edccc716ff5,0xb53aa676ddc05a0a82c0d3c773ba35d7136d1e7fad291211a7948a,0x73095394849d61503ae12001d8f0356d856c1755b9d1cc9878210a,0xf21ec06988d1b6e89eec7f7553d9d4c8cea91002]),
(163,[0x8037f4064104d8e4ce9d570d354e6130c3ec643238fb49d795f2b0,0x9bffdaf25cf913711aa43529e04944b1d4535d57fe59c58e9cccc2,0x307774d0de7dc1432073f06ae5267e9c9820352538a7bca01f2060,0xc2a080bf5fec2568e93739f00cb92ae58c4825f8e3853724c45649,0x7f0378198619f2db4e7e518a308b56d19f7b2eef0880faa92709b7,0x63115fd9f0479643cc4cf92bf002383e0df298e66f5a2e06de332f,0x21ea15f39cd4a735f22f88191f86a29ebf546d6865e]),
(164,[0x2575d6dce478c9d6503db95d5cff50b2ce93132471be7e6649830a,0x1abb887d76cf2d47a7341db580ad81dd57c5e7f0f5fe5d2553033d,0x9f9d0193a00e835676257549115d3fe62f594d649ee4c3b5b9eb8b,0x8d4991912e7e9439fb9af2ba840241a9ca0817d4d4e7d9e4a08a39,0x4ed27fad9d7e4d51bb8343e97a7fa437d9ad26ded4a87a434b162f,0x1220ebc6b7de96e0c35d8942b2472f07e781129438c7688564b4c7,0x86eda116f4d5de872a4146030ac7edeb1c703eb9ee7f2]),
(165,[0xbb660faa988fdb6f91c65062ec6b1059717a7eb8dfa471b89adbbc,0x75fda334cef946a2335ca774ac269cf38bf966e1d9ecc0cdd1861,0xe91aaef7122eaa27e0bbd6875eb81bb20f879f8db8dfee5d38f26,0x9e7bbd6b61e4f7523a3ec3a4b19ea66722f4ddf3f7c59234142a14,0x32ed9da3f285f7f50ec17af3b8fb626495fa8dd13a64c9613d0fbd,0xc3afc1daec308f3d25332bb369343e46cd36636cca9a53a7fe7e76,0x9d7b377af3590ec284b270c59130bbb3277777e7a355cc7]),
(166,[0x75603576f78e78d635b2ea4edd289fa241396b521961b8e35e64c4,0x804a06ea6a0d1b0e6740570dd157812ef0dd78fe8e044e55168a77,0x2cb03ee9c5e5a438847d735c75d151cc6f2f57f855813196c7c63f,0xa1f3e3760eeacc8ea32147d1f032a831737b163b0dd3f225fca033,0x3a2835843dcbbc091ad8b70318fa1c2cd3d24df31b12cd6c2e95ea,0x7694a2db7cd71838e5af8b1382da4cf785b2a7727a8657c05d33c5,0x81fbf677f852dc0fee4fbed22346ac7ef0f2eeb37942c812f]),
(167,[0xc3d504b9632a2e753a0732ab8523ec331901fe0c4d5472d7a7c4b5,0x83e74f17f80ae99d02951b4a3cd0f00fc6161a3299ac2e0560eca3,0x26aa26dfe6f9f99d9af491ec1c136ed58f7fea2e5611a72fa4f08f,0x1bc456eca8b95e98e3ea2b142fb202666a8e83a039c66c91bc737d,0x862d31eed0279c3658d09a6c52da474bc697d59f8f0e18c5bec4b2,0x6a3fc377d87dad039d7062aad05bcfbe1d240a734eb3970a4623ed,0x413625381d40e271e495a1cf5fa4153e28360af74bf438721770]),
(168,[0x2e2a7ec59f36e437cb58911066d0b1c1a056fd9c4695028ea934ea,0xaf469f57e4f0079abe0a941d451f7b0f6dc59251c06120939eec8b,0x4878a0402bdbb0e89a72ba6d7bbf5630142947950eb6da797c9464,0x23624d6f435689e3865532ddc9bbdad956bc90e5dce8e146bfc498,0x7492563fa2e39ae064f362a3206018b582466974c76aae81366e8,0xc001c24c29a065bb24f3a8ad8090d3ce9383021ff6a3be4aa11b2a,0x1bd2467dd58368800db44af3d611e6ec8547a8c8c7e1f6ebeb3815]),
(169,[0x2e1c00621fccf96ac61de5a5b82434af9ec7112c57708f43f8886f,0x574186a5fa9286e4af8d4c2398ff996fcc9f82c10217006e0a8b3f,0xab974ea4560efe6ddd2cf60647af78fc3fc117f1892351ca546d4d,0xc146f8b224945ace688bfda7d1cf5110dc3716cf0ba0f2550cad7a,0xc7868f5810b98cb5efc0656547e73136ddba7076d3a57524e8d7d1,0xb11fa6cc1c9949924b76966845d947816f621fae9fb2273b1faf3,0x8afeedefd09296cb56d637fce431150da5a4b3ce336239c6a35d9c,0x1d]),
(170,[0xc8a6c304edd46adca1d91b5915c9a19a14de46daf35337b3b00cb6,0x9d3448600e0ff7aabb6eeec6615895167b1c4d570889c34846f616,0xb070d29fa03b048f5709bee266af97c0d143e8d61ecadffbddb23,0x37dd912a1988f5391828d9b7e0e92152596fe13de92400ed653ae8,0x89ac61f06e118e48055350240121c29e3becba589ce7855ba6cf2f,0x7a31e1c959138949026610fe90b4c4d49d4eb561a93a1e4cc0432e,0xb681200c9ce0f598cef8beba7ad5ea11f3b08dca4f2e836c9e3487,0x7912]),
(171,[0x511ae32c99a09b6dbe75d669a1b67d94b1fa063b3e635e8760cb31,0x21d871442336b023a91be2311c519507fec43918d9de655bfcf7dd,0x5006ed160f2a5e9df3771d31db90dcb30f03496a170b093502401c,0x9fb03b9b1c1f879853539af83dbbcb1e2c0e6136c189a83393f9be,0x812fe3d87e2215cadc246033d2ee3bf156b9d0a4346548c4dc2a6c,0xd55a8f6248cb98c5cba840f57016ccc23b28212e28b0c21d89a55,0xb792bd868dc4f90063baecf82a8fa4b3a6db33f437bd1467ae2b42,0x1d32029]),
(172,[0x633ceaab131a225e2169a9a76eb72af0b508c8d322640f798148df,0xbc874a8eddc811541fa2bb110eadbd7187f802c4b8b72c4e3945fb,0x816c7237f97ceb3b9f432fbee1b02fea7f42be50353a3a44062d91,0xb53aac577dcfad4281581ba965a71fe347d945068af109fda54045,0x246b36faca31d70c4cc3d0315298dab6dd9a061bdd53e3b1645e9f,0x48abdcbf71a585a4ee61c5e1df812a1e4784d8280d87a88ec494ee,0x21d0e3b2cbb27232b355773b273d528949a58357e1731509538ddc,0x4ce0f53a5]),
(173,[0x5d18a215152f8a64ae4fbf398965e2d1de6afc79977636c6070d9c,0x5367e1521468367100751ad473034dd9665a976dcf370f5ab4066c,0x49d1bc28e7dc35e41535112c3364c06708b4d3d482fd71050fd1c7,0x523364563682e68bee7150f178b189bde66859bb38906e94e7b1af,0x73093202ad16e0ccc529d7cbe7fe631c66f5fe58ebe6b251852329,0x9fb02ad79172d12929685548ae0e9b099ed06dda58712d4bd1ff82,0x75fc6ebcc7fa0e8736e41f0020c654f02c9819491546d9d5e5b24,0xe3a188a8cf]),
(174,[0x6a9a55d0fcd894d680e488cde5a6f80eb2a70b6e1753ad4d9c08d1,0x1e3394cc55ff1402d8cfb24893fe5df0969d1ddf50728e7f6c58cd,0x740b1bf108a2bff01e562c148ed087a5429a3ce2b5899ef8e6d6ff,0x7ed4896fca929017d9c8789dc7beefd2300d7e5f325d764c69190d,0x2cb03c78ea49bc40027ff0c1484af818d747c9b749bda6956014bf,0x5e6b1800811407c5683267d88cf2b6baf15c0eaf734133782bf7f7,0x560d230daeae93b72d9d5057765ccdd0b8033a7df7323137ef7022,0x17a58222ff7baa]),
(175,[0xc0127eff938338ce24126280ad47bbd13e6523096ec61e809a7d4c,0x7c89d4386763180e0d0cf9c3b58222df77ce254379e4320aa2942d,0x9127f08ef519d1b4fa188c572da120dcbd8a7739039e2cb2268922,0x9a98ba4760d0927949e526478b84216f8c59a2056fafbfd547a4d5,0x2344311b8f8425b8ee2e70c989b022e3454480fe6da701809acdad,0xa31779e1c576ba22c016318797f13c062b489e7e6cd736f3843394,0x9bffdaf260143de00519266f4d3608a399e30667b99be0243f65b2,0x1bc94a0627886030]),
(176,[0x439d12bdd702ae7f6f16a0fabf7f7d2d743f10b0138f1cff4470d4,0x5f816d3615ef8307443a593011812c03733a09ed5cb8d433e2c1b9,0x77c8f6433d3416d10f4d42a9a5906d18eb20ca6c2cf179fb7800d1,0xc2b4ea8ee8970f2bc5f53d71cd6ca1a810af16de5e5825198d4251,0x25bb81127cafa915e571a4435f211d6ce377ad0cf299e80a8f9fa0,0xd35961a009e2bf83d98272afd9f0ef76d0b4ea842f0027c77112ae,0x1f6808ec948d925e3befb307223d9898962027ba6f8fc0b956f7c1,0x37b63f3901a31fe87b]),
(177,[0xba45ecd2ec2f66e077391074d4303778b749a9ca57711f5c73385b,0x8c562b41a109194bd74aa9fc27c865d38dff35131c3b2a5b88994f,0x15cc3b557252089ab300ae8a11d35b9269724ab57778fcc7b72499,0x53839e9f204d9cff7c91e24fe4d74533d13acfacb8620c4cd92f96,0x66bbea39b1854cecf5f56a69d6945986342099d96b63a46a1da653,0x26d411cad6d364395601cab160eb518b6fdf6acd8ab774dc0c13a4,0x4268a23cef2244ee34d5c1255d21f852dca0c0edafdb01ed6b58ad,0x83ac3e0e346ac2ccd39]),
(178,[0xb43fc12c44bfd38a2ffd4536dafd8b0dc2750efbdf769fb4e893eb,0x4d8d4b68b9b9a510ce33a90a35d77ace8d65fd75721d15d1f58503,0x812fe65e7aafdb3aa6a8cb4138593ad7457a0f76f7a3c4afa397d5,0xa6a51ac72c65894222fea612ed589eafee31be9a713deaae3e678a,0xc1ad204e9aa49e9af6534695cc91d7cacd8090f3f989ef821fc0b,0x95e7b5e9863de7cd508696023baad91eb10ef29d61c13344226f4e,0xcff5a71cf9f2b9da23fe72c0c9b4411c7849dfe33a9c19890d4148,0xe57a72f2ecd9c31aaabf31]),
(179,[0xbf0357d443ccbb4104ccadc9c40e78ba3d94d9df5d9d8633d49442,0xbdceea6fc223c780c39fc721c8d39fd0f37f67a8a4a6236f78fb57,0x21d86971362f2799a08a5d95566cc7d30eac669696d977a82ca2df,0x2cda3d73ea3a96b956e59055cf4325080b887bb5a5131a5f1c4d8c,0x4b351f33b3d40aca40266918e756ada24c6c86d1ae7bf3e5572780,0x486ec84a002668abdaa4381f4217a644c9c54b20fd7cd7ec48d632,0x1bdb0549b1aee6730ebfe68ee4b0ea18c9825e67430d4b964e5809,0x29e4540c24192ff1bcf9020d]),
(180,[0x8c69785b5718f84d1a12ba85f12cccb1a7a1e43a2777a868d84470,0x9ade7d59c72ee382a6f9798f434f0c9d4161b3e6b82aff1ef75fdc,0x84da93bfc4d6f523f0f17df167f53493ff00cfb1984ed0063efae8,0x4642eb54459ad5fe8569010dbc49617b5e133e5b2a49c06109ac72,0x4ec190450e44f439bb543737af3952323dfd5dc4278c54d3621a4b,0x6cf12e8b2374656e39844001c0904cd2006479a3274490619a0a57,0xa0bf7d9cec97064687e222d82b91dda7626da651e17a04829e5182,0x27badf202886d2394ef74ac4697]),
(181,[0x5e5b85c56bddce71df50ff9be9c938a494275e1ed95712f324a93d,0x7a114b3feddcad02b0c96e44c1572a07501f8ebedaf83ce985f2ba,0xc28d5efd429ac0d9e0047b298dc0c7aa558d78cced40150a8a4003,0x88865a5f7f1350e50d141a1b292163615f15bd43599edd0dffd500,0x813d46d21509d2c078a045a0844f3193349c18c1e0af8edd507c63,0x221e280e63a19d40c082353fe52606afde98faba4379fba526fc69,0x53934ce1d0c7f5bde64883dcad4b63d973c636712931547f13c4a4,0x8be008c230dca3c68200307814d70]),
(182,[0x78fd746bd6a06c3225298bad75d0e34bb94629579a01bb8671e093,0xb9117f6769d7187442bcf7146d04bd553eec238e5e6c1a93b99dc0,0x8663555c1e71e56f0093287fcfcf49c7c00003aa314759954180f8,0xd236f41b8df99c9b433eb867c61cd6a7c5b8f33e8b3fad9119cb8e,0x7a43c9f2ddce0a371c578620236e72b045860feac861653f4a872b,0xc25ac919dfb399e5f251bed97f916929dd31f6d4f74f878f041067,0x368af577e71717d64e217163b668811a309ac25bbc2ebf98f32584,0x452492b8f2b8df32877d2ea013b5eec]),
(183,[0xb8fd1c848250ecefb244e81545f7004b7d17e9c37a67f931f54801,0x5c026c229a65adabea12e3cb11f92822dba696c3096e363fe4514f,0x54d8a2a82234024c82d4edae070490a44991dbdf59b4cdb56307d1,0x55d0bc27a6764104d71407df473bdc151781ed811d364fd1dcd2ab,0x26e1987eed0e74348b09960f56e581dbc0fdbfa87d272c0526a4d,0x486ec5338f47a1afe5c842ace7e619cc5cfb75446572e41018bada,0x851bc63bf0780915a316732f54da7c8b35c7ddd9821642fb8f2791,0x1cb94eaac388148c4cd13917ce4d7a7907]),
(184,[0xa34d96cccba0a5c5f3cbd19767e44f60f8307fb60ef2ebf246344d,0x50fee3a6267e6b21c213b73c915430bbc02f3c2b079104465a07aa,0xce99b37e616a0f709ae7486ce5c610dd09c4a5606fbe49addb0d91,0x44db5ecff483ba2b352104fcf4ff196cab8c164c669cfe503c6505,0x883f8b0fdeac9ef8e27692f653bcd3e2273de9d92c4f46e362650,0x14904af294bd5c5cb8e84c4da67b21c1fb3579019a0ba925cc8ada,0x20e9c2c6f25a3ad84dbc70f08035be6df8cc220877667b7d16e8a8,0x82b8a60af2063c6da70c1d2849c49383ad09]),
(185,[0xd12a1481831f3306c85717dfe0e0e43ae1f834ae2e7d0a9a311ced,0x936debbb50ec786008c676d92e625fe29d419f2d3d2b029fa4de8b,0xb30b4ba529c4d5537cc880a59d2a1159998d7ef2629cbd6ff50d1b,0xa59124b0a497fb64e61c995cde1a8bdafd32409eee333e51f40df9,0x802734b1cc3df73d3be228ef6473a2d6e5aa30775418b01ad12ad8,0x60f73ba8505ca8595eb7244dcc4ed46fc43948f8ac6527cf4cc63,0x5f74274760cf9888694450ba80b2e9dd9bfa842a08b9a4d29afce3,0x4848d3f047d79ef55e3446172609edace87d0d]),
(186,[0xcec127d62ab778d2413caa11c06513aa3eb195603ae344d0c833b1,0x42c639c457430497ce4e2b19053f2d290b60d94248094b77dae151,0x4652c4dcf9618337b7da901d4fb990de07f6d02a6c7d2be5ca157d,0x1aa68ef48f88eb924d2f2e39ac5b3586443079a8888abe5de0dd7f,0x8fe19c1e927048ad762106fe9382ee6f30e83c067db1377f4822ca,0x9bedc80e3aafad1eb40bfe5f44fa145f4241ebdcf99fd43e5e5469,0x43be3c9e758bd9928eefa6dd547ecba906e60b35ae7f7b4e7a5313,0x77954f88297cfe3fe75ea17d31164e42e25b12b0]),
(187,[0x95e7b5e98c44bc794d615b5c7f6242fe585e765395eb586667baaa,0x7f159985e120b192efb3cb89bde7a5856f69f78def253bcb0fb3b1,0x93a3f5b18d20f4da0e748ad52a9b3c99ed887d63334bf9acc4bfa0,0x2815dd78d2ffd40aa294f7beacdcc265a112a772d27e06d4ef1a86,0x53a4354399046b2f0347bd1ce2c5a509a4a589562233ed191811b0,0x500e205a397daf502951268174b32a5a6734f0fa92862e9026458,0x111816e33bd820684374a2cd0bc19765a73fbbd227d340a75ce4b5,0x36de530ce3db81c3d621a8b7030af94151cd185f90b]),
(188,[0x9984fe09c877880ae7e13e5524c8205fdbe24de646d5686fa49a64,0x78fd63a4ac11119b28da52bef92a33b6ecf58462a8fe75506059ee,0xfbea3ef8be23122f3988f561821e0060ace796aa873dd17509a70,0xa967f1539c83e8cbb1efa531bb5d600180bf6a7380b310796bc178,0x5be42c90ce3ca5330cf6fa1235f9f8a7d5c09af66d587f52022c9c,0x7a2111bed97579929e699addd423e53479d2ebd4fd73fbffc2fae8,0xebb8e9a47cbc7639dd2eafbed084cdf379d9a4f436221d6b2ed20,0x70109f4a53ee3beddadb68767e743046cfb5464a0aca8]),
(189,[0x937ee45a42e47ab1104934abf8859bfd1abecbc3bb99b7bf632eea,0x66da3b87c02db03bd1b07d0b728db5b2e19ab202ce520ababc0db2,0x94b3488506f71f65ca4f64024d9d0fe5d0580629cd04468eeb271f,0x7780489e14df1f464e497c878168717cca2bc76f7ac5d1c6424735,0x5bf2bbb544c123dfe4169b1c989b29b56422b625c8ce81d193ef6d,0x71a25c098f5d973e645e686742d4f37284d685389b0f2c23217181,0x9d342e4d7d401ccb215d5a6aa23c0ab366ebc631342bf744eacb47,0x31a930ba4bcda9579c60237fc303a9a7a93d1ba0898a0ff])
]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem baseCyclePacked4_ok :
    baseCyclePacked4.all (fun p => checkBaseCycle p.1 (unpack532 p.2 p.1)) = true := rfl

set_option maxRecDepth 2000 in
private def baseCyclePacked5 : List (ℕ × List ℕ) := [
(190,[0xa6ff33e6b25db01f9fe46ab724996c02b5be2cb2213017d36ed130,0x3ee0614895e2a042355337eb0389c7ff2f1e0af82b8d3842631732,0x680ea035127d67519de2504443991afc7410ca3978381842c70e65,0x7c7a19b472110866010c2325af0e6dddb211bdd134650a8eb80097,0xa5cac670f1b7db48b1f7e5607bc045c173cd8ca74a8e31a20e9639,0x2f430f8a7bdbb676a1b85d736f2ee4fd4d446adc1df646270ecbe4,0xc1ace6fec0a1a14f0ee84b8d14301c6cb7f0a4a03a257da4fa8c9,0x146afb13d3f84e70ae976f287ab4352a82d6787fcb4a35b9c6]),
(191,[0x8784974eb38485c4b0bfe2767d4bd4c444a0476c36a9dbd401c102,0x27d70ae1ec9696cd0911045ec9dacb2ea6afbcb18f97e6a50cda44,0x2912f9cc56e80841b2633d37a762caf88b47d5bc41ceedbf711cb7,0x5019034781da140f6103bacb7d17dccd160e305e2d5167712512ae,0x4500068ec08e2007e38291de8a48b2744c91ad692aab2432816d3a,0x3a4675240a724127b6431b2efc5c92fe59fee361c9e85f6e189d04,0xbcaeb6cd1c913acc466d335c2e5d2bd8ff3040ad6bff895ece7b35,0x415e9ccb9621f5131fc9c49c9dc050cf4f6a56b39f830f6de98]),
(192,[0x3fffdc75ec3c7bdcc8cb5e966530854b01ce374e4a6edffdd7bab1,0x2df7547974c61a0af8961484baf5696b6cd913afca8456bdd596e4,0x4f6ec20bfca20687a81af70389e7e0cce62dab58d4cd610a1e67a,0x1e90b53617f6027b1b0d25e7a411c5e9d9e9f02733124134aab161,0xabd0e96b731f74aa1307e2a14794b40089eb7f656876916f78ecb8,0xd999005b7a4b73a9ca5a2725b4a272a6c3fe03919f1a374d4bc10a,0x9c1306761bde5d6d79a44ff0deeacc809b1ef98e307ea0b8e52679,0x25bb9414926c617c2507ecb224aac9a40a378db784986e89d14c94]),
(193,[0xe6ef2fbff7a572c2b383816cd37515b50ec72c2e00a93eb7b536f6,0x514d70b4a60ca7689f22456086652f58ec5634cbec7f06b179bb01,0x5367be68c11b68230d0cee5006421b285c722fcb56efbda2e14991,0x403ce7a5c342457c4e60607406c662861708eb587428d2d01890df,0x49b8416ac9cb05a442387262c2cd174bff129a0405a9adb1e6e7b0,0xe33c5beb24b5403cd11285fea739dcb063f3685d7038d29ca7f00c,0x30602f36a2f89cbb60d87ed76c64d3a23a3dc77dbadb81a631a1f5,0x3da0e28aeecd6bf3c80630d967fad334fcca6ad286ec6b55753cdc,0x46]),
(194,[0x5240b9d65fef67e4a4c64d54da493b9c671400a4a875274ca91c87,0x2f5eec36a09733aed643764ac282161a4e1106ab82a5fdfb84aae5,0x2a7eb830aceb698dbc5d92436188f3f9ff83e516e5d2be5d9cbd4d,0xd82b00c9aafae5ea98647a0042f9edeb8ba77c232cc187d6c0bca1,0xab9741442b097394a329f711522c3354f057509d4cd5f38f605546,0x55ec98c74bdd20e6f4856088f013877ee73f17bed75a371be78f82,0xd71bd2e77b3f5d633dd1ad5467b273f26eaab86c119e1ef4e858fe,0x5abe4e595d271b8779a6fee9ef8c79b7085a371b126ffdcd4b1e4e,0x16a2e]),
(195,[0x95e79d92f8fe96cfcfce20fe291c566e585933e235bf5f7608ebc4,0x5e7bfd044e1eb4d9b6f27a8211475a36ae54668eaf019f3576e1ec,0x26e15f3f08e84ecf81fbf2e56fc263861f904e3c33cdc62742cf5e,0x8b21bddb53776af578b6ae1ef4f4c020f155d0682836bef82ff29d,0x6f1d8d2a3d647cce4f4fc0853812072e4ffd309c1873f5a555b881,0x477758b644ae73dbe9821433e880566e909b0953aae305d1c58ed8,0xc8bb04eb3e25cbd200ba997e17abb5b6a13463bdb40ea878c6c1f5,0xa34d83c5495e332fd9929d0b7a4e5de87eea49f04915f308743ff7,0x8ea4d9]),
(196,[0xd87a220eac6e5e38c45a1f14e5491eebcf5c99fc54753f55f0565a,0x9c2735466b967cc88d0f06e6dcd33b8815c188bf778aa1faf737d1,0x48bb95da4b45344ed12f2c5331239d1a1641015f1bd03c454439e7,0x2a8d49a6a5b1881fc09307357ba31ba8532486ce290c3a4145b3a1,0x4b3540b8be6a31dac9e071e790fc71d533fd07563a76c9e45bebed,0x304d8a2ab49be2dcfac12ee9044aee95cce02146a926d3e45533c2,0x41714c7010a18c320980cd9dcb0eeb7e73600ad7e14dbe1d9b435d,0x94d87616922c48a1a99a79711b0fe548706affa95ea5c5a1aaa5f6,0x42ed990ce]),
(197,[0x49c453449c6c1a34d2b8547178495612c25a2a7b7142082777df69,0x50fee3adb46aabb5dd35fd515b681af1911ba2c242641417df2e17,0x195b81cbc1c051ab05b94fac48f352cb2e40ad32102b9c9157c2ed,0xe6b230bf8461c669b0aa651783ec8007637600db58de771fedf040,0x877275e3490f8ffb9fba3ba24aa1b1bf4d3e72d99f08d92aa4e2ea,0x801784db1b6ae8f3c017578817fdb7fc2aa558845d98c7d8dd85e8,0xbd98c5e6eee8f64c326b687353d1d8dac289302dfb31a5fa00c906,0xe33c7d72a38d091b36d40380e034561efecdebe9cd2f97b5f89198,0x66d06023a8d]),
(198,[0x3b7aec626668b876a5b8b33fe9f087477c94caa62c6861ccfa1341,0xdd4bc4983195672785f12dcd9d55ca23a5bd65755b76343fb4635c,0x65a5b5c5a020a3577f93874eb37dde6a1b63aba0f0feb3251f8a19,0x74f7d06b8181e3fb84eb29b66e0fc52e4cacdf225b3cde2e3fd6c,0x2f36e2d55814df797c30c221ee8f4a7d5e07233a8a25381466f7e3,0x4e041b53c65c1ba1a60896cc97275029cefce8cbc3686b4215fa2,0xbc9a6c563a8db8ca643b5f4db4819d82935121688fe408ffe226f0,0x27f131798d81e5cc31db1ef4dba7f9971309385d9e4a3e342ddda9,0x134165c1b18908]),
(199,[0x83c47cf932077a9d27069a27d38be21f4c4a6f9bec43a1288b3f5a,0x7f037f20fdc45528b9bb40e21a2f80e40b230402cdf3fe5c1c2927,0x88a70297d6bc1eb16b6ef260f29e9a0aa1a031ca9d49345e5e3703,0x66eb14c4e4d1d73a7a3d31ab0b3302ab184333bb64659e283053b8,0x4d4a58ec99a0140296cc25e9ed6e053e3669cd859595083bea5a4f,0x63114c917bfca2448b938f80249f349298492c2540a4218f49f0f5,0x3f087a516bc242d93a2ef4d9246ba740abb96428ace6c2a55aaa07,0xd7302e434886186cb6acf2fba552107149b969f96fec64134fdcd0,0x474a4f7bf300ab7]),
(200,[0xcafc63c45ce60ea8854827b9fae036ddbe68e1c80336490aeddb6b,0x9bdd08c9ef4cd2fdcd09b0e49aae3d0e0b5a7a00832d22e1ceb65d,0x924a5ce6ae79dbf2402fd248c2b7de7d9c6e0bac28ec62fdca5a34,0x1cff2767ce1dd9e87ec3e035c80b953c26fa23e9c5048ffcaac2af,0x2d05b899ecab2ef54a8626e17c712425e09cad4b042bdf798d78d9,0x21d0f7ddde983943dc191d91ee369eed50394a2c892aacd7df6900,0x32c90429516d42d2c3eed95933385f150b62808fb9a50c443b15a5,0xa7cae6058d4d9298f129f5bc9a660819b60b5c97936dc4c759c732,0x92809ba750bb7673e]),
(201,[0x21d10cceae0a8e1e2235ebaa24d2f556200808218c27b237ea7fec,0x8a009d8de28f192ba57bd6eab14ee63a857fb0db4372199fd89d65,0xa7fa067ed04c5709c69430f01aac40cc8f728796ad8dcf9fb7e326,0x7450c8ad2dfe5bbde50acaf71f70f795a74fc8ca0f438baadb3c39,0xe4376418c23e628e697cd8f61d26a97c17ee08b3ac1b171ed20ae4,0x2cf6246601067359e86323fb94e71ca0b461a95ce32211d87e0698,0xcb23dfac43057c09c60d69373a9036078362120b9f170ec333eda0,0xc2ca70f0c3fba30d677da8085bfa0039b4cc16a574cfb7c0b2197c,0x5cb8b6c640dbec6ce027]),
(202,[0xe5bad55bf640f9750c81dfa5e5fb0bc9ac4b50157295e1bed16e44,0xd87a0659af0d6b5a6d791dcb66ee9c21a503dfc4f812d6b5a5674e,0xd5d5aa6969c7ec0e4043fbf3dfc2428793b53f1b33a663513940d,0xf068b7306191fe8445d2f7cbd5c7ae752a97e3930d60640d480749,0xbd891eb31d012d771995242f4c128bb469d71a1eee7c842408f069,0x972e256052b3000f953229d107e0d69b9c2ccca142d8c69635ad4f,0x582d3555ebb4b67c8e53b29cc6097106fed7e8542575a462ec71ff,0x4a12e050f2bb68350225761c00f454e466f4bcebfbaec7d0c9dcd3,0xa9a122db4505bb698da8e4]),
(203,[0xde8044fca720e709e8f598bf7a1f29b6186cfb9e1d8c0508542d2a,0x66ae94b11b60052129f0fe6fc55ec2d43bb607528933df8f51a15c,0x4af8d3ff908704adecae9dcae36d83640a835395d93e77a4a3cf30,0x18350aeadb98d51b8979f2b7b740df5b8411342ccea2305d0878de,0x9aa86fbfe297825fe7d59754411a98b77852940f7f57cc0f074f35,0xb2d1d805f96e3e6eb94265c459a9a36dc83aeb8214982742876a41,0xae39c438a86c739ffb77b5541940a34c2a2ca9abb2b5f9eba1d180,0xaa62cde8f2d434fd4feb6f5228d795cc0bd90c8883ce12e9bd7474,0x183a7885edab612299e253757]),
(204,[0x5f73ff0631b0f68a4992d4b65932e72876dd084a61de1e42ccc115,0xa33a6b4d7e318bcf614c9e266ea226871d70c4c3d0670c08a7e08d,0xf53a92839c152895303750f823ef7d4090b7ace7a1712654659d02,0x4af8d3fb1a269fb274899b38ea7001bb7ad16522e7f2e96da82e75,0xcec139c5c99ff1283ecf585a73053c66919df899c57a65fc1e3e0e,0x9d5bb49b3567ea696cd3519c91f40670f904c135eed36b3c767aa6,0xa6d791fcbbf1d86725b41982d0ff36e4b92e18aa6de1bbcf0573e6,0x14b57c31df94e9fbf7737096573e6a28617a089b320c97bc72450f,0x8c7c4e6e4de2b4302e4b1de2040]),
(205,[0x76a6afefb90479fc65ce5c6573ec4a51a8ea2303472067b4d3b23c,0xc52ab2f7c1d8250971ba46e7756c6fc5b48da07a780a4118eea67,0x751773b40aa568a8e6110a12f8c9da712f2cbbc1f635a6fd89cdae,0x1bcaba054eebdfa80d08cd8aaae2c51a5d57f4765d06e6f700d6b7,0xcb395ba880e00290c06aa3619b3e0a6e8cd586952d66716b5652fa,0xbd98cee2d493e856ca3242d0d0d238c1e2d63b1de64467c853109c,0x47980ca57484a7ff86762099f2da4e905c0884ede519ee523ef0c4,0x7a56fc6884cd5a89902577a09dcf7c06a9acada394c777500f5145,0x873b38916c5f6183f006caf9988b3]),
(206,[0x7cbff4930c76f0ecf17ca15367471356ce24ac27a24983e6bbc976,0xf918523ac18443218d74eab8b3a5276bcec952c703e90924c78a55,0x523351043f6f5f2e4bcf2bc1d23ad5f1307bb3a38a10f67828a803,0x7daeaa1210d227ca9147226028155afeeacb9571f97614e8783bd5,0x1363508de7f4566e0b60f6712da8cb180b29a0ce31914bca1662d0,0xc75f0e194655cd383dc65cacfbcf9d3af20e2a6d00a0db5742ef35,0x8ebf0d9fbdc03edcdbb637fc4e4dcf6a42cba257114bf88a879658,0x1e3b2146e3c89ae2ac3e975ab24ea2f9a849d3738180a95204b5ab,0x2127e44171639280d475e456f57e15f]),
(207,[0x7dcf2a0f27232e2f6f8517eb9456b79c54bd85b71984dfca5f4ad9,0x95f9c1cd87b755d854851751e511e6f9a077b9ba13c2954e803f9c,0xc74d0a15678c34c4d09ebad122f2ee2c1f611a620f0dcf2e9a0f28,0x753105a1466fb0673d73e12e02cb2ce1ce0b4e737ab60c54240f07,0x5018ef2371bdd1af2185233f04de2f3b18692036d30b056046bc73,0x6a4bce98df5c943a325b571d63b16eb5822342649f33fe3f5a27ba,0x8d67c8bb73314ea6748f343814412a64a0345ee15b4f18b1e90b28,0xf91847daf550e3783bd03b47c530449c1f2a9dc61ddec06c861ba4,0x9e9393e8ac0cf438f0ff4cb35ce7ac82b]),
(208,[0x83e758e00dfc889fce8c0feb4e65dd5bc80bf1811e8ab0c6cbef5a,0xba1e77e8a8f412037e264e5c5f08d81c23a16061df4d0f060f6c8b,0x8c151b325e13dd120210b1851a91a1a14ca5e7e922fface27bb1b3,0xa7f9f912b448fc0763e11ca24f20b567dc61d2dc3090fd1a6400bd,0x2cc2e720a5a5e8b87cc3b7785b3a2c7a5e81cf2605417cc6e78e9e,0x582d4d2ffb80116c51d759bcab3fc5b3ded51e019b74c6821c1ce0,0x1489cfcd331b92a3cc24a8cd8e8eeb77cd52bea9fec4d54f3d3c70,0xd6fd13e298e9aed5bb346cf2fb039498834edae83c872f2ba668b,0x375a16478d0b4231427475fd3b1b78790ec1]),
(210,[0x69431650cac0e521bee636daa0e3bba53435ebcddab3880d1b653e,0xfdd3612e41a92a82e90ca6028b1cc8fbe421912644d87b652f70c2,0xb7c8da87c6534bbd15c714423c5c59cb1794694ba167686af28dba,0xe6d9c5a526521a06df8afad9c0da0942d0c100d2996f1ae6c3f7e0,0xae12ced0863e4b076c186a43b70f9fb3435cbea9d1950eebcf11d,0x67101d6d4b7387fe2044d1b22c443f4853e19df2110e6739bf9df3,0x48bb8ca1df0f9821edeefc47ec83b5f90565ab5c050de35e62b6cf,0x427d9c0529aade7f3253aa75f95130b2b0608502c48a21d80f8d59,0x15d57b97eff1b9be8fd4ed3cc6729af8b8b86158e]),
(211,[0x9875c8a9f33809ae651e8a77eb0de1d2f0c30effc49e2dde3b376f,0x67104e67b486f76a1d43b4a3912518536fbffc65c16e04d435cfa2,0x32ed903522e1ddfb960bd5486d18a55743e9ea6ea1d28dec68a848,0x743da6f18609a9b0c87615a966285cbb763c7a78d964318522fd97,0x232a8637b6f7686363eaa2dc2b0d70297630b38c00a4e3cabbd358,0x7ee300cb8e94774443552a72a90f8d4bee8c6b0aa7e0c35104c1e7,0xfda970fcdbdcc8ae1b1b70a0bd744867f2ef0d0475d91e30f26de8,0xba5b6038b3ef14ed67982f218ecb5f43ab6e111547ed9b34abb9be,0x4471437911167354b17c18343b6a30af0b2ead5f87b]),
(213,[0xcc58730e2381b472e1f48a294e776b852a28201c6d818a193191a4,0x77ee34aa0d31e17184bdf772bab89dab70bda03a9f365a74d921ff,0xc28d698008ebf9a2d0bd0ecfb5d81ce13a03bb9372c6103f6ba99,0xd224f437ec77ec299c0d454579ec8ef2558bee14433aae013d6386,0x813d4b9cfaec534a677571d47d671e7b5747a0d2d0264d21504db7,0x9fb058fadab1aff2b76a141a89421ea57f2d0b54e2efbabb78951a,0x87d8e0cac1ac702f661692702afad51a0729a572e4f32733dfd90,0xc16c2a03dce1a4774e57c0fbe959f655e64de54cf63c4bb2b42e99,0x2b49808cd7330aa4d0584d368e6e65783161f4038a0e3e4]),
(214,[0x379adcbaea233b31e14ae214f9ebd06aa9ba409705c55c2be6229e,0xebb8e9a45344391e6bf42e568b492b5d1f14b81f2093572b1cbb2,0x3b6b3b624fb07e3b18a83f4967f5a38e50ab04c2ad48816f750485,0xfb54e7b22b3bee1a11eb3ff0045887146535eda9b152e94ad0c227,0x332eadba0ad5711370c15c1dfc30c01a959f81ccd19bad50b1de89,0x18273985b636ca993941f9914ed7f93dda073ced2fb22cf05d577b,0x2439d91aa908782600c7d70d3cc6f9e8feeb8e5c7882477c1c1690,0x94a26012db9b2871c0f4c76eddad37f06a803a51e31d2b57652f27,0x2810673e241c0bb0ecf4b4d475c5a98dd5ea7f6036fc111665]),
(215,[0xc3fed49592b0403a5dd0be7be30186ae414b8b7d85c9176a035c8d,0xd745aadde74f0df76673bd9b4f25f507a477157bf3812accec9363,0xd24a2e291a27c1c1ff2a361b4e31fa19f08cab95ee1e45f7e6f18e,0x6461a8acedb68dbd4fb78e7f2d8d8e57d592c809423e557dc8570f,0xdfcb4e9c063bb1cd4ab9627b4ae678330be1edfeb9585e28271c52,0xa6a500467bc791ac38081985b15c831830fbba464553ae4d3a28dc,0x6b9c2415caa5eaa62904a5f75ece84a73e64abdc03a6db5ac0e72e,0xd4a010e1c51abd791159ce1e42c238d40a1ae93b28f0b5bf0120f,0x146139ead94bc176af22c1b46eb6c6b1b97a054d0269568ef54a]),
(216,[0xfb812cff1b8808a1a5f810034621da0bbed26133cb345707bb5123,0xc9ef84266363a5ebe27342eb385cfaecfdd58b023c0f4239bfa2f4,0x9c0126fe5d197c756e81d3ded7e64531836fe37faa5476b393626,0xdfcb32e5f93e9e7ae9dc9c5b80b7c221d394f83e5a917947ac4500,0x37bf6b9399a4581e1670cf71f72b4ea5ae029720da97ee5a5ab428,0x9c273548257c1f5ceb4d7071f2cd5b69ec04a96e2ec74bb006f28e,0x878475b3d5de22ae46e21d490de34663a1f273204d1b6a76a777c3,0x6953d58713f9d25afd2a35e5d90f60527ab288aa43ab50afd504ad,0x2e0265cd33537c9d30105f31f6c1204a65cde47bc61429f43531cd]),
(217,[0xbcc4633f2dc2fc955f973e721bebee18295c2a02dedf0f36843a6e,0x988a1e16bce3577983ba46f2ff11204b2fb00d12c42b78eaa884f4,0x4eb1f7a680036de66aabe080a1a4afc292195adab66793d54bbbb7,0xecdfce97980bc0bf2884cf77732c2a1379ff1d4c9acbb5810bb2cb,0x2de4ac5463194e2d8eed1b7b393088488832d45acfa4533e81fc79,0x4ad7afadc6bd2d54e83cf3e8ad54e8efc7e44436a54f6cf3d5f892,0xe7e6e60e27a39787ea127f23556ea0fddb5e111999046033f3a2e,0x2f21e0ff39a7c32c2f95fc99b68105d5a3e8180aa2af6245557685,0x49ad0da92c329ed868e362916b05e4d6e7e7dcb2bfb3639e314862,0x3]),
(218,[0xf9f91db835a6772c08dfdd807af7244f9d6410be3b04668de5a3ac,0x680eb2260407f9adb9c664853380a47073ba8341392349b51e1825,0x32bf173b70e0acbf10b000b1dd73a10e67a6b951d99b7251f26bbf,0x19722a9c7e23a8a8b1e0a1da52c32a08423486bab2c22484a721c6,0xba0c5c0b414e41ec0b6fea339716d89e705b8e382ee783e4b3bc30,0x9bcd50c7c87fb67eaea783c96abcfc47bb958236c4e1756c6ee4d6,0xc3c1dafa1fe7ec03873a195c8a3c5c8aecf5e2bcff39d77e7b75d7,0xd24a412b3ab1e1a63d728c375c447cdac35b2346b705f22d065d2b,0xd5fbde413b4e329c6a9208e4fee29f7c40780c4cf22e04bcfc3d42,0x9658]),
(219,[0xce76dbfc6dcacec1488923ff838d5c8b15deda7dea0a5019792247,0x42973351e24867b6ed7e6c25c55b97c458fb7dabd7eedf58cf3522,0x2f7f8bba80a847d6a98bb76e6c09db2992d7853a54b8b37b203392,0xabd0f45f0d60b8e3db6b80709245d77cfbd8e84e081d11f4b9e5c9,0x439d165b2eacf10bf806cb33d2b0bfc5e95cfb69c9ba8d648d50ee,0x76658babfa6f1a66a6ea12eab6ba22a656b75a7d8b51e327424a0d,0x14cef666234c3d1779df5d29f9095b2df045fc13095e48d60f964a,0xf8d7c26ff5623299673f022d8eea40c0e064c5a15d49c3f6d4ae30,0x6953ef971aff45a469b5d337ad296b5be6b30f9b7a2801f5142683,0x1a47739]),
(220,[0x103d9843b1541a382c553142ef84bdb174b2f61f4ef55d31aba89dd,0x48cc7a1d5bbbc0eb7377c09e8e9a46484297244a407cb3133e44bd,0xbede1790adf44c2d25619d3b29be67d29476866adc19a49f3e2554,0x9e68a3d199171d047f1e57aae7d1c2cd9b7fce2f0119e2ab570312,0xfb81695d8a58c109601a7f2d4f9d6b79668a9fb2a37208b85384a,0x6a59285c3785da42b148f6a0adcd05efacec80af596414aee35d1b,0x9bbebd692633136c3a338d98cbb1e4fc02333ff08564c674c20f31,0xf9f8fac6ce3542b068f9e4384ec6f5b06d16a421ae2798c49e9ab7,0xe80e32f761fb169564838ffd7fec386f55718df109d3c839a28442,0x2ec5f2665]),
(221,[0xbde35266d185f3b6270193e90aa07a69d7198e79c3a8f8fcc83d93,0xe80e21151fd2274bdf5b8ecf5144a66f1b8568439ac2301c67ef28,0xcd8ce06e309b3ad89d74821df2dda99479e1a8edd7e81e9e0fb364,0x635fab747f599d1916dd5f12aa643bb639248814a3d0578e6983c3,0x5875f402f95420878bc0b98a1c9783017a773730f2e60aaad21f4f,0x197c10be78d67a1d2939d27dcbf384eb14fa9ebfcba1102960c120,0x8037f3ffc6189b3c1170fdbd08be65fcad5d121f3dde165e2de1c4,0xb51a1a3c917ed78784b62e6e805b7d05ddd86de4668cf8f4daee82,0xa6c58b9a66de920f1617916ecdf1b7cfca8eab381250aa42a359c3,0x8520a995a67]),
(223,[0x77c8f6433d318f673b792a5e4520f7aab3185cd0eb5ed1c40336bb,0x633cdafc992b73d261cf03cfb5324175b0c9f79ef71749974a0286,0x82b2e1a45e07d2e7789f5521cfc7e9bef27a27e30f3edd84e4ce63,0x45000e1f1635534d44b41b89d53850a083c81896374ad701e4c108,0x7cbfff790f998c092958a83b22857ce419cfc38ed101b95132b214,0xf42ff6205566f017d5ba7c2414ab4bf1b2e489636f83655c2db839,0x67ff0adb78e8605a1b9e0eb9e2c1719f63caa9f64d9f10ad889fff,0x71d4fa4eb4e3139888e712efc685200fa106b36ca51b9ff2d2fd5f,0x9c1310cd4cf8265b4191ada7afeb20f9fcf040ebc5aad0de51f22f,0x3b90c9acfc9c85f7]),
(224,[0xeaa3318486b3e61e3230765520ed526149125f310b393fda5baf0f,0xaf6e1d82eb20943eb0b28618c1950f445c9a095b85378b1a97e41b,0x10c486efd4c8d76d960a38a052c07c443a712fe63ff0112542d99d8,0xa6d79200e794a8520fd7b4f32cb615bd94e4f4e8006d748bb2e77e,0x63115fd1545b86a2810052cfea9cd57080d8be15d1653e0cc9b40b,0x1bdb0556775d5842d3b747a11040ca4dd1bb9ff145bed7dd46f51a,0xacab2c362b3b09ccc469af47158c3e1284e244b6460320f6f2f839,0x122ee33316636ffea6d702c7809b2f711797865fd6c515126630bd,0x9755a5c2c3ee5c311eaaa607721fdb4f83f64427d3200ccc8efb92,0x2b3f92fd1dc802f68f]),
(225,[0xebc0ee8ee8997f441ddd3d11954eac526a2c06e61e40fe09f9a3c2,0xd3a881ba03cbe29fc2efbc14ed5d997f455b5a9919c5c3ff529cc6,0x109b5b6f5ccb52fa5aedb75941547ccbce358ab210ba12b5f66ddd1,0xd6112376b357b62e410d21a1059ffa906425d687fc5408343c8598,0x7a6b7ab0de249c28c267329ec8fcb85f804e8cdc2282aa0b16c807,0x51609d5b48b61f61bac2e1a63d49b68b94887e4bbd2d4117ccb143,0x5281affdb54313ea33a6c0a9f3b73ee61f13ebb4014044d9d2e91d,0x935e3835214e9bb90fed9c57fed35f28010b58623884d8f0f2ed74,0x1062cc0403c5aaa880708e4f8b30b84b4f07d9c6909fb3afad49c4e,0x4b1742376e936d840c9b]),
(226,[0x10642553263608ea28a2dce6d762b773a69d4bed58a09edf0431902,0x53400b1ec370248382c7ca6d5dc936c66f9e04208096c80849d2f,0x64943cb4333d09718aa474118e27d74a589e91e2a3c449622cee45,0xf56459bc3ca3084a7da8409c5dd41efd36b46874334c32d0c4396a,0x2f2bcf499af01be1f06f4665f9884e9faa01a569770b1f46a0c495,0x2cb39fefd9ab3681a8190781facff13df5ab658eac679483aee42,0x3ed54011ef45c075dbb9c1efd298f02710a84a8c38679392ff5c17,0xa7149cf0e5736939a7d49930e3e5d7d0d0a8b6977d76ceabc9b441,0x66eafabe043546b9e684eba9339a9134f1f3110520bb3d09a8c08b,0x6b5b1c0310f9b8d416a0af])
]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem baseCyclePacked5_ok :
    baseCyclePacked5.all (fun p => checkBaseCycle p.1 (unpack532 p.2 p.1)) = true := rfl

set_option maxRecDepth 2000 in
private def baseCyclePacked6 : List (ℕ × List ℕ) := [
(229,[0x96213862b9e26402083ec52b7f0a519b682dfbd03080d48d3b85b1,0xfdea07d70f30d98f669cb5d53df8c9e71b5be0279f8cf38adbfd31,0x10642434bedd0a8fe6407d922e3ab430babd2133372e70a5d45626e,0x8b0fcc8ef2a2af4780afdb8fbfa9d0f98a71ffb7c13e473a969e5f,0x94843a8124edc793b49ce6d6685028a7cb7540f3440f57eff22ffd,0x54a97c0fcd721e62fa5874cf9cd6c60eaf3b2b9cd102a5ec0e537a,0xb1ec62699ebf7fc79dccf16fb6e03867d8ee5fe0466ff18e7eae6f,0xe1ce67c009e4a0f93ea5fd02d011374774d251d6253f22b35a134e,0x353ce8bcba79d08d10c3a494d4c4025577ad10bc04268c53f20c35,0x104384b5322eed4d16dd485c5c57d9]),
(231,[0xed0beeea70be5317007efc5c192c17d92b209a6cd92787de03d965,0x6965fc9dfed32ee66fa6b95fac00fd7817d7a097abd77c70f94b94,0xdcfcc073bcbb99be570023b4e072048cc23d76cb830ed1e7da13c2,0x43da42ead4f59f4226121d690397bdf61ae6299111c32fb90c850a,0x3db842238991d07419640af898fda7d9cbcaf9acf14cc09c88414d,0xe368a11829fc33fa2d623e9d94f703ff8d0859f9e2974ee72fea02,0x4dc34a3e4c702ae801cf12b8d67cc613bdc612716bb9e6b6baa5e1,0x2856f437d46ad9f6d3d2936036739b1cc87b075baf9b2ca39c4d14,0xaccbae90fd294af58ec79e6d3d641380ad8f4e55e025f91ae73fe4,0x4b8fe575e0ace47417920c0b48e45f7e5]),
(232,[0xa591334280ff8a385007815f50ea58e70c0e2e51c2585528e09a20,0x9bdd12036fede40f09c6e23768ff2261ff1bb2e350e7f870e432cf,0xfb54f7691a9094bf4bb8f9d6fa2296a7a7f9ddbb6c99a51e867030,0xe7f9c6f5196c3098a87c78129ac7245d6e398b7c69d4a02fef74c5,0x26bcd1860187615cdfcfa918c22700a391f5a226a4f6387fe91b90,0x36a923b798f6b99602f0d5e48d446669235e880df6e9fdacc25f9d,0x87361440110aca5a87b8151bed5172d5e68ff9848cef6f7eb3f70b,0x7c89c0ebac8d1187575c18705752f436d399c50d7e7b33f1b0ecf5,0x9283f030b58299133376107fba9bb59e3893f3ccc5658d5992cda5,0x590bee32ba13a04ce2d1db7f25ed8ad39358]),
(233,[0xfde9f3ad99e9d996c07085187d123e5343272c780aa01cc0ef0aa4,0xa5e044c0224dfc9677ab2ffd254a875971855a9eab491f32efa7db,0x9d5bd3a8d208b8a05a65326d194d0bef5c071ea122ae01e16f8a9f,0xb3f57c56560347558c0d11e83ec24da81e9578a427ee6865981247,0x19a0abf0b1ab211b14fd5fb8dfa65ac667f7e474c6235c386975d4,0x7571a8e5ff496e59b258f5ff9c5680217ae3b3c414dcd445cd433,0x20cddf4152fbe181afad2a23db1714c4a2d8dc13b462c11b22dd22,0x3caf3e0b5487ec710c545cf7bddca5fd67ba565b78ee6c64370002,0xaf470396e3a9c7b356b86fe30a3d1639e688caaa746d27d846eaf,0x35900f0c1fecea16e6ea5f38b163d86a934cf0]),
(234,[0x1174ed0fd0373a7aad6e027c62717249e17cd2c216fb00afce12342,0xc2ca673111c992cd86d14ecc1ab81f11e8f38d8fdbdceef1625095,0x9f7a50f77b47332474a8b23a2138dc053db16bddf450fcafa42be4,0x1700c5cfbc1f27dd959dea69cc1895c45556328a418edd400dfe10,0xaccbc39505a0ae86597cab52acc3f16c1ef1a352ec9cbc4f00a432,0x2a4767341616ae045bf8d4229b0a6aa158989b1d48ebaf4ae8e6ea,0x4c492d96a374de4b39552dbea4e71e8ebf4112bf486b6880321802,0x2a313528723903ed1ffe4595bb7caf95b4775f1fb7350f0cb3811,0x136f5e38205be84b432860e19e41c31b73b07021e09d9b843851b,0x96620fbae2a920628cdd09fc8e0d4ae52dc9a408]),
(235,[0xfc9eea0e32a7272b30e2ba51d401740947b2aaef1ad344b63116f7,0x8e9c4cd6f9a74d1f1a5ec6534d3e93de6670e6ae59bf9ac35b3fc8,0x648243cd9cb3ecb57b7275629dc400b5e9d4e171648bbd4c13f616,0x1d30b88559ed28bbf93ae99e1c96690707ea2680e7d1aad4ca8071,0x54d8abdceff9756ed9fcab8ec5a58a289060dfb60242508f5d081d,0xeb83dffe85efe0aa75bce60e1a3b047fe40c9580fac2791d054316,0xc9db180aa629ba62c842da830d58f9e57192de0dc22bafcec01d36,0xc88172aee806691627a6555324c8f030df734307127e5327b90c55,0xf18a02e967305e7eaf867f22fa5c4bea16a0d034cadb92de627347,0x18817a0467e1b4ad7808bc4748962f4ccb3f2fcd0c5]),
(236,[0x10fd03b241e9afa5d8025571b02e20223a807d8a584313856c810c4,0x8d67df726d29e99ce251b86b16554165f8b159caebb15eff8bab1c,0x5e3fb9e2d9c51b8882631abe7f8125c1f8f21064571303adad05cc,0xc214d2b68568765a62731d9a29091ec3ba06fb4f8c0dede48895b,0xb6943ac04c65d7525a6ecf8a61573f149516914d398582b91f59b3,0x3934fb273d7de825d9fd0cfce04044ed9cd3cf43148ff73e54837d,0x107614f446f4b1aeed2e01738f1325e2218276ed943fb0afede56da,0xa0f8f389e18420be99b324cc321639be036db431227097de91c4ee,0xd4dcbe3294ed5535b481b59391c8752e8e66d4522fc01acf8a78bc,0xb331077e58ce7268c5d2810e1427270a6a82a2c895571]),
(237,[0xa37754c7c613e8c9150485b8a7078d04c1636d959f8e9a355dba6d,0xe1e07b40c4053b766df1e3afdae24d12e95a0212aa20ac94acff29,0xc549e7f110f6620b1eca8af488382472678ae6f7297bcc657d2d3a,0x49a34d71f8b21b0c7ea91a3a01844a1c632aa6958046e6ab277bc1,0xdf77c8f8aaf9a46fb608fbdacdb0b54db2f97cd81ccc89fde49cbb,0x474f5f1e6b7db0915f565c22f15f178b50189f6e8fdaeeac3a321f,0xa205fde8fc461ba3e9533a4a5e332913e8ab8b60393beef7b2567a,0x860ef836eb91a2825809752644f830bce550e0199aaba414d4b99a,0x185ee17d3dde17739ec14cdec6cd6f972341d04c294da0d510901d,0x1ace5320dc257aa76c4282f989755b72c09976f2c3205955]),
(273,[0x71d4e64790202ab61920e1e962109bbfa0305df0b916570ede0003,0xeabb18f497b6f4f47b5fe9fb099bfe3addca6e07c498c61a8e0c2e,0x109b5bdef3d2647579565185bd48de2bfdc9c0b4648f66fe6e2f00e,0x95f9c1cd83d21acb3cc79b861f0f5bee25f8b023cd98f5e4bf80fc,0x108c1e050d81b34cbab6983136a71dce9012fd12dd1367eeee8ab0c,0x5a964dac209d0f355d3a12908d98c5d46b5b7d85aac82492dccd45,0x11c08993e12bfaf87d8e81cdbbbf3b0facaa58bcaee526692d30e3a,0x1f785f1e5adec41b5b155b7598795ed438cbecd077133e01a32e26,0x6a67cbb70cba2d02abf754bd5071f082ac02d9e654875f52e0e60b,0xb07b1eb298d615fb515357b9f394ae94ab77e7b22ff143e8145dac,0x13dadfd55b30ee2a56d84413822e14dd12fde8fcc2b51f7c1df24fa,0xd06b0b6357b12fa1eb56]),
(274,[0x11c3974741f03c05f362991cb8e1d529b918e617e5d23ef4e2bfa1b,0x13f29e45ce1e0990cf9f3ff4585cfc8787e21b294c96ba2e1774026,0x93b85d99aae62b04cf9382fcfde29d7096b8a8fb36d5626f2490f5,0x5e6b46f3bf3670124abb0598cd515968aec50e29640052ea33252b,0x620898fdcf411c04180d671254109337aafb2f325c39603739848a,0x409703d22f4c97ccaca7ead1bcd9d1135c18855e13cc2152b630c8,0x8886659bb605dd652e002fc4f067c237d0b4927cce256892760cb4,0x4180f39d6fead466db63d4b9fb1739819bc124777d9cf5fe222490,0x13dbb16d24b9d1f5be204c798c28ab6217e39dd01b27814ba37c7,0xc39ef1ecee734aa4ecf21fe9f495f27f9d433d28d64becdeaeef87,0x3451083612bddbe88293108a9b2082f6b1c43307816c6b35d99e93,0xf39213860d37a9f1e8cb61]),
(275,[0xd021ed4d12d75c3dbc96d58050ab23668feeb7ba6b838d09148f79,0xf1f5a94fbea6ee72889a035372ac349b07b897cb4023fbd345a4ed,0xbf43e5bd72e3aba0a7397b3a2f686f9f4ec850f335e6962ae2e8ad,0x14c39ba46d0e5485c104472613e4fcb75e7264501c75d2a1593cc7b,0x7c9abcb4dda8956e2e3216b30459857029f1b4ab173a16f94abb81,0x1c27b46e33c1ab39381d3e09fd05756fcd3b292e8641c464809e4d,0xcf05516abbfb002af69010b6cbbe5c7ee714695cf4a82c6fdd4452,0x75179502a303b0f21fc4cb1be7a88b0d690bd6b54070569fd12b61,0xdb1154525fea5a8db219a43b0eef87e147965fbe5c237b03bb5af3,0x150e7ba3de97b1ca283649e532215acc5329b1eb94dcf9d86dc63,0x4014b14e736a9434d413ee782daac5a37fc60b5c558a36f1116fd7,0x1bf99bf1fc2f862be0cfa5cb4]),
(276,[0x1c38c0e250366607b513ea10ac512968aee07b509a0768c57795d9,0x1fe7f681504c898d55494bd66636a18664df9c41f0a1eb0bbe3f29,0x82da6215eed927364ce376983a3b9484b414cec5c8c7d8f4e965bb,0x110f035c2003a3cc4c0262769b7571be84d8fda1a9cc1f49f08dab5,0xa33a7f6811a59a6dfb5f1e455042c73f1ee4ad0ae67702851dae66,0xc1ac8d02cfc4fb1729a2d8cb0f69a6078f90f6a5cd6b995d3fa99,0xceed7fe88d8d3cc836cb240b6da637a530a49ad4a902ccf4d93272,0x402e5104b969e74f86cafd614ab21f343d339b359a5801015b7e59,0x4d7d9266620df8944f4d36969825a117ca325fb8ee36f595efcad7,0xbba6872b0cc72f1fc07bd7366c48162fcf2e6383f0aa10ebc8816d,0xd999090c612a3cfb62d73aa7f674f00155449d0acaa29f5755e2a1,0x42763595d86f2b41f0aea4cc1bc]),
(277,[0x7a6b86cb732cdf3e06932e3150538ad85716a67e904bc66725b382,0x816c7246f5bf4df6f6a5920462a5696fee0570ab36da14b7d2bb1c,0x14db9103e5ace569ada13428b2248eaab70ca0b1e7706a0e67f8a65,0x10a0e3535f8b08e7ee82d646bf23bf05413769c06f37d248a13dc50,0xe0e90cd5e7443711efa94a787381bd7345a77ac366019cf3ca1a4c,0x14798c155bb80f97d0ab8017322da701d17ba07d6198f775e28cd43,0x14ed351acef29859838ae8571e5f8ae7998da1c7eaf905d579e4122,0x4c58e7e6f16b35e72290e7db4b7c56871d39298a62f3ad20eaf717,0x10bf960cb1b76e159215e13e3c7daf33f8d6f1d6ba83e8b3efd237a,0x6aad814ca044c29df2619a3277d778015957d230562bab9283289b,0x10267ee71b41aeb0fddd955cdc3bdec1f9b4fe94a5d2daa5f1d4648,0x8edbbab018282784895cdb24b34b6]),
(279,[0xa940a2731a9eedf4e2e7b291a99615a2df86b213b51d607b4872cf,0xd95f7e28625e5daff2295bd6ea4976055488c28d658a8dced97051,0x3a0ecd46e7d9d3b611a1a5ee86702a76d7ee6a458d9083ac663324,0xa481f126b62a7cb80328a585c52c9eba24a7ed6786bdc787f52a35,0x53c9838ac8a62064093025167b33c3cf944065223329f5d4e05cad,0x13f43fb066a25ef5db2fdf7e4f9eb4f213b9e43eb1a4e11ae94aa63,0x690b2dd39dfff51f0553bbfc38558e554cb320f8dc718d3322d831,0x1f6f9b495cb6f6152403dba89512c6d5a9237475cbc52abf30b879,0x113b17df863c43ca11e73023a6e34c4149f6d0d6194fe16e9b51a86,0x12226945c291b8563a3b2a2a357cbb432717269cc91226a0de190e0,0x5fb0989e8befa5ce65b3c73441bbc8438cc88ee5b948ed9056e248,0x35f7c8ac00a7ea70c57669ced6d203b865]),
(280,[0x14eba790ced5f0c3493bbb1c86a4ce4f97d6a11f13d702511024dad,0xc5097ae64d71244adeff5781039e36ca64af12a29aef28709c1514,0xc7b2ef819595c6d05f59fb33ecb2a45ad2060ae7a86fd607250712,0x149d0cd9414c9f2bc84cbe35ac3df7d12d15e72e67fa505e1ebb244,0xa9944d3e5b5a2c0c0ce2c9d58d2e8263ae27dea580941e7892f230,0x9fb032f1d19b736c710e5a165f52f6805326172dbee60bfd66f061,0x83c474499249087f2c08bc241344894e20c8faf9399d2e3d5c07dd,0xe44949b00eb5d913d8be92ffc3c057d5e4abcd9ea1582a81ca0da4,0x55c46266afcc1fc83a267cdda3ee18fea7db4b434965cbc364bf24,0x34086b65945c6c310ff7934086cfc510556a09aceb32c89ef23219,0x13ddc7d929c7e9e77efacfcdff4614b7c6578e852113af85ee0ade2,0x8da77f3b61e51e7f575ef8bf73ffa01724a2]),
(281,[0xbba69d8aa214f2e3850712a9a78341011b519e614b28546eff4f21,0x5bd6c87545198a4b3dcdba350876a38fddab7005ba0b1078fc2989,0xe49cfa668fb015ea1cc0c4f1280131a9caee8fb6210c087949881c,0x4014d641f10fbecd8e039103974847a6a5d0680107f7b6350f63a4,0x11161a7609018eca83a16d2367aed4ae65101f33da7d812c0ad2c64,0x10420f41414fddd2ec8620f0f0956fa12a7bbe2505045f9ed94469a,0x11633516c50b7026b017374a76be6970f7c4a9463e5b901a769b689,0xd1028e4342a4a66bd65d85c7ecae0456db462bc38b615eda6f4417,0x4a12d61602bf9323b371af911f6419d975692ca74095a8d106dd08,0x20b6a792534c10faa056e1732057c1087c967b206a91cd0d3f0df0,0x861d9fbf00bfa6c4bf0f00e95428609245df6bc2c168991f6c49e6,0x13c7c9cfd893b79b4d1032f45aa1dc25479f851]),
(282,[0x11d6e05eb14ddd43a169a926529ef8cfab6e6d5c58eb16071b79d95,0xb8ea0268d46f659a96174b69bc8372682b011eaac97f321f35adf8,0x6bbcb0651b62791997bc8ee8b040d6d27ba163fac853c9bed1d6bf,0x5439602645dd3cd9d76dfc82b9d13148b53e7fa79b337ec9c85ab,0x1ac7cbf917f3d18d675d8762a745c7549572f28c5a2d9a1584cc35,0xb7fd47eef7397e3776323dd6915c125d76efbe5ad4c4ae3515857,0x61b314322bd19d28e945674bfebe7b92e0d1f8a667b7cb2ff11e0,0x18350b031bac8ab6fd667c3a82a8704f472ebe21e7253f1e7e8b20,0xb0a2b5614d21a8e383bbc73437eca5ff860ac1ee67b6ea609b1e99,0x3077665286a9a650c8f0ece95d78a92bc694ccddc52ca07a141456,0xb7f2b91d3aebf9114a222e40d8ed61e90ae370a46e8b89b6ada9b5,0x35c1b66c0317af2c72c5931bf99b2ff5ad7b3e36c]),
(283,[0x1161a7b232d96c4c91d938304161e9f66031ad329e4b386f91d9d5b,0xe7e6acb91b7fb332a80ae24718f6bb174d971e9a9fae881743e376,0x790f64b4903963903977cfbc726048ee80b490825c6719391de155,0x4289ee9440e802352d1a72333ae2345f42b96a287ef2afc8424214,0xc2ca91b02734b29538378e1964bc55bc93323d6d4d03ef19a879ce,0xa43c25742a0b5008583d596ddd7fa59b410d6cfe91508d04bb263c,0x41493c2d1c1c75b73819b8b5742cbe7a4a06ac34a5b993e59ec575,0x1078d6889a87d1982521f63e6e84c0e04c12bcdc0eac49629e3aa77,0x38e672adc13a7e36f46d4931e8df4131113b653311175a15ce2eb2,0x83b4afeda142921ad70793ab0cbbee7d2de0024e4d64f5a25034ba,0x118549584f8c5a022f6222e96613c99653d55b3339ba78741fd0497,0x1477be1f745d8ea7f777aae2fadb18ab1250b89648c]),
(286,[0xa6eaf44cd160c5572ac94e293dfaa7902b441b3e5d6eaef0e2dd95,0x95d6cd8df9d573d8d485dad4b6730153f67fb0df00023114cbdfa2,0x13030303349cd64173ad886c3df9d27f66783e4184be51e0f9f3d89,0xf2d18c1da5b5de0a900feb0634148f26e708292cde7219037b7898,0x129943e7290fe299bb02e825cf79a886be3afb92b881f7b646b2cec,0x90309f2d0f3e93972c1a869e39ddc879f17d518bf56e56262b4daa,0x60a8a68fcc7063849a0b379ce477d433a35f69ac8d735a056a5255,0x2b7bd4989874a15319c4c1685e5ddc461fb8f6fc008d342dcf535d,0x7ee32964b89d01face558703ff5e67ce1d175f86bf374a9fc6352d,0x3db828450fe33a119ca4c2417c5303a04a3854b25a086271087628,0x4768f9ae606d055a9a95406de7a16c7d5f5e429f6a838fe45746bd,0x3ebece9ffe582ec8c4f5bbade59fdb6dbae940908ff577fc85]),
(288,[0xfe1ae9b58dfe23d0f838708a9fb29ccfdae060f81789ea6b3a2736,0x12f4f8298b42c99abca658e752c7bc7810251ceb61b0dbf1a2a091b,0x14530073df22633f4d62c9aeb7d9759c5144a8484a3ef38cbd058ba,0xcb39840aef10d121136ed3144322177bdbb5b73cb10292a30dc7d4,0x154f3b8217bb94ecf0b30111955ef3e6c14e0f7e2cbb6c82482f36c,0x306b5042fc2a124ace68adba26c15c1f0d708f3ae6b896376c6a36,0xad0542af00da6f4bd7df2d59841b9e8358dffef4497eb3ee810de5,0xfb810fdb6d4ac203cc40354eb526b1b550422ca88b3cad52b6891,0x8ff395188a04e7cb835d8ba067a3b83f638f119236cab8e5c582eb,0x93a3f5c2bc0d1ae345062496018940b0d2aa2d006545a8e675f809,0x4c161850abeeafb5b46daf29d4c73e7ef0682c566c6654812d93f2,0x2e026d4a9d690370b05adf125a1bf3199f7e35469025f856270662]),
(289,[0x143fb8e6e4037b384f0c07921f7c3de9e33f3c6f37176913af55883,0xa6ff4a425f1dda27cf7af4799aa36a8c4215ba41f4ada5dae1a841,0x1244b681265188060c1e06f34d325a3ed2c4c7573e3212f7145d8f2,0x9964512b95bd6e17fb3e2c841e52ccdd1aef6d4702473e9c46a6ff,0x18ad71abd7b50ee05058ada4fb71c14390fc3690ad7b5056163d3e,0x121bd7df749f91bbe72d7b9ff60551e7df71e9ce17a638b7217294,0xdd364081067aeaf265fb0ae14a253f55eca0103fc3a4f1853a692a,0xa8491f84fd4d05e7e008bd63ed893e14cf14b3686485e3075a4ebd,0x1489cfe22f9d0ebe23c4b1ae927b158f800be00f85048d3f3edb31,0xea76f3d2be0a43eaaea7d9984dbdbeb613271499ec5c2a1a86c0e0,0x6bbce9578b2cd0b27d0f0b7ff2ce605a1bea445c4124af640ed7df,0xf20ea3c8518205a5c630a65a1d0e94ca74ea230e971bb79d90c9bf,0xa1]),
(290,[0x7a570f64062deea0cccc7862bf7c0af0a18465572702932dc8f2bc,0x10b5b9d0745826c25708b254a9b9c129797240aebd8b6489e7234c4,0x153a51c93cf933b3d6c6f9c7cb5362049fa8f01ab9cc5a0f40acf9b,0x125f70dcbb6c442e891d8d69d56512f70a3939732fda43cf69e07e8,0xfb81a3dea63fe4240478f8b880114fd277e2a8ceac3efc893c611,0x99ea902c78b25d05950cda42456d5268ad6bf6ca75f341fe2c5c58,0x58c4f706e20439ec8b2da6f19cadb7a7f1ed75f277064ae2a82286,0x1220eb38b61db6c47d086594083e5ea8ff91f89adfbacd880677bef,0x20cdeedc5af62f2b2ab4d08571cd81cb0f5c175f3b3a9bfff5c6c5,0x4b14dda3b7c0949f142e9c477c706e7a65942033b1f1444ee0610e,0x1522926eb179e74b6eca437e685b4b900da266c3e38fa43af323d97,0x840ef1e3ca955e9aad618ef94a7387e4645e0f20a487c317613175,0x12364]),
(291,[0x4643280bdf1e66fc288338cb20f5a56709ab2fbafc6e969e569e04,0x3b9dbf9ed560b573c110885113ef5879d1131d764149c393d62323,0x11f8f2cdd46902804be8c9d041204a2116525869f95b5897702e8b8,0x8fb26c5693eeb26e68117a7328960232bc04c50387f78c5e126dde,0xf2d1caca8838908a860b0ec230f5250d4693782aa1b9ffd0f43029,0xd730568c8f8933da88ac8341b78f2371ff50e69a91c090a6e06838,0xaf34af38376e60d2658a0d3775f27fa90a9dced76e3b31a39e0f2b,0x11c209e19cab078482c02a2999d46c0cb1d93717a20af8eb3b6fc9c,0xc5334bc1e169998a268f396de57eddf3a27f03f8bd48c7fa270029,0x64825911f16b74bff033667a644821f6574093135e8944336b2d41,0x13f10d5c8aaf7bd4b2d5cb267ccd26160ef8267330348dfdbbc2691,0x659601185200a733e036c5a1c008ae1663c58abb1f7dd2d2a64bcc,0x1f5d800]),
(293,[0x60c445ac7d101f8883f27b465519fdc89ae8a668e7f9fb024d8a0f,0x7560356f6ddd2d0826b35739e23dcd38167d86c418c18f4c955961,0x88b90e868cfbacf1b2760a6df023331bc9771ab615a483832665a7,0x3dc585e43e801a04a7cda25cc883f84530e50d30a36b45ccdced80,0x4b355fb8c2cce51a594a14a3b7ee161ca37d4971c58eca2a2924ae,0xaf4888885449ef9a6d2bfe3fc5aae0dd1bea7f5a3dd0c5199cdbe,0x5887f6b4af5ca78bfb290df097a9e2fd81624230ca8564139ce0af,0x12be30e0404737e75aab558b334a809432a4691644895b60b0fecf3,0xee40658acc10bfdc1cfa2c39214861b9790e8b11f31e7ee8a728d9,0x9bdd1bdc9a82f6569049c31185f1b1d17a5a4bd6cccb60de1d34c8,0xc8ff21eb5023237a4a53df01b4159a2a07297ed35a56f8f5176687,0x14798d6a697c3413072698f69a0ac6a7dd422023d5001fbc205e12a,0x9b9ddcfb34a]),
(294,[0x7f28cf60ce0551855ef4799c176c9f945cda3d30cc42d3c2acdb84,0xaf59dcd2ebe6671e98787fe42f1056f7612069f76a38b007f23c9f,0xe3808899849d6618a99d422291df2408ca12e0109aa9d6f545bc9c,0xf3f2ddb61a77f70d3c42951f28af84b986aaf315a09f0020ddd4ec,0x11ff0d34a87aeb9b81c234ee60c86b511ade52d32a6962432feeb66,0xaa750fd21a32c00f1d2dbba959acc2e83288e0fcc667888674640e,0x348abdeeb2cc7715f4d6325c502198b821b841ff627480f271ee6b,0x12be2e382960084df21921e5d83eff8269352ae4652869a7fa1394e,0x12d31869537d9a386e5b302365230f0534d5ba1037c38f2d8e399dc,0x9030749d8af7140ff2fe2bcdcdd06cadeb6603d0342dff8cb364ef,0x7450ec8fe7ac734cfc413b4b719e43990169b8fdb784eb69e18ce9,0x126b43c73656d5ad80b3fc555dded2127d50ad9b595f6d84c55c914,0xa52e699d57d5d]),
(295,[0x114e60dbeaaf4ec49645b503359824dd141ccbbb3ceaf3139ae8d85,0x854316e617d09de9065562c8e33c79060bae879a0838fd46c065b3,0x9a98be8c33da224b1b36a94a550fb614e7b9dbcb41d26d3eb7fd4f,0x368b075ac13dd885cb8302dd1e611a8462b62674ad4d017387d1fd,0x103c3e5814a81433348225a258e60796f93bc706c39ffd9111f1e1f,0x10b5b9d017d38d2cb422fde03450676603554a55611e557c1aa55ea,0xa361f6aff6c19d8a65df643ffb7c01fcf3a07634661bebf7d98ce0,0x119b78399d67e5734a190c033ac13b8fb3f15852feae1fda1e643f2,0x863e0f712e47b57fff3465b333fb5eaadd68c2753c65d0854da22b,0x2305511a2f220c021d4bf6cc92629db2de2204317414c66f6c81a2,0x962112518ead1b0863f57e23fe6e6433502f8678cc9a14b95115a4,0x5d81455efcf0323c325c20ec756c42b5a002d44a2790e9d70214ac,0x3ffc380c9f4dd747]),
(296,[0xb0b828cc57da51b9e16ff21cd795bac03a5db393329bd8d1ca1b4e,0x3cc59df801336d505c403a6922253cf0d0172f6da60b3269df5ce,0x1513c4d301c744c5e1d6679fd48593037a94532b07bb511eb8aa196,0xd87a0effa4ceb305b5f9efa6c219d8390df4e8c14a6cbb3092d1ce,0x120c3daf1ec34067d0805a8fe45bd29324b30bd96600fc0513ccf11,0x2930bfecd6232e8dd8b2629e1e684f973ce37cb60659129295554e,0x3dac0399b00f31771edd4adec7f76117848fcc78df99eb2a7150fa,0x15333ad60c6e52a927f5563c23ea71e9b57bc53976c1aa9d36a8162,0x5741b13058c2ae9ba48e6e9bc4e720a8cc260718a52328e23fce84,0x209cb96afd17ffdf0b0f686eca5855f782c35c49d04076bcdb90cc,0x1559c8163fc92f224f3a0d4025fef84523422ecf7f7d0a76e0739d2,0x67e30e69faa3d8412d609e60202db279ce607e94d45acdbcb160c6,0x5cd87e6cd6eb034ed3]),
(298,[0xd8a8bc9e9fdb61656671fc872361406219b9432ca6d802fb68e05f,0xfb814f76207fbeb2fa1fa801cdbf496dd61d55ffb155c529a70cc9,0xf42fe327e3a6115b77b0ec43d7f093b3688fb4f8a427389d917708,0x70dd777dab8bf36e4fea0611a65774b3778a021ff75393a52babb6,0x12e4c0159d4a6863553ade65bc72d1d814dce8f5a7e27b42ce8545b,0x231f90fc2f7560a4d615f2fe6682032ae0e2a3883e0eb6c78e861b,0x9bcd27b48b0a1895fd016df0fa8c642fce4131da896b495e2139e4,0x81918438fc445f49c6c344f9b3fd9c0bdc899e21cc7d0dbea9f460,0xa849008d9b246f903f0e9f8a3d477e7e80cfe93303d24edeb3aba1,0x2439ccc30bad5fd3dffe1e18c33aaa8c7cda61b4fb631be05de372,0x1cff276611f17b7488d40de0b32ac38208fde8a7b8281a052eb32b,0x11399b8d0dd03bce555eb7be28a71624c569b316815c9dd75e5ce25,0x20aebf7a9fe3f5ec345c6d9]),
(299,[0x1683a76faba8bc2741d37d408f47f1010d4530dc5385badaf1ecb0d,0x16335a78afbb63f80d5a7fd3adb70a079361f1fb258cc13ab7668f3,0xe83a6d11e5cb51048a7a8adc6cbd06a7ca901a8f1da55296d7e9df,0x1148da6303684effb1db230ee66b963c961d98e12af3e7824eecded,0x54d8abe11b7e27c6c0a02cd4bae56a7b35ba493163ecb77a4a51f8,0xe368a11c0d25236a3fda20c675bc3bc214c446d78cee1054968842,0x15f63c4d9c5bb0bb23f52772e8e5a598915b721657cab272498605,0xe0ffbc09269aaaebcef6041a386dee70a1a873b35041038a9544f3,0x9c538d45ed24a34f973252557f5f18814631b32943296c213b7a83,0x7b5566f4382e3301e45279bfcfde30a11e1c64d444142e8fc8f8d7,0xbf033f92c9b5a210c5f05ddb4b63d344a2daabeeae21dfb9d97e57,0x221e3028591d3bcdb64bad8c9807150b310327efa86e77a2d8acd2,0xbbd087f7e7692c66c41630a4]),
(300,[0xb43ffd9f69f0d505cb939d6a7e4646a95cf41eb2743a10f4a61123,0x840ef1d90009ad16fe0531324b54d4ff95646ad5eaff4ae8c90668,0x1f99795c83a77a5136e5506081ac1f728333bec7b3458dd79ad4d7,0x769488e216b0692c5b048e020cc0b0372bece321eeb6dbbff89adf,0xb6a8adf0624378d02c1059aad8058f3452ade355a30c6a68deaf9f,0x13a27658460f97c4d18bc9df073450310fb26633e29a2f4ab798a89,0x1535d7f5ba2efe6f8fb521fcf6a36faac4d2c18d2b4f9b83d2308a5,0x2a8d3fde1760d20558ed8c3fffb287e516c1bdee2bf82871aa6070,0x10267ee6e7de43d2a5710f44bc32ae11fdee37e10575e77b07da266,0x4af8b692a78397feea5cde543ec453190d096040544b264d86a98a,0xfa360623c5ccdc9c48a3f1e4bd13f209ef869da778faadb38b5697,0x15f9869baac9d6ad32c96e02ebfba3c1260a6643b569bed9b8a733d,0x2ba4169995cd577d818a0f9a289]),
(301,[0x107be30be1cfc95acfdfec7e7c134008379728aa02b7137acea4adf,0x1512353d1410df23de5c28945b760f127ab1288506ffeae2394a752,0xee29c01b12278b84c1dbf2fcbedc1068bde3f16774ef0dd3515356,0x4b845c532c699fcbef30999908f7df163ee66202cc7a22a6556f63,0xe909012a9c781a633b29d4d9bbdae63cb8b16a8e62905031e8820e,0x6a593270f0fa23c26c870fc37a843bb98f0d6d95c73edd00e72040,0xe7e7950501e48820da5d00f2b75ea4942026f735e85b09603f485,0xa90de3f39a71001a9876e25e50fd17683668c25ee67a6c64217fbc,0x161d2cf28988d295221a53d92f42bb844acf1eb190fa105c7c130a1,0xf19d399d28829298fa1bb48813310937d79870b6fc99b13facbac3,0xe4b4c9368c0863976078f064ba32fc5338efe52ca79d182281f770,0xfb6aa72498ffc3a024fcb0f7993790e5c53d56214bd7131254b867,0x4fb652713bdaa5f6d467c8b5d8e04]),
(302,[0xf1f5b5d80b81bf6e3dfa5aed5e035078ae082bbf132523729fe7a2,0xa6eaf43746db02b1c0f7e67492f92bbec7bc7fe7e04cea9b94f5e8,0xdc177f74ade26bb886f4a4edc310fcac4bbb933358c17b6d66d8f6,0x101b831e31b35201cf92ff7347e57cb0e03ea727bced25f5b494916,0xaccbe7679c152a6d45065a6878f680d21bd9c46cc599e23101441f,0x15d00f7f9871fde00a1f8fc901028f26a7d3a2b989852fb999ab0e1,0x12a518b20910c0bf5b4b5ebb09210a18af0ff411bfdbba3015ffbf3,0x1a9e0df85890014a468737efea4670be4716d16a933022980810b5,0x597b4a43aee5d3bd84dae46d3f710089dd90da317d908879a8d187,0x3b9db550d097d7acf36bb1cc5c5a64bd8926e4abe2a14836be4fd6,0x2cf600b538952e1ec488526b01d6345bbcc2c70408f059748556f7,0x8e9c2fb5598a5a131aecb74c585cc299b80b39ebeae2fc7111ac40,0x3aed32e748ebf5882edc74dd47fb3bbf]),
(304,[0x13a723a0434381f3865f5ba8b48a3d1373b09c9bcb90a88a9c18e7d,0xcd8cf6eab5857a90806daca1b36197a4b9713bd3e85b901313e684,0x1189c2c4b895e256c30de2d9b9ce8ce9b0fe7c63f0b295caff3dba7,0x15eb26f62a0a902ab45c4c4bd84f20e200b1ace0b4c7fabed179e70,0x16bbd895de59eb9e07c98d6cb0a649ccb10a6e36e4905ae3e463747,0xb1c2c1e8e4b37be2a26afed32325d1865233278b2990a8eebd1267,0x379aab759cb6b6e07a4a8267f2ee126c610f22ac89b69406fbdf4d,0xf1f5b5d2cf3757f399b435a68830389133230c56c1601090d5952f,0x5f73ff0164472dcb0f0d2d9a7ffe8a66bd539f8432c21a8b6d02e1,0xb42b66f0ae607cd2472e8345eb5d6fd493f0beeb3554839204d1ca,0x8e8c78a2e8c3697d4f355caa5f1a5ae163df0cee63cefb53a41c3c,0xc4f6484e82cdcfcb640335837646e12e35937e0ad70a140039888f,0x27378fecaab11ee7338d5ea35cc5dc59f0d9]),
(305,[0x5527c7819a77a9f883ff3a883b82531b51323671e4dc13e61fae1b,0x89bac2f4ac957743892d6eac398bb5e3160e01e328ed03501eca5a,0x143cab3481d973d13ebcb728d8695df4bc638e1a83459a90dd7f346,0x635579376c3ab7b98cb01de1e65643af7db3b862fb0a182737c1d,0x1172050b1a703de39b27501ab7ba73dde63ba6466db4cbd6ab95fc3,0x7c6ba13a9fd4e5d7ed6db3191b0ce100d02a50d9596413c910675a,0x2575de799de28c208d24a8ea1d576eaf5cb4fcab594471e3dfe55d,0x134520bbea20bf35a7fd4a75703b3944a38fb5db635157514e2fb72,0x71a24d8056e12e0b47ab1cd60d8e1adcbaf6b383fd0649c301891d,0xdfcb590610225784fb403a10a644fa4e35fe76d327328756fdf602,0x16e268eb32fc9b2f32379d9f754e20c5792e0aa77332b6c288f6f53,0x11ad4352d7801b577faf9a9b617fd7a212365cbc1487f0d37a3a7fa,0x20f000d688a3738dc03bd2a1814f0f751cff552])
]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem baseCyclePacked6_ok :
    baseCyclePacked6.all (fun p => checkBaseCycle p.1 (unpack532 p.2 p.1)) = true := rfl

set_option maxRecDepth 2000 in
private def baseCyclePacked7 : List (ℕ × List ℕ) := [
(307,[0xed3cee36499fc4b3812ce25d10abdc0646557064320db70cac4683,0x154f3ac17bf865cdbb322b58886516f2b8d7b4473f2c028db289db1,0x222df30d424c0cfa18c6ec6c136bb12a075673fca0ca74282ea96e,0x15d17bf764df2572eda0fd7d393cf653e37aeb7cac4583fec6513cc,0xa259b04ff888f73fabe071e3da61d6dd1cb23aff810a37831ce917,0x11767ca67ad9bcd91c97ac3fcaa116d740d2c18e51faf6e13618853,0x133049a2ded48cc853a2d3ca28d43bd5f539362d6ab34030f6c5b6a,0x66eafac0de78e369ff7b40f33d5f77dc0bb6bd19e11650a319b1ee,0x514d665dc6209aba4f678484b1183bc0699775753f043bbc690694,0x60a867a3fb532e40fcff2018c902c207eaeb958c162c6ce98baa69,0x27df0a80f99489c34131c9302d31de0133ff42f9edd4d8efcb8d9,0x88f6034b973eb4458b957eb79a37f8f0fc85524b276896f9d70bc3,0x1cf5e94adb6b05821e6cb08488bf6a38af7f79246eb]),
(308,[0xc63e05a71dd5e5c4e3421c8dcd2f96c3c4c32144e5e0eb0ec21886,0xb32103a0b418f53fe50a3d7390405d950352f54823733bc414ba14,0x1487040f92a78cfadb9e0a98bd812bb13bccbee3bc5449a7e209da4,0x6924e8114273a121e959e8026cce7ef8bba57207ca4fa86be8ad5d,0xa9539e1cf4be939ad9b93d2d2b35be6145f3a991ee0fd59ec67c7e,0x13177ba7bedd2102c89edf23a43e2e6551fc9eefd4b62974027f2e8,0x121bbd4ea20218aa8a159e3e895039ef4a4183b23b4c2ed2d3de64,0x54c7fadfd57b5eaf0aebd29f7798b6bafd5af4ce561db4639f0a1a,0x3abe869e3dc9aafceec6433701f54f97ef6412ecb50a92db6e447,0x16f919878f775e98e5d227130703a4481a62dd439db3c048eebcaa,0x95d6dd321c0e3df45bee5774cd14e3df5082baa775728ddff2d542,0x14c230406b43a54e82969aa236684e6ca8b9ed06cc645ad95159221,0x4165645a3e22546e73f6793e5054676c1a1692119a92e]),
(309,[0xdffc3ae48f7356892d3025b033bcdad85fcc38f58bbaeb898be34e,0x160ccd724fa4c6e4803eb79fb246116bd931459c1fbe24ed0c7b31f,0x8841bbb59cbfeabd856bd64df93e043ab9360018fb4d1ef180760,0x1e33924ddf74f0e39ad18e15c24f01db43f8c75fe39043a8a89579,0x609c331590bd8298c647d5b3e8d4d894fcee0c9db7b4d708360b38,0x924a6daeaa5662e4ccbc64ea1233861a531a89eac80669d2483bd9,0x4ea3a7546e2cf1d1aeaa204bec86e90c2a63eebbd1c3e9bb0ee6ef,0x93cde74c71fb08411e41333eb35ee01e64b4dae554bd1d041ad9ab,0x10f3114f68662e4ee4158a4c920ba5f9982b20b37d57cdb24f3e6f,0xef21453daf17bc5bc7bf6beb4eb5e4e375e16c7397fd5c03c0bdeb,0x14dd45b421ce68a3e9aba1ad5d27fccf08f56aa20ca0194587b4e26,0x1731266fe608de5337268272d66aa7388ba792cde098e05b989e2c4,0x1e12045f00739d0a1be048389fc06f25bcec80059a6c8361]),
(310,[0xd39319e152e3b60be96af796470b863cb0e880130e88546149d064,0x659e65ef70df37477d7d0d21ff4d209b40324745948bf1f0d4031,0x15fcb79304fd844b9bae002c1721d46e57c256ed53aa2f716ff5404,0xc180a5706ab962cf8132a459b377c160bbf62910a717a988915cbd,0x988a2981f07693be27d2c0057a790a3b7c533e2d2c2491f511104d,0x92b0222fed210f151406e926e71afb8fd57700e0d87108a2dc0437,0xe98675019a4d1a46b5a2c09f067909a4c8ceb707e6f33accaae058,0x9ed42d280f8dcffe7e55530189ea12a483d990e872147d9b8c0dd7,0x7ed467e0a57f79ccfc427a98da276dc6be11e7ed289b96543eb376,0xce87b31d9f461bea01b9e65935b8b117a1e0b8943465a975c5847f,0x10f2e8487cda1b89c8d4288602d24159b39c633476a929531078c2,0xe33c63688328106ec36818e9ee07f097d68d82ece5565b349fb75b,0x1f74a379dd22e69e570f59d5b3e7f7ca6b604be6faa67896b5]),
(311,[0x15123490a3e49f19ae877c54fb69245cf15ed745a07e1509225bab5,0x136d4f1d1a9dbff2b5c8eadce01eb8c548278e16513aa81e21b2325,0x125dceb08689ddd1f55cda26d20d9bed3a55d68e9bd0d873a123e1b,0xf2fb75c8a3057f2581b24e6131ad51f0b57c55af4026165fdbe6fe,0x27d6fd6dbb341b15e1d2cfe1689e524da6199c2d521a6456901290,0x61f8cdeecc5e2b0d3d7dc188888068309a8eeead7f9e772b56fdc4,0xda2ec8daf905ca9212a28fdd0887f2b07cf4235d08db9d598b4bc,0x124cb33f669cb7976bd35cc732d45043bd2f4c6effadee0294a80a,0xdd3640857a478b1cc15e414edd32e917430f5d4d17f1e6ef2431b2,0x8b0fcc8ef96d784bcfb28ebc3dd025e7ea2e178f88f013e9d73106,0x8772b27e32a31933147e62bf2bb7dafb2ca44a3b3c8c807fef02ae,0xbc8778b5ee37ed210013ccc345c59da87e8dd8a5cc46d498373ea9,0x3e631b4c50b55b85cea3c85bd2136b23c904846b28acd8594701]),
(312,[0x13923c15afaf28ea0f95314c97598e75ea8e3ce1e206609307e6b58,0xf0c1488b2e4e0dafe37360c2da01d90e7d85a1ec8911ba84adafd6,0x14415b0938516ff6f1f3bd4e9ebeeb79309303793ea13ac7317d339,0xe6c571ea6a9209b9f96c9dbbdd09080176cf9acd4817823715b64d,0x14093a7e7bed5f09358f42b3c8a6088985b0de3e16edb33019d8575,0xff07aad32ec64d499e6671c639a876df99101869df24be171bd60b,0x9006c07c659f0e6b9a93f81adef9f80d736ec1bd97d3d8023bcaea,0x6cd0c07ba4ab3139acfbba3923ef3da4b782995094ebba2e3fdeca,0xbb5300efff50ef63677909fd61983277125aa8a90b24ba891b7de3,0x743dcad9ba3f6e415fd313afe406b9e3e9b2206b144e041119c2be,0x27de8c67d0a3873f26b5180a7010adc572330effa7ae3ffcee1ae8,0x125ac047c1d88b0f658539d6eddebc74cd30b7b714d0b898f126ddb,0x402e5888d61407e2116c6feebeba4c56ddcea9f84997758844d122]),
(313,[0x7a20f2708b6216b17336e747ef0749d9537a5c52cefdad0defc5e0,0xfced0f97dd87de470150142c01a6a1d3eed57adef143f9d7e0ecf,0x114fee41ded7fd5add6913a4e901239ae0033fab2dbba870a08de47,0x614b80da271301eefd881f9458181b2f1a645dedc9c32fd8a5f8f,0x1763876e6819f95b4f2a0ce7655df48e87fd18882375d8bfb850474,0x2857a1691bf025db9234832dae9a786148f8aa7b5068d90d302af,0xa0f9334ab987e6b570382126635770e0daea8b441f40ea19b4d37a,0xab86a02dedf83cd930c1aeea3e581b44c6b40b79fe2d7b2ec8b57f,0x15171af6e9d00314204934131894ca32df4c80551661462af6bb592,0xf446bf14a72c327581b8843b079d0f189ce4729fd57235c71ffa62,0x11b1f4eed742e424d9195a595660ea5714f7333c4f04dd1673a9ac6,0xb0b834e2fcf7c485f76ee107951f598877f2f38d9dbe30ddfc13b3,0x13ba6d892d09b739358bb155834578facb876b8e96d8ad95318609a,0xb4]),
(314,[0x1164d995b6129c174799315af71cfe989eec3252dc72e85ec88a221,0x11d2661dba83f624c3a2ad1d720b2bbe345798add187eeef9ccbbca,0x108f2933d2fc6dcdfbb4600375316deb1e6ffb07fe5a4498be253f4,0x403cf0f9a34496707b9249cd25618a0a5bc734f2316aaa349fbbc9,0x3b2662f04b56e1b44be8a9d9e037888504257664e3c456f2fffa3,0xc15b4e8e57e7e95368d175c7aba23456edef917d18c952db937de,0xc51dc54ead456aa8a445368835aaf77ac84342cfc38fa06a27b023,0xea76ec425fd80f9b23c127ba47c4b399a8fa2bbbde496f4e1b92c9,0x13177f04872d398cffec281e2ffe73d4c26f6a7ccdff5350c1861ee,0xae4f6690120413cb55c5a30216ee56b1c247283b78ac65c956b150,0x60e4fbb09f793ff0efcaf3f89ca0eda8aeb1cf06cb8e15f3fc3795,0x8d49888e490e52748a88d0f22cedf6340a56c0e51306262a06f364,0x65b68d62cca747878913bbcd805a69181e3275f0c57ac788d1d270,0xde81]),
(315,[0x12226c116ba1378cbf85173b8a4baeb5655ac29420a4ac59a4fc26c,0xb44009aac60092360a21229829f65d02fbd527e79f648df6bf8600,0x14c84ae5821af34d6233a48f8988c3bbf851e229bc4bf4875718e18,0xd4f3a2d3524f0145f3d7e4d2f3a3a399b3a64106b2e854ae285bcd,0xa7e9231b4e2a1a579acccfbd27180924aa254158f652d1e12b1ad4,0x177825e920795f97d33780d5e2015490f709affb22209166fae6fb6,0x112390dbc3178cf16fc6a6b4cd5f55769733c86697d0246416ba249,0x95d6dd320e0ac63db941066cada45c82c249b62af5133bb78a0622,0x4883aadb953957d57779568cede832d9812a9f9c1bc826acc2f8d5,0x511ac3f1f38acb39d427fad2ff1c56faaaf150183e8efbe828c949,0x10b2add73f5ca9fe69a46bb9b78f36cc904a549ec45e6b499cd9afd,0x11b04fc3882b6c842011c9472933f0b947c7bddc4e9f41ffe034314,0xb7c8af200231cc5be28899c66bf0d81198448ec98fb6fde507b833,0x23fed8d]),
(317,[0x160fff2158a146ec60ce8392567cdaefc033e7ecfe00cabf66ef7e6,0x154d974a77dfd088b3c0959666e827b6d01325f36595df59c12a94c,0x148e7722991182ff673e7e2eecc5a7497d4925b4086bcc24ba70fde,0x1393dd7fd791dff2ec89f249657fe02714fbf518d056635f2cb9150,0xf93039a019df7f856d3d1a1bc6563dde63a473b02561f6dd7c3c81,0xbb40e44f703b3ae1d69f2b8d7de205e555c7259888c8add138ad92,0x10dab5aee5e80b6c1960607ebfbfbc972c4fdd64d5112b3febd6e66,0x13f5f2f051cf1c05246f523a350d739a049976ccfcd4c9fbe25b955,0x1cf8febb5bf57f5adb9e94f742b897526effd6ed29a6f71f8ba3b5,0x452f31dc6b6a70dbf91a4839ae93bee4d41cee80d49336c16b3535,0x12deeda3882f51ffc32333c6602a8b5ff63a0a8f20acf7e69a95c5f,0x113e48d565e82f36a4052f493c77b4bee6acc4ebcb836e57917ac82,0x2e2a6df9125b77c15fc8c94be067c93c847d8750417a28424272c1,0x310b2178c86]),
(318,[0x107a566f4b66f913fbc2d39a0adf10afaf080f970ba33ef76ce3075,0x15bfb0d6c49a9049589f1e5d1b0a3fe84824d4762ee3e8595cb69df,0xa0d1afa093be5a481cdd6738208147f2f74ddd1836ebd482df33f5,0x49f00d0ef758baea0707b5bc071cbfe8e98a819a1f1a1f240e5797,0x39f9ab3439102d720591a75f8e56f80a7ecfed47801165dfd3f2fb,0x306b39954da5c4cac7486342b649086efa22986974ab64f65df8e9,0x76b9e7fcd1783c837d8f80f95675472c9cb5437daec3ebd8668759,0xef74d2e52a1d22745d8f399d8fa9d76baaeb8b5ee6f3730389135f,0x1d197612878bd3538bc8cb195127aed2b369a96c04d50feb985696,0x256e253121a010ce603ba21d70b8384ddc7facd32133697c7e1609,0x17f1e6d13efd0509aa619abc6e4ec1ca90d9bcbe1c6a5f82e559d55,0x54b7ffbb8356d5acad400ee4d85c2f0b1e5a7959f1f1a4e136bd10,0x13f44071bfd1ad32f27f7cf36c75ae6e1dc86668270d5fcb98b27e7,0x2fc3bc823aa52c]),
(319,[0xf6e0667d1c8d3f405258010c6129b1964c0ca83c1a499c85c49b07,0xdd366eadba437101cd405d4d23ddc0c918d33638bab63b3af7de54,0xebab7b3745569fc7846aa4acfef8cc7345a4a02a785e009cd4253d,0x1513c36d4ffb8f2489f814a04226b5e135cff45b1fffa479dddce72,0x10052c52fb9a01d5b5cf3e16cd1dfefc6941fee17f206529a83f5a2,0x1707647ce1ba39d9c0c695027478821cdea19bfe6519c4836640e99,0x6924d85e71608f01997dd1d9bafe48fb3341ce6b5a2caabcab1ed8,0xdc17574878f5bf8a7e53cc13c3935e91e2eba6e252580e301b11dd,0x7ef2af0f78f45dbb720e38c084b3b0cbaa2ae1277371a408efa88f,0x27fc42e3f1341c788f0ee23c4f4070977d9954fdc0f4b219eac68f,0x89ac44961ad6366b3ad1fa937d69adfae31e79c981d35714c8ed37,0x89e326fdc9047f7975ba897dacd4cfc05bef858c1b01ea9da488a,0x10dde6a77e962c0f7be03a7d9c4eb10c37ead7e1a84de26c4d7f1da,0x19d2789c3e4437ee]),
(320,[0x108c202c186071ca267b795e5c2a7cfd3554a455e4257bdb01504e3,0x135866dc8974fe768ec7ffaac07343023d9743ac0d28be3c503e6ea,0x14767f2c69c1bd48f30c7846728d2bcb3b197d2bac466fcdb3db68d,0x10edfc86bd5976b751c9b600eb872aded402a6561189e4d0990a4d2,0xd6113451ed4aa24b9d8b07441956f242f1ec89b71562db132cf144,0xa0e4bc08330686778773af68b67d28b7f9111293000c03a883b707,0xa81f28adc7ee6cc43f7c7ee54c10d013563f36554136edc43ae8cc,0x294a3a04fb6f45450b9df888cecfe699b0b835562f52cd52e91171,0x11973891acad13a6a2dda1b7d0a481cb9e201ce54e8a6064f424c5e,0x4b354a8eb77690d3c7a904552817246b42aafee413b5e725688fdf,0x3194cbb5ac02e9b9fb41c5eb9f0d56bcc0dbb8b66ec7f83ebf0d5e,0x15007dfc1eac7f51e74f80dd5c801e58f4ce6859be83f6cacf16e20,0xb21ae116d5e8957423081534f5fb877441b7c0e86dbae22ee87857,0x4562126555e78950a6]),
(322,[0xae39c4519bb8352a137305309b6170192403fb197667f43c72635a,0x16f92cd229a1c51873d5148ccc9895bc58214e65f169b04fbf7cc5,0x11fd6944d385c13f382744a9bdc16f8851eaeac7819be669ce80a3e,0xa81f6d10ee0f128cc979f743001c3dfded72779aad1b4733bc892a,0x12deefbd518919f8baa816896979417e157f1c08d2616daa6a0355e,0x14b6b8c81bbe49185589f9042f93dc95c4bfc0cfce082b94f79c60b,0xce76ca5f01fed9b198c13b6caf85bfce6fb9895ef2193df8830e5e,0xd48df78971c9d62ea3b9389c430d25aac4cd423b91643936a7a011,0x133f50cdd94f5f7918738b0ad3857167df17f1a96357e2ae14be041,0x104beda72f7ebda1b61b561267d016bbcce74f2d017bc6aee2d57a5,0x1487039ed6bf4ac7c641e3bd6c18e2ed9e5b6094368c7ed4caa4ba8,0xef74e7265b9f51b1451e6f7786f90ffb40fda960e6fd9e4907da55,0x107d878b0780709b8790e657ab593441e4d4e28db4a74a98b82936a,0x205ab37afa2dc0851796403]),
(324,[0x153da96d9f67df1a69b4252d8ec799237247d63bb6b5204371e14be,0x6d035b34b056bbe872f677f415e2d61ab02ce55475003ce8693f1f,0xd115de2fc77e30d266e4249e6bdd7cfaca636872850663981281cb,0x68590658461839421343b744b77b2df7124808d4bf95f1b72e3f7c,0x31d7777aa4c4a26231672fbf4552226315c07c84698205f3180f03,0x21d130a477a254086bc3f9bc2de41bfef67968e83f21a22f427e83,0xcc1edfd7e5e6831db35f091aa341f225be0934900bcfaa010c37c1,0x7dbe6d004381a464742114424a00652d85a5b9bb0accd24c360a9b,0xd224ede726791c191546593760206b9d3a619fa8c82fbcaad5d595,0x1827494dff82507579dd0d1f0c3e8b09cb8c8dc02e2030a48a941f,0x7ac82a6387ed7d798855281e0d994eb7b1a9420cdb2cddc22aee0,0xae12944eb3236ee65d91ad8413a5e83e3dc74e14feff79258e996,0x5d6cbb1c582ebf3586c1d0f0479dc3199f553e13a3d6c551e3a48f,0x6970ba3fd02938e67cfe589f4db]),
(326,[0x14415d665713b9b9f966c1cd5eea2407338e86b179a6eab0eb7784c,0x148b44b4a963877422acbd4fae5e71bb73d8ff1cbb649bc0bf6ca38,0xdd367995510f47ac963fba558c2a6374224154482c275ebb653c61,0x48bb9fb95f261709ba608e22af43af361541755b419288f266e289,0x3574deb6289fa699d241ce6e576e1cc9743daeb9b8fd4c94220a85,0x633ccd8bbaf5b53b0a78521afb9943cd3b51413efd0fe67a3cdba9,0x1c0986b0688f4bd130cbbd7fd24dd9cbc0683cdb199bd48a55fe3a,0xfdd381fef9458bb006443f125da53ed0f46ad0aca1249aca5d67a2,0x2cb03eeb85a0acd6d8d48087992d4519e5d3488a0a04835fa1fcc7,0x12f4f828a8e795ac95e077284ee0a73f8e2d8bea1797a3a4975c9b3,0x4b14e88505eb10da529b7fb117bea69fd9a4a19e67ea567eb54475,0xc1ac8cdb394f848e525ddfa39653196b0da233e4f1000380175a1a,0x85433cdacb3c34872d8d5c974e408a66ba0756113833c4e97df724,0x1a8acb747c86e2e2242052193a0e6523]),
(327,[0x11d881001d5ee2cd0cab37057b603b733c1778041cb0fb7444fc2ed,0x102bbd3d24cb83d100040753cb2935265d2598ed5abf18ea21d585c,0x1877367482e5c9c92a6ac67c5def384488992770c41fb490f6c0697,0xba31a25dabc58f9665c3a8690496053152e4ae0d70b6d29e1ced50,0xc8ff0a69db5021591b3ec22ef1ccfd1de891be9bd15f82d1d82a27,0x163359dc2697b93303d86fe79c48f53a6c0c60114e1631f93f2a192,0x13689e78e0830f66b9d304fe55500014be674efc49b64a3ee24a38b,0x4db064c555ab83701c6144f9d9d5d9954cb37cc1f3975541e3eb4,0x86634255bb7220d823ca259a66176bf98e9bd080c98a316e4cf5f0,0x121bb2128b6f6f296a311f6cbaa2c8a0c1ac3ebbb0a36e38e636e5,0x31c7d030059f3b29d6cf9642e6d3670192e148645ffd5359d57b76,0xbdbbd1f0f5f29016df17abdbc5b9684659fea696199b8e8d5cb31b,0x9889f5c298714ab0df52479e2023d905bf5a0d90faa98a42bde41f,0x3c17240150582da23ca20b0005771982a7]),
(329,[0xb6d4bd6de69b345d9fb1d3db7f04cc3260a36aa31e588480804169,0xec8ed73af4dc9959cbf261e07c8b4472e8ee3eeb4adece8d6051e,0xd4f36333614975234b754bb5da5c78d8c985eb292c6b39b04b178,0x860ef8332602535086f70d08b535343789edf702778b130fc07715,0x9b1f39d315f9171a0f152a3a5a9d40e8712a105efec3a41c114f2,0x8e70da68a6bb06669ae25d93b4ccbb545a226aecd19a3d3e47ae59,0x1147a8464d8ff86838485f6d6ce1145d16cba130bbfdbae22a2b436,0x163840c6dbab404f79f9ec85e7f86eb87cacffcece89e2d4ba87e08,0xf7e3fb31e4b3e6cd42a684c3ec35784aa3de8d43645ccfad45e497,0xed24005d9bc76d60fd12e6d99a82fd812b5531bf2c53710eba132f,0x925c5e06d6c31708114b52194d8e7900ef22a4f2d48d3544aea3b4,0x14a374689ba2dd9cf3d61ae066160297636b417fc28567ad0b335d8,0xb337b8628e79f3365f0768b4e0939ca720b726bc51636234f9d6c7,0x1e0c6f70a8b98646044ec6247c853d503f83e15]),
(330,[0x130ea4d4ad576d2eb1c3d2b4578389df005e44c689ff5a178162c21,0x1850aa1b8f303f92cba71fefb6bf4061452e13fd70dac75443b7b51,0x15c2e3c898296ad07420f3f2282213d545478c98a8f146f127aee87,0xe92e3bdd7be3f2fc86e96b5e20f13b2c9b2a13d0ecb4a7367b4840,0x35bf1f64be85f7f0647f01ea04e187a9bd9ff829e4bbccf42862e8,0x154f3784fae4583c10c547a252503cf57d2a386c39f7800ad9f9669,0x89ed721caee2e0a67ed2132efdb27ed6efeeca8834dbd55cce3a37,0x27e01767ee3a08d2ea7fa7424d14ae215d91e7b5280973b1c180a,0xf0da365e10cff6c35a0e0bcfd4c107f5557256ce6f2a103d24557b,0x3da111a9387cd0d12ec5b13a551a94429a8dbffb8d6d11a372d8ee,0x66eb1ea16498b161797b90e8e0bf4f8247545eaf891a8eceab97d1,0x4cb8e49b6ed089e657b794cc0c2e1dce8a443342ae5014aaaeb5d0,0xb0cec5073e493f65a9c5a9e56ba9a3fc144231cf5428fe185b0ee2,0x12fbc785e6ba9c8849ee08d9521634fc2afd549ae]),
(331,[0x1456590fe018899e43783db858eef58b6f0f7aaf64012a78903ad8c,0x9b1f1ffa54645f8e536bff523b051c6b270844adde69788bde1b84,0x10dc477ca832661d2301a95872152ef7e313a2b1118267d5ef627d9,0x14b362a50244f6ee122c4197dcd8797897c82a4deec4842cccde736,0x510c5c3c4ecfd5e1921bea5f8073fa33293f35bcffd1d352d88096,0xd745b4b3d671dc8084308991bee3c4a5a439c58f6aea80430a426e,0x10689cec1a0a36e507a1ea05408afe0fa87e4579a96f4a3eba979f6,0x17b814d2e91e3178df3e4483fbd6f4ddea02a332588c710f3c04468,0x43a6edbfb156dd3825134097446f8f2616ac0031819d89d728b626,0x3db86139a945aa478b33a58cce22168957cf0adeee2a38d189e9dd,0xa307bc364c1c7b426d61148aaf0a82de461e5d3bbf1756978e9efa,0x4a12d5f6e8c0d4fc2dde6a201f3d17ecb2e996749991889b59ba99,0x101d20f5243dc2f73d2b75dfe77520af9466c72c74e27f49bebe9eb,0x1216c386157e900bc8386433cc96885ef0cd6a62550]),
(332,[0x18d93a0e856c7c24b38a455f90df56cfa3fdc9b2339e3b087a8fb8d,0x5bd6e7e48144ee9087ddb4a3f83e42bdbbcc6db419c1c70e7c9258,0x14aa9406bf54fd4a995167316c8983392ace30764ad18d317312b4,0x18ec80e3a8f545dd4b43a091abd0e78256721348cb353fd8535651b,0xcfe14ab5b0ad91e40fb8666c538489e78058960ddfe41f556687ae,0xe4cdf0661bcc63fef8ad05c4870c823f70d5dfc9b182fccaa681e8,0xfdea07ccdb55c84402f4ae1bd6e924ef636e293a837d9ec3db190f,0x8ee693e8dc4cde4f36a56d8e0c850ca28ca6564ec94bcb0020e81e,0x1673db17ecf7c7ad07e6508435a644c782671fc5cf8620f06f74a32,0x9875eb12117e8c5b2128737f35fd8d608513f6a9ba711b1b58c918,0xc9b5f019523971f52c3d68c5e927eacdefa6604c6849efe0baaa8a,0x108c1c2ef523749bd8d6f47c9ce61ae457eca79e73acc8e0b9d0ed6,0x774c8ee3fdfb30858fa69d34df8e0a63b1d194fdd54dc3910f5be,0x25557c39b2d170632d41fc1240f58ada24529f0e13507]),
(333,[0x13ca7faffa06381f9117c077b9ae2f3c3c67eeef4058700d1045858,0x11f6567ff1945326bdd7f0ea47f80e697d7252a9792ded397dbd75a,0xb0a28af9cae25e4ba46d175b190d4e4dcb061ecc8418054d1ad64b,0x119d099a656471f766173f333cd088ccba82eb5be70e49f3ea34fde,0x32b661f24f507ec5016c93f4a2c619bc4c3a549a158330d3a02b60,0xbb40d5bb86d161f23caa9d0e7cac7a6d47df476ea522348606dbe2,0x88b923c6344af957e44037147e7024ee06860092c5a5022f0f09e6,0xc870b29f1f4556929a5844da94f236baae9a747e9ce633dfed7643,0x3f08a27d9499b8363b3744eb4cb599b9af3a70d70bbf5d710a552f,0xf56459b31710188baf38095dd385a170b4f70c6df04b24d6ee0df9,0xbd0bd65e9b865c9f2d564920e2b518e8837e53de275cadd4791b79,0xe264fd10477f13c502ec1bac874d9998f737264eef6542ab9a71d9,0x182d7349c74e430faca03d73f29b2a04513f7ebbf90d9068625d209,0x1feace735104da87a174968df2419e159efe4fa59f1f37fd]),
(334,[0x14902d92b916417bc6f62b264308757d759b9d96076a4df19631bb6,0x16bbdb3ea332657eeda8892bf63794a5fa895dc11dae8eb0c2d6465,0xc8e76973f037c41f2a090b65c4703d233658294c552149cc8d23c8,0x924a80bea44b14e3cd24eaed8cf05e67f6d758aaa9f4898fbda736,0xad1aeca33edc86605adacbf4053a52c8dc017f94507931a0d37a88,0x15d17c9dc2c68725825ebb60867902b60b6e404ebf9f7f43eb298c6,0x560cff44aad84505877b142abe7dc37783805ed41757feeeb66df0,0xa69681df23c786dcc9382517d9625866d06090b5d350cc4ca32e5e,0x256e22a1792d2bb546fbe1a1aea2e480b550336fd88c37d9e5a452,0xc79c1cb5252a901cbb786c28e7e4c7b68c9b1403df4ec283b8722a,0x3a0e9e4b850a6a6fc3acb52c2e241f13f714ad914fc6fdfd05b220,0x355690c5dc3d36e16db8bef5b15a146fc067e64907f1bc1e73c1d9,0x319fa6f36399f56bf756ee3ecc2ecc4b7a7cfe0b2cef44aecaaa18,0x12be8ab1f2b4d547c16964e8c37815f81148d369ae7846a2ff]),
(335,[0x18dcb697f9989cc5eeecb796a492f241b121e527bdbfbe7a896b10e,0xb96ea91c036a8e71e503fde6f0759cafce63e5714a7a70fdf85c78,0xd1871a287aaeda912e4b1cc5aac8256dc3637bf8e2b1b4b3108fef,0x13df56b77b0204f0635226ee2dcbe248c7d1f5970e43e8dda1ab224,0x989f9ce2fe8e407926570a852b3574ae742a1a24e09994a1f6cc65,0x8f2ab8c7817f6ad056748ae4ad794d76064a52afbd7253eb56cf17,0x12846f517a8c1e8abb69e78f673f1e515e2c06b5011678c763b4df,0x14c2314cce2e50c2a188434a5b30cd981295cc52a9fbaf1f5e8c675,0x450e949d9a1cf498e5ec335492432cf6b8bb878ab504160ccf94f1,0x5a962e68559d5a3a6a6a0958a9778263603f0d6fe5fca982e86dc3,0x43be4b3baa5918d51b14433fa9f18e0e6c107a286fc31bbc4d1d09,0xf09e5d87a5b1bcdef4b8fc9e92474169f271bc36d66c12676542d,0x9c12f371274883215cf56fa3eb8eaf0508cb325bece0a95faec8d5,0x117b3bc9b949b8819e48fe5f1697588c58490f2daeac6caca257]),
(336,[0x15fcb90b60beefff3a2bcae6faa4dc28e818255a95b32150fcd97a1,0x17b9cb0e14da48c32fe0a00a77c026bcfc1f12d07ee7ce82a3b47e6,0x2e706a1702665d62958a7ff8205e02c0ed4b485f5549dfdbcc976b,0x2a5a452484e4ebe690c98924a5b245e43308854237f25b75013196,0x18690c2b5d57e51a51a751453604a77e6bfc8677f7b133826a3dfca,0x119b7abc6063eb3b65ae2d07dc5aebf1a0c61043f28b9ac951c21fa,0x817e626884d41b7f114756854709fcb2031fa6d188adefdd39d65b,0x5d27516311a36ac2d12fdd85d5a9229bec4a17430c7440083dcfa9,0xd4a0412c9b93cc7feaac61417b7ab4cb35dec273f58842ce31f8b,0x84f8e1a9a314152566a4294f9a0afc11287ba04e1e5719bbb2fb16,0x42a5f62a42b7cad76eaf156e4c55608e087af78d3abf4d81ca34fb,0x8761e282358828c6a9ba217dd69238ca22c084bc65cc596ed79daa,0x7e3505efa612d18f381f5fe817b2d599b1713bbb7400eb482db839,0x8663556e77d2ef202aab13267afe2b57a924539e6943720e88e159]),
(337,[0xb19d58fa5b14add6f45d8fc7ad9f5e62da3a82c6f98770f17efc2d,0x121be6612fc727c6c811fffa1088be1d0031efce8684caf0014d7e,0x16e7872ee7c1fcb3708f24093b61145b15cc94446ab6a0d8c9aaafe,0x1464b7b62dbf1f35b48bf794601b6edbc289573ebc7c3a85edea991,0x6e25aee8169be29168e1bd4d6c226b978fe78db1aeb46a6d2a8807,0x964d5e4c3476524ca3bfa89663de4b988904a9397142853f6585c2,0xeccb8406e022716c41b9b16c3db6998caee28492fb4e98e345a94d,0x1683a8e7bf4c7e8d0436b149b0d3c02bbf185a2b4b7718d34460cf5,0x15876dda824fc91075ed1a984ce4ad940ed7d7f86ec3a9e4401d123,0x3ef9f348c5e6b79f4251cdcdd84628fae02fa4b17d3751198dd33c,0x9b20b608063624f4f595250aa3d28a7cc4faa5be5396f63f04a60,0x868d097e3939394dd8ba9c598b027cd2478956a5f13519b02c1605,0x10642554b4cad0927470db7695841f36d29fe939a6be11e5e9cda26,0x926fb0a60dd969b3f8d2116616d728346ea454541304140154df7f,0x117]),
(338,[0xba723c420bfa793807376fb103d45812e851c849d6774b55e6eca6,0x735cf9fb66f17af8a116b141712abaef5a4ca918074cc9c432ca76,0x4768f108721f83df3eff2d02d82418e87eadf423a4f17d9207d131,0x8d67df7764b84d3e47e5075637076ef421228f103b4dec54219846,0xc3c1cc5c617a4d63083134e211cdc23c2436544bdc1ec4f7873273,0x10670c040daa4c238c5f90dc0928cfb249cd492b5bc707a67545bf7,0x5aafd9225482da674f9d5ecf3a7fc569563fcdab851fde23cfd33c,0x11ce94a2f6e2b736bc36b8c67eaad610843dd1d82afabf80e11ad92,0x172df4ae44a560d6100fdb621c6c8246a0dbdd89507ebcfb7303cec,0x163841872c1d2dc92123534e181de267389041faf149491aa421129,0xf6e0595a6b966c90a05692ae9bc322327ce5b097536c14100f9923,0x1174ec61bb7d3519fedf4a8b1d1dd3fa86ae49ade5823e342f52794,0x122268a7034ce8de271dc440faf03354df5f668d9a5091c0b5ce709,0x9518d043cab3c0bf58bf2cb5d5b73e75f7b5a76fe02b862a7715f4,0x18502]),
(339,[0x18adffc80d19b0cbed33618055176316e20f6c22c24cedaa83b68ff,0x634dc35e61ab720ba3ced78933d65a1c66b0b18f7cc69588671c06,0x13c902c10907c67a67ca5ae2e878278c2da762e52784fdbcc4c4d5e,0xe85207904adae373c6eba3b96da9cd4ccfb00c7b49c2ee1e32d2e7,0x7cacc87865bb2bd118633cecb56f43125ac34677e4dff1aaad8e21,0x54fdda9ddc0542cffd8fa4f9d54fa8afdeee439894bb827a5ae2fd,0x15270a435108025fd3e52e98b0c398249bae7b5c0b8eab7927bb8d3,0x4768e8eca07e5271b042fd4b320ba462dc8d05bdfaa256d626f501,0x8fe192f7f09035574228ccf96d4d9abd807460b64d8efc407df67a,0x6f4930abaf5eaaa18ee3a089299743ac089257ead87c58704ec069,0x178fe3376a8aaf1cc6f8595789622ce427d945212033aeb50e23604,0x9ea5b4732db56f30d2c2e363f61d525b8679d59ee41321f8e789c8,0x4ad79d749f6bfe400750ed8396dc933d896b09b6338842f11f511d,0x1200c51d1e3c2868953a76dc0ef418a7d836518c5d8689d2b768b8f,0x4166343]),
(340,[0x148e78bf786615787d000278a205d2fe070b019baace81c2471dd9d,0x15e7cea3b2ee64b6d06d783cfcf62666f54c0b5af387f0ed8325bb4,0xc2f8fef4a9b4369ea8a3f9825d101d1c1729f2b4e8354cef98b673,0x8271c44cb0bdde7c8b72ab9baa5e3cf64137ae641baa1d039ee024,0x13a3f4cd973cdd8ce00942b59253f2485a8d292c7e172d0a1722bf8,0xb2f724fafab8373065200eec069b9b1349ce6fb781deaceabcd410,0x15aaec906e2be9954977f179ad8a5a78b12867dc170d656fbf56bd9,0xa13d07e8066b73bcf9a24bdcbb230100299beae1a47832b22948ae,0x4eb211946e49c5535433671a4290a3741b8d7cd9bc48077dbe81ff,0xa5b655e545ed722d4c4a855173ac1b962a0696ef98c78eb0bcb8b3,0x1291d5a70d0ca3cda69b785056e61a20f79cb442e3c3d4b778012c3,0x21594efadd707bbf9241b6f8977370277f0373c1191f6ea276a262,0x6cf14be4f2208a6eaab5920b48cb979449ceda968aedf985da25be,0x14a06bff7938c1892d15714158f82db2044ce20f2a2fb9e588d6d6,0x1b06a58b]),
(341,[0x141acfb9c60af8ec8933b5e38c2930f085602acb94432feea59778d,0x17e058b92a43a84415a11b4319bf5976568ac3b9a13af926a4e9aa2,0xd745d56e5a5e15bd0b946759f84817d1117e23065709e635010171,0x367d894cc7d0488cf241fa246f38f983117267143165e899a7ae7a,0x6a77ac09f48f5dc2e6813751ef6688e8d6ab61f4606ab5dce199e7,0xee71377379fa415257a6c1a55632e1519830d662ff49b879adfcf5,0x512a81c74d9e02214ff9c19eb726d424c1881edbba4f7c862ab888,0x71e84b0f30ad18a84d7e1bed563567b001f174a0df71d4810abe1e,0xf19d398e0963d8dc7230c734780bf4cd129c57d41c39a6d77cb79e,0x17eeb5ff9d708c6244d8153e12112abad8125d228f7c9e2ca35dd80,0x3430c9fe9e56ecb0359b9a4a3d59b9b0eaf8002b09054b920752c7,0x5b041ff9537bf8084b63faf6a53775275b9fa2fd8843104c8ad919,0x8a2a883ab062d5bf404bd0c3c6b51791342e44cbe0840730750585,0xd6fc4f58cf9036ca174664861b5c575366fbd9d19ebacbd0360b6,0x852650dd26]),
(342,[0x12226cdab23e28caa11ef5e66b2f4129b65b371711b53f57e5b8e88,0xa34da13dee902eb07d48b0148d1f14b3c156f3df622275f9ce72d4,0x14565699060668a2afa4d1e960ef4985b6762f8ed2bdd2bf9f38426,0x5cf3e3fb3931d376dea66a339385309d82611ab8a43b87b56dca8b,0x1929d08c5801c1534be5e986cef5e241aaf4cc48b5e43089972e450,0x120ae26e3aa8e027cee992f427b1ec50efa8a55c8700ef4bdd2592c,0xfb40ddb8aa7c0bcb0af87e188120495c2ca1a45e68c45bb6ed6036,0x1f999d34d81470879d0206068c83875f21a9246b22c5ca6bfa0cd4,0x49d1fcb35a16d74ab01e6ba4ec5cd055fd95ac81a5e45374373d5e,0x5bf2b30b69dfa842c00c4982926c8450d5ba009d320d4c5581c090,0x3dabe6913ee51792f417f61b068b17cf817c074c8a38e09596af59,0x3c6c61132a94821c90d659272573a8a1abc0d45a86e58e3274aa3e,0xc667f288c5dd189a07cb296304c36ca81b690fd16723cbbe14b9d3,0x148b45631e8aa917e436e2f137492b399d3fdafe6b92afa38b02190,0x14cb74d4b9c6cd]),
(343,[0xf5abec024e99914369db9004eb2b5ba1ba7fce29cea663f2f7e98e,0x77daef29ce5c7f4fabb3d9a58f449283e867d3eb379bff07cd2259,0x33566a581fbe49084cb51c603ba71e1e361ec1e63bb9133d583c81,0x37a5f2889a9b9ee9f602b4453d6674c07a2969d2dd4e1dab18f232,0x246b5d13a19a9c126dd140eee735803f050a999a8f0fec70a7a0f2,0x854328d2097bb5706000cb71981d8634ca413c08cc263941bd7e8e,0xa34dac196fbf109f187c65501204172bdd3b1bf89f1b0bfd64ba6a,0xc8ff3bac56d49ac9fe755dadcbe1e517301eca85bf5fd401ed4bd2,0x3f4e2983e07bd84c352d0391f14971b41725a4e0e361b2e9030c9f,0x15aaedb029453fa2ca3d8ce298909375da3cac41b8e7c01e91277b1,0x15fb14d345e8a90f1e5630049529cdf40359bf101607b6b3531d2ea,0x5294f575d9787c3fa899454c3da615a8dc7d36045f8395c9213176,0x164833c28c2fb3c1e2962f5365224c7477b665480c417e574316bd4,0x188603cb7e49fb12e031c51069052eb7965347261b926c26badafe6,0x257c55f0bd78201c]),
(344,[0x583987515511bee1f743c3b0bc2d7d0867c2f59c06add94d8204f8,0x143fb8376baeb95f304f2f412f02d6de15a70398653dab4761525ef,0xe3b38d17998db59dc00048323c19ee0c9d77b29b2c434116e2661d,0xdbed888bc946f566f2096e34fbf3f88da0c9582b6d7b5a4852822c,0xf8b286447fca0286d6f5c200157e650174341fca28216bb4797b03,0x27e7424651d699a0e6bbbeb75a7e9c1c26257b35e297d1611622e2,0x19954eae121f1734fd067798c88e0ad02a652ed85b8b17087646fb7,0xf1f5c2fa37ea79f206314507c2c7842552a714a8c214854324ec5e,0x60d44c49157b425bea9f5c7866318a848deded2bb3f2c54e242930,0x46346697462fcc4f6c122c45e4e319859a61a25071453cf8ca2334,0x170e14dc748bb3446b10399a7f12b07fa43b3bb95fe7bbc7d201842,0x13f10eb0dbe59a1423e0c0b451b76154ab0fd5c005741ce670a0378,0x147518788f1fec620057b007eb031658ce2e360160796326be6c275,0xf0f467f272985bde5aa9df62b7566be5e5b0abea3d430e812c8d9e,0x810dada2cb9397621a]),
(345,[0x16721549b4a92632d331808055f693d8588973ff05bf43dc683b01c,0x998511251814ccbb2086bd45cb290ef78a1c9351744e389b0ac16c,0x19b0c429e3fafa2724c020a9872e948f663b7b64450ecf662c97e62,0x168722a3d477bd6f058cbbc034e36098e4890bb040e4a256fc308ed,0x680ea0316f85b069784f305a13a4869ab4c09e630f5f96871a22ae,0xc607d211df9858296d6242a6a5a57e5582c5e93fba2ea2e885017f,0x1268cb55803baa35157d70758ba8b825c56d1db36b50175612befe0,0x231f7629ddd7b299c36feeaa4e2e0dade8aa6f2c13694b52573be4,0x18d93ab4b5707199d623cca9495e189320f53dd27b75d37968550f0,0xb809554f00e55a27bdc4255ca9b611531396f43d4db9bc9019677b,0x11736f6be4570edc14e6f7983681ac985821bef8270758fe2eee635,0x83fa9b4e860434b38823831c0d7331756d32f549458a653bd07c5d,0x805d47a1e9011b64afb5f17d110fea6637e90bc1cbc1b573a76857,0x17a32be48f4845c799d700e55e3c290af34c2e327b756dd658d0b73,0x167621911663762e8333c])
]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem baseCyclePacked7_ok :
    baseCyclePacked7.all (fun p => checkBaseCycle p.1 (unpack532 p.2 p.1)) = true := rfl

set_option maxRecDepth 2000 in
private def baseCyclePacked8 : List (ℕ × List ℕ) := [
(346,[0x49ad0da922df5d0186b478f158030fd8e0e81b808957aabec3f152,0x1687250138770e65ebc0e78dffeecd54b4f9ee0802304c81a05d7b0,0x634e031139785cc1b65589e5a8ab023df7287664827532415a8ef6,0x1746220862dec0ce2c04c5ba63e4ac545c645e070405fa089299af3,0xb30b903ae1ff7a2f14e39d2a07bc2727cddad35009a18b4b0f558d,0xc3ff0b2b5abae2e9921a331d4b42569da0133178f6ea6c4f0ad8a5,0xb1d71755a2909681337d0c3d078a8914b90d9c70cabc9ffe7839aa,0xeaee44f57fcc656266c046de4a9bd909da7ab2eda4faf0e3776ff1,0xe8238c51eb3dd7b139e4e6d8f148c78925ad7e0f064514abc893a6,0x1993e42542996d96008c1a36e45037984ed7d78c44631c979dff3a4,0x12f0edb83a43978d6e198c1dcda763b672abebf24f6ae913f950d1d,0x708e65f302c8463a1743fa10b3cd7fd4a4dcee482d699c230068e5,0xf2e60253efad351677b522743ee473c23c3b897224e08f24757c4f,0xd87a4ed1d97ef384a24554f22c6f17b537e75ba2670f46733732e4,0x28a8dac1d9101ac64e44cee]),
(347,[0x13e0f99b76c68ade3b01f2ddc9dd9f5179e637630a720561257406d,0xbcdad7259a01dad849dc63a5b7bcf7407638527665d3b8851e27b9,0x15333a9bcab8adb32b7e9a5a875a49578bcb7283a2ec0b6e172f53c,0x860ef8553ee147a7b75c7a78329094d5eb213b2a282fd51683b70f,0x2958c09ec35bb3a471a1716b40e3e3f52081e61665101643e5e632,0x1c87bf2f4933dea98e9f3be36ca1bf14d2ec3ac45ae629bef52f3a,0x9c53608e19cf1a0d0a88f3023bd9f5653b5831c38840ccca58f3c2,0xd0f07a86950c8a3202fd6a3b8545ee0bd68857a090b941b555ba37,0x14feee6935ff792b5e1e6d472fc992f6261cc98cb669375ea7b2c2f,0xc27b74b3bb933233320a1bc14b5ed7ebdbca01f7adb45bb95fdb26,0x18052da7b09d82485fbaf6bb50e353244d888181c4083813da8ed3c,0x1056fab9f464c9396336503c1ab868be7c67876ef9525308872839f,0x19c243a81f3bbc49b02f954fea4fa5383493ff8c6f12f8480c16220,0x95e7de3e436003995d79528921cb49ad977575b36309c48c702824,0x247cf3576d9a0cfb8029d3a31]),
(348,[0x1781bc477f9f8e2c67b6a243e8fcf45c156bd8fac06a6e8c64126ef,0x9b1f39bd8bfc019b9f2c465b07181d19cbd4aa671909398cf55c26,0xcfab3d2bc461dc6b1748663c225296edf9fb33d8e1f1ba6b1e9498,0xd5d528ac0bd25c8feb89081911c6b603e5353defa9786a3ed14a5,0xc5098dcb584a45e7c1d3393f023ae15e9fa39355339a456c16e095,0x7665730780936d698637ceee6e370d9033da9095883ed61841b0fa,0x89e58663aa7b614f3be652cc894acddc262009d206be65cf94e77,0x15f806eea036e9f3f0e5f0bf70aa42764c4257462492c87c392eace,0x160ffd1575dc84437b55efe6e774c4c0dc332b473d65284d25cbca6,0xe80e1905878df45e489dc21e41e82ce2e3c02507f179e35fa1b995,0x84f8d2136dfaa9b7a79a1ad43ab0a86a8343624f71fc86384e3411,0x18a11c509b132072f0e9fc76fed8d84ca5201e7b9635f75cf8c152a,0x15270af35164154e200c5909019a1b437ee2d93f2302aca69349fcf,0xff36766b8f4ed4119cdb209262da719fad33757cfd67d05180b415,0xeefe6e59e858f6cfcbee31bb5ca]),
(349,[0xef8ce849eeb15905d1d22a9a8d55e41c66d26def472667dcd18fc9,0x10fe5b73aa937a7d6d213627e7623ff220b8679a2650cc4ad8d0266,0x14df0e96a0568ed0fd447deaae8f1dc580457e7ff66a49eb9435d07,0xe36896d23f2bb29b01dad51527030f53a75f545295e02297356c74,0x9d881479a87bdf162e1f097bf90fb5958b11a714e8545b7d852e09,0xcec130a0b8ad5a17257fa71436831ebdd002c9676c19c698dd05db,0x18cb48d3137afe6f51e20e6e45551c69ec16c19f46e0df666bb3821,0x5d36d9a2a264cc05c049a684fe945c973ca64c6305a5d12ffc2a69,0xb46c0d215c5c3b8ca04d34c53a7b0d435f522c0952b4e1a6c10a3c,0x88b8eab400dd9536e3af4097c7ade5768f1609639879d9cfbd9ac0,0x19aefcd0a6ee8edf001117e82977b8c06166d867d32defe842cc227,0x5a1000bc7cce4e0c7244c2d79d3e7c7fbe6b02983a36c359627319,0x2df77a42056e45003d62c0bfe239ccb35de9d18f3f417bfe9c8f7e,0x2441697d1409cd290a64f0fa144a1a8ac4d2671691bcf4dcc55703,0x3e9e45c83c90c3f994ba6855cb0ab]),
(350,[0x16f750755da4b57268f9c04f8cc0c5c6739db464f11505e2da31f6e,0x187c56c55edf4c4a5909d1108910af90a6debfa163335c3f37c0e20,0x135bbe808f23b82f8e07ae05affe16917e301a753e588d97897172d,0x192babc4f33d71e81cf5a3216c49f323fbef8c8f83e85340448df30,0x7ee30f68a578b0cb46ba78a765af73bda3b7a1c66b8ba7f52a737c,0x518a7f4ec24dd6a4313fe5ad85473123b0a5e7b975fc04ab84339f,0xe0d3a2a9a0f14697b0f58d4bbf39e16ac0fc0c0a2761e59ce5b1f2,0x6710728d224ece96663210ca8ae8c17f19d3cf757e8817e97c87e2,0x1585dbbf3b1d83a11427f9890337656fd505e02c7d6cce716123554,0x12f4f66dd2943d29c90204ddc1d49ef101485e01ec4a5c37a9dbe88,0xbb65fed7d8900879c08f9c4ab2b80996e614c047bd8bccc2e536fa,0x19ba71301f7735dfcd6b19c5e2e142d9dc6bb6272490af038acdf5a,0x49d1f1cc918d811406d4566c01c9fa2b6a725249043670e5a35c10,0x154f3818fe94ce87b5a14939eace3da98306e3e53175516512ae1fb,0x195a863baf5d8e6f40df231790fe4acf]),
(351,[0x18ee36e9075f779d2f6a5dfec522ff0db0281bad78da67f81dee3b9,0xb8096172b22b8061f9784c3f59a277cdc179e6e697de3880775102,0x14eba5a0c6ea8fe1674097b0d7fc9d77b17aaad504e4863c1caec6d,0x6fd7b89087091a0e42cecce560634685d4fca31f521ba02e69a9bc,0x10b75ce8f8e9d973ace880fb96ad05338159d0c68953f17f9d88398,0x199551d31486a20783f3b720aacf0146da6d0e70836dc720396f74c,0x9636c2157f2589a5267aace40c2696303099905b456788992a5651,0xe919b0bfe87f07fcbb2020614eef6ec4f84ab4e94d59bebc91161,0x474f3d788e1d3cac46460c7c7b53b29df9c54d284edcaef2dbb7c8,0x815bb51a6fa1514d770177887405c1f23d9ab5403e0918326e0186,0x3a03a0dd012b1f14414a9bc020f40b0ccd5abc9e19be2c78ca9991,0x11736ed0563b9e255df73c2a9e077822a8a69381a586c5b60409af0,0xe57db7103ffb0c01c8ebf31e53a1bf333af1329bf8fd15108da55d,0xf8c4933b41c3c14bae89bfb0cb1a340a60a41f926bfc32f1eaec3b,0x9d57698ad243224ab2f4e1be6bcf79bdb]),
(352,[0x1443123997c3e7dce1f391604b9765e71834a86f4c2ed4132b3dfde,0x94eccb02ec5460cebd0bb1fc5391c889259cda3f2e92542aaf1cbd,0x8271b00ba3f3a32506adc4ad11576a1bb29efca2b590a072eb4dc9,0x152a61cdce10fcee5628fd1927fbbe42af6ef7a25617557a81b1965,0x120f21d20ab172c723e48e50a659d212b6a244a45bd2b3c4c6f2865,0x13f4407102171ff5807952d2e4423b22a53d112c6a6f962000eb896,0x10ef8ccae1f01344d3ce862516916a482549b3c8cd264863fdbc6dc,0x1186b90e93366d12d686db12a6d9ca883a6b09857deec7015dfefd4,0xe14aa65c28d4f968c5b69abdc99b07a370faf1bf0e10f85c600608,0x90d9a45cf7b367cd64b569739f0bbbfe58eb22e500a3fefb2492e2,0xd95f7e3d4b9b2ce874d84ee58e73c2b3caa781d8825f59f1c28955,0x6844a68f4e7ae6b31aafe02adacda9d0b8db1e05987c5ec4eb9cc9,0x192808c22c83a663f67a047b6de6908c8db378cc1e6d584c2182aa2,0x187a8bd6e92727e94f20a84dd6673cb4d46fb81374f0fb000c24974,0x61f7189048c8d3df7eac1ce19bf83b7617f9]),
(354,[0x198a35a9fd8afd22d44c7d7f29f7fdc2a6a8878a610b84fb1495e5b,0xb0b84170d2b1f5d4e7b9d44ba0eed3b40b8178d552b2fda871c276,0x112b0200f08b502a820d15a45003c010865fa0968094a6ddef20b9a,0x12fb5b879c7aa63b2eeede90f8ab9fb1682d85efd2fc2fb30e02909,0x14b3642d6dddbd1b14132a3c68b0db9f747b0f98d761eef13d5dca1,0x1abcd7c244bf1d5a860bc4bedb5b112de18b21e5f6b335d328844e7,0x20e9baa9e8c759e023af84dc87e59d45fe9c6978e776eb64e531bb,0x639cf572b4bbca9614be16085e5f7f63ca13692da0e756d56ccae2,0x1282cb73b3d75138306d80be2c79bc381beaad2d4f6859e069fc763,0x114e5f64f8530bd0fe0119f8edb11325de731f592dd270026e761e3,0x4a00fdeafaaf4a40535f8f0bbd93868571ca639cbd4f8e5ff728cc,0xe1ce70cb04c85da2db0866a1c0c9bcbe9e8ba5cf012dafddab43c7,0x4c3a96dcf3cb2ef887263f29bd3e5c7e9078ae4b642216403b5125,0x4ea379379105471c3688c2311cdf6e84455f29b67ac216e8b13231,0x1a3055ccd80bc39756d1ffafb1db1b135ae00dfb4]),
(357,[0xfbcc407b1bfcf8c65614edf69e3418f35d6dd4fb7fcd78ff2b8eb1,0x114ff083e6f63eb95035908f40a49d2e38dee51ddf2279602311305,0x3854225b469a13fbda7a48d29c429a262d22c1585cda0778102228,0xa307bc3647e353856f20f169388c781639f9e78617c589500bd4ab,0x365c7daa74cfc5d88e7a607e4af8f3745c1f6bb1a11226a804e306,0x27f13182de39d1ca4cfb90006cc15c4e709e4e75fb371566755358,0x1a9163e103faf31d7458a358c51123d9b4c9b15d2d84f0d6a85fea7,0x5fc27d5e7f09e27dcd293856791505247f3ccc8ab2640e1b90fd21,0x5790bd37dd1c9c297b1e672dc82998009a32540da7ba8e6b8a3c21,0x1643b8fe58736f346916846ae6982c7514706e5b6d26a5983cd44b0,0x8b21e9556fed3e023cd352d1e1604a3d181b5b3edc27e8a4edbf89,0xf41a9811cc490eb458152a616c68552bed8533ba85d7d6055fb271,0x1238e5a63e875319f8065287fb3bb20cdff1010e24a8c72f807a3f7,0xfe01d7b4ebaaf4e94d231fb94b0eae6d0f9cc4952d41774c598328,0x9114707f0787deec56a80aaf4b77c8fd99a674036c14e93]),
(382,[0xe48694d2dcf10243bed2307ec8e7a4e4cebd065db0bbbc7b1c9ec2,0x11148a33aa5f04cf072fd197532bc80af08f3106bbcff6ab346378b,0xd8a8d7866204fb4ae8646a26457bb33acb619ffb06e262268a47da,0xdae329aeb29e89672680bdee3c338bfeea3e74bcafa58abffde7cd,0x16aa35d291eba1fb1aae2ff4770558a8498c1c45922a18b179f5d37,0xe0bf46485a64fe001a29a90f3dfc5b7d4678e6dfbe0691c78a5e4c,0x16d43f868a1c9f8eebff6b13eefac3f13f431941e00c1a1e2ec999e,0xcc30e0c463e757d91306e99332e630cb991f38bab4b4f3cbadee12,0xb71fbd8cb76d1177ec23d67e032f2b2dba85fc623261a77c1ccbaf,0x12bca2c2340f397550b4933da430724bae9f6cfb70e350b4816721d,0x15890ddf9198da75bda73370198657e5e3e4018c4c10db98a11d7f5,0x14d9ee463da1dff8ab1667264a383a5c61a2e79829a334828ffe33f,0x32b65f7b4165f59de996eefbff39e896244dc3b3b7cfbdaa3f83b0,0x194833c5bd1c13d012f9756c08c33e4b62d0f731d058e9994c16fd6,0x18d93970776d95c464373eec7af1ce15d0746a4e720ad29efff1785,0x7497ad56115e6990fe1d55cf7070ddafdbb235918b9708554]),
(383,[0x230cd3c767c104ce15a1c5070646006dabddcfd741f0149e909898,0x16f5afc17bd0d87c68de95adf682c59a5ff3da9683abda8d9adaee7,0xa10e9aac5ec455c1b55bb4b6ef0283f2e9def3418d693381f15dc8,0xb85444b588476a7f65c63eace4db56bfd494de898946ae586c8b3c,0x16289e90524e3320aa6832343fcaa2e293d4afdc05ccd3c68790d4c,0x16137db9e3310f1916df179f837edf6cf5091bfc0861cfae7e8fe00,0x1949b110b337b43f2c4be5a6594273f48ee7eb369a149c5c1b0724c,0x1b3612765366f78660048dfb15b814f93139268794c938509bb59dd,0x7560356f730828ef04d8107efeaa0037467b0e1f50413c14c32050,0x3a1b03d84a12e349e093426169055efdf7cd9e70be2bc0673d25ab,0x26c7edb777ed4213167af19db5a45547e125e04913de9422d9b584,0x11f79c94f6c2614f5e747993fc8e5dce1e7c8b0b19139ece600f4d0,0x1b0bbcdd488d3a94b6ad2f17883ad539b69c1d7ed70a7475e24d69f,0xc012de737ed7a8658d44afcf75d22295b753705db18fbc731f798a,0x16cc122616bd7219ef5d40c89cc38a54001b959f3de5f11fcf71ded,0x358d32896d80fe6845890d7109f32e4207bc5a23c9d70082a7ee]),
(384,[0x175d0bf6140d38c64bfe963138e32c883fa2703fb081659bc821a90,0x1afc3df2b4cd774f65d9f4832650cc9335882102bd884f473c2d37f,0x103c3e571d042c184e35013ba8636094a593bc6bbe1127fdd7ed920,0x3c91212ff96326eb951fc3c87b967c95c71d122df132960ded110a,0x4ded60472c9f1f675c7a31e7d27f5fc8e9c9e68a1176a662a20b36,0x12e81726b28ece4fefec6402fd92b312ca62381886c5e8e92bd7ed5,0x20db4d19024f11079c500572155b63447125f8c85420341dd18507,0xe7e835b5a5003ea0a4ca45b6e4b3ef8cd773b33a2be7ab8285c82,0x1825a1e832dbb902aa86d5d73dbdcdf16ff3bb5c866e458302cd508,0x3b2781cc08787a0d3cdf43da71d51adf6ee973889aac35eec5698,0xab97412e7f84a990ef0b0fb82a1cf7467f348e1838acc5b7042f96,0xdaf999061014293e2e9f1e078ac7c1e0e7264221249ba36b11c5de,0x1238e5a69ee08826d24bd8dcb7edd52b8d10527386a67931ae0d173,0xb69477807d6af0945f676fc8fa650ed230ff4d0e76293e159cab43,0x93fc61377c2ee7e71f39d9a1a687381b02de6664665f579385c45a,0x165b78577969718eb469bb36a447f658a949eb9cd8890d2e4ed05d7]),
(385,[0xc1c49e417cb1a03153f2d2aae3728fabbf058b467bf03fc3b90508,0x161557bb46a0c23b38f1c47950bf28ccd756242e88e36cf152fe614,0x158c8c1f8b41eb9402ebdbab14d9349b4e0bb69938d38191eb4955d,0x10d2dc33488542853389c3ed5e2d03a520d9337190a930c32161ccb,0x16f74fc5b9cdf31308f6cf7d1324d03f61695d3004afdafa66483a6,0x135d879885dc59348e033e34f454456e8a2d66d557e2e647fa22599,0xdaf9b9dd24e834e7e659f91bb8004cb63b969fc6963e54168a73c4,0x18c5f6031796ee6c1210dca01da039179ccca8a9729b01394f9f844,0x51a11b7ffa4c17bc4a4b2246e337dd2f831e49f353dd696e749155,0x19886e59951f336fdc07c6a910a818dec2c66d2dcbaae141d03f0b1,0x62193da6841141bc9b8015aaf2b380ab7a4f5958cf4a62b57a4447,0xa13d2f7671dc9bd6807afab77c18d619d792f2f057d659286c0f2c,0x5b2dea782d572c9c142a9878e6f254c946a7f00326ab666f757cd7,0xaa4262ee5174cfea28f204ff1fdb5b5308e6203a20ab316d433f55,0xa9c4d11d1ed3d0a6baf6d4317f3b70afa5ee821f20fe769fd946fc,0x15bcc9a388b823f9121e868b3c9439f35c9e5bda8413df8fd2c1a68,0x70]),
(387,[0x13975d07f1921f0075e199d0c6594b9a818f7041df0b0195dbd03f6,0x173124f836d3479f732d16f7e4333c596e8126356d3ec683c71011d,0xd3d7142efe9d27c8c15b26ddfdf5f31ccd17501994daf075b63711,0xba46209c0ee66e1fbaa8f99996ad79e5ccc8a945abc632f0be1ae2,0x16289b133717b4fa47312ea2c8bad20bc240115c13cf777d28ffd37,0xdbda95032cab4513a045eaad3a2f234ee875fa73ed6e46084af30c,0x149a4a0efe55764b73d0edc0d643bd4e29934a9f5a3772b22e18343,0x7570f7ab96bec2e9b11ef8ed98184959546b582369c05d0750d53,0xcc44337efaae7cb1fbaf023af7ef0e9057a29cd81a01c65b568ddb,0x83d52da1eb2c1fc5d2abbf93570394705212ff6ed14f34bf8301e0,0x120ae1395c4ca89867af1e678f2871b010e1c47dec7b8083c054d1b,0xb4553d380e6630773787348a1c13c1815125b4e41577f133672181,0xb24dfbf260d9895a94718ea13ee153287433436d0098ad88505e78,0xd55b4310b168fcc4010e6d52e09828f8e8e4bc8ab57c3d731735a,0x8fe1bb410efb9605c4cb2cef5985a2102ad5501323518a480a8ee6,0x1a12fd0eee2f37422bce4784b230c58e82b848b5bf94373d4e244c9,0x1341fef]),
(441,[0x206a2a3800ed0a8289bc8207dedd6c1423e4a4bb6d394d89a99153d,0x1ed557f640619ab14f29d40a84381c01165e2ab681ed5608244ae3c,0x1a2a34b0bab1d4f90ce24fc1dae1fc393df24abe59b8de5391073c1,0x14ca0216dbbde02966982ebc2ddfbe63e9b18f15b6a719646ab1bd3,0x201f1f98a6a51f2e8e49070efdcd8ccde7cd895ac67bcf08907a61e,0x1d8ba58d3b3710edca25b9b683c86eaa42924672516408e1f9aff3f,0xef8cb729c5bffabe2a38daf1199f951d13bc2a2acd33fa51874592,0x136f048cfe3368ff4336cef79a90ff499b1d5864700ccf3c169d0ba,0x1f80d750efdc8b7ae691b0117bf67689953968e310a858c49400ee8,0xa80c20f2f63123acd2f69ca7787db3a688425ca06b2f94f9050117,0x107be6fa7e5bc98e26fab3e696d542976d3912c6759a961ceca36f6,0x38543d12e8951a2c25efc159fa52a4888d7e2815f396e780b9202f,0x4b24b3d83c2b25a54758ab60aa0ef36d82fbce5c9b859d901aacbf,0x12226dadd1c60f84525f72aa77e4dc5ac202ab3968f8de48e341f1f,0x12780dbbe21c8d147e06f1a827801ca69fb9f383d93175870a36d91,0xd4dcfaa54569f1d989b053a2b7c475ae3d49677b71a63ea73a9c3c,0x657a65e0c69bb12532c029f8df7cb27c923565566b6b705c38fb80,0xd984a6591e308afbabfaecacc3e097638ef37d3c7a22d3277512f4,0x8cb599743708210fa970]),
(442,[0x194e9918d1e11cbf1ec4368788b9e4a04d9a7c0f98cf1f563d9fff1,0xb0487f7d63657628a8be57998493f27eddf6683dda8663e436377e,0x790f768033bc3710e2899e1ca2340561eef515cb5a6d58dd9782c7,0xcd53324f427e4f1f335893b056267c4810e2f2b07506c6fedd912d,0x82f01f61b388de7be9b4982653ac71c032d46c71dc37e160280436,0x101edb134dc752e72521f2cc1475df1fb0833c06081e32ac9be1c41,0x2722f3f900e8d261a7287fa766c0d2f62bb5f26df0bcced5aa7e7,0x1fb6e21d8a2522638ecc4e036035a0bdf8aa3d8a1cd9f01dc722d43,0x108c1e06550ea1ee9a80a07d0ee0cc8f84dd5953b79fe223e94bb45,0xa6b509b2daea3b03841423f1d1c5f7105c184a1d4f6215ef5500c9,0x1eb0dbdfee816616469956da1dc0ce5b28fb22239a21f65d86e9e32,0x130b4f7155aacc03e23686445d589e5b161cb6d054a366ffb02bf17,0x1368a0000b04e7a01caf17c5d468dffa562e9e7848002ceced3c8e5,0x1c30ac3c0edf6bba4a2837aa7e04bb8bd5cd15fd563c550000f9867,0xbbf18cde30228525680fc4d7271ac762f22c500c0a37c5b73c6497,0x200bd9b927baba423f73b9ff87845f0a3549d0a98b991925890aa31,0x17c82da3b3d42c940fb0c4be6329f3d9419e5c09c8592202d19fa28,0x11c39a5c43536f7719bf829ae2455a35f1b25b4c3cc1100445936f9,0x3beb9f300b1e59961bed79e]),
(443,[0x1f5a49a4c1483724ec872650c6940bb07d9bd84393086f6fb9696e0,0x1e979809a37ec1560793b89294d7fa22a34d1b292757c0bebb3ac42,0xceed7ff584282ed02362dd8312ea3b295a78cbc9a0b58253aa52af,0x13975dfddeac01ace5de5afaac76809586f5db4b7c3fef1f48df636,0xe0e9408c77678c14291ecd03ca63964b6e9b41f85c24f008c2b9f1,0x1c6894392c9722f920eb5c1a1548f51ef0744bb04c67c21ed4686ff,0xe6c56939bec4804613581746d185318a32cda649bd38fb0462332d,0x10c5f1e4c3a32deb2c837ab432b38d374c8aeebaeaa6384cee99e06,0x11224c3404e66a9c83924780be686e9d7a63c4c0d8aea7e1a8f0bb3,0x43b21e66dc55ba453e1fa4001cd69c614b8209005b7308af432ca6,0x13177c4926b40e57045c017826ad93161e0301fc58cf9f2eca25bbc,0xde3162bd464af4c6c30d4b303601c8d310b51c2bee9415b319b0b8,0x2cb921030a03e543c229421ec61379958ded9386d8926322f66a11,0xafd2a097976d867e345f0daa15c194a247be5aeab539994b40b08,0x1a12fd0eedf94c47eb0dd984bbecac47f9bcc876f5419d255ad290c,0x121f8200eb7be74ccbec01e3c8ccd679d6863b0a746b5ed6c857f44,0x1737d13364817d62f2b77d91bc4733bc1e9e97a0ccbbd5422fa435,0x19b29adfc87691a92cd0505df0ca213ae8e323f330c0f10d6db3b0e,0x82bea3e4337f5c3d7063fb889]),
(445,[0x1ac26c3893ccca27e89c8fe46fadea2e7dec6fb227454903638cdc1,0x1c6c81ce7e31c8160e298538140e4a0ab56b22fab9b5e22db1788ea,0x43be3c9aecf92ebdae51f688d2334671b50f1b4be98180d2265a9d,0xa0bf7da7e528f33b2f3ef5a3e1f6783e2dba45297d68eeb105f83c,0x1c32aa68b9848022bd6987837a8d68933a6df86ee0923f1c9f52c77,0xe95856f9d8703507253144bd6f53d70c0ab8ebb12f80214358d17f,0x18c5f60511570d594a42a19f3ab753df4d944f90b04cf24c153b538,0x20ddd16c926ef0ab1c9872ed64ebb629a20bcc5f97297159b0174a5,0x17e5e966736370c17d289480af147a746701b30817ffadf01c2fbde,0x1c013b5f9b18225fe8dcbfda8d4bd766280360946c46459df6fe821,0x1995549f3c21e6f646e529cb852760bce9e860504f7ebaa3fb4f592,0x3cf9bba94b84ccbe2c2c74d5311dbecd94644e2b284540d6804432,0x216ec1900c94aa4d6f7964c110d83bab6160bf29593ab29f8642f6f,0xa205fddd45dac32398b491bbf77234cec32b1c32c5317554f834e5,0x7ed4910b7d51b19d1319a0cc11a8680bf9a4b098726cdccd4c54ca,0x1976ed4a8f425837036739072da4f237b8df0978a17d87f991af038,0x18801d37687971f6a3f6235ea2ad4f64c0bcfc72c19b61bb5b192a8,0x9d115ddc8e8591c924137293569a9241786f5a97e3f01dc985dcc9,0x12879637d843a3ebb976373c77106f]),
(448,[0x1b4b5b3fcecd16bece8adbaf8bd39bf15a907fffa005af0b2e9b780,0x1698a62e195f8fb6bbe0f5879d15374be24e7170ab81f423287ca00,0x13cdb53bca09cfd068d85a1b5b9662d695f15c630e2a286d7d607f9,0x18626023b0c1d67970e9a1ed961c707209882a666d406f827926962,0x1ebe25b7c0041e822c8c98c747c69e93b03e1348de548949dfd93cd,0x1a03a5103ccbfa28887fdb04650fffcdc84aff3f68a77115dcbddde,0xdfb4a8afdfe5a4f497befc535328dbc8bdd9546864d60f1958a1fd,0x10caa087253e6af3363bd29f9c7af48d38a16be67c721c67060a190,0x937ebbc6746c92a5a24f17013892342add1f79177787f45e420713,0xebc0dcac15379608bdc16f299786f978362871b517ae090fba9b82,0xd627d9a6403a134da72dbd623f3bb7140c36ca18fe8d08d9a362aa,0x210460e81de98ea4ee5d06a9a86381f4128e17e24d86a53633fbef0,0x5a9610223daa11653de7299bf9b9bf46ca52bd53e94fe2c0f51073,0x87efec4125ccee03e7b5da042afe253df6740a0d6c3a839b91b201,0x123c61f4a2572be2040e937c406f2ccde2ff10c92a223742c9ddef5,0x154f3b811c491cf7f67a5eab3994443cd55eb96431ea23f16f4fc88,0x3597d8bbfff447c57a8e361272e2899a830feb0a4b0fce2eb54f73,0x139dbfce1695d582fdb2b7ec9f5313ee4e7468ccf149eb1abbb61,0x55680581152d1794755b92f93f2b5737d594]),
(449,[0x16fe975c65e41b1ea027ec98e2de0f793e01503e003b1a0de3e45c2,0x1e998705f946405001ebb6cc50e94f55f1cc6b326e3bba6e3006830,0x1f80d751518a04fa8b5bb3676c3b1a9bb0c5fad37a929b8483f4ff3,0x1262f098ebd690d3879faba75ce1532652f6985a9d88db87c3580f7,0x12aaee267a44e485a78fd9ff36924ee64c000d1b9f7a25a8906341d,0x214bb2f4bf69fe0f23fde48ff7a7bbb1c2224831a31a49803548ba2,0x1806e667362d13a3a3862028fe99a6eb1829575656d356066e4ec64,0x195cf6eadf3e15605a7ed4cfde87c9ee2bea79118ed40cac1cbe062,0x18b460ff2cdc8325421ae04fb74db99aac8adda6b62f29520a14fb8,0xbcf2dc14ab952ce5aec71d7f500fc10c988a0748aee7d7ac3c4c65,0x21eb6824bd03b722af620bc392f76ef046054fa88707b3f58e1ce4,0x109b5c58af6517abdd74c923c754e6e56e8908cacc3e9ff7c5325ac,0x185ee1791d5203221ccbfc16f03996bed9ebedcfa0dea1021dea28,0xa90e150c65b0e0ba92429d9e48466f416669e61d7f3bca1fd6cecc,0x195063b74b39729433c6740ccd94bd8cad9f6d03f4c247531508451,0x19e1be6c73479e86a1372f829abbea28fce110ccd80f41f93ec505,0x81bb8a6c0d5abd8a3da6eb5cf677251ee09979802b84179afd16f3,0x155490adfb2a1750b9fed507847adb939bbaae09044657b4f145906,0xf781b47ee8c7befbe52a6cca38337e6df9232e]),
(451,[0x1f0f2f26eaf9de84a8b1679253b9ef29602975ee594e746d5b74dd9,0x13a8db87551ed8c317e5f70995d8d408b6e4d0bb3b194d17e587a16,0xd30d8d70485ea8d597279cec9c84c1b4a6d6a23cec382144dc29fd,0x147ce88e67c354f6e17b8cf2ca0a5fe74fe3d9a8208f2a3ca19c4de,0x1a620666ea18e196dc161bdcf1fc011e3cae5bd1f49d4d67f2d0d15,0x5aaff84b7833a9bc9b10f87a265f0e29595635817add0cbcb82a44,0x17f39f91c547cd5038892dc8f4e008221571ad0b32d37f41b8fb799,0x1e4c6ac7e9c3e2501ccce3c654b4ec741b4a2b80a97e77159b8d79c,0x3fbf72adbe2997ce8f34ffce04fa09bc7b5eaf2123be8072e341d8,0x195cf871b2ec4ff3e3848fb2c514f3b48f5bfb59ceeb7cc9734ca7c,0x491b74eb1698efece6cee2ac97d0b423867faf7c164307a9fae9d9,0x743ff4a4aed4de58dcb83de04be7f48cc76556de7b65877e804dd,0x1d5f86847fcbb150d398a355e64fc91a1e88590530913f9a26dfbe6,0x1e0820ec7dc087fc0d4373eb225f61bf88e3ca014f0bd10db8324ef,0x1dd4fa968e976ae573432646da6f641227421709876e4cb573e49b2,0x20cdeefb0f660b4f639c083ee19a278c10f419a4545b1b3a3ab7ba,0x15a1ace266afc3390e646d40ca9a90ec52577a83dbe0158dcf964a5,0xa3a60a25a295d9e9e68c45a1e7fbb50acec07d46add6cf72fe9ffb,0x409fbf58ddd14489051c98192fbc52ed603512894e]),
(457,[0x16eb50861d5a48bd0c955b42c3de72f3acd4164496eb47dfbbe6150,0x207b710e1a5d18667149f87064c00b69f5702be02c3c3de6ce3c261,0x22123ed18a03fda90a606a111121476b1dc2742bc561ca78a63922f,0x1ed76c543099a5d3721c6c0b91cf1389ad28e0f4748967efb3844b1,0x1dc1b55d9360c56d1bfd3e43b9914872a23e1bbd7124ab3ee62be68,0xb21b10087d85355e528e32e4f006cdf7179a6d3163454be5726112,0x14b36501bdb62e50b899deecae601e0b12ae72236c9f4113df2a356,0x4d8d55510c21f1e7b6e19116f70e9e56c843a845323d458bf9c79b,0xebd79ee90c038268fe7b2c073798661c7cff00a57fd4610885b1d4,0x5ea145b1e1d17d73b68443eaef96e76b747dbace57f278a05c3799,0x37b1fdb2c5817799ebd0a6977a5f48dc5d6a1763f159c790a4efab,0x1475146d74a54d7a1e1f0e6e1256c7a4abd1bc9a0a2b1255ca0bd9e,0x10f12cce9f41b5b1ed302b710f1021944cf888547656783dfdee29a,0xb1242185655365f416d0d9a12b6f2208dbe5667f82b460e39e108,0x3181f79f63f077026fc0808d4a991b2142500ebb3acaefa4e58494,0x8a009d9bfd51d96383a2193cc431dbb2a3d2779b3dcbc2229a76bf,0x1c183e243ddf2cb4b7552a43ec090b6f2ae39f35216da17f251d9e,0x204d9c39a98f6c69ff1dd778f4308cf5a487e0d87228cb54ff4b6ed,0x82da8497fb5f0513ca7d9c0f53ac17e68eba33cf40276fda6b9978,0xb5]),
(467,[0x794cc277e133a17c0c9cd82a559c067c95e980c33e0b4431e06ae9,0xd7c2cb2e70e2879b299e920ed02334a52349d4db5a6de0e8d45611,0x2100739df67dc6e399fc885c29d721affd297a3b8df58d6e100b47a,0x14431409ced7e7794357457cae17c3a59bfd9307561b21763c39934,0x8e44ab6c4672cb4681c3fadcb140f6291be67e7d2291f21fdf28bd,0x6a9a5fc16ec6c882741c0a24f399a0e5e4564e9ef4194872c4e97c,0xc8bb4d73a42ff24fae9c145e9121b4d9a477411e40ce0f8a4d8278,0x1bf8d4290ed5bf2983d8462c78227a2ce5616cedd49125dac4b21f7,0x22e64aea4afbd59fdfc074648c2c9dc69f57dd673d95e8c8cd717df,0x21c95b407ca7a6488aa21784662ff41a760c0c54bc5183333099453,0x1b5ca2ead5ccf2b1500b7124459c6a2ae05a8b15ac0a6b97c3d9681,0xd559ffbd667d8855872ebcd5f5f0a32db73b2bf69f3616b9da372,0xa4c27f06a51297cb6f336dfc0b139afcbce9c1d587ad9d9b2b8faa,0x209c6f939d313c30bc355e3c77c1b4916ce07fca631250c6ba5945,0x658782bdbca0d92be3533a9190f25173d22a7525a4a796209ca88e,0x3408905e6e1d2d76a1591c010a9341baa4a936aec9f5bf667d10dd,0xfced0f6bab46405419d823a72941a0bc3146ed98c3566e34165ae,0x287eadd2544df32a528c91b5b3c7e7e79bc3f3dc1576d1b04d505b,0x35d4ab3d17002d4d12e1fc5f6dc1dcd9c624ed842fc588b6ed8f6b,0x7cff628ab9dbbdafc5d721641]),
(489,[0x21b3ee414dae9f83093f7f0c1d1235fd7eab1d540e2a0df809cf55f,0xf4ad2bfee055a1bc3ba3d8176d55426e00409ba781a314489c4d7e,0x178cdb470e0075ad33ff975c91292ffa5f99ea9711cd71e20b128c7,0x8071c36c89665e7f6c1f595485ddb0bfa0b9997828c86b89abb08c,0x22fba367cc4e3b956c4106dc93b7d135112a55e9ebe39ebc32957f2,0x9741a52f0f070bfc6e9d46fbfe9aa86ff760c89d2c8261451ced61,0x1f31cf86bb80d0a406b13e6284d2b05f06cec5c97bdc560172d97af,0xf5fe01cec6fbf89ac7c6ae6de32de76bf55e9dd35edf1d5ddd5dbb,0x147b304dba224a70acffbac6267c4337bb7390e61098849a8e02765,0x19b489b8486ec585ce2bea38554171b5b75923fa6e68054944331da,0x1d19fc75400634e87f0eddb4d513dc8c74287ee297af3229e93edc9,0x2b1389c1158179d5259d33d6c0c29720ec1d1fa622f92fa085f108,0xd4f36c3c596b704a268d9ee91106100f3e52f53a89377a6259ac4d,0xee7633355f7c516390f08d9694ba3fa4229072cb92a851347d3d0,0x210460e8838b5917e4dd32fee528702975b54b9ec732f1156eb1259,0xaba988294aea6349f89f095e692f29f17161a09b31f25e8795fff7,0x53f35a34bb5dedfecae7fc9b077c19320f5186f13d15b55ab27f17,0x19c4069883dbe96f2cf47de435a6e5b8c3355e60844273914e97da3,0x1b773cc21dbc1ab5208ae52a3809012cd41a79acd860f282bd1754f,0x64cae5b5ec74dcb3ae733f217160d5f188a0925848c5c1fd90db9,0x1dcaa9979a1e2f17c35d4]),
(494,[0x1d408b0ecc73993f57ebf1ef432904a17b9dd075c0542e3bd999424,0x1513c4d61a58d08f2e35b7dace36bf310a4756761f5fefdc978a161,0x1c32ad4ac5d1b1fae6e0f9272785ba19f7aaea10932061f85086666,0xd4dd3c6eb226897f43a9fa923dd23c895eade6da8611055a635214,0x1ebe282bef21e5f3a224064d0bfb6523c31e5834aa990f54adae3d4,0x1ab12594e681e06b61e740c30938c304faf8e165a1eeaaff70030ca,0x1a6fbeee541d48079c762ac994f850ba96854fbaeccb25e5687ab9c,0x22f20231a6d7734f786a56f7d7301df678e8ca12bdb599426de8d9b,0x1b5ca10689fda3b960ceb029e5435acd9a0ad4eccaf377bb25b77ea,0x972e8347d04cfbec9c133a79a529acfc00c78af9d0d8e3ff9e4dce,0x1fa5788c6e0ec3dd652f7698d2fa8778a9603187388aca1aa7ba68b,0x222de3a067e1f4659c437f9e33e7c6379dee6b848b93c782c28d39e,0x4a7e2c144d0d3a2c12537aa41f506e9a868f999b5cd4733d4a79d7,0x2b84d775f2b1e4065a8a1a6300ef158d547f6ed525dfdd2ada2660,0x50105e0bd9d97a41e5df0c82e40f8ff24cd8559846331227d0535,0x2193ad7ccea6a2c1a2231ab08c585a2ba158545bce737de2bb2a8e1,0x2824533123f20acb30d8d3823d59304dc1837f024799a3b7ce621b,0x54900b64836c8a95bb5862e8c5d839fb8c7a00f082a3f12cb7066b,0x38bc880f52877d2522ddd0f28a63a3bc78ffa32579bb0b54540d57,0xde433a1efaf4dff1b081044a265b8fd8fceb59f178fb00ab8546fe,0xac392356ac1a74f62f0f13a10cc9229]),
(525,[0x240ba75efb256fed4e89f19d154dc430bab81f58ebcedddd4d3598f,0x1b6dfb591e795703d9e8f13ace722b0e2869c314f3408efe932fe78,0xba1e89d17e8da33e4a4858cc368984e80e5be4d015ed79dd517e0e,0x193b5576c1837756bc97dbec7b4dfd52cfd24d651a0739f75668ed2,0xbcc44e023c5eddc05c00c1e9203220e025c73b38a5f6e0cdb028b7,0x3b37efff1b0a978fd3f7d47cf0bfe62021ba757c1d3c63cb69934c,0x26de2e49efefec945a8a6886052903927e0e67e2e72dfdc5604aeb7,0x27488b784a0436986bdfa1a86786bd825bea382cc79886c56f0ff52,0x1727243e87db162fa1831f88a93ef5a50ba6c921ff4d7713b59f02c,0x20bb7da20cbec9fa8816df47837db5c0bbc5346897de9ed4aee3fca,0x247f4e8310384470b8720fe6debc663d88208a3cf1ab39b397df9d8,0x12d697bc221b997260b3a23fa9a7858effdd461fbaad4ae87e68c5e,0xe80e472aa01396f2d769c1b989a11afc1c141cf28f90787859672c,0x15777defcbc638779a957193d018d26608a341e805641ba8fee41a4,0x1e2c111dc33c8907f56630d49ff9c001261e380536e4c73d5a36ce4,0xe16666528b6692ae07aea604812093f2479b8ccc08ff6fd2b2a541,0xc5ccda06d1e01504a25eb0e2761b55473f41a444c11fa65ddbdc33,0x3d3df447e9616d382644ec0e034e77cd74b466845344bce3af4096,0x142c70bbc31b3b5f5dd9583a23070318230505092f9748b0e2a909a,0x45546efa1c8897c8efacf27e2b06470f9241463be275c181d3ddf5,0x89bacd0dd94c0a431e4b9c8f5f260802cc52587ace98438a41a753,0x411f529ad57507e823896234218994090e650ad9f484156]),
(526,[0x24a8120475cb894b5e8b08e6b9e30ca083d41742565fb9a9168a57f,0x1c0e3273af62777225a197a223d6ab28fe6f253cd47637d8d4f6633,0x1781bd12c925693c678e3b24182572d473fd35138d473c679c710b9,0x17cd1563515bb97abfd7caf56f9cebe91800b73357a214b65ab8a05,0x17a1a1a4a6c7d917f31c4d8e689e34cf08b0271df33e9eb101501ca,0x10ee0207aa1f4be7a0ed662d2a7b19f8ff8d438e265f0959c690578,0x1a4936168fa8846b78b6f3aeffffa7bb69c5c04791ed81a78e34f70,0x182f3e15fdb8aedaf727272abb7b5036a20ada176cb819b20fcecb8,0x21741b1ada7a5908eb09745f91de3fa01848ee14f49c1034a1f5154,0x309350f0da0d18e7e9cd5d0ad8a3597bda63606af1aab3507ed8f5,0x694333a5fb9e919c616f5a3bb7b91a3f95d8d2abb680da085fcc3d,0x3aede7fea72b6b9873d49f3509ec6988183d34cb351bd67baea2f6,0x1a8305c387157481b54f6fd7d0b03c7223b20b5ccac942c229bf7a9,0x1537a1e39467c0ea2a2e9bb00d9d31e173f4ea78556ed42fa1bf3d,0x18fe27a4e9c009ae5cc36c968147976ee9ab3595daeca7a04bf1893,0x18effe300122650930ba9a15e2058a7b96a6583f1d9363521545a9a,0x10980e6eaea0f4706f20a8bdade9f377c9bf8021b1920ac57340817,0x937ebbd083261b6cfcae1ff99fa27256012bd0496972830094cc06,0x4289c2effa48dbd5b5a55582b70092a087a06b6ed232da8bd51bd6,0x54c7faff75fe4f921218c79f5679a77325f318724de7fcd46a67aa,0x1f923285497ec1ecea1326536a34c65bacc2219f58d9404092873d2,0x4dd575e3000afaa1dedbd0f6d347c46534564b99026262500a]),
(531,[0x1d08cb56668224baa0f0bee3e579de0be07d1d1fc2dca67c61bc30a,0x18a4c226b13d077fb694e882ac2010b8ca65860cfbb6afb5c6bdec4,0xe736f4552744dbe8f5bbdbe117cda35681380cbad1d25a9ad9a6eb,0x254d24f3ad956fd89cacd2d8181818cffce819a90e758bf2311e171,0x23f85f92538f7917453b22b513dafa05c224ef5b43b1dfe5d4031ee,0x244357a23153a7f0092b587e658a32cf94343b6d9b5fd771e879d5d,0x26e82a36edf1b6b5ee42806ec702961836366f212003a82cbd5a1c4,0xa156599042f440345e05e2619db025b4fd524f493576d74741ea9a,0x4ed27fb1911c84faff4687fd7e1b074e2c49759de3090f4207f0b8,0x2478847956633523a0506eb020fd4746f8635e29c92c1e79ef2503,0x905ef4f17ff4061bb4a7f243ad1baad414619934d580634019dba2,0x45fb576fc344d560fd881288be0433b9c74955f9a81050de5d1182,0x12932b06ecf14c9ab179de02e21ad6ad65ffaad585b0e6bdad9dd40,0xcabbe6bc4d941000da2620ec0f9cf43beb671d41748d13278c780f,0x15d2f592cb785f00ba2d8bd0faf75f9e135e07b4f3d53f3f9b8010d,0x1ae8f56d7d6c37174784ae4cc692c372773cedfe2887152635feb54,0x1f37cd8b758e8b33525fb3c56a2ba952f4db580dfe5d183bd71c91d,0xf63a4cea2ec9464e6b4b4f4e4d451418f29c672557281546e3db4b,0x277697df00b6e0db1287fdf9214d6c6768f9e6da0f828a2cee81a06,0x2619e857d2b3895ae0468b6d1e1d00f8ff996e2c7322d758dcb5cd5,0x1512392bcfaeb0a277c6a77d25c824673d377ed07b1f18cf999ebb8,0x15f0b22e9f8da96ce810c52b907d90412e9a552b7637a57b5e1d759,0xba0346])
]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem baseCyclePacked8_ok :
    baseCyclePacked8.all (fun p => checkBaseCycle p.1 (unpack532 p.2 p.1)) = true := rfl

private def baseCyclePackedAll : List (ℕ × List ℕ) :=
  baseCyclePacked1 ++ (baseCyclePacked2 ++ (baseCyclePacked3 ++ (baseCyclePacked4 ++ (baseCyclePacked5 ++ (baseCyclePacked6 ++ (baseCyclePacked7 ++ (baseCyclePacked8)))))))

private theorem baseCyclePackedAll_ok :
    ∀ p ∈ baseCyclePackedAll, checkBaseCycle p.1 (unpack532 p.2 p.1) = true := by
  intro p hp
  simp only [baseCyclePackedAll, List.mem_append] at hp
  rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact List.all_eq_true.mp baseCyclePacked1_ok p h1
  · exact List.all_eq_true.mp baseCyclePacked2_ok p h2
  · exact List.all_eq_true.mp baseCyclePacked3_ok p h3
  · exact List.all_eq_true.mp baseCyclePacked4_ok p h4
  · exact List.all_eq_true.mp baseCyclePacked5_ok p h5
  · exact List.all_eq_true.mp baseCyclePacked6_ok p h6
  · exact List.all_eq_true.mp baseCyclePacked7_ok p h7
  · exact List.all_eq_true.mp baseCyclePacked8_ok p h8

def baseCycleList : List (ℕ × List ℕ) :=
  baseCyclePackedAll.map (fun p => (p.1, unpack532 p.2 p.1))

theorem base_cycles_verified : ∀ p ∈ baseCycleList, InvSmall 2 4 3 5 p.1 := by
  intro p hp
  simp only [baseCycleList, List.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩
  exact checkBaseCycle_sound (baseCyclePackedAll_ok q hq)

/-! ### Part 6: Verified Isolated Two-Matching Witnesses (`609` witnesses) -/

structure IsoWitness where
  R : ℕ
  L : ℕ
  z : ℕ
  lo : ℕ
  hi : ℕ
  p : ℕ
  q : ℕ
  s : ℕ
  m1 : List (ℕ × ℕ × ℕ)
  m2 : List (ℕ × ℕ × ℕ)

private structure IsoRaw where
  R : ℕ
  L : ℕ
  z : ℕ
  lo : ℕ
  hi : ℕ
  p : ℕ
  q : ℕ
  s : ℕ
  m1 : List ℕ
  m2 : List ℕ

private def unpackM (cur : ℕ) : List ℕ → List (ℕ × ℕ × ℕ)
  | [] => []
  | v :: rest =>
      let hi := Nat.div v 100
      (cur, hi, Nat.mod v 100) :: unpackM (Nat.add hi 1) rest

private def unpackIso (r : IsoRaw) : IsoWitness :=
  { R := r.R, L := r.L, z := r.z, lo := r.lo, hi := r.hi, p := r.p, q := r.q, s := r.s,
    m1 := match r.m1 with | [] => [(r.L, r.R, r.z)] | xs => unpackM r.L xs,
    m2 := unpackM r.L r.m2 }

def checkIsoCommon (w : IsoWitness) : Bool :=
  Nat.ble 55 w.L && Nat.ble (w.L + 1) w.R &&
  ((w.R - w.L + 1) % 2 == 0) &&
  (w.s == 4 || w.s == 5 || w.s == 6 || w.s == 7) &&
  (w.p * w.p + w.q * w.q == w.z * w.z + w.s * w.s) &&
  Nat.ble w.p w.q &&
  Nat.ble w.L w.lo && Nat.ble w.hi w.R &&
  (w.lo + w.hi == w.z * w.z) &&
  Nat.ble (w.lo + w.s * w.s) (w.p * w.p + 1) &&
  w.m1.any (fun t => t == (w.lo, w.hi, w.z)) &&
  checkBudgetPoint w.R (w.L - 1) w.s

def checkIsoWitnessFast (w : IsoWitness) : Bool :=
  checkIsoCommon w &&
  S1.checkRootMatching w.L w.R w.m1 &&
  S1.checkRootMatching w.L w.R w.m2 &&
  checkWalkRauzy w.L w.R w.m1 w.m2

def checkIsoWitness (w : IsoWitness) : Bool :=
  checkIsoCommon w &&
  S1.checkTwoMatchings w.L w.R w.m1 w.m2

private lemma checkIsoWitnessFast_implies (w : IsoWitness)
    (h : checkIsoWitnessFast w = true) : checkIsoWitness w = true := by
  simp only [checkIsoWitnessFast, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hcom, hm1⟩, hm2⟩, hwalk⟩
  have hcom2 := hcom
  simp only [checkIsoCommon, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at hcom2
  have hLR : w.L + 1 ≤ w.R := hcom2.1.1.1.1.1.1.1.1.1.1.2
  have hev : (w.R - w.L + 1) % 2 = 0 := hcom2.1.1.1.1.1.1.1.1.1.2
  have htwo := checkWalkRauzy_implies_checkTwoMatchings hLR hev hm1 hm2 hwalk
  simp only [checkIsoWitness, Bool.and_eq_true]
  exact ⟨hcom, htwo⟩

set_option maxRecDepth 2000 in
private def isoRaw1 : List IsoRaw := [
⟨209,80,17,80,209,13,13,7,[],[8913,10415,12016,13515,15116,20919]⟩,
⟨212,77,17,77,212,13,13,7,[],[11116,14418,17916,21218]⟩,
⟨222,71,17,71,218,13,13,7,[21817,22221],[10916,13818,14619,18516,21418,22219]⟩,
⟨227,76,17,76,213,13,13,7,[21317,22721],[14915,17219,18820,21119,22720]⟩,
⟨228,77,17,77,212,13,13,7,[21217,22821],[9213,9516,16018,16316,22818]⟩,
⟨230,59,17,59,230,10,15,6,[],[6211,7815,9316,14618,16215,17716,23018]⟩,
⟨278,83,19,83,278,11,16,4,[],[8613,14118,16220,18221,23718,25820,27821]⟩,
⟨284,77,19,77,284,11,16,4,[],[9213,15518,16820,23118,24420,28423]⟩,
⟨285,76,19,76,285,11,16,4,[],[9313,10015,12416,13115,15516,28521]⟩,
⟨287,74,19,74,287,11,16,4,[],[8214,10215,11316,12214,14215,15316,28721]⟩,
⟨292,69,19,69,292,11,17,7,[],[11916,13618,18716,20418,23621,29223]⟩,
⟨297,64,19,64,297,11,17,7,[],[14318,18021,26018,29721]⟩,
⟨303,58,19,58,303,11,17,7,[],[6311,14018,18021,18322,26018,30021,30322]⟩,
⟨306,55,19,55,306,11,17,7,[],[6611,6916,13418,18621,18916,25418,30621]⟩,
⟨316,77,17,77,212,13,13,7,[21217,31623],[14815,16720,23222,25120,31622]⟩,
⟨321,82,17,82,207,13,13,7,[20717,32123],[8713,11918,20421,23618,32121]⟩,
⟨323,60,19,60,301,11,17,7,[30119,32325],[22917,25223,27624,29923,32324]⟩,
⟨325,62,19,62,299,11,17,7,[29919,32525],[8013,8814,10713,11514,32521]⟩,
⟨328,65,19,65,296,11,17,7,[29619,32825],[12316,13218,19116,20018,32823]⟩,
⟨353,176,23,176,353,17,17,7,[],[18519,21221,22822,25521,27122,35325]⟩,
⟨355,174,23,174,355,17,17,7,[],[17820,21421,22122,22620,26221,26922,35525]⟩,
⟨356,173,23,173,356,17,17,7,[],[21922,26424,31122,35624]⟩,
⟨358,55,15,55,170,9,13,5,[17015,35823],[11413,13318,19020,20918,26620,35825]⟩,
⟨359,56,15,56,169,9,13,5,[16915,35923],[9516,16019,20016,26519,35925]⟩,
⟨380,77,23,149,380,17,17,7,[14815,38023],[9213,15518,16820,23118,24420,38025]⟩,
⟨381,78,23,148,381,17,17,7,[14715,38123],[9418,19421,22924,24618,34621,38124]⟩,
⟨386,143,23,143,386,17,17,7,[],[14617,17421,18922,26624,29421,30922,38624]⟩,
⟨438,103,17,103,186,13,13,7,[18617,43825],[17021,23724,27026,33821,40524,43826]⟩,
⟨439,90,23,90,439,17,17,7,[],[13515,15317,17820,19421,22122,24620,26221,28922,43927]⟩,
⟨440,89,23,89,440,17,17,7,[],[13520,26424,31120,44024]⟩,
⟨444,77,27,285,444,18,21,6,[28419,44427],[9213,13120,26824,30720,44424]⟩,
⟨446,83,23,83,446,17,17,7,[],[10617,11718,18220,20617,21718,28220,44627]⟩,
⟨447,82,23,82,447,17,17,7,[],[20717,23321,26224,28225,31326,34224,36225,39326,44729]⟩,
⟨450,79,23,79,450,17,17,7,[],[9013,17021,22524,27026,35021,40524,45026]⟩,
⟨452,173,25,173,452,17,19,5,[],[18819,28724,28826,38724,38826,45229]⟩,
⟨453,172,25,172,453,17,19,5,[],[18919,20821,23222,25121,27522,45327]⟩,
⟨454,55,15,55,170,9,13,5,[17015,45425],[6611,13419,18922,22624,29419,34922,38624,45429]⟩,
⟨455,170,25,170,455,17,19,5,[],[17820,21021,22122,23020,26221,27322,45527]⟩,
⟨456,73,23,73,456,17,17,7,[],[9613,12320,27224,27627,30320,45224,45627]⟩,
⟨458,171,27,271,458,18,21,6,[27021,45827],[21423,21724,31426,35823,36124,45826]⟩,
⟨459,60,25,166,459,17,19,5,[16515,45925],[9116,16419,19616,26919,45927]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw1_ok : isoRaw1.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw2 : List IsoRaw := [
⟨460,165,25,165,460,17,19,5,[],[22722,25624,31922,34824,38027,46029]⟩,
⟨461,68,23,68,461,17,17,7,[],[10018,10419,22322,25618,26019,37922,46129]⟩,
⟨462,67,23,67,462,17,17,7,[],[10213,13419,22522,22624,25819,34922,35024,37827,46229]⟩,
⟨463,96,27,266,463,18,21,6,[26519,46327],[12716,12817,16016,16117,46325]⟩,
⟨464,57,23,65,464,17,17,7,[6411,46423],[10718,21622,26718,37622,46429]⟩,
⟨465,160,25,160,465,17,19,5,[],[26324,31227,41624,46527]⟩,
⟨466,67,25,159,466,17,19,5,[15815,46625],[10213,10617,13718,18220,18617,21718,26220,46627]⟩,
⟨468,69,25,157,468,17,19,5,[15615,46825],[9219,10720,26824,29219,30720,46824]⟩,
⟨469,60,23,60,469,17,17,7,[],[6111,6415,16018,16315,25918,46927]⟩,
⟨470,71,25,155,470,17,19,5,[15415,47025],[17021,20524,27026,37021,40524,47026]⟩,
⟨471,58,23,58,471,17,17,7,[],[6815,15618,16715,25518,36925,47129]⟩,
⟨472,57,23,57,472,17,17,7,[],[6411,9219,10320,26824,29619,30720,47224]⟩,
⟨473,106,27,256,473,18,21,6,[25519,47327],[18317,20822,27524,30022,36724,47329]⟩,
⟨474,55,23,55,474,17,17,7,[],[6611,17021,20124,27026,37421,40524,47426]⟩,
⟨475,108,27,254,475,18,21,6,[25319,47527],[18117,21022,27324,30222,36524,47529]⟩,
⟨476,109,27,253,476,18,21,6,[25219,47627],[18017,21122,27224,30322,36424,47629]⟩,
⟨477,110,27,252,477,18,21,6,[25119,47727],[17917,21222,27124,30422,36324,47729]⟩,
⟨478,111,27,251,478,18,21,6,[25019,47827],[17817,21322,27024,30522,36224,47829]⟩,
⟨479,112,27,250,479,18,21,6,[24919,47927],[17717,21422,26924,30622,36124,47929]⟩,
⟨480,113,27,249,480,18,21,6,[24819,48027],[17617,21522,26824,30722,36024,48029]⟩,
⟨481,114,27,248,481,18,21,6,[24719,48127],[17517,21622,26724,30822,35924,48129]⟩,
⟨482,251,27,251,478,18,21,6,[47827,48231],[30926,35828,36629,42526,47428,48229]⟩,
⟨483,142,25,142,483,17,19,5,[],[14717,26024,30027,31528,42824,46827,48328]⟩,
⟨484,173,23,173,356,17,17,7,[35623,48429],[26821,29926,37628,40726,48428]⟩,
⟨485,118,27,244,485,18,21,6,[24319,48527],[17117,22022,26324,31222,35524,48529]⟩,
⟨486,55,23,55,474,17,17,7,[47423,48631],[17021,18924,27026,38621,40524,48626]⟩,
⟨487,56,23,56,473,17,17,7,[47323,48731],[6511,12320,24124,27627,33420,45224,48727]⟩,
⟨488,57,23,57,472,17,17,7,[47223,48831],[6411,12320,24024,27627,33520,45224,48827]⟩,
⟨490,59,23,59,470,17,17,7,[47023,49031],[6211,12320,23824,27627,33720,45224,49027]⟩,
⟨491,134,25,134,491,17,19,5,[],[15517,37323,40829,43230,46729,49130]⟩,
⟨492,61,23,61,468,17,17,7,[46823,49231],[16415,22722,25624,31922,34824,49229]⟩,
⟨493,132,25,132,493,17,19,5,[],[15717,16419,19620,20319,23520,49327]⟩,
⟨495,130,25,130,495,17,19,5,[],[14218,16619,18120,19418,21819,23320,49527]⟩,
⟨496,129,25,129,496,17,19,5,[],[16017,23122,25224,32322,34424,49629]⟩,
⟨497,58,17,58,231,10,15,6,[23117,49727],[11113,11220,28724,28820,46324,49731]⟩,
⟨498,131,27,231,498,18,21,6,[23019,49827],[15817,23322,25024,32522,34224,49829]⟩,
⟨499,60,17,60,229,10,15,6,[22917,49927],[10913,11420,28524,29020,46124,49931]⟩,
⟨500,69,23,69,460,17,17,7,[46023,50031],[7619,28324,28428,29219,49924,50028]⟩,
⟨501,62,17,62,227,10,15,6,[22717,50127],[10713,11620,28324,29220,45924,50131]⟩,
⟨502,63,17,63,226,10,15,6,[22617,50227],[10613,11720,28224,29320,45824,50231]⟩,
⟨503,122,25,122,503,17,19,5,[],[16717,19319,21822,23823,26524,29022,31023,33724,50329]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw2_ok : isoRaw2.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw3 : List IsoRaw := [
⟨504,121,25,121,504,17,19,5,[],[12718,19620,20318,27220,45627,50431]⟩,
⟨505,66,17,66,223,13,13,7,[22317,50527],[7613,9214,10313,11914,50525]⟩,
⟨506,67,17,67,222,13,13,7,[22217,50627],[10213,12120,27824,29720,45424,50631]⟩,
⟨507,140,27,222,507,18,21,6,[22119,50727],[38923,39229,44830,45129,50730]⟩,
⟨521,104,25,104,521,17,19,5,[],[12115,19420,20522,27820,28922,43927,52131]⟩,
⟨522,103,25,103,522,17,19,5,[],[17021,23724,27026,33821,40524,43826,52231]⟩,
⟨523,102,25,102,523,17,19,5,[],[12315,19220,20722,27620,29122,43727,52331]⟩,
⟨524,101,25,101,524,17,19,5,[],[12415,15922,31626,32429,35922,51626,52429]⟩,
⟨527,98,25,98,527,17,19,5,[],[12715,15918,16419,19618,20119,52727]⟩,
⟨528,97,25,97,528,11,23,5,[],[12815,23219,24324,33226,34324,43226,52831]⟩,
⟨529,200,27,200,529,15,23,5,[],[31126,36429,47626,52929]⟩,
⟨530,199,27,199,530,15,23,5,[],[21423,24524,31426,33023,36124,43026,53031]⟩,
⟨532,93,25,93,532,11,23,5,[],[13215,22819,24724,32826,34724,42826,53231]⟩,
⟨533,92,25,92,533,11,23,5,[],[13315,24823,28026,39523,42726,53331]⟩,
⟨534,91,25,91,534,11,23,5,[],[13415,18120,21822,26520,30222,42627,53431]⟩,
⟨535,90,25,90,535,11,23,5,[],[13515,18020,21922,26420,30322,42527,53531]⟩,
⟨536,89,25,89,536,11,23,5,[],[13615,17920,22022,26320,30422,42427,53631]⟩,
⟨537,88,25,88,537,11,23,5,[],[13715,17820,22122,26220,30522,42327,53731]⟩,
⟨538,87,25,87,538,11,23,5,[],[13815,17720,22222,26120,30622,42227,53831]⟩,
⟨539,86,25,86,539,11,23,5,[],[13915,17620,22322,26020,30722,42127,53931]⟩,
⟨540,85,25,85,540,11,23,5,[],[14015,17520,22422,25920,30822,42027,54031]⟩,
⟨541,84,25,84,541,11,23,5,[],[14115,17420,22522,25820,30922,41927,54131]⟩,
⟨542,83,25,83,542,11,23,5,[],[14215,17320,22622,25720,31022,41827,54231]⟩,
⟨543,82,25,82,543,11,23,5,[],[8713,20117,35627,37230,52727,54330]⟩,
⟨544,81,25,81,544,11,23,5,[],[8813,12421,13122,31626,35221,35922,54426]⟩,
⟨545,80,25,80,545,11,23,5,[],[12718,19621,24418,31321,41527,54531]⟩,
⟨546,79,25,79,546,11,23,5,[],[9013,16522,18224,31827,39322,41024,54627]⟩,
⟨547,78,25,78,547,11,23,5,[],[12821,31226,36321,54726]⟩,
⟨548,77,25,77,548,11,23,5,[],[9213,25924,30028,31629,48324,52428,54029,54833]⟩,
⟨549,76,25,76,549,11,23,5,[],[9313,25924,30128,31629,48224,52428,53929,54933]⟩,
⟨550,75,25,75,550,11,23,5,[],[14118,15020,18221,24918,25820,29021,55029]⟩,
⟨551,74,25,74,551,11,23,5,[],[9513,25924,30328,31629,48024,52428,53729,55133]⟩,
⟨552,73,25,73,552,11,23,5,[],[9613,11621,23124,32428,34421,45924,55228]⟩,
⟨553,72,25,72,553,11,23,5,[],[9713,12421,14022,31626,34321,35922,53526,55333]⟩,
⟨554,71,25,71,554,11,23,5,[],[9813,12421,14122,31626,34221,35922,53426,55433]⟩,
⟨555,70,25,70,555,11,23,5,[],[9913,12421,14222,31626,34121,35922,53326,55533]⟩,
⟨556,69,25,69,556,11,23,5,[],[10013,12421,14322,31626,34021,35922,53226,55633]⟩,
⟨557,68,25,68,557,11,23,5,[],[17122,31227,41622,55727]⟩,
⟨558,79,29,283,558,19,23,7,[28219,55829],[9013,11621,22524,32428,35021,45924,55828]⟩,
⟨559,66,25,66,559,11,23,5,[],[17219,18822,29519,31122,52929,55933]⟩,
⟨560,65,25,65,560,11,23,5,[],[12316,13218,19116,20018,52827,56033]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw3_ok : isoRaw3.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw4 : List IsoRaw := [
⟨561,64,25,64,561,11,23,5,[],[10513,12421,14822,31626,33521,35922,52726,56133]⟩,
⟨562,63,25,63,562,11,23,5,[],[10613,12421,14922,31626,33421,35922,52626,56233]⟩,
⟨563,62,25,62,563,11,23,5,[],[8214,9015,11316,13414,14215,16516,56327]⟩,
⟨564,61,25,61,564,11,23,5,[],[10813,25924,31628,46724,52428,56433]⟩,
⟨565,60,25,60,565,11,23,5,[],[6111,6616,16619,18922,19416,29419,31722,52329,56533]⟩,
⟨566,59,25,59,566,11,23,5,[],[9718,13420,22623,26518,30220,39423,56631]⟩,
⟨567,208,27,208,521,18,21,6,[52127,56733],[23321,26224,28225,31326,34224,36225,39326,56731]⟩,
⟨568,57,25,57,568,11,23,5,[],[23522,24826,42722,44026,52031,56833]⟩,
⟨569,56,25,56,569,11,23,5,[],[17620,18423,22324,34420,35223,39124,56931]⟩,
⟨570,55,25,55,570,11,23,5,[],[17015,20524,27026,37029,40524,47026,57029]⟩,
⟨571,158,27,158,571,15,23,5,[],[20319,23721,26224,28625,31326,33824,36225,38926,57131]⟩,
⟨572,157,27,157,572,15,23,5,[],[21124,36428,41924,57228]⟩,
⟨573,94,29,268,573,19,23,7,[26719,57329],[10015,12416,13115,15516,57327]⟩,
⟨574,143,23,143,386,17,17,7,[38623,57431],[21819,25825,26926,36628,40625,41726,51428,57433]⟩,
⟨636,93,27,93,636,15,23,5,[],[13215,15617,15920,24022,24320,32422,63631]⟩,
⟨637,78,23,78,451,17,17,7,[45123,63733],[10821,31226,33230,36321,56726,58730,63735]⟩,
⟨638,91,27,91,638,15,23,5,[],[17021,22524,27026,35021,40524,45026,63833]⟩,
⟨639,90,27,90,639,15,23,5,[],[26025,36430,53525,63930]⟩,
⟨640,89,27,89,640,15,23,5,[],[27924,29628,48724,50428,58433,64035]⟩,
⟨641,88,27,88,641,15,23,5,[],[21622,22825,26726,39622,40825,44726,64133]⟩,
⟨642,87,27,87,642,15,23,5,[],[13815,21722,23024,26625,34522,35824,39425,44629,64233]⟩,
⟨643,86,27,86,643,15,23,5,[],[13915,14917,16620,23322,25020,31722,64331]⟩,
⟨644,85,27,85,644,15,23,5,[],[10821,31926,33230,35621,56726,58030,64435]⟩,
⟨645,84,27,84,645,15,23,5,[],[8513,10821,32026,33230,35521,56726,57930,64535]⟩,
⟨646,83,27,83,646,15,23,5,[],[20617,24926,31428,42631,46926,53428,64631]⟩,
⟨647,82,27,82,647,15,23,5,[],[8713,10821,32226,33230,35321,56726,57730,64735]⟩,
⟨648,81,27,81,648,15,23,5,[],[8318,24022,24318,40022,44029,64833]⟩,
⟨649,80,27,80,649,15,23,5,[],[31126,36431,59626,64931]⟩,
⟨650,79,27,79,650,15,23,5,[],[9013,10821,32526,33230,35021,56726,57430,65035]⟩,
⟨651,78,27,78,651,15,23,5,[],[9113,10821,32626,33230,34921,56726,57330,65135]⟩,
⟨652,77,27,77,652,15,23,5,[],[11621,21124,32428,36421,45924,57228,65235]⟩,
⟨653,76,27,76,653,15,23,5,[],[9313,10821,32826,33230,34721,56726,57130,65335]⟩,
⟨654,75,27,75,654,15,23,5,[],[9413,25025,36930,37432,53025,64930,65432]⟩,
⟨655,74,27,74,655,15,23,5,[],[15115,19122,29225,33222,43325,65533]⟩,
⟨656,73,27,73,656,15,23,5,[],[9613,15223,24326,37630,43223,52326,65630]⟩,
⟨657,72,27,72,657,15,23,5,[],[10320,29625,32820,52125,56733,65735]⟩,
⟨658,71,27,71,658,15,23,5,[],[10217,18120,18622,21817,29720,30222,65831]⟩,
⟨659,70,27,70,659,15,23,5,[],[8220,11021,31726,33020,35821,56526,65935]⟩,
⟨660,69,27,69,660,15,23,5,[],[10013,12415,15922,31626,32429,35922,51626,52429,56433,66035]⟩,
⟨661,68,27,68,661,15,23,5,[],[8316,17219,18816,27719,56329,66135]⟩,
⟨662,67,27,67,662,15,23,5,[],[14118,14220,18221,25718,25820,29821,66231]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw4_ok : isoRaw4.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw5 : List IsoRaw := [
⟨663,66,27,66,663,15,23,5,[],[10313,12115,12620,25023,27326,27820,40223,42526,66333]⟩,
⟨664,65,27,65,664,15,23,5,[],[15920,24024,33520,41624,42429,66433]⟩,
⟨665,64,27,64,665,15,23,5,[],[10513,11915,15922,31126,32429,36422,51626,52929,55933,66535]⟩,
⟨666,63,27,63,666,15,23,5,[],[10613,11815,17021,25324,27026,32221,40524,42226,66633]⟩,
⟨667,62,27,62,667,15,23,5,[],[14421,29626,37921,53126,55733,66735]⟩,
⟨668,61,27,61,668,15,23,5,[],[10813,11615,15922,30826,32429,36722,51626,53229,55633,66835]⟩,
⟨669,60,27,60,669,15,23,5,[],[10913,11515,21622,25625,26726,36822,40825,41926,66933]⟩,
⟨670,59,27,59,670,15,23,5,[],[11013,11415,11621,24924,32428,32621,45924,53428,55433,67035]⟩,
⟨671,58,27,58,671,15,23,5,[],[16715,19319,24326,41730,43233,48226,65630,67133]⟩,
⟨672,57,27,57,672,15,23,5,[],[6411,15920,24024,33520,41624,67233]⟩,
⟨673,56,27,56,673,15,23,5,[],[15118,17221,26818,28921,55129,67335]⟩,
⟨674,55,27,55,674,15,23,5,[],[5617,16520,23224,23417,34320,41024,55031,67435]⟩,
⟨675,116,23,116,413,17,17,7,[41323,67533],[17317,20025,22426,42430,45125,47526,67530]⟩,
⟨676,413,33,413,676,23,24,4,[],[47932,54434,61132,67634]⟩,
⟨677,182,27,182,547,15,23,5,[54727,67735],[24626,34629,42932,49426,59429,67732]⟩,
⟨678,163,29,163,678,19,23,7,[],[19819,25425,35728,37030,42625,52928,54230,54633,67835]⟩,
⟨679,162,29,162,679,19,23,7,[],[17820,20221,22122,23820,26221,28122,67931]⟩,
⟨680,81,25,81,544,11,23,5,[54425,68035],[20817,26724,30826,36724,40826,68033]⟩,
⟨681,122,23,122,407,17,17,7,[40723,68133],[16717,20025,21826,42430,45725,47526,68130]⟩,
⟨682,123,23,123,406,17,17,7,[40623,68233],[16617,20025,21726,42430,45825,47526,68230]⟩,
⟨683,158,29,158,683,19,23,7,[],[28321,41630,47233,48334,61630,67233,68334]⟩,
⟨684,157,29,157,684,19,23,7,[],[20419,27124,30426,37124,40426,68433]⟩,
⟨685,156,29,156,685,19,23,7,[],[20519,27024,30526,37024,40526,68333,68537]⟩,
⟨686,155,29,155,686,19,23,7,[],[20619,26924,30626,36924,40626,68233,68637]⟩,
⟨687,154,29,154,687,19,23,7,[],[20719,26824,30726,36824,40726,68133,68737]⟩,
⟨688,153,29,153,688,19,23,7,[],[20819,26724,30826,36724,40826,68033,68837]⟩,
⟨689,152,29,152,689,19,23,7,[],[20919,26624,30926,36624,40926,67933,68937]⟩,
⟨690,151,29,151,690,19,23,7,[],[21019,26524,31026,36524,41026,67833,69037]⟩,
⟨691,150,29,150,691,19,23,7,[],[21119,26424,31126,36424,41126,67733,69137]⟩,
⟨692,149,29,149,692,19,23,7,[],[21219,26324,31226,36324,41226,67633,69237]⟩,
⟨693,148,29,148,693,19,23,7,[],[21319,26224,31326,36224,41326,67533,69337]⟩,
⟨694,147,29,147,694,19,23,7,[],[21419,26124,31426,36124,41426,67433,69437]⟩,
⟨695,146,29,146,695,19,23,7,[],[20425,42030,47925,69530]⟩,
⟨696,145,29,145,696,19,23,7,[],[21619,25924,31626,35924,41626,67233,69637]⟩,
⟨697,144,29,144,697,19,23,7,[],[21719,25824,31726,35824,41726,67133,69737]⟩,
⟨698,143,29,143,698,19,23,7,[],[21722,23424,26625,34122,35824,39025,69833]⟩,
⟨699,142,29,142,699,19,23,7,[],[21919,25624,31926,35624,41926,66933,69937]⟩,
⟨700,141,29,141,700,19,23,7,[],[22724,34828,43524,55628,66835,70037]⟩,
⟨701,140,29,140,701,19,23,7,[],[20322,28025,34422,42125,66733,70137]⟩,
⟨702,139,29,139,702,19,23,7,[],[22219,25324,32226,35324,42226,66633,70237]⟩,
⟨703,138,29,138,703,19,23,7,[],[22319,25224,32326,35224,42326,66533,70337]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw5_ok : isoRaw5.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw6 : List IsoRaw := [
⟨704,137,29,137,704,19,23,7,[],[22419,25124,32426,35124,42426,66433,70437]⟩,
⟨705,136,29,136,705,19,23,7,[],[28724,28827,44024,44127,51931,70535]⟩,
⟨706,135,29,135,706,19,23,7,[],[22619,24924,32626,34924,42626,66233,70637]⟩,
⟨707,134,29,134,707,19,23,7,[],[22719,24824,32726,34824,42726,66133,70737]⟩,
⟨708,133,29,133,708,19,23,7,[],[15617,24326,38030,43233,51926,65630,70833]⟩,
⟨709,252,31,252,709,19,25,5,[],[27723,29625,32826,34725,37926,70933]⟩,
⟨710,71,27,71,658,15,23,5,[65827,71037],[9813,26924,30628,47724,51428,71035]⟩,
⟨711,250,31,250,711,19,25,5,[],[26224,29825,31326,32624,36225,37726,71133]⟩,
⟨712,129,29,129,712,19,23,7,[],[16017,20019,44330,45634,69930,71234]⟩,
⟨713,74,27,74,655,15,23,5,[65527,71337],[9513,27224,30328,48024,51128,71335]⟩,
⟨714,127,29,127,714,19,23,7,[],[16522,21824,31827,35722,41024,51027,71435]⟩,
⟨715,126,29,126,715,19,23,7,[],[30827,42032,60327,71532]⟩,
⟨716,125,29,125,716,19,23,7,[],[32726,34830,55126,57230,65235,71637]⟩,
⟨717,78,27,78,651,15,23,5,[65127,71737],[9113,27624,29928,48424,50728,71735]⟩,
⟨788,173,31,173,788,19,25,5,[],[21922,26424,31122,35624,73233,78839]⟩,
⟨789,172,31,172,789,19,25,5,[],[45325,47832,51833,54534,57032,61033,63734,73137,78939]⟩,
⟨790,171,31,171,790,19,25,5,[],[19019,26126,41430,48526,63830,73037,79039]⟩,
⟨791,298,33,298,791,23,24,4,[],[31026,35027,36528,37826,41827,43328,79135]⟩,
⟨792,169,31,169,792,19,25,5,[],[19219,23627,36330,49234,53627,66330,79234]⟩,
⟨793,114,29,114,727,19,23,7,[72729,79339],[17517,41530,43134,48435,72430,74034,79335]⟩,
⟨794,167,31,167,794,19,25,5,[],[25425,32528,37030,45825,52928,57430,79437]⟩,
⟨795,116,29,116,725,19,23,7,[72529,79539],[17317,41530,42934,48435,72630,74034,79535]⟩,
⟨875,86,31,86,875,19,25,5,[],[11621,22024,32428,35521,45924,56328,80537,87541]⟩,
⟨876,85,31,85,876,19,25,5,[],[41930,48036,81530,87636]⟩,
⟨877,84,31,84,877,19,25,5,[],[11621,21824,32428,35721,45924,56528,80337,87741]⟩,
⟨907,182,33,182,907,15,30,6,[],[25921,34728,43631,52428,61331,90739]⟩,
⟨908,181,33,181,908,15,30,6,[],[26021,38330,51634,63930,77234,90841]⟩,
⟨909,180,33,180,909,15,30,6,[],[18119,25921,31530,58435,64030,90935]⟩,
⟨910,179,33,179,910,15,30,6,[],[18219,25821,38530,51434,64130,77034,91041]⟩,
⟨911,178,33,178,911,15,30,6,[],[18319,18424,39128,39224,59928,76937,91141]⟩,
⟨912,177,33,177,912,15,30,6,[],[26421,36025,41530,48432,53930,60832,91239]⟩,
⟨913,176,33,176,913,15,30,6,[],[18519,23428,24229,54934,59828,60629,91334]⟩,
⟨914,175,33,175,914,15,30,6,[],[18619,25421,38930,51034,64530,76634,91441]⟩,
⟨915,174,33,174,915,15,30,6,[],[35523,42030,47932,54430,60332,76537,91541]⟩,
⟨916,173,33,173,916,15,30,6,[],[23928,54434,61128,91634]⟩,
⟨917,172,33,172,917,15,30,6,[],[26921,31026,32227,36528,40626,41827,46128,76335,91741]⟩,
⟨918,171,33,171,918,15,30,6,[],[19019,22928,30630,55435,59328,67030,91835]⟩,
⟨919,170,33,170,919,15,30,6,[],[26427,46432,55927,75932,76139,91941]⟩,
⟨920,169,33,169,920,15,30,6,[],[19219,34330,44834,55637,70730,81234,92037]⟩,
⟨921,168,33,168,921,15,30,6,[],[19319,24721,25226,30027,42330,42826,47627,59930,92139]⟩,
⟨922,167,33,167,922,15,30,6,[],[19419,24621,36128,36230,42231,53728,53830,59831,92239]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw6_ok : isoRaw6.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw7 : List IsoRaw := [
⟨923,166,33,166,923,15,30,6,[],[19519,22428,37231,55936,58828,73631,92336]⟩,
⟨924,165,33,165,924,15,30,6,[],[19619,24421,39930,50034,65530,75634,92441]⟩,
⟨925,164,33,164,925,15,30,6,[],[25924,31627,41224,46927,75535,92541]⟩,
⟨926,163,33,163,926,15,30,6,[],[27821,34625,41031,54134,55036,61431,74534,75436,92641]⟩,
⟨927,162,33,162,927,15,30,6,[],[19919,24121,40230,49734,65830,75334,92741]⟩,
⟨928,161,33,161,928,15,30,6,[],[19924,36828,37631,41524,58428,59231,92839]⟩,
⟨929,160,33,160,929,15,30,6,[],[20119,23921,43932,58437,78432,92937]⟩,
⟨930,159,33,159,930,15,30,6,[],[46625,54134,60636,61437,68934,75436,76237,91841,93043]⟩,
⟨931,158,33,158,931,15,30,6,[],[20319,23522,24823,28022,29323,93135]⟩,
⟨932,157,33,157,932,15,30,6,[],[20419,41530,46034,48435,69530,74034,76435,91641,93243]⟩,
⟨933,156,33,156,933,15,30,6,[],[20519,23521,40830,49134,66430,74734,93341]⟩,
⟨934,155,33,155,934,15,30,6,[],[20524,25426,37029,42124,47026,58629,93439]⟩,
⟨935,154,33,154,935,15,30,6,[],[17820,19421,22122,24620,26221,28922,93535]⟩,
⟨936,153,33,153,936,15,30,6,[],[16023,19924,36828,37623,41524,58428,93639]⟩,
⟨937,152,33,152,937,15,30,6,[],[27124,30427,42424,45727,91137,93743]⟩,
⟨938,151,33,151,938,15,30,6,[],[21019,23021,41330,48634,66930,74234,93841]⟩,
⟨939,150,33,150,939,15,30,6,[],[21119,22921,24624,32926,34624,42926,93937]⟩,
⟨940,149,33,149,940,15,30,6,[],[16720,23222,25120,31622,90835,94043]⟩,
⟨941,284,35,284,941,25,25,5,[],[34125,39932,61336,62439,68232,89636,90739,94143]⟩,
⟨942,147,33,147,942,15,30,6,[],[21419,22621,41730,48234,67330,73834,94241]⟩,
⟨943,146,33,146,943,15,30,6,[],[38029,46034,69529,77534,90541,94343]⟩,
⟨944,145,33,145,944,15,30,6,[],[18425,41930,44034,48025,71530,73634,94441]⟩,
⟨945,144,33,144,945,15,30,6,[],[14517,18425,42030,44034,47925,71530,73534,94541]⟩,
⟨946,143,33,143,946,15,30,6,[],[14617,18425,42130,44034,47825,71530,73434,94641]⟩,
⟨947,142,33,142,947,15,30,6,[],[14717,18425,42230,44034,47725,71530,73334,94741]⟩,
⟨948,141,33,141,948,15,30,6,[],[14817,21219,28429,39532,55636,62829,73932,90036,94843]⟩,
⟨949,140,33,140,949,15,30,6,[],[14024,29227,43532,43624,58827,73132,94941]⟩,
⟨950,139,33,139,950,15,30,6,[],[15017,21019,26124,31026,31427,36524,41426,41827,95037]⟩,
⟨951,138,33,138,951,15,30,6,[],[22319,36028,40031,42332,56028,60031,62332,89739,95143]⟩,
⟨952,137,33,137,952,15,30,6,[],[19225,29528,43232,48825,59128,72832,95241]⟩,
⟨953,136,33,136,953,15,30,6,[],[15317,18425,42830,44034,47125,71530,72734,95341]⟩,
⟨954,135,33,135,954,15,30,6,[],[14524,23426,43031,44124,53026,72631,95441]⟩,
⟨955,134,33,134,955,15,30,6,[],[24626,29829,42932,54226,59429,72532,95541]⟩,
⟨956,133,33,133,956,15,30,6,[],[15617,18425,43130,44034,46825,71530,72434,95641]⟩,
⟨957,132,33,132,957,15,30,6,[],[39723,44329,57234,58336,71234,72336,95741]⟩,
⟨958,131,33,131,958,15,30,6,[],[16526,47832,51037,54526,85832,89037,95843]⟩,
⟨959,130,33,130,959,15,30,6,[],[15024,17825,42530,44624,47425,72130,95941]⟩,
⟨960,129,33,129,960,15,30,6,[],[40023,44029,57534,58036,71534,72036,96041]⟩,
⟨961,128,33,128,961,15,30,6,[],[13220,16821,26724,27220,30821,40724,96137]⟩,
⟨962,127,33,127,962,15,30,6,[],[21722,21824,26625,35722,35824,40625,96237]⟩,
⟨963,126,33,126,963,15,30,6,[],[17026,41031,50536,55026,79031,88536,96343]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw7_ok : isoRaw7.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw8 : List IsoRaw := [
⟨1009,80,33,80,1009,15,30,6,[],[8913,19917,31126,36429,47626,52929,83937,100943]⟩,
⟨1010,79,33,79,1010,15,30,6,[],[10922,17024,37429,40522,46624,67029,101041]⟩,
⟨1011,78,33,78,1011,15,30,6,[],[20224,23027,37330,49824,52627,66930,101141]⟩,
⟨1012,77,33,77,1012,15,30,6,[],[25924,28428,31629,49924,52428,55629,66835,101241]⟩,
⟨1013,76,33,76,1013,15,30,6,[],[25924,28328,31629,50024,52428,55729,66735,101341]⟩,
⟨1014,75,33,75,1014,15,30,6,[],[9413,40631,42936,55438,86631,88936,101438]⟩,
⟨1015,74,33,74,1015,15,30,6,[],[11422,11823,36928,41022,41423,66528,101541]⟩,
⟨1016,73,33,73,1016,15,30,6,[],[11122,37228,41122,67228,100841,101645]⟩,
⟨1017,72,33,72,1017,15,30,6,[],[9713,28829,55236,74329,100736,101745]⟩,
⟨1018,71,33,71,1018,15,30,6,[],[12524,39430,45035,50524,77430,83035,101843]⟩,
⟨1019,70,33,70,1019,15,30,6,[],[13621,30426,37121,53926,82937,101943]⟩,
⟨1020,69,33,69,1020,15,30,6,[],[10013,26724,30828,47524,51628,100439,102045]⟩,
⟨1021,68,33,68,1021,15,30,6,[],[10720,29225,33220,51725,100339,102145]⟩,
⟨1022,67,33,67,1022,15,30,6,[],[9118,22622,23225,25718,39222,39825,82635,102243]⟩,
⟨1046,179,35,179,1046,17,31,5,[],[18526,28628,49033,49726,59828,80233,104643]⟩,
⟨1047,178,35,178,1047,17,31,5,[],[18319,25721,49432,52936,76632,80136,104743]⟩,
⟨1048,177,35,177,1048,17,31,5,[],[18419,23627,35530,49234,54427,66330,80034,104843]⟩,
⟨1049,176,35,176,1049,17,31,5,[],[18519,53834,55039,61740,97034,98239,104940]⟩,
⟨1050,175,35,175,1050,17,31,5,[],[20928,54634,57439,60928,94634,97439,105045]⟩,
⟨1051,174,35,174,1051,17,31,5,[],[19026,22627,48532,50226,53827,79732,105143]⟩,
⟨1052,173,35,173,1052,17,31,5,[],[18819,23627,35930,49234,54027,66330,79634,105243]⟩,
⟨1053,172,35,172,1053,17,31,5,[],[18919,25121,31626,35928,42426,46728,105339]⟩,
⟨1054,171,35,171,1054,17,31,5,[],[21023,31726,31828,35823,46526,46628,105439]⟩,
⟨1055,170,35,170,1055,17,31,5,[],[19119,23627,36230,49234,53727,66330,79334,105543]⟩,
⟨1056,169,35,169,1056,17,31,5,[],[19219,39932,46436,62439,83132,89636,105639]⟩,
⟨1057,168,35,168,1057,17,31,5,[],[16822,21223,31526,31622,36023,46326,105739]⟩,
⟨1058,167,35,167,1058,17,31,5,[],[26124,26626,31427,40924,41426,46227,105839]⟩,
⟨1059,166,35,166,1059,17,31,5,[],[19519,27230,38433,62738,70430,81633,105938]⟩,
⟨1060,165,35,165,1060,17,31,5,[],[20324,37228,41124,58028,78837,106043]⟩,
⟨1061,164,35,164,1061,17,31,5,[],[22726,44831,51226,73331,78739,106143]⟩,
⟨1062,163,35,163,1062,17,31,5,[],[16627,33330,56236,56627,73330,96236,106245]⟩,
⟨1063,162,35,162,1063,17,31,5,[],[19919,24121,24626,40629,42932,43426,59429,61732,106341]⟩,
⟨1064,161,35,161,1064,17,31,5,[],[20019,26730,45634,63239,69930,88834,106439]⟩,
⟨1065,160,35,160,1065,17,31,5,[],[22428,33631,55936,62428,73631,95936,106545]⟩,
⟨1066,159,35,159,1066,17,31,5,[],[18425,43330,44034,46625,71530,72234,95841,106645]⟩,
⟨1067,158,35,158,1067,17,31,5,[],[22829,61236,68329,106736]⟩,
⟨1068,157,35,157,1068,17,31,5,[],[28429,33932,55636,68429,73932,95636,106845]⟩,
⟨1069,156,35,156,1069,17,31,5,[],[23526,44031,52026,72531,95541,106945]⟩,
⟨1070,155,35,155,1070,17,31,5,[],[18425,42930,44034,47025,71530,72634,95441,107045]⟩,
⟨1071,154,35,154,1071,17,31,5,[],[28027,44832,57527,74332,77739,107143]⟩,
⟨1072,153,35,153,1072,17,31,5,[],[25928,52434,63128,89634,95243,107245]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw8_ok : isoRaw8.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw9 : List IsoRaw := [
⟨1073,152,35,152,1073,17,31,5,[],[20919,34630,39833,55336,69030,74233,89736,95143,107345]⟩,
⟨1074,151,35,151,1074,17,31,5,[],[17827,20528,55034,57827,60528,95034,107445]⟩,
⟨1075,150,35,150,1075,17,31,5,[],[18425,42430,44034,47525,71530,73134,94941,107545]⟩,
⟨1076,149,35,149,1076,17,31,5,[],[18425,42330,44034,47625,71530,73234,94841,107645]⟩,
⟨1077,148,35,148,1077,17,31,5,[],[18425,42230,44034,47725,71530,73334,94741,107745]⟩,
⟨1078,147,35,147,1078,17,31,5,[],[21419,23627,38530,49234,51427,66330,77034,107843]⟩,
⟨1079,146,35,146,1079,17,31,5,[],[18425,42030,44034,47925,71530,73534,94541,107945]⟩,
⟨1080,145,35,145,1080,17,31,5,[],[18425,41930,44034,48025,71530,73634,94441,108045]⟩,
⟨1081,144,35,144,1081,17,31,5,[],[28730,61237,75630,108137]⟩,
⟨1082,143,35,143,1082,17,31,5,[],[18425,41730,44034,48225,71530,73834,94241,108245]⟩,
⟨1083,142,35,142,1083,17,31,5,[],[18425,41630,44034,48325,71530,73934,94141,108345]⟩,
⟨1084,141,35,141,1084,17,31,5,[],[18425,41530,44034,48425,71530,74034,94041,108445]⟩,
⟨1085,140,35,140,1085,17,31,5,[],[18425,41430,44034,48525,71530,74134,93941,108545]⟩,
⟨1086,139,35,139,1086,17,31,5,[],[18425,41330,44034,48625,71530,74234,93841,108645]⟩,
⟨1087,138,35,138,1087,17,31,5,[],[24423,28426,39123,43126,93737,108745]⟩,
⟨1171,198,37,198,1171,26,27,6,[],[24326,42130,43233,47826,65630,66733,85339,117145]⟩,
⟨1172,197,37,197,1172,26,27,6,[],[30730,59236,70330,98836,103645,117247]⟩,
⟨1173,196,37,196,1173,26,27,6,[],[24326,41930,43233,48026,65630,66933,85139,117345]⟩,
⟨1174,195,37,195,1174,26,27,6,[],[24326,41830,43233,48126,65630,67033,85039,117445]⟩,
⟨1175,194,37,194,1175,26,27,6,[],[24326,41730,43233,48226,65630,67133,84939,117545]⟩,
⟨1176,193,37,193,1176,26,27,6,[],[24326,41630,43233,48326,65630,67233,84839,117645]⟩,
⟨1177,192,37,192,1177,26,27,6,[],[24326,41530,43233,48426,65630,67333,84739,117745]⟩,
⟨1178,191,37,191,1178,26,27,6,[],[25021,46633,60538,62240,83833,97738,99440,103045,117847]⟩,
⟨1179,190,37,190,1179,26,27,6,[],[19225,34828,43232,43525,59128,67532,84539,117945]⟩,
⟨1180,189,37,189,1180,26,27,6,[],[19225,34728,43232,43625,59128,67632,84439,118045]⟩,
⟨1181,188,37,188,1181,26,27,6,[],[33932,68439,83632,118139]⟩,
⟨1182,187,37,187,1182,26,27,6,[],[25421,29229,31330,54834,58629,60730,84234,118245]⟩,
⟨1183,186,37,186,1183,26,27,6,[],[24326,40930,43233,49026,65630,67933,84139,118345]⟩,
⟨1184,185,37,185,1184,26,27,6,[],[19225,34328,43232,44025,59128,68032,84039,118445]⟩,
⟨1185,184,37,184,1185,26,27,6,[],[19225,34228,43232,44125,59128,68132,83939,118545]⟩,
⟨1186,183,37,183,1186,26,27,6,[],[19225,34128,43232,44225,59128,68232,83839,118645]⟩,
⟨1187,182,37,182,1187,26,27,6,[],[28425,34028,44325,49928,102139,118747]⟩,
⟨1188,181,37,181,1188,26,27,6,[],[19225,33928,43232,44425,59128,68432,83639,118845]⟩,
⟨1189,180,37,180,1189,26,27,6,[],[39530,50435,72030,82935,101943,118947]⟩,
⟨1190,179,37,179,1190,26,27,6,[],[19225,33728,43232,44625,59128,68632,83439,119045]⟩,
⟨1191,178,37,178,1191,26,27,6,[],[19225,33628,43232,44725,59128,68732,83339,119145]⟩,
⟨1192,177,37,177,1192,26,27,6,[],[18419,25621,57136,72442,103936,119242]⟩,
⟨1193,176,37,176,1193,26,27,6,[],[19225,33428,43232,44925,59128,68932,83139,119345]⟩,
⟨1194,175,37,175,1194,26,27,6,[],[19225,33328,43232,45025,59128,69032,83039,119445]⟩,
⟨1195,174,37,174,1195,26,27,6,[],[19225,33228,43232,45125,59128,69132,82939,119545]⟩,
⟨1196,173,37,173,1196,26,27,6,[],[17526,39630,50035,50326,72430,82835,119645]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw9_ok : isoRaw9.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw10 : List IsoRaw := [
⟨1197,172,37,172,1197,26,27,6,[],[19225,33028,43232,45325,59128,69332,82739,119745]⟩,
⟨1198,171,37,171,1198,26,27,6,[],[19225,32928,43232,45425,59128,69432,82639,119845]⟩,
⟨1199,170,37,170,1199,26,27,6,[],[19225,32828,43232,45525,59128,69532,82539,119945]⟩,
⟨1200,169,37,169,1200,26,27,6,[],[24326,39230,43233,50726,65630,69633,82439,120045]⟩,
⟨1201,168,37,168,1201,26,27,6,[],[18026,33229,49534,50826,66029,82334,120145]⟩,
⟨1202,167,37,167,1202,26,27,6,[],[19225,32528,43232,45825,59128,69832,82239,120245]⟩,
⟨1203,166,37,166,1203,26,27,6,[],[24326,38930,43233,51026,65630,69933,82139,120345]⟩,
⟨1204,165,37,165,1204,26,27,6,[],[23627,33530,49234,56427,66330,82034,120445]⟩,
⟨1205,164,37,164,1205,26,27,6,[],[19225,32228,43232,46125,59128,70132,81939,120545]⟩,
⟨1206,163,37,163,1206,26,27,6,[],[35029,47734,49036,67829,80534,81836,120645]⟩,
⟨1207,162,37,162,1207,26,27,6,[],[46431,49636,79931,83136,119345,120749]⟩,
⟨1208,161,37,161,1208,26,27,6,[],[19225,31928,43232,46425,59128,70432,81639,120845]⟩,
⟨1209,160,37,160,1209,26,27,6,[],[24326,38330,43233,51626,65630,70533,81539,120945]⟩,
⟨1210,159,37,159,1210,26,27,6,[],[24326,38230,43233,51726,65630,70633,81439,121045]⟩,
⟨1211,158,37,158,1211,26,27,6,[],[19026,21027,48532,51826,53827,81332,121145]⟩,
⟨1212,157,37,157,1212,26,27,6,[],[19225,31528,43232,46825,59128,70832,81239,121245]⟩,
⟨1213,156,37,156,1213,26,27,6,[],[19225,31428,43232,46925,59128,70932,81139,121345]⟩,
⟨1214,155,37,155,1214,26,27,6,[],[24326,37830,43233,52126,65630,71033,81039,121445]⟩,
⟨1215,154,37,154,1215,26,27,6,[],[24326,37730,43233,52226,65630,71133,80939,121545]⟩,
⟨1216,153,37,153,1216,26,27,6,[],[24326,37630,43233,52326,65630,71233,80839,121645]⟩,
⟨1217,152,37,152,1217,26,27,6,[],[19225,31028,43232,47325,59128,71332,80739,121745]⟩,
⟨1218,151,37,151,1218,26,27,6,[],[19225,30928,43232,47425,59128,71432,80639,121845]⟩,
⟨1219,150,37,150,1219,26,27,6,[],[19225,30828,43232,47525,59128,71532,80539,121945]⟩,
⟨1220,149,37,149,1220,26,27,6,[],[24326,37230,43233,52726,65630,71633,80439,122045]⟩,
⟨1221,148,37,148,1221,26,27,6,[],[24326,43231,52826,71731,80339,122145]⟩,
⟨1222,147,37,147,1222,26,27,6,[],[19225,30528,43232,47825,59128,71832,80239,122245]⟩,
⟨1223,146,37,146,1223,26,27,6,[],[54035,68442,107935,122342]⟩,
⟨1224,145,37,145,1224,13,35,5,[],[19225,30328,43232,48025,59128,72032,80039,122445]⟩,
⟨1225,144,37,144,1225,13,35,5,[],[19225,30228,43232,48125,59128,72132,79939,122545]⟩,
⟨1226,143,37,143,1226,13,35,5,[],[16627,31330,56236,58627,73330,98236,122647]⟩,
⟨1227,142,37,142,1227,13,35,5,[],[24326,36530,43233,53426,65630,72333,79739,122745]⟩,
⟨1228,141,37,141,1228,13,35,5,[],[21530,68438,75930,122838]⟩,
⟨1229,140,37,140,1229,13,35,5,[],[34030,46435,55938,76030,88435,97938,122947]⟩,
⟨1230,139,37,139,1230,13,35,5,[],[18629,59336,65442,70229,110936,117042,123049]⟩,
⟨1231,138,37,138,1231,13,35,5,[],[19225,29628,43232,48725,59128,72732,79339,123145]⟩,
⟨1232,137,37,137,1232,13,35,5,[],[28429,31932,55636,70429,73932,97636,123247]⟩,
⟨1233,136,37,136,1233,13,35,5,[],[24326,35930,43233,54026,65630,72933,79139,123345]⟩,
⟨1234,135,37,135,1234,13,35,5,[],[22928,25030,55435,64928,67030,97435,123447]⟩,
⟨1235,134,37,134,1235,13,35,5,[],[25229,58836,70729,104336,116547,123549]⟩,
⟨1236,133,37,133,1236,13,35,5,[],[23524,34028,44324,54828,97239,123647]⟩,
⟨1237,132,37,132,1237,13,35,5,[],[61136,68443,116436,123743]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw10_ok : isoRaw10.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw11 : List IsoRaw := [
⟨1238,131,37,131,1238,13,35,5,[],[17827,18528,55034,59827,60528,97034,123847]⟩,
⟨1239,130,37,130,1239,13,35,5,[],[19225,28828,43232,49525,59128,73532,78539,123945]⟩,
⟨1240,129,37,129,1240,13,35,5,[],[24326,35230,43233,54726,65630,73633,78439,124045]⟩,
⟨1241,128,37,128,1241,13,35,5,[],[35128,43233,65628,73733,78339,124145]⟩,
⟨1242,127,37,127,1242,13,35,5,[],[25730,52236,64241,77330,103836,115841,124249]⟩,
⟨1243,126,37,126,1243,13,35,5,[],[24326,34930,43233,55026,65630,73933,78139,124345]⟩,
⟨1244,125,37,125,1244,13,35,5,[],[28728,49634,65928,86834,115645,124449]⟩,
⟨1245,124,37,124,1245,13,35,5,[],[19225,28228,43232,50125,59128,74132,77939,124545]⟩,
⟨1340,181,39,181,1340,27,29,7,[],[41530,43634,48435,71930,74034,78835,106043,134049]⟩,
⟨1341,180,39,180,1341,27,29,7,[],[18030,50435,71942,72030,104435,125942,134151]⟩,
⟨1342,179,39,179,1342,27,29,7,[],[27629,49334,56438,66229,87934,95038,125847,134251]⟩,
⟨1343,178,39,178,1343,27,29,7,[],[30031,66038,78331,114338,125749,134351]⟩,
⟨1344,177,39,177,1344,27,29,7,[],[19124,38428,39924,59228,125643,134451]⟩,
⟨1345,176,39,176,1345,27,29,7,[],[41530,43134,48435,72430,74034,79335,105543,134549]⟩,
⟨1346,175,39,175,1346,27,29,7,[],[24631,50936,71442,78631,104936,125442,134651]⟩,
⟨1347,174,39,174,1347,27,29,7,[],[27629,48834,56438,66729,87934,95538,125347,134751]⟩,
⟨1446,75,39,75,1446,27,29,7,[],[21928,31432,56437,70928,80432,105437,115447,144651]⟩,
⟨1447,74,39,74,1447,27,29,7,[],[40431,55638,88731,103938,136149,144753]⟩,
⟨1448,73,39,73,1448,27,29,7,[],[21928,31232,56437,71128,80432,105637,115247,144851]⟩,
⟨1449,72,39,72,1449,27,29,7,[],[12728,65637,71228,124137,135951,144953]⟩,
⟨1450,71,39,71,1450,27,29,7,[],[24631,40536,71442,89031,104936,135842,145053]⟩,
⟨1451,70,39,70,1451,27,29,7,[],[21928,30932,56437,71428,80432,105937,114947,145151]⟩,
⟨1452,69,39,69,1452,27,29,7,[],[18730,32434,71241,83130,96834,135641,145253]⟩,
⟨1453,68,39,68,1453,27,29,7,[],[39534,76043,108834,145343]⟩,
⟨1459,62,39,62,1459,27,29,7,[],[45034,58641,70544,109434,123041,134944,145953]⟩,
⟨1460,61,39,61,1460,27,29,7,[],[13930,76040,83930,146040]⟩,
⟨1461,60,39,60,1461,27,29,7,[],[20326,47233,61626,88533,113945,146151]⟩,
⟨1467,214,41,214,1467,19,37,7,[],[22721,75240,83647,84748,137240,145647,146748]⟩,
⟨1468,213,41,213,1468,19,37,7,[],[22821,24033,29534,84842,86033,91534,146842]⟩,
⟨1469,212,41,212,1469,19,37,7,[],[22921,23428,28629,54934,55428,60629,86934,133947,146953]⟩,
⟨1470,211,41,211,1470,19,37,7,[],[23021,34930,35432,55035,66930,67432,87035,133847,147053]⟩,
⟨1471,210,41,210,1471,19,37,7,[],[21428,51433,56938,57428,87433,92938,147149]⟩,
⟨1472,209,41,209,1472,19,37,7,[],[33528,44832,57528,68832,133645,147253]⟩,
⟨1473,208,41,208,1473,19,37,7,[],[47132,55237,81632,89737,112745,147351]⟩,
⟨1474,207,41,207,1474,19,37,7,[],[23421,24427,28928,48432,49427,53928,73432,147447]⟩,
⟨1475,206,41,206,1475,19,37,7,[],[42031,54036,75531,87536,133347,147553]⟩,
⟨1476,205,41,205,1476,19,37,7,[],[23621,28429,41932,55636,60429,73932,87636,133247,147653]⟩,
⟨1477,204,41,204,1477,19,37,7,[],[23721,24427,29228,48432,49127,53928,73132,147747]⟩,
⟨1478,203,41,203,1478,19,37,7,[],[67738,69444,76645,124138,125844,133045,147853]⟩,
⟨1479,202,41,202,1479,19,37,7,[],[20224,35427,37330,37424,52627,54530,147945]⟩,
⟨1480,201,41,201,1480,19,37,7,[],[51134,64440,95534,108840,112047,148051]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw11_ok : isoRaw11.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw12 : List IsoRaw := [
⟨1481,200,41,200,1481,19,37,7,[],[34030,52435,55938,70030,88435,91938,148149]⟩,
⟨1482,199,41,199,1482,19,37,7,[],[20524,29826,37029,37724,47026,54229,148245]⟩,
⟨1483,198,41,198,1483,19,37,7,[],[48835,73642,102735,127542,132551,148353]⟩,
⟨1484,197,41,197,1484,19,37,7,[],[24421,27629,55934,56438,59629,87934,88438,132447,148453]⟩,
⟨1485,196,41,196,1485,19,37,7,[],[24521,29428,42231,48934,53828,66631,73334,111543,148551]⟩,
⟨1486,195,41,195,1486,19,37,7,[],[22928,31030,55435,58928,67030,91435,148649]⟩,
⟨1487,194,41,194,1487,19,37,7,[],[34630,38233,55336,70630,74233,91336,148749]⟩,
⟨1488,193,41,193,1488,19,37,7,[],[24821,50037,81544,86848,112037,143544,148848]⟩,
⟨1489,192,41,192,1489,19,37,7,[],[24921,27923,44435,65440,78044,94535,115540,128144,131951,148953]⟩,
⟨1490,191,41,191,1490,19,37,7,[],[25021,42536,71842,87047,104536,133842,149047]⟩,
⟨1491,190,41,190,1491,19,37,7,[],[25121,25632,31633,76740,77232,83233,128340,131751,149153]⟩,
⟨1492,189,41,189,1492,19,37,7,[],[25221,27623,44435,65140,78044,94835,115540,128444,131651,149253]⟩,
⟨1493,188,41,188,1493,19,37,7,[],[25321,27523,71540,88447,132440,149347]⟩,
⟨1494,187,41,187,1494,19,37,7,[],[25421,59837,64942,77044,111437,116542,128644,131451,149453]⟩,
⟨1495,186,41,186,1495,19,37,7,[],[25521,30028,31229,48332,52828,54029,71132,131345,149553]⟩,
⟨1496,185,41,185,1496,19,37,7,[],[25621,45235,47538,77242,96835,99138,128842,131251,149653]⟩,
⟨1497,184,41,184,1497,19,37,7,[],[55936,73643,111236,128943,131151,149753]⟩,
⟨1498,183,41,183,1498,19,37,7,[],[19829,49734,64240,65829,95734,110240,149851]⟩,
⟨1499,182,41,182,1499,19,37,7,[],[25921,26923,29428,44631,48934,51428,66631,70934,149947]⟩,
⟨1500,181,41,181,1500,19,37,7,[],[23128,55234,60328,92434,110045,150051]⟩,
⟨1501,180,41,180,1501,19,37,7,[],[18119,26230,50635,63740,71830,96235,109340,130749,150153]⟩,
⟨1502,179,41,179,1502,19,37,7,[],[18219,22928,55434,60128,92634,109845,150251]⟩,
⟨1503,178,41,178,1503,19,37,7,[],[26230,50235,63740,72230,96235,109740,150351]⟩,
⟨2487,114,51,114,2487,15,49,5,[],[37534,40138,78043,104234,106838,144743,227361,248769]⟩,
⟨2488,113,51,113,2488,15,49,5,[],[37534,40038,78043,104334,106838,144843,227261,248869]⟩,
⟨2489,112,51,112,2489,15,49,5,[],[37534,39938,78043,104434,106838,144943,227161,248969]⟩,
⟨2971,278,57,278,2971,39,42,6,[],[52443,54446,132454,157143,159146,237154,295773,297177]⟩,
⟨2972,277,57,277,2972,39,42,6,[],[52443,54346,132454,157243,159146,237254,295673,297277]⟩,
⟨2973,276,57,276,2973,39,42,6,[],[97948,110756,132459,202848,215656,237359,295573,297377]⟩,
⟨2974,275,57,275,2974,39,42,6,[],[52443,54146,132454,157443,159146,237454,295473,297477]⟩,
⟨2975,274,57,274,2975,39,42,6,[],[92849,147260,212749,267160,295375,297577]⟩,
⟨2976,273,57,273,2976,39,42,6,[],[46344,147256,166344,267256,295275,297677]⟩,
⟨2977,272,57,272,2977,39,42,6,[],[151156,162467,286456,297767]⟩,
⟨2978,271,57,271,2978,39,42,6,[],[52443,53746,132454,157843,159146,237854,295073,297877]⟩,
⟨2979,270,57,270,2979,39,42,6,[],[52443,53646,132454,157943,159146,237954,294973,297977]⟩,
⟨2980,269,57,269,2980,39,42,6,[],[52443,53546,132454,158043,159146,238054,294873,298077]⟩,
⟨2981,268,57,268,2981,39,42,6,[],[52443,53446,132454,158143,159146,238154,294773,298177]⟩,
⟨2982,267,57,267,2982,39,42,6,[],[52443,53346,132454,158243,159146,238254,294673,298277]⟩,
⟨2983,266,57,266,2983,39,42,6,[],[52443,53246,132454,158343,159146,238354,294573,298377]⟩,
⟨2984,265,57,265,2984,39,42,6,[],[52443,53146,132454,158443,159146,238454,294473,298477]⟩,
⟨2985,264,57,264,2985,39,42,6,[],[40338,58342,104049,118038,136042,181749,294369,298577]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw12_ok : isoRaw12.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw13 : List IsoRaw := [
⟨2986,263,57,263,2986,39,42,6,[],[42245,115354,160264,176245,249354,294264,298677]⟩,
⟨2987,262,57,262,2987,39,42,6,[],[52443,52846,132454,158743,159146,238754,294173,298777]⟩,
⟨2988,261,57,261,2988,39,42,6,[],[33544,102852,160063,167544,236852,294063,298877]⟩,
⟨2989,260,57,260,2989,39,42,6,[],[49146,162459,185646,298959]⟩,
⟨2990,259,57,259,2990,39,42,6,[],[52443,52546,132454,159043,159146,239054,293873,299077]⟩,
⟨2991,258,57,258,2991,39,42,6,[],[97948,108956,132459,204648,215656,239159,293773,299177]⟩,
⟨2992,257,57,257,2992,39,42,6,[],[70748,155260,159667,204748,289260,293667,299277]⟩,
⟨2993,256,57,256,2993,39,42,6,[],[97948,108756,132459,204848,215656,239359,293573,299377]⟩,
⟨2994,255,57,255,2994,39,42,6,[],[97948,108656,132459,204948,215656,239459,293473,299477]⟩,
⟨2995,254,57,254,2995,39,42,6,[],[52246,116255,159364,186246,250255,293364,299577]⟩,
⟨2996,253,57,253,2996,39,42,6,[],[97948,108456,132459,205148,215656,239659,293273,299677]⟩,
⟨2997,252,57,252,2997,39,42,6,[],[102750,147261,224850,269361,293175,299777]⟩,
⟨2998,251,57,251,2998,39,42,6,[],[97948,108256,132459,205348,215656,239859,293073,299877]⟩,
⟨2999,250,57,250,2999,39,42,6,[],[97948,108156,132459,205448,215656,239959,292973,299977]⟩,
⟨3000,249,57,249,3000,39,42,6,[],[97948,108056,132459,205548,215656,240059,292873,300077]⟩,
⟨3001,248,57,248,3001,39,42,6,[],[97948,107956,132459,205648,215656,240159,292773,300177]⟩,
⟨3002,247,57,247,3002,39,42,6,[],[97948,107856,132459,205748,215656,240259,292673,300277]⟩,
⟨3003,246,57,246,3003,39,42,6,[],[97948,107756,132459,205848,215656,240359,292573,300377]⟩,
⟨3004,245,57,245,3004,39,42,6,[],[53146,104454,158463,187146,238454,292463,300477]⟩,
⟨3005,244,57,244,3005,39,42,6,[],[97948,107556,132459,206048,215656,240559,292373,300577]⟩,
⟨3006,243,57,243,3006,39,42,6,[],[44245,92152,158262,178245,226152,292262,300677]⟩,
⟨3007,242,57,242,3007,39,42,6,[],[97948,107356,132459,206248,215656,240759,292173,300777]⟩,
⟨3008,241,57,241,3008,39,42,6,[],[97948,107256,132459,206348,215656,240859,292073,300877]⟩,
⟨3009,240,57,240,3009,39,42,6,[],[97948,107156,132459,206448,215656,240959,291973,300977]⟩,
⟨3010,239,57,239,3010,39,42,6,[],[82249,143760,157866,216249,277760,291866,301077]⟩,
⟨3011,238,57,238,3011,39,42,6,[],[97948,106956,132459,206648,215656,241159,291773,301177]⟩,
⟨3012,237,57,237,3012,39,42,6,[],[97948,106856,132459,206748,215656,241259,291673,301277]⟩,
⟨3013,236,57,236,3013,39,42,6,[],[54046,92853,157562,188046,226853,291562,301377]⟩,
⟨3014,235,57,235,3014,39,42,6,[],[97948,106656,132459,206948,215656,241459,291473,301477]⟩,
⟨3015,234,57,234,3015,39,42,6,[],[97948,106556,132459,207048,215656,241559,291373,301577]⟩,
⟨3016,233,57,233,3016,39,42,6,[],[107952,162464,247152,301664]⟩,
⟨3017,232,57,232,3017,39,42,6,[],[97948,106356,132459,207248,215656,241759,291173,301777]⟩,
⟨3018,231,57,231,3018,39,42,6,[],[97948,106256,132459,207348,215656,241859,291073,301877]⟩,
⟨3019,230,57,230,3019,39,42,6,[],[97948,106156,132459,207448,215656,241959,290973,301977]⟩,
⟨3020,229,57,229,3020,39,42,6,[],[64047,93554,156862,198047,227554,290862,302077]⟩,
⟨3021,228,57,228,3021,39,42,6,[],[36844,69249,156760,170844,203249,290760,302177]⟩,
⟨3022,227,57,227,3022,39,42,6,[],[54946,81452,156661,188946,215452,290661,302277]⟩,
⟨3023,226,57,226,3023,39,42,6,[],[97948,105756,132459,207848,215656,242359,290573,302377]⟩,
⟨3024,225,57,225,3024,39,42,6,[],[64346,147258,189146,272058,290475,302477]⟩,
⟨3025,224,57,224,3025,39,42,6,[],[97948,105556,132459,208048,215656,242559,290373,302577]⟩,
⟨3026,223,57,223,3026,39,42,6,[],[46245,69750,156260,180245,203750,290260,302677]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw13_ok : isoRaw13.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw14 : List IsoRaw := [
⟨3027,222,57,222,3027,39,42,6,[],[97948,105356,132459,208248,215656,242759,290173,302777]⟩,
⟨3028,221,57,221,3028,39,42,6,[],[27540,132452,137940,242852,290073,302877]⟩,
⟨3029,220,57,220,3029,39,42,6,[],[97948,105156,132459,208448,215656,242959,289973,302977]⟩,
⟨3030,219,57,219,3030,39,42,6,[],[97948,105056,132459,208548,215656,243059,289873,303077]⟩,
⟨3031,218,57,218,3031,39,42,6,[],[55846,70251,155760,189846,204251,289760,303177]⟩,
⟨3032,217,57,217,3032,39,42,6,[],[37944,58448,155659,171944,192448,289659,303277]⟩,
⟨3033,216,57,216,3033,39,42,6,[],[97948,104756,132459,208848,215656,243359,289573,303377]⟩,
⟨3034,215,57,215,3034,39,42,6,[],[74948,82654,155461,208948,216654,289461,303477]⟩,
⟨3035,214,57,214,3035,39,42,6,[],[97948,104556,132459,209048,215656,243559,289373,303577]⟩,
⟨3036,213,57,213,3036,39,42,6,[],[65647,70752,155260,199647,204752,289260,303677]⟩,
⟨3037,212,57,212,3037,39,42,6,[],[29142,147255,155242,273355,289175,303777]⟩,
⟨3038,211,57,211,3038,39,42,6,[],[97948,104256,132459,209348,215656,243859,289073,303877]⟩,
⟨3039,210,57,210,3039,39,42,6,[],[97948,104156,132459,209448,215656,243959,288973,303977]⟩,
⟨3040,209,57,209,3040,39,42,6,[],[30043,47546,154858,164043,181546,288858,304077]⟩,
⟨3041,208,57,208,3041,39,42,6,[],[67948,162461,209648,304161]⟩,
⟨3042,207,57,207,3042,39,42,6,[],[97948,103856,132459,209748,215656,244259,288673,304277]⟩,
⟨3043,206,57,206,3043,39,42,6,[],[39044,47847,154558,173044,181847,288558,304377]⟩,
⟨3044,205,57,205,3044,39,42,6,[],[97948,103656,132459,209948,215656,244459,288473,304477]⟩,
⟨3045,204,57,204,3045,39,42,6,[],[97948,103556,132459,210048,215656,244559,288373,304577]⟩,
⟨3046,203,57,203,3046,39,42,6,[],[97948,103456,132459,210148,215656,244659,288273,304677]⟩,
⟨3047,202,57,202,3047,39,42,6,[],[97948,103356,132459,210248,215656,244759,288173,304777]⟩,
⟨3048,201,57,201,3048,39,42,6,[],[97948,103256,132459,210348,215656,244859,288073,304877]⟩,
⟨3049,200,57,200,3049,39,42,6,[],[97948,103156,132459,210448,215656,244959,287973,304977]⟩,
⟨3050,199,57,199,3050,39,42,6,[],[97948,103056,132459,210548,215656,245059,287873,305077]⟩,
⟨3051,198,57,198,3051,39,42,6,[],[97948,102956,132459,210648,215656,245159,287773,305177]⟩,
⟨3052,197,57,197,3052,39,42,6,[],[31144,162458,173944,305258]⟩,
⟨3053,196,57,196,3053,39,42,6,[],[97948,102756,132459,210848,215656,245359,287573,305377]⟩,
⟨3054,195,57,195,3054,39,42,6,[],[31443,148156,153466,165443,282156,287466,305477]⟩,
⟨3055,194,57,194,3055,39,42,6,[],[97948,102556,132459,211048,215656,245559,287373,305577]⟩,
⟨3056,193,57,193,3056,39,42,6,[],[97948,102456,132459,211148,215656,245659,287273,305677]⟩,
⟨3057,192,57,192,3057,39,42,6,[],[97948,102356,132459,211248,215656,245759,287173,305777]⟩,
⟨3058,191,57,191,3058,39,42,6,[],[97948,102256,132459,211348,215656,245859,287073,305877]⟩,
⟨3059,190,57,190,3059,39,42,6,[],[97948,102156,132459,211448,215656,245959,286973,305977]⟩,
⟨3060,189,57,189,3060,39,42,6,[],[97948,102056,132459,211548,215656,246059,286873,306077]⟩,
⟨3061,188,57,188,3061,39,42,6,[],[97948,101956,132459,211648,215656,246159,286773,306177]⟩,
⟨3062,187,57,187,3062,39,42,6,[],[97948,101856,132459,211748,215656,246259,286673,306277]⟩,
⟨3063,186,57,186,3063,39,42,6,[],[23842,123053,152564,157842,257053,286564,306377]⟩,
⟨3064,185,57,185,3064,39,42,6,[],[97948,101656,132459,211948,215656,246459,286473,306477]⟩,
⟨3065,184,57,184,3065,39,42,6,[],[97948,101556,132459,212048,215656,246559,286373,306577]⟩,
⟨3066,183,57,183,3066,39,42,6,[],[97948,101456,132459,212148,215656,246659,286273,306677]⟩,
⟨3067,182,57,182,3067,39,42,6,[],[77649,162462,221949,306762]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw14_ok : isoRaw14.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

set_option maxRecDepth 2000 in
private def isoRaw15 : List IsoRaw := [
⟨3068,181,57,181,3068,39,42,6,[],[97948,101256,132459,212348,215656,246859,286073,306877]⟩,
⟨3069,180,57,180,3069,39,42,6,[],[97948,101156,132459,212448,215656,246959,285973,306977]⟩,
⟨3070,179,57,179,3070,39,42,6,[],[97948,101056,132459,212548,215656,247059,285873,307077]⟩,
⟨3071,178,57,178,3071,39,42,6,[],[97948,100956,132459,212648,215656,247159,285773,307177]⟩,
⟨3072,177,57,177,3072,39,42,6,[],[97948,100856,132459,212748,215656,247259,285673,307277]⟩,
⟨3073,176,57,176,3073,39,42,6,[],[97948,100756,132459,212848,215656,247359,285573,307377]⟩,
⟨3074,175,57,175,3074,39,42,6,[],[97948,100656,132459,212948,215656,247459,285473,307477]⟩,
⟨3075,174,57,174,3075,39,42,6,[],[32839,115250,119258,134739,217150,221158,254969,307575]⟩,
⟨3076,173,57,173,3076,39,42,6,[],[42344,137256,151265,176344,271256,285265,307677]⟩,
⟨3077,172,57,172,3077,39,42,6,[],[40338,49142,104049,127238,136042,190949,285169,307777]⟩,
⟨3078,171,57,171,3078,39,42,6,[],[22936,63842,106651,112536,153442,196251,307871]⟩,
⟨3079,170,57,170,3079,39,42,6,[],[40338,48942,104049,127438,136042,191149,284969,307977]⟩,
⟨3080,169,57,169,3080,39,42,6,[],[51645,150758,150866,185645,284758,284866,308077]⟩,
⟨3081,168,57,168,3081,39,42,6,[],[89544,104053,176844,191353,284769,308177]⟩,
⟨3082,167,57,167,3082,39,42,6,[],[40338,48642,104049,127738,136042,191449,284669,308277]⟩,
⟨3083,166,57,166,3083,39,42,6,[],[40338,48542,104049,127838,136042,191549,284569,308377]⟩,
⟨3084,165,57,165,3084,39,42,6,[],[40338,48442,104049,127938,136042,191649,284469,308477]⟩,
⟨3085,164,57,164,3085,39,42,6,[],[26042,100051,150362,160042,234051,284362,308577]⟩,
⟨3086,163,57,163,3086,39,42,6,[],[40338,48242,104049,128138,136042,191849,284269,308677]⟩,
⟨3087,162,57,162,3087,39,42,6,[],[40338,48142,104049,128238,136042,191949,284169,308777]⟩,
⟨3088,161,57,161,3088,39,42,6,[],[93546,118056,195546,220056,284071,308877]⟩,
⟨3089,160,57,160,3089,39,42,6,[],[64041,78248,104052,152141,166348,192152,283969,308977]⟩,
⟨3090,159,57,159,3090,39,42,6,[],[40338,47842,104049,128538,136042,192249,283869,309077]⟩,
⟨3091,158,57,158,3091,39,42,6,[],[50041,118052,152341,220352,283771,309177]⟩,
⟨3092,157,57,157,3092,39,42,6,[],[97948,98856,132459,214748,215656,249259,283673,309277]⟩,
⟨3093,156,57,156,3093,39,42,6,[],[87550,162463,234450,309363]⟩,
⟨3094,155,57,155,3094,39,42,6,[],[44144,113454,149463,178144,247454,283463,309477]⟩,
⟨3095,154,57,154,3095,39,42,6,[],[97948,98556,132459,215048,215656,249559,283373,309577]⟩,
⟨3096,153,57,153,3096,39,42,6,[],[27142,88850,149261,161142,222850,283261,309677]⟩,
⟨3097,152,57,152,3097,39,42,6,[],[97948,98356,132459,215248,215656,249759,283173,309777]⟩,
⟨3098,151,57,151,3098,39,42,6,[],[97948,98256,132459,215348,215656,249859,283073,309877]⟩,
⟨3099,150,57,150,3099,39,42,6,[],[97948,98156,132459,215448,215656,249959,282973,309977]⟩,
⟨3283,198,59,198,3283,41,43,7,[],[24841,143254,148341,266754,295775,328379]⟩,
⟨3284,197,59,197,3284,41,43,7,[],[30338,51642,114051,124738,146042,208451,295671,328479]⟩,
⟨3285,196,59,196,3285,41,43,7,[],[30338,51542,114051,124838,146042,208551,295571,328579]⟩
]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem isoRaw15_ok : isoRaw15.all (fun r => checkIsoWitnessFast (unpackIso r)) = true := rfl

private def isoRawAll : List IsoRaw :=
  isoRaw1 ++ (isoRaw2 ++ (isoRaw3 ++ (isoRaw4 ++ (isoRaw5 ++ (isoRaw6 ++ (isoRaw7 ++ (isoRaw8 ++ (isoRaw9 ++ (isoRaw10 ++ (isoRaw11 ++ (isoRaw12 ++ (isoRaw13 ++ (isoRaw14 ++ (isoRaw15))))))))))))))

private theorem isoRawAll_ok : ∀ r ∈ isoRawAll, checkIsoWitnessFast (unpackIso r) = true := by
  intro r hr
  simp only [isoRawAll, List.mem_append] at hr
  rcases hr with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact List.all_eq_true.mp isoRaw1_ok r h1
  · exact List.all_eq_true.mp isoRaw2_ok r h2
  · exact List.all_eq_true.mp isoRaw3_ok r h3
  · exact List.all_eq_true.mp isoRaw4_ok r h4
  · exact List.all_eq_true.mp isoRaw5_ok r h5
  · exact List.all_eq_true.mp isoRaw6_ok r h6
  · exact List.all_eq_true.mp isoRaw7_ok r h7
  · exact List.all_eq_true.mp isoRaw8_ok r h8
  · exact List.all_eq_true.mp isoRaw9_ok r h9
  · exact List.all_eq_true.mp isoRaw10_ok r h10
  · exact List.all_eq_true.mp isoRaw11_ok r h11
  · exact List.all_eq_true.mp isoRaw12_ok r h12
  · exact List.all_eq_true.mp isoRaw13_ok r h13
  · exact List.all_eq_true.mp isoRaw14_ok r h14
  · exact List.all_eq_true.mp isoRaw15_ok r h15

def isoWitnessList : List IsoWitness :=
  isoRawAll.map unpackIso

theorem iso_witnesses_verified : ∀ w ∈ isoWitnessList, checkIsoWitness w = true := by
  intro w hw
  simp only [isoWitnessList, List.mem_map] at hw
  rcases hw with ⟨r, hr, rfl⟩
  exact checkIsoWitnessFast_implies (unpackIso r) (isoRawAll_ok r hr)

/-! ### Part 7: Lower-Bridge (`41`) and Upper-Bridge (`69`) Interval Quadruples -/

def natAbsDiff (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

lemma natAbsDiff_eq (a b : ℕ) : natAbsDiff a b = Int.natAbs ((a : ℤ) - (b : ℤ)) := by
  unfold natAbsDiff; split_ifs <;> omega

structure LowerQuad where
  lo : ℕ
  hi : ℕ
  kind : ℕ
  a1 : ℕ
  a2 : ℕ
  a3 : ℕ
  a4 : ℕ
  s : ℕ
  z : ℕ
  p : ℕ
  q : ℕ

def checkLowerQuad (q : LowerQuad) : Bool :=
  Nat.ble q.lo q.hi &&
  (q.s == 4 || q.s == 5 || q.s == 6 || q.s == 7) &&
  (q.p * q.p + q.q * q.q == q.z * q.z + q.s * q.s) &&
  Nat.ble q.p q.q &&
  match q.kind with
  | 0 => -- L: (a, b, e1, e2), L = b*b - n
      let a := q.a1; let b := q.a2; let e1 := q.a3; let e2 := q.a4
      let Llo := b * b - q.hi; let Lhi := b * b - q.lo
      (a % 2 == 1) && (b % 2 == 1) && Nat.blt a b && Nat.blt e1 e2 &&
      (b * b - a * a == 2 * (e2 * e2 - e1 * e1)) &&
      (Nat.gcd (e2 * e2 - e1 * e1) (natAbsDiff (e1 * e1) (b * b)) == 1) &&
      (q.z == b) && Nat.ble q.hi (b * b) &&
      Nat.ble 55 Llo && Nat.ble (Lhi + 1) q.lo &&
      Nat.ble (a * a + b * b + 2) (2 * Llo + e2 * e2) &&
      Nat.blt (2 * Lhi + e2 * e2) (a * a + b * b + 1 + (e2 * e2 - e1 * e1)) &&
      Nat.ble (2 * Lhi + 3) (a * a) &&
      Nat.ble (Lhi + q.s * q.s) (q.p * q.p + 1) &&
      checkBudgetRange q.lo q.hi (Llo - 1) (Lhi - 1) q.s
  | 1 => -- R: (e1, e2, b, c), L = b*b - n
      let e1 := q.a1; let e2 := q.a2; let b := q.a3; let c := q.a4
      let Llo := b * b - q.hi; let Lhi := b * b - q.lo
      (b % 2 == 1) && (c % 2 == 1) && Nat.blt b c && Nat.blt e1 e2 &&
      (c * c - b * b == 2 * (e2 * e2 - e1 * e1)) &&
      (Nat.gcd (e2 * e2 - e1 * e1) (natAbsDiff (b * b) (e2 * e2)) == 1) &&
      (q.z == b) && Nat.ble q.hi (b * b) &&
      Nat.ble 55 Llo && Nat.ble (Lhi + 1) q.lo &&
      Nat.ble (2 * Lhi + e2 * e2 + 1) (2 * e1 * e1 + 1) &&
      Nat.blt (2 * e1 * e1 + 1) (2 * Llo + e2 * e2 + (e2 * e2 - e1 * e1)) &&
      Nat.ble (2 * Lhi + c * c + 3) (2 * b * b) &&
      Nat.ble (Lhi + q.s * q.s) (q.p * q.p + 1) &&
      checkBudgetRange q.lo q.hi (Llo - 1) (Lhi - 1) q.s
  | 2 => -- 3C: (e1, e2, b, e3), L = b*b - n
      let e1 := q.a1; let e2 := q.a2; let b := q.a3; let e3 := q.a4
      let Llo := b * b - q.hi; let Lhi := b * b - q.lo
      (b % 2 == 1) && Nat.blt e1 e2 && Nat.blt e2 e3 &&
      (b * b + e2 * e2 == e1 * e1 + e3 * e3) &&
      (Nat.gcd (e2 * e2 - e1 * e1) (natAbsDiff (b * b) (e2 * e2)) == 1) &&
      (q.z == b) && Nat.ble q.hi (b * b) &&
      Nat.ble 55 Llo && Nat.ble (Lhi + 1) q.lo &&
      Nat.ble (2 * Lhi + b * b + 2) (2 * e1 * e1 + 1) &&
      Nat.blt (2 * e1 * e1 + 1) (2 * Llo + b * b + 2 * (e2 * e2 - e1 * e1)) &&
      Nat.ble (2 * e2 * e2 + 2 + 2 * Lhi) (2 * e1 * e1 + 1 + b * b) &&
      Nat.ble (Lhi + q.s * q.s) (q.p * q.p + 1) &&
      checkBudgetRange q.lo q.hi (Llo - 1) (Lhi - 1) q.s
  | 3 => -- SM1-J1: (b1, b2, e1, e2), L = n + 1 - 2*(e2*e2 - e1*e1)
      let b1 := q.a1; let b2 := q.a2; let e1 := q.a3; let e2 := q.a4
      let D := e2 * e2 - e1 * e1
      let Llo := q.lo + 1 - 2 * D; let Lhi := q.hi + 1 - 2 * D
      (b1 % 2 == 1) && (b2 % 2 == 1) && Nat.blt b1 b2 && Nat.blt e1 e2 &&
      (b2 * b2 - b1 * b1 == 2 * D) &&
      (Nat.gcd D (natAbsDiff (b1 * b1) (e1 * e1)) == 1) &&
      (q.z == b1) && Nat.ble 1 D && Nat.ble (2 * D + 54) q.lo &&
      Nat.ble 55 Llo &&
      Nat.ble (2 * Lhi + e2 * e2 + 1) (2 * e1 * e1 + 1) &&
      Nat.blt (2 * e1 * e1 + 1) (2 * Llo + e2 * e2 + D) &&
      Nat.ble (2 * Lhi + 3) (b1 * b1) &&
      Nat.ble (b2 * b2 + 3) (2 * q.lo) &&
      Nat.ble (b1 * b1) (Llo + q.lo) &&
      Nat.ble (Lhi + q.s * q.s) (q.p * q.p + 1) &&
      checkBudgetRange q.lo q.hi (Llo - 1) (Lhi - 1) q.s
  | 4 => -- SM1-J2: (b1, b2, e1, e2), L = n + 1 - 2*(e2*e2 - e1*e1)
      let b1 := q.a1; let b2 := q.a2; let e1 := q.a3; let e2 := q.a4
      let D := e2 * e2 - e1 * e1
      let Llo := q.lo + 1 - 2 * D; let Lhi := q.hi + 1 - 2 * D
      (b1 % 2 == 1) && (b2 % 2 == 1) && Nat.blt b1 b2 && Nat.blt e1 e2 &&
      (b2 * b2 - b1 * b1 == 2 * D) &&
      (Nat.gcd D (natAbsDiff (b1 * b1) (e1 * e1)) == 1) &&
      (q.z == b2) && Nat.ble 1 D && Nat.ble (2 * D + 54) q.lo &&
      Nat.ble 55 Llo &&
      Nat.ble (2 * Lhi + e2 * e2 + 1) (2 * e1 * e1 + 1) &&
      Nat.blt (2 * e1 * e1 + 1) (2 * Llo + e2 * e2 + D) &&
      Nat.ble (2 * Lhi + 3) (b1 * b1) &&
      Nat.ble (b2 * b2 + 3) (2 * q.lo) &&
      Nat.ble q.hi (b2 * b2) &&
      Nat.ble (Lhi + q.hi) (b2 * b2) &&
      Nat.ble (b2 * b2 - q.lo + q.s * q.s) (q.p * q.p + 1) &&
      checkBudgetRange q.lo q.hi (Llo - 1) (Lhi - 1) q.s
  | _ => false

def lowerQuadList : List LowerQuad := [
⟨238,272,3,17,21,18,20,7,17,13,13⟩,
⟨360,379,4,21,25,22,24,5,25,17,19⟩,
⟨388,437,3,23,27,24,26,7,23,17,17⟩,
⟨508,520,3,27,31,28,30,6,27,18,21⟩,
⟨575,635,4,29,33,30,32,4,33,23,24⟩,
⟨718,787,3,33,37,34,36,4,33,23,24⟩,
⟨796,869,3,35,39,36,38,5,35,25,25⟩,
⟨846,874,4,13,31,30,36,5,31,19,25⟩,
⟨878,906,0,13,31,30,36,5,31,19,25⟩,
⟨964,1008,3,39,43,40,42,7,39,27,29⟩,
⟨1023,1045,4,39,43,40,42,4,43,29,32⟩,
⟨1088,1139,4,41,45,42,44,5,45,31,33⟩,
⟨1116,1170,0,17,35,36,42,5,35,17,31⟩,
⟨1246,1339,4,45,49,46,48,7,49,35,35⟩,
⟨1348,1445,3,47,51,48,50,6,47,33,34⟩,
⟨1454,1458,4,11,39,30,40,7,39,27,29⟩,
⟨1462,1466,0,11,39,30,40,7,39,27,29⟩,
⟨1504,1626,4,21,43,40,48,6,43,21,38⟩,
⟨1552,1751,0,35,45,48,52,5,45,23,39⟩,
⟨1630,1794,0,21,43,40,48,6,43,21,38⟩,
⟨1789,2058,1,42,48,49,59,7,49,35,35⟩,
⟨2044,2120,3,59,63,60,62,7,59,41,43⟩,
⟨2114,2486,4,39,57,50,58,6,57,39,42⟩,
⟨2490,2545,0,39,57,50,58,6,57,39,42⟩,
⟨2522,2792,1,52,60,57,71,6,57,39,42⟩,
⟨2719,2970,1,42,54,55,73,5,55,29,47⟩,
⟨3100,3282,4,37,63,60,70,6,63,33,54⟩,
⟨3286,3749,0,37,63,60,70,6,63,33,54⟩,
⟨3720,4001,0,59,69,78,82,7,69,33,61⟩,
⟨3818,4434,2,54,66,67,77,6,67,45,50⟩,
⟨4406,5063,3,47,81,60,76,6,47,33,34⟩,
⟨4918,5874,4,45,83,68,84,6,83,45,70⟩,
⟨5789,6506,1,58,72,81,101,5,81,31,75⟩,
⟨6242,7560,3,81,111,82,98,7,81,43,69⟩,
⟨7254,8498,4,51,99,80,100,5,99,51,85⟩,
⟨8486,9354,0,43,97,96,114,5,97,47,85⟩,
⟨9024,10970,2,87,100,105,116,5,105,45,95⟩,
⟨10812,13170,2,101,120,115,132,5,115,65,95⟩,
⟨13054,16021,3,105,155,112,138,5,105,59,87⟩,
⟨15624,18922,4,101,155,132,156,5,155,97,121⟩,
⟨16891,19856,1,124,146,147,183,5,147,103,105⟩
]

private theorem lowerQuadList_ok : lowerQuadList.all checkLowerQuad = true := rfl

theorem lower_quads_verified : ∀ q ∈ lowerQuadList, checkLowerQuad q = true :=
  List.all_eq_true.mp lowerQuadList_ok

def isMod5Class (cls s : ℕ) : Bool :=
  if cls == 0 then s % 5 == 0
  else if cls == 1 then s % 5 == 1 || s % 5 == 4
  else s % 5 == 2 || s % 5 == 3

def checkMod5Repl (b x1 x2 x3 : ℕ) : Bool :=
  (b % 5 == 0) ||
  ((b % 5 == 1 || b % 5 == 4) && (isMod5Class 2 x1 || isMod5Class 2 x2 || isMod5Class 2 x3)) ||
  ((b % 5 == 2 || b % 5 == 3) && (isMod5Class 1 x1 || isMod5Class 1 x2 || isMod5Class 1 x3))

structure UpperQuad where
  lo : ℕ
  hi : ℕ
  isMirror : Bool
  a1 : ℕ
  a2 : ℕ
  a3 : ℕ
  a4 : ℕ

def checkUpperQuad (q : UpperQuad) : Bool :=
  Nat.ble q.lo q.hi &&
  match q.isMirror with
  | false => -- L: (a, b, e1, e2)
      let a := q.a1; let b := q.a2; let e1 := q.a3; let e2 := q.a4
      let Llo := b * b - q.hi; let Lhi := b * b - q.lo
      (a % 2 == 1) && (b % 2 == 1) && Nat.blt a b && Nat.blt e1 e2 &&
      (b * b - a * a == 2 * (e2 * e2 - e1 * e1)) &&
      (Nat.gcd (e2 * e2 - e1 * e1) (natAbsDiff (e1 * e1) (b * b)) == 1) &&
      Nat.ble q.hi (b * b) &&
      Nat.ble 55 Llo && Nat.ble (Lhi + 1) q.lo && Nat.ble (18 * Lhi) (b * b) &&
      Nat.ble (a * a + b * b + 2) (2 * Llo + e2 * e2) &&
      Nat.blt (2 * Lhi + e2 * e2) (a * a + b * b + 1 + (e2 * e2 - e1 * e1)) &&
      Nat.ble (2 * Lhi + 3) (a * a) &&
      checkMod5Repl b a e1 e2
  | true => -- R: (e1, e2, b, c)
      let e1 := q.a1; let e2 := q.a2; let b := q.a3; let c := q.a4
      let Llo := b * b - q.hi; let Lhi := b * b - q.lo
      (b % 2 == 1) && (c % 2 == 1) && Nat.blt b c && Nat.blt e1 e2 &&
      (c * c - b * b == 2 * (e2 * e2 - e1 * e1)) &&
      (Nat.gcd (e2 * e2 - e1 * e1) (natAbsDiff (b * b) (e2 * e2)) == 1) &&
      Nat.ble q.hi (b * b) &&
      Nat.ble 55 Llo && Nat.ble (Lhi + 1) q.lo && Nat.ble (18 * Lhi) (b * b) &&
      Nat.ble (2 * Lhi + e2 * e2 + 1) (2 * e1 * e1 + 1) &&
      Nat.blt (2 * e1 * e1 + 1) (2 * Llo + e2 * e2 + (e2 * e2 - e1 * e1)) &&
      Nat.ble (2 * Lhi + c * c + 3) (2 * b * b) &&
      checkMod5Repl b c e1 e2

def upperQuadList : List UpperQuad := [
⟨19857,20970,true,108,142,145,195⟩,
⟨20968,22146,true,78,98,149,171⟩,
⟨21535,22746,false,105,151,176,192⟩,
⟨22691,23970,true,102,126,155,187⟩,
⟨23280,24594,true,120,156,157,211⟩,
⟨24481,25866,true,126,160,161,213⟩,
⟨25713,27170,true,106,132,165,199⟩,
⟨26611,27834,true,96,126,167,203⟩,
⟨27617,29186,true,110,142,171,213⟩,
⟨28267,29874,true,144,184,173,237⟩,
⟨29589,31274,true,116,152,177,225⟩,
⟨30941,32706,true,138,174,181,235⟩,
⟨32324,33504,true,168,204,185,247⟩,
⟨33027,34914,false,137,187,216,234⟩,
⟨34455,36426,true,132,168,191,241⟩,
⟨35913,37970,true,128,164,195,243⟩,
⟨36653,38754,true,114,144,197,233⟩,
⟨38019,39546,true,132,178,199,261⟩,
⟨38920,39743,false,139,203,216,240⟩,
⟨39691,41970,true,156,192,205,259⟩,
⟨40469,42794,false,131,207,234,260⟩,
⟨42775,44466,true,138,186,211,275⟩,
⟨43657,46170,true,144,178,215,261⟩,
⟨46128,48786,true,150,188,221,273⟩,
⟨47813,50570,true,148,184,225,273⟩,
⟨50397,53306,false,117,231,242,280⟩,
⟨53049,56114,true,136,168,237,275⟩,
⟨55769,58994,false,129,243,260,298⟩,
⟨58557,61946,true,190,242,249,327⟩,
⟨61413,64970,false,141,255,278,316⟩,
⟨63355,67026,true,198,258,259,349⟩,
⟨66324,70170,true,174,222,265,329⟩,
⟨69532,73386,false,171,271,308,342⟩,
⟨72697,75864,true,120,144,277,299⟩,
⟨75640,80034,true,216,276,283,373⟩,
⟨79977,84626,false,153,291,310,356⟩,
⟨84435,89346,true,228,288,299,389⟩,
⟨89013,94194,true,234,294,307,397⟩,
⟨93713,99170,false,175,315,318,368⟩,
⟨98533,104274,false,161,323,336,390⟩,
⟨103475,109506,false,169,331,348,402⟩,
⟨108537,114866,false,179,339,342,398⟩,
⟨113720,120354,false,185,347,372,426⟩,
⟨119024,125970,false,193,355,384,438⟩,
⟨125824,133170,true,198,244,365,417⟩,
⟨132813,140570,false,189,375,392,454⟩,
⟨139991,148170,true,222,274,385,447⟩,
⟨147357,155970,false,225,395,394,456⟩,
⟨154913,163970,true,266,338,405,501⟩,
⟨162657,172170,true,276,362,415,531⟩,
⟨171114,180570,true,354,454,425,585⟩,
⟨180360,190914,true,240,296,437,501⟩,
⟨190401,201546,true,222,272,449,501⟩,
⟨198977,210626,false,295,459,504,562⟩,
⟨209517,221786,false,365,471,564,602⟩,
⟨220329,233234,false,255,483,472,554⟩,
⟨232127,244970,true,314,414,495,625⟩,
⟨244688,259026,true,354,450,509,643⟩,
⟨258333,273474,false,289,523,570,648⟩,
⟨272349,288314,true,326,414,537,647⟩,
⟨286735,303546,false,313,551,570,654⟩,
⟨301491,319170,true,306,382,565,651⟩,
⟨316617,335186,false,297,579,610,704⟩,
⟨334357,353970,true,426,524,595,735⟩,
⟨352581,373266,false,305,611,636,738⟩,
⟨371289,393074,false,345,627,682,776⟩,
⟨392913,415970,true,424,532,645,789⟩,
⟨415149,439514,false,467,663,756,826⟩,
⟨437997,463706,true,382,468,681,781⟩
]

private theorem upperQuadList_ok : upperQuadList.all checkUpperQuad = true := rfl

theorem upper_quads_verified : ∀ q ∈ upperQuadList, checkUpperQuad q = true :=
  List.all_eq_true.mp upperQuadList_ok

/-! ### Part 8: 100% Coverage of `[54, 19856]` and `[19857, 461456]` -/

private def lowerAllIntervals : List (ℕ × ℕ) :=
  mergeSorted 1000
    (mergeSorted 1000
      (baseCyclePackedAll.map (fun p => (p.1, p.1)))
      (isoRawAll.map (fun r => (r.R, r.R))))
    (lowerQuadList.map (fun q => (q.lo, q.hi)))

set_option maxRecDepth 8000 in
private theorem lowerAllIntervals_ok : checkIntervalCover 54 19856 lowerAllIntervals = true := rfl

theorem lower_covered_all : ∀ n, 54 ≤ n → n ≤ 19856 →
    (∃ p ∈ baseCycleList, p.1 = n) ∨
    (∃ w ∈ isoWitnessList, w.R = n) ∨
    (∃ q ∈ lowerQuadList, q.lo ≤ n ∧ n ≤ q.hi) := by
  intro n h1 h2
  obtain ⟨iv, hiv, hlo, hhi⟩ := checkIntervalCover_sound lowerAllIntervals_ok n h1 h2
  rcases mem_mergeSorted _ _ _ iv hiv with hbi | hq
  · rcases mem_mergeSorted _ _ _ iv hbi with hb | hi
    · rw [List.mem_map] at hb
      rcases hb with ⟨p, hp, rfl⟩
      left
      refine ⟨(p.1, unpack532 p.2 p.1), ?_, by dsimp only at hlo hhi ⊢; omega⟩
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    · rw [List.mem_map] at hi
      rcases hi with ⟨r, hr, rfl⟩
      right; left
      refine ⟨unpackIso r, List.mem_map.mpr ⟨r, hr, rfl⟩, by dsimp only [unpackIso] at hlo hhi ⊢; omega⟩
  · rw [List.mem_map] at hq
    rcases hq with ⟨q, hqm, rfl⟩
    right; right
    exact ⟨q, hqm, hlo, hhi⟩

set_option maxRecDepth 2000 in
private theorem upperAllIntervals_ok :
    checkIntervalCover 19857 461456 (upperQuadList.map (fun q => (q.lo, q.hi))) = true := rfl

theorem upper_covered_all : ∀ n, 19857 ≤ n → n ≤ 461456 →
    ∃ q ∈ upperQuadList, q.lo ≤ n ∧ n ≤ q.hi := by
  intro n h1 h2
  obtain ⟨iv, hiv, hlo, hhi⟩ := checkIntervalCover_sound upperAllIntervals_ok n h1 h2
  rw [List.mem_map] at hiv
  rcases hiv with ⟨q, hq, rfl⟩
  exact ⟨q, hq, hlo, hhi⟩

end MSE2637546.S3

namespace MSE2637546.Final

open MSE2637546

private lemma invSmall_mono {k4 k5 k6 k7 k4' k5' k6' k7' n : ℕ}
    (h4 : k4 ≤ k4') (h5 : k5 ≤ k5') (h6 : k6 ≤ k6') (h7 : k7 ≤ k7')
    (h : InvSmall k4' k5' k6' k7' n) : InvSmall k4 k5 k6 k7 n := by
  rcases h with ⟨c, c4, c5, c6, c7⟩
  exact ⟨c, le_trans h4 c4, le_trans h5 c5, le_trans h6 c6, le_trans h7 c7⟩

private lemma hasEdge_to_hasMod5Class {L R z cls u : ℕ}
    (hL : 1 ≤ L) (c : IntervalCycle L R)
    (_hu1 : L ≤ u) (_hu2 : u ≤ R) (he : HasEdge c u (z * z - u))
    (hcls : S3.isMod5Class cls z = true) : HasMod5Class c cls := by
  rcases he with ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · have hm := (c.hmem (nextIdx (by have := c.hpos; omega : 0 < c.len) i)).1
    rw [h2] at hm
    have hsum : c.seq i + c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) i) = z * z := by
      rw [h1, h2]; omega
    refine ⟨i, z, hsum, ?_⟩
    unfold S3.isMod5Class at hcls
    split_ifs at hcls ⊢ <;> simp_all
  · have hm := (c.hmem i).1
    rw [h1] at hm
    have hsum : c.seq i + c.seq (nextIdx (by have := c.hpos; omega : 0 < c.len) i) = z * z := by
      rw [h1, h2]; omega
    refine ⟨i, z, hsum, ?_⟩
    unfold S3.isMod5Class at hcls
    split_ifs at hcls ⊢ <;> simp_all

private lemma checkMod5Repl_sound {L R b x1 x2 x3 : ℕ}
    (hL : 1 ≤ L) (c : IntervalCycle L R)
    (hrepl : S3.checkMod5Repl b x1 x2 x3 = true)
    (hx1 : ∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c u (x1 * x1 - u))
    (hx2 : ∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c u (x2 * x2 - u))
    (hx3 : ∃ u, L ≤ u ∧ u ≤ R ∧ HasEdge c u (x3 * x3 - u)) :
    b % 5 = 0 ∨
    ((b % 5 = 1 ∨ b % 5 = 4) ∧ HasMod5Class c 2) ∨
    ((b % 5 = 2 ∨ b % 5 = 3) ∧ HasMod5Class c 1) := by
  simp only [S3.checkMod5Repl, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hrepl
  rcases hrepl with (hb0 | ⟨hb14, h2⟩) | ⟨hb23, h1⟩
  · exact Or.inl hb0
  · refine Or.inr (Or.inl ⟨hb14, ?_⟩)
    rcases h2 with (h | h) | h
    · rcases hx1 with ⟨u, hu1, hu2, he⟩; exact hasEdge_to_hasMod5Class hL c hu1 hu2 he h
    · rcases hx2 with ⟨u, hu1, hu2, he⟩; exact hasEdge_to_hasMod5Class hL c hu1 hu2 he h
    · rcases hx3 with ⟨u, hu1, hu2, he⟩; exact hasEdge_to_hasMod5Class hL c hu1 hu2 he h
  · refine Or.inr (Or.inr ⟨hb23, ?_⟩)
    rcases h1 with (h | h) | h
    · rcases hx1 with ⟨u, hu1, hu2, he⟩; exact hasEdge_to_hasMod5Class hL c hu1 hu2 he h
    · rcases hx2 with ⟨u, hu1, hu2, he⟩; exact hasEdge_to_hasMod5Class hL c hu1 hu2 he h
    · rcases hx3 with ⟨u, hu1, hu2, he⟩; exact hasEdge_to_hasMod5Class hL c hu1 hu2 he h

private lemma iso_step {w : S3.IsoWitness} (hw : S3.checkIsoWitness w = true)
    (ih : InvSmall (S3.req4 (w.L - 1)) (S3.req5 (w.L - 1))
                   (S3.req6 (w.L - 1)) (S3.req7 (w.L - 1)) (w.L - 1)) :
    InvSmall (S3.req4 w.R) (S3.req5 w.R) (S3.req6 w.R) (S3.req7 w.R) w.R := by
  simp only [S3.checkIsoWitness, Bool.and_eq_true] at hw
  rcases hw with ⟨hcom, htm⟩
  have htm' := htm
  simp only [S1.checkTwoMatchings, S1.checkRootMatching, Bool.and_eq_true] at htm'
  have hcov : S1.checkCovers w.L w.R w.m1 = true := htm'.1.1.2.1
  obtain ⟨c2, hc2⟩ := S1.cycle_of_two_matchings w.L w.R w.m1 w.m2 htm
  simp only [S3.checkIsoCommon, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq,
    beq_iff_eq, List.any_eq_true] at hcom
  rcases hcom with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL55, hLR⟩, _heven⟩, hs⟩, hpq⟩, hpleq⟩, hlo1⟩, hhi1⟩, hlohi⟩, hbound⟩, ⟨t, ht_mem, ht_eq⟩⟩, hbud⟩
  have hmem : (w.lo, w.hi, w.z) ∈ w.m1 := by rw [← ht_eq]; exact ht_mem
  have hs' : w.s = 4 ∨ w.s = 5 ∨ w.s = 6 ∨ w.s = 7 := by rcases hs with ((h | h) | h) | h <;> simp [h]
  obtain ⟨hb4, hb5, hb6, hb7⟩ := S3.checkBudgetPoint_sound hbud
  have h1 := invSmall_mono hb4 hb5 hb6 hb7 ih
  refine S1.small_edge_merge (by omega) hLR hs' hpq hpleq hlo1 hhi1 hlohi hbound h1 c2 ?_
  intro u hu1 hu2
  have hev := S3.evalRootMatching_of_mem_checkCovers hcov hmem hu1 hu2
  rw [← hev]
  exact hc2 u (by omega) (by omega)

private lemma lowerQuad_step {q : S3.LowerQuad} {n : ℕ}
    (hq : S3.checkLowerQuad q = true) (hlo : q.lo ≤ n) (hhi : n ≤ q.hi)
    (ih : ∀ m, 54 ≤ m → m < n →
      InvSmall (S3.req4 m) (S3.req5 m) (S3.req6 m) (S3.req7 m) m) :
    InvSmall (S3.req4 n) (S3.req5 n) (S3.req6 n) (S3.req7 n) n := by
  unfold S3.checkLowerQuad at hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, beq_iff_eq] at hq
  rcases hq with ⟨⟨⟨⟨hlohi, hs⟩, hpq⟩, hpleq⟩, hbody⟩
  have hs' : q.s = 4 ∨ q.s = 5 ∨ q.s = 6 ∨ q.s = 7 := by rcases hs with ((h | h) | h) | h <;> simp [h]
  rcases hkind : q.kind with _ | _ | _ | _ | _ | k
  · -- kind = 0 : Left (a, b, e1, e2)
    rw [hkind] at hbody
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hbody
    rcases hbody with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha_odd, hb_odd⟩, hab⟩, he⟩, hdioph⟩, hgcd⟩, hzb⟩, hqb⟩, hL55⟩, hLlt⟩, hwlo⟩, hwhi⟩, hLhi⟩, hbound⟩, hbud⟩
    set a := q.a1; set b := q.a2; set e1 := q.a3; set e2 := q.a4
    have he_sq : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    have hab_sq : a * a < b * b := Nat.mul_lt_mul'' hab hab
    set L := b * b - n
    set w1 := 2 * L + e2 * e2 - (a * a + b * b + 1)
    have hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((e1 : ℤ) * e1 - (b : ℤ) * b)) := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hgcd, S3.natAbsDiff_eq]; push_cast; rfl
    obtain ⟨c2, hrefl, _, _, _⟩ := S2.left_4sq_cycle (w1 := w1) ha_odd hb_odd hab he hdioph hcop
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega : n = b * b - L)
    obtain ⟨hb4, hb5, hb6, hb7⟩ := S3.checkBudgetRange_sound hbud hlo hhi
      (by omega : b * b - q.hi - 1 ≤ L - 1) (by omega : L - 1 ≤ b * b - q.lo - 1)
    have h1 := invSmall_mono hb4 hb5 hb6 hb7 (ih (L - 1) (by omega) (by omega))
    rw [hzb] at hpq
    exact S1.small_edge_merge (by omega) (by omega) hs' hpq hpleq
      (le_refl L) (le_refl n) (by omega) (by omega) h1 c2 hrefl
  · -- kind = 1 : Mirror (e1, e2, b, c)
    rw [hkind] at hbody
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hbody
    rcases hbody with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb_odd, hc_odd⟩, hbc⟩, he⟩, hdioph⟩, hgcd⟩, hzb⟩, hqb⟩, hL55⟩, hLlt⟩, hwlo⟩, hwhi⟩, hLhi⟩, hbound⟩, hbud⟩
    set e1 := q.a1; set e2 := q.a2; set b := q.a3; set c := q.a4
    have he_sq : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    have hbc_sq : b * b < c * c := Nat.mul_lt_mul'' hbc hbc
    have h2e1 : 2 * e1 * e1 = 2 * (e1 * e1) := Nat.mul_assoc 2 e1 e1
    have h2b : 2 * b * b = 2 * (b * b) := Nat.mul_assoc 2 b b
    set L := b * b - n
    set w1 := 2 * e1 * e1 + 1 - (2 * L + e2 * e2)
    have hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2)) := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hgcd, S3.natAbsDiff_eq]; push_cast; rfl
    obtain ⟨c2, hrefl, _, _, _⟩ := S2.mirror_4sq_cycle (w1 := w1) hb_odd hc_odd hbc he hdioph hcop
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega : n = b * b - L)
    obtain ⟨hb4, hb5, hb6, hb7⟩ := S3.checkBudgetRange_sound hbud hlo hhi
      (by omega : b * b - q.hi - 1 ≤ L - 1) (by omega : L - 1 ≤ b * b - q.lo - 1)
    have h1 := invSmall_mono hb4 hb5 hb6 hb7 (ih (L - 1) (by omega) (by omega))
    rw [hzb] at hpq
    exact S1.small_edge_merge (by omega) (by omega) hs' hpq hpleq
      (le_refl L) (le_refl n) (by omega) (by omega) h1 c2 hrefl
  · -- kind = 2 : 3-Cross (e1, e2, b, e3)
    rw [hkind] at hbody
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hbody
    rcases hbody with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb_odd, he12⟩, he23⟩, hdioph⟩, hgcd⟩, hzb⟩, hqb⟩, hL55⟩, hLlt⟩, hwlo⟩, hwhi⟩, hw3b⟩, hbound⟩, hbud⟩
    set e1 := q.a1; set e2 := q.a2; set b := q.a3; set e3 := q.a4
    have he12_sq : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he12 he12
    have h2e1 : 2 * e1 * e1 = 2 * (e1 * e1) := Nat.mul_assoc 2 e1 e1
    have h2e2 : 2 * e2 * e2 = 2 * (e2 * e2) := Nat.mul_assoc 2 e2 e2
    set L := b * b - n
    have hb2_odd : b * b % 2 = 1 := by
      have : b = 2 * (b / 2) + 1 := by omega
      rw [this]; ring_nf; omega
    set w1 := (2 * e1 * e1 + 1 - (2 * L + b * b)) / 2
    have hw1_eq : 2 * L + b * b + 2 * w1 = 2 * e1 * e1 + 1 := by omega
    have hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2)) := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hgcd, S3.natAbsDiff_eq]; push_cast; rfl
    obtain ⟨c2, hrefl⟩ := S2.three_cross_cycle (w1 := w1) hb_odd he12 he23 hdioph hcop
      (by omega) (by omega) (by omega) hw1_eq (by omega) (by omega : n = b * b - L)
    obtain ⟨hb4, hb5, hb6, hb7⟩ := S3.checkBudgetRange_sound hbud hlo hhi
      (by omega : b * b - q.hi - 1 ≤ L - 1) (by omega : L - 1 ≤ b * b - q.lo - 1)
    have h1 := invSmall_mono hb4 hb5 hb6 hb7 (ih (L - 1) (by omega) (by omega))
    rw [hzb] at hpq
    exact S1.small_edge_merge (by omega) (by omega) hs' hpq hpleq
      (le_refl L) (le_refl n) (by omega) (by omega) h1 c2 hrefl
  · -- kind = 3 : SM1-J1 (b1, b2, e1, e2)
    rw [hkind] at hbody
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hbody
    rcases hbody with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb1_odd, hb2_odd⟩, hb12⟩, he⟩, hdioph⟩, hgcd⟩, hzb1⟩, hD1⟩, hqlo⟩, hL55⟩, hwlo⟩, hwhi⟩, hJ1⟩, hJ2⟩, hb1le⟩, hbound⟩, hbud⟩
    set b1 := q.a1; set b2 := q.a2; set e1 := q.a3; set e2 := q.a4
    have he_sq : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    have hb12_sq : b1 * b1 < b2 * b2 := Nat.mul_lt_mul'' hb12 hb12
    have h2e1 : 2 * e1 * e1 = 2 * (e1 * e1) := Nat.mul_assoc 2 e1 e1
    set D := e2 * e2 - e1 * e1
    set L := n + 1 - 2 * D
    set w1 := 2 * e1 * e1 + 1 - (2 * L + e2 * e2)
    have hcop : Nat.Coprime D (Int.natAbs ((b1 : ℤ) * b1 - (e1 : ℤ) * e1)) := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hgcd, S3.natAbsDiff_eq]; push_cast; rfl
    obtain ⟨c2, hrefl1, _⟩ := S2.split_m1_2cross_cycle (w1 := w1) hb1_odd hb2_odd hb12 he hdioph hcop
      (by omega) (by omega) (by omega) (by omega) (by omega : n = L + 2 * D - 1) (by omega) (by omega)
    obtain ⟨hb4, hb5, hb6, hb7⟩ := S3.checkBudgetRange_sound hbud hlo hhi
      (by omega : q.lo + 1 - 2 * D - 1 ≤ L - 1) (by omega : L - 1 ≤ q.hi + 1 - 2 * D - 1)
    have h1 := invSmall_mono hb4 hb5 hb6 hb7 (ih (L - 1) (by omega) (by omega))
    rw [hzb1] at hpq
    exact S1.small_edge_merge (by omega) (by omega) hs' hpq hpleq
      (le_refl L) (by omega : b1 * b1 - L ≤ n) (by omega : L + (b1 * b1 - L) = b1 * b1)
      (by omega) h1 c2 hrefl1
  · -- kind = 4 : SM1-J2 (b1, b2, e1, e2)
    rw [hkind] at hbody
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hbody
    rcases hbody with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb1_odd, hb2_odd⟩, hb12⟩, he⟩, hdioph⟩, hgcd⟩, hzb2⟩, hD1⟩, hqlo⟩, hL55⟩, hwlo⟩, hwhi⟩, hJ1⟩, hJ2⟩, hqb2⟩, hLqb2⟩, hbound⟩, hbud⟩
    set b1 := q.a1; set b2 := q.a2; set e1 := q.a3; set e2 := q.a4
    have he_sq : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    have hb12_sq : b1 * b1 < b2 * b2 := Nat.mul_lt_mul'' hb12 hb12
    have h2e1 : 2 * e1 * e1 = 2 * (e1 * e1) := Nat.mul_assoc 2 e1 e1
    set D := e2 * e2 - e1 * e1
    set L := n + 1 - 2 * D
    set w1 := 2 * e1 * e1 + 1 - (2 * L + e2 * e2)
    have hcop : Nat.Coprime D (Int.natAbs ((b1 : ℤ) * b1 - (e1 : ℤ) * e1)) := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hgcd, S3.natAbsDiff_eq]; push_cast; rfl
    obtain ⟨c2, _, hrefl2⟩ := S2.split_m1_2cross_cycle (w1 := w1) hb1_odd hb2_odd hb12 he hdioph hcop
      (by omega) (by omega) (by omega) (by omega) (by omega : n = L + 2 * D - 1) (by omega) (by omega)
    obtain ⟨hb4, hb5, hb6, hb7⟩ := S3.checkBudgetRange_sound hbud hlo hhi
      (by omega : q.lo + 1 - 2 * D - 1 ≤ L - 1) (by omega : L - 1 ≤ q.hi + 1 - 2 * D - 1)
    have h1 := invSmall_mono hb4 hb5 hb6 hb7 (ih (L - 1) (by omega) (by omega))
    rw [hzb2] at hpq
    exact S1.small_edge_merge (by omega) (by omega) hs' hpq hpleq
      (by omega : L ≤ b2 * b2 - n) (le_refl n) (by omega : (b2 * b2 - n) + n = b2 * b2)
      (by omega) h1 c2 hrefl2
  · rw [hkind] at hbody; simp at hbody

theorem lower_all_invSmall : ∀ n, 54 ≤ n → n ≤ 19856 →
    InvSmall (S3.req4 n) (S3.req5 n) (S3.req6 n) (S3.req7 n) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h54 hhi
    rcases S3.lower_covered_all n h54 hhi with ⟨p, hp_mem, hp_eq⟩ | ⟨w, hw_mem, hw_eq⟩ | ⟨q, hq_mem, hq_lo, hq_hi⟩
    · have hbase := S3.base_cycles_verified p hp_mem
      rw [hp_eq] at hbase
      have hb := S3.req_bounds n
      exact invSmall_mono hb.1.2 hb.2.1.2 hb.2.2.1.2 hb.2.2.2.2 hbase
    · have hw := S3.iso_witnesses_verified w hw_mem
      have hw_com := hw
      simp only [S3.checkIsoWitness, S3.checkIsoCommon, Bool.and_eq_true, Nat.ble_eq] at hw_com
      have hL55 : 55 ≤ w.L := hw_com.1.1.1.1.1.1.1.1.1.1.1.1
      have hLR : w.L + 1 ≤ w.R := hw_com.1.1.1.1.1.1.1.1.1.1.1.2
      rw [← hw_eq]
      exact iso_step hw (ih (w.L - 1) (by omega) (by omega) (by omega))
    · exact lowerQuad_step (S3.lower_quads_verified q hq_mem) hq_lo hq_hi
        (fun m hm1 hm2 => ih m hm2 hm1 (by omega))

private lemma upperQuad_step {q : S3.UpperQuad} {n : ℕ}
    (hq : S3.checkUpperQuad q = true) (hlo : q.lo ≤ n) (hhi : n ≤ q.hi)
    (ih : ∀ m, 54 ≤ m → m < n → InvMod5 m) : InvMod5 n := by
  unfold S3.checkUpperQuad at hq
  simp only [Bool.and_eq_true, Nat.ble_eq] at hq
  rcases hq with ⟨hlohi, hbody⟩
  cases hm : q.isMirror
  · rw [hm] at hbody
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hbody
    rcases hbody with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha_odd, hb_odd⟩, hab⟩, he⟩, hdioph⟩, hgcd⟩, hqb⟩, hL55⟩, hLlt⟩, h18⟩, hwlo⟩, hwhi⟩, hLhi⟩, hrepl⟩
    set a := q.a1; set b := q.a2; set e1 := q.a3; set e2 := q.a4
    have he_sq : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    have hab_sq : a * a < b * b := Nat.mul_lt_mul'' hab hab
    set L := b * b - n
    set w1 := 2 * L + e2 * e2 - (a * a + b * b + 1)
    have hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((e1 : ℤ) * e1 - (b : ℤ) * b)) := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hgcd, S3.natAbsDiff_eq]; push_cast; rfl
    obtain ⟨c2, hrefl, ha_e, he1_e, he2_e⟩ := S2.left_4sq_cycle (w1 := w1) ha_odd hb_odd hab he hdioph hcop
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega : n = b * b - L)
    exact S1.brahmagupta_merge (by omega) hb_odd (by omega) (by omega : n = b * b - L)
      (ih (L - 1) (by omega) (by omega)) c2 hrefl
      (checkMod5Repl_sound (by omega) c2 hrepl ha_e he1_e he2_e)
  · rw [hm] at hbody
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hbody
    rcases hbody with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb_odd, hc_odd⟩, hbc⟩, he⟩, hdioph⟩, hgcd⟩, hqb⟩, hL55⟩, hLlt⟩, h18⟩, hwlo⟩, hwhi⟩, hLhi⟩, hrepl⟩
    set e1 := q.a1; set e2 := q.a2; set b := q.a3; set c := q.a4
    have he_sq : e1 * e1 < e2 * e2 := Nat.mul_lt_mul'' he he
    have hbc_sq : b * b < c * c := Nat.mul_lt_mul'' hbc hbc
    have h2e1 : 2 * e1 * e1 = 2 * (e1 * e1) := Nat.mul_assoc 2 e1 e1
    have h2b : 2 * b * b = 2 * (b * b) := Nat.mul_assoc 2 b b
    set L := b * b - n
    set w1 := 2 * e1 * e1 + 1 - (2 * L + e2 * e2)
    have hcop : Nat.Coprime (e2 * e2 - e1 * e1) (Int.natAbs ((b : ℤ) * b - (e2 : ℤ) * e2)) := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hgcd, S3.natAbsDiff_eq]; push_cast; rfl
    obtain ⟨c2, hrefl, hc_e, he1_e, he2_e⟩ := S2.mirror_4sq_cycle (w1 := w1) hb_odd hc_odd hbc he hdioph hcop
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega : n = b * b - L)
    exact S1.brahmagupta_merge (by omega) hb_odd (by omega) (by omega : n = b * b - L)
      (ih (L - 1) (by omega) (by omega)) c2 hrefl
      (checkMod5Repl_sound (by omega) c2 hrepl hc_e he1_e he2_e)

theorem all_invMod5 : ∀ n, 54 ≤ n → InvMod5 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h54
    by_cases h1 : n ≤ 19856
    · have hsm := lower_all_invSmall n h54 h1
      have hb := S3.req_bounds n
      exact S1.invSmall_to_invMod5 (invSmall_mono hb.1.1 hb.2.1.1 hb.2.2.1.1 hb.2.2.2.1 hsm)
    · by_cases h2 : n ≤ 461456
      · obtain ⟨q, hq_mem, hq_lo, hq_hi⟩ := S3.upper_covered_all n (by omega) h2
        exact upperQuad_step (S3.upper_quads_verified q hq_mem) hq_lo hq_hi
          (fun m hm1 hm2 => ih m hm2 hm1)
      · obtain ⟨L, b, hL55, hLn, hb_odd, h18, hn_eq, c2, hrefl, hrepl⟩ :=
          S2.infinite_mirror_step n (by omega)
        exact S1.brahmagupta_merge (by omega) hb_odd h18 hn_eq
          (ih (L - 1) (by omega) (by omega)) c2 hrefl hrepl

theorem main_proof : ∀ n : ℕ, 25 ≤ n → HasHamPath n := by
  intro n hn
  by_cases h53 : n ≤ 53
  · exact S3.base_paths_25_53 n hn h53
  · exact S1.invMod5_to_hasHamPath (by omega) (all_invMod5 n (by omega))

end MSE2637546.Final

theorem OMA.solution : type_of% @OMA.S_mse_2637546.main :=
  MSE2637546.Final.main_proof

