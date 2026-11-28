import OMAReductions.R_Erdos23_erdos_23_variants_n5_R1_H2_R1_H1_R1
import Mathlib

-- Problem: Erdős Problem 23 — n5, step R1.H2.R1.H1.R1.H2
-- Credit: @hyprspacecoyote (the owner of the agent is credited as the solver)

/-! A degree-12 root whose 12-vertex core is bipartite with at least 28 edges, and at most
65 edges outside the core.

The core is classified up to isomorphism: every triangle-free graph on 12 vertices with at
least 28 edges is one of 955 explicit graphs, proved by induction on the number of vertices
(delete a vertex of minimum degree) with kernel-checked isomorphism certificates, packed as
natural numbers. For each listed graph the kernel checks either an odd cycle (so it is not the
bipartite core) or a weighted family of cuts of the core: for every independent set the
weighted cost of a root neighbour with that neighbourhood is at most a + m * size, and the
weighted total stays below 26. The root neighbourhoods are independent sets of total size at
most 53, so some cut, completed by putting every neighbour on its cheaper side, leaves at
most 25 same-side edges.
-/

namespace TFClass

open Finset

abbrev Gr (k : ℕ) := Fin k → Fin k → Bool

def adjOf (k b : ℕ) : Gr k := fun i j => b.testBit (i.val * k + j.val)

def ecount {k : ℕ} (A : Gr k) : ℕ := ∑ i, ∑ j, if A i j then 1 else 0

def deg {k : ℕ} (A : Gr k) (x : Fin k) : ℕ := ∑ j, if A x j then 1 else 0

structure Good {k : ℕ} (A : Gr k) : Prop where
  symm : ∀ i j, A i j = A j i
  irrefl : ∀ i, A i i = false
  tf : ∀ i j l, A i j = true → A j l = true → A i l = true → False

def ClassP (k : ℕ) (L : ℕ → Prop) (t : ℕ) : Prop :=
  ∀ A : Gr k, Good A → t ≤ ecount A →
    ∃ b, L b ∧ ∃ σ : Equiv.Perm (Fin k), ∀ i j, A (σ i) (σ j) = adjOf k b i j

def ext {n : ℕ} (B : Gr n) (N : Fin n → Bool) : Gr (n+1) :=
  fun i j => Fin.cases (Fin.cases false N j) (fun i' => Fin.cases (N i') (B i') j) i

def popc {n : ℕ} (m : ℕ) : ℕ := ∑ i : Fin n, if m.testBit i.val then 1 else 0

def StepP (n : ℕ) (Lp Ln : ℕ → Prop) (t : ℕ) : Prop :=
  ∀ b, Lp b → ∀ m < 2^n,
    (∀ i j : Fin n, m.testBit i.val = true → m.testBit j.val = true → adjOf n b i j = false) →
    t ≤ ecount (adjOf n b) + 2 * popc (n := n) m →
    ∃ b', Ln b' ∧ ∃ π : Equiv.Perm (Fin (n+1)), ∀ i j,
      ext (adjOf n b) (fun x => m.testBit x.val) (π i) (π j) = adjOf (n+1) b' i j

lemma exists_mask : ∀ (n : ℕ) (N : Fin n → Bool), ∃ m < 2^n, ∀ i : Fin n, m.testBit i.val = N i
  | 0, _ => ⟨0, by simp, fun i => i.elim0⟩
  | n+1, N => by
    obtain ⟨m, hm, h⟩ := exists_mask n (fun i => N i.succ)
    refine ⟨2*m + (if N 0 then 1 else 0), ?_, ?_⟩
    · rw [pow_succ]; split <;> omega
    · intro i
      cases i using Fin.cases with
      | zero => simp only [Fin.val_zero, Nat.testBit_zero]; split <;> simp_all
      | succ i =>
        simp only [Fin.val_succ, Nat.testBit_succ]
        rw [← h i]; congr 1; split <;> omega

lemma ecount_perm {k : ℕ} (A : Gr k) (σ : Equiv.Perm (Fin k)) :
    ecount (fun i j => A (σ i) (σ j)) = ecount A := by
  unfold ecount
  rw [← Equiv.sum_comp σ (fun i => ∑ j, if A i j then 1 else 0)]
  apply Finset.sum_congr rfl; intro i _
  exact Equiv.sum_comp σ (fun j => if A (σ i) j then 1 else 0)

lemma deg_perm {k : ℕ} (A : Gr k) (σ : Equiv.Perm (Fin k)) (x : Fin k) :
    deg (fun i j => A (σ i) (σ j)) x = deg A (σ x) := by
  unfold deg
  exact Equiv.sum_comp σ (fun j => if A (σ x) j then 1 else 0)

lemma good_perm {k : ℕ} {A : Gr k} (hA : Good A) (σ : Equiv.Perm (Fin k)) :
    Good (fun i j => A (σ i) (σ j)) where
  symm i j := hA.symm _ _
  irrefl i := hA.irrefl _
  tf i j l h1 h2 h3 := hA.tf _ _ _ h1 h2 h3

lemma ecount_eq_sum_deg {k : ℕ} (A : Gr k) : ecount A = ∑ x, deg A x := rfl

lemma ecount_succ {n : ℕ} (A : Gr (n+1)) (hA : Good A) :
    ecount A = ecount (fun i j : Fin n => A i.succ j.succ) + 2 * deg A 0 := by
  unfold ecount deg
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ (f := fun j => if A _ j = true then 1 else 0)]
  rw [hA.irrefl 0]
  have hs : (∑ i : Fin n, if A i.succ 0 = true then 1 else 0) =
      ∑ j : Fin n, if A 0 j.succ = true then 1 else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [hA.symm]
  rw [Finset.sum_add_distrib, hs]
  simp only [Bool.false_eq_true, if_false, zero_add]
  ring

lemma good_succ {n : ℕ} {A : Gr (n+1)} (hA : Good A) : Good (fun i j : Fin n => A i.succ j.succ) where
  symm i j := hA.symm _ _
  irrefl i := hA.irrefl _
  tf i j l h1 h2 h3 := hA.tf _ _ _ h1 h2 h3

lemma min_deg {k : ℕ} (A : Gr (k+1)) : ∃ x, (k+1) * deg A x ≤ ecount A := by
  obtain ⟨x, -, hx⟩ := Finset.exists_min_image Finset.univ (deg A) Finset.univ_nonempty
  refine ⟨x, ?_⟩
  rw [ecount_eq_sum_deg]
  have := Finset.card_nsmul_le_sum Finset.univ (deg A) (deg A x) (fun y _ => hx y (mem_univ y))
  simpa using this

theorem stepP (n : ℕ) (Lp Ln : ℕ → Prop) (tp tn : ℕ)
    (hok : StepP n Lp Ln tn)
    (hT : ∀ E d : ℕ, tn ≤ E → (n+1) * d ≤ E → tp + 2 * d ≤ E)
    (IH : ClassP n Lp tp) : ClassP (n+1) Ln tn := by
  intro A hA hE
  obtain ⟨x, hx⟩ := min_deg A
  let τ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 x
  let A1 : Gr (n+1) := fun i j => A (τ i) (τ j)
  have g1 : Good A1 := good_perm hA τ
  have e1 : ecount A1 = ecount A := ecount_perm A τ
  have d1 : deg A1 0 = deg A x := by
    simp only [A1, deg_perm, τ, Equiv.swap_apply_left]
  let A0 : Gr n := fun i j => A1 i.succ j.succ
  have e0 : ecount A1 = ecount A0 + 2 * deg A1 0 := ecount_succ A1 g1
  obtain ⟨b', hb', σ', hσ'⟩ := IH A0 (good_succ g1) (by
    have := hT (ecount A) (deg A x) hE hx
    change tp ≤ ecount A0
    omega)
  let σ'' : Equiv.Perm (Fin (n+1)) := Equiv.Perm.decomposeFin.symm (0, σ')
  have s0 : σ'' 0 = 0 := Equiv.Perm.decomposeFin_symm_apply_zero _ _
  have ss : ∀ i : Fin n, σ'' i.succ = (σ' i).succ := by
    intro i
    simp [σ'', Equiv.Perm.decomposeFin_symm_apply_succ]
  let A2 : Gr (n+1) := fun i j => A1 (σ'' i) (σ'' j)
  have g2 : Good A2 := good_perm g1 σ''
  let N : Fin n → Bool := fun j => A2 0 j.succ
  have hext : ∀ i j, A2 i j = ext (adjOf n b') N i j := by
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp [ext, g2.irrefl]
      | succ j => simp [ext, N]
    | succ i =>
      cases j using Fin.cases with
      | zero => simp [ext, N, g2.symm (i.succ) 0]
      | succ j =>
        simp only [ext, Fin.cases_succ]
        rw [← hσ' i j]
        simp [A2, A0, ss]
  obtain ⟨m, hm, hmN⟩ := exists_mask n N
  have hN : (fun x : Fin n => m.testBit x.val) = N := funext hmN
  have indep : ∀ i j : Fin n, m.testBit i.val = true → m.testBit j.val = true →
      adjOf n b' i j = false := by
    intro i j hi hj
    rw [hmN] at hi hj
    by_contra hb
    have hb' : adjOf n b' i j = true := by simpa using hb
    have h3 : A2 i.succ j.succ = true := by
      rw [hext]; simpa [ext] using hb'
    exact g2.tf 0 i.succ j.succ hi h3 hj
  have cnt : tn ≤ ecount (adjOf n b') + 2 * popc (n := n) m := by
    have e2 := ecount_succ A2 g2
    have e2' : ecount A2 = ecount A1 := ecount_perm A1 σ''
    have eb : ecount (fun i j : Fin n => A2 i.succ j.succ) = ecount (adjOf n b') := by
      congr 1; funext i j; rw [hext]; simp [ext]
    have pc : deg A2 0 = popc (n := n) m := by
      unfold deg popc
      rw [Fin.sum_univ_succ, g2.irrefl]
      simp only [Bool.false_eq_true, if_false, zero_add]
      apply Finset.sum_congr rfl; intro j _; rw [hmN]
    omega
  obtain ⟨b'', hb''L, π, hπ⟩ := hok b' hb' m hm indep cnt
  refine ⟨b'', hb''L, π.trans (σ''.trans τ), ?_⟩
  intro i j
  have := hπ i j
  rw [hN] at this
  rw [← this, ← hext]
  rfl

/-! Kernel-friendly computations -/

/-- neighbourhood of `i` as a bit mask -/
def row (n b i : ℕ) : ℕ := (b >>> (i * n)) % 2 ^ n

/-- independent masks: vertices `i-1, …, 0` still to decide, `acc` the chosen higher ones -/
def gen (n b : ℕ) : ℕ → ℕ → List ℕ
  | 0, acc => [acc]
  | i+1, acc => gen n b i acc ++
      (if row n b i &&& acc == 0 then gen n b i (acc ||| 2 ^ i) else [])

def pcF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f+1, m => m % 2 + pcF f (m / 2)

def extAdj (n b m i j : ℕ) : Bool :=
  if i = 0 then (if j = 0 then false else m.testBit (j - 1))
  else if j = 0 then m.testBit (i - 1) else b.testBit ((i - 1) * n + (j - 1))

/-! Bit lemmas -/

lemma testBit_row (n b i j : ℕ) : (row n b i).testBit j = (decide (j < n) && b.testBit (i * n + j)) := by
  simp [row, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.add_comm]

lemma land_eq_zero_iff (a c : ℕ) : a &&& c = 0 ↔ ∀ j, ¬ (a.testBit j = true ∧ c.testBit j = true) := by
  constructor
  · intro h j hj
    have := congrArg (fun x => x.testBit j) h
    simp [Nat.testBit_land, hj.1, hj.2] at this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_land, Nat.zero_testBit]
    by_cases ha : a.testBit j <;> by_cases hc : c.testBit j <;> simp_all

/-- the bits of `m` at positions `≥ i` -/
def hi (m i : ℕ) : ℕ := m >>> i <<< i

lemma testBit_hi (m i j : ℕ) : (hi m i).testBit j = (decide (i ≤ j) && m.testBit j) := by
  unfold hi
  rw [Nat.testBit_shiftLeft]
  by_cases h : i ≤ j
  · simp [h, Nat.testBit_shiftRight, Nat.add_sub_cancel' h]
  · simp [h]

lemma hi_zero (m : ℕ) : hi m 0 = m := by simp [hi]

lemma hi_succ_false {m i : ℕ} (h : m.testBit i = false) : hi m (i+1) = hi m i := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_hi, testBit_hi]
  by_cases hj : j = i
  · subst hj; simp [h]
  · by_cases hij : i + 1 ≤ j
    · simp [hij, show i ≤ j by omega]
    · simp [hij, show ¬ i ≤ j by omega]

lemma hi_succ_true {m i : ℕ} (h : m.testBit i = true) : hi m (i+1) ||| 2 ^ i = hi m i := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_lor, testBit_hi, testBit_hi, Nat.testBit_two_pow]
  by_cases hj : j = i
  · subst hj; simp [h]
  · have : i ≠ j := fun e => hj e.symm
    by_cases hij : i + 1 ≤ j
    · simp [hij, show i ≤ j by omega, this]
    · simp [hij, show ¬ i ≤ j by omega, this]

lemma gen_complete_aux (n b m : ℕ)
    (ind : ∀ i j, i < n → j < n → m.testBit i = true → m.testBit j = true →
      b.testBit (i * n + j) = false) :
    ∀ i, i ≤ n → m ∈ gen n b i (hi m i) := by
  intro i
  induction i with
  | zero => intro _; simp [gen, hi_zero]
  | succ i ih =>
    intro hle
    simp only [gen, List.mem_append]
    cases hmi : m.testBit i with
    | false => left; rw [hi_succ_false hmi]; exact ih (by omega)
    | true =>
      right
      have hz : (row n b i &&& hi m (i+1) == 0) = true := by
        rw [beq_iff_eq, land_eq_zero_iff]
        rintro j ⟨h1, h2⟩
        rw [testBit_row] at h1
        rw [testBit_hi] at h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
        have := ind i j (by omega) h1.1 hmi h2.2
        rw [this] at h1; exact absurd h1.2 (by simp)
      rw [if_pos hz, hi_succ_true hmi]
      exact ih (by omega)

lemma gen_complete (n b m : ℕ) (hm : m < 2 ^ n)
    (ind : ∀ i j, i < n → j < n → m.testBit i = true → m.testBit j = true →
      b.testBit (i * n + j) = false) : m ∈ gen n b n 0 := by
  have h := gen_complete_aux n b m ind n le_rfl
  have : hi m n = 0 := by
    unfold hi; rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hm]; simp
  rwa [this] at h


lemma pcF_eq : ∀ (n m : ℕ), pcF n m = popc (n := n) m
  | 0, m => by simp [pcF, popc]
  | n+1, m => by
    unfold popc
    rw [Fin.sum_univ_succ, pcF, pcF_eq n (m / 2)]
    unfold popc
    congr 1
    · simp only [Fin.val_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
    · apply Finset.sum_congr rfl; intro i _
      simp [Fin.val_succ, Nat.testBit_succ]

lemma extAdj_eq (n b m : ℕ) (i j : Fin (n+1)) :
    extAdj n b m i.val j.val = ext (adjOf n b) (fun x : Fin n => m.testBit x.val) i j := by
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [extAdj, ext]
    | succ j => simp [extAdj, ext]
  | succ i =>
    cases j using Fin.cases with
    | zero => simp [extAdj, ext]
    | succ j => simp [extAdj, ext, adjOf]


/-! Packed certificates -/

def slot (P w i : ℕ) : ℕ := (P >>> (w * i)) % 2 ^ w

def inP (k P cnt : ℕ) (b : ℕ) : Prop := ∃ i < cnt, b = slot P (k * k) i

/-- `bitsOf f N` has bit `x` equal to `f x` for `x < N`. -/
def bitsOf (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | N+1 => bitsOf f N ||| (if f N then 2 ^ N else 0)

lemma testBit_bitsOf (f : ℕ → Bool) : ∀ N x, (bitsOf f N).testBit x = (decide (x < N) && f x)
  | 0, x => by simp [bitsOf]
  | N+1, x => by
    simp only [bitsOf, Nat.testBit_lor, testBit_bitsOf f N x]
    by_cases hx : x = N
    · subst hx; cases f x <;> simp
    · have : (if f N = true then 2 ^ N else 0).testBit x = false := by
        split <;> simp [Nat.testBit_two_pow, Ne.symm hx]
      rw [this]
      by_cases h : x < N
      · simp [h, show x < N + 1 by omega]
      · simp [h, show ¬ x < N + 1 by omega]

/-- certificate layout: class index (10 bits), then the permutation `p` (4 bits per vertex) -/
def cidx (c : ℕ) : ℕ := c % 1024
def pv (c i : ℕ) : ℕ := (c >>> (10 + 4 * i)) % 16

def permCode (n b m c : ℕ) : ℕ :=
  bitsOf (fun x => extAdj n b m (pv c (x / (n+1))) (pv c (x % (n+1)))) ((n+1) * (n+1))

def injOK (k c : ℕ) : Bool :=
  (List.range k).all (fun i => decide (pv c i < k) &&
    (List.range k).all (fun j => (i == j) || !(pv c i == pv c j)))
def isoP (n b m c Pn : ℕ) : Bool :=
  injOK (n+1) c && (permCode n b m c == slot Pn ((n+1) * (n+1)) (cidx c))

def consume (n b Pn cntN : ℕ) : List ℕ → ℕ → Bool
  | [], D => D == 0
  | m :: ms, D => decide (cidx (D % 2 ^ 64) < cntN) && isoP n b m (D % 2 ^ 64) Pn &&
      consume n b Pn cntN ms (D >>> 64)

def blocksOK (n t Pp Pn cntN : ℕ) : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | i, (b, e, D) :: rest => (slot Pp (n * n) i == b) && decide (ecount (adjOf n b) = e) &&
      consume n b Pn cntN ((gen n b n 0).filter (fun m => decide (t ≤ e + 2 * pcF n m))) D &&
      blocksOK n t Pp Pn cntN (i+1) rest

lemma blocksOK_app {n t Pp Pn cntN i0 k : ℕ} {l1 l2 : List (ℕ × ℕ × ℕ)}
    (h1 : blocksOK n t Pp Pn cntN i0 l1 = true) (hl : l1.length = k)
    (h2 : blocksOK n t Pp Pn cntN (i0 + k) l2 = true) :
    blocksOK n t Pp Pn cntN i0 (l1 ++ l2) = true := by
  subst hl
  induction l1 generalizing i0 with
  | nil => simpa using h2
  | cons a l ih =>
    obtain ⟨b, e, D⟩ := a
    rw [List.cons_append]
    simp only [blocksOK, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ih h1.2 ?_⟩
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h2

lemma isoP_sound {n b m c Pn : ℕ} (h : isoP n b m c Pn = true) :
    ∃ π : Equiv.Perm (Fin (n+1)), ∀ i j,
      ext (adjOf n b) (fun x => m.testBit x.val) (π i) (π j) =
        adjOf (n+1) (slot Pn ((n+1) * (n+1)) (cidx c)) i j := by
  unfold isoP at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hinj, hcode⟩ := h
  unfold injOK at hinj
  rw [List.all_eq_true] at hinj
  have H : ∀ i : Fin (n+1), _ := fun i => hinj i.val (List.mem_range.mpr i.isLt)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at H
  let P : Fin (n+1) → Fin (n+1) := fun i => ⟨pv c i.val, (H i).1⟩
  have Pinj : Function.Injective P := by
    intro i j hij
    by_contra hne
    have := (H i).2 j.val j.isLt
    rcases this with h1 | h1
    · exact hne (Fin.ext h1)
    · have : pv c i.val = pv c j.val := congrArg Fin.val hij
      simp [this] at h1
  let π : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective P (Finite.injective_iff_bijective.mp Pinj)
  refine ⟨π, fun i j => ?_⟩
  have hk : 0 < n + 1 := Nat.succ_pos n
  have hlt : i.val * (n+1) + j.val < (n+1) * (n+1) := by
    have := i.isLt; have := j.isLt; nlinarith
  have hdiv : (i.val * (n+1) + j.val) / (n+1) = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt j.isLt, add_zero]
  have hmod : (i.val * (n+1) + j.val) % (n+1) = j.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
  show _ = (slot Pn ((n+1) * (n+1)) (cidx c)).testBit (i.val * (n+1) + j.val)
  rw [← hcode, permCode, testBit_bitsOf, hdiv, hmod, ← extAdj_eq]
  simp [hlt, π, P]

lemma consume_sound (n b Pn cntN : ℕ) : ∀ (ms : List ℕ) (D : ℕ), consume n b Pn cntN ms D = true →
    ∀ m ∈ ms, ∃ j < cntN, ∃ π : Equiv.Perm (Fin (n+1)), ∀ x y,
      ext (adjOf n b) (fun z => m.testBit z.val) (π x) (π y) =
        adjOf (n+1) (slot Pn ((n+1) * (n+1)) j) x y
  | [], _, _ => by simp
  | m :: ms, D, h => by
    simp only [consume, Bool.and_eq_true, decide_eq_true_eq] at h
    intro m' hm'
    rcases List.mem_cons.mp hm' with rfl | hm'
    · obtain ⟨π, hπ⟩ := isoP_sound h.1.2
      exact ⟨_, h.1.1, π, hπ⟩
    · exact consume_sound n b Pn cntN ms _ h.2 m' hm'

lemma blocksOK_sound (n t Pp Pn cntN : ℕ) : ∀ (blks : List (ℕ × ℕ × ℕ)) (i0 : ℕ),
    blocksOK n t Pp Pn cntN i0 blks = true → ∀ i, i0 ≤ i → i < i0 + blks.length →
    ∀ m < 2^n,
      (∀ x y : Fin n, m.testBit x.val = true → m.testBit y.val = true →
        adjOf n (slot Pp (n * n) i) x y = false) →
      t ≤ ecount (adjOf n (slot Pp (n * n) i)) + 2 * popc (n := n) m →
      ∃ j < cntN, ∃ π : Equiv.Perm (Fin (n+1)), ∀ x y,
        ext (adjOf n (slot Pp (n * n) i)) (fun z => m.testBit z.val) (π x) (π y) =
          adjOf (n+1) (slot Pn ((n+1) * (n+1)) j) x y
  | [], _, _ => by intro i h1 h2; simp at h2; omega
  | (b, e, D) :: rest, i0, h => by
    simp only [blocksOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨hb, he⟩, hc⟩, hr⟩ := h
    intro i h1 h2 m hm ind dense
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rw [hb] at ind dense ⊢
      apply consume_sound n _ Pn cntN _ D hc m
      rw [List.mem_filter]
      refine ⟨gen_complete n _ m hm (fun x y hx hy h1 h2 => ind ⟨x, hx⟩ ⟨y, hy⟩ h1 h2), ?_⟩
      rw [decide_eq_true_eq, pcF_eq, ← he]; exact dense
    · exact blocksOK_sound n t Pp Pn cntN rest (i0+1) hr i hlt
        (by simp at h2; omega) m hm ind dense

theorem stepB_sound (n t Pp cntP Pn cntN : ℕ) (blks : List (ℕ × ℕ × ℕ))
    (hlen : blks.length = cntP) (h : blocksOK n t Pp Pn cntN 0 blks = true) :
    StepP n (inP n Pp cntP) (inP (n+1) Pn cntN) t := by
  intro b ⟨i, hi, hb⟩ m hm ind dense
  subst hb
  obtain ⟨j, hj, π, hπ⟩ := blocksOK_sound n t Pp Pn cntN blks 0 h i (Nat.zero_le _)
    (by rw [hlen]; omega) m hm ind dense
  exact ⟨_, ⟨j, hj, rfl⟩, π, hπ⟩

theorem baseP : ClassP 1 (inP 1 0 1) 0 := by
  intro A hA _
  refine ⟨0, ⟨0, by norm_num, by simp [slot]⟩, Equiv.refl _, ?_⟩
  intro i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [hA.irrefl, adjOf]


def P1 : ℕ := 0

def P2 : ℕ := 0x6

def B2_0 : List (ℕ × ℕ × ℕ) := [(0x0, 0, 0x4000)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB2_0 : blocksOK 1 1 P1 P2 1 0 B2_0 = true := by decide +kernel

def B2 : List (ℕ × ℕ × ℕ) := B2_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk2 : blocksOK 1 1 P1 P2 1 0 B2 = true := okB2_0

set_option maxRecDepth 100000 in
theorem len2 : B2.length = 1 := by decide +kernel

theorem cl2 : ClassP 2 (inP 2 P2 1) 1 :=
  stepP 1 _ _ 0 1 (stepB_sound 1 1 P1 1 P2 1 B2 len2 blk2) (by intro E d h1 h2; omega) baseP

def P3 : ℕ := 0xaa

def B3_0 : List (ℕ × ℕ × ℕ) := [(0x6, 2, 0x480000000000000084000)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB3_0 : blocksOK 2 3 P2 P3 1 0 B3_0 = true := by decide +kernel

def B3 : List (ℕ × ℕ × ℕ) := B3_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk3 : blocksOK 2 3 P2 P3 1 0 B3 = true := okB3_0

set_option maxRecDepth 100000 in
theorem len3 : B3.length = 1 := by decide +kernel

theorem cl3 : ClassP 3 (inP 3 P3 1) 3 :=
  stepP 2 _ _ 1 3 (stepB_sound 2 3 P2 1 P3 1 B3 len3 blk3) (by intro E d h1 h2; omega) cl2

def P4 : ℕ := 0x5a5a4b444a52

def B4_0 : List (ℕ × ℕ × ℕ) := [(0xaa, 4, 0xc84002000000000048c0000000000000c840010000000000c84000)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB4_0 : blocksOK 3 6 P3 P4 3 0 B4_0 = true := by decide +kernel

def B4 : List (ℕ × ℕ × ℕ) := B4_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk4 : blocksOK 3 6 P3 P4 3 0 B4 = true := okB4_0

set_option maxRecDepth 100000 in
theorem len4 : B4.length = 1 := by decide +kernel

theorem cl4 : ClassP 4 (inP 4 P4 3) 6 :=
  stepP 3 _ _ 3 6 (stepB_sound 3 6 P3 1 P4 3 B4 len4 blk4) (by intro E d h1 h2; omega) cl3

def P5 : ℕ := 0x26c94d93451648aa8aa

def B5_0 : List (ℕ × ℕ × ℕ) := [(0x4a52, 6, 0x48d00000000000010c840010000000010c84000),
  (0x4b44, 6, 0x10c840020000000004c810000000000008c410000000000010c40800),
  (0x5a5a, 8, 0xc8410020000000001048c000000000010480c020000000000c850000000000000850c00000000000048d000)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB5_0 : blocksOK 4 10 P4 P5 3 0 B5_0 = true := by decide +kernel

def B5 : List (ℕ × ℕ × ℕ) := B5_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk5 : blocksOK 4 10 P4 P5 3 0 B5 = true := okB5_0

set_option maxRecDepth 100000 in
theorem len5 : B5.length = 3 := by decide +kernel

theorem cl5 : ClassP 5 (inP 5 P5 3) 10 :=
  stepP 4 _ _ 6 10 (stepB_sound 4 10 P4 3 P5 3 B5 len5 blk5) (by intro E d h1 h2; omega) cl4

def P6 : ℕ := 0x4ec4d3b2c4ad492b5246a54a56a46a50b52446a50a56242b50b51442a54a54a

def B6_0 : List (ℕ × ℕ × ℕ) := [(0x8aa8aa, 10, 0x150c84004000000015048c0020000000150c840030000000150c840020000000150c840010000000150c84000),
  (0x9a28b2, 10, 0x550c08030000000114480c030000000150c8040300000000d1440803000000010c841403),
  (0x9b2536, 12, 0x150c84006000000008540d00400000000c54090040000000015084c000000000150c840050000000010c494010000000144c09004000000000d08540000000000090c54000000000004d09401)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB6_0 : blocksOK 5 14 P5 P6 7 0 B6_0 = true := by decide +kernel

def B6 : List (ℕ × ℕ × ℕ) := B6_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk6 : blocksOK 5 14 P5 P6 7 0 B6 = true := okB6_0

set_option maxRecDepth 100000 in
theorem len6 : B6.length = 3 := by decide +kernel

theorem cl6 : ClassP 6 (inP 6 P6 7) 14 :=
  stepP 5 _ _ 10 14 (stepB_sound 5 14 P5 3 P6 7 B6 len6 blk6) (by intro E d h1 h2; omega) cl5

def P7 : ℕ := 0x25b4952da4b6925b4892da44886b292ca54d6435941652a6321a8aca2b29510d454555159482aaa2aa8aaa

def B7_0 : List (ℕ × ℕ × ℕ) := [(0x42a54a54a, 14, 0x1950c840020000001950c840010000001950c84000),
  (0x42b50b514, 14, 0x1950c840040000001944d080030000001948d040030000001950c840030000001948c41000),
  (0x46a50a562, 14, 0xc859410030000001158480c03),
  (0x46a50b524, 14, 0x4d14818010000001950c80401),
  (0x46a54a56a, 16, 0xc958410040000000d0194480300000000d14858010000000c819450030000001850c814040000001940d084030000000c958410020000001850c814020000001840d09403),
  (0x4ad492b52, 16, 0x1950c84006000000049810d4040000000c981054040000000114c8580200000010980c540400000000d5085802000000005508d8020000001950c8400500000018900c540400000000d5885002000000005588d0020000000055890c02),
  (0x4ec4d3b2c, 18, 0x15084c18060000000114c8580400000000d5085804000000018904d4000000001890c41406000000009850d404000000005890d40400000001508c580000000000d5885004000000010984d40000000000c9851400000000005950c80400000000914c580000000000514c9800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB7_0 : blocksOK 6 19 P6 P7 7 0 B7_0 = true := by decide +kernel

def B7 : List (ℕ × ℕ × ℕ) := B7_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk7 : blocksOK 6 19 P6 P7 7 0 B7 = true := okB7_0

set_option maxRecDepth 100000 in
theorem len7 : B7.length = 7 := by decide +kernel

theorem cl7 : ClassP 7 (inP 7 P7 7) 19 :=
  stepP 6 _ _ 14 19 (stepB_sound 6 19 P6 7 P7 7 B7 len7 blk7) (by intro E d h1 h2; omega) cl6

def P8 : ℕ := 0x4bb44b4bb44bb4b449b64949b64949b643ac532c5353acac42ad522d5252ad5243ac512c53538cac43ac512c52538ca442ad502d52528d5243a857285728a8a842a956285629a94643a8542b542b949441aa552a552a55aa41aa542b542b549441aa542a552a558a40ab542b542b545440aa552a552a552a

def B8_0 : List (ℕ × ℕ × ℕ) := [(0x82aaa2aa8aaa, 20, 0x1d950c84004000001d85148c002000001d8d1484002000001d950c84003000001d950c84002000001d950c84001000001d950c84000),
  (0x86a2a2aa8aca, 20, 0x1c5148d8005000001d950c84005000001d950c80403000001c5148c1803),
  (0x86a2b28aca54, 20, 0x1d950c84007000001c1148c5805000001c550c81804000001d81148c402000001d948d04006000001d950c84006000001c41148d802),
  (0x86b282ca54c6, 20, 0x1d950c8400a000001d9508c4009000001d950c8400900000159c4c09002000001d950c84008000001d950c08402),
  (0x86b292ca54d6, 22, 0x1d950c8400c000001c4914c180a000001c4d148180a000000150d885c020000001158c49c03000001c550c8180a0000000d15885c0200000009158c5c02000001d950c8400b000001d810c854080000010d9c409407000001c550c09804000001d940d04806000001d940904c06000001c410c99408000001d8c0905406),
  (0x92da4496d224, 20, 0x1d950c8400d000000594108dc0b000000994104dc0b0000001588c51c07000001194084dc0b0000001590c49c070000001590c85c07000001590084dc0b0000001194c49c070000001194c85c070000000994d05c07000001d90084d40b000000119cc49407000000119cc85407000000099cd05407000000099cd45007),
  (0x96d254b692da, 24, 0x1d950c8400e0000008dc150580c0000010dc148580c0000001590c85c040000014dc108580c0000001194c85c040000000994d05c040000001d90c85400000001cd5048180d000000194508dc0b000000194d085c0b000000194d049c01000001cd4108580c000000119cc85404000000099cd054040000001590c85c00000000099cd450040000001194c85c000000000d59085c0b0000000d59049c010000000994d05c0000000005590c9c01)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB8_0 : blocksOK 7 25 P7 P8 15 0 B8_0 = true := by decide +kernel

def B8 : List (ℕ × ℕ × ℕ) := B8_0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk8 : blocksOK 7 25 P7 P8 15 0 B8 = true := okB8_0

set_option maxRecDepth 100000 in
theorem len8 : B8.length = 7 := by decide +kernel

theorem cl8 : ClassP 8 (inP 8 P8 15) 25 :=
  stepP 7 _ _ 19 25 (stepB_sound 7 25 P7 7 P8 15 B8 len8 blk8) (by intro E d h1 h2; omega) cl7

def P9 : ℕ := 0x4b5a12c96b425ad1680024ed89349db12693b65b1256d4924ada92495b52485ad294b4a552d694b5a4256d485b52292b6a45221ab0a22ca914d19a48990b5a509694aa58d296b485ad284b4a452c694b4a4256d405b5229236a45221ea0af282bca150a85410953561455852a9a314886a8aa0aca82b4a6528641d515654559515754aa20aaaaa2a2a8aaaaaaa290555551515454555550482aa2a8aaaa2aaaaa8284155154545595157540a20aa8aa2a2a8aaaaaa829075454959525654ca2a883aa2a0aea82baa251284155150565495953290b20ea8a92a2aca8ab8a551075454951545455c528883aa2a0aaaa2aaaa292841d5150545595157148a20aaaa82a2a8aaaa8aa290554541555455554545481ab2a4aca92b2a5535640d5950575415d50a894206aca82b2a4aca954c59035654159505654aa60c80abaa0aea82baa150a840d515654559515654aa206a8aa2aaa8aaaa2aca90354551515654559522881aa2a8a8aa2aaa8ab0a40555545555155545555202aaaa2a2a8aaaa2aa29015455951565455950a880aa2a8aaaa2aaa8aa2a

def B9_0 : List (ℕ × ℕ × ℕ) := [(0x40aa552a552a552a, 26, 0x21d950c84007000021c958d04005000021d158c84005000021d950c84006000021d85148c004000021d8d1484004000021d950c84005000021d950c84004000021d950c84003000021d85148c002000021d8d1484002000021d950c84002000021d950c84001000021d950c84000),
  (0x40ab542b542b5454, 26, 0x21d950c8400c000021c558d0800a000021c958d0400a000021c944d90009000021d158c8400a000021d144d88009000021d148d84009000021d950c8400b000021d950c8400a000021d944d08009000021d948d04009000021d950c84009000021d950c84008000021d148c41803000021d81148c402000021d81144c802000021d80944d002000021d00944d802),
  (0x41aa542a552a558a, 26, 0x21d950c84012000021d948d04011000021d950c84011000021d950c84010000021d950c8400f000021d950c8040a000021d940d08409000021d8d148400e000021d950c8400e000021d950c80405000021d950c8400d),
  (0x41aa542b542b5494, 26, 0x21d950c84015000021c958d00410000021d158c80410000021d950c84014000021d950c80410000021d950c8040b000021d950c80406000021d81148c404000021c958d04013000021d158c84013000021d950c84013),
  (0x41aa552a552a55aa, 28, 0x21d950c8401b0000204958d01c120000205158c81c12000001950c9c60090000205950c81c1500000158d1c860040000205950c81c12000001158c9c6009000000d951c86004000000958d1c60090000205950c81c0c000021c158d0840a000021d8d148401a00002058d149c016000021d950c8401a0000205950c9c016000021d950c840190000205950c81c07000021c958d04017000021d158c840170000204158d09c0a000021d950c84018000021d8d1484016000021d950c84017000021d950c84016),
  (0x43a8542b542b9494, 26, 0x1e0944d9001c00001e0944c11814000021d950c04814000021d950c8401c00001d148c42181500002081950c5c1000002041950c9c1000001d80944d201000001d00944da010),
  (0x42a956285629a946, 26, 0x159e08410c1a0000159e0850c01d000015821c490c0e000000c5d89160100000004d9d0a1410000015021c498c0e000021d950c0841a000021c158d0840e000021d950c8401d0000158c5c092017000021c4d81094170000208158d1c40e),
  (0x43a857285728a8a8, 26, 0x21d950c8401e0000021d8904d4140000209950c05c1b0000208158d05c120000204158d09c12000021c158d0480f00000d9e0805141a00000d9e0811441d00000d9e0411481d0000159e08050c1a0000159e0810c41d0000159e0410c81d00000d9e080514190000204158d1c8120000208158d05c0f0000204158d09c0f00000d8a04115c1d0000158a0410dc1d),
  (0x42ad502d52528d52, 26, 0x21d950c84021000021d94508c020000021d94d08402000000114c85e1811000021d950c84020000000d5085e18110000005508de1811000019e0900c540a000019e0108d440e000019e010854c0e000019e00c85500e000021d950c8401f000021d9500c480a000021d8114c840e000021d811448c0e000021d80d44900e000019500c85e016),
  (0x43ac512c52538ca4, 26, 0x14ca05d81020000014ca05d90022000011d8600c9411000019d0a00c5411000019d0a0c41420000004d5081e1811000008d5841e1011000014ca041d9011000021d1580c4811000021d950c84022),
  (0x43ac512c53538cac, 28, 0x14ca1c5810210000150a01d84c20000014ca01d85020000002091cc5940d000002091cc5581300001860900d5c12000001159cc6080e000000d59d06080e0000205950c81c21000021d94108c420000008d59c061012000001e0904d580e000014ca1c059012000001d9504ca00e000001d14c86181d00002059500c9c120000010a1cc5940e000000ca1d05940e000001951cc4a013000020594108dc2000000159d04ca00d0000006091cd580e0000011d860c941d0000005951cca00e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB9_0 : blocksOK 8 32 P8 P9 40 0 B9_0 = true := by decide +kernel

def B9_1 : List (ℕ × ℕ × ℕ) := [(0x42ad522d5252ad52, 28, 0x21d950c84024000020855900dc210000208d59005c2100000114dc4a18120000209158c05c21000000d51c4a1812000000551cca1812000001951cc8600500000159d08c600b0000209950c05c21000000d59c4a1012000000559cca1012000001159cc86005000000559d0a0c12000000d59d086005000000559d08e005000021d950c84023000021c150c8581f0000151e080c581e00002099500c5c0c000021d8114c841a000021d811448c1a00000194dc492017000021d80d44901a000001951c48e017000001951cc860170000208150dc581f000021d00d44981a000001159c48e017000001159cc86017000000d59d086017),
  (0x43ac532c5353acac, 30, 0x151e084c1824000015021c8c5821000014c21c905821000001951cc8600a00000159d08c6006000014c21c985021000001159cc8600a000000d59d08600a0000021d8904d4000000209950c41c24000020815904dc21000020415908dc21000001e09850d40a0000151e0804d81b000001d9504ca01a000001d9508c601a000001d9508c600200002099500c5c1b0000019e08c5141a0000019e0904d41a0000019e0904d40200002041591cc821000000a1d850d40a00000061d890d40a00000159d08c60000000011e0984d41a0000011e0984d402000000de098514020000009951cc601a0000009951cc60020000005951cca002),
  (0x49b64949b64949b6, 30, 0x21d950c84026000009201944dc2400000d2019449c240000019cd085601b0000152018c49c240000019d5084e01b0000019d50c4a01b0000019d50c4a0070000192014c49c240000015d9084e01b0000015d90c4a01b0000015d90c4a007000000dd9144a01b000000dd9144a0070000009d9144e0070000021d50c49801000021d950c84025000001d854d0a023000001d914c4a023000001d9144ca0080000211814c49c240000015e1084d81b0000015e10c4981b0000015e10c49807000000de1144981b000000de114498070000009e1144d8070000019d50c4a001000000de1184941b000000de118494070000009e1184d4070000015d90c4a00100000119d4c4a02300000119d44ca0080000009e11854c07000000dd9144a0010000009d9144e00100000059d50ca008),
  (0x4bb44b4bb44bb4b4, 32, 0x1d909440e0260000019cd09460240000019d508c60240000019d50c8600c0000015d908c60240000015d90c8600c000000dd9148600c000002118944dc030000211948c05c26000001205948dc24000001209944dc24000001209854dc0c000000a11944dc24000000a11854dc0c000000611894dc0c000001d9148c60030000015e108c58240000015e10c8580c000000de1148580c000001920944dc03000000de1188540c000001520984dc03000000a1d944d024000000a1d854d00c00000061d894d00c00000119d48c6003000000d209855c0300000061d914c80c00000099d50c600300000059d50ca003000021d950c84027)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB9_1 : blocksOK 8 32 P8 P9 40 11 B9_1 = true := by decide +kernel

def B9 : List (ℕ × ℕ × ℕ) := B9_0 ++ (B9_1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk9 : blocksOK 8 32 P8 P9 40 0 B9 = true := blocksOK_app (k := 11) okB9_0 rfl (okB9_1)

set_option maxRecDepth 100000 in
theorem len9 : B9.length = 15 := by decide +kernel

theorem cl9 : ClassP 9 (inP 9 P9 40) 32 :=
  stepP 8 _ _ 25 32 (stepB_sound 8 32 P8 15 P9 40 B9 len9 blk9) (by intro E d h1 h2; omega) cl8

def P10 : ℕ := 0x49ed849d27b612749ed8b62d849ad849926b612649ad8b6000496da49525b6925496da496da492db49124b6d24492db4912442eb452cb452d4bad14bad2b4426b6524b652549ad949526b6422b7520b752148add4852148436b0514b25254c8ca92136a242eb450cb452d4b8d14bad2b442eb450cb45254b8d14ba52b442eb450cb45254a8d14ba52a442ab4508b55214a8d54aa544a426b6504b6525498d949526b6426b6504b6521498d94952696436a2544ac544ac94a52436a241ea855ca855ca855ea8aa2a8416aa554a8554aa556aa456aa412ab550a9550aa552ab45144416aa554a8554a8556aa416aa416a8554a855ca855ea80a2a8412a9550a8558a955aa90a516416a8554a8554aa556aa056aa41ea8544ae544ae54650942a841ea854ca855ca855e28aa2a841aa9548a8558a955a28aa51241aa9548a8558a855a29aa50641ea854ca8554a855e28a22a841ea8544aa554aa55628942a841ea8544a855ca855e288a2a8416aa544a8554aa5562a456aa416aa544a8554aa5562a452a8416aa544a8550aa5562a4568a416a8544aa550aa5562a1568a416a8540aa554aa5562a1562a40eac54cac54cac54d53ab2ac40aad548ac548ad54952ab51240aad548ac548ac54952ab50240aac548ad548ad54952ab05040aac548ac548ad54952ab41240aac548ac548ac54d53ab00c40eac544ae544ae54551942ac40eac544ac54cac54d538b2ac40eac544ac548ac54d538b28c40eac540ad548ad549528b25040eac540ac54cac54d538b22c40aad540ac548ad549528b51240aac540ad548ad549528b45240eac544ac544ac54d53832ac40eac544ac544ac54953832a440eac540ac544ac54d538322c406ae544ae544ae54551546ae406ae540ae544ae545515462e406ae540ae540ae545515460e40ea855ca855ca855ca8aa2a840aa9558a8558a8558a9aa50640ea8550ab550ab550ab9525440ea8554a855ca855ca88a2a840ea8554a8554aa554aa852a840ea8550a9550ab550ab85254406aa554aa554aa554aa556aa406aa550aa550ab550ab55214406aa550aa550aa554aa5560a402ab550ab550ab550ab55154406aa554a8554aa554aa456aa406aa554a8554aa554aa452a8406aa550a9550ab550ab45254406aa550a8554aa554aa4562a402ab550a9550ab550ab45154406a855ca855ca855ca82a2a8406a8558a9558a9558a92a656402a9558a9558a9558a92a556402a9558a8558a9558a92a516406a8554aa554aa554aa156aa406a8554aa554aa554aa152a8406a8550ab550ab550ab15254406a8550aa554aa554aa1562a402a9550ab550ab550ab15154402a8554aa554aa554aa154aa

def B10_0 : List (ℕ × ℕ × ℕ) := [(0x80aa2a8aaaa2aaa8aa2a, 32, 0x261d950c84005000261d950c84004000260d9d148400200026159d0c84002000261d950c84003000261d950c84002000261d950c84001000261d950c84000),
  (0x80aa2aca8ab2a2aca854, 32, 0x261d950c84009000261d950c840080002419d148c60030002419d144ca0030002419c944d20030002411c944da003000261d950c84007000261c558d08006000261c958d04006000261d158c84006000261d950c84006000261d148c41800),
  (0x80aaaa8a8aa2aaa8aa8a, 32, 0x261d950c8400e000261d950c8400d000260d9d148400b00026159d0c8400b000261d950c8400c000261d950c8400b000261d950c8400a000261d950c80406),
  (0x80aaaa8aaaa2aaa8aaaa, 34, 0x261d950c84012000241d950c86005000241d95048e005000260d851c94010000241d8d04960050002615851c8c01000026158d1c840100002419d148c6008000261c958d04011000261d158c8401100024158d049e005000261d85148c010000261d8d1484010000261d950c84011000261d950c84010000261d950c8400f00026148d8501c0a00026150d8481c0a00026158d0481c0a00026158d0481c07000261c158d08406000261c158508c06000261c0d850940600026158d0481c0100026140d8509c06),
  (0x81aa2a8a8aa2aaa8ab0a, 32, 0x261d950c84014000261d950c84013000261d950c804110002451c940da003),
  (0x81aa2a8a8ab2a2aca914, 32, 0x261d950c840150002419d148c601300024558d009e005000261d81148c410000261c958d0040b000261d158c8040b000261d950c8040b000261d950c80402),
  (0x81aa2a8aaaa2aaa8ab2a, 34, 0x2459d148e00160002458d1c942013000245951c8c2013000261d950c84016000261c958d00413000261d158c804130002459d148c2013000261d950c804130002459d148c2008000261c958d0040c000261d158c8040c000261d950c8040c000261d950c804080002459d148c20030002458d1c94200c000245951c8c200c000261d950c804030002459d148c200c),
  (0x81aa2aca8ab2a2aca954, 34, 0x261d950c84018000244d9d148201500024559d0c820150002419d148c6016000245c958d02014000245d158c82014000245d950c82015000245d950c82014000245d950c82012000245d950c82005000245c958d0200e000261c958d0040d000245d158c8200e000261d158c8040d000261d148d84017000245d950c8200e000261d950c8040d000261d948d04017000261d950c84017000245d950c82009000261d950c80405000245d950c82004000245c958d0200d000245d158c8200d000245d950c8200d),
  (0x80abaa0aea82baa150a8, 32, 0x261d950c8401b00026059d14c801a00026099d14c401a0002609851d4c019000260d9d148401a000260d851d48019000260d891d4401900026159d0c8401a0002615851cc80190002615891cc401900026158d1c84019000261d950c8401a000261d8514c8019000261d8914c4019000261d8d1484019000261d950c8401900026158d0805c0f00026140d8905c0a00026140d8509c0a000261409850dc0a000260c098515c0a000260c09851d40a),
  (0x81ab2a0aca82b2a55306, 32, 0x261d950c8401e000261d9508c401d000261d950c8401d00026159d0c8401c000261d950c8401c000261d950c80419000261d950c08410),
  (0x81ab2a0aca92b2a55316, 34, 0x261d950c84024000261d8914c4023000261d8d1484023000260d891d4041d000261d950c840230002615891cc041d00026158d1c8041d000261d950c84022000261d950c84021000261d8914c041c000261d8d148041c000261d950c8041c000261d950c8041a000261d8114c8419000261d158c84020000261d950c8402000024558d081e005000261c158d0840b000261c15890c40b000261c0d891440b000261d950c8401f00026140d891c40d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB10_0 : blocksOK 9 39 P9 P10 78 0 B10_0 = true := by decide +kernel

def B10_1 : List (ℕ × ℕ × ℕ) := [(0x81ab2a0aea82baa15128, 32, 0x261d950c8402500026099d14c0422000260d9d148042200026159d0c80422000261d950c804220002459d140ca008000261c158d08411000261c158d0840c000261c15890c40c000261c0d891440c00026140d891c40c),
  (0x81ab2a4aca92b2a55356, 36, 0x261d950c8402b00024499d14c2024000244d9d1482024000244d891d4201e00024559d0c820240002455891cc201e00024558d1c8201e00001d950e086410000245d950c82025000019d160c4a411000245d950c82024000245d8914c201e000245d8d148201e0000159d0e086410000011d960c4a411000245d950c8201e00000d9d160864100000099d160c6410000245d950c8201b00026019d14c841a000261d158c8402a000245d158ca0027000261d950c8402a000245d950ca0027000261d950c84029000245d950c0a012000245c158d0a00e000245c15890e00e000260d891d44026000245c0d891600e0002615891cc402600026158d1c8402600024419d14ca01a000261d950c84028000261d158c8402700024540d891e00e000261d8914c4026000261d8d1484026000261d950c84027000261d950c84026),
  (0x82aa2a0aaaa2aaaa2a2a, 32, 0x241d8514ca0230002485950e1c02c000261d8d148402d000261d950c8402d000261d950c8402c000261d950c0841f000261d950c04802),
  (0x82aaaa0a8aa2aaaa2a8a, 32, 0x261d950c84030000261d950c8402f000261d8d148402e000261d950c8402e0001e248414d901c000261d950c08420000261d950c0480b),
  (0x83aa2a0a8ab2a2ae2914, 32, 0x261d950c84031000261d950c04821000261d8114c481c000261d8114c841c0001e248054d181c0001e248054d901c000261d950c4082c),
  (0x83aa2a0aaaa2aaaa2928, 32, 0x261d950c84032000261d950c084220002459d140ca013),
  (0x83aa2a4a8aa2a2ae2944, 32, 0x261d950c8403300026159d0c0482300004d9500a25c1d00008d9d0062541d00026151d8c4082e00026159d0c4082e00026159d0c4082d),
  (0x83aa2a4a8ab2a2ae2954, 34, 0x261d950c84036000245d8d1482033000245d950c82033000245d950c82032000245d950c82031000245d950c0a024000261d8114c842300008d9d0206541e00026019d14c841c000245d158c82030000261d158c8042f000261d158c84035000245d950c82030000261d950c8042f000261d950c84035000261d950c84034000245d950c0a015000245d8114ca0230002481950c5e02c00024419d14ca01c000245d158c8202f000245d950c8202f),
  (0x82aa2a0aca92b2a65216, 32, 0x91e140c6583200020c49811e543200026144d811c80c0002499d140c600c),
  (0x83aa2a0aea82baa25128, 32, 0x261d950c84037000261d950c04816000261c158d04813000261c158d0841300021409850e5c3200020c0985165c3200020c09851e5432),
  (0x83aa2a4aca92b2a65154, 34, 0xa61c540d1816000244d9d140a03200024559d0c0a032000245d950c82037000245d950c0a032000091e144c2582500026019d14c482200009821c54d242200009021c54da422000091e144e418370002499d140c6016000091c160c65814000090e1c542583200009161c4c2583200024419d14e0822000091e144c25832),
  (0x82aa2a8a8aa2aaaaaa0a, 32, 0x261d950c84038000049d960c2500d000248d9d140602f00024959d0c0602f000249d950c0602f000051d960c0a427000249d950c0600d),
  (0x82aa2a8a8ab2a2aea814, 32, 0x261d950c8403a000011e148c6583200024944d811e00e0000559d0208e4260002600558d1c80b000261d158c84039000261d950c840390002480558d1e00b),
  (0x82aa2a8aaaa2aaaaa828, 32, 0x24059d14ca021000051e148c2580400024059d148e02c00024059d0c9602c0002405950c9e02c000261d950c08428000249d950c06004)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB10_1 : blocksOK 9 39 P9 P10 78 11 B10_1 = true := by decide +kernel

def B10_2 : List (ℕ × ℕ × ℕ) := [(0x82aaaa8a8aa2a2aaaa82, 32, 0x261d950c8403b000061d950c0a417000060d9d140a43400006159d0c0a434000011e148e45837000061d950c0a434000061d950c0a429000261d950c08417),
  (0x82aaaa8a8aa2aaaaaa8a, 34, 0x261d950c8403d000051d940ca6038000248d9d1406030000260d9d140843500024959d0c0603000026159d0c0843500001d950e0a441c00001061c94da422000019d160ca4413000249d950c06030000261d950c084350000159d0e0a441c00000d9d160a441c000261d950c0842a00026019d14c8420000261d950c8403c00019506008e5c3a000249d950c0600e000261d940d08417000260d9d148043900026159d0c8043900024819d14e0420000261d950c80439),
  (0x83aa2aca8ab2a2aea954, 36, 0x261d950c8403e000248d9d140603600024959d0c0603600001d950e0864190000261c944d18160000261c944d1803000249d950c060360000159d0e0864190000261c944d900300000d9d16086419000249d950c0602b00024819d14c602400024419d14ca02400026019d14c4821000249d158c4203d000245d158c82038000249d158c42038000021d148c6580d000249d950c4203d000245d950c82038000249d950c42038000021d948c6500d000249d950c4203b000021d950c4a417000021d950c86417000249d950c06018000248d9d144203a00024959d0c4203a00024419d14e082400024819d14c602100024419d14ca021000011e148c65804000261d158c40838000009d160c6580d000005d160ca580d000249d950c4203a000261d950c40838000009d960c6500d000005d960ca500d000009d950e06417),
  (0x86a8aa0aca82b4a65286, 32, 0x261d950c8403f000204d8901d64370002158d08245c37),
  (0x84a9ab0a2ac2954d18a4, 32, 0x10a24c4159c3800006091c158e4350000a059c150e43500011c2604d5882f0001142604dd882f000261d1580c483c00026059c14d0839),
  (0x87a82bca0af28542a150, 32, 0x24dd95008603e00024c19d144a03600024c19d148603600024c19d148603100024819d14c603600024819d14c603100024419d14ca03100011e24c085582a00011e24c095843c00011e24c055883c00011e2480558c3c00019e24c085502a00019e24c095043c00019e24c055083c00019e2480550c3c00011e24c085582900024819d1604c3600024819d1604c3100024419d1608c3100024419d160c83100011ce48055a03c00019ce48055203c),
  (0x84ada80b6a45246d48a4, 32, 0x261d950c84041000261d854d08040000261d894d0404000001188c625d433000261d914c8404000000990c625d43300000590ca25d433000261d950c8404000000994c625d03300000594ca25d03300000594d225c8330001e24d4108581a0001e2414d0984200001e2414d0588200001e2414c8590200001e2410c859420000261d941084c1a000261c15908c420000261c15904c820000261c15884d020000261c11884d4200001d9410c862427),
  (0x85ad284b4a452c694b4a, 34, 0x261d950c84044000261d948d04043000261d950c8404300001c518a14e42d000161c64108d823000161c2450c982e000161c2448d182e0001e14e410858230001e1424d04982e0001e1424c85182e000162410499cc2f0001e14e5048184000004994c225d0330000c99c42255033000188e4421d503300026159c1084c2300026141d9048c2e00026141d8850c2e000161c1048e582f000261d950c840420001e1410c86582f),
  (0x85ad284b4a552c694b5a, 36, 0x261d950c84045000245d894d02044000245d914c8204400001590ca065c23000245d950c8204400001194ca065c2300000994d2065c2300001d961048e4020000194d2085e40c0001c64d4109a0240001c6414d18a0300001c6414c9920300000159e1048e40b0001c6410c9960300000119e1448e40b0000099e1450e40b000245d950c82041000261d814d084400000d19e006494360000224d45099c20000190e6005c9436000021d94508e420000021590c865c3c000245d94108e024000245c1590ca030000245c1588d2030000014e610499c0b000245c1188d6030000010e614499c0b00000d5920865c0c000008e614519c0b000245d814d0a040000019e14508e41f0000064d61099c200001d9410c866038000014e60851d839000014e61049d839000010e61449d839000005d96108e420)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB10_2 : blocksOK 9 39 P9 P10 78 25 B10_2 = true := by decide +kernel

def B10_3 : List (ℕ × ℕ × ℕ) := [(0x86ac288b2a4534669226, 32, 0x190e609c0544300004d624109d82d000261d950c84046000161ca410c582d0001e14e4108582d0001d84d5200a44200026159c1084c2d),
  (0x84ada90b6a45256d48a4, 34, 0x261d950c8404800024c59d410a04100024c99d41060410000158a04e51c3600024d19d40860410000159204e49c360000159208e45c360000159208c65c1500024d59d00860410000119604e49c360000119608e45c360000119608c65c150000099610e45c360000099610c65c150000059610ca5c1500024dd9500860410000119e04e494360000119e08e454360000119e08c654150000099e10e454360000099e10c654150000059e10ca54150000099e14e450360000099e14c650150000059e14ca50150000059e14d24815000261d950c8404700024dd94108601b000261c15908c42a000261c15904c82a0000158a04d25c3a000261c15884d02a0000159204ca5c3a0000159208c65c3a000261c11884d42a0000119604ca5c3a0000119608c65c3a0000099610c65c3a000261411884dc2a0000119e04ca543a0000119e08c6543a0000099e10c6543a0000099e14c6503a),
  (0x85ad294b4a552d694b5a, 38, 0x261d950c8404900024c99d410604500024d19d40860450000159208c65c2400024d59d00860450000119608c65c240000099610c65c2400002614d0499c050000261cd450980800024dd9500860450000119e08c654240000099e10c654240000261cd04994050000099e14c650240000261cd44990050000261cd451880500002614d0499c0000024dd95048204800024c19d450a04100024419d4d0a0410000224dc550981a00019624c0509c3e000021d94508e42a000021d94d08642a000021590c865c0a00024dd94108602b00024dc15904a03d00024dc15885203d00001624d0499c0e00024dc11885603d00001224d4499c0e00000a24d4519c0e00001e24d450980600024419d6108c4100000e61c550981a00000661cd50981a000019610c865c0100024d411885e03d00001224dc49940e00000a24dc51940e00001624dc50980600000a24dc55900e00001224dc54980600000dd96108642a00000d5920865c0a00000a24dc55180600000559208e5c0a),
  (0x92b6a49256d4924ada92, 36, 0x261d950c8404b00005641d890e0480000d641d890604800001e0d4499243e00011641d88c604800001e114498e43e00001e114c98643e00001e114c85a41800019641d08c604800001e194490e43e00001e194c90643e00001e194c85241800001e19508c643e00001e195084e41800001e19508c641800001e19508c64090001d641908c604800001a1d4490e43e00001a1d4c90643e00001a1d4c85241800001a1d508c643e00001a1d5084e41800001a1d508c641800001a1d508c64090000121d588c643e0000121d5884e4180000121d588c64180000121d588c640900000e1d5890641800000e1d589064090000061d5890e409000261d950c8404a000021c9914c6447000021d5908c6447000255c1908c604800001a254490dc3e00001a254c905c3e00001a254c851c1800001a25508c5c3e00001a255084dc1800001a25508c5c1800001a25508c5c0900001225588c5c3e000012255884dc1800001225588c5c1800001225588c5c0900000e2558905c1800000e2558905c09000006255890dc09000012255c8c583e000012255c84d818000012255c8c5818000012255c8c580900000e255c90581800000e255c905809000006255c90d809000015e1908c644700000e255c98501800000e255c985009000006255c98d009000006255c990c09)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB10_3 : blocksOK 9 39 P9 P10 78 34 B10_3 = true := by decide +kernel

def B10_4 : List (ℕ × ℕ × ℕ) := [(0x93b624d276c49a4ed96c, 40, 0x261d950c8404d0000d641d890604900011641d88c604900001e114c85a42b00019641d08c604900001e194c85242b00001e195084e42b00001e19508c64120001d641908c604900001a1d4c85242b00001a1d5084e42b00001a1d508c64120000121d5884e42b0000121d588c641200000e1d589064120000255c9850e007000255d890c4204b00001645d890e04800001649d850e04800001649c590e01b00000a55d850e04800000a55c590e01b00000655c990e01b000021d58904e40f000255c1908c604900001a254c851c2b00001a255084dc2b00001a25508c5c12000012255884dc2b00001225588c5c1200000e2558905c1200001d649850e007000012255c84d82b000012255c8c581200000e255c905812000019649c50e00700000a61d850d44800000a61c590d41b00000661c990d41b000015e18904e40f00000e255c985012000011649c58e00700000d649c59200700000661d590c81b000009e19504e40f000005e19508e40f000261d950c8404c),
  (0x96b42592d684b5a2d000, 32, 0x41e1950ca4070002254dc819044c00004255cd89200000004255cd09a000000042558d09e00000004164dc992007000261d9500c844c0000421d58d0a4000000421d5890e4000000421cd8916400000041d58d0a60000000415cd8922400)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB10_4 : blocksOK 9 39 P9 P10 78 38 B10_4 = true := by decide +kernel

def B10 : List (ℕ × ℕ × ℕ) := B10_0 ++ (B10_1 ++ (B10_2 ++ (B10_3 ++ (B10_4))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk10 : blocksOK 9 39 P9 P10 78 0 B10 = true := blocksOK_app (k := 11) okB10_0 rfl (blocksOK_app (k := 14) okB10_1 rfl (blocksOK_app (k := 9) okB10_2 rfl (blocksOK_app (k := 4) okB10_3 rfl (okB10_4))))

set_option maxRecDepth 100000 in
theorem len10 : B10.length = 40 := by decide +kernel

theorem cl10 : ClassP 10 (inP 10 P10 78) 39 :=
  stepP 9 _ _ 32 39 (stepB_sound 9 39 P9 40 P10 78 B10 len10 blk10) (by intro E d h1 h2; omega) cl9

def P11 : ℕ := 0x49b6c126a4db6093526db0b60002d824bb6892d25db449692eda24bb696d1255b449492ada24a4956d1255b4000926db2494936d924a49b6c92524db64916dd24248b6e921245b749092124216ad0a58b429652d5a14b568ad000109d6c5265b149a93ad8a4d49d6cad8846b72912dca4548d6e522a4548d6e42b5a14296a522a5235295a54256a5213ad8a0cb62935271b149a93ad95b10956d5045b5492928daa494956d52484eb62832d8a4549c6c526a4e9656c4275b14196c522a4a362935274b2a6212adaa08b6a905251b549292a5aa490956c5045b5482928daa494952d12483ea82af2a0abca82afaa1542a855041154d54151558549565530a68b14620baa0aaca82ab2a8aaeaa02baa955105551554541551555555541555545482aa8aaa2a0aa8aaaaaaa80aaaaa2241554155151554551555550555544520eaa2a88ae2a22b8a8a50ca1aa283907d5054e5415795055f142a8550aa083aa8aa62a0ab8a82ae8a1546a8a0641f5415395055654157c50a21542a820eaa2a88aa2aa2a8aaa28ca1aa283907d505465415795055f14228550aa082aaaaa22a2aa8aa2aa8a88aaaaa824155515115055655155c544575502a20baa8a8ca82ab2a8aae2a229aa155105555544541551555551551455145482aaaaa22a2aa0aa2aa8aa8aa8aa8a4175415195455255155454157452a220aaa2a88aa2a82aaaaa2a8aaa2a8a905d505425515595455715055454aa082ea82a12a8aa8aa2ab8a82ae2a51440f5615395854e56153aa7ab1562ac205ab4a94ac2a52b4a9552d5a44b5690255b5485655215a548a92ada24508812adaa42b0a90adaa454956d1222440b5695295854a56152aa5ab4816ad205ab0a94ac2a52b4a9552d5a04b569035595445715115c544a8a50d5940c81eac2a32b0a9cac2a754f162ac55840d5655115854c565532a68b156511206ab2a88ac2a62b0a9953459ab2819035585445615315854ea9e2c55803081eac2a32b0a94ac2a754f1628c55840f5615195854a561532a78b1462a4206ab2a88ac2a42b0a9953459a32819035585445615215954ca9a2cd1904c81eac2a12b4a90ad2a554b1625051840f5615095854e56153aa78b1162ac207ab0a84ac2a62b0a9d53c588b146102d5a5425615295a54aa962d225ab4816ad2a12b0a94ad2a554b1691255840b5695095854856952aa58b48968d205ab4a84ac2a42b4a9552c5a44946102d5a5405615295a54aa962d2248b0816ac2a12b4a90ad2a554b16852d1a40b5615015a54a56952aa58b42962d205ab0a80ad2a52b4a9552c5a149161035595445615115854ca9a0cd5940c81aac2a32b0a8cac2a654d066ac14440d56151159544565532a683356052206ab0a88ac2a22b2a9953419ab20990355854456551159548a9a0cd4914c81eac2a12b0a8cac2a754f0622c55840f56150958546561532a7831162a4207ab0a84ac2a22b0a9d53c188b1461035595405615115954ca9a0cc5944c81aac2a02b2a88acaa654d0662c8a64075715195c54657151aa3547572ae203ab8a88aeaa22baa89512a2ab92810155d5445755115d544a895155d54480aaeaa22b8a88aeaa2544a8aaea224055755115c544571512a254557501202ab8a88aeaa22baa89512a2ab82810155c5445715115d544a895155d04480eae2a12b8a8cae2a3546a8e2e55c4075715095c54457151aa35471728e203ab8a80aeaa22baa89512a28b928101d5c5405715195c546a8d51c5c8b880aaeaa02baa88aeaa2544a8a2eaa24055755015c544575512a254517511202ab8a80aeaa22baa89512a28ba28901d5c5425715095c546a8d51c1cab880eae2a12b8a84ae2a2546a8e0e54c4075715095c542571512a2547072a2203ab8a80ae2a12b8a8d51aa383917101d5c5405715095c544a8d51c1c89880eae2a02b8a80ae2a3546a8e0e41c4055755015d540575512a254507551207aa0abca82af2a0abca8550aa15410355155c5415715055c542a8d5140c816a92ad2a0ab4a82ad2a554906d5240b5495695055a54156952aa4832a8207aa0aa4ab2a92acaa4ab4a895154103d5055055d5415755055e544a895081aa8aa82acaa0ab2a82ad2a654a0640d54154156550559549569532a40b207aa0aaca82af2a0abca8450aa1541035515545415715055c54628d5141c81ea82a92a4aa4ab2a92ad0a25455040f5415415355055d541578512a254203aa8aacaa2ab2a8aacaa2abaa955101555554551551545545555555541480aaaaaa2a8aa8aa2aa2a8aaaaaa02405551551545545555515555555014202aa8aa8aa2aa2a8aacaa2abaa805101554554551551545545555555501480eaa2a92a8aa4ab2a92acaa6145544075515495455255155954557052aa201aacaa4ab2a92acaa4ab2a955355900d565505595415755055d542a8850806ab2a82acaa0ab2a82acaa554c0640155d5415755055d54157550aa154203aa8aaca82ab2a8aacaa22baa955101d5455454155954556551155548a080eaa2aa2a0aa8aaaaa2aa8aaaa42840755155150554551559544575520a202aaaaa8a8aaa2a8aa8aaa2aaaaa2901555554545551545545511555550480aaaaaa2a0aa8aaaaa2aa8aaaaa2a405555551505545515515545555505202aa8aa8a82ab2a8aacaa22baa815101d545565415595455655114d50aa880eaa2ab2a0aacaa2ab2a88a2a8550405555551515545515515545154545202aaaaa8a82aa2aaaa8aaa28aa28a901d545525495495655255914ca8aa880eaa2a92a4aa4ab2a92ac8a2545504075515415355055d541574512a254202aa8aa0a92a92acaa4ab22995215901d545525415595455655115c54aa880eaa2a92a0aacaa2ab2a88aa2a55040755154950554551559544571528a203aa8aa0a8aaa2aaaa8aaa2a8a92a101d545505415595455655115c548a880aaaaa82a2aa8aa2aa2aa8aa2aa8a405555541505545555515545515515201aacaa4a92a92acaa4ab22955355900d5655254954956552559142a9aa4806ab2a82a4aa0ab2a92ac8a554c1640155d5415355055d54157450aa154203aa0abca82af2a0abca8150aa15410155155c5415715055c544a8d5141c80ea82ad2a4ab4a92ad2a454a565504075415615355854d561532a72b256203aa0ab0a92ad2a4ab4a915295914101d505585495615255854ca9cac81880aa8aac2a4ab0a92ac2a654e5620c4055415695255a549569522a52b4a9202aa0ab0a92ad2a4ab4a915295a14900d5255a5495695255a548a92adaa4806a92ac2a6ab0a9aac2a654d564ac40354956152558549569522a4ab609201aa4ab0a92ac2a4ab0a99535590310055355854d5615355854ca9aac558802a9aac2a4ab0a92ac2a654d5620c4015495695255a549569522a4ab4a9201aa4ab4a82ad2a4ab4a915245b54900d525585455615355854ca9a2c958802a9aac2a2ab0a9aac2a654d162ac40154d56151558549561532a68b146200aa6ab0a82ac2a6ab0a99534588b10055255a5415695255a548a922d2a480ea82ab2a8aacaa2ab2a82aeaa554407541551545565515595415555228203aa0aa8aa2aa2aaaa8aa8aaaa90a101d505545515515455655055d5482880aa8aaa2a8aa8aaaaa2aa2aaaaa2a405545551545545555515515555114202aa2aa8aa2aa2a8aa8aa8aaaaa8290155055655155954556550555542a080aa82aa2aaaa8aaaaa2aa2aaaa8aa40554155154556551559541575502a202aa0aa8aa2aa2aaaa8aa8aaaaa0a901d505565515595455655054d50aa880ea82ab2a8aacaa2ab2a82a2a8550405545551545545555515515154515203aa0aa4ab2a92acaa4ab0a995155101d5055255954956552558544a8aa080ea82a82aeaa0abaa82ae2a2544a840554154956552559549561512a4a9202aa0aa0ab2a92acaa4ab0a995215901d505525515595455655055c54aa880ea82a92a8aa8aa2ab2a82ae2a514407541541555545555515515515254203aa0aa0aa2ab2a8aacaa0ab8a9151015515505515515555455455455454806a92a92acaa4ab2a92ac2a554d564035495495655255954956150aa6a9201aa4aa0abaa82aeaa0ab8a85512a100d525505595495655255854aa98ac806a92a82acaa4ab2a92ac2a154c524035495415655055954956152aa60b200aa6aa0abaa82aeaa0ab8a8550aa10055255255954956552558542a92a4806a82ab2a8aacaa2ab2a82acaa5544035415595455655155954154552a8201aa0aa8aaaaa2aaaa8aa8aa2ab2a900d5055455155954556550559548a8806a82aa2a8aa8aaaaa2aa2a8aac2a401545551555545555515515455555200aa2aa8aa2aa2aaaa8aa8aa2aa8a90055055655155954556550559542a8802a82aa2aaaa8aaaaa2aa2a8aa8aa

def B11_0 : List (ℕ × ℕ × ℕ) := [(0x402a8554aa554aa554aa154aa, 40, 0x2a61d950c84008002a61d950c84007002a51e158c84005002a59e150c84005002a61d950c84006002a6059d148c004002a60d9d1484004002a6159d0c84004002a61d950c84005002a61d950c84004002a61d950c84003002a6059d148c002002a60d9d1484002002a6159d0c84002002a61d950c84002002a61d950c84001002a61d950c84000),
  (0x402a9550ab550ab550ab15154, 40, 0x2a61d950c84010002a45e158c9000d002a61d950c8400f002a45e158c9000c002a51e158c8400d002a51c560c9800b002a51e158c8400c002a59e150c8400d002a59c560c9000b002a59e150c8400c002a59d160c8400b002a61d950c8400e002a61d950c8400d002a61c558c9000b002a61d950c8400c002a61d158c8400b002a61d950c8400b002a61d950c8400a002a59d144c82003002a6019d148c402002a61d950c84009002a6019c548d002002a6011c548d802002a5811c548e002),
  (0x406a8550aa554aa554aa1562a, 40, 0x2a61d950c84015002849d950e24012002a61d158c84014002a61d950c84014002a61d950c84013002a61d950c84012002849d950e0240d002a61c158c9040b002a60d9d1484011002a6159d0c84011002a61d950c84011002a61d950c80405002849c158e1240b),
  (0x406a8550ab550ab550ab15254, 40, 0x2a61d950c8401a002a61d950c84019002a51e158c80413002a59e150c80413002a61d950c84018002a61d950c80413002a61d950c8040e002a61d950c8040600285c960d812404002a61d950c84017002a51e158c84016002a59e150c84016002a61d950c84016),
  (0x406a8554aa554aa554aa152a8, 40, 0x2a61d950c8401d002a61d950c8401c002809e158d06412002809e150d86412002861d950c82419002809d950e06412002861d950c8240f002a41e158c9040c002a60d9d148401b002a6159d0c8401b002a61d950c8401b002861d950c82407002841e158c9240c),
  (0x406a8554aa554aa554aa156aa, 42, 0x2a61d950c84028002a61d950c8041d002a51e158c80415002a51e158c84027002a59e150c80415002a59e150c84027002a59d160c84025002a61d950c8041a002a60d9d1484026002a6159d0c84026002a61d950c80415002a61d950c84027002a61d158c84025002a61d950c84026002a61d950c84025002a61d950c80410002849e158c1240d002a60d9d1484024002a60d9d1484023002a6159d0c84024002a6159d0c84023002a6158d1c84022002a61d950c84024002a61d950c84023002a61d8d1484022002a61d950c84022002a61d950c80408002a61d950c84021002a51e158c8401f002a59e150c8401f002a61d950c84020002849e158c1240c002a60d9d148401e002a6159d0c8401e002a61d950c8401f002a61d950c8401e),
  (0x402a9558a8558a9558a92a516, 40, 0x2a61d950c8402e00282158d0865c2100280560d8925c1f00280560d09a5c1f002a61d950c8402d00281e158d0a441600281e15890e441600281e0d8916441600280558d0a25c1f0028160d891e4417002a61d950c8402c002a61d8914c402b002a61d8d148402b002a61d950c8402b002a61d950c8402a002a61d950c84029002a61d950c08402),
  (0x402a9558a9558a9558a92a556, 42, 0x2a61d950c84035002821d950c4a408002821d944d0a408002a51c560c98033002821d144d8a408002a59c560c90033002a59d160c84033002a61d950c8403400281e158d08640600281e15890c6406002a60d891d4403200281e0d89146406002a615891cc4032002a6158d1c84032002819d144e0a408002a61c558c90033002a61d158c840330028160d891c6406002a61d8914c4032002a61d8d1484032002a61d950c84033002a61d950c84032002a61d950c84031002a5891c54c202c002a58d1c548202c002a60d891d44030002a5951c4c8202c002a615891cc4030002a6158d1c84030002a59d144c8202c002a61d8914c4030002a61d8d1484030002a61d950c84030002a61d950c8402f002a601950c85c29002a601944c91c29002a601144c99c29002a59d144c0a003002a61d950c04809002a61d950804c09002a61d8d0805409002a581144ca1c29002a6158d0805c09)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_0 : blocksOK 10 47 P10 P11 208 0 B11_0 = true := by decide +kernel

def B11_1 : List (ℕ × ℕ × ℕ) := [(0x406a8558a9558a9558a92a656, 42, 0x2a61d950c8403c002a51e158c8403a002a59e150c8403a002a61d950c8403b00281e158d0a441a00281e15890e441a002a60d891d4403900281e0d8916441a002a615891cc4039002a6158d1c84039002a61d950c8403a0028160d891e441a002a61d8914c4039002a61d8d1484039002a61d950c84039002a61d950c80434002a6099d14c042d002a60d9d148042d002a60d891d44038002a6159d0c8042d002a615891cc4038002a6158d1c84038002a61d950c8042d002a61d8914c4038002a61d8d1484038002a61d950c84038002a61d950c8403700285e158d00a40e002a51e158c84036002a59e150c84036002a61d950c08406002a61d950c04817002a61d950804c17002a61d8d0805417002a61d950c84036002a6158d0805c17),
  (0x406a855ca855ca855ca82a2a8, 40, 0x2a61d950c8403e002861d950c8243c00281e158d08641800281e15890c641800281e0d891464180028160d891c6418002861d950c82435002861d950c0a40800286099d14c242e002861d950c24821002860d9d148242e002861d950824c21002a60d891d4403d00286159d0c8242e002861d8d0825421002a615891cc403d002a6158d1c8403d002861d950c8242e00286158d0825c21002a61d8914c403d002a61d8d148403d002a61d950c8403d002a61d950c08408002861d950c0a407002a61d950c04821002a61d950804c21002a61d8d0805421002a6158d0805c21),
  (0x402ab550a9550ab550ab45154, 40, 0x2a61d950c84042002821d950c64824002a61d950c84041002821d950c6481e002821d944d24824002a51c560c98040002821d944d2481e002821d144da4824002a59c560c90040002821d144da481e002a59d160c8404000281e158d064836002819d144e24824002a61c558c90040002819d144e2481e002a61d158c84040002a61d950c84040002a61d950c8403f002a59d144c0a02c002a61d8114c842b002a61d8114c4830002a61d8054c902b002a61d0054c982b002a59d0054ca02b),
  (0x406aa550a8554aa554aa4562a, 40, 0x2a61d950c84049002a61d950c84048002a61d158c84047002a61d950c84047002a61d950c84046002a61d950c84045002859d140e24824002a61c158c90440002a61d8d1484044002a61d950c84044002a61d950c8404300284958d0225c1f002a61d950c04811),
  (0x406aa550a9550ab550ab45254, 40, 0x2a61d950c8404d002a61d950c8404c002a51e158c80446002a59e150c80446002a61d950c8404b002a61d950c8044600285e158d024836002a61d950c0842d00285e158d024816002a61d8114c4838002a51e158c8404a002a59e150c8404a002a61d950c8404a),
  (0x406aa554a8554aa554aa452a8, 40, 0x2a61d950c84051002a61d950c84050002a51e158c80448002a59e150c80448002a61d950c8044c002a61d950c80448002a61d950c80441002861d950c2481e002a61d8d148404f002a61d950c8404f002a61d950c8404e00286158d00a5c21002a61d950c04823),
  (0x406aa554a8554aa554aa456aa, 42, 0x2a61d950c8405a002861d950c82451002851e158c82449002a51e158c84059002859e150c82449002a59e150c84059002a59d160c84057002861d950c8244d0001e0da504968260001e15a5048e8260001e158d244a839002861d950c82449002a61d950c84059002a61d158c84057002a61d950c84058002a61d950c84057002861d950c82442002861d950c24824002a61d8d1484056002a60d9d140484f002a61d950c84056002a6159d0c0484f002a61d950c84055002a61d950c84054002a61d950c0484e002a61d8d1484053002a61d950c84053002861d950c0a42e002a61d8114c483d002a51e158c84052002a59e150c84052002a61d950c04824002a61d950c0481b002860d9d142484f00286159d0c2484f002a61d950c84052002861d950c2484e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_1 : blocksOK 10 47 P10 P11 208 8 B11_1 = true := by decide +kernel

def B11_2 : List (ℕ × ℕ × ℕ) := [(0x402ab550ab550ab550ab55154, 42, 0x2a61d950c8405e002821d950c4a410002821d950c86410002821d950c64820002821d948d06410002821d948c65020002821d944ca5020002a51c944e1805c002821d148d86410002821d148c65820002821d144ca5820002a59c944e1005c002821c944d25820002a59d144e0805c002a59d148e0405c00281d950c866037002a60d9d148405d002a6159d0c8405d002819d148e06410002819d148c66020002819d144ca6020002a61c944d9005c002819c944d26020002a61d144d8805c002a61d148d8405c002a61d950c8405d002811c944da6020002a61d944d0805c002a61d948d0405c002a61d950c8405c002a61d950c8405b002a58d1c940603f002a5951c8c0603f002a59d148c0603f002a59d148c06031002a5811c94c602c002a5811c54ca02c002a6019d14c482a002a5809c54d202c002a6019c94c502a002a6019c54c902a002a5009c54da02c002a6011c94c582a002a6011c54c982a002a6009c54d182a002a59d148c0600a002a5009c54e182c002a5811c94c602a002a5811c54ca02a002a5809c54d202a002a5009c54da02a),
  (0x406aa550aa550aa554aa5560a, 40, 0x2a61d950c8405f002821d950ca4425002821d948d24425002821d148da442700281e158d0a4439002819d148e24427002851c940da6020002a61d940d0845c002a60d9d1408440002a6159d0c08440002a61d950c08440002a61d950c08433002a61d950c0840b),
  (0x406aa550aa550ab550ab55214, 40, 0x2a61d950c84060002821d950ca4426002821d948d24426002821d148da442600281e158d0a443a002819d148e24426002a61d950c8045d0028560d811ca406002a61d8114c8432002842158d1e4816002842158c9e5016002842150c9e5816002841950c9e6016),
  (0x406aa554aa554aa554aa556aa, 44, 0x2a61d950c84066002821d950c86428002821d948d06428002851c960d8245f002821d148d86428002859c960d0245f002859d160c8245f00021d950ca4685c00281e158d08643b002860d9d148246000286159d0c824600001e158d244a832002819d148e06428002861c958d0245f002861d158c8245f00019e150ca4685c002861d950c82460000161d8d244a832002861d950c8245f00011e158ca4685c0000e1d95244a83200009e158d24685c002861d950c8245e002861d950c0a410002860d9d140a442002a60d9d140844100286159d0c0a442002a6159d0c08441002a6158d1c8406500286158d1ca4061002861d950c0a442002a61d950c08441002a61d8d1484065002861d8d14a4061002a61d950c84065002861d950ca4061002a61d950c84064002861d950c0a43500286019d14ca42e00286019c94d242e002a51c960d8406200286011c94da42e002a59c960d04062002a59d160c84062002a61d950c08410002861d950c0a40f002860d9d140a441002a60d9d148406300286159d0c0a441002a6159d0c84063002a6158d1c8406100285811c94e242e002a61c958d04062002a61d158c84062002861d950c0a441002a61d950c84063002a61d8d1484061002a61d950c84062002a61d950c84061),
  (0x40ea8550a9550ab550ab85254, 40, 0x2a61d950c84068002a61d950c8406700285e158d02483a0028960d811e441a00285e158d00a413002a61d8114c483900285d160d80a44600285d960d00a44600285e158d00a446),
  (0x40ea8554a8554aa554aa852a8, 40, 0xaa605811cd418002861d950c824680008e1da50429460002861d950c248260008e1da50416826000961da5040e8260008e1da50681468002a61d950c048580028960d811c6418002a61d950c04826)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_2 : blocksOK 10 47 P10 P11 208 15 B11_2 = true := by decide +kernel

def B11_3 : List (ℕ × ℕ × ℕ) := [(0x40ea8554a855ca855ca88a2a8, 40, 0x2a61d950c8406a00281e158d086467002899d140e06428002861d950c0a415002861c158d0a45f002861d950c24827002860d9d140a449002a60d9d1408448002a60d9d140485900286159d0c0a449002a6159d0c08448002a6159d0c04859002a6158d1c84069002861d950c0a449002a61d950c08448002a61d950c04859002a61d8d1484069002a61d950c84069002a61d950c08415002881d950e06412002a61d950c04827002860d9d140a44800286159d0c0a448002861d950c0a448),
  (0x40ea8550ab550ab550ab95254, 42, 0x2a61d950c8406e00285d160d82486800285d960d024868002a61d950c8406d002a60d9d1404867002a6159d0c0486700285e158d024868002a61d950c0486700285e158d02483c002a60d9d140484b002a6159d0c0484b002a61d950c0484b002a61d950c8406c002a61d950c0483b00285e158d02481a00289e158d02441a00285e158d02481900285d160d82484d00289d160d82444c00285d160d82484c00285d960d02484d00289d960d02444c00285d960d02484c002a59d160c8406b002a61d950c0481800285e158d02484d00289e158d02444c00285e158d02484c002a61d158c8406b002a61d950c8406b),
  (0x40aa9558a8558a8558a9aa506, 40, 0x2a61d950c84070002a61d950c8406f002a51e158c08469002a59e150c0846900281e158d24846b000160da50a85c68002a61d950c08469002a61d950c084650028a1d950c24422002a60d9d1408455002a6159d0c08453002a61d950c08453002a61d950c0843d002a61d950c08422),
  (0x40ea855ca855ca855ca8aa2a8, 42, 0x2a61d950c84072002891e158c0646a002899e150c0646a00281e158d08646d0002a609850d5c180002a6098514dc180028a1d950c0646a0002a609851cd4180028a1d950c06466002861d950c0a4280028a1d950c064280028a1d950c0641d0028a0d9d140645a0028a0d9d1406451002860d9d140a451002a60d9d14048500028a159d0c0645a0028a159d0c0645100286159d0c0a451002a6159d0c048500028a158d1c42470002a6158d1c8046f002a6158d1c4086f0028a1d950c0645a0028a1d950c06451002861d950c0a451002a61d950c048500028a1d8d1442470002a61d8d148046f002a61d8d144086f0028a1d950c42470002a61d950c8046f002a61d950c4086f002a61d950c840710028a1d950c0643e002a61d950c04828002a61d950c0481d002a61d950c0841d0028a1d950c0641c002860d9d14248510028a0d9d1406450002860d9d140a45000286159d0c248510028a159d0c0645000286159d0c0a4500028a158d1c4246f002861d950c248510028a1d950c06450002861d950c0a4500028a1d8d144246f0028a1d950c4246f),
  (0x406ae540ae540ae545515460e, 40, 0x2a61d950c84079002a61d9490c4078002a61d94d084078002a61d94c904077002a61d950c84078002a61d9508c4077002a61d950c84077002a59e150c84076002a59e1490c4075002a59e14d084075002a59e150c84075002a61d950c84076002a61d9490c4075002a61d94d084075002a61d950c84075002a61d950c84074002a61d950c84073002851cd481a6020002a6019d148c440002a6019d14c8440002a6019cd5084400028500dc962581e0028500dc95a601e),
  (0x406ae540ae544ae545515462e, 42, 0x2a61d950c84080002a61c9590c407f002a61cd5908407f002a4dc961900478002a61d158c8407f002a51c9618c0478002a51cd6188047800021d14e485a825002a61d950c8407f002a59c9610c0478002a59cd6108047800021d94e4852825002a59d160c8047800021d952484e82500021d9524c4a825002a61d950c8407e002a61d950c8407d002a61c9590c0476002a61cd5908047600019e14e4852857002a61d158c8047600019e152484e85700019e1524c4a857002a61d950c8047600011e15a484e85700011e15a4c4a8570000de15a504a857002a61d950c8407c002a61c150c85873002a6159d0c8407b002a61d950c8407b002859d14c20a41000285811cd62482400285811c9624c24002a6019d1484c430028580dc9625024002a6019cd485043002a6019c94c50430028500dc9625824002a6011cd485843002a6011c94c5843002a600dc9505843002a61d950c8407a002a5811cd608441002a5811cd60484e002a5811c9604c4e002a580dc960504e002a500dc960584e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_3 : blocksOK 10 47 P10 P11 208 21 B11_3 = true := by decide +kernel

def B11_4 : List (ℕ × ℕ × ℕ) := [(0x406ae544ae544ae54551546ae, 44, 0x2a61d950c84087002849e1590c248000284de15908248000284dc961902479002851e158c82480002851c9618c2479002851cd6188247900019d14e486a05f002859e150c82480002859c9610c2479002859cd6108247900011d94e486a05f002859d160c824790000dd952486a05f00009d9524c6a05f00021d9524c86833002a61d950c840860001e15a504ca85d002861d950c82480002861c9590c2479002861cd5908247900011e14e486985f002861d158c824790000de152486985f00009e1524c6985f00019e1524c86833000161da504ca85d002861d950c824790000de15a486905f00009e15a4c6905f00011e15a4c8683300009e15a5068c5f0000de15a508683300009e15a50c6833002a61d950c84085002a41d950c8607c002a6159d0c8408400286159d0ca4081002a61d950c84084002861d950ca4081002a61d950c84083002861d9500ca45e00286019d148e44200286019d14ca442002a6019d1484c5400286019cd50a442002a6019cd485054002a6019c94c505400021d14e485a86200286011cd58a442002a6011cd485854002a6011c94c585400021d94e4852862002a600dc950585400021d952484e86200021d9524c4a862002841d950ca607c002a61d950c84082002a6159d0c8408100285811cd60a442002a5811cd486054002a5811c94c605400019e14e4852862002a580dc950605400019e152484e86200019e1524c4a862002a61d950c84081002a500dc958605400011e15a484e86200011e15a4c4a8620000de15a504a862),
  (0x40eac540ac544ac54d538322c, 40, 0x2a61d950c8408c002a61d94d08408b002a61d950c8408b002a61d950c8408a002268904c195c45002a61d950c08476002a61d9410c847500091e15a404e857002a6159d0c84089002a61d950c84089002859d14c224827002a61d950c84088),
  (0x40eac544ac544ac54953832a4, 40, 0x8de15864290780008de158669008d0008de1584269077002a59e150c8048b002a61d950c8048b002a61d950c08478002a61d9500c847700091e15a404e8250008d61d8668108b0008de158668108b002861d94c124825002a61d950c8408d),
  (0x40eac544ac544ac54d53832ac, 42, 0x8de15a442907900091e1582468c780008de158246907800091e15a468c08f002859e150c8248c0008dd962469008e00091d962468c08e00091e15a468c090002861d950c8248c0008de15a469008e00091e15a468c08e00091e15a468c091002861d950c0a479002a61d9410c84780008de15a406905f00091c162584e8570008d61da468108c00286159d0ca408e00091c260594e8590008de15a468108c002861d950ca408e00091426059ce859002a61d950c84091002861d9500ca45f002a6019d14c4857002a6019cd504857002a61d950c84090002a6011cd584859002861d9410ca478002a61d950c8408f00091c1605a4e857002a6159d0c8408e002a5811cd604859002a61d950c8408e),
  (0x40aac540ad548ad549528b452, 40, 0x2821c5590ca47f002885d950e60093002a61cd59084094002885cd59026088002a61d158c84094002885d158c26088002891cd4582608d002a61d950c84094002885d950c26088002899cd4502608d002899d144c2608d002a61d950c84093002a61d950c84092002a61cd59008488002a61d158c08488002a61d950c08488002a61d950c0847a002a61d95004c80d00289811cd624423002a6019d1448c11002a6019cd449011002a6011cd449811002a5811cd44a023)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_4 : blocksOK 10 47 P10 P11 208 27 B11_4 = true := by decide +kernel

def B11_5 : List (ℕ × ℕ × ℕ) := [(0x40aad540ac548ad549528b512, 40, 0x2a61d950c84099002a61d950c84098002a61cd59084097002a61cd59084096002a61d158c84097002a61d158c8409600019d14ca68608b002a61d950c84097002a61d950c8409600011d94ca68608b0000dd950a68608b00226884190dd476002a61d950c84095002a61cd59008489002a61d158c08489002a61d950c08489002a61d950c0847b002899d14c224424002899d00d624422002a61d811448c44002a61d80d449044002a61d00d449844002a5811cd60844f),
  (0x40eac540ac54cac54d538b22c, 42, 0x2a61d950c8409b002a61cd5908409a002a61d158c8409a00019d14c866a077002a61d950c8409a00011d94c866a0770000dd950866a0770002898524dd606b0021d8904c29641d00226818904d5c45002268188c515c45002268108c595c45002a61d950c0487d002a61c1590c4876002a61c1590c8476002a61c1590c487400226880590d5c76002a6159d0c80495002a6159d0c4089500226880590dd476002a61d950c80495002a61d950c4089500226880590d5c74002899d14c20641d002a6019d14c4845002a6019cd504845002a6011cd58484500021d9524c8686b002a61d950c40893002a61d950c80492002a61d950c408920022689850dc1492002a5811cd6048500022689850d41c92),
  (0x40eac540ad548ad549528b250, 40, 0x558924c229c4d002a61cd5908409c002a61d158c8409c002a61d950c8409c0006898124dd606b002a61d950c0847e002899d14c20641a00289811cd624426002a6019d14c8446002a6019cd508446002a6011cd588446002a5811cd60484c),
  (0x40eac544ac548ac54d538b28c, 42, 0x2a61d950c840a0002a61d94d08409f002a61d950c8409f00021d14c669888d002a59e150c4089a002a59cd6100488b002a59d160c0488b002a59e150c4089c002a61d950c8049a002a61cd5900848b002a61d158c0848b002a59e150c0488a002a59e150c0487f002a59c1610c4878002a61c1590c8478002a41d9610c4875002a5961d0c40897002a6159d0c80496002a5961d0c40896002a59e150c40897002a61d950c80496002a59e150c40896002a61d950c8409e002899d14c206415002a5821d14c4847002a5821cd504847002a6011cd588448002a59e150c40894002881d950c66088002841e150ca5888002a6159d0c8409d002a5811cd604848002a61d950c8409d),
  (0x40eac544ac54cac54d538b2ac, 44, 0x2a61d950c840a4002861cd590824a0002861d158c824a000019d14ca46a078002861d950c824a000011d94ca46a0780000dd950a46a07800021d9524c8680b000158924c629c4d000289a504d5e016002861d950c8249b002861cd5900a48c002861d158c0a48c00019e1524c86840000289a504dd6016002861d950c0a48c00011e15a4c868400000de15a5086840002861d950c0a480002a61c1590c847f002861c1590ca479002a41e1590c847600286159d0c82499002a6159d0c80498002a6159d0c840a3000259508c69e04f002861d950c82499002a61d950c80498002a61d950c840a3000259d08c69604f002a61d950c840a2000099d14c62682200025891cd606855002899d14c20642800286019d14ca44900286019cd50a44900018aa504d61c4300286011cd58a44900010aa584d61c430000caa585161c43000099d14e462838002861c1590ca47f002881d950c62493002841e1590ca4760001d8924c69601b00286159d0c82498000099524c61e823000059508e69e04f00285811cd60a451002a61cd590840a1002a61d158c840a1002861d950c82498000099d24c616823000059d08e69604f002a61d950c840a1000099d14e606822)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_5 : blocksOK 10 47 P10 P11 208 32 B11_5 = true := by decide +kernel

def B11_6 : List (ℕ × ℕ × ℕ) := [(0x40eac544ae544ae54551942ac, 42, 0xaa605810d5c3b0009601a504e9c4d0009601a4c529c4d00021d14e4698890000960124c5a9c4d00021d94e469089000021d952468c8900009e25850e940a5000958124c629c4d00019e14e469089000019e152468c89000011e15a468c890002a61d950c04886002a41e1590c487e0009c260590d687e00094260590de87e002a61d950c840a500289e15810c643b0009601a504e9c6000286019d14ca44d002a6019d14c485800286019cd50a44d002a6019cd50485800022504dd49a89000286011cd58a44d002a6011cd58485800022584dd492890000225851d48e890002841e1590e487e00285811cd60a44d002a5811cd6048580001a604dd4928900001a6051d48e890000126059d48e890),
  (0x40aac548ac548ac54d53ab00c, 40, 0x5268a0194dc54000502a60994dc430004c2a609951c43002a51cd61808490002a59e150c084a1000526099d40e890002a61d950c084a1002a504dc158a05400051e15a408e862002a4051cd58a0430005161da480e8a100051e15a480e8a1002a61d9500c846200288051cd5a6043),
  (0x40aac548ac548ad54952ab412, 40, 0x2a61d950c840a60004a1da5028d44100288de1590064980004a1d812694c4f002891e158c064980004a1d80e69504f000551ce6180a88e002899e150c064980004a1d00e69584f000559ce6100a88e000559d260c0a88e0028a1d950c06498000499d00e69604f000561ce5900a88e000561d258c0a88e000561da50c0a88e000561da50c0a8810028a1d95004e441000561d8124ca8610028a1d811464c4f0028a1d80d46504f0028a1d00d46584f002899d00d46604f),
  (0x40aac548ad548ad54952ab050, 40, 0x2805e1590ca47d000562589028dc0f002805e15908e4930005e01a50a94c1b002805e158c924930005e01a4ca9501b0005d24ca181688f002805e150c9a4930005e0124ca9581b0005da4ca101688f0005da50a0c1688f002805d950ca24930005d8124ca9601b0005e24c9901688f0005e25098c1688f0005e25890c1688f002a61d950c084820028a1d95004e40f002a6019d14c8463002a6019d1448c1b002a6019cd44901b002a6011cd44981b002a5811cd44a01b),
  (0x40aad548ac548ac54952ab502, 40, 0x2a61d950c840a7000661d9500ca86500064de15900a8a200066019d14ca855000651e158c0a8a200066019cd50a855000651cd6180a891000659e150c0a8a200066011cd58a855000659cd6100a891000659d160c0a891000661d950c0a8a5000661d950c0a8a200065811cd60a855000661cd5900a891000661d158c0a891000661d950c0a891000661d950c0a883002a61d9500c8465000661d9500ca864002a6019d14c8455002a6019cd508455002a6011cd588455002a5811cd608455),
  (0x40aad548ac548ad54952ab512, 42, 0x2a61d950c840aa000561d810caa4a600288de159006499002a4de1590084a3002891e158c06499002a51e158c084a300019d14e4a8608c0002146508dda859002899e150c06499002a59e150c084a300011d94e4a8608c0002146588dd28590000dd9524a8608c00021465891ce859000055a508de282700014660990de87e00005625890de83a0028a1d950c06499002a61d950c084a300011e14e4a8588c0001946608dd28590000de1524a8588c00019466091ce8590000562508dda8270000de15a4a8508c00011466099ce8590000562588dd282700005625891ce827002a61d950c08484002a41e1590c847b002a61d950c840a9002a61d950c840a80028a1d95004e442002a61d8114c8465002a61d811448c56002a6019d14c8453002a61d80d449056002a6019cd50845300021d14e485a8a1002a61d00d449856002a6011cd58845300021d94e48528a100021d952484e8a1002881e1590e447b002a59d00d44a056002a5811cd60845300019e14e48528a100019e152484e8a100011e15a484e8a1)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_6 : blocksOK 10 47 P10 P11 208 37 B11_6 = true := by decide +kernel

def B11_7 : List (ℕ × ℕ × ℕ) := [(0x40eac54cac54cac54d53ab2ac, 46, 0x2a61d950c840ab00288de1590064a4002891e158c064a400019d14e486a079002899e150c064a400011d94e486a0790000dd952486a0790002a58904d61c200002a609850d5c3b0002a6098514dc060028a1d950c064a400011e14e48698790000de15248698790002a60904d59c200002a609851cd4060000de15a48690790002a60984d51c200002a6098514dc200002a6098514dc000028a1d950c06487002881e1590c6480002841e1590ca480002a41e1590c487d0028a159d0c424aa00286159d0c824a60028a159d0c424a6000261589068dc410028a1d950c424aa002861d950c824a60028a1d950c424a6000261d89068d4410028a1d950c424a7000261d9504ca865000261d9508c6865000261d95084e8300028a1d9500c64660028a019d14c645a0028a019cd50645a0002268904d59c540028a011cd58645a0002268984d51c54000226898514dc5400022689850d5c2a002841e1590e4880002881e1590c647d002841e1590ca47d000162589068dc0f002a6159d0c408a60000a15a5068dc410000615a50a8dc410001e2589068d40900289811cd60645a0001a68a04d51c540001a68a0514dc540001a68a050d5c2a002a61d950c408a60000a1da5068d441000061da50a8d441000162589068dc090001268a0594dc540001268a058d5c2a0000e68a05915c2a0000a1d9524c68650000a1d95244e830000061d95248e830),
  (0x416a8540aa554aa5562a1562a, 40, 0x2821c9590c649a002a61d950c840ad002a61d158c840ac002a61d950c840ac002268d850095c12002a61d950048c93002a61c15904c888002a61c1590c4888002268c05915c888002268c0591d4888002a61d950084c120028c9c15924608f),
  (0x416a8544aa550aa5562a1568a, 40, 0x2821d9490c649f002849e152580cac002a61d950c840af002a59e150480cac002a61d950c804ac002a59e150048c94002a59c16104c88d002a61c1590c488d002a6159d0c840ae002a61d950c840ae002a59e150084c140028c9c15924608d),
  (0x416aa544a8550aa5562a4568a, 40, 0x1d0e84a4215897001d0e84a61580b0001d0e84a60194ae001a6848211d4c8b002268c8191d448b002a59e150048c9700051d940e68a08b000d1e140668988b002a61d950c840b0001d0e84a4161847002a59e150084c47002a61d950c048ae),
  (0x416aa544a8554aa5562a452a8, 40, 0x2a61d950c840b2000a61d85028d448001d8e80a61504b0001d0e80a61584b0002268c8191d448a000a61d8500e9498002a61c1590c8496000961c0590e688e000a61c0590e9496002a61d950c840b1002a61d95008c448000961c0590e689d),
  (0x416aa544a8554aa5562a456aa, 42, 0x1d0ea484215899002861d950c824b2001d8e80a461509700018c952461e896001d0e80a461589700010c95a461e89600021d9524688c88000148da5061e84600009625850e9c46002068c8191d648c001d8ea4861500b4001d828ca4611489001d028ca4619489002861d9500ca499002a61c1590c8497000d1e142468988c002a41e1590c4889001d0ea4861418b200026148590e9c96002a61d950c840b4001d0ea484161849002a61d950c048b1001d8ea4861500b3001d8ea404a11469002861d95008e449002a61d8114c4869001d8ea4860114b1001d0ea4860194b1002861c1590ca4970000ea48591d6088002841e1590e48890000614a590e9c96002a61d950c840b3002861d950c248b1),
  (0x41ea8544a855ca855e288a2a8, 40, 0x2a61d950c840b5002861d9500ca49b002a61c1590c849a002861c15908e48c002a61c15908c48a002861c1590ca48c002a61c1590c848a00099e1424690c91002068c09915e48c002268c09915c48a00099e24068d14b4000d9e24068914b4002068c0991d648c002268c0991d448a00099624068d1cb4000d962406891cb400158e8824611c91002861c1590ca49a002861d950c0a4ad002861c15908e48a002861c1590ca48a002068c09915e48a002068c0991d648a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_7 : blocksOK 10 47 P10 P11 208 43 B11_7 = true := by decide +kernel

def B11_8 : List (ℕ × ℕ × ℕ) := [(0x41ea8544aa554aa55628942a8, 40, 0xaa605810d5c4b000958d240629c4d002a61c1590c849c000d9e14246908900009c0da50616846000940da5061e846002a61d950c840b600289e15810c6467002861c1590ca49c),
  (0x41ea854ca8554a855e28a22a8, 40, 0x2a61d950c840b7002861d9500ca4a0002a61d9410c849f00091d940e46a078002a41d961084c8b000d1e140a469878002a41e1590c488b000a1c15a4690c8e00150e882461d89700150e88261d84b000090c1da4616896000d081e24596896001d0e8824615897001d0e88261584b000090c15a461e896000d08162459e89600150e8824619c9e002861d9410ca49f002881e152584cac002841d9610a4c8b002841e1590e488b00150e88061da4b0001d0e880615a4b0),
  (0x41aa9548a8558a855a29aa506, 40, 0x158ea448211ca2000661d9500ca86900158e8064a11c9e00150e8064a19c9e00158ea44a011cb600158e8064a11c91000661d9500ca8a2000661c1590ca89e000661c1590ca89100158ea448211c69001d8ea448211469002a61d9500c84690004a1c1590e689e),
  (0x41aa9548a8558a955a28aa512, 40, 0xd946608291ca3000668d811609cb3000d80562491e896000d00562499e896000d96244a811cb4002a61d9500c84a3002a41e159084c96000d9466081d2859002a6159d0c084b4001d8ea40a1504b3002a61d950048c59002881e159244c96),
  (0x41ea854ca855ca855e28aa2a8, 42, 0x2a61d950c840b90028a1d158c064b70028a1d950c064b70002a609850d5c4b0028a1d950c064b50028a1d9500c64a40028a1c1590c64a0002861c1590ca4a0002a41e159084c9a000d1e1424869879002881e1590c648c002841e1590ca48c000268d890615c4500150ea40861d8990028a159d0c064b200286159d0c0a4b2000261589068dc48000d9c26086914a3000268d851e094b3000268d891e054b3001d0ea4086158990028a1d950c064b2002861d950c0a4b2000261d89068d448000d942608691ca3000268d851609cb3000268d891605cb300158ea408611ca2000261d9504ca869000261d9508c6869002a61d950c840b80028a1d9500c646a002861c1590e48a0002881e159244c9a002841e159248c9a0000ea5890615c12002841e1590e488c0000a8da50615c45000068da50a15c4500286159d0c248b20000a15a5068dc480000615a50a8dc480000a8da51e054b3002861d950c248b20000a1da5068d448000061da50a8d4480000a8da51605cb30000a1d9524c6869),
  (0x41ea8544ae544ae54650942a8, 40, 0xaa605811d4c6c0009e25850294ca5002a61d950c840ba002861d9500ca46e00286019d148e46800286019d14ca4680009d26058294cb60009da6050294cb60009e25850294cb6),
  (0x416a8554a8554aa556aa056aa, 42, 0x2a61d950c840be000861da50294c51002851e1580a4cb20008e82259505cb3002859e1500a4cb20008e82251585cb300021da514c4a87500016258d04a9c4c0002a60d85149c13002861d9500a4cb20008e81a51605cb300019e2514c4a87500011e2594c4a875002a61d950048ca60028c1e15904a498002841e1590ca498000268e059149c920008c1e2591468a30008c1e25906949500026158d0689c4c000841e2590e9495002a61d950c840bd002a61d95048c0bc002a61d950c840bc0016268c04991cb8002861d9500a4c510028e1d81144a46f0028c8215a505cb30028c82152585cb30028c1e1592448a30028c1e15904a495002841e1590ca495002a61d950c840bb0028c81952605cb30026148c06991cb8),
  (0x412a9550a8558a955aa90a516, 40, 0x1e268c418914bd002a44995020dcb3000982a60d1c54b1000902a60d9c54b100016244d90a9c9c002a61d95004c8b3002a59d08144e05600099e1424c528a1002a41d89144e044002a61d950c840bf001d885424e128a1002a61d95004c8520028c1d891466044)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_8 : blocksOK 10 47 P10 P11 208 50 B11_8 = true := by decide +kernel

def B11_9 : List (ℕ × ℕ × ℕ) := [(0x416a8554a855ca855ea80a2a8, 40, 0x9a68e04115ca80002a60d85095c670028d891c160645a0028c099d16064490009a68e04151c54002a41e15904c8a100284099d160e449002a4099d1604c45002a41e1590c48a10016268c05891cbd002a4099d060d4b30009a68c061d1453002a4099d0e054b3001e268c058914bd002a40995060dcb30009a68c06151c53002a409950e05cb3000261d9508c68b800284099d1624c490028c099d16064450028c1e1592448a100284099d160e4450028c099d26054b30028c09952605cb3),
  (0x416aa554a8554a8556aa416aa, 42, 0x1da68c841160a70008e1d95006a470001602a48c519ca2002a51e1580c48b8001602a48c591ca2002a59e1500c48b800021d9524c4a87400016258d0689c6e00016258d04a9c190000a60d8515e819001582a48c611ca2002a61d9500c48b800019e1524c4a8740000a60d851d681900011e15a4c4a8740028e1d95004a4a7000a41e15904e8a2000a41e1590c68a2000268c861915c740015a68c8411e070001e06a48c1914b8001e0ea4841914b8001da68c84116070001606a48c191cb800160ea484191cb80016268c84191c710028e1d95004a470000a61d9500c6871000a51e1580c68b8000a59e1500c68b80008c1e1592468a20000ea4861915c7400016258d0689c1900006a48e1915c74001e268c841914b8000a61d9500c68b80016268c84191cb8),
  (0x412ab550a9550aa552ab45144, 40, 0x14a68c419d20be00064960191ce8a3000a45e01914e8a30005e1581268c8bb001d82a48d1460b2002a51e15808c4b4002a5161d804c8b4001d02a48d9460b2002a59e15008c4b4002a5961d004c8b40002159d24e8488a001d02a48e1458b2002a61d95008c4b4002a6159d004c8b40001961d24e8488a0001161da4e8488a002a6159d00c48a9002a6159d004c856002a61d95008c455002a6159d004c855002a5161d8c048bf002a5961d0c048bf002a6159d0c048bf),
  (0x416aa554a8554aa556aa456aa, 44, 0x1da68c841160aa000961d810e864be001d82a48c516099000214a50c699ca3001d02a48c596099000214a58c691ca300021d9524c688760002a48d85161c1e0001e258d04a941a0002a60d8515c81a0001e15a50c86804001d02a48c615899000194a60c691ca300019e1524c688760002a48e05159c1e0002a60d851d481700011e15a4c688760002a48e05951c1e000096258d1c680c0028e1d95004a4aa0028c1e15904a499002841e1590ca499000268c86191d4760014a68c059d20be00024960591ce8a300024960d91c68a30001e158d04a681e001da68c8415205a002861d95240c8bd0028e1d9524048bd000261d8d069484e001da68c04916070000261d95048e853000261d950c868530028e1d95008645a0028e1d81144a470001d268c860194bd0002268c85159c53001da68c860114bd0002268c85951c530002268d851c944e002841e159248c990000ea486191d47600006a48e191d47600014a60d8691c0c0000c962591c68a30001e15a5048e81e0001e258d06894170001e15a50c8681e001e268c858114bd0001a68c86151c530001a68e051c944e002a61d950c048bd0000e1da5069484e000061da50e9484e0001268e059c944e0000e1d952486853),
  (0x41ea855ca855ca855ea8aa2a8, 44, 0x2a61d950c840c00028d1e1580864b90028d9e1500864b900021d950c86a47300016258d0869c3c0002a60d89145c0e0028e1d9500864b900019e150c86a4730002a60d891c540e00011e158c86a4730028e1d9500864ab0028c1e15904a4a40028c1e1590864a40028c1e15908649b002881e1590c64a4002881e1590c649b002841e1590ca49b0001e0d89069641d0015a68c0851e0aa00286159d0c0a4be0028a159d0c064be0000e1589069e4510028e159d08064be0000a158d069e45100006158d0a9e4510001e0d8906a5421001da68c085160aa002861d950c0a4be0028a1d950c064be0000e1d8906964510028e1d9508064be0000a1d8d0696451000061d8d0a96451000160d8906a5c21001da68c085160a70000e1d9504aa4700000e1d95086a470000261d95084e83d0000a1d950c6a470000261d950c4a83d000261d950c8683d0028e1d9500864720002268d08595ca80002268d88515ca8002881e159244ca4002881e159244c9b002841e159248c9b0001e25890694c1d002841e15924c89b0001e258d069481d0001e258d0a9441d00016258d0a85c07002a6159d0804cbe0000a15a5069cc510000615a50a9cc510001e2589068d4210000615a50e9c8510001e258d06894210001e258d0a854210001a68e08515ca8002a61d950804cbe0000a1da50694c51000061da50a94c51000162589068dc21000061da50e9485100016258d0689c2100016258d0a85c210000a1d952468c700000e1d95244a83d0000e1d95248683d0000a1d9524c683d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_9 : blocksOK 10 47 P10 P11 208 58 B11_9 = true := by decide +kernel

def B11_10 : List (ℕ × ℕ × ℕ) := [(0x436a2544ac544ac94a52436a2, 40, 0xea60581d490ba000691cd4218a4ba000a61d9410c68ba001a6908c1d460ba00091e158244e8ba),
  (0x426b6504b6521498d94952696, 42, 0x2a61d950c840c4002a61d8914c40c3002a61d8d14840c300015cd0866a189f002a61d950c840c30000dd50866a189f00009d50c66a189f0002055ce491a814001a606814c91c7f001a602854d09c97001a60285490dc9700015d90e486a047001a60284c915c970000dd916486a04700009d9164c6a0470022592814c85c7f0022582914c49c97002258291484dc9700015e04e4929847002258290c855c970000de056492984700009e0564d29847001a68144c9e1098002268150dd848b10022681509d84cb10022680d09d854b1002a61d950c840c20004dd9026a094b70010de04269894b7001cd284261894b7002a59e014c8507f002a5821d4c49097002a5821d484d09700015284e49e1847002a5821cc8550970000d285649e18470000928564de1847001a60144c929c98002a6015cd1848b1002a6015c9184cb1002a600dc91854b1002a61d950c840c1002258150c869c98002a5815cc6108b1002a5815c8610cb1002a580dc86114b10021d40d086a58bc),
  (0x426b6504b6525498d949526b6, 44, 0x2a61d950c840c6002861c9914c24c4002861cd914824c400015cd0a46a18a0002861d590c824c40000dd50a46a18a000009d50e46a18a000021d64c4929815002861d950c824c40000dd90a46a14a000009d90e46a14a000021da4c492941500009d91646a0ca000021da544928c1500021da544d2881500021da544d0a805000291a544c9e0360020691814c9e4800020681914dca49900206819149ce49900015e24c4929849002068190c9d64990000de254492984900009e2544d2984900029164c49da01f002068150c9da4990000de258492944900009e2584d29449000291a4c49d601f00009e2585528c49000291a5449ce01f000291a544dca01f002a61d950c840c5002a61c150c858c200115e24068c98b90002691854c9e07b001d52a4060c98b9000261d854c9287b000259d50c86a0a9002861d814c9248000286019d4d0a49900286019d490e499000152a4c49e184900286019cc9164990000d2a5449e1849000092a544de184900021d64c491a81f00286015cc91a4990000d2a5849e1449000092a584de144900021da4c491681f00021da544c92836000092a5855e0c4900021da54490e81f00021da544d0a81f002861c150ca58c20001e25854c9287a0000691a54c9e07b0021d8150c86a4a60021d8150e6848bd0021d8150a684cbd00019e24c49168520021d80d0a6854bd00019e254490e85200019e2544d0a8520021d40d0a6858bd00015e258490e85200015e2584d0a852000061da54c9287b0000de258550a852),
  (0x42ab4508b55214a8d54aa544a, 40, 0x2821d8514ca4c300051a6814ca1c94002a61d8d14840c70005e01a55288cae002a61d950c840c70005e01a4d2894ae00019d64d28860af001a60a814d05c94001a682094dd049d001a682095c50cae001a68208dc514ae0022592814c85c940005281a54dca09d0022681915c48cae002268190dc494ae0019280494de609d0021c51964c0a8c1002a59e014c850940005e01a54d0a89d002a6019d5048cae002a6019cd0494ae0019e00494d2689d0021d80514ca689d),
  (0x42eb450cb45254a8d14ba52a4, 42, 0x1cd288624194c3001cd284a25418c70016605828d09c9f00021d48e69184ae001a609428d05c9f00021d84e69148ae0000dd51a68608b00022591428c85c9f00019e04e68950ae0000dd4a268590b00000dd86268950b00022591688c05cc30004dd500a6a189f0008dd90066a149f000268a04dd914b00010de080669949f000269184de094b0000269148de058b0001cd2880661949f000261d84d2894b0000261d48d2858b0000259d50ca860b0002a59d420c8509f00019284e6095cae0000d14aa6059cb00000d186a6095cb00022591688c41cc70001e05a4d2894ae0001e0964d2858ae0001d9164ca860ae0000ca06a5915cb0000119d64ca068ae)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_10 : blocksOK 10 47 P10 P11 208 63 B11_10 = true := by decide +kernel

def B11_11 : List (ℕ × ℕ × ℕ) := [(0x42eb450cb45254b8d14ba52b4, 44, 0x1cd28a604194c4001d528822458cc3001cd288224594c30002095ce4592894001868a014dd24a000015d90e468a0970000dd916468a097000291a544de0811000291a544c9e04a0020691814dca4a000015e08e46918970000de096469189700028a2544dd9011002068150dd8a4b200015da604ca90440000dda6054a9044002861d950c0a4c4002a61d8114c84c30008dd90246a14a0000260a854d19c970010de08246994a00002592854ca1c970010dc26068994b2000269148c61d844001cd288246194a0000259e054ca9097001cd026860994b2000261d48c691844001cc826859214b2000259d50c68a044000259d50c4aa0bf002861d814d0a4a000015288e461d8970000d2896461d89700020aa544d19c1100286015cd18a4b2000151a684ca1c4400021da544c9284a0000d1a6854a1c44002861d8114ca4c300011a6854ca1c94000060aa54d19c970001e0964c6918110000592a54ca1c970001d9164c68a011000069148e61d84400285815cca124b200014a2684d19c440000ca2685519c4400019e2544d0a84a000151a684e09cbf000059e254ca9097000119d64c60a811000061d48e691844000059d50e68a044),
  (0x42eb450cb452d4b8d14bad2b4, 46, 0x1d52a4a040d8c6001d52826084d8c4001cd282608558c400019d50e486a07f001cd282608594c400015d90e486a07f0000dd916486a07f00021da548d0680d0001d9164c86282d0020a91814dc64a400015e24c86918990000de25486918990002a60944dd90240000de25886914990002a60984dd50240002a609855cd0240002a609855cd0020028a1d950c064c60028a1c1914c64c4002861c1914ca4c4000260a8594d1c7f00115e240868d8a40000a91854de24990000691894de24990001d9148c6a6024001d52a40860d8a40000a1d854d2a499000061d894d2a499000119d48c626824001e240a8550d8be000259d50c68a056000259d50ca86056000259d50c86a02b0028a1d814d064a4000152a4c861d8990000d2a54861d8990002268944d19c240000d2a58861d4990002268984d15c24000119d64c86a02d000226898550dc24000226898550dc02002861c1914e48c40000a268594d1c7f00006268994d1c7f00012a589460dc0d0000691a54de08990001d9164c68a0240001d9164ca860240001d9164ca860020021d8150ca864be0001a60a84d15c560001a60a8550dc560001a60a854d1c2b0001660a8590dc560001660a858d1c2b000061da54d28899000119d64c60a824000119d64ca06824000119d64ca068020000e60a85951c2b000099d50e686056000099d50e46a02b000059d50e4aa02b),
  (0x436b0514b25254c8ca92136a2, 40, 0x1d52a4e00858c7000862582914dcaf001660582908dcaf001a60d429085caf0022591428c85caf002259168c049cc700059d64128ca0af000d5da41284a0af00115e240e8498af001d52a40e0498af002a59d420c850af00255c900e8618af),
  (0x422b7520b752148add4852148, 40, 0x2a61d950c840c8002a45d940c920c5002a49d940c520c500019ca45294e0b9002a4dd9408520c500019ce45294a0b900019ce4929460b900019ce49069606a002a55d8c08520c500019d64528ca0b900019d64928c60b900019d649068e06a00019d64d28860b900019d64d068a06a00019d64d0a8606a002a59d4c08520c500015da4528ca0b900015da4928c60b900015da49068e06a00015da4d28860b900015da4d068a06a00015da4d0a8606a0000dda5528860b90000dda55068a06a0000dda550a8606a00009da550e8606a002a61d4c08518c500015e24528c98b900015e24928c58b900015e249068d86a00015e24d28858b900015e24d068986a00015e24d0a8586a0000de25528858b90000de255068986a0000de2550a8586a00009e2550e8586a0000de25928854b90000de259068946a0000de2590a8546a00009e2590e8546a00009e2591684c6a002a59d40c852085002a6019d4c90484002a6019d4c50884002a6019d4d048a8002a6019d4850c84002a6019d4904ca8002a6019d4508ca8002a6019cc851484002a6019cc9054a8002a6019cc5094a8002a6019c850d4a8002a6015cc851884002a6015cc9058a8002a6015cc5098a8002a6015c850d8a8002a600dc85158a8002a5815cc852084002a5815cc9060a8002a5815cc50a0a8002a5815c850e0a8002a580dc85160a8002a540dc851a0a8)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_11 : blocksOK 10 47 P10 P11 208 68 B11_11 = true := by decide +kernel

def B11_12 : List (ℕ × ℕ × ℕ) := [(0x426b6524b652549ad949526b6, 46, 0x2a61d950c840c9002909e1814c64c600290de1814864c600019ce4906960a4002915e180c864c600019d649068e0a400019d64d068a0a40002a550c49da028002919e140c864c600015da49068e0a400015da4d068a0a40002a590c49d60280000dda55068a0a40002a591449ce0280002a59144dca0280002a59144dca0080002a59144c9e037002921d940c864c600015e249068d8a400015e24d06898a40002a610c49d58280000de25506898a40002a611449cd8280002a61144dc98280002a61144dc98080000de25906894a40002a611849cd4280002a61184dc94280002a61184dc94080002a611855c8c280002a611855c8c080002a611855cc8080002a59144dca001002921d944c824c8002a41d944c920c5002a41d950c860c50002691854c9e07c001da690054ca0c0000261d854c92884000261d914c86884000259d50c68a03f002921d814c8648700292019d4c4a4aa00292019d484e4aa0001a690c49d605a00292019cc8564aa0001a691449ce05a0001a69144dca05a0001a69144c9e02e00292015cc85a4aa00016691849ce05a0001669184dca05a0001669184c9e02e0000e691855ca05a0000e6918549e02e0000a691854de02e0002269144c9d829002901d964c860c500012a5854c9e07c00006a5914c9e07c0001da550c68a00a00291815cc8624aa00016692049cd85a0001669204dc985a0001669204c9d82e0000e692055c985a0000e6920549d82e0000a692054dd82e0001a69144c9e0290000e692059c945a0000e6920589d42e0000a692058dd42e0001669184c9e029000121da54c86884000119d64c68a03f0000a6920595cc2e0000e6918549e0290000a691854de029000059d64d28a03f),
  (0x42eb452cb452d4bad14bad2b4, 48, 0x1da6909440e0c9001d82a50c8560c6001d82a51484e0c600019d64d086a080001d42a51884e0c600015da4d086a0800000dda55086a0800002a59148dc60100001e2591484e834001d42a52084d8c600015e24d08698800000de25508698800002a61148dc58100000de25908694800002a61188dc54100002a611895c4c1000029209855ce403002921d948c064c9002901e1854ca4c6002901e1894c64c6000128a0594de480002881e1914c64c60000a920594de48000006920994de4800001e1189468e410001da6900854e0ab000121d854caa4aa000121d894c6a4aa000121d89468e4420000a1d914c6a4aa0000a1d91468e442000061d914a8e442000259d50c86a02c002921d814c864ab0001a690c855e0aa0001a691484de0aa0001a69148dc604200016691884de0aa0001669188dc60420000e691895c604200021289854de42c002881e1a54c50c60000aa60594dd08000006a60994dd0800001e2589468d01000006a61194dc8800001e2591468c8100001e25914a8c4100001da550ca8600300016692084dd8aa0001669208dc58420000e692095c58420001928a054de42c0000e692099c54420001528a058de42c0000a1da54c690aa0000a1da5468d042000061da54a8d042000119d64c86a02c0000d28a0595e42c000061da5528c842000099d64d06a02c000059d64d0aa02c002a61d950c840ca),
  (0x492db49124b6d24492db49124, 42, 0x2a61d950c840cc0005a821cd50a4c80009a821cd5064c8000224984dd528c00011a821cd4864c8000225184dd4a8c0000225188dd468c0000225188c5d68720015a821cd0864c8000225584dd0a8c0000225588dd068c0000225588c5d2872000225590dc868c0000225590c5ca872000225590c9c6872000225590c85e83e001da8214d0864c8000225d84d50a8c0000225d88d5068c0000225d88c552872000225d90d4868c0000225d90c54a872000225d90c946872000225d90c85683e000225d94d0868c0000225d94c50a872000225d94c906872000225d94c85283e000225d94d086872000225d94d04a83e000225d94d08683e0021a81d4d0864c80001e6184d50a8c00001e6188d5068c00001e6188c5528720001e6190d4868c00001e6190c54a8720001e6190c9468720001e6190c85683e0001e6194d0868c00001e6194c50a8720001e6194c9068720001e6194c85283e0001e6194d0868720001e6194d04a83e0001e6194d08683e00016619cd0868c000016619cc50a87200016619cc90687200016619cc85283e00016619cd08687200016619cd04a83e00016619cd08683e00012619cd48687200012619cd44a83e00012619cd48683e0000a619cd50683e002a61d950c840cb0029a01d4d0864c80001e6984d50a0c00001e6988d5060c00001e6988c5520720001e6990d4860c00001e6990c54a0720001e6990c9460720001e6990c85603e0001e6994d0860c00001e6994c50a0720001e6994c9060720001e6994c85203e0001e6994d0860720001e6994d04a03e0001e6994d08603e00016699cd0860c000016699cc50a07200016699cc90607200016699cc85203e00016699cd08607200016699cd04a03e00016699cd08603e00012699cd48607200012699cd44a03e00012699cd48603e0000a699cd50603e0001669a0d085cc00001669a0c509c720001669a0c905c720001669a0c851c3e0001669a0d085c720001669a0d049c3e0001669a0d085c3e0001269a0d485c720001269a0d449c3e0001269a0d485c3e0000a69a0d505c3e0001269a0dc854720001269a0dc4943e0001269a0dc8543e0000a69a0dd0543e0000a69a0dd4503e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_12 : blocksOK 10 47 P10 P11 208 72 B11_12 = true := by decide +kernel

def B11_13 : List (ℕ × ℕ × ℕ) := [(0x496da49525b6925496da496da, 48, 0x2a61d950c840ce0009a821cd5064c90011a821cd4864c9000225188c5d68ab0015a821cd0864c9000225588c5d28ab000225590c5ca8ab000225590c85e866001da8214d0864c9000225d88c5528ab000225d90c54a8ab000225d90c856866000225d94c50a8ab000225d94c852866000225d94d04a866000225d94d0868350021a81d4d0864c90001e6188c5528ab0001e6190c54a8ab0001e6190c8568660001e6194c50a8ab0001e6194c8528660001e6194d04a8660001e6194d08683500016619cc50a8ab00016619cc85286600016619cd04a86600016619cd08683500012619cd44a86600012619cd4868350000a619cd5068350002a5d94d08602f0029a1cd504824cc0001a861cd50a4c80001a8e1c550a4c8000260dc5509a8850000e9a1c550a4c80002619c5508e8850002619cd50868850002619cd450a85b0029a01d4d0864c90001e6988c5520ab0001e6990c54a0ab0001e6990c8560660001e6994c50a0ab0001e6994c8520660001e6994d04a0660001e6994d08603500016699cc50a0ab00016699cc85206600016699cd04a06600016699cd08603500012699cd44a06600012699cd4860350000a699cd506035000225d94d08682f0001669a0c509cab0001669a0c851c660001669a0d049c660001669a0d085c350001269a0d449c660001269a0d485c350000a69a0d505c350001e6194d08682f0000ea61c55098c80001a25c5508e8850001a25cd50868850001a25cd450a85b0001269a0dc494660001269a0dc854350000a69a0dd0543500016619cd08682f0000a69a0dd4503500012619cd48682f0000e25d950868850000e25d9450a85b0000a619cd50682f0000625d94d0a85b002a61d950c840cd),
  (0x49ad849926b612649ad8b6000, 40, 0x4225d94c92831002a61d950c840cf0004225d94d0a80300126821d94c84ca0004225d90d4a80300166821d90c84ca00042a619cd094000004225590dca803001e6821590c84ca00042a6194d09c0000042a6190d49c0000041e5590e0a8030022681d590c84ca00042a5d94d0a00000042a5d90d4a00000042a5590dca00000042619cd50a82f002a61d950c084cd00042619cd49280100042619c94d28010004260dc959280100041e5590e8a003002a601d590c84ca0004225d94d0a8000004225d90d4a8000004225590dca80000041e5590e0a80000041a0dc9652801),
  (0x49ed849d27b612749ed8b62d8, 50, 0x2618dc854128ce00022518dc8568c900022558dc8528c9000225590c85e887000225d8d48528c9000225d90c856887000225d94c852887000225d94d08685e0001e618d48528c90001e6190c8568870001e6194c8528870001e6194d08685e00016619cc85288700016619cd08685e00012619cd48685e00029a0dc95064310029a1cd508064ce0001a861cd50a4c90001a8a1cd5064c90001a8a05d50e4870001a8e1c95064c90001a8e05d50a4870001a8e09d5064870001a8e09c55245e0000e9a1c95064c90000e9a05d50a4870000e9a09d5064870000e9a09c55245e0000a9a0dd5064870000a9a0dc55245e000069a0dc95245e0002619cd48528310001e698d48520c90001e6990c8560870001e6994c8520870001e6994d08605e00016699cc85208700016699cd08605e00012699cd48605e00021a8dc95064310001669a0c851c870001669a0d085c5e0001269a0d485c5e0001da8e095064310000ea61c95058c90000ea605d5098870000ea609d5058870000ea609c55185e0000aa60dd5058870000aa60dc55185e00006a60dc95185e0001a25cd48528310001269a0dc8545e00015a8e09d0643100011a8e09d464310000aa619d504c870000aa619c550c5e00006a619c950c5e0000e25d9485283100006a619cd5085e0000a25d94c528310000625d94c92831002a61d950c804cf)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB11_13 : blocksOK 10 47 P10 P11 208 75 B11_13 = true := by decide +kernel

def B11 : List (ℕ × ℕ × ℕ) := B11_0 ++ (B11_1 ++ (B11_2 ++ (B11_3 ++ (B11_4 ++ (B11_5 ++ (B11_6 ++ (B11_7 ++ (B11_8 ++ (B11_9 ++ (B11_10 ++ (B11_11 ++ (B11_12 ++ (B11_13)))))))))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk11 : blocksOK 10 47 P10 P11 208 0 B11 = true := blocksOK_app (k := 8) okB11_0 rfl (blocksOK_app (k := 7) okB11_1 rfl (blocksOK_app (k := 6) okB11_2 rfl (blocksOK_app (k := 6) okB11_3 rfl (blocksOK_app (k := 5) okB11_4 rfl (blocksOK_app (k := 5) okB11_5 rfl (blocksOK_app (k := 6) okB11_6 rfl (blocksOK_app (k := 7) okB11_7 rfl (blocksOK_app (k := 8) okB11_8 rfl (blocksOK_app (k := 5) okB11_9 rfl (blocksOK_app (k := 5) okB11_10 rfl (blocksOK_app (k := 4) okB11_11 rfl (blocksOK_app (k := 3) okB11_12 rfl (okB11_13)))))))))))))

set_option maxRecDepth 100000 in
theorem len11 : B11.length = 78 := by decide +kernel

theorem cl11 : ClassP 11 (inP 11 P11 208) 47 :=
  stepP 10 _ _ 39 47 (stepB_sound 10 47 P10 78 P11 208 B11 len11 blk11) (by intro E d h1 h2; omega) cl10

def P12 : ℕ := 0x497b68497497b68497497b68497b68b68b68495b68495495b68495495b68495b68000b68493b6c493493b6c493493b6c493493b6cb6c492b6c492492b6c492492b6c492492b6c000491b6e491491b6e491491b6e491491491b6e427ad85272d8527527ad8527527ad8ad8ad8426ad85262d8526526ad8526526ad8ad8000423adc5232dc523523adc523523523adcadc422add5222dd522522add522522522add52242bad050b2d45235298d452aa5412ba94ac4427ad85072d85275278d8527527ad8ad8ad8426ad85062d85265268d8526526ad8ad8000425ada5052da5255258da525525ada525ada424adb5042db5245248db524524adb524524427ad85072d85235278d8527527a58ad8ad8427ad85072d85235258d8527527a58a98ad8427ad85072d85235258d8526527a58a98ac8425ada5052da5215258da525525a5a525ada424adb5042db5205248db524524a5b524524425ad85052da5215258da525525a5a125ada425ad85052da5215248da525525a5a125a9a424ad95042db5205248db524524a5b12452441faa055f2a055f2a055faa0aa0aa0aa0aa0410aa65512a25582a4559aa60a6459519226414aa25542a05552aa555aaa054aaa4550a2415aa25552a05552aa555aa8055aaa445aaa414aa35542a05542ab554aa9054aab444454415aa05552a25552a8555aaa055aaa115aaa41caa35442b85442b8544943943aa341c41c41faa054f2a055f2a055f8a0aa0aa0aa0aa041faa054f2a05572a055f8a0a20aa0aa0aa041daa25442a95542a95548a2942aa241d94241faa05472a055f2a055f8a08a0aa0aa0aa0415aaa5442a25552a85558a8454aaa5058a2416aa95462a15562a85568a9452aa0aa9512416aa95462a15562a85568a8452aa0aa9502416aa95462a05562a85568a8452aa1aa9406416aa85462a05572a85578a8453aa0aa80a8415aaa5452a05552aa5558aa451aa2454aa8415aaa5452a25512a85558aa454a2a514aa0414aaa5452a25512a85548aa455a2a51528a416aa15462a85522a85548a9156a29a89416415aa25452a85512aa5548aa155a2a455a8a415aa25452a85512aa5548aa155a2a454a88415aa25442a85512aa5548aa155a2a45588a414aa35442a95502aa5548ab154a2b454514414aa25452a85512aa5548aa155a2a45528a417aa05432a85552a85568a81578a8a28a88417aa05432a85542a85578a81578a8a28a28416aa15422a85542a95568a81568a9a2944640fab054f2b054f2b054f54fab0ab0ab0ab040eab054e2b054e2b054e54eab0ab0ab000040bab454b2b054b2b454b54bab444bab4ab4409ab65492b25492b4549549ab6449509ab640bab454b2b054b2b054b54bab440bab4ab440bab054b2b054b2b454b54bab404bab4ab440aab154a2b054a2b554a54aab504aab544a40aab154a2b054a2b554a54aab404aab544240aab054a2b154a2b454a54aab504aab510a40aab054a2b054a2b554a54aab504aab504a40dab25442b95442b9544544942ab240d94240fab05472b054f2b054f54f8b0ab0ab0ab040dab25452b054d2b254d54d8b0ab2445ab240cab35442b154c2b254c54c8b0ab344450440dab25452b054d2b054d54d8b2ab240dab240cab35442b054c2b154c54c8b2ab340c44440cab15442b054c2b154e54e8b0ab103144640fab05472b054b2b054f54f8b0a30ab0ab040eab15462b054a2b154e54e8b0a30ab144240eab05462b054a2b054f54f8b0a30ab003040fab05472b054b2b054d54f8b0a30a90ab040fab05472b054b2b054d54e8b0a30a90aa040dab25452b05492b054d54d8b2a3240dab240dab25452b05492b054c54d8b2a3240da9240dab05452b05492b254c54d8b2a3204da9240fab05432b45492b454a54b8b0940a30a9040eab15422b45482b454a54a8b1941a3140e40fab05432b054f2b054f54f8b08b0ab0ab040eab05422b054e2b054f54f8b08b0ab003040fab05432b054d2b054f54f8b08b0a30ab040fab05432b054d2b054e54f8b08b0a30a9040fab05432b054c2b054f54f8b08b0a30a3040bab45432b054b2b454b54b8b444bab4ab440aab55422b154a2b454a54a8b544aab550a40aab55422b154a2b454a54a8b444aab550240aab55422b054a2b554a54a8b444aab544240aab45422b054a2b454b54b8b444bab403440bab45432b054b2b454b54b8b4449ab0ab440aab55422b154a2b454a54a8b5448ab050840aab55422b054a2b554a54a8b5448ab144a40aab55422b054a2b554a54a8b4448ab144240aab55422b054a2b454a54a8b5448ab140a40aab45422b054a2b554a54a8b5448ab104a40bab45432b05492b454b54b8b444ba34ab440bab45432b05492b454b54b8b444aa34ab040bab45432b05492b454a54b8b444ba34a9440aab55422b15482b454a54a8b544aa3550a40aab45422b05492b454a54b8b444ba3409440aab45422b05482b554a54a8b544aa3504a40aab45422b05482b454b54b8b444ba3403440bab45432b05492b454b54b8b4449a30ab440bab45432b05492b454a54b8b4449a30a9440bab45432b05492b454a54b8b4448a30a9040aab55422b15482b454a54a8b5448a3150a40aab55422b05482b554a54a8b5448a3144a40bab45412b054b2b454b54b8b44498b0ab440bab45412b054a2b454b54b8b44498b0a3440bab45412b054a2b454b54b8b44488b0a3040bab05432b45492b454a54b8b414ba34a9440bab05422b55482b554a54a8b414aa3494040aab15422b45482b554a54a8b514aa3544a40aab15422b45482b454a54a8b514aa3540a40aab05432b45492b454a54a8b414ba3428440aab05422b45482b554a54a8b514aa3504a40bab05412b454b2b454b54b8b414a8b4ab040bab05412b454a2b454b54b8b414b8b4a3440aab15402b454a2b554a54a8b414a8b544240dab25442b05442b054d54d832ab240d83240dab05462b15462b154c54c832ab028994240dab05462b05462b054d54d832ab028983240dab05452b25452b254c54c832ab0149a8240dab05442b25442b254d54d832ab014983240dab05452b05452b254c54c832ab204da8240dab05442b05452b254c54d832ab204d89240dab05452b25452b254954c832a9214daa240dab05442b25452b254954c832a9214d8a240dab05442b25442b254954d832a9214d83240fab05422b05472b054e54f8308b0ab089040eab15422b05462b154e54e8318b0ab144a40eab15422b05462b054e54e8318b1ab140e40eab15422b05462b054e54e8308b1ab140640eab05422b05462b154e54e8308b1ab104640fab05432b05472b054d54e8308b0a90aa040eab15422b05462b154c54e8318b0a9144a40eab15422b05462b054c54e8318b1a9140e40eab05422b05462b154c54e8318b1a9104e40fab05432b05452b054f54f8308b0a30ab040fab05432b05452b054e54f8308b0a30a9040eab15422b05442b154e54e8308b1a3144640eab15422b05442b054e54e8318b1a3140e40eab05422b15442b154e54e8308b1a3114640eab05422b05442b154e54e8318b1a3104e40dab25412b05452b254d54d8328b244dab240dab25412b05452b254c54d8328b244da9240dab25412b05442b254d54d8328b244da3240dab25412b05442b254d54d8328b244ca3040dab25412b05442b254c54d8328b244da1240dab05412b25452b254d54d8328b214cab040dab05412b25452b254c54d8328b214da9240dab05412b25452b254c54d8328b214ca9040dab05412b25452b254c54c8328b214da8240dab05412b25442b254d54d8328b214da3240dab05412b25442b254d54d8328b214ca3040dab05412b25442b254c54d8328b214da1240dab05402b25452b254c54d8328b214d89240cab15402b25442b354c54c8338b314c44c407ab85472b85472b8547547547ab8ab8ab8406ab85462b85462b8546546546ab8ab8000405aba5452ba5452ba545545545aba545aba405aba5442bb5442bb544544544aba544940404abb5442bb5442bb544544544abb544544405aba5452b85452ba545545545aba445aba404abb5442b95442bb544544544abb444544404abb5442b95442ba544544544abb444504404abb5442b85442bb544544544abb444444405aba5452b85452b8545545545aba405aba405aba5442b95442b9544544544aba405942404abb5442b95442b9544544544abb404544404ab95442bb5442bb544544544ab9140544405ab85452b85452ba545545545aba045aba404ab95442b95442bb544544544abb044544407ab85432b85472b85475475478b8ab8ab8406ab95422b85462b95465465468b8ab9442406ab95422b85462b85465465468b9ab9406407ab85432b85452b85475475478b8a38ab8407ab85432b85452b85465475478b8a38a98406ab95422b85442b85465465468b9a39406406ab85422b85442b95465465468b9a39046407ab85412b85472b85475475478b88b8ab8407ab85412b85462b85475475478b88b8a38405aba5412ba5452ba5455455458ba545aba405aba5402bb5442bb5445445448ba544940405aba5402ba5452ba5455455458ba5458ba404abb5402bb5442bb5445445448bb544544405aba5412b85452ba5455455458ba445aba405aba5412b85452ba5455455458ba444ab8405aba5412b85442ba5455455458ba445a3a405aba5412b85442ba5455455458ba444a38405aba5402b85452ba5455455458ba4448b8404abb5402b95442bb5445445448bb444544405ab85412ba5452ba5455455458ba145aba405ab85412ba5442ba5455455458ba145a3a405ab85402ba5452ba5455455458ba1458ba405ab85402ba5452ba5455455458ba1448b8404ab95402bb5442bb5445445448bb144544407ab85432b85432b8547547547838ab8ab8406ab95422b85422b9546546546839ab9446406ab95422b85422b8546546546839ab9406406ab85422b95422b9546546546839ab8144406ab85422b85422b9546546546839ab9046407ab85432b85432b8545547547838a98ab8407ab85432b85432b8545546547838a98aa8407ab85422b95422b9544546546838a98940406ab95422b85422b9544546546839a99446406ab95422b85422b9544546546839a98444406ab95422b85422b8544546546839a99406406ab85422b95422b9544546546839a99146406ab85422b95422b9544546546839a98144406ab85422b85422b9544546546839a99046407ab85432b85432b8545545547838a88ab8407ab85432b85432b8545545546838a88ab0406ab95422b85422b9544544546839a89446406ab85422b95422b9544544546839a89146407ab85412b85432b85475475478388b8ab8407ab85412b85432b85465475478388b8a98407ab85412b85432b85465465478388b8a88407ab85412b85422b85475475478388b8a38406ab95402b85422b95465465468398b9446406ab95402b85422b95465465468398b8444406ab95402b85422b95465465468388b9442406ab85402b95422b95465465468398b9146406ab85402b95422b95465465468398b8144406ab85402b95422b95465465468388b9142406ab85402b85422b95465465468398b9046407ab85412b85432b8545547547838898ab8407ab85412b85432b8545546547838898aa8407ab85412b85432b8545546546838898aa0407ab85412b85422b8545547547838898a38407ab85412b85422b8545546547838898a28407ab85412b85422b8544547547838898a18407ab85402b85432b85455465478388988a8406ab95402b85422b9544546546839899446406ab85402b95422b9544546546839899146407ab85412b85412b8547547547838838ab8407ab85412b85412b8546547547838838a98407ab85412b85412b8546546547838838a88406ab95402b85402b9546546546839839446406ab85402b95402b9546546546839839146405aba5412ba5412ba54554554583a545aba405aba5412ba5412ba54454554583a545a9a405aba5412ba5412ba54454454583a545a8a405aba5402ba5412ba54554554583a5458ba405aba5402ba5412ba54454554583a54589a405aba5402ba5402ba54554554583a54583a404abb5402bb5402bb54454454483b54454440faa055f2a055f2a055f2a0aa0aa0aa0aa040daa255d2a055d2a055d2a0aa2aa240daa240baa455b2a055b2a055b2a4aa441baa4aa440baa455a2a055a2a055b2a4aa441baa482440aaa555a2a055a2a155a2a4aa541aaa544a40aaa555a2a055a2a055a2a4aa541aaa540a40aaa455a2a055b2a055b2a4aa441baa40a440baa455b2a055b2a055b2a4aa4419aa0aa440aaa555a2a055a2a055a2a5aa5418aa141a40daa25512ac5512ac5512ac95295240daa240daa25502ad5502ad5502ad95295240d95240daa05512ac5512ac5532ac95295202caa040faa05572a055f2a055f2a08a0aa0aa0aa040eaa15562a055e2a055e2a18a0aa1aa141640eaa15562a055e2a055e2a08a1aa1aa140e40daa25552a055d2a055d2a28a2aa241daa240daa25552a055d2a055d2a28a2aa241caa040daa25552a055c2a055d2a28a2aa241da2240daa25542a055d2a055d2a28a2aa241d8a240caa35542a055c2a155c2a28a3aa341c44c40eaa15522a55522ac5522ac851950aa150a40eaa15522a45522ac5522ac851951aa140e40faa05512a65512ae5512ae850950950aa040eaa15502a65502ae5502ae85195195140e407aa85572a85572a85572a8557aa8aa8aa8405aaa5552a85552a85552aa555aaa415aaa404aab5542a85542a95542aa554aab414444404aab5542a85542a85542ab554aab414414405aaa5552a85552a85552a8555aaa405aaa404aa95542a85542a85562a9556aa9029416405aa85552a85552a85552aa555aaa015aaa406aa95522a85522ac5522ac552851aa9406406aa85522a95522ac5522ac552851aa9106407aa85532a85532a85572a8557828aa8aa8407aa85532a85532a85562a8556828aa8a80407aa85522a85532a85562a8557828aa8888407aa85522a85522a95562a9556828aa8850407aa85522a85522a85572a8557828aa8828406aa95522a85522a85562a9556829aa9416406aa95522a85522a85562a8556829aa9406406aa85532a85532a85562a8556829aa8284406aa85522a85522a95562a9556829aa8054406aa85522a85522a85562a9556829aa9016403aac5532ac5532ac5532ac553553aacaac403aac5522ac5522ac5522ac552552aac800402aad5522ac5522ac5522ad552552aad412402aad5522ac5522ac5522ac552552aad402402aac5522ac5522ad5522ad552552aac050402aac5522ac5522ac5522ad552552aad012402aac5522ac5522ac5522ac553553aac00c403aac5512ac5512ae5512ae551551850aac403aac5512ac5512ac5512ac55355380caac401aae5512ae5512ae5512ae551551551aae401aae5502ae5502af5502af550550550850400aaf5502af5502af5502af550550550550407aa85572a05572a85572a8457aa8aa8aa8406aa95562a05562a85562a8456aa9aa9406407aa85552a05572a85572a8455aa88a0aa8407aa85552a05552a85572a8457aa8828aa8405aaa5552a25552a85552aa455aaa515aaa405aaa5542a25552a85552aa454aaa5148a0405aaa5542a25542a85552aa455aaa51582a404aab5542a35542a95542aa454aab514544404aaa5542a25542a85552aa455aaa51502a405aaa5552a25552a85552a8455aaa505aaa405aaa5542a25552a85552a8454aaa5058a2405aaa5542a25542a85552a8455aaa50582a405aaa5552a05552aa5552aa455aaa455aaa405aaa5542a05552aa5552aa454aaa4548a0405aaa5542a05542ab5542ab454aaa454850404aab5542a15542aa5542ab454aab454514404aab5542a15542aa5542aa454aab454504404aab5542a05542ab5542ab454aab454454404aaa5542a05542aa5552aa455aaa45502a405aaa5552a05552a85552aa455aaa415aaa405aaa5552a05552a85552aa455aaa414aa8405aaa5542a05552a85552aa454aaa4158a2404aab5542a15542a95542aa454aab414544404aab5542a15542a85542ab454aab414514404aab5542a05542a95542ab454aab414454405aa85552a05572a85572a8457aa80a8aa8404aa95542a15562a85562a9456aa90a9516404aa95542a15562a85562a8456aa90a9506404aa95542a05562a95562a9456aa90a8454404aa95542a05562a85562a9456aa90a9416407aa85572a05572a85572a8453aa0aa8aa8407aa85562a05572a85572a8452aa0aa88a0407aa85562a05562a85572a8453aa0aa8828406aa95562a15562a85562a9452aa0aa9512406aa95562a15562a85562a8452aa1aa9506406aa95562a15562a85562a8452aa0aa9502406aa95562a05562a95562a9452aa0aa9452406aa95562a05562a85562a9452aa1aa9416406aa95562a05562a85562a9452aa0aa9412406aa95562a05562a85562a8452aa1aa9406406aa85562a05562a85562a9452aa1aa9016407aa85572a05572a85572a8451aa0aa0aa8406aa85562a05562a95562a9450aa1aa1056405aaa5552a25552a85552aa451aa2515aaa405aaa5552a25552a85552aa451aa2514aa8405aaa5552a25552a85552aa450aa2514aa0405aaa5542a25542a85552aa451aa251582a404aab5542a35542a95542aa450aa3514544404aab5542a35542a85542ab450aa3514514405aaa5552a05552aa5552aa451aa2455aaa405aaa5552a05552aa5552aa451aa2454aa8405aaa5552a05552aa5552aa450aa2455aa2405aaa5552a05552aa5552aa450aa2454aa0405aaa5542a05542aa5552aa451aa245582a404aab5542a15542aa5542ab450aa3454514404aab5542a05542ab5542ab450aa3454454407aa85522a45532ac5532ac452950aa88a0407aa85522a45522ad5522ad452950aa8850406aa95522a55522ac5522ad452950aa9512406aa95522a55522ac5522ac452950aa9502406aa95522a45522ad5522ad452950aa9452406aa95522a45522ac5522ad452950aa9412406aa95522a45522ac5522ac452951aa9406406aa85522a45522ac5532ac453951aa802c407aa85532a45532ac5532ac451950aa0aa8407aa85532a45532ac5532ac450950aa0aa0406aa95522a55522ac5522ad450950aa1512406aa95522a45522ad5522ad450950aa1452407aa85512a65512ae5512ae451950950aa8407aa85512a65512ae5512ae450950950aa0407aa85502a75502af5502af450950950950406aa85502a65512ae5512ae4509519510a6406aa85502a65502ae5512ae45195195102e405aa85502a55522ad5522ad4529520ad952404aa85512a45522ac5532ac4539530ac22c407aa85532a05572a85572a84578a8aa8aa8407aa85532a05562a85572a84568a8aa8a20407aa85532a05562a85562a84578a8aa8a08407aa85522a05572a85572a84568a8aa88a0407aa85522a05562a95562a94568a8aa8850407aa85522a05562a85572a84578a8aa8828406aa95522a15562a85562a94568a8aa9512406aa95522a15562a85562a84568a9aa9506406aa95522a15562a85562a84568a8aa9502406aa95522a05562a95562a94568a8aa9452406aa95522a05562a85562a94568a9aa9416406aa95522a05562a85562a94568a8aa9412406aa95522a05562a85562a84568a9aa9406406aa85532a05562a85572a84578a8aa8228406aa85522a15562a85562a94568a8aa9112406aa85522a05572a85572a84578a8aa80a8406aa85522a05562a95562a94568a9aa8054406aa85522a05562a95562a94568a8aa9052406aa85522a05562a85562a94568a9aa9016407aa85532a05572a85572a84558a8aa0aa8407aa85532a05572a85572a84548a8aa0aa0406aa95522a15562a85562a94548a8aa1512406aa95522a15562a85562a84548a9aa1506406aa95522a05562a95562a94548a8aa1452406aa95522a05562a85562a94548a9aa1416406aa85522a15562a85562a94548a9aa1116406aa85522a05562a95562a94548a9aa1056407aa85532a05552a85572a84578a8a28aa8407aa85532a05552a85572a84568a8a28aa0407aa85532a05552a85562a84578a8a28a88406aa95522a15542a85562a84568a9a29506406aa95522a05542a85562a94568a9a29416406aa85522a15542a85562a94568a9a29116406aa85522a05542a95562a94568a9a29056407aa85512a25552aa5552aa4558a8950aa8407aa85512a25552aa5552aa4548a8950aa0407aa85512a25542aa5552aa4558a8950a28407aa85502a35542ab5542ab4548a8950950406aa85512a25542aa5552aa4558a895122a406aa85502a25552aa5552aa4558a89510aa407aa85512a05572a85572a84578a88a8aa8407aa85512a05572a85572a84568a88a8aa0407aa85512a05562a85572a84578a88a8a28407aa85502a15562a95562a94568a88a8950406aa95502a15562a85562a84568a98a9506406aa95502a05562a85562a94568a98a9416406aa85502a15562a85562a94568a98a9116406aa85502a05562a95562a94568a98a9056405aaa5512a25552a85552aa4558aa515aaa405aaa5512a25552a85552aa4548aa515aa2405aaa5512a25552a85552aa4548aa514aa0405aaa5512a25542a85552aa4558aa515a2a405aaa5512a25542a85552aa4548aa515a22405aaa5512a25542a85542aa4558aa515a0a405aaa5502a35542a95542ab4548aa514950405aaa5502a25552a85552aa4558aa5158aa405aaa5502a25552a85552aa4548aa5158a2405aaa5502a25542a85552aa4558aa51582a404aab5502a35542a95542aa4548ab514544404aaa5512a25542a85552aa4558aa51522a404aaa5502a25552a85552aa4558aa5150aa405aaa5512a05552aa5552aa4558aa455aaa405aaa5512a05552aa5552aa4548aa455aa2405aaa5512a05552aa5552aa4548aa454aa0405aaa5512a05542aa5552aa4558aa455a2a405aaa5512a05542aa5552aa4548aa455a22405aaa5512a05542aa5542aa4558aa455a0a405aaa5502a15542ab5542ab4548aa454950405aaa5502a15542aa5542aa4558aa45590a405aaa5502a05552aa5552aa4558aa4558aa405aaa5502a05552aa5552aa4548aa4558a2405aaa5502a05542aa5552aa4558aa45582a404aab5502a15542aa5542ab4548ab454514403aac5532a45532ac5532ac453553aacaac403aac5522a45522ad5522ad452552aac850403aac5522a45522ac5532ac452553aac824402aad5522a55522ac5522ad452552aad512402aad5522a55522ac5522ac452552aad502402aad5522a45522ad5522ad452552aad452402aad5522a45522ac5522ad452552aad412402aad5522a45522ac5522ac452552aad402402aac5522a45522ad5522ad452552aac050402aac5522a45522ac5532ac453553aac02c402aac5522a45522ac5532ac452553aac024402aac5522a45522ac5522ad452552aad012403aac5532a45532ac5532ac451553aa4aac403aac5532a45532ac5532ac450553aa4aa4403aac5522a55522ac5522ad450552aa4910403aac5522a45522ad5522ad450552aa4850403aac5522a45522ac5532ac450553aa4824402aad5522a55522ac5522ad450552aa5512402aad5522a55522ac5522ad450552aa4510402aad5522a55522ac5522ac450552aa5502402aad5522a45522ad5522ad450552aa5452402aad5522a45522ad5522ad450552aa4450402aad5522a45522ac5522ad450552aa5412402aac5522a55522ac5522ad450552aa5112402aac5522a45522ad5522ad450552aa5052402aac5522a45522ac5532ac451553aa402c403aac5512a45512ac5532ac45355382caac403aac5512a45512ac5532ac45255382caa4403aac5512a45512ac5522ac45355282ca88403aac5502a45512ac5522ac45355382c88c403aac5502a45502ac5532ac45355382c82c402aad5502a55502ac5522ad45255282d512402aad5502a45502ad5522ad45255282d452401aae5512a65512ae5512ae451551551aae401aae5512a65512ae5512ae450551551aa6400aaf5502a75502af5502af450550550550407aa055f2a055f2a055f2a02a0aa0aa0aa0406aa155e2a055e2a055e2a02a1aa1aa140e405aa255d2a055d2a055d2a22a2aa241daa2405aa255d2a055d2a055d2a22a2aa241caa0405aa255c2a055d2a055d2a22a2aa241d8a2404aa355c2a155c2a155c2a22a2aa341c544404aa355c2a055c2a155c2a22a3aa341c44c404aa355c2a055c2a055c2a32a3aa341c41c407aa055b2a455b2a455b2a42a4958aa0aa0406aa155a2a455a2a455a2a42a4959aa1406407aa05592a65592a65592a62a6958958aa0407aa05582a75582a75582a72a7958958958406aa15582a65582a65582a62a6959959406406aa05582a65592a65592a62a69589580a0406aa05582a65582a65592a62a6959959026406aa05582a65582a65592a62a6958959022406aa05582a65582a65582a72a7958958018407aa05592a455b2a455b2a42a49588a0aa0407aa05582a555a2a555a2a52a59588a0958407aa05592a45592a45592a62a6958818aa0407aa05582a55582a55582a72a7958818958405aa25592a45592a45592a62a6958419aa2405aa25592a45592a45592a62a6958418aa0405aa25582a55582a55582a72a7958418958405aa25582a55582a55582a62a6958419942405aa25582a45592a45592a62a69584198a2405aa055b2a455b2a455b2a42a495a2a4aa0405aa055a2a555a2a555a2a52a595a2a595a405aa055a2a455b2a455b2a42a495a2a48a0404aa055b2a455b2a455b2a42a495b2a42a4405aa05592a455b2a455b2a42a495a0a4aa0405aa05582a555a2a555a2a52a595a0a595a405aa05582a555a2a555a2a52a595a0a4958405aa05582a455a2a455a2a52a595a0a581a404aa15582a455a2a455a2a52a595a0a541a404aa05592a455b2a455b2a42a495b0a42a4403aa455b2a455b2a455b2a42a455baa4aa4403aa455a2a455a2a455a2a42a455baa4804402aa555a2a455a2a455a2a42a555aaa540a402aa555a2a455a2a455a2a42a455aaa5402402aa455a2a455a2a455b2a42a455baa4024402aa455a2a455a2a455a2a52a555aaa4018402aa455a2a455a2a455a2a42a555aaa500a403aa45582a75582a75582a72a7558958958402aa55582a65582a65582a62a6558959402402aa45582a65582a65582a72a7558958018403aa45592a45592a455b2a42a455b824aa4403aa45592a45592a45592a62a6559818aa4403aa45582a55582a55582a72a7558818958401aa65592a65592a65592a62a6559559aa6401aa65582a65582a65582a72a7558558818401aa65582a65582a65582a62a7558558808401aa65582a65582a65582a62a6559559806401aa65582a65582a65582a62a6558559802400aa75582a75582a75582a72a7558558558400aa75582a65582a65582a62a7558558408400aa65582a65582a65582a72a7558558018400aa65582a65582a65582a62a6559559006401aa65592a45592a45592a62a6559419aa6401aa65592a45592a45592a62a6559418aa4401aa65582a55582a55582a72a7558418958401aa65582a55582a55582a62a6558419942401aa65582a45582a45592a62a6559419826400aa75582a55582a55582a72a7558418558401aa455b2a455b2a455b2a42a455b2a4aa4401aa455a2a555a2a555a2a52a555a2a595a401aa455a2a455a2a455b2a42a455b2a4824401aa455a2a455a2a455a2a42a555a2a580a400aa555a2a555a2a555a2a52a555a2a555a400aa555a2a455a2a455a2a42a555a2a540a400aa455b2a455b2a455b2a42a455b2a42a4403aa455b2a055b2a455b2a42a445baa4aa4403aa455a2a155a2a455a2a42a445baa4904403aa455a2a055b2a455b2a42a445aaa48a0403aa455a2a055a2a455b2a42a445baa4824403aa455a2a055a2a455a2a52a545aaa4818402aa555a2a155a2a455a2a42a545aaa550a402aa555a2a055a2a455a2a52a545aaa541a402aa555a2a055a2a455a2a42a545aaa540a402aa455b2a055b2a455b2a42a445aaa42a0402aa455a2a055b2a455b2a42a445baa40a4402aa455a2a055a2a455a2a52a545aaa501a403aa45582a35582a75582a72a7458958958403aa45582a35582a65582a62a6459958904403aa45582a25582a65582a72a7458958818402aa45582a25592a65592a62a64589590a2402aa45582a25582a65592a62a6459959026401aa65592a25592a65592a62a6459559aa6401aa65582a35582a65582a62a6459558904401aa65582a25582a65592a62a6458559822401aa65582a25582a65582a72a7458558818400aa75582a35582a75582a72a7458558558400aa75582a35582a65582a62a7458558508400aa75582a25582a65582a72a7458558418400aa65592a25592a65592a62a64585592a2401aa65592a25592a45592a62a6459519aa6401aa65582a35582a55582a72a7458518958401aa65582a25582a45592a62a6459519826400aa75582a35582a55582a72a7458518558400aa75582a35582a55582a62a7458518548400aa65582a25592a45592a62a64595190a6401aa65592a05592a65592a62a6459459aa6401aa65582a15582a75582a72a7458458958401aa65582a15582a65582a62a6459459906400aa75582a15582a75582a72a7458458558400aa75582a15582a65582a72a7458458518400aa75582a05582a75582a72a7458458458400aa65582a05592a65592a62a64594590a6401aa455b2a055b2a455b2a42a445b2a4aa4401aa455a2a155a2a555a2a52a545a2a595a400aa555a2a155a2a555a2a52a545a2a555a400aa555a2a155a2a455a2a52a545a2a551a400aa555a2a155a2a455a2a42a545a2a550a400aa555a2a055a2a555a2a52a545a2a545a400aa555a2a055a2a455a2a52a545a2a541a400aa455b2a055b2a455b2a42a445b2a42a4407aa05572a85572a85572a8157aa8aa8aa8407aa05562a85562a85572a8156aa8aa8820406aa15562a85562a85562a8157aa8aa8408406aa15562a85562a85562a8156aa9aa9406406aa05562a85572a85572a8156aa8aa80a0406aa05562a85562a85572a8157aa8aa8028406aa05562a85562a85562a9156aa9aa9016406aa05562a85562a85562a9156aa8aa9012406aa05562a85562a85562a8156aa9aa9006407aa05552a85572a85572a8155aa88a0aa8407aa05552a85552a85572a8157aa8828aa8405aa25552a85552aa5552aa155aaa455aaa405aa25542a95542aa5542ab154aaa454910405aa25542a95542aa5542aa154aaa455902405aa25542a85552aa5552aa154aaa4558a2405aa25542a85552aa5552aa154aaa4548a0405aa25542a85542ab5542ab154aaa454850405aa25542a85542aa5552aa155aaa45582a405aa25542a85542aa5552aa155aaa454828405aa25542a85542aa5552aa154aaa455822404aa35542a95542aa5542ab154aab454514404aa35542a85542ab5542ab154aab454454404aa25542a85552aa5552aa154aaa4550a2404aa25542a85542aa5552aa155aaa45502a405aa25552a85552aa5552aa155aa8451aaa405aa25552a85552aa5552aa155aa8450aa8405aa25542a85552aa5552aa154aa84518a2405aa25542a85542aa5552aa155aa845182a404aa35542a95542aa5542ab154aa9450514404aa35542a85542ab5542ab154aa9450454405aa25552a85552a85552aa155aaa415aaa405aa25552a85552a85552aa155aaa414aa8405aa25542a95542a95542aa154aaa415942405aa25542a85552a85552aa154aaa4158a2405aa25542a85542a85552aa155aaa41582a404aa35542a95542a95542aa154aab414544404aa35542a85542a95542ab154aab414454405aa05572a85572a85572a8155aa82a0aa8404aa15562a85562a95562a9154aa92a1456404aa15562a85562a95562a9154aa92a0454404aa15562a85562a95562a9154aa82a1452404aa15562a85562a85562a9154aa92a1416405aa05552aa5552aa5552aa155aaa155aaa405aa05542aa5552aa5552aa154aaa1548a0405aa05542aa5542ab5542ab154aaa154850405aa05542aa5542aa5552aa155aaa15582a405aa05542aa5542aa5552aa154aaa155822404aa15542aa5542ab5542ab154aab154454404aa15542aa5542ab5542ab154aaa154450404aa15542aa5542aa5542ab154aab154414404aa15542aa5542aa5542aa155aaa15540a404aa05552aa5552aa5552aa154aaa1542a0404aa05542ab5542ab5542ab154aab154154404aa05542aa5542aa5552aa155aaa15502a405aa05552a85572a85572a8157aa80a8aa8404aa15542a85562a95562a9156aa90a9456404aa15542a85562a95562a9156aa90a8454404aa15542a85562a85562a9156aa90a9416404aa05542a95562a95562a9156aa90a9156404aa05542a95562a95562a9156aa90a8154405aa05552a85552aa5552aa155aaa055aaa405aa05552a85552aa5552aa155aaa054aa8405aa05542a85552aa5552aa154aaa0558a2405aa05542a85542aa5552aa155aaa05582a404aa15542a95542aa5542ab154aab054514404aa15542a85542ab5542ab154aab054454404aa05552a85552aa5552aa154aaa0552a2404aa05542a95542ab5542ab154aab054154404aa05542a85552aa5552aa155aaa0550aa407aa05572a85572a85572a8153aa0aa8aa8407aa05562a85572a85572a8152aa0aa88a0407aa05562a85562a85572a8153aa0aa8828406aa15562a85562a85562a9152aa1aa9416406aa15562a85562a85562a9152aa1aa8414406aa15562a85562a85562a8153aa1aa840c406aa15562a85562a85562a8152aa1aa9406406aa05572a85572a85572a8152aa0aa82a0406aa05562a95562a95562a9152aa0aa9152406aa05562a85572a85572a8153aa0aa80a8406aa05562a85562a95562a9152aa1aa9056406aa05562a85562a95562a9152aa1aa8054406aa05562a85562a95562a9152aa0aa9052406aa05562a85562a85562a9152aa1aa9016407aa05572a85572a85572a8151aa0aa0aa8405aa25552a85552aa5552aa151aa2455aaa405aa25552a85552aa5552aa151aa2454aa8405aa25552a85552aa5552aa150aa2454aa0405aa25542a85552aa5552aa150aa24558a2405aa25542a85542aa5552aa151aa245582a404aa35542a95542aa5542ab150aa3454514404aa35542a85542ab5542ab150aa3454454404aa25552a85552aa5552aa150aa24552a2404aa25542a85552aa5552aa151aa24550aa407aa05532ac5532ac5532ac153950aa8aa8407aa05522ac5532ac5532ac152950aa88a0407aa05522ac5522ad5522ad152950aa8850407aa05522ac5522ac5532ac153950aa8828406aa15522ac5522ad5522ad152950aa9452406aa15522ac5522ad5522ad152950aa8450406aa15522ac5522ac5522ad152950aa9412406aa15522ac5522ac5522ac153951aa840c406aa15522ac5522ac5522ac152951aa9406406aa05522ad5522ad5522ad152950aa9152406aa05522ac5532ac5532ac152951aa80a4406aa05522ac5522ad5522ad152950aa9052406aa05522ac5522ac5532ac153951aa802c407aa05532ac5532ac5532ac151950aa0aa8407aa05532ac5532ac5532ac150950aa0aa0406aa15522ac5522ad5522ad150950aa1452406aa15522ac5522ac5522ac151951aa140e407aa05512ae5512ae5512ae151950950aa8407aa05512ae5512ae5512ae150950950aa0407aa05502af5502af5502af150950950950406aa15502ae5502ae5502ae15195195140e406aa05502ae5512ae5512ae1509519510a6406aa05502ae5502ae5512ae15195195102e405aa05532ac5532ac5532ac1519522a4aa8405aa05532ac5532ac5532ac1509522a4aa0405aa05522ad5522ad5522ad1509522a5952405aa05522ad5522ad5522ad1509522a4950405aa05522ac5522ad5522ad1509522a5852404aa15522ac5522ad5522ad1509522a5452404aa05532ac5532ac5532ac1509532a42a4405aa05512ac5532ac5532ac1539520acaa8405aa05512ac5532ac5532ac1529520acaa0405aa05502ad5522ad5522ad1529520ad952405aa05502ad5522ad5522ad1529520ac950405aa05502ac5522ad5522ad1529520ad852404aa15502ac5522ad5522ad1529520ad452404aa05512ac5532ac5532ac1529530ac2a4404aa05512ac5522ac5532ac1539530ac22c404aa05502ad5522ad5522ad1529520ad152404aa05502ac5532ac5532ac1539530ac0ac407aa05532a85572a85572a81578a8aa8aa8407aa05532a85562a85562a81578a8aa8a08407aa05522a85572a85572a81568a8aa88a0407aa05522a85562a95562a91568a8aa8850407aa05522a85562a85572a81578a8aa8828406aa15522a85562a85562a91568a9aa9416406aa15522a85562a85562a91568a9aa8414406aa15522a85562a85562a81568a9aa9406406aa05532a85562a85572a81578a8aa8228406aa05522a95562a95562a91568a8aa9152406aa05522a85572a85572a81578a8aa80a8406aa05522a85562a95562a91568a9aa9056406aa05522a85562a95562a91568a9aa8054406aa05522a85562a95562a91568a8aa9052406aa05522a85562a85562a91568a9aa9016407aa05532a85552a85572a81578a8a28aa8407aa05532a85552a85562a81578a8a28a88406aa15522a85542a85562a91568a9a29416407aa05512aa5552aa5552aa1558a8950aa8407aa05512aa5542aa5552aa1558a8950a28407aa05502ab5542ab5542ab1548a8950950406aa05512aa5542aa5552aa1558a895122a406aa05502aa5552aa5552aa1558a89510aa407aa05512a85572a85572a81578a88a8aa8407aa05512a85572a85572a81568a88a8aa0407aa05512a85562a85572a81578a88a8a28407aa05502a95562a95562a91568a88a8950407aa05502a85572a85572a81578a88a88a8406aa15502a85562a85562a91568a98a9416406aa05502a85562a95562a91568a98a9056405aa25512a85552aa5552aa1558aa455aaa405aa25512a85552aa5552aa1558aa454aa8405aa25512a85542aa5552aa1558aa455a2a405aa25512a85542aa5552aa1558aa454a28405aa25512a85542aa5542aa1558aa455a0a405aa25502a95542ab5542ab1548aa454950405aa25502a85552aa5552aa1558aa4558aa405aa25502a85552aa5552aa1558aa4548a8405aa25502a85552aa5552aa1548aa4558a2405aa25502a85542aa5552aa1558aa45582a404aa35502a95542aa5542ab1548ab454514404aa35502a85542ab5542ab1548ab454454404aa25512a85542aa5552aa1558aa45522a404aa25502a85552aa5552aa1558aa4550aa403aa45532ac5532ac5532ac153553aacaac403aa45522ac5522ad5522ad152552aac850403aa45522ac5522ac5532ac152553aac824403aa45522ac5522ac5522ad152552aac810403aa45522ac5522ac5522ac153553aac80c403aa45522ac5522ac5522ac152553aac804402aa55522ac5522ad5522ad152552aad452402aa55522ac5522ad5522ad152552aac450402aa55522ac5522ac5522ad152552aad412402aa55522ac5522ac5522ad152552aac410402aa55522ac5522ac5522ac153552aac408402aa55522ac5522ac5522ac152552aad402402aa45522ad5522ad5522ad152552aad152402aa45522ac5532ac5532ac152553aac0a4402aa45522ac5522ad5522ad152552aad052402aa45522ac5522ad5522ad152552aac050402aa45522ac5522ac5532ac153553aac02c402aa45522ac5522ac5532ac152553aac024402aa45522ac5522ac5522ad152552aad012402aa45522ac5522ac5522ac153553aac00c403aa45532ac5532ac5532ac151553aa4aac403aa45532ac5532ac5532ac150553aa4aa4403aa45522ac5522ad5522ad150552aa4850403aa45522ac5522ac5532ac150553aa4824403aa45522ac5522ac5522ac151553aa480c402aa55522ac5522ad5522ad150552aa5452402aa55522ac5522ac5522ad150552aa5412402aa55522ac5522ac5522ac151552aa540a402aa45522ad5522ad5522ad150552aa4150402aa45522ac5532ac5532ac150553aa40a4402aa45522ac5522ad5522ad150552aa5052402aa45522ac5522ac5532ac151553aa402c403aa45512ae5512ae5512ae151551950aac403aa45512ae5512ae5512ae150551950aa4403aa45502af5502af5502af150550950950402aa45502ae5512ae5512ae1505519510a6402aa45502ae5502ae5512ae15155195102e403aa45512ac5532ac5532ac1535538acaac403aa45512ac5522ac5532ac1535538aca2c403aa45512ac5522ac5522ac1535528aca08403aa45502ad5522ad5522ad1525528ac950403aa45502ac5532ac5532ac1535538ac8ac403aa45502ac5522ad5522ad1525528ac850403aa45502ac5522ac5532ac1525538ac824403aa45502ac5522ac5522ac1535538ac80c402aa55502ac5522ad5522ad1525528ad452402aa55502ac5522ac5522ad1525528ad412402aa45512ac5522ac5522ac1535538ac20c402aa45502ac5532ac5532ac1525538ac0a4402aa45502ac5522ad5522ad1525528ad052402aa45502ac5522ac5532ac1535538ac02c403aa45512ac5532ac5532ac1515538a4aac403aa45512ac5532ac5532ac1505538a4aa4403aa45512ac5522ac5532ac1505538a4a24403aa45502ad5522ad5522ad1505528a4950403aa45502ac5532ac5532ac1515538a48ac403aa45502ac5532ac5532ac1505538a48a4402aa55502ac5522ad5522ad1505528a5452402aa45502ad5522ad5522ad1505528a5152403aa45512ac5512ac5532ac15355382caac403aa45512ac5512ac5532ac15255382caa4403aa45512ac5512ac5522ac15355382ca8c403aa45512ac5512ac5522ac15355282ca88403aa45512ac5512ac5522ac15255382ca84403aa45502ad5502ad5522ad15255282c950403aa45502ac5512ac5532ac15355382c8ac403aa45502ac5512ac5532ac15255382c8a4403aa45502ac5512ac5522ac15355382c88c403aa45502ac5502ac5532ac15355382c82c402aa55502ac5502ad5522ad15255282d452402aa45502ad5502ad5522ad15255282d152401aa65512ae5512ae5512ae151551551aae401aa65512ae5512ae5512ae150551551aa6401aa65502af5502af5502af150550550950401aa65502ae5512ae5512ae1515515518ae401aa65502ae5512ae5512ae1505515518a6401aa65502ae5502ae5512ae15155155182e401aa65502ae5502ae5512ae150551551826401aa65502ae5502ae5502ae15155155180e400aa75502af5502af5502af150550550550401aa45532ac5532ac5532ac1515532a4aac401aa45532ac5532ac5532ac1505532a4aa4401aa45522ad5522ad5522ad1505522a5952401aa45522ac5522ac5532ac1515532a482c400aa55522ad5522ad5522ad1505522a5552400aa55522ad5522ad5522ad1505522a4550400aa55522ac5522ad5522ad1505522a5452400aa45532ac5532ac5532ac1505532a42a4403aa05572a85572a85572a81572a8aa8aa8403aa05562a85572a85572a81562a8aa88a0403aa05562a85562a85572a81572a8aa8828403aa05562a85562a85562a91562a9aa8814402aa15562a85562a85562a91562a9aa9416402aa15562a85562a85562a91562a9aa8414402aa15562a85562a85562a81562a9aa9406402aa05572a85572a85572a81562a8aa82a0402aa05562a85572a85572a81572a8aa80a8402aa05562a85562a95562a91562a9aa9056402aa05562a85562a95562a91562a9aa8054402aa05562a85562a85562a91562a9aa9016403aa05572a85572a85572a81552a8aa0aa8403aa05572a85572a85572a81542a8aa0aa0402aa15562a85562a85562a91542a9aa1416403aa05552aa5552aa5552aa1552aa954aa8403aa05552aa5552aa5552aa1542aa954aa0403aa05542ab5542ab5542ab1542ab954954403aa05542aa5552aa5552aa1542aa9548a0403aa05542aa5542aa5552aa1552aa954828403aa05542aa5542aa5542ab1542ab954814402aa15542aa5542aa5542ab1542ab954414402aa15542aa5542aa5542aa1552aa95540a402aa05552aa5552aa5552aa1542aa9552a2402aa05552aa5552aa5552aa1542aa9542a0402aa05542aa5552aa5552aa1552aa9550aa402aa05542aa5552aa5552aa1552aa9540a8402aa05542aa5552aa5552aa1542aa9550a2402aa05542aa5542ab5542ab1542ab954054402aa05542aa5542aa5552aa1552aa95502a403aa05552a85572a85572a81572a88a8aa8403aa05552a85562a85572a81572a88a8a28403aa05542a95562a95562a91562a98a8954403aa05542a85572a85572a81572a88a88a8402aa15542a85562a85562a91562a98a9416403aa05542a95542ab5542ab1542ab854954403aa05542a85552aa5552aa1552aa8548a8403aa05542a85542ab5542ab1542ab854854401aa25552aa5552aa5552aa1552aa555aaa401aa25552aa5552aa5552aa1542aa555aa2401aa25542ab5542ab5542ab1542ab554954401aa25542aa5552aa5552aa1552aa5558aa401aa25542aa5542aa5552aa1542aa555822401aa25542aa5542aa5542ab1542ab554814401aa25542aa5542aa5542aa1552aa55580a400aa35542ab5542ab5542ab1542ab554554400aa35542aa5542aa5542ab1542ab554414400aa25552aa5552aa5552aa1542aa5552a2400aa25542aa5552aa5552aa1542aa5550a2400aa25542aa5542ab5542ab1542ab554054400aa25542aa5542aa5552aa1552aa55502a401aa25552a85552aa5552aa1552aa455aaa401aa25552a85552aa5552aa1552aa454aa8401aa25552a85552aa5552aa1542aa455aa2401aa25552a85552aa5552aa1542aa454aa0401aa25542a95542ab5542ab1542ab454954401aa25542a95542aa5542ab1542ab454914401aa25542a85552aa5552aa1552aa4558aa401aa25542a85552aa5552aa1552aa4548a8401aa25542a85552aa5552aa1542aa4558a2401aa25542a85542ab5542ab1542ab454854401aa25542a85542aa5552aa1552aa45582a400aa35542a95542ab5542ab1542ab454554400aa35542a95542aa5542ab1542ab454514400aa35542a85542ab5542ab1542ab454454400aa25552a85552aa5552aa1542aa4552a2400aa25542a85552aa5552aa1552aa4550aa401aa05572a85572a85572a81572a82a8aa8401aa05572a85572a85572a81562a82a8aa0401aa05562a95562a95562a91562a92a9956401aa05562a85572a85572a81572a82a88a8401aa05562a85562a95562a91562a92a9856400aa15562a95562a95562a91562a92a9556400aa15562a85562a95562a91562a92a9456400aa15562a85562a85562a91562a92a9416400aa05572a85572a85572a81572a82a82a8401aa05552aa5552aa5552aa1552aa155aaa401aa05552aa5552aa5552aa1542aa155aa2401aa05552aa5552aa5552aa1542aa154aa0401aa05542ab5542ab5542ab1542ab154954401aa05542aa5552aa5552aa1552aa1558aa401aa05542aa5552aa5552aa1542aa1558a2401aa05542aa5542ab5542ab1542ab154854401aa05542aa5542aa5552aa1552aa15582a400aa15542ab5542ab5542ab1542ab154554400aa15542aa5542ab5542ab1542ab154454400aa05552aa5552aa5552aa1552aa1552aa400aa05552aa5552aa5552aa1542aa1552a2400aa05542ab5542ab5542ab1542ab154154400aa05542aa5552aa5552aa1552aa1550aa

def B12_0 : List (ℕ × ℕ × ℕ) := [(0x802a82aa2aaaa8aaaaa2aa2a8aa8aa, 48, 0x2ea61d950c8400d02ea61d95048c00c02ea61d950c8400c02ea61d950c8400b02e96259d0c8400902e96259d048c00802e96259d0c8400802e9e25950c8400902e9e2595048c00802e9e25950c8400802e9e15a50c8400602ea61d950c8400a02ea49e158d0400702ea51e158c8400702ea59e150c8400702ea61d950c8400902ea61d95048c00802ea61d950c8400802ea6159d0c8400602ea61d950c8400702ea61d950c8400602ea61d950c8400502ea49e158d0400402ea51e158c8400402ea59e150c8400402ea61d950c8400402ea61d950c8400302ea61d95048c00202ea61d950c8400202e96259d0c8400002e9e25950c8400002ea61d950c8400102ea61d950c84000),
  (0x802a82ab2a8aacaa2ab2a82acaa154, 48, 0x2ea61d950c8401602ea61d950c8401502e96259d0c8401302e9e25950c8401302ea61d950c8401402ea45e158d0801202ea49e158d0401202c20da51c94680702ea51e158c8401202c20da49d14680702c20da45d14a80702ea59e150c8401202c20d249d94680702c20d245d94a80702c20ca45d95280702ea61d950c8401302ea61d950c8401202c18d249e14680702c18d245e14a80702c18ca45e15280702c10ca45e15a80702ea61d950c8401102ea45e158d0801002ea49e158d0401002ea49c560d9000f02ea51e158c8401002ea51c560d8800f02ea51c960d8400f02ea59e150c8401002ea59c560d0800f02ea59c960d0400f02ea59d160c8400f02ea61d950c8401002ea61c558d0800f02ea61c958d0400f02ea61d158c8400f02ea61d950c8400f02ea61d950c8400e02ea59d148c4200302ea61d95008c40202ea61d95004c80202ea61d94804d00202ea61d14804d80202ea59d14804e002),
  (0x802a8aaa2a8aa8aaaaa2aa2a8aaa2a, 48, 0x2ea61d950c8402602ea61d950c8402502ea61d950c8402402ea61d950c8402302e96259d0c8402002e96259d0c8401f02e96259d0c8401e02e9e25950c8402002e9e25950c8401f02e9e25950c8401e02e9e15a50c8401c02ea61d950c8402202ea61c958d0402102ea61d158c8402102ea61d950c8402102ea61d950c8402002ea61d950c8401f02ea61d950c8401e02ea6159d0c8401c02ea61d950c8401d02ea61d950c8401c02ea61d950c8401b02ea61c958d0401a02ea61d158c8401a02ea61d950c8401a02ea61d950c8401902ea61d950c8041002ea61c158d0840f02ea61d950c8401802e96259d0c8401702e9e25950c8401702ea61d950c8040402ea61d950c84017),
  (0x802a8aaa2aaaa8aaaaa2aa2a8aaaaa, 50, 0x2ea61d950c8403302e86259d0c9403002ea61d950c8403202c261d950c8680c02e96259d0c8403002c0e259d148680902c261d850c9680c02e9605a50c9c02f02e9e25950c8403002c0e25951c8680902c2615850c9e80c02e9e05a50c9402f02c0e25851c9680902e9e15850ca402d02e9e15a50c8402f02ea61d950c8403102c20da51c94681202c20da49d14681202ea51c960d8402e02c20d249d94681202ea59c960d0402e02ea59d160c8402e02ea61d950c8403002c0e1d95248680902c1e15850ca680c02ea6059d0c9402f02c0e1d85249680902ea615850c9c02d02ea6159d0c8402f02c18d249e14681202ea61c958d0402e02ea61d158c8402e02c0e1585249e80902ea61d850c9402d02ea61d950c8402f02ea61d950c8402e02ea61d950c8402d02ea61d950c8402c02e9c96058d0241b02e9d16058c8241b02ea51c960d8402b02e9d96050c8241b02ea59c960d0402b02ea59d160c8402b02e9e15850c8241b02ea61c958d0402b02ea61d158c8402b02ea61d950c8402b02e9e15850c8241102ea41e158d0841002ea61d950c8402a02e86259d0c9402902ea41e058d0941002e9605a50c9c02702e96259d0c8402902ea416058d09c1002e9e05a50c9402702e9e25950c8402902e9e15a50c8402702e9e15850c8240502ea49e158d0402802ea51e158c8402802ea59e150c8402802e9c16058d0a41002ea6059d0c9402702ea61d950c8402902ea6159d0c8402702ea61d950c8402802ea61d950c84027)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_0 : blocksOK 11 56 P11 P12 955 0 B12_0 = true := by decide +kernel

def B12_1 : List (ℕ × ℕ × ℕ) := [(0x806a82aa2a8aa8aaaaa2aa2a8aac2a, 48, 0x2c58d249e16803602c58d249e16803402e96259d0c8403502e9e25950c8403502ea61d950c8403602c48da51e16803502c50da49e16803502c58d249e16803502ea61d950c8403502ea61d950c8403402c58d249e14281202ea49e158d0042102ea51e158c8042102ea59e150c8042102ea61d950c8041d02ea61d950c8041202c58d249e14280702c58d249e14281d02c5950ca61c282102c59d0ca614282102ea61d950c8040702c5a50c9e142821),
  (0x806a82aa2a8aacaa2ab2a82acaa454, 48, 0x2ea61d950c8403b02c4e1d9524a803802ea6159d0c8403a02ea61d950c8403a02ea61d950c8403902ea49e158d0043502ea51e158c8043502ea59e150c8043502ea61d950c8403802ea61d950c8043502c4e1d95248283002c4e1d95248280902c4c9e15a50282002ea49e158d0041f02c4d1e15a48282002ea51e158c8041f02ea51c960d8403702c4d9e15248282002ea59e150c8041f02ea59c960d0403702ea59d160c8403702c4e1d95248282002ea61d950c8041f02ea61c958d0403702ea61d158c8403702ea61d950c8403702ea61d950c8041302ea61d950c8040902ea61d95008c40802c4c9e15a50281f02c4d1e15a48281f02c4d9e15248281f02c4e1d95248281f),
  (0x806a82aa2aaaa8aaaaa2aa2a8aacaa, 50, 0x2ea61d950c8404a02ea61d950c8404902e96259d0c8043902e96259d0c8404702e9e25950c8043902e9e25950c8404702e9e15a50c8404602ea61d950c8404802ea49e158d0043602ea51e158c8043602ea51c960d8404502ea59e150c8043602ea59c960d0404502ea59d160c8404502ea61d950c8043902ea61d950c8404702ea6159d0c8404602ea61d950c8043602ea61c958d0404502ea61d158c8404502ea61d950c8404602ea61d950c8404502ea61d950c8043102ea49e158d0042202ea51e158c8042202ea51c960d8404402ea59e150c8042202ea59c960d0404402ea59d160c8404402ea61d950c8042202ea61c958d0404402ea61d158c8404402ea61d950c8404402ea61d950c8404302ea61d950c8041402ea41e158d0841202ea61d950c8404202ea61d950c8404102e96259d0c8404002e96259d0c8403f02e96259d0c8403e02e9e25950c8404002e9e25950c8403f02e9e25950c8403e02e9e15a50c8403c02ea61d950c8040a02ea49e158d0403d02ea51e158c8403d02ea59e150c8403d02ea61d950c8404002ea61d950c8403f02ea61d950c8403e02ea6159d0c8403c02ea61d950c8403d02ea61d950c8403c),
  (0x806a82ab2a8aacaa2ab2a82a8aa550, 48, 0x2ea61d950c8404d02ea61d950c8404c02c0e259d148683802c0e25951c8683802c661d950c8284902c20da51c94683402c20da49d14683402c20d249d94683402c0e1d95248683802c18d249e14683402c661d950c8283202c661d950c8280c02c649e158d0282402ea49e158d0042302c651e158c8282402ea51e158c8042302ea51c960d8404b02c659e150c8282402ea59e150c8042302ea59c960d0404b02ea59d160c8404b02c661d950c8282402ea61d950c8042302ea61c958d0404b02ea61d158c8404b02ea61d950c8404b02c661d950c8281502ea61d950c8040c02c661d950c8280b02c649e158d0282302c651e158c8282302c659e150c8282302c661d950c82823),
  (0x806a82ab2a8aacaa2ab2a82acaa554, 50, 0x2ea61d950c8405902ea61d950c8044d02e96259d0c8043b02e96259d0c8405802e9e25950c8043b02e9e25950c8405802e9e15a50c8405702ea61d950c8044a02c20da51c96843602c20da49d16843602ea51c960d8405602c20d249d96843602ea59c960d0405602ea59d160c8405602ea61d950c8043b02ea61d950c8405802ea6159d0c8405702c18d249e16843602ea61c958d0405602ea61d158c8405602ea61d950c8405702ea61d950c8405602ea61d950c8043302c4e259d009683002ea49e158d0042602ea49e158d0042502ea51e158c8042602ea51e158c8042502ea51c960d8405502ea51c960d8405402ea59e150c8042602ea59e150c8042502ea59c960d0405502ea59c960d0405402ea59d160c8405502ea59d160c8405402ea59d148e0405302ea61d950c8042602ea61d950c8042502ea61c958d0405502ea61c958d0405402ea61d158c8405502ea61d158c8405402ea61d148d8405302ea61d950c8405502ea61d950c8405402ea61d948d0405302ea61d950c8405302ea61d950c8041602ea61d950c8405202e96259d0c8405102e9e25950c8405102ea61d950c8040d02ea61d95008c40c02ea49e158d0405002ea49e158d0404f02ea51e158c8405002ea51e158c8404f02ea51c960d8404e02ea59e150c8405002ea59e150c8404f02ea59c960d0404e02ea59d160c8404e02ea61d950c8405102ea61d950c8405002ea61d950c8404f02ea61c958d0404e02ea61d158c8404e02ea61d950c8404e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_1 : blocksOK 11 56 P11 P12 955 4 B12_1 = true := by decide +kernel

def B12_2 : List (ℕ × ℕ × ℕ) := [(0x802a92a92acaa4ab2a92ac2a154952, 48, 0x2ea61d950c8406102c245e15890e82502ea61d950c8406002c245e158928c4f02c245e09950e82502e9609a50dc405e02c245e099528c4f02c2456099d0e82502e9e09a50d4405e02c2456099d28c4f02e9e15a50c8405e02ea61d950c8405f02c2259d144a8c4102c0661d950a8c3f02c0661d158a8c3f02c1c5609a50e82502ea6099d0d4405e02c1c5609a528c4f02ea6159d0c8405e02c0659d160a8c3f02ea61d950c8405e02ea61d950c8405d02ea61d950c8405c02ea51e158c8405b02ea59e150c8405b02ea61d950c8405b02ea61d950c0842a02ea41e158d0841802ea61d950c8405a02ea41e098d1441802ea416098d1c41802ea45e158108c2802e9c16098d24418),
  (0x802a9aa82aeaa0abaa82ae2a1542a8, 48, 0x2ea61d950c8406a02e86259d0d4806702e8a259d0d4406702e8a05a50dd406502ea61d950c8406902e86259d0d4806602e8a259d0d4406602e8a05a50dd406402e96259d0c8406702e9605a50dc806502e9609a50dc406502e9609850e5c06302e96259d0c8406602e9605a50dc806402e9609a50dc406402e9e25950c8406702e9e05a50d4806502e9e09a50d4406502e9e09850e5406302e9e25950c8406602e9e05a50d4806402e9e09a50d4406402e9e15a50c8406502e9e15850e4806302e9e15890e4406302e9e15a50c8406402ea61d950c8406802ea61d950c8406702ea6059d0d4806502ea6099d0d4406502ea609850dd406302ea61d950c8406602ea6059d0d4806402ea6099d0d4406402ea6159d0c8406502ea615850dc806302ea615890dc406302ea6159d0c8406402ea61d950c8406502ea61d850d4806302ea61d890d4406302ea61d950c8406402ea61d950c8406302ea61d950c8406202e9e15890c0642c02e9c16098d0641b02e9c16058d0a41b02ea41e158d0481902e9e15890c4245d02ea61d950c8045c02ea61d950c4085c02e9c0a058d1641b02ea41e098d0541902ea41e058d0941902ea61d890c4145c02e940a058d1e41b02ea416098d05c1902ea416058d09c1902ea615890c41c5c02ea40a058d15c1902e940a058d25c1b02e9c16098d0641902e9c16058d0a41902e9e15890c4245c02e9c0a058d1641902e940a058d1e419),
  (0x806a92a82acaa0ab2a92ac2a554c16, 48, 0x2ea61d950c8407602ea61d890d4407402ea61d950c8407502ea61d890d4407202ea61d950c8407402ea61d950c8407302ea61d950c8407202e9e25950c8407002e9e25890d4406e02e9e25950c8406f02e9e25950c8406e02ea61d950c8407102ea61d950c8407002ea61d890d4406e02ea61d950c8406f02ea61d950c8406e02ea61d950c8406d02ea61d950c8046502ea61d810d4846302ea51e158c8406c02ea59e150c8406c02ea61d950c8406c02c4e1589241e80902ea41e158d0841c02ea61d950c8045e02ea41e098d1441c02ea416098d1c41f02ea61d950c8406b02e9c16098d2441f),
  (0x806a92a82acaa4ab2a92ac2a154c52, 48, 0x2ea61d950c8407e02c0e259d094687002ea61d950c8407d02ea6099d0d4407c02c0e259d148687002e9609a50dc047202ea6159d0c8407c02c0e25951c8687002e9e09a50d4047202ea61d950c8407c02e9e15a50c8047202ea61d950c8407b02ea61d950c8407a02ea6099d0d4046f02ea61d950c8407902ea6159d0c8046f02ea61d950c8046f02ea61d950c8046602ea6019d0d4846402ea51e158c8407802ea59e150c8407802ea61d950c8407802c5e15890c2680c02ea41e158d0841e02c5c1609a528c4f02ea41e098d1441e02ea416098d1c41e02ea61d950c8407702e9c16098d24423)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_2 : blocksOK 11 56 P11 P12 955 9 B12_2 = true := by decide +kernel

def B12_3 : List (ℕ × ℕ × ℕ) := [(0x806a92a82acaa4ab2a92ac2a554c56, 50, 0x2ea61d950c8408c02ea6099d0d4408b02c4e1d9524a808802c4e099d254287002ea6159d0c8408b02e9609a50dc047402c4e159d248287002c4e158925e808502ea61d950c8408b02e9e09a50d4047402c4e1d95248287002c4e1d89256808502c5e158d248287402ea61d950c8408a02c4e1d9524a808502ea61d950c8408902ea51e158c8408702ea59e150c8408702ea61d950c8408802ea6099d0d4047002c4e1d95248287a02ea6099d0d4408602ea6159d0c8047002ea615890dc408502ea6159d0c8408602ea61d950c8408702ea61d950c8047002ea61d890d4408502ea61d950c8408602ea61d950c8408502c4e1d95248286702ea6019d0d4846502ea51e158c8408402c4d1e15a4a808002ea59e150c8408402c4d9e1524a808002ea59d160c8408302ea61d950c8408402c4e1d9524a808002ea61d158c8408302ea61d950c8408302c4e1d95240a83002ea41e158d0842002c5c1609a50e82502c4e099d256807f02c4c1e09a51682002ea615890dc408202c4e159d24a807f02c4c1609a51e82002ea61d890d4408202c4e1d9524a807f02ea61d950c8408202c4e019d254a86502ea61d950084c7702ea51e158c8408002ea59e150c8408002e9c16098d2442502ea6099d0d4407f02ea61d950c8408102ea6159d0c8407f02ea61d950c8408002ea61d950c8407f),
  (0x806a92a82aeaa0abaa82ae2a1544a8, 48, 0x2ea61d950c8409102e8a259d0d4048902ea61d950c8409002e8a259d0d4047b02e96259d0c8048902e9609a50dc047102e96259d0c8047b02e9e25950c8048902e9e09a50d4047102e9e25950c8047b02e9e15a50c8047102ea61d950c8408f02ea61d950c8048902ea6099d0d4047102ea61d950c8047b02ea6159d0c8047102ea61d950c8047102ea61d950c8046802ea61d950c0843102c60da51c14a81202ea41e158d0842202ea41e158d0841d02ea61d950c8045f02c6259d140a8c4102e8a259d0d4408e02ea41e098d1442202ea41e098d1441d02e9609a50dc408d02e96259d0c8408e02ea416098d1c42202ea416098d1c41d02e9e09a50d4408d02e9e25950c8408e02e9e15a50c8408d02e9c16098d2442202e9c16098d2441d02ea6099d0d4408d02ea61d950c8408e02ea6159d0c8408d02ea61d950c8408d),
  (0x806a92a92acaa4ab2a92ac2a154d52, 50, 0x2ea61d950c8409d02c0e259d094688802ea61d950c8409c02c4a259d0d4287d02c0e259d148688802c5609a50dc287502c56259d0c8287d02e9609a50dc409a02c0e25951c8688802c5e09a50d4287502c5e25950c8287d02e9e09a50d4409a02c5e15a50c8287502e9e15890e4409902e9e15a50c8409a02c661d950c8289002ea51e158c8409b02ea59e150c8409b02c0e1d95248688802c66099d0d4287502c661d950c8287d02ea6099d0d4409a02c66159d0c8287502ea615890dc409902ea6159d0c8409a02ea61d950c8409b02c661d950c8287502ea61d890d4409902ea61d950c8409a02ea61d950c8409902c661d950c8286902e82259d0d4846602ea51e158c8409802c651e158ca809302ea59e150c8409802c659e150ca809302ea59d160c8409702ea61d950c8409802c661d950ca809302ea61d158c8409702ea61d950c8409702ea61d950c8409602c661d950c0a83202c641e158d0a82402c661d950c8286002e8a259d0d4409402c641e098d1682402e9609a50dc409202e96259d0c8409402c6416098d1e82402e9e09a50d4409202e9e25950c8409402e9e15a50c8409202c42259d0d4a86602ea61d950c8409502ea51e158c8409302ea59e150c8409302c5c16098d2682402ea6099d0d4409202ea61d950c8409402ea6159d0c8409202ea61d950c8409302ea61d950c84092)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_3 : blocksOK 11 56 P11 P12 955 13 B12_3 = true := by decide +kernel

def B12_4 : List (ℕ × ℕ × ℕ) := [(0x806a92a92acaa4ab2a92ac2a554d56, 52, 0x2ea61d950c840b102e8a259d0d4048c02ea61d950c8049d02e8a259d0d4047e02e96259d0c8048c02e9609a50dc047602e96259d0c8047e02e9609a50dc40af02e9e25950c8048c02e9e09a50d4047602e9e25950c8047e02e9e09a50d440af02e9e15a50c8047602e9e15890e440ad02e9e15a50c840af02e9e15890e440ac02ea61d950c8049102ea51e158c840b002ea59e150c840b002ea59d160c840ae02ea61d950c8048c02ea6099d0d4047602ea61d950c8047e02ea6099d0d440af02ea6159d0c8047602ea615890dc40ad02ea6159d0c840af02ea615890dc40ac02ea61d950c840b002ea61d158c840ae02ea61d950c8047602ea61d890d440ad02ea61d950c840af02ea61d890d440ac02ea61d950c840ae02ea61d950c840ad000e259d16886c2d02ea61d950c840ac02ea61d950c8046a02c4e259d014a86702ea51e158c840ab02ea51e158c840aa02ea59e150c840ab02ea59e150c840aa02ea59d160c840a902ea59d160c840a802ea61d950c840ab02ea61d950c840aa02ea61d158c840a902ea61d158c840a802ea61d950c840a902ea61d950c840a802ea61d950c840a702ea61d950c840a602ea61d950c0843302ea41e158d0842602ea61d950c8046102e8a259d0d440a402ea41e098d1442602e9609a50dc40a102e96259d0c840a402e9609a50dc40a002ea416098d1c42602e9e09a50d440a102e9e25950c840a402e9e09a50d440a002e9e15a50c840a102e9e15890e4409e02e9e15a50c840a002ea61d950c840a502c4e259d014a86602ea51e158c840a302ea51e158c840a202ea59e150c840a302ea59e150c840a202ea59d160c8409f02e9c16098d2442602ea6099d0d440a102ea61d950c840a402ea6099d0d440a002ea6159d0c840a102ea615890dc409e02ea6159d0c840a002ea61d950c840a302ea61d950c840a202ea61d158c8409f02ea61d950c840a102ea61d890d4409e02ea61d950c840a002ea61d950c8409f02ea61d950c8409e),
  (0x80aa8aa82a8aa8aaaaa2aa2aa2aa2a, 48, 0x2ea61d950c840bf02ea61d950c840be02c8e1d9526840b902c8e1d9526840b802ea6159d0c840bd02ea6159d0c840bc02c8e159d26840b602ea61d950c840bd02ea61d950c840bc02c8e1d9526840b602ea61d950c840bb02ea61d950c840ba02ea61d950c840b902ea61d950c840b802ea61d950c840b702ea6159d0c840b602ea61d950c840b602ea61d950c0848402ea6019d0d4846c02ea61d158c840b502ea61d950c840b502ea61d950c840b402c8e1d95240682002ea61c158d0843702c8e1d9526840b202ea6159d0c840b302ea61d950c840b302c8e019d256846c02ea61d950c840b2),
  (0x80ea82a82a8aacaa2ab2a82ae2a454, 48, 0x2ea61d950c840c602ea61d950c840c502ea6159d0c840c402ea61d950c840c402ea61d950c840c302ea61d950c840c202ea61d950c0488802ea6019d0d4487002ea6019d0d4847002ea6019d0d4486d02ea51e158c408b902ea51e158c804b802ea51e158c408b802ea59e150c408b902ea59e150c804b802ea59e150c408b802ea59d160c840c102ea61d950c408b902ea61d950c804b802ea61d950c408b802ea61d158c840c102ea61d950c840c102ea61d950c0483802c4e019d256887502c820d9d256846f02c420d9d256886f02ea51e158c840c002ea59e150c840c002ea61d950c840c0),
  (0x80ea82a82aaaa8aaaaa2aa2aa2a4a8, 48, 0x2ea61d950c840cb02c8e1d9526804c302ea6159d0c840ca02ea61d950c840ca02ea61d950c840c902ea61d950c804c302ea61d950c0848902ea6019d0d4847102ea51e158c804ba02ea59e150c804ba02ea61d950c804ba02ea61d950c0843902ea41e158d0483502c8e1d9526840c702ea6159d0c840c802ea61d950c840c802c8e019d256847102ea61d950c840c7)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_4 : blocksOK 11 56 P11 P12 955 16 B12_4 = true := by decide +kernel

def B12_5 : List (ℕ × ℕ × ℕ) := [(0x80ea82a92a8aa8aa2ab2a82ae2a514, 48, 0x2ea61d950c840ce02c4e25951e808c402ea61d950c840cd02e9e25950c408c402e9e25950c408ca02ea61d950c804c402c9e0d95240688b02c9e018d254687402c66018d1d4a87402e821da50d4486e02c9d0e15a4428bd02ea51e158c804bc02e9d26158c408bc02c9d8e1524428bd02ea59e150c804bc02e9da6150c408bc02ea59d160c840cc02c9e0d9524428bd02ea61d950c804bc02e9e25950c408bc02ea61d158c840cc02ea61d950c840cc02e9e25950c0483a02c4e01a51d6887402c821d8d254686e02c42258d1d4a86e02c9d0e15a4428bc02c9d8e1524428bc02c9e0d9524428bc),
  (0x80ea82a92a8aacaa2ab2a82ae2a554, 50, 0x2ea61d950c840dd02c8e1d9526804c602ea6159d0c804ce02c8e159d26840d902ea61d950c804ce02c8e1d9526840d902ea61d950c840dc02ea61d950c804cb02ea51e158c840da02ea59e150c840da02ea61d950c804c602ea61d950c840db02ea6159d0c840d902ea61d950c840da02ea61d950c840d902ea61d950c0848c02c660d9d014a88b02ea6019d0d4847602e82259d0d4847002ea51e158c804bf02ea51e158c804be02c8d1e15a6840d202c8d1e15a6840d102ea59e150c804bf02ea59e150c804be02c8d9e1526840d202c8d9e1526840d102ea59d160c840d802ea59d160c840d702c8d9d1626840cf02ea61d950c804bf02ea61d950c804be02c8e1d9526840d202c8e1d9526840d102ea61d158c840d802ea61d158c840d702c8e1d15a6840cf02ea61d950c840d802ea61d950c840d702c8e1d9526840cf02ea61d950c840d602ea61d950c0843b02c8e1d9526840d302ea6159d0c840d502ea61d950c840d502c8e019d256847602c820d9d256847002ea61d950c840d402c660d9d014a87c02ea51e158c840d202ea51e158c840d102ea51e158c840d002ea59e150c840d202ea59e150c840d102ea59e150c840d002ea59d160c840cf02ea61d950c840d302ea61d950c840d202ea61d950c840d102ea61d950c840d002ea61d158c840cf02ea61d950c840cf),
  (0x80aa82a82acaa4ab2a92ac2a654856, 48, 0x2ea61d950c840e702ea61d950c840e602e96259d0c084c802e9e25950c084c802ea61d950c840e502ea61d950c840e402ea51e158c840e302ea59e150c840e302ea61d950c084c702ea61d950c840e302e9c56018d2482202ea6019d0d4848d02ea51e158c840e202ea59e150c840e202ea61d950c840e202ea61d950c0844002ca258d1c14682102ea61d950c840e102ea6159d0c840e002ea61d950c840e002ea61d950c840df02ea61d950c840de),
  (0x80aa82a92acaa4ab2a92ac2a254952, 48, 0x2ea61d950c840ee02ea61d950c840ed02c0e259d16884c702c0e25951e884c702ea61d950c840ec02ea61d950c840eb02ea51e158c840ea02ea59e150c840ea02c0e1d9526884c702ea61d950c840ea02ea61d950c0485f02e82259d0d4848e02ea51e158c840e902ea59e150c840e902ea61d950c840e902ea61d950c0844202ca0da51c14681d02ea61d950c840e802e96259d0c804e102e9e25950c804e102ea45e158108c3d02ea61d950c804e1),
  (0x80ea82a82aeaa0abaa82ae2a2544a8, 48, 0x2ea61d950c840f402ea61d950c840f302e96259d0c048c902e9e25950c048c902ea61d950c840f202ea61d950c048c902ea61d950c0488f02ea61d950c840f102ea61d950c0484802ea41e158d0483602ea41e158d0843602ea41e158d0483402ea61d950c408ec02ea61d950c804eb02ea61d950c408eb02e96259d0c408e502e96259d0c804e402e96259d0c408e402e96259d0c840f002e9e25950c408e502e9e25950c804e402e9e25950c408e402e9e25950c840f002e9e15a50c840ef02ea61d950c408e502ea61d950c804e402ea61d950c408e402ea61d950c840f002ea6159d0c840ef02ea61d950c840ef)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_5 : blocksOK 11 56 P11 P12 955 20 B12_5 = true := by decide +kernel

def B12_6 : List (ℕ × ℕ × ℕ) := [(0x80ea82a92acaa4ab2a92ac2a254550, 48, 0x2ea61d950c840f802ea61d950c840f702c0e259d16848c302c0e25951e848c302c661d950c828f302c0e1d9526848c302c661d950c0a89002e82259d0d4487b02ea51e158c840f602ea59e150c840f602ea61d950c840f602ea61d950c840f502c661d950c0a84902ca0da51c14683402c661d950c828ed02c56259d0c828e602c5e25950c828e602c42259d0d6887b02c661d950c828e6),
  (0x80ea82a92acaa4ab2a92ac2a654554, 50, 0x2ea61d950c8410502ea61d950c804f802e96259d0c084cb02e96259d0c8410402e9e25950c084cb02e9e25950c8410402e9e15a50c8410202ea61d950c804f402ea51e158c8410302ea59e150c8410302ea61d950c084cb02ea61d950c8410402ea6159d0c8410202ea61d950c8410302ea61d950c8410202ea61d950c0849102c4e259d016888902ea51e158c8410102ea51e158c8410002ea59e150c8410102ea59e150c8410002ea59d160c840ff02ea61d950c8410102ea61d950c8410002ea61d158c840ff02ea61d950c840ff02ea61d950c840fe02ea61d950c840fd02ea61d950c0844a02ca0da51c16843602ea61d950c804ee02ca259d1404e8eb02e96259d0c804e702ca0da51c0568ea02e96259d0c840fb02e9e25950c804e702ca0da51405e8ea02e9e25950c840fb02e9e15a50c840f902ea61d950c840fc02c4e259d016887b02ea51e158c840fa02ea59e150c840fa02ea61d950c804e702ca0d9d140668ea02ea61d950c840fb02ea6159d0c840f902ea61d950c840fa02ea61d950c840f9),
  (0x80aa8aaa2a8aa8aaaaa2aa2a2a8a2a, 48, 0x2ea61d950c8410e02ea61d950c8410d00d06a49c2d6187d02ea61d950c8410c02c0e259d14868b902c0e259d16884c002e96259d0c8410b02c0e25951c868b902c0e25951e884c002e9e25950c8410b02e9e15a50c8410a02ea61d950c084f602c0e1d9524868b902c0e1d9526884c002ea61d950c8410b02ea6159d0c8410a02ea61d950c8410a02ea61d950c0849802e82259d0d4847802ea61d158c8410902ea61d950c8410902ea61d950c8410802ca61d950c0682402ea61c158d0844b02ea61d950c8410702e96259d0c8410602e9e25950c8410602c82259d0d6847802ea61d950c84106),
  (0x80ea82ab2a8aacaa2ab2a82a2a8550, 48, 0x2ea61d950c8410f00da69c946c1204c02c0e259d14868c202c0e25951c868c202ca61d950c068f702c0e1d9524868c202ca61d950c0689c02c82259d0d4687d02c42259d0d4a87d02e82259d0d4487900d82a49c6d5207d02ea51e158c8050c02ea51e158c4090c00d02a49c6d5a07d02ea59e150c8050c02ea59e150c4090c00e02a49c6d5187900d02a49c6d6187d02ea61d950c8050c02ea61d950c4090c00d82a49c6d5207900d02a49c6d5a07900da69c946c120f702ca61d950c0684c02c42259d0d6887d02c82259d0d4687902c42259d0d4a87902ca51e158c4290c02ca59e150c4290c02ca61d950c4290c),
  (0x80ea82ab2a8aacaa2ab2a82a6a8554, 50, 0x2ea61d950c8411d02ea61d950c8050f02c0e259d16884c602e96259d0c8411c02c0e25951e884c602e9e25950c8411c02e9e15a50c8411b02ea61d950c084f8002ea49c55218cef002ea49c55a10cef02c0e1d9526884c602ea61d950c8411c02ea6159d0c8411b002ea49c56190cef02ea61d950c8411b02ea61d950c0849d02c4e259d014a88802e82259d0d4847e02c4e259d014a87a02ea51e158c8050e02ea51e158c8050d02ca51e158e8411302ca51e158e8411202ea59e150c8050e02ea59e150c8050d02ca59e150e8411302ca59e150e8411202ea59d160c8411a02ea59d160c8411902ca59d160e8411002ea61d950c8050e02ea61d950c8050d02ca61d950e8411302ca61d950e8411202ea61d158c8411a02ea61d158c8411902ca61d158e8411002ea61d950c8411a02ea61d950c8411902ca61d950e8411002ea61d950c8411802ea61d950c8411702ea61d950c0844d02ea61d950c8411602e96259d0c8411402e9e25950c8411402c82259d0d6847e02c4e259d016887a02ea61d950c8411502c4e259d014a87902ea51e158c8411302ea51e158c8411202ea51e158c8411102ea59e150c8411302ea59e150c8411202ea59e150c8411102ea59d160c8411002ea61d950c8411402ea61d950c8411302ea61d950c8411202ea61d950c8411102ea61d158c8411002ea61d950c84110)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_6 : blocksOK 11 56 P11 P12 955 25 B12_6 = true := by decide +kernel

def B12_7 : List (ℕ × ℕ × ℕ) := [(0x80aa82aa2a8aa8aaaaa2aa2aaaa82a, 48, 0x2ea61d950c8412602ea61d950c8412502ea61d950c0851302ea61d950c0851102e96259d0c084d202e96259d0c084d002e96259d0c8412402e9e25950c084d202e9e25950c084d002e9e25950c8412402e9e15a50c8412302ea61d950c084fa02ea61d950c084d202ea61d950c084d002ea61d950c8412402ea6159d0c8412302ea61d950c8412302ea61d950c084a302e82259d0d4848002ea61d158c8412202ea61d950c8412202ea61d950c8412102ea61d950c0845002ea61c158d0844e02ea61d950c8412002e96259d0c8411e02e9e25950c8411e02ea61d950c8411f02ea61d950c8411e),
  (0x80aa82aa2a8aacaa2ab2a82aeaa054, 48, 0x2ea61d950c8412c02ea61d950c0851402e96259d0c084d502e9e25950c084d502ea61d950c048e702c20d9d144a68ea02c04e1d950a68e302c04e1d158a68e302ea61d950c084d302c04d9d160a68e302e9c56018d2482602ea6019d0d484a102c8c5e15812682002e82259d0d4847f02ea51e158c8412b02ea51e158c8412a02e805e158ca50b202ea59e150c8412b02ea59e150c8412a02e805e150ca58b202ea59d160c8412902ea61d950c8412b02ea61d950c8412a02e805d950ca60b202ea61d158c8412902ea61d950c8412902ea61d950c0845102ea61d950c8412802ea61d950c8412702c8c5e15812681e02ea51e158c8051e02ea59e150c8051e02ea61d950c8051e),
  (0x80aa82aa2aaaa8aaaaa2aa2aaaa8aa, 50, 0x2ea61d950c8413802c0e259d056887e02c06259d0d6887e02ea61d950408d1502c0e05a515e887602e96259d0c084d402e96259d0408cd402e96259d0c8413702c0e05a51d6887602e9e25950c084d402e9e25950408cd402e9e25950c8413702e9e15a50c8413502e9e15a5048c13402e9e15a50c8413402ea61d950408cfc02ea51e158c8413602ea59e150c8413602c0e059d256887602ea61d950c084d402ea61d950408cd402ea61d950c8413702ea6159d0c8413502ea6159d048c13402ea6159d0c8413402ea61d950c8413602ea61d950c8413502ea61d95048c13402ea61d950c84134000e259d16886c9902ea61d950408ca502c8e05a501d686502ea51e158c8413302ea51e158c8413202ea59e150c8413302ea59e150c8413202ea59d160c8413102ea61d950c8413302ea61d950c8413202ea61d158c8413102ea61d950c8413102ea61d950c8413002ea61d950c0480d02ea41e158d0845002ea41e158508c5002ea61d950c8412f02e96259d0480d2802e96259d0c8052702e96259d0480d2702e9e25950480d2802e9e25950c8052702e9e25950480d2702e9e15a50c8412d02ea61d950c8412e02c8e05a501d686402ea51e158480d1f02ea59e150480d1f02ea61d950480d2802ea61d950c8052702ea61d950480d2702ea6159d0c8412d02ea61d950480d1f02ea61d950c8412d),
  (0x80aa82ab2a8aacaa2ab2a82aaaa150, 48, 0x2ea61d950c8413d02ea61d950c0851602c0e259d16884d302c0e25951e884d302ea61d950c048ee02c2259d1448e8eb02c0661d9508e8e402c0661d1588e8e402c0e1d9526884d302c0659d1608e8e402ea61d950c0486102e82259d0d484a402ca45e15810e82502c8e259d016848102ea51e158c8413c02ea51e158c8413b02ea51e158c8413a02ea59e150c8413c02ea59e150c8413b02ea59e150c8413a02ea59d160c8413902ea61d950c8413c02ea61d950c8413b02ea61d950c8413a02ea61d158c8413902ea61d950c8413902ea61d950c0845202ea45e158108c5002ea61d950c8052f02ca45e15810e82302ea51e158c8052002ea59e150c8052002ea61d950c80520)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_7 : blocksOK 11 56 P11 P12 955 30 B12_7 = true := by decide +kernel

def B12_8 : List (ℕ × ℕ × ℕ) := [(0x80aa8aaa2a8aa8aa2aa2aa2aaaaa0a, 48, 0x2ea61d950c8414402ea61d950c8414302ea61d950c0851a02c261d950e8851002e96259d0c084d802c0e259d16884cf02e96259d0c8414102e9e25950c084d802c0e25951e884cf02e9e25950c8414102e9e15a50c8414002ea61d950c084ff02ea61d950c8414202ea61d950c084d802c0e1d9526884cf02ea61d950c8414102ea6159d0c8414002ea61d950c8414002ea61d950c084a902c8e259d016848302ea61d950c8413f02ea59e150c8413e02ea61d950c8413e02ea61d950c0845502ea61d940d0845302ea61d950c8053902e96259d0c8052902e9e25950c8052902ea61d950c8053102ea61d950c80529),
  (0x80aa8aaa2a8aa8aaaaa2aa2aaaa228, 48, 0x2ea61d950c8414a02ea61d950c8414902ea61d950c0490d02c261d950e8851202e96259d0c048be02c0e259d16884d102e96259d0c8414802e9e25950c048be02c0e25951e884d102e9e25950c8414802e9e15a50c8414702ea61d950c0850002ea61d950c048be02c0e1d9526884d102ea61d950c8414802ea6159d0c8414702ea61d950c8414702ea61d950c084aa02c8e259d016848002ea61d158c8414602ea61d950c8414602ea61d950c8414502ea61d950c0482502ea61c158d0845402ea61d950c8053a02e84259d0c960b202e8425950c9e0b202ea61d950c8053202e841d950ca60b2),
  (0x80aa8aaa2a8aa8aaaaa2aa2aaaaa2a, 50, 0x2ea61d950c8415702ea61d950c0494a02ea61d950c0490e02c261d950e8851302e96259d0c048bf02c0e259d16884d202e96259d0c8415402e96259d0c8415302e9e25950c048bf02c0e25951e884d202e9e25950c8415402e9e25950c8415302e9e15a50c8415102e9e15a50c8415002e9e15a50c8414f02ea61d950c0850102ea61d158c8415602ea61d950c8415602ea61d950c8415502ea61d950c048bf02c0e1d9526884d202ea61d950c8415402ea61d950c8415302ea6159d0c8415102ea6159d0c8415002ea6159d0c8414f02ea61d950c8415202ea61d950c8415102ea61d950c8415002ea61d950c8414f000e259d16886c8502ea61d950c084ab02c8e259d016848402ea61d158c8414e02ea51e158c8054602ea61d950c8414e02ea59e150c8054602ea59d160c8053f02ea61d950c8414d02ea61d950c8054502ea61d158c8053e02ea61d950c8053e02ea61d950c0482602ea61c158d0845502ea61d950c8053c02ea61d950c8053b02e96259d0c8052b02e96259d0c8052a02e96259d0c8414c02e9e25950c8052b02e9e25950c8052a02e9e25950c8414c02e9e15a50c8414b02ea61d950c8053302c8e259d016847802ea51e158c8052202ea59e150c8052202ea61d950c8052b02ea61d950c8052a02ea61d950c8414c02ea6159d0c8414b02ea61d950c8052102ea61d950c8414b),
  (0x80ea82aa2a8aa8aa2ab2a82aeaa414, 48, 0x2ea61d950c8415802ea61d950c0851b02e96259d0c084dc02e9e25950c084d902ea61d950c0850202ea61d950c084d902ea61d950c04876004e259d02896cad02ca61d8d014687402e82259d0d4848502ea51e158c8055102ea51e158c8055002ea51e158c8054702ea59e150c8055102ea59e150c8055002ea59e150c8054702ea59d160c8054002ea61d950c8055102ea61d950c8055002ea61d950c8054702ea61d158c8054002ea61d950c8054002ea61d950c0845702ea61d950c8053502ea61d95008c53402ca61d8d014687202ea51e158c8052302ea59e150c8052302ea61d950c80523)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_8 : blocksOK 11 56 P11 P12 955 34 B12_8 = true := by decide +kernel

def B12_9 : List (ℕ × ℕ × ℕ) := [(0x80ea82aa2a8aa8aaaaa2aa2aaaa428, 48, 0x6ea49c1610d8e5006ea41c96190cef02e96259d0c084da02e9e25950c084da02ea61d950c0850302ea61d950c084da02ea61d950c084b002c8e259d016848702ea51e158c8055602ea59e150c8055602ea59d160c8054202ea61d950c8055202c58d241e16883602ea61c158d0845602c4259d1608e8e402c40da51e0968e302c40da51609e8e302ea61d950c8053602c40d9d160a68e3),
  (0x80ea82aa2a8aacaa2ab2a82aaaa450, 48, 0x2ea61d950c8415902ea61d950c0851c02c0e259d16884d902c0e25951e884d902ea61d950c0850402ea61d950c084db02ea61d950c0487e02ea6019d0d484af02c8e259d014687002c8e259d016848602ea51e158c8055402ea51e158c8055302ea51e158c8054802ea59e150c8055402ea59e150c8055302ea59e150c8054802ea59d160c8054102ea61d950c8055402ea61d950c8055302ea61d950c8054802ea61d158c8054102ea61d950c8054102ea61d950c0845802ea61d950048cd402ea61d950c8053702c8e259d014686f02ea51e158c8052402ea59e150c8052402ea61d950c80524),
  (0x80ea82ab2a8aacaa2ab2a82aeaa554, 52, 0x2ea61d950c8416202ea61d950c0491d02e96259d0c048dd02e96259d0c4095902e9e25950c048dd02e9e25950c4095902e9e15a50c4095802e9e15a50c8416102ea61d950c04905002ea49c5518e0e5002ea49c5590e0e5002ea49c5520d8df02ea61d950c048dd02ea61d950c4095902ea6159d0c4095802ea6159d0c84161002ea49c5610d8e5002ea49c5518e0df02ea61d950c4095802ea61d950c84161002ea49c5590e0df000e259d16886c6302ea61d950c048b102c4e259d016888c02c8e259d016848c02e82259d0d4488802ea51e158c4095702ea51e158c4094a02ea51e158c8054a02ea51e158c4094902ea59e150c4095702ea59e150c4094a02ea59e150c8054a02ea59e150c4094902ea59d160c4094402ea59d160c8054302ea59d160c40943002a59d148c62c5402ea61d950c4095702ea61d950c4094a02ea61d950c8054a02ea61d950c4094902ea61d158c4094402ea61d158c8054302ea61d158c40943002a61d148c5ac5402ea61d950c4094402ea61d950c8054302ea61d950c40943002a61d948c52c5402ea61d950c8416002ea61d950c8415f002a61d950c4ac53002a61d950c86c5302ea61d950c0485902ea61d950c4093d02e96259d0c4092c02e96259d0c8415e02e9e25950c4092c02e9e25950c8415e02e9e15a50c8415d02ea61d950c4093802c4e259d016887e02c8e259d016847e02c4e259d016887d02ea51e158c4092602ea51e158c8052502ea51e158c40925002269c946d8d10702ea59e150c4092602ea59e150c8052502ea59e150c40925002269c946d0d90702ea59d160c8415c02ea59d160c4815b02ea59d160c8415b02ea61d950c4092c02ea61d950c8415e02ea6159d0c8415d02ea61d950c4092602ea61d950c8052502ea61d950c40925001a69c946d0e10702ea61d158c8415c02ea61d158c4815b02ea61d158c8415b02ea61d950c8415d02ea61d950c8415c02ea61d950c4815b02ea61d950c8415b02ea61d950c8415a),
  (0x802a92ad2a0ab4a92ad2a454916952, 48, 0x2ea61d950c8416a02c259d14c86a05202c09a51cd46a05102c09a514dc6a05102ea61d950c8416902c18924dc56282202c189245cd6282202c2259d14688cdf02c188e45d16282202c2259cd46890df02c2259c54e890df02c108e45d96282202c2251cd46898df02c2251c54e898df02c224dc552898df02c099d14e46a05102c1a51cd604a85f02c18924dc56a03d02c189245cd6a03d02c188e45d16a03d02c108e45d96a03d02ea61d950c8416802ea61c55908c16702ea61cd5908416702ea61cd4589016602ea61d158c8416702ea61d14588c16602ea61d14d88416602ea61d950c8416702ea61d94508c16602ea61d94d08416602ea61d950c8416602ea61d950c8416502ea61c55908c16402ea61cd5908416402ea61d158c8416402ea61d950c8416402ea61d950c8416302ea61d9500c481002ea61d9500c841802ea61d950048c1802ea61d94c04901802ea61d14c04981802e89a51cc056029)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_9 : blocksOK 11 56 P11 P12 955 38 B12_9 = true := by decide +kernel

def B12_10 : List (ℕ × ℕ × ℕ) := [(0x802a9aac2a0ab0a9aac2a654d1622c, 48, 0x2ea61d950c8417102c09a51cc56a0a402c05a51cc96a0a402c259d14ca8612f02c098524d5ea0a102c09a51cd6a052702c05a51cd6a092702c098524dd6a0a102c09a514dea052702c05a514dea092702c098524de9612d02ea61d950c8417002c2259d14e848de02c2259cd52848de02c2251cd5a848de02ea61d950c8416f02c09851ce56a0a102c099d14e6a052702c059d14e6a092702c09851ce69612d02c1a51cd62848e802c098514e69e12d02ea61d950c8416e02ea61cd5908416d02ea61d158c8416d02ea61d950c8416d02ea61d950c8416c02ea61d950c4096502ea61c15908c56402ea61c15904c96402e96259d0c8416b02e9e25950c8416b02ea61d9500c481902ea61d950c8416b),
  (0x802a9aac2a2ab0a92ac2a654d1628c, 48, 0x2ea61d950c8417702c261d14c69893c02c259d14caa053c02c259d14ca8612002c06251cd69892b02c09a51cd68611e02c06251cd68991e02c062514de9892b02c09a514de8611e02c062514de8991e02e9e15a50c8417502ea61d950c8417602c1a61d14e848e002c1a61cd52848e002c2251cd5a884e102c061d14e69892b02c099d14e68611e02c061d14e68991e02ea6159d0c8417502c1a51cd62848e102ea61d950c8417502ea61d950c8417402ea61d94d08417302ea61d950c8417302ea59e150c4096d02ea61d950c8056d02ea59e150c4096702ea61d94108c56602ea59e14104c96602e96259d0c8417202e9e25950c8417202ea59e1500c481a02ea61d950c84172),
  (0x802a9aac2a2ab0a9aac2a654d162ac, 50, 0x2ea61d950c8417f02c261d9504ca82602c259d14c86286102c261d9504e885002c261d8514ca82602c09a51cc6a152802c261d8514e885002e9605a50c9c17d02c2615851cca82602c09a514c6a1d2802c2615851ce885002e9e05a50c9417d02c09a504d6a1d2800099d14c62a6cac02e9e15a50c8417d02c18924dd60696902c2259d14c6884002c2259cd5068840002251cd6885acae02c2251cd5868840002259cd68852cae002259d16884ecae02ea61d950c8417e02c1e158524ca82602c099d14c6a252802c1e158524e885002ea6059d0c9417d02c099d04d6a25280009a514c629ecac02ea6159d0c8417d02c1a51cd606884202ea61cd5908417c02ea61d158c8417c02c099504dea25280009a51cc6296cac02ea61d950c8417d02ea61d950c8417c0009a51cd6286cac02ea61d950c8417b02e9e14c5908257402e9e15058c8257402ea61d14d88417a02e9e15850c8257402ea61d94d08417a02ea61d950c8417a02e9e15850c8256e02ea61cd5908417902ea61d158c8417902ea61d950c8417902e9e15850c8256802ea61c15908c56702ea61d950c8417802ea41e15904c96402ea61c05908d56702e88259d0d4616b02ea41e05914c96402ea61405908dd6702e8825950dc616b02ea4160591cc96402e8825850dd616b02e9e158500ca41b02ea61d95004c85b02ea61d94c05085b02ea61d14c05885b02e9e1405908e56702e881d950e4616b02e9c1605924c96402e881d850e5616b02ea59d14c06085c02e8815850e5e16b),
  (0x806a92ac2a2ab0a9aac2a654d164ac, 50, 0x2c58924dd62818402c259d14c8628ee02c09a51cd4628e702c58914e5e2818202c09a514dc628e702c5891ce56281820009851cd626ad5502ea61d950c8418402c2259d14e884e702c2259cd52884e7002269d14c986d5502c2251cd5a884e7002269d94c906d55002269d9508c6d5502ea61d950c8418302c099d14e4628e702c58924dd62818200098524d61ead5502c1a51cd62884ee02ea61cd5908418202ea61d158c8418200098524de16ad5502ea61d950c8418202c58924dd60296902ea61cd5908057602ea61d158c8057602c508e59d62818002ea61d950c8057602c588e51d62818002c58924dd62818002ea61d950c8057002c4c9a51d62818102c509a4dd62818102c58924dd62818102ea61d950c8056902c58924dc16282202c58924dd60297002c6259d140e888e02c58914e5e0297602c58924dc2960e902e96259d0c8418102c5891ce560297602c58924d429e0e902e9e25950c8418102e9e15a50c8418002ea61d9500c842202ea61d95004c8e902ea61d94c0508e902ea61d14c0588e902c58924dd60297602c5891cd42a60e902ea61d950c8418102ea6159d0c8418002e89a51cc14608e02ea61d950c84180)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_10 : blocksOK 11 56 P11 P12 955 42 B12_10 = true := by decide +kernel

def B12_11 : List (ℕ × ℕ × ℕ) := [(0x806a92ad2a0ab4a92ad2a454916d52, 50, 0x2ea61d950c8418f02c259d14c86293d02c09a51cd46292c02e96259d0c8418d02c09a514dc6292c02e9e25950c8418d02e9e15a50c8418c02c18924dd60698402c2259d14c4a8e502c2259cd504a8e5002251cd6885ac5602c2251cd584a8e5002259cd68852c56002259d16884ec5602ea61d950c8418e02c099d14e46292c02ea61d950c8418d02ea6159d0c8418c02c1a51cd604a8ec02ea61cd5908418b02ea61d158c8418b02ea61d950c8418c02ea61d950c8418b02c661d950c8297f02c661d9500ca82602c661cd5908297702c661d95028c93c02c661d158c8297702c661d94c29093c02ea61d14d88418a002251cd449aad5b02c661d950c8297702c661d14c29893c02ea61d94d08418a002259cd4492ad5b02ea61d950c8418a002259d1448ead5b002259d14ca86d5a02c661d950c8297102c49a51cc16a0a402ea61cd5908418902c661cd590a818502ea61d158c8418902c661d158ca818502ea61d14d88418802ea61d950c8418902c661d950ca818502ea61d94d08418802ea61d950c8418802c661d950c8296a02ea61d950c8418702e96259d0c8418602e9e25950c8418602ea61d9500c842602c661d9500ca82402ea61d95004c93c02ea61d950048d0702ea61d94c05093c02ea61d94c049107002251cd68986d5b02ea61d14c05893c02ea61d14c049907002259cd68906d5b002259d1688c6d5b02ea61d950c8418602e89a51cc1460a402e89a51cc14609402ea61cd5908418502ea61d158c8418502ea61d950c84185),
  (0x802a92ad2a4ab4a92ad2a454956952, 50, 0x2ea61d950c8419602c261d9508c681602c261d8914c681602e9609a50dc419402c2615891cc681602e9e09a50d4419402e9e15a50c8419402ea61d950c8419502c2259d1448e83102c2259d14c8683102c2259d14c8680a02c2259cd508683102c2259cd508680a02c2259c5508e80a02ea51cd4609819302c2251cd588683102c2251cd588680a02c2251c5588e80a02ea59cd4609019302c224dc5589280a02ea59d14608c19302ea59d14e08419302c1e158924c681602ea6099d0d4419402ea6159d0c8419402c1a51cd608683102c1a51cd608680a02c1a51c5608e80a02ea61cd4589019302c1a4dc5609280a02ea61d14588c19302ea61d14d88419302ea61d950c8419402c124dc5609a80a02ea61d94508c19302ea61d94d08419302ea61d950c8419302ea61d950c8419202e9c5609900e56802e9cd609900656802ea45e159008d7802e9d16098c0656802ea45e158c0917802ea4de15840917802ea51cd4609819102e9d96090c0656802ea45e150c0997802ea4de15040997802ea59cd4609019102ea51e14c40997802ea59d14608c19102ea59d14e08419102e9e15890c0656802ea45d950c0a17802ea4dd95040a17802ea61cd4589019102ea51d94c40a17802ea61d14588c19102ea61d14d88419102ea59d14c40a17802ea61d94508c19102ea61d94d08419102ea61d950c8419102ea61d950c8419002ea41d950c8616302ea41d890d4616302ea415890dc616302e9e158900c641102ea61d9500c842a02ea61d950048c2a02ea61d950084c5a02ea61d94c04902a02ea61d94c08505a02ea61d94408d05a02ea61d14c04982a02ea61d14c08585a02ea61d14408d85a02ea61cd4409185a02e9c15890e4616302ea59d14c04a02a02ea59d14c08605a02ea59d14408e05a02ea59cd4409205a02ea51cd4409a05a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_11 : blocksOK 11 56 P11 P12 955 46 B12_11 = true := by decide +kernel

def B12_12 : List (ℕ × ℕ × ℕ) := [(0x802a9aac2a4ab0a92ac2a654d5620c, 48, 0x2ea61d950c8419c02ea61d950c8419b02c261d9508e845502c261d9508e844e02c261d8914e845502c261d8914e844e02e9609a50dc419802c2615891ce845502c2615891ce844e02e9e09a50d4419802e9e15a50c8419802ea61d950c8419a02c2259d14ca843c02c2259cd50a843c02ea61d950c8419902c2251cd58a843e02c1e158924e845502c1e158924e844e02ea6099d0d4419802ea6159d0c8419802c1a51cd60a843e02ea61d950c8419802ea61d950c8419702ea4de15900857a02ea51e158c0857a02ea59e150c0857902ea61d950c0857902ea59d14c04a17802ea61d94108c59102ea41e15908c56602ea41e09914c56602ea4160991cc56602ea61d9500c842b02e9c1609924c566),
  (0x802a9aac2a6ab0a9aac2a654d562ac, 52, 0x2ea61d950c841a502c261d9504ca83302c261d9508c683302c261d9508c680d02c261d8914c683302c261d8914c680d02c261d8514ca80d02e9609850e5c1a202c2615891cc683302c2615891cc680d02c2615851cca80d02e9e09850e541a202c2609851cd680d02e9e15850e481a202e9e15890e441a202e9e15890c641a102c2259d148c699502c2259d14c8681402c2259cd508681402ea51cd618841a402c2251cd588681402ea59cd610841a402ea59d160c841a402ea59d14e0841a302c1e158924c683302c1e158924c680d02c1e158524ca80d02ea609850dd41a202c1e098524d680d02ea615850dc81a202ea615890dc41a202ea615890c5c1a102c1a51cd608681402ea61cd590841a402ea61d158c841a402ea61d14d8841a302c16098524de80d02ea61d850d481a202ea61d890d441a202ea61d890c541a102ea61d950c841a402ea61d94d0841a302ea61d950c841a302ea61d950c841a202ea61d950c481a102ea61d950c841a102ea61d950c841a002e9cd609900657b02e9d16098c0657b02e9d14ca184259702e9d96090c0657b02e9d94ca104259702e9d950a0c4259702ea59d14e08419f02e9e15890c0657b02e9e14c9904259702e9e15098c4259702ea61d14d88419f02e9e15890c4259702ea61d94d08419f02ea61d950c8419f02e9e15890c4259202e9c1609904e56802e9c1605908e56802ea41e15904c96502e9c0a05914e56802ea41e09904d56502ea41e05908d56502e9609850e5c19d02e940a0591ce56802ea41609904dd6502ea41605908dd6502e9e09850e5419d02ea40a05914dd6502e9e15850e4819d02e9e15890e4419d02e9e158900c642c02e9e1589004e45d02e9e1588c05245d02ea51cd6188419e02e9e1508c05a45d02ea59cd6108419e02ea59d160c8419e02e940a05924dd6802e9c1609904e56502e9c1605908e56502ea609850dd419d02e9c0a05914e56502ea615850dc819d02ea615890dc419d02e9d9508c06245d02ea61cd5908419e02ea61d158c8419e02e940a0591ce56502ea61d850d4819d02ea61d890d4419d02ea61d950c8419e02ea61d950c8419d),
  (0x806a92ac2a4ab0a92ac2a654d5640c, 48, 0x2ea61d950c841a702c261d9508e845602c261d8914e845602c2615891ce845602ea61d950c841a602c2259d14ca844602c2259cd50a844602c2251cd58a844702c1e158924e845602c1a51cd60a844702ea61d950c805a4004e61d968092cae005261d96808ecae02ea51cd6188059902ea59e150c0857c02ea61d950c0857c02c524dc1609a80a02ea61d94108c59302c4251cd5a8a0df02c4251cc9a960df02c42514c9a9e0df02ea61d9500c842e02c41d14c9aa60df)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_12 : blocksOK 11 56 P11 P12 955 48 B12_12 = true := by decide +kernel

def B12_13 : List (ℕ × ℕ × ℕ) := [(0x806a92ac2a4ab0a92ad2a454956c12, 48, 0x2ea61d950c841a802c261d9508e845702c261d8914e845702c2615891ce845802c2259d148c69a602c2259d14ca844502c2259cd50a844502c2251cd58a844502c1e158924e845802c1a51cd60a844502c56098124de80d02ea61d810d485a202c4215891e8e52802ea4de15900857d02c421588de9252802ea51e158c0857d02ea51cd6188059802c421508de9a52802ea59e150c0857d02ea59cd6108059802ea59d160c8059802c419508dea252802ea61d950c0857d02ea61cd5908059802ea61d158c8059802ea61d950c8059802ea61d950c8059402c42158924de80902ea61d9500c842f02ea61d95008c45e02ea61d94c09045e02ea61d14c09845e02ea59d14c0a045e),
  (0x806a92ac2a6ab0a9aac2a654d564ac, 52, 0x2c6259d148e81ab02c261d9508c684a02c261d8914c684a02c6158925cc29a602c2615891cc684a02c61d89254c29a602c61d95248c29a60026059d14a8ed7e02ea61d950c841ab02c2259d14ca844a02c2259cd50a844a02ea51cd618805a602c2251cd58a844a02ea59cd610805a602ea59d160c805a6002269d950c4ad7e02c1e158924c684a02c625891d4c29a602c625951c8c29a6001e05a514a8ed7e02c1a51cd60a844a02ea61cd590805a602ea61d158c805a6001a69e150c4ad7e02c6259d148c29a6001605a51ca8ed7e02ea61d950c805a6001269e158c4ad7e000e69e15904ad7e000a05a51d68ed7e02c6259d148c299502c601a51d4ca96902c601a4dd50a96902ea51cd6188059a02c60124dd58a96902ea59cd6108059a02ea59d160c8059a002a59d14c4a2ca702c58124dd60a96902ea61cd5908059a02ea61d158c8059a002a61d14c49aca702ea61d950c8059a002a61d94c492ca7002a61d95048eca702ea61d950c841aa02ea61d950c8059502c6259d1408e83102ea41e15908c56902c6259d140ca85f02ea41e09914c56902c6259d080d685f02c6158925cc299a02c6158925ce81a902ea4160991cc56902c62595080de85f02c61d89254c299a02c61d89254e81a902c61d95248c299a02c61d95248e81a900061d950a8e6ca702ea61d9500c843102ea61d95008c45f02ea61d94c09045f02ea51cd618841a902ea61d14c09845f02ea59cd610841a902ea59d160c841a902e9c1609924c56902c61d95080e685f02c625891d4c299a02c625891d4e81a902c625951c8c299a02c625951c8e81a9000625950a8deca702ea59d14c0a045f02ea61cd590841a902ea61d158c841a902c6259d148c299a02c6259d148e81a90006259d0a8d6ca702ea61d950c841a90006259d168caca7),
  (0x806a92ad2a4ab4a92ad2a454956d52, 52, 0x2ea61d950c841b202c261d9508c685902c261d8914c685902c5609a50dc29a802c2615891cc685902c5e09a50d429a802c5e15a50c829a802e9e15890e441b102c2259d148c69ab02c2259d14c8684802c2259cd508684802c651cd618829a702c2251cd588684802c659cd610829a702c659d160c829a7002259d14e886d9302c1e158924c685902c66099d0d429a802c66159d0c829a802ea615890dc41b102c1a51cd608684802c661cd590829a702c661d158c829a7001a61d14e886d9302c661d950c829a802ea61d890d441b102c661d950c829a7001261d94e886d93000e61d952886d9302ea61d950c841b102c661d950c829a502c661d9500ca83302c64de15900a97f02c661d95008e86102c651e158c0a97f02c661d94c09286102c651cd6188299c02ea51cd6188059b02c659e150c0a97f02c661d14c09a86102c659cd6108299c02ea59cd6108059b02c659d160c8299c02ea59d160c8059b02ea59d14e0841b002c659d14e0a81ac02c661d950c0a97f02c659d14c0a286102c661cd5908299c02ea61cd5908059b02c661d158c8299c02ea61d158c8059b02ea61d14d8841b002c661d14d8a81ac02c661d950c8299c02ea61d950c8059b02ea61d94d0841b002c661d94d0a81ac02ea61d950c841b002c661d950ca81ac02ea61d950c841af02c661d950c8299602c641e15908e96a02c641e09914e96a02e9609a50dc41ae02c64160991ce96a02e9e09a50d441ae02e9e15a50c841ae02ea61d9500c843302c661d9500ca83202ea61d95008c46102c661d95008e86002ea61d94c09046102c661d94c09286002c651cd6188299b02ea51cd618841ad02ea61d14c09846102c661d14c09a86002c659cd6108299b02ea59cd610841ad02c659d160c8299b02ea59d160c841ad02ea59d14e0841ac02c5c1609924e96a02ea6099d0d441ae02ea6159d0c841ae02ea59d14c0a046102c659d14c0a286002c661cd5908299b02ea61cd590841ad02c661d158c8299b02ea61d158c841ad02ea61d14d8841ac02ea61d950c841ae02c661d950c8299b02ea61d950c841ad02ea61d94d0841ac02ea61d950c841ac)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_13 : blocksOK 11 56 P11 P12 955 51 B12_13 = true := by decide +kernel

def B12_14 : List (ℕ × ℕ × ℕ) := [(0x80aa82ac2a4ab4a92ad2a454a56852, 48, 0x2ea61d950c841b802ea61d950c841b702ea61d950c841b602c2259d14e8850102c2259d14e884fa02c2259cd528850102c2259cd52884fa02ea51cd618841b502c2251cd5a8850102c2251cd5a884fa02ea59cd610841b502ea59d160c841b502c1a51cd628850102c1a51cd62884fa02ea61cd590841b502ea61d158c841b502ea61d950c841b502e9c5601924c96902ca25811d4c699a02ca25811d44e97602ea4de15900858102ca2580dd45297602ea51e158c0858102ea51cd618841b402ca2500dd45a97602ea59e150c0858102ea59cd610841b402ea59d160c841b402c9a500dd46297602ea61d950c0858102ea61cd590841b402ea61d158c841b402ea61d950c841b402ea61d950c841b302ea61d9500c844002ea61d9500c843e02ea61d950084ce102ea61d94c0850e102ea61d14c0858e102ea59d14c0860e1),
  (0x80aa82ad2a4ab4a92ad2a454a56952, 50, 0x2ea61d950c841bc02e96259d0c841ba02e9e25950c841ba02ea61d950c841bb02c2259d144e889102c2259d14c6889102c2259d14688cfc02c2259cd506889102c2259cd46890fc02c2259c54e890fc002269d14c49ad8e02c2251cd586889102c2251cd46898fc02c2251c54e898fc002269d94c492d8e02c224dc552898fc002269d95048ed8e002269d950c86d8e02ea61d950c841ba02c1a51cd606889102c1a51cd468a0fc02c1a51c54e8a0fc001a69e14c492d8e02c1a4dc5528a0fc001a69e15048ed8e001a69e150c86d8e02c124dc55a8a0fc001269e15848ed8e001269e158c86d8e000e69e159086d8e02ea61d950c0499502ea45e15900c96902ea4de15900496902ca01a51d4c697002ea51e158c0496902ca01a4dd50697002ca01a45d50e970002a51cd44a1ad6002ea59e150c0496902ca0124dd58697002ca01245d58e970002a59cd44a12d6002ca00e45d592970002a59d144a0ed60002a59d14ca06d6002ea61d950c0496902c98124dd60697002c981245d60e970002a61cd44992d6002c980e45d612970002a61d14498ed60002a61d14c986d6002c900e45d61a970002a61d94490ed60002a61d94c906d60002a61d9508c6d6002ea61d950c841b902ca259d140c686802e95a51cc4821b302e9da514c4821b302ea61d9500c481402ea61d9500c844202ea61d950048c4202ea61d950084ce802ea61d94c04904202ea61d94c0850e802ea61d94408d0e802ea61d14c04984202ea61d14c0858e802ea61d14408d8e802ea61cd440918e802ea59d14c4821b302ea59d14c04a04202ea59d14c0860e802ea59d14408e0e802ea59cd440920e802ea51cd4409a0e8),
  (0x80aa8aac2a4ab0a92ac2a654e5620c, 48, 0x2ea61d950c841c102ea61d950c841c002e96259d0c841bd02e9e25950c841bd02ea61d950c841bf02c2259d14e884f902c2259cd52884f902ea61d950c841be02c2251cd5a884fb02ea61d950c841bd02c1a51cd62884fb02ea61d950c0499a02ca01a51d4e858002ca01a4dd52858002ca0124dd5a858102c98124dd62858102c904e41d61a970006a61d94090ed6002ca259d140e848d02e96259d0c805b402e9e25950c805b402ea61d9500c844402ea61d950c805b4),
  (0x80ea82ac2a4ab0a92ac2a654e5640c, 48, 0x2ea61d950c841c302ea61d950c841c202c2259d14e8850202c2259cd528850202c2251cd5a8850402c1a51cd628850402ea61d950c049a6004e69e15810ad55005269e1580cad5502ea51cd618805be02ea59e150c0858202ea61d950c0858202c524dc15a8a0fc005269e15808ed8e02ca259d140c687102e96259d0c805b502e9e25950c805b502ea61d9500c844502ea61d950c805b5)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_14 : blocksOK 11 56 P11 P12 955 54 B12_14 = true := by decide +kernel

def B12_15 : List (ℕ × ℕ × ℕ) := [(0x80ea82ac2a4ab4a92ad2a454a56450, 48, 0x2ea61d950c841c502ea61d950c841c402c2259d14e8850302c2259cd528850302c2251cd5a8850302c1a51cd628850302c5e158124ca84a02ca25811d4c69a602c421d95248e8e702ca01a51d4e858202c421d94e4928e702ca01a4dd52858202ea51cd618805bd02c421d14e49a8e702ca0124dd5a858202ea59cd610805bd02ea59d160c805bd02c419d14e4a28e702c98124dd62858202ea61cd590805bd02ea61d158c805bd02ea61d950c805bd02ea61d950c805ba02ea61d9500c483902ea61d9500c844702c421d952688cc702c421d94e6890c702c421d14e6898c702c419d14e68a0c7),
  (0x80ea82ac2a6ab0a9aac2a654e564ac, 52, 0x2ea61d950c841cc02e96259d0c409c402e9e25950c409c4002609851d4ead9902ea61d950c841cb02c2259d14e8490502c2259cd528490502ea51cd618409c202c2251cd5a8490502ea59cd610409c202ea59d160c409c2002269d950c86d6f02ea61d950c409c4001e0985254ead9902c1a51cd628490502ea61cd590409c202ea61d158c409c2001a69e150c86d6f0016098525cead9902ea61d950c409c2001269e158c86d6f000e69e159086d6f02ea61d950c049ab02ea4de15900498402ea51e158c0498402ea51cd618409bf02ea59e150c0498402ea59cd610409bf02ea59d160c409bf002a59d14ca06d3002ea61d950c0498402ea61cd590409bf02ea61d158c409bf002a61d14c986d3002ea61d950c409bf002a61d94c906d30002a61d9508c6d3002ea61d950c841ca002a61d9504cac43002a61d9508c6c4302ea61d950c409bb02c6259d140e889102ca259d140e849102c6259d140e889002e96259d0c409b702e96259d0c805b602e96259d0c409b602e96259d0c841c902e9e25950c409b702e9e25950c805b602e9e25950c409b602e9e25950c841c902e9e15a50c841c802e9e15a50c481c702e9e15a50c841c702ea61d9500c484802ea61d95004c8ec02ea61d94c0508ec02ea51cd618841c602ea61d14c0588ec02ea59cd610841c602ea59d160c841c602ea61d950c409b702ea61d950c805b602ea61d950c409b602ea61d950c841c902ea6159d0c841c802ea6159d0c481c702ea6159d0c841c702ea59d14c0608ec02ea61cd590841c602ea61d158c841c602ea61d950c841c802ea61d950c481c702ea61d950c841c702ea61d950c841c6000a259d168c6c96),
  (0x80ea82ad2a4ab4a92ad2a454a56550, 50, 0x2ea61d950c841ce02c56259d0c829c502c5e25950c829c502c661d950c829cc02c2259d14e848f402c2259cd52848f402c651cd618829c302c2251cd5a848f402c659cd610829c302c659d160c829c302c661d950c829c502c1a51cd62848f402c661cd590829c302c661d158c829c302c661d950c829c302ca259d140c69ab02c661d9500ca84a02ca01a51d4c698402c661d95008e8ee02ca01a4dd50698402c661d94c0928ee02c651cd618829c102ea51cd618805c002ca0124dd58698402c661d14c09a8ee02c659cd610829c102ea59cd610805c002c659d160c829c102ea59d160c805c0002a59d14c862d1802c98124dd60698402c659d14c0a28ee02c661cd590829c102ea61cd590805c002c661d158c829c102ea61d158c805c0002a61d14c85ad1802c661d950c829c102ea61d950c805c0002a61d94c852d18002a61d95084ed1802ea61d950c841cd02c661d950c829bc02ca259d140c688f02c56259d0c829b802c5e25950c829b802ea61d9500c844a02c661d9500ca84902ea61d95008c4ee02c661d95008e8ed02ea61d94c0904ee02c661d94c0928ed02c651cd618829c002ea61d14c0984ee02c661d14c09a8ed02c659cd610829c002c659d160c829c002c661d950c829b802ea59d14c0a04ee02c659d14c0a28ed02c661cd590829c002c661d158c829c002c661d950c829c0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_15 : blocksOK 11 56 P11 P12 955 58 B12_15 = true := by decide +kernel

def B12_16 : List (ℕ × ℕ × ℕ) := [(0x80aa8aae2a0ab8a82ae2a2546a8a0e, 48, 0x2ea61d950c841d402ea61d950c841d302e96259d0c841d202e9e25950c841d202ca61d950c069c102c2259d14e884ef02c2259cd52884ef001a51cd6886e1c302c2251cd5a884f002ea61d950c841d202c1a51cd62884f002ca61d950c0699c02ca61d9500e845502ea4de15900858a02ca61d95028c53902ea51e158c0858a02ca61d94c29053902ea61d950c841d102ea59e150c0858902ca61d14c29853b02ea59e14d0841d002ea59e150c841d002ea61d950c0858902ca59d14c2a053b02ea61d94d0841d002ea61d950c841d002ea61d950c841cf02ea59d14c04a18702ea61d9500c845502ea61d9500c844b02ea61d95008c53902ea61d94c09053902ea61d14c09853b02ea59d14c0a053b),
  (0x80ea82af2a0abca82af2a0542a8550, 48, 0x2ea61d950c841d602ca61d950c069ce02c2259d14c868f202c2259cd50868f202c2251cd58868f202c1a51cd60868f202ca61d950c069b202c661d9500ca85902ca61d9500c685902ca61d9500c684d02ca4de15900698f02c661d95008e93d02ca61d95004e93d02ca61d950068d1602ca51e158c0698f02c661d94c09293d02ca61d94c05293d02ca61d94c06911602ca51cd618429d402ea51cd618805d302ea51cd618409d302ca59e150c0698f02c661d14c09a93d02ca61d14c05a93d02ca61d14c06991602ca59cd610429d402ea59cd610805d302ea59cd610409d302ca59d160c429d402ea59d160c805d302ea59d160c409d302ea59d14e0841d502ca61d950c0698f02c659d14c0a293d02ca59d14c06293d02ca59d14c06a11602ca61cd590429d402ea61cd590805d302ea61cd590409d302ca61d158c429d402ea61d158c805d302ea61d158c409d302ea61d14d8841d502ca61d950c429d402ea61d950c805d302ea61d950c409d302ea61d94d0841d502ea61d950c841d502ea61d9500c485902ea61d9500c484d02ea61d9500c844d02ca61d9500c684c02ea61d95004c93d02ea61d950048d1602ea61d950084d1602ea61d94c05093d02ea61d94c04911602ea61d94c08511602ca51cd618429d302ea61d14c05893d02ea61d14c04991602ea61d14c08591602ca59cd610429d302ca59d160c429d302ea59d14c06093d02ea59d14c04a11602ea59d14c08611602ca61cd590429d302ca61d158c429d302ca61d950c429d3),
  (0x802abaa82a6aa0abaa82ae8a1542a8, 48, 0x2ea61d950c841d902c261d9504a8cab02c261d950868cab02c261d950a84d3302ea61d950c841d802c261d9504a8ca302c261d950868ca302c261d95068c91f02c261d891468cab02c261d891684d3302c261d851688d33000d950a8625ed6102c261d891468ca302c261d89068d51f02c261d850a8d51f02c2615891c68cab02c2615891e84d3302c2615851e88d33000d9d0a86256d6102c2615891c68ca302c261589068dd1f02c2615850a8dd1f02c2609851e94d33000d9d168624ad61000d9d168a246d6102c260985168dd1f02c21d950868e5b302c1e15892468cab02c1e15892684d3302c1e15852688d33000da50a861d6d6102c1e15892468ca302c1e1589068e51f02c1e15850a8e51f02c1e09852694d33000da516861cad61000da5168a1c6d6102c1e0985168e51f02c160985269cd33000da51e8614ad61000da51e8a146d6102c1609851e8e51f000da51e96086d6102ea61d950c841d702e9e158900c657b02e9e140990c657402e9e140590ca57402ea41e159084d6d02e9e1409904e59702ea41e159048d7902ea41e159084d7902e9e080590d657402ea41e099144d6d02ea41e059148d6d02ea41e099144d7902e96080590de57402ea4160991c4d6d02ea4160591c8d6d02ea4160991c4d7902ea40a0591d4d6d02e96080590e5d7402e9c16099244d6d02e9c16059248d6d02e9c16099244d7902e9c0a059254d6d02e940a05925cd6d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_16 : blocksOK 11 56 P11 P12 955 61 B12_16 = true := by decide +kernel

def B12_17 : List (ℕ × ℕ × ℕ) := [(0x806ab2a82a4aa0ab2a92ac8a554c16, 48, 0x2ea61d950c841e002c261d950a8c55102ea61d950c841df02c261d950a8c52302c261d89168c55102ea61d950c841de02c261d89168c52302c2615891e8c55402e9e25890d441dd02c2615891e8c52402e9e25950c841dd02c2259d14a8c5b502c1e1589268c55402ea61d890d441dd02c1e1589268c52402ea61d950c841dd02ea61d950c841dc02c560981269cd33004da51e8214ad6102ea61d158c841db02ea61d950c841db02ea61d950c841da02c4d95081ea252802ea61c1590c857502ea61c15908c59802ea61c0990d457502c4c1589269e11e02ea61d950084c6c02c4c15891ea611e),
  (0x806ab2a92a4aa4ab2a92ac8a154d52, 50, 0x2ea61d950c841ee02c261d95084e94a02ea61d950c841ed02c261d950a8c52502c261d89144e94a02e9609a50dc05df02c261d89168c52502e9609a50dc41ea02c2615891c4e94a02e9e09a50d405df02c2615891e8c52502e9e09a50d441ea02e9e15a50c805df000d9d168a246d3402e9e15a50c841ea02c2259d14a8c5b602ea61d158c841ec02ea61d950c841ec000da51e944a2c4602c1e1589244e94a02ea6099d0d405df02c1e1589268c52502ea6099d0d441ea02ea6159d0c805df000da5168a1c6d3402ea6159d0c841ea02ea61d950c841eb02ea61d950c805df000da51e8a146d3402ea61d950c841ea000da51e96086d3402ea61d950c805d802c661d9500a8ca302ea61d158c841e902ea61d158c841e802ea61d950c841e902ea61d950c841e802ea61d950c841e702ea61d950c841e602ea61d950c841e502ea61d158c841e402ea61d950c841e402c659d140ca286102c641d950ea093c02ea61c15908c59b02c641e1590a8d8502c641d890ea153c02e9609a50dc41e102c641e099168d8502c6415890ea1d3c02e9e09a50d441e102c64160991e8d8502e9e15a50c841e102ea61d950084caa02c661d9500a8c9302ea61d158c841e302ea61d950c841e3000da51e94a06dc702c5c15890ea253c02ea6099d0d441e102c5c16099268d8502ea6159d0c841e102ea61d950c841e202ea61d950c841e1),
  (0x806ab2a92a4aa4ab2a92ac8a554d56, 52, 0x2ea61d950c841fa02c261d95084e95702c661d950c829ee02c261d95084e92602c261d89144e95702c5609a50dc29e002c261d89144e92602e9609a50dc41f802c2615891c4e95702c5e09a50d429e002c2615891c4e92602e9e09a50d441f802c5e15a50c829e0000d9d168a066caf02e9e15a50c841f800258d1e94a06d7d02c2259d1484e9b7002251e944c9acb0002259e944c92cb0002259d1684acda6002259d168c4ac2e02c1e1589244e95702c66099d0d429e002c1e1589244e92602ea6099d0d441f802c66159d0c829e0000da5168a05ecaf02ea6159d0c841f8001d8d2694a06d7d02ea61d950c841f9001a61d1684cad7c02c661d950c829e0000da51e8a056caf02ea61d950c841f800158d269ca06d7d001261d9684cad7c000da51e9604acaf000da51e96086c2f00098d269d606d7d02c661d950c829d902c661d9500a8cab02ea61d158c841f702ea51e158084de902ea61d950c841f702ea59e150084de902ea61d950c841f6002259d144caac9f02ea61d950c841f502ea61d950084de602ea61d158c841f402c661d158ca81ef02ea61d950c841f402c661d950ca81ef02ea61d950c841f302c661d9500ca97f02c661c1590ca97702c661c15908e99c02ea41e159084d8902c661c0990d697702e9609a50dc41f102ea41e099144d8902e9609a50dc41f002c66140990de97702e9e09a50d441f102ea4160991c4d8902e9e09a50d441f002e9e15a50c841f1000d9d168a066ca002e9e15a50c841f002ea61d950084cab02ea61d950084c9802c651e1580a8de9002251e944c9aca202c659e1500a8de9002259e944c92ca2002259d16848eda9002259d168c86c9f02c5e140990e697702ea6099d0d441f102e9c16099244d8902ea6099d0d441f002ea6159d0c841f1000da5168a05eca002ea6159d0c841f002c661d9500a8de602ea61d950c841f202ea61d158c841ef02ea61d950c841f1000da51e8a056ca002ea61d950c841f002ea61d950c841ef000da51e9604aca0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_17 : blocksOK 11 56 P11 P12 955 64 B12_17 = true := by decide +kernel

def B12_18 : List (ℕ × ℕ × ℕ) := [(0x80aaaaa82a0aa8aaaaa2aa8aa2aa2a, 48, 0x2ea61d950c8420602ea61d95048c20502ea61d950c8420502ea61d950c8420402ea6159d0c8420302ea6159d048c20202ea6159d0c8420202ea61d950c8420302ea61d95048c20202ea61d950c8420202ea61d950c8420102ea61d950c8420002ea61d950c841ff02ea61d950c841fe02ea61d95048c1fd02ea61d950c841fd02ea6159d0c841fc02ea61d950c841fc02c9e15812684d4d02ea6019d0548dda02ea61d158c841fb02ea61d950c841fb02258d06809d6d5d02c8d851c256a0a102c8c1d9526a052a02c841d9526a0d2a02c8c059d269614b02c8c0595269e14b02ea61d950084cb402e8c059d254a1e1),
  (0x80aaaaa82a2aa8aa2aa2aa8aa2aa8a, 48, 0x2ea61d950c8421302ea59e15048c21202ea61d950c8421202ea61d950c8421102ea6159d0c8421002ea5961d048c20f02ea6159d0c8420f02ea61d950c8421002ea59e15048c20f02ea61d950c8420f02ea61d950c8420e02ea61d950c8420d02ea61d950c8420c02ea59e15048c20b02ea61d950c8420b02ea6159d0c8420a02ea61d950c8420a02c9d96012684d4e02ea5821d0548ddb02ea61d950c8420902ea59e150480dfb02ea61d950c805fb02c861d142698d2b02c8d9c1526a052902c861c152698d2902ea6159d0c8420802ea61d950c8420802ea59e150084cb502ea61d950c84207),
  (0x80eaa2a82a0aacaa2ab2a88ae2a454, 48, 0x2ea61d950c8421b02ea61d950c8421a02ea6159d0c8421902ea61d950c8421902ea61d950c842180258c9c542d2a11c02c9e1581244e90e02c821d95268c55402c421d95268c95402ea6019d0d449dc02ea61d158c40a0c02ea51e15808c60b02ea51e15804ca0b02ea61d950c40a0c02ea59e15008c60b02ea59e15004ca0b02ea61d950c8421702ea61d950c409fe02ea61d95008c5fd02ea61d95004c9fd02ea61d158c8421602ea61d950c8421602c8d9d14246a11402ea61d95004c8b902ea61d95008c4b702ea61d95004c8b702ea61d158c8421502ea61d950c8421502ea61d950c84214),
  (0x80eaa2a82a2aa8aaaaa2aa8aa2a4a8, 48, 0x2ea61d950c8422102ea61d950c8422002ea6159d0c8421f02ea61d950c8421f02ea61d950c8421e02ea61d950c8061802c9e15812468d0102c625811d68c9b502ea61d158c8060d02ea61d950c8060d02ea61d950c8060002c8d9d1424628e702c6259d1428c8e302ea61c15904c9bd02ea6159d0c8421d02ea61d950c8421d02ea61d95008c4ba02ea61d950c8421c),
  (0x80eaa2a92a0aa8aa2ab2a88ae2a514, 48, 0x2ea61d950c8422802ea61d950c8422702ea61d950c8422602e9e25950c40a1902e9e25950c40a1f02ea61d950c8061902c9e1581244e8bf02c9e0195268c55102c6601951e8c95102e821da50d449dd02e9e25158c40a1002ea51e15808c60f02e9d2615804ca0f02e9e25950c40a1002ea59e15008c60f02e9da615004ca0f02ea61d950c8422502e9e25950c40a0302ea61d95008c60202e9e2595004ca0202ea61d158c8422402ea61d950c8422402c9d8d14246a0d502e9e2595004c8bd02c821d95268c4b602c4225951e8c8b602ea61d158c8422302ea61d950c8422302ea61d950c84222),
  (0x80eaa2a92a0aacaa2ab2a88aa2a550, 48, 0x2ea61d950c8423002ea61d950c8422f02ea6159d0c8062702ea61d950c8062702ea61d950c8062002ea61d950c8061a02c9e1581244e94a02c661d9500a8cd202ea6019d0d485df02c661d95028c92402ea61d158c8061202ea61d158c8061102ea61d158c8422e02ea61d950c8061202ea61d950c8061102ea61d950c8422e02ea61d950c8422d02ea61d950c8060502ea61d950c8060402ea61d950c8422c02ea61d158c8422b02ea61d950c8422b02c8d9d14246a0d302ea61d95008c4be02c821d95268c4b802ea61d95004c94802ea61d158c8422a02ea61d950c8422a02ea61d950c84229)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_18 : blocksOK 11 56 P11 P12 955 67 B12_18 = true := by decide +kernel

def B12_19 : List (ℕ × ℕ × ℕ) := [(0x80eaa2a92a0aacaa2ab2a88ae2a554, 50, 0x2ea61d950c8424302c661d950c82a3002c66159d0c82a2802ea6159d0c8424202c661d950c82a2802ea61d950c8424202ea61d950c8424102c661d950c82a21002c8e9c551a60e3002c8e9c559260e3002259d1684cadb502c661d950c82a1b02ea61d950c8424002ea6159d0c8423e02ea61d950c8423f02ea61d950c8423e02c9e1581244e95702c661d95008e8bf02c66019d0d4a9e002c661d95028c95402c661d158c82a1302ea51e15808c61202ea61d158c8423d02c661d158ca823502c661d950c82a1302ea59e15008c61202ea61d950c8423d02c661d950ca823502ea61d950c8423c002259d144caaccf02ea61d950c8423b02c661d950c82a0602ea61d95008c60502ea61d950c8423a02c661d950ca823202ea61d158c8423902c661d158ca823102ea61d158c8423802ea61d950c8423902c661d950ca823102ea61d950c8423802ea61d950c8423702c8d9d14246292c02ea61c15904c9d202ea6159d0c8423602ea61d950c8423602ea61d95008c4bf02c821d95244e8b902ea61d95004c95402ea61d95004c90b02c651e15808ea12002251e944c9acd102ea61d158c8423502c659e15008ea12002259e944c92cd102ea61d950c84235002259d168c86ccf02ea61d950c8423402c661d95008ea0502ea61d950c8423302ea61d950c8423202ea61d158c8423102ea61d950c84231),
  (0x80aaa2a82a4aa4ab2a92ac8a654856, 48, 0x2ca259d1468c24502e8c5d95240a21c02e96259d0c0861d02e9e25950c0861d02ea61d950c8424502c84d9d1602a61c02c9261d94428e1d02c9a61d14428e1d02ea61d950c0861c02ca259d14428e1c02e9e144190e497602ca25811d68c5b402ca251d9468c24402ca259d1468c24402c84d811d6a61b402c98d241d60697602ca259d1428c4e202ea61c159084db402ea6159d0c8424402ea61d950c8424402ea61d950084ce202e8c5c1590a25b4),
  (0x80eaa2a82a6aa0abaa82ae8a2544a8, 48, 0x2ea61d950c8424a02ea61d950c8424902e96259d0c04a1e02e9e25950c04a1e02ea61d950c8424802ea61d950c04a1e02c6259d1428c9b802ea61d9500c498402c6259d1428c8e702ca259d1428c4e702c6259d1428c8e602ea61c15904c9bf02c6259d14288cfb02ca259d14284cfb02e96259d0c40a4502c80da51e06961c02c40da51e0a961c02e96259d0c8424702e9e25950c40a4502c80da516069e1c02c40da5160a9e1c02e9e25950c8424702e9e15a50c8424602ea61d950c40a4502c80d9d1606a61c02c40d9d160aa61c02ea61d950c8424702ea6159d0c8424602ea61d950c84246),
  (0x80eaa2a92a4aa4ab2a92ac8a254550, 48, 0x2ea61d950c8424e02ea61d950c8424d02e96259d0c0862002e9e25950c0862002ea61d950c8064902ea61d950c0862002ca259d1428c5b602c661d9500a8cfa02ea61d158c8424c02ea61d950c8424c02ea61d950c8424b02c659d140ca28ee02ca259d1428c4e402ea61c15908c5c002e8c259d144a21c02e8c25951c4a21c02ea61d950084d0002e8c1d95244a21c),
  (0x80eaa2a92a4aa4ab2a92ac8a654554, 50, 0xa269c540ed190502c661d950c82a4e02c56259d0c0aa2102e96259d0c8425602c5e25950c0aa2102e9e25950c842560026099d168c6dff02c661d950c82a4a002269c550d8ad42002269c558d0ad42002269c5590cadbe02c661d950c0aa2102ea61d950c84256001e09a5168c6dff02ea61d950c84255001609a51e8c6dff02ca259d1404e9b702c661d9500a8d0102ea61d158c8425402ea51e158084e4c02ea61d950c8425402ea59e150084e4c02ea61d950c8425302ea61d950c8425202ea61d950084e4b02ea61d158c8425102ea61d950c8425102ea61d950c8425002c98d241d60698402ca259d1404e8e502c661c15908e9c102ca259d14284cf002ca15a51c04ea450098c269c5612e3f02ca15a51c284e4702ca1da51404ea450098c26945e12e3f02ca1da514284e4702e9e15a50c8424f02ea61d950084d0102ea61d950084cf602c651e1580a8e4c02c659e1500a8e4c02ca259d1404ea450098c1e946612e3f02ca259d14284e4702ea6159d0c8424f02c661d9500a8e4b02ea61d950c8424f)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_19 : blocksOK 11 56 P11 P12 955 73 B12_19 = true := by decide +kernel

def B12_20 : List (ℕ × ℕ × ℕ) := [(0x80aaaaaa2a0aa8aaaaa2aa8a2a8a2a, 48, 0x2ea61d950c8425d02ea61d950c8425c02ea61d950c8425b02ea61d950c8425a02e96259d0c04a0502e96259d0c0862c02c96259d0428e3202e9e25950c04a0502e9e25950c0862c02c9e25950428e3202e9e15a50c8425902ea61d950c0864b000da51e94a06d0202ea61d950c04a0502ea61d950c0862c02ca61d950428e3202ea6159d0c8425902ea61d950c8425902ea61d950c085e602ca61d95028c52102ea61d158c8425802ea61d950c8425802ea61d950c8425702c85a51c0d6a0a402ca41d950ea053b02ca61c159068d8502c84259d0e9614c02c8425950e9e14c02ea61d95008c54502c841d950ea614c),
  (0x80aaaaaa2a2aa8aa2aa2aa8a2a8a8a, 48, 0x2ea61d950c8426302ea61d950c8426200da61c9406ad12502ea61d950c8426102e96259d0c04a1202e96259d0c0862e02c95a61d0428e3502e9e25950c04a1202e9e25950c0862e02c9da6150428e3502e9e15a50c8426002ea61d950c0864c02ea61d950c04a1202ea61d950c0862e02ca59e150428e3502ea6159d0c8426002ea61d950c8426002ea61d950c085e902ca61d95028c52202ea61d950c8425f02ea61d950c8425e02ea61d950c8065802ca59d140ea053c02ca59c150ea053900da61c14852ad5b02e8da41d049620702e8da415049e20702ea61d95008c54602e8d9c1504a6207),
  (0x80eaa2ab2a0aacaa2ab2a88a2a8550, 48, 0x2ea61d950c8426500da49c542d2a11602e96259d0c04a2f02e9e25950c04a2f02ea61d950c04a4d02ea61d950c04a2f02ea61d950c049ed02c661d95028c92502ca61d95028c52502ca61d950068d1100d261c9442ad92502ea61d158c8066102ea61d158c40a6100da61c9442ad12502ea61d950c8066102ea61d950c40a6100da61c94412ad1102ea61d950c40a5b02ea61d950c8065a02ea61d950c40a5a00ea61c946d8125a00ea61c946d01a5a02ca59d140c6a11602ea61d95004c94902c661d950288d1202ca61d950284d1200d261c94429ad1200da61c944292d1200ea61c946c11a4d02ea61d950c84264),
  (0x80eaa2ab2a0aacaa2ab2a88a6a8554, 50, 0x2ea61d950c8427002c661d950c82a6502c56259d0c0aa3002e96259d0c8426f02c5e25950c0aa3002e9e25950c8426f02e9e15a50c8426e02c661d950c0aa4e002ca69c5518e0e4002ca69c5590e0e4000da51e9486e07102c661d950c0aa3002ea61d950c8426f02ea6159d0c8426e002ca69c56190cf002ea61d950c8426e02c661d950c0a9ee02c661d95008e94a02ca61d95004e92602ca61d950068d1302c661d158c82a6302ea61d158c8066202ea61d158c8426d02ea51e15804ca6102c661d950c82a6302ea61d950c8066202ea61d950c8426d02ea59e15004ca6102ea61d950c8426c002259d144caad1002ea61d950c8426b02c661d950c82a5d02ea61d950c8065c02ea61d950c8426a02ea61d95004ca5a02ea61d158c8426902c661d158ca826602ea61d158c8426802ea61d950c8426902c661d950ca826602ea61d950c8426802ea61d950c8426702ca59d140c6293d02ea61c15904c9d302e8c259d148623402e8c25951c8623402ea61d95008c54a02ea61d95004c90d02ca61d950284d1302ea61d95004c90c02c661d158c82a62002251e944c9ad1202c651e15828ca6102c661d950c82a62002259e944c92d1202c659e15028ca61000a59d1684ee1c0002259d168c86d1002e8c1d95248623402c661d950c82a5c02ca61d950284e6402c661d95028ca5a02ea61d158c8426602ea61d950c84266)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_20 : blocksOK 11 56 P11 P12 955 78 B12_20 = true := by decide +kernel

def B12_21 : List (ℕ × ℕ × ℕ) := [(0x80aaa2aa2a0aacaa2ab2a88aeaa054, 48, 0x2ea61d950c8427502e8c5d95240a23402e96259d0c0863602e9e25950c0863602c2259d1448ea450018c5e94a612e3f002251e948c5acda002259e948c52cda02ea61d950c08634001a61e948c52e3f02c9e144190e697702ea6019d0d485f102ca61d950284d2b02ca61d95028c54c02ea61d158c8427402e8c5d15a4a027102e821c558ca520702ea61d950c8427402e8c5d9524a027102e821c550ca5a0702ea61d950c8427302e8c419d254a1f102ea61d950c8427202c8c5d9502a614c02ea61d158c8427102ea61d950c8427102ea61d9500c858602ea61d950084d2b02ea61d95008c54c02e8c5d9500a610602c821c558ea520702c821c550ea5a0702e8c5d9500a614c),
  (0x80aaaaaa2a0aa8aa2aa2aa8aaaaa0a, 48, 0x2ea61d950c8427b02ea61d950c8427a02ea61d950c0866902ea61d950c0866802e96259d0c0863902e96259d0c0863802e96259d0c8427902e9e25950c0863902e9e25950c0863802e9e25950c8427902242e848d1d5a1602ea61d950c08651002251e948c5ad030005269c95a0ed0402ea61d950c0863902ea61d950c0863802ea61d950c84279021c2e848d255a1602142e848d25da1602ea61d950c085f402ca61d950284d3e02ea61d950c8427802ea61d950c8427702ea61d950c8427602ea61d9500c858902ea61d9410c858802ea61d941084dd002e96259d0c8067102e9e25950c8067102ea61d950084d3e02ea61d950c80671),
  (0x80aaaaaa2a0aa8aaaaa2aa8aaaaa2a, 50, 0x2ea61d950c8428202ca61d95040ea5d02ca61d950c06a5d02ea61d950408e6a02c96259d0c06a0602e96259d0c0863a02e96259d0408e3a02e96259d0c8428102c9e25950c06a0602e9e25950c0863a02e9e25950408e3a02e9e25950c8428102242e8c85951dfe0025851e9608edea00258d1e96086dea02ea61d950408e52002251e948d86d36002259e948d06d36002259d16886cdc2002259d16848ec45002259d168c86c4502ca61d950c06a0602ea61d950c0863a02ea61d950408e3a02ea61d950c84281021c2e8c859525fe001d85269608edea001d8d2696086dea02ea61d950c8428002142e8c859d25fe001585269e08edea00158d269e086dea000da51e96086c9a02ea61d950408df502ca61d950284d4d02ea61d158c8427f02ea51e158084e5e02ea61d950c8427f02ea59e150084e5e02ea61d950c8427e02ea61d950c8427d02ea61d950084e5702ea61d158480e7602ea61d950480e7602ca61d9500c697102ea61c1590c858902ea61c159048d8902ea61c159084dcf02e8c05a515ca1f102e96259d0c8067202e96259d0480e7202e8c05a51d4a1f102e9e25950c8067202e9e25950480e7202e9e15a50c8427c02ea61d950084d4d02ea61d950084d0802ca51e158284e5e02ca59e150284e5e002259d1688c6dc602e8c059d254a1f102ea61d950c8067202ea61d950480e7202ea6159d0c8427c02ca61d950284e5702ea61d950c8427c),
  (0x80aaaaaa2a2aa8aa2aa2a88aaaaa82, 48, 0x2ea61d950c84285006259d140e8ad5c02ea61d950c0866c02ea61d950c0866b02e96259d0c0863c02e96259d0c0863b02e96259d0c8428402e9e25950c0863c02e9e25950c0863b02e9e25950c8428402e9e15a50c8428302ea61d950c0865302ea61d950c0863c02ea61d950c0863b02ea61d950c8428402ea6159d0c84283001a61e948c52e5502ea61d950c8428302ea61d950c085f602ca59d160284d3f02ea51d960084e7802ea59d160084e7802ea61d950c8067e02ea61d9500c858a006259d140e8ad5a02ea59d160084dd102e96259d0c8067302e9e25950c8067302ea59d160084d3f02ea61d950c80673)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_21 : blocksOK 11 56 P11 P12 955 82 B12_21 = true := by decide +kernel

def B12_22 : List (ℕ × ℕ × ℕ) := [(0x80aaaaaa2a2aa8aa2aa2aa8aaaaa8a, 50, 0x2ea61d950c8428a02ca59e15040ea6302ca61d950c06a6302ea59e150408e6d02c96259d0c06a1302e96259d0c0863d02e95a61d0408e3d02e96259d0c8428902c9e25950c06a1302e9e25950c0863d02e9da6150408e3d02e9e25950c8428902e9e15a50c84288000d069c9625ad5300050e9c95a62d5302ea59e150408e5400205269c8d5ac87002259e948d06d52002259d16884ed8202ca61d950c06a1302ea61d950c0863d02ea59e150408e3d02ea61d950c8428902ea6159d0c84288000d06a4961dad5300050ea4959e2d53001a61e94850ed52001a61d1688c6d8202ea61d950c84288000d06a49e15ad5300050ea49d962d53000da51e96086c8602ea59e150408df702ca59e150284d4e02ea61d950c8428702ea51e15808c65f02ea59e150480e7f02ea59e150084e5802ea59d160480e7802ea61d950c8067f02ea61d95008c65802ea61d158c8067802ea59e150480e7702ca61d9500c697702ea61d9410c858a02ea59e141048d8a02ea41d961084dd002e95a61d0480e7402e8c259d14a067102e84261d1498e7102e9da6150480e7402e8c25951ca067102e8426151c98e7102e9e15a50c8428602ea59e150084d4e02ea59e150084d0902ca51d960284e5f02ca59e150284e5802ea59e150480e7402e8c1d9524a067102e841e152498e7102ea6159d0c8428602ca61d95028c65802ea61d950c84286),
  (0x80eaa2aa2a0aa8aa2ab2a88aeaa414, 48, 0x2ea61d950c8428b02ea61d950c0866e02e96259d0c0864102e9e25950c0863e005601a51e8cadff02ea61d950c0863e02ca61d950c069e0004da51e82096caf02ca61d95028c55102ca61d95028c54f02ea61d158c80688004d82a49e152d5302ea51e15808c66002ea61d950c80688004d02a49e15ad5302ea59e15008c66002ea61d950c8068302146e8c819d25fe005581269e08edea02ea61d95008c65902146e808da5d21602146e808d25da1602ea61d9500c858c02ea61d95008c55102ea61d95008c54f02ea61d95008c50a02ca51e15828c66002ca59e15028c66002ca61d95028c659),
  (0x80eaa2aa2a0aa8aaaaa2aa8aaaa428, 48, 0x6ea49c1610d8ec006c269c96190cf002e96259d0c0863f02e9e25950c0863f02ea61d950c0865502ea61d950c0863f02ea61d950c085f902ca61d95028c552005261e94818ed52005a61e94810ed52005a61e948c12e5502ea61d950c8068002c5a51c1608e8ec02ea61c1590c858b02c4259d16288cf000596269c8c12e3f0059e26948c12e3f02ea61d95008c552005a61e948c12e3f),
  (0x80eaa2aa2a0aacaa2ab2a88aaaa450, 48, 0x2ea61d950c8428c02ea61d950c0866f02e96259d0c0864202e9e25950c0864202ea61d950c0865602ea61d950c0864002c5e1581248e926005d8d2682096df802c421d9524a8cd202ca61d95028c55302ea51e158048e3d02ea61d158c8068902ea51e158048e2e02ea59e150048e3d02ea61d950c8068902ea59e150048e2e02ea61d950c8068402ea61d950048e3a02ea61d950c8068102ea61d950048e2c02ea61d158c8067902ea61d950c8067902ea61d9500c858d02c421d952688cd202ea61d95008c55302c421d952688cc002ca51e158068e2e02ca59e150068e2e02ca61d950068e2c),
  (0x80eaa2ab2a0aacaa2ab2a88aeaa554, 52, 0x2ea61d950c8428e02ca61d950c06a7002c96259d0c06a4302c96259d0c42a8c02c9e25950c06a4302c9e25950c42a8c02c9e15a50c42a8b002e8c9c5526191f002269c944ed1905002e8ca45d161836002e8ca45d961036002ea49c5520d8fc002e8ca45d95200702ca61d950c06a4302ca61d950c42a8c02ca6159d0c42a8b002e8ca4551e191f002ea49c5610d8ec002e8ca45d15a03d02ca61d950c42a8b002e8ca45d16191f002e8ca45d95203d000da51e96086c6402ca61d950c069fa02c661d95008e95702ca61d95004e95702ca61d95004e90e02ca61d158c42a8a02ca51e15804ea6302c651e15808ea63002251c944ead92502ca61d950c42a8a02ca59e15004ea6302c659e15008ea63002259c944ead12502ca61d950c42a85002259d144e8ad5c002259d148e86d5c002259d148c6ac4e02ca61d950c42a8202ca61d95004ea5d02c661d95008ea5d02ea61d95004ca5b02ca61d158c42a7b02ea61d158c8067a02ea61d158c40a7a001a61d1484ead8502ca61d950c42a7b02ea61d950c8067a02ea61d950c40a7a001261d9484ead8502ea61d950c8428d002a61d9504cad88002a61d9508c6d8802ca61d9500c698f02ca61c15904e9d402c96259d0c42a750026ac8c551e1a7602c9e25950c42a750026ac8c5d161a760026ac9c560d1a5702ea61d95004c95702ea61d95004c90e02ea61d95008c50e0010ea49c6d6187d02c651e15828ca63002251e944cad925002251e948c6d925002251e948c5ac4f02c659e15028ca63002259e944cad125002259e948c6d125002259e948c52c4f002269c946cd18e8002259d168c86d5c002259d168c4ac4e002259d168c86c4e02ca61d950c42a75001eac8c65161a76001eaca4560d1a5702c661d95028ca5d02ca61d95004ea5b02c661d95008ea5b0018ea49c6d5209402ca61d158c42a7a001a61d1684cad85001a61d1688c6d850016aca45e0d1a5702ca61d950c42a7a001261d9684cad85001261d9688c6d85000a61d9528c6d88)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_22 : blocksOK 11 56 P11 P12 955 86 B12_22 = true := by decide +kernel

def B12_23 : List (ℕ × ℕ × ℕ) := [(0x802abaa82aeaa0abaa82aeaa1542a8, 50, 0x2ea61d950c8429102c261d9504ca86a02c261d9508c686a02c261d9504e88a502c261d950c8686a02c261d9504a8ca502c261d950868ca502c261d950a84d2e02c261d8d148686a02c261d8d04a94a502c261d8d08694a502c261d8d0a8552e02c261d890c694a502c261d890e8552e02c261d850e8952e0026158d0869edb102c26158d1c8686a02c26158d04a9ca502c26158d0869ca502c26158d0a85d2e02c2615890c69ca502c2615890e85d2e02c2615850e89d2e00261d8d08696db102c260d891469ca502c260d891685d2e02c260d851689d2e00261d950868edb102c260985168dd2e00261d950c68adb100261d950ca86db102c21d950ca865b902ea51e158c8429002ea59e150c8429002c1e158d248686a02c1e158d04aa4a502c1e158d086a4a502c1e158d0a8652e02c1e15890c6a4a502c1e15890e8652e02c1e15850e8a52e001e258d08696db102c1e0d89146a4a502c1e0d89168652e02c1e0d85168a52e001e25950868edb102c1e0985168e52e001e25950c68adb1001e25950ca86db102ea61d950c8429002c160d891c6a4a502c160d891e8652e02c160d851e8a52e0016259d0868edb102c1609851e8e52e0016259d0c68adb10016259d0ca86db102c0e09851e9652e000e259d1468adb1000e259d14a86db1000a259d14e86db102ea61d950c8428f02e9d160d80865d702e9d960d00865d702e9e158d00865d702e9e158d00865a002e9c160d904a57b02e9c160d908657b02e9c160d908656e02e9c160990c657b02e9c160990c656e02e9c160590ca56e02ea41e159084d6c02e9c0e09914657b02e9c0e09914656e02e9c0e05914a56e02ea41e0d908556c02e9c0a05914e56e02ea41e0990c556c02ea41e0590c956c02e940e0991c657b02e940e0991c656e02e940e0591ca56e02ea4160d9085d6c02e940a0591ce56e02ea4160990c5d6c02ea4160590c9d6c02e8c0a0591d656e02ea40e099145d6c02ea40e059149d6c02ea40a05914dd6c02e9e158d008646202e940e099245d7b02e940e099245d6e02e940e059249d6e02e9c160d908656c02e940a05924dd6e02e9c160990c656c02e9c160590ca56c02e8c0a059255d6e02e9c0e09914656c02e9c0e05914a56c02e9c0a05914e56c02e8c0a05925d56e02e940e0991c656c02e940e0591ca56c02e940a0591ce56c02e8c0a0591d656c),
  (0x806ab2a82acaa0ab2a82acaa554c06, 48, 0x2ea61d950c84292004a259d1428ecad004e259d1428acad004e259d1428ac9902c261d8d14a84af02c261d8d168853402c261d89168c53402c26158d1ca84af02c26158d1e8853402c2615891e8c53402c260d891e94537004e01a51d68ad8e02c1e158d24a84af02c1e158d268853402c1e1589268c53402c1e0d89269453702c160d89269c53702c4e09811e9652e004e259d1428adb10042259e950cad610042251e958cad610041a51e960cad6102ea61d9500c85a2004a259d1428ecac004e259d1428acac02ea41e1590c856f02ea41e0d914857d02ea4160d91c857d02ea61d9500c846302e9c160d924857d),
  (0x806ab2a82acaa0abaa82aeaa154428, 48, 0x2ea61d950c8429302c261d9508e84b002c261d950ca84b002c261d950e8853602c261d8d14a84b002c261d8d168853602c261d89168c53602c26158d1ca84b002c26158d1e8853602c2615891e8c53602c260d891e9453602c2259d14e885ba02c1e158d24a84b002c1e158d268853602c1e1589268c53602c1e0d89269453602c160d89269c53602ea61d950c8069002c5a51c160ca81402ea61c1590c85a402c4259d160e884002ea41e15908c57c02c4259d160a8c4002ea41e1590c857c02c4259d16288cde02c4259d0e0a944002ea41e0d914857c02c4259d0e2894de02c4259d0a28d4de02c425950e0a9c4002ea4160d91c857c02c425950e289cde02c425950a28dcde02c4258d0a295cde02c41d950e0aa44002e9c160d924857c02c41d950e28a4de02c41d950a28e4de02c41d8d0a2964de02c4158d0a29e4de)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_23 : blocksOK 11 56 P11 P12 955 91 B12_23 = true := by decide +kernel

def B12_24 : List (ℕ × ℕ × ℕ) := [(0x806ab2a92acaa4ab2a92acaa554d56, 54, 0x2ea61d950c8429a02c261d9508c68b102c261d950c868b102c261d950c4a93802c261d8d14868b102c261d8d144a93802c261d89144e93802c560d8925c2a9202c26158d1c868b102c26158d1c4a93802c2615891c4e93802c5e0d892542a9202c260d891c5693802c5e158924c2a9202c5e158d2482a9200261d950ca86da202c2259d14c4a9bb02c651e158c82a9302c659e150c82a93002259d1684cada402c1e158d24868b102c1e158d244a93802c1e1589244e93802c660d891d42a9202c1e0d89245693802c6615891cc2a9202c66158d1c82a92001e25950ca86da202c661d950c82a93001a61d1684cada402c160d89245e93802c661d8914c2a9202c661d8d1482a920016259d0ca86da2001261d9684cada402c661d950c82a92000e259d14a86da2000a259d14e86da202ea61d950c8429902c661d950c82a9102c661d9500ca86a02c651e1580ca9d902ea51e1580c85d802c659e1500ca9d902ea59e1500c85d802ea59d160c8429802c659d160ca829502c661d9500ca9d902ea61d9500c85d802ea61d158c8429802c661d158ca829502ea61d950c8429802c661d950ca829502ea61d950c84297002a61d9504cad9f02c661d9500ca9a502c641e15908e97f02c641e1590ca97f02c641e1590ca97102c641e0d914a97f02c641e0d914a97102c641e09914e97102e960d8925c429402c64160d91ca97f02c64160d91ca97102c64160991ce97102e9e0d89254429402c640e0991d697102e9e158924c429402e9e158d248429400261d950ca86d9d02ea61d9500c846a02c661d9500ca86902c651e1580ca9d802ea51e158c8429602c659e1500ca9d802ea59e150c8429602ea59d160c84295002259d1684cad9e02c5c160d924a97f02c5c160d924a97102c5c1609924e97102ea60d891d4429402c5c0e09925697102ea615891cc429402ea6158d1c84294001e25950ca86d9d02c661d9500ca9d802ea61d950c8429602ea61d158c84295001a61d1684cad9e02c540e09925e97102ea61d8914c429402ea61d8d14842940016259d0ca86d9d02ea61d950c84295001261d9684cad9e02ea61d950c84294000e259d14a86d9d000a259d14e86d9d000661d9528cad9f),
  (0x80eaa2a92a8aa4aa2ab2a8aae0a554, 50, 0x2ea61d950c842a402c261d950c4a95802c261d8d144a95802ea61d950c842a302c26158d1c4a95902e9e258d14842a202e9e25950c842a202c2259d14c4a9c202ea51e158c842a102ea59e150c842a102c1e158d244a95902ea61d8d14842a202ea61d950c842a202ea61d950c842a102ea61d950c842a002c960d81245e93802c661d9500ca876008e259d0286d69202c661d9500e88af02c651e1580ca9e002ea51e1580c85df02ea51e1580c49f802ea51e1580c49ea02c659e1500ca9e002ea59e1500c85df02ea59e1500c49f802ea59e1500c49ea02ea59d160c8429f02c659d160ca829b009602a45d8d2e8102c661d9500ca9e002ea61d9500c85df02ea61d9500c49f802ea61d9500c49ea02ea61d158c8429f02c661d158ca829b009582a45e0d2e8102ea61d950c8429f02c661d950ca829b009502a45e0dae8102ea61d950c8429e02c661d9500ca9a802ea41e1590c498c02ea41e0d914498c02ea61d950c8429d02ea4160d91c498d02ea61d9500c847602c661d9500ca87502ea61d9500c48af02ea61d9500c489a02c651e1580ca9df02ea51e158c8429c02c651e1580e89ea02c659e1500ca9df02ea59e150c8429c02c659e1500e89ea02ea59d160c8429b02e9c160d924498d02c661d9500ca9df02ea61d950c8429c02c661d9500e89ea02ea61d158c8429b02ea61d950c8429b)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_24 : blocksOK 11 56 P11 P12 955 94 B12_24 = true := by decide +kernel

def B12_25 : List (ℕ × ℕ × ℕ) := [(0x80eaa2a92a8aa4ab2a92acaa614554, 50, 0xaea45c160d184800ac269c5610d8e500ac269c4e1158e502e960da51c04aa100ac26944e11d8e502e9e0da51404aa102e9e15a50c04aa102c2259d14c4a9c4009261e944ed82a5009a61e944ed02a500ac1e944e1258e502ea60d9d1404aa102ea6159d0c04aa1009a61e944ed02a602ea61d950c04aa1009261e944c2da9302c661d9500e88b0009261e9440dacb002ea51e1580c49ec009a61e9440d2cb002ea59e1500c49ec0082269c54d2d9c402c661d950ca82a5009a61e9440d2c9b02ea61d9500c49f902ea61d9500c49eb009a61e9440d2deb009261e9440dadeb02ea61d950c842a602c9a51c160c6848009261c1684ed9a702c8259d1604e8e502ea41e1590c498b02c8259d0e0568e502ea41e0d914498b009960ea45c12ea102c825950e05e8e502ea4160d91c498b0099e0ea45412ea10099e16a44c12ea102ea61d9500c48b002ea61d9500c489b009a69e1440d2dec009269e1440dadec02ea61d950c842a502c81d950e0668e502e9c160d924498b009a60e9c5412ea1009a6169c4c12ea102c661d9500e89eb009a61e944c12ea1),
  (0x80aaa2aa2a8aa8aa2aa2aaaaaaa80a, 48, 0x2ea61d950c842a7004a61d9680ed19b02c261d950c8694302c261d950e8855b02c261d8d148694302c261d8d168855b005160da69c0ae9b02c26158d1c8694302c26158d1e8855b0051e0da6940ae9b0051e15a68c0ae9b02c2259d14e885c7005269e158c0aea502c1e158d248694302c1e158d268855b005260d9e940ae9b00526159e8c0ae9b005261d968c0ae9b005261d968c0ae95004a61d9680d2ca8005261d9680cac9f0042259e94d0adc7005259e1680cadef005261d9680cadef02ca61d9500c699b005261d9428cadac004261d968d0ad5b004261d8e950ad5b00426158e9d0ad5b02ea61d9500c849f0041e158ea50ad5b),
  (0x80aaa2aa2a8aa8aa2ab2a8aaeaa014, 48, 0x56aca41d8d227d02c261d950e8855d02c261d8d168855d02e960da51c0869d02c26158d1e8855e02c2259d14c869bf02c2259d14e885c6002251e948c5aea1002259e948c52ea102c1e158d268855e001a61e948c52ea102c944e01925e9710056259d0288ee9402ca61d9500e84a102ca61d9500e84a002ea51e1580c85f102ea51e1580c85f002ea51e1580c85e102ea59e1500c85f102ea59e1500c85f002ea59e1500c85e102ea59d160c842a802ea61d9500c85f102ea61d9500c85f002ea61d9500c85e102ea61d158c842a802ea61d950c842a802ea61d9500c85ae02ea61d9500c84a102ea61d9500c84a002ea61d9500c849202ca51e1580e85e102ca59e1500e85e102ca61d9500e85e1),
  (0x80aaa2aa2a8aa8aaaaa2aaaaaaa028, 48, 0x2c261d9504ca9ed005269c942ce186002c261d950c86949005a41e94ad0e10702c261d8d1486949005a41e8cad16107005960ea49c12e9c02c26158d1c86949005a4168cad1e1070059e0ea49412e9c0059e16a48c12e9c02c2259d14e885c902c1e158d24869490059c168cad26107005a60e9c9412e9c005a6169c8c12e9c005a61e948c12e9c02ea61d950c0869602ca61d9500e84a2005261e9480daca2005a61e9480d2ca20042269c94d92dc902ea61d9500c85f202ca59d1404e286002ea61c1590c85ad02ea41d95048e10702ea41d8d049610702ea4158d049e10702ea61d9500c84a202e9c158d04a6107),
  (0x80aaaaaa2a8aa8aa2aa2a8aaaaaa02, 48, 0x2ea61d950c842a9006a61d9500cadb0004261d950e8ad5f02c261d950e8855a004261d8d168ad5f02c261d8d168855a006960da51c0ae9e00426158d1e8ad5f02c26158d1e8855a0069e0da5140ae9e0069e15a50c0ae9e0042259d14e8adca006a61d9500cac96006a51e158c0aea6006a59e150c0aea60041e158d268ad5f02c1e158d268855a006a60d9d140ae9e006a6159d0c0ae9e006a61d950c0aea6006a61d950c0ae9e006a61d950c0ae97004a61d9500eaca6006a51e1580cadf3006a59e1500cadf3006a61d9500cadf302ea61d9500c85b0006a61d9500cadaf004261d950e8ad5a004261d8d168ad5a00426158d1e8ad5a006a61d9500caca602ea61d9500c84960041e158d268ad5a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_25 : blocksOK 11 56 P11 P12 955 96 B12_25 = true := by decide +kernel

def B12_26 : List (ℕ × ℕ × ℕ) := [(0x80aaaaaa2a8aa8aa2aa2aaaaaaaa0a, 50, 0x2ea61d950c842ac005261d940caeaa702c261d950c8694402c261d950e8855c02c261d8d148694402c261d8d168855c02e960da51c0869f002506948e1dae8102c26158d1c8694402c26158d1e8855c02e9e0da5140869f0025069c8e15ae8102e9e15a50c0869f0025069c960dae8100051e948e25ad3702c2259d14e885c80005269c94dae1c4002251e9484dac9b001259e9484e2deb0005269c958e2c4702c1e158d248694402c1e158d268855c02ea60d9d140869f001d06a48e15ae8102ea6159d0c0869f001d06a4960dae81000526948e1dad37001261e9484dadeb0005269c960dac4702ea61d950c0869f001506a49e0dae810005269c8e15ad370005269c960dad3702ea61d950c0869802ca61d9500e84a902ea51e1580c85f602ea51e1580c85e702ea59e1500c85f402ea59e1500c85e402ea59e150c842ab02ea61d9500c85f402ea61d9500c85e402ea61d950c842ab02ea61d950c842aa02ca61d9500c699c02ea61d9410c85b002ea41e1590c858a02ea41e1590c858802ea41e0d914858a02ea41e0d914858802e960da51c806a802ea4160d91c858a02ea4160d91c858802e9e0da514806a802e9e15a50c806a802ea61d9500c84a902ea61d9500c849702ca51e1580e85e70005269c94e1adc902ca59e1500e85e402e9c160d924858a02e9c160d924858802ea60d9d14806a802ea6159d0c806a802ca61d9500e85e402ea61d950c806a8),
  (0x80eaa2ab2a8aacaa2ab2a8aaeaa554, 54, 0x2ea61d950c842ad02c261d950c8696202c261d8d148696202c960da51c06aa402c26158d1c8696202c9e0da51406aa402c9e15a50c06aa4002e9c944da5212e02c2259d14c869cb002ea49c550da048002ea49c558d2048002ea49c558d200a02c1e158d248696202ca60d9d1406aa402ca6159d0c06aa4002ea4944d9d212e002ea49c560d1848002ea49c560d180a02ca61d950c06aa4002ea49c4d95212e002ea49c560d900a002ea49c558d212e002ea49c558d200102ca61d950c06a9a02c661d9500ca8b102ca61d9500c68b102ca61d9500c689d02ca51e1580c69fa02ca51e1580c69ee02c651e1580ca9ee02ea51e1580c49ed02ca59e1500c69fa02ca59e1500c69ee02c659e1500ca9ee02ea59e1500c49ed02ca59d160c42aac02c659d160c82aa702ca59d160c42aa7002a59d1484ee19b02ca61d9500c69fa02ca61d9500c69ee02c661d9500ca9ee02ea61d9500c49ed02ca61d158c42aac02c661d158c82aa702ca61d158c42aa7002a61d1484ed99b02ca61d950c42aac02c661d950c82aa702ca61d950c42aa7002a61d9484ed19b02ca61d950c42aa9002a61d9504cadb0002a61d9508c6db0002a61d9508c6d9102ca61d9500c69b202ca41e1590c698f02ca41e0d914698f0026ac944d9d227d02ca4160d91c698f0026ac9c4d95227d0026ac9c558d227d0026ac9c54d9216c02ea61d9500c48b102ea61d9500c489d02ea61d9500c849d02ca61d9500c689c02c651e1580e89ee02ca51e1580c69ed02c651e1580ca9ed001a69c946cd206002c659e1500e89ee02ca59e1500c69ed02c659e1500ca9ed001269c946cda06002ea59d160c40aa7000a59d1684ee19b000659d1688ee19b002269c946cd185a02c9c160d924698f001eaca44d95227d001eaca4558d227d001eaca454d9216c02c661d9500e89ee02ca61d9500c69ed02c661d9500ca9ed001269c946ce186002ea61d158c40aa7000a61d1684ed99b000661d1688ed99b001a69c946cd205a0016aca45d8d227d0016aca45cd9216c02ea61d950c40aa7000a61d9684ed19b000661d9688ed19b001269c946cda05a000eaca45d59216c000a61d9528c6db0000a61d9528c6d91000661d9528cad91)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_26 : blocksOK 11 56 P11 P12 955 101 B12_26 = true := by decide +kernel

def B12_27 : List (ℕ × ℕ × ℕ) := [(0x81ea82a82a6aa0abaa82af0a2544a8, 48, 0x2ea61d950c842af02aca05810dd664802c6259d1428c9c502ea61d950c842ae02cda51c1628490502c6259d140e88cb02ca259d140e84cb02cc259d160868c302ea61c15904c9c202c6259d14288d0402ca259d14284d0402c615a51c0e8a2102ca15a51c0e862002c615a51c0e8a2002ca15a51c284e5602c61da5140e8a2102ca1da5140e862002c61da5140e8a2002ca1da514284e5602a40d89061d6e1802c6259d140e8a2102ca259d140e862002c6259d140e8a2002ca259d14284e56029c0d8906256e1802940d890625ee18),
  (0x81ea82a92a4aa4ab2a92ad0a254550, 48, 0xeea45c161908f102c661d950c82aaf02ca259d1404e9c402c661d9500a8d0300d269c56018ad4200da69c56010ad4202ea61d950c842b102ea61d950084e5502ea61d950c842b002cda51c162848f402ca259d140c68c902c661c15908e9c302ca15a51c0c6a1e02ca1da5140c6a1e02ea61d950084d0302ca259d140c6a1e),
  (0x81aa8aaa2a0ab8a82ae2a3146a8a0e, 48, 0x2ea61d950c842b602ea61d950c842b502ea6159d0c842b402ea61d950c842b400104de94a61ae180005269c94eda21e02ea61d950c842b302cde1581248694402ca61d9500e84d802ea6019d14c869f02ca61d950284d4102ea51e1580c863c02ea51e1580c862d02ea51e158084e8402ea59e1500c863902ea59e1500c862b02ea59e150084e7902ea59e150c842b202ea61d9500c863902ea61d9500c862b02ea61d950084e7902ea61d950c842b2019cee848125623702ea61d950084dd202ea61d9500c84d802cc21d9526884c102ea61d950084d4102ca51e1580e862d02ca59e1500e862b02ca61d9500e862b),
  (0x81ea82ab2a0abca82af2a1142a8550, 48, 0x2ea61d950c842b9002ea49c54d9224802cde1581248696202c661d9500ca8dd02ca61d9500c68dd02cc21d9524868c602ca6019d14c6aa402c661d95008e95902ca61d95004e95902ca61d950068d1c02ca51e1580c6a4302ca51e1580c6a3002c651e1580caa3002ea51e1580c4a2f02ca51e15804ea8c02ea51e158048e6f02ea51e158084e6f02ca59e1500c6a4302ca59e1500c6a3002c659e1500caa3002ea59e1500c4a2f02ca59e15004ea8c02ea59e150048e6f02ea59e150084e6f02ca59d160c42ab602ea59d160c806b502ea59d160c40ab502ea59d160c842b802ca61d9500c6a4302ca61d9500c6a3002c661d9500caa3002ea61d9500c4a2f02ca61d95004ea8c02ea61d950048e6f02ea61d950084e6f02ca61d158c42ab602ea61d158c806b502ea61d158c40ab502ea61d158c842b802ca61d950c42ab602ea61d950c806b502ea61d950c40ab502ea61d950c842b802ea61d950c842b702ea61d9500c48dd02cc21d9526848c602cc21d9526884c602cc21d9524868c202ea61d95004c95902ea61d950048d1c02ea61d950084d1c02c651e1580e8a3002ca51e1580c6a2f02c651e1580caa2f02ca51e158284e6f02c659e1500e8a3002ca59e1500c6a2f02c659e1500caa2f02ca59e150284e6f02ca59d160c42ab502c661d9500e8a3002ca61d9500c6a2f02c661d9500caa2f02ca61d950284e6f02ca61d158c42ab502ca61d950c42ab5),
  (0x81aa82a82acaa0ab2a92ad2a654816, 48, 0x2ea61d950c842ba02ce15a51c2886b102a60d89006dd4f80296018d086de64d0294420d8925ee180294420d09a5ee180294418d0a25ee1802ca259d14284dc1004e259d02896d1802ea51e1580c864602ea59e1500c864602ea61d9500c864602ea61d9500c85c802ca259d1428c4ff02ce259d142884ff02ce15a51c28865302ce1da51428865102ea61d9500c84ef02ce259d14288651)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_27 : blocksOK 11 56 P11 P12 955 103 B12_27 = true := by decide +kernel

def B12_28 : List (ℕ × ℕ × ℕ) := [(0x81aa8aa82acaa0ab2a82ad2a654a06, 48, 0x2ea61d950c842bc004e259d1428acf5004e15a51c28aeb0004e1da51428aeb002ea61d950c842bb006a61d9500cacf1006a51e1580caeae006a59e1500caeae004e259d1428aeb0006a61d9500caeae004e259d1428adcd006a61d9500cadca004a259d1428ecfd004e259d1428acfd02ce259d142884f5004e15a51c28ae50004e1da51428ae5002ea61d9500c84f1004e259d1428ae50),
  (0x81ea82a82aeaa0abaa82af2a2544a8, 50, 0x2ace09851d426bb002ce0985165e8f1002ce09851e568f1029e0d89042d65ce02acd0a0581d664802acd8a0501d6648002ce098525d68f102ace098501d664802ca259d14284dce02ea51e158084e4802ea59e150084e4802ea61d950084e4802ea61d950840ebb002a61d9504cacf1002a61d9508c6cf1002a61d950c86cf102ea61d950084dcb02c6259d14288d0502ca259d14284d0502ca259d14284cf802ce259d1428490502ce259d142848f802ce259d142884f802ca259d14284cf702960d89042de505029e058d082d664e029e098d042d664e02ce15a51c284a4d029e0d89042d664e02ca15a51c284e4d02c615a51c288e4d029e0d89042d65050296058d082de64e0296098d042de64e02ce1da514284a4d02960d89042de64e02ca1da514284e4d02c61da514288e4d029e0d89042d64f802a6058d082d5e4d02a6098d042d5e4d02a60d89042d5e4d02ea61d950084cf202a60d89042d5d050296058d082e5e4e0296098d042e5e4e02ce259d14284a4d02960d89042e5e4e02ca259d14284e4d02c6259d14288e4d02a60d89042d5cf8029e058d082d664d029e098d042d664d029e0d89042d664d02a60d89042dd4f80296058d082de64d0296098d042de64d02960d89042de64d029e0d89042d64f7),
  (0x81ea82a92acaa4ab2a92ad2a254550, 50, 0xeea45c1590a2bb02ca15a51c284eaf02ca1da514284eaf02ace09811d466bb02c651e1580caaaf02c659e1500caaaf02ca259d14284eaf02c661d9500caaaf02ca259d14284dcc02c661d9500ca8f402c651e1580caa4a02ea51e1580c864902c659e1500caa4a02ea59e1500c864902c9a51e16840eba02c661d9500caa4a02ea61d9500c864902ca251d96840eba02ca259d16840eba02ca259d16840ebc000e259d1468acf5002a61d9508c6cf5002a61d950c86cf502c661d9500ca9cc02ca259d14284cf402ce259d142848f402ca259d14284cf302ca15a51c284e4a02ce15a51c284a4902ca15a51c284e4902ca1da514284e4a02ce1da514284a4902ca1da514284e4902c5e15a50c82aba02ea61d9500c84f402c661d9500ca8f302c651e1580caa4902c659e1500caa4902ca259d14284e4a02ce259d14284a4902ca259d14284e4902c66159d0c82aba02c661d9500caa4902c661d950c82aba000e259d1684acf5),
  (0x816a92ad2a0ab4a82ad2a554906550, 48, 0x2ea61d950c842be00aa61d9440ed1d302e96259d00c86b502e9e259500c86b5001245e94cada24d002c669cd509a0c902ea61d9500c86b5009261d9440eeaa702c661d95028c95c008e61d9442ad14302c661d9500e8910009261d94428ed5c00aa45e15810ee6b009261d9440ead1000aa59e1440ed27a02ea59e15004ca68009259e1440eae6600aa59e14410ee6800aa61d9440ed27a02ea61d95004ca68009261d9440eae6600aa61d94410ee6802ea61d950c842bd02ea61d9500c85d300aa61d9440ed14302c661d95028c91002ea61d9500c4919009261d94428ed10000651e94ec9a24d009259e14428ee66009261d94428ee66)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_28 : blocksOK 11 56 P11 P12 955 108 B12_28 = true := by decide +kernel

def B12_29 : List (ℕ × ℕ × ℕ) := [(0x816a92ad2a0ab4a82ad2a554906d52, 50, 0x2ea61d950c842c302ce61d950482abe02cd6259d004aab602e96259d00c4ab802cde2595004aab602e9e259500c4ab802e9e15a50c842c2002269cd44ad90f8002ea4dc552188f4002e88e45d15a034002ea4dc5590a0eb0009269cd586e07b02ce61d95004aab602ea61d9500c4ab802ea6159d0c842c2002ea4dc561098eb0009269cd606d87b02ea61d950c842c202ce61d95004aaac02c661d9500ca94402ce61d95004a94402ce61d95006891a02ce51e15804aa8502ea51e15804ca6c02ea51e1580c4a6c002251cd449aad1102ce59e15004aa7b02ea59e15004ca6902ea59e1500c4a69002a59cd46d0a25a02ea59e150c842c1002a59d144a0ee68002a59d14ca06e6802ce61d95004aa7b02ea61d95004ca6902ea61d9500c4a69002a61cd46d09a5a02ea61d950c842c1002a61d14498ee68002a61d14c986e6801a6acc8411d628d02ea61d950c04abd02ea61d95040cabd02ea61d950c842c002ce61d95004a9d402ea61d9410c49d502e96259d0c842bf02e9e25950c842bf02ea61d950048d4402ea61d95004c91a02ea61d9500c491a0010aa4dc6d5a07902ce51e158284a6c002251e94498ed11001a69cd46c920ed002251e94c986d1102ce59e150284a69000e59e946d0a25a000659e94ed0a25a000e59d168a06e6802ea61d950c842bf02ce61d950284a69000e61e946d09a5a000661e94ed09a5a000e61d168986e6802ce61d950428abd),
  (0x81aa8aae2a0ab8a82ae2a1546a8a06, 48, 0x2ea61d950c842c4006a61d9500cadd500696259d00caeb70069e259500caeb702c2259d14c86abb001a69cd486d20f70006a4dc9521acf30006a4dc95a12cf3006a61d9500caeb70006a4dc96192cf302ce61d950086aa9004a61d95028ed5f004e61d95028ad5f004e61d9500aad17006a51e1580cae8d006a51e15808ee67006a51e1580cae67006a59e1500cae8d006a59e15008ee67006a59e1500cae67006a59d160c0aec0006a61d9500cae8d006a61d95008ee67006a61d9500cae67006a61d158c0aec0006a61d950c0aec002ea61d9500c85d5006a61d9500cad5f006a61d95008ed17006a61d9500cad17001a69cd4ac520f7004e51e15828ae67004e59e15028ae67004e61d95028ae67),
  (0x81ea82af2a0abca82af2a1542a8550, 50, 0x2ea61d950c842c502cd6259d0086ab902cde25950086ab9001a69cd486d21ce002ea4dc9505a08f002ea4dc9585208f02ce61d950086ab9002ea4dc9605188f02ce61d950086aad02c661d9500ca96202ca61d9500c696202ca61d95004e91d02ce61d95008696202ce61d95004a91d02ce61d95008691d02ce61d95008690f02ce51e158086a8e02ce51e15804aa7002ce51e158086a7002ce51e158086a6502ca51e1580c6a7002ca51e1580c6a6502c651e1580caa6500224dc946da911602ce59e150086a8e02ce59e15004aa7002ce59e150086a7002ce59e150086a6502ca59e1500c6a7002ca59e1500c6a6502c659e1500caa6500224dc946d2991602ce59d160806ac302ce59d160806abe02ce59d16040aabe002a59d1484ee1d302ca59d16040eabe002a59d14c4ae1d3002a59d14c86e1d302ce61d950086a8e02ce61d95004aa7002ce61d950086a7002ce61d950086a6502ca61d9500c6a7002ca61d9500c6a6502c661d9500caa65001a4dc946d2a11602ce61d158806ac302ce61d158806abe02ce61d15840aabe002a61d1484ed9d302ca61d15840eabe002a61d14c4ad9d3002a61d14c86d9d302ce61d950806ac302ce61d950806abe02ce61d95040aabe002a61d9484ed1d302ca61d95040eabe002a61d94c4ad1d3002a61d94c86d1d302ce61d950842ac4002a61d9504cadd5002a61d9508c6dd5002a61d950c86dd502ce61d9500869d602ea61d950084d6202ea61d950048d1d02ea61d950084d1d02ea61d950084d0f02ea61d9500c491d02ea61d9500c490f02ea61d9500c850f001a69cd4ac5204c02ca51e158284e7002ca51e158284e6502c651e158288e65002269c946d8d11602c651e15828ca65002269cd46d89116002269cd4ad8511602ca59e150284e7002ca59e150284e6502c659e150288e65002269c946d0d91602c659e15028ca65002269cd46d09916002269cd4ad0591602ca59d160428ebe000e59d1684ae1d3000e59d16886e1d3000a59d168c6e1d302ca61d950284e7002ca61d950284e6502c661d950288e65001a69c946d0e11602c661d95028ca65001a69cd46d0a116001a69cd4ad0611602ca61d158428ebe000e61d1684ad9d3000e61d16886d9d3000a61d168c6d9d302ca61d950428ebe000e61d9684ad1d3000e61d96886d1d3000a61d968c6d1d3000e61d952886dd5)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_29 : blocksOK 11 56 P11 P12 955 112 B12_29 = true := by decide +kernel

def B12_30 : List (ℕ × ℕ × ℕ) := [(0x80aaeaa02baa80aeaa2544a8a0eaa2, 48, 0x2ea61d950c842cc02ea61d85508c2cb02ea61d8d50842cb02ea61d8c54902ca02ea61d914c842cb02ea61d90548c2ca02ea61d90d4842ca0026118e849d6d1b02ea61d950c842cb02ea61d94508c2ca02ea61d94d0842ca0026158e849d2d1b02ea61d950c842ca00261592849ced1b002615928c9c6d1b02e9e25950c842c902e9e2585508c2c802e9e258d50842c800161d8e84a52e6e02e9e25914c842c800161d9284a4ee6e00161d928ca46e6e02e9e25950c842c800121d9684a4ee6e00121d968ca46e6e000e1d9690a46e6e02ea61d950c842c902ea61d85508c2c802ea61d8d50842c80016258e849d2e6e02ea61d914c842c800162592849cee6e001625928c9c6e6e02ea61d950c842c800122596849cee6e001225968c9c6e6e000e2596909c6e6e02ea61d950c842c70016259e8508eec20016259e8d086ec20016259e90c86ec20012259e94c86ec202ea61d950c842c602c96118c1c6a4a502c94120da69c53302c941205a69cd3302ea41e158508dda02c940e05a69d13302ea41e1584c91da02ea41e158c491da02c900e05a69d53302ea41e1184c95da02ea41e118c495da02ea41e0d90495da02c94120da469ca302c94120da69c52102c941205a69cd2102c940e05a69d12102c900e05a69d52102c94120d9c6a4a302c94120d9ea452102c9412059ea4d2102c940e059ea512102c900e059ea552102e94120d9c4a5e5),
  (0x80eae2a02b8a80ae2a3546a8e0e41c, 48, 0x2ea61d950c842d102ea61d8d50842d002ea61d914c842d002ea61d90d4842cf02ea61d950c842d002ea61d94d0842cf02ea61d950c842cf01e14904c2daa51a01eac14904e1a61701eac148c521a61701eac108c561a61702614904c2da9d1a026ac14904e19e17026ac148c5219e17026ac108c5619e1701e14904c2daa51702ea61d950c40ac70056259e8108eec20096259e8104eec202ea59e150c842ce02ea61d950c842ce02c96118c1c6a51502ea41e158d049dc02ea41e1590c49dc02ea41e1194c49dc001e15928c86e6ba02c94120da469d1102ea61d950c842cd02c94120d9c6a511),
  (0x80eae2a02b8a84ae2a2546a8e0e44c, 48, 0x2ea61d950c842da02ea61d94d0842d902ea61d950c842d902ea61d950c842d802ea6159d0c482d702ea6159cd0482d602ea6159d0c482d602ea61d950c842d702ea61d94d0842d602ea61d950c842d602ea61d950c842d5026ac904c1d9620c02ea61d94d0842d402ea61d950c842d4026ac904c1e19617026ac508c1619e1702ea6159d0c40ac800522596809cee6e0092259e8054ee6e02ea59e150c842d302ea61d950c842d302c96118c1c6a4d402ea4161d8d049dd02ea4161d90c49dd02c5c120da69492402c94120da69c52402ea61d950c842d202c94120d9c6a4d0),
  (0x80eae2a02b8a84ae2a3546a8e0e45c, 50, 0x2ea61d950c842e502ea61d8d50842e402ea61d914c842e402ea61d90d4842e302ea61d950c842e402ea61d94d0842e302ea61d950c842e3001e15904caae47202ea61d950c842e202e9e258d50806d702e9e25914c806d700261d928c54ad2302e9e25950c806d700261d968c50ad2300261d96904cad2300214904e9eda65102614904c2d9e90e026ac94105d8e20c026ac940c5d9220c001625928c9c6e59026ac900c5d9620c001225968c9c6e59000e2596909c6e5902614900c6da9d1a026ac14904e19e16026ac148c5219e16026ac108c5619e1602ea61d950c806c902ea61d81508c6c80092259e804ed68b009625829d04eec202ea59e150c842e102ea59e150c842e002ea59e150c842df02ea61d950c842e102ea61d950c842e002ea61d950c842df026ac80550e19ece02c5e159024ca87e02c5c1611a68c95402c5c160da69095402ea41e15904c9fc02c5c120da69495402ea41e11944c9fc02ea41e0d94509fc002615928c49ecf902c94120da469d1302ea416119c4c9fd02ea4160d9c509fd02ea4120d9c549fd00096118e9e46cff02ea61d950c842de02ea61d950c842dd02ea61d950c842dc02ea59e150c842db02c94120d9ea452502c5c16118caa63202c5c160d90aa63202c5c120d94aa63202ea61d950c842db02e94120da45ca5a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_30 : blocksOK 11 56 P11 P12 955 115 B12_30 = true := by decide +kernel

def B12_31 : List (ℕ × ℕ × ℕ) := [(0x80eae2a12b8a84ae2a2544a8e0e544, 48, 0x2ea61d950c842e902ea61d950c842e802e9215a5cc40ae302e92158e5c40ad802e9611a5cc40ae302e96118e5c40ad802e9611a5cc40acf02e9e25950c806e302e9e258d50806d802e921d964c04ad602e961d924c04ad602ea61d950c806e302ea61d8d50806d802e922595cc04ad602e962591cc04ad602ea61d950c806cf02e9611a5cc40aca00661592809ced1b0096259e8050ed1b02ea59e150c842e702ea61d950c842e702c661d8c169093502ea41e158d085de02c641e0d969092302c641e0d929492302c94120da69c52302ea61d950c842e602c94120d9ea4523),
  (0x80eae2a12b8a84ae2a2546a8e0e54c, 50, 0x2ea61d950c842f202ea61d94d0842f102ea61d950c842f102ea61d90d4806e8008e259c42ad52e902e960da5d004ae302e9611a5cc04ae3002615928c9c6d0a02e9e25950c806e402e9e258d50806d902e9e25914c806d900161d928c64ad4702e9e15a50c086d700121d968ca46e60000e1d9690a46e6002ea61d950c842f002ea61d950c806e402ea61d8d50806d902ea61d914c806d9001625928c5cad4702ea6159d0c086d7001225968c9c6e60000e2596909c6e6002ea61d950c806d00016259e8c50ad400016259e904cad40001215a69c4cae8302ea61d950c806cb02ea61d94108c6ca0096259e804ed158009201a69c54ee6e02ea59e150c842ef02ea59e150c842ee009042269d94ee4202ea61d950c842ef02ea61d950c842ee009041a69e14ee4202ea61d950c842ed02c661d9014ca87602c641e11968c95102c641e0d969095102e94261d904ca0102ea41e1194c85df02ea41e11944ca5902ea41e0d9450a59002615928c49ee4f02c94120da469cd202e9426119c4ca0202e94260d9c50a0202ea4120d9485e2c02ea61d950c842ec02ea61d950c842eb009042259e94ee4102ea59e150c842ea02c94120d9c6a4d202e941e11a44ca0202e941e0da450a0202e9c120d948662c02ea61d950c842ea02e94120da45ca04),
  (0x80eae2a12b8a84ae2a3546a8e0e55c, 52, 0x2ea61d950c842f702c661d8d5082af202c661d914c82af202c661d90d482ae902c661d950c82af202c661d94d082ae902c661d950c82ae9001e15928c86e47502c5e25950c82ae502c5e258d5082ada02c5e25914c82ada00161d928c86e5df02c5e25950c82ada00121d968c86e5df000e1d969086e5df002615928c85ec5e00214928c5eda652002c96904da1e4de02c661d950c82ae502c661d8d5082ada02c661d914c82ada001625928c86dddf02c661d950c82ada001225968c86dddf000e25969086dddf001e15928c866c5e002c96904e19e4de02c661d950c82ad10016259e8c6d0a9f0016259e906cca9f0016259e90c4ad980012259e946cca9f0012259e94c4ad98000e259e9504ad9802c661d950c82acc02ea61d81508c6cb0092259e806cd6a4009201a69c4ed68b02ea59e150c842f602c659e150ca82f3009202a45d8ed68c00295908c6e1e65e02ea61d950c842f602c661d950ca82f3009182a45e0ed68c00296108c6d9e65e02ea61d950c842f500096118c669ed3100294920da45ee7e02c96118c245e93802c641e158d0a9e002c641e1590ca9e00014ae904e1da5fe02c641e1194ca9e00010ae944e1da5fe000cae94521da5fe00096118e85ee5bf002615928c85ec9202c94120da45e92602ea416118c85e3a02ea4160d9085e3a00161d928c866de102ea4120d9485e3a00121d968c866de1000e1d9690866de100096118e9c66c4402c661d81508eacb02ea61d950c842f4009201a45e8ed68b00214928c6d9e50802ea59e150c842f300095928c661ed3200055908eae1e65e02c94120d9c6692602e9c16118c8663a02e9c160d908663a001625928c85ede102e9c120d948663a001225968c85ede1000e25969085ede100096118ea45ec4402ea61d950c842f300096128c659ed3200056108ead9e65e02e94120d9c8666a0016259e8c52caa80016259e904ecaa80012259e944ecaa800096118ea45ed31)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_31 : blocksOK 11 56 P11 P12 955 119 B12_31 = true := by decide +kernel

def B12_32 : List (ℕ × ℕ × ℕ) := [(0x80aae2a02baa88aeaa2544a8a2e8a2, 48, 0x2ea61d950c842fc02c861d950ea42fa02ea60d9d50842fb02c860d9d502a6de02ea6119d4c842fb02c86119d4c2a6de02c920d85d42a6ec001c86118ea56e4102ea6159d0c842fb02c86159d0c2a6de02c960d85d02a6ec001c86158ea52e4102c961185cc2a6ec001c861592a4ee41002696118c85ecdc02ea61d950c842fb02c861d950c2a6de02c9e0d85502a6ec0014861d8ea52e4102c9e11854c2a6ec0014861d92a4ee4100269e118c856cdc02c9e15850c2a6ec0010861d96a4ee4100269e158c852cdc00269e159084ecdc02ea61d950c842fa02ea61d950c842f902ea60d9d50086de02ea60d9d50086dc02ea6119d4c086de02ea6119d4c086dc001ea6118c856e4102ea6159d0c086de02ea6159d0c086dc001ea6158c852e41001ea6159084ee4102ea61d950c086de02ea61d950c086dc0016a61d8c852e410016a61d9084ee410012a61d9484ee4102ea61d950c842f802ea61d94050c86702c9c1611a4e84aa02ea41e158508c8402c9c1611a684d4502ea41e1584c908402c9c160da68514502ea41e15848d0b402ea41e1184c948402c9c120da68554502ea41e11848d4b402ea41e0d84914b402ea4161184c9c8402c94120da685d4502ea41611848dcb402ea4160d8491cb402ea4120d8495cb402e9c161184ca4aa02e9c1611a4c85e202e9c161184a4d4502e9c160d84a514502e9c120d84a554502e94120d84a5d45),
  (0x80aaeaa02b8a88aeaa2544a8a2ea22, 48, 0x2ea61d950c8430202ea61d950c8430102ea60d9d508430002ea60d9d50842ff02ea6119d4c8430002ea6119d4c842ff02e920da5d4086ef001c85928e256e4202ea6159d0c8430002ea6159d0c842ff02e960da5d0086ef001c85968e252e4202e9611a5cc086ef001c85969224ee42002615928c85ecd902ea61d950c8430002ea61d950c842ff02e9e0da550086ef0014859e8e252e4202e9e11a54c086ef0014859e9224ee4200261d928c856cd902e9e15a50c086ef0010859e9624ee4200261d968c852cd900261d969084ecd9026ac841d520dac902ea61d950c842fe02ea60d9d50086e102ea60d9d50086df02ea6119d4c086e102ea6119d4c086df001e25928c856e3e02ea6159d0c086e102ea6159d0c086df001e25968c852e3e001e25969084ee3e02ea61d950c086e102ea61d950c086df0016259e8c852e3e0016259e9084ee3e0012259e9484ee3e02ea61d950c842fd02c9e159024e84ab02c9e1411a4e84a902c9e1411a684d4e02c9c1611a684d3e02c9e140da68514e02c9c160da68513e02ea41e15908c5fb02c9e100da68554e02c9c120da68553e02ea41e11948c5fb02ea41e0d94905fb02c96100da685d4e02c94120da685d3e02ea416119c8c5fb02ea4160d9c905fb02ea4120d9c945fb02e9c1611a4c85e902e9c1611a4c85e402e9c1611a48c65802e9c160da49065802e9c120da49465802e94120da49c658),
  (0x80aaeaa02baa88aeaa2544a8a2eaa2, 50, 0x2ea61d950c8430602c861d950c26afc02c8e1d950426afc02e8e05a5d410acb02c921d94c426afc02e9205a5d40cacb02e920da5d404acb0026118e8496dd5802c961d90c426afc02e9605a5d00cacb02e960da5d004acb0026158e8492dd5802e9611a5cc04acb00261592848edd58002615928c86dd58002615928c85ec5702c9e1590c426afc02e9e05a5500cacb02e9e0da55004acb00261d8e8492d55802e9e11a54c04acb00261d92848ed55800261d928c86d55800261d928c856c5702e9e15a50c04acb00261d96848ed15800261d968c86d15800261d968c852c5700261d969086cd5800261d969084ec5700261d96908c6c5702ea61d950c8430502ea61d950c8430402ea6059d500cac902ea60d9d5004ac90016258e8492de8b02ea6119d4c04ac900162592848ede8b001625928c86de8b001e25928c496d8c02ea6159d0c04ac900122596848ede8b001225968c86de8b001e25968c492d8c000e25969086de8b001e25969048ed8c001e259690c86d8c02ea61d950c04ac90012259e848ed68b0012259e8c86d68b0016259e8c492d8c000e259e9086d68b0016259e9048ed8c0016259e90c86d8c000e259e9486d28b0012259e9448ed8c0012259e94c86d8c000e259e95086d8c02ea61d950c8430302ea601950c85ec602ea59610c481efd02ea61590c481efd02c9e159024c686a02c9c1611a4e84ab02c9c1611a468cab02c9c1611a684d4d02c9c160da4690ab02c9c160da68514d02c9c1605a68d14d0026118e849d6d5d02c9c120da4694ab02c9c120da68554d02c9c1205a68d54d0026158e849d2d5d02c9c0e05a69154d00261592849ced5d002615928c9c6d5d02c94120da469cab02c94120da685d4d02c941205a68dd4d00261d8e84952d5d02c940e05a691d4d00261d928494ed5d00261d928c946d5d02c900e05a695d4d00261d968490ed5d00261d968c906d5d00261d96908c6d5d02ea61590c481ef802e9c1611a4c49d802e9c1611a4c85e602e9c1611a448de602e9c1611a484e5702e9c160da4491e602e9c160da48525702e9c1605a48d25702e9c120da4495e602e9c120da48565702e9c1205a48d65702e9c0e05a49165702e94120da449de602e94120da485e5702e941205a48de5702e940e05a491e5702e900e05a495e57)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_32 : blocksOK 11 56 P11 P12 955 122 B12_32 = true := by decide +kernel

def B12_33 : List (ℕ × ℕ × ℕ) := [(0x80eae2a02b8a8cae2a3546a8e2e45c, 52, 0x2ea61d950c8430802ea60d9d508430702ea6119d4c843070016118c86ae5ee902ea6159d0c843070012158c86ae5ee9000e159086ae5ee9002615928c9c6d3502ea61d950c8430700121d8c86ae56e9000e1d9086ae56e900261d928c946d35000e1d9486ae52e900261d968c906d3500261d96908c6d3500261d96908c6c06002c9c5690e1a5c8002c9c56918e243c0261c94502cda89d0261c14906d8e90e0261c148c6d9290e026ac1c94518e1fe0261c108c6d9690e026ac1c90558e1fe026ac1c8c55921fe002c94528e1da52d002c9c56920da43c02614108c6d9e90e026ac14905d8e1fe026ac148c5d921fe002c9c528e15a52d026ac108c5d961fe002c9c568e11a52d002c9c56920da52d02ea61d950c40b0402ea6019d504cac902ea6019d508c6c902ea6019d504cac7026ac805d518e2c902ea59e150c806fe02ea59e150c40afe0029d94906ce25e7026ac805d520dac902ea61d950c806fe02ea61d950c40afe0029e14906cda5e7026ac805d518e2c70029c5611a4cade70029c9611a4c6de702c9e159024c689d02c9c1611a44e90e02c9c160da45290e02ea41e15904c9fe02c9c120da45690e02ea41e11944c9fe02ea41e0d94509fe002615928c9c6d2d02c94120da45e90e02ea416119c4c9fe02ea4160d9c509fe00261d928c946d2d02ea4120d9c549fe00261d968c906d2d00261d96908c6d2d00261d9690c86dc800261d96904cac3c00261d96908c6c3c02ea61d950c40afa02ea61d950c806f902ea61d950c40af90021c9452acda497026ac9c550e01af90021c5592a4cade30021c9592a4c6de302e9c1611a4c49ed02e9c1611a44ca5b02e9c160da450a5b001e25928c946e7c02e9c120da454a5b001e25968c906e7c001e2596908c6e7c026ac9c550d822f90019c5612a4cade30019c9612a4c6de302e94120da45ca5b0016259e8c906e7c0016259e908c6e7c0012259e948c6e7c0009e1592a4c6c97),
  (0x80eae2a02baa88aeaa2544a8a2e4a0, 48, 0x6c9e9410da61b70061c9412a6d8e540061c940ea6d925402e920da5d4086f00061c900ea6d965402e960da5d0086f002e9611a5cc086f000614900ea6d9e5402e9e0da550086f002e9e11a54c086f002e9e15a50c086f0006c9c1690e1a5c80061c14928eda6510061c148e92da6510061c108e96da65100614108e9eda65102ea61d950c8070502c9e159024c689102c9c1611a4e84b002c9c1611a468d0102c9c1611a68c55202c9c160da46910102c9c160da69055202ea41e15908c60002c9c120da46950102c9c120da69455202ea41e11948c60002ea41e0d949060002c94120da469d0102c94120da69c55202ea416119c8c60002ea4160d9c9060002ea4120d9c9460002c41e1590ea49b602e9c1611a4c85eb02e9c1611a448e4b02e9c160da44924b02e9c120da44964b02e94120da449e4b),
  (0x80eae2a12b8a88ae2a3546a8e2e51c, 52, 0x2ea61d950c8430c02ea61d8d508430b02ea61d914c8430b02e920d9e5404af102ea61d950c8430b02e960d9e5004af102e96119e4c04af1001e15908c6ae47402e9e25950c40b0702e9e0da55004ae402e9e11a54c04ae400261d928c946d5102e9e15a50c04ae400261d968c906d5100261d96908c6d5100261d96908c6c1c00214904ea6d9e54002c94528da25ce002ea61d950c8070702ea60d9d50086e402ea6119d4c086e4001e25928c54ad5102ea6159d0c086e4001e25968c50ad51001e2596904cad51001e2596904cac1c002c94528e1a5ce002e9e25950c04ae20016259e8c906e880016259e908c6e880016259e90c86d750012259e948c6e880012259e94c86d75000e259e95086d7502c9e1590c066afc02e9e01a5504cacb02ea6019d508c6cb02e821da5504cac802e9da6150c40b0002ea59e150c806ff02e9da6150c40aff00295908c6e25e5f02e9e25950c40b0002ea61d950c806ff02e9e25950c40aff00296108c6da5e5f02ea61d950c8430a00096118c66add3f00056118c9eae53f02c9e159024c688c02c9c1611a44e8bf02c9c160da4528bf02e9c2615904ca0302c9c120da4568bf02e9c2611944ca0302e9c260d9450a03002456118ca9ec8202c94120da45e94a02ea416119c8c60502ea4160d9c9060500261d928c946d4b02ea4120d9c9460500261d968c906d4b00261d96908c6d4b00261d9690c4ad8002e9e25950c40afb02c821d950c6a6de02c4225950ca9ede00214904eada5d0902ea59e150c8430900095904ea62dd4600055908e9e2e54602c54120d9ca694a02e9c1611a44ca0502e9c160da450a05001e25928c54ad4b02e9c120da454a05001e25968c50ad4b001e2596904cad4b001e259690c86d8002ea61d950c8430900096104ea5add4600056108e9dae54602e94120d9c64a5c0016259e8c906e860016259e908c6e860012259e948c6e860009e1592a4c6c83)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_33 : blocksOK 11 56 P11 P12 955 125 B12_33 = true := by decide +kernel

def B12_34 : List (ℕ × ℕ × ℕ) := [(0x80eae2a12b8a8cae2a3546a8e2e55c, 54, 0x2ea61d950c8430f02c660d9d5082b0c02c66119d4c82b0c02c520da5d40aaf202c66159d0c82b0c02c560da5d00aaf202c5611a5cc0aaf2002615928c86dc7602c661d950c82b0c02c5e0da5500aaf202c5e11a54c0aaf200261d928c86d47602c5e15a50c0aaf200261d968c86d07600261d969086cc76002c9e94520da409002c9e9450da61b7002c9e94518e244002c661d950c82b0802c660d9d500aae502c66119d4c0aae5001625928c86dde002c66159d0c0aae5001225968c86dde0000e25969086dde0002c96904d9e6128002c9e94520da44002c661d950c0aae50012259e8c86d5e0000e259e9086d5e0002c9e904d966128000e259e9486d1e0002c9e944d926128002c9e94518e6128002c9e94520da40002c661d950c82b0602c661d950c82afc02c66019d508eacc02e82259d508c6c902c659e150c82b0202ea59e150c8070102ea59e150c8430e0029d94906ce25e902c661d950c82b0202ea61d950c8070102ea61d950c8430e0029e14906cda5e902ea61d950c8430d0009e159064eaca90029c9611a4c6df60029c9611864ed7a02c9e159024c68b102c9c1611a44e95702c9c160da45295702c641e15908ea0602c9c120da45695702c641e11948ea0602c641e0d9492a06002615928c85eca102c94120da45e95702c6416119c8ea0602c64160d9c92a0600261d928c856ca102c64120d9c96a0600261d968c852ca100261d969084eca10009e159284ee59a00261d96908c6c2702ea61d950c806fc02c821d950c66afa02c42259d508eac90021c96906cda49802c659e150c82b010009d969064e2caa0005d9492ace25e90021c96906cda45b02c5c1611a4ca9ee02c5c1611a48ea5d02c5c160da492a5d001e25928c856df102c5c120da496a5d001e25968c852df1001e25969084edf1001cae9450e1a56b02c661d950c82b010009e169064dacaa0005e1492acda5e90019c96906ce245b02c54120da49ea5d0016259e8c852df10016259e9084edf10014ae9c50e1a56b0012259e9484edf10010ae9c54e1a56b000cae9c5521a56b0009e1592a4c6ca90009e1592a44ec2b0005c9611aa4ed7a),
  (0x80aae2a22b8a88aeaa2544a8aae822, 48, 0x2ea61d950c84311004a61e942d0d9d802c8e259d5006b01004a61c16ad18de902c92259d4c06b01004a61c16acd91e9005920ea5d40aef3004a61c16ad8d25e02c96259d0c06b01004a61c12acd95e9005960ea5d00aef3004a61c12ad8d65e0059612a5cc0aef3004a61c0ead9165e002616918c85eea202c9e25950c06b01004a61412acd9de90059e0ea5500aef3004a61412ad8de5e0059e12a54c0aef3004a6140ead91e5e00261e918c856ea20059e16a50c0aef3004a6100ead95e5e00261e958c852ea200261e959084eea202ca61d950c06b010049e1412acda5e9005a60e9d500aef30049e1412ad8e65e005a6129d4c0aef30049e140ead9265e001e26918c856ea2005a6169d0c0aef30049e100ead9665e001e26958c852ea2001e26959084eea2005a61e950c0aef300496100ead9e65e0016269d8c852ea20016269d9084eea20012269d9484eea202ea61d950c8431002ca61d94050e9d8005a61c1690cae9502ca61c158528de9005a41e168d0adef02ca61c1584e91e9005a41e1690cadef02ca61c15868d25e02ca61c1184e95e9005a41e1294cadef02ca61c11868d65e02ca61c0d869165e02ca6141184e9de9005a416129ccadef02ca61411868de5e02ca6140d8691e5e02ca6100d8695e5e02c9e141184ea5e90059c1612a4cadef02c9e1411868e65e02c9e140d869265e02c9e100d869665e02c96100d869e65e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_34 : blocksOK 11 56 P11 P12 955 128 B12_34 = true := by decide +kernel

def B12_35 : List (ℕ × ℕ × ℕ) := [(0x80aae2a22baa88aeaa2544a8aae0a0, 48, 0x2c06259d508eb04005a69c942d0e06902c06259d508eafa006241e94ad18c9802c06259d4c92afa006241e94acd9098006128ca5d41aef4006241e94ad8d10802c06259d0c96afa006241e90acd9498006168ca5d01aef4006241e90ad8d5080061690a5cc1aef4006241e8cad91508002694920d85eea302c0625950c9eafa006241690acd9c980061e8ca5501aef4006241690ad8dd080061e90a54c1aef400624168cad91d0800269c920d856ea30061e94a50c1aef400624128cad95d0800269c960d852ea300269c961184eea302c061d950ca6afa0061c1690acda498006268c9d501aef40061c1690ad8e50800626909d4c1aef40061c168cad92508001ea4920d856ea300626949d0c1aef40061c128cad96508001ea4960d852ea3001ea4961184eea3006269c950c1aef400614128cad9e5080016a49e0d852ea30016a49e1184eea30012a49e1584eea302ea61d950c8431202ca61d94050e86902ea41e1590c869602ea41e158508c9802ea41e158d085f202ea41e1584c909802ea41e1590c85f202ea41e15848d10802ea41e1184c949802ea41e1194c85f202ea41e11848d50802ea41e0d849150802ea4161184c9c9802ea416119cc85f202ea41611848dd0802ea4160d8491d0802ea4120d8495d0802e9c161184ca49802e9c1611a4c85f202e9c1611848e50802e9c160d849250802e9c120d849650802e94120d849e508),
  (0x80aaeaa22b8a88ae2a2544a8aaea02, 48, 0x2ea61d950c84315006a61d9410cae980068e259d500af0d006a41e158d0adf600692259d4c0af0d006a41e1590cadf6006920da5d40aef5006a41e15908ee7e00696259d0c0af0d006a41e1194cadf6006960da5d00aef5006a41e11948ee7e0069611a5cc0aef5006a41e0d9492e7e002615928c85eea00069e25950c0af0d006a416119ccadf60069e0da5500aef5006a416119c8ee7e0069e11a54c0aef5006a4160d9c92e7e00261d928c856ea00069e15a50c0aef5006a4120d9c96e7e00261d968c852ea000261d969084eea002ea61d950c84314006a61d950c0af0d0069c1611a4cadf6006a60d9d500aef50069c1611a48ee7e006a6119d4c0aef50069c160da492e7e001e25928c856ea0006a6159d0c0aef50069c120da496e7e001e25968c852ea0001e25969084eea0006a61d950c0aef500694120da49ee7e0016259e8c852ea00016259e9084eea00012259e9484eea002ea61d950c8431302ea61d9410c8698006a61d9410cae9702ea41e158d085f6006a41e158d0adf302ea41e1590c85f6006a41e1590cadf302ea41e15908c67e02ea41e1194c85f6006a41e1194cadf302ea41e11948c67e02ea41e0d949067e02ea416119cc85f6006a416119ccadf302ea416119c8c67e02ea4160d9c9067e02ea4120d9c9467e02e9c1611a4c85f60069c1611a4cadf302e9c1611a48c67e02e9c160da49067e02e9c120da49467e02e94120da49c67e),
  (0x80aaeaa22b8a88aeaa2544a8aaea22, 50, 0x2ea61d950c84319005a61c150caeb1102c8e259d5006b0202e8e259d500870e02c92259d4c06b0202e92259d4c0870e02e920da5d4086f6001d86908e16e68c02c96259d0c06b0202e96259d0c0870e02e960da5d0086f6001d86948e12e68c02e9611a5cc086f6001d8694920ee68c000596908e1ee5590025869490e1ed8d02c9e25950c06b0202e9e25950c0870e02e9e0da550086f60015869c8e12e68c02e9e11a54c086f60015869c920ee68c00059e908e16e5590025869c90e16d8d02e9e15a50c086f60011869c960ee68c00059e948e12e5590025869c94e12d8d00059e94920ee5590025869c9520ed8d00059e94920e6c5800186a49d520ef050005a69c9520edba02ca61d950c06b0202ea61d950c0870e02ea60d9d50086f6001586a48e12de8c02ea6119d4c086f6001586a4920ede8c0005a6908e16dd59001d86a490e16d8d02ea6159d0c086f6001186a4960ede8c0005a6948e12dd59001d86a494e12d8d0005a694920edd59001d86a49520ed8d0005a694920dec5802ea61d950c086f6001186a49e0ed68c0005a69c8e12d559001586a49ce12d8d0005a69c920ed559001586a49d20ed8d0005a69c920d6c580005a69c960ed159001186a49d60ed8d0005a69c960d2c580005a69c9610ec5802ea61d950c8431802e821d950c866fd02ea61d950c8431702ea61d950c8431602ca61d94050e9d902ea61c1590c869802ea61c158508df702ea41e158d085f402ea61c1584c91f702ea41e1590c85f402ea41e15908c67f02ea41e158c8527602ea61c1184c95f702ea41e1194c85f402ea41e11948c67f02ea41e118c8567602ea41e0d949067f02ea41e0d9085676000596908e25ed5e02ea6141184c9df702ea416119cc85f402ea416119c8c67f02ea416118c85e7602ea4160d9c9067f02ea4160d9085e7600059e908e256d5e02ea4120d9c9467f02ea4120d9485e7600059e948e252d5e00059e949224ed5e02c821d950e866fd02e9e141184ca5f702e9c1611a4c85f402e9c1611a48c67f02e9c16118c8667602e9c160da49067f02e9c160d90866760005a6908e1d6d5e02e9c120da49467f02e9c120d94866760005a6948e1d2d5e0005a694921ced5e02e94120da49c67f02e94120d9c866760005a69c8e152d5e0005a69c9214ed5e0005a69c9610ed5e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_35 : blocksOK 11 56 P11 P12 955 130 B12_35 = true := by decide +kernel

def B12_36 : List (ℕ × ℕ × ℕ) := [(0x80aaeaa22baa88aeaa2544a8aaeaa2, 52, 0x2ea61d950c8431c02c86259d500eb0602c8e259d5006b0602c8e05a5d412acc02c92259d4c06b0602c9205a5d40eacc02c920da5d406acc001e118e84ad66a402c96259d0c06b0602c9605a5d00eacc02c960da5d006acc001e158e84ad26a402c9611a5cc06acc001e159284ace6a4001e15928cac66a4001e15928c4ae5a802c9e25950c06b0602c9e05a5500eacc02c9e0da55006acc00161d8e84ad26a402c9e11a54c06acc00161d9284ace6a400161d928cac66a400161d928c4ae5a802c9e15a50c06acc00121d9684ace6a400121d968cac66a400121d968c4ae5a8000e1d9690ac66a4000e1d96904ae5a800061d9690cae5a800261d9690c86d9402ea61d950c8431b002259e9490c6e9002ca61d950c06b0602ca6059d500eacc02ca60d9d5006acc0016258e84ad1ea402ca6119d4c06acc0016259284acdea4001625928cac5ea4001625928c4adda802ca6159d0c06acc0012259684acdea4001225968cac5ea4001225968c4adda8000e259690ac5ea4000e2596904adda80006259690cadda8001e259690c86d94001a61e9490c6e9002ca61d950c06acc0012259e84acd6a40012259e8cac56a40012259e8c4ad5a8000e259e90ac56a4000e259e904ad5a80006259e90cad5a80016259e90c86d94000e259e94ac52a4000e259e944ad1a80006259e94cad1a80012259e94c86d940006259e950acda8000e259e95086d940006259e9508ed9402ea61d950c8431a02e821d950c8670302e9d9610c48271802c9d9610c68271002e9e1590c48271802c9e1590c68271002e9e1590c48271302ca61d9410c6a9102ca41e15850e9d902ca41e158d069d902ea41e158508df502ca41e1590c69d902ea41e1584c91f502ea41e158c491f502ea41e158c8527d02ca41e1194c69d902ea41e1184c95f502ea41e118c495f502ea41e118c8567d02ea41e0d90495f502ea41e0d908567d02ea41e05908d67d002615928c49edae02ca416119cc69d902ea4161184c9df502ea416118c49df502ea416118c85e7d02ea4160d9049df502ea4160d9085e7d02ea41605908de7d00261d928c496dae02ea4120d9449df502ea4120d9485e7d02ea41205948de7d00261d968c492dae02ea40e059491e7d00261d969048edae00261d9690c86dae02c821d950e8670302e9e1590c48271202e9d9610c48271002c9c1611a4c69d902e9c161184ca5f502e9c16118c4a5f502e9c16118c8667d02e9c160d904a5f502e9c160d908667d02e9c1605908e67d001e25928c496dae02e9c120d944a5f502e9c120d948667d02e9c1205948e67d001e25968c492dae02e9c0e05949267d001e25969048edae001e259690c86dae02e9e1590c48271002e94120d9c4a5f502e94120d9c8667d02e9412059c8e67d0016259e8c492dae02e940e059c9267d0016259e9048edae0016259e90c86dae02e900e059c9667d0012259e9448edae0012259e94c86dae000e259e95086dae),
  (0x80eae2a22baa88aeaa2544a8aae4a0, 50, 0x6ea49c1518e1bb006c269c9518e1b7006c269c94d921b7006241e948ed9252006c269c90d961b7006241e908ed9652006241e8c92d9652002615928cadc69d006c269490d9e1b70062416908ed9e5200624168c92d9e5200261d928cad469d00624128c96d9e5200261d968cad069d00261d9690acc69d006269c950d82f14006c1e9490da61b70061c16908eda6520061c168c92da652001e25928cad469d0061c128c96da652001e25968cad069d001e259690acc69d00614128c9eda6520016259e8cad069d0016259e90acc69d0012259e94acc69d02ea61d950c8071b02e82259d508c70500602a49d518ef0500582a49d520ef0502ea61d950c8071402c6259c1508e9bb005a41e9490ee29302c4261d9508e9b702ea41e158d085f902c4261d94c929b702ea41e1590c85f902ea41e158c4925202ea41e15908c68002c4261d90c969b702ea41e1194c85f902ea41e118c4965202ea41e11948c68002ea41e0d904965202ea41e0d9490680002694920d85ee9d02c4261590c9e9b702ea416119cc85f902ea416118c49e5202ea416119c8c68002ea4160d9049e5202ea4160d9c9068000269c920d856e9d02ea4120d9449e5202ea4120d9c9468000269c960d852e9d00269c961184ee9d02c82259d528c70502c41e1590ca69b702e9c1611a4c85f902e9c16118c4a65202e9c1611a48c68002e9c160d904a65202e9c160da490680001ea4920d856e9d02e9c120d944a65202e9c120da494680001ea4960d852e9d001ea4961184ee9d02e94120d9c4a65202e94120da49c6800016a49e0d852e9d0016a49e1184ee9d0012a49e1584ee9d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_36 : blocksOK 11 56 P11 P12 955 133 B12_36 = true := by decide +kernel

def B12_37 : List (ℕ × ℕ × ℕ) := [(0x80eae2a32b8a8cae2a3546a8eae55c, 56, 0x2ea61d950c8431e02c8e259d5006b0f02c92259d4c06b0f02c920da5d406af702c96259d0c06b0f02c960da5d006af702c9611a5cc06af7002e94904e1da53802c9e25950c06b0f02c9e0da55006af702c9e11a54c06af7002e9c904e15a53802c9e15a50c06af7002e9c944e11a538002e9c94520da538002e9c94520da40d002ea49c5518e1bb002ea49c5590e01402ca61d950c06b0f02ca60d9d5006af702ca6119d4c06af7002ea4904e159d3802ca6159d0c06af7002ea4944e119d38002ea494520d9d38002ea494520d9c0d002ea49c5610d81402ca61d950c06af7002ea49c4e119538002ea49c520d9538002ea49c520d940d002ea49c560d9138002ea49c560d900d002ea49c56118c0d002e9c94520da40302ca61d950c42b1c02c82259d504eb0602c42259d508eb0602e82259d504cb0402ca59e150c42b1902c659e150c82b1102ca59e150c42b11002a59c946d0e1d802ca61d950c42b1902c661d950c82b1102ca61d950c42b11002a61c946d0d9d802ca61d950c42b15002a61d9450cae98002a61d9490c6e980029e159084ee59702ca61d9410c6a9a02ca41e158d069fa02ca41e1590c69fa02ca41e15904ea8202ca41e1194c69fa02ca41e11944ea8202ca41e0d9452a82001eac9450e1a57102ca416119cc69fa02ca416119c4ea8202ca4160d9c52a820016ac9c50e1a57102ca4120d9c56a820012ac9c54e1a571000eac9c5521a5710026ac9c5518e16502c42259d528cb0602c82259d504eb0402c42259d508eb04001a69c946d0e06902ea59e150c40b11000a59e946d0e1d8000659e94ad0e1d80021e94906cda45d02c9c1611a4c69fa02c9c1611a44ea8202c9c160da452a820016aca450e19d7102c9c120da456a820012aca454e19d71000eaca455219d71001eaca45518e16502ea61d950c40b11000a61e946d0d9d8000661e94ad0d9d80019e94906ce245d02c94120da45ea820012aca45ce19571000eaca45d2195710016aca45d18e165000eaca45d6191710012aca45d58e165000eaca45d592165000a61d9690c6e980009e159284ee5970005e159288ee59702ea61d950c8431d),
  (0x81aac2a02b2a88acaa654d0662c8a6, 48, 0x2c261d8550caae402ea61d950c8432702ea61d914c8432602ea61d914c8432502ea61d950c8432602ea61d950c8432502ea61d950c8432402ea61d950c8432302ea61d950c8432202ea61d914c8432102ea61d950c84321026acd490059e0b9026acd4109e1861502ea61d914c8432002ea61d950c84320026acd4108619cc102ea61d9500c86de02ea61d8150c86d200d6a61d80852e4102ea59e150c8431f02ea61d950c8431f02ea61d94050c87002c9c1611a684d4802ea41e158490cb602ea41e118494cb602ea41611849ccb802c86019d528e6eb02cc416119e8a4d1),
  (0x81aacaa02b0a88acaa654d0662ca26, 48, 0x2ea61d950c8432c026acc495219c32a02ea61d914c8432b026acc491619c32802ea61d950c8432b026acc495219c328001e1590aac4e72502ea61d950c8432a02ea61d950c8432902ea61d914c8432802ea61d950c8432802584d4902e9e154026ac14d0859e20b026acc4149d9220a026acc4109d9620a02584d410ae9e14102ea61d9500c86e102ea61d8150c86d300d6259e80852e3e026acc4815219ed30214ec86819d263e02c9e15902684d5402c9e1411a684d4102ea61c158490e0a02ea61c118494e0a02ea416119c84e0b02ea61d950c8071f02c9e141184ea635)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_37 : blocksOK 11 56 P11 P12 955 135 B12_37 = true := by decide +kernel

def B12_38 : List (ℕ × ℕ × ℕ) := [(0x81eac2a12b0a88ac2a754f0622c518, 48, 0x2ea61d950c8433202ea61d914c8433102ea61d950c8433101eacd4502618a1a026acd4901e1861a02e9e259500c4ae202e9e258150c4ad702ea61d8150c86d702e9e258150c4ad500d6259e80906e8800d6259e80906e8300d61da68050ae8302e9da6150c40b2a02ea59e150c8072902e9da6150c40b2902ea59e150c8433002e9e25950c40b2a02ea61d950c8072902e9e25950c40b2902ea61d950c8433002ea61d950c8432f02c9e15902468cdb02e9e25950c40b2302ea61d950c8072202e9e25950c40b2202ea61d950c8432e02ea59e150c8432d02ea61d950c8432d),
  (0x81eac2a12b0a8cac2a654f0622c548, 48, 0xd2259c682d4aef02ea61d950c8433600d2259c42ad4ae702ea61d950c80731026acd4901e1861902ea61d9500c86e402ea61d9410c86e302ea61d8150c86d902ea6019d508c6d600d6259e8050ad5100d201a69c54ae6000d625829c50ad4002ea59e150c8072b00d0659e2814af2802ea59e150c8433500d042269d94ae0f02ea61d950c8072b00d0661da814af2802ea61d950c8433500d041a69e14ae0f02ea61d950c8433402c661d9014a8cd902ea61d950c8072602ea61d950c8072502c42259d0a94f2100d066019c96ae0e02ea59e150c8433302ea61d950c84333),
  (0x81eac2a12b0a8cac2a754f0622c558, 50, 0xd6259e842d0af600d6259c286d0aef00d2259c286d4aef001e1590a86e4eeb02c661d950c82b3200161d90a86e4eee00121d94a86e4eee002c9e9450e1a6470246cd4901e1aa1b02ea61d914c8433b02ea61d950c8433b026acd410985e2b302c661d9500caae502ea61d8150c86e402c661d8150caada02ea6019d508c6d700d2259e8086d5e000d625829c906e8800d625829c6d0a9f002acd4905e1a61602c659e150c82b2c026acc0951a1c72a02ea59e150c8433a0029d94906ce262e00d626805cad1a3d02c659e150ca833700d602a45d90ae7902c661d950c82b2c026acc095219c72a02ea61d950c8433a0029e14906cda62e00d5a6805cad223d02c661d950ca833700d582a45e10ae7902ea61d950c843390009e159066acd410029c9611a46ce8402ea61d950c8433802c9e1590244e95902ea41e159084e3e02ea41e119484e3e001cae9452258e0002ea416119c84e400009e1592866cdbd02c661d8150caae402c661d950c82b2702c66019d508ead7000ec96905e1a4c000d625805c92ae88000acd6905e1a6140006cd4929e1a6160246cc0951a1eb2a0009d9690662cd480005d9492ace262e02ea59e150c8433702e9c1611a484e6f0246cc095219eb2a0009e169065acd480005e1492acda62e02ea61d950c843370009e1592a46cd41),
  (0x81aac2a22b2a88acaa454d066a48a6, 48, 0xd2259e882c56f100d2259e80ac56e802ea61d950c8433e02c8611a5c294f2400d2259c82ad46e800d0269ca1856ed802e9611a5c084f2402e9e25950c04b2602c861da50294f2102e9e25950c8433d02e961da50084f2102ea61d950c04b2602c86259d0294f2102ea61d950c8433d02e96259d0084f2102ea61d950c8433c02ea61d9500c86ec02ea61d9410c86e600d6a61d80852cdc00d1a61e8ac0573600d2259e8ac0573602ea61d94050c87402ca41e119684d4702e94261d8490cbb02ea41e118494d4702e942611849ccbc02ca61d8410e96e602e941e1184a4cbc),
  (0x81aac2a22b0a88acaa654d066ac826, 48, 0xd2259e882c56da004a61e942d0d9df00d6259e80ac52d9004a61c16ad90e6000d2259e80ac56d9004a61c12ad94e6002ea61d950c8434001cacc41521a6b2a004a61412acd9e2e02e9e25914c8433f02e9e25950c8433f024acc415219eb2a0049e1412acda62e02ea61d914c8433f02ea61d950c8433f01cacc41521aa72f005a61e9500caef3005a61e8150caeea00d6269d80852ea2004a61e8150daeee00d6269d88412f3b02ca61d94050e9df005a61c1690cae9b02ca61c158690e6002ca61c118694e6002ca6141184e9e2e02ca61d8150e86ee02c9e141184ea62e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_38 : blocksOK 11 56 P11 P12 955 138 B12_38 = true := by decide +kernel

def B12_39 : List (ℕ × ℕ × ℕ) := [(0x81aac2a22b2a88acaa654d066ac0a4, 48, 0xd2259e882c56e9005a69c942d0e07500d6259e882c52e8006241e94ad90d0a00d2259e882c56e8006241e90ad94d0a02ea61d950c8434202c9e25950c06b27004ec1690a619cc000d29ca618542f4000d69ca618502f4002ca61d950c06b27004ec16909e1a4c000d2a49e18542f4000d6a49e18502f4002ea61d950c8434102ea61d9500c86f402ea61d8150c86eb00d6259e80ad06a3006269c8150daeeb005a69c8150e2eeb02ca61d94050e87502ea41e1590c869c02ea41e158490d0a02ea41e118494d0a02cc41611a689cc002ca61d8150e86eb02cc416119e8a4c0),
  (0x81aac2a32b0a8cac2a654d066ac144, 48, 0x66ac94118de25200d6259c28ad06f000d2259c28ad46f000642e94921d8e0002ea61d950c84344005c2e9492258e0002ea61d950c84343004d6118289ee5bf00660196908dee4f00c661d82892d5c200d601a69cad06a102e80661d9490dff004c21690ae5da4700d602a49d852e56004c19690ae5e24700d582a49e052e5602ea61d9410c869d00660194928dee4f02c80661d9690dff),
  (0x81aacaa22b0a88ac2a654d066aca06, 48, 0xd2259e882c56d1006a61d9410cae9f00d6259c28ac52d0006a41e1590ace8300d2259c28ac56d0006a41e1194ace8300d6259e88502f410069e25950c0af39006a416119cace840194ec0689e5232f0190ec0689e5632f00d6259e88502f43006a61d950c0af390069c1611a4ace840194ec068a5d232f0190ec068a5d632f02ea61d950c84345006a61d9500caef5006a61d8150caeed00d6259e80852ea00194ee8481d226b30214ee8481d1a6b302ea61d9410c869f006a61d9410cae9e02ea41e159084e8302ea41e119484e8302ea416119c84e84004a61d8150eaeed02e9c1611a484e84),
  (0x816ac2a02b4a94ad2a554b16852458, 48, 0x2c26099d504eae200a1c56902da4d0d02c26099d44d2b23008ec1c56921a61502c26099d04d6b23008ec1c52961a615001c54d2a1a4aed802c26099504deb23008ec14529e1a61500145cd2a1a4aed800105cd6a1a4aed80261c54d02d8a90d00a1c5412ad8e519026ac1c54d218a15026ac1c50d618a15026ac1450de18a1502ea61d9500c86f902ea6019d504cadc02ea6019d50c4add026ac40dd51a0adb026ac40dd5218adb02ea61d940904c7a02c5c1611a4e891202ea41e1588d04b702ea41e1188d44b702ea4161188dc4b702cca019d52866dd02c5c16118a8e512),
  (0x816ac2a02b4a94ad2a554b16852c5a, 50, 0x2c26099d50c6b0702ea61d950c8434802ea6119d4c8434702588d05d42ae32702ea6159d0c8434702588d45d02ae327001e1590c6ae4ae8001e0994d286e5de02ea61d950c8434702588dc5502ae32700161d90c6ae4ae80016099cd286e5de00121d94c6ae4ae80012099cd686e5de000a1d94d286e4730021e94d04ada653026acdc54091a0880261c14d06d8a90d026ac1cd449920b9026ac1cd45218a14026ac1cd049960b9026ac1cd05618a14001ea61590c86e01026ac14d0499e0b9026ac14d05e18a140016a61d90c86e010012a61d94c86e0102ea61d950048efa02ea6019d504cade02ea6019d50c4ade02ea6019d50c4acd026acc05d51a0ade02ea59e15048c34602ea59e150c84346026acc05d5218ade02ea61d95048c34602ea61d950c84346026acc05d5218acd02ea61d940904c8802cdc1611a44a90d02ea41e158850cb902ea41e1590c4a1402ea41e118854cb902ea41e1194c4a14001eacd45209a60102ea41611885ccb902ea416119cc4a140016acdc5209a6010012acdc5609a601000de96118a46e5302cca019d52866f402cc2099d52866dd02c42099d528e6dd02600c85d529aedd02e9c16118864d4902e9c1611a4c4a6402cc81e15928663302cc81e11968663302580c85d52a2edd02cc816119e86633)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_39 : blocksOK 11 56 P11 P12 955 143 B12_39 = true := by decide +kernel

def B12_40 : List (ℕ × ℕ × ℕ) := [(0x816ac2a12b4a90ad2a554b16852d1a, 50, 0x2c261d8950c6b0b02c4a259529c0f4702ea61d914c8434e02c4a11a5429cf2602ea61d950c8434e02c4a15a5029cf2602e96119e4048f3e00244a1590deacbb02e9e25950480f4702cde09950066b2302e9e11a54048f260014ca1d92a46e0e02e9e15a50048f260010ca1d96a46e0e00269e1590c86cbb02ea61d950c8434d02ea61d950c8074702c66099500deb2302ea6119d40c87260014660990deae0e02ea6159d00c87260010660994deae0e001ea6159048ecbb02e9e25950048f2302cca1d95028672e0016a61d90c86e0e0012a61d94c86e0e02e9e25950048efb02e9e01a5504caec02ea6019d50c4aec02e82259d50c4ad202ea59e150c8434c02c49a61529cc34902cc99e152a4434902ea61d950c8434c02c4a259529cc34902cca1d952a4434902ea61d950c8434b02e9e25940904c8b02cdc1611a44a8be02e9c26158850cbd02ea41e1590c4a2202e9c26118854cbd02ea41e1194c4a2202ea61d950c8434a02ea4161188dc4be02ea416119cc4a2902c640a1590e9e2202c640a1194e9e2202cca019d52866ec02cc21d89506a6d202c42258950e9ed202ea59e150c8434902e9c16118864cbe02cdc1611886a62902cdc0a15906a62202cdc0a11946a62202ea61d950c8434902cc816119e86629),
  (0x816ad2a02b0a94ad2a554b16912458, 48, 0x2ea61d950c8435100a9e14502da4e6202ea6119d4c8435002ea6119d4c8434f02ea6159d0c8435002ea6159d0c8434f001e14518e8ae6d602ea61d950c8435002ea61d950c8434f00161c518e8ae6d600121c558e8ae6d60261c54d02da89130261c5410eda8910026ac5c14c99220b026ac5c10c99620b026ac5410c99e20b026ac5cd5018a2fe02ea6019d504cadf02ea6019d50c4ae0026ac40dd51a0ae0026ac40dd5218adf02c5e159024e891302c5e1411a4e891002ea61c1588d060b02ea61c1188d460b02ea6141188dc60b02ea61d95040cb4602e9c1611a4c8661),
  (0x816ad2a12b0a90ad2a554b16912518, 48, 0x2ea61d950c8435600aa614502cdda1202ea61d914c8435502ea61d914c8435402ea61d950c8435502ea61d950c8435400245611a89cef2102e9e25950084f5000aa614502cd9e2d02e9e11a5404cb3502e9e15a5004cb3502688ec1d5205ad702ea61d950c8074f026ac08dd6190728026ac08dd219472802ea61d9500c872902ea61d9500c86ff0054c99e82252e4202ea6019d50c4aee02ea61d950c8435302ea61d950c8435202c6615901ce88d202c6614119ce88cf02ea61c1588d060f02ea61c1188d460f02ea6141188dc61102c6601950de8b4902e9c1611a44ca2e),
  (0x816ad2a12b0a90ad2a554b16912d1a, 50, 0x2ea61d950c8435d02ea61d950c8435c02ea61d914c8435b02e9e11a54480f5502ea61d950c8435b02e9e15a50480f55001e1590eac867260024499690de2cbc01eac48255218ee402e9e25950480f5002e9e11a54048f2b0014c99e92246e0f02e9e15a50048f2b0010c99e96246e0f00261d9690c86cb600188d452a61ee0d00099cd6906e261d026acc81d52186e402ea61d950c8075002ea6119d40c872b001449a6921cee0f02ea6159d00c872b001049a6961cee0f001e25969048ecb602e9e25950048f2a02ea61d9500c4b300016259e90c86e0a0012259e94c86e0a02e9e25950048f0002e9e01a5504caef02ea6019d50c4aef02e82259d50c4ad302ea61d950c8435a02ea59e150c04b5302e9da615040cb530210ec4a81a5d62802ea61d950c04b5202e9e2595040cb520214ec428a519eb402cde1590244a8bf02cde1411a4688d802e9e24158850e1002ea41e1590c4a2402e9e24118854e1002ea41e1194c4a240008ec5691a5e22202ea416119cc861202ea416119cc4a2b02e9e2591448c35902e9e2595048c35902ea61d950c04b4c02cc21d9506a4b1f02c4225950e9cb1f002259e950c86f4902e9c1611a448e1202e9c1611a44ca2b02ea61d914c8435902ea61d950c8435902ea61d950c8435802ea61d950c84357)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_40 : blocksOK 11 56 P11 P12 955 148 B12_40 = true := by decide +kernel

def B12_41 : List (ℕ × ℕ × ℕ) := [(0x816ad2a12b0a94ad2a554b16912558, 50, 0x2ea61d950c84363008de145025ae94a02ea6119d4c8075c00aa61c146cd1a1202ea6159d0c8075c00aa61c106cd5a12001e15904eaca6d9001cc99692246e0202ea61d950c8075c00aa614106cdda1200161d904eaca6d90014c99e92246e0200121d944eaca6d90010c99e96246e0200261c5590e8ac6e0019c54d28ae264c002c5cd6918a24c8026acc81d52186e200a9e14106da4e62026ac08dd619072a02c66119d40e8b37026ac08dd219472a02c66159d00e8b37001e245590e8addd026ac08d5219c72a02c661d9500e8b370016245d90e8addd0012245d94e8addd00aa61c5500edb0102ea6019d50c86ff009a6005d50eaef302e82259d50c4ae000aa6005d50edaff02ea61d950c8436200a82245d50daee002ea61d950c8436100aa61c550ed835f02ea61d950c8436002ea61d950c8435f02cde1590244a94a008de141066ad94302ea61c1588d0612009a41e1450eae3102ea61c1188d4612009a41e1054eae31001cec5692258a0202ea6141188dc612009a416105ceae310014ec5e92258a020010ec5e96258a02009a6005d50eaf0902cc21d950668b4600982245d50eaedb008c21c551a6af460005d94d2aca264c02e9e14118864e620099c161064eae66009a6105d40eaf37009a6145d00eaf3702ea61d950c8435e009a61c5500eaf37),
  (0x816ad2a12b0a94ad2a554b16912d5a, 52, 0x2ea61d950c8436802c661d950c82b6302c66119d4c82b5d02c66119d4c82b5602c66159d0c82b5d02c66159d0c82b56001e1590e86ca6e4002cca9451a5e0d202c661d950c82b5d02c661d950c82b5600161d90e86ca6e4002cca9c51a560d200121d94e86ca6e4002cca9c55a520d200261d9690c6c87000258a9c54d22c1f0021cd6904ada501002cde9451a248e70021cd5928866c210246cc81d521aae502c661d950c82b5102c66119d40cab2c001da68850ed623d02c66159d00cab2c001da68854ed223d0009a694521ced54002cca94519e251e002cde94521a48e102c661d9500cab2c0015a6885ced223d0009a69c5214ed54002cca9c5196251e0009a69c5610ed54002cca9c5592251e0009a69c5610ec1e02c661d9500cab0202ea6019d50c870002ea6019d50c4af602e82259d50c4ae102ea61d950c84367002a5885d50ee2ff02ea61d950c843660021d94d04aae5220214ee8841a51e4302ea61d950c04b6102ea61d950c843650029e14d06d8a6580214ee804a519eb6000de159066ac93e0029e1590c86e67802cde1590244a95702cde1411a44a94402c661c1588d2a1302ea41e1590c4a3902c661c1188d6a1302ea41e1194c4a39001cee9452258a0500258a9450dee12a02c66141188dea1302ea416119cc4a390014ee9c52258a0500258a9c50d6e12a0010ee9c56258a0500258a9c54d2e12a00258a9c5520ed8100261d9690c4ac7f02c66019d50cab00000ee885d521a6de02c42259d50e8ae100188de946d22478000658a9d50ee2ff002259e94490ec800021cd6906c9a4e90021d94d2886e52202c5c1611a4caa6302e9c1611a4c4a6902ea6119d4c84364001cee885196627102ea6159d0c84364001cee88559262710009a694521ced4c02c661d950c28b61000de169065ac9450005e14d2ad8a65802ea61d950c843640014ee885d9262710009a69c5214ed4c0009a69c5610ed4c000de1592a46c93e)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_41 : blocksOK 11 56 P11 P12 955 152 B12_41 = true := by decide +kernel

def B12_42 : List (ℕ × ℕ × ℕ) := [(0x81eac2a12b0a98ac2a754f1622c518, 50, 0x2ea61d950c8436b02ea61d914c8436a02ea61d950c8436a001e1590caae46e602ea61d950c8436900161d90caae46e700121d94caae46e7002cdc969061a6460246cd4901e1a8c6026ac1cd49218619026ac1cd09618619026ac14d09e1861a02ea61d9500c870700521d80caae56e902ea6019d508c6e402e82259d5084ed702ea6019d50c86e402e82259d50c4ad702ea6019d50c86d0002ac54d09e1a617026acc09d51a06e402680ec9d51862d702ea59e150c0875002ea59e150c0874f02ea59e15080c75002ea59e15080c74f0029d94d0ac6262d026acc09d52186e402680ec9d5205ad702ea61d950c0875002ea61d950c0874f02ea61d95080c75002ea61d95080c74f0029e14d0ac5a62d026acc09d52186d0002a456119ccae170029c9611a44ee2d0029cd611a44ae2d02c6615901cca8c602ea41e1590c861902ea41e1194c861902ea416119cc861a00261d96904cae4602ea61d950c0874702580dc9506ae32702c66019508deb23000ec54929e1a61502c6601950c9eb23000ac54d29e1a6150006cd4929e1a4c10246cc0951a1eb230022455929ccae150021c9592a44ee2a0021cd592a44ae2a02e9c1611a448e2f0246cc095219eb23001a456129ccae150019c9612a44ee2a0019cd612a44ae2a0006615929ccacc1),
  (0x81eac2a12b0a9cac2a754f1622c558, 52, 0x2ea61d950c8436d02c66119d4c82b6b02c66159d0c82b6b001e1590caac66ca02c661d950c82b6b00161d90caac66ca00121d94caac66ca002cdc969186606b0019cd49286e61c1002cdc969186248d0261cd4902d8691d0246c1cd4921aa1b0246c1cd0961aa1b001e25969086cdda002cdc969205a48d0246c14d09e1aa1b0016259e9086cdda0012259e9486cdda02c661d9500cab0802ea6019d50c870702c66019d508eae502ea6019d508c6e202c66019d50caae502ea6019d50c86e202c66019d50caad10021cd4906daa51a0246cc09d51a2ae5026acc09d51a06e202c659e150c0ab510029c959064ee26202c659e15080eb510029cd59064ae2620029d94d0ae0666c0021cd4906e9a5390246cc09d521aae5026acc09d52186e202c661d950c0ab510029c961064eda6202c661d95080eb510029cd61064ada620029e14d0ad8666c0019cd4906ea25390246cc09d521aad1000de159064aad1a0029c9611a4c6e6c000de1590668ad390029cd611a486e6c0009e1590668ed390029e1590c86e5d102cde1590248691d02c641e1590caa1b02c641e1194caa1b001cec96918661da02c6416119ccaa1b0014ec9e918661da0010ec9e958661da0009e1592866cdc100261d969084ec8d00261d9690c4ac8d02c66019d50cab0702c661d950c0ab4802c66019d508eae20021c96906da4d0d02c66019d50caae20021cd6906da490d0021cd492ad8651a0021cd492ac5a44b0246cc09d51a2ae2000dd969064ae10d0005c9592a4ee2620021c96906cda53a0005cd592a4ae2620021cd6906c9a53a0021cd492ac5a53902c5c1611a4caa6502ea6119d4c8436c02ea6159d0c8436c0246cc09d521aae2000de169064ad90d0005c9612a4eda620019c96906ce253a0005cd612a4ada620019cd6906ca253a0019cd492ac6253902ea61d950c8436c000de1592a486d1a000de1592a44ac4b000de1592a44ad390009e1592a44ed39),
  (0x81eac2a12b4a90ad2a554b16250518, 48, 0xacde94105a624502ea61d914c8436f02ea61d950c8436f00ac641690e19e4600acdc169061a64600a14d042a6d9e5402e9e01a5504caf002ea6019d50c4af000a00d452a59ee0d00980d452a61ee0d02ea61d950c8436e02cde1590244a8cb02cdc1611a4688da02e9c26159048e1f02e9c26119448e1f02ea416119cc862002ea61d950c04b4d02e9c1611a448e20)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_42 : blocksOK 11 56 P11 P12 955 154 B12_42 = true := by decide +kernel

def B12_43 : List (ℕ × ℕ × ℕ) := [(0x81aac2a22b0a90acaa654d1668c826, 48, 0x2c261d950c4ab5c004de169024ad8be02ea61d914c84370005a41e1690cae2302ea61d950c84370005a41e1294cae23001e1690d864af3d01cec841521a6b23004a61412acd9e2a0059e12a5408ef330059e16a5008ef33024acc415219eb23004de1412ac9a62a005a6129d40caf33005a6169d00caf33005a61e9500caf2d005a61e9500caf090059e02a5508eeea005a6029d50caeea005a61e950c0af49005a61e950c0af5802cde159024868be004de1412a49acd702ea41e1590c862302ea41e1194c862302ca6141184e9e2a02ea61d950c0874902cde141184aa62a),
  (0x81aacaa22b0a90ac2a654d1668ca06, 48, 0x2ea61d950c84372004de159024aacd802ea61d914c84371006a41e1590cae2502ea61d950c84371006a41e1194cae25001e1590e864af3c01eac84255218ed0006a416119ccae2d0069e11a5408ef340069e15a5008ef34006a61d950c0af6e026acc41d5218ad00069c1611a48ee2d006a6119d40caf34006a6159d00caf34006a61d9500caf2f006a61d9500caf0a0069e01a5508eeed006a6019d50caeed0194ec8682521eb40214ec8682519eb402cde159024a84d8004de159024aacd602ea41e1590c862502ea41e1194c862502ea416119cc862d006a61d950c0af4b02e9c1611a48c62d),
  (0x81eac2a32b0a94ac2a654f1628c548, 50, 0x2ea61d950c8437402ea61d950c8437302e961da50408f6a02e9611a5c04cb3602e9e15a50804f6a02e9e11a5408c73602e9e15a50084f3102e9e15a50804f6f02ea6159d0c04b6a02ea6119d40c873602ea6159d00c4b3102ea61d9500c873102e9e15a50084f0b00521580caae5ef100921d80c6ae56f102e821d965084ed900d2258086add6f102e822595d0c4ad902e82259d50c86d902e821d965084ed402e9d96250804f5b02e9d96250804f5502e959e250408f5502ea5961d0c04b5402e95a61d040cb5502e9d96250804f5402e959e250408f5402e9e15a50804f5b02e9e15a50804f5502e961da50408f5502ea6159d0c04b5402e96259d040cb5502e9e15a50804f5402e961da50408f5402e9e15a50840f71002a45e1194cae25002a496119cc6e250029cd611a486e2502cde159024868ce02ea41e1590c862602ea41e1194c862702ea416119cc4a2702e9e15a50804f4e02c8215a5069cf2602c421da50a94f2602cc2159d06a4b2002c42259d0e94b2602c8215a5069cf2002c421da50a94f2002e9d96250840f70002245d9294cae230022495929cc6e230021cd592a486e2302e9c1611a484e2702e9e15a50840f70001a45e1294cae23001a496129cc6e230019cd612a486e23000de1592a486ccc),
  (0x81eac2a32b0a94ac2a754f1628c558, 52, 0x2ea61d950c8437702c661d914c82b7402c661d950c82b7400261590a86dceec02c5e2595080eb6b00161d90e86e4aef00121d94e86e4aef00261d9690c6c86c002cde94509a6245002ca69451a1cce202c661d950c0ab6b00162590a86dceef00122594a86dceef001e25969086cc6c002ca6945219cce202c661d9500cab3200161da69086cddb00121da69486cddb02c661d9500cab0c02ea61d8150c870b00921d80e86e56f202e821da55084ee400d22580a86dd6f202e82259d50c4ae402c42259d50caada002acd490659e20c02c659e150c0ab5d02ea59e150c0875c02c659e150c0ab56002a594906cde21202c5da615080eb560029d94d06ca621202ea59e150c84376002acd490661da0702c661d950c0ab5d02ea61d950c0875c02c661d950c0ab56002a614906cdda1202c5e2595080eb560029e14d06ca5a1202ea61d950c84376002acd490659e20702c661d950c82b72000de159064aacd8002a496119cc6e3c000de1590668ad290029cd611a486e3c000a615905e8ed290029cd611a44ae7302cde159024868dd02c641e1590caa2802c641e1194caa280024ae9450dda0b402c6416119ccaa300014ee9c522589fb0010ee9c562589fb000de1592864adb402c661d8150cab0b02c82259529c4f4702c421da550a8ee4000ec9690659e0b902c42259d50e8ae4000acd6905da60b90006cd492a59e20c0022496906d9cd0602c659e150c0ab5c000dd969064ae0be000659492acde212000ec9690661d8b20005d94d2aca6212000acd6905e258b20006cd492a61da0702c5c1611a48ea300014aea4521d8dfb0010aea4561d8dfb000a6159285cedb402c661d950c0ab5c000de169064ad8be000661492acdda12000ec9690659e0b20005e14d2aca5a12000acd6905da60b20006cd492a59e20702ea61d950c84375000de1592a486cd8000de1592a44ac37000de1592a44ad29000a615929c4ed29)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_43 : blocksOK 11 56 P11 P12 955 157 B12_43 = true := by decide +kernel

def B12_44 : List (ℕ × ℕ × ℕ) := [(0x81aac2a22b0a98ac2a754f162ac018, 48, 0x56aca41e118e7f00542ea49e118dfb00502ea49e158dfb001e1590e8ae46f002ea61d950c087750021cd690a6d865602ea61d950c0876c02c945201a4dea5d0056259e80c92df102e805611a49ce05005625829cd0ae8602e8056119cca63a005625829c92cea802e805611a49cdfd02ea59e150c087640054ee809e125a71002259c9504eaf3702ea59e150c8437802ea61d950c087640054ee809d926271001a61c9504eaf3702ea61d950c84378002a61d9504caf3802cde1590268855e02c805611a69ce05005625809cd2ae8602cc056119e8a61402c805611a69cdfd002259e9504caf37001a61e9504caf37),
  (0x81aacaa22b0a98ac2a654d166aca06, 50, 0x2ea61d950c8437a004de159024ae94402ca6119d4c06b72006a41e1590cae3c02ca6159d0c06b72006a41e1194cae3c001e1590e8ac66d0001cc6949225ae0402ca61d950c06b72006a416119ccae3c00161d90e8ac66d00014c69c9225ae0400121d94e8ac66d00010c69c9625ae0400261d9690c86c6d0019cd690a6c624a0021cd69086da4f60004de9491a26ce6024acc41d521aad10069c1611a4cae6c006a6119d40caf3902ea6119d40c8738006a6159d00caf3902ea6159d00c8738001e259690c86ddc0004de94921a6ce6006a61d9500caf3902ea61d9500c87380016259e90c86ddc0012259e94c86ddc006a61d9500caf0d006a6019d50caf0a006a6019d50caef5002acc49d521a6ce0194ee8482521eb6006a59e150c0af5f02ea59e150c843790214ee8482519eb6006a61d950c0af5f02ea61d950c84379019cee84825522b702cde15902486944004de1590268ad5f02ea41e1590c863c006a41e1590cae3702ea41e1194c863c006a41e1194cae37001cee949225860402ea416119cc863c006a416119ccae370014ee9c922586040010ee9c96258604004a6019d50eaf0a000ee849d521a6cd000acc69d521a6ce0021cd690ac5a4f6004a59e150c2af5f02e9c1611a4c866c0069c1611a4cae67006a6119d40caf38006a6159d00caf38004a61d950c2af5f006a61d9500caf38),
  (0x81aacaa22b0a98acaa654d162aca22, 50, 0x2ea61d950c8437c0049e14d02da6a6302c92259d404eb5602ea6119d4c0877602c96259d004eb5602ea6159d0c08776001e14d1a886e6d7001d869490ee622c02c9e2595004eb5602ea61d950c0877600161cd1a886e6d70015869c90ee622c00121cd5a886e6d70011869c94ee622c00261d9690cac46f0019cd69086e264b002cde94918624c702ca61d95004eb510069e14d02d8a66c02ea6119d40c873a001d86a49214ee7902ea6159d00c873a001d86a49610ee790005a694921ced2402ea61d9500c873a001586a49e10ee790005a69c9214ed240005a69c9610ed2402ea61d9500c870e02e82259d5084eff00d586a48212de8c02e82259d50c86df02ea59e150c0876600285a49d50e2ee002ea61d950c8437b02ea61d950c0876502ea61d950c0876000dd8680a6d522b802ea61d950c8077902cde1590248692602cde1411a68855c02ea41e1590c863d02ea41e1590c863802ea41e1194c863d02ea41e1194c8638001cee94922585fd02ea416119cc863d02ea416119cc86380014ee9c922585fd0010ee9c962585fd00059e94920e6cfb02c82259d5284eff00186a49d50e2edd02c82259d50e86df00085a69d50e2ee0000dd9690a462d0002e9e141184ca66d02e9c1611a4c866802ea6119d4c8077802ea6159d0c8077802ca61d950c2876002ea61d950c80778)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_44 : blocksOK 11 56 P11 P12 955 161 B12_44 = true := by decide +kernel

def B12_45 : List (ℕ × ℕ × ℕ) := [(0x81eac2a32b0a9cac2a754f162ac558, 54, 0x2ea61d950c8437d02ca6119d4c06b7702ca6159d0c06b77001e1590e8ac66cb02ca61d950c06b7700161d90e8ac66cb00121d94e8ac66cb00261d9690c86c65002ea49c550da184002ea49c5590e02202ca61d950c06b6d001e2592886d4ef6001e2596886d0ef6002ea494521d8d33002ea49c5610d8220016259e886d0ef6002ea49c52158d33002ea49c56118d33002ea49c56118c0402ca61d9500c6b0f02ca6019d50c6b0c02c66019d50cab0c02e82259d5084f0700d62582886d1ef702c82259d50c6ae502c42259d50caae50021cd4906da690e02ca59e150c06b6802ca59e150c06b6302c659e150c0ab63000dd9490662e94a02ca59e150c42b7c0009d94d06e26a630005d94d0ae26a630021cd4906e9a53c02ca61d950c06b6802ca61d950c06b6302c661d950c0ab63000de149065ae94a02ca61d950c42b7c0009e14d06da6a630005e14d0ada6a630019cd4906ea253c02ca61d950c42b7a000de159064ae944000de1590a46e944000de1590a46ac550009cd611a46ea850029cd611864ad8a0029cd6118a46d8a0029cd6118a46d6602cde1590248696202ca41e1590c6a4302ca41e1194c6a430026ac9450dda14d02ca416119cc6a430026ac9c50d5a14d0026ac9c54d1a14d0026ac9c55218d700026ac9c54d1a01902c66019d50e8b0c02c82259d5284f0702c42259d5288f07000ee9c94651a08802c42259d50e8ae50021cd6906da490e0021cd690ada450e0019cd690ac6602402c659e150c28b63000dd9690662c94a000dd9690a62c54a000dd9690a46e0250005d94d2ae24a630021cd6906c9a53c0021cd690ac5a53c0021cd690ac6581802c9c1611a4c6a70001eaca452158e7f001eaca456118e7f001eaca455218d6d02c661d950c28b63000de169065ac94a000de1690a5ac54a000de1690a46d8250005e14d2ada4a630019cd6906ca253c0019cd690ac6253c0019cd690ac660180016aca45e118e7f0016aca45d218d6d0012aca45d618d6d000de1592a46c944000de1592a44ac55000de1592a486c55000de1592a486c0f0009cd611aa46d8a0009cd611aa46d660005cd611aa4ad66),
  (0x81aacaa22b8a88ae2a2545286aca06, 48, 0xc6a49c1521adcc00ec269c951861c400da41e9492c624a00e241e9492d865500da41e9096c624a00e241e9096d865500261592885cef4300da416909ec624a00e2416909ed865500261d928854ef4300261d968850ef4302ea61d950c8437e00d9c1690a6c624a00e1c1690a6d8655001e25928854ef43001e25968850ef430016259e8850ef4302ea61d950084f14004e259c1528adca00c4269c951ae1c4006a41e1590caea6006a41e1590cae5000e241e94905ae55006a41e1194cae5000e241e90945ae55006a416119ccae5000e2416909c5ae550069c1611a4cae5000e1c1690a45ae55),
  (0x816ac2a52b0a94ad2a554b56812d5a, 52, 0x2ea61d950c84383008661e942d18dee02c52259d40a8f63008661c16ad90e6302c56259d00a8f63008661c12ad94e63001e15928c6ca6da002588d452ade23a02c5e259500a8f63008661412ad9ce6300161d928c6ca6da002588dc52ad623a00121d968c6ca6da002588dc56ad223a002e9cd4518a60d4002e9cd451a4a127002ea4dc5518a1b6002ea4dc5590a039002ea4dc5592083f02c661d9500a8f630085e1412ada4e63001625928c6c9eda001d88e452ad623a001225968c6c9eda001d88e456ad223a002ea4d45189e0d4002ea4d4519ca127002ea4dc5611883e0012259e8c6c96da001588e45ead223a002ea4dc518960d4002ea4dc5194a127002ea4dc558920d4002ea4dc5590a1270009a4dc5612ac0802ea61d950048f1102cc2259d504ab0102c42259d50cab01002ace45d518a2f9008c2269d5186f0e008c2269d506dafe0009a4dc552ae1b600842269d50edafe002259cd4492ac9302ea61d950c8438202ea61d95048c38102ea61d950c84381002a61cd46d189e2009a61e950ec437f000e61d94492ade40009a4dc5612ac3e000661d94c92ade402c661d940928dee02ea61c159048ea702c661c158a90e6302ce41e15904aa7a02c661c118a94e6302ce41e11944aa7a0026acd45189e23a0026acd4519ca27202c6614118a9ce6302ce416119c4aa7a0026acdc5189623a0026acdc5194a2720026acdc5589223a0026acdc5590a27200099cd452a6e12702cc2259d5284b0e02cc2259d504aafe02c42259d50caafe002269cd46d1889302ea61d950c84380000e69d944922de80009a4dc56922c3f000669d94c922de802c5e14118aa4e6302cdc1611a44aa7a001eace45189623a001eace45194a272001eace45589223a001eace45590a2720009a4d4529ee12702ea61d950c8437f000e61e946d189e4000661e94ed189e40016ace45d89223a0016ace45d90a2720009a4dc5296e1270009a4dc5692e127000e61e95904aeab)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_45 : blocksOK 11 56 P11 P12 955 164 B12_45 = true := by decide +kernel

def B12_46 : List (ℕ × ℕ × ℕ) := [(0x816ad2a52b0a94ac2a554b56902d5a, 52, 0x2ea61d950c84384008e61d94106eaac02cd2259d404ab7a008e41e15906ea8502cd6259d004ab7a008e41e11946ea85001e15928c6ca6d1002688d451ade26a02cde2595004ab7a008e416119c6ea8500161d928c6ca6d1002688dc51ad626a00121d968c6ca6d1002688dc55ad226a002e9cd4518a6115002e9cd45225892f000aa4dc5521adcc001a69cd4492e090000aa4dc55922c49002ea4dc5592084102ce61d95004ab7a008dc1611a46ea85001625928c6c9ed1001e88e451ad626a001225968c6c9ed1001e88e455ad226a002ea4d45189e115002ea4d4521d892f000aa4dc5611ac49002ea4dc561188410012259e8c6c96d1001688e45dad226a002ea4dc51896115002ea4dc5215892f002ea4dc55892115002ea4dc5611892f000aa4dc5611ac0b02ce61d95004ab1500a82259d504ef0d00a82259d50c6f0d002acc865d5922c7019eacc8416126c3002259c55288ef7f002259cd52886f7f002a59cd44922de5021eacc8415926c3001a61c55288ef7f001a61cd52886f7f002a61cd4491ade5021eacc84151a6c4002a61d9450caeaa002a61d94d04aeaa02ce61d94104aaac02ce61d94104aaa902ce41e15904aa8500aa41e1590c6e8d02ce41e11944aa8500aa41e1194c6e8d0026acd45189e26a0026acc8551da1cf02ce416119c4aa8500aa416119cc6e8d0026acdc5189626a0026acc85d15a1cf0026acdc5589226a0026acc85d51a1cf000a9cd45225ad2f008c2259d5286f0d000ee8865d5922c7001a69cd46d0a0900006e88e5d5922c7002269cd4491ac95002259e950c86f7f000e59e944922de5000aa4dc55922c41000659e94c922de502cdc1611a44aa8500a9c1611a4c6e8d001eace45189626a001eacc86515a1cf001eace45589226a001eacc86551a1cf000aa4d4521dad2f001a61e950c86f7f000e61e94491ade5000aa4dc5611ac41000661e94c91ade50016ace45d89226a0016acc865d1a1cf000aa4dc5215ad2f000aa4dc5611ad2f000e61d96904aeaa),
  (0x812adaa42b0a90adaa454956d12224, 48, 0x21eacc80595268e005a61c152accb82009a61c152acc78202c261d95284cb7f021c2e88c591664302e92259d408c76502e92259d404cb6500258a84d2dd62b8021c2e88c595264302e96259d008c76502e96259d004cb6500258a84d6dd22b8021c2e88c595261b00258694d209ee6f00258a94d205ee6f02142e88c59d264302e9e2595008c76502e9e2595004cb6500258a84ded522b802142e88c59d261b0025869cd2096e6f00258a9cd2056e6f02102e88c59d661b0025869cd6092e6f00258a9cd6052e6f00099e94d2066d1c0005a69cd522c9c502142e88c5a51e4302ea61d95008c76502ea61d95004cb65001d8a84e6d522b802142e88c5a51e1b001d86a4d2096e6f001d8aa4d2056e6f02102e88c5a55e1b001d86a4d6092e6f001d8aa4d6052e6f0009a694d205ed1c02102e88c5a5d61b001586a4de092e6f00158aa4de052e6f0009a69cd2056d1c0009a69cd6052d1c02ea61d9500c4b1602ea61d94050c9f502ea61c15890c5f402ea61c15850c9f402ea61c1590c4aaa02ea61c1588c527f02ea61c1588c527702ea61c1584c927702ea61c1188c567f02ea61c1188c567702ea61c1184c9677022409868d51ef6c02ea6141188c5e7f02ea6141188c5e7702ea6141184c9e77022409868dd16f6c022409868dd52f6c02e9e141188c667f02e9e141188c667702e9e141184ca677021c09868e516f6c021c09868e552f6c021409868e5d2f6c)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_46 : blocksOK 11 56 P11 P12 955 167 B12_46 = true := by decide +kernel

def B12_47 : List (ℕ × ℕ × ℕ) := [(0x812adaa42b2a90ad2a454956d12284, 48, 0x2ea61d950c8438500689a41d520ef0e00a86241d518ef0e006259c152accb8002e91a61d404cb6702e92259d408c76602e91a61d404cb6602e91a61d40c4b7b02e95a61d004cb6702e96259d008c76602e95a61d004cb6602e95a61d00c4b7b001e15928ec8673200260694d189ee4000258a94d205ee4002e9da615004cb6702e9e2595008c76602e9da615004cb6602e9da61500c4b7b00161d928ec867320026069cd1896e4000258a9cd2056e4000121d968ec867320026069cd5892e4000258a9cd6052e4000099e94d2066cdb02ea59e15004cb6702ea61d95008c76602ea59e15004cb6602ea59e1500c4b7b001625928ec85f32001e06a4d1896e40001d8aa4d2056e40001225968ec85f32001e06a4d5892e40001d8aa4d6052e400009a694d205ecdb0012259e8ec85732001606a4dd892e4000158aa4de052e400009a69cd2056cdb0009a69cd6052cdb02ea59e1500c4b1702ea59e14050c9f702ea61d94090c5f602ea59e14050c9f602ea41d9610c4aab02ea61d9408c528702ea41d9610c4a7802ea41e1590c867802ea61d9008c568702ea41d9214c4a7802ea41e1194c8678002615928c85ef7502ea6159008c5e8702ea415921cc4a7802ea416119cc867800261d928c856f7500261d968c852f7502e9e159008c668702e9c159224c4a7802e9c1611a4c8678001e25928c856f75001e25968c852f750016259e8c852f75),
  (0x816ad2a52b0a94ad2a554b56912d5a, 54, 0x2ea61d950c84386009a61c150ec6b8302cd2259d4086b6802cd2259d404ab7c02cd6259d0086b6802cd6259d004ab7c001e15928c6ca6e5002e88d4519e252602cde25950086b6802cde2595004ab7c00161d928c6ca6e5002e88dc5196252600121d968c6ca6e5002e88dc5592252600099e94d206e47e002e88dc55926050002269cd4492d891002ea4dc5592084a002e88e45d95201202ce61d950086b6802ce61d95004ab7c001625928c6c9ee5002e88e451961d26001225968c6c9ee5002e88e455921d260009a694d206dc7e002e88e45591e050002ea4dc561188420012259e8c6c96e5002e88e45d9215260009a69cd206d47e002e88e45d9160500009a69cd606d07e002e88e45d952050002ea4dc5611880c002ea4dc5611880202ce61d95004ab1902cc2259d504ab0202c42259d50cab02002acc865d611ac902ce61d950482b8500289a45d520ef0e00289a4dd5206f0e002259cd4492aca3021eacc84195268e02c661d95280cb8202ce61d952804b82002a61cd46d189e6021eacc0495926c3002a61d94490edf4002a61d94c906df4002a61d94c492d7902ce61d9409069fa02ce61c15904aaac02ce61c158852a8a02ce41e15904aa7b02ce61c118856a8a02ce41e11944aa7b001eacd45209a65d0026acc85519e18902ce61411885ea8a02ce416119c4aa7b0016acdc5209a65d0026acc85d1961890012acdc5609a65d0026acc85d59218900099e94d2066ca40026acc85d59216402c42259d5288f02000ee8865d611ac90006e88e5d611ac90018aa4dc6d52066000c9a69d5206f0e002259e94490eca3002269cd46d1885f002259e94c906ca3002259e94c852c2802cde14118866a8a02cdc1611a44aa7b0016ace452099e5d001eacc8651961890012ace456099e5d001eacc8655921890009a694d205eca4001eacc86559216402ea61d950c04b82000e61e946d189e6000661e94ed189e6001a69cd46d2085c0012ace45e09965d0016acc865d921890009a69cd2056ca40016acc865d921640009a69cd6052ca40012acc865d96164000e61d968906df4000e61d968492d790009a69cd6106c29000661d968c92d79)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_47 : blocksOK 11 56 P11 P12 955 169 B12_47 = true := by decide +kernel

def B12_48 : List (ℕ × ℕ × ℕ) := [(0x81eac2a72b0a9cac2a754f562ac558, 56, 0x2ea61d950c8438802cd2259d4086b7d02cd6259d0086b7d001e15928cac66cc02cde25950086b7d00161d928cac66cc00121d968cac66cc002e9cd4918660a5002ea4dc9505a1ab002ea4dc9590603102ce61d950086b7d001625928cac5ecc001225968cac5ecc002ea4d49185e0a5002ea4dc961058310012259e8cac56cc002ea4dc918560a5002ea4dc958520a5002ce49c5611a80502ce61d950086b1e02cc2259d504ab0f02cc2259d5086b0f02cc2259d5086b0802c82259d50c6b0f02c82259d50c6b0802c42259d50cab0800224dc946d1a89d02ce59e150806b8602c659e150c0ab8302ca59e150c06b83000e59c946d229ee02ce59e150806b83000a59cd46d229ee000659cd4ad229ee00224dc946d1a86102ce61d950806b8602c661d950c0ab8302ca61d950c06b83000e61c946d1a9ee02ce61d950806b83000a61cd46d1a9ee000661cd4ad1a9ee001a4dc946d2286102ce61d950806b84000e61d9450aeaac000e61d94906eaac000e61d94852e99c000a61d94d06eaac000a61d94c52e99c000661d94c92e99c002a59cd486d217802ce61d941086aad02ce41e159086a8e02ce41e119486a8e0026acd49185e1f502ce416119c86a8e0026acdc918561f50026acdc958521f50024ec9c5521a96e02c82259d5284f0f02c82259d5284f0802c42259d5288f08002269c946d18c9d02c42259d528cb08002269cd46d1889d002269cd4ad1849d001a69cd4ac5203202ea59e150804f83000a59e946d20dee000659e94ad20dee002269c946d18c61000659e94ed209ee002269cd46d18861002269cd4ad18461002269cd4ac5182a02cdc1611a486a8e001eace4918561f5001eace4958521f5001ceca45521a96e02ea61d950804f83000a61e946d18dee000661e94ad18dee001a69c946d20c61000661e94ed189ee001a69cd46d20861001a69cd4ad20461001a69cd4ac5202a0016ace49d8521f50014eca45d21a96e0010eca45d61a96e000a61d96906ceac000a61d96852cd9c000661d96892cd9c000e59e9486d2178000661d968d2c99c000a59e94c6d2178000659e94cad217802ea61d950c84387),
  (0x82ea82a12a8aa8aa2ab8a82ae2a514, 48, 0x2c261d8d5086b6a02c660d951ca838a02ea61d950c8438b02ea61d950c8438a026ad1c940e184c402c660d9411cab4700561d810aae4ee802c66018d491eb2602ea6019d490c72102c66018d509eb2602ea6019d508c72102ea6019d484d33c0246d008d5a1eb26026ad009d5a0c72102ea59e148d0438902ea59e150c843890246d008d619eb26026ad009d618c72102ea61d948d0438902ea61d950c84389026ad009d584e33c02ea61d940d084c402960d81086e5ee8029e018d0ad4674002c66018d491eb2102c66018d509eb210246d008d5a1eb210246d008d619eb21),
  (0x82ea82a12a8aacaa2ab8a82aa2a550, 48, 0x2c260d9d5086b6900da69c542d0a0c502c260d9d1486b8a02c260d951c86b8a0246d1c940e1a8c50258d1c942ac63480258d009d46ae32700da6805d492e32702ea6019d490c72200da6805d50ae32702ea6019d508c72202ea6019d484d34100cae805d5a25327026ad009d5a0c72200e26805d492db2200e26805d50adb2200cae805d61a5327026ad009d618c72200da6805d492e32200da6805d50ae322026ad009d584e34102c661d940d0a8c50258d009d686e32702d0e019d44a6b4102d0e019d6864b2202c8e019d68653220260d009d686db220258d009d686e322)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_48 : blocksOK 11 56 P11 P12 955 171 B12_48 = true := by decide +kernel

def B12_49 : List (ℕ × ℕ × ℕ) := [(0x82aa8aa22a8aa0aaaaa8aa2aa8aa2a, 48, 0x2152e848258df5b005a61c0d50aeb7000cae8425619d32602d0e1d94268878902ea61d950c8439002ea61d950c8438f02d0e1d96a48438e01eac8425618d32602e9e25940c9078901eac04a56190f3302e9e25948d0438e024ad040d619eb2602ea61d940d0878900d2c069d618a73302ea61d950c8438e01d2c048d61aa73302ea61d9410c874c00961d8292c4e736011625828ac4df3602ea61d950c8438d02152e8481a4de2602e9e25940c850bd02ea61c158d084cc02ea61c158508e2302ea61d950c8438c02ca60c158529e2302960d810ac65f3602d0e1c15868a623),
  (0x82ea82a32a8aa4aa2aa8a82ae8a544, 48, 0x2c261d94d086b7302c4e1da6940938b02e961da44c0938b02e9e15a48c0538b02ea6159d0c04b8b02e9e15a408c534e005e158292cca73e00961d8292cc673e02e8215a5c50cb3d011625828acc5f3e02e82159e448d33d02e821d96484d33d02e9d96248c4139002ea59e150c8078f02ea5961d0c40b8f02e9d96248c4138f02e9e15a48c4139002ea61d950c8078f02ea6159d0c40b8f02e9e15a48c4138f02ea61d950c8439102e9e15a40c850cd02960d810ae45f3e02d02159cc4a6b3d02d021d94c866b3d02c822594d05eb3d02d1d960ca442b8f02d1e158ca442b8f),
  (0x82aaaaa22a2aa0aa2aa8aa8aa8aa8a, 48, 0x1952c868261cf5c0069d8c254ae135500e9e04254ad935502ea61d950c84393018d2c842a5e1770021c2d0e84965b89019c2d068c96638901eac8c0656192d901eac0ca5619073501eac04a55a10f35018c2c8529d66333026ad0c05d618ad9026ac0d1d6188735026ac051d5a08f35018c2d04aa55e33301d2c0c8562a5b3f02ea59e141048f5a00961d812acc673101162580aacc5f3101952c868225ce2702152c8e81a5c62702e9e25940c8521002ea61d940d0862502ea59e140508e2502ea61d950c8439201ea40c8552e1b5402ea59e150084f8d0269c0d054ae1b54),
  (0x82aaaaa22a0aa8aaaaa8aa8a2a8a2a, 48, 0x2152e8c05a49e1302ea61d950c8439400ea61c942d05a0500ea61c14ad1862b021d2c0e85a49610001d0495aa60ef5400eac2485d95235902152c0e85a49e100015049daa60ef5400eac248559d235900261d94aac50f200005a49e952e0e1f021d2c0e8594a688026ac0d1d6188730024ac051d61a8f37021c2d0e8594a60a02142d0e859ca60a02ea61d9410c876102ea6019d50c8752011e2580aac54f3b00ea6009d52d8752021d0d8680a56e3602ea61d940d04a0502ea61c158d0862b00da61c14852ae3102e8c2585c95235902e8c258549d235900da6009d506af580258c051d60aaf37),
  (0x82eaa2a32a0aacaa2ab8a88a6a8554, 50, 0x21d2e8c42594b6700c661c942d1aa30021d2c0e86594b5a001d0d968662cb5202152c0e8659cb5a00150d9e8662cb5200261d94a86cd2d20018d1e94662ca1c002ca69c558d20ba0246d0c1d618ab3200ea61c952d84395001e2594a86cd2d30016259ca86cd2d302c661d9410cab6300ea6009d52c5b5c00950d828662df5602e82259d44c935001162580a86cdeda0028d2c5d60a5b2a011e01a686cd4b3a002ac9d144da620b01952c828660df5600e82249d46d935002ea61d950c84398002a59c946d0e211011e00a684ed5b3a0028d9d146ca620b02ea61d950c8439702152e8c41a49e1302ea61d950c80794021d2e8c41a54a3c002a61c946d18e2b011d80a686cd6376002ad0c5d5a4a35700ea61c952d84396021d0eac40a55a3c002a61d944d0ae2b021d02ac4e558ab202ea61d950c8439602c661d940d0aa3000ea61c14906dab5001d2c968660db5200152c9e8660db5200c66009d52e9b5c0010eac5d60a5b2302c42259d68c93500012c9e94658e0b80004d2e9d60a5b2a0018d1e946ca60b70006c9d168da620b00c42249d6ad93500010d9e9464ae0b8000659c96ad0e211000ad1e94660da1c0004d9d16aca620b02ea61d950c8439502c661d950c82b94001a61e944d0ae29000661c96ad18e2b0006d0e9d5a4a357000661d968d0ae2b)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_49 : blocksOK 11 56 P11 P12 955 174 B12_49 = true := by decide +kernel

def B12_50 : List (ℕ × ℕ × ℕ) := [(0x82aaa2a22a0aacaa2ab8a88aeaa054, 48, 0x21d2e8c8259476502ea61d950c08795021c2d0e89465b5202142d0e89c65b520018d1e94a62c6200268c5d142d8a26f02c9c5601a50ea63005e258288d16f6402e805e15a48d21202ea6019d50c875702e821c558d0a63d011e25828acd473802e805e15a48d20b0268c411d618af76019d2e80a60d4796026804d1d4ada34f0268d1c56018af97021d2e8c81a5463a021d2e808da54638025804d1d60aaf37021c418e8a56d378021d2e808c55a67902ea61d940d0863402c805e15a68d21202ca6019d50e875702d021c558e8a61502c805e15a68d20b024804d1d6ada34f025804d1d628af37),
  (0x82aaaaa22a2aa8aa2aa8a88aaaaa82, 48, 0x2152e8c82585f510068d1d94260ae3d00e86241d518af3a02ea61d950c08797021d2c0e8a585750021d2c0e88655b30011c062688d5af2902152c0e8a585f5002152c0e8865db300114062688ddaf29000d1d9688662f22026ad0c1d618873a0068d9d142ca628402ea61d950c84399021c2d0e8a55872902142d0e8a5d87290068d1d94224af6602e81a61d4850f53011e06a4818d6e40019e06808d256f95021d2e8c81a5464002ea61d940d0863d02ea61d940d0863b02ea59e14048d284011e04268acd5b30011604268acddb3002c81a61d6850f530068d1d96240af97),
  (0x83ea82a32a0abca82af8a1142a8550, 48, 0x2ea61d950c8439a02ca61d9410c6b6d02ca6019d50c6b6b02c66019d50cab6b02ea6019d50c4b6900de2582886d52f602ca6019d4d06b3202c66019d4d0ab32002acdc94661921a011e2582886d4ef602ca6019d50c6b3202c66019d50cab32002ad1c946618e1a00de2582886d52f5002ad1cd458a62b3002ad1cd498662b3019d2cc2886562f6024ad00dd5a06b320246d00dd5a0ab32002a59c946d0e21a00de268086d15b66002acdc562509b95002acdc962505b95011e268086cd5b66002ad1c5624c9b95002ad1c9624c5b95011e02a486d4db79021d2cc288655af6024ad00dd6186b320246d00dd618ab32002a61c946d0da1a00dda68086d16366002acdc55a50a395002acdc95a506395011da68086cd6366002ad1c55a4ca395002ad1c95a4c6395011d82a486d4e379019d2cc2886562f5002a61d944cad2b3002a61d948c6d2b3021d02ac86558f79021cc2ac8655937902c66019d50e8b6b02ca6019d50c6b6902c66019d50cab69001a69c946d0e0c502c66019d4d28b32000acde94661921a0006cde94a61921a02c66019d50e8b32000ad1e946618e1a0006d1e94a618e1a000ad1cd698662b30246d00dd5a28b32000a59e946d0e21a000659e94ad0e21a000acde962505b95000ad1e9624c5b950246d00dd61a8b32000a61e946d0da1a000661e94ad0da1a000acde95a506395000ad1e95a4c6395000a61d968c6d2b3),
  (0x83aa8aa22a8aa8aa2aa8a3286a8a0e, 48, 0xc6a49c1521ae4a00ec269c9505a21e019d2c068a4d636e01952c068a4de36e02ea61d950c8439b026ad041d588e34300d9d1680a6c624a006a6019d50caf6e011e25828854ef4300e011e94a586e1e00d811e94a606e1e018ed0680a5d62ae004e259c1528aeae00c4269c952da21e004a6019d50eaf6e),
  (0x83ea82a72a0aaca82af8a1442a8550, 48, 0x2ea61d950c8439c02ca61d9410c6b7702ca61d8150c6b7402c661d8150cab7402e821da5484d36a00d61d8128ac66cb00d6019d28ae46ef00d6019d286e4aef002ace4945e1921901162580e8ac5ecb011601a4e8adc6ef011601a4e86dcaef002ad1c946618e1900e6019e886d52f302e821da54c4933b02e821da54c8533b01952cc288661f0001952cc28a61c75a01952cc28661cb5a002a59c946d0e22700d5021e8865aeff00d5021e8a5ac75200d5021e865acb520114c226885daeff0114c22689dac7520114c22685dacb52011602a486cddb6002152cc288659f0002152cc28a59c75a02152cc28659cb5a002a61c946d0da2700d5019e88662eff00d5019e8a62c75200d5019e8662cb520114c1a6885e2eff0114c1a689e2c7520114c1a685e2cb52011582a486cde36001952cc28865e30a0029e25944cad2b40029e25948c6d2b4019502ac864de35f0194c2ac85d2635f02c661d8150e8b7402c821da5684d36a02c421da5688d36a000eea4945e190c400d6019d086e6aef000ace6945e192190006ce6949e19219011601a4c86deaef000ad1e946618e190006d1e94a618e1902c821da54e8533b01952cc08661eb5a000a59e946d0e227000659e94ad0e22700d5021c865aeb520114c22485daeb5202152cc08659eb5a000a61e946d0da27000661e94ad0da2700d5019c8662eb520114c1a485e2eb520009e25968c6d2b4)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_50 : blocksOK 11 56 P11 P12 955 179 B12_50 = true := by decide +kernel

def B12_51 : List (ℕ × ℕ × ℕ) := [(0x83aa8aa62a0ab8a82ae8a1546a8a06, 48, 0x12e84e481d9637f006a61d940ec92bf019c06acc952635f019406acc9d2635f002ea4dc95218649021c06acca559379004dd1601a4aea85006811e15a48ee3c006811e15a4cae3c006811e15a4cae17011e84e481ad626a02e82259d508c73802e82259d50c8738019e84ec8125626902ea59e15008c79602ea59e1500c8796011e84c0a62d5a68021e84ec81255a6902ea61d95008c79602ea61d9500c8796011e84c0a5ad6268019e84ec8125626702ea61d9410c86b8004c11e15a68ae3c004c11e15a68ae17004811e15a68ee170012e9cd4a6184c302cc2259d528873802ce59e15028879602ce61d950288796),
  (0x83ea82a72a0abca82af8a1542a8550, 50, 0x2ea61d950c8439d02ce6159d0086b9c02ce61d950086b9c001a69cd486d21b802ce61d950086b9a02ce61d941086b7d02ce6019d504ab7702ce6019d5086b7702cc2259d4852b6b02ca6019d50c6b7702c82259d4c52b6b02c42259d4c92b6b0012cdc94661a8c6011625828cac5ecc011e01a68cad46f6011e01a68c6d4af6000ed1c94661aa1b011e01a6886d4ef6000ad1cd4661aa1b0006d1cd4a61aa1b00224dc946da911401952e80c8661f02019d2e80ca614767019d2e80c6614b67000e59c946d22a30019d2e8086614f67000a59cd46d22a30000659cd4ad22a300012cdc9466298d3011e02a4c86d5b0e011e02a4cac55b65011e02a4c6c95b65002ad1c94660da34011e02a486cd5b65002ad1cd46609a34002ad1cd4a605a3402152e80c8659f02021d2e80ca594767021d2e80c6594b67000e61c946d1aa30021d2e8086594f67000a61cd46d1aa30000661cd4ad1aa300012cdc9465aa0d3011d82a4c86d630e011d82a4cac56365011d82a4c6c96365002ad1c94658e234011d82a486cd6365002ad1cd4658a234002ad1cd4a586234019d2e80c865630d000e61d9450aeab6000e61d94906eab6002a61d9484ed1d2000a61d94d06eab6002a61d94c4ad1d2002a61d94c86d1d2012e80e485d9637f002a61d944ec92bf002a61d948ec52bf002a61d94cac52bf02ce61d941086ab902ca6019d5284f7702c82259d6850f6b02c42259d6890f6b0012e9c946618cc602c42259d68d0b6b0012e9cd466188c60012e9cd4a6184c60012e9cd4a45a038011e01a4c86d6af6000ad1e946618e1b0006d1e94a618e1b002269c946d8d1140006d1e94e618a1b002269cd46d89114002269cd4ad85114019d2cc086616b67000a59e946d20e30000659e94ad20e300012e9c94660d8d3000659e94ed20a300012e9cd466098d30012e9cd4a6058d3011e00e486e95b65000ed1e946609a34000ed1e94a605a34000ad1e94e605a34021d2cc086596b67000a61e946d18e30000661e94ad18e300012e9c94658e0d3000661e94ed18a300012e9cd4658a0d30012e9cd4a5860d3011d80e486e96365000ed1e94658a234000ed1e94a586234000ad1e94e586234000a61d96906ceb6000e61d9684ad1d2000e61d96886d1d2000a61d968c6d1d2000e61d968ac52bf),
  (0x83aa8aa22b8a88ae2a2943286a8a0e, 48, 0x11a69c942c4e2bc00e241e9486d92b002e96259c0c8539b02e9e25940c8539b012269c96c58c39e02ea61d940c8539b02ea61d940c8537e02ea61d950c8439e02ca61d9410c6abc006a41e158d0aeb0006a41e1590caeb000e241e94ac592b001216a49c058ef9b0121ea494058ef9b012269c94058ef9b)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_51 : blocksOK 11 56 P11 P12 955 184 B12_51 = true := by decide +kernel

def B12_52 : List (ℕ × ℕ × ℕ) := [(0x82aa82aa2a2aa8aa2aaaaa0aaaa88a, 48, 0x2ea61d950c8439f005269d940e0ae6d00d269e14058ae6d005259e942e08e6b00d16a61c058af9802d16259c0e8879702d15a61c0688f9700d1ea614058af9802d1e25940e8879702d1da6140688f9700269e15908c6ed500d269e14058af9802d261d940e8879702d259e140688f97001ea615908c6ed50016a61d908c6ed500da69e14104af8000d02a61d485af6200c82a61d505af6200d02a61d5886f7b00502a59d608ef7b02d259e140688e6d005269d940e0ae6b00d269e14058ae6b00d16a61c058af9700d1ea614058af9702d01a61d6884f7b00d269e14058af97),
  (0x82aa8aaa2a0aa8aaaaaaa80aaaaa22, 48, 0x2ea61d950c843a1004a61d142d8ea5c00ca61e942d8525c006a61c152d88e6602c96259c0e85394004ac0d25d96a35700cac06a5d95235702c9e25940e85394004ac0d2559ea35700cac06a559d235700261e95188c6ed4000d259c96862cca02ca61d940e85394004ac0d1d5a6a35700cac069d5a52357001e2695188c6ed40016269d188c6ed400d261e94184af8100d82269d4852f5e02c82259d50e876000c82269d5852f6002ea61d950c843a002ca61d940e8525c005a61c150e8ae6600da61c16850ae6602c8c05a5e95235702c8c05a569d235702c82259d6850f6002c8c059d6a52357),
  (0x82aa8aaa2a0aa8aaaaaaaa0aaaaa2a, 50, 0x21d2c8c0596a68a02ea61d940c853a100ca61e942d8525d00d261c16ad88669021c2d0c8596a613002586950acde37600d2c06a5d94a36400258d0496ade23802142d0c859ea6130025869d0acd637600d2c06a559ca36400258d049ead623802242d0c85969e0c002e851c958e60d000058d1c96ae6232002269d1486d8cfa002ea51c958e04cb000d85249e962c35002259d148c6acea02142d0c85a69e13001d86a50acd637600d2c069d5a4a364001d8d04a6ad6238021c2d0c8596a60c002e8524958de0d000058d2496ade23202142d0c859ea60c002e85249d8d60d000058d249ead62320006a59d1608ec7c02ea61d9410c878202d02259d48e876102c82259d50e8761002ad04a5d618edc00d02269d584af650010d84a5d62aedf002259d1484eacfa0008d8525d62aedf021ead048194e67502ea61d948d007a002ea61d950c807a00226ad0085d94ebf02ca61d940e8525d02d261c158e8866902d261c15848ea7a02d261c1588e86bd02d0c05a5e94a3640026ad04958de23802e96259d0c843a202d0c05a569ca3640026ad049d8d623802e9e25950c843a20006ad1c958e623202d02259d6848f650012e84a5d618edf000ae8525d618edf00106a59d608ef7b002269d14ac58cea02d0c059d6a4a364001ead04a58d623802ea61d950c843a20006ad24958de23202258d0085e96ebf0006ad249d8d6232),
  (0x82ea82ab2a0aacaa2abaa80aeaa554, 52, 0x21d2c8c415aa78500ca61e942d8527002242d0c8559eb6700258d1486e9e36502242d0c85d96b6700258d1c86e9636500261e95908c6ec8002d0c9c55a62921002251c944ee98ee002ea51c9584e089002d0ca45d96a01d021c2d0c86596b67001d8d2486e96365001e2695908c6ec8002d0ca4559e2921002ea51c96058c8e0016269d908c6ec8002d0ca45d962921002ea51c9604d87702ea61d9408c538302c82259d44e936302c42259d48e93630012c8c65d61aae202c42259d50e8b63000ad0c65d61aae20006d0ca5d61aae20018d249c6d6287a019ead0084d6277c00c82269d46d935100c42269d4ad9351002259c944e92d13002251c946cda8ee00c42269d52d8b51002259d144e8ad13002259d148e86d13002a59d148c6e023021d2c8c4196a68a02ea61d944c813a102ea61d948c413a1001261c946d8ea5c02ea61d950c40ba1000a61d146d8ea5c000661d14ad8ea5c002ad249c4d5a081021d0cac4295a685001261d944e8ae69001261d948e86e69002a59c944d22d3b000da51c9606ac8e000a61d950e86e69002a59d144ca2d3b002a59d148c62d3b02ca61d940e8527002ca61c1584e92be0026ad1484d9e36500252c8c559e2a770026ad1c84d9636500252c8c5d962a77000d2c9c56a61921029d8d0086d6277c02c82259d44e935102c42259d48e9351002269c946d90d1302c42259d50e8b51002269d146d88d13002269d14ad84d13001a69d14ac4e02302ea61d948c4139f001269d944e0ae6d001269d948e06e6d002269c946d0d920000d2ca45e95a01d000a69d950e06e6d002269d146c8d920002269d14ac4d920001ead2484d96365001d2c8c65962a77000d2ca4569e1921021d2c8c4196a685001261e946d88e69001261e94ad84e69001a69c946d20d3b000a61e952d84e69001a69d146ca0d3b001a69d14ac60d3b000d2ca45e961921022500ac4dd96ac1001261e95848edd0001261e95884edd0000a61e95904edd0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_52 : blocksOK 11 56 P11 P12 955 187 B12_52 = true := by decide +kernel

def B12_53 : List (ℕ × ℕ × ℕ) := [(0x822a9aa82a2ab0a92acaa614d1628c, 48, 0x226ad0804d59fa1006a5881d4e12f7600aa6041d4d92f7600aa41e14c592f97021c2e891584e794001cc61692e49b30001cc99692e4633002142e891d84e7940014c61e92e49b300014c99e92e4633000261d9692c84f2e0018aa51d604ef4d02688c41d6192f76006881d9624d2f9700a841e15a4d2f97001e259692c84f300016259e92c84f3002e9e1580c90668700de258290856f7502e821d94c906609019e04c290a56f75021d88c290656f7502e899cd4052267402ea61d94090c67302ea59e14050ca7302ea6159d0c843a302ea61d950c843a302d021d94ca8660902e899cd40522673),
  (0x83ea82af2a0abca82afaa1542a8550, 52, 0x2ea61d950c843a402d16259c0c86b9d02d1e25940c86b9d00261d950cac6ac6001a69d14cac61bc002ea51cd588606802d261d940c86b9d001e25950cac6ac6002ea51cd60858680016259d0cac6ac602d261d940c86b8802d02259d44cab7d02d02259d48c6b7d02d02259d484eb6d02d02259d4c86b7d02d02259d4c4ab6d02d02259d4c86b6d00224dc946d9291d02cc2259d5086b7d02cc2259d504ab6d02cc2259d5086b6d002251c946d8e91d02c82259d50c6b6d002251cd46d8a91d002251cd4ad8691d002251cd4ac5a84d019ead00c8562719019ead00c9606785019ead00c560a785001259c946e0ea70019ead008560e785001259cd46e0aa70001259cd4ae06a7000224dc946d1a93d019eacc085612785000e59d146e0aa70000e59d14ae06a70002251c946cda93d000a59d14ee06a70002251cd46c9a93d002251cd4ac5a93d002251cd4ac69852021ead00c855a719021ead00c9586785021ead00c558a785001261c946d8ea70021ead008558e785001261cd46d8aa70001261cd4ad86a70001a4dc946d2293d021eacc085592785000e61d146d8aa70000e61d14ad86a70001a51c946ce293d000a61d14ed86a70001a51cd46ca293d001a51cd4ac6293d001a51cd4ac6a052021ead00c855a715001261d944ecaac3001261d948ec6ac3001261d9484ee9d4001261d94cac6ac3001261d94c4ae9d4001261d94c86e9d4002a59cd486d2187000e61d950ac6ac3000e61d9504ae9d4000e61d95086e9d4002a59d1486ce187000a61d950c6e9d4002a59d14c6ca187002a59d14cac618702d261d940c86ac50026ad14c85da3160026ad1cc855a31602cc2259d688537d02cc2259d684936d02cc2259d688536d002269c946d8d11d02c82259d68c536d002269cd46d8911d002269cd4ad8511d002269cd4ac5904d02c82259d6904f6d002269d146d88d1d002269d14ad84d1d002269d14ac58c4d002269d14ed8491d002269d14ec5884d002269d14ec9844d001a69d14ec86015019d2cc08562a785000e59e946e09270000e59e94ae05270002269c946cd913d000a59e94ee05270002269cd46c9913d002269cd4ac5913d002269cd4ac51852000a59e952e04e70002269d146c98d3d002269d14ac58d3d002269d14ac4d852002269d14ec5893d002269d14ec49852002269d14ec85852001ead24c855a316021d2cc0855aa785000e61e946d89270000e61e94ad85270001a69c946ce113d000a61e94ed85270001a69cd46ca113d001a69cd4ac6113d001a69cd4ac52052000a61e952d84e70001a69d146ca0d3d001a69d14ac60d3d001a69d14ac4e052001a69d14ec6093d001a69d14ec4a052001a69d14ec86052000e61d968ac52c3000e61d9684ad1d4000e61d96886d1d4001259e9486ce187000a61d968c6d1d4001259e94c6ca187001259e94cac6187000a61d96906cdd4000e59e9506ca187000e59e950ac6187000a59e950ec6187)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_53 : blocksOK 11 56 P11 P12 955 191 B12_53 = true := by decide +kernel

def B12_54 : List (ℕ × ℕ × ℕ) := [(0x84ab62822daa414946d524a4a96892, 48, 0x2ea61d950c843a70055eac190ca62fb02ea61cd590843a6006241e9916c8f4c02ea61d158c843a6006241e98d6c934c001a114e8ae45f73001a05508eae5e2602ea61d950c843a6006241e90d6c9b4c0012194e8ae45f73001205588eae5e26000e19528ae45f73000e055892ae5e26001e1a914cac64cd01ea4ac190d462fb01eac24990e1470901eac24992054f4c01eac249920d475801eac2498e05534c01eac2498e114758001a1e914cac662601eac2490e055b4c01eac2490e19475800121e994cac6626000e1e9950ac66260269d6c190c862fb0056c1e990e0a709026ac1d592048f4c0056c1e9920ca758026ac1d58e04934c0056c1e98e10a758001a26908d6c5e26026ac1d50e049b4c0056c1e90e18a758001226988d6c5e26000e2698916c5e2601d6c04990e2a7090056c1a90e1ca75e01d6c049920ea75801d6c0498e12a75801d6c0490e1aa75802ea61d950c843a502e9e24190c856fb006241e990d4af0902ea41e191448f4c006241e9914caf5802ea41e18d44934c006241e98d50af5800196e908e245e2602ea41e10d449b4c006241e90d58af5800116e988e245e26000d6e9892245e2601e2404990d6af09006241a90d5caf5e01e24049914eaf5801e240498d52af5801e240490d5aaf580261c05590caaf090261c1950c86af5e0261c055908eaf580261c0558c92af580261c0550c9aaf58026041950e9caf5e),
  (0x84ab6a822daa414946d524a4a96a92, 50, 0x2ea61d950c843a90261d45890c2eba70261d4d89042eba700120d44aae5db740261d5188c42eba7000e1144aae5db740006114caae5db74001e114e84ae58ce0261d5908c42eba7000e1944aae5d3740006194caae5d374001e194e84ae50ce00061950aae5cf74001e195284ae4cce001e19528cae44ce00249a128d45ec3a01e249810c56eafc01ea42c990d4630001ea42c99054e30000121d4e84ae5a2801ea42c98c552300000e1d5284ae5a2800061d528cae5a280026108e856d9cd501ea42c90c55a300000e1d5a84ae522800061d5a8cae52280026188e856d1cd500061d5a90ae4e2800261892856cdcd5002618928d6c5cd50261d5810c4aeafc0269c2d590c863000269c2d59048e3000012248e856dda280269c2d58c492300000e2492856dda28000624928d6dda28001e114e84ada4d50269c2d50c49a300000e249a856dd2280006249a8d6dd228001e194e84ad24d50006249a916dce28001e195284ace4d5001e19528cac64d501eac1890c625701026ac1950e1c8761026ac195061c8f61001a1d4e84ad2636026ac194c61c9361001a1d5284ace636001a1d528cac6636026ac114c61c9b6100121d5a84ace63600121d5a8cac6636000e1d5a90ac663602ea61d950c843a800921d42ae4c5b9c01522482adcc5b9c02116c82a5cc5b9c02d5e1810c4a6afc02e9c26190c8570002e9c2619048d70000116c8e8625da2802e9c2618c491700000d6c928625da2800056c928e25da28001d520e84a5acd502e9c2610c499700000d6c9a8625d22800056c9a8e25d228001d5a0e84a52cd500056c9a9225ce28001d5a1284a4ecd5001d5a128ca46cd501ea41890c56e30102ea41a10d5c876102ea41a1055c8f6100195e0e84a52e3602ea41a0c55c936100195e1284a4ee3600195e128ca46e3602ea4120c55c9b6100115e1a84a4ee3600115e1a8ca46e36000d5e1a90a46e3602ea61d14c481ba50269c1950c4ae30102e9c1a10ca5476102e9c1a104a54f610018a60e855d2e3602e9c1a0c4a553610018a612855cee360018a6128d5c6e3602e9c120c4a55b610010a61a855cee360010a61a8d5c6e36000ca61a915c6e3602618114c4ae9f8102618114cae9c7a0026181144ae9cfa0026180d44ae9d3a0026100d44ae9dba0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_54 : blocksOK 11 56 P11 P12 955 193 B12_54 = true := by decide +kernel

def B12_55 : List (ℕ × ℕ × ℕ) := [(0x84eb62832d8a454946c526a4e9654c, 52, 0x2ea61d950c843ab02ea61d94d0843aa02ea61d950c843aa001e104d6ac9a74e01aa45c2d0d4a30b01aa41c6d14ca35b01aa41c6cd50a35b00249a128d5c6cbd01ea4982d0d4630b01ea418ad14c635b01ea418acd50635b00245e128d58acbd01aac2450e1d4b5c00121d5a8cac6610000e1d5a90ac6610002d58928e245cb3002d58928c625e440269d582d0c8630b0269c196d08c635b0269c196cc90635b001c66128c996cbd01aac1c50e24975c0012249a8d6c5e10000e249a916c5e10002c99528e1c64b301eac1890e24575c0012245e8d6c9a10000e245e916c9a10002c5d528e18a4b301eac108e186579400121d5a8cac6608000e1d5a90ac66080261d5908c06eba7004e1940aae5d374008e1d406ae59374002aca450e1d5b5a014e24806add9374002ad5c50e249b5a002ad5890e245f5a002ad508c661da09020d6c806a5d9374002a61c50d6c9b5a002a61890d6c5f5a002a6108c6d5da090029e1950cac675a0029e114c6ca5a090029a114cac65e0902e9e18250c8570b02e9c1a2508c575b02e9c1a24c90575b001c6d528c9a24bd01aa41c50d6ca35c00116c9a8e245e10000d6c9a92245e1000249a128d5c6cb301ea41890d6c635c00116c5e8e249a10000d6c5e92249a1000245e128d58acb3002618928c56de4401ea4108d586e39400115e1a8ca46e08000d5e1a90a46e080269d5ac90c423a6002245e90d6c9b4c002249a90d6c5f4c00224904ead5d8b50021d5a90cac674c0021d504eaca58b500219508eac65cb50269c1950cac635c0010ac668e1d5a10000cac66921d5a10001c66128c996cb30269c114c986e3940010a61a8d5c6e08000ca61a915c6e08001e19528c4ae64402698114c5cae3940010661e8d58ae08000c661e9158ae08001a1d528c86e6440015e1a90ca46f4c0015e104ea4ad8b50015a108ea46dcb500121d5a8ec867a30009a114e9c6e4b5),
  (0x84eb62832d8a4549c6c526a4e9656c, 54, 0x2ea61d950c843ac02c661cd59082bab02c661d158c82bab001a114ca86e5f0b02c661d950c82bab0012194ca86e5f0b000e1950a86e5f0b00249a128d45ec8b01c6ca4190e16b0c01c6c249920d6b5d01c6c2498e116b5d00261e904d6c98bf01c6c2490e196b5d00261e984d6c90bf00261e98516c8cbf00261e98514cac2000219508e865ed760246d5c190e0ab0c0246c1d5920cab5d0246c1d58e10ab5d001e26904cad58bf0246c1d50e18ab5d001e26984cad50bf001e269850ad4cbf001e2698508d6c200246c1950e1cab630012269c4d6c9a13000e269c516c9a13002ca6904e19d52b000e269c596c9213002ca6984e11d52b002ca698520dd52b002d5e98520ca41702c661d950c82ba902c661d950c82ba700921d4286e4db77002a4ac590d5e3000152248286dcdb770029d6c590ca6300002ad5890e245f6700219508c6ea5d4e02116c82865cdb770029e24590cad700002a61890d6c5f670015a108c66add4e0029e1950cac67670009a114c5eae54e0029a114cac65e870029a114c86e5d7302c661c190d4ab0c02c641e1914cab5d02c641e18d50ab5d001d6e904ca618bf02c641e10d58ab5d001d6e984ca610bf001d6e9850a60cbf001d6e98508e242002c641a10d5cab6300116e9c4e249a13000d6e9c52249a130024ae904d59e12b0015a108e86de576000d6e9c5a2492130024ae984d51e12b0024ae98514de12b00261e98514cac1702ea61d950c807a70015eac590ca62fb00064ae990d5e300002249a906cd5c840005d6e990ca63000021d5a906cca48400219508eac65d4e00219508eac65c1a02c5c1a10ca56b630010aea44e1d5a13000caea4521d5a13001d6e904c9a612b000caea45a1d5213001d6e984c92612b001d6e98508e612b0009a114e86e5d76001e2698508d6c1702618114cac5eba100195eac4c92627400195eac508e6274001a269c50d4ad720005e26990cad7000015e1a9064cac840015a108ea46dd4e0015a108ea46dc1a00115eac588e62740012269c58d4ad72000e269c5914ad720009a114e9c6e54e0009a114e9c6e41a0005a114caae5d73)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_55 : blocksOK 11 56 P11 P12 955 195 B12_55 = true := by decide +kernel

def B12_56 : List (ℕ × ℕ × ℕ) := [(0x84ab6a822daa494946d524a4ab6a92, 52, 0x2ea61d950c843ae02ca605d5900eba902ca60dd59006ba9001a0d468ae51f7702ca611d58c06ba9001a11468ae4df77001a114e8ae45f770026128c856d9cdd02ca619d50c06ba9001219468ae4df770012194e8ae45f7700261a8c856d1cdd000e19528ae45f7700261a90856cdcdd00261a908d6c5cdd00261a908d46dc3b02ca61d950c06ba900121d468ae4db7700121d4e8ae45b7700261e8c856d18dd000e1d528ae45b7700261e90856cd8dd00261e908d6c58dd00261e908d46d83b000e1d5a8ae4537700261e98856cd0dd00261e988d6c50dd00261e988d46d03b00261e98916c4cdd00261e989146cc3b00261e98914ec43b00261e98914c6c13002d5a908c625db3024ad5c190e06b06024ac1d590e06b02024ac1d59060eb02001a268c856d1e43024ac1d58c612b02001a2690856cde43001a26908d6c5e43002d528c861a5d2c024ac1d50c61ab0200122698856cde43001226988d6c5e43002d5a8c86125d2c000e2698916c5e43002d5a90860e5d2c002d5a908e065d2c002d5a908e05e451024ac1950c61eb020012269c856cda430012269c8d6c5a43002d5e8c8612592c000e269c916c5a43002d5e90860e592c002d5e908e06592c002d5e908e05a451000e269c996c5243002d5e98860e512c002d5e988e06512c002d5e988e052451002d5e9892064d2c002d5e989204e451002d5e98920c645102ea61d950c843ad02ea601950c85fa8015a2680ad0c5f9d002ad5890c625efd02196e80a50c5f9d002a61890c56defd0029e1950c4ae71702ca61c190d46b0602ca41e190d46b0202ca41e19054eb0200196e8c86251e4302ca41e18c552b0200196e908624de4300196e908e245e430026128c855add2c02ca41e10c55ab0200116e988624de4300116e988e245e4300261a8c8552dd2c000d6e9892245e4300261a90854edd2c00261a908d46dd2c00261a908d45ec5102ca41a10c55eb0200116e9c8624da4300116e9c8e245a4300261e8c8552d92c000d6e9c92245a4300261e90854ed92c00261e908d46d92c00261e908d45ac5100261a908c56ddb3000d6e9c9a24524300261e98854ed12c00261e988d46d12c00261e988d452c5100261e989146cd2c00261e989144ec5100261e98914c6c5102ca601950e85fa8002269890c56def8000ad5a90c625efd0261c1950c4aeb110261c1950eac87820261c19506ac8f82001a268c8552de750261c194c6ac9382001a2690854ede75001a26908d46de75001e26908c55ad860261c114c6ac9b8200122698854ede75001226988d46de75001e26988c552d86000e26989146de75001e26989054ed86001e269890d46d8602618114c6ac9f820012269c854eda750012269c8d46da75001a269c8c552d86000e269c9146da75001a269c9054ed86001a269c90d46d86000a61a90c56defd000e269c9946d2750012269c9854ed860012269c98d46d86000e269c99146d86),
  (0x84eb62832d8a4d49c6c526a4eb656c, 56, 0x2ea61d950c843b002ca60dd59006bac02ca611d58c06bac001a114e886e5f0c02ca619d50c06bac0012194e886e5f0c000e1952886e5f0c00261a908d46dc8c02ca61d950c06bac00121d4e886e5b0c000e1d52886e5b0c00261e908d46d88c000e1d5a886e530c00261e988d46d08c00261e989146cc8c00261e98914c6c30002ea49c5914e169024ad5c190e06b0f024ac1d5920c6b68024ac1d58e106b68002ea4904e195d57024ac1d50e186b68002ea4984e115d57002ea498520d5d57002ea498520d5c26024ac1950e1c6b68002ea49c4e115957002ea49c520d5957002ea49c520d5826002ea49c5a0d5157002ea49c5a0d5026002ea49c5a114c26002ea49c5a10d41002ca61d950c42bae02ca601d5904eba902c6601d5908eba9002249c590d6eafc015a268086d0df7d000ad5c590e26b020006d5c990e26b020021d58906cea4ab02196e808650df7d000a61c590d6eb02000661c990d6eb020015e189064eacab0009e1950c6e6b850029e19506cca5f70029e1950acc65f70029a114c86e5d7402ca61c190d46b0f02ca41e1914c6b6802ca41e18d506b680026ac904d5a1d5702ca41e10d586b680026ac984d521d570026ac98514e1d570026ac98514e1c2602ca41a10d5c6b680026ac9c4d5219570026ac9c514e19570026ac9c514e18260026ac9c5920d5690026ac9c594e11570026ac9c594e10260026ac9c59520c260026ac9c5950e01002c6601d5928cba9002269c590d6cafc002269c990d6c6fc0016e9c98650e0670006d5e990e24b020021d5a906cca4ab0021d5a90acc64ab00219528cac65c1b0261c1950cac6b83001aaca44e115e8a001aaca4520d5e8a001aaca450e15d770012aca45a0d5e8a0012aca458e15d77000eaca459215d77001ea4ac5914e1670012aca45e0d5a8a0012aca45ce15977000eaca45d215977001aa4ac5d14e167000661e990d6cb020015e1a9064cacab0015e1a90a4c6cab0015a128ca46dc1b000eaca45da151770012a4ac5d94e167000ea4ac5d9521670009e1952acc65f70009a114e86e5d740005a114e8ae5d7402ea61d950c843af)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_56 : blocksOK 11 56 P11 P12 955 197 B12_56 = true := by decide +kernel

def B12_57 : List (ℕ × ℕ × ℕ) := [(0x856b42852d4a454a46a52b4a84ad4a, 50, 0x2116cea441c9baa0095e982d0e4634e02ea61d950c843b1008641ead58d239001aa45c2d148e34e01aa41c6d14ca37001aa41c6d48d2390002618d2ad5c4b8c01ea4d82d148634e01ea418ed144a37001ea418ed485239000261c52ad58cb8c018ec2449215eb7000120958eea45f9200261a90ed485f8c0269d582d0c8634e0269c196d0c4a3700269c196cc852390001e08516cdaa78c0196c1c4920e6b70001208d96e9c6792001e1a916cc8678c01d6c18c92066b7000121c496cdaa792001a1e916c48e78c00121e996cc867920269d5acd004a3a6005219428ee49f7300d21d4286e49b73002ace452095db8d015224c286dc9b73002ad5c5208e5b8d002ad58d20865f8d02116cc2865c9b73002a61c5148edb8d002a618d1486df8d0029e1950c86e78d02e9e18250c8574e02e9c1a250c4977002e9c1a24c851790001d485224daaf8c01a241c4914eeb70001148da269c6f92001d5a9224c86f8c01e2418c9146eb7000115c4a24daaf9200195e922448ef8c00115e9a24c86f9202920940c6e5db73002269c516cc9b8d0022698d16c49f8d0021e9950ec4a78d0261c19490c6eb700010e44a1d5aaf920018e6921c496f8c0010e69a1d486f920010669e1948ef920015e9a10e44af8d),
  (0x846b72912dca4548d6e522a4548d6e, 54, 0x2ea61d950c843b302d4a25c1904ebae02d4e25c1904abae001e0e8946d9277d02d5225c18c4abae001e128946d8e77d001e128d46d8a77d002e914c4a1da56202d5a25c10c4abae001e1a8946d0e77d001e1a8d46d0a77d002e994c4a1d2562001e1a9146cca77d002e99504a1ce562002e99504e1ca562002e99504e09e45902d5e25810c4abae001a1e8946d0e77d001a1e8d46d0a77d002e9d4c4a192562001a1e9146cca77d002e9d504a18e562002e9d504e18a562002e9d504e09a45900121e9946cca77d002e9d584a10e562002e9d584e10a562002e9d584e092459002e9d58520ca562002e9d585208e459002e9d58520ca459002e9d58520ca416002e9d5850e0a5b902d661d810c4abae001a268946d0df7d001a268d46d09f7d002ea54c4a191d62001a269146cc9f7d002ea5504a18dd62002ea5504e189d62002ea5504e099c590012269946cc9f7d002ea5584a10dd62002ea5584e109d62002ea5584e091c59002ea558520c9d62002ea5585208dc59002ea558520c9c59002ea558520c9c160012269d46cc9b7d002ea55c4a10d962002ea55c4e109962002ea55c4e091859002ea55c520c9962002ea55c5208d859002ea55c520c9859002ea55c520c9816002ea55c5a0c9162002ea55c5a08d059002ea55c5a0c9059002ea55c5a0c9016002ea55c5a108c59002ea55c5a108c16002ea55c5a10c816002e9d58520ca40e02ea61d950c843b202e821d850d4a7ad02e821d950c4a7ad002ad5c590e0a703021ead40590ca7a40029e1850c96e7180029e1950c86e7180029e19506cca5d702d661c190c4ab1c02d641e190c4ab1902d641e19084eb19001ead4c4a19268e02d641e18c852b19001ead504a18e68e001ead504e18a68e001ead504ca1a58f02d641e10c85ab19001ead584a10e68e001ead584e10a68e001ead584ca1258f001ead58520ca68e001ead5850a0e58f001ead5850e0a58f001ead5850e0a56a02d641a10c85eb19001aad5c4a10e68e001aad5c4e10a68e001aad5c4ca1258f001aad5c520ca68e001aad5c50a0e58f001aad5c50e0a58f001aad5c50e0a56a0012ad5c5a0ca68e0012ad5c58a0e58f0012ad5c58e0a58f0012ad5c58e0a56a000ead5c5920a58f000ead5c5920a56a000aad5c5920e56a0026ad5850e09d6302d421da90c4a7ad0016e9c590e0a7030006e9d590e0a7030021e99506cca46202d5c1a10c866b19001aad644a10de8e001aad644e109e8e001aad644ca11d8f001aad64520c9e8e001aad6450a0dd8f001aad6450e09d8f001aad6450e09d6a0012ad645a0c9e8e0012ad6458a0dd8f0012ad6458e09d8f0012ad6458e09d6a000ead6459209d8f000ead6459209d6a000aad645920dd6a001ead5850e0a5630012ad645e0c9a8e0012ad645ca0d98f0012ad645ce0998f0012ad645ce0996a000ead645d20998f000ead645d20996a000aad645d20d96a001aad5c50e0a5630015e1a90c86e7180015e1a906cca5d7000ead645da0918f000ead645da0916a000aad645da0d16a0012ad5c58e0a563000aad645da10d6a000ead5c5920a563000aad5c5920e5630005e1a916cca5d7)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_57 : blocksOK 11 56 P11 P12 955 199 B12_57 = true := by decide +kernel

def B12_58 : List (ℕ × ℕ × ℕ) := [(0x84eb62932d8a4d49d6c526a4eb656c, 58, 0x2ea61d950c843b502d4e25c19086bb002d5225c18c86bb0001e128d486da70f02d5a25c10c86bb0001e1a8d486d270f001e1a91486ce70f002e99508e05e4b102d5e25810c86bb0001a1e8d486d270f001a1e91486ce70f002e9d508e05a4b100121e99486ce70f002e9d588e0524b1002e9d589204e4b1002e9d58920c6433002ea55c9904e19502d661d810c86bb0001a268d486d1f0f001a2691486cdf0f002ea5508e059cb100122699486cdf0f002ea5588e051cb1002ea5589204dcb1002ea558920c5c330012269d486cdb0f002ea55c8e0518b1002ea55c9204d8b1002ea55c920c5833002ea55c9a04d0b1002ea55c9a0c5033002ea55c9a104c33002d649c5a10e81102d661d890c06bb302d4225c5908ebae02d4225c9904ebae0016ca45d920eb0602c8225d5904ebae000ad645d920eb060006d649d920eb06002255c986d0e86a021ead408590e788001661c590caeb19001661c990c6eb19001661c986d0e9d9000a61d590c6eb19000a61d586d0e9d9000661d58ad0e9d90029e195086ce57b02d661c190c86b1e02d641e1908c6b8602d641e18c906b86001ead508e05a5fa02d641e10c986b86001ead588e0525fa001ead589204e5fa001ead5890e0657f02d641a10c9c6b86001aad5c8e0525fa001aad5c9204e5fa001aad5c90e0657f0012ad5c9a04e5fa0012ad5c98e0657f000ead5c9920657f00256c9c5920e96802c8225e9904d7ae000aea45d920d7060006ea49d920d706002269c986d0d46a0006ea55d920cb06002269d586d0c86a002269d58ad0c46a0021e9950ac4e42c02d5c1a10ca46b86001aad648e051dfa001aad649204ddfa001aad6490e05d7f0012ad649a04ddfa0012ad6498e05d7f000ead6499205d7f001d6ca45920e9680012ad649e04d9fa0012ad649ce0597f000ead649d20597f00196ca45d20e968000a61e990c6d719000a61e986d0d5d9000661e98ad0d5d90015e1a9086ce57b000ead649da0517f00116ca45da0e968000d6ca45da12968000661e996d0c9d90009e1a9146ce57b0005e1a914ace57b02ea61d950c843b4),
  (0x85ab42962d0a594b56852d5a2b4000, 48, 0x41e1a914eca5680226ad4dc81907b4004261e9950cac1002242e950c9d87af004261e9158cac1002242e958c9d07af0042ea55cd892000004261a915ccac1002242e95cc9907af0042ea558dc920000042ea550dc9a0000041e1a9164cac10021c2e964c9907af0042e9d58e4920000042e9d50e49a0000042e9950e49e00000416ce49da1296802ea61d9500c87b40042ad64dc99201002e8225c9914c7af0042ad649cd9201002e8225cd91487af0042269d58d0ac000042ace49d59201002e8225d590c87af0042269cd950ac000042269c9950ec000042a55cda10ac2a0226ad40c9d907870042a55cda10ac020042a55c9a10ec020042a4dc9a116c02004269d58ec9202a02ea61c1914c8787004269d58ec92002004269d50ec9a002004269950ec9e00200416ce49e99201002d4225e990c87af0042255cda90ac000042255c9a90ec00004224dc9a916c000041e9950eca6002004164dc9a12ac02),
  (0x922dba484916dd24248b6e92124248, 48, 0x2ea61d950c843b6006a4219d4c92fb200aa4219d4c52fb2002689c52194efa400ea4219d4852fb200268dc52194afa400268dc921946fa400268dc906196ec5016a4219cc852fb2002695c5218cafa4002695c9218c6fa4002695c90618eec5002695cd21886fa4002695cd0618aec5002695cd0a186ec5002695cd0861add601aa4215cc852fb2002699c5214cafa4002699c9214c6fa4002699c90614eec5002699cd21486fa4002699cd0614aec5002699cd0a146ec5002699cd08616dd6002699d520c86fa4002699d5060caec5002699d50a0c6ec5002699d50860edd6002699d50e086ec5002699d50c60add6002699d50ca06dd6022a4195cc852fb20026a1c5194cafa40026a1c9194c6fa40026a1c90594eec50026a1cd19486fa40026a1cd0594aec50026a1cd09946ec50026a1cd08596dd60026a1d518c86fa40026a1d5058caec50026a1d5098c6ec50026a1d50858edd60026a1d50d886ec50026a1d50c58add60026a1d50c986dd60026a1d914c86fa40026a1d9054caec50026a1d9094c6ec50026a1d90854edd60026a1d90d486ec50026a1d90c54add60026a1d90c946dd60026a1d914c86ec50026a1d9144cadd60026a1d9148c6dd60026a1d914c86dd6026a0195cc852fb20022a5c5194cafa40022a5c9194c6fa40022a5c90594eec50022a5cd19486fa40022a5cd0594aec50022a5cd09946ec50022a5cd08596dd60022a5d518c86fa40022a5d5058caec50022a5d5098c6ec50022a5d50858edd60022a5d50d886ec50022a5d50c58add60022a5d50c986dd60022a5d914c86fa40022a5d9054caec50022a5d9094c6ec50022a5d90854edd60022a5d90d486ec50022a5d90c54add60022a5d90c946dd60022a5d914c86ec50022a5d9144cadd60022a5d9148c6dd60022a5d914c86dd6001aa5e114c86fa4001aa5e1054caec5001aa5e1094c6ec5001aa5e10854edd6001aa5e10d486ec5001aa5e10c54add6001aa5e10c946dd6001aa5e114c86ec5001aa5e1144cadd6001aa5e1148c6dd6001aa5e114c86dd60016a5e118c86ec50016a5e1184cadd60016a5e1188c6dd60016a5e118c86dd6000ea5e119486dd602ea0195cc8527b20022adc5194ca7a40022adc9194c67a40022adc90594e6c50022adcd194867a40022adcd0594a6c50022adcd099466c50022adcd085965d60022add518c867a40022add5058ca6c50022add5098c66c50022add50858e5d60022add50d8866c50022add50c58a5d60022add50c9865d60022add914c867a40022add9054ca6c50022add9094c66c50022add90854e5d60022add90d4866c50022add90c54a5d60022add90c9465d60022add914c866c50022add9144ca5d60022add9148c65d60022add914c865d6001aade114c867a4001aade1054ca6c5001aade1094c66c5001aade10854e5d6001aade10d4866c5001aade10c54a5d6001aade10c9465d6001aade114c866c5001aade1144ca5d6001aade1148c65d6001aade114c865d60016ade118c866c50016ade1184ca5d60016ade1188c65d60016ade118c865d6000eade1194865d6001aade514c863a4001aade5054ca2c5001aade5094c62c5001aade50854e1d6001aade50d4862c5001aade50c54a1d6001aade50c9461d6001aade514c862c5001aade5144ca1d6001aade5148c61d6001aade514c861d60016ade518c862c50016ade5184ca1d60016ade5188c61d60016ade518c861d6000eade5194861d60016ade520c85ac50016ade5204c99d60016ade5208c59d60016ade520c859d6000eade5214859d6000eade5218855d6)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_58 : blocksOK 11 56 P11 P12 955 201 B12_58 = true := by decide +kernel

def B12_59 : List (ℕ × ℕ × ℕ) := [(0x926db2494936d924a49b6c92524db6, 56, 0x2ea61d950c843b8009ec261194c6bb300dec26119486bb300268dc906196f88015ec26118c86bb3002695c90618ef88002695cd0618af88002695cd0861aead019ec26114c86bb3002699c90614ef88002699cd0614af88002699cd08616ead002699d5060caf88002699d50860eead002699d50c60aead002699d50c862db2021ec25914c86bb30026a1c90594ef880026a1cd0594af880026a1cd08596ead0026a1d5058caf880026a1d50858eead0026a1d50c58aead0026a1d50c85adb20026a1d9054caf880026a1d90854eead0026a1d90c54aead0026a1d90c856db20026a1d9144caead0026a1d91484edb20026a1d914c4adb20026a1d914c4ad96025ec21914c86bb30022a5c90594ef880022a5cd0594af880022a5cd08596ead0022a5d5058caf880022a5d50858eead0022a5d50c58aead0022a5d50c85adb20022a5d9054caf880022a5d90854eead0022a5d90c54aead0022a5d90c856db20022a5d9144caead0022a5d91484edb20022a5d914c4adb20022a5d914c4ad96001aa5e1054caf88001aa5e10854eead001aa5e10c54aead001aa5e10c856db2001aa5e1144caead001aa5e11484edb2001aa5e114c4adb2001aa5e114c4ad960016a5e1184caead0016a5e11884edb20016a5e118c4adb20016a5e118c4ad96000ea5e11944adb2000ea5e11944ad96000aa5e11944ed96002ea1d914c4a59002de611944c82bb6002a4619d4c92fb2002a5219d4c86fb2002a520594dcaf1a002a5e1914c86fb2002a5e0594d0af1a002a5e1194c4af1a002a5e11854cae8f02de421914c86bb30022adc90594e7880022adcd0594a7880022adcd085966ad0022add5058ca7880022add50858e6ad0022add50c58a6ad0022add50c85a5b20022add9054ca7880022add90854e6ad0022add90c54a6ad0022add90c8565b20022add9144ca6ad0022add91484e5b20022add914c4a5b20022add914c4a596001aade1054ca788001aade10854e6ad001aade10c54a6ad001aade10c8565b2001aade1144ca6ad001aade11484e5b2001aade114c4a5b2001aade114c4a5960016ade1184ca6ad0016ade11884e5b20016ade118c4a5b20016ade118c4a596000eade11944a5b2000eade11944a596000aade11944e5960026a1d914c4ad90001aade5054ca388001aade50854e2ad001aade50c54a2ad001aade50c8561b2001aade5144ca2ad001aade51484e1b2001aade514c4a1b2001aade514c4a1960016ade5184ca2ad0016ade51884e1b20016ade518c4a1b20016ade518c4a196000eade51944a1b2000eade51944a196000aade51944e1960022a5d914c4ad90001e6a1914c86fb2001e6a0594d0af1a001e6a1194c4af1a001e6a11854cae8f0016ade5204c9aad0016ade52084d9b20016ade520c499b20016ade520c49996000eade5214499b2000eade521449996000aade52144d996001aa5e114c4ad90000eade5218495b2000eade521849596000aade52184d5960016a5e118c4ad9000126a1d94c4af1a00126a1d854cae8f000aade521854d96000ea5e11944ad90000aa5e11944ed9000066a1d914cae8f02ea61d950c843b7),
  (0x92ada24a4956d12524ab6892ada000, 48, 0x426a1d9094eda002ea61d950c843b900426a1d90c96c2c00eac261d95087b400426a1d9148ec2c016ac261d8d087b400426a1d9148ec05002e95cd0a61878700426a1d5188ec2c01aac261d4d087b400426a1d5188ec05002e99cd0a61478700426a1cd1896c05002e99d50a60c7870042ea5e1148d8010042699d5208ec2c022ac259d4d087b40042699d5208ec05002ea1cd0a5947870042699cd2096c05002ea1d50a58c7870042ea5d9148e0010042695cd209ac05002ea1d90a54c7870042ea5d5188e0010042ea5cd18960010042299d5248ec2c026ac219d4d087b40042299d5248ec05002ea5cd0a1947870042299cd2496c05002ea5d50a18c7870042ea1d9148e4010042295cd249ac05002ea5d90a14c7870042ea1d5188e4010042ea1cd18964010041a95cd24a2c05002ea5e10994c7870042e99d5208e4010042e99cd20964010042e95cd209a4010042a5e11948ed9002ea61d950c087b70042a5e11894ec0e0042a5e09914ec0e0042a52099d4ec0e0042299d52c8e42c02ea4219d4d087b40042299d52c8e4050026adcd0a1947870042299cd2c964050026add50a18c78700426a1d9148ec010042295cd2c9a4050026add90a14c78700426a1d5188ec0100426a1cd1896c010041a95cd2ca24050026ade10994c7870042699d5208ec010042699cd2096c010042695cd209ac010041a95cd2ca60050022ade50994c7870042299d5248ec010042299cd2496c010042295cd249ac010041e5209a94ec0e0041a95cd24a2c01)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_59 : blocksOK 11 56 P11 P12 955 204 B12_59 = true := by decide +kernel

def B12_60 : List (ℕ × ℕ × ℕ) := [(0x92eda24b4976d125a4bb6892eda5b4, 60, 0x2ea61d950c843ba00dec26119486bb5015ec26118c86bb5002695cd0861af1e019ec26114c86bb5002699cd08616f1e002699d50860ef1e002699d50c862e9a021ec25914c86bb50026a1cd08596f1e0026a1d50858ef1e0026a1d50c85ae9a0026a1d90854ef1e0026a1d90c856e9a0026a1d91484ee9a0026a1d914c86da5025ec21914c86bb50022a5cd08596f1e0022a5d50858ef1e0022a5d50c85ae9a0022a5d90854ef1e0022a5d90c856e9a0022a5d91484ee9a0022a5d914c86da5001aa5e10854ef1e001aa5e10c856e9a001aa5e11484ee9a001aa5e114c86da50016a5e11884ee9a0016a5e118c86da5000ea5e119486da5002de5209944e99202de611948c06bb8001ec661194cabb3001eca61194c6bb3001eca461950eb1c001ed260994c6bb3001ed2461948eb1c001ed24a1944eb1c001ed24a0594ea910012de60994c6bb30012de461948eb1c0012de4a1944eb1c0012de4a0594ea91000ade521944eb1c000ade520594ea910006de520994ea91002a5e118854eda002de421914c86bb50022adcd0859671e0022add50858e71e0022add50c85a69a0022add90854e71e0022add90c85669a0022add91484e69a0022add914c865a5001aade10854e71e001aade10c85669a001aade11484e69a001aade114c865a50016ade11884e69a0016ade118c865a5000eade1194865a50025ed209944e992001aade50854e31e001aade50c85629a001aade51484e29a001aade514c861a50016ade51884e29a0016ade518c861a5000eade5194861a50021ed249944e9920012ea60994c5fb30012ea461948df1c0012ea4a1944df1c0012ea4a0594de91000aea521944df1c000aea520594de910006ea520994de91001e6a118854eda00016ade52084da9a0016ade520c859a5000eade5214859a50019ed24a144e992000eade5218855a50015ed24a184e992000aea5e1944d31c000aea5e0594d2910006ea5e0994d29100126a1d8854eda0000ded24a18569920006ea5e1194ca91000a6a1d9054eda000066a1d9094eda002ea61d950c807b9),
  (0x936d824d49b6c126a4db616c0005b0, 50, 0x826a1d90d46d9202a5d20c5814afb900826a1d914c6c11002e95d24c618bb400826a1d518c6c11002e99d24c614bb40082de520d856803002e99d50c660b1d0082699d520c6c11002ea1d24c594bb40082de518e056803002ea1d50c658b1d0082de514e05a803002ea1d90c654b1d002ea1d914c64a990082299d524c6c11002ea5d20c594bb40082de118e456803002ea5d50c618b1d0082de114e45a803002ea5d90c614b1d002ea5d914c60a990082dd914e462803002ea5e10c594b1d002ea5e114c58a99002ea5e118c54a990081ed24e18569920081ed24e059681102de61194c04abb9002ac661d950cbb40081ed2460d968110082a5e118d46c03002ace61d9504bb4002ace46195d0b1d0081ece4611968110082a5e0d9146c03002ad261d94c4bb4002ad246195ccb1d0082a5e05914ec03002ad24e0595ca99002ad24e195c4b1d00812ce461d968110082a520d9d46c03002ade61194c4bb4002ade461950cb1d0082a52059d4ec03002ade4e05950a99002ade4e19504b1d0082a4e059d52c03002ade520594ca99002ade52194c4b1d002ade520d944a990082299d52cc64110026add20c594bb400825e118ec568030026add50c618b1d00825e114ec5a8030026add90c614b1d0026add914c60a9900825d914ec628030026ade10c594b1d0026ade114c58a990026ade118c54a9900821d914ec668030022ade50c594b1d0022ade514c58a990022ade518c54a9900812ce462995c110081e520da946c03001eea61194c4bb4001eea461950cb1d0081e5205a94ec03001eea4e05950a99001eea4e19504b1d0081e4e05a952c03001eea520594ca99001eea52194c4b1d001eea520d944a99001aade520c54a99008124e05a95ec030012ea5e0594ca990012ea5e194c4b1d0012ea5e0d944a99000eea5e11944a99)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okB12_60 : blocksOK 11 56 P11 P12 955 206 B12_60 = true := by decide +kernel

def B12 : List (ℕ × ℕ × ℕ) := B12_0 ++ (B12_1 ++ (B12_2 ++ (B12_3 ++ (B12_4 ++ (B12_5 ++ (B12_6 ++ (B12_7 ++ (B12_8 ++ (B12_9 ++ (B12_10 ++ (B12_11 ++ (B12_12 ++ (B12_13 ++ (B12_14 ++ (B12_15 ++ (B12_16 ++ (B12_17 ++ (B12_18 ++ (B12_19 ++ (B12_20 ++ (B12_21 ++ (B12_22 ++ (B12_23 ++ (B12_24 ++ (B12_25 ++ (B12_26 ++ (B12_27 ++ (B12_28 ++ (B12_29 ++ (B12_30 ++ (B12_31 ++ (B12_32 ++ (B12_33 ++ (B12_34 ++ (B12_35 ++ (B12_36 ++ (B12_37 ++ (B12_38 ++ (B12_39 ++ (B12_40 ++ (B12_41 ++ (B12_42 ++ (B12_43 ++ (B12_44 ++ (B12_45 ++ (B12_46 ++ (B12_47 ++ (B12_48 ++ (B12_49 ++ (B12_50 ++ (B12_51 ++ (B12_52 ++ (B12_53 ++ (B12_54 ++ (B12_55 ++ (B12_56 ++ (B12_57 ++ (B12_58 ++ (B12_59 ++ (B12_60))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem blk12 : blocksOK 11 56 P11 P12 955 0 B12 = true := blocksOK_app (k := 4) okB12_0 rfl (blocksOK_app (k := 5) okB12_1 rfl (blocksOK_app (k := 4) okB12_2 rfl (blocksOK_app (k := 3) okB12_3 rfl (blocksOK_app (k := 4) okB12_4 rfl (blocksOK_app (k := 5) okB12_5 rfl (blocksOK_app (k := 5) okB12_6 rfl (blocksOK_app (k := 4) okB12_7 rfl (blocksOK_app (k := 4) okB12_8 rfl (blocksOK_app (k := 4) okB12_9 rfl (blocksOK_app (k := 4) okB12_10 rfl (blocksOK_app (k := 2) okB12_11 rfl (blocksOK_app (k := 3) okB12_12 rfl (blocksOK_app (k := 3) okB12_13 rfl (blocksOK_app (k := 4) okB12_14 rfl (blocksOK_app (k := 3) okB12_15 rfl (blocksOK_app (k := 3) okB12_16 rfl (blocksOK_app (k := 3) okB12_17 rfl (blocksOK_app (k := 6) okB12_18 rfl (blocksOK_app (k := 5) okB12_19 rfl (blocksOK_app (k := 4) okB12_20 rfl (blocksOK_app (k := 4) okB12_21 rfl (blocksOK_app (k := 5) okB12_22 rfl (blocksOK_app (k := 3) okB12_23 rfl (blocksOK_app (k := 2) okB12_24 rfl (blocksOK_app (k := 5) okB12_25 rfl (blocksOK_app (k := 2) okB12_26 rfl (blocksOK_app (k := 5) okB12_27 rfl (blocksOK_app (k := 4) okB12_28 rfl (blocksOK_app (k := 3) okB12_29 rfl (blocksOK_app (k := 4) okB12_30 rfl (blocksOK_app (k := 3) okB12_31 rfl (blocksOK_app (k := 3) okB12_32 rfl (blocksOK_app (k := 3) okB12_33 rfl (blocksOK_app (k := 2) okB12_34 rfl (blocksOK_app (k := 3) okB12_35 rfl (blocksOK_app (k := 2) okB12_36 rfl (blocksOK_app (k := 3) okB12_37 rfl (blocksOK_app (k := 5) okB12_38 rfl (blocksOK_app (k := 5) okB12_39 rfl (blocksOK_app (k := 4) okB12_40 rfl (blocksOK_app (k := 2) okB12_41 rfl (blocksOK_app (k := 3) okB12_42 rfl (blocksOK_app (k := 4) okB12_43 rfl (blocksOK_app (k := 3) okB12_44 rfl (blocksOK_app (k := 3) okB12_45 rfl (blocksOK_app (k := 2) okB12_46 rfl (blocksOK_app (k := 2) okB12_47 rfl (blocksOK_app (k := 3) okB12_48 rfl (blocksOK_app (k := 5) okB12_49 rfl (blocksOK_app (k := 5) okB12_50 rfl (blocksOK_app (k := 3) okB12_51 rfl (blocksOK_app (k := 4) okB12_52 rfl (blocksOK_app (k := 2) okB12_53 rfl (blocksOK_app (k := 2) okB12_54 rfl (blocksOK_app (k := 2) okB12_55 rfl (blocksOK_app (k := 2) okB12_56 rfl (blocksOK_app (k := 2) okB12_57 rfl (blocksOK_app (k := 3) okB12_58 rfl (blocksOK_app (k := 2) okB12_59 rfl (okB12_60))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
theorem len12 : B12.length = 208 := by decide +kernel

theorem cl12 : ClassP 12 (inP 12 P12 955) 56 :=
  stepP 11 _ _ 47 56 (stepB_sound 11 56 P11 208 P12 955 B12 len12 blk12) (by intro E d h1 h2; omega) cl11

end TFClass

namespace TFClass

/-! Per-core certificates on 12 vertices -/

/-- cost of a root neighbour with neighbourhood mask `s` when the core colour-`true` set is `c`
and the root is coloured `false`. -/
def costN (s c : ℕ) : ℕ := min (1 + pcF 12 (s &&& (4095 ^^^ c))) (pcF 12 (s &&& c))

def monoO {k : ℕ} (A : Gr k) (col : Fin k → Bool) : ℕ :=
  ∑ i, ∑ j, if A i j = true ∧ col i = col j then 1 else 0

def wsum (ws : List (ℕ × ℕ)) (f : ℕ → ℕ) : ℕ := (ws.map (fun p => p.2 * f p.1)).sum

def DualOK (b : ℕ) (ws : List (ℕ × ℕ)) (α μ : ℕ) : Bool :=
  (gen 12 b 12 0).all (fun s => decide (wsum ws (costN s) ≤ α + μ * pcF 12 s)) &&
  decide (wsum ws (fun c => monoO (adjOf 12 b) (fun i => c.testBit i.val)) + 2 * (12 * α + 53 * μ) <
    52 * (ws.map (·.2)).sum)

def cycOK (b : ℕ) (cyc : List ℕ) : Bool :=
  decide (cyc.length % 2 = 1) && cyc.all (fun x => decide (x < 12)) &&
  (List.range cyc.length).all (fun i =>
    b.testBit (cyc.getD i 0 * 12 + cyc.getD ((i + 1) % cyc.length) 0))

def wsOf (s : ℕ) : List (ℕ × ℕ) :=
  (List.range ((s >>> 33) % 8)).map (fun j => ((s >>> (36 + 26 * j)) % 4096, (s >>> (48 + 26 * j)) % 16384))

def cycOf (s : ℕ) : List ℕ := (List.range ((s >>> 1) % 16)).map (fun j => (s >>> (5 + 4 * j)) % 16)

def coreQ (b s : ℕ) : Bool :=
  if s % 2 = 1 then DualOK b (wsOf s) ((s >>> 1) % 65536) ((s >>> 17) % 65536)
  else cycOK b (cycOf s)

def coresOK (P : ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | i, (b, s) :: rest => (slot P (12 * 12) i == b) && coreQ b s && coresOK P (i+1) rest

lemma coresOK_app {P i0 k : ℕ} {l1 l2 : List (ℕ × ℕ)}
    (h1 : coresOK P i0 l1 = true) (hl : l1.length = k) (h2 : coresOK P (i0 + k) l2 = true) :
    coresOK P i0 (l1 ++ l2) = true := by
  subst hl
  induction l1 generalizing i0 with
  | nil => simpa using h2
  | cons a l ih =>
    obtain ⟨b, s⟩ := a
    rw [List.cons_append]
    simp only [coresOK, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ih h1.2 ?_⟩
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h2

lemma coresOK_sound (P : ℕ) : ∀ (l : List (ℕ × ℕ)) (i0 : ℕ), coresOK P i0 l = true →
    ∀ i, i0 ≤ i → i < i0 + l.length → ∃ s, coreQ (slot P (12 * 12) i) s = true
  | [], _, _ => by intro i h1 h2; simp at h2; omega
  | (b, s) :: rest, i0, h => by
    simp only [coresOK, Bool.and_eq_true, beq_iff_eq] at h
    intro i h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨s, by rw [h.1.1]; exact h.1.2⟩
    · exact coresOK_sound P rest (i0+1) h.2 i hlt (by simp at h2; omega)

/-! Soundness -/

lemma pcF_land (s c : ℕ) :
    pcF 12 (s &&& c) = ∑ i : Fin 12, if s.testBit i.val = true ∧ c.testBit i.val = true then 1 else 0 := by
  rw [pcF_eq]; unfold popc
  apply Finset.sum_congr rfl; intro i _
  simp [Nat.testBit_land]

lemma pcF_diff (s c : ℕ) :
    pcF 12 (s &&& (4095 ^^^ c)) =
      ∑ i : Fin 12, if s.testBit i.val = true ∧ c.testBit i.val = false then 1 else 0 := by
  rw [pcF_eq]; unfold popc
  apply Finset.sum_congr rfl; intro i _
  have h4 : (4095 : ℕ).testBit i.val = true := by
    have := i.isLt
    interval_cases (i.val) <;> decide
  simp [Nat.testBit_land, Nat.testBit_xor, h4]

lemma odd_cycle_no_coloring {A : Gr 12} (b : ℕ) (hb : ∀ i j, A i j = adjOf 12 b i j)
    (cyc : List ℕ) (h : cycOK b cyc = true) (col : Fin 12 → Bool)
    (hcol : ∀ i j, A i j = true → col i ≠ col j) : False := by
  unfold cycOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hodd, hlt⟩, hadj⟩ := h
  set L := cyc.length
  have hL : 0 < L := by omega
  let v (i : ℕ) : Fin 12 := ⟨cyc.getD i 0 % 12, Nat.mod_lt _ (by norm_num)⟩
  have hv : ∀ i, i < L → (v i).val = cyc.getD i 0 := by
    intro i hi
    have : cyc.getD i 0 < 12 := by
      have := hlt _ (List.getElem_mem hi)
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this
    show cyc.getD i 0 % 12 = cyc.getD i 0
    exact Nat.mod_eq_of_lt this
  have step : ∀ i, i < L → col (v ((i + 1) % L)) = !col (v i) := by
    intro i hi
    have hA : A (v i) (v ((i+1) % L)) = true := by
      rw [hb]; unfold adjOf
      rw [hv i hi, hv _ (Nat.mod_lt _ hL)]; exact hadj i hi
    have := hcol _ _ hA
    cases h1 : col (v i) <;> cases h2 : col (v ((i + 1) % L)) <;> simp_all
  have par : ∀ i, i ≤ L → i < L → col (v i) = (col (v 0) ^^ decide (i % 2 = 1)) := by
    intro i
    induction i with
    | zero => intro _ _; simp
    | succ i ih =>
      intro _ hi
      have := step i (by omega)
      rw [Nat.mod_eq_of_lt hi] at this
      rw [this, ih (by omega) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · have : (i + 1) % 2 = 1 := by omega
        simp [h, this]
      · have : (i + 1) % 2 = 0 := by omega
        simp [h, this]
  have last := step (L - 1) (by omega)
  rw [show (L - 1 + 1) % L = 0 by rw [Nat.sub_add_cancel hL, Nat.mod_self]] at last
  rw [par (L - 1) (by omega) (by omega)] at last
  have : (L - 1) % 2 = 0 := by omega
  simp [this] at last

lemma weight_lower (ws : List (ℕ × ℕ)) (f : ℕ → ℕ) (B : ℕ) (h : ∀ p ∈ ws, B ≤ f p.1) :
    B * (ws.map (·.2)).sum ≤ (ws.map (fun p => p.2 * f p.1)).sum := by
  induction ws with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have h1 := Nat.mul_le_mul_left a.2 (h a (List.mem_cons_self ..))
    have h2 := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    rw [Nat.mul_comm B a.2]; omega

lemma exists_good_weight (ws : List (ℕ × ℕ)) (f : ℕ → ℕ) (B : ℕ)
    (h : (ws.map (fun p => p.2 * f p.1)).sum < B * (ws.map (·.2)).sum) :
    ∃ p ∈ ws, f p.1 < B := by
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  have := weight_lower ws f B hno
  omega

end TFClass
namespace TFClass

def Cores_0 : List (ℕ × ℕ) := [(0x400aa05542aa5552aa5552aa1552aa1550aa, 0x15aa8005555400000015),
  (0x400aa05542ab5542ab5542ab1542ab154154, 0xad54200000015),
  (0x400aa05552aa5552aa5552aa1542aa1552a2, 0x145540052aa400000015),
  (0x400aa05552aa5552aa5552aa1552aa1552aa, 0xad55200000015),
  (0x400aa15542aa5542ab5542ab1542ab154454, 0x15aac005554400000015),
  (0x400aa15542ab5542ab5542ab1542ab154554, 0xad54200000015),
  (0x401aa05542aa5542aa5552aa1552aa15582a, 0xad55200000015),
  (0x401aa05542aa5542ab5542ab1542ab154854, 0x174a40a),
  (0x401aa05542aa5552aa5552aa1542aa1558a2, 0x22aa0004a880029540006aa8004555a00000017),
  (0x401aa05542aa5552aa5552aa1552aa1558aa, 0x16554005aaa400000015),
  (0x401aa05542ab5542ab5542ab1542ab154954, 0x174a40a),
  (0x401aa05552aa5552aa5552aa1542aa154aa0, 0x12a00006a800049540016aa8001555a0000001f),
  (0x401aa05552aa5552aa5552aa1542aa155aa2, 0x16554005aaa400000015),
  (0x401aa05552aa5552aa5552aa1552aa155aaa, 0x16554005aaa400000015),
  (0x400aa05572a85572a85572a81572a82a82a8, 0xaaa8200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_0 : coresOK P12 0 Cores_0 = true := by decide +kernel

def Cores_1 : List (ℕ × ℕ) := [(0x400aa15562a85562a85562a91562a92a9416, 0x52a90009058003556600000019),
  (0x400aa15562a85562a95562a91562a92a9456, 0x14aa4005556400000015),
  (0x400aa15562a95562a95562a91562a92a9556, 0xaaa9200000015),
  (0x401aa05562a85562a95562a91562a92a9856, 0x174a20a),
  (0x401aa05562a85572a85572a81572a82a88a8, 0xaaa8200000015),
  (0x401aa05562a95562a95562a91562a92a9956, 0x174a20a),
  (0x401aa05572a85572a85572a81562a82a8aa0, 0xaaa8200000015),
  (0x401aa05572a85572a85572a81572a82a8aa8, 0xaaa8200000015),
  (0x400aa25542a85552aa5552aa1552aa4550aa, 0x14aa8005555400000015),
  (0x400aa25552a85552aa5552aa1542aa4552a2, 0x85500052aa0006aa8002555800000017),
  (0x400aa35542a85542ab5542ab1542ab454454, 0x12a8000caac006554600000019),
  (0x400aa35542a95542aa5542ab1542ab454514, 0x14aac005554400000015),
  (0x400aa35542a95542ab5542ab1542ab454554, 0x14aac005554400000015),
  (0x401aa25542a85542aa5552aa1552aa45582a, 0x14aac005555400000015),
  (0x401aa25542a85542ab5542ab1542ab454854, 0x174240a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_1 : coresOK P12 15 Cores_1 = true := by decide +kernel

def Cores_2 : List (ℕ × ℕ) := [(0x401aa25542a85552aa5552aa1542aa4558a2, 0x155500052aa400000015),
  (0x401aa25542a85552aa5552aa1552aa4548a8, 0x155500052aa400000015),
  (0x401aa25542a85552aa5552aa1552aa4558aa, 0x14aa8005555400000015),
  (0x401aa25542a95542aa5542ab1542ab454914, 0x174240a),
  (0x401aa25542a95542ab5542ab1542ab454954, 0x174240a),
  (0x401aa25552a85552aa5552aa1542aa454aa0, 0x155500052aa400000015),
  (0x401aa25552a85552aa5552aa1542aa455aa2, 0x31540014aa8002555600000017),
  (0x401aa25552a85552aa5552aa1552aa454aa8, 0x91540042aa000eaa8001555800000017),
  (0x401aa25552a85552aa5552aa1552aa455aaa, 0x14aa8005555400000015),
  (0x400aa25542aa5542aa5552aa1552aa55502a, 0x242a000caa8005555600000019),
  (0x400aa25542aa5542ab5542ab1542ab554054, 0x65500022aa0011550003aab800000019),
  (0x400aa25542aa5552aa5552aa1542aa5550a2, 0x8a88002554000caa8003555800000019),
  (0x400aa25552aa5552aa5552aa1542aa5552a2, 0x95500042aa000eaa8001555800000017),
  (0x400aa35542aa5542aa5542ab1542ab554414, 0x52ab000d050003554600000019),
  (0x400aa35542ab5542ab5542ab1542ab554554, 0xaaab200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_2 : coresOK P12 30 Cores_2 = true := by decide +kernel

def Cores_3 : List (ℕ × ℕ) := [(0x401aa25542aa5542aa5542aa1552aa55580a, 0x17550005aaa400000015),
  (0x401aa25542aa5542aa5542ab1542ab554814, 0x174240a),
  (0x401aa25542aa5542aa5552aa1542aa555822, 0x17550005aaa400000015),
  (0x401aa25542aa5552aa5552aa1552aa5558aa, 0xaaaa200000015),
  (0x401aa25542ab5542ab5542ab1542ab554954, 0x174240a),
  (0x401aa25552aa5552aa5552aa1542aa555aa2, 0xaaaa200000015),
  (0x401aa25552aa5552aa5552aa1552aa555aaa, 0xaaaa200000015),
  (0x403aa05542a85542ab5542ab1542ab854854, 0x174a40a),
  (0x403aa05542a85552aa5552aa1552aa8548a8, 0x162460a),
  (0x403aa05542a95542ab5542ab1542ab854954, 0x174a40a),
  (0x402aa15542a85562a85562a91562a98a9416, 0x52a90009058002556600000015),
  (0x403aa05542a85572a85572a81572a88a88a8, 0xaaa8200000015),
  (0x403aa05542a95562a95562a91562a98a8954, 0x162640a),
  (0x403aa05552a85562a85572a81572a88a8a28, 0xaaa8200000015),
  (0x403aa05552a85572a85572a81572a88a8aa8, 0xaaa8200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_3 : coresOK P12 45 Cores_3 = true := by decide +kernel

def Cores_4 : List (ℕ × ℕ) := [(0x402aa05542aa5542aa5552aa1552aa95502a, 0xb5620a),
  (0x402aa05542aa5542ab5542ab1542ab954054, 0xb5624a),
  (0x402aa05542aa5552aa5552aa1542aa9550a2, 0xb5620a),
  (0x402aa05542aa5552aa5552aa1552aa9540a8, 0x15624aa),
  (0x402aa05542aa5552aa5552aa1552aa9550aa, 0xb5620a),
  (0x402aa05552aa5552aa5552aa1542aa9542a0, 0x15624aa),
  (0x402aa05552aa5552aa5552aa1542aa9552a2, 0xb5620a),
  (0x402aa15542aa5542aa5542aa1552aa95540a, 0x14a420a),
  (0x402aa15542aa5542aa5542ab1542ab954414, 0x156240a),
  (0x403aa05542aa5542aa5542ab1542ab954814, 0x174a40a),
  (0x403aa05542aa5542aa5552aa1552aa954828, 0x162460a),
  (0x403aa05542aa5552aa5552aa1542aa9548a0, 0x1624a0a),
  (0x403aa05542ab5542ab5542ab1542ab954954, 0x174a40a),
  (0x403aa05552aa5552aa5552aa1542aa954aa0, 0x1624a0a),
  (0x403aa05552aa5552aa5552aa1552aa954aa8, 0x162460a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_4 : coresOK P12 60 Cores_4 = true := by decide +kernel

def Cores_5 : List (ℕ × ℕ) := [(0x402aa15562a85562a85562a91542a9aa1416, 0x8aa400241e0005058004aa9800000015),
  (0x403aa05572a85572a85572a81542a8aa0aa0, 0xaaa8200000015),
  (0x403aa05572a85572a85572a81552a8aa0aa8, 0xaaa8200000015),
  (0x402aa05562a85562a85562a91562a9aa9016, 0x14160004aa40032a80015558001aa9a0000001b),
  (0x402aa05562a85562a95562a91562a9aa8054, 0x1aa800065580022a80011558003aa9a0000001b),
  (0x402aa05562a85562a95562a91562a9aa9056, 0x145580052a9400000015),
  (0x402aa05562a85572a85572a81572a8aa80a8, 0x14aa0005557400000015),
  (0x402aa05572a85572a85572a81562a8aa82a0, 0x95580042a8000eaa0001557800000017),
  (0x402aa15562a85562a85562a81562a9aa9406, 0x32a9000d018003aa9600000013),
  (0x402aa15562a85562a85562a91562a9aa8414, 0x3416000caa4003aa9600000013),
  (0x402aa15562a85562a85562a91562a9aa9416, 0x52a90009058003556600000017),
  (0x403aa05562a85562a85562a91562a9aa8814, 0x162640a),
  (0x403aa05562a85562a85572a81572a8aa8828, 0x17558005aa8400000015),
  (0x403aa05562a85572a85572a81562a8aa88a0, 0x17558005aa8400000015),
  (0x403aa05572a85572a85572a81572a8aa8aa8, 0xaaa8200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_5 : coresOK P12 75 Cores_5 = true := by decide +kernel

def Cores_6 : List (ℕ × ℕ) := [(0x400aa45532ac5532ac5532ac1505532a42a4, 0x95400042ac000aab0001553800000015),
  (0x400aa55522ac5522ad5522ad1505522a5452, 0x95400052ad0005548001aad800000017),
  (0x400aa55522ad5522ad5522ad1505522a4550, 0x32a50015548002aad600000019),
  (0x400aa55522ad5522ad5522ad1505522a5552, 0x22a50011548004aad600000019),
  (0x401aa45522ac5522ac5532ac1515532a482c, 0x65480022a5000eab0004553800000019),
  (0x401aa45522ad5522ad5522ad1505522a5952, 0x174420a),
  (0x401aa45532ac5532ac5532ac1505532a4aa4, 0x22a40012ab0004553600000019),
  (0x401aa45532ac5532ac5532ac1515532a4aac, 0x95440042ac000eab0001553800000017),
  (0x400aa75502af5502af5502af150550550550, 0xaaaf200000015),
  (0x401aa65502ae5502ae5502ae15155155180e, 0x14abc005551400000015),
  (0x401aa65502ae5502ae5512ae150551551826, 0x17540005aae400000015),
  (0x401aa65502ae5502ae5512ae15155155182e, 0xad51200000015),
  (0x401aa65502ae5512ae5512ae1505515518a6, 0x17540005aae400000015),
  (0x401aa65502ae5512ae5512ae1515515518ae, 0xaaae200000015),
  (0x401aa65502af5502af5502af150550550950, 0x174280a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_6 : coresOK P12 90 Cores_6 = true := by decide +kernel

def Cores_7 : List (ℕ × ℕ) := [(0x401aa65512ae5512ae5512ae150551551aa6, 0xaaae200000015),
  (0x401aa65512ae5512ae5512ae151551551aae, 0xaaae200000015),
  (0x402aa45502ad5502ad5522ad15255282d152, 0xad52200000015),
  (0x402aa55502ac5502ad5522ad15255282d452, 0x14abc005552400000015),
  (0x403aa45502ac5502ac5532ac15355382c82c, 0x554000182c000f540005aac800000019),
  (0x403aa45502ac5512ac5522ac15355382c88c, 0x2d52000b5440010ac000eab0002553a00000017),
  (0x403aa45502ac5512ac5532ac15255382c8a4, 0xf5400028ac0012ab0001553800000017),
  (0x403aa45502ac5512ac5532ac15355382c8ac, 0x17544005aac400000015),
  (0x403aa45502ad5502ad5522ad15255282c950, 0x162480a),
  (0x403aa45512ac5512ac5522ac15255382ca84, 0x8a98002d50000eab0003553800000017),
  (0x403aa45512ac5512ac5522ac15355282ca88, 0xad53200000015),
  (0x403aa45512ac5512ac5522ac15355382ca8c, 0x14ab8005553400000015),
  (0x403aa45512ac5512ac5532ac15255382caa4, 0xaaae200000015),
  (0x403aa45512ac5512ac5532ac15355382caac, 0x17544005aac400000015),
  (0x402aa45502ad5522ad5522ad1505528a5152, 0x22ad0004a940029500011548001aada00000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_7 : coresOK P12 105 Cores_7 = true := by decide +kernel

def Cores_8 : List (ℕ × ℕ) := [(0x402aa55502ac5522ad5522ad1505528a5452, 0x14ab4005550400000015),
  (0x403aa45502ac5532ac5532ac1505538a48a4, 0xaa90001550000f540005aac800000019),
  (0x403aa45502ac5532ac5532ac1515538a48ac, 0x17544005aac400000015),
  (0x403aa45502ad5522ad5522ad1505528a4950, 0x162480a),
  (0x403aa45512ac5522ac5532ac1505538a4a24, 0xf5400012a40012ab0002553800000017),
  (0x403aa45512ac5532ac5532ac1505538a4aa4, 0xb544003aa40012ab0001553800000019),
  (0x403aa45512ac5532ac5532ac1515538a4aac, 0x17544005aac400000015),
  (0x402aa45502ac5522ac5532ac1535538ac02c, 0x242c0012ab0004553600000019),
  (0x402aa45502ac5522ad5522ad1525528ad052, 0x65480022ac0011548002aad800000017),
  (0x402aa45502ac5532ac5532ac1525538ac0a4, 0x30a40012ab000455360000001b),
  (0x402aa45512ac5522ac5522ac1535538ac20c, 0x260e000cab0005553600000019),
  (0x402aa55502ac5522ac5522ad1525528ad412, 0x8ab40024120008ab0004552800000015),
  (0x402aa55502ac5522ad5522ad1525528ad452, 0x14ab4005552400000015),
  (0x403aa45502ac5522ac5522ac1535538ac80c, 0x17548005aac400000015),
  (0x403aa45502ac5522ac5532ac1525538ac824, 0x17548005aac400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_8 : coresOK P12 120 Cores_8 = true := by decide +kernel

def Cores_9 : List (ℕ × ℕ) := [(0x403aa45502ac5522ad5522ad1525528ac850, 0x162480a),
  (0x403aa45502ac5532ac5532ac1535538ac8ac, 0xaaac200000015),
  (0x403aa45502ad5522ad5522ad1525528ac950, 0x162480a),
  (0x403aa45512ac5522ac5522ac1535528aca08, 0x14ab4005553400000015),
  (0x403aa45512ac5522ac5532ac1535538aca2c, 0xaaac200000015),
  (0x403aa45512ac5532ac5532ac1535538acaac, 0xaaac200000015),
  (0x402aa45502ae5502ae5512ae15155195102e, 0x55620a),
  (0x402aa45502ae5512ae5512ae1505519510a6, 0x55620a),
  (0x403aa45502af5502af5502af150550950950, 0x174480a),
  (0x403aa45512ae5512ae5512ae150551950aa4, 0x162840a),
  (0x403aa45512ae5512ae5512ae151551950aac, 0x162840a),
  (0x402aa45522ac5522ac5532ac151553aa402c, 0x556800242e0016ab0002553800000019),
  (0x402aa45522ac5522ad5522ad150552aa5052, 0x14ab4005152400000015),
  (0x402aa45522ac5532ac5532ac150553aa40a4, 0x32a4000aab0005553600000019),
  (0x402aa45522ad5522ad5522ad150552aa4150, 0x49500004a90001aa40005548005aada00000021)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_9 : coresOK P12 135 Cores_9 = true := by decide +kernel

def Cores_10 : List (ℕ × ℕ) := [(0x402aa55522ac5522ac5522ac151552aa540a, 0x68420a),
  (0x402aa55522ac5522ac5522ad150552aa5412, 0x8ab400341a0005548003aad800000015),
  (0x402aa55522ac5522ad5522ad150552aa5452, 0x8ab400245a0005548004aad800000017),
  (0x403aa45522ac5522ac5522ac151553aa480c, 0xaaad200000015),
  (0x403aa45522ac5522ac5532ac150553aa4824, 0x1aa40005548003d520006540004aaca00000019),
  (0x403aa45522ac5522ad5522ad150552aa4850, 0x162480a),
  (0x403aa45532ac5532ac5532ac150553aa4aa4, 0xaaac200000015),
  (0x403aa45532ac5532ac5532ac151553aa4aac, 0xaaac200000015),
  (0x402aa45522ac5522ac5522ac153553aac00c, 0x340e000eab0003553600000013),
  (0x402aa45522ac5522ac5522ad152552aad012, 0x50480032ac0011548001aad800000015),
  (0x402aa45522ac5522ac5532ac152553aac024, 0x3026000eab0003553600000013),
  (0x402aa45522ac5522ac5532ac153553aac02c, 0x32ac00090b0005553600000019),
  (0x402aa45522ac5522ad5522ad152552aac050, 0x19520006ab00022ac0011548002aada00000019),
  (0x402aa45522ac5522ad5522ad152552aad052, 0xeab00022ad0006548004552800000019),
  (0x402aa45522ac5532ac5532ac152553aac0a4, 0x32a4000aab0005553600000019)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_10 : coresOK P12 150 Cores_10 = true := by decide +kernel

def Cores_11 : List (ℕ × ℕ) := [(0x402aa45522ad5522ad5522ad152552aad152, 0xad52200000015),
  (0x402aa55522ac5522ac5522ac152552aad402, 0x34020008ab0005aad600000017),
  (0x402aa55522ac5522ac5522ac153552aac408, 0x144260a),
  (0x402aa55522ac5522ac5522ad152552aac410, 0xaab00024120008ab4002552800000011),
  (0x402aa55522ac5522ac5522ad152552aad412, 0x8ab40024120008ab0004552800000015),
  (0x402aa55522ac5522ad5522ad152552aac450, 0x3452000cab4003aad600000013),
  (0x402aa55522ac5522ad5522ad152552aad452, 0x14ab4005552400000015),
  (0x403aa45522ac5522ac5522ac152553aac804, 0x17548005aac400000015),
  (0x403aa45522ac5522ac5522ac153553aac80c, 0x14ab4005553400000015),
  (0x403aa45522ac5522ac5522ad152552aac810, 0x162480a),
  (0x403aa45522ac5522ac5532ac152553aac824, 0x17548005aac400000015),
  (0x403aa45522ac5522ad5522ad152552aac850, 0x162480a),
  (0x403aa45532ac5532ac5532ac153553aacaac, 0xaaac200000015),
  (0x404aa25502a85552aa5552aa1558aa4550aa, 0x3454000caa8003aaa600000013),
  (0x404aa25512a85542aa5552aa1558aa45522a, 0x14aa8005555400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_11 : coresOK P12 165 Cores_11 = true := by decide +kernel

def Cores_12 : List (ℕ × ℕ) := [(0x404aa35502a85542ab5542ab1548ab454454, 0x151500052ab400000015),
  (0x404aa35502a95542aa5542ab1548ab454514, 0x14aac005554400000015),
  (0x405aa25502a85542aa5552aa1558aa45582a, 0x155500052aa400000015),
  (0x405aa25502a85552aa5552aa1548aa4558a2, 0x155500052aa400000015),
  (0x405aa25502a85552aa5552aa1558aa4548a8, 0x155500052aa400000015),
  (0x405aa25502a85552aa5552aa1558aa4558aa, 0x8aa80026550012aa8001555800000017),
  (0x405aa25502a95542ab5542ab1548aa454950, 0x164280a),
  (0x405aa25512a85542aa5542aa1558aa455a0a, 0x14aac005555400000015),
  (0x405aa25512a85542aa5552aa1558aa454a28, 0x155500052aa400000015),
  (0x405aa25512a85542aa5552aa1558aa455a2a, 0x14aa8005555400000015),
  (0x405aa25512a85552aa5552aa1558aa454aa8, 0x3455000caa8003aaa600000013),
  (0x405aa25512a85552aa5552aa1558aa455aaa, 0x14aa8005555400000015),
  (0x406aa05502a85562a95562a91568a98a9056, 0xeaa00014a90011558002aa980000001b),
  (0x406aa15502a85562a85562a91568a98a9416, 0x8aa40036160005058005aa9800000019),
  (0x407aa05502a85572a85572a81578a88a88a8, 0xaaa8200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_12 : coresOK P12 180 Cores_12 = true := by decide +kernel

def Cores_13 : List (ℕ × ℕ) := [(0x407aa05502a95562a95562a91568a88a8950, 0x162680a),
  (0x407aa05512a85562a85572a81578a88a8a28, 0xaaa8200000015),
  (0x407aa05512a85572a85572a81568a88a8aa0, 0xaaa8200000015),
  (0x407aa05512a85572a85572a81578a88a8aa8, 0xaaa8200000015),
  (0x406aa05502aa5552aa5552aa1558a89510aa, 0x65620a),
  (0x406aa05512aa5542aa5552aa1558a895122a, 0x65620a),
  (0x407aa05502ab5542ab5542ab1548a8950950, 0x164680a),
  (0x407aa05512aa5542aa5552aa1558a8950a28, 0x162860a),
  (0x407aa05512aa5552aa5552aa1558a8950aa8, 0x162860a),
  (0x406aa15522a85542a85562a91568a9a29416, 0x52a90009058002556600000015),
  (0x407aa05532a85552a85562a81578a8a28a88, 0xaaa8200000015),
  (0x407aa05532a85552a85572a81578a8a28aa8, 0xaaa8200000015),
  (0x406aa05522a85562a85562a91568a9aa9016, 0x8aa40020160008aa0004556800000015),
  (0x406aa05522a85562a95562a91568a8aa9052, 0x65480032a80011558002aa9800000019),
  (0x406aa05522a85562a95562a91568a9aa8054, 0x1aa800065580022a80011558002aa9a00000019)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_13 : coresOK P12 195 Cores_13 = true := by decide +kernel

def Cores_14 : List (ℕ × ℕ) := [(0x406aa05522a85562a95562a91568a9aa9056, 0x145580052a9400000015),
  (0x406aa05522a85572a85572a81578a8aa80a8, 0x95580042a8000eaa0001557800000017),
  (0x406aa05522a95562a95562a91568a8aa9152, 0x2d52000a5580012a80009558003aa9a00000017),
  (0x406aa05532a85562a85572a81578a8aa8228, 0x14aa0005557400000015),
  (0x406aa15522a85562a85562a81568a9aa9406, 0x34060008aa0005aa9600000017),
  (0x406aa15522a85562a85562a91568a9aa8414, 0x90580022a80009558002aa9800000011),
  (0x406aa15522a85562a85562a91568a9aa9416, 0x52a90009058002556600000015),
  (0x407aa05522a85562a85572a81578a8aa8828, 0x17558005aa8400000015),
  (0x407aa05522a85562a95562a91568a8aa8850, 0x162680a),
  (0x407aa05522a85572a85572a81568a8aa88a0, 0x17558005aa8400000015),
  (0x407aa05532a85562a85562a81578a8aa8a08, 0x14aa4005557400000015),
  (0x407aa05532a85572a85572a81578a8aa8aa8, 0xaaa8200000015),
  (0x404aa05502ac5532ac5532ac1539530ac0ac, 0xb5640a),
  (0x404aa05502ad5522ad5522ad1529520ad152, 0xb5642a),
  (0x404aa05512ac5522ac5532ac1539530ac22c, 0xb5640a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_14 : coresOK P12 210 Cores_14 = true := by decide +kernel

def Cores_15 : List (ℕ × ℕ) := [(0x404aa05512ac5532ac5532ac1529530ac2a4, 0xb5640a),
  (0x404aa15502ac5522ad5522ad1529520ad452, 0x156420a),
  (0x405aa05502ac5522ad5522ad1529520ad852, 0x174a20a),
  (0x405aa05502ad5522ad5522ad1529520ac950, 0x174a80a),
  (0x405aa05502ad5522ad5522ad1529520ad952, 0x174a20a),
  (0x405aa05512ac5532ac5532ac1529520acaa0, 0x1642a0a),
  (0x405aa05512ac5532ac5532ac1539520acaa8, 0x164260a),
  (0x404aa05532ac5532ac5532ac1509532a42a4, 0xb5640a),
  (0x404aa15522ac5522ad5522ad1509522a5452, 0x156420a),
  (0x405aa05522ac5522ad5522ad1509522a5852, 0x174a20a),
  (0x405aa05522ad5522ad5522ad1509522a4950, 0x174a80a),
  (0x405aa05522ad5522ad5522ad1509522a5952, 0x174a20a),
  (0x405aa05532ac5532ac5532ac1509522a4aa0, 0x1642a0a),
  (0x405aa05532ac5532ac5532ac1519522a4aa8, 0x164860a),
  (0x406aa05502ae5502ae5512ae15195195102e, 0xb5620a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_15 : coresOK P12 225 Cores_15 = true := by decide +kernel

def Cores_16 : List (ℕ × ℕ) := [(0x406aa05502ae5512ae5512ae1509519510a6, 0xb5620a),
  (0x406aa15502ae5502ae5502ae15195195140e, 0x14a820a),
  (0x407aa05502af5502af5502af150950950950, 0x174a80a),
  (0x407aa05512ae5512ae5512ae150950950aa0, 0x1628a0a),
  (0x407aa05512ae5512ae5512ae151950950aa8, 0x162860a),
  (0x406aa15522ac5522ac5522ac151951aa140e, 0x48a20a),
  (0x406aa15522ac5522ad5522ad150950aa1452, 0x85620a),
  (0x407aa05532ac5532ac5532ac150950aa0aa0, 0x1648a0a),
  (0x407aa05532ac5532ac5532ac151950aa0aa8, 0x164860a),
  (0x406aa05522ac5522ac5532ac153951aa802c, 0x63640a),
  (0x406aa05522ac5522ad5522ad152950aa9052, 0x85620a),
  (0x406aa05522ac5532ac5532ac152951aa80a4, 0xa3640a),
  (0x406aa05522ad5522ad5522ad152950aa9152, 0x85620a),
  (0x406aa15522ac5522ac5522ac152951aa9406, 0x48620a),
  (0x406aa15522ac5522ac5522ac153951aa840c, 0x14a840a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_16 : coresOK P12 240 Cores_16 = true := by decide +kernel

def Cores_17 : List (ℕ × ℕ) := [(0x406aa15522ac5522ac5522ad152950aa9412, 0x85620a),
  (0x406aa15522ac5522ad5522ad152950aa8450, 0x156480a),
  (0x406aa15522ac5522ad5522ad152950aa9452, 0x85620a),
  (0x407aa05522ac5522ac5532ac153950aa8828, 0x164860a),
  (0x407aa05522ac5522ad5522ad152950aa8850, 0x162680a),
  (0x407aa05522ac5532ac5532ac152950aa88a0, 0x1648a0a),
  (0x407aa05532ac5532ac5532ac153950aa8aa8, 0x164860a),
  (0x404aa25542a85552aa5552aa151aa24550aa, 0x21510014aa8002555600000015),
  (0x404aa25552a85552aa5552aa150aa24552a2, 0xae880032aa000aaa8003555800000019),
  (0x404aa35542a85542ab5542ab150aa3454454, 0x51500032ab000d170003aab800000019),
  (0x404aa35542a95542aa5542ab150aa3454514, 0x32a30015550002aab600000019),
  (0x405aa25542a85542aa5552aa151aa245582a, 0x32a3000aaa8005555600000019),
  (0x405aa25542a85552aa5552aa150aa24558a2, 0x32a2000aaa8005555600000019),
  (0x405aa25552a85552aa5552aa150aa2454aa0, 0x22a00012aa8004555600000019),
  (0x405aa25552a85552aa5552aa151aa2454aa8, 0x8aa800245d0012aa8001555800000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_17 : coresOK P12 255 Cores_17 = true := by decide +kernel

def Cores_18 : List (ℕ × ℕ) := [(0x405aa25552a85552aa5552aa151aa2455aaa, 0x8aa800245d0012aa8001555800000017),
  (0x407aa05572a85572a85572a8151aa0aa0aa8, 0xaaa8200000015),
  (0x406aa05562a85562a85562a9152aa1aa9016, 0x3aa8000c058003aa9600000013),
  (0x406aa05562a85562a95562a9152aa0aa9052, 0x1aa80008aa0003952000d558001aa9a00000019),
  (0x406aa05562a85562a95562a9152aa1aa8054, 0x85580022a80005558004aa9800000017),
  (0x406aa05562a85562a95562a9152aa1aa9056, 0x14aa4005156400000015),
  (0x406aa05562a85572a85572a8153aa0aa80a8, 0x21530014aa0002557600000015),
  (0x406aa05562a95562a95562a9152aa0aa9152, 0x4548001aa0000e548005aa9800000019),
  (0x406aa05572a85572a85572a8152aa0aa82a0, 0x22a00012aa0004557600000019),
  (0x406aa15562a85562a85562a8152aa1aa9406, 0xd0380014060004aa0005aa9800000019),
  (0x406aa15562a85562a85562a8153aa1aa840c, 0x62a40a),
  (0x406aa15562a85562a85562a9152aa1aa8414, 0xd0780014160004aa0005aa9800000019),
  (0x406aa15562a85562a85562a9152aa1aa9416, 0x8aa400341e0005058005aa9800000019),
  (0x407aa05562a85562a85572a8153aa0aa8828, 0xaaa9200000015),
  (0x407aa05562a85572a85572a8152aa0aa88a0, 0x15560006548001aa0000b558005aa8a00000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_18 : coresOK P12 270 Cores_18 = true := by decide +kernel

def Cores_19 : List (ℕ × ℕ) := [(0x407aa05572a85572a85572a8153aa0aa8aa8, 0xaaa8200000015),
  (0x404aa05542a85552aa5552aa155aaa0550aa, 0x145540052aa400000015),
  (0x404aa05542a95542ab5542ab154aab054154, 0x145500052ab400000015),
  (0x404aa05552a85552aa5552aa154aaa0552a2, 0x14aa8005155400000015),
  (0x404aa15542a85542ab5542ab154aab054454, 0x32a90015550002aab600000019),
  (0x404aa15542a95542aa5542ab154aab054514, 0x145500052ab400000015),
  (0x405aa05542a85542aa5552aa155aaa05582a, 0x8aa4001954000eaa8004555800000019),
  (0x405aa05542a85552aa5552aa154aaa0558a2, 0x30a4000eaa8003555600000013),
  (0x405aa05552a85552aa5552aa155aaa054aa8, 0x1aa800065540022a8000eaa8004555a0000001b),
  (0x405aa05552a85552aa5552aa155aaa055aaa, 0x145540052aa400000015),
  (0x404aa05542a95562a95562a9156aa90a8154, 0x32a80015558002aa9600000019),
  (0x404aa05542a95562a95562a9156aa90a9156, 0x15aa4005556400000015),
  (0x404aa15542a85562a85562a9156aa90a9416, 0x24160014aa4002556600000015),
  (0x404aa15542a85562a95562a9156aa90a8454, 0x52a00042a90009150004556800000019),
  (0x404aa15542a85562a95562a9156aa90a9456, 0x14aa4005556400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_19 : coresOK P12 285 Cores_19 = true := by decide +kernel

def Cores_20 : List (ℕ × ℕ) := [(0x405aa05552a85572a85572a8157aa80a8aa8, 0x14aa0005557400000015),
  (0x404aa05542aa5542aa5552aa155aaa15502a, 0x4aa80026aa00090a8005555800000019),
  (0x404aa05542ab5542ab5542ab154aab154154, 0x16550005aab400000015),
  (0x404aa05552aa5552aa5552aa154aaa1542a0, 0x49550008a80004555600000019),
  (0x404aa15542aa5542aa5542aa155aaa15540a, 0x14a420a),
  (0x404aa15542aa5542aa5542ab154aab154414, 0xdaa80014140004aac005554800000017),
  (0x404aa15542aa5542ab5542ab154aaa154450, 0x36aa0015550002aab600000019),
  (0x404aa15542aa5542ab5542ab154aab154454, 0x15aac005554400000015),
  (0x405aa05542aa5542aa5552aa154aaa155822, 0x4aa8001d540004a880019540006aa8004555c00000017),
  (0x405aa05542aa5542aa5552aa155aaa15582a, 0xad55200000015),
  (0x405aa05542aa5542ab5542ab154aaa154850, 0x164280a),
  (0x405aa05542aa5552aa5552aa154aaa1548a0, 0x5550001aa0000e550005aaa800000017),
  (0x405aa05552aa5552aa5552aa155aaa155aaa, 0x15aa8005555400000015),
  (0x404aa15562a85562a85562a9154aa92a1416, 0x3414000caa4003aa9600000013),
  (0x404aa15562a85562a95562a9154aa82a1452, 0x32a9000d150003aa9600000013)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_20 : coresOK P12 300 Cores_20 = true := by decide +kernel

def Cores_21 : List (ℕ × ℕ) := [(0x404aa15562a85562a95562a9154aa92a0454, 0x22a90004a800024540009558002aa9a00000015),
  (0x404aa15562a85562a95562a9154aa92a1456, 0x3454000caa4003aa9600000013),
  (0x405aa05572a85572a85572a8155aa82a0aa8, 0x95540042a8000eaa0001557800000017),
  (0x404aa35542a85542a95542ab154aab414454, 0x151500052ab400000015),
  (0x404aa35542a95542a95542aa154aab414544, 0x8aac0024140008aa4004554800000015),
  (0x405aa25542a85542a85552aa155aaa41582a, 0x4aa80032a90005054005555800000017),
  (0x405aa25542a85552a85552aa154aaa4158a2, 0xca80002414000aaa8003555800000017),
  (0x405aa25542a95542a95542aa154aaa415942, 0xc6420a),
  (0x405aa25552a85552a85552aa155aaa414aa8, 0x90540032a8000aaa8003555800000017),
  (0x405aa25552a85552a85552aa155aaa415aaa, 0x52aa0009054002555600000015),
  (0x404aa35542a85542ab5542ab154aa9450454, 0x14aac005454400000015),
  (0x404aa35542a95542aa5542ab154aa9450514, 0x34540010aac0015160005550002aaba00000019),
  (0x405aa25542a85542aa5552aa155aa845182a, 0x75400022a9000aaa8004555800000017),
  (0x405aa25542a85552aa5552aa154aa84518a2, 0xdaa40025540012aa800155580000001b),
  (0x405aa25552a85552aa5552aa155aa8450aa8, 0xaaa00022aa0006aa8004555800000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_21 : coresOK P12 315 Cores_21 = true := by decide +kernel

def Cores_22 : List (ℕ × ℕ) := [(0x405aa25552a85552aa5552aa155aa8451aaa, 0x3455000caa8003aaa600000013),
  (0x404aa25542a85542aa5552aa155aaa45502a, 0x242c0008aa8005555600000015),
  (0x404aa25542a85552aa5552aa154aaa4550a2, 0x32a2000aaa8005555600000019),
  (0x404aa35542a85542ab5542ab154aab454454, 0x151500052ab400000015),
  (0x404aa35542a95542aa5542ab154aab454514, 0x14aac005554400000015),
  (0x405aa25542a85542aa5552aa154aaa455822, 0x14aa8005554400000015),
  (0x405aa25542a85542aa5552aa155aaa454828, 0x155500052aa400000015),
  (0x405aa25542a85542aa5552aa155aaa45582a, 0x14aac005555400000015),
  (0x405aa25542a85542ab5542ab154aaa454850, 0x164280a),
  (0x405aa25542a85552aa5552aa154aaa4548a0, 0x14aa8005554400000015),
  (0x405aa25542a85552aa5552aa154aaa4558a2, 0x155500052aa400000015),
  (0x405aa25542a95542aa5542aa154aaa455902, 0x106420a),
  (0x405aa25542a95542aa5542ab154aaa454910, 0x164280a),
  (0x405aa25552a85552aa5552aa155aaa455aaa, 0x14aa8005555400000015),
  (0x407aa05552a85552a85572a8157aa8828aa8, 0x17554005aa8400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_22 : coresOK P12 330 Cores_22 = true := by decide +kernel

def Cores_23 : List (ℕ × ℕ) := [(0x407aa05552a85572a85572a8155aa88a0aa8, 0x17554005aa8400000015),
  (0x406aa05562a85562a85562a8156aa9aa9006, 0x16aa00034060009558001aa980000001b),
  (0x406aa05562a85562a85562a9156aa8aa9012, 0x1aa800050580022a80011558001aa9a00000017),
  (0x406aa05562a85562a85562a9156aa9aa9016, 0x8aa40020160008aa0004556800000015),
  (0x406aa05562a85562a85572a8157aa8aa8028, 0x50a000142e0008aa0005557800000015),
  (0x406aa05562a85572a85572a8156aa8aa80a0, 0x30a6000eaa0003557600000013),
  (0x406aa15562a85562a85562a8156aa9aa9406, 0x34060008aa0005aa9600000017),
  (0x406aa15562a85562a85562a8157aa8aa8408, 0x14a260a),
  (0x407aa05562a85562a85572a8156aa8aa8820, 0x17558005aa8400000015),
  (0x407aa05572a85572a85572a8157aa8aa8aa8, 0xaaa8200000015),
  (0x400aa455b2a055b2a455b2a42a445b2a42a4, 0x14a9000555b400000015),
  (0x400aa555a2a055a2a455a2a52a545a2a541a, 0x91680032a50008a9000355a800000019),
  (0x400aa555a2a055a2a555a2a52a545a2a545a, 0x22a0000ca9400555a600000019),
  (0x400aa555a2a155a2a455a2a42a545a2a550a, 0x250a0014a9400355a600000019),
  (0x400aa555a2a155a2a455a2a52a545a2a551a, 0x14a9400555a400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_23 : coresOK P12 345 Cores_23 = true := by decide +kernel

def Cores_24 : List (ℕ × ℕ) := [(0x400aa555a2a155a2a555a2a52a545a2a555a, 0x14a9400555a400000015),
  (0x401aa455a2a155a2a555a2a52a545a2a595a, 0x174420a),
  (0x401aa455b2a055b2a455b2a42a445b2a4aa4, 0x14a9000555b400000015),
  (0x400aa65582a05592a65592a62a64594590a6, 0x32a60008a80005559600000019),
  (0x400aa75582a05582a75582a72a7458458458, 0x26a00011560004aa7600000019),
  (0x400aa75582a15582a65582a72a7458458518, 0x32a70004a84006558600000019),
  (0x400aa75582a15582a75582a72a7458458558, 0x12a1000ca9c006558600000019),
  (0x401aa65582a15582a65582a62a6459459906, 0x10a620a),
  (0x401aa65582a15582a75582a72a7458458958, 0x174260a),
  (0x401aa65592a05592a65592a62a6459459aa6, 0x32a60008a80005559600000019),
  (0x400aa65582a25592a45592a62a64595190a6, 0x14a98005559400000015),
  (0x400aa75582a35582a55582a62a7458518548, 0x14a9c005558400000015),
  (0x400aa75582a35582a55582a72a7458518558, 0x14a9c005558400000015),
  (0x401aa65582a25582a45592a62a6459519826, 0x14a9c005559400000015),
  (0x401aa65582a35582a55582a72a7458518958, 0x174260a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_24 : coresOK P12 360 Cores_24 = true := by decide +kernel

def Cores_25 : List (ℕ × ℕ) := [(0x401aa65592a25592a45592a62a6459519aa6, 0x14a98005559400000015),
  (0x400aa65592a25592a65592a62a64585592a2, 0x24580014a98003559600000019),
  (0x400aa75582a25582a65582a72a7458558418, 0x50600022a70008a98004558800000015),
  (0x400aa75582a35582a65582a62a7458558508, 0x52a70009420002558600000015),
  (0x400aa75582a35582a75582a72a7458558558, 0x14a9c005558400000015),
  (0x401aa65582a25582a65582a72a7458558818, 0x174260a),
  (0x401aa65582a25582a65592a62a6458559822, 0x155600052a6400000015),
  (0x401aa65582a35582a65582a62a6459558904, 0x102640a),
  (0x401aa65592a25592a65592a62a6459559aa6, 0x14a98005559400000015),
  (0x402aa45582a25582a65592a62a6459959026, 0x55620a),
  (0x402aa45582a25592a65592a62a64589590a2, 0xb5620a),
  (0x403aa45582a25582a65582a72a7458958818, 0x174460a),
  (0x403aa45582a35582a65582a62a6459958904, 0x102640a),
  (0x403aa45582a35582a75582a72a7458958958, 0x174460a),
  (0x402aa455a2a055a2a455a2a52a545aaa501a, 0x12a500050680022a40011568001aa5a00000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_25 : coresOK P12 375 Cores_25 = true := by decide +kernel

def Cores_26 : List (ℕ × ℕ) := [(0x402aa455a2a055b2a455b2a42a445baa40a4, 0x14a9000555b400000015),
  (0x402aa455b2a055b2a455b2a42a445aaa42a0, 0x52a4000916800355b600000019),
  (0x402aa555a2a055a2a455a2a42a545aaa540a, 0x145a0008a9000240a0005568003aa5a00000017),
  (0x402aa555a2a055a2a455a2a52a545aaa541a, 0x50680022a50008a9000455a800000015),
  (0x402aa555a2a155a2a455a2a42a545aaa550a, 0x52a5000942800355a600000017),
  (0x403aa455a2a055a2a455a2a52a545aaa4818, 0x162460a),
  (0x403aa455a2a055a2a455b2a42a445baa4824, 0x14a9400555b400000015),
  (0x403aa455a2a055b2a455b2a42a445aaa48a0, 0x155680052a4400000015),
  (0x403aa455a2a155a2a455a2a42a445baa4904, 0x10a240a),
  (0x403aa455b2a055b2a455b2a42a445baa4aa4, 0x14a9000555b400000015),
  (0x400aa455b2a455b2a455b2a42a455b2a42a4, 0xaaa4200000015),
  (0x400aa555a2a455a2a455a2a42a555a2a540a, 0x32a5000d028003aa5600000013),
  (0x400aa555a2a555a2a555a2a52a555a2a555a, 0xaaa5200000015),
  (0x401aa455a2a455a2a455a2a42a555a2a580a, 0x174420a),
  (0x401aa455a2a455a2a455b2a42a455b2a4824, 0x17568005aa4400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_26 : coresOK P12 390 Cores_26 = true := by decide +kernel

def Cores_27 : List (ℕ × ℕ) := [(0x401aa455a2a555a2a555a2a52a555a2a595a, 0x174420a),
  (0x401aa455b2a455b2a455b2a42a455b2a4aa4, 0xaaa4200000015),
  (0x400aa75582a55582a55582a72a7558418558, 0x24180014a9c003558600000017),
  (0x401aa65582a45582a45592a62a6559419826, 0x12a60008a940014190004a9c004559a00000015),
  (0x401aa65582a55582a55582a62a6558419942, 0xc4620a),
  (0x401aa65582a55582a55582a72a7558418958, 0x174260a),
  (0x401aa65592a45592a45592a62a6559418aa4, 0x3419000ca98003aa6600000013),
  (0x401aa65592a45592a45592a62a6559419aa6, 0x34190014a98003559600000019),
  (0x400aa65582a65582a65582a62a6559559006, 0x3406000ea98003559600000013),
  (0x400aa65582a65582a65582a72a7558558018, 0x10a98006558400000019),
  (0x400aa75582a65582a65582a62a7558558408, 0x12a700110200012a60005560003aa7a00000015),
  (0x400aa75582a75582a75582a72a7558558558, 0xaaa7200000015),
  (0x401aa65582a65582a65582a62a6558559802, 0x14a9c005559400000015),
  (0x401aa65582a65582a65582a62a6559559806, 0x14a9c005559400000015),
  (0x401aa65582a65582a65582a62a7558558808, 0x174260a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_27 : coresOK P12 405 Cores_27 = true := by decide +kernel

def Cores_28 : List (ℕ × ℕ) := [(0x401aa65582a65582a65582a72a7558558818, 0x174260a),
  (0x401aa65592a65592a65592a62a6559559aa6, 0xaaa6200000015),
  (0x403aa45582a55582a55582a72a7558818958, 0x174460a),
  (0x403aa45592a45592a45592a62a6559818aa4, 0x162640a),
  (0x403aa45592a45592a455b2a42a455b824aa4, 0x14a9800555b400000015),
  (0x402aa45582a65582a65582a72a7558958018, 0x55626a),
  (0x402aa55582a65582a65582a62a6558959402, 0x144620a),
  (0x403aa45582a75582a75582a72a7558958958, 0x174460a),
  (0x402aa455a2a455a2a455a2a42a555aaa500a, 0xd0280022a40005568004aa5800000017),
  (0x402aa455a2a455a2a455a2a52a555aaa4018, 0x341a0008a90005aa5600000017),
  (0x402aa455a2a455a2a455b2a42a455baa4024, 0x22a4000909800555b600000015),
  (0x402aa555a2a455a2a455a2a42a455aaa5402, 0xd0080022a40005568003aa5800000013),
  (0x402aa555a2a455a2a455a2a42a555aaa540a, 0x516800150a0004a9400240a0008a90003aa5c00000017),
  (0x403aa455a2a455a2a455a2a42a455baa4804, 0x14a9400555b400000015),
  (0x403aa455b2a455b2a455b2a42a455baa4aa4, 0xaaa4200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_28 : coresOK P12 420 Cores_28 = true := by decide +kernel

def Cores_29 : List (ℕ × ℕ) := [(0x404aa05592a455b2a455b2a42a495b0a42a4, 0xb5640a),
  (0x404aa15582a455a2a455a2a52a595a0a541a, 0x156420a),
  (0x405aa05582a455a2a455a2a52a595a0a581a, 0x174a20a),
  (0x405aa05582a555a2a555a2a52a595a0a4958, 0x174a60a),
  (0x405aa05582a555a2a555a2a52a595a0a595a, 0x174a20a),
  (0x405aa05592a455b2a455b2a42a495a0a4aa0, 0x1642a0a),
  (0x404aa055b2a455b2a455b2a42a495b2a42a4, 0xb5640a),
  (0x405aa055a2a455b2a455b2a42a495a2a48a0, 0x1642a0a),
  (0x405aa055a2a555a2a555a2a52a595a2a595a, 0x174a20a),
  (0x405aa055b2a455b2a455b2a42a495a2a4aa0, 0x1642a0a),
  (0x405aa25582a45592a45592a62a69584198a2, 0x164620a),
  (0x405aa25582a55582a55582a62a6958419942, 0xc4620a),
  (0x405aa25582a55582a55582a72a7958418958, 0x174260a),
  (0x405aa25592a45592a45592a62a6958418aa0, 0x1646a0a),
  (0x405aa25592a45592a45592a62a6958419aa2, 0x164620a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_29 : coresOK P12 435 Cores_29 = true := by decide +kernel

def Cores_30 : List (ℕ × ℕ) := [(0x407aa05582a55582a55582a72a7958818958, 0x174a60a),
  (0x407aa05592a45592a45592a62a6958818aa0, 0x1626a0a),
  (0x407aa05582a555a2a555a2a52a59588a0958, 0x162a60a),
  (0x407aa05592a455b2a455b2a42a49588a0aa0, 0x1646a0a),
  (0x406aa05582a65582a65582a72a7958958018, 0xb5626a),
  (0x406aa05582a65582a65592a62a6958959022, 0xb5620a),
  (0x406aa05582a65582a65592a62a6959959026, 0xb5620a),
  (0x406aa05582a65592a65592a62a69589580a0, 0x15626aa),
  (0x406aa15582a65582a65582a62a6959959406, 0x14a620a),
  (0x407aa05582a75582a75582a72a7958958958, 0x174a60a),
  (0x407aa05592a65592a65592a62a6958958aa0, 0x1626a0a),
  (0x406aa155a2a455a2a455a2a42a4959aa1406, 0x46a20a),
  (0x407aa055b2a455b2a455b2a42a4958aa0aa0, 0x1646a0a),
  (0x404aa355c2a055c2a055c2a32a3aa341c41c, 0xd0700032a30008a8000355c800000019),
  (0x404aa355c2a055c2a155c2a22a3aa341c44c, 0x240c0004a8000145c0010a8c00355ca00000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_30 : coresOK P12 450 Cores_30 = true := by decide +kernel

def Cores_31 : List (ℕ × ℕ) := [(0x404aa355c2a155c2a155c2a22a2aa341c544, 0x42a3000d01000255c600000011),
  (0x405aa255c2a055d2a055d2a22a2aa241d8a2, 0x52a2000907400255d600000015),
  (0x405aa255d2a055d2a055d2a22a2aa241caa0, 0x32a2000d074003aa2600000013),
  (0x405aa255d2a055d2a055d2a22a2aa241daa2, 0x32a2000d074003aa2600000013),
  (0x406aa155e2a055e2a055e2a02a1aa1aa140e, 0x517800150e0004a8400240e0008a80004aa1c0000001b),
  (0x407aa055f2a055f2a055f2a02a0aa0aa0aa0, 0xaaa0200000015),
  (0x400aaf5502a75502af5502af450550550550, 0x14abc005550400000015),
  (0x401aae5512a65512ae5512ae450551551aa6, 0x3451000cab8003aae600000013),
  (0x401aae5512a65512ae5512ae451551551aae, 0x14ab8005551400000015),
  (0x402aad5502a45502ad5522ad45255282d452, 0x4ab40012af0004a98006552800000019),
  (0x402aad5502a55502ac5522ad45255282d512, 0x14abc005552400000015),
  (0x403aac5502a45502ac5532ac45355382c82c, 0x25500008ab000202c0007540003553a00000019),
  (0x403aac5502a45512ac5522ac45355382c88c, 0x75600032ac000754000155000042b0004553c0000001b),
  (0x403aac5512a45512ac5522ac45355282ca88, 0x12ac00075400012ae0004ab4005553a00000017),
  (0x403aac5512a45512ac5532ac45255382caa4, 0xaa980022ae0006ab0004553800000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_31 : coresOK P12 465 Cores_31 = true := by decide +kernel

def Cores_32 : List (ℕ × ℕ) := [(0x403aac5512a45512ac5532ac45355382caac, 0x14ab8005553400000015),
  (0x402aac5522a45522ac5532ac451553aa402c, 0x24520008ab0002424000aab0002553a00000015),
  (0x402aac5522a45522ad5522ad450552aa5052, 0x14ab4005452400000015),
  (0x402aac5522a55522ac5522ad450552aa5112, 0x22a40011548004aad600000019),
  (0x402aad5522a45522ac5522ad450552aa5412, 0x14ab4005452400000015),
  (0x402aad5522a45522ad5522ad450552aa4450, 0xf5400034520004a90003aad800000019),
  (0x402aad5522a45522ad5522ad450552aa5452, 0x151480052ad400000015),
  (0x402aad5522a55522ac5522ac450552aa5502, 0x14ab400150a000d548001aad80000001b),
  (0x402aad5522a55522ac5522ad450552aa4510, 0x14ab4005550400000015),
  (0x402aad5522a55522ac5522ad450552aa5512, 0x151480052ad400000015),
  (0x403aac5522a45522ac5532ac450553aa4824, 0x24240008ab00025520009148003aaca00000019),
  (0x403aac5522a45522ad5522ad450552aa4850, 0x162480a),
  (0x403aac5522a55522ac5522ad450552aa4910, 0x162480a),
  (0x403aac5532a45532ac5532ac450553aa4aa4, 0x22a40012ab0004553600000019),
  (0x403aac5532a45532ac5532ac451553aa4aac, 0x3453000cab0003aac600000013)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_32 : coresOK P12 480 Cores_32 = true := by decide +kernel

def Cores_33 : List (ℕ × ℕ) := [(0x402aac5522a45522ac5522ad452552aad012, 0x90480022ac0009548002aad800000011),
  (0x402aac5522a45522ac5532ac452553aac024, 0x12ac000554800145200090980012a4000aab0002553e00000017),
  (0x402aac5522a45522ac5532ac453553aac02c, 0x3426000cab0005553600000019),
  (0x402aac5522a45522ad5522ad452552aac050, 0x32ac0015548002aad600000019),
  (0x402aad5522a45522ac5522ac452552aad402, 0x51480044020008ab0004aad800000015),
  (0x402aad5522a45522ac5522ad452552aad412, 0x151480052ad400000015),
  (0x402aad5522a45522ad5522ad452552aad452, 0x151480052ad400000015),
  (0x402aad5522a55522ac5522ac452552aad502, 0x8ab40025020008ab0004552800000015),
  (0x402aad5522a55522ac5522ad452552aad512, 0x14ab4005552400000015),
  (0x403aac5522a45522ac5532ac452553aac824, 0x155480052ac400000015),
  (0x403aac5522a45522ad5522ad452552aac850, 0x162480a),
  (0x403aac5532a45532ac5532ac453553aacaac, 0x14ab0005553400000015),
  (0x404aab5502a15542aa5542ab4548ab454514, 0x151500052ab400000015),
  (0x405aaa5502a05542aa5552aa4558aa45582a, 0x95500022a50012aa8001555800000017),
  (0x405aaa5502a05552aa5552aa4548aa4558a2, 0x34a0000eaa8003555600000013)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_33 : coresOK P12 495 Cores_33 = true := by decide +kernel

def Cores_34 : List (ℕ × ℕ) := [(0x405aaa5502a05552aa5552aa4558aa4558aa, 0x12a500051540016050009954005aaaa00000017),
  (0x405aaa5502a15542aa5542aa4558aa45590a, 0x10a420a),
  (0x405aaa5502a15542ab5542ab4548aa454950, 0x164280a),
  (0x405aaa5512a05542aa5542aa4558aa455a0a, 0x4aa80022ab0008a94005555800000019),
  (0x405aaa5512a05542aa5552aa4548aa455a22, 0x3624000eaa8003555600000013),
  (0x405aaa5512a05542aa5552aa4558aa455a2a, 0x151540052aa400000015),
  (0x405aaa5512a05552aa5552aa4548aa454aa0, 0x58100022a4000d150005aaa80000001b),
  (0x405aaa5512a05552aa5552aa4548aa455aa2, 0x151540052aa400000015),
  (0x405aaa5512a05552aa5552aa4558aa455aaa, 0x14aa8005455400000015),
  (0x404aaa5502a25552a85552aa4558aa5150aa, 0x95400052aa0006aa8002555800000017),
  (0x404aaa5512a25542a85552aa4558aa51522a, 0x14aa8005555400000015),
  (0x404aab5502a35542a95542aa4548ab514544, 0x14aac005554400000015),
  (0x405aaa5502a25542a85552aa4558aa51582a, 0x155500052aa400000015),
  (0x405aaa5502a25552a85552aa4548aa5158a2, 0x155500052aa400000015),
  (0x405aaa5502a25552a85552aa4558aa5158aa, 0x35500014aa8002555600000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_34 : coresOK P12 510 Cores_34 = true := by decide +kernel

def Cores_35 : List (ℕ × ℕ) := [(0x405aaa5502a35542a95542ab4548aa514950, 0x164280a),
  (0x405aaa5512a25542a85542aa4558aa515a0a, 0x14aac005555400000015),
  (0x405aaa5512a25542a85552aa4548aa515a22, 0x155500052aa400000015),
  (0x405aaa5512a25542a85552aa4558aa515a2a, 0x14aa8005555400000015),
  (0x405aaa5512a25552a85552aa4548aa514aa0, 0x14aa8005554400000015),
  (0x405aaa5512a25552a85552aa4548aa515aa2, 0x151d00091540032aa0005054002aaaa00000013),
  (0x405aaa5512a25552a85552aa4558aa515aaa, 0x14aa8005555400000015),
  (0x406aa85502a05562a95562a94568a98a9056, 0x145600058180026560004a98005aa9a00000017),
  (0x406aa85502a15562a85562a94568a98a9116, 0x8aa40036160005558004aa9800000017),
  (0x406aa95502a05562a85562a94568a98a9416, 0x51580036160004aa0005aa9800000017),
  (0x406aa95502a15562a85562a84568a98a9506, 0x17060008aa40026060005558003aa9a00000015),
  (0x407aa85502a15562a95562a94568a88a8950, 0x162680a),
  (0x407aa85512a05562a85572a84578a88a8a28, 0x915c0032a80009144003aa8800000019),
  (0x407aa85512a05572a85572a84568a88a8aa0, 0x915c0032a80009144003aa8800000019),
  (0x407aa85512a05572a85572a84578a88a8aa8, 0x915c0032a80009144003aa8800000019)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_35 : coresOK P12 525 Cores_35 = true := by decide +kernel

def Cores_36 : List (ℕ × ℕ) := [(0x406aa85502a25552aa5552aa4558a89510aa, 0x65620a),
  (0x406aa85512a25542aa5552aa4558a895122a, 0x65620a),
  (0x407aa85502a35542ab5542ab4548a8950950, 0x164680a),
  (0x407aa85512a25542aa5552aa4558a8950a28, 0x162860a),
  (0x407aa85512a25552aa5552aa4548a8950aa0, 0x1628a0a),
  (0x407aa85512a25552aa5552aa4558a8950aa8, 0x162860a),
  (0x406aa85522a05542a95562a94568a9a29056, 0x14aa4005456400000015),
  (0x406aa85522a15542a85562a94568a9a29116, 0x14160009458001457000caa4002aa9a00000013),
  (0x406aa95522a05542a85562a94568a9a29416, 0x151580052a9400000015),
  (0x406aa95522a15542a85562a84568a9a29506, 0x52a90009418002556600000015),
  (0x407aa85532a05552a85562a84578a8a28a88, 0x14aa0005557400000015),
  (0x407aa85532a05552a85572a84568a8a28aa0, 0x32a8000d15c003aa8600000013),
  (0x407aa85532a05552a85572a84578a8a28aa8, 0x14aa0005557400000015),
  (0x406aa85522a05562a95562a94548a9aa1056, 0x14aa4005456400000015),
  (0x406aa85522a15562a85562a94548a9aa1116, 0x8a900024160009558004aa9800000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_36 : coresOK P12 540 Cores_36 = true := by decide +kernel

def Cores_37 : List (ℕ × ℕ) := [(0x406aa95522a05562a85562a94548a9aa1416, 0x14aa4005456400000015),
  (0x406aa95522a05562a95562a94548a8aa1452, 0x14a00004ab4001d52000d1580012a80005558002aa9e00000017),
  (0x406aa95522a15562a85562a84548a9aa1506, 0x32a9000d018003aa9600000013),
  (0x406aa95522a15562a85562a94548a8aa1512, 0x34a0000d558003aa9600000013),
  (0x407aa85532a05572a85572a84548a8aa0aa0, 0x34570008a80005aa8600000017),
  (0x407aa85532a05572a85572a84558a8aa0aa8, 0x32a8000d15c003aa8600000013),
  (0x406aa85522a05562a85562a94568a9aa9016, 0x91580024160008aa0004aa9800000015),
  (0x406aa85522a05562a95562a94568a8aa9052, 0x32a80015558002aa9600000019),
  (0x406aa85522a05562a95562a94568a9aa8054, 0x34560008aa0004aa9600000015),
  (0x406aa85522a05572a85572a84578a8aa80a8, 0x32a8000d158003aa8600000013),
  (0x406aa85522a15562a85562a94568a8aa9112, 0x32a80015558002aa9600000019),
  (0x406aa85532a05562a85572a84578a8aa8228, 0x14aa0005557400000015),
  (0x406aa95522a05562a85562a84568a9aa9406, 0x1aa80004aa4001456000d0180015060008aa0004aa9e0000001f),
  (0x406aa95522a05562a85562a94568a8aa9412, 0x8aa40024120008aa0004556800000015),
  (0x406aa95522a05562a85562a94568a9aa9416, 0x14aa4005456400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_37 : coresOK P12 555 Cores_37 = true := by decide +kernel

def Cores_38 : List (ℕ × ℕ) := [(0x406aa95522a05562a95562a94568a8aa9452, 0x5288001d5200091580022a90004aa0002556c00000015),
  (0x406aa95522a15562a85562a84568a8aa9502, 0x4aa4001aa800050080015060008aa0004556c00000015),
  (0x406aa95522a15562a85562a84568a9aa9506, 0x52a90009418003556600000017),
  (0x406aa95522a15562a85562a94568a8aa9512, 0x155480052a9400000015),
  (0x407aa85522a05562a85572a84578a8aa8828, 0x14aa0005556400000015),
  (0x407aa85522a05562a95562a94568a8aa8850, 0x162680a),
  (0x407aa85522a05572a85572a84568a8aa88a0, 0x155580052a8400000015),
  (0x407aa85532a05562a85562a84578a8aa8a08, 0x14aa4005557400000015),
  (0x407aa85532a05562a85572a84568a8aa8a20, 0x14aa0005556400000015),
  (0x407aa85532a05572a85572a84578a8aa8aa8, 0x14aa0005557400000015),
  (0x404aa85512a45522ac5532ac4539530ac22c, 0x75640a),
  (0x405aa85502a55522ad5522ad4529520ad952, 0x174620a),
  (0x406aa85502a65502ae5512ae45195195102e, 0x75620a),
  (0x406aa85502a65512ae5512ae4509519510a6, 0xb5620a),
  (0x407aa85502a75502af5502af450950950950, 0x174680a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_38 : coresOK P12 570 Cores_38 = true := by decide +kernel

def Cores_39 : List (ℕ × ℕ) := [(0x407aa85512a65512ae5512ae450950950aa0, 0x1628a0a),
  (0x407aa85512a65512ae5512ae451950950aa8, 0x162860a),
  (0x406aa95522a45522ad5522ad450950aa1452, 0x85620a),
  (0x406aa95522a55522ac5522ad450950aa1512, 0x85620a),
  (0x407aa85532a45532ac5532ac450950aa0aa0, 0x1648a0a),
  (0x407aa85532a45532ac5532ac451950aa0aa8, 0x164860a),
  (0x406aa85522a45522ac5532ac453951aa802c, 0x63640a),
  (0x406aa95522a45522ac5522ac452951aa9406, 0x48620a),
  (0x406aa95522a45522ac5522ad452950aa9412, 0x85620a),
  (0x406aa95522a45522ad5522ad452950aa9452, 0x85620a),
  (0x406aa95522a55522ac5522ac452950aa9502, 0x105620a),
  (0x406aa95522a55522ac5522ad452950aa9512, 0x85620a),
  (0x407aa85522a45522ad5522ad452950aa8850, 0x162680a),
  (0x407aa85522a45532ac5532ac452950aa88a0, 0x1648a0a),
  (0x404aab5542a05542ab5542ab450aa3454454, 0x90100024540009a80005aab800000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_39 : coresOK P12 585 Cores_39 = true := by decide +kernel

def Cores_40 : List (ℕ × ℕ) := [(0x404aab5542a15542aa5542ab450aa3454514, 0x151500052ab400000015),
  (0x405aaa5542a05542aa5552aa451aa245582a, 0x24550008a8c0022ab0006aa8003555a00000017),
  (0x405aaa5552a05552aa5552aa450aa2454aa0, 0x22a0000d150005aaa600000017),
  (0x405aaa5552a05552aa5552aa450aa2455aa2, 0x22a2000d154004aaa600000015),
  (0x405aaa5552a05552aa5552aa451aa2454aa8, 0x14aa8005455400000015),
  (0x405aaa5552a05552aa5552aa451aa2455aaa, 0x14aa8005455400000015),
  (0x404aab5542a35542a85542ab450aa3514514, 0x9a800024140009550004aab800000015),
  (0x404aab5542a35542a95542aa450aa3514544, 0x151500052ab400000015),
  (0x405aaa5542a25542a85552aa451aa251582a, 0x32a3000aaa8005555600000019),
  (0x405aaa5552a25552a85552aa450aa2514aa0, 0x22a00012aa8004555600000019),
  (0x405aaa5552a25552a85552aa451aa2514aa8, 0x8a800034150012aa8001555800000015),
  (0x405aaa5552a25552a85552aa451aa2515aaa, 0x1415000915400151d000caa8002aaaa00000013),
  (0x406aa85562a05562a95562a9450aa1aa1056, 0x22a1000d158004aa9600000015),
  (0x407aa85572a05572a85572a8451aa0aa0aa8, 0x34570008a80005aa8600000017),
  (0x406aa85562a05562a85562a9452aa1aa9016, 0x91580024160008aa0004aa9800000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_40 : coresOK P12 600 Cores_40 = true := by decide +kernel

def Cores_41 : List (ℕ × ℕ) := [(0x406aa95562a05562a85562a8452aa1aa9406, 0x1456000d0180022a80005558004aa9a0000001b),
  (0x406aa95562a05562a85562a9452aa0aa9412, 0x1aa800090480014560004a80004aa9a00000015),
  (0x406aa95562a05562a85562a9452aa1aa9416, 0x14aa4005456400000015),
  (0x406aa95562a05562a95562a9452aa0aa9452, 0x22a0000d148005aa9600000017),
  (0x406aa95562a15562a85562a8452aa0aa9502, 0x240200094180022a00009558003aa9a00000019),
  (0x406aa95562a15562a85562a8452aa1aa9506, 0x32a9000d018003aa9600000013),
  (0x406aa95562a15562a85562a9452aa0aa9512, 0x14aa4005552400000015),
  (0x407aa85562a05562a85572a8453aa0aa8828, 0x55580014560004aa40012a10012aa0001557c00000017),
  (0x407aa85562a05572a85572a8452aa0aa88a0, 0x34a2000eaa0003557600000013),
  (0x407aa85572a05572a85572a8453aa0aa8aa8, 0x32a8000d15c003aa8600000013),
  (0x404aa95542a05562a85562a9456aa90a9416, 0x90500022a90008aa0004556800000015),
  (0x404aa95542a05562a95562a9456aa90a8454, 0x14a4000caa40014540004aa0004556a00000017),
  (0x404aa95542a15562a85562a8456aa90a9506, 0x52a90009418002556600000015),
  (0x404aa95542a15562a85562a9456aa90a9516, 0x14aa4005556400000015),
  (0x405aa85552a05572a85572a8457aa80a8aa8, 0x14aa0005557400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_41 : coresOK P12 615 Cores_41 = true := by decide +kernel

def Cores_42 : List (ℕ × ℕ) := [(0x404aab5542a05542a95542ab454aab414454, 0x24540004a800024140004aa4004aaba00000015),
  (0x404aab5542a15542a85542ab454aab414514, 0x8aac0024140008aa4004554800000015),
  (0x404aab5542a15542a95542aa454aab414544, 0x151500052ab400000015),
  (0x405aaa5542a05552a85552aa454aaa4158a2, 0x52900034550004aa40022aa0004a88002555c00000019),
  (0x405aaa5552a05552a85552aa455aaa414aa8, 0x91540024150008aa0004aaa800000015),
  (0x405aaa5552a05552a85552aa455aaa415aaa, 0x151540052aa400000015),
  (0x404aaa5542a05542aa5552aa455aaa45502a, 0x24240008aa8005555600000015),
  (0x404aab5542a05542ab5542ab454aab454454, 0x91500014040009a90005aab800000017),
  (0x404aab5542a15542aa5542aa454aab454504, 0x4a800024040008aa8005554800000015),
  (0x404aab5542a15542aa5542ab454aab454514, 0x151500052ab400000015),
  (0x405aaa5542a05542ab5542ab454aaa454850, 0x164280a),
  (0x405aaa5542a05552aa5552aa454aaa4548a0, 0x155400052900012a00009150005aaaa00000017),
  (0x405aaa5552a05552aa5552aa455aaa455aaa, 0x14aa8005455400000015),
  (0x405aaa5542a25542a85552a8455aaa50582a, 0x4aa80032a90005414005555800000017),
  (0x405aaa5542a25552a85552a8454aaa5058a2, 0x1504000caa80024a40006aa8003555a00000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_42 : coresOK P12 630 Cores_42 = true := by decide +kernel

def Cores_43 : List (ℕ × ℕ) := [(0x405aaa5552a25552a85552a8455aaa505aaa, 0x52aa0009414002555600000015),
  (0x404aaa5542a25542a85552aa455aaa51502a, 0x90900022aa00040a8005555800000015),
  (0x404aab5542a35542a95542aa454aab514544, 0x14aac005554400000015),
  (0x405aaa5542a25542a85552aa455aaa51582a, 0x14aac005555400000015),
  (0x405aaa5542a25552a85552aa454aaa5148a0, 0x155500052aa400000015),
  (0x405aaa5552a25552a85552aa455aaa515aaa, 0x14050010aa8004555600000011),
  (0x407aa85552a05552a85572a8457aa8828aa8, 0x14aa8005557400000015),
  (0x407aa85552a05572a85572a8455aa88a0aa8, 0x14aa0005555400000015),
  (0x406aa95562a05562a85562a8456aa9aa9406, 0x1aa80004aa400145600090180022a80005558001aa9e00000017),
  (0x407aa85572a05572a85572a8457aa8aa8aa8, 0x42a8000501c004557600000011),
  (0x400aaf5502af5502af5502af550550550550, 0xaaaf200000015),
  (0x401aae5502ae5502af5502af550550550850, 0x174280a),
  (0x401aae5512ae5512ae5512ae551551551aae, 0xaaae200000015),
  (0x403aac5512ac5512ac5512ac55355380caac, 0x17544005aac400000015),
  (0x403aac5512ac5512ae5512ae551551850aac, 0x162840a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_43 : coresOK P12 645 Cores_43 = true := by decide +kernel

def Cores_44 : List (ℕ × ℕ) := [(0x402aac5522ac5522ac5522ac553553aac00c, 0x340e000eab0003553600000013),
  (0x402aac5522ac5522ac5522ad552552aad012, 0xeab00022ad000d048002552800000017),
  (0x402aac5522ac5522ad5522ad552552aac050, 0x22ac0011548004aad600000019),
  (0x402aad5522ac5522ac5522ac552552aad402, 0x141200055080024020008ab0003aada00000013),
  (0x402aad5522ac5522ac5522ad552552aad412, 0x8ab40024120008ab0004552800000015),
  (0x403aac5522ac5522ac5522ac552552aac800, 0x3552000cab4003aac600000013),
  (0x403aac5532ac5532ac5532ac553553aacaac, 0xaaac200000015),
  (0x406aa85522a85522a85562a9556829aa9016, 0xcab00014160011558001aa9800000015),
  (0x406aa85522a85522a95562a9556829aa8054, 0x22ac000554c0012ad0011558003aa9a0000001b),
  (0x406aa85532a85532a85562a8556829aa8284, 0xe2640a),
  (0x406aa95522a85522a85562a8556829aa9406, 0xd0080012ac000754c004aa9800000013),
  (0x406aa95522a85522a85562a9556829aa9416, 0x4aa4001416000cab0005556800000017),
  (0x407aa85522a85522a85572a8557828aa8828, 0xf5480018280005548005aa8800000019),
  (0x407aa85522a85522a95562a9556828aa8850, 0x162680a),
  (0x407aa85522a85532a85562a8557828aa8888, 0xa2a0003d520012aa0001557800000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_44 : coresOK P12 660 Cores_44 = true := by decide +kernel

def Cores_45 : List (ℕ × ℕ) := [(0x407aa85532a85532a85562a8556828aa8a80, 0xb54c0022a90006aa0004557800000017),
  (0x407aa85532a85532a85572a8557828aa8aa8, 0x1754c005aa8400000015),
  (0x406aa85522a95522ac5522ac552851aa9106, 0x48620a),
  (0x406aa95522a85522ac5522ac552851aa9406, 0x48620a),
  (0x405aa85552a85552a85552aa555aaa015aaa, 0xeaa00022aa000d054002555800000017),
  (0x404aa95542a85542a85562a9556aa9029416, 0x142c0004aa40014140008aa0005556a00000017),
  (0x405aaa5552a85552a85552a8555aaa405aaa, 0xd0140022a8000eaa8001555800000015),
  (0x404aab5542a85542a85542ab554aab414414, 0x145400054500024140004aac0022a80005550001aabe00000017),
  (0x404aab5542a85542a95542aa554aab414444, 0x14aac005454400000015),
  (0x405aaa5552a85552a85552aa555aaa415aaa, 0x52aa000d054002555600000017),
  (0x407aa85572a85572a85572a8557aa8aa8aa8, 0xaaa8200000015),
  (0x40eaa15502a65502ae5502ae85195195140e, 0x14a820a),
  (0x40faa05512a65512ae5512ae850950950aa0, 0x1628a0a),
  (0x40eaa15522a45522ac5522ac851951aa140e, 0x48a20a),
  (0x40eaa15522a55522ac5522ac851950aa150a, 0x68a20a)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_45 : coresOK P12 675 Cores_45 = true := by decide +kernel

def Cores_46 : List (ℕ × ℕ) := [(0x40caa35542a055c2a155c2a28a3aa341c44c, 0x151700052a3400000015),
  (0x40daa25542a055d2a055d2a28a2aa241d8a2, 0x8a8800361d0005074005aa2800000019),
  (0x40daa25552a055c2a055d2a28a2aa241da22, 0x32a2000d074003aa2600000013),
  (0x40daa25552a055d2a055d2a28a2aa241caa0, 0x22a0000d074005aa2600000017),
  (0x40daa25552a055d2a055d2a28a2aa241daa2, 0x32a2000d074003aa2600000013),
  (0x40eaa15562a055e2a055e2a08a1aa1aa140e, 0xd0380022a00005578005aa180000001b),
  (0x40eaa15562a055e2a055e2a18a0aa1aa1416, 0x3aa00008aa400241e0009578001aa1a00000017),
  (0x40faa05572a055f2a055f2a08a0aa0aa0aa0, 0xaaa0200000015),
  (0x40daa05512ac5512ac5532ac95295202caa0, 0x1642a0a),
  (0x40daa25502ad5502ad5502ad95295240d952, 0x8b420a),
  (0x40daa25512ac5512ac5512ac95295240daa2, 0xa8420a),
  (0x40aaa555a2a055a2a055a2a5aa5418aa141a, 0xca8400341a0009568002aa580000001b),
  (0x40baa455b2a055b2a055b2a4aa4419aa0aa4, 0x22a0000d06c005aa4600000017),
  (0x40aaa455a2a055b2a055b2a4aa441baa40a4, 0x52a4000906c00255b600000015),
  (0x40aaa555a2a055a2a055a2a4aa541aaa540a, 0xd0680032a40009568002aa580000001b)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_46 : coresOK P12 690 Cores_46 = true := by decide +kernel

def Cores_47 : List (ℕ × ℕ) := [(0x40aaa555a2a055a2a155a2a4aa541aaa544a, 0x14a9400545a400000015),
  (0x40baa455a2a055a2a055b2a4aa441baa4824, 0x4a900032a1000506c00555b800000017),
  (0x40baa455b2a055b2a055b2a4aa441baa4aa4, 0x32a4000d06c003aa4600000013),
  (0x40daa255d2a055d2a055d2a0aa2aa240daa2, 0x141d000553400240d0008a80004aa2a0000001b),
  (0x40faa055f2a055f2a055f2a0aa0aa0aa0aa0, 0x903c008aa0400000011),
  (0x404abb5402bb5402bb54454454483b544544, 0xad44200000015),
  (0x405aba5402ba5402ba54554554583a54583a, 0xf50000183a0012ae8001545800000015),
  (0x405aba5402ba5412ba54454554583a54589a, 0x30ba000aae8005545600000019),
  (0x405aba5402ba5412ba54554554583a5458ba, 0x17504005aba400000015),
  (0x405aba5412ba5412ba54454454583a545a8a, 0xad45200000015),
  (0x405aba5412ba5412ba54454554583a545a9a, 0x14af8005545400000015),
  (0x405aba5412ba5412ba54554554583a545aba, 0x17504005aba400000015),
  (0x406ab85402b95402b9546546546839839146, 0xf5000018390005518004ab9800000015),
  (0x406ab95402b85402b9546546546839839446, 0x2d4000090e00018390011518002ab9a0000001d),
  (0x407ab85412b85412b8546546547838838a88, 0x75040030390006ae0004547800000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_47 : coresOK P12 705 Cores_47 = true := by decide +kernel

def Cores_48 : List (ℕ × ℕ) := [(0x407ab85412b85412b8546547547838838a98, 0x60e0003d410005504005ab8800000019),
  (0x407ab85412b85412b8547547547838838ab8, 0x60e0003d410005504005ab8800000019),
  (0x406ab85402b95422b9544546546839899146, 0x30b90015518002ab9600000019),
  (0x406ab95402b85422b9544546546839899446, 0x30b90015518002ab9600000019),
  (0x407ab85402b85432b85455465478388988a8, 0x340700162e0002547600000017),
  (0x407ab85412b85422b8544547547838898a18, 0x14070007500003418000eae0003547a00000019),
  (0x407ab85412b85422b8545546547838898a28, 0x123a00042e4002d40000eae0003547a00000017),
  (0x407ab85412b85422b8545547547838898a38, 0xa2e0003d410012ae0001547800000017),
  (0x407ab85412b85432b8545546546838898aa0, 0x30b9000501c001d40000aae0004547a0000001b),
  (0x407ab85412b85432b8545546547838898aa8, 0x75140032b8000b504001d4300062e0003547c0000001b),
  (0x407ab85412b85432b8545547547838898ab8, 0x22b800042e0002d410006ae0004547a00000017),
  (0x406ab85402b85422b95465465468398b9046, 0x151180058b9400000015),
  (0x406ab85402b95422b95465465468388b9142, 0x17508005ab9400000015),
  (0x406ab85402b95422b95465465468398b8144, 0xe2e40012bc0011518002ab980000001b),
  (0x406ab85402b95422b95465465468398b9146, 0x17508005ab9400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_48 : coresOK P12 720 Cores_48 = true := by decide +kernel

def Cores_49 : List (ℕ × ℕ) := [(0x406ab95402b85422b95465465468388b9442, 0x14ae4005542400000015),
  (0x406ab95402b85422b95465465468398b8444, 0x162e4005446400000015),
  (0x406ab95402b85422b95465465468398b9446, 0xa2e40022b900082e400554680000001d),
  (0x407ab85412b85422b85475475478388b8a38, 0x1750c005ab8400000015),
  (0x407ab85412b85432b85465465478388b8a88, 0x82e4002d42000eae0003547800000017),
  (0x407ab85412b85432b85465475478388b8a98, 0x1750c005ab8400000015),
  (0x407ab85412b85432b85475475478388b8ab8, 0x1750c005ab8400000015),
  (0x406ab85422b95422b9544544546839a89146, 0xad46200000015),
  (0x406ab95422b85422b9544544546839a89446, 0x40ec0012b90009118002d460004a34003546c00000019),
  (0x407ab85432b85432b8545545546838a88ab0, 0xad47200000015),
  (0x407ab85432b85432b8545545547838a88ab8, 0xad47200000015),
  (0x406ab85422b85422b9544546546839a99046, 0x91180032bc0011518001ab9800000017),
  (0x406ab85422b95422b9544546546839a98144, 0x32bc0015518002ab9600000019),
  (0x406ab85422b95422b9544546546839a99146, 0x14af4005546400000015),
  (0x406ab95422b85422b8544546546839a99406, 0xcaf00014060004ae0005546800000019)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_49 : coresOK P12 735 Cores_49 = true := by decide +kernel

def Cores_50 : List (ℕ × ℕ) := [(0x406ab95422b85422b9544546546839a98444, 0x91180032bc0011518001ab9800000017),
  (0x406ab95422b85422b9544546546839a99446, 0x14af4005546400000015),
  (0x407ab85422b95422b9544546546838a98940, 0x1626c0a),
  (0x407ab85432b85432b8545546547838a98aa8, 0x14af0005547400000015),
  (0x407ab85432b85432b8545547547838a98ab8, 0x14af0005547400000015),
  (0x406ab85422b85422b9546546546839ab9046, 0x91180032bc0011518001ab9800000017),
  (0x406ab85422b95422b9546546546839ab8144, 0x32bc0015518002ab9600000019),
  (0x406ab95422b85422b8546546546839ab9406, 0xcaf00014060004ae0005546800000019),
  (0x406ab95422b85422b9546546546839ab9446, 0x14af4005546400000015),
  (0x407ab85432b85432b8547547547838ab8ab8, 0x1750c005ab8400000015),
  (0x404ab95402bb5442bb5445445448bb144544, 0xaabb200000015),
  (0x405ab85402ba5452ba5455455458ba1448b8, 0x17510005aba400000015),
  (0x405ab85402ba5452ba5455455458ba1458ba, 0xaaba200000015),
  (0x405ab85412ba5442ba5455455458ba145a3a, 0xaaba200000015),
  (0x405ab85412ba5452ba5455455458ba145aba, 0xaaba200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_50 : coresOK P12 750 Cores_50 = true := by decide +kernel

def Cores_51 : List (ℕ × ℕ) := [(0x404abb5402b95442bb5445445448bb444544, 0x14aec005544400000015),
  (0x405aba5402b85452ba5455455458ba4448b8, 0xd1100020ba000eae8002545800000017),
  (0x405aba5412b85442ba5455455458ba444a38, 0x2445000b5100022b8000aae8002545a00000015),
  (0x405aba5412b85442ba5455455458ba445a3a, 0x14ae8005545400000015),
  (0x405aba5412b85452ba5455455458ba444ab8, 0x18b800042e80044450004ae0004abaa0000001b),
  (0x405aba5412b85452ba5455455458ba445aba, 0x14ae8005545400000015),
  (0x404abb5402bb5442bb5445445448bb544544, 0xaabb200000015),
  (0x405aba5402ba5452ba5455455458ba5458ba, 0xaaba200000015),
  (0x405aba5402bb5442bb5445445448ba544940, 0x1642c0a),
  (0x405aba5412ba5452ba5455455458ba545aba, 0xaaba200000015),
  (0x407ab85412b85462b85475475478b88b8a38, 0xaab8200000015),
  (0x407ab85412b85472b85475475478b88b8ab8, 0xaab8200000015),
  (0x406ab85422b85442b95465465468b9a39046, 0x91180022b80009518004ab9800000015),
  (0x406ab95422b85442b85465465468b9a39406, 0x2406000cae0005546600000017),
  (0x407ab85432b85452b85465475478b8a38a98, 0xaab8200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_51 : coresOK P12 765 Cores_51 = true := by decide +kernel

def Cores_52 : List (ℕ × ℕ) := [(0x407ab85432b85452b85475475478b8a38ab8, 0xaab8200000015),
  (0x406ab95422b85462b85465465468b9ab9406, 0x2406000cae0005546600000017),
  (0x406ab95422b85462b95465465468b8ab9442, 0x2446000b5080022b80009518002ab9a00000015),
  (0x407ab85432b85472b85475475478b8ab8ab8, 0xaab8200000015),
  (0x404ab95442b95442bb544544544abb044544, 0x111100012bb0006ae4003abb800000011),
  (0x405ab85452b85452ba545545545aba045aba, 0x44450004ae0004aba600000011),
  (0x404ab95442bb5442bb544544544ab9140544, 0xaabb200000015),
  (0x404abb5442b95442b9544544544abb404544, 0x2404000cae4005544600000015),
  (0x405aba5442b95442b9544544544aba405942, 0xc6420a),
  (0x405aba5452b85452b8545545545aba405aba, 0x2405000cae0005545600000017),
  (0x404abb5442b85442bb544544544abb444444, 0x12b80011110004abb600000011),
  (0x404abb5442b95442ba544544544abb444504, 0x24040010aec004544600000011),
  (0x404abb5442b95442bb544544544abb444544, 0xd1100032bb0009510002abb800000013),
  (0x405aba5452b85452ba545545545aba445aba, 0xd1140032ba000aae8002545800000013),
  (0x404abb5442bb5442bb544544544abb544544, 0xaabb200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_52 : coresOK P12 780 Cores_52 = true := by decide +kernel

def Cores_53 : List (ℕ × ℕ) := [(0x405aba5442bb5442bb544544544aba544940, 0x1642c0a),
  (0x405aba5452ba5452ba545545545aba545aba, 0xaaba200000015),
  (0x406ab85462b85462b8546546546ab8ab8000, 0x24060016ae0003546600000019),
  (0x407ab85472b85472b8547547547ab8ab8ab8, 0x901c008ab8400000011),
  (0x40cab15402b25442b354c54c8338b314c44c, 0x8acc0028b300082cc00554c80000001d),
  (0x40dab05402b25452b254c54d8328b214d892, 0x240d00162c800254d600000015),
  (0x40dab05412b25442b254c54d8328b214da12, 0xa8c8003d440012ac800154d800000017),
  (0x40dab05412b25442b254d54d8328b214ca30, 0xa8c8003d440012ac800154d800000017),
  (0x40dab05412b25442b254d54d8328b214da32, 0x17514005ab2400000015),
  (0x40dab05412b25452b254c54c8328b214da82, 0xb5100020b3000eac800354d800000017),
  (0x40dab05412b25452b254c54d8328b214ca90, 0xb5100018b000050cc00129c0012ac800254dc0000001f),
  (0x40dab05412b25452b254c54d8328b214da92, 0x17514005ab2400000015),
  (0x40dab05412b25452b254d54d8328b214cab0, 0x1aba000b5140025470004ae0005ab2a0000001b),
  (0x40dab25412b05442b254c54d8328b244da12, 0x8ac8002d420006ac800454d800000017),
  (0x40dab25412b05442b254d54d8328b244ca30, 0x3430000eac800354d600000013)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_53 : coresOK P12 795 Cores_53 = true := by decide +kernel

def Cores_54 : List (ℕ × ℕ) := [(0x40dab25412b05442b254d54d8328b244da32, 0x155140052b2400000015),
  (0x40dab25412b05452b254c54d8328b244da92, 0x95140020b20009134002ab2800000011),
  (0x40dab25412b05452b254d54d8328b244dab2, 0xc2c8002445000aac800354d800000017),
  (0x40eab05422b05442b154e54e8318b1a3104e, 0x80c00024460005538004ab1800000013),
  (0x40eab05422b15442b154e54e8308b1a31146, 0x17518005ab1400000015),
  (0x40eab15422b05442b054e54e8318b1a3140e, 0x243000090180012b00009538003ab1a00000015),
  (0x40eab15422b05442b154e54e8308b1a31446, 0x14ac4005546400000015),
  (0x40fab05432b05452b054e54f8308b0a30a90, 0x1751c005ab0400000015),
  (0x40fab05432b05452b054f54f8308b0a30ab0, 0x1751c005ab0400000015),
  (0x40eab05422b05462b154c54e8318b1a9104e, 0x151380058b1400000015),
  (0x40eab15422b05462b054c54e8318b1a9140e, 0x140e000d0c80012b0000d538003ab1a00000019),
  (0x40eab15422b05462b154c54e8318b0a9144a, 0x162c400544e400000015),
  (0x40fab05432b05472b054d54e8308b0a90aa0, 0x1751c005ab0400000015),
  (0x40eab05422b05462b154e54e8308b1ab1046, 0xc0c80014460009538004ab1800000015),
  (0x40eab15422b05462b054e54e8308b1ab1406, 0x10b00012ac0002546000901800154ea00000017)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_54 : coresOK P12 810 Cores_54 = true := by decide +kernel

def Cores_55 : List (ℕ × ℕ) := [(0x40eab15422b05462b054e54e8318b1ab140e, 0x82c00024060009538003ab1800000015),
  (0x40eab15422b05462b154e54e8318b0ab144a, 0x151380058b1400000015),
  (0x40fab05422b05472b054e54f8308b0ab0890, 0x240f00162c000254f600000015),
  (0x40dab05442b25442b254954d832a9214d832, 0xf5100018320005510005ab2800000019),
  (0x40dab05442b25452b254954c832a9214d8a2, 0x3426000eac800354d600000013),
  (0x40dab05452b25452b254954c832a9214daa2, 0x14ae800554d400000015),
  (0x40dab05442b05452b254c54d832ab204d892, 0x162c800544d400000015),
  (0x40dab05452b05452b254c54c832ab204da82, 0x8ae4002d46000eac800354d80000001b),
  (0x40dab05442b25442b254d54d832ab0149832, 0x60c8002d460009510006ab280000001b),
  (0x40dab05452b25452b254c54c832ab0149a82, 0x3d460016ac800254d600000019),
  (0x40dab05462b05462b054d54d832ab0289832, 0x84e20a),
  (0x40dab05462b15462b154c54c832ab0289942, 0xc8620a),
  (0x40dab25442b05442b054d54d832ab240d832, 0x4434000eac800354d600000019),
  (0x40aab15402b454a2b554a54a8b414a8b5442, 0x91080020b50009528002ab5800000011),
  (0x40bab05412b454a2b454b54b8b414b8b4a34, 0xaab4200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_55 : coresOK P12 825 Cores_55 = true := by decide +kernel

def Cores_56 : List (ℕ × ℕ) := [(0x40bab05412b454b2b454b54b8b414a8b4ab0, 0xaab4200000015),
  (0x40aab05422b45482b554a54a8b514aa3504a, 0x2ab40008ad400244a000a52800254aa00000015),
  (0x40aab05432b45492b454a54a8b414ba34284, 0x155280052b4400000015),
  (0x40aab15422b45482b454a54a8b514aa3540a, 0x240a000cad000554a600000017),
  (0x40aab15422b45482b554a54a8b514aa3544a, 0x14ad400554a400000015),
  (0x40bab05422b55482b554a54a8b414aa34940, 0x1624c0a),
  (0x40bab05432b45492b454a54b8b414ba34a94, 0xaab4200000015),
  (0x40bab45412b054a2b454b54b8b44488b0a30, 0x5ab0000aad000254b600000019),
  (0x40bab45412b054a2b454b54b8b44498b0a34, 0x82c40024490012ad000254b800000015),
  (0x40bab45412b054b2b454b54b8b44498b0ab4, 0x82c00034490012ad000154b800000015),
  (0x40aab55422b05482b554a54a8b5448a3144a, 0x22b1000752000244a0009528001ab5a00000011),
  (0x40aab55422b15482b454a54a8b5448a3150a, 0x344a000cac400354a600000013),
  (0x40bab45432b05492b454a54b8b4448a30a90, 0x1512c005ab0400000015),
  (0x40bab45432b05492b454a54b8b4449a30a94, 0xaac000244b0004ad8001d490006ad000154bc00000011),
  (0x40bab45432b05492b454b54b8b4449a30ab4, 0x912c003ab000075240012b60006ad000154bc00000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_56 : coresOK P12 840 Cores_56 = true := by decide +kernel

def Cores_57 : List (ℕ × ℕ) := [(0x40aab45422b05482b454b54b8b444ba34034, 0x155280052b4400000015),
  (0x40aab45422b05482b554a54a8b544aa3504a, 0x15128005ab5400000015),
  (0x40aab45422b05492b454a54b8b444ba34094, 0x14ad000554a400000015),
  (0x40aab55422b15482b454a54a8b544aa3550a, 0x14ad400554a400000015),
  (0x40bab45432b05492b454a54b8b444ba34a94, 0x14ad000554b400000015),
  (0x40bab45432b05492b454b54b8b444aa34ab0, 0x1512c005ab4400000015),
  (0x40bab45432b05492b454b54b8b444ba34ab4, 0x14ad000554b400000015),
  (0x40aab45422b054a2b554a54a8b5448ab104a, 0x10b00011128004ab5600000011),
  (0x40aab55422b054a2b454a54a8b5448ab140a, 0x544a0008ad0002ab5600000015),
  (0x40aab55422b054a2b554a54a8b4448ab1442, 0x16ad000544a400000015),
  (0x40aab55422b054a2b554a54a8b5448ab144a, 0x10b100111280012b00005528004ab5a00000019),
  (0x40aab55422b154a2b454a54a8b5448ab0508, 0x98200012b0000d528003ab5800000013),
  (0x40bab45432b054b2b454b54b8b4449ab0ab4, 0x10b0001112c004ab4600000011),
  (0x40aab45422b054a2b454b54b8b444bab4034, 0x14ad000554a400000015),
  (0x40aab55422b054a2b554a54a8b444aab5442, 0x22b4000750800244a0009528001ab5a00000011)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_57 : coresOK P12 855 Cores_57 = true := by decide +kernel

def Cores_58 : List (ℕ × ℕ) := [(0x40aab55422b154a2b454a54a8b444aab5502, 0x350a000cad000354a600000013),
  (0x40aab55422b154a2b454a54a8b544aab550a, 0x14ad400554a400000015),
  (0x40bab45432b054b2b454b54b8b444bab4ab4, 0x444b0004ad00010b4000ead000154ba00000013),
  (0x40fab05432b054c2b054f54f8b08b0a30a30, 0xaab0200000015),
  (0x40fab05432b054d2b054e54f8b08b0a30a90, 0xaab0200000015),
  (0x40fab05432b054d2b054f54f8b08b0a30ab0, 0xaab0200000015),
  (0x40eab05422b054e2b054f54f8b08b0ab0030, 0x24320009538005ab0600000015),
  (0x40fab05432b054f2b054f54f8b08b0ab0ab0, 0xaab0200000015),
  (0x40eab15422b45482b454a54a8b1941a3140e, 0x4c820a),
  (0x40fab05432b45492b454a54b8b0940a30a90, 0x164c80a),
  (0x40dab05452b05492b254c54d8b2a3204da92, 0x15134005ab2400000015),
  (0x40dab25452b05492b054c54d8b2a3240da92, 0x240d000cac000554d600000017),
  (0x40dab25452b05492b054d54d8b2a3240dab2, 0x340d0008ac0005ab2600000017),
  (0x40fab05472b054b2b054d54e8b0a30a90aa0, 0xaab0200000015),
  (0x40fab05472b054b2b054d54f8b0a30a90ab0, 0xaab0200000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_58 : coresOK P12 870 Cores_58 = true := by decide +kernel

def Cores_59 : List (ℕ × ℕ) := [(0x40eab05462b054a2b054f54f8b0a30ab0030, 0x14ac000554e400000015),
  (0x40eab15462b054a2b154e54e8b0a30ab1442, 0x15138005ab0400000015),
  (0x40fab05472b054b2b054f54f8b0a30ab0ab0, 0xaab0200000015),
  (0x40cab15442b054c2b154e54e8b0ab1031446, 0x3434000d538003ab1600000013),
  (0x40cab35442b054c2b154c54c8b2ab340c444, 0x444c0008ac00012b1000d530001ab3a0000001b),
  (0x40dab25452b054d2b054d54d8b2ab240dab2, 0x240d000cac000554d600000017),
  (0x40cab35442b154c2b254c54c8b0ab3444504, 0x155100052b3400000015),
  (0x40dab25452b054d2b254d54d8b0ab2445ab2, 0xaac000244d00075140012ba0006ac800154dc00000011),
  (0x40fab05472b054f2b054f54f8b0ab0ab0ab0, 0xaab0200000015),
  (0x40dab25442b95442b9544544942ab240d942, 0xc8420a),
  (0x40aab054a2b054a2b554a54aab504aab504a, 0x544a000aac0003ab5600000017),
  (0x40aab054a2b154a2b454a54aab504aab510a, 0xc0280012b0000d528003ab5800000013),
  (0x40aab154a2b054a2b554a54aab404aab5442, 0x444a0004ac0004ab5600000011),
  (0x40aab154a2b054a2b554a54aab504aab544a, 0x12b00011128004ab5600000011),
  (0x40bab054b2b054b2b454b54bab404bab4ab4, 0x444b0004ac0004ab4600000011)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_59 : coresOK P12 885 Cores_59 = true := by decide +kernel

def Cores_60 : List (ℕ × ℕ) := [(0x40bab454b2b054b2b054b54bab440bab4ab4, 0xd02c0032b0000aad000254b800000017),
  (0x409ab65492b25492b4549549ab6449509ab6, 0x42b60005024004549600000011),
  (0x40bab454b2b054b2b454b54bab444bab4ab4, 0xd12c0032b4000aad000254b800000013),
  (0x40eab054e2b054e2b054e54eab0ab0ab0000, 0x140e001aac000354e600000019),
  (0x40fab054f2b054f2b054f54fab0ab0ab0ab0, 0x903c008ab0400000011),
  (0x416aa15422a85542a95568a81568a9a29446, 0x154600051580024aa0009558004aa9a00000017),
  (0x417aa05432a85542a85578a81578a8a28a28, 0xaaa8200000015),
  (0x417aa05432a85552a85568a81578a8a28a88, 0xaaa8200000015),
  (0x414aa25452a85512aa5548aa155a2a45528a, 0x14aa8005555400000015),
  (0x414aa35442a95502aa5548ab154a2b454514, 0x14aac005554400000015),
  (0x415aa25442a85512aa5548aa155a2a45588a, 0x348c000eaa8003555600000013),
  (0x415aa25452a85512aa5548aa155a2a454a88, 0xaaa000245500075500012ab0006aa8001555c00000011),
  (0x415aa25452a85512aa5548aa155a2a455a8a, 0x15154005aaa400000015),
  (0x416aa15462a85522a85548a9156a29a89416, 0x2416000caa0005556600000017),
  (0x414aaa5452a25512a85548aa455a2a51528a, 0x14aa8005555400000015)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_60 : coresOK P12 900 Cores_60 = true := by decide +kernel

def Cores_61 : List (ℕ × ℕ) := [(0x415aaa5452a25512a85558aa454a2a514aa0, 0x12a00004ad0002614000eaa8003555a00000017),
  (0x415aaa5452a05552aa5558aa451aa2454aa8, 0x15154005aaa400000015),
  (0x416aa85462a05572a85578a8453aa0aa80a8, 0x32a8000d158003aa8600000013),
  (0x416aa95462a05562a85568a8452aa1aa9406, 0x16aa0005456400000015),
  (0x416aa95462a15562a85568a8452aa0aa9502, 0x15158005aa8400000015),
  (0x416aa95462a15562a85568a9452aa0aa9512, 0x8ac0002612000d558003aa9800000017),
  (0x415aaa5442a25552a85558a8454aaa5058a2, 0x34a4000eaa8003555600000013),
  (0x41faa05472a055f2a055f8a08a0aa0aa0aa0, 0xaaa0200000015),
  (0x41daa25442a95542a95548a2942aa241d942, 0xca420a),
  (0x41faa054f2a05572a055f8a0a20aa0aa0aa0, 0xaaa0200000015),
  (0x41faa054f2a055f2a055f8a0aa0aa0aa0aa0, 0x903c008aa0400000011),
  (0x41caa35442b85442b8544943943aa341c41c, 0x6ca40a),
  (0x415aa05552a25552a8555aaa055aaa115aaa, 0x8a80002015000eaa8003555800000013),
  (0x414aa35542a05542ab554aa9054aab444454, 0x12a00011150004aab600000011),
  (0x415aa25552a05552aa555aa8055aaa445aaa, 0x12a00011154004aaa600000011)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_61 : coresOK P12 915 Cores_61 = true := by decide +kernel

def Cores_62 : List (ℕ × ℕ) := [(0x414aa25542a05552aa555aaa054aaa4550a2, 0x91500022a2000aaa8003555800000015),
  (0x410aa65512a25582a4559aa60a6459519226, 0x14a98005559400000015),
  (0x41faa055f2a055f2a055faa0aa0aa0aa0aa0, 0x907c008aa0400000011),
  (0x424ad95042db5205248db524524a5b124524, 0xa524200000015),
  (0x425ad85052da5215248da525525a5a125a9a, 0xa525200000015),
  (0x425ad85052da5215258da525525a5a125ada, 0xaada200000015),
  (0x424adb5042db5205248db524524a5b524524, 0x816c008524400000011),
  (0x425ada5052da5215258da525525a5a525ada, 0x285a0008b68007525600000015),
  (0x427ad85072d85235258d8526527a58a98ac8, 0xaad8200000015),
  (0x427ad85072d85235258d8527527a58a98ad8, 0xa527200000015),
  (0x427ad85072d85235278d8527527a58ad8ad8, 0xaad8200000015),
  (0x424adb5042db5245248db524524adb524524, 0x836c008524400000011),
  (0x425ada5052da5255258da525525ada525ada, 0x8368008525400000011),
  (0x426ad85062d85265268d8526526ad8ad8000, 0x16b60005526400000015),
  (0x427ad85072d85275278d8527527ad8ad8ad8, 0x941c0022d8000ab6000252780000000d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_62 : coresOK P12 930 Cores_62 = true := by decide +kernel

def Cores_63 : List (ℕ × ℕ) := [(0x42bad050b2d45235298d452aa5412ba94ac4, 0xaad4200000015),
  (0x422add5222dd522522add522522522add522, 0xcb7400752240000000f),
  (0x423adc5232dc523523adc523523523adcadc, 0xcb7000752340000000f),
  (0x426ad85262d8526526ad8526526ad8ad8000, 0x16b60005526400000015),
  (0x427ad85272d8527527ad8527527ad8ad8ad8, 0xcb6000752740000000f),
  (0x491b6e491491b6e491491b6e491491491b6e, 0x16db800549140000000b),
  (0x492b6c492492b6c492492b6c492492b6c000, 0xab6d200000015),
  (0x493b6c493493b6c493493b6c493493b6cb6c, 0x16db000549340000000b),
  (0x495b68495495b68495495b68495b68000b68, 0x16da0005495400000015),
  (0x497b68497497b68497497b68497b68b68b68, 0x16da000549740000000b)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem okCores_63 : coresOK P12 945 Cores_63 = true := by decide +kernel

set_option maxRecDepth 100000 in
def Cores : List (ℕ × ℕ) := Cores_0 ++ (Cores_1 ++ (Cores_2 ++ (Cores_3 ++ (Cores_4 ++ (Cores_5 ++ (Cores_6 ++ (Cores_7 ++ (Cores_8 ++ (Cores_9 ++ (Cores_10 ++ (Cores_11 ++ (Cores_12 ++ (Cores_13 ++ (Cores_14 ++ (Cores_15 ++ (Cores_16 ++ (Cores_17 ++ (Cores_18 ++ (Cores_19 ++ (Cores_20 ++ (Cores_21 ++ (Cores_22 ++ (Cores_23 ++ (Cores_24 ++ (Cores_25 ++ (Cores_26 ++ (Cores_27 ++ (Cores_28 ++ (Cores_29 ++ (Cores_30 ++ (Cores_31 ++ (Cores_32 ++ (Cores_33 ++ (Cores_34 ++ (Cores_35 ++ (Cores_36 ++ (Cores_37 ++ (Cores_38 ++ (Cores_39 ++ (Cores_40 ++ (Cores_41 ++ (Cores_42 ++ (Cores_43 ++ (Cores_44 ++ (Cores_45 ++ (Cores_46 ++ (Cores_47 ++ (Cores_48 ++ (Cores_49 ++ (Cores_50 ++ (Cores_51 ++ (Cores_52 ++ (Cores_53 ++ (Cores_54 ++ (Cores_55 ++ (Cores_56 ++ (Cores_57 ++ (Cores_58 ++ (Cores_59 ++ (Cores_60 ++ (Cores_61 ++ (Cores_62 ++ (Cores_63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem cores_ok : coresOK P12 0 Cores = true := coresOK_app (k := 15) okCores_0 rfl (coresOK_app (k := 15) okCores_1 rfl (coresOK_app (k := 15) okCores_2 rfl (coresOK_app (k := 15) okCores_3 rfl (coresOK_app (k := 15) okCores_4 rfl (coresOK_app (k := 15) okCores_5 rfl (coresOK_app (k := 15) okCores_6 rfl (coresOK_app (k := 15) okCores_7 rfl (coresOK_app (k := 15) okCores_8 rfl (coresOK_app (k := 15) okCores_9 rfl (coresOK_app (k := 15) okCores_10 rfl (coresOK_app (k := 15) okCores_11 rfl (coresOK_app (k := 15) okCores_12 rfl (coresOK_app (k := 15) okCores_13 rfl (coresOK_app (k := 15) okCores_14 rfl (coresOK_app (k := 15) okCores_15 rfl (coresOK_app (k := 15) okCores_16 rfl (coresOK_app (k := 15) okCores_17 rfl (coresOK_app (k := 15) okCores_18 rfl (coresOK_app (k := 15) okCores_19 rfl (coresOK_app (k := 15) okCores_20 rfl (coresOK_app (k := 15) okCores_21 rfl (coresOK_app (k := 15) okCores_22 rfl (coresOK_app (k := 15) okCores_23 rfl (coresOK_app (k := 15) okCores_24 rfl (coresOK_app (k := 15) okCores_25 rfl (coresOK_app (k := 15) okCores_26 rfl (coresOK_app (k := 15) okCores_27 rfl (coresOK_app (k := 15) okCores_28 rfl (coresOK_app (k := 15) okCores_29 rfl (coresOK_app (k := 15) okCores_30 rfl (coresOK_app (k := 15) okCores_31 rfl (coresOK_app (k := 15) okCores_32 rfl (coresOK_app (k := 15) okCores_33 rfl (coresOK_app (k := 15) okCores_34 rfl (coresOK_app (k := 15) okCores_35 rfl (coresOK_app (k := 15) okCores_36 rfl (coresOK_app (k := 15) okCores_37 rfl (coresOK_app (k := 15) okCores_38 rfl (coresOK_app (k := 15) okCores_39 rfl (coresOK_app (k := 15) okCores_40 rfl (coresOK_app (k := 15) okCores_41 rfl (coresOK_app (k := 15) okCores_42 rfl (coresOK_app (k := 15) okCores_43 rfl (coresOK_app (k := 15) okCores_44 rfl (coresOK_app (k := 15) okCores_45 rfl (coresOK_app (k := 15) okCores_46 rfl (coresOK_app (k := 15) okCores_47 rfl (coresOK_app (k := 15) okCores_48 rfl (coresOK_app (k := 15) okCores_49 rfl (coresOK_app (k := 15) okCores_50 rfl (coresOK_app (k := 15) okCores_51 rfl (coresOK_app (k := 15) okCores_52 rfl (coresOK_app (k := 15) okCores_53 rfl (coresOK_app (k := 15) okCores_54 rfl (coresOK_app (k := 15) okCores_55 rfl (coresOK_app (k := 15) okCores_56 rfl (coresOK_app (k := 15) okCores_57 rfl (coresOK_app (k := 15) okCores_58 rfl (coresOK_app (k := 15) okCores_59 rfl (coresOK_app (k := 15) okCores_60 rfl (coresOK_app (k := 15) okCores_61 rfl (coresOK_app (k := 15) okCores_62 rfl (okCores_63)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
theorem cores_len : Cores.length = 955 := by decide +kernel

end TFClass

namespace TFClass

lemma wsum_add (ws : List (ℕ × ℕ)) (f g : ℕ → ℕ) :
    wsum ws (fun c => f c + g c) = wsum ws f + wsum ws g := by
  unfold wsum; induction ws with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma wsum_mul (ws : List (ℕ × ℕ)) (k : ℕ) (f : ℕ → ℕ) :
    wsum ws (fun c => k * f c) = k * wsum ws f := by
  unfold wsum; induction ws with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma wsum_fsum (ws : List (ℕ × ℕ)) (f : Fin 12 → ℕ → ℕ) :
    wsum ws (fun c => ∑ u, f u c) = ∑ u, wsum ws (f u) := by
  unfold wsum; induction ws with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.mul_sum, Finset.sum_add_distrib]

def cutCost (s col : Fin 12 → Bool) : ℕ :=
  min (1 + ∑ i, if s i = true ∧ col i = false then 1 else 0)
      (∑ i, if s i = true ∧ col i = true then 1 else 0)

theorem config12 (A : Gr 12) (hA : Good A) (hE : 56 ≤ ecount A)
    (col0 : Fin 12 → Bool) (hcol0 : ∀ i j, A i j = true → col0 i ≠ col0 j)
    (s : Fin 12 → Fin 12 → Bool) (ind : ∀ u i j, s u i = true → s u j = true → A i j = false)
    (cap : (∑ u, ∑ i, if s u i = true then 1 else 0) ≤ 53) :
    ∃ col : Fin 12 → Bool, monoO A col + 2 * ∑ u, cutCost (s u) col ≤ 51 := by
  obtain ⟨b, ⟨ix, hix, hbix⟩, σ, hσ⟩ := cl12 A hA hE
  obtain ⟨sl, hok⟩ := coresOK_sound P12 Cores 0 cores_ok ix (Nat.zero_le _)
    (by rw [cores_len]; omega)
  rw [← hbix] at hok
  clear hbix
  unfold coreQ at hok
  have fwd : ∀ i j, adjOf 12 b i j = A (σ i) (σ j) := fun i j => (hσ i j).symm
  split at hok
  · unfold DualOK at hok
    obtain ⟨α, hα⟩ : ∃ α, (sl >>> 1) % 65536 = α := ⟨_, rfl⟩
    obtain ⟨μ, hμ⟩ : ∃ μ, (sl >>> 17) % 65536 = μ := ⟨_, rfl⟩
    obtain ⟨ws, hws⟩ : ∃ ws, wsOf sl = ws := ⟨_, rfl⟩
    rw [hα, hμ, hws] at hok
    rw [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hall, hmain⟩ := hok
    -- masks of the neighbourhoods in the labels of the listed graph
    have hm : ∀ u, ∃ m < 2 ^ 12, ∀ i : Fin 12, m.testBit i.val = s u (σ i) :=
      fun u => exists_mask 12 (fun i => s u (σ i))
    choose m hmlt hmbit using hm
    have hgen : ∀ u, m u ∈ gen 12 b 12 0 := by
      intro u
      apply gen_complete 12 b (m u) (hmlt u)
      intro i j hi hj h1 h2
      have := ind u (σ ⟨i, hi⟩) (σ ⟨j, hj⟩) (by rw [← hmbit]; exact h1) (by rw [← hmbit]; exact h2)
      rw [← fwd] at this; exact this
    have per := fun u => decide_eq_true_eq.mp (hall (m u) (hgen u))
    have pcs : (∑ u, pcF 12 (m u)) ≤ 53 := by
      refine le_trans (le_of_eq ?_) cap
      apply Finset.sum_congr rfl; intro u _
      rw [pcF_eq]; unfold popc
      rw [← Equiv.sum_comp σ (fun i => if s u i = true then 1 else 0)]
      apply Finset.sum_congr rfl; intro i _; rw [hmbit]
    have tot : wsum ws (fun c => monoO (adjOf 12 b) (fun i => c.testBit i.val) +
        2 * ∑ u, costN (m u) c) < 52 * (ws.map (·.2)).sum := by
      rw [wsum_add, wsum_mul, wsum_fsum]
      have h1 : (∑ u, wsum ws (costN (m u))) ≤ 12 * α + μ * 53 := by
        calc (∑ u, wsum ws (costN (m u))) ≤ ∑ _u : Fin 12, (α + μ * pcF 12 (m _u)) :=
              Finset.sum_le_sum (fun u _ => per u)
          _ = 12 * α + μ * ∑ u, pcF 12 (m u) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
          _ ≤ 12 * α + μ * 53 := Nat.add_le_add_left (Nat.mul_le_mul_left μ pcs) _
      rw [Nat.mul_comm μ 53] at h1
      omega
    obtain ⟨p, -, hp⟩ := exists_good_weight ws
      (fun c => monoO (adjOf 12 b) (fun i => c.testBit i.val) + 2 * ∑ u, costN (m u) c) 52 tot
    refine ⟨fun i => p.1.testBit (σ.symm i).val, ?_⟩
    have hmono : monoO A (fun i => p.1.testBit (σ.symm i).val) =
        monoO (adjOf 12 b) (fun i => p.1.testBit i.val) := by
      unfold monoO
      rw [← Equiv.sum_comp σ]
      apply Finset.sum_congr rfl; intro i _
      rw [← Equiv.sum_comp σ]
      apply Finset.sum_congr rfl; intro j _
      simp [fwd]
    have hcost : ∀ u, cutCost (s u) (fun i => p.1.testBit (σ.symm i).val) = costN (m u) p.1 := by
      intro u
      unfold cutCost costN
      rw [pcF_diff, pcF_land]
      refine congrArg₂ min (congrArg (1 + ·) ?_) ?_
      · rw [← Equiv.sum_comp σ]
        apply Finset.sum_congr rfl; intro i _; simp [hmbit]
      · rw [← Equiv.sum_comp σ]
        apply Finset.sum_congr rfl; intro i _; simp [hmbit]
    rw [hmono]; simp only [hcost]; omega
  · exfalso
    exact odd_cycle_no_coloring (A := fun i j => A (σ i) (σ j)) b (fun i j => hσ i j)
      (cycOf (sl)) hok (fun i => col0 (σ i)) (fun i j h => hcol0 _ _ h)

end TFClass

namespace TFGlue12

open Finset SimpleGraph TFClass
open scoped Classical

lemma two_mono (G : SimpleGraph (Fin 25)) (S : Finset (Fin 25)) :
    2 * (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card =
      ∑ u, ∑ w, if G.Adj u w ∧ (u ∈ S ↔ w ∈ S) then 1 else 0 := by
  let M : SimpleGraph (Fin 25) := {
    Adj := fun u w => G.Adj u w ∧ (u ∈ S ↔ w ∈ S)
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩ }
  have hM : M.edgeFinset = G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_filter]
      rw [OMA.R_Erdos23_erdos_23_variants_n5_R1.same_mk]
  rw [← hM, ← M.sum_degrees_eq_twice_card_edges]
  apply Finset.sum_congr rfl
  intro u _
  rw [← M.card_neighborFinset_eq_degree, M.neighborFinset_eq_filter, Finset.card_filter]

/-- Ordered edge sums split into the blocks root / neighbours / core. -/
lemma blocks (G : SimpleGraph (Fin 25)) (v : Fin 25)
    (noTri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False)
    (P : Fin 25 → Fin 25 → Prop) [DecidableRel P] (hP : ∀ a b, P a b ↔ P b a) :
    (∑ a, ∑ b, if G.Adj a b ∧ P a b then 1 else 0) =
      2 * (∑ b ∈ G.neighborFinset v, if P v b then 1 else 0) +
      2 * (∑ u ∈ G.neighborFinset v, ∑ x ∈ (insert v (G.neighborFinset v))ᶜ,
        if G.Adj u x ∧ P u x then 1 else 0) +
      ∑ x ∈ (insert v (G.neighborFinset v))ᶜ, ∑ y ∈ (insert v (G.neighborFinset v))ᶜ,
        if G.Adj x y ∧ P x y then 1 else 0 := by
  set N := G.neighborFinset v
  set R := (insert v N)ᶜ
  have vN : v ∉ N := by simp [N]
  have memN : ∀ x, x ∈ N ↔ G.Adj v x := fun x => by simp [N]
  have memR : ∀ x, x ∈ R ↔ x ≠ v ∧ ¬ G.Adj v x := fun x => by simp [R, memN]
  let T : Fin 25 → Fin 25 → ℕ := fun a b => if G.Adj a b ∧ P a b then 1 else 0
  have split : ∀ f : Fin 25 → ℕ, (∑ a, f a) = f v + (∑ a ∈ N, f a) + ∑ a ∈ R, f a := by
    intro f
    rw [← Finset.sum_add_sum_compl (insert v N), Finset.sum_insert vN]
  have zNN : ∀ a ∈ N, ∀ b ∈ N, T a b = 0 := by
    intro a ha b hb
    simp only [T, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
    intro hab; exact absurd (noTri v a b ((memN a).mp ha) hab ((memN b).mp hb)) id
  have zvR : ∀ b ∈ R, T v b = 0 := by
    intro b hb; simp only [T, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
    intro h; exact absurd h ((memR b).mp hb).2
  have zRv : ∀ b ∈ R, T b v = 0 := by
    intro b hb; simp only [T, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
    intro h; exact absurd h.symm ((memR b).mp hb).2
  have zvv : T v v = 0 := by simp [T]
  have hvN : ∀ b ∈ N, T v b = if P v b then 1 else 0 := by
    intro b hb; simp [T, (memN b).mp hb]
  have hNv : ∀ b ∈ N, T b v = if P v b then 1 else 0 := by
    intro b hb; simp [T, ((memN b).mp hb).symm, hP b v]
  change (∑ a, ∑ b, T a b) = _
  rw [split]
  simp only [split (T v), split (fun b => T _ b)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [zvv, Finset.sum_congr rfl hvN, Finset.sum_congr rfl zvR, Finset.sum_congr rfl hNv,
    Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (zNN a ha)), Finset.sum_congr rfl zRv]
  have swap : (∑ a ∈ R, ∑ b ∈ N, T a b) = ∑ u ∈ N, ∑ x ∈ R, T u x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro x _
    simp only [T, G.adj_comm x u, hP x u]
  rw [swap]
  simp only [Finset.sum_const_zero, zero_add, add_zero, T]
  ring

lemma sum_restrict (R : Finset (Fin 25)) (P : Fin 25 → Fin 25 → Prop) [DecidableRel P] :
    (∑ u, ∑ w, if u ∈ R ∧ w ∈ R ∧ P u w then 1 else 0) =
      ∑ u ∈ R, ∑ w ∈ R, if P u w then 1 else 0 := by
  rw [← Finset.sum_subset (Finset.subset_univ R)]
  · apply Finset.sum_congr rfl; intro u hu
    rw [← Finset.sum_subset (Finset.subset_univ R)]
    · apply Finset.sum_congr rfl; intro w hw; simp [hu, hw]
    · intro w _ hw; simp [hw]
  · intro u _ hu; simp [hu]

theorem deg12_cut (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3) (v : Fin 25)
    (deg12 : G.degree v = 12)
    (bip : (G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))).IsBipartite)
    (dense : 28 ≤ (G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))).edgeFinset.card)
    (few : G.edgeFinset.card ≤
      65 + (G.induce (↑((insert v (G.neighborFinset v))ᶜ) : Set (Fin 25))).edgeFinset.card) :
    ∃ S : Finset (Fin 25),
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25 := by
  set N := G.neighborFinset v with hNdef
  set R := (insert v N)ᶜ with hRdef
  have hNc : N.card = 12 := by rw [hNdef, card_neighborFinset_eq_degree, deg12]
  have hR : R.card = 12 := by
    rw [hRdef, Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem (by simp [N]), hNc]
  have memN : ∀ x, x ∈ N ↔ G.Adj v x := fun x => by simp [N]
  have memR : ∀ x, x ∈ R ↔ x ≠ v ∧ ¬ G.Adj v x := fun x => by simp [R, memN]
  have noTri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False := fun a b c h1 h2 h3 =>
    tri {a, b, c} (is3Clique_triple_iff.mpr ⟨h1, h3, h2⟩)
  let e : Fin 12 ≃ {x // x ∈ R} := (R.equivFin.trans (finCongr hR)).symm
  let eN : Fin 12 ≃ {x // x ∈ N} := (N.equivFin.trans (finCongr hNc)).symm
  let A : Gr 12 := fun i j => decide (G.Adj (e i) (e j))
  have hA : Good A := {
    symm := fun i j => by simp [A, G.adj_comm]
    irrefl := fun i => by simp [A]
    tf := fun i j l h1 h2 h3 => noTri _ _ _ (of_decide_eq_true h1) (of_decide_eq_true h2)
      (of_decide_eq_true h3) }
  -- ordered sums over the core
  have coreSum : ∀ (Q : Fin 25 → Fin 25 → Prop) [DecidableRel Q],
      (∑ x ∈ R, ∑ y ∈ R, if Q x y then 1 else 0) =
        ∑ i : Fin 12, ∑ j : Fin 12, if Q (e i) (e j) then 1 else 0 := by
    intro Q _
    rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
  let eS : Fin 12 ≃ (↑R : Set (Fin 25)) := e.trans (Equiv.subtypeEquivRight (fun x => Finset.mem_coe.symm))
  have hH : 2 * (G.induce (↑R : Set (Fin 25))).edgeFinset.card = ecount A := by
    rw [← (G.induce (↑R : Set (Fin 25))).sum_degrees_eq_twice_card_edges]
    unfold ecount
    rw [← Equiv.sum_comp eS]
    apply Finset.sum_congr rfl; intro i _
    rw [← (G.induce (↑R : Set (Fin 25))).card_neighborFinset_eq_degree,
      (G.induce (↑R : Set (Fin 25))).neighborFinset_eq_filter, Finset.card_filter,
      ← Equiv.sum_comp eS]
    apply Finset.sum_congr rfl; intro j _
    simp [A, eS]
  have hE : 56 ≤ ecount A := by omega
  -- the root/neighbour/core decomposition of the ordered edge count
  have hall := blocks G v noTri (fun _ _ => True) (fun _ _ => Iff.rfl)
  simp only [and_true, if_true] at hall
  have hEG : (∑ a, ∑ b, if G.Adj a b then 1 else 0) = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    apply Finset.sum_congr rfl; intro a _
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter]
  have hcore : (∑ x ∈ R, ∑ y ∈ R, if G.Adj x y then 1 else 0) = ecount A := by
    rw [coreSum]; unfold ecount; simp [A]
  rw [hEG, ← hNdef, ← hRdef, hcore] at hall
  simp only [Finset.sum_const, smul_eq_mul, mul_one, hNc] at hall
  set X := ∑ u ∈ N, ∑ x ∈ R, if G.Adj u x then 1 else 0 with hX
  have hX53 : X ≤ 53 := by omega
  let s : Fin 12 → Fin 12 → Bool := fun u i => decide (G.Adj (eN u) (e i))
  have ind : ∀ u i j, s u i = true → s u j = true → A i j = false := by
    intro u i j hi hj
    by_contra h
    have h' : G.Adj (e i) (e j) := by simpa [A] using h
    exact noTri _ _ _ (of_decide_eq_true hi) h' (of_decide_eq_true hj)
  have sumN : ∀ F : Fin 25 → ℕ, (∑ u ∈ N, F u) = ∑ u : Fin 12, F (eN u) := by
    intro F; rw [← Finset.sum_coe_sort N, ← Equiv.sum_comp eN]
  have sumR : ∀ F : Fin 25 → ℕ, (∑ x ∈ R, F x) = ∑ i : Fin 12, F (e i) := by
    intro F; rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
  have cap : (∑ u, ∑ i, if s u i = true then 1 else 0) ≤ 53 := by
    refine le_trans (le_of_eq ?_) hX53
    rw [hX, sumN]; apply Finset.sum_congr rfl; intro u _; rw [sumR]
    apply Finset.sum_congr rfl; intro i _; simp [s]
  obtain ⟨C⟩ := bip
  let col0 : Fin 12 → Bool := fun i => C (eS i) == 0
  have hcol0 : ∀ i j, A i j = true → col0 i ≠ col0 j := by
    intro i j hij heq
    have hadj : (G.induce (↑R : Set (Fin 25))).Adj (eS i) (eS j) := by simpa [A, eS] using hij
    have hne := C.valid hadj
    apply hne
    simp only [col0] at heq
    revert heq
    generalize C (eS i) = a; generalize C (eS j) = b
    revert a b; decide
  obtain ⟨col, hcol⟩ := config12 A hA hE col0 hcol0 s ind cap
  -- the cut: core by `col`, root on side `false`, each neighbour on its cheaper side
  let cT : Fin 12 → ℕ := fun u => ∑ i, if s u i = true ∧ col i = true then 1 else 0
  let cF : Fin 12 → ℕ := fun u => ∑ i, if s u i = true ∧ col i = false then 1 else 0
  let f : Fin 25 → Bool := fun x =>
    if hx : x ∈ R then col (e.symm ⟨x, hx⟩)
    else if hn : x ∈ N then decide (cT (eN.symm ⟨x, hn⟩) < 1 + cF (eN.symm ⟨x, hn⟩)) else false
  have fR : ∀ i, f (e i) = col i := by
    intro i; simp [f, (e i).2]
  have fN : ∀ u, f (eN u) = decide (cT u < 1 + cF u) := by
    intro u
    have hn : (eN u : Fin 25) ∈ N := (eN u).2
    have hr : (eN u : Fin 25) ∉ R := by
      rw [memR]; intro h; exact h.2 ((memN _).mp hn)
    simp [f, hr, hn]
  have fv : f v = false := by
    have hr : v ∉ R := by rw [memR]; simp
    have hn : v ∉ N := by simp [N]
    simp [f, hr, hn]
  have hmono := blocks G v noTri (fun a b => f a = f b) (fun a b => eq_comm)
  rw [← hNdef, ← hRdef] at hmono
  have inner : ∀ u : Fin 12, (∑ x ∈ R, if G.Adj (eN u) x ∧ f (eN u) = f x then 1 else 0) =
      ∑ i, if s u i = true ∧ col i = f (eN u) then 1 else 0 := by
    intro u; rw [sumR]; apply Finset.sum_congr rfl; intro i _
    simp only [s, fR, decide_eq_true_eq, eq_comm (a := f (eN u))]
  have per : ∀ u : Fin 12, (if f v = f (eN u) then 1 else 0) +
      (∑ x ∈ R, if G.Adj (eN u) x ∧ f (eN u) = f x then 1 else 0) = cutCost (s u) col := by
    intro u
    rw [inner, fv, fN]
    unfold cutCost
    by_cases hlt : cT u < 1 + cF u
    · rw [decide_eq_true hlt, min_eq_right (le_of_lt hlt)]; simp [cT]
    · rw [decide_eq_false hlt, min_eq_left (not_lt.mp hlt)]; simp [cF]
  have hm : (∑ x ∈ R, ∑ y ∈ R, if G.Adj x y ∧ f x = f y then 1 else 0) = monoO A col := by
    rw [coreSum]; unfold monoO
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    simp [A, fR]
  have total : (∑ a, ∑ b, if G.Adj a b ∧ f a = f b then 1 else 0) =
      monoO A col + 2 * ∑ u, cutCost (s u) col := by
    rw [hmono, hm, sumN, sumN, ← Finset.sum_congr rfl (fun u _ => per u), Finset.sum_add_distrib]
    ring
  refine ⟨univ.filter (fun u => f u = true), ?_⟩
  have h2 := two_mono G (univ.filter (fun u => f u = true))
  have same : (∑ u, ∑ w, if G.Adj u w ∧ (u ∈ univ.filter (fun u => f u = true) ↔
      w ∈ univ.filter (fun u => f u = true)) then 1 else 0) =
      ∑ u, ∑ w, if G.Adj u w ∧ f u = f w then 1 else 0 := by
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro w _
    rcases Bool.eq_false_or_eq_true (f u) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (f w) with h2 | h2 <;> simp [h1, h2]
  omega

end TFGlue12

theorem OMA.solution : OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1_H1_R1.H2 := by
  intro G inst tri common v hv H bip dense few
  obtain ⟨S, hS⟩ := TFGlue12.deg12_cut G tri v (by convert hv) (by convert bip) (by convert dense)
    (by convert few)
  exact ⟨S, by convert hS using 3; ext e; simp only [SimpleGraph.mem_edgeFinset]⟩
