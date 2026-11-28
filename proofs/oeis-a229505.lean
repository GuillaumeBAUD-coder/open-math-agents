import OMAStatements.S_oeis_a229505
import Mathlib

/-!
# A229505: proof of the closed form and g.f.

Values introduced in row major order: with u = the number of values used so far, a row σ is
admissible iff each entry is at most the current u, where u increases by one
whenever an entry equals it.
So the arrays are counted by a transfer recursion on the state (u, previous row, remaining
mistakes). Every state count is D G = (α + β m) 6^m + (terms at m = 0, 1), with integer
tables checked by `decide` against the transfer step; the start state gives
27 a(n) = (24 n - 12) 6^n for n ≥ 2.
-/


open OMA.S_oeis_a229505

namespace OMA.P_a229505

open Finset

abbrev Row := Fin 3 → Fin 3

def Aext {n : ℕ} (A : Fin n → Row) (i : ℕ) : Row := if h : i < n then A ⟨i, h⟩ else fun _ => 0

lemma Aext_fin {n : ℕ} (A : Fin n → Row) (r : Fin n) : A r = Aext A r.1 := by simp [Aext]

lemma Aext_cons0 {m : ℕ} (σ : Row) (B : Fin m → Row) :
    Aext (Fin.cons σ B : Fin (m + 1) → Row) 0 = σ := by simp [Aext]

lemma Aext_cons_succ {m : ℕ} (σ : Row) (B : Fin m → Row) (i : ℕ) :
    Aext (Fin.cons σ B : Fin (m + 1) → Row) (i + 1) = Aext B i := by
  unfold Aext
  by_cases h : i < m
  · rw [dif_pos (by omega), dif_pos h]
    exact Fin.cons_succ (α := fun _ => Row) σ B ⟨i, h⟩
  · rw [dif_neg (by omega), dif_neg h]

def loc (σ : Row) : ℕ := 0
def pair (ρ σ : Row) : ℕ := (∑ c : Fin 2, if ρ ⟨c.1, by omega⟩ = σ ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 2, if ρ ⟨c.1 + 1, by omega⟩ = σ ⟨c.1, by omega⟩ then 1 else 0)

def mG {n : ℕ} (A : Fin n → Row) : ℕ :=
  ∑ r ∈ range (n - 1), pair (Aext A r) (Aext A (r + 1))

lemma mist_eq {n : ℕ} (A : Fin n → Row) : mistakes n A = mG A := by
  unfold mistakes mG
  rw [Finset.sum_range]
  simp only [Aext_fin A]
  rfl

lemma mG_cons {m : ℕ} (σ : Row) (B : Fin m → Row) :
    mG (Fin.cons σ B : Fin (m + 1) → Row) = loc σ + (if 0 < m then pair σ (Aext B 0) else 0) + mG B := by
  unfold mG
  rcases m with _ | k
  · simp [Aext_cons0, loc]
  · simp only [Finset.sum_range_succ', Aext_cons0, Aext_cons_succ, show k + 1 + 1 - 1 = k + 1 by omega,
      show k + 1 - 1 = k by omega, if_pos (Nat.succ_pos k), loc]
    ring

def fl {n : ℕ} (A : Fin n → Row) (i : ℕ) : ℕ := (Aext A (i / 3) ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩).val

def RGN (u N : ℕ) (s : ℕ → ℕ) : Prop := ∀ i < N, ∀ v < s i, v < u ∨ ∃ j < i, s j = v

lemma fl_eq {n : ℕ} (A : Fin n → Row) (i : ℕ) (_hi : i < 3 * n) (p1 : i / 3 < n) (p2 : i % 3 < 3) :
    (A ⟨i / 3, p1⟩ ⟨i % 3, p2⟩).val = fl A i := by
  simp [fl, Aext, p1]

lemma rm_iff {n : ℕ} (A : Fin n → Row) : isRowMajor n A ↔ RGN 0 (3 * n) (fl A) := by
  unfold isRowMajor RGN
  constructor
  · intro h i hi v hv
    right
    have := h ⟨i, hi⟩ v (by rw [fl_eq A i hi]; exact hv)
    obtain ⟨j, hj, e⟩ := this
    exact ⟨j.1, hj, by rw [← fl_eq A j.1 j.2]; exact e⟩
  · intro h i v hv
    rw [fl_eq A i.1 i.2] at hv
    rcases h i.1 i.2 v hv with h0 | ⟨j, hj, e⟩
    · omega
    · exact ⟨⟨j, by omega⟩, hj, by rw [fl_eq A j (by omega)]; exact e⟩

lemma RGN_succ (u N : ℕ) (s : ℕ → ℕ) :
    RGN u (N + 1) s ↔ s 0 ≤ u ∧ RGN (if s 0 = u then u + 1 else u) N (fun i => s (i + 1)) := by
  unfold RGN
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc
      rcases h 0 (by omega) u (by omega) with h1 | ⟨j, hj, -⟩
      · omega
      · omega
    · intro i hi v hv
      have h0 : s 0 ≤ u := by
        by_contra hc
        rcases h 0 (by omega) u (by omega) with h1 | ⟨j, hj, -⟩
        · omega
        · omega
      rcases h (i + 1) (by omega) v hv with h1 | ⟨j, hj, e⟩
      · left; split_ifs <;> omega
      · rcases j with _ | j
        · left; split_ifs <;> omega
        · right; exact ⟨j, by omega, e⟩
  · rintro ⟨h0, h⟩ i hi v hv
    rcases i with _ | i
    · left; omega
    · rcases h i (by omega) v hv with h1 | ⟨j, hj, e⟩
      · split_ifs at h1 with hu
        · by_cases hv' : v < u
          · left; exact hv'
          · right; exact ⟨0, by omega, by omega⟩
        · left; exact h1
      · right; exact ⟨j + 1, by omega, e⟩

lemma fl_cons_ss {m : ℕ} (σ : Row) (B : Fin m → Row) (i : ℕ) :
    fl (Fin.cons σ B : Fin (m + 1) → Row) (i + 3) = fl B i := by
  unfold fl
  have e1 : (i + 3) / 3 = i / 3 + 1 := by omega
  have e2 : (⟨(i + 3) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩ :=
    Fin.ext (by simp only; omega)
  rw [e1, e2, Aext_cons_succ]

def st (u : ℕ) (x : Fin 3) : ℕ := if x.val = u then u + 1 else u
def okR (u : ℕ) (σ : Row) : Prop := (σ 0).val ≤ u ∧ (σ 1).val ≤ st u (σ 0) ∧ (σ 2).val ≤ st (st u (σ 0)) (σ 1)
def nx (u : ℕ) (σ : Row) : ℕ := st (st (st u (σ 0)) (σ 1)) (σ 2)

instance (u : ℕ) (σ : Row) : Decidable (okR u σ) := by unfold okR; infer_instance

lemma rm_cons {m : ℕ} (u : ℕ) (σ : Row) (B : Fin m → Row) :
    RGN u (3 * (m + 1)) (fl (Fin.cons σ B : Fin (m + 1) → Row)) ↔ okR u σ ∧ RGN (nx u σ) (3 * m) (fl B) := by
  rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, RGN_succ, RGN_succ, RGN_succ]
  have f0 : fl (Fin.cons σ B : Fin (m + 1) → Row) (0) = (σ 0).val := by simp [fl, Aext]
  have f1 : fl (Fin.cons σ B : Fin (m + 1) → Row) (0 + 1) = (σ 1).val := by simp [fl, Aext]
  have f2 : fl (Fin.cons σ B : Fin (m + 1) → Row) (0 + 1 + 1) = (σ 2).val := by simp [fl, Aext]
  simp only [f0, f1, f2, fl_cons_ss, okR, nx, st, and_assoc]
  exact Iff.rfl

def cntF (m : ℕ) (P : (Fin m → Row) → Prop) [DecidablePred P] : ℕ := ((univ : Finset (Fin m → Row)).filter P).card

lemma cntF_succ (m : ℕ) (P : (Fin (m + 1) → Row) → Prop) [DecidablePred P] :
    cntF (m + 1) P = ∑ σ : Row, cntF m (fun B => P (Fin.cons σ B)) := by
  unfold cntF
  rw [Finset.card_filter, ← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.card_filter]
  rfl

lemma cntF_congr (m : ℕ) (P Q : (Fin m → Row) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ B, P B ↔ Q B) : cntF m P = cntF m Q := by
  unfold cntF; congr 1; ext B; simp [h]

def pairO (p : Option Row) (σ : Row) : ℕ :=
  match p with
  | none => 0
  | some ρ => pair ρ σ

def Mx {m : ℕ} (p : Option Row) (B : Fin m → Row) : ℕ := mG B + (if 0 < m then pairO p (Aext B 0) else 0)

lemma Mx_cons {m : ℕ} (p : Option Row) (σ : Row) (B : Fin m → Row) :
    Mx p (Fin.cons σ B : Fin (m + 1) → Row) = loc σ + pairO p σ + Mx (some σ) B := by
  unfold Mx
  rw [mG_cons, if_pos (Nat.succ_pos m), Aext_cons0]
  simp only [pairO]
  ring

instance (u N : ℕ) (s : ℕ → ℕ) : Decidable (RGN u N s) := by unfold RGN; infer_instance

def G (m u : ℕ) (p : Option Row) (c : ℕ) : ℕ := cntF m (fun B => RGN u (3 * m) (fl B) ∧ Mx p B = c)

lemma G_succ (m u : ℕ) (p : Option Row) (c : ℕ) :
    G (m + 1) u p c = ∑ σ : Row, if okR u σ ∧ loc σ + pairO p σ ≤ c then
      G m (nx u σ) (some σ) (c - (loc σ + pairO p σ)) else 0 := by
  unfold G
  rw [cntF_succ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs with h
  · refine cntF_congr _ _ _ fun B => ?_
    rw [rm_cons, Mx_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨h.1, h2⟩, by omega⟩
  · unfold cntF
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B _
    rw [rm_cons, Mx_cons]
    intro hh
    exact h ⟨hh.1.1, by omega⟩

lemma G_zero (u : ℕ) (p : Option Row) (c : ℕ) : G 0 u p c = if c = 0 then 1 else 0 := by
  unfold G cntF
  have hR : ∀ B : Fin 0 → Row, RGN u (3 * 0) (fl B) := fun B i hi => by omega
  have hM : ∀ B : Fin 0 → Row, Mx p B = 0 := fun B => by simp [Mx, mG, loc]
  split_ifs with hc
  · rw [Finset.card_eq_one]
    refine ⟨fun i => i.elim0, ?_⟩
    ext B
    simp only [mem_filter, mem_univ, true_and, mem_singleton, hR, hM, hc]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _; trivial
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B _
    simp [hM, Ne.symm hc]

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = G n 0 none 1 := by
  unfold a
  rw [if_neg (by omega), Fintype.card_subtype]
  unfold G cntF
  congr 1
  apply Finset.filter_congr
  intro A _
  rw [mist_eq, rm_iff]
  simp only [Mx, pairO]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by simpa using h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h2, h1⟩


def dec (k : Fin 27) : Row := ![⟨k.val / 1 % 3, by omega⟩, ⟨k.val / 3 % 3, by omega⟩, ⟨k.val / 9 % 3, by omega⟩]

def encR : Row ≃ Fin 27 where
  toFun σ := ⟨1 * (σ 0).val + 3 * (σ 1).val + 9 * (σ 2).val, by omega⟩
  invFun := dec
  left_inv := by decide +kernel
  right_inv := by decide +kernel

lemma sumR (g : Row → ℤ) : ∑ σ : Row, g σ = ∑ k : Fin 27, g (dec k) := by
  rw [← encR.symm.sum_comp]
  rfl

def decO (p : ℕ) : Option Row := if h : p < 27 then some (dec ⟨p, h⟩) else none

def TA0 : List (List (List ℤ)) := [[[0, 6], [0, 0], [0, 6], [9, -6], [0, 12], [9, -3], [9, -6], [0, 15], [9, 0], [0, 0], [0, 3], [0, 3], [0, 12], [3, -2], [3, 7], [0, 15], [6, -4], [6, 5], [0, 6], [0, 3], [0, 9], [9, -3], [3, 7], [12, -8], [9, 0], [6, 5], [15, -10], [18, -12]], [[18, -6], [9, 12], [9, 18], [9, 6], [0, 18], [9, 3], [27, -18], [9, 27], [18, 12], [9, 12], [18, -9], [9, 15], [0, 18], [3, 10], [3, 13], [9, 27], [24, -16], [15, 17], [9, 18], [9, 15], [18, -3], [9, 3], [3, 13], [12, 4], [18, 12], [15, 17], [33, -22], [54, -36]], [[36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [108, -72]], [[36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [18, 30], [18, 30], [36, -12], [108, -72]]]
def TA1 : List (List (List ℤ)) := [[[0, 0], [0, 0], [0, 0], [0, 12], [0, 0], [0, 12], [0, 12], [0, 0], [0, 12], [0, 0], [0, 0], [0, 0], [0, 0], [0, 4], [0, 4], [0, 0], [0, 8], [0, 8], [0, 0], [0, 0], [0, 0], [0, 12], [0, 4], [0, 16], [0, 12], [0, 8], [0, 20], [0, 24]], [[0, 24], [0, 12], [0, 12], [0, 12], [0, 0], [0, 12], [0, 36], [0, 12], [0, 24], [0, 12], [0, 24], [0, 12], [0, 0], [0, 4], [0, 4], [0, 12], [0, 32], [0, 20], [0, 12], [0, 12], [0, 24], [0, 12], [0, 4], [0, 16], [0, 24], [0, 20], [0, 44], [0, 72]], [[0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 144]], [[0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 24], [0, 24], [0, 48], [0, 144]]]
def TD0 : List (List (List ℤ)) := [[[27, -6], [27, 0], [27, -6], [18, 6], [27, -12], [18, 3], [18, 6], [27, -15], [18, 0], [27, 0], [27, -3], [27, -3], [27, -12], [24, 2], [24, -7], [27, -15], [21, 4], [21, -5], [27, -6], [27, -3], [27, -9], [18, 3], [24, -7], [15, 8], [18, 0], [21, -5], [12, 10], [9, 12]], [[9, 6], [18, -12], [18, -18], [18, -6], [27, -18], [18, -3], [0, 18], [18, -27], [9, -12], [18, -12], [9, 9], [18, -15], [27, -18], [24, -10], [24, -13], [18, -27], [3, 16], [12, -17], [18, -18], [18, -15], [9, 3], [18, -3], [24, -13], [15, -4], [9, -12], [12, -17], [-6, 22], [-27, 36]], [[-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [-81, 72]], [[-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [9, -30], [9, -30], [-9, 12], [-81, 72]]]
def TD1 : List (List (List ℤ)) := [[[0, 18], [0, 0], [0, 18], [0, -9], [0, 9], [0, 0], [0, -9], [0, 18], [0, 9], [0, 0], [0, 9], [0, 9], [0, 9], [9, 15], [9, 15], [0, 18], [18, -24], [18, -24], [0, 18], [0, 9], [0, 27], [0, 0], [9, 15], [9, 6], [0, 9], [18, -24], [18, -33], [27, -72]], [[0, 0], [0, -9], [0, 9], [0, 27], [0, 27], [0, 18], [0, -27], [0, 9], [0, 0], [0, -9], [0, -9], [0, 0], [0, 27], [9, 51], [9, 33], [0, 9], [18, -42], [18, -33], [0, 9], [0, 0], [0, 9], [0, 18], [9, 33], [9, 42], [0, 0], [18, -33], [18, -51], [54, -216]], [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [81, -432]], [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [81, -432]]]

def tk (u p c : ℕ) : ℕ := u * 56 + p * 2 + c

def CA0 (u p c : ℕ) : ℤ := ((TA0.getD u []).getD p []).getD c 0
def CA1 (u p c : ℕ) : ℤ := ((TA1.getD u []).getD p []).getD c 0
def CD0 (u p c : ℕ) : ℤ := ((TD0.getD u []).getD p []).getD c 0
def CD1 (u p c : ℕ) : ℤ := ((TD1.getD u []).getD p []).getD c 0

def TT (u p c : ℕ) (k : Fin 27) : ℤ :=
  if okR u (dec k) ∧ loc (dec k) + pairO (decO p) (dec k) ≤ c then 1 else 0

def kk (p : ℕ) (k : Fin 27) : ℕ := loc (dec k) + pairO (decO p) (dec k)

lemma coA0 : ∀ u : Fin 4, ∀ p : Fin 28, ∀ c : Fin 2,
    ∑ k : Fin 27, TT u p c k * CA0 (nx u (dec k)) k.val (c - kk p k) = 6 * CA0 u.val p.val c.val + 6 * CA1 u.val p.val c.val := by
  decide +kernel
lemma coA1 : ∀ u : Fin 4, ∀ p : Fin 28, ∀ c : Fin 2,
    ∑ k : Fin 27, TT u p c k * CA1 (nx u (dec k)) k.val (c - kk p k) = 6 * CA1 u.val p.val c.val := by
  decide +kernel
lemma coD0 : ∀ u : Fin 4, ∀ p : Fin 28, ∀ c : Fin 2,
    ∑ k : Fin 27, TT u p c k * CD0 (nx u (dec k)) k.val (c - kk p k) = CD1 u.val p.val c.val := by
  decide +kernel
lemma coD1 : ∀ u : Fin 4, ∀ p : Fin 28, ∀ c : Fin 2,
    ∑ k : Fin 27, TT u p c k * CD1 (nx u (dec k)) k.val (c - kk p k) = 0 := by
  decide +kernel
lemma co_base : ∀ u : Fin 4, ∀ p : Fin 28, ∀ c : Fin 2,
    (if c.val = 0 then (27 : ℤ) else 0) = CA0 u p c + CD0 u p c := by decide +kernel

lemma nx_le (u : ℕ) (hu : u ≤ 3) (σ : Row) (h : okR u σ) : nx u σ ≤ 3 := by
  unfold okR at h
  unfold nx st
  have := (σ 0).isLt
  have := (σ 1).isLt
  have := (σ 2).isLt
  split_ifs <;> omega

def del (t m : ℕ) : ℤ := if m = t then 1 else 0

def EE (m u p c : ℕ) : ℤ :=
  (CA0 u p c * (m : ℤ) ^ 0 + CA1 u p c * (m : ℤ) ^ 1) * 6 ^ m + CD0 u p c * del 0 m + CD1 u p c * del 1 m

lemma decO_k (k : Fin 27) : decO k.val = some (dec k) := by simp [decO]

lemma G_closed (m : ℕ) : ∀ u : Fin 4, ∀ p : Fin 28, ∀ c : Fin 2,
    (27 : ℤ) * G m u (decO p) c = EE m u p c := by
  induction m with
  | zero =>
    intro u p c
    rw [G_zero]
    have := co_base u p c
    simp only [EE, del]
    by_cases hc : (c : ℕ) = 0
    · simp only [hc, if_true] at this ⊢
      push_cast
      simp only [pow_zero, mul_one, if_true, Nat.cast_zero]
      simp
      linarith
    · simp only [hc, if_false] at this ⊢
      push_cast
      simp
      linarith
  | succ m ih =>
    intro u p c
    rw [G_succ]
    push_cast
    rw [Finset.mul_sum, sumR]
    have e : ∀ k : Fin 27, (27 : ℤ) * (if okR u (dec k) ∧ loc (dec k) + pairO (decO p) (dec k) ≤ c then
        (G m (nx u (dec k)) (some (dec k)) (c - (loc (dec k) + pairO (decO p) (dec k))) : ℤ) else 0) =
        TT u p c k * EE m (nx u (dec k)) k.val (c - kk p k) := by
      intro k
      unfold TT kk
      split_ifs with h
      · have hu := nx_le u (by omega) (dec k) h.1
        have := ih ⟨nx u (dec k), by omega⟩ ⟨k.val, by omega⟩ ⟨c - (loc (dec k) + pairO (decO p) (dec k)), by omega⟩
        simp only [decO_k] at this
        rw [this]; ring
      · ring
    simp only [e]
    have hs : ∀ k : Fin 27, TT u p c k * EE m (nx u (dec k)) k.val (c - kk p k) =
        (TT u p c k * CA0 (nx u (dec k)) k.val (c - kk p k)) * ((m : ℤ) ^ 0 * 6 ^ m) + (TT u p c k * CA1 (nx u (dec k)) k.val (c - kk p k)) * ((m : ℤ) ^ 1 * 6 ^ m) + (TT u p c k * CD0 (nx u (dec k)) k.val (c - kk p k)) * del 0 m + (TT u p c k * CD1 (nx u (dec k)) k.val (c - kk p k)) * del 1 m := by
      intro k; simp only [EE]; ring
    simp only [hs, Finset.sum_add_distrib, ← Finset.sum_mul, coA0, coA1, coD0, coD1]
    have d0 : del 0 (m + 1) = 0 := by simp [del]
    have d1 : del 1 (m + 1) = del 0 m := by simp [del]
    simp only [EE, d0, d1]
    push_cast
    ring

lemma start_vals : CA0 0 27 1 = -12 ∧ CA1 0 27 1 = 24 ∧ CD0 0 27 1 = 12 ∧ CD1 0 27 1 = -72 := by
  decide +kernel

lemma a_form (n : ℕ) (hn : 1 ≤ n) :
    (27 : ℚ) * a n = (24 * n - 12) * 6 ^ n + 12 * del 0 n - 72 * del 1 n := by
  have h : (27 : ℤ) * G n 0 (decO 27) 1 = EE n 0 27 1 := G_closed n 0 27 1
  have hd : decO 27 = none := by simp [decO]
  rw [hd, ← a_eq n hn] at h
  obtain ⟨e0, e1, e2, e3⟩ := start_vals
  simp only [EE, e0, e1, e2, e3] at h
  have h' : ((27 * a n : ℤ) : ℚ) = (((-12 + 24 * (n : ℤ) ^ 1) * 6 ^ n + 12 * del 0 n + -72 * del 1 n : ℤ) : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (by simpa using h)
  push_cast at h'
  rw [h']
  ring

lemma a_big (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = (24 * n - 12) * 6 ^ n / 27 := by
  have := a_form n (by omega)
  simp only [del, show n ≠ 0 by omega, show n ≠ 1 by omega, if_false] at this
  push_cast at this
  linarith

lemma cnum (c : ℕ) [c.AtLeastTwo] (p : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n ((no_index (OfNat.ofNat c : PowerSeries ℚ)) * p) =
      (OfNat.ofNat c : ℚ) * PowerSeries.coeff n p := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) c, PowerSeries.coeff_C_mul]

lemma cnum0 (c : ℕ) [c.AtLeastTwo] (n : ℕ) :
    PowerSeries.coeff n (no_index (OfNat.ofNat c : PowerSeries ℚ)) =
      if n = 0 then (OfNat.ofNat c : ℚ) else 0 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) c, PowerSeries.coeff_C]

open PowerSeries in
theorem mainP :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - 6 * PowerSeries.X) ^ 2 = 48 * PowerSeries.X ^ 2 * (1 - 2 * PowerSeries.X) ∧
    ∀ n : ℕ, 1 < n → (a n : ℤ) = 2 ^ (2 + n) * 3 ^ (n - 2) * (2 * (n : ℤ) - 1) := by
  have v0 : (a 0 : ℚ) = 0 := by simp [a]
  have v1 : (a 1 : ℚ) = 0 := by
    have := a_form 1 (by norm_num)
    simp only [del, show (1 : ℕ) ≠ 0 by norm_num, if_true, if_false] at this
    push_cast at this
    linarith
  have hb := a_big
  generalize a = f at v0 v1 hb ⊢
  refine ⟨?_, ?_⟩
  · have hL : ∀ S : PowerSeries ℚ, S * (1 - 6 * X) ^ 2 = S - 12 * (S * X ^ 1) + 36 * (S * X ^ 2) :=
      fun S => by ring
    have hR : (48 * X ^ 2 * (1 - 2 * X) : PowerSeries ℚ) = X ^ 2 * (48 - 96 * X) := by ring
    rw [hL, hR]
    ext n
    simp only [map_add, map_sub, coeff_mul_X_pow', cnum, coeff_mk]
    rcases lt_or_ge n 4 with hn | hn
    · have v2 := hb 2 (by norm_num)
      have v3 := hb 3 (by norm_num)
      norm_num at v2 v3
      interval_cases n <;> simp [coeff_X_pow, coeff_X_pow_mul', coeff_X, cnum, cnum0, map_ofNat, v0, v1, v2, v3] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hR0 : coeff (m + 4) (X ^ 2 * (48 - 96 * X) : PowerSeries ℚ) = 0 := by
        simp [coeff_X_pow, coeff_X_pow_mul', coeff_X, cnum, cnum0]
      rw [hR0]
      simp only [show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, if_true]
      rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
        hb (m + 4) (by omega), hb (m + 3) (by omega), hb (m + 2) (by omega)]
      push_cast
      ring
  · intro n hn
    have h := hb n (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 - 2 = k by omega]
    refine Int.cast_injective (α := ℚ) ?_
    push_cast
    rw [h, show (6 : ℚ) ^ (k + 2) = 36 * (2 ^ k * 3 ^ k) by rw [pow_add, ← mul_pow]; norm_num; ring]
    push_cast
    ring

end OMA.P_a229505

theorem OMA.solution : type_of% @OMA.S_oeis_a229505.main := OMA.P_a229505.mainP
