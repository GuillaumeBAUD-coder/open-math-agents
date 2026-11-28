import OMAStatements.S_oeis_a229600
import Mathlib

/-!
# A229600: proof of the closed form and g.f.

Values introduced in row major order: with u = the number of values used so far, a row σ is
admissible iff σ 0 ≤ u and σ 1 ≤ u' (u' = u + 1 if σ 0 = u, else u), and u is updated the same way.
So the arrays are counted by a transfer recursion on the state (u, previous row, remaining
mistakes). Every state count is D G = (α + β m + γ m^2) 3^m + (terms at m = 0, 1, 2), with integer
tables checked by `decide` against the transfer step; the start state gives
243 a(n) = (32 n^2 + 31 n - 30) 3^n for n ≥ 3.
-/

open OMA.S_oeis_a229600

namespace OMA.P_a229600

open Finset

abbrev Row := Fin 2 → Fin 3

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

def loc (σ : Row) : ℕ := if σ 0 = σ 1 then 1 else 0
def pair (ρ σ : Row) : ℕ := (if ρ 0 = σ 0 then 1 else 0) + (if ρ 1 = σ 1 then 1 else 0)

def mG {n : ℕ} (A : Fin n → Row) : ℕ :=
  (∑ r ∈ range n, loc (Aext A r)) + ∑ r ∈ range (n - 1), pair (Aext A r) (Aext A (r + 1))

lemma mist_eq {n : ℕ} (A : Fin n → Row) : mistakes n A = mG A := by
  unfold mistakes mG
  rw [Finset.sum_range, Finset.sum_range]
  simp only [Aext_fin A]
  rfl

lemma mG_cons {m : ℕ} (σ : Row) (B : Fin m → Row) :
    mG (Fin.cons σ B : Fin (m + 1) → Row) = loc σ + (if 0 < m then pair σ (Aext B 0) else 0) + mG B := by
  unfold mG
  rcases m with _ | k
  · simp [Aext_cons0]
  · simp only [Finset.sum_range_succ', Aext_cons0, Aext_cons_succ, show k + 1 + 1 - 1 = k + 1 by omega,
      show k + 1 - 1 = k by omega, if_pos (Nat.succ_pos k)]
    ring

def fl {n : ℕ} (A : Fin n → Row) (i : ℕ) : ℕ := (Aext A (i / 2) ⟨i % 2, Nat.mod_lt _ (by norm_num)⟩).val

def RGN (u N : ℕ) (s : ℕ → ℕ) : Prop := ∀ i < N, ∀ v < s i, v < u ∨ ∃ j < i, s j = v

lemma fl_eq {n : ℕ} (A : Fin n → Row) (i : ℕ) (hi : i < 2 * n) (p1 : i / 2 < n) (p2 : i % 2 < 2) :
    (A ⟨i / 2, p1⟩ ⟨i % 2, p2⟩).val = fl A i := by
  simp [fl, Aext, p1]

lemma rm_iff {n : ℕ} (A : Fin n → Row) : isRowMajor n A ↔ RGN 0 (2 * n) (fl A) := by
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
    fl (Fin.cons σ B : Fin (m + 1) → Row) (i + 2) = fl B i := by
  unfold fl
  have e1 : (i + 2) / 2 = i / 2 + 1 := by omega
  have e2 : (⟨(i + 2) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = ⟨i % 2, Nat.mod_lt _ (by norm_num)⟩ :=
    Fin.ext (by simp only; omega)
  rw [e1, e2, Aext_cons_succ]

def st (u : ℕ) (x : Fin 3) : ℕ := if x.val = u then u + 1 else u
def okR (u : ℕ) (σ : Row) : Prop := (σ 0).val ≤ u ∧ (σ 1).val ≤ st u (σ 0)
def nx (u : ℕ) (σ : Row) : ℕ := st (st u (σ 0)) (σ 1)

instance (u : ℕ) (σ : Row) : Decidable (okR u σ) := by unfold okR; infer_instance

lemma rm_cons {m : ℕ} (u : ℕ) (σ : Row) (B : Fin m → Row) :
    RGN u (2 * (m + 1)) (fl (Fin.cons σ B : Fin (m + 1) → Row)) ↔ okR u σ ∧ RGN (nx u σ) (2 * m) (fl B) := by
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, RGN_succ, RGN_succ]
  have f0 : fl (Fin.cons σ B : Fin (m + 1) → Row) 0 = (σ 0).val := by simp [fl, Aext]
  have f1 : fl (Fin.cons σ B : Fin (m + 1) → Row) (0 + 1) = (σ 1).val := by simp [fl, Aext]
  simp only [f0, f1, fl_cons_ss, okR, nx, st, and_assoc]
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

def G (m u : ℕ) (p : Option Row) (c : ℕ) : ℕ := cntF m (fun B => RGN u (2 * m) (fl B) ∧ Mx p B = c)

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
  have hR : ∀ B : Fin 0 → Row, RGN u (2 * 0) (fl B) := fun B i hi => by omega
  have hM : ∀ B : Fin 0 → Row, Mx p B = 0 := fun B => by simp [Mx, mG]
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

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = G n 0 none 2 := by
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


def dec (k : Fin 9) : Row := ![⟨k.val % 3, by omega⟩, ⟨k.val / 3 % 3, by omega⟩]

def encR : Row ≃ Fin 9 where
  toFun σ := ⟨(σ 0).val + 3 * (σ 1).val, by omega⟩
  invFun := dec
  left_inv := by decide
  right_inv := by decide

lemma sumR (g : Row → ℤ) : ∑ σ : Row, g σ = ∑ k : Fin 9, g (dec k) := by
  rw [← encR.symm.sum_comp]
  rfl

def decO (p : ℕ) : Option Row := if h : p < 9 then some (dec ⟨p, h⟩) else none

def TA0 : List ℤ := [0, 81, -63, 81, -63, -30, 81, -63, -30, 0, 0, 108, 0, 108, -36, 0, 108, -36, 0, 81, -36, 81, -36, -30, 81, -36, -30, 81, -36, -30, 81, 153, -129, 81, 18, 42, 162, 9, -96, 162, -126, 48, 0, 270, -162, 162, -18, -96, 81, 153, -102, 81, 45, 42, 162, 36, -96, 243, -108, -90, 162, 306, -258, 243, 27, -54, 243, 27, -54, 243, 27, -54, 162, 306, -258, 243, 27, -54, 243, 27, -54, 243, 27, -54, 162, 306, -258, 486, -216, -180, 162, 306, -258, 243, 27, -54, 243, 27, -54, 243, 27, -54, 162, 306, -258, 243, 27, -54, 243, 27, -54, 243, 27, -54, 162, 306, -258, 486, -216, -180]
def TA1 : List ℤ := [0, 0, 72, 0, 72, 7, 0, 72, 7, 0, 0, 0, 0, 0, 96, 0, 0, 96, 0, 0, 72, 0, 72, 31, 0, 72, 31, 0, 72, 31, 0, 72, 199, 0, 72, 79, 0, 144, 134, 0, 144, 14, 0, 0, 240, 0, 144, 110, 0, 72, 199, 0, 72, 103, 0, 144, 158, 0, 216, 93, 0, 144, 398, 0, 216, 213, 0, 216, 213, 0, 216, 213, 0, 144, 398, 0, 216, 213, 0, 216, 213, 0, 216, 213, 0, 144, 398, 0, 432, 186, 0, 144, 398, 0, 216, 213, 0, 216, 213, 0, 216, 213, 0, 144, 398, 0, 216, 213, 0, 216, 213, 0, 216, 213, 0, 144, 398, 0, 432, 186]
def TA2 : List ℤ := [0, 0, 0, 0, 0, 32, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 32, 0, 0, 32, 0, 0, 32, 0, 0, 32, 0, 0, 64, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 0, 32, 0, 0, 32, 0, 0, 64, 0, 0, 96, 0, 0, 64, 0, 0, 96, 0, 0, 96, 0, 0, 96, 0, 0, 64, 0, 0, 96, 0, 0, 96, 0, 0, 96, 0, 0, 64, 0, 0, 192, 0, 0, 64, 0, 0, 96, 0, 0, 96, 0, 0, 96, 0, 0, 64, 0, 0, 96, 0, 0, 96, 0, 0, 96, 0, 0, 64, 0, 0, 192]
def TD0 : List ℤ := [243, -81, 63, 162, 63, 30, 162, 63, 30, 243, 0, -108, 243, -108, 36, 243, -108, 36, 243, -81, 36, 162, 36, 30, 162, 36, 30, 162, 36, 30, 162, -153, 129, 162, -18, -42, 81, -9, 96, 81, 126, -48, 243, -270, 162, 81, 18, 96, 162, -153, 102, 162, -45, -42, 81, -36, 96, 0, 108, 90, 81, -306, 258, 0, -27, 54, 0, -27, 54, 0, -27, 54, 81, -306, 258, 0, -27, 54, 0, -27, 54, 0, -27, 54, 81, -306, 258, -243, 216, 180, 81, -306, 258, 0, -27, 54, 0, -27, 54, 0, -27, 54, 81, -306, 258, 0, -27, 54, 0, -27, 54, 0, -27, 54, 81, -306, 258, -243, 216, 180]
def TD1 : List ℤ := [0, 0, -27, 0, -27, 216, 0, -27, 216, 0, 0, 162, 0, 162, -180, 0, 162, -180, 0, 0, 135, 0, 135, -99, 0, 135, -99, 0, 135, -99, 0, 54, -306, 0, -27, 270, 0, 27, -63, 0, -54, 351, 0, 162, -234, 0, 108, 9, 0, 54, -144, 0, 135, -45, 0, 189, -378, 0, 162, -297, 0, 108, -612, 0, 0, -36, 0, 0, -36, 0, 0, -36, 0, 108, -612, 0, 0, -36, 0, 0, -36, 0, 0, -36, 0, 108, -612, 0, 81, -594, 0, 108, -612, 0, 0, -36, 0, 0, -36, 0, 0, -36, 0, 108, -612, 0, 0, -36, 0, 0, -36, 0, 0, -36, 0, 108, -612, 0, 81, -594]
def TD2 : List ℤ := [0, 0, 0, 0, 0, -36, 0, 0, -36, 0, 0, 0, 0, 0, 54, 0, 0, 54, 0, 0, 0, 0, 0, 18, 0, 0, 18, 0, 0, 18, 0, 0, 72, 0, 0, -36, 0, 0, 36, 0, 0, -72, 0, 0, 54, 0, 0, -18, 0, 0, 72, 0, 0, 18, 0, 0, 90, 0, 0, 54, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 108, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 108]

def tk (u p c : ℕ) : ℕ := u * 30 + p * 3 + c

def CA0 (u p c : ℕ) : ℤ := (TA0).getD (tk u p c) 0
def CA1 (u p c : ℕ) : ℤ := (TA1).getD (tk u p c) 0
def CA2 (u p c : ℕ) : ℤ := (TA2).getD (tk u p c) 0
def CD0 (u p c : ℕ) : ℤ := (TD0).getD (tk u p c) 0
def CD1 (u p c : ℕ) : ℤ := (TD1).getD (tk u p c) 0
def CD2 (u p c : ℕ) : ℤ := (TD2).getD (tk u p c) 0

def TT (u p c : ℕ) (k : Fin 9) : ℤ :=
  if okR u (dec k) ∧ loc (dec k) + pairO (decO p) (dec k) ≤ c then 1 else 0

def kk (p : ℕ) (k : Fin 9) : ℕ := loc (dec k) + pairO (decO p) (dec k)

lemma coA0 : ∀ u : Fin 4, ∀ p : Fin 10, ∀ c : Fin 3,
    ∑ k : Fin 9, TT u p c k * CA0 (nx u (dec k)) k.val (c - kk p k) = 3 * CA0 u.val p.val c.val + 3 * CA1 u.val p.val c.val + 3 * CA2 u.val p.val c.val := by
  decide
lemma coA1 : ∀ u : Fin 4, ∀ p : Fin 10, ∀ c : Fin 3,
    ∑ k : Fin 9, TT u p c k * CA1 (nx u (dec k)) k.val (c - kk p k) = 3 * CA1 u.val p.val c.val + 6 * CA2 u.val p.val c.val := by
  decide
lemma coA2 : ∀ u : Fin 4, ∀ p : Fin 10, ∀ c : Fin 3,
    ∑ k : Fin 9, TT u p c k * CA2 (nx u (dec k)) k.val (c - kk p k) = 3 * CA2 u.val p.val c.val := by
  decide
lemma coD0 : ∀ u : Fin 4, ∀ p : Fin 10, ∀ c : Fin 3,
    ∑ k : Fin 9, TT u p c k * CD0 (nx u (dec k)) k.val (c - kk p k) = CD1 u.val p.val c.val := by
  decide
lemma coD1 : ∀ u : Fin 4, ∀ p : Fin 10, ∀ c : Fin 3,
    ∑ k : Fin 9, TT u p c k * CD1 (nx u (dec k)) k.val (c - kk p k) = CD2 u.val p.val c.val := by
  decide
lemma coD2 : ∀ u : Fin 4, ∀ p : Fin 10, ∀ c : Fin 3,
    ∑ k : Fin 9, TT u p c k * CD2 (nx u (dec k)) k.val (c - kk p k) = 0 := by
  decide
lemma co_base : ∀ u : Fin 4, ∀ p : Fin 10, ∀ c : Fin 3,
    (if c.val = 0 then (243 : ℤ) else 0) = CA0 u p c + CD0 u p c := by decide

lemma nx_le (u : ℕ) (hu : u ≤ 3) (σ : Row) (h : okR u σ) : nx u σ ≤ 3 := by
  unfold okR at h
  unfold nx st
  have := (σ 0).isLt
  have := (σ 1).isLt
  split_ifs <;> omega

def del (t m : ℕ) : ℤ := if m = t then 1 else 0

def EE (m u p c : ℕ) : ℤ :=
  (CA0 u p c * (m : ℤ) ^ 0 + CA1 u p c * (m : ℤ) ^ 1 + CA2 u p c * (m : ℤ) ^ 2) * 3 ^ m + CD0 u p c * del 0 m + CD1 u p c * del 1 m + CD2 u p c * del 2 m

lemma decO_k (k : Fin 9) : decO k.val = some (dec k) := by simp [decO]

lemma G_closed (m : ℕ) : ∀ u : Fin 4, ∀ p : Fin 10, ∀ c : Fin 3,
    (243 : ℤ) * G m u (decO p) c = EE m u p c := by
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
    have e : ∀ k : Fin 9, (243 : ℤ) * (if okR u (dec k) ∧ loc (dec k) + pairO (decO p) (dec k) ≤ c then
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
    have hs : ∀ k : Fin 9, TT u p c k * EE m (nx u (dec k)) k.val (c - kk p k) =
        (TT u p c k * CA0 (nx u (dec k)) k.val (c - kk p k)) * ((m : ℤ) ^ 0 * 3 ^ m) + (TT u p c k * CA1 (nx u (dec k)) k.val (c - kk p k)) * ((m : ℤ) ^ 1 * 3 ^ m) + (TT u p c k * CA2 (nx u (dec k)) k.val (c - kk p k)) * ((m : ℤ) ^ 2 * 3 ^ m) + (TT u p c k * CD0 (nx u (dec k)) k.val (c - kk p k)) * del 0 m + (TT u p c k * CD1 (nx u (dec k)) k.val (c - kk p k)) * del 1 m + (TT u p c k * CD2 (nx u (dec k)) k.val (c - kk p k)) * del 2 m := by
      intro k; simp only [EE]; ring
    simp only [hs, Finset.sum_add_distrib, ← Finset.sum_mul, coA0, coA1, coA2, coD0, coD1, coD2]
    have d0 : del 0 (m + 1) = 0 := by simp [del]
    have d1 : del 1 (m + 1) = del 0 m := by simp [del]
    have d2 : del 2 (m + 1) = del 1 m := by simp [del]
    simp only [EE, d0, d1, d2]
    push_cast
    ring

lemma start_vals : CA0 0 9 2 = -30 ∧ CA1 0 9 2 = 31 ∧ CA2 0 9 2 = 32 ∧ CD0 0 9 2 = 30 ∧
    CD1 0 9 2 = -99 ∧ CD2 0 9 2 = 18 := by decide

lemma a_form (n : ℕ) (hn : 1 ≤ n) :
    (243 : ℚ) * a n = (-30 + 31 * n + 32 * n ^ 2) * 3 ^ n + 30 * del 0 n - 99 * del 1 n + 18 * del 2 n := by
  have h : (243 : ℤ) * G n 0 (decO 9) 2 = EE n 0 9 2 := G_closed n 0 9 2
  have hd : decO 9 = none := by simp [decO]
  rw [hd, ← a_eq n hn] at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := start_vals
  simp only [Fin.val_zero, hd, EE, e0, e1, e2, e3, e4, e5] at h
  have h' : ((243 * a n : ℤ) : ℚ) = (((-30 + 31 * (n : ℤ) ^ 1 + 32 * (n : ℤ) ^ 2) * 3 ^ n + 30 * del 0 n +
      -99 * del 1 n + 18 * del 2 n : ℤ) : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (by simpa using h)
  push_cast at h'
  rw [h']
  ring

lemma a_big (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = (32 * n ^ 2 + 31 * n - 30) * 3 ^ n / 243 := by
  have := a_form n (by omega)
  simp only [del, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, if_false] at this
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
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - 3 * PowerSeries.X) ^ 3 = PowerSeries.X ^ 2 * (6 - 15 * PowerSeries.X + 13 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) = (3 : ℚ) ^ ((n : ℤ) - 5) * (31 * (n : ℚ) + 32 * (n : ℚ) ^ 2 - 30) := by
  have v0 : (a 0 : ℚ) = 0 := by simp [a]
  have v1 : (a 1 : ℚ) = 0 := by
    have := a_form 1 (by norm_num)
    simp only [del, show (1 : ℕ) ≠ 0 by norm_num, show (1 : ℕ) ≠ 2 by norm_num, if_true, if_false] at this
    push_cast at this
    linarith
  have v2 : (a 2 : ℚ) = 6 := by
    have := a_form 2 (by norm_num)
    simp only [del, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_true, if_false] at this
    push_cast at this
    linarith
  have hb := a_big
  generalize a = f at v0 v1 v2 hb ⊢
  refine ⟨?_, ?_⟩
  · have hL : ∀ S : PowerSeries ℚ, S * (1 - 3 * X) ^ 3 =
        S - 9 * (S * X ^ 1) + 27 * (S * X ^ 2) - 27 * (S * X ^ 3) := fun S => by ring
    rw [hL]
    ext n
    simp only [map_add, map_sub, coeff_mul_X_pow', cnum, coeff_mk]
    rcases lt_or_ge n 6 with hn | hn
    · have v3 := hb 3 (by norm_num)
      have v4 := hb 4 (by norm_num)
      have v5 := hb 5 (by norm_num)
      norm_num at v3 v4 v5
      interval_cases n <;> simp [coeff_X_pow, coeff_X_pow_mul', coeff_X, cnum, cnum0, map_ofNat, v0, v1, v2, v3, v4, v5] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have hR : coeff (m + 6) (X ^ 2 * (6 - 15 * X + 13 * X ^ 2 - 2 * X ^ 3) : PowerSeries ℚ) = 0 := by
        simp [coeff_X_pow, coeff_X_pow_mul', coeff_X, cnum, cnum0]
      rw [hR]
      simp only [show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, if_true]
      rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega,
        hb (m + 6) (by omega), hb (m + 5) (by omega), hb (m + 4) (by omega), hb (m + 3) (by omega)]
      push_cast
      ring
  · intro n hn
    rw [hb n (by omega), zpow_sub₀ (by norm_num : (3 : ℚ) ≠ 0), zpow_natCast]
    ring

end OMA.P_a229600

theorem OMA.solution : type_of% @OMA.S_oeis_a229600.main := OMA.P_a229600.mainP
