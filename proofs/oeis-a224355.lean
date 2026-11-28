import OMAStatements.S_oeis_a224355
import Mathlib

/-!
Proof of the empirical formula and Barker's conjectures for OEIS A224355
(Number of 4 X n 0..2 arrays with diagonals and antidiagonals unimodal and rows nondecreasing.).

Outline.
1. Generic part (namespace UG, proved for any number of rows): the array is read column by column.
   A line (row, diagonal or antidiagonal) is unimodal iff it has no valley; appending a column
   keeps every line valley-free iff no line that has already strictly descended rises again at the
   new cell (`UC_snoc`), and the descent flags update locally (`DS_snoc`). The state after a column
   is coded as a natural number (the column in base m plus one flag bit per line ending there), and
   the computable transition `okc`/`dc` is shown to match the semantics (`okc_stS`, `dc_stS`). This
   gives a(n + 1) as a sum of continuation counts `Wc n` over the admissible first columns
   (`count_eq`).
2. Certificate (checked by the kernel, `decide +kernel`): the list of the 358 reachable states,
   their successor lists, a lumping of the states into 74 blocks with equal continuation counts,
   and the block tables up to length 15. From them, the pointwise identity
   Sum_i (-1)^i C(9, i) Wc (n + 9 - i) s = 0 for n >= 4 and every reachable s, hence the
   binomial recurrence for a(n), n >= 14.
3. The recurrence, the polynomial and the generating function follow from the recurrence and
   the computed values a(1), ..., a(16).
-/

namespace UG

open Finset

/-- Cells (i1, j1) and (i2, j2) (row, column) lie on a common line of type t:
0 a row, 1 a diagonal (i - j constant), 2 an antidiagonal (i + j constant). -/
def al (t i1 j1 i2 j2 : ℕ) : Prop :=
  (t = 0 ∧ i1 = i2) ∨ (t = 1 ∧ i1 + j2 = i2 + j1) ∨ (t = 2 ∧ i1 + j1 = i2 + j2)

instance (t i1 j1 i2 j2 : ℕ) : Decidable (al t i1 j1 i2 j2) := by unfold al; infer_instance

/-- The cell (i, j + 1) continues the line of type t through (p, j). -/
def PR (t i p : ℕ) : Prop := (t = 0 ∧ p = i) ∨ (t = 1 ∧ p + 1 = i) ∨ (t = 2 ∧ p = i + 1)

section Sem

variable {R m : ℕ}

/-- No valley along the lines of type t (arrays given by their columns). -/
def UC (t : ℕ) {N : ℕ} (y : Fin N → Fin R → Fin m) : Prop :=
  ∀ j1 j2 j3 : Fin N, ∀ i1 i2 i3 : Fin R, j1 < j2 → j2 < j3 →
    al t i1 j1 i3 j3 → al t i2 j2 i3 j3 → ¬ (y j2 i2 < y j1 i1 ∧ y j2 i2 < y j3 i3)

/-- Rows nondecreasing. -/
def RN {N : ℕ} (y : Fin N → Fin R → Fin m) : Prop :=
  ∀ j1 j2 : Fin N, j1 ≤ j2 → ∀ i, y j1 i ≤ y j2 i

/-- The line of type t through the cell (p, N) of the last column has a strict descent. -/
def DS (t : ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (p : ℕ) : Prop :=
  ∃ j1 j2 : Fin (N + 1), ∃ i1 i2 : Fin R, j1 < j2 ∧ al t i1 j1 p N ∧ al t i2 j2 p N ∧
    y j2 i2 < y j1 i1

instance (t : ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (p : ℕ) : Decidable (DS t y p) := by
  unfold DS; infer_instance

lemma al_last {t p N : ℕ} {i2 : ℕ} (ht : t < 3) (h : al t i2 N p N) : i2 = p := by
  unfold al at h; omega

lemma al_pred {t i1 j1 i N : ℕ} (ht : t < 3) (hj : j1 ≤ N) (h : al t i1 j1 i (N + 1)) :
    ∃ p, PR t i p ∧ al t i1 j1 p N := by
  unfold al at h; unfold PR al
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨i, by omega, by omega⟩
  · exact ⟨i - 1, by omega, by omega⟩
  · exact ⟨i + 1, by omega, by omega⟩

lemma al_pred_bound {t i1 j1 i N p R : ℕ} (hi1 : i1 < R) (hi : i < R) (hj : j1 ≤ N)
    (hp : PR t i p) (h : al t i1 j1 p N) : p < R := by
  unfold PR at hp; unfold al at h; omega

lemma al_succ {t i1 j1 i N p : ℕ} (hp : PR t i p) (h : al t i1 j1 p N) : al t i1 j1 i (N + 1) := by
  unfold PR at hp; unfold al at h ⊢; omega

lemma al_self_succ {t i N p : ℕ} (hp : PR t i p) : al t p N i (N + 1) := by
  unfold PR at hp; unfold al; omega

lemma al_refl (t i N : ℕ) (ht : t < 3) : al t i N i N := by unfold al; omega

theorem UC_snoc (t : ℕ) (ht : t < 3) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) :
    UC t (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) ↔
      UC t y ∧ ∀ i p : Fin R, PR t i p → ¬ (DS t y p ∧ y (Fin.last N) p < c i) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
      have := h j1.castSucc j2.castSucc j3.castSucc i1 i2 i3 (by simpa using h12)
        (by simpa using h23) (by simpa using a1) (by simpa using a2)
      simpa using this
    · rintro i p hp ⟨⟨j1, j2, i1, i2, h12, a1, a2, hv⟩, hc⟩
      by_cases hj2 : (j2 : ℕ) = N
      · have hi2 : (i2 : ℕ) = p := al_last ht (hj2 ▸ a2)
        have e2 : j2 = Fin.last N := Fin.ext hj2
        have e3 : i2 = p := Fin.ext hi2
        subst e2 e3
        apply h j1.castSucc (Fin.last N).castSucc (Fin.last (N + 1)) i1 i2 i
          (Fin.castSucc_lt_castSucc_iff.2 h12) (Fin.castSucc_lt_last _) (by simpa using al_succ hp a1)
          (by simpa using al_self_succ (N := N) hp)
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact ⟨hv, hc⟩
      · have hj2' : (j2 : ℕ) < N := by have := j2.isLt; omega
        by_cases hlt : y (Fin.last N) p < y j2 i2
        · apply h j2.castSucc (Fin.last N).castSucc (Fin.last (N + 1)) i2 p i
            (by rw [Fin.lt_iff_val_lt_val]; simp only [Fin.coe_castSucc, Fin.val_last]; omega) (Fin.castSucc_lt_last _) (by simpa using al_succ hp a2)
            (by simpa using al_self_succ (N := N) hp)
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          exact ⟨hlt, hc⟩
        · push_neg at hlt
          apply h j1.castSucc j2.castSucc (Fin.last (N + 1)) i1 i2 i
            (Fin.castSucc_lt_castSucc_iff.2 h12) (Fin.castSucc_lt_last _) (by simpa using al_succ hp a1)
            (by simpa using al_succ hp a2)
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          exact ⟨hv, lt_of_le_of_lt hlt hc⟩
  · rintro ⟨h, hn⟩ j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    by_cases hj3 : (j3 : ℕ) = N + 1
    · have e3 : j3 = Fin.last (N + 1) := Fin.ext hj3
      subst e3
      have k12 : (j1 : ℕ) < j2 := h12
      have k23 : (j2 : ℕ) < N + 1 := h23
      have hj1 : (j1 : ℕ) ≤ N := by omega
      have hj2 : (j2 : ℕ) ≤ N := by omega
      obtain ⟨p, hp, ap1⟩ := al_pred ht hj1 (by simpa using a1)
      obtain ⟨p', hp', ap2⟩ := al_pred ht hj2 (by simpa using a2)
      have hpp : p' = p := by unfold PR at hp hp'; omega
      subst hpp
      have hpR : p' < R := al_pred_bound i1.isLt i3.isLt hj1 hp ap1
      let j1' : Fin (N + 1) := ⟨j1, by omega⟩
      let j2' : Fin (N + 1) := ⟨j2, by omega⟩
      have ej1 : j1 = j1'.castSucc := Fin.ext rfl
      have ej2 : j2 = j2'.castSucc := Fin.ext rfl
      rw [ej1, ej2]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rintro ⟨v1, v2⟩
      have hds : DS t y p' := ⟨j1', j2', i1, i2, show (j1 : ℕ) < j2 from k12,
        ap1, ap2, v1⟩
      have hnot := hn i3 ⟨p', hpR⟩ hp
      have hle : c i3 ≤ y (Fin.last N) ⟨p', hpR⟩ := by
        by_contra hh; push_neg at hh; exact hnot ⟨hds, hh⟩
      by_cases hj2N : (j2 : ℕ) = N
      · have : j2' = Fin.last N := Fin.ext hj2N
        have hi2 : (i2 : ℕ) = p' := al_last ht (by simpa [j2', hj2N] using ap2)
        have : i2 = ⟨p', hpR⟩ := Fin.ext hi2
        subst this
        rw [show j2' = Fin.last N from Fin.ext hj2N] at v2
        exact absurd (lt_of_lt_of_le v2 hle) (lt_irrefl _)
      · apply h j1' j2' (Fin.last N) i1 i2 ⟨p', hpR⟩ (show (j1 : ℕ) < j2 from k12)
          (show (j2 : ℕ) < N by omega) ap1 ap2
        exact ⟨v1, lt_of_lt_of_le v2 hle⟩
    · have hj3' : (j3 : ℕ) < N + 1 := by have := j3.isLt; omega
      have k12 : (j1 : ℕ) < j2 := h12
      have k23 : (j2 : ℕ) < j3 := h23
      let j1' : Fin (N + 1) := ⟨j1, by omega⟩
      let j2' : Fin (N + 1) := ⟨j2, by omega⟩
      let j3' : Fin (N + 1) := ⟨j3, hj3'⟩
      have ej1 : j1 = j1'.castSucc := Fin.ext rfl
      have ej2 : j2 = j2'.castSucc := Fin.ext rfl
      have ej3 : j3 = j3'.castSucc := Fin.ext rfl
      rw [ej1, ej2, ej3]
      simp only [Fin.snoc_castSucc]
      exact h j1' j2' j3' i1 i2 i3 h12 h23 a1 a2

theorem DS_snoc (t : ℕ) (ht : t < 3) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m)
    (i : Fin R) :
    DS t (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) i ↔
      ∃ p : Fin R, PR t i p ∧ (DS t y p ∨ c i < y (Fin.last N) p) := by
  constructor
  · rintro ⟨j1, j2, i1, i2, h12, a1, a2, hv⟩
    have k12 : (j1 : ℕ) < j2 := h12
    have hj1 : (j1 : ℕ) ≤ N := by have := j2.isLt; omega
    obtain ⟨p, hp, ap1⟩ := al_pred ht hj1 a1
    have hpR : p < R := al_pred_bound i1.isLt i.isLt hj1 hp ap1
    refine ⟨⟨p, hpR⟩, hp, ?_⟩
    let j1' : Fin (N + 1) := ⟨j1, by omega⟩
    have ej1 : j1 = j1'.castSucc := Fin.ext rfl
    by_cases hj2 : (j2 : ℕ) = N + 1
    · have e2 : j2 = Fin.last (N + 1) := Fin.ext hj2
      have hi2 : (i2 : ℕ) = i := al_last ht (by simpa [hj2] using a2)
      have e2' : i2 = i := Fin.ext hi2
      subst e2 e2'
      rw [ej1] at hv
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at hv
      by_cases hj1N : (j1 : ℕ) = N
      · right
        have hi1 : (i1 : ℕ) = p := al_last ht (by simpa [hj1N] using ap1)
        have : i1 = ⟨p, hpR⟩ := Fin.ext hi1
        subst this
        rwa [show j1' = Fin.last N from Fin.ext hj1N] at hv
      · by_cases hlt : c i2 < y (Fin.last N) ⟨p, hpR⟩
        · exact Or.inr hlt
        · left
          push_neg at hlt
          exact ⟨j1', Fin.last N, i1, ⟨p, hpR⟩, show (j1 : ℕ) < N by omega, ap1,
            al_refl t p N ht, lt_of_le_of_lt hlt hv⟩
    · left
      have hj2' : (j2 : ℕ) < N + 1 := by have := j2.isLt; omega
      let j2' : Fin (N + 1) := ⟨j2, hj2'⟩
      have ej2 : j2 = j2'.castSucc := Fin.ext rfl
      rw [ej1, ej2] at hv
      simp only [Fin.snoc_castSucc] at hv
      obtain ⟨p', hp', ap2⟩ := al_pred ht (by omega : (j2 : ℕ) ≤ N) a2
      have hpp : p' = p := by unfold PR at hp hp'; omega
      subst hpp
      exact ⟨j1', j2', i1, i2, h12, ap1, ap2, hv⟩
  · rintro ⟨p, hp, hd | hc⟩
    · obtain ⟨j1, j2, i1, i2, h12, a1, a2, hv⟩ := hd
      refine ⟨j1.castSucc, j2.castSucc, i1, i2, by simpa using h12, by simpa using al_succ hp a1,
        by simpa using al_succ hp a2, ?_⟩
      simpa using hv
    · refine ⟨(Fin.last N).castSucc, Fin.last (N + 1), p, i, Fin.castSucc_lt_last _,
        by simpa using al_self_succ (N := N) hp, by simpa using al_refl t i (N + 1) ht, ?_⟩
      simpa using hc

theorem RN_snoc {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) :
    RN (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) ↔ RN y ∧ ∀ i, y (Fin.last N) i ≤ c i := by
  constructor
  · intro h
    refine ⟨fun j1 j2 hj i => ?_, fun i => ?_⟩
    · have := h j1.castSucc j2.castSucc (by simpa using hj) i
      simpa using this
    · have := h (Fin.last N).castSucc (Fin.last (N + 1)) (Fin.castSucc_lt_last _).le i
      simpa using this
  · rintro ⟨h, hl⟩ j1 j2 hj i
    by_cases hj2 : (j2 : ℕ) = N + 1
    · have e2 : j2 = Fin.last (N + 1) := Fin.ext hj2
      subst e2
      by_cases hj1 : (j1 : ℕ) = N + 1
      · have e1 : j1 = Fin.last (N + 1) := Fin.ext hj1
        subst e1; exact le_refl _
      · let j1' : Fin (N + 1) := ⟨j1, by have := j1.isLt; omega⟩
        have ej1 : j1 = j1'.castSucc := Fin.ext rfl
        rw [ej1]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact le_trans (h j1' (Fin.last N) (Fin.le_last _) i) (hl i)
    · have k12 : (j1 : ℕ) ≤ j2 := hj
      let j1' : Fin (N + 1) := ⟨j1, by have := j2.isLt; omega⟩
      let j2' : Fin (N + 1) := ⟨j2, by have := j2.isLt; omega⟩
      have ej1 : j1 = j1'.castSucc := Fin.ext rfl
      have ej2 : j2 = j2'.castSucc := Fin.ext rfl
      rw [ej1, ej2]
      simp only [Fin.snoc_castSucc]
      exact h j1' j2' hj i

end Sem

end UG

namespace UG

open Finset

section Gen

variable {R m : ℕ}

/-- The generic array condition: every column satisfies CO, rows are nondecreasing when rn,
and no line of a type in U has a valley. -/
def P (CO : (Fin R → Fin m) → Prop) (rn : Bool) (U : List ℕ) {N : ℕ}
    (y : Fin N → Fin R → Fin m) : Prop :=
  (∀ j, CO (y j)) ∧ (rn = true → RN y) ∧ ∀ t ∈ U, UC t y

/-- The condition on a new last column c. -/
def OK (CO : (Fin R → Fin m) → Prop) (rn : Bool) (U : List ℕ) {N : ℕ}
    (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) : Prop :=
  CO c ∧ (rn = true → ∀ i, y (Fin.last N) i ≤ c i) ∧
    ∀ t ∈ U, ∀ i p : Fin R, PR t i p → ¬ (DS t y p ∧ y (Fin.last N) p < c i)

theorem P_snoc (CO : (Fin R → Fin m) → Prop) (rn : Bool) (U : List ℕ) (hU : ∀ t ∈ U, t < 3)
    {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) :
    P CO rn U (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) ↔ P CO rn U y ∧ OK CO rn U y c := by
  unfold P OK
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hr : (rn = true → RN (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m)) ↔
      (rn = true → RN y) ∧ (rn = true → ∀ i, y (Fin.last N) i ≤ c i) := by
    rw [RN_snoc]
    constructor
    · intro h; exact ⟨fun h1 => (h h1).1, fun h1 => (h h1).2⟩
    · intro h h1; exact ⟨h.1 h1, h.2 h1⟩
  have hu : (∀ t ∈ U, UC t (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m)) ↔
      (∀ t ∈ U, UC t y) ∧
        ∀ t ∈ U, ∀ i p : Fin R, PR t i p → ¬ (DS t y p ∧ y (Fin.last N) p < c i) := by
    constructor
    · intro h
      exact ⟨fun t ht => ((UC_snoc t (hU t ht) y c).1 (h t ht)).1,
        fun t ht => ((UC_snoc t (hU t ht) y c).1 (h t ht)).2⟩
    · intro h t ht
      exact (UC_snoc t (hU t ht) y c).2 ⟨h.1 t ht, h.2 t ht⟩
  rw [hr, hu]
  tauto

theorem P_one (CO : (Fin R → Fin m) → Prop) (rn : Bool) (U : List ℕ)
    (y : Fin 1 → Fin R → Fin m) : P CO rn U y ↔ CO (y 0) := by
  unfold P
  constructor
  · rintro ⟨h, -, -⟩; exact h 0
  · intro h
    refine ⟨fun j => by rw [Fin.fin_one_eq_zero j]; exact h, fun _ => ?_, fun t _ => ?_⟩
    · intro j1 j2 _ i
      rw [Fin.fin_one_eq_zero j1, Fin.fin_one_eq_zero j2]
    · intro j1 j2 _ _ _ _ h12
      rw [Fin.fin_one_eq_zero j1, Fin.fin_one_eq_zero j2] at h12
      exact absurd h12 (lt_irrefl _)

lemma DS_one (t : ℕ) (y : Fin 1 → Fin R → Fin m) (p : ℕ) : ¬ DS t y p := by
  rintro ⟨j1, j2, -, -, h12, -⟩
  rw [Fin.fin_one_eq_zero j1, Fin.fin_one_eq_zero j2] at h12
  exact lt_irrefl _ h12

/-! Codes. -/

def dg (m c i : ℕ) : ℕ := c / m ^ i % m

def ccode (v : Fin R → Fin m) : ℕ := (finFunctionFinEquiv v : ℕ)

lemma ccode_lt (v : Fin R → Fin m) : ccode v < m ^ R := (finFunctionFinEquiv v).isLt

lemma dg_ccode (v : Fin R → Fin m) (i : Fin R) : dg m (ccode v) i = v i := by
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv v) i
  rw [Equiv.symm_apply_apply] at this
  rw [this]; rfl

lemma ccode_inj {v w : Fin R → Fin m} (h : ccode v = ccode w) : v = w := by
  have : finFunctionFinEquiv v = finFunctionFinEquiv w := Fin.ext h
  exact finFunctionFinEquiv.injective this

/-- The flags of y: bit t * R + p says that the line of type t ∈ U through (p, last) descends. -/
def gS (U : List ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) : Fin (3 * R) → Fin 2 :=
  fun q => if (q : ℕ) / R ∈ U ∧ DS ((q : ℕ) / R) y ((q : ℕ) % R) then 1 else 0

/-- The code of the state after y: last column and flags. -/
def stS (U : List ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) : ℕ :=
  ccode (y (Fin.last N)) + m ^ R * (finFunctionFinEquiv (gS U y) : ℕ)

def fb (R m s q : ℕ) : Bool := s / m ^ R / 2 ^ q % 2 == 1

def vb (R t i : ℕ) : Bool := t == 0 || (t == 1 && decide (0 < i)) || (t == 2 && decide (i + 1 < R))

def pv (t i : ℕ) : ℕ := if t = 0 then i else if t = 1 then i - 1 else i + 1

def allB (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allB f n && f n

def bsum (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bsum f n + if f n then 2 ^ n else 0

def okc (R m : ℕ) (COc : ℕ → Bool) (rn : Bool) (U : List ℕ) (s c : ℕ) : Bool :=
  COc c && (!rn || allB (fun i => decide (dg m (s % m ^ R) i ≤ dg m c i)) R) &&
    U.all (fun t => allB (fun i => !(vb R t i) ||
      !(fb R m s (t * R + pv t i) && decide (dg m (s % m ^ R) (pv t i) < dg m c i))) R)

def nfl (R m : ℕ) (U : List ℕ) (s c q : ℕ) : Bool :=
  U.contains (q / R) && vb R (q / R) (q % R) &&
    (fb R m s ((q / R) * R + pv (q / R) (q % R)) ||
      decide (dg m c (q % R) < dg m (s % m ^ R) (pv (q / R) (q % R))))

def dc (R m : ℕ) (U : List ℕ) (s c : ℕ) : ℕ := c + m ^ R * bsum (nfl R m U s c) (3 * R)

lemma allB_iff (f : ℕ → Bool) (n : ℕ) : allB f n = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allB]
  | succ n ih =>
    simp only [allB, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h
      · rw [h]; exact h2
    · intro h; exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

lemma bsum_eq (f : ℕ → Bool) (n : ℕ) : bsum f n = ∑ i ∈ range n, if f i then 2 ^ i else 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bsum, ih, Finset.sum_range_succ]

lemma vb_pv (R t i : ℕ) (ht : t < 3) (hi : i < R) (p : ℕ) :
    (PR t i p ∧ p < R) ↔ (vb R t i = true ∧ p = pv t i) := by
  unfold PR vb pv
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with h | h | h <;> subst h <;> simp <;> omega

lemma stS_mod (U : List ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) :
    stS U y % m ^ R = ccode (y (Fin.last N)) := by
  unfold stS
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ccode_lt _)]

lemma fb_stS (U : List ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (q : Fin (3 * R)) :
    fb R m (stS U y) q = decide ((q : ℕ) / R ∈ U ∧ DS ((q : ℕ) / R) y ((q : ℕ) % R)) := by
  have hm : 0 < m ^ R := by
    have := ccode_lt (y (Fin.last N)); omega
  unfold fb stS
  rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (ccode_lt _), zero_add]
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv (gS U y)) q
  rw [Equiv.symm_apply_apply] at this
  rw [← this]
  unfold gS
  split_ifs with h <;> simp [h]

theorem okc_stS (CO : (Fin R → Fin m) → Prop) (COc : ℕ → Bool)
    (hCO : ∀ v, COc (ccode v) = true ↔ CO v) (rn : Bool) (U : List ℕ) (hU : ∀ t ∈ U, t < 3)
    {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) :
    okc R m COc rn U (stS U y) (ccode c) = true ↔ OK CO rn U y c := by
  unfold okc OK
  simp only [Bool.and_eq_true, hCO, stS_mod]
  rw [and_assoc]
  apply and_congr (Iff.rfl)
  apply and_congr
  · cases rn
    · simp
    · simp only [Bool.not_true, Bool.false_or, allB_iff, decide_eq_true_eq, forall_const]
      constructor
      · intro h i
        have := h i i.isLt
        rw [dg_ccode, dg_ccode] at this
        exact this
      · intro h i hi
        have := h ⟨i, hi⟩
        rw [show i = ((⟨i, hi⟩ : Fin R) : ℕ) from rfl, dg_ccode, dg_ccode]
        exact this
  · simp only [List.all_eq_true, allB_iff]
    apply forall_congr'; intro t
    apply forall_congr'; intro htU
    have ht := hU t htU
    constructor
    · intro h i p hp ⟨hd, hc⟩
      have hpR : (p : ℕ) < R := p.isLt
      obtain ⟨hvb, hpe⟩ := (vb_pv R t i ht i.isLt p).1 ⟨hp, hpR⟩
      have := h i i.isLt
      rw [hvb, ← hpe] at this
      have hq : t * R + p < 3 * R := by
        have : t * R ≤ 2 * R := Nat.mul_le_mul_right _ (by omega)
        omega
      have hfb := fb_stS U y ⟨t * R + p, hq⟩
      simp only at hfb
      have e1 : (t * R + p) / R = t := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hpR, zero_add]
      have e2 : (t * R + p) % R = p := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpR]
      rw [e1, e2] at hfb
      rw [hfb] at this
      have hdg1 : dg m (ccode (y (Fin.last N))) p = y (Fin.last N) p := dg_ccode _ p
      have hdg2 : dg m (ccode c) i = c i := dg_ccode _ i
      rw [hdg1, hdg2] at this
      simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at this
      rcases this with h1 | h1
      · exact h1 ⟨htU, hd⟩
      · exact h1 hc
    · intro h i hi
      cases hv : vb R t i
      · simp
      · simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true', Bool.and_eq_false_iff,
          decide_eq_false_iff_not]
        have hpe : pv t i < R ∧ PR t i (pv t i) := by
          have := (vb_pv R t i ht hi (pv t i)).2 ⟨hv, rfl⟩
          exact ⟨this.2, this.1⟩
        have hq : t * R + pv t i < 3 * R := by
          have : t * R ≤ 2 * R := Nat.mul_le_mul_right _ (by omega)
          omega
        have hfb := fb_stS U y ⟨t * R + pv t i, hq⟩
        simp only at hfb
        have e1 : (t * R + pv t i) / R = t := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hpe.1, zero_add]
        have e2 : (t * R + pv t i) % R = pv t i := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpe.1]
        rw [e1, e2] at hfb
        rw [hfb]
        have hdg1 : dg m (ccode (y (Fin.last N))) (pv t i) = y (Fin.last N) ⟨pv t i, hpe.1⟩ :=
          dg_ccode _ ⟨pv t i, hpe.1⟩
        have hdg2 : dg m (ccode c) i = c ⟨i, hi⟩ := dg_ccode _ ⟨i, hi⟩
        rw [hdg1, hdg2]
        have := h ⟨i, hi⟩ ⟨pv t i, hpe.1⟩ hpe.2
        by_cases hd : t ∈ U ∧ DS t y (pv t i)
        · right
          intro hc
          exact this ⟨hd.2, hc⟩
        · left
          simpa using hd

theorem dc_stS (U : List ℕ) (hU : ∀ t ∈ U, t < 3) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m)
    (c : Fin R → Fin m) :
    dc R m U (stS U y) (ccode c) = stS U (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) := by
  unfold dc
  conv_rhs => unfold stS
  simp only [Fin.snoc_last]
  congr 2
  rw [bsum_eq, finFunctionFinEquiv_apply, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  have hR : 0 < R := by have := q.isLt; omega
  have hqR : (q : ℕ) % R < R := Nat.mod_lt _ hR
  have ht3 : (q : ℕ) / R < 3 := by
    have := q.isLt
    exact Nat.div_lt_of_lt_mul (by linarith)
  have key : nfl R m U (stS U y) (ccode c) q = true ↔
      ((q : ℕ) / R ∈ U ∧ DS ((q : ℕ) / R) (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m)
        ((q : ℕ) % R)) := by
    have hds := DS_snoc ((q : ℕ) / R) ht3 y c ⟨(q : ℕ) % R, hqR⟩
    simp only at hds
    rw [hds]
    unfold nfl
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hU', hv⟩, hor⟩
      have hp := (vb_pv R _ _ ht3 hqR (pv ((q : ℕ) / R) ((q : ℕ) % R))).2 ⟨hv, rfl⟩
      refine ⟨hU', ⟨_, hp.2⟩, hp.1, ?_⟩
      have hq : (q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R) < 3 * R := by
        have : (q : ℕ) / R * R ≤ 2 * R := Nat.mul_le_mul_right _ (by omega)
        omega
      have hfb := fb_stS U y ⟨_, hq⟩
      simp only at hfb
      have e1 : ((q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R)) / R = (q : ℕ) / R := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hp.2, zero_add]
      have e2 : ((q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R)) % R =
          pv ((q : ℕ) / R) ((q : ℕ) % R) := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp.2]
      rw [e1, e2] at hfb
      rcases hor with h1 | h1
      · rw [hfb] at h1
        simp only [decide_eq_true_eq] at h1
        exact Or.inl h1.2
      · right
        rw [stS_mod, dg_ccode c ⟨_, hqR⟩, dg_ccode _ ⟨_, hp.2⟩] at h1
        exact h1
    · rintro ⟨hU', ⟨p, hpR⟩, hp, hor⟩
      have hv := (vb_pv R _ _ ht3 hqR p).1 ⟨hp, hpR⟩
      refine ⟨⟨hU', hv.1⟩, ?_⟩
      have hpe : p = pv ((q : ℕ) / R) ((q : ℕ) % R) := hv.2
      subst hpe
      have hq : (q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R) < 3 * R := by
        have : (q : ℕ) / R * R ≤ 2 * R := Nat.mul_le_mul_right _ (by omega)
        omega
      have hfb := fb_stS U y ⟨_, hq⟩
      simp only at hfb
      have e1 : ((q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R)) / R = (q : ℕ) / R := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hpR, zero_add]
      have e2 : ((q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R)) % R =
          pv ((q : ℕ) / R) ((q : ℕ) % R) := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpR]
      rw [e1, e2] at hfb
      rcases hor with h1 | h1
      · left
        rw [hfb]
        simp only [decide_eq_true_eq]
        exact ⟨hU', h1⟩
      · right
        rw [stS_mod, dg_ccode c ⟨_, hqR⟩, dg_ccode _ ⟨_, hpR⟩]
        exact h1
  unfold gS
  by_cases h : nfl R m U (stS U y) (ccode c) q = true
  · rw [if_pos h, if_pos (key.1 h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (key.2 h'))]; simp

end Gen

end UG

namespace UG

open Finset

section Count

variable {R m : ℕ} (CO : (Fin R → Fin m) → Prop) [DecidablePred CO] (COc : ℕ → Bool)
  (hCO : ∀ v, COc (ccode v) = true ↔ CO v) (rn : Bool) (U : List ℕ) (hU : ∀ t ∈ U, t < 3)

instance instDecP {N : ℕ} (y : Fin N → Fin R → Fin m) : Decidable (P CO rn U y) := by
  unfold P UC RN; infer_instance

/-- Arrays of width N + 1 satisfying P, weighted by g of their final state. -/
def Cnt (N : ℕ) (g : ℕ → ℕ) : ℕ :=
  ∑ y : Fin (N + 1) → Fin R → Fin m, if P CO rn U y then g (stS U y) else 0

lemma sum_range_list (f : ℕ → ℕ) (B : ℕ) : ∑ i ∈ range B, f i = ((List.range B).map f).sum := by
  induction B with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp

lemma sum_col (f : ℕ → ℕ) :
    ∑ c : Fin R → Fin m, f (ccode c) = ((List.range (m ^ R)).map f).sum := by
  rw [← sum_range_list, ← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv finFunctionFinEquiv _ _ (fun c => rfl)

include hCO hU in
theorem Cnt_succ (N : ℕ) (g : ℕ → ℕ) :
    Cnt CO rn U (N + 1) g = Cnt CO rn U N (fun s => ((List.range (m ^ R)).map (fun c =>
      if okc R m COc rn U s c = true then g (dc R m U s c) else 0)).sum) := by
  unfold Cnt
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin R → Fin m))
    (fun p => if P CO rn U (Fin.snoc p.2 p.1 : Fin (N + 2) → Fin R → Fin m) then
      g (stS U (Fin.snoc p.2 p.1 : Fin (N + 2) → Fin R → Fin m)) else 0) _ (fun p => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : P CO rn U y
  · rw [if_pos hy]
    beta_reduce
    rw [← sum_col]
    apply Finset.sum_congr rfl
    intro c _
    rw [dc_stS U hU y c]
    by_cases hc : OK CO rn U y c
    · rw [if_pos ((P_snoc CO rn U hU y c).2 ⟨hy, hc⟩),
        if_pos ((okc_stS CO COc hCO rn U hU y c).2 hc)]
    · rw [if_neg (fun h => hc ((P_snoc CO rn U hU y c).1 h).2),
        if_neg (fun h => hc ((okc_stS CO COc hCO rn U hU y c).1 h))]
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg (fun h => hy ((P_snoc CO rn U hU y c).1 h).1)]

/-- Continuation counts on codes. -/
def Wc (R m : ℕ) (COc : ℕ → Bool) (rn : Bool) (U : List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j + 1, s => ((List.range (m ^ R)).map (fun c =>
      if okc R m COc rn U s c = true then Wc R m COc rn U j (dc R m U s c) else 0)).sum

include hCO hU in
theorem Cnt_W (N j : ℕ) :
    Cnt CO rn U N (Wc R m COc rn U j) = Cnt CO rn U 0 (Wc R m COc rn U (N + j)) := by
  induction N generalizing j with
  | zero => simp
  | succ N ih =>
    rw [Cnt_succ CO COc hCO rn U hU]
    have : (fun s => ((List.range (m ^ R)).map (fun c =>
      if okc R m COc rn U s c = true then Wc R m COc rn U j (dc R m U s c) else 0)).sum) =
        Wc R m COc rn U (j + 1) := rfl
    rw [this, ih, show N + (j + 1) = N + 1 + j by omega]

include hCO in
theorem Cnt_zero (g : ℕ → ℕ) :
    Cnt CO rn U 0 g = ((List.range (m ^ R)).map (fun k => if COc k = true then g k else 0)).sum := by
  unfold Cnt
  rw [← sum_col]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin R → Fin m)) _ _ (fun y => ?_)
  have hy : y = fun _ => y 0 := by funext j; rw [Fin.fin_one_eq_zero j]
  have hst : stS U y = ccode (y 0) := by
    unfold stS
    have : gS U y = fun _ => 0 := by
      funext q; unfold gS; rw [if_neg (fun h => DS_one _ y _ h.2)]
    rw [this, finFunctionFinEquiv_apply]
    simp
  simp only [Equiv.funUnique_apply, Function.eval]
  rw [show (default : Fin 1) = 0 from rfl, hst]
  by_cases h : CO (y 0)
  · rw [if_pos ((P_one CO rn U y).2 h), if_pos ((hCO _).2 h)]
  · rw [if_neg (fun h' => h ((P_one CO rn U y).1 h')), if_neg (fun h' => h ((hCO _).1 h'))]

include hCO hU in
theorem count_eq (N : ℕ) :
    (univ.filter (fun y : Fin (N + 1) → Fin R → Fin m => P CO rn U y)).card =
      ((List.range (m ^ R)).map (fun k => if COc k = true then Wc R m COc rn U N k else 0)).sum := by
  rw [Finset.card_filter]
  have : (∑ y : Fin (N + 1) → Fin R → Fin m, if P CO rn U y then 1 else 0) =
      Cnt CO rn U N (Wc R m COc rn U 0) := rfl
  rw [this, Cnt_W CO COc hCO rn U hU, Cnt_zero CO COc hCO, Nat.add_zero]

end Count

/-! The certificate. -/

def gL (L : List ℕ) (i : ℕ) : ℕ := L.getD i 0

lemma flt_sum (L : List ℕ) (p : ℕ → Bool) (g : ℕ → ℕ) (f : ℕ → ℕ) :
    (L.map (fun c => if p c = true then f (g c) else 0)).sum =
      ((L.filterMap (fun c => if p c = true then some (g c) else none)).map f).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => by_cases h : p a = true <;> simp [List.filterMap_cons, h, ih]

def Lin (cs : List (ℕ × ℕ)) (F : ℕ → ℕ) (n : ℕ) : ℕ := (cs.map (fun p => p.1 * F (n + p.2))).sum

lemma Lin_sum (cs : List (ℕ × ℕ)) (L : List ℕ) (G : ℕ → ℕ → ℕ) (n : ℕ) :
    Lin cs (fun j => (L.map (fun t => G t j)).sum) n = (L.map (fun t => Lin cs (G t) n)).sum := by
  induction cs with
  | nil => simp [Lin]
  | cons p cs ih =>
    unfold Lin at ih ⊢
    rw [List.map_cons, List.sum_cons, ih, ← List.sum_map_mul_left]
    simp only [List.map_cons, List.sum_cons]
    rw [← List.sum_map_add]

section Cert

variable (R m : ℕ) (COc : ℕ → Bool) (rn : Bool) (U : List ℕ) (RL : List ℕ) (SI : List (List ℕ))
  (BL : List ℕ) (BS : List (List ℕ)) (VT : List (List ℕ)) (NS NB : ℕ)

def c1 (idx : ℕ) : Bool :=
  ((List.range (m ^ R)).filterMap (fun c =>
    if okc R m COc rn U (gL RL idx) c = true then some (dc R m U (gL RL idx) c) else none)) ==
      (SI.getD idx []).map (gL RL) && (SI.getD idx []).all (fun t => decide (t < NS))

def chk1 : Bool := (List.range NS).all (c1 R m COc rn U RL SI NS)

lemma all_split (f : ℕ → Bool) (a k n : ℕ) (h1 : (List.range' a k).all f = true)
    (h2 : (List.range' (a + k) n).all f = true) : (List.range' a (k + n)).all f = true := by
  rw [List.all_eq_true] at h1 h2 ⊢
  intro x hx
  rw [List.mem_range'_1] at hx
  by_cases hxa : x < a + k
  · exact h1 x (List.mem_range'_1.2 ⟨hx.1, hxa⟩)
  · exact h2 x (List.mem_range'_1.2 ⟨by omega, by omega⟩)

lemma chk1_of (h : (List.range' 0 NS).all (c1 R m COc rn U RL SI NS) = true) :
    chk1 R m COc rn U RL SI NS = true := by
  unfold chk1; rw [List.range_eq_range']; exact h

def c2 : ℕ → Bool := fun idx =>
  decide (gL BL idx < NB) && ((SI.getD idx []).map (gL BL)).isPerm (BS.getD (gL BL idx) [])

def chk2 : Bool := (List.range NS).all (c2 SI BL BS NB)

lemma chk2_of (h : (List.range' 0 NS).all (c2 SI BL BS NB) = true) : chk2 SI BL BS NS NB = true := by
  unfold chk2; rw [List.range_eq_range']; exact h

def chkV (J : ℕ) : Bool :=
  (List.range NB).all (fun b => gL (VT.getD 0 []) b == 1) &&
    (List.range J).all (fun j => (List.range NB).all (fun b =>
      gL (VT.getD (j + 1) []) b == ((BS.getD b []).map (gL (VT.getD j []))).sum))

lemma W_succ (h1 : chk1 R m COc rn U RL SI NS = true) (idx : ℕ) (hi : idx < NS) (j : ℕ) :
    Wc R m COc rn U (j + 1) (gL RL idx) =
      ((SI.getD idx []).map (fun t => Wc R m COc rn U j (gL RL t))).sum := by
  unfold chk1 at h1
  rw [List.all_eq_true] at h1
  have h := h1 idx (List.mem_range.2 hi)
  unfold c1 at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  rw [Wc, flt_sum, h.1, List.map_map]
  rfl

lemma W_SI_lt (h1 : chk1 R m COc rn U RL SI NS = true) (idx : ℕ) (hi : idx < NS) :
    ∀ t ∈ SI.getD idx [], t < NS := by
  unfold chk1 at h1
  rw [List.all_eq_true] at h1
  have h := h1 idx (List.mem_range.2 hi)
  unfold c1 at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro t ht
  simpa using h.2 t ht

theorem W_eq_V (J : ℕ) (h1 : chk1 R m COc rn U RL SI NS = true) (h2 : chk2 SI BL BS NS NB = true)
    (hV : chkV BS VT NB J = true) :
    ∀ j ≤ J, ∀ idx < NS, Wc R m COc rn U j (gL RL idx) = gL (VT.getD j []) (gL BL idx) := by
  unfold chk2 c2 at h2
  unfold chkV at hV
  rw [List.all_eq_true] at h2
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hV
  intro j
  induction j with
  | zero =>
    intro _ idx hi
    have hb := h2 idx (List.mem_range.2 hi)
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    have := hV.1 _ (List.mem_range.2 hb.1)
    rw [beq_iff_eq] at this
    rw [this]; rfl
  | succ j ih =>
    intro hj idx hi
    rw [W_succ R m COc rn U RL SI NS h1 idx hi]
    have hb := h2 idx (List.mem_range.2 hi)
    rw [Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hb
    have e : ((SI.getD idx []).map (fun t => Wc R m COc rn U j (gL RL t))).sum =
        (((SI.getD idx []).map (gL BL)).map (gL (VT.getD j []))).sum := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact ih (by omega) t (W_SI_lt R m COc rn U RL SI NS h1 idx hi t ht)
    rw [e, (hb.2.map _).sum_eq]
    have := List.all_eq_true.1 (hV.2 j (List.mem_range.2 (by omega))) (gL BL idx)
      (List.mem_range.2 hb.1)
    rw [beq_iff_eq] at this
    rw [this]

def chkI (LC RC : List (ℕ × ℕ)) (e : ℕ) : Bool :=
  (List.range NB).all (fun b =>
    Lin LC (fun j => gL (VT.getD j []) b) e == Lin RC (fun j => gL (VT.getD j []) b) e)

theorem W_ident (J : ℕ) (h1 : chk1 R m COc rn U RL SI NS = true) (h2 : chk2 SI BL BS NS NB = true)
    (hV : chkV BS VT NB J = true) (LC RC : List (ℕ × ℕ)) (e : ℕ)
    (hI : chkI VT NB LC RC e = true) (hJ : ∀ p ∈ LC ++ RC, e + p.2 ≤ J) :
    ∀ n, ∀ idx < NS, Lin LC (fun j => Wc R m COc rn U j (gL RL idx)) (e + n) =
      Lin RC (fun j => Wc R m COc rn U j (gL RL idx)) (e + n) := by
  intro n
  induction n with
  | zero =>
    intro idx hi
    have hWV := W_eq_V R m COc rn U RL SI BL BS VT NS NB J h1 h2 hV
    have hb : gL BL idx < NB := by
      unfold chk2 c2 at h2; rw [List.all_eq_true] at h2
      have := h2 idx (List.mem_range.2 hi)
      rw [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    unfold chkI at hI
    rw [List.all_eq_true] at hI
    have := hI _ (List.mem_range.2 hb)
    rw [beq_iff_eq] at this
    have eL : Lin LC (fun j => Wc R m COc rn U j (gL RL idx)) (e + 0) =
        Lin LC (fun j => gL (VT.getD j []) (gL BL idx)) e := by
      unfold Lin; congr 1; apply List.map_congr_left; intro p hp
      dsimp only
      rw [Nat.add_zero, hWV _ (hJ p (List.mem_append_left _ hp)) idx hi]
    have eR : Lin RC (fun j => Wc R m COc rn U j (gL RL idx)) (e + 0) =
        Lin RC (fun j => gL (VT.getD j []) (gL BL idx)) e := by
      unfold Lin; congr 1; apply List.map_congr_left; intro p hp
      dsimp only
      rw [Nat.add_zero, hWV _ (hJ p (List.mem_append_right _ hp)) idx hi]
    rw [eL, eR, this]
  | succ n ih =>
    intro idx hi
    have key : ∀ cs : List (ℕ × ℕ), Lin cs (fun j => Wc R m COc rn U j (gL RL idx)) (e + (n + 1)) =
        ((SI.getD idx []).map (fun t => Lin cs (fun j => Wc R m COc rn U j (gL RL t)) (e + n))).sum := by
      intro cs
      rw [← Lin_sum]
      unfold Lin
      congr 1
      apply List.map_congr_left
      intro p _
      dsimp only
      rw [show e + (n + 1) + p.2 = (e + n + p.2) + 1 by omega,
        W_succ R m COc rn U RL SI NS h1 idx hi]
    rw [key, key]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact ih t (W_SI_lt R m COc rn U RL SI NS h1 idx hi t ht)

/-- The total counts. -/
def Ac (N : ℕ) : ℕ :=
  ((List.range (m ^ R)).map (fun k => if COc k = true then Wc R m COc rn U N k else 0)).sum

def chk3 (IL : List ℕ) : Bool :=
  ((List.range (m ^ R)).filterMap (fun k => if COc k = true then some k else none)) ==
    IL.map (gL RL) && IL.all (fun t => decide (t < NS))

lemma Ac_IL (IL : List ℕ) (h3 : chk3 R m COc RL NS IL = true) (N : ℕ) :
    Ac R m COc rn U N = (IL.map (fun t => Wc R m COc rn U N (gL RL t))).sum := by
  unfold chk3 at h3
  rw [Bool.and_eq_true, beq_iff_eq] at h3
  unfold Ac
  have e := flt_sum (List.range (m ^ R)) COc (fun k => k) (Wc R m COc rn U N)
  rw [e, h3.1, List.map_map]
  rfl

theorem A_ident (J : ℕ) (h1 : chk1 R m COc rn U RL SI NS = true) (h2 : chk2 SI BL BS NS NB = true)
    (hV : chkV BS VT NB J = true) (LC RC : List (ℕ × ℕ)) (e : ℕ)
    (hI : chkI VT NB LC RC e = true) (hJ : ∀ p ∈ LC ++ RC, e + p.2 ≤ J) (IL : List ℕ)
    (h3 : chk3 R m COc RL NS IL = true) (n : ℕ) :
    Lin LC (Ac R m COc rn U) (e + n) = Lin RC (Ac R m COc rn U) (e + n) := by
  have hA : Ac R m COc rn U = fun N => (IL.map (fun t => Wc R m COc rn U N (gL RL t))).sum := by
    funext N; exact Ac_IL R m COc rn U RL NS IL h3 N
  rw [hA, Lin_sum, Lin_sum]
  congr 1
  apply List.map_congr_left
  intro t ht
  have : t < NS := by
    unfold chk3 at h3; rw [Bool.and_eq_true, List.all_eq_true] at h3
    simpa using h3.2 t ht
  exact W_ident R m COc rn U RL SI BL BS VT NS NB J h1 h2 hV LC RC e hI hJ n t this

theorem A_val (J : ℕ) (h1 : chk1 R m COc rn U RL SI NS = true) (h2 : chk2 SI BL BS NS NB = true)
    (hV : chkV BS VT NB J = true) (IL : List ℕ) (h3 : chk3 R m COc RL NS IL = true) (N : ℕ)
    (hN : N ≤ J) :
    Ac R m COc rn U N = (IL.map (fun t => gL (VT.getD N []) (gL BL t))).sum := by
  rw [Ac_IL R m COc rn U RL NS IL h3]
  congr 1
  apply List.map_congr_left
  intro t ht
  have : t < NS := by
    unfold chk3 at h3; rw [Bool.and_eq_true, List.all_eq_true] at h3
    simpa using h3.2 t ht
  exact W_eq_V R m COc rn U RL SI BL BS VT NS NB J h1 h2 hV N hN t this

end Cert

end UG

namespace PA224355

open OMA.S_oeis_a224355 UG PowerSeries

def CO (_v : Fin 4 → Fin 3) : Prop := True

instance : DecidablePred CO := fun _ => instDecidableTrue

def COc (_c : ℕ) : Bool := true

theorem hCO (v : Fin 4 → Fin 3) : COc (ccode v) = true ↔ CO v := by simp [COc, CO]

theorem hU : ∀ t ∈ ([1, 2] : List ℕ), t < 3 := by decide

theorem uc_anti {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : AntidiagUnimodal x ↔ UC 2 (fun j i => x i j) := by
  constructor
  · intro h j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    exact h i1 i2 i3 j1 j2 j3 h12 h23 (by unfold al at a1 a2; omega) (by unfold al at a1 a2; omega)
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    exact h j1 j2 j3 i1 i2 i3 h12 h23 (by unfold al; omega) (by unfold al; omega)

theorem uc_diag {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : DiagUnimodal x ↔ UC 1 (fun j i => x i j) := by
  constructor
  · intro h j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    exact h i1 i2 i3 j1 j2 j3 h12 h23 (by unfold al at a1 a2; omega) (by unfold al at a1 a2; omega)
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    exact h j1 j2 j3 i1 i2 i3 h12 h23 (by unfold al; omega) (by unfold al; omega)

theorem rn_iff {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : (∀ i, Monotone (x i)) ↔ RN (fun j i => x i j) := by
  constructor
  · intro h j1 j2 hj i; exact h i hj
  · intro h i j1 j2 hj; exact h j1 j2 hj i

theorem good_iff {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : Good x ↔ P CO true [1, 2] (fun j i => x i j) := by
  unfold Good P
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, CO,
    forall_const, true_and, implies_true, eq_self_iff_true, true_implies, uc_diag, uc_anti, rn_iff]
  tauto

theorem a_eq (N : ℕ) : a (N + 1) = Ac 4 3 COc true [1, 2] N := by
  rw [a, Ac, ← count_eq CO COc hCO true [1, 2] hU N]
  apply Finset.card_equiv (Equiv.piComm _)
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact good_iff x

def RL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
    70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 2593, 2594, 2602, 2603, 2611, 2612, 2620, 2621,
    2629, 2630, 2638, 2639, 2647, 2648, 2656, 2657, 2665, 2666, 2597, 2606, 2615, 2624, 2633, 2642,
    2651, 2660, 2669, 25923, 5188, 5189, 25926, 5191, 5192, 20748, 20751, 20757, 20760, 25950,
    5215, 5216, 25953, 5218, 5219, 20775, 20778, 20784, 20787, 25977, 5242, 5243, 25980, 5245,
    5246, 20802, 20805, 20811, 20814, 7781, 7808, 7835, 25927, 25935, 25936, 5201, 20761, 25954,
    25962, 25963, 5228, 20788, 25981, 25989, 25990, 5255, 20815, 51849, 51850, 51851, 10380, 10381,
    10382, 10383, 10384, 10385, 51858, 51859, 51860, 10389, 10390, 10391, 10392, 10393, 10394,
    41508, 41509, 41510, 41517, 41518, 41519, 41535, 41536, 41537, 41544, 41545, 41546, 54442,
    54443, 54451, 54452, 44101, 44102, 44110, 44111, 44128, 44129, 44137, 44138, 12974, 12983,
    31116, 31119, 31125, 31128, 36303, 36304, 15569, 31129, 51861, 51862, 51863, 51885, 51886,
    51887, 51888, 51889, 51890, 10419, 10420, 10421, 41547, 41548, 41549, 54478, 54479, 54455,
    54482, 44141, 72597, 72624, 31155, 62283, 31156, 82971, 82972, 82973, 82974, 82975, 82976,
    82977, 82978, 82979, 82998, 82999, 83000, 83001, 83002, 83003, 83004, 83005, 83006, 85564,
    85565, 85591, 85592, 85568, 85595, 108894, 88159, 88160, 108897, 88162, 88163, 108921, 88186,
    88187, 108924, 88189, 88190, 90752, 90779, 108898, 108925, 83007, 83008, 83009, 83010, 83011,
    83012, 83013, 83014, 83015, 85600, 85601, 85604, 103746, 103749, 108933, 108934, 88199, 124479,
    124480, 124481, 127072, 127073, 7777, 7778, 7804, 7805, 7831, 7832, 90748, 90749, 90775, 90776,
    7790, 7817, 7844, 18158, 90788, 36291, 15556, 15557, 36294, 15559, 15560, 18149, 36295, 36330,
    36331, 15596, 72585, 72594, 62244, 62253, 62271, 62280, 72621, 145215, 72598, 72625, 62284,
    124443, 124444, 124445, 124470, 124471, 124472, 127036, 127037, 127063, 127064, 132220, 132221,
    132247, 132248, 124482, 124483, 124484, 127076, 145218, 132260, 18145, 18146, 18185, 145179,
    145206, 145219]

def SI : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
    44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
    68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80], [81, 82, 4, 5, 7, 8, 83, 84, 13, 14, 16,
    17, 85, 86, 22, 23, 25, 26, 87, 88, 31, 32, 34, 35, 89, 90, 40, 41, 43, 44, 91, 92, 49, 50, 52,
    53, 93, 94, 58, 59, 61, 62, 95, 96, 67, 68, 70, 71, 97, 98, 76, 77, 79, 80], [82, 99, 8, 84,
    100, 17, 86, 101, 26, 88, 102, 35, 90, 103, 44, 92, 104, 53, 94, 105, 62, 96, 106, 71, 98, 107,
    80], [108, 109, 110, 111, 112, 113, 114, 13, 14, 115, 16, 17, 116, 22, 23, 117, 25, 26, 118,
    119, 120, 121, 122, 123, 124, 40, 41, 125, 43, 44, 126, 49, 50, 127, 52, 53, 128, 129, 130,
    131, 132, 133, 134, 67, 68, 135, 70, 71, 136, 76, 77, 137, 79, 80], [109, 110, 112, 113, 13,
    14, 16, 17, 22, 23, 25, 26, 119, 120, 122, 123, 40, 41, 43, 44, 49, 50, 52, 53, 129, 130, 132,
    133, 67, 68, 70, 71, 76, 77, 79, 80], [138, 113, 100, 17, 101, 26, 139, 123, 103, 44, 104, 53,
    140, 133, 106, 71, 107, 80], [111, 141, 113, 142, 143, 144, 117, 145, 26, 121, 146, 123, 147,
    148, 149, 127, 150, 53, 131, 151, 133, 152, 153, 154, 137, 155, 80], [141, 113, 143, 144, 145,
    26, 146, 123, 148, 149, 150, 53, 151, 133, 153, 154, 155, 80], [113, 144, 26, 123, 149, 53,
    133, 154, 80], [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171,
    172, 173, 174, 175, 176, 39, 40, 41, 42, 43, 44, 177, 178, 179, 48, 49, 50, 51, 52, 53, 180,
    181, 182, 66, 67, 68, 69, 70, 71, 183, 184, 185, 75, 76, 77, 78, 79, 80], [186, 187, 160, 161,
    163, 164, 188, 189, 169, 170, 172, 173, 190, 191, 40, 41, 43, 44, 192, 193, 49, 50, 52, 53,
    194, 195, 67, 68, 70, 71, 196, 197, 76, 77, 79, 80], [187, 198, 164, 189, 199, 173, 191, 103,
    44, 193, 104, 53, 195, 106, 71, 197, 107, 80], [200, 160, 161, 201, 163, 164, 202, 169, 170,
    203, 172, 173, 124, 40, 41, 125, 43, 44, 126, 49, 50, 127, 52, 53, 134, 67, 68, 135, 70, 71,
    136, 76, 77, 137, 79, 80], [160, 161, 163, 164, 169, 170, 172, 173, 40, 41, 43, 44, 49, 50, 52,
    53, 67, 68, 70, 71, 76, 77, 79, 80], [198, 164, 199, 173, 103, 44, 104, 53, 106, 71, 107, 80],
    [204, 205, 206, 203, 207, 173, 147, 148, 149, 127, 150, 53, 152, 153, 154, 137, 155, 80], [205,
    206, 207, 173, 148, 149, 150, 53, 153, 154, 155, 80], [206, 173, 149, 53, 154, 80], [165, 166,
    167, 208, 209, 210, 171, 172, 173, 211, 212, 213, 214, 215, 216, 217, 218, 219, 183, 184, 185,
    220, 221, 222, 78, 79, 80], [188, 189, 209, 210, 172, 173, 223, 224, 215, 216, 218, 219, 196,
    197, 221, 222, 79, 80], [189, 225, 173, 224, 226, 219, 197, 227, 80], [228, 209, 210, 203, 172,
    173, 229, 215, 216, 230, 218, 219, 231, 221, 222, 137, 79, 80], [209, 210, 172, 173, 215, 216,
    218, 219, 221, 222, 79, 80], [225, 173, 226, 219, 227, 80], [203, 207, 173, 230, 232, 219, 137,
    155, 80], [207, 173, 232, 219, 155, 80], [173, 219, 80], [233, 234, 235, 236, 237, 238, 239,
    240, 241, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 242, 243,
    244, 245, 246, 247, 248, 249, 250, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77,
    78, 79, 80], [251, 252, 237, 238, 240, 241, 89, 90, 40, 41, 43, 44, 91, 92, 49, 50, 52, 53,
    253, 254, 246, 247, 249, 250, 95, 96, 67, 68, 70, 71, 97, 98, 76, 77, 79, 80], [252, 255, 241,
    90, 103, 44, 92, 104, 53, 254, 256, 250, 96, 106, 71, 98, 107, 80], [257, 258, 259, 260, 261,
    262, 124, 40, 41, 125, 43, 44, 126, 49, 50, 127, 52, 53, 263, 264, 265, 266, 267, 268, 134, 67,
    68, 135, 70, 71, 136, 76, 77, 137, 79, 80], [258, 259, 261, 262, 40, 41, 43, 44, 49, 50, 52,
    53, 264, 265, 267, 268, 67, 68, 70, 71, 76, 77, 79, 80], [269, 262, 103, 44, 104, 53, 270, 268,
    106, 71, 107, 80], [260, 271, 262, 147, 148, 149, 127, 150, 53, 266, 272, 268, 152, 153, 154,
    137, 155, 80], [271, 262, 148, 149, 150, 53, 272, 268, 153, 154, 155, 80], [262, 149, 53, 268,
    154, 80], [174, 175, 176, 39, 40, 41, 42, 43, 44, 177, 178, 179, 48, 49, 50, 51, 52, 53, 180,
    181, 182, 66, 67, 68, 69, 70, 71, 183, 184, 185, 75, 76, 77, 78, 79, 80], [190, 191, 40, 41,
    43, 44, 192, 193, 49, 50, 52, 53, 194, 195, 67, 68, 70, 71, 196, 197, 76, 77, 79, 80], [191,
    103, 44, 193, 104, 53, 195, 106, 71, 197, 107, 80], [124, 40, 41, 125, 43, 44, 126, 49, 50,
    127, 52, 53, 134, 67, 68, 135, 70, 71, 136, 76, 77, 137, 79, 80], [40, 41, 43, 44, 49, 50, 52,
    53, 67, 68, 70, 71, 76, 77, 79, 80], [103, 44, 104, 53, 106, 71, 107, 80], [147, 148, 149, 127,
    150, 53, 152, 153, 154, 137, 155, 80], [148, 149, 150, 53, 153, 154, 155, 80], [149, 53, 154,
    80], [211, 212, 213, 214, 215, 216, 217, 218, 219, 183, 184, 185, 220, 221, 222, 78, 79, 80],
    [223, 224, 215, 216, 218, 219, 196, 197, 221, 222, 79, 80], [224, 226, 219, 197, 227, 80],
    [229, 215, 216, 230, 218, 219, 231, 221, 222, 137, 79, 80], [215, 216, 218, 219, 221, 222, 79,
    80], [226, 219, 227, 80], [230, 232, 219, 137, 155, 80], [232, 219, 155, 80], [219, 80], [242,
    243, 244, 245, 246, 247, 248, 249, 250, 273, 274, 275, 276, 277, 278, 279, 280, 281, 72, 73,
    74, 75, 76, 77, 78, 79, 80], [253, 254, 246, 247, 249, 250, 282, 283, 277, 278, 280, 281, 97,
    98, 76, 77, 79, 80], [254, 256, 250, 283, 284, 281, 98, 107, 80], [263, 264, 265, 266, 267,
    268, 285, 277, 278, 286, 280, 281, 136, 76, 77, 137, 79, 80], [264, 265, 267, 268, 277, 278,
    280, 281, 76, 77, 79, 80], [270, 268, 284, 281, 107, 80], [266, 272, 268, 287, 288, 289, 137,
    155, 80], [272, 268, 288, 289, 155, 80], [268, 289, 80], [290, 291, 292, 276, 277, 278, 279,
    280, 281, 183, 184, 185, 75, 76, 77, 78, 79, 80], [293, 294, 277, 278, 280, 281, 196, 197, 76,
    77, 79, 80], [294, 284, 281, 197, 107, 80], [285, 277, 278, 286, 280, 281, 136, 76, 77, 137,
    79, 80], [277, 278, 280, 281, 76, 77, 79, 80], [284, 281, 107, 80], [287, 288, 289, 137, 155,
    80], [288, 289, 155, 80], [289, 80], [183, 184, 185, 220, 221, 222, 78, 79, 80], [196, 197,
    221, 222, 79, 80], [197, 227, 80], [231, 221, 222, 137, 79, 80], [221, 222, 79, 80], [227, 80],
    [137, 155, 80], [155, 80], [80], [295, 296, 109, 110, 112, 113, 297, 298, 119, 120, 122, 123,
    299, 300, 129, 130, 132, 133], [296, 138, 113, 298, 139, 123, 300, 140, 133], [], [], [], [],
    [301, 302, 258, 259, 261, 262, 303, 304, 264, 265, 267, 268], [302, 269, 262, 304, 270, 268],
    [], [], [], [], [303, 304, 264, 265, 267, 268], [304, 270, 268], [], [], [], [], [138, 113,
    305, 144, 139, 123, 306, 149, 140, 133, 307, 154], [308, 206, 306, 149, 307, 154], [], [269,
    262, 306, 149, 270, 268, 307, 154], [306, 149, 307, 154], [], [270, 268, 309, 289], [309, 289],
    [], [310, 311, 312, 313, 314, 315, 200, 160, 161, 201, 163, 164, 202, 169, 170, 203, 172, 173],
    [311, 312, 314, 315, 160, 161, 163, 164, 169, 170, 172, 173], [316, 315, 198, 164, 199, 173],
    [313, 317, 315, 204, 205, 206, 203, 207, 173], [317, 315, 205, 206, 207, 173], [315, 206, 173],
    [200, 160, 161, 201, 163, 164, 202, 169, 170, 203, 172, 173, 124, 40, 41, 125, 43, 44, 126, 49,
    50, 127, 52, 53, 134, 67, 68, 135, 70, 71, 136, 76, 77, 137, 79, 80], [204, 205, 206, 203, 207,
    173, 147, 148, 149, 127, 150, 53, 152, 153, 154, 137, 155, 80], [228, 209, 210, 203, 172, 173,
    229, 215, 216, 230, 218, 219, 231, 221, 222, 137, 79, 80], [203, 207, 173, 230, 232, 219, 137,
    155, 80], [], [], [], [], [], [], [124, 40, 41, 125, 43, 44, 126, 49, 50, 127, 52, 53, 134, 67,
    68, 135, 70, 71, 136, 76, 77, 137, 79, 80], [147, 148, 149, 127, 150, 53, 152, 153, 154, 137,
    155, 80], [229, 215, 216, 230, 218, 219, 231, 221, 222, 137, 79, 80], [230, 232, 219, 137, 155,
    80], [], [], [], [], [], [], [285, 277, 278, 286, 280, 281, 136, 76, 77, 137, 79, 80], [287,
    288, 289, 137, 155, 80], [231, 221, 222, 137, 79, 80], [137, 155, 80], [316, 315, 308, 206],
    [], [], [317, 315, 205, 206, 207, 173], [204, 205, 206, 203, 207, 173, 318, 319, 320, 230, 232,
    219], [205, 206, 207, 173, 319, 320, 232, 219], [206, 173, 320, 219], [207, 173, 232, 219, 155,
    80], [], [318, 319, 320, 230, 232, 219], [319, 320, 232, 219], [320, 219], [232, 219, 155, 80],
    [], [], [], [], [155, 80], [321, 200, 201, 322, 202, 203, 323, 124, 125, 324, 126, 127, 325,
    134, 135, 326, 136, 137], [], [], [200, 160, 161, 201, 163, 164, 202, 169, 170, 203, 172, 173,
    124, 40, 41, 125, 43, 44, 126, 49, 50, 127, 52, 53, 134, 67, 68, 135, 70, 71, 136, 76, 77, 137,
    79, 80], [160, 161, 163, 164, 169, 170, 172, 173, 40, 41, 43, 44, 49, 50, 52, 53, 67, 68, 70,
    71, 76, 77, 79, 80], [198, 164, 199, 173, 103, 44, 104, 53, 106, 71, 107, 80], [204, 205, 206,
    203, 207, 173, 147, 148, 149, 127, 150, 53, 152, 153, 154, 137, 155, 80], [205, 206, 207, 173,
    148, 149, 150, 53, 153, 154, 155, 80], [206, 173, 149, 53, 154, 80], [322, 228, 203, 327, 229,
    230, 326, 231, 137], [], [], [228, 209, 210, 203, 172, 173, 229, 215, 216, 230, 218, 219, 231,
    221, 222, 137, 79, 80], [209, 210, 172, 173, 215, 216, 218, 219, 221, 222, 79, 80], [225, 173,
    226, 219, 227, 80], [203, 207, 173, 230, 232, 219, 137, 155, 80], [207, 173, 232, 219, 155,
    80], [173, 219, 80], [323, 124, 125, 324, 126, 127, 325, 134, 135, 326, 136, 137], [], [],
    [327, 229, 230, 326, 231, 137], [], [], [328, 285, 286, 326, 136, 137], [], [], [326, 231,
    137], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [308, 206, 306, 149, 307, 154],
    [], [200, 160, 161, 201, 163, 164, 202, 169, 170, 203, 172, 173, 124, 40, 41, 125, 43, 44, 126,
    49, 50, 127, 52, 53, 134, 67, 68, 135, 70, 71, 136, 76, 77, 137, 79, 80], [204, 205, 206, 203,
    207, 173, 147, 148, 149, 127, 150, 53, 152, 153, 154, 137, 155, 80], [228, 209, 210, 203, 172,
    173, 229, 215, 216, 230, 218, 219, 231, 221, 222, 137, 79, 80], [203, 207, 173, 230, 232, 219,
    137, 155, 80], [204, 205, 206, 203, 207, 173, 318, 319, 320, 230, 232, 219], [205, 206, 207,
    173, 319, 320, 232, 219], [206, 173, 320, 219], [207, 173, 232, 219, 155, 80], [228, 329, 203,
    207, 229, 330, 230, 232, 231, 331, 137, 155], [329, 207, 330, 232, 331, 155], [], [327, 229,
    230, 326, 231, 137], [], [], [229, 330, 230, 232, 231, 331, 137, 155], [330, 232, 331, 155],
    [], [230, 232, 219, 137, 155, 80], [232, 219, 155, 80], [219, 80], [231, 331, 137, 155], [331,
    155], [], [], [], [], [], [], [228, 329, 203, 207, 229, 330, 230, 232, 231, 331, 137, 155],
    [229, 330, 230, 232, 231, 331, 137, 155], [230, 232, 219, 137, 155, 80], [231, 331, 137, 155],
    [232, 219, 155, 80], [332, 333, 334, 174, 175, 176, 177, 178, 179, 335, 336, 337, 180, 181,
    182, 183, 184, 185], [338, 339, 190, 191, 192, 193, 340, 341, 194, 195, 196, 197], [339, 191,
    193, 341, 195, 197], [], [], [], [], [], [], [335, 336, 337, 290, 291, 292, 183, 184, 185],
    [340, 341, 293, 294, 196, 197], [341, 294, 197], [], [], [], [], [], [], [342, 343, 344, 345],
    [343, 345], [344, 345], [345], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [290, 291, 292, 346, 347, 348, 183, 184, 185, 220, 221, 222], [293, 294, 347, 348, 196,
    197, 221, 222], [294, 349, 197, 227], [350, 347, 348, 231, 221, 222], [347, 348, 221, 222],
    [349, 227], [], [], [], [], [], [351], [350, 347, 348, 231, 221, 222], [], [], [], [], [328,
    350, 326, 231], [], [], [], [], [352, 353, 311, 312, 314, 315], [353, 316, 315], [], [], [],
    [], [], [], [], [], [308, 206, 354, 320], [354, 320], [], [308, 206, 354, 320], [], [310, 311,
    312, 313, 314, 315, 200, 160, 161, 201, 163, 164, 202, 169, 170, 203, 172, 173], [311, 312,
    314, 315, 160, 161, 163, 164, 169, 170, 172, 173], [316, 315, 198, 164, 199, 173], [313, 317,
    315, 204, 205, 206, 203, 207, 173], [317, 315, 205, 206, 207, 173], [315, 206, 173], [316, 315,
    308, 206], [317, 315, 205, 206, 207, 173], [318, 319, 320, 230, 232, 219], [319, 320, 232,
    219], [320, 219], [321, 200, 201, 322, 202, 203, 323, 124, 125, 324, 126, 127, 325, 134, 135,
    326, 136, 137], [322, 228, 203, 327, 229, 230, 326, 231, 137], [323, 124, 125, 324, 126, 127,
    325, 134, 135, 326, 136, 137], [327, 229, 230, 326, 231, 137], [328, 285, 286, 326, 136, 137],
    [326, 231, 137], [327, 229, 230, 326, 231, 137], [328, 350, 326, 231], [329, 207, 330, 232,
    331, 155], [330, 232, 331, 155], [331, 155], [355, 323, 324, 356, 325, 326], [], [], [356, 328,
    326], [], [], [], [], [], [], [], [], [], [], [350, 357, 231, 331], [357, 331], [], [], [350,
    357, 231, 331], [], [352, 353, 311, 312, 314, 315], [353, 316, 315], [354, 320], [355, 323,
    324, 356, 325, 326], [356, 328, 326], [357, 331]]

def BL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 3, 9, 10, 11, 12, 13, 14, 15, 16, 6, 17, 18, 14, 19,
    20, 21, 22, 23, 1, 24, 25, 9, 26, 27, 17, 28, 29, 4, 26, 27, 12, 30, 31, 19, 32, 33, 7, 28, 34,
    15, 32, 35, 22, 36, 37, 2, 25, 38, 10, 27, 39, 18, 34, 40, 5, 27, 39, 13, 31, 41, 20, 35, 42,
    8, 29, 40, 16, 33, 42, 23, 37, 43, 44, 45, 46, 46, 46, 46, 47, 48, 46, 46, 46, 46, 48, 49, 46,
    46, 46, 46, 50, 51, 46, 52, 53, 46, 54, 55, 46, 56, 57, 58, 59, 60, 61, 11, 14, 14, 21, 46, 46,
    46, 46, 46, 46, 12, 19, 15, 22, 46, 46, 46, 46, 46, 46, 13, 20, 16, 23, 62, 46, 46, 60, 63, 64,
    65, 22, 46, 66, 67, 68, 36, 46, 46, 46, 46, 37, 56, 46, 46, 11, 12, 13, 14, 15, 16, 59, 46, 46,
    14, 19, 20, 21, 22, 23, 57, 46, 46, 60, 46, 46, 58, 46, 46, 61, 46, 46, 46, 46, 46, 46, 46, 46,
    46, 46, 46, 46, 46, 46, 51, 46, 11, 14, 14, 21, 63, 64, 65, 22, 63, 66, 46, 60, 46, 46, 64, 67,
    46, 22, 36, 37, 65, 68, 46, 46, 46, 46, 46, 46, 63, 64, 22, 65, 36, 44, 47, 48, 46, 46, 46, 46,
    46, 46, 45, 48, 49, 46, 46, 46, 46, 46, 46, 54, 55, 55, 69, 46, 46, 46, 46, 46, 46, 46, 46, 46,
    46, 46, 46, 46, 46, 46, 46, 46, 46, 50, 52, 54, 51, 53, 55, 46, 46, 46, 46, 46, 69, 51, 46, 46,
    46, 46, 62, 46, 46, 46, 46, 70, 71, 46, 46, 46, 46, 46, 46, 46, 46, 72, 73, 46, 72, 46, 56, 57,
    58, 59, 60, 61, 62, 60, 66, 67, 68, 56, 59, 57, 60, 58, 61, 60, 62, 66, 67, 68, 70, 46, 46, 71,
    46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 72, 73, 46, 46, 72, 46, 70, 71, 73, 70, 71, 73]

def BS : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 3, 9, 10, 11, 12, 13, 14, 15, 16, 6, 17, 18,
    14, 19, 20, 21, 22, 23, 1, 24, 25, 9, 26, 27, 17, 28, 29, 4, 26, 27, 12, 30, 31, 19, 32, 33, 7,
    28, 34, 15, 32, 35, 22, 36, 37, 2, 25, 38, 10, 27, 39, 18, 34, 40, 5, 27, 39, 13, 31, 41, 20,
    35, 42, 8, 29, 40, 16, 33, 42, 23, 37, 43], [44, 45, 4, 5, 7, 8, 46, 46, 12, 13, 15, 16, 46,
    46, 19, 20, 22, 23, 47, 48, 26, 27, 28, 29, 46, 46, 30, 31, 32, 33, 46, 46, 32, 35, 36, 37, 48,
    49, 27, 39, 34, 40, 46, 46, 31, 41, 35, 42, 46, 46, 33, 42, 37, 43], [45, 50, 8, 46, 51, 16,
    46, 46, 23, 48, 52, 29, 46, 53, 33, 46, 46, 37, 49, 54, 40, 46, 55, 42, 46, 46, 43], [56, 57,
    58, 59, 60, 61, 11, 12, 13, 14, 15, 16, 14, 19, 20, 21, 22, 23, 46, 46, 46, 46, 46, 46, 12, 30,
    31, 19, 32, 33, 15, 32, 35, 22, 36, 37, 46, 46, 46, 46, 46, 46, 13, 31, 41, 20, 35, 42, 16, 33,
    42, 23, 37, 43], [57, 58, 60, 61, 12, 13, 15, 16, 19, 20, 22, 23, 46, 46, 46, 46, 30, 31, 32,
    33, 32, 35, 36, 37, 46, 46, 46, 46, 31, 41, 35, 42, 33, 42, 37, 43], [62, 61, 51, 16, 46, 23,
    46, 46, 53, 33, 46, 37, 46, 46, 55, 42, 46, 43], [59, 60, 61, 63, 64, 65, 21, 22, 23, 46, 46,
    46, 66, 67, 68, 22, 36, 37, 46, 46, 46, 46, 46, 46, 23, 37, 43], [60, 61, 64, 65, 22, 23, 46,
    46, 67, 68, 36, 37, 46, 46, 46, 46, 37, 43], [61, 65, 23, 46, 68, 37, 46, 46, 43], [46, 46, 12,
    13, 15, 16, 46, 46, 19, 20, 22, 23, 46, 46, 30, 31, 32, 33, 46, 46, 32, 35, 36, 37, 46, 46, 31,
    41, 35, 42, 46, 46, 33, 42, 37, 43], [46, 51, 16, 46, 46, 23, 46, 53, 33, 46, 46, 37, 46, 55,
    42, 46, 46, 43], [11, 12, 13, 14, 15, 16, 14, 19, 20, 21, 22, 23, 12, 30, 31, 19, 32, 33, 15,
    32, 35, 22, 36, 37, 13, 31, 41, 20, 35, 42, 16, 33, 42, 23, 37, 43], [12, 13, 15, 16, 19, 20,
    22, 23, 30, 31, 32, 33, 32, 35, 36, 37, 31, 41, 35, 42, 33, 42, 37, 43], [51, 16, 46, 23, 53,
    33, 46, 37, 55, 42, 46, 43], [63, 64, 65, 21, 22, 23, 66, 67, 68, 22, 36, 37, 46, 46, 46, 23,
    37, 43], [64, 65, 22, 23, 67, 68, 36, 37, 46, 46, 37, 43], [65, 23, 68, 37, 46, 43], [46, 46,
    66, 46, 22, 23, 46, 46, 67, 46, 36, 37, 46, 46, 68, 46, 37, 43], [46, 46, 23, 46, 46, 37, 46,
    46, 43], [66, 46, 22, 23, 67, 46, 36, 37, 68, 46, 37, 43], [46, 23, 46, 37, 46, 43], [21, 22,
    23, 22, 36, 37, 23, 37, 43], [22, 23, 36, 37, 37, 43], [23, 37, 43], [54, 55, 46, 46, 46, 46,
    46, 46, 30, 31, 32, 33, 46, 46, 32, 35, 36, 37, 55, 69, 46, 46, 46, 46, 46, 46, 31, 41, 35, 42,
    46, 46, 33, 42, 37, 43], [55, 46, 46, 46, 53, 33, 46, 46, 37, 69, 46, 46, 46, 55, 42, 46, 46,
    43], [46, 46, 46, 46, 30, 31, 32, 33, 32, 35, 36, 37, 46, 46, 46, 46, 31, 41, 35, 42, 33, 42,
    37, 43], [46, 46, 53, 33, 46, 37, 46, 46, 55, 42, 46, 43], [46, 46, 67, 68, 36, 37, 46, 46, 46,
    46, 37, 43], [46, 68, 37, 46, 46, 43], [30, 31, 32, 33, 32, 35, 36, 37, 31, 41, 35, 42, 33, 42,
    37, 43], [53, 33, 46, 37, 55, 42, 46, 43], [67, 68, 36, 37, 46, 46, 37, 43], [68, 37, 46, 43],
    [46, 46, 37, 46, 46, 43], [46, 37, 46, 43], [36, 37, 37, 43], [37, 43], [69, 46, 46, 46, 69,
    46, 46, 46, 43], [46, 46, 69, 46, 46, 43], [46, 46, 43], [69, 46, 46, 43], [46, 43], [43], [70,
    71, 57, 58, 60, 61, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46], [71, 62, 61, 46, 46, 46,
    46, 46, 46], [], [46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46], [46, 46, 46, 46, 46, 46],
    [46, 46, 46], [62, 61, 72, 65, 46, 46, 73, 68, 46, 46, 46, 46], [72, 65, 73, 68, 46, 46], [46,
    46, 73, 68, 46, 46, 46, 46], [73, 68, 46, 46], [46, 46, 46, 46], [46, 46], [56, 57, 58, 59, 60,
    61, 11, 12, 13, 14, 15, 16, 14, 19, 20, 21, 22, 23], [57, 58, 60, 61, 12, 13, 15, 16, 19, 20,
    22, 23], [62, 61, 51, 16, 46, 23], [59, 60, 61, 63, 64, 65, 21, 22, 23], [60, 61, 64, 65, 22,
    23], [61, 65, 23], [62, 61, 72, 65], [63, 64, 65, 21, 22, 23, 66, 67, 68, 22, 36, 37], [64, 65,
    22, 23, 67, 68, 36, 37], [65, 23, 68, 37], [66, 67, 68, 22, 36, 37], [67, 68, 36, 37], [68,
    37], [46], [70, 71, 57, 58, 60, 61], [71, 62, 61], [72, 65, 73, 68], [73, 68]]

def VT : List (List ℕ) := [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [81, 54, 27, 54, 36, 18, 27, 18, 9, 36,
    18, 36, 24, 12, 18, 12, 6, 18, 9, 12, 6, 9, 6, 3, 36, 18, 24, 12, 12, 6, 16, 8, 8, 4, 6, 4, 4,
    2, 9, 6, 3, 4, 2, 1, 18, 9, 0, 12, 6, 3, 12, 6, 8, 4, 4, 2, 18, 12, 6, 9, 6, 3, 4, 12, 8, 4, 6,
    4, 2, 1, 6, 3, 4, 2], [1296, 378, 90, 378, 189, 37, 90, 45, 15, 162, 30, 324, 162, 30, 72, 36,
    12, 30, 6, 30, 6, 36, 18, 6, 90, 18, 81, 15, 15, 5, 81, 15, 15, 5, 3, 3, 9, 3, 3, 2, 1, 2, 1,
    1, 36, 10, 0, 0, 0, 0, 19, 12, 4, 4, 0, 0, 216, 108, 22, 60, 30, 10, 15, 66, 33, 11, 24, 12, 4,
    0, 36, 10, 12, 4], [5880, 946, 98, 1727, 647, 69, 350, 140, 35, 477, 44, 1281, 477, 44, 250,
    100, 25, 80, 10, 80, 10, 100, 40, 10, 177, 14, 177, 14, 32, 8, 177, 14, 32, 8, 4, 4, 16, 4, 1,
    1, 1, 1, 1, 1, 216, 35, 0, 0, 0, 0, 56, 31, 8, 8, 0, 0, 1250, 470, 55, 270, 108, 27, 48, 240,
    96, 24, 70, 28, 7, 0, 216, 35, 31, 8], [19608, 2500, 231, 5954, 1767, 163, 1095, 365, 73, 1107,
    88, 3774, 1107, 88, 690, 230, 46, 180, 15, 180, 15, 225, 75, 15, 321, 22, 321, 22, 60, 12, 321,
    22, 60, 12, 5, 5, 25, 5, 1, 1, 1, 1, 1, 1, 911, 110, 0, 0, 0, 0, 145, 70, 15, 15, 0, 0, 4847,
    1446, 141, 915, 305, 61, 130, 675, 225, 45, 165, 55, 11, 0, 911, 110, 70, 15], [57387, 6147,
    521, 17164, 4267, 356, 2898, 828, 138, 2314, 165, 9449, 2314, 165, 1617, 462, 77, 357, 21, 357,
    21, 441, 126, 21, 558, 34, 558, 34, 102, 17, 558, 34, 102, 17, 6, 6, 36, 6, 1, 1, 1, 1, 1, 1,
    2974, 301, 0, 0, 0, 0, 332, 141, 26, 26, 0, 0, 14850, 3709, 322, 2541, 726, 121, 306, 1596,
    456, 76, 336, 96, 16, 0, 2974, 301, 141, 26], [151010, 14088, 1105, 43407, 9349, 717, 6748,
    1687, 241, 4471, 290, 21138, 4471, 290, 3360, 840, 120, 644, 28, 644, 28, 784, 196, 28, 928,
    51, 928, 51, 161, 23, 928, 51, 161, 23, 7, 7, 49, 7, 1, 1, 1, 1, 1, 1, 8153, 728, 0, 0, 0, 0,
    686, 259, 42, 42, 0, 0, 38936, 8421, 666, 6104, 1526, 218, 644, 3332, 833, 119, 616, 154, 22,
    0, 8153, 728, 259, 42], [363392, 30194, 2202, 99226, 18927, 1343, 14220, 3160, 395, 8096, 481,
    43355, 8096, 481, 6372, 1416, 177, 1080, 36, 1080, 36, 1296, 288, 36, 1479, 74, 1479, 74, 240,
    30, 1479, 74, 240, 30, 8, 8, 64, 8, 1, 1, 1, 1, 1, 1, 19712, 1590, 0, 0, 0, 0, 1304, 442, 64,
    64, 0, 0, 91130, 17448, 1269, 13140, 2920, 365, 1240, 6336, 1408, 176, 1044, 232, 29, 0, 19712,
    1590, 442, 64], [810436, 60911, 4143, 209154, 35879, 2364, 27675, 5535, 615, 13877, 759, 82882,
    13877, 759, 11250, 2250, 250, 1710, 45, 1710, 45, 2025, 405, 45, 2267, 104, 2267, 104, 342, 38,
    2267, 104, 342, 38, 9, 9, 81, 9, 1, 1, 1, 1, 1, 1, 43304, 3195, 0, 0, 0, 0, 2316, 711, 93, 93,
    0, 0, 195277, 33612, 2260, 25965, 5193, 577, 2223, 11205, 2241, 249, 1665, 333, 37, 0, 43304,
    3195, 711, 93], [1693423, 116455, 7406, 412329, 64339, 3948, 50490, 9180, 918, 22697, 1148,
    149445, 22697, 1148, 18755, 3410, 341, 2585, 55, 2585, 55, 3025, 550, 55, 3356, 142, 3356, 142,
    470, 47, 3356, 142, 470, 47, 10, 10, 100, 10, 1, 1, 1, 1, 1, 1, 88141, 5995, 0, 0, 0, 0, 3890,
    1090, 130, 130, 0, 0, 389632, 60983, 3806, 47905, 8710, 871, 3760, 18700, 3400, 340, 2530, 460,
    46, 0, 88141, 5995, 1090, 130], [3344982, 212349, 12656, 768387, 110029, 6306, 87318, 14553,
    1323, 35659, 1675, 256480, 35659, 1675, 29832, 4972, 452, 3762, 66, 3762, 66, 4356, 726, 66,
    4818, 189, 4818, 189, 627, 57, 4818, 189, 627, 57, 11, 11, 121, 11, 1, 1, 1, 1, 1, 1, 168506,
    10626, 0, 0, 0, 0, 6237, 1606, 176, 176, 0, 0, 732728, 105211, 6117, 83556, 13926, 1266, 6061,
    29766, 4961, 451, 3696, 616, 56, 0, 168506, 10626, 1606, 176], [6292120, 371347, 20790,
    1364793, 180631, 9697, 144378, 22212, 1851, 54111, 2370, 421989, 54111, 2370, 45630, 7020, 585,
    5304, 78, 5304, 78, 6084, 936, 78, 6733, 246, 6733, 246, 816, 68, 6733, 246, 816, 68, 12, 12,
    144, 12, 1, 1, 1, 1, 1, 1, 305652, 17953, 0, 0, 0, 0, 9616, 2289, 232, 232, 0, 0, 1310682,
    173898, 9451, 139074, 21396, 1783, 9384, 45552, 7008, 584, 5226, 804, 67, 0, 305652, 17953,
    2289, 232], [11340202, 625790, 32987, 2325770, 286199, 14433, 229775, 32825, 2525, 79671, 3266,
    669486, 79671, 3266, 67522, 9646, 742, 7280, 91, 7280, 91, 8281, 1183, 91, 9189, 314, 9189,
    314, 1040, 80, 9189, 314, 1040, 80, 13, 13, 169, 13, 1, 1, 1, 1, 1, 1, 530133, 29120, 0, 0, 0,
    0, 14339, 3172, 299, 299, 0, 0, 2246099, 277010, 14119, 222495, 31785, 2445, 14040, 67431,
    9633, 741, 7189, 1027, 79, 0, 530133, 29120, 3172, 299], [19682181, 1020439, 50763, 3822986,
    439611, 20884, 353850, 47180, 3370, 114252, 4399, 1029033, 114252, 4399, 97125, 12950, 925,
    9765, 105, 9765, 105, 11025, 1470, 105, 12282, 394, 12282, 394, 1302, 93, 12282, 394, 1302, 93,
    14, 14, 196, 14, 1, 1, 1, 1, 1, 1, 884612, 45605, 0, 0, 0, 0, 20776, 4291, 378, 378, 0, 0,
    3708734, 427329, 20490, 344085, 45878, 3277, 20398, 97020, 12936, 924, 9660, 1288, 92, 0,
    884612, 45605, 4291, 378], [33037788, 1615830, 76031, 6088159, 657061, 29483, 529560, 66195,
    4413, 160087, 5808, 1538366, 160087, 5808, 136320, 17040, 1136, 12840, 120, 12840, 120, 14400,
    1800, 120, 16116, 487, 16116, 487, 1605, 107, 16116, 487, 1605, 107, 15, 15, 225, 15, 1, 1, 1,
    1, 1, 1, 1427191, 69280, 0, 0, 0, 0, 29360, 5685, 470, 470, 0, 0, 5928072, 640945, 28996,
    516720, 64590, 4306, 28890, 136200, 17025, 1135, 12720, 1590, 106, 0, 1427191, 69280, 5685,
    470], [53827802, 2492196, 111166, 9427740, 958591, 40731, 772888, 90928, 5683, 219754, 7535,
    2244111, 219754, 7535, 187272, 22032, 1377, 16592, 136, 16592, 136, 18496, 2176, 136, 20803,
    594, 20803, 594, 1952, 122, 20803, 594, 1952, 122, 16, 16, 256, 16, 1, 1, 1, 1, 1, 1, 2235308,
    102476, 0, 0, 0, 0, 40592, 7396, 576, 576, 0, 0, 9207986, 937788, 40137, 756296, 88976, 5561,
    40016, 187136, 22016, 1376, 16456, 1936, 121, 0, 2235308, 102476, 7396, 576]]

def IL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
    70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80]

def AV : List ℕ := [0, 81, 1296, 5880, 19608, 57387, 151010, 363392, 810436, 1693423, 3344982,
    6292120, 11340202, 19682181, 33037788, 53827802, 85388930]

def LC : List (ℕ × ℕ) := [(1, 9), (36, 7), (126, 5), (84, 3), (9, 1)]

def RC : List (ℕ × ℕ) := [(9, 8), (84, 6), (126, 4), (36, 2), (1, 0)]

set_option maxRecDepth 100000 in
theorem h1_0 : (List.range' 0 50).all (c1 4 3 COc true [1, 2] RL SI 358) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_1 : (List.range' 50 50).all (c1 4 3 COc true [1, 2] RL SI 358) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_2 : (List.range' 100 50).all (c1 4 3 COc true [1, 2] RL SI 358) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_3 : (List.range' 150 50).all (c1 4 3 COc true [1, 2] RL SI 358) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_4 : (List.range' 200 50).all (c1 4 3 COc true [1, 2] RL SI 358) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_5 : (List.range' 250 50).all (c1 4 3 COc true [1, 2] RL SI 358) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_6 : (List.range' 300 50).all (c1 4 3 COc true [1, 2] RL SI 358) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_7 : (List.range' 350 8).all (c1 4 3 COc true [1, 2] RL SI 358) = true := by
  decide +kernel

theorem h1 : chk1 4 3 COc true [1, 2] RL SI 358 = true :=
  chk1_of 4 3 COc true [1, 2] RL SI 358 (all_split (c1 4 3 COc true [1, 2] RL SI 358) 0 350 8 (all_split (c1 4 3 COc true [1, 2] RL SI 358) 0 300 50 (all_split (c1 4 3 COc true [1, 2] RL SI 358) 0 250 50 (all_split (c1 4 3 COc true [1, 2] RL SI 358) 0 200 50 (all_split (c1 4 3 COc true [1, 2] RL SI 358) 0 150 50 (all_split (c1 4 3 COc true [1, 2] RL SI 358) 0 100 50 (all_split (c1 4 3 COc true [1, 2] RL SI 358) 0 50 50 h1_0 h1_1) h1_2) h1_3) h1_4) h1_5) h1_6) h1_7)


set_option maxRecDepth 100000 in
theorem h2_0 : (List.range' 0 48).all (c2 SI BL BS 74) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_1 : (List.range' 48 48).all (c2 SI BL BS 74) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_2 : (List.range' 96 48).all (c2 SI BL BS 74) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_3 : (List.range' 144 48).all (c2 SI BL BS 74) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_4 : (List.range' 192 48).all (c2 SI BL BS 74) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_5 : (List.range' 240 48).all (c2 SI BL BS 74) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_6 : (List.range' 288 48).all (c2 SI BL BS 74) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_7 : (List.range' 336 22).all (c2 SI BL BS 74) = true := by
  decide +kernel

theorem h2 : chk2 SI BL BS 358 74 = true :=
  chk2_of SI BL BS 358 74 (all_split (c2 SI BL BS 74) 0 336 22 (all_split (c2 SI BL BS 74) 0 288 48 (all_split (c2 SI BL BS 74) 0 240 48 (all_split (c2 SI BL BS 74) 0 192 48 (all_split (c2 SI BL BS 74) 0 144 48 (all_split (c2 SI BL BS 74) 0 96 48 (all_split (c2 SI BL BS 74) 0 48 48 h2_0 h2_1) h2_2) h2_3) h2_4) h2_5) h2_6) h2_7)


set_option maxRecDepth 100000 in
theorem hV : chkV BS VT 74 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hI : chkI VT 74 LC RC 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem h3 : chk3 4 3 COc RL 358 IL = true := by decide +kernel

theorem hJ : ∀ p ∈ LC ++ RC, 4 + p.2 ≤ 15 := by decide

set_option maxRecDepth 100000 in
theorem hAV : ∀ N ≤ 15, (IL.map (fun t => gL (VT.getD N []) (gL BL t))).sum = gL AV (N + 1) := by
  decide +kernel

theorem hid (M : ℕ) : Lin LC (Ac 4 3 COc true [1, 2]) (4 + M) = Lin RC (Ac 4 3 COc true [1, 2]) (4 + M) :=
  A_ident 4 3 COc true [1, 2] RL SI BL BS VT 358 74 15 h1 h2 hV LC RC 4 hI hJ IL h3 M

theorem hval (N : ℕ) (hN : N ≤ 15) : a (N + 1) = gL AV (N + 1) := by
  rw [a_eq, A_val 4 3 COc true [1, 2] RL SI BL BS VT 358 74 15 h1 h2 hV IL h3 N hN, hAV N hN]

/-! The rest is about any sequence with these properties (kept abstract for the kernel). -/

theorem recN (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (4 + M) = Lin RC A (4 + M)) (hval : ∀ N ≤ 15, f (N + 1) = gL AV (N + 1)) (M : ℕ) : 1 * f (M + 14) + 36 * f (M + 14 - 2) + 126 * f (M + 14 - 4) + 84 * f (M + 14 - 6) + 9 * f (M + 14 - 8) = 9 * f (M + 14 - 1) + 84 * f (M + 14 - 3) + 126 * f (M + 14 - 5) + 36 * f (M + 14 - 7) + 1 * f (M + 14 - 9) := by
  have h := hid M
  simp only [LC, RC, Lin, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [show M + 14 - 1 = 4 + M + 8 + 1 by omega, ha (4 + M + 8), show M + 14 - 2 = 4 + M + 7 + 1 by omega, ha (4 + M + 7), show M + 14 - 3 = 4 + M + 6 + 1 by omega, ha (4 + M + 6), show M + 14 - 4 = 4 + M + 5 + 1 by omega, ha (4 + M + 5), show M + 14 - 5 = 4 + M + 4 + 1 by omega, ha (4 + M + 4), show M + 14 - 6 = 4 + M + 3 + 1 by omega, ha (4 + M + 3), show M + 14 - 7 = 4 + M + 2 + 1 by omega, ha (4 + M + 2), show M + 14 - 8 = 4 + M + 1 + 1 by omega, ha (4 + M + 1), show M + 14 - 9 = 4 + M + 1 by omega, ha (4 + M), show M + 14 = 4 + M + 9 + 1 by omega, ha (4 + M + 9)]
  omega

theorem recZ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (4 + M) = Lin RC A (4 + M)) (hval : ∀ N ≤ 15, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 12 < n) : (f n : ℤ) = 9 * f (n - 1) - 36 * f (n - 2) + 84 * f (n - 3) - 126 * f (n - 4) + 126 * f (n - 5) - 84 * f (n - 6) + 36 * f (n - 7) - 9 * f (n - 8) + f (n - 9) := by
  have v1 : f 1 = 81 := hval 0 (by norm_num)
  have v2 : f 2 = 1296 := hval 1 (by norm_num)
  have v3 : f 3 = 5880 := hval 2 (by norm_num)
  have v4 : f 4 = 19608 := hval 3 (by norm_num)
  have v5 : f 5 = 57387 := hval 4 (by norm_num)
  have v6 : f 6 = 151010 := hval 5 (by norm_num)
  have v7 : f 7 = 363392 := hval 6 (by norm_num)
  have v8 : f 8 = 810436 := hval 7 (by norm_num)
  have v9 : f 9 = 1693423 := hval 8 (by norm_num)
  have v10 : f 10 = 3344982 := hval 9 (by norm_num)
  have v11 : f 11 = 6292120 := hval 10 (by norm_num)
  have v12 : f 12 = 11340202 := hval 11 (by norm_num)
  have v13 : f 13 = 19682181 := hval 12 (by norm_num)
  have v14 : f 14 = 33037788 := hval 13 (by norm_num)
  have v15 : f 15 = 53827802 := hval 14 (by norm_num)
  have v16 : f 16 = 85388930 := hval 15 (by norm_num)
  by_cases hb : 14 ≤ n
  · obtain ⟨M, rfl⟩ : ∃ M, n = M + 14 := ⟨n - 14, by omega⟩
    have := recN f A ha hid hval M
    omega
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]

theorem recQ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (4 + M) = Lin RC A (4 + M)) (hval : ∀ N ≤ 15, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 12 < n) : (f n : ℚ) = 9 * (f (n - 1) : ℚ) - 36 * (f (n - 2) : ℚ) + 84 * (f (n - 3) : ℚ) - 126 * (f (n - 4) : ℚ) + 126 * (f (n - 5) : ℚ) - 84 * (f (n - 6) : ℚ) + 36 * (f (n - 7) : ℚ) - 9 * (f (n - 8) : ℚ) + (f (n - 9) : ℚ) := by
  have := recZ f A ha hid hval n hn
  exact_mod_cast this

theorem poly (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (4 + M) = Lin RC A (4 + M)) (hval : ∀ N ≤ 15, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 3 < n) : (f n : ℚ) = (41/4032) * (n : ℚ) ^ 8 + (9/112) * (n : ℚ) ^ 7 + (239/288) * (n : ℚ) ^ 6 + (109/24) * (n : ℚ) ^ 5 + (12079/576) * (n : ℚ) ^ 4 + (39/16) * (n : ℚ) ^ 3 + (310151/1008) * (n : ℚ) ^ 2 - (21299/84) * (n : ℚ) + 142 := by
  have v1 : f 1 = 81 := hval 0 (by norm_num)
  have v2 : f 2 = 1296 := hval 1 (by norm_num)
  have v3 : f 3 = 5880 := hval 2 (by norm_num)
  have v4 : f 4 = 19608 := hval 3 (by norm_num)
  have v5 : f 5 = 57387 := hval 4 (by norm_num)
  have v6 : f 6 = 151010 := hval 5 (by norm_num)
  have v7 : f 7 = 363392 := hval 6 (by norm_num)
  have v8 : f 8 = 810436 := hval 7 (by norm_num)
  have v9 : f 9 = 1693423 := hval 8 (by norm_num)
  have v10 : f 10 = 3344982 := hval 9 (by norm_num)
  have v11 : f 11 = 6292120 := hval 10 (by norm_num)
  have v12 : f 12 = 11340202 := hval 11 (by norm_num)
  have v13 : f 13 = 19682181 := hval 12 (by norm_num)
  have v14 : f 14 = 33037788 := hval 13 (by norm_num)
  have v15 : f 15 = 53827802 := hval 14 (by norm_num)
  have v16 : f 16 = 85388930 := hval 15 (by norm_num)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hs : n ≤ 12
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    rw [recQ f A ha hid hval (k + 9) (by omega), ih (k + 9 - 1) (by omega) (by omega), ih (k + 9 - 2) (by omega) (by omega), ih (k + 9 - 3) (by omega) (by omega), ih (k + 9 - 4) (by omega) (by omega), ih (k + 9 - 5) (by omega) (by omega), ih (k + 9 - 6) (by omega) (by omega), ih (k + 9 - 7) (by omega) (by omega), ih (k + 9 - 8) (by omega) (by omega), ih (k + 9 - 9) (by omega) (by omega)]
    simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega, show k + 9 - 9 = k + 0 by omega]
    push_cast
    ring

theorem gf (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (4 + M) = Lin RC A (4 + M)) (hval : ∀ N ≤ 15, f (N + 1) = gL AV (N + 1)) : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 9 =
    X * (81 + 567 * X - 2868 * X ^ 2 + 6540 * X ^ 3 - 6063 * X ^ 4 - 415 * X ^ 5 + 7550 * X ^ 6 - 8564 * X ^ 7 + 4918 * X ^ 8 - 1584 * X ^ 9 + 262 * X ^ 10 - 14 * X ^ 11) := by
  have v1 : f 1 = 81 := hval 0 (by norm_num)
  have v2 : f 2 = 1296 := hval 1 (by norm_num)
  have v3 : f 3 = 5880 := hval 2 (by norm_num)
  have v4 : f 4 = 19608 := hval 3 (by norm_num)
  have v5 : f 5 = 57387 := hval 4 (by norm_num)
  have v6 : f 6 = 151010 := hval 5 (by norm_num)
  have v7 : f 7 = 363392 := hval 6 (by norm_num)
  have v8 : f 8 = 810436 := hval 7 (by norm_num)
  have v9 : f 9 = 1693423 := hval 8 (by norm_num)
  have v10 : f 10 = 3344982 := hval 9 (by norm_num)
  have v11 : f 11 = 6292120 := hval 10 (by norm_num)
  have v12 : f 12 = 11340202 := hval 11 (by norm_num)
  have v13 : f 13 = 19682181 := hval 12 (by norm_num)
  have v14 : f 14 = 33037788 := hval 13 (by norm_num)
  have v15 : f 15 = 53827802 := hval 14 (by norm_num)
  have v16 : f 16 = 85388930 := hval 15 (by norm_num)
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hF
  have hmul : F * (1 - X) ^ 9 = F - C (9 : ℚ) * (X ^ 1 * F) + C (36 : ℚ) * (X ^ 2 * F) - C (84 : ℚ) * (X ^ 3 * F) + C (126 : ℚ) * (X ^ 4 * F) - C (126 : ℚ) * (X ^ 5 * F) + C (84 : ℚ) * (X ^ 6 * F) - C (36 : ℚ) * (X ^ 7 * F) + C (9 : ℚ) * (X ^ 8 * F) - X ^ 9 * F := by
    (try simp only [map_ofNat]); ring
  have hnum : (X * (81 + 567 * X - 2868 * X ^ 2 + 6540 * X ^ 3 - 6063 * X ^ 4 - 415 * X ^ 5 + 7550 * X ^ 6 - 8564 * X ^ 7 + 4918 * X ^ 8 - 1584 * X ^ 9 + 262 * X ^ 10 - 14 * X ^ 11) : PowerSeries ℚ) = C (81 : ℚ) * X ^ 1 + C (567 : ℚ) * X ^ 2 - C (2868 : ℚ) * X ^ 3 + C (6540 : ℚ) * X ^ 4 - C (6063 : ℚ) * X ^ 5 - C (415 : ℚ) * X ^ 6 + C (7550 : ℚ) * X ^ 7 - C (8564 : ℚ) * X ^ 8 + C (4918 : ℚ) * X ^ 9 - C (1584 : ℚ) * X ^ 10 + C (262 : ℚ) * X ^ 11 - C (14 : ℚ) * X ^ 12 := by
    (try simp only [map_ofNat]); ring
  rw [hmul, hnum]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, hF, coeff_mk]
  by_cases hn : 13 ≤ n
  · simp only [if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_pos (show 9 ≤ n by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega),
      if_neg (show n ≠ 9 by omega),
      if_neg (show n ≠ 10 by omega),
      if_neg (show n ≠ 11 by omega),
      if_neg (show n ≠ 12 by omega),
      if_neg (show n ≠ 0 by omega),
      if_neg (show n - 1 ≠ 0 by omega),
      if_neg (show n - 2 ≠ 0 by omega),
      if_neg (show n - 3 ≠ 0 by omega),
      if_neg (show n - 4 ≠ 0 by omega),
      if_neg (show n - 5 ≠ 0 by omega),
      if_neg (show n - 6 ≠ 0 by omega),
      if_neg (show n - 7 ≠ 0 by omega),
      if_neg (show n - 8 ≠ 0 by omega),
      if_neg (show n - 9 ≠ 0 by omega),
      mul_zero, sub_zero, add_zero, mul_one, neg_zero]
    rw [recQ f A ha hid hval n (by omega)]
    ring
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16]

theorem final (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (4 + M) = Lin RC A (4 + M)) (hval : ∀ N ≤ 15, f (N + 1) = gL AV (N + 1)) :
    (∀ n : ℕ, 3 < n → (f n : ℚ) = (41/4032) * (n : ℚ) ^ 8 + (9/112) * (n : ℚ) ^ 7 + (239/288) * (n : ℚ) ^ 6 + (109/24) * (n : ℚ) ^ 5 + (12079/576) * (n : ℚ) ^ 4 + (39/16) * (n : ℚ) ^ 3 + (310151/1008) * (n : ℚ) ^ 2 - (21299/84) * (n : ℚ) + 142) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 9 =
      X * (81 + 567 * X - 2868 * X ^ 2 + 6540 * X ^ 3 - 6063 * X ^ 4 - 415 * X ^ 5 + 7550 * X ^ 6 - 8564 * X ^ 7 + 4918 * X ^ 8 - 1584 * X ^ 9 + 262 * X ^ 10 - 14 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (f n : ℤ) = 9 * f (n - 1) - 36 * f (n - 2) + 84 * f (n - 3) - 126 * f (n - 4) + 126 * f (n - 5) - 84 * f (n - 6) + 36 * f (n - 7) - 9 * f (n - 8) + f (n - 9) :=
  ⟨fun n hn => poly f A ha hid hval n hn, gf f A ha hid hval, fun n hn => recZ f A ha hid hval n hn⟩

end PA224355

theorem OMA.solution : type_of% @OMA.S_oeis_a224355.main :=
  PA224355.final _ _ PA224355.a_eq PA224355.hid PA224355.hval
