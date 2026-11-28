import OMAStatements.S_oeis_a224014
import Mathlib

/-!
Proof of the empirical formula and Barker's conjectures for OEIS A224014
(Number of 4 X n 0..2 arrays with rows nondecreasing and antidiagonals unimodal.).

Outline.
1. Generic part (namespace UG, proved for any number of rows): the array is read column by column.
   A line (row, diagonal or antidiagonal) is unimodal iff it has no valley; appending a column
   keeps every line valley-free iff no line that has already strictly descended rises again at the
   new cell (`UC_snoc`), and the descent flags update locally (`DS_snoc`). The state after a column
   is coded as a natural number (the column in base m plus one flag bit per line ending there), and
   the computable transition `okc`/`dc` is shown to match the semantics (`okc_stS`, `dc_stS`). This
   gives a(n + 1) as a sum of continuation counts `Wc n` over the admissible first columns
   (`count_eq`).
2. Certificate (checked by the kernel, `decide +kernel`): the list of the 200 reachable states,
   their successor lists, a lumping of the states into 97 blocks with equal continuation counts,
   and the block tables up to length 14. From them, the pointwise identity
   Sum_i (-1)^i C(9, i) Wc (n + 9 - i) s = 0 for n >= 3 and every reachable s, hence the
   binomial recurrence for a(n), n >= 13.
3. The recurrence, the polynomial and the generating function follow from the recurrence and
   the computed values a(1), ..., a(15).
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

namespace PA224014

open OMA.S_oeis_a224014 UG PowerSeries

def CO (_v : Fin 4 → Fin 3) : Prop := True

instance : DecidablePred CO := fun _ => instDecidableTrue

def COc (_c : ℕ) : Bool := true

theorem hCO (v : Fin 4 → Fin 3) : COc (ccode v) = true ↔ CO v := by simp [COc, CO]

theorem hU : ∀ t ∈ ([2] : List ℕ), t < 3 := by decide

theorem uc_anti {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : AntidiagUnimodal x ↔ UC 2 (fun j i => x i j) := by
  constructor
  · intro h j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    exact h i1 i2 i3 j1 j2 j3 h12 h23 (by unfold al at a1 a2; omega) (by unfold al at a1 a2; omega)
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    exact h j1 j2 j3 i1 i2 i3 h12 h23 (by unfold al; omega) (by unfold al; omega)

theorem rn_iff {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : (∀ i, Monotone (x i)) ↔ RN (fun j i => x i j) := by
  constructor
  · intro h j1 j2 hj i; exact h i hj
  · intro h i j1 j2 hj; exact h j1 j2 hj i

theorem good_iff {n : ℕ} (x : Fin 4 → Fin n → Fin 3) : Good x ↔ P CO true [2] (fun j i => x i j) := by
  unfold Good P
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, CO,
    forall_const, true_and, implies_true, eq_self_iff_true, true_implies, uc_anti, rn_iff]

theorem a_eq (N : ℕ) : a (N + 1) = Ac 4 3 COc true [2] N := by
  rw [a, Ac, ← count_eq CO COc hCO true [2] hU N]
  apply Finset.card_equiv (Equiv.piComm _)
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact good_iff x

def RL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
    70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 20739, 20742, 20748, 20751, 20757, 20760, 20766,
    20769, 20775, 20778, 20784, 20787, 20793, 20796, 20802, 20805, 20811, 20814, 20743, 20752,
    20761, 20770, 20779, 20788, 20797, 20806, 20815, 41481, 41482, 41483, 41490, 41491, 41492,
    41508, 41509, 41510, 41517, 41518, 41519, 41535, 41536, 41537, 41544, 41545, 41546, 41493,
    41494, 41495, 41520, 41521, 41522, 41547, 41548, 41549, 62229, 62256, 62283, 82971, 82972,
    82973, 82974, 82975, 82976, 82977, 82978, 82979, 82998, 82999, 83000, 83001, 83002, 83003,
    83004, 83005, 83006, 103710, 103713, 103737, 103740, 103714, 103741, 83007, 83008, 83009,
    83010, 83011, 83012, 83013, 83014, 83015, 103746, 103749, 103750, 124479, 124480, 124481,
    62217, 62226, 62244, 62253, 62271, 62280, 145215, 62230, 62257, 62284, 124443, 124444, 124445,
    124470, 124471, 124472, 124482, 124483, 124484, 145218, 145179, 145206, 145219]

def SI : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
    44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
    68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80], [1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17,
    19, 20, 22, 23, 25, 26, 28, 29, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44, 46, 47, 49, 50, 52, 53,
    55, 56, 58, 59, 61, 62, 64, 65, 67, 68, 70, 71, 73, 74, 76, 77, 79, 80], [2, 5, 8, 11, 14, 17,
    20, 23, 26, 29, 32, 35, 38, 41, 44, 47, 50, 53, 56, 59, 62, 65, 68, 71, 74, 77, 80], [81, 4, 5,
    82, 7, 8, 83, 13, 14, 84, 16, 17, 85, 22, 23, 86, 25, 26, 87, 31, 32, 88, 34, 35, 89, 40, 41,
    90, 43, 44, 91, 49, 50, 92, 52, 53, 93, 58, 59, 94, 61, 62, 95, 67, 68, 96, 70, 71, 97, 76, 77,
    98, 79, 80], [4, 5, 7, 8, 13, 14, 16, 17, 22, 23, 25, 26, 31, 32, 34, 35, 40, 41, 43, 44, 49,
    50, 52, 53, 58, 59, 61, 62, 67, 68, 70, 71, 76, 77, 79, 80], [5, 8, 14, 17, 23, 26, 32, 35, 41,
    44, 50, 53, 59, 62, 68, 71, 77, 80], [82, 99, 8, 84, 100, 17, 86, 101, 26, 88, 102, 35, 90,
    103, 44, 92, 104, 53, 94, 105, 62, 96, 106, 71, 98, 107, 80], [99, 8, 100, 17, 101, 26, 102,
    35, 103, 44, 104, 53, 105, 62, 106, 71, 107, 80], [8, 17, 26, 35, 44, 53, 62, 71, 80], [108,
    109, 110, 12, 13, 14, 15, 16, 17, 111, 112, 113, 21, 22, 23, 24, 25, 26, 114, 115, 116, 39, 40,
    41, 42, 43, 44, 117, 118, 119, 48, 49, 50, 51, 52, 53, 120, 121, 122, 66, 67, 68, 69, 70, 71,
    123, 124, 125, 75, 76, 77, 78, 79, 80], [109, 110, 13, 14, 16, 17, 112, 113, 22, 23, 25, 26,
    115, 116, 40, 41, 43, 44, 118, 119, 49, 50, 52, 53, 121, 122, 67, 68, 70, 71, 124, 125, 76, 77,
    79, 80], [110, 14, 17, 113, 23, 26, 116, 41, 44, 119, 50, 53, 122, 68, 71, 125, 77, 80], [83,
    13, 14, 84, 16, 17, 85, 22, 23, 86, 25, 26, 89, 40, 41, 90, 43, 44, 91, 49, 50, 92, 52, 53, 95,
    67, 68, 96, 70, 71, 97, 76, 77, 98, 79, 80], [13, 14, 16, 17, 22, 23, 25, 26, 40, 41, 43, 44,
    49, 50, 52, 53, 67, 68, 70, 71, 76, 77, 79, 80], [14, 17, 23, 26, 41, 44, 50, 53, 68, 71, 77,
    80], [84, 100, 17, 86, 101, 26, 90, 103, 44, 92, 104, 53, 96, 106, 71, 98, 107, 80], [100, 17,
    101, 26, 103, 44, 104, 53, 106, 71, 107, 80], [17, 26, 44, 53, 71, 80], [111, 112, 113, 126,
    127, 128, 24, 25, 26, 117, 118, 119, 129, 130, 131, 51, 52, 53, 123, 124, 125, 132, 133, 134,
    78, 79, 80], [112, 113, 127, 128, 25, 26, 118, 119, 130, 131, 52, 53, 124, 125, 133, 134, 79,
    80], [113, 128, 26, 119, 131, 53, 125, 134, 80], [135, 127, 128, 86, 25, 26, 136, 130, 131, 92,
    52, 53, 137, 133, 134, 98, 79, 80], [127, 128, 25, 26, 130, 131, 52, 53, 133, 134, 79, 80],
    [128, 26, 131, 53, 134, 80], [86, 101, 26, 92, 104, 53, 98, 107, 80], [101, 26, 104, 53, 107,
    80], [26, 53, 80], [138, 139, 140, 141, 142, 143, 144, 145, 146, 36, 37, 38, 39, 40, 41, 42,
    43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 147, 148, 149, 150, 151, 152, 153, 154, 155, 63,
    64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80], [139, 140, 142, 143, 145,
    146, 37, 38, 40, 41, 43, 44, 46, 47, 49, 50, 52, 53, 148, 149, 151, 152, 154, 155, 64, 65, 67,
    68, 70, 71, 73, 74, 76, 77, 79, 80], [140, 143, 146, 38, 41, 44, 47, 50, 53, 149, 152, 155, 65,
    68, 71, 74, 77, 80], [156, 142, 143, 157, 145, 146, 89, 40, 41, 90, 43, 44, 91, 49, 50, 92, 52,
    53, 158, 151, 152, 159, 154, 155, 95, 67, 68, 96, 70, 71, 97, 76, 77, 98, 79, 80], [142, 143,
    145, 146, 40, 41, 43, 44, 49, 50, 52, 53, 151, 152, 154, 155, 67, 68, 70, 71, 76, 77, 79, 80],
    [143, 146, 41, 44, 50, 53, 152, 155, 68, 71, 77, 80], [157, 160, 146, 90, 103, 44, 92, 104, 53,
    159, 161, 155, 96, 106, 71, 98, 107, 80], [160, 146, 103, 44, 104, 53, 161, 155, 106, 71, 107,
    80], [146, 44, 53, 155, 71, 80], [114, 115, 116, 39, 40, 41, 42, 43, 44, 117, 118, 119, 48, 49,
    50, 51, 52, 53, 120, 121, 122, 66, 67, 68, 69, 70, 71, 123, 124, 125, 75, 76, 77, 78, 79, 80],
    [115, 116, 40, 41, 43, 44, 118, 119, 49, 50, 52, 53, 121, 122, 67, 68, 70, 71, 124, 125, 76,
    77, 79, 80], [116, 41, 44, 119, 50, 53, 122, 68, 71, 125, 77, 80], [89, 40, 41, 90, 43, 44, 91,
    49, 50, 92, 52, 53, 95, 67, 68, 96, 70, 71, 97, 76, 77, 98, 79, 80], [40, 41, 43, 44, 49, 50,
    52, 53, 67, 68, 70, 71, 76, 77, 79, 80], [41, 44, 50, 53, 68, 71, 77, 80], [90, 103, 44, 92,
    104, 53, 96, 106, 71, 98, 107, 80], [103, 44, 104, 53, 106, 71, 107, 80], [44, 53, 71, 80],
    [117, 118, 119, 129, 130, 131, 51, 52, 53, 123, 124, 125, 132, 133, 134, 78, 79, 80], [118,
    119, 130, 131, 52, 53, 124, 125, 133, 134, 79, 80], [119, 131, 53, 125, 134, 80], [136, 130,
    131, 92, 52, 53, 137, 133, 134, 98, 79, 80], [130, 131, 52, 53, 133, 134, 79, 80], [131, 53,
    134, 80], [92, 104, 53, 98, 107, 80], [104, 53, 107, 80], [53, 80], [147, 148, 149, 150, 151,
    152, 153, 154, 155, 162, 163, 164, 165, 166, 167, 168, 169, 170, 72, 73, 74, 75, 76, 77, 78,
    79, 80], [148, 149, 151, 152, 154, 155, 163, 164, 166, 167, 169, 170, 73, 74, 76, 77, 79, 80],
    [149, 152, 155, 164, 167, 170, 74, 77, 80], [158, 151, 152, 159, 154, 155, 171, 166, 167, 172,
    169, 170, 97, 76, 77, 98, 79, 80], [151, 152, 154, 155, 166, 167, 169, 170, 76, 77, 79, 80],
    [152, 155, 167, 170, 77, 80], [159, 161, 155, 172, 173, 170, 98, 107, 80], [161, 155, 173, 170,
    107, 80], [155, 170, 80], [174, 175, 176, 165, 166, 167, 168, 169, 170, 123, 124, 125, 75, 76,
    77, 78, 79, 80], [175, 176, 166, 167, 169, 170, 124, 125, 76, 77, 79, 80], [176, 167, 170, 125,
    77, 80], [171, 166, 167, 172, 169, 170, 97, 76, 77, 98, 79, 80], [166, 167, 169, 170, 76, 77,
    79, 80], [167, 170, 77, 80], [172, 173, 170, 98, 107, 80], [173, 170, 107, 80], [170, 80],
    [123, 124, 125, 132, 133, 134, 78, 79, 80], [124, 125, 133, 134, 79, 80], [125, 134, 80], [137,
    133, 134, 98, 79, 80], [133, 134, 79, 80], [134, 80], [98, 107, 80], [107, 80], [80], [81, 4,
    5, 82, 7, 8, 83, 13, 14, 84, 16, 17, 85, 22, 23, 86, 25, 26, 87, 31, 32, 88, 34, 35, 89, 40,
    41, 90, 43, 44, 91, 49, 50, 92, 52, 53, 93, 58, 59, 94, 61, 62, 95, 67, 68, 96, 70, 71, 97, 76,
    77, 98, 79, 80], [82, 99, 8, 84, 100, 17, 86, 101, 26, 88, 102, 35, 90, 103, 44, 92, 104, 53,
    94, 105, 62, 96, 106, 71, 98, 107, 80], [83, 13, 14, 84, 16, 17, 85, 22, 23, 86, 25, 26, 89,
    40, 41, 90, 43, 44, 91, 49, 50, 92, 52, 53, 95, 67, 68, 96, 70, 71, 97, 76, 77, 98, 79, 80],
    [84, 100, 17, 86, 101, 26, 90, 103, 44, 92, 104, 53, 96, 106, 71, 98, 107, 80], [135, 127, 128,
    86, 25, 26, 136, 130, 131, 92, 52, 53, 137, 133, 134, 98, 79, 80], [86, 101, 26, 92, 104, 53,
    98, 107, 80], [156, 142, 143, 157, 145, 146, 89, 40, 41, 90, 43, 44, 91, 49, 50, 92, 52, 53,
    158, 151, 152, 159, 154, 155, 95, 67, 68, 96, 70, 71, 97, 76, 77, 98, 79, 80], [157, 160, 146,
    90, 103, 44, 92, 104, 53, 159, 161, 155, 96, 106, 71, 98, 107, 80], [89, 40, 41, 90, 43, 44,
    91, 49, 50, 92, 52, 53, 95, 67, 68, 96, 70, 71, 97, 76, 77, 98, 79, 80], [90, 103, 44, 92, 104,
    53, 96, 106, 71, 98, 107, 80], [136, 130, 131, 92, 52, 53, 137, 133, 134, 98, 79, 80], [92,
    104, 53, 98, 107, 80], [158, 151, 152, 159, 154, 155, 171, 166, 167, 172, 169, 170, 97, 76, 77,
    98, 79, 80], [159, 161, 155, 172, 173, 170, 98, 107, 80], [171, 166, 167, 172, 169, 170, 97,
    76, 77, 98, 79, 80], [172, 173, 170, 98, 107, 80], [137, 133, 134, 98, 79, 80], [98, 107, 80],
    [99, 8, 100, 17, 101, 26, 102, 35, 103, 44, 104, 53, 105, 62, 106, 71, 107, 80], [100, 17, 101,
    26, 103, 44, 104, 53, 106, 71, 107, 80], [101, 26, 104, 53, 107, 80], [160, 146, 103, 44, 104,
    53, 161, 155, 106, 71, 107, 80], [103, 44, 104, 53, 106, 71, 107, 80], [104, 53, 107, 80],
    [161, 155, 173, 170, 107, 80], [173, 170, 107, 80], [107, 80], [177, 83, 84, 178, 85, 86, 179,
    89, 90, 180, 91, 92, 181, 95, 96, 182, 97, 98], [], [], [178, 135, 86, 180, 136, 92, 182, 137,
    98], [], [], [179, 89, 90, 180, 91, 92, 181, 95, 96, 182, 97, 98], [], [], [180, 136, 92, 182,
    137, 98], [], [], [183, 171, 172, 182, 97, 98], [], [], [182, 137, 98], [], [], [135, 184, 86,
    101, 136, 185, 92, 104, 137, 186, 98, 107], [184, 101, 185, 104, 186, 107], [], [136, 185, 92,
    104, 137, 186, 98, 107], [185, 104, 186, 107], [], [137, 186, 98, 107], [186, 107], [], [135,
    184, 86, 101, 136, 185, 92, 104, 137, 186, 98, 107], [136, 185, 92, 104, 137, 186, 98, 107],
    [137, 186, 98, 107], [187, 188, 189, 114, 115, 116, 117, 118, 119, 190, 191, 192, 120, 121,
    122, 123, 124, 125], [188, 189, 115, 116, 118, 119, 191, 192, 121, 122, 124, 125], [189, 116,
    119, 192, 122, 125], [], [], [], [], [], [], [190, 191, 192, 174, 175, 176, 123, 124, 125],
    [191, 192, 175, 176, 124, 125], [192, 176, 125], [], [], [], [], [], [], [], [], [], [], [],
    [], [174, 175, 176, 193, 194, 195, 123, 124, 125, 132, 133, 134], [175, 176, 194, 195, 124,
    125, 133, 134], [176, 195, 125, 134], [196, 194, 195, 137, 133, 134], [194, 195, 133, 134],
    [195, 134], [], [], [], [196, 194, 195, 137, 133, 134], [], [], [183, 196, 182, 137], [], [],
    [177, 83, 84, 178, 85, 86, 179, 89, 90, 180, 91, 92, 181, 95, 96, 182, 97, 98], [178, 135, 86,
    180, 136, 92, 182, 137, 98], [179, 89, 90, 180, 91, 92, 181, 95, 96, 182, 97, 98], [180, 136,
    92, 182, 137, 98], [183, 171, 172, 182, 97, 98], [182, 137, 98], [183, 196, 182, 137], [184,
    101, 185, 104, 186, 107], [185, 104, 186, 107], [186, 107], [197, 179, 180, 198, 181, 182], [],
    [], [198, 183, 182], [], [], [196, 199, 137, 186], [199, 186], [], [196, 199, 137, 186], [197,
    179, 180, 198, 181, 182], [198, 183, 182], [199, 186]]

def BL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 31, 32, 37, 38, 39, 40, 41, 42, 43,
    44, 45, 46, 47, 48, 25, 49, 50, 51, 52, 53, 54, 55, 56, 20, 45, 57, 58, 55, 56, 59, 60, 61, 23,
    48, 62, 63, 64, 57, 65, 66, 62, 26, 50, 67, 3, 6, 12, 15, 21, 24, 30, 33, 37, 40, 46, 25, 54,
    20, 59, 23, 65, 26, 7, 16, 25, 34, 41, 49, 45, 48, 50, 68, 69, 69, 70, 69, 69, 71, 69, 69, 72,
    69, 69, 73, 69, 69, 74, 69, 69, 75, 76, 69, 77, 78, 69, 79, 80, 69, 75, 77, 79, 81, 82, 83, 69,
    69, 69, 69, 69, 69, 84, 83, 85, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 86, 87, 88, 89,
    90, 91, 69, 69, 69, 89, 69, 69, 92, 69, 69, 68, 70, 71, 72, 73, 74, 92, 76, 78, 80, 93, 69, 69,
    94, 69, 69, 95, 96, 69, 95, 93, 94, 96]

def BS : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 31, 32, 37, 38, 39, 40, 41,
    42, 43, 44, 45, 46, 47, 48, 25, 49, 50, 51, 52, 53, 54, 55, 56, 20, 45, 57, 58, 55, 56, 59, 60,
    61, 23, 48, 62, 63, 64, 57, 65, 66, 62, 26, 50, 67], [1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17,
    19, 20, 22, 23, 25, 26, 28, 29, 31, 32, 34, 35, 31, 32, 38, 39, 41, 42, 44, 45, 47, 48, 49, 50,
    52, 53, 55, 56, 45, 57, 55, 56, 60, 61, 48, 62, 64, 57, 66, 62, 50, 67], [2, 5, 8, 11, 14, 17,
    20, 23, 26, 29, 32, 35, 32, 39, 42, 45, 48, 50, 53, 56, 57, 56, 61, 62, 57, 62, 67], [3, 4, 5,
    6, 7, 8, 12, 13, 14, 15, 16, 17, 21, 22, 23, 24, 25, 26, 30, 31, 32, 33, 34, 35, 37, 38, 39,
    40, 41, 42, 46, 47, 48, 25, 49, 50, 54, 55, 56, 20, 45, 57, 59, 60, 61, 23, 48, 62, 65, 66, 62,
    26, 50, 67], [4, 5, 7, 8, 13, 14, 16, 17, 22, 23, 25, 26, 31, 32, 34, 35, 38, 39, 41, 42, 47,
    48, 49, 50, 55, 56, 45, 57, 60, 61, 48, 62, 66, 62, 50, 67], [5, 8, 14, 17, 23, 26, 32, 35, 39,
    42, 48, 50, 56, 57, 61, 62, 62, 67], [6, 7, 8, 15, 16, 17, 24, 25, 26, 33, 34, 35, 40, 41, 42,
    25, 49, 50, 20, 45, 57, 23, 48, 62, 26, 50, 67], [7, 8, 16, 17, 25, 26, 34, 35, 41, 42, 49, 50,
    45, 57, 48, 62, 50, 67], [8, 17, 26, 35, 42, 50, 57, 62, 67], [68, 69, 69, 12, 13, 14, 15, 16,
    17, 70, 69, 69, 21, 22, 23, 24, 25, 26, 71, 69, 69, 37, 38, 39, 40, 41, 42, 72, 69, 69, 46, 47,
    48, 25, 49, 50, 73, 69, 69, 59, 60, 61, 23, 48, 62, 74, 69, 69, 65, 66, 62, 26, 50, 67], [69,
    69, 13, 14, 16, 17, 69, 69, 22, 23, 25, 26, 69, 69, 38, 39, 41, 42, 69, 69, 47, 48, 49, 50, 69,
    69, 60, 61, 48, 62, 69, 69, 66, 62, 50, 67], [69, 14, 17, 69, 23, 26, 69, 39, 42, 69, 48, 50,
    69, 61, 62, 69, 62, 67], [12, 13, 14, 15, 16, 17, 21, 22, 23, 24, 25, 26, 37, 38, 39, 40, 41,
    42, 46, 47, 48, 25, 49, 50, 59, 60, 61, 23, 48, 62, 65, 66, 62, 26, 50, 67], [13, 14, 16, 17,
    22, 23, 25, 26, 38, 39, 41, 42, 47, 48, 49, 50, 60, 61, 48, 62, 66, 62, 50, 67], [14, 17, 23,
    26, 39, 42, 48, 50, 61, 62, 62, 67], [15, 16, 17, 24, 25, 26, 40, 41, 42, 25, 49, 50, 23, 48,
    62, 26, 50, 67], [16, 17, 25, 26, 41, 42, 49, 50, 48, 62, 50, 67], [17, 26, 42, 50, 62, 67],
    [70, 69, 69, 75, 76, 69, 24, 25, 26, 72, 69, 69, 77, 78, 69, 25, 49, 50, 74, 69, 69, 79, 80,
    69, 26, 50, 67], [69, 69, 76, 69, 25, 26, 69, 69, 78, 69, 49, 50, 69, 69, 80, 69, 50, 67], [69,
    69, 26, 69, 69, 50, 69, 69, 67], [75, 76, 69, 24, 25, 26, 77, 78, 69, 25, 49, 50, 79, 80, 69,
    26, 50, 67], [76, 69, 25, 26, 78, 69, 49, 50, 80, 69, 50, 67], [69, 26, 69, 50, 69, 67], [24,
    25, 26, 25, 49, 50, 26, 50, 67], [25, 26, 49, 50, 50, 67], [26, 50, 67], [81, 82, 83, 69, 69,
    69, 69, 69, 69, 36, 31, 32, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 25, 49, 50, 84, 83,
    85, 69, 69, 69, 69, 69, 69, 58, 55, 56, 59, 60, 61, 23, 48, 62, 63, 64, 57, 65, 66, 62, 26, 50,
    67], [82, 83, 69, 69, 69, 69, 31, 32, 38, 39, 41, 42, 44, 45, 47, 48, 49, 50, 83, 85, 69, 69,
    69, 69, 55, 56, 60, 61, 48, 62, 64, 57, 66, 62, 50, 67], [83, 69, 69, 32, 39, 42, 45, 48, 50,
    85, 69, 69, 56, 61, 62, 57, 62, 67], [69, 69, 69, 69, 69, 69, 37, 38, 39, 40, 41, 42, 46, 47,
    48, 25, 49, 50, 69, 69, 69, 69, 69, 69, 59, 60, 61, 23, 48, 62, 65, 66, 62, 26, 50, 67], [69,
    69, 69, 69, 38, 39, 41, 42, 47, 48, 49, 50, 69, 69, 69, 69, 60, 61, 48, 62, 66, 62, 50, 67],
    [69, 69, 39, 42, 48, 50, 69, 69, 61, 62, 62, 67], [69, 69, 69, 40, 41, 42, 25, 49, 50, 69, 69,
    69, 23, 48, 62, 26, 50, 67], [69, 69, 41, 42, 49, 50, 69, 69, 48, 62, 50, 67], [69, 42, 50, 69,
    62, 67], [71, 69, 69, 37, 38, 39, 40, 41, 42, 72, 69, 69, 46, 47, 48, 25, 49, 50, 73, 69, 69,
    59, 60, 61, 23, 48, 62, 74, 69, 69, 65, 66, 62, 26, 50, 67], [37, 38, 39, 40, 41, 42, 46, 47,
    48, 25, 49, 50, 59, 60, 61, 23, 48, 62, 65, 66, 62, 26, 50, 67], [38, 39, 41, 42, 47, 48, 49,
    50, 60, 61, 48, 62, 66, 62, 50, 67], [39, 42, 48, 50, 61, 62, 62, 67], [40, 41, 42, 25, 49, 50,
    23, 48, 62, 26, 50, 67], [41, 42, 49, 50, 48, 62, 50, 67], [42, 50, 62, 67], [72, 69, 69, 77,
    78, 69, 25, 49, 50, 74, 69, 69, 79, 80, 69, 26, 50, 67], [69, 69, 78, 69, 49, 50, 69, 69, 80,
    69, 50, 67], [69, 69, 50, 69, 69, 67], [77, 78, 69, 25, 49, 50, 79, 80, 69, 26, 50, 67], [78,
    69, 49, 50, 80, 69, 50, 67], [69, 50, 69, 67], [49, 50, 50, 67], [50, 67], [84, 83, 85, 69, 69,
    69, 69, 69, 69, 86, 87, 88, 89, 90, 91, 69, 69, 69, 63, 64, 57, 65, 66, 62, 26, 50, 67], [83,
    85, 69, 69, 69, 69, 87, 88, 90, 91, 69, 69, 64, 57, 66, 62, 50, 67], [85, 69, 69, 88, 91, 69,
    57, 62, 67], [69, 69, 69, 69, 69, 69, 89, 90, 91, 69, 69, 69, 65, 66, 62, 26, 50, 67], [69, 69,
    69, 69, 90, 91, 69, 69, 66, 62, 50, 67], [69, 69, 91, 69, 62, 67], [69, 69, 67], [92, 69, 69,
    89, 90, 91, 69, 69, 69, 74, 69, 69, 65, 66, 62, 26, 50, 67], [89, 90, 91, 69, 69, 69, 65, 66,
    62, 26, 50, 67], [90, 91, 69, 69, 66, 62, 50, 67], [91, 69, 62, 67], [69, 67], [74, 69, 69, 79,
    80, 69, 26, 50, 67], [69, 69, 80, 69, 50, 67], [79, 80, 69, 26, 50, 67], [80, 69, 50, 67],
    [67], [68, 12, 15, 70, 21, 24, 71, 37, 40, 72, 46, 25, 73, 59, 23, 74, 65, 26], [], [70, 75,
    24, 72, 77, 25, 74, 79, 26], [71, 37, 40, 72, 46, 25, 73, 59, 23, 74, 65, 26], [72, 77, 25, 74,
    79, 26], [92, 89, 69, 74, 65, 26], [74, 79, 26], [75, 76, 24, 25, 77, 78, 25, 49, 79, 80, 26,
    50], [76, 25, 78, 49, 80, 50], [77, 78, 25, 49, 79, 80, 26, 50], [78, 49, 80, 50], [79, 80, 26,
    50], [80, 50], [93, 69, 69, 71, 69, 69, 72, 69, 69, 94, 69, 69, 73, 69, 69, 74, 69, 69], [69,
    69, 69, 69, 69, 69, 69, 69, 69, 69, 69, 69], [69, 69, 69, 69, 69, 69], [94, 69, 69, 92, 69, 69,
    74, 69, 69], [69, 69, 69], [92, 69, 69, 95, 96, 69, 74, 69, 69, 79, 80, 69], [69, 69, 96, 69,
    69, 69, 80, 69], [69, 69, 69, 69], [95, 96, 69, 79, 80, 69], [96, 69, 80, 69], [69, 69], [92,
    95, 74, 79], [93, 71, 72, 94, 73, 74], [94, 92, 74], [95, 96, 79, 80], [96, 80]]

def VT : List (List ℕ) := [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1], [81, 54, 27, 54, 36, 18, 27, 18, 9, 54, 36, 18, 36, 24, 12, 18, 12,
    6, 27, 18, 9, 18, 12, 6, 9, 6, 3, 54, 36, 18, 36, 24, 12, 18, 12, 6, 36, 24, 16, 8, 12, 8, 4,
    18, 12, 6, 12, 8, 4, 4, 2, 27, 18, 9, 18, 12, 6, 3, 18, 12, 8, 4, 2, 9, 6, 6, 4, 1, 18, 0, 9,
    12, 6, 6, 3, 12, 6, 8, 4, 4, 2, 18, 12, 6, 9, 3, 12, 8, 4, 6, 4, 2, 4, 6, 3, 4, 2], [1296, 648,
    216, 648, 324, 108, 216, 108, 36, 378, 162, 54, 324, 162, 54, 108, 54, 18, 90, 30, 6, 72, 30,
    6, 36, 18, 6, 378, 189, 63, 162, 81, 27, 54, 27, 9, 189, 162, 81, 27, 54, 27, 9, 45, 15, 3, 36,
    15, 3, 9, 3, 90, 45, 15, 30, 15, 5, 1, 37, 30, 15, 5, 1, 15, 5, 12, 5, 1, 216, 0, 60, 108, 30,
    22, 10, 66, 24, 33, 12, 11, 4, 36, 0, 0, 10, 0, 19, 4, 0, 12, 4, 0, 15, 36, 10, 12, 4], [7378,
    2880, 710, 3280, 1300, 320, 840, 336, 84, 1866, 556, 134, 1420, 556, 134, 380, 152, 38, 350,
    80, 10, 250, 80, 10, 100, 40, 10, 1016, 360, 86, 532, 208, 50, 140, 56, 14, 702, 532, 208, 50,
    140, 56, 14, 140, 32, 4, 100, 32, 4, 16, 4, 98, 24, 3, 44, 14, 2, 1, 69, 44, 14, 2, 1, 35, 8,
    25, 8, 1, 1310, 0, 270, 494, 108, 55, 27, 240, 70, 96, 28, 24, 7, 216, 0, 0, 35, 0, 56, 8, 0,
    31, 8, 0, 48, 216, 35, 31, 8], [28541, 8990, 1740, 11725, 3828, 740, 2505, 835, 167, 6754,
    1439, 269, 4490, 1439, 269, 1020, 340, 68, 1095, 180, 15, 690, 180, 15, 225, 75, 15, 2836, 738,
    134, 1320, 419, 77, 300, 100, 20, 2004, 1320, 419, 77, 300, 100, 20, 365, 60, 5, 230, 60, 5,
    25, 5, 231, 39, 3, 88, 22, 2, 1, 163, 88, 22, 2, 1, 73, 12, 46, 12, 1, 5315, 0, 915, 1585, 305,
    141, 61, 675, 165, 225, 55, 45, 11, 935, 0, 0, 110, 0, 145, 15, 0, 70, 15, 0, 130, 935, 110,
    70, 15], [90051, 23522, 3732, 33844, 9377, 1486, 6258, 1788, 298, 19997, 3161, 479, 11675,
    3161, 479, 2310, 660, 110, 2898, 357, 21, 1617, 357, 21, 441, 126, 21, 7097, 1358, 197, 2849,
    760, 112, 567, 162, 27, 4941, 2849, 760, 112, 567, 162, 27, 828, 102, 6, 462, 102, 6, 36, 6,
    521, 62, 3, 165, 34, 2, 1, 356, 165, 34, 2, 1, 138, 17, 77, 17, 1, 16836, 0, 2541, 4181, 726,
    322, 121, 1596, 336, 456, 96, 76, 16, 3137, 0, 0, 301, 0, 332, 26, 0, 141, 26, 0, 306, 3137,
    301, 141, 26], [245055, 54193, 7266, 84302, 20267, 2713, 13776, 3444, 492, 51272, 6214, 787,
    26545, 6214, 787, 4648, 1162, 166, 6748, 644, 28, 3360, 644, 28, 784, 196, 28, 16302, 2313,
    277, 5567, 1279, 156, 980, 245, 35, 10917, 5567, 1279, 156, 980, 245, 35, 1687, 161, 7, 840,
    161, 7, 49, 7, 1105, 95, 3, 290, 51, 2, 1, 717, 290, 51, 2, 1, 241, 23, 120, 23, 1, 45058, 0,
    6104, 9638, 1526, 666, 218, 3332, 616, 833, 154, 119, 22, 8788, 0, 0, 728, 0, 686, 42, 0, 259,
    42, 0, 644, 8788, 728, 259, 42], [595822, 113449, 13145, 188278, 39949, 4618, 27576, 6128, 766,
    117853, 11257, 1219, 54643, 11257, 1219, 8568, 1904, 238, 14220, 1080, 36, 6372, 1080, 36,
    1296, 288, 36, 34839, 3712, 376, 10081, 2032, 210, 1584, 352, 44, 22129, 10081, 2032, 210,
    1584, 352, 44, 3160, 240, 8, 1416, 240, 8, 64, 8, 2202, 140, 3, 481, 74, 2, 1, 1343, 481, 74,
    2, 1, 395, 30, 177, 30, 1, 106596, 0, 13140, 20097, 2920, 1269, 365, 6336, 1044, 1408, 232,
    176, 29, 21564, 0, 0, 1590, 0, 1304, 64, 0, 442, 64, 0, 1240, 21564, 1590, 442, 64], [1325316,
    220339, 22445, 386339, 73325, 7445, 51255, 10251, 1139, 248506, 19141, 1804, 104119, 19141,
    1804, 14760, 2952, 328, 27675, 1710, 45, 11250, 1710, 45, 2025, 405, 45, 69960, 5680, 496,
    17182, 3083, 275, 2430, 486, 54, 41833, 17182, 3083, 275, 2430, 486, 54, 5535, 342, 9, 2250,
    342, 9, 81, 9, 4143, 199, 3, 759, 104, 2, 1, 2364, 759, 104, 2, 1, 615, 38, 250, 38, 1, 229365,
    0, 25965, 38750, 5193, 2260, 577, 11205, 1665, 2241, 333, 249, 37, 47805, 0, 0, 3195, 0, 2316,
    93, 0, 711, 93, 0, 2223, 47805, 3195, 711, 93], [2742301, 402824, 36570, 740638, 127108, 11490,
    89760, 16320, 1632, 488564, 30934, 2574, 186454, 30934, 2574, 24090, 4380, 438, 50490, 2585,
    55, 18755, 2585, 55, 3025, 550, 55, 133071, 8358, 639, 27870, 4504, 352, 3575, 650, 65, 74650,
    27870, 4504, 352, 3575, 650, 65, 9180, 470, 10, 3410, 470, 10, 100, 10, 7406, 274, 3, 1148,
    142, 2, 1, 3948, 1148, 142, 2, 1, 918, 47, 341, 47, 1, 457630, 0, 47905, 70146, 8710, 3806,
    871, 18700, 2530, 3400, 460, 340, 46, 97780, 0, 0, 5995, 0, 3890, 130, 0, 1090, 130, 0, 3760,
    97780, 5995, 1090, 130], [5343468, 700566, 57312, 1342596, 210222, 17106, 149688, 24948, 2268,
    906342, 47946, 3564, 317274, 47946, 3564, 37620, 6270, 570, 87318, 3762, 66, 29832, 3762, 66,
    4356, 726, 66, 241378, 11903, 807, 43379, 6375, 442, 5082, 847, 77, 126912, 43379, 6375, 442,
    5082, 847, 77, 14553, 627, 11, 4972, 627, 11, 121, 11, 12656, 367, 3, 1675, 189, 2, 1, 6306,
    1675, 189, 2, 1, 1323, 57, 452, 57, 1, 858396, 0, 83556, 120537, 13926, 6117, 1266, 29766,
    3696, 4961, 616, 451, 56, 187308, 0, 0, 10626, 0, 6237, 176, 0, 1606, 176, 0, 6061, 187308,
    10626, 1606, 176], [9896484, 1168242, 86916, 2322228, 334242, 24708, 239616, 36864, 3072,
    1601052, 71754, 4812, 517254, 71754, 4812, 56628, 8712, 726, 144378, 5304, 78, 45630, 5304, 78,
    6084, 936, 78, 419934, 16488, 1002, 65202, 8784, 546, 7020, 1080, 90, 207048, 65202, 8784, 546,
    7020, 1080, 90, 22212, 816, 12, 7020, 816, 12, 144, 12, 20790, 480, 3, 2370, 246, 2, 1, 9697,
    2370, 246, 2, 1, 1851, 68, 585, 68, 1, 1529298, 0, 139074, 198264, 21396, 9451, 1783, 45552,
    5226, 7008, 804, 584, 67, 339780, 0, 0, 17953, 0, 9616, 232, 0, 2289, 232, 0, 9384, 339780,
    17953, 2289, 232], [17548273, 1879428, 128150, 3859273, 513874, 34778, 370461, 52923, 4071,
    2712378, 104227, 6359, 813112, 104227, 6359, 82628, 11804, 908, 229775, 7280, 91, 67522, 7280,
    91, 8281, 1183, 91, 704132, 22302, 1226, 95116, 11827, 665, 9464, 1352, 104, 326010, 95116,
    11827, 665, 9464, 1352, 104, 32825, 1040, 13, 9646, 1040, 13, 169, 13, 32987, 615, 3, 3266,
    314, 2, 1, 14433, 3266, 314, 2, 1, 2525, 80, 742, 80, 1, 2608151, 0, 222495, 314183, 31785,
    14119, 2445, 67431, 7189, 9633, 1027, 741, 79, 588627, 0, 0, 29120, 0, 14339, 299, 0, 3172,
    299, 0, 14040, 588627, 29120, 3172, 299], [29963249, 2931098, 184380, 6196288, 767475, 47870,
    555870, 74116, 5294, 4431871, 147551, 8249, 1238693, 147551, 8249, 117390, 15652, 1118, 353850,
    9765, 105, 97125, 9765, 105, 11025, 1470, 105, 1142689, 29550, 1481, 135207, 15608, 800, 12495,
    1666, 119, 497739, 135207, 15608, 800, 12495, 1666, 119, 47180, 1302, 14, 12950, 1302, 14, 196,
    14, 50763, 774, 3, 4399, 394, 2, 1, 20884, 4399, 394, 2, 1, 3370, 93, 925, 93, 1, 4284320, 0,
    344085, 482131, 45878, 20490, 3277, 97020, 9660, 12936, 1288, 924, 92, 980279, 0, 0, 45605, 0,
    20776, 378, 0, 4291, 378, 0, 20398, 980279, 45605, 4291, 378], [49496631, 4448783, 259650,
    9653866, 1117613, 64615, 812640, 101580, 6772, 7016324, 204254, 10529, 1836143, 204254, 10529,
    162960, 20370, 1358, 529560, 12840, 120, 136320, 12840, 120, 14400, 1800, 120, 1801166, 38453,
    1769, 187895, 20239, 952, 16200, 2025, 135, 739671, 187895, 20239, 952, 16200, 2025, 135,
    66195, 1605, 15, 17040, 1605, 15, 225, 15, 76031, 959, 3, 5808, 487, 2, 1, 29483, 5808, 487, 2,
    1, 4413, 107, 1136, 107, 1, 6812070, 0, 516720, 719432, 64590, 28996, 4306, 136200, 12720,
    17025, 1590, 1135, 106, 1577660, 0, 0, 69280, 0, 29360, 470, 0, 5685, 470, 0, 28890, 1577660,
    69280, 5685, 470]]

def IL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
    70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80]

def AV : List ℕ := [0, 81, 1296, 7378, 28541, 90051, 245055, 595822, 1325316, 2742301, 5343468,
    9896484, 17548273, 29963249, 49496631, 79408380]

def LC : List (ℕ × ℕ) := [(1, 9), (36, 7), (126, 5), (84, 3), (9, 1)]

def RC : List (ℕ × ℕ) := [(9, 8), (84, 6), (126, 4), (36, 2), (1, 0)]

set_option maxRecDepth 100000 in
theorem h1_0 : (List.range' 0 50).all (c1 4 3 COc true [2] RL SI 200) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_1 : (List.range' 50 50).all (c1 4 3 COc true [2] RL SI 200) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_2 : (List.range' 100 50).all (c1 4 3 COc true [2] RL SI 200) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_3 : (List.range' 150 50).all (c1 4 3 COc true [2] RL SI 200) = true := by
  decide +kernel

theorem h1 : chk1 4 3 COc true [2] RL SI 200 = true :=
  chk1_of 4 3 COc true [2] RL SI 200 (all_split (c1 4 3 COc true [2] RL SI 200) 0 150 50 (all_split (c1 4 3 COc true [2] RL SI 200) 0 100 50 (all_split (c1 4 3 COc true [2] RL SI 200) 0 50 50 h1_0 h1_1) h1_2) h1_3)


set_option maxRecDepth 100000 in
theorem h2_0 : (List.range' 0 48).all (c2 SI BL BS 97) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_1 : (List.range' 48 48).all (c2 SI BL BS 97) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_2 : (List.range' 96 48).all (c2 SI BL BS 97) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_3 : (List.range' 144 48).all (c2 SI BL BS 97) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_4 : (List.range' 192 8).all (c2 SI BL BS 97) = true := by
  decide +kernel

theorem h2 : chk2 SI BL BS 200 97 = true :=
  chk2_of SI BL BS 200 97 (all_split (c2 SI BL BS 97) 0 192 8 (all_split (c2 SI BL BS 97) 0 144 48 (all_split (c2 SI BL BS 97) 0 96 48 (all_split (c2 SI BL BS 97) 0 48 48 h2_0 h2_1) h2_2) h2_3) h2_4)


set_option maxRecDepth 100000 in
theorem hV : chkV BS VT 97 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hI : chkI VT 97 LC RC 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem h3 : chk3 4 3 COc RL 200 IL = true := by decide +kernel

theorem hJ : ∀ p ∈ LC ++ RC, 3 + p.2 ≤ 14 := by decide

set_option maxRecDepth 100000 in
theorem hAV : ∀ N ≤ 14, (IL.map (fun t => gL (VT.getD N []) (gL BL t))).sum = gL AV (N + 1) := by
  decide +kernel

theorem hid (M : ℕ) : Lin LC (Ac 4 3 COc true [2]) (3 + M) = Lin RC (Ac 4 3 COc true [2]) (3 + M) :=
  A_ident 4 3 COc true [2] RL SI BL BS VT 200 97 14 h1 h2 hV LC RC 3 hI hJ IL h3 M

theorem hval (N : ℕ) (hN : N ≤ 14) : a (N + 1) = gL AV (N + 1) := by
  rw [a_eq, A_val 4 3 COc true [2] RL SI BL BS VT 200 97 14 h1 h2 hV IL h3 N hN, hAV N hN]

/-! The rest is about any sequence with these properties (kept abstract for the kernel). -/

theorem recN (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (3 + M) = Lin RC A (3 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) (M : ℕ) : 1 * f (M + 13) + 36 * f (M + 13 - 2) + 126 * f (M + 13 - 4) + 84 * f (M + 13 - 6) + 9 * f (M + 13 - 8) = 9 * f (M + 13 - 1) + 84 * f (M + 13 - 3) + 126 * f (M + 13 - 5) + 36 * f (M + 13 - 7) + 1 * f (M + 13 - 9) := by
  have h := hid M
  simp only [LC, RC, Lin, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [show M + 13 - 1 = 3 + M + 8 + 1 by omega, ha (3 + M + 8), show M + 13 - 2 = 3 + M + 7 + 1 by omega, ha (3 + M + 7), show M + 13 - 3 = 3 + M + 6 + 1 by omega, ha (3 + M + 6), show M + 13 - 4 = 3 + M + 5 + 1 by omega, ha (3 + M + 5), show M + 13 - 5 = 3 + M + 4 + 1 by omega, ha (3 + M + 4), show M + 13 - 6 = 3 + M + 3 + 1 by omega, ha (3 + M + 3), show M + 13 - 7 = 3 + M + 2 + 1 by omega, ha (3 + M + 2), show M + 13 - 8 = 3 + M + 1 + 1 by omega, ha (3 + M + 1), show M + 13 - 9 = 3 + M + 1 by omega, ha (3 + M), show M + 13 = 3 + M + 9 + 1 by omega, ha (3 + M + 9)]
  omega

theorem recZ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (3 + M) = Lin RC A (3 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 11 < n) : (f n : ℤ) = 9 * f (n - 1) - 36 * f (n - 2) + 84 * f (n - 3) - 126 * f (n - 4) + 126 * f (n - 5) - 84 * f (n - 6) + 36 * f (n - 7) - 9 * f (n - 8) + f (n - 9) := by
  have v1 : f 1 = 81 := hval 0 (by norm_num)
  have v2 : f 2 = 1296 := hval 1 (by norm_num)
  have v3 : f 3 = 7378 := hval 2 (by norm_num)
  have v4 : f 4 = 28541 := hval 3 (by norm_num)
  have v5 : f 5 = 90051 := hval 4 (by norm_num)
  have v6 : f 6 = 245055 := hval 5 (by norm_num)
  have v7 : f 7 = 595822 := hval 6 (by norm_num)
  have v8 : f 8 = 1325316 := hval 7 (by norm_num)
  have v9 : f 9 = 2742301 := hval 8 (by norm_num)
  have v10 : f 10 = 5343468 := hval 9 (by norm_num)
  have v11 : f 11 = 9896484 := hval 10 (by norm_num)
  have v12 : f 12 = 17548273 := hval 11 (by norm_num)
  have v13 : f 13 = 29963249 := hval 12 (by norm_num)
  have v14 : f 14 = 49496631 := hval 13 (by norm_num)
  have v15 : f 15 = 79408380 := hval 14 (by norm_num)
  by_cases hb : 13 ≤ n
  · obtain ⟨M, rfl⟩ : ∃ M, n = M + 13 := ⟨n - 13, by omega⟩
    have := recN f A ha hid hval M
    omega
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

theorem recQ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (3 + M) = Lin RC A (3 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 11 < n) : (f n : ℚ) = 9 * (f (n - 1) : ℚ) - 36 * (f (n - 2) : ℚ) + 84 * (f (n - 3) : ℚ) - 126 * (f (n - 4) : ℚ) + 126 * (f (n - 5) : ℚ) - 84 * (f (n - 6) : ℚ) + 36 * (f (n - 7) : ℚ) - 9 * (f (n - 8) : ℚ) + (f (n - 9) : ℚ) := by
  have := recZ f A ha hid hval n hn
  exact_mod_cast this

theorem poly (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (3 + M) = Lin RC A (3 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 2 < n) : (f n : ℚ) = (41/4032) * (n : ℚ) ^ 8 + (55/336) * (n : ℚ) ^ 7 + (733/480) * (n : ℚ) ^ 6 + (1037/120) * (n : ℚ) ^ 5 + (4789/192) * (n : ℚ) ^ 4 + (2125/48) * (n : ℚ) ^ 3 + (216821/5040) * (n : ℚ) ^ 2 + (9329/210) * (n : ℚ) + 4 := by
  have v1 : f 1 = 81 := hval 0 (by norm_num)
  have v2 : f 2 = 1296 := hval 1 (by norm_num)
  have v3 : f 3 = 7378 := hval 2 (by norm_num)
  have v4 : f 4 = 28541 := hval 3 (by norm_num)
  have v5 : f 5 = 90051 := hval 4 (by norm_num)
  have v6 : f 6 = 245055 := hval 5 (by norm_num)
  have v7 : f 7 = 595822 := hval 6 (by norm_num)
  have v8 : f 8 = 1325316 := hval 7 (by norm_num)
  have v9 : f 9 = 2742301 := hval 8 (by norm_num)
  have v10 : f 10 = 5343468 := hval 9 (by norm_num)
  have v11 : f 11 = 9896484 := hval 10 (by norm_num)
  have v12 : f 12 = 17548273 := hval 11 (by norm_num)
  have v13 : f 13 = 29963249 := hval 12 (by norm_num)
  have v14 : f 14 = 49496631 := hval 13 (by norm_num)
  have v15 : f 15 = 79408380 := hval 14 (by norm_num)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hs : n ≤ 11
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    rw [recQ f A ha hid hval (k + 9) (by omega), ih (k + 9 - 1) (by omega) (by omega), ih (k + 9 - 2) (by omega) (by omega), ih (k + 9 - 3) (by omega) (by omega), ih (k + 9 - 4) (by omega) (by omega), ih (k + 9 - 5) (by omega) (by omega), ih (k + 9 - 6) (by omega) (by omega), ih (k + 9 - 7) (by omega) (by omega), ih (k + 9 - 8) (by omega) (by omega), ih (k + 9 - 9) (by omega) (by omega)]
    simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega, show k + 9 - 9 = k + 0 by omega]
    push_cast
    ring

theorem gf (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (3 + M) = Lin RC A (3 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 9 =
    X * (81 + 567 * X - 1370 * X ^ 2 + 1991 * X ^ 3 + 132 * X ^ 4 - 4590 * X ^ 5 + 7855 * X ^ 6 - 6900 * X ^ 7 + 3514 * X ^ 8 - 990 * X ^ 9 + 120 * X ^ 10) := by
  have v1 : f 1 = 81 := hval 0 (by norm_num)
  have v2 : f 2 = 1296 := hval 1 (by norm_num)
  have v3 : f 3 = 7378 := hval 2 (by norm_num)
  have v4 : f 4 = 28541 := hval 3 (by norm_num)
  have v5 : f 5 = 90051 := hval 4 (by norm_num)
  have v6 : f 6 = 245055 := hval 5 (by norm_num)
  have v7 : f 7 = 595822 := hval 6 (by norm_num)
  have v8 : f 8 = 1325316 := hval 7 (by norm_num)
  have v9 : f 9 = 2742301 := hval 8 (by norm_num)
  have v10 : f 10 = 5343468 := hval 9 (by norm_num)
  have v11 : f 11 = 9896484 := hval 10 (by norm_num)
  have v12 : f 12 = 17548273 := hval 11 (by norm_num)
  have v13 : f 13 = 29963249 := hval 12 (by norm_num)
  have v14 : f 14 = 49496631 := hval 13 (by norm_num)
  have v15 : f 15 = 79408380 := hval 14 (by norm_num)
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hF
  have hmul : F * (1 - X) ^ 9 = F - C (9 : ℚ) * (X ^ 1 * F) + C (36 : ℚ) * (X ^ 2 * F) - C (84 : ℚ) * (X ^ 3 * F) + C (126 : ℚ) * (X ^ 4 * F) - C (126 : ℚ) * (X ^ 5 * F) + C (84 : ℚ) * (X ^ 6 * F) - C (36 : ℚ) * (X ^ 7 * F) + C (9 : ℚ) * (X ^ 8 * F) - X ^ 9 * F := by
    (try simp only [map_ofNat]); ring
  have hnum : (X * (81 + 567 * X - 1370 * X ^ 2 + 1991 * X ^ 3 + 132 * X ^ 4 - 4590 * X ^ 5 + 7855 * X ^ 6 - 6900 * X ^ 7 + 3514 * X ^ 8 - 990 * X ^ 9 + 120 * X ^ 10) : PowerSeries ℚ) = C (81 : ℚ) * X ^ 1 + C (567 : ℚ) * X ^ 2 - C (1370 : ℚ) * X ^ 3 + C (1991 : ℚ) * X ^ 4 + C (132 : ℚ) * X ^ 5 - C (4590 : ℚ) * X ^ 6 + C (7855 : ℚ) * X ^ 7 - C (6900 : ℚ) * X ^ 8 + C (3514 : ℚ) * X ^ 9 - C (990 : ℚ) * X ^ 10 + C (120 : ℚ) * X ^ 11 := by
    (try simp only [map_ofNat]); ring
  rw [hmul, hnum]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, hF, coeff_mk]
  by_cases hn : 12 ≤ n
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
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

theorem final (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (3 + M) = Lin RC A (3 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) :
    (∀ n : ℕ, 2 < n → (f n : ℚ) = (41/4032) * (n : ℚ) ^ 8 + (55/336) * (n : ℚ) ^ 7 + (733/480) * (n : ℚ) ^ 6 + (1037/120) * (n : ℚ) ^ 5 + (4789/192) * (n : ℚ) ^ 4 + (2125/48) * (n : ℚ) ^ 3 + (216821/5040) * (n : ℚ) ^ 2 + (9329/210) * (n : ℚ) + 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 9 =
      X * (81 + 567 * X - 1370 * X ^ 2 + 1991 * X ^ 3 + 132 * X ^ 4 - 4590 * X ^ 5 + 7855 * X ^ 6 - 6900 * X ^ 7 + 3514 * X ^ 8 - 990 * X ^ 9 + 120 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (f n : ℤ) = 9 * f (n - 1) - 36 * f (n - 2) + 84 * f (n - 3) - 126 * f (n - 4) + 126 * f (n - 5) - 84 * f (n - 6) + 36 * f (n - 7) - 9 * f (n - 8) + f (n - 9) :=
  ⟨fun n hn => poly f A ha hid hval n hn, gf f A ha hid hval, fun n hn => recZ f A ha hid hval n hn⟩

end PA224014

theorem OMA.solution : type_of% @OMA.S_oeis_a224014.main :=
  PA224014.final _ _ PA224014.a_eq PA224014.hid PA224014.hval
