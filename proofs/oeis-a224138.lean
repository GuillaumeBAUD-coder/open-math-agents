import OMAStatements.S_oeis_a224138
import Mathlib

/-!
Proof of the empirical formula and Barker's conjectures for OEIS A224138
(Number of 7 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal.).

Outline.
1. Generic part (namespace UG, proved for any number of rows): the array is read column by column.
   A line (row, diagonal or antidiagonal) is unimodal iff it has no valley; appending a column
   keeps every line valley-free iff no line that has already strictly descended rises again at the
   new cell (`UC_snoc`), and the descent flags update locally (`DS_snoc`). The state after a column
   is coded as a natural number (the column in base m plus one flag bit per line ending there), and
   the computable transition `okc`/`dc` is shown to match the semantics (`okc_stS`, `dc_stS`). This
   gives a(n + 1) as a sum of continuation counts `Wc n` over the admissible first columns
   (`count_eq`).
2. Certificate (checked by the kernel, `decide +kernel`): the list of the 610 reachable states,
   their successor lists, a lumping of the states into 131 blocks with equal continuation counts,
   and the block tables up to length 16. From them, the pointwise identity
   Sum_i (-1)^i C(8, i) Wc (n + 8 - i) s = 0 for n >= 6 and every reachable s, hence the
   binomial recurrence for a(n), n >= 15.
3. The recurrence, the polynomial and the generating function follow from the recurrence and
   the computed values a(1), ..., a(17).
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

namespace PA224138

open OMA.S_oeis_a224138 UG PowerSeries

def CO (_v : Fin 7 → Fin 2) : Prop := True

instance : DecidablePred CO := fun _ => instDecidableTrue

def COc (_c : ℕ) : Bool := true

theorem hCO (v : Fin 7 → Fin 2) : COc (ccode v) = true ↔ CO v := by simp [COc, CO]

theorem hU : ∀ t ∈ ([2] : List ℕ), t < 3 := by decide

theorem uc_anti {n : ℕ} (x : Fin 7 → Fin n → Fin 2) : AntidiagUnimodal x ↔ UC 2 (fun j i => x i j) := by
  constructor
  · intro h j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    exact h i1 i2 i3 j1 j2 j3 h12 h23 (by unfold al at a1 a2; omega) (by unfold al at a1 a2; omega)
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    exact h j1 j2 j3 i1 i2 i3 h12 h23 (by unfold al; omega) (by unfold al; omega)

theorem rn_iff {n : ℕ} (x : Fin 7 → Fin n → Fin 2) : (∀ i, Monotone (x i)) ↔ RN (fun j i => x i j) := by
  constructor
  · intro h j1 j2 hj i; exact h i hj
  · intro h i j1 j2 hj; exact h j1 j2 hj i

theorem good_iff {n : ℕ} (x : Fin 7 → Fin n → Fin 2) : Good x ↔ P CO true [2] (fun j i => x i j) := by
  unfold Good P
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, CO,
    forall_const, true_and, implies_true, eq_self_iff_true, true_implies, uc_anti, rn_iff]

theorem a_eq (N : ℕ) : a (N + 1) = Ac 7 2 COc true [2] N := by
  rw [a, Ac, ← count_eq CO COc hCO true [2] hU N]
  apply Finset.card_equiv (Equiv.piComm _)
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact good_iff x

def RL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
    70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
    94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
    114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 2097154, 2097158,
    2097162, 2097166, 2097170, 2097174, 2097178, 2097182, 2097186, 2097190, 2097194, 2097198,
    2097202, 2097206, 2097210, 2097214, 2097218, 2097222, 2097226, 2097230, 2097234, 2097238,
    2097242, 2097246, 2097250, 2097254, 2097258, 2097262, 2097266, 2097270, 2097274, 2097278,
    4194308, 4194309, 4194316, 4194317, 4194324, 4194325, 4194332, 4194333, 4194340, 4194341,
    4194348, 4194349, 4194356, 4194357, 4194364, 4194365, 4194372, 4194373, 4194380, 4194381,
    4194388, 4194389, 4194396, 4194397, 4194404, 4194405, 4194412, 4194413, 4194420, 4194421,
    4194428, 4194429, 8388616, 8388617, 8388618, 8388619, 8388632, 8388633, 8388634, 8388635,
    8388648, 8388649, 8388650, 8388651, 8388664, 8388665, 8388666, 8388667, 8388680, 8388681,
    8388682, 8388683, 8388696, 8388697, 8388698, 8388699, 8388712, 8388713, 8388714, 8388715,
    8388728, 8388729, 8388730, 8388731, 10485770, 10485786, 10485802, 10485818, 10485834, 10485850,
    10485866, 10485882, 16777232, 16777233, 16777234, 16777235, 16777236, 16777237, 16777238,
    16777239, 16777264, 16777265, 16777266, 16777267, 16777268, 16777269, 16777270, 16777271,
    16777296, 16777297, 16777298, 16777299, 16777300, 16777301, 16777302, 16777303, 16777328,
    16777329, 16777330, 16777331, 16777332, 16777333, 16777334, 16777335, 18874386, 18874390,
    18874418, 18874422, 18874450, 18874454, 18874482, 18874486, 20971540, 20971541, 20971572,
    20971573, 20971604, 20971605, 20971636, 20971637, 33554464, 33554465, 33554466, 33554467,
    33554468, 33554469, 33554470, 33554471, 33554472, 33554473, 33554474, 33554475, 33554476,
    33554477, 33554478, 33554479, 33554528, 33554529, 33554530, 33554531, 33554532, 33554533,
    33554534, 33554535, 33554536, 33554537, 33554538, 33554539, 33554540, 33554541, 33554542,
    33554543, 35651618, 35651622, 35651626, 35651630, 35651682, 35651686, 35651690, 35651694,
    37748772, 37748773, 37748780, 37748781, 37748836, 37748837, 37748844, 37748845, 41943080,
    41943081, 41943082, 41943083, 41943144, 41943145, 41943146, 41943147, 44040234, 44040298,
    67108928, 67108929, 67108930, 67108931, 67108932, 67108933, 67108934, 67108935, 67108936,
    67108937, 67108938, 67108939, 67108940, 67108941, 67108942, 67108943, 67108944, 67108945,
    67108946, 67108947, 67108948, 67108949, 67108950, 67108951, 67108952, 67108953, 67108954,
    67108955, 67108956, 67108957, 67108958, 67108959, 69206082, 69206086, 69206090, 69206094,
    69206098, 69206102, 69206106, 69206110, 71303236, 71303237, 71303244, 71303245, 71303252,
    71303253, 71303260, 71303261, 75497544, 75497545, 75497546, 75497547, 75497560, 75497561,
    75497562, 75497563, 77594698, 77594714, 83886160, 83886161, 83886162, 83886163, 83886164,
    83886165, 83886166, 83886167, 85983314, 85983318, 88080468, 88080469, 6291460, 6291468,
    6291476, 6291484, 6291492, 6291500, 6291508, 6291516, 6291524, 6291532, 6291540, 6291548,
    6291556, 6291564, 6291572, 6291580, 23068692, 23068724, 23068756, 23068788, 39845924, 39845932,
    39845988, 39845996, 73400388, 73400396, 73400404, 73400412, 90177620, 12582920, 12582921,
    12582936, 12582937, 12582952, 12582953, 12582968, 12582969, 12582984, 12582985, 12583000,
    12583001, 12583016, 12583017, 12583032, 12583033, 46137384, 46137385, 46137448, 46137449,
    79691848, 79691849, 79691864, 79691865, 25165840, 25165841, 25165842, 25165843, 25165872,
    25165873, 25165874, 25165875, 25165904, 25165905, 25165906, 25165907, 25165936, 25165937,
    25165938, 25165939, 27262994, 27263026, 27263058, 27263090, 92274768, 92274769, 92274770,
    92274771, 94371922, 50331680, 50331681, 50331682, 50331683, 50331684, 50331685, 50331686,
    50331687, 50331744, 50331745, 50331746, 50331747, 50331748, 50331749, 50331750, 50331751,
    52428834, 52428838, 52428898, 52428902, 54525988, 54525989, 54526052, 54526053, 56623140,
    56623204, 100663360, 100663361, 100663362, 100663363, 100663364, 100663365, 100663366,
    100663367, 100663368, 100663369, 100663370, 100663371, 100663372, 100663373, 100663374,
    100663375, 102760514, 102760518, 102760522, 102760526, 104857668, 104857669, 104857676,
    104857677, 109051976, 109051977, 109051978, 109051979, 111149130, 106954820, 106954828,
    113246280, 113246281, 14680072, 14680088, 14680104, 14680120, 14680136, 14680152, 14680168,
    14680184, 48234536, 48234600, 81789000, 81789016, 115343432, 29360144, 29360145, 29360176,
    29360177, 29360208, 29360209, 29360240, 29360241, 96469072, 96469073, 58720288, 58720289,
    58720290, 58720291, 58720352, 58720353, 58720354, 58720355, 60817442, 60817506, 117440576,
    117440577, 117440578, 117440579, 117440580, 117440581, 117440582, 117440583, 119537730,
    119537734, 121634884, 121634885, 123732036, 31457296, 31457328, 31457360, 31457392, 98566224,
    62914592, 62914593, 62914656, 62914657, 125829184, 125829185, 125829186, 125829187, 127926338,
    65011744, 65011808, 130023488, 130023489, 132120640]

def SI : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
    44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
    68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91,
    92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
    112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127], [1, 3, 5, 7,
    9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55,
    57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 97, 99, 101,
    103, 105, 107, 109, 111, 113, 115, 117, 119, 121, 123, 125, 127], [128, 3, 129, 7, 130, 11,
    131, 15, 132, 19, 133, 23, 134, 27, 135, 31, 136, 35, 137, 39, 138, 43, 139, 47, 140, 51, 141,
    55, 142, 59, 143, 63, 144, 67, 145, 71, 146, 75, 147, 79, 148, 83, 149, 87, 150, 91, 151, 95,
    152, 99, 153, 103, 154, 107, 155, 111, 156, 115, 157, 119, 158, 123, 159, 127], [3, 7, 11, 15,
    19, 23, 27, 31, 35, 39, 43, 47, 51, 55, 59, 63, 67, 71, 75, 79, 83, 87, 91, 95, 99, 103, 107,
    111, 115, 119, 123, 127], [160, 161, 6, 7, 162, 163, 14, 15, 164, 165, 22, 23, 166, 167, 30,
    31, 168, 169, 38, 39, 170, 171, 46, 47, 172, 173, 54, 55, 174, 175, 62, 63, 176, 177, 70, 71,
    178, 179, 78, 79, 180, 181, 86, 87, 182, 183, 94, 95, 184, 185, 102, 103, 186, 187, 110, 111,
    188, 189, 118, 119, 190, 191, 126, 127], [161, 7, 163, 15, 165, 23, 167, 31, 169, 39, 171, 47,
    173, 55, 175, 63, 177, 71, 179, 79, 181, 87, 183, 95, 185, 103, 187, 111, 189, 119, 191, 127],
    [129, 7, 131, 15, 133, 23, 135, 31, 137, 39, 139, 47, 141, 55, 143, 63, 145, 71, 147, 79, 149,
    87, 151, 95, 153, 103, 155, 111, 157, 119, 159, 127], [7, 15, 23, 31, 39, 47, 55, 63, 71, 79,
    87, 95, 103, 111, 119, 127], [192, 193, 194, 195, 12, 13, 14, 15, 196, 197, 198, 199, 28, 29,
    30, 31, 200, 201, 202, 203, 44, 45, 46, 47, 204, 205, 206, 207, 60, 61, 62, 63, 208, 209, 210,
    211, 76, 77, 78, 79, 212, 213, 214, 215, 92, 93, 94, 95, 216, 217, 218, 219, 108, 109, 110,
    111, 220, 221, 222, 223, 124, 125, 126, 127], [193, 195, 13, 15, 197, 199, 29, 31, 201, 203,
    45, 47, 205, 207, 61, 63, 209, 211, 77, 79, 213, 215, 93, 95, 217, 219, 109, 111, 221, 223,
    125, 127], [224, 195, 131, 15, 225, 199, 135, 31, 226, 203, 139, 47, 227, 207, 143, 63, 228,
    211, 147, 79, 229, 215, 151, 95, 230, 219, 155, 111, 231, 223, 159, 127], [195, 15, 199, 31,
    203, 47, 207, 63, 211, 79, 215, 95, 219, 111, 223, 127], [162, 163, 14, 15, 166, 167, 30, 31,
    170, 171, 46, 47, 174, 175, 62, 63, 178, 179, 78, 79, 182, 183, 94, 95, 186, 187, 110, 111,
    190, 191, 126, 127], [163, 15, 167, 31, 171, 47, 175, 63, 179, 79, 183, 95, 187, 111, 191,
    127], [131, 15, 135, 31, 139, 47, 143, 63, 147, 79, 151, 95, 155, 111, 159, 127], [15, 31, 47,
    63, 79, 95, 111, 127], [232, 233, 234, 235, 236, 237, 238, 239, 24, 25, 26, 27, 28, 29, 30, 31,
    240, 241, 242, 243, 244, 245, 246, 247, 56, 57, 58, 59, 60, 61, 62, 63, 248, 249, 250, 251,
    252, 253, 254, 255, 88, 89, 90, 91, 92, 93, 94, 95, 256, 257, 258, 259, 260, 261, 262, 263,
    120, 121, 122, 123, 124, 125, 126, 127], [233, 235, 237, 239, 25, 27, 29, 31, 241, 243, 245,
    247, 57, 59, 61, 63, 249, 251, 253, 255, 89, 91, 93, 95, 257, 259, 261, 263, 121, 123, 125,
    127], [264, 235, 265, 239, 134, 27, 135, 31, 266, 243, 267, 247, 142, 59, 143, 63, 268, 251,
    269, 255, 150, 91, 151, 95, 270, 259, 271, 263, 158, 123, 159, 127], [235, 239, 27, 31, 243,
    247, 59, 63, 251, 255, 91, 95, 259, 263, 123, 127], [272, 273, 238, 239, 166, 167, 30, 31, 274,
    275, 246, 247, 174, 175, 62, 63, 276, 277, 254, 255, 182, 183, 94, 95, 278, 279, 262, 263, 190,
    191, 126, 127], [273, 239, 167, 31, 275, 247, 175, 63, 277, 255, 183, 95, 279, 263, 191, 127],
    [265, 239, 135, 31, 267, 247, 143, 63, 269, 255, 151, 95, 271, 263, 159, 127], [239, 31, 247,
    63, 255, 95, 263, 127], [196, 197, 198, 199, 28, 29, 30, 31, 204, 205, 206, 207, 60, 61, 62,
    63, 212, 213, 214, 215, 92, 93, 94, 95, 220, 221, 222, 223, 124, 125, 126, 127], [197, 199, 29,
    31, 205, 207, 61, 63, 213, 215, 93, 95, 221, 223, 125, 127], [225, 199, 135, 31, 227, 207, 143,
    63, 229, 215, 151, 95, 231, 223, 159, 127], [199, 31, 207, 63, 215, 95, 223, 127], [166, 167,
    30, 31, 174, 175, 62, 63, 182, 183, 94, 95, 190, 191, 126, 127], [167, 31, 175, 63, 183, 95,
    191, 127], [135, 31, 143, 63, 151, 95, 159, 127], [31, 63, 95, 127], [280, 281, 282, 283, 284,
    285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
    58, 59, 60, 61, 62, 63, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309,
    310, 311, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127],
    [281, 283, 285, 287, 289, 291, 293, 295, 49, 51, 53, 55, 57, 59, 61, 63, 297, 299, 301, 303,
    305, 307, 309, 311, 113, 115, 117, 119, 121, 123, 125, 127], [312, 283, 313, 287, 314, 291,
    315, 295, 140, 51, 141, 55, 142, 59, 143, 63, 316, 299, 317, 303, 318, 307, 319, 311, 156, 115,
    157, 119, 158, 123, 159, 127], [283, 287, 291, 295, 51, 55, 59, 63, 299, 303, 307, 311, 115,
    119, 123, 127], [320, 321, 286, 287, 322, 323, 294, 295, 172, 173, 54, 55, 174, 175, 62, 63,
    324, 325, 302, 303, 326, 327, 310, 311, 188, 189, 118, 119, 190, 191, 126, 127], [321, 287,
    323, 295, 173, 55, 175, 63, 325, 303, 327, 311, 189, 119, 191, 127], [313, 287, 315, 295, 141,
    55, 143, 63, 317, 303, 319, 311, 157, 119, 159, 127], [287, 295, 55, 63, 303, 311, 119, 127],
    [328, 329, 330, 331, 292, 293, 294, 295, 204, 205, 206, 207, 60, 61, 62, 63, 332, 333, 334,
    335, 308, 309, 310, 311, 220, 221, 222, 223, 124, 125, 126, 127], [329, 331, 293, 295, 205,
    207, 61, 63, 333, 335, 309, 311, 221, 223, 125, 127], [336, 331, 315, 295, 227, 207, 143, 63,
    337, 335, 319, 311, 231, 223, 159, 127], [331, 295, 207, 63, 335, 311, 223, 127], [322, 323,
    294, 295, 174, 175, 62, 63, 326, 327, 310, 311, 190, 191, 126, 127], [323, 295, 175, 63, 327,
    311, 191, 127], [315, 295, 143, 63, 319, 311, 159, 127], [295, 63, 311, 127], [240, 241, 242,
    243, 244, 245, 246, 247, 56, 57, 58, 59, 60, 61, 62, 63, 256, 257, 258, 259, 260, 261, 262,
    263, 120, 121, 122, 123, 124, 125, 126, 127], [241, 243, 245, 247, 57, 59, 61, 63, 257, 259,
    261, 263, 121, 123, 125, 127], [266, 243, 267, 247, 142, 59, 143, 63, 270, 259, 271, 263, 158,
    123, 159, 127], [243, 247, 59, 63, 259, 263, 123, 127], [274, 275, 246, 247, 174, 175, 62, 63,
    278, 279, 262, 263, 190, 191, 126, 127], [275, 247, 175, 63, 279, 263, 191, 127], [267, 247,
    143, 63, 271, 263, 159, 127], [247, 63, 263, 127], [204, 205, 206, 207, 60, 61, 62, 63, 220,
    221, 222, 223, 124, 125, 126, 127], [205, 207, 61, 63, 221, 223, 125, 127], [227, 207, 143, 63,
    231, 223, 159, 127], [207, 63, 223, 127], [174, 175, 62, 63, 190, 191, 126, 127], [175, 63,
    191, 127], [143, 63, 159, 127], [63, 127], [338, 339, 340, 341, 342, 343, 344, 345, 346, 347,
    348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366,
    367, 368, 369, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112,
    113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127], [339, 341, 343,
    345, 347, 349, 351, 353, 355, 357, 359, 361, 363, 365, 367, 369, 97, 99, 101, 103, 105, 107,
    109, 111, 113, 115, 117, 119, 121, 123, 125, 127], [370, 341, 371, 345, 372, 349, 373, 353,
    374, 357, 375, 361, 376, 365, 377, 369, 152, 99, 153, 103, 154, 107, 155, 111, 156, 115, 157,
    119, 158, 123, 159, 127], [341, 345, 349, 353, 357, 361, 365, 369, 99, 103, 107, 111, 115, 119,
    123, 127], [378, 379, 344, 345, 380, 381, 352, 353, 382, 383, 360, 361, 384, 385, 368, 369,
    184, 185, 102, 103, 186, 187, 110, 111, 188, 189, 118, 119, 190, 191, 126, 127], [379, 345,
    381, 353, 383, 361, 385, 369, 185, 103, 187, 111, 189, 119, 191, 127], [371, 345, 373, 353,
    375, 361, 377, 369, 153, 103, 155, 111, 157, 119, 159, 127], [345, 353, 361, 369, 103, 111,
    119, 127], [386, 387, 388, 389, 350, 351, 352, 353, 390, 391, 392, 393, 366, 367, 368, 369,
    216, 217, 218, 219, 108, 109, 110, 111, 220, 221, 222, 223, 124, 125, 126, 127], [387, 389,
    351, 353, 391, 393, 367, 369, 217, 219, 109, 111, 221, 223, 125, 127], [394, 389, 373, 353,
    395, 393, 377, 369, 230, 219, 155, 111, 231, 223, 159, 127], [389, 353, 393, 369, 219, 111,
    223, 127], [380, 381, 352, 353, 384, 385, 368, 369, 186, 187, 110, 111, 190, 191, 126, 127],
    [381, 353, 385, 369, 187, 111, 191, 127], [373, 353, 377, 369, 155, 111, 159, 127], [353, 369,
    111, 127], [396, 397, 398, 399, 400, 401, 402, 403, 362, 363, 364, 365, 366, 367, 368, 369,
    256, 257, 258, 259, 260, 261, 262, 263, 120, 121, 122, 123, 124, 125, 126, 127], [397, 399,
    401, 403, 363, 365, 367, 369, 257, 259, 261, 263, 121, 123, 125, 127], [404, 399, 405, 403,
    376, 365, 377, 369, 270, 259, 271, 263, 158, 123, 159, 127], [399, 403, 365, 369, 259, 263,
    123, 127], [406, 407, 402, 403, 384, 385, 368, 369, 278, 279, 262, 263, 190, 191, 126, 127],
    [407, 403, 385, 369, 279, 263, 191, 127], [405, 403, 377, 369, 271, 263, 159, 127], [403, 369,
    263, 127], [390, 391, 392, 393, 366, 367, 368, 369, 220, 221, 222, 223, 124, 125, 126, 127],
    [391, 393, 367, 369, 221, 223, 125, 127], [395, 393, 377, 369, 231, 223, 159, 127], [393, 369,
    223, 127], [384, 385, 368, 369, 190, 191, 126, 127], [385, 369, 191, 127], [377, 369, 159,
    127], [369, 127], [296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310,
    311, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127], [297,
    299, 301, 303, 305, 307, 309, 311, 113, 115, 117, 119, 121, 123, 125, 127], [316, 299, 317,
    303, 318, 307, 319, 311, 156, 115, 157, 119, 158, 123, 159, 127], [299, 303, 307, 311, 115,
    119, 123, 127], [324, 325, 302, 303, 326, 327, 310, 311, 188, 189, 118, 119, 190, 191, 126,
    127], [325, 303, 327, 311, 189, 119, 191, 127], [317, 303, 319, 311, 157, 119, 159, 127], [303,
    311, 119, 127], [332, 333, 334, 335, 308, 309, 310, 311, 220, 221, 222, 223, 124, 125, 126,
    127], [333, 335, 309, 311, 221, 223, 125, 127], [337, 335, 319, 311, 231, 223, 159, 127], [335,
    311, 223, 127], [326, 327, 310, 311, 190, 191, 126, 127], [327, 311, 191, 127], [319, 311, 159,
    127], [311, 127], [256, 257, 258, 259, 260, 261, 262, 263, 120, 121, 122, 123, 124, 125, 126,
    127], [257, 259, 261, 263, 121, 123, 125, 127], [270, 259, 271, 263, 158, 123, 159, 127], [259,
    263, 123, 127], [278, 279, 262, 263, 190, 191, 126, 127], [279, 263, 191, 127], [271, 263, 159,
    127], [263, 127], [220, 221, 222, 223, 124, 125, 126, 127], [221, 223, 125, 127], [231, 223,
    159, 127], [223, 127], [190, 191, 126, 127], [191, 127], [159, 127], [127], [128, 3, 129, 7,
    130, 11, 131, 15, 132, 19, 133, 23, 134, 27, 135, 31, 136, 35, 137, 39, 138, 43, 139, 47, 140,
    51, 141, 55, 142, 59, 143, 63, 144, 67, 145, 71, 146, 75, 147, 79, 148, 83, 149, 87, 150, 91,
    151, 95, 152, 99, 153, 103, 154, 107, 155, 111, 156, 115, 157, 119, 158, 123, 159, 127], [129,
    7, 131, 15, 133, 23, 135, 31, 137, 39, 139, 47, 141, 55, 143, 63, 145, 71, 147, 79, 149, 87,
    151, 95, 153, 103, 155, 111, 157, 119, 159, 127], [224, 195, 131, 15, 225, 199, 135, 31, 226,
    203, 139, 47, 227, 207, 143, 63, 228, 211, 147, 79, 229, 215, 151, 95, 230, 219, 155, 111, 231,
    223, 159, 127], [131, 15, 135, 31, 139, 47, 143, 63, 147, 79, 151, 95, 155, 111, 159, 127],
    [264, 235, 265, 239, 134, 27, 135, 31, 266, 243, 267, 247, 142, 59, 143, 63, 268, 251, 269,
    255, 150, 91, 151, 95, 270, 259, 271, 263, 158, 123, 159, 127], [265, 239, 135, 31, 267, 247,
    143, 63, 269, 255, 151, 95, 271, 263, 159, 127], [225, 199, 135, 31, 227, 207, 143, 63, 229,
    215, 151, 95, 231, 223, 159, 127], [135, 31, 143, 63, 151, 95, 159, 127], [312, 283, 313, 287,
    314, 291, 315, 295, 140, 51, 141, 55, 142, 59, 143, 63, 316, 299, 317, 303, 318, 307, 319, 311,
    156, 115, 157, 119, 158, 123, 159, 127], [313, 287, 315, 295, 141, 55, 143, 63, 317, 303, 319,
    311, 157, 119, 159, 127], [336, 331, 315, 295, 227, 207, 143, 63, 337, 335, 319, 311, 231, 223,
    159, 127], [315, 295, 143, 63, 319, 311, 159, 127], [266, 243, 267, 247, 142, 59, 143, 63, 270,
    259, 271, 263, 158, 123, 159, 127], [267, 247, 143, 63, 271, 263, 159, 127], [227, 207, 143,
    63, 231, 223, 159, 127], [143, 63, 159, 127], [370, 341, 371, 345, 372, 349, 373, 353, 374,
    357, 375, 361, 376, 365, 377, 369, 152, 99, 153, 103, 154, 107, 155, 111, 156, 115, 157, 119,
    158, 123, 159, 127], [371, 345, 373, 353, 375, 361, 377, 369, 153, 103, 155, 111, 157, 119,
    159, 127], [394, 389, 373, 353, 395, 393, 377, 369, 230, 219, 155, 111, 231, 223, 159, 127],
    [373, 353, 377, 369, 155, 111, 159, 127], [404, 399, 405, 403, 376, 365, 377, 369, 270, 259,
    271, 263, 158, 123, 159, 127], [405, 403, 377, 369, 271, 263, 159, 127], [395, 393, 377, 369,
    231, 223, 159, 127], [377, 369, 159, 127], [316, 299, 317, 303, 318, 307, 319, 311, 156, 115,
    157, 119, 158, 123, 159, 127], [317, 303, 319, 311, 157, 119, 159, 127], [337, 335, 319, 311,
    231, 223, 159, 127], [319, 311, 159, 127], [270, 259, 271, 263, 158, 123, 159, 127], [271, 263,
    159, 127], [231, 223, 159, 127], [159, 127], [408, 129, 409, 131, 410, 133, 411, 135, 412, 137,
    413, 139, 414, 141, 415, 143, 416, 145, 417, 147, 418, 149, 419, 151, 420, 153, 421, 155, 422,
    157, 423, 159], [], [409, 131, 411, 135, 413, 139, 415, 143, 417, 147, 419, 151, 421, 155, 423,
    159], [], [424, 265, 411, 135, 425, 267, 415, 143, 426, 269, 419, 151, 427, 271, 423, 159], [],
    [411, 135, 415, 143, 419, 151, 423, 159], [], [428, 313, 429, 315, 414, 141, 415, 143, 430,
    317, 431, 319, 422, 157, 423, 159], [], [429, 315, 415, 143, 431, 319, 423, 159], [], [425,
    267, 415, 143, 427, 271, 423, 159], [], [415, 143, 423, 159], [], [432, 371, 433, 373, 434,
    375, 435, 377, 420, 153, 421, 155, 422, 157, 423, 159], [], [433, 373, 435, 377, 421, 155, 423,
    159], [], [436, 405, 435, 377, 427, 271, 423, 159], [], [435, 377, 423, 159], [], [430, 317,
    431, 319, 422, 157, 423, 159], [], [431, 319, 423, 159], [], [427, 271, 423, 159], [], [423,
    159], [], [437, 438, 162, 163, 439, 440, 166, 167, 441, 442, 170, 171, 443, 444, 174, 175, 445,
    446, 178, 179, 447, 448, 182, 183, 449, 450, 186, 187, 451, 452, 190, 191], [438, 163, 440,
    167, 442, 171, 444, 175, 446, 179, 448, 183, 450, 187, 452, 191], [], [], [439, 440, 166, 167,
    443, 444, 174, 175, 447, 448, 182, 183, 451, 452, 190, 191], [440, 167, 444, 175, 448, 183,
    452, 191], [], [], [453, 454, 322, 323, 443, 444, 174, 175, 455, 456, 326, 327, 451, 452, 190,
    191], [454, 323, 444, 175, 456, 327, 452, 191], [], [], [443, 444, 174, 175, 451, 452, 190,
    191], [444, 175, 452, 191], [], [], [457, 458, 380, 381, 459, 460, 384, 385, 449, 450, 186,
    187, 451, 452, 190, 191], [458, 381, 460, 385, 450, 187, 452, 191], [], [], [459, 460, 384,
    385, 451, 452, 190, 191], [460, 385, 452, 191], [], [], [455, 456, 326, 327, 451, 452, 190,
    191], [456, 327, 452, 191], [], [], [451, 452, 190, 191], [452, 191], [], [], [], [], [], [],
    [], [], [], [], [461, 462, 463, 464, 196, 197, 198, 199, 465, 466, 467, 468, 204, 205, 206,
    207, 469, 470, 471, 472, 212, 213, 214, 215, 473, 474, 475, 476, 220, 221, 222, 223], [462,
    464, 197, 199, 466, 468, 205, 207, 470, 472, 213, 215, 474, 476, 221, 223], [477, 464, 225,
    199, 478, 468, 227, 207, 479, 472, 229, 215, 480, 476, 231, 223], [464, 199, 468, 207, 472,
    215, 476, 223], [], [], [], [], [465, 466, 467, 468, 204, 205, 206, 207, 473, 474, 475, 476,
    220, 221, 222, 223], [466, 468, 205, 207, 474, 476, 221, 223], [478, 468, 227, 207, 480, 476,
    231, 223], [468, 207, 476, 223], [], [], [], [], [481, 482, 483, 484, 390, 391, 392, 393, 473,
    474, 475, 476, 220, 221, 222, 223], [482, 484, 391, 393, 474, 476, 221, 223], [485, 484, 395,
    393, 480, 476, 231, 223], [484, 393, 476, 223], [], [], [], [], [473, 474, 475, 476, 220, 221,
    222, 223], [474, 476, 221, 223], [480, 476, 231, 223], [476, 223], [], [], [], [], [477, 464,
    225, 199, 478, 468, 227, 207, 479, 472, 229, 215, 480, 476, 231, 223], [], [478, 468, 227, 207,
    480, 476, 231, 223], [], [485, 484, 395, 393, 480, 476, 231, 223], [], [480, 476, 231, 223],
    [], [], [], [], [], [], [], [], [], [486, 487, 488, 489, 490, 491, 492, 493, 240, 241, 242,
    243, 244, 245, 246, 247, 494, 495, 496, 497, 498, 499, 500, 501, 256, 257, 258, 259, 260, 261,
    262, 263], [487, 489, 491, 493, 241, 243, 245, 247, 495, 497, 499, 501, 257, 259, 261, 263],
    [502, 489, 503, 493, 266, 243, 267, 247, 504, 497, 505, 501, 270, 259, 271, 263], [489, 493,
    243, 247, 497, 501, 259, 263], [506, 507, 492, 493, 274, 275, 246, 247, 508, 509, 500, 501,
    278, 279, 262, 263], [507, 493, 275, 247, 509, 501, 279, 263], [503, 493, 267, 247, 505, 501,
    271, 263], [493, 247, 501, 263], [], [], [], [], [], [], [], [], [494, 495, 496, 497, 498, 499,
    500, 501, 256, 257, 258, 259, 260, 261, 262, 263], [495, 497, 499, 501, 257, 259, 261, 263],
    [504, 497, 505, 501, 270, 259, 271, 263], [497, 501, 259, 263], [508, 509, 500, 501, 278, 279,
    262, 263], [509, 501, 279, 263], [505, 501, 271, 263], [501, 263], [], [], [], [], [], [], [],
    [], [502, 489, 503, 493, 266, 243, 267, 247, 504, 497, 505, 501, 270, 259, 271, 263], [503,
    493, 267, 247, 505, 501, 271, 263], [], [], [504, 497, 505, 501, 270, 259, 271, 263], [505,
    501, 271, 263], [], [], [510, 503, 425, 267, 511, 505, 427, 271], [], [], [], [511, 505, 427,
    271], [], [], [], [], [], [], [], [], [], [], [], [], [], [512, 513, 514, 515, 516, 517, 518,
    519, 520, 521, 522, 523, 524, 525, 526, 527, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305,
    306, 307, 308, 309, 310, 311], [513, 515, 517, 519, 521, 523, 525, 527, 297, 299, 301, 303,
    305, 307, 309, 311], [528, 515, 529, 519, 530, 523, 531, 527, 316, 299, 317, 303, 318, 307,
    319, 311], [515, 519, 523, 527, 299, 303, 307, 311], [532, 533, 518, 519, 534, 535, 526, 527,
    324, 325, 302, 303, 326, 327, 310, 311], [533, 519, 535, 527, 325, 303, 327, 311], [529, 519,
    531, 527, 317, 303, 319, 311], [519, 527, 303, 311], [536, 537, 538, 539, 524, 525, 526, 527,
    332, 333, 334, 335, 308, 309, 310, 311], [537, 539, 525, 527, 333, 335, 309, 311], [540, 539,
    531, 527, 337, 335, 319, 311], [539, 527, 335, 311], [534, 535, 526, 527, 326, 327, 310, 311],
    [535, 527, 327, 311], [531, 527, 319, 311], [527, 311], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [528, 515, 529, 519, 530, 523, 531, 527, 316, 299, 317, 303, 318, 307,
    319, 311], [529, 519, 531, 527, 317, 303, 319, 311], [540, 539, 531, 527, 337, 335, 319, 311],
    [531, 527, 319, 311], [], [], [], [], [541, 529, 542, 531, 430, 317, 431, 319], [], [542, 531,
    431, 319], [], [], [], [], [], [543, 544, 534, 535, 455, 456, 326, 327], [544, 535, 456, 327],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [408, 129, 409,
    131, 410, 133, 411, 135, 412, 137, 413, 139, 414, 141, 415, 143, 416, 145, 417, 147, 418, 149,
    419, 151, 420, 153, 421, 155, 422, 157, 423, 159], [409, 131, 411, 135, 413, 139, 415, 143,
    417, 147, 419, 151, 421, 155, 423, 159], [424, 265, 411, 135, 425, 267, 415, 143, 426, 269,
    419, 151, 427, 271, 423, 159], [411, 135, 415, 143, 419, 151, 423, 159], [428, 313, 429, 315,
    414, 141, 415, 143, 430, 317, 431, 319, 422, 157, 423, 159], [429, 315, 415, 143, 431, 319,
    423, 159], [425, 267, 415, 143, 427, 271, 423, 159], [415, 143, 423, 159], [432, 371, 433, 373,
    434, 375, 435, 377, 420, 153, 421, 155, 422, 157, 423, 159], [433, 373, 435, 377, 421, 155,
    423, 159], [436, 405, 435, 377, 427, 271, 423, 159], [435, 377, 423, 159], [430, 317, 431, 319,
    422, 157, 423, 159], [431, 319, 423, 159], [427, 271, 423, 159], [423, 159], [], [], [], [],
    [510, 503, 425, 267, 511, 505, 427, 271], [], [511, 505, 427, 271], [], [541, 529, 542, 531,
    430, 317, 431, 319], [542, 531, 431, 319], [], [], [], [545, 409, 546, 411, 547, 413, 548, 415,
    549, 417, 550, 419, 551, 421, 552, 423], [], [546, 411, 548, 415, 550, 419, 552, 423], [],
    [553, 429, 548, 415, 554, 431, 552, 423], [], [548, 415, 552, 423], [], [555, 433, 556, 435,
    551, 421, 552, 423], [], [556, 435, 552, 423], [], [554, 431, 552, 423], [], [552, 423], [],
    [], [], [], [], [557, 542, 554, 431], [], [], [], [558, 559, 439, 440, 560, 561, 443, 444, 562,
    563, 447, 448, 564, 565, 451, 452], [559, 440, 561, 444, 563, 448, 565, 452], [], [], [560,
    561, 443, 444, 564, 565, 451, 452], [561, 444, 565, 452], [], [], [566, 567, 459, 460, 564,
    565, 451, 452], [567, 460, 565, 452], [], [], [564, 565, 451, 452], [565, 452], [], [], [], [],
    [], [], [], [], [], [], [], [568, 569, 570, 571, 465, 466, 467, 468, 572, 573, 574, 575, 473,
    474, 475, 476], [569, 571, 466, 468, 573, 575, 474, 476], [576, 571, 478, 468, 577, 575, 480,
    476], [571, 468, 575, 476], [], [], [], [], [572, 573, 574, 575, 473, 474, 475, 476], [573,
    575, 474, 476], [577, 575, 480, 476], [575, 476], [], [], [], [], [576, 571, 478, 468, 577,
    575, 480, 476], [], [577, 575, 480, 476], [], [], [], [], [], [], [], [578, 579, 580, 581, 582,
    583, 584, 585, 494, 495, 496, 497, 498, 499, 500, 501], [579, 581, 583, 585, 495, 497, 499,
    501], [586, 581, 587, 585, 504, 497, 505, 501], [581, 585, 497, 501], [588, 589, 584, 585, 508,
    509, 500, 501], [589, 585, 509, 501], [587, 585, 505, 501], [585, 501], [], [], [], [], [], [],
    [], [], [586, 581, 587, 585, 504, 497, 505, 501], [587, 585, 505, 501], [], [], [590, 587, 511,
    505], [], [], [], [], [], [], [], [], [590, 587, 511, 505], [], [], [], [545, 409, 546, 411,
    547, 413, 548, 415, 549, 417, 550, 419, 551, 421, 552, 423], [546, 411, 548, 415, 550, 419,
    552, 423], [553, 429, 548, 415, 554, 431, 552, 423], [548, 415, 552, 423], [555, 433, 556, 435,
    551, 421, 552, 423], [556, 435, 552, 423], [554, 431, 552, 423], [552, 423], [], [], [557, 542,
    554, 431], [], [], [591, 546, 592, 548, 593, 550, 594, 552], [], [592, 548, 594, 552], [],
    [595, 556, 594, 552], [], [594, 552], [], [], [], [596, 597, 560, 561, 598, 599, 564, 565],
    [597, 561, 599, 565], [], [], [598, 599, 564, 565], [599, 565], [], [], [], [], [600, 601, 602,
    603, 572, 573, 574, 575], [601, 603, 573, 575], [604, 603, 577, 575], [603, 575], [], [], [],
    [], [604, 603, 577, 575], [], [], [], [], [591, 546, 592, 548, 593, 550, 594, 552], [592, 548,
    594, 552], [595, 556, 594, 552], [594, 552], [], [605, 592, 606, 594], [], [606, 594], [],
    [607, 608, 598, 599], [608, 599], [], [], [], [605, 592, 606, 594], [606, 594], [609, 606], [],
    [609, 606]]

def BL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 11, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 18, 21, 22, 24, 22, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 32, 36, 37, 38, 37,
    39, 40, 41, 30, 33, 34, 38, 37, 39, 40, 42, 34, 39, 40, 43, 40, 44, 45, 46, 47, 28, 48, 49, 50,
    30, 51, 52, 53, 32, 54, 55, 54, 34, 56, 57, 50, 32, 54, 58, 59, 37, 60, 61, 54, 37, 60, 62, 60,
    40, 63, 64, 48, 30, 51, 55, 54, 34, 56, 61, 54, 37, 60, 62, 60, 40, 63, 65, 51, 34, 56, 62, 60,
    40, 63, 66, 56, 40, 63, 67, 63, 45, 68, 2, 6, 10, 13, 17, 21, 21, 25, 29, 33, 36, 39, 33, 39,
    39, 44, 28, 30, 32, 34, 32, 37, 37, 40, 30, 34, 37, 40, 34, 40, 40, 45, 69, 70, 71, 70, 72, 70,
    73, 70, 74, 70, 75, 70, 75, 70, 76, 70, 77, 70, 78, 70, 79, 70, 80, 70, 78, 70, 80, 70, 80, 70,
    81, 70, 82, 83, 70, 70, 84, 85, 70, 70, 86, 85, 70, 70, 87, 88, 70, 70, 89, 85, 70, 70, 90, 88,
    70, 70, 90, 88, 70, 70, 91, 92, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 93, 94, 83, 85, 70, 70,
    70, 70, 95, 96, 85, 88, 70, 70, 70, 70, 97, 98, 85, 88, 70, 70, 70, 70, 99, 100, 88, 92, 70,
    70, 70, 70, 83, 70, 85, 70, 85, 70, 88, 70, 70, 70, 70, 70, 70, 70, 70, 70, 101, 102, 94, 96,
    83, 85, 85, 88, 70, 70, 70, 70, 70, 70, 70, 70, 103, 104, 96, 100, 85, 88, 88, 92, 70, 70, 70,
    70, 70, 70, 70, 70, 94, 85, 70, 70, 96, 88, 70, 70, 85, 70, 70, 70, 88, 70, 70, 70, 70, 70, 70,
    70, 70, 70, 70, 70, 70, 70, 105, 106, 102, 104, 107, 98, 96, 100, 83, 85, 85, 88, 85, 88, 88,
    92, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 102, 96, 85, 88, 70, 70,
    70, 70, 108, 70, 88, 70, 70, 70, 70, 70, 85, 88, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70,
    70, 70, 70, 70, 70, 70, 70, 70, 70, 69, 71, 72, 73, 74, 75, 75, 76, 77, 78, 79, 80, 78, 80, 80,
    81, 70, 70, 70, 70, 85, 70, 88, 70, 108, 88, 70, 70, 70, 109, 70, 110, 70, 87, 70, 111, 70,
    112, 70, 91, 70, 91, 70, 113, 70, 70, 70, 70, 70, 88, 70, 70, 70, 114, 85, 70, 70, 115, 88, 70,
    70, 116, 88, 70, 70, 117, 92, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 118, 96, 85, 88, 70,
    70, 70, 70, 119, 100, 88, 92, 70, 70, 70, 70, 85, 70, 88, 70, 70, 70, 70, 70, 70, 70, 120, 104,
    96, 100, 85, 88, 88, 92, 70, 70, 70, 70, 70, 70, 70, 70, 96, 88, 70, 70, 88, 70, 70, 70, 70,
    70, 70, 70, 70, 88, 70, 70, 70, 109, 110, 87, 111, 112, 91, 91, 113, 70, 70, 88, 70, 70, 121,
    70, 122, 70, 117, 70, 123, 70, 70, 70, 124, 88, 70, 70, 125, 92, 70, 70, 70, 70, 126, 100, 88,
    92, 70, 70, 70, 70, 88, 70, 70, 70, 70, 121, 122, 117, 123, 70, 127, 70, 128, 70, 129, 92, 70,
    70, 70, 127, 128, 130, 70, 130]

def BS : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 11, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 18, 21, 22, 24, 22, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 32, 36, 37,
    38, 37, 39, 40, 41, 30, 33, 34, 38, 37, 39, 40, 42, 34, 39, 40, 43, 40, 44, 45, 46, 47, 28, 48,
    49, 50, 30, 51, 52, 53, 32, 54, 55, 54, 34, 56, 57, 50, 32, 54, 58, 59, 37, 60, 61, 54, 37, 60,
    62, 60, 40, 63, 64, 48, 30, 51, 55, 54, 34, 56, 61, 54, 37, 60, 62, 60, 40, 63, 65, 51, 34, 56,
    62, 60, 40, 63, 66, 56, 40, 63, 67, 63, 45, 68], [1, 3, 5, 7, 9, 11, 11, 14, 16, 18, 20, 22,
    18, 22, 22, 26, 28, 30, 32, 34, 32, 37, 37, 40, 30, 34, 37, 40, 34, 40, 40, 45, 47, 48, 50, 51,
    53, 54, 54, 56, 50, 54, 59, 60, 54, 60, 60, 63, 48, 51, 54, 56, 54, 60, 60, 63, 51, 56, 60, 63,
    56, 63, 63, 68], [2, 3, 6, 7, 10, 11, 13, 14, 17, 18, 21, 22, 21, 22, 25, 26, 29, 30, 33, 34,
    36, 37, 39, 40, 33, 34, 39, 40, 39, 40, 44, 45, 28, 48, 30, 51, 32, 54, 34, 56, 32, 54, 37, 60,
    37, 60, 40, 63, 30, 51, 34, 56, 37, 60, 40, 63, 34, 56, 40, 63, 40, 63, 45, 68], [3, 7, 11, 14,
    18, 22, 22, 26, 30, 34, 37, 40, 34, 40, 40, 45, 48, 51, 54, 56, 54, 60, 60, 63, 51, 56, 60, 63,
    56, 63, 63, 68], [69, 70, 6, 7, 71, 70, 13, 14, 72, 70, 21, 22, 73, 70, 25, 26, 74, 70, 33, 34,
    75, 70, 39, 40, 75, 70, 39, 40, 76, 70, 44, 45, 77, 70, 30, 51, 78, 70, 34, 56, 79, 70, 37, 60,
    80, 70, 40, 63, 78, 70, 34, 56, 80, 70, 40, 63, 80, 70, 40, 63, 81, 70, 45, 68], [70, 7, 70,
    14, 70, 22, 70, 26, 70, 34, 70, 40, 70, 40, 70, 45, 70, 51, 70, 56, 70, 60, 70, 63, 70, 56, 70,
    63, 70, 63, 70, 68], [6, 7, 13, 14, 21, 22, 25, 26, 33, 34, 39, 40, 39, 40, 44, 45, 30, 51, 34,
    56, 37, 60, 40, 63, 34, 56, 40, 63, 40, 63, 45, 68], [7, 14, 22, 26, 34, 40, 40, 45, 51, 56,
    60, 63, 56, 63, 63, 68], [82, 83, 70, 70, 12, 11, 13, 14, 84, 85, 70, 70, 24, 22, 25, 26, 86,
    85, 70, 70, 38, 37, 39, 40, 87, 88, 70, 70, 43, 40, 44, 45, 89, 85, 70, 70, 55, 54, 34, 56, 90,
    88, 70, 70, 62, 60, 40, 63, 90, 88, 70, 70, 62, 60, 40, 63, 91, 92, 70, 70, 67, 63, 45, 68],
    [83, 70, 11, 14, 85, 70, 22, 26, 85, 70, 37, 40, 88, 70, 40, 45, 85, 70, 54, 56, 88, 70, 60,
    63, 88, 70, 60, 63, 92, 70, 63, 68], [70, 70, 13, 14, 70, 70, 25, 26, 70, 70, 39, 40, 70, 70,
    44, 45, 70, 70, 34, 56, 70, 70, 40, 63, 70, 70, 40, 63, 70, 70, 45, 68], [70, 14, 70, 26, 70,
    40, 70, 45, 70, 56, 70, 63, 70, 63, 70, 68], [71, 70, 13, 14, 73, 70, 25, 26, 75, 70, 39, 40,
    76, 70, 44, 45, 78, 70, 34, 56, 80, 70, 40, 63, 80, 70, 40, 63, 81, 70, 45, 68], [13, 14, 25,
    26, 39, 40, 44, 45, 34, 56, 40, 63, 40, 63, 45, 68], [14, 26, 40, 45, 56, 63, 63, 68], [93, 94,
    83, 85, 70, 70, 70, 70, 23, 18, 21, 22, 24, 22, 25, 26, 95, 96, 85, 88, 70, 70, 70, 70, 42, 34,
    39, 40, 43, 40, 44, 45, 97, 98, 85, 88, 70, 70, 70, 70, 61, 54, 37, 60, 62, 60, 40, 63, 99,
    100, 88, 92, 70, 70, 70, 70, 66, 56, 40, 63, 67, 63, 45, 68], [94, 85, 70, 70, 18, 22, 22, 26,
    96, 88, 70, 70, 34, 40, 40, 45, 98, 88, 70, 70, 54, 60, 60, 63, 100, 92, 70, 70, 56, 63, 63,
    68], [83, 85, 70, 70, 21, 22, 25, 26, 85, 88, 70, 70, 39, 40, 44, 45, 85, 88, 70, 70, 37, 60,
    40, 63, 88, 92, 70, 70, 40, 63, 45, 68], [85, 70, 22, 26, 88, 70, 40, 45, 88, 70, 60, 63, 92,
    70, 63, 68], [70, 70, 70, 70, 73, 70, 25, 26, 70, 70, 70, 70, 76, 70, 44, 45, 70, 70, 70, 70,
    80, 70, 40, 63, 70, 70, 70, 70, 81, 70, 45, 68], [70, 70, 70, 26, 70, 70, 70, 45, 70, 70, 70,
    63, 70, 70, 70, 68], [70, 70, 25, 26, 70, 70, 44, 45, 70, 70, 40, 63, 70, 70, 45, 68], [70, 26,
    70, 45, 70, 63, 70, 68], [84, 85, 70, 70, 24, 22, 25, 26, 87, 88, 70, 70, 43, 40, 44, 45, 90,
    88, 70, 70, 62, 60, 40, 63, 91, 92, 70, 70, 67, 63, 45, 68], [73, 70, 25, 26, 76, 70, 44, 45,
    80, 70, 40, 63, 81, 70, 45, 68], [25, 26, 44, 45, 40, 63, 45, 68], [26, 45, 63, 68], [101, 102,
    94, 96, 83, 85, 85, 88, 70, 70, 70, 70, 70, 70, 70, 70, 41, 30, 33, 34, 38, 37, 39, 40, 42, 34,
    39, 40, 43, 40, 44, 45, 103, 104, 96, 100, 85, 88, 88, 92, 70, 70, 70, 70, 70, 70, 70, 70, 65,
    51, 34, 56, 62, 60, 40, 63, 66, 56, 40, 63, 67, 63, 45, 68], [102, 96, 85, 88, 70, 70, 70, 70,
    30, 34, 37, 40, 34, 40, 40, 45, 104, 100, 88, 92, 70, 70, 70, 70, 51, 56, 60, 63, 56, 63, 63,
    68], [94, 96, 85, 88, 70, 70, 70, 70, 33, 34, 39, 40, 39, 40, 44, 45, 96, 100, 88, 92, 70, 70,
    70, 70, 34, 56, 40, 63, 40, 63, 45, 68], [96, 88, 70, 70, 34, 40, 40, 45, 100, 92, 70, 70, 56,
    63, 63, 68], [85, 70, 85, 88, 70, 70, 70, 70, 75, 70, 39, 40, 76, 70, 44, 45, 88, 70, 88, 92,
    70, 70, 70, 70, 80, 70, 40, 63, 81, 70, 45, 68], [70, 88, 70, 70, 70, 40, 70, 45, 70, 92, 70,
    70, 70, 63, 70, 68], [85, 88, 70, 70, 39, 40, 44, 45, 88, 92, 70, 70, 40, 63, 45, 68], [88, 70,
    40, 45, 92, 70, 63, 68], [70, 70, 70, 70, 70, 70, 70, 70, 87, 88, 70, 70, 43, 40, 44, 45, 70,
    70, 70, 70, 70, 70, 70, 70, 91, 92, 70, 70, 67, 63, 45, 68], [70, 70, 70, 70, 70, 70, 44, 45,
    70, 70, 70, 70, 70, 70, 45, 68], [70, 70, 70, 45, 70, 70, 70, 68], [70, 70, 70, 70, 76, 70, 44,
    45, 70, 70, 70, 70, 81, 70, 45, 68], [70, 70, 44, 45, 70, 70, 45, 68], [70, 45, 70, 68], [95,
    96, 85, 88, 70, 70, 70, 70, 42, 34, 39, 40, 43, 40, 44, 45, 99, 100, 88, 92, 70, 70, 70, 70,
    66, 56, 40, 63, 67, 63, 45, 68], [87, 88, 70, 70, 43, 40, 44, 45, 91, 92, 70, 70, 67, 63, 45,
    68], [76, 70, 44, 45, 81, 70, 45, 68], [44, 45, 45, 68], [45, 68], [105, 106, 102, 104, 107,
    98, 96, 100, 83, 85, 85, 88, 85, 88, 88, 92, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70,
    70, 70, 70, 70, 64, 48, 30, 51, 55, 54, 34, 56, 61, 54, 37, 60, 62, 60, 40, 63, 65, 51, 34, 56,
    62, 60, 40, 63, 66, 56, 40, 63, 67, 63, 45, 68], [106, 104, 98, 100, 85, 88, 88, 92, 70, 70,
    70, 70, 70, 70, 70, 70, 48, 51, 54, 56, 54, 60, 60, 63, 51, 56, 60, 63, 56, 63, 63, 68], [104,
    100, 88, 92, 70, 70, 70, 70, 51, 56, 60, 63, 56, 63, 63, 68], [108, 70, 96, 100, 88, 70, 88,
    92, 70, 70, 70, 70, 70, 70, 70, 70, 78, 70, 34, 56, 80, 70, 40, 63, 80, 70, 40, 63, 81, 70, 45,
    68], [70, 100, 70, 92, 70, 70, 70, 70, 70, 56, 70, 63, 70, 63, 70, 68], [100, 92, 70, 70, 56,
    63, 63, 68], [85, 88, 70, 70, 85, 88, 88, 92, 70, 70, 70, 70, 70, 70, 70, 70, 90, 88, 70, 70,
    62, 60, 40, 63, 91, 92, 70, 70, 67, 63, 45, 68], [88, 70, 88, 92, 70, 70, 70, 70, 88, 70, 60,
    63, 92, 70, 63, 68], [70, 92, 70, 70, 70, 63, 70, 68], [88, 70, 88, 92, 70, 70, 70, 70, 80, 70,
    40, 63, 81, 70, 45, 68], [92, 70, 63, 68], [70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70,
    70, 70, 70, 99, 100, 88, 92, 70, 70, 70, 70, 66, 56, 40, 63, 67, 63, 45, 68], [70, 70, 70, 70,
    70, 70, 70, 70, 70, 70, 70, 70, 81, 70, 45, 68], [70, 70, 70, 70, 70, 70, 70, 68], [70, 70, 70,
    68], [70, 70, 70, 70, 70, 70, 70, 70, 91, 92, 70, 70, 67, 63, 45, 68], [70, 70, 70, 70, 81, 70,
    45, 68], [70, 68], [103, 104, 96, 100, 85, 88, 88, 92, 70, 70, 70, 70, 70, 70, 70, 70, 65, 51,
    34, 56, 62, 60, 40, 63, 66, 56, 40, 63, 67, 63, 45, 68], [99, 100, 88, 92, 70, 70, 70, 70, 66,
    56, 40, 63, 67, 63, 45, 68], [91, 92, 70, 70, 67, 63, 45, 68], [81, 70, 45, 68], [68], [69, 6,
    71, 13, 72, 21, 73, 25, 74, 33, 75, 39, 75, 39, 76, 44, 77, 30, 78, 34, 79, 37, 80, 40, 78, 34,
    80, 40, 80, 40, 81, 45], [], [71, 13, 73, 25, 75, 39, 76, 44, 78, 34, 80, 40, 80, 40, 81, 45],
    [70, 70, 73, 25, 70, 70, 76, 44, 70, 70, 80, 40, 70, 70, 81, 45], [73, 25, 76, 44, 80, 40, 81,
    45], [85, 85, 70, 70, 75, 39, 76, 44, 88, 88, 70, 70, 80, 40, 81, 45], [70, 70, 76, 44, 70, 70,
    81, 45], [76, 44, 81, 45], [108, 96, 88, 88, 70, 70, 70, 70, 78, 34, 80, 40, 80, 40, 81, 45],
    [88, 88, 70, 70, 80, 40, 81, 45], [70, 70, 70, 70, 70, 70, 81, 45], [70, 70, 81, 45], [81, 45],
    [109, 70, 71, 70, 110, 70, 73, 70, 87, 70, 75, 70, 111, 70, 76, 70, 112, 70, 78, 70, 91, 70,
    80, 70, 91, 70, 80, 70, 113, 70, 81, 70], [70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70,
    70, 70, 70], [110, 70, 73, 70, 111, 70, 76, 70, 91, 70, 80, 70, 113, 70, 81, 70], [70, 70, 70,
    70, 70, 70, 70, 70], [70, 70, 70, 70, 111, 70, 76, 70, 70, 70, 70, 70, 113, 70, 81, 70], [111,
    70, 76, 70, 113, 70, 81, 70], [70, 70, 70, 70], [88, 70, 88, 70, 70, 70, 70, 70, 91, 70, 80,
    70, 113, 70, 81, 70], [70, 70, 70, 70, 113, 70, 81, 70], [113, 70, 81, 70], [70, 70], [114, 85,
    70, 70, 84, 85, 70, 70, 115, 88, 70, 70, 87, 88, 70, 70, 116, 88, 70, 70, 90, 88, 70, 70, 117,
    92, 70, 70, 91, 92, 70, 70], [85, 70, 85, 70, 88, 70, 88, 70, 88, 70, 88, 70, 92, 70, 92, 70],
    [115, 88, 70, 70, 87, 88, 70, 70, 117, 92, 70, 70, 91, 92, 70, 70], [88, 70, 88, 70, 92, 70,
    92, 70], [70, 70, 70, 70, 70, 70, 70, 70, 117, 92, 70, 70, 91, 92, 70, 70], [70, 70, 70, 70,
    92, 70, 92, 70], [117, 92, 70, 70, 91, 92, 70, 70], [92, 70, 92, 70], [118, 96, 85, 88, 70, 70,
    70, 70, 95, 96, 85, 88, 70, 70, 70, 70, 119, 100, 88, 92, 70, 70, 70, 70, 99, 100, 88, 92, 70,
    70, 70, 70], [96, 88, 70, 70, 96, 88, 70, 70, 100, 92, 70, 70, 100, 92, 70, 70], [119, 100, 88,
    92, 70, 70, 70, 70, 99, 100, 88, 92, 70, 70, 70, 70], [100, 92, 70, 70, 100, 92, 70, 70], [120,
    104, 96, 100, 85, 88, 88, 92, 70, 70, 70, 70, 70, 70, 70, 70, 103, 104, 96, 100, 85, 88, 88,
    92, 70, 70, 70, 70, 70, 70, 70, 70], [104, 100, 88, 92, 70, 70, 70, 70, 104, 100, 88, 92, 70,
    70, 70, 70], [88, 70, 88, 92, 70, 70, 70, 70, 88, 70, 88, 92, 70, 70, 70, 70], [88, 88, 70, 70,
    88, 88, 70, 70], [109, 71, 110, 73, 87, 75, 111, 76, 112, 78, 91, 80, 91, 80, 113, 81], [110,
    73, 111, 76, 91, 80, 113, 81], [111, 76, 113, 81], [88, 88, 70, 70, 91, 80, 113, 81], [113,
    81], [121, 70, 110, 70, 122, 70, 111, 70, 117, 70, 91, 70, 123, 70, 113, 70], [122, 70, 111,
    70, 123, 70, 113, 70], [70, 70, 70, 70, 123, 70, 113, 70], [123, 70, 113, 70], [124, 88, 70,
    70, 115, 88, 70, 70, 125, 92, 70, 70, 117, 92, 70, 70], [125, 92, 70, 70, 117, 92, 70, 70],
    [126, 100, 88, 92, 70, 70, 70, 70, 119, 100, 88, 92, 70, 70, 70, 70], [121, 110, 122, 111, 117,
    91, 123, 113], [122, 111, 123, 113], [123, 113], [127, 70, 122, 70, 128, 70, 123, 70], [128,
    70, 123, 70], [129, 92, 70, 70, 125, 92, 70, 70], [127, 122, 128, 123], [128, 123], [130, 70,
    128, 70], [130, 128]]

def VT : List (List ℕ) := [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [128, 64, 64, 32, 64, 32, 32, 16, 64, 32, 32, 16, 32, 16, 8,
    64, 32, 32, 16, 32, 16, 16, 8, 32, 16, 8, 4, 64, 32, 32, 16, 32, 16, 16, 8, 32, 16, 8, 16, 8,
    4, 32, 16, 8, 4, 2, 64, 32, 16, 32, 16, 8, 32, 16, 8, 16, 4, 32, 16, 8, 4, 16, 8, 2, 32, 16, 8,
    4, 1, 32, 0, 16, 16, 8, 16, 8, 4, 16, 8, 8, 4, 2, 32, 16, 16, 8, 16, 8, 4, 16, 8, 4, 2, 32, 16,
    16, 8, 16, 8, 8, 4, 32, 16, 16, 8, 32, 16, 16, 8, 16, 8, 4, 8, 2, 16, 8, 8, 4, 16, 8, 16, 8, 4,
    2, 8, 4, 8, 4, 2, 4, 2], [2187, 729, 729, 243, 405, 81, 243, 81, 405, 135, 81, 27, 135, 81, 27,
    405, 135, 135, 45, 45, 9, 27, 9, 135, 45, 27, 9, 405, 135, 135, 45, 75, 15, 45, 15, 45, 9, 3,
    15, 9, 3, 135, 45, 15, 9, 3, 405, 135, 45, 75, 15, 15, 75, 25, 5, 25, 5, 45, 5, 1, 1, 15, 5, 1,
    135, 45, 15, 5, 1, 324, 0, 108, 36, 36, 60, 12, 12, 60, 20, 4, 4, 4, 108, 0, 36, 0, 12, 12, 0,
    20, 4, 4, 0, 108, 36, 36, 12, 12, 4, 12, 4, 108, 36, 36, 12, 108, 36, 20, 16, 108, 36, 12, 20,
    4, 36, 12, 4, 4, 36, 12, 36, 36, 12, 4, 12, 4, 12, 12, 4, 4, 4], [9688, 2332, 2592, 648, 1440,
    180, 720, 180, 700, 100, 200, 50, 400, 200, 50, 700, 168, 112, 28, 112, 14, 56, 14, 196, 112,
    56, 14, 752, 184, 192, 48, 64, 8, 32, 8, 56, 16, 4, 32, 16, 4, 200, 56, 32, 16, 4, 680, 164,
    46, 96, 12, 12, 28, 4, 2, 16, 2, 50, 8, 1, 1, 14, 8, 1, 188, 50, 14, 8, 1, 1260, 0, 350, 98,
    98, 56, 28, 28, 84, 14, 7, 7, 7, 400, 0, 112, 0, 32, 32, 0, 16, 8, 8, 0, 112, 0, 32, 0, 8, 0,
    8, 0, 128, 32, 32, 8, 128, 32, 0, 0, 400, 112, 32, 16, 8, 112, 32, 8, 8, 32, 8, 32, 112, 32, 8,
    32, 8, 8, 32, 8, 8, 8], [25047, 4589, 5850, 1170, 3588, 299, 1495, 299, 1694, 154, 385, 77,
    924, 385, 77, 860, 100, 200, 40, 240, 20, 100, 20, 440, 240, 100, 20, 805, 145, 125, 25, 120,
    10, 50, 10, 110, 25, 5, 60, 25, 5, 215, 110, 60, 25, 5, 678, 128, 29, 60, 5, 5, 44, 4, 2, 24,
    2, 43, 12, 1, 1, 22, 12, 1, 161, 43, 22, 12, 1, 3289, 0, 847, 220, 220, 110, 55, 55, 55, 22,
    11, 11, 11, 1155, 0, 300, 0, 75, 75, 0, 30, 15, 15, 0, 320, 0, 80, 0, 16, 0, 16, 0, 80, 0, 16,
    0, 80, 16, 0, 0, 1155, 300, 75, 30, 15, 320, 80, 16, 16, 80, 16, 16, 320, 80, 16, 80, 16, 16,
    80, 16, 16, 16], [52581, 7555, 11100, 1850, 7735, 455, 2730, 455, 3808, 224, 672, 112, 1904,
    672, 112, 1755, 135, 324, 54, 459, 27, 162, 27, 918, 459, 162, 27, 864, 84, 180, 30, 204, 12,
    72, 12, 204, 36, 6, 102, 36, 6, 390, 204, 102, 36, 6, 531, 73, 14, 85, 5, 5, 68, 4, 2, 34, 2,
    65, 17, 1, 1, 34, 17, 1, 144, 65, 34, 17, 1, 7280, 0, 1792, 432, 432, 192, 96, 96, 80, 32, 16,
    16, 16, 2912, 0, 702, 0, 156, 156, 0, 52, 26, 26, 0, 837, 0, 186, 0, 31, 0, 31, 0, 192, 0, 32,
    0, 32, 0, 0, 0, 2912, 702, 156, 52, 26, 837, 186, 31, 31, 192, 32, 32, 837, 186, 31, 192, 32,
    32, 192, 32, 32, 32], [101412, 11668, 19530, 2790, 15295, 665, 4655, 665, 7956, 312, 1092, 156,
    3588, 1092, 156, 3465, 175, 490, 70, 805, 35, 245, 35, 1785, 805, 245, 35, 1463, 98, 245, 35,
    322, 14, 98, 14, 357, 49, 7, 161, 49, 7, 693, 357, 161, 49, 7, 520, 42, 14, 115, 5, 5, 102, 4,
    2, 46, 2, 99, 23, 1, 1, 51, 23, 1, 209, 99, 51, 23, 1, 14630, 0, 3432, 770, 770, 308, 154, 154,
    110, 44, 22, 22, 22, 6552, 0, 1470, 0, 294, 294, 0, 84, 42, 42, 0, 1995, 0, 399, 0, 57, 0, 57,
    0, 441, 0, 63, 0, 64, 0, 0, 0, 6552, 1470, 294, 84, 42, 1995, 399, 57, 57, 441, 63, 64, 1995,
    399, 57, 441, 63, 64, 441, 63, 64, 64], [186348, 17484, 32656, 4082, 28200, 940, 7520, 940,
    15540, 420, 1680, 210, 6300, 1680, 210, 6600, 220, 704, 88, 1320, 44, 352, 44, 3256, 1320, 352,
    44, 2464, 112, 320, 40, 480, 16, 128, 16, 592, 64, 8, 240, 64, 8, 1200, 592, 240, 64, 8, 729,
    42, 14, 150, 5, 5, 148, 4, 2, 60, 2, 150, 30, 1, 1, 74, 30, 1, 308, 150, 74, 30, 1, 27260, 0,
    6090, 1276, 1276, 464, 232, 232, 145, 58, 29, 29, 29, 13440, 0, 2816, 0, 512, 512, 0, 128, 64,
    64, 0, 4356, 0, 792, 0, 99, 0, 99, 0, 960, 0, 120, 0, 127, 0, 0, 0, 13440, 2816, 512, 128, 64,
    4356, 792, 99, 99, 960, 120, 127, 4356, 792, 99, 960, 120, 127, 960, 120, 127, 127], [329167,
    25580, 52344, 5816, 49096, 1292, 11628, 1292, 28600, 550, 2475, 275, 10450, 2475, 275, 12096,
    270, 972, 108, 2052, 54, 486, 54, 5616, 2052, 486, 54, 4122, 126, 405, 45, 684, 18, 162, 18,
    936, 81, 9, 342, 81, 9, 2016, 936, 342, 81, 9, 1037, 42, 14, 190, 5, 5, 208, 4, 2, 76, 2, 224,
    38, 1, 1, 104, 38, 1, 458, 224, 104, 38, 1, 47804, 0, 10175, 1998, 1998, 666, 333, 333, 185,
    74, 37, 37, 37, 25575, 0, 5022, 0, 837, 837, 0, 186, 93, 93, 0, 8802, 0, 1467, 0, 163, 0, 163,
    0, 1971, 0, 219, 0, 247, 0, 0, 0, 25575, 5022, 837, 186, 93, 8802, 1467, 163, 163, 1971, 219,
    247, 8802, 1467, 163, 1971, 219, 247, 1971, 219, 247, 247], [561329, 36621, 80960, 8096, 81498,
    1734, 17340, 1734, 49984, 704, 3520, 352, 16544, 3520, 352, 21320, 325, 1300, 130, 3055, 65,
    650, 65, 9230, 3055, 650, 65, 6820, 140, 500, 50, 940, 20, 200, 20, 1420, 100, 10, 470, 100,
    10, 3280, 1420, 470, 100, 10, 1495, 42, 14, 235, 5, 5, 284, 4, 2, 94, 2, 328, 47, 1, 1, 142,
    47, 1, 682, 328, 142, 47, 1, 79764, 0, 16192, 2990, 2990, 920, 460, 460, 230, 92, 46, 46, 46,
    45760, 0, 8450, 0, 1300, 1300, 0, 260, 130, 130, 0, 16640, 0, 2560, 0, 256, 0, 256, 0, 3820, 0,
    382, 0, 466, 0, 0, 0, 45760, 8450, 1300, 260, 130, 16640, 2560, 256, 256, 3820, 382, 466,
    16640, 2560, 256, 3820, 382, 466, 3820, 382, 466, 466], [927323, 51407, 121451, 11041, 129960,
    2280, 25080, 2280, 83538, 884, 4862, 442, 25194, 4862, 442, 36190, 385, 1694, 154, 4389, 77,
    847, 77, 14553, 4389, 847, 77, 11110, 154, 605, 55, 1254, 22, 242, 22, 2079, 121, 11, 627, 121,
    11, 5170, 2079, 627, 121, 11, 2177, 42, 14, 285, 5, 5, 378, 4, 2, 114, 2, 470, 57, 1, 1, 189,
    57, 1, 1010, 470, 189, 57, 1, 127680, 0, 24752, 4312, 4312, 1232, 616, 616, 280, 112, 56, 56,
    56, 77792, 0, 13552, 0, 1936, 1936, 0, 352, 176, 176, 0, 29722, 0, 4246, 0, 386, 0, 386, 0,
    7018, 0, 638, 0, 848, 0, 0, 0, 77792, 13552, 1936, 352, 176, 29722, 4246, 386, 386, 7018, 638,
    848, 29722, 4246, 386, 7018, 638, 848, 7018, 638, 848, 848], [1488515, 70890, 177432, 14786,
    200260, 2945, 35340, 2945, 134316, 1092, 6552, 546, 37128, 6552, 546, 59310, 450, 2160, 180,
    6120, 90, 1080, 90, 22140, 6120, 1080, 90, 17760, 168, 720, 60, 1632, 24, 288, 24, 2952, 144,
    12, 816, 144, 12, 7908, 2952, 816, 144, 12, 3187, 42, 14, 340, 5, 5, 492, 4, 2, 136, 2, 659,
    68, 1, 1, 246, 68, 1, 1480, 659, 246, 68, 1, 197315, 0, 36582, 6030, 6030, 1608, 804, 804, 335,
    134, 67, 67, 67, 126672, 0, 20880, 0, 2784, 2784, 0, 464, 232, 232, 0, 50580, 0, 6744, 0, 562,
    0, 562, 0, 12288, 0, 1024, 0, 1486, 0, 0, 0, 126672, 20880, 2784, 464, 232, 50580, 6744, 562,
    562, 12288, 1024, 1486, 50580, 6744, 562, 12288, 1024, 1486, 12288, 1024, 1486, 1486],
    [2327716, 96192, 253279, 19483, 299600, 3745, 48685, 3745, 208810, 1330, 8645, 665, 53200,
    8645, 665, 94120, 520, 2704, 208, 8320, 104, 1352, 104, 32656, 8320, 1352, 104, 27807, 182,
    845, 65, 2080, 26, 338, 26, 4082, 169, 13, 1040, 169, 13, 11765, 4082, 1040, 169, 13, 4667, 42,
    14, 400, 5, 5, 628, 4, 2, 160, 2, 905, 80, 1, 1, 314, 80, 1, 2139, 905, 314, 80, 1, 295855, 0,
    52535, 8216, 8216, 2054, 1027, 1027, 395, 158, 79, 79, 79, 198835, 0, 31096, 0, 3887, 3887, 0,
    598, 299, 299, 0, 82576, 0, 10322, 0, 794, 0, 794, 0, 20618, 0, 1586, 0, 2510, 0, 0, 0, 198835,
    31096, 3887, 598, 299, 82576, 10322, 794, 794, 20618, 1586, 2510, 82576, 10322, 794, 20618,
    1586, 2510, 20618, 1586, 2510, 2510], [3554534, 128624, 354228, 25302, 436821, 4697, 65758,
    4697, 315200, 1600, 11200, 800, 74400, 11200, 800, 145061, 595, 3332, 238, 11067, 119, 1666,
    119, 46886, 11067, 1666, 119, 42616, 196, 980, 70, 2604, 28, 392, 28, 5516, 196, 14, 1302, 196,
    14, 17066, 5516, 1302, 196, 14, 6806, 42, 14, 465, 5, 5, 788, 4, 2, 186, 2, 1219, 93, 1, 1,
    394, 93, 1, 3044, 1219, 394, 93, 1, 432124, 0, 73600, 10948, 10948, 2576, 1288, 1288, 460, 184,
    92, 92, 92, 302400, 0, 44982, 0, 5292, 5292, 0, 756, 378, 378, 0, 130067, 0, 15302, 0, 1093, 0,
    1093, 0, 33320, 0, 2380, 0, 4096, 0, 0, 0, 302400, 44982, 5292, 756, 378, 130067, 15302, 1093,
    1093, 33320, 2380, 4096, 130067, 15302, 1093, 33320, 2380, 4096, 33320, 2380, 4096, 4096],
    [5311574, 169706, 486480, 32432, 622633, 5819, 87285, 5819, 463624, 1904, 14280, 952, 101864,
    14280, 952, 217755, 675, 4050, 270, 14445, 135, 2025, 135, 65745, 14445, 2025, 135, 63945, 210,
    1125, 75, 3210, 30, 450, 30, 7305, 225, 15, 1605, 225, 15, 24195, 7305, 1605, 225, 15, 9850,
    42, 14, 535, 5, 5, 974, 4, 2, 214, 2, 1613, 107, 1, 1, 487, 107, 1, 4263, 1613, 487, 107, 1,
    616814, 0, 100912, 14310, 14310, 3180, 1590, 1590, 530, 212, 106, 106, 106, 447440, 0, 63450,
    0, 7050, 7050, 0, 940, 470, 470, 0, 198585, 0, 22065, 0, 1471, 0, 1471, 0, 52095, 0, 3473, 0,
    6476, 0, 0, 0, 447440, 63450, 7050, 940, 470, 198585, 22065, 1471, 1471, 52095, 3473, 6476,
    198585, 22065, 1471, 52095, 3473, 6476, 52095, 3473, 6476, 6476], [7781550, 221188, 657312,
    41082, 869860, 7130, 114080, 7130, 666468, 2244, 17952, 1122, 136884, 17952, 1122, 319200, 760,
    4864, 304, 18544, 152, 2432, 152, 90288, 18544, 2432, 152, 94016, 224, 1280, 80, 3904, 32, 512,
    32, 9504, 256, 16, 1952, 256, 16, 33600, 9504, 1952, 256, 16, 14113, 42, 14, 610, 5, 5, 1188,
    4, 2, 244, 2, 2100, 122, 1, 1, 594, 122, 1, 5876, 2100, 594, 122, 1, 862730, 0, 135762, 18392,
    18392, 3872, 1936, 1936, 605, 242, 121, 121, 121, 646272, 0, 87552, 0, 9216, 9216, 0, 1152,
    576, 576, 0, 295032, 0, 31056, 0, 1941, 0, 1941, 0, 79104, 0, 4944, 0, 9949, 0, 0, 0, 646272,
    87552, 9216, 1152, 576, 295032, 31056, 1941, 1941, 79104, 4944, 9949, 295032, 31056, 1941,
    79104, 4944, 9949, 79104, 4944, 9949, 9949], [11195373, 285072, 875194, 51482, 1193700, 8650,
    147050, 8650, 938676, 2622, 22287, 1311, 180918, 22287, 1311, 457980, 850, 5780, 340, 23460,
    170, 2890, 170, 121720, 23460, 2890, 170, 135592, 238, 1445, 85, 4692, 34, 578, 34, 12172, 289,
    17, 2346, 289, 17, 45798, 12172, 2346, 289, 17, 19989, 42, 14, 690, 5, 5, 1432, 4, 2, 276, 2,
    2694, 138, 1, 1, 716, 138, 1, 7976, 2694, 716, 138, 1, 1185050, 0, 179607, 23290, 23290, 4658,
    2329, 2329, 685, 274, 137, 137, 137, 913767, 0, 118490, 0, 11849, 11849, 0, 1394, 697, 697, 0,
    427890, 0, 42789, 0, 2517, 0, 2517, 0, 117045, 0, 6885, 0, 14893, 0, 0, 0, 913767, 118490,
    11849, 1394, 697, 427890, 42789, 2517, 2517, 117045, 6885, 14893, 427890, 42789, 2517, 117045,
    6885, 14893, 117045, 6885, 14893, 14893]]

def IL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
    70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93,
    94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113,
    114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]

def AV : List ℕ := [0, 128, 2187, 9688, 25047, 52581, 101412, 186348, 329167, 561329, 927323,
    1488515, 2327716, 3554534, 5311574, 7781550, 11195373, 15841279]

def LC : List (ℕ × ℕ) := [(1, 8), (28, 6), (70, 4), (28, 2), (1, 0)]

def RC : List (ℕ × ℕ) := [(8, 7), (56, 5), (56, 3), (8, 1)]

set_option maxRecDepth 100000 in
theorem h1_0 : (List.range' 0 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_1 : (List.range' 32 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_2 : (List.range' 64 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_3 : (List.range' 96 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_4 : (List.range' 128 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_5 : (List.range' 160 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_6 : (List.range' 192 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_7 : (List.range' 224 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_8 : (List.range' 256 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_9 : (List.range' 288 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_10 : (List.range' 320 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_11 : (List.range' 352 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_12 : (List.range' 384 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_13 : (List.range' 416 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_14 : (List.range' 448 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_15 : (List.range' 480 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_16 : (List.range' 512 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_17 : (List.range' 544 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_18 : (List.range' 576 32).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_19 : (List.range' 608 2).all (c1 7 2 COc true [2] RL SI 610) = true := by
  decide +kernel

theorem h1 : chk1 7 2 COc true [2] RL SI 610 = true :=
  chk1_of 7 2 COc true [2] RL SI 610 (all_split (c1 7 2 COc true [2] RL SI 610) 0 608 2 (all_split (c1 7 2 COc true [2] RL SI 610) 0 576 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 544 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 512 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 480 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 448 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 416 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 384 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 352 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 320 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 288 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 256 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 224 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 192 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 160 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 128 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 96 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 64 32 (all_split (c1 7 2 COc true [2] RL SI 610) 0 32 32 h1_0 h1_1) h1_2) h1_3) h1_4) h1_5) h1_6) h1_7) h1_8) h1_9) h1_10) h1_11) h1_12) h1_13) h1_14) h1_15) h1_16) h1_17) h1_18) h1_19)


set_option maxRecDepth 100000 in
theorem h2_0 : (List.range' 0 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_1 : (List.range' 48 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_2 : (List.range' 96 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_3 : (List.range' 144 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_4 : (List.range' 192 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_5 : (List.range' 240 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_6 : (List.range' 288 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_7 : (List.range' 336 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_8 : (List.range' 384 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_9 : (List.range' 432 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_10 : (List.range' 480 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_11 : (List.range' 528 48).all (c2 SI BL BS 131) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_12 : (List.range' 576 34).all (c2 SI BL BS 131) = true := by
  decide +kernel

theorem h2 : chk2 SI BL BS 610 131 = true :=
  chk2_of SI BL BS 610 131 (all_split (c2 SI BL BS 131) 0 576 34 (all_split (c2 SI BL BS 131) 0 528 48 (all_split (c2 SI BL BS 131) 0 480 48 (all_split (c2 SI BL BS 131) 0 432 48 (all_split (c2 SI BL BS 131) 0 384 48 (all_split (c2 SI BL BS 131) 0 336 48 (all_split (c2 SI BL BS 131) 0 288 48 (all_split (c2 SI BL BS 131) 0 240 48 (all_split (c2 SI BL BS 131) 0 192 48 (all_split (c2 SI BL BS 131) 0 144 48 (all_split (c2 SI BL BS 131) 0 96 48 (all_split (c2 SI BL BS 131) 0 48 48 h2_0 h2_1) h2_2) h2_3) h2_4) h2_5) h2_6) h2_7) h2_8) h2_9) h2_10) h2_11) h2_12)


set_option maxRecDepth 100000 in
theorem hV : chkV BS VT 131 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hI : chkI VT 131 LC RC 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem h3 : chk3 7 2 COc RL 610 IL = true := by decide +kernel

theorem hJ : ∀ p ∈ LC ++ RC, 6 + p.2 ≤ 16 := by decide

set_option maxRecDepth 100000 in
theorem hAV : ∀ N ≤ 16, (IL.map (fun t => gL (VT.getD N []) (gL BL t))).sum = gL AV (N + 1) := by
  decide +kernel

theorem hid (M : ℕ) : Lin LC (Ac 7 2 COc true [2]) (6 + M) = Lin RC (Ac 7 2 COc true [2]) (6 + M) :=
  A_ident 7 2 COc true [2] RL SI BL BS VT 610 131 16 h1 h2 hV LC RC 6 hI hJ IL h3 M

theorem hval (N : ℕ) (hN : N ≤ 16) : a (N + 1) = gL AV (N + 1) := by
  rw [a_eq, A_val 7 2 COc true [2] RL SI BL BS VT 610 131 16 h1 h2 hV IL h3 N hN, hAV N hN]

/-! The rest is about any sequence with these properties (kept abstract for the kernel). -/

theorem recN (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (6 + M) = Lin RC A (6 + M)) (hval : ∀ N ≤ 16, f (N + 1) = gL AV (N + 1)) (M : ℕ) : 1 * f (M + 15) + 28 * f (M + 15 - 2) + 70 * f (M + 15 - 4) + 28 * f (M + 15 - 6) + 1 * f (M + 15 - 8) = 8 * f (M + 15 - 1) + 56 * f (M + 15 - 3) + 56 * f (M + 15 - 5) + 8 * f (M + 15 - 7) := by
  have h := hid M
  simp only [LC, RC, Lin, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [show M + 15 - 1 = 6 + M + 7 + 1 by omega, ha (6 + M + 7), show M + 15 - 2 = 6 + M + 6 + 1 by omega, ha (6 + M + 6), show M + 15 - 3 = 6 + M + 5 + 1 by omega, ha (6 + M + 5), show M + 15 - 4 = 6 + M + 4 + 1 by omega, ha (6 + M + 4), show M + 15 - 5 = 6 + M + 3 + 1 by omega, ha (6 + M + 3), show M + 15 - 6 = 6 + M + 2 + 1 by omega, ha (6 + M + 2), show M + 15 - 7 = 6 + M + 1 + 1 by omega, ha (6 + M + 1), show M + 15 - 8 = 6 + M + 1 by omega, ha (6 + M), show M + 15 = 6 + M + 8 + 1 by omega, ha (6 + M + 8)]
  omega

theorem recZ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (6 + M) = Lin RC A (6 + M)) (hval : ∀ N ≤ 16, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 13 < n) : (f n : ℤ) = 8 * f (n - 1) - 28 * f (n - 2) + 56 * f (n - 3) - 70 * f (n - 4) + 56 * f (n - 5) - 28 * f (n - 6) + 8 * f (n - 7) - f (n - 8) := by
  have v1 : f 1 = 128 := hval 0 (by norm_num)
  have v2 : f 2 = 2187 := hval 1 (by norm_num)
  have v3 : f 3 = 9688 := hval 2 (by norm_num)
  have v4 : f 4 = 25047 := hval 3 (by norm_num)
  have v5 : f 5 = 52581 := hval 4 (by norm_num)
  have v6 : f 6 = 101412 := hval 5 (by norm_num)
  have v7 : f 7 = 186348 := hval 6 (by norm_num)
  have v8 : f 8 = 329167 := hval 7 (by norm_num)
  have v9 : f 9 = 561329 := hval 8 (by norm_num)
  have v10 : f 10 = 927323 := hval 9 (by norm_num)
  have v11 : f 11 = 1488515 := hval 10 (by norm_num)
  have v12 : f 12 = 2327716 := hval 11 (by norm_num)
  have v13 : f 13 = 3554534 := hval 12 (by norm_num)
  have v14 : f 14 = 5311574 := hval 13 (by norm_num)
  have v15 : f 15 = 7781550 := hval 14 (by norm_num)
  have v16 : f 16 = 11195373 := hval 15 (by norm_num)
  have v17 : f 17 = 15841279 := hval 16 (by norm_num)
  by_cases hb : 15 ≤ n
  · obtain ⟨M, rfl⟩ : ∃ M, n = M + 15 := ⟨n - 15, by omega⟩
    have := recN f A ha hid hval M
    omega
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]

theorem recQ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (6 + M) = Lin RC A (6 + M)) (hval : ∀ N ≤ 16, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 13 < n) : (f n : ℚ) = 8 * (f (n - 1) : ℚ) - 28 * (f (n - 2) : ℚ) + 56 * (f (n - 3) : ℚ) - 70 * (f (n - 4) : ℚ) + 56 * (f (n - 5) : ℚ) - 28 * (f (n - 6) : ℚ) + 8 * (f (n - 7) : ℚ) - (f (n - 8) : ℚ) := by
  have := recZ f A ha hid hval n hn
  exact_mod_cast this

theorem poly (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (6 + M) = Lin RC A (6 + M)) (hval : ∀ N ≤ 16, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 5 < n) : (f n : ℚ) = (4/315) * (n : ℚ) ^ 7 + (1/5) * (n : ℚ) ^ 6 + (112/45) * (n : ℚ) ^ 5 + (461/24) * (n : ℚ) ^ 4 + (19267/180) * (n : ℚ) ^ 3 + (50171/120) * (n : ℚ) ^ 2 + (463243/420) * (n : ℚ) - 511 := by
  have v1 : f 1 = 128 := hval 0 (by norm_num)
  have v2 : f 2 = 2187 := hval 1 (by norm_num)
  have v3 : f 3 = 9688 := hval 2 (by norm_num)
  have v4 : f 4 = 25047 := hval 3 (by norm_num)
  have v5 : f 5 = 52581 := hval 4 (by norm_num)
  have v6 : f 6 = 101412 := hval 5 (by norm_num)
  have v7 : f 7 = 186348 := hval 6 (by norm_num)
  have v8 : f 8 = 329167 := hval 7 (by norm_num)
  have v9 : f 9 = 561329 := hval 8 (by norm_num)
  have v10 : f 10 = 927323 := hval 9 (by norm_num)
  have v11 : f 11 = 1488515 := hval 10 (by norm_num)
  have v12 : f 12 = 2327716 := hval 11 (by norm_num)
  have v13 : f 13 = 3554534 := hval 12 (by norm_num)
  have v14 : f 14 = 5311574 := hval 13 (by norm_num)
  have v15 : f 15 = 7781550 := hval 14 (by norm_num)
  have v16 : f 16 = 11195373 := hval 15 (by norm_num)
  have v17 : f 17 = 15841279 := hval 16 (by norm_num)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hs : n ≤ 13
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [recQ f A ha hid hval (k + 8) (by omega), ih (k + 8 - 1) (by omega) (by omega), ih (k + 8 - 2) (by omega) (by omega), ih (k + 8 - 3) (by omega) (by omega), ih (k + 8 - 4) (by omega) (by omega), ih (k + 8 - 5) (by omega) (by omega), ih (k + 8 - 6) (by omega) (by omega), ih (k + 8 - 7) (by omega) (by omega), ih (k + 8 - 8) (by omega) (by omega)]
    simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega, show k + 8 - 8 = k + 0 by omega]
    push_cast
    ring

theorem gf (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (6 + M) = Lin RC A (6 + M)) (hval : ∀ N ≤ 16, f (N + 1) = gL AV (N + 1)) : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 8 =
    X * (128 + 1163 * X - 4224 * X ^ 2 + 1611 * X ^ 3 + 9957 * X ^ 4 - 14526 * X ^ 5 + 3960 * X ^ 6 + 4357 * X ^ 7 - 1401 * X ^ 8 - 1818 * X ^ 9 + 659 * X ^ 10 + 353 * X ^ 11 - 155 * X ^ 12) := by
  have v1 : f 1 = 128 := hval 0 (by norm_num)
  have v2 : f 2 = 2187 := hval 1 (by norm_num)
  have v3 : f 3 = 9688 := hval 2 (by norm_num)
  have v4 : f 4 = 25047 := hval 3 (by norm_num)
  have v5 : f 5 = 52581 := hval 4 (by norm_num)
  have v6 : f 6 = 101412 := hval 5 (by norm_num)
  have v7 : f 7 = 186348 := hval 6 (by norm_num)
  have v8 : f 8 = 329167 := hval 7 (by norm_num)
  have v9 : f 9 = 561329 := hval 8 (by norm_num)
  have v10 : f 10 = 927323 := hval 9 (by norm_num)
  have v11 : f 11 = 1488515 := hval 10 (by norm_num)
  have v12 : f 12 = 2327716 := hval 11 (by norm_num)
  have v13 : f 13 = 3554534 := hval 12 (by norm_num)
  have v14 : f 14 = 5311574 := hval 13 (by norm_num)
  have v15 : f 15 = 7781550 := hval 14 (by norm_num)
  have v16 : f 16 = 11195373 := hval 15 (by norm_num)
  have v17 : f 17 = 15841279 := hval 16 (by norm_num)
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hF
  have hmul : F * (1 - X) ^ 8 = F - C (8 : ℚ) * (X ^ 1 * F) + C (28 : ℚ) * (X ^ 2 * F) - C (56 : ℚ) * (X ^ 3 * F) + C (70 : ℚ) * (X ^ 4 * F) - C (56 : ℚ) * (X ^ 5 * F) + C (28 : ℚ) * (X ^ 6 * F) - C (8 : ℚ) * (X ^ 7 * F) + X ^ 8 * F := by
    (try simp only [map_ofNat]); ring
  have hnum : (X * (128 + 1163 * X - 4224 * X ^ 2 + 1611 * X ^ 3 + 9957 * X ^ 4 - 14526 * X ^ 5 + 3960 * X ^ 6 + 4357 * X ^ 7 - 1401 * X ^ 8 - 1818 * X ^ 9 + 659 * X ^ 10 + 353 * X ^ 11 - 155 * X ^ 12) : PowerSeries ℚ) = C (128 : ℚ) * X ^ 1 + C (1163 : ℚ) * X ^ 2 - C (4224 : ℚ) * X ^ 3 + C (1611 : ℚ) * X ^ 4 + C (9957 : ℚ) * X ^ 5 - C (14526 : ℚ) * X ^ 6 + C (3960 : ℚ) * X ^ 7 + C (4357 : ℚ) * X ^ 8 - C (1401 : ℚ) * X ^ 9 - C (1818 : ℚ) * X ^ 10 + C (659 : ℚ) * X ^ 11 + C (353 : ℚ) * X ^ 12 - C (155 : ℚ) * X ^ 13 := by
    (try simp only [map_ofNat]); ring
  rw [hmul, hnum]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, hF, coeff_mk]
  by_cases hn : 14 ≤ n
  · simp only [if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
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
      if_neg (show n ≠ 13 by omega),
      if_neg (show n ≠ 0 by omega),
      if_neg (show n - 1 ≠ 0 by omega),
      if_neg (show n - 2 ≠ 0 by omega),
      if_neg (show n - 3 ≠ 0 by omega),
      if_neg (show n - 4 ≠ 0 by omega),
      if_neg (show n - 5 ≠ 0 by omega),
      if_neg (show n - 6 ≠ 0 by omega),
      if_neg (show n - 7 ≠ 0 by omega),
      if_neg (show n - 8 ≠ 0 by omega),
      mul_zero, sub_zero, add_zero, mul_one, neg_zero]
    rw [recQ f A ha hid hval n (by omega)]
    ring
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]

theorem final (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (6 + M) = Lin RC A (6 + M)) (hval : ∀ N ≤ 16, f (N + 1) = gL AV (N + 1)) :
    (∀ n : ℕ, 5 < n → (f n : ℚ) = (4/315) * (n : ℚ) ^ 7 + (1/5) * (n : ℚ) ^ 6 + (112/45) * (n : ℚ) ^ 5 + (461/24) * (n : ℚ) ^ 4 + (19267/180) * (n : ℚ) ^ 3 + (50171/120) * (n : ℚ) ^ 2 + (463243/420) * (n : ℚ) - 511) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 8 =
      X * (128 + 1163 * X - 4224 * X ^ 2 + 1611 * X ^ 3 + 9957 * X ^ 4 - 14526 * X ^ 5 + 3960 * X ^ 6 + 4357 * X ^ 7 - 1401 * X ^ 8 - 1818 * X ^ 9 + 659 * X ^ 10 + 353 * X ^ 11 - 155 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (f n : ℤ) = 8 * f (n - 1) - 28 * f (n - 2) + 56 * f (n - 3) - 70 * f (n - 4) + 56 * f (n - 5) - 28 * f (n - 6) + 8 * f (n - 7) - f (n - 8) :=
  ⟨fun n hn => poly f A ha hid hval n hn, gf f A ha hid hval, fun n hn => recZ f A ha hid hval n hn⟩

end PA224138

theorem OMA.solution : type_of% @OMA.S_oeis_a224138.main :=
  PA224138.final _ _ PA224138.a_eq PA224138.hid PA224138.hval
