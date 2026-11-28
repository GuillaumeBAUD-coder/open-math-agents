import OMAStatements.S_oeis_a224137
import Mathlib

/-!
Proof of the empirical formula and Barker's conjectures for OEIS A224137
(Number of 6 X n 0..1 arrays with rows nondecreasing and antidiagonals unimodal.).

Outline.
1. Generic part (namespace UG, proved for any number of rows): the array is read column by column.
   A line (row, diagonal or antidiagonal) is unimodal iff it has no valley; appending a column
   keeps every line valley-free iff no line that has already strictly descended rises again at the
   new cell (`UC_snoc`), and the descent flags update locally (`DS_snoc`). The state after a column
   is coded as a natural number (the column in base m plus one flag bit per line ending there), and
   the computable transition `okc`/`dc` is shown to match the semantics (`okc_stS`, `dc_stS`). This
   gives a(n + 1) as a sum of continuation counts `Wc n` over the admissible first columns
   (`count_eq`).
2. Certificate (checked by the kernel, `decide +kernel`): the list of the 233 reachable states,
   their successor lists, a lumping of the states into 72 blocks with equal continuation counts,
   and the block tables up to length 14. From them, the pointwise identity
   Sum_i (-1)^i C(7, i) Wc (n + 7 - i) s = 0 for n >= 5 and every reachable s, hence the
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

namespace PA224137

open OMA.S_oeis_a224137 UG PowerSeries

def CO (_v : Fin 6 → Fin 2) : Prop := True

instance : DecidablePred CO := fun _ => instDecidableTrue

def COc (_c : ℕ) : Bool := true

theorem hCO (v : Fin 6 → Fin 2) : COc (ccode v) = true ↔ CO v := by simp [COc, CO]

theorem hU : ∀ t ∈ ([2] : List ℕ), t < 3 := by decide

theorem uc_anti {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : AntidiagUnimodal x ↔ UC 2 (fun j i => x i j) := by
  constructor
  · intro h j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    exact h i1 i2 i3 j1 j2 j3 h12 h23 (by unfold al at a1 a2; omega) (by unfold al at a1 a2; omega)
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    exact h j1 j2 j3 i1 i2 i3 h12 h23 (by unfold al; omega) (by unfold al; omega)

theorem rn_iff {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : (∀ i, Monotone (x i)) ↔ RN (fun j i => x i j) := by
  constructor
  · intro h j1 j2 hj i; exact h i hj
  · intro h i j1 j2 hj; exact h j1 j2 hj i

theorem good_iff {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Good x ↔ P CO true [2] (fun j i => x i j) := by
  unfold Good P
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, CO,
    forall_const, true_and, implies_true, eq_self_iff_true, true_implies, uc_anti, rn_iff]

theorem a_eq (N : ℕ) : a (N + 1) = Ac 6 2 COc true [2] N := by
  rw [a, Ac, ← count_eq CO COc hCO true [2] hU N]
  apply Finset.card_equiv (Equiv.piComm _)
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact good_iff x

def RL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 262146, 262150, 262154,
    262158, 262162, 262166, 262170, 262174, 262178, 262182, 262186, 262190, 262194, 262198, 262202,
    262206, 524292, 524293, 524300, 524301, 524308, 524309, 524316, 524317, 524324, 524325, 524332,
    524333, 524340, 524341, 524348, 524349, 1048584, 1048585, 1048586, 1048587, 1048600, 1048601,
    1048602, 1048603, 1048616, 1048617, 1048618, 1048619, 1048632, 1048633, 1048634, 1048635,
    1310730, 1310746, 1310762, 1310778, 2097168, 2097169, 2097170, 2097171, 2097172, 2097173,
    2097174, 2097175, 2097200, 2097201, 2097202, 2097203, 2097204, 2097205, 2097206, 2097207,
    2359314, 2359318, 2359346, 2359350, 2621460, 2621461, 2621492, 2621493, 4194336, 4194337,
    4194338, 4194339, 4194340, 4194341, 4194342, 4194343, 4194344, 4194345, 4194346, 4194347,
    4194348, 4194349, 4194350, 4194351, 4456482, 4456486, 4456490, 4456494, 4718628, 4718629,
    4718636, 4718637, 5242920, 5242921, 5242922, 5242923, 5505066, 786436, 786444, 786452, 786460,
    786468, 786476, 786484, 786492, 2883604, 2883636, 4980772, 4980780, 1572872, 1572873, 1572888,
    1572889, 1572904, 1572905, 1572920, 1572921, 5767208, 5767209, 3145744, 3145745, 3145746,
    3145747, 3145776, 3145777, 3145778, 3145779, 3407890, 3407922, 6291488, 6291489, 6291490,
    6291491, 6291492, 6291493, 6291494, 6291495, 6553634, 6553638, 6815780, 6815781, 7077924,
    1835016, 1835032, 1835048, 1835064, 6029352, 3670032, 3670033, 3670064, 3670065, 7340064,
    7340065, 7340066, 7340067, 7602210, 3932176, 3932208, 7864352, 7864353, 8126496]

def SI : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
    44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], [1, 3, 5, 7,
    9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55,
    57, 59, 61, 63], [64, 3, 65, 7, 66, 11, 67, 15, 68, 19, 69, 23, 70, 27, 71, 31, 72, 35, 73, 39,
    74, 43, 75, 47, 76, 51, 77, 55, 78, 59, 79, 63], [3, 7, 11, 15, 19, 23, 27, 31, 35, 39, 43, 47,
    51, 55, 59, 63], [80, 81, 6, 7, 82, 83, 14, 15, 84, 85, 22, 23, 86, 87, 30, 31, 88, 89, 38, 39,
    90, 91, 46, 47, 92, 93, 54, 55, 94, 95, 62, 63], [81, 7, 83, 15, 85, 23, 87, 31, 89, 39, 91,
    47, 93, 55, 95, 63], [65, 7, 67, 15, 69, 23, 71, 31, 73, 39, 75, 47, 77, 55, 79, 63], [7, 15,
    23, 31, 39, 47, 55, 63], [96, 97, 98, 99, 12, 13, 14, 15, 100, 101, 102, 103, 28, 29, 30, 31,
    104, 105, 106, 107, 44, 45, 46, 47, 108, 109, 110, 111, 60, 61, 62, 63], [97, 99, 13, 15, 101,
    103, 29, 31, 105, 107, 45, 47, 109, 111, 61, 63], [112, 99, 67, 15, 113, 103, 71, 31, 114, 107,
    75, 47, 115, 111, 79, 63], [99, 15, 103, 31, 107, 47, 111, 63], [82, 83, 14, 15, 86, 87, 30,
    31, 90, 91, 46, 47, 94, 95, 62, 63], [83, 15, 87, 31, 91, 47, 95, 63], [67, 15, 71, 31, 75, 47,
    79, 63], [15, 31, 47, 63], [116, 117, 118, 119, 120, 121, 122, 123, 24, 25, 26, 27, 28, 29, 30,
    31, 124, 125, 126, 127, 128, 129, 130, 131, 56, 57, 58, 59, 60, 61, 62, 63], [117, 119, 121,
    123, 25, 27, 29, 31, 125, 127, 129, 131, 57, 59, 61, 63], [132, 119, 133, 123, 70, 27, 71, 31,
    134, 127, 135, 131, 78, 59, 79, 63], [119, 123, 27, 31, 127, 131, 59, 63], [136, 137, 122, 123,
    86, 87, 30, 31, 138, 139, 130, 131, 94, 95, 62, 63], [137, 123, 87, 31, 139, 131, 95, 63],
    [133, 123, 71, 31, 135, 131, 79, 63], [123, 31, 131, 63], [100, 101, 102, 103, 28, 29, 30, 31,
    108, 109, 110, 111, 60, 61, 62, 63], [101, 103, 29, 31, 109, 111, 61, 63], [113, 103, 71, 31,
    115, 111, 79, 63], [103, 31, 111, 63], [86, 87, 30, 31, 94, 95, 62, 63], [87, 31, 95, 63], [71,
    31, 79, 63], [31, 63], [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153,
    154, 155, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], [141, 143, 145, 147,
    149, 151, 153, 155, 49, 51, 53, 55, 57, 59, 61, 63], [156, 143, 157, 147, 158, 151, 159, 155,
    76, 51, 77, 55, 78, 59, 79, 63], [143, 147, 151, 155, 51, 55, 59, 63], [160, 161, 146, 147,
    162, 163, 154, 155, 92, 93, 54, 55, 94, 95, 62, 63], [161, 147, 163, 155, 93, 55, 95, 63],
    [157, 147, 159, 155, 77, 55, 79, 63], [147, 155, 55, 63], [164, 165, 166, 167, 152, 153, 154,
    155, 108, 109, 110, 111, 60, 61, 62, 63], [165, 167, 153, 155, 109, 111, 61, 63], [168, 167,
    159, 155, 115, 111, 79, 63], [167, 155, 111, 63], [162, 163, 154, 155, 94, 95, 62, 63], [163,
    155, 95, 63], [159, 155, 79, 63], [155, 63], [124, 125, 126, 127, 128, 129, 130, 131, 56, 57,
    58, 59, 60, 61, 62, 63], [125, 127, 129, 131, 57, 59, 61, 63], [134, 127, 135, 131, 78, 59, 79,
    63], [127, 131, 59, 63], [138, 139, 130, 131, 94, 95, 62, 63], [139, 131, 95, 63], [135, 131,
    79, 63], [131, 63], [108, 109, 110, 111, 60, 61, 62, 63], [109, 111, 61, 63], [115, 111, 79,
    63], [111, 63], [94, 95, 62, 63], [95, 63], [79, 63], [63], [64, 3, 65, 7, 66, 11, 67, 15, 68,
    19, 69, 23, 70, 27, 71, 31, 72, 35, 73, 39, 74, 43, 75, 47, 76, 51, 77, 55, 78, 59, 79, 63],
    [65, 7, 67, 15, 69, 23, 71, 31, 73, 39, 75, 47, 77, 55, 79, 63], [112, 99, 67, 15, 113, 103,
    71, 31, 114, 107, 75, 47, 115, 111, 79, 63], [67, 15, 71, 31, 75, 47, 79, 63], [132, 119, 133,
    123, 70, 27, 71, 31, 134, 127, 135, 131, 78, 59, 79, 63], [133, 123, 71, 31, 135, 131, 79, 63],
    [113, 103, 71, 31, 115, 111, 79, 63], [71, 31, 79, 63], [156, 143, 157, 147, 158, 151, 159,
    155, 76, 51, 77, 55, 78, 59, 79, 63], [157, 147, 159, 155, 77, 55, 79, 63], [168, 167, 159,
    155, 115, 111, 79, 63], [159, 155, 79, 63], [134, 127, 135, 131, 78, 59, 79, 63], [135, 131,
    79, 63], [115, 111, 79, 63], [79, 63], [169, 65, 170, 67, 171, 69, 172, 71, 173, 73, 174, 75,
    175, 77, 176, 79], [], [170, 67, 172, 71, 174, 75, 176, 79], [], [177, 133, 172, 71, 178, 135,
    176, 79], [], [172, 71, 176, 79], [], [179, 157, 180, 159, 175, 77, 176, 79], [], [180, 159,
    176, 79], [], [178, 135, 176, 79], [], [176, 79], [], [181, 182, 82, 83, 183, 184, 86, 87, 185,
    186, 90, 91, 187, 188, 94, 95], [182, 83, 184, 87, 186, 91, 188, 95], [], [], [183, 184, 86,
    87, 187, 188, 94, 95], [184, 87, 188, 95], [], [], [189, 190, 162, 163, 187, 188, 94, 95],
    [190, 163, 188, 95], [], [], [187, 188, 94, 95], [188, 95], [], [], [], [], [], [], [191, 192,
    193, 194, 100, 101, 102, 103, 195, 196, 197, 198, 108, 109, 110, 111], [192, 194, 101, 103,
    196, 198, 109, 111], [199, 194, 113, 103, 200, 198, 115, 111], [194, 103, 198, 111], [], [],
    [], [], [195, 196, 197, 198, 108, 109, 110, 111], [196, 198, 109, 111], [200, 198, 115, 111],
    [198, 111], [], [], [], [], [199, 194, 113, 103, 200, 198, 115, 111], [], [200, 198, 115, 111],
    [], [], [], [], [], [201, 202, 203, 204, 205, 206, 207, 208, 124, 125, 126, 127, 128, 129, 130,
    131], [202, 204, 206, 208, 125, 127, 129, 131], [209, 204, 210, 208, 134, 127, 135, 131], [204,
    208, 127, 131], [211, 212, 207, 208, 138, 139, 130, 131], [212, 208, 139, 131], [210, 208, 135,
    131], [208, 131], [], [], [], [], [], [], [], [], [209, 204, 210, 208, 134, 127, 135, 131],
    [210, 208, 135, 131], [], [], [213, 210, 178, 135], [], [], [], [], [], [], [], [], [169, 65,
    170, 67, 171, 69, 172, 71, 173, 73, 174, 75, 175, 77, 176, 79], [170, 67, 172, 71, 174, 75,
    176, 79], [177, 133, 172, 71, 178, 135, 176, 79], [172, 71, 176, 79], [179, 157, 180, 159, 175,
    77, 176, 79], [180, 159, 176, 79], [178, 135, 176, 79], [176, 79], [], [], [213, 210, 178,
    135], [], [214, 170, 215, 172, 216, 174, 217, 176], [], [215, 172, 217, 176], [], [218, 180,
    217, 176], [], [217, 176], [], [], [], [219, 220, 183, 184, 221, 222, 187, 188], [220, 184,
    222, 188], [], [], [221, 222, 187, 188], [222, 188], [], [], [], [], [223, 224, 225, 226, 195,
    196, 197, 198], [224, 226, 196, 198], [227, 226, 200, 198], [226, 198], [], [], [], [], [227,
    226, 200, 198], [], [], [], [], [214, 170, 215, 172, 216, 174, 217, 176], [215, 172, 217, 176],
    [218, 180, 217, 176], [217, 176], [], [228, 215, 229, 217], [], [229, 217], [], [230, 231, 221,
    222], [231, 222], [], [], [], [228, 215, 229, 217], [229, 217], [232, 229], [], [232, 229]]

def BL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 11, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 18, 21, 22, 24, 22, 25, 26, 27, 28, 16, 29, 30, 31, 18, 32, 33, 31, 20, 34, 35, 34,
    22, 36, 37, 29, 18, 32, 35, 34, 22, 36, 38, 32, 22, 36, 39, 36, 26, 40, 2, 6, 10, 13, 17, 21,
    21, 25, 16, 18, 20, 22, 18, 22, 22, 26, 41, 42, 43, 42, 44, 42, 45, 42, 46, 42, 47, 42, 47, 42,
    48, 42, 49, 50, 42, 42, 51, 52, 42, 42, 53, 52, 42, 42, 54, 55, 42, 42, 42, 42, 42, 42, 56, 57,
    50, 52, 42, 42, 42, 42, 58, 59, 52, 55, 42, 42, 42, 42, 50, 42, 52, 42, 42, 42, 42, 42, 60, 61,
    57, 59, 50, 52, 52, 55, 42, 42, 42, 42, 42, 42, 42, 42, 57, 52, 42, 42, 52, 42, 42, 42, 42, 42,
    42, 42, 42, 41, 43, 44, 45, 46, 47, 47, 48, 42, 42, 52, 42, 62, 42, 63, 42, 54, 42, 64, 42, 42,
    42, 65, 52, 42, 42, 66, 55, 42, 42, 42, 42, 67, 59, 52, 55, 42, 42, 42, 42, 52, 42, 42, 42, 42,
    62, 63, 54, 64, 42, 68, 42, 69, 42, 70, 55, 42, 42, 42, 68, 69, 71, 42, 71]

def BS : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 11, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 18, 21, 22, 24, 22, 25, 26, 27, 28, 16, 29, 30, 31, 18, 32, 33, 31, 20, 34,
    35, 34, 22, 36, 37, 29, 18, 32, 35, 34, 22, 36, 38, 32, 22, 36, 39, 36, 26, 40], [1, 3, 5, 7,
    9, 11, 11, 14, 16, 18, 20, 22, 18, 22, 22, 26, 28, 29, 31, 32, 31, 34, 34, 36, 29, 32, 34, 36,
    32, 36, 36, 40], [2, 3, 6, 7, 10, 11, 13, 14, 17, 18, 21, 22, 21, 22, 25, 26, 16, 29, 18, 32,
    20, 34, 22, 36, 18, 32, 22, 36, 22, 36, 26, 40], [3, 7, 11, 14, 18, 22, 22, 26, 29, 32, 34, 36,
    32, 36, 36, 40], [41, 42, 6, 7, 43, 42, 13, 14, 44, 42, 21, 22, 45, 42, 25, 26, 46, 42, 18, 32,
    47, 42, 22, 36, 47, 42, 22, 36, 48, 42, 26, 40], [42, 7, 42, 14, 42, 22, 42, 26, 42, 32, 42,
    36, 42, 36, 42, 40], [6, 7, 13, 14, 21, 22, 25, 26, 18, 32, 22, 36, 22, 36, 26, 40], [7, 14,
    22, 26, 32, 36, 36, 40], [49, 50, 42, 42, 12, 11, 13, 14, 51, 52, 42, 42, 24, 22, 25, 26, 53,
    52, 42, 42, 35, 34, 22, 36, 54, 55, 42, 42, 39, 36, 26, 40], [50, 42, 11, 14, 52, 42, 22, 26,
    52, 42, 34, 36, 55, 42, 36, 40], [42, 42, 13, 14, 42, 42, 25, 26, 42, 42, 22, 36, 42, 42, 26,
    40], [42, 14, 42, 26, 42, 36, 42, 40], [43, 42, 13, 14, 45, 42, 25, 26, 47, 42, 22, 36, 48, 42,
    26, 40], [13, 14, 25, 26, 22, 36, 26, 40], [14, 26, 36, 40], [56, 57, 50, 52, 42, 42, 42, 42,
    23, 18, 21, 22, 24, 22, 25, 26, 58, 59, 52, 55, 42, 42, 42, 42, 38, 32, 22, 36, 39, 36, 26,
    40], [57, 52, 42, 42, 18, 22, 22, 26, 59, 55, 42, 42, 32, 36, 36, 40], [50, 52, 42, 42, 21, 22,
    25, 26, 52, 55, 42, 42, 22, 36, 26, 40], [52, 42, 22, 26, 55, 42, 36, 40], [42, 42, 42, 42, 45,
    42, 25, 26, 42, 42, 42, 42, 48, 42, 26, 40], [42, 42, 42, 26, 42, 42, 42, 40], [42, 42, 25, 26,
    42, 42, 26, 40], [42, 26, 42, 40], [51, 52, 42, 42, 24, 22, 25, 26, 54, 55, 42, 42, 39, 36, 26,
    40], [45, 42, 25, 26, 48, 42, 26, 40], [25, 26, 26, 40], [26, 40], [60, 61, 57, 59, 50, 52, 52,
    55, 42, 42, 42, 42, 42, 42, 42, 42, 37, 29, 18, 32, 35, 34, 22, 36, 38, 32, 22, 36, 39, 36, 26,
    40], [61, 59, 52, 55, 42, 42, 42, 42, 29, 32, 34, 36, 32, 36, 36, 40], [59, 55, 42, 42, 32, 36,
    36, 40], [52, 42, 52, 55, 42, 42, 42, 42, 47, 42, 22, 36, 48, 42, 26, 40], [42, 55, 42, 42, 42,
    36, 42, 40], [55, 42, 36, 40], [42, 42, 42, 42, 42, 42, 42, 42, 54, 55, 42, 42, 39, 36, 26,
    40], [42, 42, 42, 40], [42, 42, 42, 42, 48, 42, 26, 40], [42, 40], [58, 59, 52, 55, 42, 42, 42,
    42, 38, 32, 22, 36, 39, 36, 26, 40], [54, 55, 42, 42, 39, 36, 26, 40], [48, 42, 26, 40], [40],
    [41, 6, 43, 13, 44, 21, 45, 25, 46, 18, 47, 22, 47, 22, 48, 26], [], [43, 13, 45, 25, 47, 22,
    48, 26], [42, 42, 45, 25, 42, 42, 48, 26], [45, 25, 48, 26], [52, 52, 42, 42, 47, 22, 48, 26],
    [42, 42, 48, 26], [48, 26], [62, 42, 43, 42, 63, 42, 45, 42, 54, 42, 47, 42, 64, 42, 48, 42],
    [42, 42, 42, 42, 42, 42, 42, 42], [63, 42, 45, 42, 64, 42, 48, 42], [42, 42, 42, 42], [42, 42,
    42, 42, 64, 42, 48, 42], [64, 42, 48, 42], [42, 42], [65, 52, 42, 42, 51, 52, 42, 42, 66, 55,
    42, 42, 54, 55, 42, 42], [52, 42, 52, 42, 55, 42, 55, 42], [66, 55, 42, 42, 54, 55, 42, 42],
    [55, 42, 55, 42], [67, 59, 52, 55, 42, 42, 42, 42, 58, 59, 52, 55, 42, 42, 42, 42], [59, 55,
    42, 42, 59, 55, 42, 42], [62, 43, 63, 45, 54, 47, 64, 48], [63, 45, 64, 48], [64, 48], [68, 42,
    63, 42, 69, 42, 64, 42], [69, 42, 64, 42], [70, 55, 42, 42, 66, 55, 42, 42], [68, 63, 69, 64],
    [69, 64], [71, 42, 69, 42], [71, 69]]

def VT : List (List ℕ) := [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [64, 32, 32, 16, 32, 16, 16, 8, 32, 16, 16, 8,
    16, 8, 4, 32, 16, 16, 8, 16, 8, 8, 4, 16, 8, 4, 2, 32, 16, 8, 16, 8, 4, 16, 4, 8, 2, 16, 8, 4,
    1, 16, 0, 8, 8, 4, 8, 4, 2, 16, 8, 8, 4, 8, 4, 2, 16, 8, 8, 4, 16, 8, 8, 4, 2, 8, 4, 8, 4, 2,
    4, 2], [729, 243, 243, 81, 135, 27, 81, 27, 135, 45, 27, 9, 45, 27, 9, 135, 45, 45, 15, 15, 3,
    9, 3, 45, 15, 9, 3, 135, 45, 15, 25, 5, 5, 15, 1, 5, 1, 45, 15, 5, 1, 108, 0, 36, 12, 12, 20,
    4, 4, 36, 0, 12, 0, 4, 4, 0, 36, 12, 12, 4, 36, 12, 36, 12, 4, 12, 4, 12, 12, 4, 4, 4], [2692,
    648, 720, 180, 400, 50, 200, 50, 196, 28, 56, 14, 112, 56, 14, 200, 48, 32, 8, 32, 4, 16, 4,
    56, 32, 16, 4, 188, 46, 12, 16, 2, 2, 14, 1, 8, 1, 50, 14, 8, 1, 350, 0, 98, 28, 28, 14, 7, 7,
    112, 0, 32, 0, 8, 8, 0, 32, 0, 8, 0, 32, 8, 112, 32, 8, 32, 8, 8, 32, 8, 8, 8], [6392, 1170,
    1495, 299, 924, 77, 385, 77, 440, 40, 100, 20, 240, 100, 20, 215, 25, 50, 10, 60, 5, 25, 5,
    110, 60, 25, 5, 161, 29, 5, 24, 2, 2, 22, 1, 12, 1, 43, 22, 12, 1, 847, 0, 220, 55, 55, 22, 11,
    11, 300, 0, 75, 0, 15, 15, 0, 80, 0, 16, 0, 16, 0, 300, 75, 15, 80, 16, 16, 80, 16, 16, 16],
    [12874, 1850, 2730, 455, 1904, 112, 672, 112, 918, 54, 162, 27, 459, 162, 27, 390, 30, 72, 12,
    102, 6, 36, 6, 204, 102, 36, 6, 144, 14, 5, 34, 2, 2, 34, 1, 17, 1, 65, 34, 17, 1, 1792, 0,
    432, 96, 96, 32, 16, 16, 702, 0, 156, 0, 26, 26, 0, 186, 0, 31, 0, 32, 0, 702, 156, 26, 186,
    31, 32, 186, 31, 32, 32], [24095, 2790, 4655, 665, 3588, 156, 1092, 156, 1785, 70, 245, 35,
    805, 245, 35, 693, 35, 98, 14, 161, 7, 49, 7, 357, 161, 49, 7, 209, 14, 5, 46, 2, 2, 51, 1, 23,
    1, 99, 51, 23, 1, 3432, 0, 770, 154, 154, 44, 22, 22, 1470, 0, 294, 0, 42, 42, 0, 399, 0, 57,
    0, 63, 0, 1470, 294, 42, 399, 57, 63, 399, 57, 63, 63], [42832, 4082, 7520, 940, 6300, 210,
    1680, 210, 3256, 88, 352, 44, 1320, 352, 44, 1200, 40, 128, 16, 240, 8, 64, 8, 592, 240, 64, 8,
    308, 14, 5, 60, 2, 2, 74, 1, 30, 1, 150, 74, 30, 1, 6090, 0, 1276, 232, 232, 58, 29, 29, 2816,
    0, 512, 0, 64, 64, 0, 792, 0, 99, 0, 120, 0, 2816, 512, 64, 792, 99, 120, 792, 99, 120, 120],
    [72888, 5816, 11628, 1292, 10450, 275, 2475, 275, 5616, 108, 486, 54, 2052, 486, 54, 2016, 45,
    162, 18, 342, 9, 81, 9, 936, 342, 81, 9, 458, 14, 5, 76, 2, 2, 104, 1, 38, 1, 224, 104, 38, 1,
    10175, 0, 1998, 333, 333, 74, 37, 37, 5022, 0, 837, 0, 93, 93, 0, 1467, 0, 163, 0, 219, 0,
    5022, 837, 93, 1467, 163, 219, 1467, 163, 219, 219], [119424, 8096, 17340, 1734, 16544, 352,
    3520, 352, 9230, 130, 650, 65, 3055, 650, 65, 3280, 50, 200, 20, 470, 10, 100, 10, 1420, 470,
    100, 10, 682, 14, 5, 94, 2, 2, 142, 1, 47, 1, 328, 142, 47, 1, 16192, 0, 2990, 460, 460, 92,
    46, 46, 8450, 0, 1300, 0, 130, 130, 0, 2560, 0, 256, 0, 382, 0, 8450, 1300, 130, 2560, 256,
    382, 2560, 256, 382, 382], [189263, 11041, 25080, 2280, 25194, 442, 4862, 442, 14553, 154, 847,
    77, 4389, 847, 77, 5170, 55, 242, 22, 627, 11, 121, 11, 2079, 627, 121, 11, 1010, 14, 5, 114,
    2, 2, 189, 1, 57, 1, 470, 189, 57, 1, 24752, 0, 4312, 616, 616, 112, 56, 56, 13552, 0, 1936, 0,
    176, 176, 0, 4246, 0, 386, 0, 638, 0, 13552, 1936, 176, 4246, 386, 638, 4246, 386, 638, 638],
    [291226, 14786, 35340, 2945, 37128, 546, 6552, 546, 22140, 180, 1080, 90, 6120, 1080, 90, 7908,
    60, 288, 24, 816, 12, 144, 12, 2952, 816, 144, 12, 1480, 14, 5, 136, 2, 2, 246, 1, 68, 1, 659,
    246, 68, 1, 36582, 0, 6030, 804, 804, 134, 67, 67, 20880, 0, 2784, 0, 232, 232, 0, 6744, 0,
    562, 0, 1024, 0, 20880, 2784, 232, 6744, 562, 1024, 6744, 562, 1024, 1024], [436500, 19483,
    48685, 3745, 53200, 665, 8645, 665, 32656, 208, 1352, 104, 8320, 1352, 104, 11765, 65, 338, 26,
    1040, 13, 169, 13, 4082, 1040, 169, 13, 2139, 14, 5, 160, 2, 2, 314, 1, 80, 1, 905, 314, 80, 1,
    52535, 0, 8216, 1027, 1027, 158, 79, 79, 31096, 0, 3887, 0, 299, 299, 0, 10322, 0, 794, 0,
    1586, 0, 31096, 3887, 299, 10322, 794, 1586, 10322, 794, 1586, 1586], [639038, 25302, 65758,
    4697, 74400, 800, 11200, 800, 46886, 238, 1666, 119, 11067, 1666, 119, 17066, 70, 392, 28,
    1302, 14, 196, 14, 5516, 1302, 196, 14, 3044, 14, 5, 186, 2, 2, 394, 1, 93, 1, 1219, 394, 93,
    1, 73600, 0, 10948, 1288, 1288, 184, 92, 92, 44982, 0, 5292, 0, 378, 378, 0, 15302, 0, 1093, 0,
    2380, 0, 44982, 5292, 378, 15302, 1093, 2380, 15302, 1093, 2380, 2380], [915991, 32432, 87285,
    5819, 101864, 952, 14280, 952, 65745, 270, 2025, 135, 14445, 2025, 135, 24195, 75, 450, 30,
    1605, 15, 225, 15, 7305, 1605, 225, 15, 4263, 14, 5, 214, 2, 2, 487, 1, 107, 1, 1613, 487, 107,
    1, 100912, 0, 14310, 1590, 1590, 212, 106, 106, 63450, 0, 7050, 0, 470, 470, 0, 22065, 0, 1471,
    0, 3473, 0, 63450, 7050, 470, 22065, 1471, 3473, 22065, 1471, 3473, 3473]]

def IL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
    22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
    46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

def AV : List ℕ := [0, 64, 729, 2692, 6392, 12874, 24095, 42832, 72888, 119424, 189263, 291226,
    436500, 639038, 915991, 1288172]

def LC : List (ℕ × ℕ) := [(1, 7), (21, 5), (35, 3), (7, 1)]

def RC : List (ℕ × ℕ) := [(7, 6), (35, 4), (21, 2), (1, 0)]

set_option maxRecDepth 100000 in
theorem h1_0 : (List.range' 0 64).all (c1 6 2 COc true [2] RL SI 233) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_1 : (List.range' 64 64).all (c1 6 2 COc true [2] RL SI 233) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_2 : (List.range' 128 64).all (c1 6 2 COc true [2] RL SI 233) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h1_3 : (List.range' 192 41).all (c1 6 2 COc true [2] RL SI 233) = true := by
  decide +kernel

theorem h1 : chk1 6 2 COc true [2] RL SI 233 = true :=
  chk1_of 6 2 COc true [2] RL SI 233 (all_split (c1 6 2 COc true [2] RL SI 233) 0 192 41 (all_split (c1 6 2 COc true [2] RL SI 233) 0 128 64 (all_split (c1 6 2 COc true [2] RL SI 233) 0 64 64 h1_0 h1_1) h1_2) h1_3)


set_option maxRecDepth 100000 in
theorem h2_0 : (List.range' 0 48).all (c2 SI BL BS 72) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_1 : (List.range' 48 48).all (c2 SI BL BS 72) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_2 : (List.range' 96 48).all (c2 SI BL BS 72) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_3 : (List.range' 144 48).all (c2 SI BL BS 72) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem h2_4 : (List.range' 192 41).all (c2 SI BL BS 72) = true := by
  decide +kernel

theorem h2 : chk2 SI BL BS 233 72 = true :=
  chk2_of SI BL BS 233 72 (all_split (c2 SI BL BS 72) 0 192 41 (all_split (c2 SI BL BS 72) 0 144 48 (all_split (c2 SI BL BS 72) 0 96 48 (all_split (c2 SI BL BS 72) 0 48 48 h2_0 h2_1) h2_2) h2_3) h2_4)


set_option maxRecDepth 100000 in
theorem hV : chkV BS VT 72 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hI : chkI VT 72 LC RC 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem h3 : chk3 6 2 COc RL 233 IL = true := by decide +kernel

theorem hJ : ∀ p ∈ LC ++ RC, 5 + p.2 ≤ 14 := by decide

set_option maxRecDepth 100000 in
theorem hAV : ∀ N ≤ 14, (IL.map (fun t => gL (VT.getD N []) (gL BL t))).sum = gL AV (N + 1) := by
  decide +kernel

theorem hid (M : ℕ) : Lin LC (Ac 6 2 COc true [2]) (5 + M) = Lin RC (Ac 6 2 COc true [2]) (5 + M) :=
  A_ident 6 2 COc true [2] RL SI BL BS VT 233 72 14 h1 h2 hV LC RC 5 hI hJ IL h3 M

theorem hval (N : ℕ) (hN : N ≤ 14) : a (N + 1) = gL AV (N + 1) := by
  rw [a_eq, A_val 6 2 COc true [2] RL SI BL BS VT 233 72 14 h1 h2 hV IL h3 N hN, hAV N hN]

/-! The rest is about any sequence with these properties (kept abstract for the kernel). -/

theorem recN (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (5 + M) = Lin RC A (5 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) (M : ℕ) : 1 * f (M + 13) + 21 * f (M + 13 - 2) + 35 * f (M + 13 - 4) + 7 * f (M + 13 - 6) = 7 * f (M + 13 - 1) + 35 * f (M + 13 - 3) + 21 * f (M + 13 - 5) + 1 * f (M + 13 - 7) := by
  have h := hid M
  simp only [LC, RC, Lin, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [show M + 13 - 1 = 5 + M + 6 + 1 by omega, ha (5 + M + 6), show M + 13 - 2 = 5 + M + 5 + 1 by omega, ha (5 + M + 5), show M + 13 - 3 = 5 + M + 4 + 1 by omega, ha (5 + M + 4), show M + 13 - 4 = 5 + M + 3 + 1 by omega, ha (5 + M + 3), show M + 13 - 5 = 5 + M + 2 + 1 by omega, ha (5 + M + 2), show M + 13 - 6 = 5 + M + 1 + 1 by omega, ha (5 + M + 1), show M + 13 - 7 = 5 + M + 1 by omega, ha (5 + M), show M + 13 = 5 + M + 7 + 1 by omega, ha (5 + M + 7)]
  omega

theorem recZ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (5 + M) = Lin RC A (5 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 11 < n) : (f n : ℤ) = 7 * f (n - 1) - 21 * f (n - 2) + 35 * f (n - 3) - 35 * f (n - 4) + 21 * f (n - 5) - 7 * f (n - 6) + f (n - 7) := by
  have v1 : f 1 = 64 := hval 0 (by norm_num)
  have v2 : f 2 = 729 := hval 1 (by norm_num)
  have v3 : f 3 = 2692 := hval 2 (by norm_num)
  have v4 : f 4 = 6392 := hval 3 (by norm_num)
  have v5 : f 5 = 12874 := hval 4 (by norm_num)
  have v6 : f 6 = 24095 := hval 5 (by norm_num)
  have v7 : f 7 = 42832 := hval 6 (by norm_num)
  have v8 : f 8 = 72888 := hval 7 (by norm_num)
  have v9 : f 9 = 119424 := hval 8 (by norm_num)
  have v10 : f 10 = 189263 := hval 9 (by norm_num)
  have v11 : f 11 = 291226 := hval 10 (by norm_num)
  have v12 : f 12 = 436500 := hval 11 (by norm_num)
  have v13 : f 13 = 639038 := hval 12 (by norm_num)
  have v14 : f 14 = 915991 := hval 13 (by norm_num)
  have v15 : f 15 = 1288172 := hval 14 (by norm_num)
  by_cases hb : 13 ≤ n
  · obtain ⟨M, rfl⟩ : ∃ M, n = M + 13 := ⟨n - 13, by omega⟩
    have := recN f A ha hid hval M
    omega
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

theorem recQ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (5 + M) = Lin RC A (5 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 11 < n) : (f n : ℚ) = 7 * (f (n - 1) : ℚ) - 21 * (f (n - 2) : ℚ) + 35 * (f (n - 3) : ℚ) - 35 * (f (n - 4) : ℚ) + 21 * (f (n - 5) : ℚ) - 7 * (f (n - 6) : ℚ) + (f (n - 7) : ℚ) := by
  have := recZ f A ha hid hval n hn
  exact_mod_cast this

theorem poly (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (5 + M) = Lin RC A (5 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 4 < n) : (f n : ℚ) = (2/45) * (n : ℚ) ^ 6 + (8/15) * (n : ℚ) ^ 5 + (181/36) * (n : ℚ) ^ 4 + 28 * (n : ℚ) ^ 3 + (19247/180) * (n : ℚ) ^ 2 + (3952/15) * (n : ℚ) - 120 := by
  have v1 : f 1 = 64 := hval 0 (by norm_num)
  have v2 : f 2 = 729 := hval 1 (by norm_num)
  have v3 : f 3 = 2692 := hval 2 (by norm_num)
  have v4 : f 4 = 6392 := hval 3 (by norm_num)
  have v5 : f 5 = 12874 := hval 4 (by norm_num)
  have v6 : f 6 = 24095 := hval 5 (by norm_num)
  have v7 : f 7 = 42832 := hval 6 (by norm_num)
  have v8 : f 8 = 72888 := hval 7 (by norm_num)
  have v9 : f 9 = 119424 := hval 8 (by norm_num)
  have v10 : f 10 = 189263 := hval 9 (by norm_num)
  have v11 : f 11 = 291226 := hval 10 (by norm_num)
  have v12 : f 12 = 436500 := hval 11 (by norm_num)
  have v13 : f 13 = 639038 := hval 12 (by norm_num)
  have v14 : f 14 = 915991 := hval 13 (by norm_num)
  have v15 : f 15 = 1288172 := hval 14 (by norm_num)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hs : n ≤ 11
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [recQ f A ha hid hval (k + 7) (by omega), ih (k + 7 - 1) (by omega) (by omega), ih (k + 7 - 2) (by omega) (by omega), ih (k + 7 - 3) (by omega) (by omega), ih (k + 7 - 4) (by omega) (by omega), ih (k + 7 - 5) (by omega) (by omega), ih (k + 7 - 6) (by omega) (by omega), ih (k + 7 - 7) (by omega) (by omega)]
    simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega, show k + 7 - 7 = k + 0 by omega]
    push_cast
    ring

theorem gf (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (5 + M) = Lin RC A (5 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 7 =
    X * (64 + 281 * X - 1067 * X ^ 2 + 617 * X ^ 3 + 1387 * X ^ 4 - 1840 * X ^ 5 + 160 * X ^ 6 + 696 * X ^ 7 - 172 * X ^ 8 - 154 * X ^ 9 + 60 * X ^ 10) := by
  have v1 : f 1 = 64 := hval 0 (by norm_num)
  have v2 : f 2 = 729 := hval 1 (by norm_num)
  have v3 : f 3 = 2692 := hval 2 (by norm_num)
  have v4 : f 4 = 6392 := hval 3 (by norm_num)
  have v5 : f 5 = 12874 := hval 4 (by norm_num)
  have v6 : f 6 = 24095 := hval 5 (by norm_num)
  have v7 : f 7 = 42832 := hval 6 (by norm_num)
  have v8 : f 8 = 72888 := hval 7 (by norm_num)
  have v9 : f 9 = 119424 := hval 8 (by norm_num)
  have v10 : f 10 = 189263 := hval 9 (by norm_num)
  have v11 : f 11 = 291226 := hval 10 (by norm_num)
  have v12 : f 12 = 436500 := hval 11 (by norm_num)
  have v13 : f 13 = 639038 := hval 12 (by norm_num)
  have v14 : f 14 = 915991 := hval 13 (by norm_num)
  have v15 : f 15 = 1288172 := hval 14 (by norm_num)
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hF
  have hmul : F * (1 - X) ^ 7 = F - C (7 : ℚ) * (X ^ 1 * F) + C (21 : ℚ) * (X ^ 2 * F) - C (35 : ℚ) * (X ^ 3 * F) + C (35 : ℚ) * (X ^ 4 * F) - C (21 : ℚ) * (X ^ 5 * F) + C (7 : ℚ) * (X ^ 6 * F) - X ^ 7 * F := by
    (try simp only [map_ofNat]); ring
  have hnum : (X * (64 + 281 * X - 1067 * X ^ 2 + 617 * X ^ 3 + 1387 * X ^ 4 - 1840 * X ^ 5 + 160 * X ^ 6 + 696 * X ^ 7 - 172 * X ^ 8 - 154 * X ^ 9 + 60 * X ^ 10) : PowerSeries ℚ) = C (64 : ℚ) * X ^ 1 + C (281 : ℚ) * X ^ 2 - C (1067 : ℚ) * X ^ 3 + C (617 : ℚ) * X ^ 4 + C (1387 : ℚ) * X ^ 5 - C (1840 : ℚ) * X ^ 6 + C (160 : ℚ) * X ^ 7 + C (696 : ℚ) * X ^ 8 - C (172 : ℚ) * X ^ 9 - C (154 : ℚ) * X ^ 10 + C (60 : ℚ) * X ^ 11 := by
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
      mul_zero, sub_zero, add_zero, mul_one, neg_zero]
    rw [recQ f A ha hid hval n (by omega)]
    ring
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

theorem final (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (5 + M) = Lin RC A (5 + M)) (hval : ∀ N ≤ 14, f (N + 1) = gL AV (N + 1)) :
    (∀ n : ℕ, 4 < n → (f n : ℚ) = (2/45) * (n : ℚ) ^ 6 + (8/15) * (n : ℚ) ^ 5 + (181/36) * (n : ℚ) ^ 4 + 28 * (n : ℚ) ^ 3 + (19247/180) * (n : ℚ) ^ 2 + (3952/15) * (n : ℚ) - 120) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 7 =
      X * (64 + 281 * X - 1067 * X ^ 2 + 617 * X ^ 3 + 1387 * X ^ 4 - 1840 * X ^ 5 + 160 * X ^ 6 + 696 * X ^ 7 - 172 * X ^ 8 - 154 * X ^ 9 + 60 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (f n : ℤ) = 7 * f (n - 1) - 21 * f (n - 2) + 35 * f (n - 3) - 35 * f (n - 4) + 21 * f (n - 5) - 7 * f (n - 6) + f (n - 7) :=
  ⟨fun n hn => poly f A ha hid hval n hn, gf f A ha hid hval, fun n hn => recZ f A ha hid hval n hn⟩

end PA224137

theorem OMA.solution : type_of% @OMA.S_oeis_a224137.main :=
  PA224137.final _ _ PA224137.a_eq PA224137.hid PA224137.hval
