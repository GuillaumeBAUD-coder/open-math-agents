import OMAStatements.S_oeis_a275229
import Mathlib

namespace OMA.Helpers_a275229
open OMA.S_oeis_a275229 Finset

/-! ### Orbit lemma: renaming colours -/

def perm (σ : Equiv.Perm (Fin 3)) {R C : ℕ} (x : Fin R → Fin C → Fin 3) : Fin R → Fin C → Fin 3 :=
  fun i j => σ (x i j)

lemma cond_perm {R C : ℕ} (L : List (ℤ × ℤ)) (σ : Equiv.Perm (Fin 3)) (x : Fin R → Fin C → Fin 3) :
    Cond L (perm σ x) ↔ Cond L x := by
  unfold Cond perm
  constructor
  · intro h i i' j j' hm he; exact h i i' j j' hm (by rw [he])
  · intro h i i' j j' hm he; exact h i i' j j' hm (σ.injective he)

/-- the row-major first position -/
lemma rmn_zero {R C : ℕ} (x : Fin R → Fin C → Fin 3) (h : RowMajorNew x) (i : Fin R) (j : Fin C)
    (hi : i.val = 0) (hj : j.val = 0) : x i j = 0 := by
  by_contra hne
  obtain ⟨i', j', hij, _⟩ := h i j 0 (by
    rcases Fin.eq_zero_or_eq_succ (x i j) with h0 | ⟨k, hk⟩
    · exact absurd h0 hne
    · rw [hk]; exact Fin.succ_pos k)
  rcases hij with h1 | ⟨_, h2⟩
  · exact absurd h1 (by rw [Fin.lt_def]; omega)
  · exact absurd h2 (by rw [Fin.lt_def]; omega)

def before {R C : ℕ} (p q : Fin R × Fin C) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

lemma before_iff {R C : ℕ} (p q : Fin R × Fin C) : before p q ↔ toLex p < toLex q := by
  unfold before; rw [Prod.Lex.toLex_lt_toLex]

/-- If x is in row major order and uses a nonzero value, the first nonzero value is 1 -/
lemma first_nonzero {R C : ℕ} (x : Fin R → Fin C → Fin 3) (h : RowMajorNew x) (p : Fin R × Fin C)
    (hp : x p.1 p.2 ≠ 0) (hmin : ∀ q, before q p → x q.1 q.2 = 0) : x p.1 p.2 = 1 := by
  by_contra h1
  have h2 : x p.1 p.2 = 2 := by
    have := (x p.1 p.2).isLt
    apply Fin.ext
    have h0 : (x p.1 p.2).val ≠ 0 := fun e => hp (Fin.ext e)
    have h1' : (x p.1 p.2).val ≠ 1 := fun e => h1 (Fin.ext e)
    simp only [Fin.val_two]; omega
  obtain ⟨i', j', hij, he⟩ := h p.1 p.2 1 (by rw [h2]; decide)
  have := hmin (i', j') hij
  rw [he] at this
  exact absurd this (by decide)

lemma exists_first {R C : ℕ} (P : Fin R × Fin C → Prop) [DecidablePred P] (h : ∃ q, P q) :
    ∃ p, P p ∧ ∀ q, before q p → ¬P q := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Lex (Fin R × Fin C)), S = (univ.filter P).image toLex := ⟨_, rfl⟩
  have hne : S.Nonempty := by
    obtain ⟨q, hq⟩ := h; exact ⟨toLex q, by simp [hS, hq]⟩
  have hm := Finset.min'_mem S hne
  have hmin := Finset.min'_le S
  have hm' : S.min' hne ∈ (univ.filter P).image toLex := by rw [← hS]; exact hm
  obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hm'
  refine ⟨p, (Finset.mem_filter.mp hp).2, fun q hq hPq => ?_⟩
  have h1 := hmin (toLex q) (by rw [hS]; exact Finset.mem_image.mpr ⟨q, by simp [hPq], rfl⟩)
  rw [← hpe] at h1
  rw [before_iff] at hq
  exact absurd hq (not_lt.mpr h1)

lemma before_zero {R C : ℕ} (i : Fin R) (j : Fin C) (i0 : Fin R) (j0 : Fin C) (hi0 : i0.val = 0)
    (hj0 : j0.val = 0) (hne : ¬(i.val = 0 ∧ j.val = 0)) : before (i0, j0) (i, j) := by
  unfold before
  by_cases hi : i.val = 0
  · right; refine ⟨Fin.ext (by simp [hi0, hi]), ?_⟩
    rw [Fin.lt_def]; simp only; omega
  · left; rw [Fin.lt_def]; simp only; omega

lemma perm_fix {ρ : Equiv.Perm (Fin 3)} (h0 : ρ 0 = 0) (h1 : ρ 1 = 1) : ρ = 1 := by
  have h2 : ρ 2 = 2 := by
    have a := ρ.injective.ne (show (2 : Fin 3) ≠ 0 by decide)
    have b := ρ.injective.ne (show (2 : Fin 3) ≠ 1 by decide)
    rw [h0] at a; rw [h1] at b
    revert a b; generalize ρ 2 = v; decide +revert
  ext k; fin_cases k <;> simp [h0, h1, h2]

theorem orbit {R C : ℕ} (hR : 0 < R) (hC : 0 < C) (L : List (ℤ × ℤ))
    (h2 : ∀ x : Fin R → Fin C → Fin 3, Cond L x → ∃ p q : Fin R × Fin C, x p.1 p.2 ≠ x q.1 q.2) :
    ((univ : Finset (Fin R → Fin C → Fin 3)).filter (Cond L)).card =
      6 * ((univ : Finset (Fin R → Fin C → Fin 3)).filter (fun x => Cond L x ∧ RowMajorNew x)).card := by
  classical
  set i0 : Fin R := ⟨0, hR⟩
  set j0 : Fin C := ⟨0, hC⟩
  have hperm : (univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by
    rw [Finset.card_univ, Fintype.card_perm]; rfl
  rw [← hperm, ← Finset.card_product]
  symm
  apply Finset.card_bij (fun (a : Equiv.Perm (Fin 3) × (Fin R → Fin C → Fin 3)) _ => perm a.1 a.2)
  · rintro ⟨σ, x⟩ ha
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at ha ⊢
    exact (cond_perm L σ x).2 ha.1
  · rintro ⟨σ, x⟩ ha ⟨τ, y⟩ hb he
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at ha hb
    simp only at he
    set ρ := τ⁻¹ * σ with hρ
    have hy : ∀ i j, y i j = ρ (x i j) := by
      intro i j
      have := congrFun (congrFun he i) j
      simp only [perm] at this
      rw [hρ, Equiv.Perm.mul_apply, this]; simp
    have hx0 := rmn_zero x ha.2 i0 j0 rfl rfl
    have hy0 := rmn_zero y hb.2 i0 j0 rfl rfl
    have hr0 : ρ 0 = 0 := by have := hy i0 j0; rw [hx0, hy0] at this; exact this.symm
    obtain ⟨p, q, hpq⟩ := h2 x ha.1
    have hex : ∃ r : Fin R × Fin C, x r.1 r.2 ≠ 0 := by
      by_contra hc; push Not at hc; exact hpq (by rw [hc p, hc q])
    obtain ⟨r, hr, hrmin⟩ := exists_first (fun r : Fin R × Fin C => x r.1 r.2 ≠ 0) hex
    have hrmin' : ∀ q, before q r → x q.1 q.2 = 0 := fun q hq => by simpa using hrmin q hq
    have hx1 := first_nonzero x ha.2 r hr hrmin'
    have hy1 : y r.1 r.2 = 1 := by
      apply first_nonzero y hb.2 r
      · rw [hy, hx1]; intro h; rw [← hr0] at h; exact absurd (ρ.injective h) (by decide)
      · intro q hq; rw [hy, hrmin' q hq, hr0]
    have hr1 : ρ 1 = 1 := by have := hy r.1 r.2; rw [hx1, hy1] at this; exact this.symm
    have hρ1 := perm_fix hr0 hr1
    have hxy : x = y := by funext i j; rw [hy, hρ1]; rfl
    subst hxy
    have : σ = τ := by
      have := congrArg (fun g => τ * g) hρ1
      simp only [hρ, mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at this
      exact this
    rw [this]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    set c0 := y i0 j0
    obtain ⟨p, q, hpq⟩ := h2 y hy
    have hex : ∃ r : Fin R × Fin C, y r.1 r.2 ≠ c0 := by
      by_contra hc; push Not at hc; exact hpq (by rw [hc p, hc q])
    obtain ⟨r, hr, hrmin⟩ := exists_first (fun r : Fin R × Fin C => y r.1 r.2 ≠ c0) hex
    have hrmin' : ∀ q, before q r → y q.1 q.2 = c0 := fun q hq => by simpa using hrmin q hq
    set c1 := y r.1 r.2
    -- the third colour
    obtain ⟨c2, h20, h21⟩ : ∃ c2 : Fin 3, c2 ≠ c0 ∧ c2 ≠ c1 := by
      revert hr; generalize c0 = a; generalize c1 = b; intro hr; revert a b; decide
    have hall : ∀ v : Fin 3, v = c0 ∨ v = c1 ∨ v = c2 := by
      revert hr h20 h21; generalize c0 = a; generalize c1 = b; generalize c2 = c; revert a b c; decide
    let f : Fin 3 → Fin 3 := ![c0, c1, c2]
    have hf : Function.Injective f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [f, eq_comm]
    let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    have hσ0 : σ 0 = c0 := rfl
    have hσ1 : σ 1 = c1 := rfl
    have hσ2 : σ 2 = c2 := rfl
    refine ⟨(σ, perm σ.symm y), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter]
      refine ⟨(cond_perm L σ.symm y).2 hy, ?_⟩
      intro i j u hu
      have hval : ∀ i j, perm σ.symm y i j = 0 ↔ y i j = c0 := fun i j => by
        simp only [perm]; rw [Equiv.symm_apply_eq, hσ0]
      have hval1 : ∀ i j, perm σ.symm y i j = 1 ↔ y i j = c1 := fun i j => by
        simp only [perm]; rw [Equiv.symm_apply_eq, hσ1]
      have hval2 : ∀ i j, perm σ.symm y i j = 2 ↔ y i j = c2 := fun i j => by
        simp only [perm]; rw [Equiv.symm_apply_eq, hσ2]
      have hnz : perm σ.symm y i j ≠ 0 := by
        intro h0; rw [h0] at hu; exact absurd hu (by simp [Fin.lt_def])
      have hne00 : ¬(i.val = 0 ∧ j.val = 0) := by
        rintro ⟨hi, hj⟩
        have : i = i0 := Fin.ext hi
        have : j = j0 := Fin.ext hj
        subst_vars
        exact hnz ((hval _ _).2 rfl)
      fin_cases u
      · exact ⟨i0, j0, before_zero i j i0 j0 rfl rfl hne00, (hval _ _).2 rfl⟩
      · -- the entry is 2
        have h2' : perm σ.symm y i j = 2 := by
          have := (perm σ.symm y i j).isLt
          rw [Fin.lt_def] at hu; apply Fin.ext; simp only [Fin.val_two]
          simp only [Fin.val_one] at hu; omega
        have hyc2 := (hval2 i j).1 h2'
        refine ⟨r.1, r.2, ?_, (hval1 _ _).2 rfl⟩
        have hb : ¬before (i, j) r := fun hb => by
          have := hrmin' (i, j) hb; rw [hyc2] at this; exact h20 this
        have hneq : (i, j) ≠ r := fun e => by
          have : c1 = y i j := by rw [show c1 = y r.1 r.2 from rfl, ← e]
          rw [hyc2] at this; exact h21 this.symm
        show before r (i, j)
        rw [before_iff] at hb ⊢
        rcases lt_trichotomy (toLex r) (toLex (i, j)) with h | h | h
        · exact h
        · exact absurd (toLex.injective h).symm hneq
        · exact absurd h hb
      · exact absurd hu (by have := (perm σ.symm y i j).isLt; rw [Fin.lt_def]; simp; omega)
    · funext i j; simp [perm]

/-! ### Transfer over columns -/

def A {R n : ℕ} (x : Fin R → Fin n → Fin 3) (i j : ℤ) : ℕ :=
  if h : 0 ≤ i ∧ i < R ∧ 0 ≤ j ∧ j < n then (x ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩).val else 3

lemma A_lt {R n : ℕ} (x : Fin R → Fin n → Fin 3) (i j : ℤ) (h : 0 ≤ i ∧ i < R ∧ 0 ≤ j ∧ j < n) :
    A x i j < 3 := by
  unfold A; rw [dif_pos h]; exact (x _ _).isLt

lemma A_out {R n : ℕ} (x : Fin R → Fin n → Fin 3) (i j : ℤ) (h : ¬(0 ≤ i ∧ i < R ∧ 0 ≤ j ∧ j < n)) :
    A x i j = 3 := by
  unfold A; rw [dif_neg h]

lemma A_fin {R n : ℕ} (x : Fin R → Fin n → Fin 3) (i : Fin R) (j : Fin n) :
    A x (i.val : ℤ) (j.val : ℤ) = (x i j).val := by
  unfold A; rw [dif_pos ⟨by omega, by omega, by omega, by omega⟩]; simp

def Pd {R n : ℕ} (d : ℤ × ℤ) (x : Fin R → Fin n → Fin 3) : Prop :=
  ∀ i j : ℤ, 0 ≤ i → i < R → 0 ≤ j → j < n → A x (i + d.1) (j + d.2) ≠ A x i j

lemma cond_iff_Pd {R n : ℕ} (L : List (ℤ × ℤ)) (x : Fin R → Fin n → Fin 3) :
    Cond L x ↔ ∀ d ∈ L, Pd d x := by
  unfold Cond Pd
  constructor
  · intro h d hd i j hi0 hi1 hj0 hj1
    by_cases hin : 0 ≤ i + d.1 ∧ i + d.1 < R ∧ 0 ≤ j + d.2 ∧ j + d.2 < n
    · have e1 := A_fin x ⟨(i + d.1).toNat, by omega⟩ ⟨(j + d.2).toNat, by omega⟩
      have e2 := A_fin x ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩
      simp only [Int.toNat_of_nonneg hin.1, Int.toNat_of_nonneg hin.2.2.1, Int.toNat_of_nonneg hi0,
        Int.toNat_of_nonneg hj0] at e1 e2
      rw [e1, e2]
      intro he
      have hm : (((⟨(i + d.1).toNat, by omega⟩ : Fin R) : ℕ) - ((⟨i.toNat, by omega⟩ : Fin R) : ℕ) : ℤ) =
          d.1 := by simp only; omega
      have hm2 : (((⟨(j + d.2).toNat, by omega⟩ : Fin n) : ℕ) - ((⟨j.toNat, by omega⟩ : Fin n) : ℕ) : ℤ) =
          d.2 := by simp only; omega
      have hdm := h ⟨i.toNat, by omega⟩ ⟨(i + d.1).toNat, by omega⟩ ⟨j.toNat, by omega⟩
        ⟨(j + d.2).toNat, by omega⟩
      rw [hm, hm2] at hdm
      exact hdm hd (Fin.ext he)
    · rw [A_out x _ _ hin]
      have := A_lt x i j ⟨hi0, hi1, hj0, hj1⟩
      omega
  · intro h i i' j j' hm he
    have := h _ hm i j (by omega) (by omega) (by omega) (by omega)
    simp only [add_sub_cancel] at this
    rw [A_fin, A_fin, he] at this
    exact this rfl

lemma Pd_neg {R n : ℕ} (d : ℤ × ℤ) (x : Fin R → Fin n → Fin 3) : Pd d x ↔ Pd (-d.1, -d.2) x := by
  have key : ∀ d : ℤ × ℤ, Pd d x → Pd (-d.1, -d.2) x := by
    intro d h i j hi0 hi1 hj0 hj1
    simp only
    by_cases hin : 0 ≤ i + -d.1 ∧ i + -d.1 < R ∧ 0 ≤ j + -d.2 ∧ j + -d.2 < n
    · have := h (i + -d.1) (j + -d.2) hin.1 hin.2.1 hin.2.2.1 hin.2.2.2
      simp only [neg_add_cancel_right] at this
      exact fun e => this e.symm
    · rw [A_out x _ _ hin]
      have := A_lt x i j ⟨hi0, hi1, hj0, hj1⟩
      omega
  exact ⟨key d, fun h => by simpa using key _ h⟩

def getZ (l : List ℕ) (k : ℤ) : ℕ := if 0 ≤ k then l.getD k.toNat 3 else 3

def col {R n : ℕ} (x : Fin R → Fin n → Fin 3) (j : ℕ) : List ℕ :=
  (List.range R).map (fun i : ℕ => A x (i : ℤ) (j : ℤ))

lemma getZ_col {R n : ℕ} (x : Fin R → Fin n → Fin 3) (j : ℕ) (k : ℤ) : getZ (col x j) k = A x k j := by
  unfold getZ col
  split_ifs with hk
  · by_cases hkR : k.toNat < R
    · rw [List.getD_eq_getElem _ _ (by simpa using hkR)]
      simp [Int.toNat_of_nonneg hk]
    · rw [List.getD_eq_default _ _ (by simp; omega), A_out x _ _ (by omega)]
  · rw [A_out x _ _ (by omega)]

lemma getD_col {R n : ℕ} (x : Fin R → Fin n → Fin 3) (j i : ℕ) : (col x j).getD i 3 = A x i j := by
  have := getZ_col x j (i : ℤ)
  unfold getZ at this
  simpa using this

def okW (R : ℕ) (F : List (ℤ × ℤ)) (c p : List ℕ) : Prop :=
  ∀ i < R, ∀ d ∈ F, getZ (if d.2 = 0 then c else p) ((i : ℤ) + d.1) ≠ c.getD i 3

instance (R : ℕ) (F : List (ℤ × ℤ)) (c p : List ℕ) : Decidable (okW R F c p) := by
  unfold okW; infer_instance

lemma Pd_iff_okW {R n : ℕ} (F : List (ℤ × ℤ)) (hF : ∀ d ∈ F, d.2 = 0 ∨ d.2 = 1)
    (x : Fin R → Fin n → Fin 3) :
    (∀ d ∈ F, Pd d x) ↔ ∀ j < n, okW R F (col x j) (col x (j + 1)) := by
  have hc : ∀ d ∈ F, ∀ (j : ℕ) (k : ℤ), getZ (if d.2 = 0 then col x j else col x (j + 1)) k =
      A x k ((j : ℤ) + d.2) := by
    intro d hd j k
    rcases hF d hd with h | h
    · rw [if_pos h, getZ_col, h, add_zero]
    · rw [if_neg (by omega), getZ_col, h]; push_cast; ring_nf
  constructor
  · intro h j hj i hi d hd
    rw [hc d hd, getD_col]
    exact h d hd i j (by omega) (by omega) (by omega) (by omega)
  · intro h d hd i j hi0 hi1 hj0 hj1
    have := h j.toNat (by omega) i.toNat (by omega) d hd
    rw [hc d hd, getD_col] at this
    simpa [Int.toNat_of_nonneg hi0, Int.toNat_of_nonneg hj0] using this

def absent (R : ℕ) : List ℕ := List.replicate R 3

lemma col_ge {R n : ℕ} (x : Fin R → Fin n → Fin 3) (j : ℕ) (hj : n ≤ j) : col x j = absent R := by
  unfold col absent
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact A_out x _ _ (by omega)

def consA {R n : ℕ} (c : Fin R → Fin 3) (w : Fin R → Fin n → Fin 3) : Fin R → Fin (n + 1) → Fin 3 :=
  fun i => Fin.cons (c i) (w i)

def colOf {R : ℕ} (c : Fin R → Fin 3) : List ℕ :=
  (List.range R).map (fun i => if h : i < R then (c ⟨i, h⟩).val else 3)

lemma A_cons_succ {R n : ℕ} (c : Fin R → Fin 3) (w : Fin R → Fin n → Fin 3) (i : ℤ) (j : ℕ) :
    A (consA c w) i ((j : ℤ) + 1) = A w i j := by
  unfold A consA
  by_cases h : 0 ≤ i ∧ i < R ∧ 0 ≤ (j : ℤ) ∧ (j : ℤ) < n
  · rw [dif_pos ⟨h.1, h.2.1, by omega, by push_cast; omega⟩, dif_pos h]
    have e : (⟨((j : ℤ) + 1).toNat, by omega⟩ : Fin (n + 1)) = Fin.succ ⟨j, by omega⟩ := by
      apply Fin.ext; simp
    rw [e]
    exact congrArg Fin.val (Fin.cons_succ (α := fun _ => Fin 3) _ _ _)
  · rw [dif_neg (by push_cast; omega), dif_neg h]

lemma col_cons_succ {R n : ℕ} (c : Fin R → Fin 3) (w : Fin R → Fin n → Fin 3) (j : ℕ) :
    col (consA c w) (j + 1) = col w j := by
  unfold col; push_cast; simp only [A_cons_succ]

lemma col_cons_zero {R n : ℕ} (c : Fin R → Fin 3) (w : Fin R → Fin n → Fin 3) :
    col (consA c w) 0 = colOf c := by
  unfold col colOf A consA
  refine List.map_congr_left (fun i hi => ?_)
  rw [List.mem_range] at hi
  rw [dif_pos ⟨by omega, by omega, le_rfl, by omega⟩, dif_pos hi]
  simp

def T {R n : ℕ} (F : List (ℤ × ℤ)) (w : Fin R → Fin n → Fin 3) : Prop :=
  ∀ j < n, okW R F (col w j) (col w (j + 1))

instance {R n : ℕ} (F : List (ℤ × ℤ)) (w : Fin R → Fin n → Fin 3) : Decidable (T F w) := by
  unfold T; infer_instance

lemma T_cons {R n : ℕ} (F : List (ℤ × ℤ)) (c : Fin R → Fin 3) (w : Fin R → Fin n → Fin 3) :
    T F (consA c w) ↔ okW R F (colOf c) (col w 0) ∧ T F w := by
  unfold T
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have := h 0 (by omega)
      rwa [col_cons_zero, show (0 + 1 : ℕ) = 0 + 1 from rfl, col_cons_succ] at this
    · have := h (j + 1) (by omega)
      rwa [col_cons_succ, col_cons_succ] at this
  · rintro ⟨h0, h1⟩ j hj
    rcases j with _ | k
    · rw [col_cons_zero, col_cons_succ]; exact h0
    · rw [col_cons_succ, col_cons_succ]; exact h1 k (by omega)

def consEquiv (R n : ℕ) : (Fin R → Fin 3) × (Fin R → Fin n → Fin 3) ≃ (Fin R → Fin (n + 1) → Fin 3) where
  toFun cw := consA cw.1 cw.2
  invFun x := (fun i => x i 0, fun i => Fin.tail (x i))
  left_inv cw := by
    obtain ⟨c, w⟩ := cw
    simp only [consA, Fin.cons_zero, Fin.tail_cons]
  right_inv x := by
    funext i
    simp only [consA, Fin.cons_self_tail]

lemma sum_cons {R n : ℕ} (G : (Fin R → Fin (n + 1) → Fin 3) → ℕ) :
    ∑ x, G x = ∑ c : Fin R → Fin 3, ∑ w : Fin R → Fin n → Fin 3, G (consA c w) := by
  rw [← (consEquiv R n).sum_comp, Fintype.sum_prod_type]; rfl

def cols3 : ℕ → List (List ℕ)
  | 0 => [[]]
  | R + 1 => (cols3 R).flatMap (fun l => [0 :: l, 1 :: l, 2 :: l])

def allCols (R : ℕ) : List (List ℕ) := cols3 R ++ [absent R]

lemma mem_cols3 : ∀ (R : ℕ) (l : List ℕ), l.length = R → (∀ a ∈ l, a < 3) → l ∈ cols3 R := by
  intro R
  induction R with
  | zero => intro l hl _; simp [cols3, List.length_eq_zero_iff.mp hl]
  | succ R ih =>
    intro l hl ha
    obtain ⟨b, t, rfl⟩ : ∃ b t, l = b :: t := by
      cases l with
      | nil => simp at hl
      | cons b t => exact ⟨b, t, rfl⟩
    simp only [cols3, List.mem_flatMap, List.mem_cons]
    refine ⟨t, ih t (by simpa using hl) (fun a h => ha a (by simp [h])), ?_⟩
    have := ha b (by simp)
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;> simp

lemma cols3_spec : ∀ (R : ℕ) (l : List ℕ), l ∈ cols3 R → l.length = R ∧ ∀ a ∈ l, a < 3 := by
  intro R
  induction R with
  | zero => intro l hl; simp [cols3] at hl; subst hl; simp
  | succ R ih =>
    intro l hl
    simp only [cols3, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hl
    obtain ⟨t, ht, rfl | rfl | rfl⟩ := hl <;>
    · obtain ⟨h1, h2⟩ := ih t ht
      refine ⟨by simp [h1], fun a ha => ?_⟩
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · norm_num
      · exact h2 a ha

lemma col_mem {R n : ℕ} (x : Fin R → Fin n → Fin 3) (j : ℕ) : col x j ∈ allCols R := by
  unfold allCols
  by_cases hj : j < n
  · apply List.mem_append_left
    apply mem_cols3 _ _ (by simp [col])
    intro a ha
    simp only [col, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact A_lt x _ _ ⟨by omega, by omega, by omega, by omega⟩
  · rw [col_ge x j (by omega)]; simp

lemma col_ne_absent {R n : ℕ} (hR : 0 < R) (x : Fin R → Fin n → Fin 3) (j : ℕ) (hj : j < n) :
    col x j ≠ absent R := by
  intro h
  have := congrArg (fun l => l.getD 0 3) h
  simp only [getD_col] at this
  have h2 := A_lt x 0 j ⟨le_rfl, by omega, by omega, by omega⟩
  unfold absent at this
  rw [List.getD_eq_getElem _ _ (by simp; omega)] at this
  simp at this; omega

lemma colOf_unique {R : ℕ} (c : List ℕ) (hc : c ∈ cols3 R) :
    ((Finset.univ : Finset (Fin R → Fin 3)).filter (fun c' => colOf c' = c)).card = 1 := by
  obtain ⟨hl, h2⟩ := cols3_spec R c hc
  rw [Finset.card_eq_one]
  refine ⟨fun i => ⟨c.getD i.val 0, ?_⟩, ?_⟩
  · have hi : i.val < c.length := by omega
    rw [List.getD_eq_getElem _ _ hi]; exact h2 _ (List.getElem_mem hi)
  · ext c'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro rfl
      funext i
      apply Fin.ext
      simp only [colOf]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    · rintro rfl
      unfold colOf
      apply List.ext_getElem (by simp [hl])
      intro i h1 h2'
      simp only [List.getElem_map, List.getElem_range]
      rw [dif_pos (by simpa using h1)]
      exact List.getD_eq_getElem _ _ (by simpa [hl] using h1)

def S (R : ℕ) (F : List (ℤ × ℤ)) (n : ℕ) (p : List ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin R → Fin n → Fin 3)).filter (fun w => T F w ∧ col w 0 = p)).card

lemma S_sum (R : ℕ) (F : List (ℤ × ℤ)) (n : ℕ) (p : List ℕ) : S R F n p =
    ∑ w : Fin R → Fin n → Fin 3, if T F w ∧ col w 0 = p then 1 else 0 := by
  unfold S; rw [Finset.card_filter]

lemma collapse {R : ℕ} (c : List ℕ) (hc : c ∈ cols3 R) (G : ℕ) :
    ∑ c' : Fin R → Fin 3, (if colOf c' = c then G else 0) = G := by
  rw [← Finset.sum_filter, Finset.sum_const, colOf_unique c hc, one_smul]

lemma S_zero (R : ℕ) (F : List (ℤ × ℤ)) (p : List ℕ) : S R F 0 p = if p = absent R then 1 else 0 := by
  rw [S_sum, Fintype.sum_unique]
  have hT : ∀ w : Fin R → Fin 0 → Fin 3, T F w := fun w j hj => by omega
  rw [col_ge _ 0 le_rfl]
  by_cases h : p = absent R
  · subst h; rw [if_pos ⟨hT _, rfl⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.2.symm), if_neg h]

lemma S_succ (R : ℕ) (F : List (ℤ × ℤ)) (n : ℕ) (c : List ℕ) (hc : c ∈ cols3 R) :
    S R F (n + 1) c = ∑ p ∈ (allCols R).toFinset, if okW R F c p then S R F n p else 0 := by
  rw [S_sum, sum_cons]
  have h1 : ∀ (c' : Fin R → Fin 3) (w : Fin R → Fin n → Fin 3),
      (if T F (consA c' w) ∧ col (consA c' w) 0 = c then 1 else 0) =
      if colOf c' = c then (if okW R F c (col w 0) ∧ T F w then 1 else 0) else 0 := by
    intro c' w
    simp only [T_cons, col_cons_zero]
    by_cases hc' : colOf c' = c
    · subst hc'; simp
    · simp [hc']
  simp only [h1]
  have h2 : ∀ c' : Fin R → Fin 3, (∑ w : Fin R → Fin n → Fin 3, if colOf c' = c then
      (if okW R F c (col w 0) ∧ T F w then 1 else 0) else 0) =
      if colOf c' = c then ∑ w : Fin R → Fin n → Fin 3,
        (if okW R F c (col w 0) ∧ T F w then 1 else 0) else 0 := by
    intro c'; split_ifs <;> simp
  simp only [h2, collapse c hc]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := (allCols R).toFinset)
    (g := fun w => col w 0) (fun w _ => by simpa using col_mem w 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_filter, S_sum]
  split_ifs with hp
  · refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : col w 0 = p
    · simp [h, hp]
    · simp [h]
  · apply Finset.sum_eq_zero
    intro w _
    by_cases h : col w 0 = p
    · simp [h, hp]
    · simp [h]

lemma S_absent (R : ℕ) (hR : 0 < R) (F : List (ℤ × ℤ)) (n : ℕ) : S R F (n + 1) (absent R) = 0 := by
  rw [S_sum]
  apply Finset.sum_eq_zero
  intro w _
  rw [if_neg]
  rintro ⟨_, h⟩
  exact col_ne_absent hR w 0 (by omega) h

def Sv (R : ℕ) (F : List (ℤ × ℤ)) : ℕ → List ℕ → ℕ
  | 0, p => if p = absent R then 1 else 0
  | n + 1, p => if p = absent R then 0 else
      ((allCols R).map (fun q => if okW R F p q then Sv R F n q else 0)).sum

lemma S_eq_Sv (R : ℕ) (hR : 0 < R) (F : List (ℤ × ℤ)) (hnd : (allCols R).Nodup) :
    ∀ n, ∀ p ∈ allCols R, S R F n p = Sv R F n p := by
  intro n
  induction n with
  | zero => intro p _; rw [S_zero]; rfl
  | succ n ih =>
    intro p hp
    by_cases hpa : p = absent R
    · subst hpa; rw [S_absent R hR]; simp [Sv]
    · have hpc : p ∈ cols3 R := by
        unfold allCols at hp
        rcases List.mem_append.mp hp with h | h
        · exact h
        · simp at h; exact absurd h hpa
      rw [S_succ R F n p hpc]
      simp only [Sv, hpa, if_false]
      rw [← List.sum_toFinset _ hnd]
      refine Finset.sum_congr rfl fun q hq => ?_
      split_ifs
      · exact ih q (by simpa using hq)
      · rfl

lemma total_eq {R n : ℕ} (F : List (ℤ × ℤ)) :
    ((Finset.univ : Finset (Fin R → Fin n → Fin 3)).filter (T F)).card =
      ∑ p ∈ (allCols R).toFinset, S R F n p := by
  rw [Finset.card_filter, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := (allCols R).toFinset)
    (g := fun w => col w 0) (fun w _ => by simpa using col_mem w 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_filter, S_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : col w 0 = p
  · simp [h]
  · simp [h]

def F : List (ℤ × ℤ) := [(2, 1), (-2, 1), (-1, 0)]

lemma hF : ∀ d ∈ F, d.2 = 0 ∨ d.2 = 1 := by decide

lemma cond_iff_T {n : ℕ} (x : Fin 3 → Fin n → Fin 3) : Cond offs x ↔ T F x := by
  rw [cond_iff_Pd]
  unfold T
  rw [← Pd_iff_okW F hF]
  simp only [offs, F, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  rw [Pd_neg (-2, -1)]
  norm_num

lemma nd : (allCols 3).Nodup := by decide +kernel

def Tv (n : ℕ) : ℕ := ((allCols 3).map (fun p => Sv 3 F n p)).sum

lemma card_cond (n : ℕ) : ((Finset.univ : Finset (Fin 3 → Fin n → Fin 3)).filter (Cond offs)).card = Tv n := by
  have : (Finset.univ : Finset (Fin 3 → Fin n → Fin 3)).filter (Cond offs) =
      (Finset.univ : Finset (Fin 3 → Fin n → Fin 3)).filter (T F) :=
    Finset.filter_congr (fun x _ => cond_iff_T x)
  rw [this, total_eq, Tv, ← List.sum_toFinset _ nd]
  exact Finset.sum_congr rfl fun p hp => S_eq_Sv 3 (by norm_num) F nd n p (by simpa using hp)

lemma six_a (n : ℕ) (hn : 1 ≤ n) : 6 * a n = Tv n := by
  rw [← card_cond, orbit (by norm_num) (by omega) offs]
  · rfl
  · intro x hx
    refine ⟨(0, ⟨0, by omega⟩), (1, ⟨0, by omega⟩), ?_⟩
    exact hx 1 0 ⟨0, by omega⟩ ⟨0, by omega⟩ (by simp [offs])

def Wv (m : ℕ) (p : List ℕ) : ℤ := (Sv 3 F (m + 2) p : ℤ) - 7 * Sv 3 F (m + 1) p + 8 * Sv 3 F m p

lemma W1 : ∀ p ∈ allCols 3, Wv 1 p = 0 := by decide +kernel

lemma Sv_succ (n : ℕ) (p : List ℕ) : (Sv 3 F (n + 1) p : ℤ) =
    if p = absent 3 then 0 else ∑ q ∈ (allCols 3).toFinset, if okW 3 F p q then (Sv 3 F n q : ℤ) else 0 := by
  simp only [Sv]
  split_ifs with h
  · simp
  · rw [← List.sum_toFinset _ nd]; push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp

lemma W_zero : ∀ m, 1 ≤ m → ∀ p ∈ allCols 3, Wv m p = 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact W1
  | succ m hm ih =>
    intro p hp
    unfold Wv
    rw [show m + 1 + 2 = (m + 2) + 1 by ring, show m + 1 + 1 = (m + 1) + 1 by ring, Sv_succ, Sv_succ, Sv_succ]
    split_ifs with ha
    · ring
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro q hq
      have := ih q (by simpa using hq)
      unfold Wv at this
      split_ifs <;> linarith

lemma Tv_rec (m : ℕ) (hm : 1 ≤ m) : (Tv (m + 2) : ℤ) = 7 * Tv (m + 1) - 8 * Tv m := by
  simp only [Tv, ← List.sum_toFinset _ nd]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have := W_zero m hm p (by simpa using hp)
  unfold Wv at this
  linarith

lemma vals : Tv 1 = 12 ∧ Tv 2 = 66 := by decide +kernel

end OMA.Helpers_a275229

open OMA.S_oeis_a275229 OMA.Helpers_a275229 in
theorem OMA.solution : type_of% @OMA.S_oeis_a275229.main := by
  obtain ⟨t1, t2⟩ := vals
  have a1 : a 1 = 2 := by have := six_a 1 le_rfl; omega
  have a2 : a 2 = 11 := by have := six_a 2 (by norm_num); omega
  have hrec : ∀ m : ℕ, 1 ≤ m → (a (m + 2) : ℤ) = 7 * a (m + 1) - 8 * a m := by
    intro m hm
    have h := Tv_rec m hm
    have e2 := six_a (m + 2) (by omega)
    have e1 := six_a (m + 1) (by omega)
    have e0 := six_a m hm
    have : (6 : ℤ) * a (m + 2) = 6 * (7 * a (m + 1) - 8 * a m) := by
      rw [show (6 : ℤ) * a (m + 2) = ((6 * a (m + 2) : ℕ) : ℤ) by push_cast; ring, e2, h,
        ← e1, ← e0]; push_cast; ring
    linarith
  constructor
  · set G : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hG
    have hL : G * (1 - 7 * PowerSeries.X + 8 * PowerSeries.X ^ 2) =
        G - 7 * (G * PowerSeries.X ^ 1) + 8 * (G * PowerSeries.X ^ 2) := by ring
    have hR : (PowerSeries.X * (2 - 3 * PowerSeries.X) : PowerSeries ℚ) =
        2 * PowerSeries.X ^ 1 - 3 * PowerSeries.X ^ 2 := by ring
    rw [hL, hR]
    ext d
    simp only [map_add, map_sub, ← map_ofNat PowerSeries.C, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mul_X_pow', hG, PowerSeries.coeff_mk]
    rcases (show d ≤ 2 ∨ 3 ≤ d by omega) with hd | hd
    · interval_cases d <;> simp [a1, a2] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
      have h := hrec m (by omega)
      have h' : (a (m + 2) : ℚ) = 7 * a (m + 1) - 8 * a m := by exact_mod_cast h
      have c1 : 1 ≤ m + 2 := by omega
      have c2 : 2 ≤ m + 2 := by omega
      have n0 : m + 2 ≠ 0 := by omega
      have n1 : m + 2 - 1 ≠ 0 := by omega
      have n2 : m + 2 - 2 ≠ 0 := by omega
      have m1 : m + 2 ≠ 1 := by omega
      have m2 : m + 2 ≠ 2 := by omega
      have hm0 : m ≠ 0 := by omega
      have hm1 : m + 1 ≠ 0 := by omega
      simp only [c1, c2, n0, hm0, hm1, ↓reduceIte, PowerSeries.coeff_C,
        ite_self,
        show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
      linear_combination h'
  · intro n hn
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt 17 := ⟨_, rfl⟩
    rw [← hs]
    have hs2 : s * s = 17 := by rw [hs]; exact Real.mul_self_sqrt (by norm_num)
    have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (by norm_num)
    have hcf : ∀ k : ℕ, (2 : ℝ) ^ (-4 - (k : ℤ)) * ((7 - s) ^ k * (-11 + 3 * s) + (7 + s) ^ k * (11 + 3 * s)) / s =
        (((7 - s) / 2) ^ k * (-11 + 3 * s) + ((7 + s) / 2) ^ k * (11 + 3 * s)) / (16 * s) := by
      intro k
      have h2 : (2 : ℝ) ^ (-4 - (k : ℤ)) = ((2 : ℝ) ^ 4 * 2 ^ k)⁻¹ := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_neg]; congr 1; push_cast; ring
      rw [h2, div_pow, div_pow]
      field_simp
      ring
    rw [hcf]
    have e1 : ((7 - s) / 2) * ((7 - s) / 2) = 7 * ((7 - s) / 2) - 8 := by
      linear_combination (1 / 4 : ℝ) * hs2
    have e2 : ((7 + s) / 2) * ((7 + s) / 2) = 7 * ((7 + s) / 2) - 8 := by
      linear_combination (1 / 4 : ℝ) * hs2
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
      · rw [a1, eq_div_iff (by positivity)]; push_cast; ring
      · rw [a2, eq_div_iff (by positivity)]; push_cast
        linear_combination (-(3 / 2) * s) * hs2
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        have h := hrec m (by omega)
        have h' : (a (m + 2) : ℝ) = 7 * a (m + 1) - 8 * a m := by exact_mod_cast h
        rw [h', ih (m + 1) (by omega) (by omega), ih m (by omega) (by omega)]
        have p1 : ((7 - s) / 2) ^ (m + 2) = ((7 - s) / 2) ^ m * (7 * ((7 - s) / 2) - 8) := by
          rw [pow_add, sq, e1]
        have p2 : ((7 + s) / 2) ^ (m + 2) = ((7 + s) / 2) ^ m * (7 * ((7 + s) / 2) - 8) := by
          rw [pow_add, sq, e2]
        rw [p1, p2, pow_succ ((7 - s) / 2) m, pow_succ ((7 + s) / 2) m]
        field_simp
        ring
