import OMAStatements.S_oeis_a233083
import Mathlib

namespace OMA.S_oeis_a233083
open PowerSeries

def V {S : Type} [Fintype S] (R : S → S → Prop) [DecidableRel R] : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V R n t else 0

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_w (m : ℕ) (c : ℕ → ℤ) (w : S → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, w s * (V R (n + j) s : ℤ)) = 0 := by
  have h : ∑ s, w s * ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 :=
    Finset.sum_eq_zero (fun s _ => by rw [rec_gen R m c h0 n s, mul_zero])
  simp only [Finset.mul_sum] at h ⊢
  rw [Finset.sum_comm] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  ring
end generic

abbrev Col := Fin 2 → Fin 4
abbrev St := Fin 3 × Col × Bool

def clash (c d : Col) : Prop := (∀ i : Fin 2, (c i).val + (d i).val ≠ 3) ∧ (d 0).val + (c 1).val ≠ 3
instance (c d : Col) : Decidable (clash c d) := by unfold clash; infer_instance

theorem noClash_cons {m : ℕ} (c : Col) (y : Fin (m + 1) → Col) :
    noClash (m + 2) (Fin.cons c y : Fin (m + 2) → Col) ↔ clash c (y 0) ∧ noClash (m + 1) y := by
  unfold noClash clash
  constructor
  · intro h
    refine ⟨by simpa using h 0 1 (by simp), ?_⟩
    intro j k hjk
    simpa using h j.succ k.succ (by simpa using hjk)
  · rintro ⟨h1, h2⟩ j k hjk
    induction j using Fin.cases with
    | zero =>
      induction k using Fin.cases with
      | zero => simp at hjk
      | succ k' =>
        have : k' = 0 := Fin.ext (by simpa using hjk)
        subst this
        simpa using h1
    | succ j' =>
      induction k using Fin.cases with
      | zero => simp at hjk
      | succ k' => simpa using h2 j' k' (by simpa using hjk)

def SemTop {n : ℕ} (f : Bool) (y : Fin n → Col) : Prop :=
  ∀ j, y j 0 = 2 → f = true ∨ ∃ j' : Fin n, j' < j ∧ y j' 0 = 1
def SemBot {n : ℕ} (f : Bool) (y : Fin n → Col) : Prop :=
  ∀ j, y j 1 = 2 → f = true ∨ ∃ j' : Fin n, j' < j ∧ y j' 1 = 1
def Top03 {n : ℕ} (y : Fin n → Col) : Prop := ∀ j, y j 0 = 0 ∨ y j 0 = 3
instance {n : ℕ} (f : Bool) (y : Fin n → Col) : Decidable (SemTop f y) := by unfold SemTop; infer_instance
instance {n : ℕ} (f : Bool) (y : Fin n → Col) : Decidable (SemBot f y) := by unfold SemBot; infer_instance
instance {n : ℕ} (y : Fin n → Col) : Decidable (Top03 y) := by unfold Top03; infer_instance

theorem SemTop_cons {n : ℕ} (f : Bool) (c : Col) (z : Fin n → Col) :
    SemTop f (Fin.cons c z : Fin (n + 1) → Col) ↔
      (c 0 = 2 → f = true) ∧ SemTop (f || decide (c 0 = 1)) z := by
  unfold SemTop
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.exists_fin_succ, Fin.succ_lt_succ_iff,
    Fin.succ_pos, Fin.not_lt_zero, true_and, false_and, exists_false, or_false,
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun j hj => by
      rcases h1 j hj with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h⟩
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun j hj => ?_⟩
    rcases h1 j hj with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem SemBot_cons {n : ℕ} (f : Bool) (c : Col) (z : Fin n → Col) :
    SemBot f (Fin.cons c z : Fin (n + 1) → Col) ↔
      (c 1 = 2 → f = true) ∧ SemBot (f || decide (c 1 = 1)) z := by
  unfold SemBot
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.exists_fin_succ, Fin.succ_lt_succ_iff,
    Fin.succ_pos, Fin.not_lt_zero, true_and, false_and, exists_false, or_false,
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0, fun j hj => by
      rcases h1 j hj with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h⟩
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun j hj => ?_⟩
    rcases h1 j hj with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem Top03_cons {n : ℕ} (c : Col) (z : Fin n → Col) :
    Top03 (Fin.cons c z : Fin (n + 1) → Col) ↔ (c 0 = 0 ∨ c 0 = 3) ∧ Top03 z := by
  unfold Top03
  rw [Fin.forall_fin_succ]
  simp

def nxt (k : Fin 3) (f : Bool) (t : Col) : Bool :=
  if k = 0 then (f || decide (t 0 = 1)) else if k = 1 then false else (f || decide (t 1 = 1))
def okStep (k : Fin 3) (f : Bool) (t : Col) : Prop :=
  (k = 0 → (t 0 = 2 → f = true)) ∧ (k = 1 → (t 0 = 0 ∨ t 0 = 3)) ∧
  (k = 2 → ((t 0 = 0 ∨ t 0 = 3) ∧ (t 1 = 2 → f = true)))
def SemK (k : Fin 3) (f : Bool) {n : ℕ} (y : Fin n → Col) : Prop :=
  (k = 0 → SemTop f y) ∧ (k = 1 → Top03 y) ∧ (k = 2 → Top03 y ∧ SemBot f y)
instance (k : Fin 3) (f : Bool) (t : Col) : Decidable (okStep k f t) := by unfold okStep; infer_instance
instance (k : Fin 3) (f : Bool) {n : ℕ} (y : Fin n → Col) : Decidable (SemK k f y) := by
  unfold SemK; infer_instance

def Rel (s t : St) : Prop :=
  s.1 = t.1 ∧ clash s.2.1 t.2.1 ∧ okStep s.1 s.2.2 t.2.1 ∧ t.2.2 = nxt s.1 s.2.2 t.2.1
instance : DecidableRel Rel := fun s t => by unfold Rel; infer_instance

theorem SemK_cons (k : Fin 3) (f : Bool) {n : ℕ} (c : Col) (z : Fin n → Col) :
    SemK k f (Fin.cons c z : Fin (n + 1) → Col) ↔ okStep k f c ∧ SemK k (nxt k f c) z := by
  fin_cases k <;> simp [SemK, okStep, nxt, SemTop_cons, SemBot_cons, Top03_cons] <;> tauto

def T (n : ℕ) (s : St) : ℕ :=
  (Finset.univ.filter (fun x : Fin (n + 1) → Col =>
    x 0 = s.2.1 ∧ noClash (n + 1) x ∧ SemK s.1 s.2.2 (Fin.tail x))).card

theorem T_zero (s : St) : T 0 s = 1 := by
  unfold T
  rw [Finset.card_eq_one]
  refine ⟨fun _ => s.2.1, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h, _⟩
    funext i
    have : i = 0 := Fin.ext (by have := i.2; omega)
    subst this; exact h
  · rintro rfl
    refine ⟨rfl, ?_, ?_⟩
    · intro j k hjk
      have := j.2; have := k.2; omega
    · unfold SemK SemTop SemBot Top03
      refine ⟨fun _ j => j.elim0, fun _ j => j.elim0, fun _ => ⟨fun j => j.elim0, fun j => j.elim0⟩⟩

theorem T_succ (n : ℕ) (s : St) : T (n + 1) s =
    ∑ r : Col, if clash s.2.1 r ∧ okStep s.1 s.2.2 r then T n (s.1, r, nxt s.1 s.2.2 r) else 0 := by
  obtain ⟨k, c, f⟩ := s
  unfold T
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (n + 2) → Col => x 1) (t := Finset.univ)
    (by simp)]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.filter_filter]
  by_cases h : clash c r ∧ okStep k f r
  · rw [if_pos h]
    refine Finset.card_bij' (fun x _ => Fin.tail x) (fun x _ => Fin.cons c x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨⟨h0, h1, h2⟩, h3⟩ := hx
      have e : x = Fin.cons c (Fin.tail x) := by rw [← h0]; exact (Fin.cons_self_tail x).symm
      rw [e, noClash_cons] at h1
      rw [e, Fin.tail_cons] at h2
      have e2 : Fin.tail x 0 = r := by rw [← h3]; rfl
      rw [e2] at h1
      have h2' := h2
      have e3 : Fin.tail x = Fin.cons r (Fin.tail (Fin.tail x)) := by
        rw [← e2]; exact (Fin.cons_self_tail _).symm
      rw [e3, SemK_cons] at h2'
      refine ⟨e2, h1.2, ?_⟩
      simpa using h2'.2
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨h0, h1, h2⟩ := hx
      have e : x = Fin.cons r (Fin.tail x) := by rw [← h0]; exact (Fin.cons_self_tail x).symm
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
      · rw [noClash_cons]; exact ⟨by simpa [h0] using h.1, h1⟩
      · rw [Fin.tail_cons, e, SemK_cons]; exact ⟨h.2, by simpa using h2⟩
      · simpa using h0
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨⟨h0, _⟩, _⟩ := hx
      rw [← h0]; exact Fin.cons_self_tail x
    · intro x _
      exact Fin.tail_cons _ _
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x _ ⟨⟨h0, h1, h2⟩, h3⟩
    apply h
    have h0 : x 0 = c := h0
    have e : x = Fin.cons c (Fin.tail x) := by rw [← h0]; exact (Fin.cons_self_tail x).symm
    have e2 : Fin.tail x 0 = r := by rw [← h3]; rfl
    have e3 : Fin.tail x = Fin.cons r (Fin.tail (Fin.tail x)) := by
      rw [← e2]; exact (Fin.cons_self_tail _).symm
    rw [e, noClash_cons, e2] at h1
    rw [e, Fin.tail_cons, e3, SemK_cons] at h2
    exact ⟨h1.1, h2.1⟩

theorem T_eq (n : ℕ) (s : St) : T n s = V Rel n s := by
  induction n generalizing s with
  | zero => rw [T_zero]; rfl
  | succ n ih =>
    rw [T_succ]
    obtain ⟨k, c, f⟩ := s
    simp only [V]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
    · rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_eq_single (nxt k f r)]
      · by_cases h : clash c r ∧ okStep k f r
        · have hr : Rel (k, c, f) (k, r, nxt k f r) := ⟨rfl, h.1, h.2, rfl⟩
          simp only [if_pos h, if_pos hr]
          exact ih _
        · have hr : ¬ Rel (k, c, f) (k, r, nxt k f r) := fun hh => h ⟨hh.2.1, hh.2.2.1⟩
          simp only [if_neg h, if_neg hr]
      · intro b _ hb
        have hr : ¬ Rel (k, c, f) (k, r, b) := fun hh => hb hh.2.2.2
        simp only [if_neg hr]
      · simp
    · intro k' _ hk'
      apply Finset.sum_eq_zero
      intro p _
      have hr : ¬ Rel (k, c, f) (k', p.1, p.2) := fun hh => hk' hh.1.symm
      simp only [if_neg hr]
    · simp

theorem cnt_gen (m : ℕ) (R : Col → Prop) [DecidablePred R] (g : Col → Bool) (k : Fin 3) :
    (Finset.univ.filter (fun x : Fin (m + 1) → Col =>
      R (x 0) ∧ noClash (m + 1) x ∧ SemK k (g (x 0)) (Fin.tail x))).card =
    ∑ c : Col, if R c then T m (k, c, g c) else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (m + 1) → Col => x 0) (t := Finset.univ)
    (by simp)]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.filter_filter]
  by_cases h : R c
  · rw [if_pos h]
    unfold T
    congr 1
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨⟨_, h2, h3⟩, h4⟩
      subst h4
      exact ⟨rfl, h2, h3⟩
    · rintro ⟨h4, h2, h3⟩
      have h4' : x 0 = c := h4
      subst h4'
      exact ⟨⟨h, h2, h3⟩, rfl⟩
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x _ ⟨⟨h1, _⟩, h4⟩
    subst h4
    exact h h1

theorem obt_iff {n : ℕ} (x : Fin n → Col) :
    oneBeforeTwo n x ↔ SemTop false x ∧ ((∃ j, x j 0 = 1) ∨ SemBot false x) := by
  unfold oneBeforeTwo SemTop SemBot
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · obtain ⟨j', i', h1, h2⟩ := h j 0 hj
      right
      fin_cases i'
      · exact ⟨j', by simpa using h1, h2⟩
      · simp at h1
    · by_cases ht : ∃ j, x j 0 = 1
      · exact Or.inl ht
      · right
        intro j hj
        obtain ⟨j', i', h1, h2⟩ := h j 1 hj
        fin_cases i'
        · exact absurd ⟨j', h2⟩ ht
        · right; exact ⟨j', by simpa using h1, h2⟩
  · rintro ⟨h1, h2⟩ j i hj
    fin_cases i
    · obtain ⟨j', hj', hx⟩ := (h1 j hj).resolve_left (by simp)
      exact ⟨j', 0, Or.inr ⟨rfl, hj'⟩, hx⟩
    · rcases h2 with ⟨j', hj'⟩ | h2
      · exact ⟨j', 0, Or.inl (by simp), hj'⟩
      · obtain ⟨j', hj', hx⟩ := (h2 j hj).resolve_left (by simp)
        exact ⟨j', 1, Or.inr ⟨rfl, hj'⟩, hx⟩

def PA (m : ℕ) (x : Fin (m + 1) → Col) : Prop :=
  noClash (m + 1) x ∧ x 0 0 = 0 ∧ SemTop false x
def PB (m : ℕ) (x : Fin (m + 1) → Col) : Prop :=
  noClash (m + 1) x ∧ x 0 0 = 0 ∧ Top03 x
def PC (m : ℕ) (x : Fin (m + 1) → Col) : Prop :=
  noClash (m + 1) x ∧ x 0 0 = 0 ∧ Top03 x ∧ SemBot false x
instance (m : ℕ) (x : Fin (m + 1) → Col) : Decidable (PA m x) := by unfold PA; infer_instance
instance (m : ℕ) (x : Fin (m + 1) → Col) : Decidable (PB m x) := by unfold PB; infer_instance
instance (m : ℕ) (x : Fin (m + 1) → Col) : Decidable (PC m x) := by unfold PC; infer_instance

theorem top03_semTop {n : ℕ} (x : Fin n → Col) (h : Top03 x) : SemTop false x := by
  intro j hj
  exfalso
  have := h j
  rw [hj] at this
  revert this; decide

theorem F_iff (m : ℕ) (x : Fin (m + 1) → Col) :
    (noClash (m + 1) x ∧ topLeftZero (m + 1) x ∧ oneBeforeTwo (m + 1) x) ↔
      ((PA m x ∧ ¬ PB m x) ∨ PC m x) := by
  have hz : topLeftZero (m + 1) x ↔ x 0 0 = 0 := by
    unfold topLeftZero
    constructor
    · intro h; exact h 0 rfl
    · intro h j hj
      have : j = 0 := Fin.ext (by simpa using hj)
      subst this; exact h
  rw [hz, obt_iff]
  unfold PA PB PC
  constructor
  · rintro ⟨hc, hz, hs, ht⟩
    by_cases h3 : Top03 x
    · right
      refine ⟨hc, hz, h3, ?_⟩
      rcases ht with ⟨j, hj⟩ | hb
      · exfalso
        have := h3 j
        rw [hj] at this
        revert this; decide
      · exact hb
    · left
      exact ⟨⟨hc, hz, hs⟩, fun h => h3 h.2.2⟩
  · rintro (⟨⟨hc, hz, hs⟩, hn⟩ | ⟨hc, hz, h3, hb⟩)
    · refine ⟨hc, hz, hs, Or.inl ?_⟩
      have h3 : ¬ Top03 x := fun h => hn ⟨hc, hz, h⟩
      unfold Top03 at h3
      push_neg at h3
      obtain ⟨j, hj0, hj3⟩ := h3
      have hv : x j 0 = 1 ∨ x j 0 = 2 := by
        generalize x j 0 = v at hj0 hj3 ⊢
        revert v; decide
      rcases hv with hv | hv
      · exact ⟨j, hv⟩
      · obtain ⟨j', _, hj'⟩ := (hs j hv).resolve_left (by simp)
        exact ⟨j', hj'⟩
    · exact ⟨hc, hz, top03_semTop x h3, Or.inr hb⟩

theorem a_cards (m : ℕ) : (a (m + 1) : ℤ) =
    ((Finset.univ.filter (fun x : Fin (m + 1) → Col => PA m x)).card : ℤ) -
    (Finset.univ.filter (fun x : Fin (m + 1) → Col => PB m x)).card +
    (Finset.univ.filter (fun x : Fin (m + 1) → Col => PC m x)).card := by
  have hBA : Finset.univ.filter (fun x : Fin (m + 1) → Col => PB m x) ⊆
      Finset.univ.filter (fun x : Fin (m + 1) → Col => PA m x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, hx.2.1, top03_semTop x hx.2.2⟩
  have hCB : Finset.univ.filter (fun x : Fin (m + 1) → Col => PC m x) ⊆
      Finset.univ.filter (fun x : Fin (m + 1) → Col => PB m x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
  have hF : Finset.univ.filter (fun x : Fin (m + 1) → Col =>
      noClash (m + 1) x ∧ topLeftZero (m + 1) x ∧ oneBeforeTwo (m + 1) x) =
      (Finset.univ.filter (fun x : Fin (m + 1) → Col => PA m x) \
        Finset.univ.filter (fun x : Fin (m + 1) → Col => PB m x)) ∪
      Finset.univ.filter (fun x : Fin (m + 1) → Col => PC m x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
    exact F_iff m x
  have hd : Disjoint (Finset.univ.filter (fun x : Fin (m + 1) → Col => PA m x) \
        Finset.univ.filter (fun x : Fin (m + 1) → Col => PB m x))
      (Finset.univ.filter (fun x : Fin (m + 1) → Col => PC m x)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_sdiff.mp h1).2 (hCB h2)
  have : a (m + 1) = (Finset.univ.filter (fun x : Fin (m + 1) → Col => PA m x)).card -
      (Finset.univ.filter (fun x : Fin (m + 1) → Col => PB m x)).card +
      (Finset.univ.filter (fun x : Fin (m + 1) → Col => PC m x)).card := by
    unfold a
    rw [hF, Finset.card_union_of_disjoint hd, Finset.card_sdiff_of_subset hBA]
  rw [this, Nat.cast_add, Nat.cast_sub (Finset.card_le_card hBA)]

theorem semK0 {n : ℕ} (f : Bool) (y : Fin n → Col) : SemK 0 f y ↔ SemTop f y := by simp [SemK]
theorem semK1 {n : ℕ} (f : Bool) (y : Fin n → Col) : SemK 1 f y ↔ Top03 y := by simp [SemK]
theorem semK2 {n : ℕ} (f : Bool) (y : Fin n → Col) : SemK 2 f y ↔ Top03 y ∧ SemBot f y := by
  simp [SemK]

theorem semTop_tail {m : ℕ} (x : Fin (m + 1) → Col) (h : x 0 0 = 0) :
    SemTop false x ↔ SemTop false (Fin.tail x) := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  rw [SemTop_cons]
  simp [h]

theorem top03_tail {m : ℕ} (x : Fin (m + 1) → Col) (h : x 0 0 = 0) :
    Top03 x ↔ Top03 (Fin.tail x) := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  rw [Top03_cons]
  simp [h]

theorem semBot_tail {m : ℕ} (x : Fin (m + 1) → Col) :
    SemBot false x ↔ (x 0 1 = 2 → False) ∧ SemBot (decide (x 0 1 = 1)) (Fin.tail x) := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  rw [SemBot_cons]
  simp

theorem cntA (m : ℕ) : (Finset.univ.filter (fun x : Fin (m + 1) → Col => PA m x)).card =
    ∑ c : Col, if c 0 = 0 then T m (0, c, false) else 0 := by
  rw [← cnt_gen m (fun c => c 0 = 0) (fun _ => false) 0]
  congr 1
  apply Finset.filter_congr
  intro x _
  unfold PA
  rw [semK0]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, (semTop_tail x h2).mp h3⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨h1, h2, (semTop_tail x h2).mpr h3⟩

theorem cntB (m : ℕ) : (Finset.univ.filter (fun x : Fin (m + 1) → Col => PB m x)).card =
    ∑ c : Col, if c 0 = 0 then T m (1, c, false) else 0 := by
  rw [← cnt_gen m (fun c => c 0 = 0) (fun _ => false) 1]
  congr 1
  apply Finset.filter_congr
  intro x _
  unfold PB
  rw [semK1]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, (top03_tail x h2).mp h3⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨h1, h2, (top03_tail x h2).mpr h3⟩

theorem cntC (m : ℕ) : (Finset.univ.filter (fun x : Fin (m + 1) → Col => PC m x)).card =
    ∑ c : Col, if c 0 = 0 ∧ c 1 ≠ 2 then T m (2, c, decide (c 1 = 1)) else 0 := by
  rw [← cnt_gen m (fun c => c 0 = 0 ∧ c 1 ≠ 2) (fun c => decide (c 1 = 1)) 2]
  congr 1
  apply Finset.filter_congr
  intro x _
  unfold PC
  rw [semK2]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨hb1, hb2⟩ := (semBot_tail x).mp h4
    exact ⟨⟨h2, hb1⟩, h1, (top03_tail x h2).mp h3, hb2⟩
  · rintro ⟨⟨h2, hb1⟩, h1, h3, hb2⟩
    exact ⟨h1, h2, (top03_tail x h2).mpr h3, (semBot_tail x).mpr ⟨hb1, hb2⟩⟩

def w (s : St) : ℤ :=
  if s.2.1 0 = 0 then
    (if s.1 = 0 then (if s.2.2 = false then 1 else 0)
     else if s.1 = 1 then (if s.2.2 = false then -1 else 0)
     else (if s.2.1 1 ≠ 2 ∧ s.2.2 = decide (s.2.1 1 = 1) then 1 else 0))
  else 0

theorem a_eq (m : ℕ) : (a (m + 1) : ℤ) = ∑ s : St, w s * (V Rel m s : ℤ) := by
  rw [a_cards, cntA, cntB, cntC]
  push_cast
  simp only [T_eq]
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp only [w]
  split_ifs <;> simp_all <;> ring

def cc : ℕ → ℤ := fun j => [(0 : ℤ), 0, -7, -6, 22, -10, 1].getD j 0

def A (m : ℕ) : ℤ := ∑ s : St, w s * (V Rel m s : ℤ)

theorem hrecA (k : ℕ) : A (k + 6) = 10 * A (k + 5) - 22 * A (k + 4) + 6 * A (k + 3) + 7 * A (k + 2) := by
  have h := rec_w Rel 6 cc w (by decide +kernel) k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = -7 := rfl
  have e3 : cc 3 = -6 := rfl
  have e4 : cc 4 = 22 := rfl
  have e5 : cc 5 = -10 := rfl
  have e6 : cc 6 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, zero_mul,
    zero_add] at h
  unfold A
  linarith

theorem v1 : A 1 = 14 := by unfold A; decide +kernel
theorem v2 : A 2 = 95 := by unfold A; decide +kernel
theorem v3 : A 3 = 662 := by unfold A; decide +kernel
theorem v4 : A 4 = 4631 := by unfold A; decide +kernel
theorem v5 : A 5 = 32414 := by unfold A; decide +kernel
theorem v0 : A 0 = 3 := by unfold A; decide +kernel

theorem closed (j : ℕ) : (a (j + 2) : ℚ) = (49 + 27 * 7 ^ (j + 2)) / 98 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have ha : ∀ i, (a (i + 1) : ℚ) = (A i : ℚ) := fun i => by exact_mod_cast a_eq i
    by_cases h : j ≤ 4
    · interval_cases j
      · rw [ha 1, v1]; norm_num
      · rw [ha 2, v2]; norm_num
      · rw [ha 3, v3]; norm_num
      · rw [ha 4, v4]; norm_num
      · rw [ha 5, v5]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := ⟨j - 5, by omega⟩
      have r : (A (k + 6) : ℚ) = 10 * A (k + 5) - 22 * A (k + 4) + 6 * A (k + 3) + 7 * A (k + 2) := by
        exact_mod_cast hrecA k
      have e : k + 5 + 2 = (k + 6) + 1 := by omega
      rw [e, ha (k + 6), r, ← ha (k + 5), ← ha (k + 4), ← ha (k + 3), ← ha (k + 2)]
      have i1 := ih (k + 4) (by omega)
      have i2 := ih (k + 3) (by omega)
      have i3 := ih (k + 2) (by omega)
      have i4 := ih (k + 1) (by omega)
      rw [show k + 4 + 2 = k + 5 + 1 by omega] at i1
      rw [show k + 3 + 2 = k + 4 + 1 by omega] at i2
      rw [show k + 2 + 2 = k + 3 + 1 by omega] at i3
      rw [show k + 1 + 2 = k + 2 + 1 by omega] at i4
      rw [i1, i2, i3, i4]
      ring

theorem gf_final (b : ℕ → ℚ) (h0 : b 0 = 0) (h1 : b 1 = 3) (h2 : b 2 = 14) (h3 : b 3 = 95)
    (h4 : ∀ n, b (n + 4) - 8 * b (n + 3) + 7 * b (n + 2) = 0) :
    PowerSeries.mk b * ((1 - PowerSeries.X) * (1 - 7 * PowerSeries.X)) =
      PowerSeries.X * (3 - 10 * PowerSeries.X + 4 * PowerSeries.X ^ 2) := by
  have e : (PowerSeries.mk b * ((1 - PowerSeries.X) * (1 - 7 * PowerSeries.X)) : PowerSeries ℚ) =
      PowerSeries.mk b - PowerSeries.C 8 * (PowerSeries.X * PowerSeries.mk b) +
        PowerSeries.C 7 * (PowerSeries.X * (PowerSeries.X * PowerSeries.mk b)) := by
    rw [map_ofNat, map_ofNat]; ring
  have e2 : (PowerSeries.X * (3 - 10 * PowerSeries.X + 4 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
      PowerSeries.C 3 * PowerSeries.X + PowerSeries.C (-10) * PowerSeries.X ^ 2 +
        PowerSeries.C 4 * PowerSeries.X ^ 3 := by
    simp only [map_neg, map_ofNat]; ring
  rw [e, e2]
  ext n
  rcases n with _ | _ | _ | _ | n
  · simp [h0]
  · simp [h1, h0, PowerSeries.coeff_X]
  · simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_X, h1, h2]
    linarith
  · simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_X, h2, h3]
    linarith
  · simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
    linarith [h4 n]

end OMA.S_oeis_a233083

theorem OMA.solution : type_of% @OMA.S_oeis_a233083.main := by
  refine ⟨?_, ?_⟩
  · have ha : ∀ i, (OMA.S_oeis_a233083.a (i + 1) : ℚ) = (OMA.S_oeis_a233083.A i : ℚ) :=
      fun i => by exact_mod_cast OMA.S_oeis_a233083.a_eq i
    apply OMA.S_oeis_a233083.gf_final
    · simp [OMA.S_oeis_a233083.a]
    · simp only [if_neg one_ne_zero]; rw [ha 0, OMA.S_oeis_a233083.v0]; norm_num
    · simp only [if_neg two_ne_zero]; rw [ha 1, OMA.S_oeis_a233083.v1]; norm_num
    · simp only [if_neg three_ne_zero]; rw [ha 2, OMA.S_oeis_a233083.v2]; norm_num
    · intro n
      simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, if_false]
      have c1 := OMA.S_oeis_a233083.closed (n + 2)
      have c2 := OMA.S_oeis_a233083.closed (n + 1)
      have c3 := OMA.S_oeis_a233083.closed n
      rw [show n + 4 = n + 2 + 2 by omega, c1, show n + 3 = n + 1 + 2 by omega, c2, c3]
      ring
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    exact OMA.S_oeis_a233083.closed j
