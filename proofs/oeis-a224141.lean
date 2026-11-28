import OMAStatements.S_oeis_a224141

-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Sketch: the slices of the array form a sequence of states with conditions on single slices, on
-- adjacent pairs and on adjacent triples (handled through the overlapping pairs, with the pair transfer summed over the next slice only).
-- w k y counts valid sequences ending in y (bijection via Fin.init / Fin.snoc, adapted from the merged
-- proof of oeis-a223443 by @sntntHb); the dual vectors u j are tabulated and checked by decide +kernel,
-- together with the coordinatewise relation that gives the recurrence; the g.f. follows coefficientwise
-- from the recurrence and the first values, and the closed form by strong induction.

namespace OMA.P_oeis_a224141

open Finset

section Gen
variable {σ : Type} [Fintype σ] [DecidableEq σ] (B : σ → Prop) [DecidablePred B]
  (T : σ → σ → Prop) [DecidableRel T]

def Gd (n : ℕ) (f : Fin n → σ) : Prop :=
  (∀ i, B (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → T (f i) (f j)

instance (n : ℕ) : DecidablePred (Gd B T n) := fun f => by unfold Gd; infer_instance

def w : ℕ → σ → ℕ
  | 0, y => if B y then 1 else 0
  | k + 1, y => ∑ x, if B y ∧ T x y then w k x else 0

def u : ℕ → σ → ℕ
  | 0, _ => 1
  | j + 1, x => ∑ y, if B y ∧ T x y then u j y else 0

def cnt (k : ℕ) (y : σ) : ℕ :=
  ((univ : Finset (Fin (k + 1) → σ)).filter (fun f => Gd B T (k + 1) f ∧ f (Fin.last k) = y)).card

lemma gd_succ (k : ℕ) (f : Fin (k + 2) → σ) :
    Gd B T (k + 2) f ↔ Gd B T (k + 1) (Fin.init f) ∧ B (f (Fin.last (k + 1))) ∧
      T (f (Fin.castSucc (Fin.last k))) (f (Fin.last (k + 1))) := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨⟨fun i => h0 _, fun i j hij => h _ _ (by simp [hij])⟩, h0 _, h _ _ (by simp)⟩
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · by_cases hi : i.val < k + 1
      · have := h0 ⟨i.val, hi⟩
        simpa [Fin.init] using this
      · have hi' : i = Fin.last (k + 1) := Fin.ext (by simp; omega)
        subst hi'; exact h2
    · by_cases hj : j.val < k + 1
      · have := h1 ⟨i.val, by omega⟩ ⟨j.val, hj⟩ hij
        simpa [Fin.init] using this
      · have hj' : j = Fin.last (k + 1) := Fin.ext (by simp; omega)
        have hi' : i = Fin.castSucc (Fin.last k) := Fin.ext (by simp; omega)
        subst hj' hi'; exact h3

lemma cnt_zero (y : σ) : cnt B T 0 y = if B y then 1 else 0 := by
  unfold cnt
  split_ifs with hy
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => y, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
    · rintro rfl; exact ⟨⟨fun _ => hy, fun i j hij => by omega⟩, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro f - ⟨⟨h0, -⟩, h⟩; exact hy (h ▸ h0 _)

lemma cnt_succ (k : ℕ) (y : σ) :
    cnt B T (k + 1) y = ∑ x, if B y ∧ T x y then cnt B T k x else 0 := by
  by_cases hy : B y
  · have e : cnt B T (k + 1) y = ((univ : Finset (Fin (k + 1) → σ)).filter
        (fun g => Gd B T (k + 1) g ∧ T (g (Fin.last k)) y)).card := by
      unfold cnt
      apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g y)
      · intro f hf
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
        obtain ⟨hg, hl⟩ := hf
        rw [gd_succ] at hg
        refine ⟨hg.1, ?_⟩
        have := hg.2.2; rw [hl] at this; simpa [Fin.init] using this
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        refine ⟨?_, by simp⟩
        rw [gd_succ]
        refine ⟨by simpa using hg.1, by simpa using hy, ?_⟩
        simpa using hg.2
      · intro f hf
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
        rw [← hf.2]; exact Fin.snoc_init_self f
      · intro g _; exact Fin.init_snoc _ _
    rw [e, Finset.card_eq_sum_card_fiberwise
      (f := fun g : Fin (k + 1) → σ => g (Fin.last k))
      (t := univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.filter_filter]
    split_ifs with h
    · unfold cnt; congr 1; apply Finset.filter_congr
      intro g _
      constructor
      · rintro ⟨⟨hg, -⟩, hx⟩; exact ⟨hg, hx⟩
      · rintro ⟨hg, hx⟩; exact ⟨⟨hg, hx ▸ h.2⟩, hx⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro g - ⟨⟨-, ha⟩, hx⟩; exact h ⟨hy, hx ▸ ha⟩
  · have : cnt B T (k + 1) y = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro f - ⟨⟨h0, -⟩, h⟩; exact hy (h ▸ h0 _)
    rw [this]; symm
    apply Finset.sum_eq_zero; intro x _
    rw [if_neg (fun h => hy h.1)]

lemma cnt_eq (k : ℕ) (y : σ) : cnt B T k y = w B T k y := by
  induction k generalizing y with
  | zero => rw [cnt_zero]; rfl
  | succ k ih => rw [cnt_succ]; simp only [w, ih]

lemma total (k : ℕ) :
    ((univ : Finset (Fin (k + 1) → σ)).filter (Gd B T (k + 1))).card = ∑ y, w B T k y := by
  simp only [← cnt_eq]
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin (k + 1) → σ => g (Fin.last k))
    (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.filter_filter]

lemma w_zero_of (k : ℕ) (x : σ) (hx : ¬ B x) : w B T k x = 0 := by
  cases k with
  | zero => simp [w, hx]
  | succ k =>
    simp only [w]
    apply Finset.sum_eq_zero; intro y _
    rw [if_neg (fun h => hx h.1)]

lemma dual (j k : ℕ) : ∑ y, w B T (k + j) y = ∑ x, w B T k x * u B T j x := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

/-- The count of valid sequences of length k + 1 + j through the dual vectors. -/
lemma total_dual (k j : ℕ) :
    ((univ : Finset (Fin (k + j + 1) → σ)).filter (Gd B T (k + j + 1))).card =
      ∑ x, w B T k x * u B T j x := by
  rw [total, dual]

end Gen

section Gen3
variable {σ : Type} [Fintype σ] [DecidableEq σ] (B : σ → Prop) [DecidablePred B]
  (T : σ → σ → Prop) [DecidableRel T] (U : σ → σ → σ → Prop) [∀ a b c, Decidable (U a b c)]

def Gd3 (n : ℕ) (f : Fin n → σ) : Prop :=
  (∀ i, B (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → T (f i) (f j)) ∧
    ∀ i j l : Fin n, j.val = i.val + 1 → l.val = j.val + 1 → U (f i) (f j) (f l)

instance (n : ℕ) : DecidablePred (Gd3 B T U n) := fun f => by unfold Gd3; infer_instance

def PB (p : σ × σ) : Prop := B p.1 ∧ B p.2 ∧ T p.1 p.2

def PT (p q : σ × σ) : Prop := p.2 = q.1 ∧ U p.1 p.2 q.2

instance : DecidablePred (PB B T) := fun p => by unfold PB; infer_instance
instance : DecidableRel (PT U) := fun p q => by unfold PT; infer_instance

/-- The overlapping pairs of a sequence. -/
def toP (n : ℕ) (f : Fin (n + 2) → σ) : Fin (n + 1) → σ × σ :=
  fun i => (f i.castSucc, f i.succ)

/-- A sequence from a sequence of pairs. -/
def ofP (n : ℕ) (h : Fin (n + 1) → σ × σ) : Fin (n + 2) → σ :=
  fun i => if hi : i.val < n + 1 then (h ⟨i.val, hi⟩).1 else (h (Fin.last n)).2

lemma gd3_toP (n : ℕ) (f : Fin (n + 2) → σ) (hf : Gd3 B T U (n + 2) f) :
    Gd (PB B T) (PT U) (n + 1) (toP n f) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨fun i => ⟨h1 _, h1 _, h2 _ _ (by simp)⟩, fun i j hij => ⟨?_, ?_⟩⟩
  · simp only [toP]; congr 1; ext; simp [hij]
  · simp only [toP]
    exact h3 _ _ _ (by simp) (by simp [hij])

lemma toP_ofP (n : ℕ) (h : Fin (n + 1) → σ × σ) (hh : Gd (PB B T) (PT U) (n + 1) h) :
    toP n (ofP n h) = h := by
  funext i
  simp only [toP, ofP]
  ext
  · simp only [Fin.coe_castSucc, i.isLt, dite_true]
  · by_cases hi : i.val + 1 < n + 1
    · simp only [Fin.val_succ, hi, dite_true]
      have := (hh.2 i ⟨i.val + 1, hi⟩ rfl).1
      exact this.symm
    · have hi' : i = Fin.last n := Fin.ext (by simp; omega)
      subst hi'
      simp

lemma ofP_toP (n : ℕ) (f : Fin (n + 2) → σ) : ofP n (toP n f) = f := by
  funext i
  simp only [ofP, toP]
  split_ifs with hi
  · rfl
  · have : i = Fin.last (n + 1) := Fin.ext (by simp; omega)
    subst this; rfl

lemma gd_ofP (n : ℕ) (h : Fin (n + 1) → σ × σ) (hh : Gd (PB B T) (PT U) (n + 1) h) :
    Gd3 B T U (n + 2) (ofP n h) := by
  have e := toP_ofP B T U n h hh
  set f := ofP n h
  have hp : ∀ i : Fin (n + 1), PB B T (f i.castSucc, f i.succ) := fun i => by
    have := hh.1 i; rw [← e] at this; exact this
  have hq : ∀ i j : Fin (n + 1), j.val = i.val + 1 →
      PT U (f i.castSucc, f i.succ) (f j.castSucc, f j.succ) := fun i j hij => by
    have := hh.2 i j hij; rw [← e] at this; exact this
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j l hij hjl => ?_⟩
  · by_cases hi : i.val < n + 1
    · have := (hp ⟨i.val, hi⟩).1; exact this
    · have := (hp (Fin.last n)).2.1
      have hi' : i = (Fin.last n).succ := Fin.ext (by simp; omega)
      rw [hi']; exact this
  · have := (hp ⟨i.val, by omega⟩).2.2
    have hj : j = (⟨i.val, by omega⟩ : Fin (n + 1)).succ := Fin.ext (by simp; omega)
    rw [hj]; exact this
  · have := (hq ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij).2
    have e1 : (⟨i.val, by omega⟩ : Fin (n + 1)).castSucc = i := Fin.ext rfl
    have e2 : (⟨i.val, by omega⟩ : Fin (n + 1)).succ = j := Fin.ext (by simp; omega)
    have e3 : (⟨j.val, by omega⟩ : Fin (n + 1)).succ = l := Fin.ext (by simp; omega)
    rw [e1, e2, e3] at this; exact this

lemma card_pairs (n : ℕ) :
    ((univ : Finset (Fin (n + 2) → σ)).filter (Gd3 B T U (n + 2))).card =
      ((univ : Finset (Fin (n + 1) → σ × σ)).filter (Gd (PB B T) (PT U) (n + 1))).card := by
  apply Finset.card_nbij' (toP n) (ofP n)
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    exact gd3_toP B T U n f hf
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh ⊢
    exact gd_ofP B T U n h hh
  · intro f _; exact ofP_toP n f
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh
    exact toP_ofP B T U n h hh

end Gen3

section Gen3s
variable {σ : Type} [Fintype σ] [DecidableEq σ] (B : σ → Prop) [DecidablePred B]
  (T : σ → σ → Prop) [DecidableRel T] (U : σ → σ → σ → Prop) [∀ a b c, Decidable (U a b c)]

/-- The dual vectors of the pair transfer, summed over the next slice only. -/
def v3 : ℕ → σ × σ → ℕ
  | 0, _ => 1
  | j + 1, p => ∑ c, if PB B T (p.2, c) ∧ U p.1 p.2 c then v3 j (p.2, c) else 0

lemma u_eq_v3 (j : ℕ) (p : σ × σ) : u (PB B T) (PT U) j p = v3 B T U j p := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
    simp only [u, v3, ih]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single p.2]
    · apply Finset.sum_congr rfl; intro c _
      simp only [PT, true_and]
    · intro b _ hb; apply Finset.sum_eq_zero; intro c _
      rw [if_neg]; rintro ⟨-, h, -⟩; exact hb h.symm
    · intro h; exact absurd (Finset.mem_univ _) h

end Gen3s

end OMA.P_oeis_a224141

namespace OMA.P_oeis_a224141

open Finset OMA.S_oeis_a224141

abbrev St := Fin 3 → Fin 2

def B (s : St) : Prop := LineOK s

def T (s t : St) : Prop := BlockOK s t

instance : DecidablePred B := fun s => by unfold B LineOK; infer_instance
instance : DecidableRel T := fun s t => by unfold T BlockOK; infer_instance

def U (s t v : St) : Prop := TriOK s t v

instance : ∀ s t v, Decidable (U s t v) := fun s t v => by unfold U TriOK; infer_instance

lemma good_iff {n : ℕ} (x : Fin n → St) : Good x ↔ Gd3 B T U n x := by
  unfold Good
  simp only [Gd3, B, T, U, implies_true, true_and]

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → St)).filter (Gd3 B T U n)).card := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => good_iff x)), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

abbrev Sx := St × St
abbrev PB' : Sx → Prop := PB B T
abbrev PT' : Sx → Sx → Prop := PT U

lemma aw (k j : ℕ) : a (k + j + 2) = ∑ x, w PB' PT' k x * u PB' PT' j x := by
  rw [a_eq, card_pairs]; exact total_dual PB' PT' k j

def idx1 (s : St) : ℕ := (s 0).val + 2 * (s 1).val + 4 * (s 2).val

def idx (p : Sx) : ℕ := idx1 p.1 * 8 + idx1 p.2

def tb (L : List ℕ) (s : Sx) : ℕ := L.getD (idx s) 0

def T1 : List ℕ := [7, 3, 4, 2, 3, 0, 2, 1, 7, 3, 4, 2, 3, 0, 2, 1, 7, 3, 4, 2, 3, 0, 2, 1, 7, 3, 4, 2, 3, 0, 2, 1, 4, 0, 4, 2, 2, 0, 2, 1, 4, 0, 4, 2, 2, 0, 2, 1, 4, 0, 4, 2, 2, 0, 2, 1, 4, 0, 4, 2, 2, 0, 2, 1]
def T2 : List ℕ := [22, 6, 9, 3, 5, 0, 3, 1, 22, 6, 9, 3, 5, 0, 3, 1, 22, 6, 9, 3, 5, 0, 3, 1, 22, 6, 9, 3, 5, 0, 3, 1, 16, 0, 9, 3, 4, 0, 3, 1, 16, 0, 9, 3, 4, 0, 3, 1, 16, 0, 9, 3, 4, 0, 3, 1, 16, 0, 9, 3, 4, 0, 3, 1]
def T3 : List ℕ := [49, 10, 16, 4, 8, 0, 4, 1, 49, 10, 16, 4, 8, 0, 4, 1, 49, 10, 16, 4, 8, 0, 4, 1, 49, 10, 16, 4, 8, 0, 4, 1, 39, 0, 16, 4, 7, 0, 4, 1, 39, 0, 16, 4, 7, 0, 4, 1, 39, 0, 16, 4, 7, 0, 4, 1, 39, 0, 16, 4, 7, 0, 4, 1]
def T4 : List ℕ := [92, 15, 25, 5, 12, 0, 5, 1, 92, 15, 25, 5, 12, 0, 5, 1, 92, 15, 25, 5, 12, 0, 5, 1, 92, 15, 25, 5, 12, 0, 5, 1, 77, 0, 25, 5, 11, 0, 5, 1, 77, 0, 25, 5, 11, 0, 5, 1, 77, 0, 25, 5, 11, 0, 5, 1, 77, 0, 25, 5, 11, 0, 5, 1]
def T5 : List ℕ := [155, 21, 36, 6, 17, 0, 6, 1, 155, 21, 36, 6, 17, 0, 6, 1, 155, 21, 36, 6, 17, 0, 6, 1, 155, 21, 36, 6, 17, 0, 6, 1, 134, 0, 36, 6, 16, 0, 6, 1, 134, 0, 36, 6, 16, 0, 6, 1, 134, 0, 36, 6, 16, 0, 6, 1, 134, 0, 36, 6, 16, 0, 6, 1]

set_option maxRecDepth 100000 in
lemma hs1 : ∀ p : Sx, (∑ c : St, if PB' (p.2, c) ∧ U p.1 p.2 c then 1 else 0) = tb T1 p := by
  decide +kernel

lemma hu1 (p : Sx) : u PB' PT' 1 p = tb T1 p := by
  rw [u_eq_v3]; exact hs1 p

lemma hv1 (p : Sx) : v3 B T U 1 p = tb T1 p := by
  rw [← u_eq_v3]; exact hu1 p

set_option maxRecDepth 100000 in
lemma hs2 : ∀ p : Sx, (∑ c : St, if PB' (p.2, c) ∧ U p.1 p.2 c then tb T1 (p.2, c) else 0) = tb T2 p := by
  decide +kernel

lemma hv2 (p : Sx) : v3 B T U 2 p = tb T2 p := by
  show (∑ c, if PB B T (p.2, c) ∧ U p.1 p.2 c then v3 B T U 1 (p.2, c) else 0) = _
  simp only [hv1]; exact hs2 p

lemma hu2 (p : Sx) : u PB' PT' 2 p = tb T2 p := by
  rw [u_eq_v3]; exact hv2 p

set_option maxRecDepth 100000 in
lemma hs3 : ∀ p : Sx, (∑ c : St, if PB' (p.2, c) ∧ U p.1 p.2 c then tb T2 (p.2, c) else 0) = tb T3 p := by
  decide +kernel

lemma hv3 (p : Sx) : v3 B T U 3 p = tb T3 p := by
  show (∑ c, if PB B T (p.2, c) ∧ U p.1 p.2 c then v3 B T U 2 (p.2, c) else 0) = _
  simp only [hv2]; exact hs3 p

lemma hu3 (p : Sx) : u PB' PT' 3 p = tb T3 p := by
  rw [u_eq_v3]; exact hv3 p

set_option maxRecDepth 100000 in
lemma hs4 : ∀ p : Sx, (∑ c : St, if PB' (p.2, c) ∧ U p.1 p.2 c then tb T3 (p.2, c) else 0) = tb T4 p := by
  decide +kernel

lemma hv4 (p : Sx) : v3 B T U 4 p = tb T4 p := by
  show (∑ c, if PB B T (p.2, c) ∧ U p.1 p.2 c then v3 B T U 3 (p.2, c) else 0) = _
  simp only [hv3]; exact hs4 p

lemma hu4 (p : Sx) : u PB' PT' 4 p = tb T4 p := by
  rw [u_eq_v3]; exact hv4 p

set_option maxRecDepth 100000 in
lemma hs5 : ∀ p : Sx, (∑ c : St, if PB' (p.2, c) ∧ U p.1 p.2 c then tb T4 (p.2, c) else 0) = tb T5 p := by
  decide +kernel

lemma hv5 (p : Sx) : v3 B T U 5 p = tb T5 p := by
  show (∑ c, if PB B T (p.2, c) ∧ U p.1 p.2 c then v3 B T U 4 (p.2, c) else 0) = _
  simp only [hv4]; exact hs5 p

lemma hu5 (p : Sx) : u PB' PT' 5 p = tb T5 p := by
  rw [u_eq_v3]; exact hv5 p

set_option maxRecDepth 100000 in
lemma hrel : ∀ x, PB' x → tb T5 x + 6 * tb T3 x + tb T1 x = 4 * tb T4 x + 4 * tb T2 x := by
  decide +kernel

lemma arec (k : ℕ) : (a (k + 7) : ℤ) = 4 * a (k + 6) - 6 * a (k + 5) + 4 * a (k + 4) - a (k + 3) := by
  have e5 : a (k + 7) = ∑ x, w PB' PT' k x * u PB' PT' 5 x := aw k 5
  have e4 : a (k + 6) = ∑ x, w PB' PT' k x * u PB' PT' 4 x := aw k 4
  have e3 : a (k + 5) = ∑ x, w PB' PT' k x * u PB' PT' 3 x := aw k 3
  have e2 : a (k + 4) = ∑ x, w PB' PT' k x * u PB' PT' 2 x := aw k 2
  have e1 : a (k + 3) = ∑ x, w PB' PT' k x * u PB' PT' 1 x := aw k 1
  have key : ∑ x, w PB' PT' k x * u PB' PT' 5 x + 6 * ∑ x, w PB' PT' k x * u PB' PT' 3 x + ∑ x, w PB' PT' k x * u PB' PT' 1 x = 4 * ∑ x, w PB' PT' k x * u PB' PT' 4 x + 4 * ∑ x, w PB' PT' k x * u PB' PT' 2 x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : PB' x
    · have h := hrel x hx
      rw [hu5, hu4, hu3, hu2, hu1]
      try simp only [u]
      calc (w PB' PT' k x * tb T5 x) + 6 * (w PB' PT' k x * tb T3 x) + (w PB' PT' k x * tb T1 x)
          = w PB' PT' k x * (tb T5 x + 6 * tb T3 x + tb T1 x) := by ring
        _ = w PB' PT' k x * (4 * tb T4 x + 4 * tb T2 x) := by rw [h]
        _ = _ := by ring
    · simp [w_zero_of PB' PT' k x hx]
  rw [e5, e4, e3, e2, e1]
  have := congrArg (fun t : ℕ => (t : ℤ)) key
  push_cast at this ⊢
  linarith

lemma val (j : ℕ) : a (j + 2) = ∑ x, (if PB' x then 1 else 0) * u PB' PT' j x := by
  rw [show j + 2 = 0 + j + 2 by ring, aw]; rfl

set_option maxRecDepth 100000 in
lemma av1 : a 1 = 7 := by
  rw [a_eq]; decide +kernel

set_option maxRecDepth 100000 in
lemma av2 : a 2 = 22 := by
  rw [val 0]; simp only [u]; decide +kernel

set_option maxRecDepth 100000 in
lemma av3 : a 3 = 49 := by
  rw [val 1]; simp only [hu1]; decide +kernel

set_option maxRecDepth 100000 in
lemma av4 : a 4 = 92 := by
  rw [val 2]; simp only [hu2]; decide +kernel

set_option maxRecDepth 100000 in
lemma av5 : a 5 = 155 := by
  rw [val 3]; simp only [hu3]; decide +kernel

set_option maxRecDepth 100000 in
lemma av6 : a 6 = 242 := by
  rw [val 4]; simp only [hu4]; decide +kernel

lemma recur (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  rcases (show n < 7 ∨ 7 ≤ n by omega) with h | h
  · interval_cases n <;> norm_num [av1, av2, av3, av4, av5, av6]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega]
    exact arec k

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n - 1) else 0 := by
  rw [← ps, pow_one]

open PowerSeries in
lemma gfC : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 4 =
    PowerSeries.C (7:ℚ) * X - PowerSeries.C (6:ℚ) * X ^ 2 + PowerSeries.C (3:ℚ) * X ^ 3 := by
  rw [show ((1 - PowerSeries.X) ^ 4 : PowerSeries ℚ) =
      1 - PowerSeries.C (4:ℚ) * X + PowerSeries.C (6:ℚ) * X ^ 2 - PowerSeries.C (4:ℚ) * X ^ 3 + X ^ 4 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, map_neg, mul_neg, mul_left_comm _ (PowerSeries.C _),
    PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  rcases (show n ≤ 4 ∨ 5 ≤ n by omega) with h | h
  · interval_cases n <;> simp [av1, av2, av3, av4] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have hq : (a (m + 5) : ℚ) = 4 * a (m + 4) - 6 * a (m + 3) + 4 * a (m + 2) - a (m + 1) := by
      have := recur (m + 5) (by omega)
      rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega] at this
      exact_mod_cast this
    simp [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega]
    rw [hq]; ring

def pc (n : ℕ) : ℚ := (2 / 3) * (n : ℚ) ^ 3 + 2 * (n : ℚ) ^ 2 + (13 / 3) * (n : ℚ)

lemma closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = pc n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n ≤ 4 ∨ 5 ≤ n by omega) with h | h
    · interval_cases n <;> norm_num [pc, av1, av2, av3, av4, av5, av6]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      have hr := recur (m + 5) (by omega)
      rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega] at hr
      have hq : (a (m + 5) : ℚ) = 4 * a (m + 4) - 6 * a (m + 3) + 4 * a (m + 2) - a (m + 1) := by exact_mod_cast hr
      rw [hq, ih (m + 4) (by omega) (by omega), ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega)]
      simp only [pc]; push_cast; ring

end OMA.P_oeis_a224141

open PowerSeries Finset in
open OMA.S_oeis_a224141 OMA.P_oeis_a224141 in
theorem OMA.solution : type_of% @OMA.S_oeis_a224141.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => closed n hn⟩
  · have := recur n (by omega)
    push_cast at this ⊢
    linarith
  · unfold G
    rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp), gfC]
    simp only [map_ofNat]; ring
