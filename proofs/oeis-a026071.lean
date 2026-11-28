import OMAStatements.S_oeis_a026071
import Mathlib

namespace WK

/-- Centred trinomial coefficients: `T n k` is the coefficient of `x^k` in `(1/x + 1 + x)^n`. -/
def T : ℕ → ℤ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => T n (k - 1) + T n k + T n (k + 1)

theorem T_zero (k : ℤ) : T 0 k = if k = 0 then 1 else 0 := by
  rw [T]

theorem T_succ' (n n' : ℕ) (k km kp : ℤ) (hn : n' = n + 1) (hm : km = k - 1) (hp : kp = k + 1) :
    T n' k = T n km + T n k + T n kp := by
  subst hn hm hp
  rw [T]

theorem T_symm (n : ℕ) : ∀ k : ℤ, T n (-k) = T n k := by
  induction n with
  | zero =>
    intro k
    simp only [T_zero, neg_eq_zero]
  | succ n ih =>
    intro k
    rw [T_succ' n (n + 1) (-k) (-(k + 1)) (-(k - 1)) rfl (by ring) (by ring),
      T_succ' n (n + 1) k (k - 1) (k + 1) rfl rfl rfl, ih, ih, ih]
    ring

/-- The three-term relation in `k` (from `f' (1 + x + x^2) = n (1 + 2x) f`). -/
theorem R (n : ℕ) : ∀ k km kp : ℤ, km = k - 1 → kp = k + 1 →
    (k + n + 1) * T n kp + k * T n k + (k - n - 1) * T n km = 0 := by
  induction n with
  | zero =>
    intro k km kp hm hp
    subst hm hp
    simp only [T_zero]
    by_cases h0 : k = 0
    · subst h0
      simp
    · by_cases h1 : k = 1
      · subst h1
        simp
      · by_cases h2 : k = -1
        · subst h2
          simp
        · have a1 : ¬ (k + 1 = 0) := by omega
          have a2 : ¬ (k - 1 = 0) := by omega
          simp [h0, a1, a2]
  | succ n ih =>
    intro k km kp hm hp
    subst hm hp
    have e1 := T_succ' n (n + 1) (k + 1) k (k + 2) rfl (by ring) (by ring)
    have e2 := T_succ' n (n + 1) k (k - 1) (k + 1) rfl rfl rfl
    have e3 := T_succ' n (n + 1) (k - 1) (k - 2) k rfl (by ring) (by ring)
    have i1 := ih (k + 1) k (k + 2) (by ring) (by ring)
    have i2 := ih k (k - 1) (k + 1) rfl rfl
    have i3 := ih (k - 1) (k - 2) k (by ring) (by ring)
    push_cast
    linear_combination (k + n + 2) * e1 + k * e2 + (k - n - 2) * e3 + i1 + i2 + i3

/-- Walks `s 0 = a, …, s n = h` whose step into index `j` satisfies `P j (s (j-1)) (s j)`. -/
def GW (P : ℕ → ℤ → ℤ → Prop) (a : ℤ) (n : ℕ) (h : ℤ) : Set (Fin (n + 1) → ℤ) :=
  {s | s 0 = a ∧ s (Fin.last n) = h ∧ ∀ i : Fin n, P (i.val + 1) (s i.castSucc) (s i.succ)}

/-- Forget the last entry. -/
def ini (n : ℕ) (s : Fin (n + 2) → ℤ) : Fin (n + 1) → ℤ := fun i => s i.castSucc

/-- The walks ending at `x` that may be extended by a step to `h`. -/
def B (P : ℕ → ℤ → ℤ → Prop) (a : ℤ) (n : ℕ) (h x : ℤ) : Set (Fin (n + 1) → ℤ) :=
  {s | P (n + 1) x h ∧ s ∈ GW P a n x}

open Classical in
/-- `v` if `Q` holds, else `0`. -/
noncomputable def sel (Q : Prop) (v : ℤ) : ℤ := if Q then v else 0

theorem sel_pos {Q : Prop} (hQ : Q) (v : ℤ) : sel Q v = v := by
  unfold sel
  simp [hQ]

theorem sel_neg {Q : Prop} (hQ : ¬ Q) (v : ℤ) : sel Q v = 0 := by
  unfold sel
  simp [hQ]

theorem GW_zero_self (P : ℕ → ℤ → ℤ → Prop) (a : ℤ) : ((GW P a 0 a).ncard : ℤ) = 1 := by
  have : GW P a 0 a = {fun _ => a} := by
    ext s
    simp only [GW, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h0, -, -⟩
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact h0
    · rintro rfl
      exact ⟨rfl, rfl, fun i => i.elim0⟩
  rw [this, Set.ncard_singleton]
  norm_num

theorem GW_zero_ne (P : ℕ → ℤ → ℤ → Prop) (a h : ℤ) (hh : h ≠ a) : ((GW P a 0 h).ncard : ℤ) = 0 := by
  have : GW P a 0 h = ∅ := by
    ext s
    simp only [GW, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h0, hl, -⟩
    apply hh
    rw [← hl, ← h0]
    rfl
  rw [this, Set.ncard_empty]
  norm_num

theorem GW_image (P : ℕ → ℤ → ℤ → Prop) (a : ℤ) (n : ℕ) (h : ℤ) :
    ini n '' GW P a (n + 1) h = {s | ∃ x, P (n + 1) x h ∧ s ∈ GW P a n x} := by
  ext s
  simp only [Set.mem_image, Set.mem_ofPred_eq, GW]
  constructor
  · rintro ⟨t, ⟨t0, tl, tP⟩, rfl⟩
    refine ⟨t (Fin.last n).castSucc, ?_, ?_, rfl, ?_⟩
    · simpa [tl] using tP (Fin.last n)
    · simpa [ini] using t0
    · intro i
      have h1 := tP i.castSucc
      rw [Fin.succ_castSucc] at h1
      simpa [ini] using h1
  · rintro ⟨x, hPx, s0, sl, sP⟩
    refine ⟨Fin.snoc (α := fun _ => ℤ) s h, ⟨?_, ?_, ?_⟩, ?_⟩
    · have e : (0 : Fin (n + 2)) = Fin.castSucc (0 : Fin (n + 1)) := rfl
      rw [e, Fin.snoc_castSucc]
      exact s0
    · exact Fin.snoc_last _ _
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [sl] using hPx
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        simpa using sP j
    · funext i
      simp [ini]

theorem GW_injOn (P : ℕ → ℤ → ℤ → Prop) (a : ℤ) (n : ℕ) (h : ℤ) :
    Set.InjOn (ini n) (GW P a (n + 1) h) := by
  rintro s ⟨-, hs, -⟩ t ⟨-, ht, -⟩ hst
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [hs, ht]
  · exact congrFun hst j

theorem GW_image3 (P : ℕ → ℤ → ℤ → Prop) (a : ℤ)
    (hP : ∀ j x y, P j x y → y = x - 1 ∨ y = x ∨ y = x + 1) (n : ℕ) (h : ℤ) :
    ini n '' GW P a (n + 1) h = B P a n h (h - 1) ∪ B P a n h h ∪ B P a n h (h + 1) := by
  rw [GW_image]
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_union, B]
  constructor
  · rintro ⟨x, hx, hs⟩
    rcases hP _ _ _ hx with e | e | e
    · have e' : x = h + 1 := by omega
      subst e'
      exact Or.inr ⟨hx, hs⟩
    · have e' : x = h := e.symm
      subst e'
      exact Or.inl (Or.inr ⟨hx, hs⟩)
    · have e' : x = h - 1 := by omega
      subst e'
      exact Or.inl (Or.inl ⟨hx, hs⟩)
  · rintro ((⟨hx, hs⟩ | ⟨hx, hs⟩) | ⟨hx, hs⟩)
    · exact ⟨_, hx, hs⟩
    · exact ⟨_, hx, hs⟩
    · exact ⟨_, hx, hs⟩

theorem GW_finite (P : ℕ → ℤ → ℤ → Prop) (a : ℤ)
    (hP : ∀ j x y, P j x y → y = x - 1 ∨ y = x ∨ y = x + 1) : ∀ (n : ℕ) (h : ℤ), (GW P a n h).Finite := by
  intro n
  induction n with
  | zero =>
    intro h
    refine (Set.finite_singleton (fun _ : Fin 1 => a)).subset ?_
    rintro s ⟨s0, -, -⟩
    rw [Set.mem_singleton_iff]
    funext i
    rw [Subsingleton.elim i 0]
    exact s0
  | succ n ih =>
    intro h
    refine Set.Finite.of_finite_image ?_ (GW_injOn P a n h)
    rw [GW_image3 P a hP n h]
    exact (((ih (h - 1)).subset (fun s hs => hs.2)).union ((ih h).subset (fun s hs => hs.2))).union
      ((ih (h + 1)).subset (fun s hs => hs.2))

theorem B_card (P : ℕ → ℤ → ℤ → Prop) (a : ℤ) (n : ℕ) (h x : ℤ) :
    ((B P a n h x).ncard : ℤ) = sel (P (n + 1) x h) ((GW P a n x).ncard : ℤ) := by
  by_cases hQ : P (n + 1) x h
  · rw [sel_pos hQ]
    have e : B P a n h x = GW P a n x := by
      ext s
      simp only [B, Set.mem_ofPred_eq]
      exact ⟨fun hh => hh.2, fun hh => ⟨hQ, hh⟩⟩
    rw [e]
  · rw [sel_neg hQ]
    have e : B P a n h x = ∅ := by
      ext s
      simp only [B, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hh => hQ hh.1
    rw [e, Set.ncard_empty]
    norm_num

/-- The transfer step: a walk of length `n + 1` is a walk of length `n` plus one allowed step. -/
theorem GW_succ (P : ℕ → ℤ → ℤ → Prop) (a : ℤ)
    (hP : ∀ j x y, P j x y → y = x - 1 ∨ y = x ∨ y = x + 1) (n : ℕ) (h : ℤ) :
    ((GW P a (n + 1) h).ncard : ℤ) =
      sel (P (n + 1) (h - 1) h) ((GW P a n (h - 1)).ncard : ℤ) + sel (P (n + 1) h h) ((GW P a n h).ncard : ℤ) +
        sel (P (n + 1) (h + 1) h) ((GW P a n (h + 1)).ncard : ℤ) := by
  rw [← Set.InjOn.ncard_image (GW_injOn P a n h), GW_image3 P a hP n h]
  have f1 : (B P a n h (h - 1)).Finite := (GW_finite P a hP n (h - 1)).subset (fun s hs => hs.2)
  have f2 : (B P a n h h).Finite := (GW_finite P a hP n h).subset (fun s hs => hs.2)
  have f3 : (B P a n h (h + 1)).Finite := (GW_finite P a hP n (h + 1)).subset (fun s hs => hs.2)
  have d12 : Disjoint (B P a n h (h - 1)) (B P a n h h) := by
    rw [Set.disjoint_left]
    rintro s ⟨-, -, hl, -⟩ ⟨-, -, hl', -⟩
    linarith
  have d3 : Disjoint (B P a n h (h - 1) ∪ B P a n h h) (B P a n h (h + 1)) := by
    rw [Set.disjoint_left]
    rintro s (⟨-, -, hl, -⟩ | ⟨-, -, hl, -⟩) ⟨-, -, hl', -⟩
    · linarith
    · linarith
  rw [Set.ncard_union_eq d3 (f1.union f2) f3, Set.ncard_union_eq d12 f1 f2]
  push_cast
  rw [B_card, B_card, B_card]

theorem GW_zero (P : ℕ → ℤ → ℤ → Prop) (a h : ℤ) : ((GW P a 0 h).ncard : ℤ) = T 0 (h - a) := by
  rw [T_zero]
  by_cases e : h = a
  · subst e
    rw [GW_zero_self]
    simp
  · have e' : ¬ (h - a = 0) := by omega
    rw [GW_zero_ne _ _ _ e, if_neg e']

/-- A walk on the natural numbers, read as an integer walk. -/
def up (n : ℕ) (s : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ := fun i => (s i : ℤ)

theorem up_inj (n : ℕ) : Function.Injective (up n) := by
  intro s t hst
  funext i
  have h := congrFun hst i
  simp only [up] at h
  omega

end WK

namespace A026071
open WK

/-- Steps `-1, 0, 1`; the first two steps are not `0`. -/
def P4 : ℕ → ℤ → ℤ → Prop := fun j x y => (y = x - 1 ∨ y = x ∨ y = x + 1) ∧ (j ≤ 2 → y ≠ x)

theorem hP4 : ∀ j x y, P4 j x y → y = x - 1 ∨ y = x ∨ y = x + 1 := fun _ _ _ h => h.1

theorem bridge (n : ℕ) : OMA.S_oeis_a026071.walks n = GW P4 0 n 4 := by
  ext s
  simp only [OMA.S_oeis_a026071.walks, Set.mem_ofPred_eq, GW, P4]
  constructor
  · rintro ⟨h0, hl, h1, hst⟩
    refine ⟨h0 0 rfl, hl (Fin.last n) (Fin.val_last n), ?_⟩
    intro i
    by_cases hi : i.val + 1 ≤ 2
    · have h2 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp (h1 i.castSucc i.succ (by simp) (by rw [Fin.val_succ]; omega))
      refine ⟨by omega, fun _ => by omega⟩
    · have h2 := abs_le.mp (hst i.castSucc i.succ (by simp) (by rw [Fin.val_succ]; omega))
      refine ⟨by omega, fun h => absurd h hi⟩
  · rintro ⟨t0, tl, tP⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      have e : i = 0 := Fin.ext (by simpa using hi)
      subst e
      exact t0
    · intro i hi
      have e : i = Fin.last n := Fin.ext (by simpa using hi)
      subst e
      exact tl
    · intro i j hij hj2
      have hj := j.isLt
      have hi : i.val < n := by omega
      have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext (by simp)
      have e2 : j = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simpa using hij)
      obtain ⟨h3, h4⟩ := tP ⟨i.val, hi⟩
      have h5 := h4 (by show i.val + 1 ≤ 2; omega)
      rw [← e1, ← e2] at h3 h5
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
      omega
    · intro i j hij _
      have hj := j.isLt
      have hi : i.val < n := by omega
      have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext (by simp)
      have e2 : j = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simpa using hij)
      have h1 := (tP ⟨i.val, hi⟩).1
      rw [← e1, ← e2] at h1
      exact abs_le.mpr ⟨by omega, by omega⟩

theorem T0_congr (a b : ℤ) (h : a = b) : T 0 a = T 0 b := by rw [h]

theorem one (h : ℤ) : ((GW P4 0 (0 + 1) h).ncard : ℤ) = T 0 (h - 1) + T 0 (h + 1) := by
  have q1 : P4 (0 + 1) (h - 1) h := ⟨by omega, fun _ => by omega⟩
  have q2 : ¬ P4 (0 + 1) h h := fun hq => hq.2 (by norm_num) rfl
  have q3 : P4 (0 + 1) (h + 1) h := ⟨by omega, fun _ => by omega⟩
  rw [GW_succ P4 0 hP4 0 h, sel_pos q1, sel_neg q2, sel_pos q3, GW_zero, GW_zero,
    T0_congr (h - 1 - 0) (h - 1) (by ring), T0_congr (h + 1 - 0) (h + 1) (by ring)]
  ring

/-- Walks after the two forced steps: from `-2`, `0` (twice) and `2`. -/
def G (n : ℕ) (h : ℤ) : ℤ := T n (h + 2) + 2 * T n h + T n (h - 2)

theorem G_succ (n : ℕ) (h hm hp : ℤ) (e1 : hm = h - 1) (e2 : hp = h + 1) :
    G (n + 1) h = G n hm + G n h + G n hp := by
  subst e1 e2
  unfold G
  rw [T_succ' n (n + 1) h (h - 1) (h + 1) rfl rfl rfl,
    T_succ' n (n + 1) (h + 2) (h - 1 + 2) (h + 1 + 2) rfl (by ring) (by ring),
    T_succ' n (n + 1) (h - 2) (h - 1 - 2) (h + 1 - 2) rfl (by ring) (by ring)]
  ring

theorem cnt_eq : ∀ (m : ℕ) (h : ℤ), ((GW P4 0 (m + 1 + 1) h).ncard : ℤ) = G m h := by
  intro m
  induction m with
  | zero =>
    intro h
    have q1 : P4 (0 + 1 + 1) (h - 1) h := ⟨by omega, fun _ => by omega⟩
    have q2 : ¬ P4 (0 + 1 + 1) h h := fun hq => hq.2 (by norm_num) rfl
    have q3 : P4 (0 + 1 + 1) (h + 1) h := ⟨by omega, fun _ => by omega⟩
    rw [GW_succ P4 0 hP4 (0 + 1) h, sel_pos q1, sel_neg q2, sel_pos q3, one, one]
    unfold G
    rw [T0_congr (h - 1 - 1) (h - 2) (by ring), T0_congr (h - 1 + 1) h (by ring),
      T0_congr (h + 1 - 1) h (by ring), T0_congr (h + 1 + 1) (h + 2) (by ring)]
    ring
  | succ m ih =>
    intro h
    have q1 : P4 (m + 1 + 1 + 1) (h - 1) h := ⟨by omega, fun _ => by omega⟩
    have q2 : P4 (m + 1 + 1 + 1) h h := ⟨by omega, fun hq => by omega⟩
    have q3 : P4 (m + 1 + 1 + 1) (h + 1) h := ⟨by omega, fun _ => by omega⟩
    rw [GW_succ P4 0 hP4 (m + 1 + 1) h, sel_pos q1, sel_pos q2, sel_pos q3, ih, ih, ih,
      G_succ m h (h - 1) (h + 1) rfl rfl]

theorem a_eq (m : ℕ) : OMA.S_oeis_a026071.a (m + 2) = T m 6 + 2 * T m 4 + T m 2 := by
  have e := cnt_eq m 4
  rw [← bridge] at e
  unfold OMA.S_oeis_a026071.a
  rw [show m + 2 = m + 1 + 1 from rfl, e, G]
  norm_num

end A026071

theorem OMA.solution : type_of% @OMA.S_oeis_a026071.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have s1 : m + 6 - 1 = m + 5 := by omega
  have s2 : m + 6 - 2 = m + 4 := by omega
  have s3 : m + 6 - 3 = m + 3 := by omega
  have s4 : m + 6 - 4 = m + 2 := by omega
  rw [s1, s2, s3, s4]
  have a6 : OMA.S_oeis_a026071.a (m + 6) = WK.T (m + 4) 6 + 2 * WK.T (m + 4) 4 + WK.T (m + 4) 2 := A026071.a_eq (m + 4)
  have a5 : OMA.S_oeis_a026071.a (m + 5) = WK.T (m + 3) 6 + 2 * WK.T (m + 3) 4 + WK.T (m + 3) 2 := A026071.a_eq (m + 3)
  have a4 : OMA.S_oeis_a026071.a (m + 4) = WK.T (m + 2) 6 + 2 * WK.T (m + 2) 4 + WK.T (m + 2) 2 := A026071.a_eq (m + 2)
  have a3 : OMA.S_oeis_a026071.a (m + 3) = WK.T (m + 1) 6 + 2 * WK.T (m + 1) 4 + WK.T (m + 1) 2 := A026071.a_eq (m + 1)
  have a2 : OMA.S_oeis_a026071.a (m + 2) = WK.T m 6 + 2 * WK.T m 4 + WK.T m 2 := A026071.a_eq m
  rw [a6, a5, a4, a3, a2]
  push_cast
  have p3_2 := WK.T_succ' (m + 3) (m + 4) (2:ℤ) (1:ℤ) (3:ℤ) rfl (by norm_num) (by norm_num)
  have p3_4 := WK.T_succ' (m + 3) (m + 4) (4:ℤ) (3:ℤ) (5:ℤ) rfl (by norm_num) (by norm_num)
  have p3_6 := WK.T_succ' (m + 3) (m + 4) (6:ℤ) (5:ℤ) (7:ℤ) rfl (by norm_num) (by norm_num)
  have p2_1 := WK.T_succ' (m + 2) (m + 3) (1:ℤ) (0:ℤ) (2:ℤ) rfl (by norm_num) (by norm_num)
  have p2_2 := WK.T_succ' (m + 2) (m + 3) (2:ℤ) (1:ℤ) (3:ℤ) rfl (by norm_num) (by norm_num)
  have p2_3 := WK.T_succ' (m + 2) (m + 3) (3:ℤ) (2:ℤ) (4:ℤ) rfl (by norm_num) (by norm_num)
  have p2_4 := WK.T_succ' (m + 2) (m + 3) (4:ℤ) (3:ℤ) (5:ℤ) rfl (by norm_num) (by norm_num)
  have p2_5 := WK.T_succ' (m + 2) (m + 3) (5:ℤ) (4:ℤ) (6:ℤ) rfl (by norm_num) (by norm_num)
  have p2_6 := WK.T_succ' (m + 2) (m + 3) (6:ℤ) (5:ℤ) (7:ℤ) rfl (by norm_num) (by norm_num)
  have p2_7 := WK.T_succ' (m + 2) (m + 3) (7:ℤ) (6:ℤ) (8:ℤ) rfl (by norm_num) (by norm_num)
  have p1_0 := WK.T_succ' (m + 1) (m + 2) (0:ℤ) (-1:ℤ) (1:ℤ) rfl (by norm_num) (by norm_num)
  have p1_1 := WK.T_succ' (m + 1) (m + 2) (1:ℤ) (0:ℤ) (2:ℤ) rfl (by norm_num) (by norm_num)
  have p1_2 := WK.T_succ' (m + 1) (m + 2) (2:ℤ) (1:ℤ) (3:ℤ) rfl (by norm_num) (by norm_num)
  have p1_3 := WK.T_succ' (m + 1) (m + 2) (3:ℤ) (2:ℤ) (4:ℤ) rfl (by norm_num) (by norm_num)
  have p1_4 := WK.T_succ' (m + 1) (m + 2) (4:ℤ) (3:ℤ) (5:ℤ) rfl (by norm_num) (by norm_num)
  have p1_5 := WK.T_succ' (m + 1) (m + 2) (5:ℤ) (4:ℤ) (6:ℤ) rfl (by norm_num) (by norm_num)
  have p1_6 := WK.T_succ' (m + 1) (m + 2) (6:ℤ) (5:ℤ) (7:ℤ) rfl (by norm_num) (by norm_num)
  have p1_7 := WK.T_succ' (m + 1) (m + 2) (7:ℤ) (6:ℤ) (8:ℤ) rfl (by norm_num) (by norm_num)
  have p1_8 := WK.T_succ' (m + 1) (m + 2) (8:ℤ) (7:ℤ) (9:ℤ) rfl (by norm_num) (by norm_num)
  have p0_n1 := WK.T_succ' m (m + 1) (-1:ℤ) (-2:ℤ) (0:ℤ) rfl (by norm_num) (by norm_num)
  have p0_0 := WK.T_succ' m (m + 1) (0:ℤ) (-1:ℤ) (1:ℤ) rfl (by norm_num) (by norm_num)
  have p0_1 := WK.T_succ' m (m + 1) (1:ℤ) (0:ℤ) (2:ℤ) rfl (by norm_num) (by norm_num)
  have p0_2 := WK.T_succ' m (m + 1) (2:ℤ) (1:ℤ) (3:ℤ) rfl (by norm_num) (by norm_num)
  have p0_3 := WK.T_succ' m (m + 1) (3:ℤ) (2:ℤ) (4:ℤ) rfl (by norm_num) (by norm_num)
  have p0_4 := WK.T_succ' m (m + 1) (4:ℤ) (3:ℤ) (5:ℤ) rfl (by norm_num) (by norm_num)
  have p0_5 := WK.T_succ' m (m + 1) (5:ℤ) (4:ℤ) (6:ℤ) rfl (by norm_num) (by norm_num)
  have p0_6 := WK.T_succ' m (m + 1) (6:ℤ) (5:ℤ) (7:ℤ) rfl (by norm_num) (by norm_num)
  have p0_7 := WK.T_succ' m (m + 1) (7:ℤ) (6:ℤ) (8:ℤ) rfl (by norm_num) (by norm_num)
  have p0_8 := WK.T_succ' m (m + 1) (8:ℤ) (7:ℤ) (9:ℤ) rfl (by norm_num) (by norm_num)
  have p0_9 := WK.T_succ' m (m + 1) (9:ℤ) (8:ℤ) (10:ℤ) rfl (by norm_num) (by norm_num)
  have r_9 := WK.R m (9:ℤ) (8:ℤ) (10:ℤ) (by norm_num) (by norm_num)
  have r_7 := WK.R m (7:ℤ) (6:ℤ) (8:ℤ) (by norm_num) (by norm_num)
  have r_6 := WK.R m (6:ℤ) (5:ℤ) (7:ℤ) (by norm_num) (by norm_num)
  have r_5 := WK.R m (5:ℤ) (4:ℤ) (6:ℤ) (by norm_num) (by norm_num)
  have r_4 := WK.R m (4:ℤ) (3:ℤ) (5:ℤ) (by norm_num) (by norm_num)
  have r_3 := WK.R m (3:ℤ) (2:ℤ) (4:ℤ) (by norm_num) (by norm_num)
  have r_2 := WK.R m (2:ℤ) (1:ℤ) (3:ℤ) (by norm_num) (by norm_num)
  have r_1 := WK.R m (1:ℤ) (0:ℤ) (2:ℤ) (by norm_num) (by norm_num)
  have r_0 := WK.R m (0:ℤ) (-1:ℤ) (1:ℤ) (by norm_num) (by norm_num)
  have r_n1 := WK.R m (-1:ℤ) (-2:ℤ) (0:ℤ) (by norm_num) (by norm_num)
  linear_combination (-(m:ℤ)^2 - 12*(m:ℤ) - 20) * p3_2 + (-2*(m:ℤ)^2 - 24*(m:ℤ) - 40) * p3_4 + (-(m:ℤ)^2 - 12*(m:ℤ) - 20) * p3_6 + (-(m:ℤ)^2 - 12*(m:ℤ) - 20) * p2_1 + (3*(m:ℤ)^2 + 27*(m:ℤ) + 42) * p2_2 + (-3*(m:ℤ)^2 - 36*(m:ℤ) - 60) * p2_3 + (6*(m:ℤ)^2 + 54*(m:ℤ) + 84) * p2_4 + (-3*(m:ℤ)^2 - 36*(m:ℤ) - 60) * p2_5 + (3*(m:ℤ)^2 + 27*(m:ℤ) + 42) * p2_6 + (-(m:ℤ)^2 - 12*(m:ℤ) - 20) * p2_7 + (-(m:ℤ)^2 - 12*(m:ℤ) - 20) * p1_0 + (2*(m:ℤ)^2 + 15*(m:ℤ) + 22) * p1_1 + (-3*(m:ℤ)^2 - 22*(m:ℤ) + 16) * p1_2 + (6*(m:ℤ)^2 + 45*(m:ℤ) + 66) * p1_3 + (-4*(m:ℤ)^2 - 20*(m:ℤ) + 72) * p1_4 + (6*(m:ℤ)^2 + 45*(m:ℤ) + 66) * p1_5 + (-3*(m:ℤ)^2 - 22*(m:ℤ) + 16) * p1_6 + (2*(m:ℤ)^2 + 15*(m:ℤ) + 22) * p1_7 + (-(m:ℤ)^2 - 12*(m:ℤ) - 20) * p1_8 + (-(m:ℤ)^2 - 12*(m:ℤ) - 20) * p0_n1 + ((m:ℤ)^2 + 3*(m:ℤ) + 2) * p0_0 + (-2*(m:ℤ)^2 - 19*(m:ℤ) + 18) * p0_1 + ((m:ℤ)^2 + 3*(m:ℤ) + 50) * p0_2 + (-(m:ℤ)^2 + 3*(m:ℤ) + 154) * p0_3 + (96) * p0_4 + (-(m:ℤ)^2 + 3*(m:ℤ) + 154) * p0_5 + ((m:ℤ)^2 + 3*(m:ℤ) + 50) * p0_6 + (-2*(m:ℤ)^2 - 19*(m:ℤ) + 18) * p0_7 + ((m:ℤ)^2 + 3*(m:ℤ) + 2) * p0_8 + (-(m:ℤ)^2 - 12*(m:ℤ) - 20) * p0_9 + (-(m:ℤ) - 2) * r_9 + (2 - 3*(m:ℤ)) * r_7 + (8) * r_6 + (28 - 2*(m:ℤ)) * r_5 + (24) * r_4 + (2*(m:ℤ) + 52) * r_3 + (24) * r_2 + (3*(m:ℤ) + 38) * r_1 + (8) * r_0 + ((m:ℤ) + 10) * r_n1
