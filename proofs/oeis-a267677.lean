import OMAStatements.S_oeis_a267677

-- Problem: oeis-a267677
-- The automaton row is shown equal to an explicit pattern (left front, centre, right front, periodic bulk)
-- by a finite kernel check on a window of representatives; counts follow by a shift argument.

namespace OMA.CA1

def ruleG (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

def cellG (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleG rule (cellG rule t (i - 1)) (cellG rule t i) (cellG rule t (i + 1))

def clampZ (lo hi x : ℤ) : ℤ := max lo (min hi x)

def earlyG (W : ℕ) (E : List (List Bool)) (bgl : List Bool) (t : ℕ) (i : ℤ) : Bool :=
  if -((W : ℤ) + 1) ≤ i ∧ i ≤ (W : ℤ) + 1 then
    ((E.getD t []).getD (i + ((W : ℤ) + 1)).toNat false)
  else bgl.getD t false

def lateG (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ) (i : ℤ) : Bool :=
  ((((G.getD (t % 2) []).getD (clampZ (-2) C (i + t) + 2).toNat []).getD
    (clampZ (-(C : ℤ)) C i + C).toNat []).getD (clampZ (-2) C ((t : ℤ) - i) + 2).toNat []).getD
    (i % 2).toNat false

def patG (W C : ℕ) (E : List (List Bool)) (bgl : List Bool)
    (G : List (List (List (List (List Bool))))) (t : ℕ) (i : ℤ) : Bool :=
  if t ≤ W then earlyG W E bgl t i else lateG C G t i

theorem lateG_congr (C : ℕ) (G : List (List (List (List (List Bool))))) (t t' : ℕ) (i i' : ℤ)
    (h1 : t % 2 = t' % 2)
    (h2 : clampZ (-2) C (i + t) = clampZ (-2) C (i' + t'))
    (h3 : clampZ (-(C : ℤ)) C i = clampZ (-(C : ℤ)) C i')
    (h4 : clampZ (-2) C ((t : ℤ) - i) = clampZ (-2) C ((t' : ℤ) - i'))
    (h5 : i % 2 = i' % 2) : lateG C G t i = lateG C G t' i' := by
  unfold lateG
  rw [h1, h2, h3, h4, h5]

theorem step_transfer (rule C : ℕ) (G : List (List (List (List (List Bool))))) (t t' : ℕ)
    (i i' : ℤ) (hp : t % 2 = t' % 2) (hi : i % 2 = i' % 2)
    (hl : ∀ d : ℤ, -1 ≤ d → d ≤ 1 →
      clampZ (-2) C (i + t + d) = clampZ (-2) C (i' + t' + d))
    (hc : ∀ d : ℤ, -1 ≤ d → d ≤ 1 →
      clampZ (-(C : ℤ)) C (i + d) = clampZ (-(C : ℤ)) C (i' + d))
    (hr : ∀ d : ℤ, -1 ≤ d → d ≤ 1 →
      clampZ (-2) C ((t : ℤ) - i + d) = clampZ (-2) C ((t' : ℤ) - i' + d))
    (hs : lateG C G (t' + 1) i' = ruleG rule (lateG C G t' (i' - 1)) (lateG C G t' i')
      (lateG C G t' (i' + 1))) :
    lateG C G (t + 1) i = ruleG rule (lateG C G t (i - 1)) (lateG C G t i)
      (lateG C G t (i + 1)) := by
  have e1 : lateG C G (t + 1) i = lateG C G (t' + 1) i' := by
    refine lateG_congr C G _ _ _ _ (by omega) ?_ ?_ ?_ hi
    · have := hl 1 (by omega) (by omega)
      push_cast
      rw [show i + ((t : ℤ) + 1) = i + t + 1 by ring, show i' + ((t' : ℤ) + 1) = i' + t' + 1 by ring]
      exact this
    · have := hc 0 (by omega) (by omega)
      simpa using this
    · have := hr 1 (by omega) (by omega)
      push_cast
      rw [show (t : ℤ) + 1 - i = t - i + 1 by ring, show (t' : ℤ) + 1 - i' = t' - i' + 1 by ring]
      exact this
  have e2 : lateG C G t (i - 1) = lateG C G t' (i' - 1) := by
    refine lateG_congr C G _ _ _ _ hp ?_ ?_ ?_ (by omega)
    · have := hl (-1) (by omega) (by omega)
      rw [show i - 1 + (t : ℤ) = i + t + -1 by ring, show i' - 1 + (t' : ℤ) = i' + t' + -1 by ring]
      exact this
    · have := hc (-1) (by omega) (by omega)
      rw [show i - 1 = i + -1 by ring, show i' - 1 = i' + -1 by ring]
      exact this
    · have := hr 1 (by omega) (by omega)
      rw [show (t : ℤ) - (i - 1) = t - i + 1 by ring, show (t' : ℤ) - (i' - 1) = t' - i' + 1 by ring]
      exact this
  have e3 : lateG C G t i = lateG C G t' i' := by
    refine lateG_congr C G _ _ _ _ hp ?_ ?_ ?_ hi
    · have := hl 0 (by omega) (by omega)
      simpa using this
    · have := hc 0 (by omega) (by omega)
      simpa using this
    · have := hr 0 (by omega) (by omega)
      simpa using this
  have e4 : lateG C G t (i + 1) = lateG C G t' (i' + 1) := by
    refine lateG_congr C G _ _ _ _ hp ?_ ?_ ?_ (by omega)
    · have := hl 1 (by omega) (by omega)
      rw [show i + 1 + (t : ℤ) = i + t + 1 by ring, show i' + 1 + (t' : ℤ) = i' + t' + 1 by ring]
      exact this
    · exact hc 1 (by omega) (by omega)
    · have := hr (-1) (by omega) (by omega)
      rw [show (t : ℤ) - (i + 1) = t - i + -1 by ring, show (t' : ℤ) - (i' + 1) = t' - i' + -1 by ring]
      exact this
  rw [e1, e2, e3, e4]
  exact hs

theorem late_step (rule C W : ℕ) (G : List (List (List (List (List Bool))))) (hW : 2 * C + 3 ≤ W)
    (hL : ∀ t' ∈ ({W + 1, W + 2} : Finset ℕ), ∀ i' ∈ Finset.Icc (-((t' : ℤ) + 4)) ((t' : ℤ) + 4),
      lateG C G (t' + 1) i' = ruleG rule (lateG C G t' (i' - 1)) (lateG C G t' i')
        (lateG C G t' (i' + 1)))
    (t : ℕ) (ht : W + 1 ≤ t) (i : ℤ) :
    lateG C G (t + 1) i = ruleG rule (lateG C G t (i - 1)) (lateG C G t i)
      (lateG C G t (i + 1)) := by
  obtain ⟨t', ht', hp⟩ : ∃ t' : ℕ, t' ∈ ({W + 1, W + 2} : Finset ℕ) ∧ t % 2 = t' % 2 := by
    rcases Nat.mod_two_eq_zero_or_one (t + W + 1) with h | h
    · exact ⟨W + 1, by simp, by omega⟩
    · exact ⟨W + 2, by simp, by omega⟩
  have ht'' : t' = W + 1 ∨ t' = W + 2 := by simpa using ht'
  have key : ∀ i' : ℤ, -((t' : ℤ) + 4) ≤ i' → i' ≤ (t' : ℤ) + 4 → i % 2 = i' % 2 →
      (∀ d : ℤ, -1 ≤ d → d ≤ 1 → clampZ (-2) C (i + t + d) = clampZ (-2) C (i' + t' + d)) →
      (∀ d : ℤ, -1 ≤ d → d ≤ 1 → clampZ (-(C : ℤ)) C (i + d) = clampZ (-(C : ℤ)) C (i' + d)) →
      (∀ d : ℤ, -1 ≤ d → d ≤ 1 →
        clampZ (-2) C ((t : ℤ) - i + d) = clampZ (-2) C ((t' : ℤ) - i' + d)) →
      lateG C G (t + 1) i = ruleG rule (lateG C G t (i - 1)) (lateG C G t i)
        (lateG C G t (i + 1)) := by
    intro i' h1 h2 hi hl hc hr
    exact step_transfer rule C G t t' i i' hp hi hl hc hr
      (hL t' ht' i' (Finset.mem_Icc.mpr ⟨h1, h2⟩))
  have hz : (i + t ≤ -3) ∨ (-3 < i + t ∧ i + (t : ℤ) ≤ C) ∨ ((C : ℤ) < i + t ∧ i < -(C : ℤ)) ∨
      (-(C : ℤ) ≤ i ∧ i ≤ C) ∨ ((C : ℤ) < i ∧ (C : ℤ) < t - i) ∨
      (-3 < (t : ℤ) - i ∧ (t : ℤ) - i ≤ C) ∨ ((t : ℤ) - i ≤ -3) := by omega
  rcases hz with h | h | h | h | h | h | h
  · refine key (-(t' : ℤ) - 3 - (i + t' + 3) % 2) (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
      (intro d hd1 hd2; unfold clampZ; omega)
  · refine key (i + t - t') (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
      (intro d hd1 hd2; unfold clampZ; omega)
  · refine key (-(C : ℤ) - 1 - (i + C + 1) % 2) (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
      (intro d hd1 hd2; unfold clampZ; omega)
  · refine key i (by omega) (by omega) rfl ?_ ?_ ?_ <;>
      (intro d hd1 hd2; unfold clampZ; omega)
  · refine key ((C : ℤ) + 1 + (i + C + 1) % 2) (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
      (intro d hd1 hd2; unfold clampZ; omega)
  · refine key (i - t + t') (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
      (intro d hd1 hd2; unfold clampZ; omega)
  · refine key ((t' : ℤ) + 3 + (i + t' + 3) % 2) (by omega) (by omega) (by omega) ?_ ?_ ?_ <;>
      (intro d hd1 hd2; unfold clampZ; omega)

end OMA.CA1

namespace OMA.CA1

theorem earlyG_out (W : ℕ) (E : List (List Bool)) (bgl : List Bool) (t : ℕ) (i : ℤ)
    (h : ¬ (-((W : ℤ) + 1) ≤ i ∧ i ≤ (W : ℤ) + 1)) :
    earlyG W E bgl t i = bgl.getD t false := if_neg h

theorem cell_pat (rule W C : ℕ) (E : List (List Bool)) (bgl : List Bool)
    (G : List (List (List (List (List Bool))))) (hW : 2 * C + 3 ≤ W)
    (h0 : ∀ i ∈ Finset.Icc (-((W : ℤ) + 1)) ((W : ℤ) + 1), earlyG W E bgl 0 i = decide (i = 0))
    (hb0 : bgl.getD 0 false = false)
    (hE : ∀ t ∈ Finset.range W, ∀ i ∈ Finset.Icc (-((W : ℤ) + 2)) ((W : ℤ) + 2),
      earlyG W E bgl (t + 1) i = ruleG rule (earlyG W E bgl t (i - 1)) (earlyG W E bgl t i)
        (earlyG W E bgl t (i + 1)))
    (hbg : ∀ t ∈ Finset.range (W + 1), bgl.getD (t + 1) false =
      ruleG rule (bgl.getD t false) (bgl.getD t false) (bgl.getD t false))
    (hT : ∀ i ∈ Finset.Icc (-((W : ℤ) + 5)) ((W : ℤ) + 5),
      lateG C G (W + 1) i = ruleG rule (earlyG W E bgl W (i - 1)) (earlyG W E bgl W i)
        (earlyG W E bgl W (i + 1)))
    (hL : ∀ t' ∈ ({W + 1, W + 2} : Finset ℕ), ∀ i' ∈ Finset.Icc (-((t' : ℤ) + 4)) ((t' : ℤ) + 4),
      lateG C G (t' + 1) i' = ruleG rule (lateG C G t' (i' - 1)) (lateG C G t' i')
        (lateG C G t' (i' + 1))) :
    ∀ (t : ℕ) (i : ℤ), cellG rule t i = patG W C E bgl G t i := by
  intro t
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = patG W C E bgl G 0 i
    unfold patG
    rw [if_pos (Nat.zero_le W)]
    by_cases hb : -((W : ℤ) + 1) ≤ i ∧ i ≤ (W : ℤ) + 1
    · exact (h0 i (Finset.mem_Icc.mpr hb)).symm
    · rw [earlyG_out W E bgl 0 i hb, hb0]
      have : ¬ (i = 0) := by
        rintro rfl
        exact hb ⟨by omega, by omega⟩
      simp [this]
  | succ t ih =>
    intro i
    show ruleG rule (cellG rule t (i - 1)) (cellG rule t i) (cellG rule t (i + 1))
      = patG W C E bgl G (t + 1) i
    rw [ih, ih, ih]
    rcases Nat.lt_trichotomy t W with ht | ht | ht
    · -- early step
      have he : ∀ x : ℤ, patG W C E bgl G t x = earlyG W E bgl t x :=
        fun x => if_pos (by omega : t ≤ W)
      have he' : patG W C E bgl G (t + 1) i = earlyG W E bgl (t + 1) i :=
        if_pos (by omega : t + 1 ≤ W)
      rw [he, he, he, he']
      by_cases hb : -((W : ℤ) + 2) ≤ i ∧ i ≤ (W : ℤ) + 2
      · exact (hE t (Finset.mem_range.mpr ht) i (Finset.mem_Icc.mpr hb)).symm
      · rw [earlyG_out W E bgl t (i - 1) (by omega), earlyG_out W E bgl t i (by omega),
          earlyG_out W E bgl t (i + 1) (by omega), earlyG_out W E bgl (t + 1) i (by omega)]
        exact (hbg t (Finset.mem_range.mpr (by omega))).symm
    · -- transition
      subst ht
      have he : ∀ x : ℤ, patG t C E bgl G t x = earlyG t E bgl t x :=
        fun x => if_pos (le_refl t)
      have he' : patG t C E bgl G (t + 1) i = lateG C G (t + 1) i :=
        if_neg (by omega : ¬ t + 1 ≤ t)
      rw [he, he, he, he']
      by_cases hb : -((t : ℤ) + 5) ≤ i ∧ i ≤ (t : ℤ) + 5
      · exact (hT i (Finset.mem_Icc.mpr hb)).symm
      · rw [earlyG_out t E bgl t (i - 1) (by omega), earlyG_out t E bgl t i (by omega),
          earlyG_out t E bgl t (i + 1) (by omega)]
        have hrep : ∃ i' : ℤ, (-((t : ℤ) + 5) ≤ i' ∧ i' ≤ (t : ℤ) + 5) ∧
            (i' ≤ -((t : ℤ) + 4) ∨ (t : ℤ) + 4 ≤ i') ∧ lateG C G (t + 1) i = lateG C G (t + 1) i' := by
          have hside : i < -((t : ℤ) + 5) ∨ (t : ℤ) + 5 < i := by omega
          rcases hside with hs | hs
          · refine ⟨-((t : ℤ) + 4) - (i + t + 4) % 2, by omega, by omega, ?_⟩
            refine lateG_congr C G _ _ _ _ rfl ?_ ?_ ?_ (by omega) <;>
              (unfold clampZ; push_cast; omega)
          · refine ⟨(t : ℤ) + 4 + (i + t + 4) % 2, by omega, by omega, ?_⟩
            refine lateG_congr C G _ _ _ _ rfl ?_ ?_ ?_ (by omega) <;>
              (unfold clampZ; push_cast; omega)
        obtain ⟨i', hi', hfar, heq⟩ := hrep
        rw [heq, hT i' (Finset.mem_Icc.mpr hi'),
          earlyG_out t E bgl t (i' - 1) (by omega), earlyG_out t E bgl t i' (by omega),
          earlyG_out t E bgl t (i' + 1) (by omega)]
    · -- late step
      have he : ∀ x : ℤ, patG W C E bgl G t x = lateG C G t x :=
        fun x => if_neg (by omega : ¬ t ≤ W)
      have he' : patG W C E bgl G (t + 1) i = lateG C G (t + 1) i :=
        if_neg (by omega : ¬ t + 1 ≤ W)
      rw [he, he, he, he']
      exact (late_step rule C W G hW hL t (by omega) i).symm

def onCountG (rule t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (2 * t + 1), if cellG rule t ((j : ℤ) - t) then 1 else 0

theorem sum_shift (f : ℤ → ℤ) (t : ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), f ((i : ℤ) - t) = ∑ x ∈ Finset.Icc (-(t : ℤ)) t, f x := by
  have himg : Finset.Icc (-(t : ℤ)) t =
      (Finset.range (2 * t + 1)).image (fun i : ℕ => (i : ℤ) - t) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      exact ⟨(x + t).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  simp only at hab
  omega

theorem Icc_split (a b c : ℤ) (h1 : a ≤ b + 1) (h2 : b ≤ c) (F : ℤ → ℤ) :
    ∑ i ∈ Finset.Icc a c, F i = ∑ i ∈ Finset.Icc a b, F i + ∑ i ∈ Finset.Icc (b + 1) c, F i := by
  have hu : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) c) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    omega
  rw [hu, Finset.sum_union hd]

theorem sum_shift2 (a b k : ℤ) (F : ℤ → ℤ) :
    ∑ i ∈ Finset.Icc a b, F (i + k) = ∑ j ∈ Finset.Icc (a + k) (b + k), F j := by
  have himg : Finset.Icc (a + k) (b + k) = (Finset.Icc a b).image (fun i : ℤ => i + k) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro hx
      exact ⟨x - k, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩
      omega
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  simp only at hxy
  omega

theorem Icc_split' (a b b' c : ℤ) (hb : b' = b + 1) (h1 : a ≤ b + 1) (h2 : b ≤ c) (F : ℤ → ℤ) :
    ∑ i ∈ Finset.Icc a c, F i = ∑ i ∈ Finset.Icc a b, F i + ∑ i ∈ Finset.Icc b' c, F i := by
  subst hb
  exact Icc_split a b c h1 h2 F

theorem sum_shift2' (a b k a' b' : ℤ) (ha : a' = a + k) (hb : b' = b + k) (F : ℤ → ℤ) :
    ∑ i ∈ Finset.Icc a b, F (i + k) = ∑ j ∈ Finset.Icc a' b', F j := by
  subst ha hb
  exact sum_shift2 a b k F

theorem sum_pair (a a' : ℤ) (ha : a' = a + 1) (F : ℤ → ℤ) :
    ∑ i ∈ Finset.Icc a a', F i = F a + F a' := by
  subst ha
  rw [Icc_split a a (a + 1) (by omega) (by omega) F, Finset.Icc_self, Finset.Icc_self,
    Finset.sum_singleton, Finset.sum_singleton]

theorem sum_three (f g : ℤ → ℤ) (c t : ℤ) (hc : 0 ≤ c) (ht : c + 2 ≤ t)
    (hLt : ∀ i : ℤ, i ≤ -c - 2 → g i = f (i + 2))
    (hMd : ∀ i : ℤ, -c - 1 ≤ i → i ≤ c + 1 → g i = f i)
    (hRt : ∀ i : ℤ, c + 2 ≤ i → g i = f (i - 2)) :
    ∑ i ∈ Finset.Icc (-(t + 2)) (t + 2), g i
      = ∑ i ∈ Finset.Icc (-t) t, f i + f (-c - 1) + f (-c) + f c + f (c + 1) := by
  have s1 := Icc_split' (-(t + 2)) (-c - 2) (-c - 1) (t + 2) (by ring) (by omega) (by omega) g
  have s2 := Icc_split' (-c - 1) (c + 1) (c + 2) (t + 2) (by ring) (by omega) (by omega) g
  have gL : ∑ i ∈ Finset.Icc (-(t + 2)) (-c - 2), g i
      = ∑ i ∈ Finset.Icc (-(t + 2)) (-c - 2), f (i + 2) :=
    Finset.sum_congr rfl fun i hi => hLt i (Finset.mem_Icc.mp hi).2
  have gM : ∑ i ∈ Finset.Icc (-c - 1) (c + 1), g i = ∑ i ∈ Finset.Icc (-c - 1) (c + 1), f i :=
    Finset.sum_congr rfl fun i hi => hMd i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  have gR : ∑ i ∈ Finset.Icc (c + 2) (t + 2), g i
      = ∑ i ∈ Finset.Icc (c + 2) (t + 2), f (i + -2) :=
    Finset.sum_congr rfl fun i hi => by
      rw [hRt i (Finset.mem_Icc.mp hi).1]
      rfl
  have sL := sum_shift2' (-(t + 2)) (-c - 2) 2 (-t) (-c) (by ring) (by ring) f
  have sR := sum_shift2' (c + 2) (t + 2) (-2) c t (by ring) (by ring) f
  have f1 := Icc_split' (-t) (-c - 2) (-c - 1) t (by ring) (by omega) (by omega) f
  have f2 := Icc_split' (-c - 1) (c + 1) (c + 2) t (by ring) (by omega) (by omega) f
  have f3 := Icc_split' (-t) (-c - 2) (-c - 1) (-c) (by ring) (by omega) (by omega) f
  have f4 := sum_pair (-c - 1) (-c) (by ring) f
  have f5 := Icc_split' c (c + 1) (c + 2) t (by ring) (by omega) (by omega) f
  have f6 := sum_pair c (c + 1) rfl f
  linarith

noncomputable def kap (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ) : ℤ :=
  (if lateG C G t (-(C : ℤ) - 1) then 1 else 0) + (if lateG C G t (-(C : ℤ)) then 1 else 0)
    + (if lateG C G t (C : ℤ) then 1 else 0) + (if lateG C G t ((C : ℤ) + 1) then 1 else 0)

theorem count_step (rule W C : ℕ) (E : List (List Bool)) (bgl : List Bool)
    (G : List (List (List (List (List Bool))))) (hW : 2 * C + 3 ≤ W)
    (hcell : ∀ (t : ℕ) (i : ℤ), cellG rule t i = patG W C E bgl G t i)
    (t t' : ℕ) (ht : W + 1 ≤ t) (ht' : W + 1 ≤ t') (hp : t % 2 = t' % 2) :
    (onCountG rule (t + 2) : ℤ) = onCountG rule t + kap C G t' := by
  have hlate : ∀ (s : ℕ), W + 1 ≤ s → ∀ i : ℤ, cellG rule s i = lateG C G s i := by
    intro s hs i
    rw [hcell, patG, if_neg (by omega)]
  have oc : ∀ s : ℕ, W + 1 ≤ s → (onCountG rule s : ℤ)
      = ∑ x ∈ Finset.Icc (-(s : ℤ)) s, (if lateG C G s x then (1 : ℤ) else 0) := by
    intro s hs
    unfold onCountG
    push_cast
    simp only [hlate s hs]
    exact sum_shift (fun x => if lateG C G s x then (1 : ℤ) else 0) s
  rw [oc (t + 2) (by omega), oc t ht]
  have hk : kap C G t' = kap C G t := by
    unfold kap
    have hx : ∀ x : ℤ, -(C : ℤ) - 1 ≤ x → x ≤ (C : ℤ) + 1 → lateG C G t' x = lateG C G t x := by
      intro x h1 h2
      refine lateG_congr C G _ _ _ _ hp.symm ?_ rfl ?_ rfl <;> (unfold clampZ; omega)
    rw [hx _ (by omega) (by omega), hx _ (by omega) (by omega), hx _ (by omega) (by omega),
      hx _ (by omega) (by omega)]
  rw [hk]
  have h3 := sum_three (fun x => if lateG C G t x then (1 : ℤ) else 0)
    (fun x => if lateG C G (t + 2) x then (1 : ℤ) else 0) (C : ℤ) (t : ℤ) (by omega) (by omega)
    (fun i hi => by
      show (if lateG C G (t + 2) i then (1 : ℤ) else 0) = if lateG C G t (i + 2) then 1 else 0
      rw [lateG_congr C G (t + 2) t i (i + 2) (by omega) (by unfold clampZ; push_cast; omega)
        (by unfold clampZ; omega) (by unfold clampZ; push_cast; omega) (by omega)])
    (fun i h1 h2 => by
      show (if lateG C G (t + 2) i then (1 : ℤ) else 0) = if lateG C G t i then 1 else 0
      rw [lateG_congr C G (t + 2) t i i (by omega) (by unfold clampZ; push_cast; omega)
        rfl (by unfold clampZ; push_cast; omega) rfl])
    (fun i hi => by
      show (if lateG C G (t + 2) i then (1 : ℤ) else 0) = if lateG C G t (i - 2) then 1 else 0
      rw [lateG_congr C G (t + 2) t i (i - 2) (by omega) (by unfold clampZ; push_cast; omega)
        (by unfold clampZ; omega) (by unfold clampZ; push_cast; omega) (by omega)])
  unfold kap
  have e : (((t + 2 : ℕ) : ℤ)) = (t : ℤ) + 2 := by push_cast; ring
  rw [e, h3]
  ring

end OMA.CA1

namespace OMA.CA1

theorem wsumL (f g : ℤ → ℤ) (B c t : ℤ) (hc : 0 ≤ c) (ht : c + 2 ≤ t)
    (hLt : ∀ i : ℤ, i ≤ -c - 2 → g i = f (i + 2)) :
    ∑ x ∈ Finset.Icc (-(t + 2)) (-c - 2), g x * B ^ (t + 2 - x).toNat
      = B ^ 4 * (∑ x ∈ Finset.Icc (-t) (-c - 2), f x * B ^ (t - x).toNat
        + f (-c - 1) * B ^ (t + c + 1).toNat + f (-c) * B ^ (t + c).toNat) := by
  have e1 : ∑ x ∈ Finset.Icc (-(t + 2)) (-c - 2), g x * B ^ (t + 2 - x).toNat
      = ∑ x ∈ Finset.Icc (-(t + 2)) (-c - 2),
        (fun y : ℤ => f y * B ^ (t - y + 4).toNat) (x + 2) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hLt x (Finset.mem_Icc.mp hx).2]
    show f (x + 2) * B ^ (t + 2 - x).toNat = f (x + 2) * B ^ (t - (x + 2) + 4).toNat
    rw [show t - (x + 2) + 4 = t + 2 - x by ring]
  rw [e1, sum_shift2' (-(t + 2)) (-c - 2) 2 (-t) (-c) (by ring) (by ring)
    (fun y : ℤ => f y * B ^ (t - y + 4).toNat)]
  have e2 : ∑ y ∈ Finset.Icc (-t) (-c), f y * B ^ (t - y + 4).toNat
      = ∑ y ∈ Finset.Icc (-t) (-c), B ^ 4 * (f y * B ^ (t - y).toNat) := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have h1 := (Finset.mem_Icc.mp hy).2
    have : (t - y + 4).toNat = (t - y).toNat + 4 := by omega
    rw [this, pow_add]
    ring
  rw [e2, ← Finset.mul_sum,
    Icc_split' (-t) (-c - 2) (-c - 1) (-c) (by ring) (by omega) (by omega)
      (fun y => f y * B ^ (t - y).toNat),
    sum_pair (-c - 1) (-c) (by ring) (fun y => f y * B ^ (t - y).toNat)]
  rw [show t - (-c - 1) = t + c + 1 by ring, show t - -c = t + c by ring]
  ring

theorem wsumM (f g : ℤ → ℤ) (B c t : ℤ) (hc : 0 ≤ c) (ht : c + 2 ≤ t)
    (hMd : ∀ i : ℤ, -c - 1 ≤ i → i ≤ c + 1 → g i = f i) :
    ∑ x ∈ Finset.Icc (-c - 1) (c + 1), g x * B ^ (t + 2 - x).toNat
      = B ^ 2 * ∑ x ∈ Finset.Icc (-c - 1) (c + 1), f x * B ^ (t - x).toNat := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have h1 := (Finset.mem_Icc.mp hx).1
  have h2 := (Finset.mem_Icc.mp hx).2
  rw [hMd x h1 h2]
  have : (t + 2 - x).toNat = (t - x).toNat + 2 := by omega
  rw [this, pow_add]
  ring

theorem wsumR (f g : ℤ → ℤ) (B c t : ℤ) (hc : 0 ≤ c) (ht : c + 2 ≤ t)
    (hRt : ∀ i : ℤ, c + 2 ≤ i → g i = f (i - 2)) :
    ∑ x ∈ Finset.Icc (c + 2) (t + 2), g x * B ^ (t + 2 - x).toNat
      = f c * B ^ (t - c).toNat + f (c + 1) * B ^ (t - c - 1).toNat
        + ∑ x ∈ Finset.Icc (c + 2) t, f x * B ^ (t - x).toNat := by
  have e1 : ∑ x ∈ Finset.Icc (c + 2) (t + 2), g x * B ^ (t + 2 - x).toNat
      = ∑ x ∈ Finset.Icc (c + 2) (t + 2), (fun y : ℤ => f y * B ^ (t - y).toNat) (x + -2) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hRt x (Finset.mem_Icc.mp hx).1]
    show f (x - 2) * B ^ (t + 2 - x).toNat = f (x + -2) * B ^ (t - (x + -2)).toNat
    rw [show t - (x + -2) = t + 2 - x by ring, show x + -2 = x - 2 by ring]
  rw [e1, sum_shift2' (c + 2) (t + 2) (-2) c t (by ring) (by ring)
    (fun y : ℤ => f y * B ^ (t - y).toNat),
    Icc_split' c (c + 1) (c + 2) t (by ring) (by omega) (by omega)
      (fun y => f y * B ^ (t - y).toNat),
    sum_pair c (c + 1) rfl (fun y => f y * B ^ (t - y).toNat)]
  rw [show t - (c + 1) = t - c - 1 by ring]

noncomputable def bitf (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ) (x : ℤ) : ℤ :=
  if lateG C G t x then 1 else 0

noncomputable def LfG (B : ℤ) (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ) : ℤ :=
  ∑ x ∈ Finset.Icc (-(t : ℤ)) (-(C : ℤ) - 2), bitf C G t x * B ^ ((t : ℤ) - x).toNat

noncomputable def MfG (B : ℤ) (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ) : ℤ :=
  ∑ x ∈ Finset.Icc (-(C : ℤ) - 1) ((C : ℤ) + 1), bitf C G t x * B ^ ((t : ℤ) - x).toNat

noncomputable def RfG (B : ℤ) (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ) : ℤ :=
  ∑ x ∈ Finset.Icc ((C : ℤ) + 2) (t : ℤ), bitf C G t x * B ^ ((t : ℤ) - x).toNat

def digitsG (rule : ℕ) (B : ℤ) (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * t + 1), if cellG rule t ((j : ℤ) - t) then B ^ (2 * t - j) else 0

theorem bitf_shiftL (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ)
    (ht : 2 * C + 4 ≤ t) (i : ℤ) (hi : i ≤ -(C : ℤ) - 2) :
    bitf C G (t + 2) i = bitf C G t (i + 2) := by
  unfold bitf
  rw [lateG_congr C G (t + 2) t i (i + 2) (by omega) (by unfold clampZ; push_cast; omega)
    (by unfold clampZ; omega) (by unfold clampZ; push_cast; omega) (by omega)]

theorem bitf_shiftM (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ)
    (ht : 2 * C + 4 ≤ t) (i : ℤ) (h1 : -(C : ℤ) - 1 ≤ i) (h2 : i ≤ (C : ℤ) + 1) :
    bitf C G (t + 2) i = bitf C G t i := by
  unfold bitf
  rw [lateG_congr C G (t + 2) t i i (by omega) (by unfold clampZ; push_cast; omega)
    rfl (by unfold clampZ; push_cast; omega) rfl]

theorem bitf_shiftR (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ)
    (ht : 2 * C + 4 ≤ t) (i : ℤ) (hi : (C : ℤ) + 2 ≤ i) :
    bitf C G (t + 2) i = bitf C G t (i - 2) := by
  unfold bitf
  rw [lateG_congr C G (t + 2) t i (i - 2) (by omega) (by unfold clampZ; push_cast; omega)
    (by unfold clampZ; omega) (by unfold clampZ; push_cast; omega) (by omega)]

theorem bitf_par (C : ℕ) (G : List (List (List (List (List Bool))))) (t t' : ℕ)
    (ht : 2 * C + 4 ≤ t) (ht' : 2 * C + 4 ≤ t') (hp : t % 2 = t' % 2) (x : ℤ)
    (h1 : -(C : ℤ) - 1 ≤ x) (h2 : x ≤ (C : ℤ) + 1) : bitf C G t x = bitf C G t' x := by
  unfold bitf
  rw [lateG_congr C G t t' x x hp (by unfold clampZ; omega) rfl (by unfold clampZ; omega) rfl]

theorem stepL (B : ℤ) (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ)
    (ht : 2 * C + 4 ≤ t) :
    LfG B C G (t + 2) = B ^ 4 * (LfG B C G t + bitf C G t (-(C : ℤ) - 1) * B ^ (t + C + 1)
      + bitf C G t (-(C : ℤ)) * B ^ (t + C)) := by
  have h := wsumL (bitf C G t) (bitf C G (t + 2)) B (C : ℤ) (t : ℤ) (by omega) (by omega)
    (fun i hi => bitf_shiftL C G t ht i hi)
  unfold LfG
  have e : (((t + 2 : ℕ) : ℤ)) = (t : ℤ) + 2 := by push_cast; ring
  rw [e, h]
  have e1 : ((t : ℤ) + C + 1).toNat = t + C + 1 := by omega
  have e2 : ((t : ℤ) + C).toNat = t + C := by omega
  rw [e1, e2]

theorem stepM (B : ℤ) (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ)
    (ht : 2 * C + 4 ≤ t) : MfG B C G (t + 2) = B ^ 2 * MfG B C G t := by
  have h := wsumM (bitf C G t) (bitf C G (t + 2)) B (C : ℤ) (t : ℤ) (by omega) (by omega)
    (fun i h1 h2 => bitf_shiftM C G t ht i h1 h2)
  unfold MfG
  have e : (((t + 2 : ℕ) : ℤ)) = (t : ℤ) + 2 := by push_cast; ring
  rw [e, h]

theorem stepR (B : ℤ) (C : ℕ) (G : List (List (List (List (List Bool))))) (t : ℕ)
    (ht : 2 * C + 4 ≤ t) :
    RfG B C G (t + 2) = bitf C G t (C : ℤ) * B ^ (t - C) + bitf C G t ((C : ℤ) + 1) * B ^ (t - C - 1)
      + RfG B C G t := by
  have h := wsumR (bitf C G t) (bitf C G (t + 2)) B (C : ℤ) (t : ℤ) (by omega) (by omega)
    (fun i hi => bitf_shiftR C G t ht i hi)
  unfold RfG
  have e : (((t + 2 : ℕ) : ℤ)) = (t : ℤ) + 2 := by push_cast; ring
  rw [e, h]
  have e1 : ((t : ℤ) - C).toNat = t - C := by omega
  have e2 : ((t : ℤ) - C - 1).toNat = t - C - 1 := by omega
  rw [e1, e2]

theorem digits_split (rule W C : ℕ) (B : ℤ) (E : List (List Bool)) (bgl : List Bool)
    (G : List (List (List (List (List Bool))))) (hW : 2 * C + 3 ≤ W)
    (hcell : ∀ (t : ℕ) (i : ℤ), cellG rule t i = patG W C E bgl G t i)
    (t : ℕ) (ht : W + 1 ≤ t) :
    digitsG rule B t = LfG B C G t + MfG B C G t + RfG B C G t := by
  have hlate : ∀ i : ℤ, cellG rule t i = lateG C G t i := by
    intro i
    rw [hcell, patG, if_neg (by omega)]
  have e0 : digitsG rule B t = ∑ j ∈ Finset.range (2 * t + 1),
      (fun x : ℤ => bitf C G t x * B ^ ((t : ℤ) - x).toNat) ((j : ℤ) - t) := by
    unfold digitsG
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    show (if cellG rule t ((j : ℤ) - t) then B ^ (2 * t - j) else 0)
      = bitf C G t ((j : ℤ) - t) * B ^ ((t : ℤ) - ((j : ℤ) - t)).toNat
    have : ((t : ℤ) - ((j : ℤ) - t)).toNat = 2 * t - j := by omega
    rw [this, hlate]
    unfold bitf
    split_ifs <;> simp
  rw [e0, sum_shift (fun x : ℤ => bitf C G t x * B ^ ((t : ℤ) - x).toNat) t,
    Icc_split' (-(t : ℤ)) (-(C : ℤ) - 2) (-(C : ℤ) - 1) (t : ℤ) (by ring) (by omega) (by omega),
    Icc_split' (-(C : ℤ) - 1) ((C : ℤ) + 1) ((C : ℤ) + 2) (t : ℤ) (by ring) (by omega) (by omega)]
  unfold LfG MfG RfG
  ring

end OMA.CA1

namespace OMA.P267677
open OMA.CA1 OMA.S_oeis_a267677

def E : List (List Bool) :=
  [[false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false],
   [true, true, true, true, true, true, true, false, true, false, true, true, true, true, true, true, true],
   [true, true, true, true, true, true, true, false, true, false, false, true, true, true, true, true, true],
   [true, true, true, true, true, true, true, false, true, false, false, false, true, true, true, true, true],
   [true, true, true, true, true, true, true, false, true, false, true, false, false, true, true, true, true],
   [true, true, true, true, true, true, true, false, true, false, true, false, false, false, true, true, true],
   [true, true, true, true, true, true, true, false, true, false, true, false, true, false, false, true, true],
   [true, true, true, true, true, true, true, false, true, false, true, false, true, false, false, false, true]]

def bgl : List Bool := [false, true, true, true, true, true, true, true, true, true]

def G : List (List (List (List (List Bool)))) :=
  [[[[[false, false], [false, false], [false, false], [false, false], [true, true]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]]],
    [[[false, false], [false, false], [false, false], [false, false], [false, true]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]]],
    [[[false, false], [false, false], [false, false], [false, false], [true, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]]],
    [[[false, false], [false, false], [false, false], [false, false], [false, true]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]]],
    [[[false, false], [false, false], [false, false], [false, false], [true, true]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [true, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[true, true], [false, true], [false, false], [false, false], [true, false]]]],
   [[[[false, false], [false, false], [false, false], [false, false], [true, true]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]]],
    [[[false, false], [false, false], [false, false], [false, false], [true, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]]],
    [[[false, false], [false, false], [false, false], [false, false], [false, true]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]]],
    [[[false, false], [false, false], [false, false], [false, false], [true, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]]],
    [[[false, false], [false, false], [false, false], [false, false], [true, true]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[false, false], [false, false], [false, false], [false, false], [true, false]], [[false, false], [false, false], [false, false], [false, false], [false, false]], [[true, true], [true, false], [false, false], [false, false], [true, false]]]]]

theorem cellG_eq : ∀ (t : ℕ) (i : ℤ), cell 197 t i = cellG 197 t i := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih => intro i; simp only [cell, cellG, ruleOut, ruleG, ih]

theorem cellG_pat : ∀ (t : ℕ) (i : ℤ), cellG 197 t i = patG 7 2 E bgl G t i :=
  cell_pat 197 7 2 E bgl G (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem cell_eq (t : ℕ) (i : ℤ) : cell 197 t i = patG 7 2 E bgl G t i := by
  rw [cellG_eq]
  exact cellG_pat t i

theorem onCount_eq (t : ℕ) : onCount 197 t = onCountG 197 t := by
  unfold onCount onCountG
  simp only [cellG_eq]

theorem kap0 : kap 2 G 8 = 3 := by decide +kernel

theorem ocb0 : onCount 197 8 = 11 := by
  simp only [onCount, cell_eq]
  decide +kernel

theorem ocstep0 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 0) :
    (onCount 197 (t + 2) : ℤ) = onCount 197 t + 3 := by
  rw [onCount_eq, onCount_eq, count_step 197 7 2 E bgl G (by norm_num) cellG_pat t 8 h (by norm_num) (by omega), kap0]

theorem ock0 (k : ℕ) : (onCount 197 (8 + 2 * k) : ℤ) = 11 + 3 * k := by
  induction k with
  | zero => rw [show 8 + 2 * 0 = 8 from rfl, ocb0]; norm_num
  | succ k ih =>
    rw [show 8 + 2 * (k + 1) = 8 + 2 * k + 2 from by ring, ocstep0 _ (by omega) (by omega), ih]
    push_cast
    ring

theorem ocq0 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 0) :
    ((onCount 197 t : ℕ) : ℚ) = 11 + 3 * (((t : ℚ) - 8) / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = 8 + 2 * k := ⟨(t - 8) / 2, by omega⟩
  have e := ock0 k
  have e' : ((onCount 197 (8 + 2 * k) : ℕ) : ℚ) = 11 + 3 * k := by exact_mod_cast e
  rw [e']
  push_cast
  ring

theorem kap1 : kap 2 G 9 = 3 := by decide +kernel

theorem ocb1 : onCount 197 9 = 12 := by
  simp only [onCount, cell_eq]
  decide +kernel

theorem ocstep1 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 1) :
    (onCount 197 (t + 2) : ℤ) = onCount 197 t + 3 := by
  rw [onCount_eq, onCount_eq, count_step 197 7 2 E bgl G (by norm_num) cellG_pat t 9 h (by norm_num) (by omega), kap1]

theorem ock1 (k : ℕ) : (onCount 197 (9 + 2 * k) : ℤ) = 12 + 3 * k := by
  induction k with
  | zero => rw [show 9 + 2 * 0 = 9 from rfl, ocb1]; norm_num
  | succ k ih =>
    rw [show 9 + 2 * (k + 1) = 9 + 2 * k + 2 from by ring, ocstep1 _ (by omega) (by omega), ih]
    push_cast
    ring

theorem ocq1 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 1) :
    ((onCount 197 t : ℕ) : ℚ) = 12 + 3 * (((t : ℚ) - 9) / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = 9 + 2 * k := ⟨(t - 9) / 2, by omega⟩
  have e := ock1 k
  have e' : ((onCount 197 (9 + 2 * k) : ℕ) : ℚ) = 12 + 3 * k := by exact_mod_cast e
  rw [e']
  push_cast
  ring

theorem A0 : a 0 = 1 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A1 : a 1 = 10 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A2 : a 2 = 10100 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A3 : a 3 = 1101000 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A4 : a 4 = 111010100 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A5 : a 5 = 11110101000 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A6 : a 6 = 1111101010100 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A7 : a 7 = 111111010101000 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A8 : a 8 = 11111110101010100 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A9 : a 9 = 1111111101010101000 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A10 : a 10 = 111111111010101010100 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A11 : a 11 = 11111111110101010101000 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem A12 : a 12 = 1111111111101010101010100 := by
  simp only [a, onCount, cell_eq]
  decide +kernel

theorem a_dig (t : ℕ) : a t = digitsG 197 10 t := by
  unfold a digitsG
  simp only [cellG_eq]

theorem bits0 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 0) :
    bitf 2 G t (-((2 : ℕ) : ℤ) - 1) = 1 ∧ bitf 2 G t (-((2 : ℕ) : ℤ)) = 1 ∧ bitf 2 G t ((2 : ℕ) : ℤ) = 1 ∧ bitf 2 G t (((2 : ℕ) : ℤ) + 1) = 0 := by
  rw [bitf_par 2 G t 8 (by omega) (by norm_num) (by omega) _ (by norm_num) (by norm_num),
    bitf_par 2 G t 8 (by omega) (by norm_num) (by omega) _ (by norm_num) (by norm_num),
    bitf_par 2 G t 8 (by omega) (by norm_num) (by omega) _ (by norm_num) (by norm_num),
    bitf_par 2 G t 8 (by omega) (by norm_num) (by omega) _ (by norm_num) (by norm_num)]
  decide +kernel

theorem Lstep0 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 0) :
    LfG 10 2 G (t + 2) = (10 : ℤ) ^ 4 * (LfG 10 2 G t + 1 * (10 : ℤ) ^ (t + 2 + 1) + 1 * (10 : ℤ) ^ (t + 2)) := by
  rw [stepL 10 2 G t (by omega), (bits0 t h hp).1, (bits0 t h hp).2.1]

theorem Rstep0 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 0) :
    RfG 10 2 G (t + 2) = 1 * (10 : ℤ) ^ (t - 2) + 0 * (10 : ℤ) ^ (t - 2 - 1) + RfG 10 2 G t := by
  rw [stepR 10 2 G t (by omega), (bits0 t h hp).2.2.1, (bits0 t h hp).2.2.2]

theorem L0_0 : LfG 10 2 G 8 = 11111000000000000 := by decide +kernel

theorem M0_0 : MfG 10 2 G 8 = 110101000000 := by decide +kernel

theorem R0_0 : RfG 10 2 G 8 = 10100 := by decide +kernel

theorem Lk0 (k : ℕ) : ((10 : ℤ) ^ 4 - 10 ^ 2) * LfG 10 2 G (8 + 2 * k)
    = (((10 : ℤ) ^ 4 - 10 ^ 2) * 11111000000000000 + 1100000000000000) * 10 ^ (4 * k) - 1100000000000000 * 10 ^ (2 * k) := by
  induction k with
  | zero => rw [show 8 + 2 * 0 = 8 from rfl, L0_0]; norm_num
  | succ k ih =>
    rw [show 8 + 2 * (k + 1) = 8 + 2 * k + 2 from by ring, Lstep0 _ (by omega) (by omega)]
    linear_combination (10 : ℤ) ^ 4 * ih

theorem Mk0 (k : ℕ) : MfG 10 2 G (8 + 2 * k) = 110101000000 * (10 : ℤ) ^ (2 * k) := by
  induction k with
  | zero => rw [show 8 + 2 * 0 = 8 from rfl, M0_0]; norm_num
  | succ k ih =>
    rw [show 8 + 2 * (k + 1) = 8 + 2 * k + 2 from by ring, stepM 10 2 G _ (by omega), ih]
    ring

theorem Rk0 (k : ℕ) : ((10 : ℤ) ^ 2 - 1) * RfG 10 2 G (8 + 2 * k)
    = ((10 : ℤ) ^ 2 - 1) * 10100 + 1000000 * ((10 : ℤ) ^ (2 * k) - 1) := by
  induction k with
  | zero => rw [show 8 + 2 * 0 = 8 from rfl, R0_0]; norm_num
  | succ k ih =>
    rw [show 8 + 2 * (k + 1) = 8 + 2 * k + 2 from by ring, Rstep0 _ (by omega) (by omega),
      show 8 + 2 * k - 2 - 1 = 5 + 2 * k from by omega, show 8 + 2 * k - 2 = 6 + 2 * k from by omega]
    linear_combination ih

theorem M0 (n : ℕ) (h : 8 ≤ n) (hp : n % 2 = 0) : ((a n : ℤ) : ℚ) = (10 / 9 : ℚ) * ((10 : ℚ) ^ n) ^ 2 + (-1000 / 99 : ℚ) * (10 : ℚ) ^ n + (-100 / 99 : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 + 2 * k := ⟨(n - 8) / 2, by omega⟩
  have hd : a (8 + 2 * k) = LfG 10 2 G (8 + 2 * k) + MfG 10 2 G (8 + 2 * k) + RfG 10 2 G (8 + 2 * k) := by
    rw [a_dig, digits_split 197 7 2 10 E bgl G (by norm_num) cellG_pat _ (by omega)]
  have hL : ((10 : ℚ) ^ 4 - 10 ^ 2) * ((LfG 10 2 G (8 + 2 * k) : ℤ) : ℚ)
      = (((10 : ℚ) ^ 4 - 10 ^ 2) * 11111000000000000 + 1100000000000000) * 10 ^ (4 * k) - 1100000000000000 * 10 ^ (2 * k) := by
    exact_mod_cast Lk0 k
  have hR : ((10 : ℚ) ^ 2 - 1) * ((RfG 10 2 G (8 + 2 * k) : ℤ) : ℚ)
      = ((10 : ℚ) ^ 2 - 1) * 10100 + 1000000 * ((10 : ℚ) ^ (2 * k) - 1) := by
    exact_mod_cast Rk0 k
  rw [hd]
  push_cast
  rw [Mk0 k]
  push_cast
  linear_combination (1 / 9900 : ℚ) * hL + (1 / 99 : ℚ) * hR

theorem bits1 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 1) :
    bitf 2 G t (-((2 : ℕ) : ℤ) - 1) = 1 ∧ bitf 2 G t (-((2 : ℕ) : ℤ)) = 1 ∧ bitf 2 G t ((2 : ℕ) : ℤ) = 1 ∧ bitf 2 G t (((2 : ℕ) : ℤ) + 1) = 0 := by
  rw [bitf_par 2 G t 9 (by omega) (by norm_num) (by omega) _ (by norm_num) (by norm_num),
    bitf_par 2 G t 9 (by omega) (by norm_num) (by omega) _ (by norm_num) (by norm_num),
    bitf_par 2 G t 9 (by omega) (by norm_num) (by omega) _ (by norm_num) (by norm_num),
    bitf_par 2 G t 9 (by omega) (by norm_num) (by omega) _ (by norm_num) (by norm_num)]
  decide +kernel

theorem Lstep1 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 1) :
    LfG 10 2 G (t + 2) = (10 : ℤ) ^ 4 * (LfG 10 2 G t + 1 * (10 : ℤ) ^ (t + 2 + 1) + 1 * (10 : ℤ) ^ (t + 2)) := by
  rw [stepL 10 2 G t (by omega), (bits1 t h hp).1, (bits1 t h hp).2.1]

theorem Rstep1 (t : ℕ) (h : 8 ≤ t) (hp : t % 2 = 1) :
    RfG 10 2 G (t + 2) = 1 * (10 : ℤ) ^ (t - 2) + 0 * (10 : ℤ) ^ (t - 2 - 1) + RfG 10 2 G t := by
  rw [stepR 10 2 G t (by omega), (bits1 t h hp).2.2.1, (bits1 t h hp).2.2.2]

theorem L0_1 : LfG 10 2 G 9 = 1111110000000000000 := by decide +kernel

theorem M0_1 : MfG 10 2 G 9 = 1101010000000 := by decide +kernel

theorem R0_1 : RfG 10 2 G 9 = 101000 := by decide +kernel

theorem Lk1 (k : ℕ) : ((10 : ℤ) ^ 4 - 10 ^ 2) * LfG 10 2 G (9 + 2 * k)
    = (((10 : ℤ) ^ 4 - 10 ^ 2) * 1111110000000000000 + 11000000000000000) * 10 ^ (4 * k) - 11000000000000000 * 10 ^ (2 * k) := by
  induction k with
  | zero => rw [show 9 + 2 * 0 = 9 from rfl, L0_1]; norm_num
  | succ k ih =>
    rw [show 9 + 2 * (k + 1) = 9 + 2 * k + 2 from by ring, Lstep1 _ (by omega) (by omega)]
    linear_combination (10 : ℤ) ^ 4 * ih

theorem Mk1 (k : ℕ) : MfG 10 2 G (9 + 2 * k) = 1101010000000 * (10 : ℤ) ^ (2 * k) := by
  induction k with
  | zero => rw [show 9 + 2 * 0 = 9 from rfl, M0_1]; norm_num
  | succ k ih =>
    rw [show 9 + 2 * (k + 1) = 9 + 2 * k + 2 from by ring, stepM 10 2 G _ (by omega), ih]
    ring

theorem Rk1 (k : ℕ) : ((10 : ℤ) ^ 2 - 1) * RfG 10 2 G (9 + 2 * k)
    = ((10 : ℤ) ^ 2 - 1) * 101000 + 10000000 * ((10 : ℤ) ^ (2 * k) - 1) := by
  induction k with
  | zero => rw [show 9 + 2 * 0 = 9 from rfl, R0_1]; norm_num
  | succ k ih =>
    rw [show 9 + 2 * (k + 1) = 9 + 2 * k + 2 from by ring, Rstep1 _ (by omega) (by omega),
      show 9 + 2 * k - 2 - 1 = 6 + 2 * k from by omega, show 9 + 2 * k - 2 = 7 + 2 * k from by omega]
    linear_combination ih

theorem M1 (n : ℕ) (h : 8 ≤ n) (hp : n % 2 = 1) : ((a n : ℤ) : ℚ) = (10 / 9 : ℚ) * ((10 : ℚ) ^ n) ^ 2 + (-1000 / 99 : ℚ) * (10 : ℚ) ^ n + (-1000 / 99 : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 9 + 2 * k := ⟨(n - 9) / 2, by omega⟩
  have hd : a (9 + 2 * k) = LfG 10 2 G (9 + 2 * k) + MfG 10 2 G (9 + 2 * k) + RfG 10 2 G (9 + 2 * k) := by
    rw [a_dig, digits_split 197 7 2 10 E bgl G (by norm_num) cellG_pat _ (by omega)]
  have hL : ((10 : ℚ) ^ 4 - 10 ^ 2) * ((LfG 10 2 G (9 + 2 * k) : ℤ) : ℚ)
      = (((10 : ℚ) ^ 4 - 10 ^ 2) * 1111110000000000000 + 11000000000000000) * 10 ^ (4 * k) - 11000000000000000 * 10 ^ (2 * k) := by
    exact_mod_cast Lk1 k
  have hR : ((10 : ℚ) ^ 2 - 1) * ((RfG 10 2 G (9 + 2 * k) : ℤ) : ℚ)
      = ((10 : ℚ) ^ 2 - 1) * 101000 + 10000000 * ((10 : ℚ) ^ (2 * k) - 1) := by
    exact_mod_cast Rk1 k
  rw [hd]
  push_cast
  rw [Mk1 k]
  push_cast
  linear_combination (1 / 9900 : ℚ) * hL + (1 / 99 : ℚ) * hR

theorem Aq0 : ((a 0 : ℤ) : ℚ) = 1 := by
  rw [A0]
  norm_num

theorem Aq1 : ((a 1 : ℤ) : ℚ) = 10 := by
  rw [A1]
  norm_num

theorem Aq2 : ((a 2 : ℤ) : ℚ) = 10100 := by
  rw [A2]
  norm_num

theorem Aq3 : ((a 3 : ℤ) : ℚ) = 1101000 := by
  rw [A3]
  norm_num

theorem Aq4 : ((a 4 : ℤ) : ℚ) = 111010100 := by
  rw [A4]
  norm_num

theorem Aq5 : ((a 5 : ℤ) : ℚ) = 11110101000 := by
  rw [A5]
  norm_num

theorem Aq6 : ((a 6 : ℤ) : ℚ) = 1111101010100 := by
  rw [A6]
  norm_num

theorem Aq7 : ((a 7 : ℤ) : ℚ) = 111111010101000 := by
  rw [A7]
  norm_num

theorem Aq8 : ((a 8 : ℤ) : ℚ) = 11111110101010100 := by
  rw [A8]
  norm_num

theorem Aq9 : ((a 9 : ℤ) : ℚ) = 1111111101010101000 := by
  rw [A9]
  norm_num

theorem Aq10 : ((a 10 : ℤ) : ℚ) = 111111111010101010100 := by
  rw [A10]
  norm_num

theorem Aq11 : ((a 11 : ℤ) : ℚ) = 11111111110101010101000 := by
  rw [A11]
  norm_num

theorem Aq12 : ((a 12 : ℤ) : ℚ) = 1111111111101010101010100 := by
  rw [A12]
  norm_num

theorem rec0 (m : ℕ) : (1 : ℚ) * (OMA.S_oeis_a267677.a (m + 12) : ℚ) + (-110 : ℚ) * (OMA.S_oeis_a267677.a (m + 11) : ℚ) + (999 : ℚ) * (OMA.S_oeis_a267677.a (m + 10) : ℚ) + (110 : ℚ) * (OMA.S_oeis_a267677.a (m + 9) : ℚ) + (-1000 : ℚ) * (OMA.S_oeis_a267677.a (m + 8) : ℚ) = 0 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [M0 (2 * k + 12) (by omega) (by omega), M1 (2 * k + 11) (by omega) (by omega), M0 (2 * k + 10) (by omega) (by omega), M1 (2 * k + 9) (by omega) (by omega), M0 (2 * k + 8) (by omega) (by omega)]
    push_cast
    ring
  · rw [M1 (2 * k + 1 + 12) (by omega) (by omega), M0 (2 * k + 1 + 11) (by omega) (by omega), M1 (2 * k + 1 + 10) (by omega) (by omega), M0 (2 * k + 1 + 9) (by omega) (by omega), M1 (2 * k + 1 + 8) (by omega) (by omega)]
    push_cast
    ring

theorem rec1 (m : ℕ) : (1 : ℚ) * (OMA.S_oeis_a267677.a (m + 12) : ℚ) + (-110 : ℚ) * (OMA.S_oeis_a267677.a (m + 11) : ℚ) + (999 : ℚ) * (OMA.S_oeis_a267677.a (m + 10) : ℚ) + (110 : ℚ) * (OMA.S_oeis_a267677.a (m + 9) : ℚ) + (-1000 : ℚ) * (OMA.S_oeis_a267677.a (m + 8) : ℚ) = 0 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [M0 (2 * k + 12) (by omega) (by omega), M1 (2 * k + 11) (by omega) (by omega), M0 (2 * k + 10) (by omega) (by omega), M1 (2 * k + 9) (by omega) (by omega), M0 (2 * k + 8) (by omega) (by omega)]
    push_cast
    ring
  · rw [M1 (2 * k + 1 + 12) (by omega) (by omega), M0 (2 * k + 1 + 11) (by omega) (by omega), M1 (2 * k + 1 + 10) (by omega) (by omega), M0 (2 * k + 1 + 9) (by omega) (by omega), M1 (2 * k + 1 + 8) (by omega) (by omega)]
    push_cast
    ring

end OMA.P267677

theorem OMA.solution : type_of% @OMA.S_oeis_a267677.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 12 with h | h
    · interval_cases n <;> norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4, OMA.P267677.Aq5, OMA.P267677.Aq6, OMA.P267677.Aq7, OMA.P267677.Aq8, OMA.P267677.Aq9, OMA.P267677.Aq10, OMA.P267677.Aq11]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      have hr := OMA.P267677.rec0 m
      simp only [show m + 12 - 1 = m + 11 from rfl, show m + 12 - 2 = m + 10 from rfl, show m + 12 - 3 = m + 9 from rfl, show m + 12 - 4 = m + 8 from rfl]
      linarith
  · have hD : (((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 10 * PowerSeries.X) * (1 - 100 * PowerSeries.X)) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-110 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (999 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (110 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-1000 : ℚ) * PowerSeries.X ^ 4 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have hNum : ((1 - 100 * PowerSeries.X + 9999 * PowerSeries.X ^ 2 + 100 * PowerSeries.X ^ 3 - 9900 * PowerSeries.X ^ 4 - 10000 * PowerSeries.X ^ 5) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-100 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (9999 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (100 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-9900 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-10000 : ℚ) * PowerSeries.X ^ 5 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have key : ∀ F : PowerSeries ℚ, F * (PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-110 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (999 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (110 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-1000 : ℚ) * PowerSeries.X ^ 4)
        = PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 0) + PowerSeries.C (-110 : ℚ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (999 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (110 : ℚ) * (F * PowerSeries.X ^ 3) + PowerSeries.C (-1000 : ℚ) * (F * PowerSeries.X ^ 4) := by
      intro F; ring
    rw [hD, hNum, key]
    ext n
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
    · norm_num [OMA.P267677.Aq0]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4, OMA.P267677.Aq5]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4, OMA.P267677.Aq5, OMA.P267677.Aq6]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4, OMA.P267677.Aq5, OMA.P267677.Aq6, OMA.P267677.Aq7]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4, OMA.P267677.Aq5, OMA.P267677.Aq6, OMA.P267677.Aq7, OMA.P267677.Aq8]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4, OMA.P267677.Aq5, OMA.P267677.Aq6, OMA.P267677.Aq7, OMA.P267677.Aq8, OMA.P267677.Aq9]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4, OMA.P267677.Aq5, OMA.P267677.Aq6, OMA.P267677.Aq7, OMA.P267677.Aq8, OMA.P267677.Aq9, OMA.P267677.Aq10]
    · norm_num [OMA.P267677.Aq0, OMA.P267677.Aq1, OMA.P267677.Aq2, OMA.P267677.Aq3, OMA.P267677.Aq4, OMA.P267677.Aq5, OMA.P267677.Aq6, OMA.P267677.Aq7, OMA.P267677.Aq8, OMA.P267677.Aq9, OMA.P267677.Aq10, OMA.P267677.Aq11]
    · rw [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 12 from rfl]
      have hr := OMA.P267677.rec1 m
      simp only [show 0 ≤ m + 12 from by omega,
        show m + 12 - 0 = m + 12 from rfl,
        show ¬ (m + 12 = 0) from by omega,
        show 1 ≤ m + 12 from by omega,
        show m + 12 - 1 = m + 11 from rfl,
        show ¬ (m + 11 = 0) from by omega,
        show 2 ≤ m + 12 from by omega,
        show m + 12 - 2 = m + 10 from rfl,
        show ¬ (m + 10 = 0) from by omega,
        show 3 ≤ m + 12 from by omega,
        show m + 12 - 3 = m + 9 from rfl,
        show ¬ (m + 9 = 0) from by omega,
        show 4 ≤ m + 12 from by omega,
        show m + 12 - 4 = m + 8 from rfl,
        show ¬ (m + 8 = 0) from by omega,
        show 5 ≤ m + 12 from by omega,
        show m + 12 - 5 = m + 7 from rfl,
        show ¬ (m + 7 = 0) from by omega,
        if_true, if_false]
      linear_combination hr
