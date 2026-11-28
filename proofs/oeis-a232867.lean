import OMAStatements.S_oeis_a232867

namespace OMA.S_oeis_a232867

open Finset





/-! ### The distance function -/

/-- The number of moves needed to reach z from 0. -/
def d (z : GaussianInt) : ℤ :=
  (if z.re < 0 then -z.re else z.re) + (if z.im < 0 then -z.im else z.im) +
    (if z.im < 0 then 3 else if z.re < 0 then 2 else if 0 < z.im then 1 else 0)

lemma iu_mul_re (x : GaussianInt) : (iu * x).re = -x.im := by simp [iu]
lemma iu_mul_im (x : GaussianInt) : (iu * x).im = x.re := by simp [iu]

lemma d_add_one (x : GaussianInt) : d (x + 1) ≤ d x + 1 := by
  have h1 : (x + 1).re = x.re + 1 := by simp
  have h2 : (x + 1).im = x.im := by simp
  unfold d
  rw [h1, h2]
  split_ifs <;> omega

lemma d_iu_mul (x : GaussianInt) : d (iu * x) ≤ d x + 1 := by
  unfold d
  rw [iu_mul_re, iu_mul_im]
  split_ifs <;> omega

lemma d_zero_iff (z : GaussianInt) : d z ≤ 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold d at h
    have : z.re = 0 ∧ z.im = 0 := by split_ifs at h <;> omega
    exact Zsqrtd.ext this.1 this.2
  · rintro rfl
    simp [d]

/-- Every z with d(z) = t + 1 has a parent at distance t. -/
lemma d_parent (z : GaussianInt) (t : ℕ) (h : d z = t + 1) :
    d (z - 1) = t ∧ 1 ≤ z.re ∨ d ⟨z.im, -z.re⟩ = t ∧ iu * ⟨z.im, -z.re⟩ = z := by
  have hz : z - 1 = ⟨z.re - 1, z.im⟩ := by ext <;> simp
  rcases lt_or_ge 0 z.re with hre | hre
  · left
    refine ⟨?_, by omega⟩
    rw [hz]
    unfold d at h ⊢
    simp only at h ⊢
    split_ifs at h ⊢ <;> omega
  · right
    refine ⟨?_, ?_⟩
    · unfold d at h ⊢
      simp only at h ⊢
      split_ifs at h ⊢ <;> omega
    · ext <;> simp [iu]

/-! ### The lists -/

/-- The children of x, in order. -/
def ch (x : GaussianInt) : List GaussianInt := [x, x + 1, iu * x]

lemma step_eq (L : List GaussianInt) : step L = (L.flatMap ch).eraseDups := rfl

lemma mem_Lst_succ {t : ℕ} {z : GaussianInt} :
    z ∈ Lst (t + 1) ↔ ∃ x ∈ Lst t, z = x ∨ z = x + 1 ∨ z = iu * x := by
  rw [Lst, step_eq, List.mem_eraseDups, List.mem_flatMap]
  simp [ch, eq_comm]

/-- Membership in the list after t rounds is distance at most t. -/
lemma mem_Lst (t : ℕ) (z : GaussianInt) : z ∈ Lst t ↔ d z ≤ t := by
  induction t generalizing z with
  | zero =>
    simp only [Lst, List.mem_singleton, Nat.cast_zero]
    exact (d_zero_iff z).symm
  | succ t ih =>
    rw [mem_Lst_succ]
    constructor
    · rintro ⟨x, hx, h | h | h⟩
      · rw [h]; have := (ih x).1 hx; push_cast; omega
      · rw [h]; have := (ih x).1 hx; have := d_add_one x; push_cast; omega
      · rw [h]; have := (ih x).1 hx; have := d_iu_mul x; push_cast; omega
    · intro h
      rcases lt_or_ge (d z) (t + 1) with hlt | hge
      · exact ⟨z, (ih z).2 (by omega), Or.inl rfl⟩
      · have heq : d z = t + 1 := by push_cast at h; omega
        rcases d_parent z t heq with ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact ⟨z - 1, (ih _).2 (by omega), Or.inr (Or.inl (by ring))⟩
        · exact ⟨_, (ih _).2 (by omega), Or.inr (Or.inr h2.symm)⟩

/-! ### Generations -/

/-- The t-th generation: the new elements of round t, in order. -/
def gen : ℕ → List GaussianInt
  | 0 => [0]
  | t + 1 => (((gen t).flatMap ch).removeAll (Lst t)).eraseDups

lemma removeAll_congr {xs ys zs : List GaussianInt} (h : ∀ x, x ∈ ys ↔ x ∈ zs) :
    xs.removeAll ys = xs.removeAll zs := by
  unfold List.removeAll
  congr 1
  funext x
  simp [List.elem_eq_mem, h]

/-- Each round appends the next generation. -/
lemma Lst_succ (t : ℕ) : Lst (t + 1) = Lst t ++ gen (t + 1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have e1 : Lst (t + 1 + 1) = ((Lst (t + 1)).flatMap ch).eraseDups := rfl
    rw [e1, ih, List.flatMap_append, List.eraseDups_append, ← ih]
    have e2 : ((Lst t).flatMap ch).eraseDups = Lst (t + 1) := rfl
    rw [e2]
    congr 1
    show _ = (((gen (t + 1)).flatMap ch).removeAll (Lst (t + 1))).eraseDups
    congr 1
    apply removeAll_congr
    intro x
    rw [← e2, List.mem_eraseDups]

lemma d_nat (n : ℕ) : d (((n : ℤ) : GaussianInt)) = n := by
  unfold d
  simp only [Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  split_ifs <;> omega

lemma d_iu_nat (k : ℕ) (hk : 1 ≤ k) : d (iu * ((k : ℤ) : GaussianInt)) = k + 1 := by
  unfold d
  rw [iu_mul_re, iu_mul_im]
  simp only [Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  split_ifs <;> omega

lemma d_iu_nat_add_one (k : ℕ) (hk : 1 ≤ k) :
    d (iu * ((k : ℤ) : GaussianInt) + 1) = k + 2 := by
  have h1 : (iu * ((k : ℤ) : GaussianInt) + 1).re = 1 := by simp [iu]
  have h2 : (iu * ((k : ℤ) : GaussianInt) + 1).im = k := by simp [iu]
  unfold d
  rw [h1, h2]
  split_ifs <;> omega

lemma iu_iu (k : ℕ) : iu * (iu * ((k : ℤ) : GaussianInt)) = -((k : ℤ) : GaussianInt) := by
  ext <;> simp [iu]

lemma d_neg_nat (k : ℕ) (hk : 1 ≤ k) : d (-((k : ℤ) : GaussianInt)) = k + 2 := by
  unfold d
  simp only [Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  split_ifs <;> omega

/-- Generation k + 1 begins with k + 1 and i k (for k >= 1); then generation k + 2 begins with
k + 2, i (k + 1), i k + 1 and -k. -/
lemma gen_four (k : ℕ) (hk : 1 ≤ k) :
    (∃ r, gen (k + 1) = (((k + 1 : ℕ) : ℤ) : GaussianInt) :: (iu * ((k : ℤ) : GaussianInt)) :: r) ∧
    ∃ r, gen (k + 2) = (((k + 2 : ℕ) : ℤ) : GaussianInt) ::
      (iu * (((k + 1 : ℕ) : ℤ) : GaussianInt)) :: (iu * ((k : ℤ) : GaussianInt) + 1) ::
      (-((k : ℤ) : GaussianInt)) :: r := by
  induction k with
  | zero => omega
  | succ k ih =>
    have P : ∃ r, gen (k + 1 + 1) =
        (((k + 1 + 1 : ℕ) : ℤ) : GaussianInt) :: (iu * (((k + 1 : ℕ) : ℤ) : GaussianInt)) :: r := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨[], by decide⟩
      · obtain ⟨_, r, hr⟩ := ih hk0
        exact ⟨_, hr⟩
    refine ⟨P, ?_⟩
    obtain ⟨r, hr⟩ := P
    set m : ℕ := k + 1 with hm
    have hm1 : 1 ≤ m := by omega
    have e : gen (m + 2) = (((gen (m + 1)).flatMap ch).removeAll (Lst (m + 1))).eraseDups := rfl
    have x1 : (((m + 1 : ℕ) : ℤ) : GaussianInt) ∈ Lst (m + 1) := by
      rw [mem_Lst, d_nat]
    have x2 : (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 ∉ Lst (m + 1) := by
      rw [mem_Lst, show (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 = (((m + 2 : ℕ) : ℤ) : GaussianInt) by
        push_cast; ring, d_nat]
      push_cast; omega
    have x3 : iu * (((m + 1 : ℕ) : ℤ) : GaussianInt) ∉ Lst (m + 1) := by
      rw [mem_Lst, d_iu_nat _ (by omega)]
      push_cast; omega
    have x4 : iu * ((m : ℤ) : GaussianInt) ∈ Lst (m + 1) := by
      rw [mem_Lst, d_iu_nat _ hm1]
      push_cast; omega
    have x5 : iu * ((m : ℤ) : GaussianInt) + 1 ∉ Lst (m + 1) := by
      rw [mem_Lst, d_iu_nat_add_one _ hm1]
      push_cast; omega
    have x6 : iu * (iu * ((m : ℤ) : GaussianInt)) ∉ Lst (m + 1) := by
      rw [mem_Lst, iu_iu, d_neg_nat _ hm1]
      push_cast; omega
    have n12 : iu * (((m + 1 : ℕ) : ℤ) : GaussianInt) ≠ (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 := by
      intro h; have := congrArg Zsqrtd.im h; simp [iu] at this <;> omega
    have n13 : iu * ((m : ℤ) : GaussianInt) + 1 ≠ (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 := by
      intro h; have := congrArg Zsqrtd.im h; simp [iu] at this <;> omega
    have n14 : iu * (iu * ((m : ℤ) : GaussianInt)) ≠ (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 := by
      intro h; have := congrArg Zsqrtd.re h; simp [iu] at this <;> omega
    have n23 : iu * ((m : ℤ) : GaussianInt) + 1 ≠ iu * (((m + 1 : ℕ) : ℤ) : GaussianInt) := by
      intro h; have := congrArg Zsqrtd.re h; simp [iu] at this <;> omega
    have n24 : iu * (iu * ((m : ℤ) : GaussianInt)) ≠ iu * (((m + 1 : ℕ) : ℤ) : GaussianInt) := by
      intro h; have := congrArg Zsqrtd.im h; simp [iu] at this <;> omega
    have n34 : iu * (iu * ((m : ℤ) : GaussianInt)) ≠ iu * ((m : ℤ) : GaussianInt) + 1 := by
      intro h; have := congrArg Zsqrtd.re h; simp [iu] at this <;> omega
    have b12 := beq_false_of_ne n12
    have b13 := beq_false_of_ne n13
    have b14 := beq_false_of_ne n14
    have b23 := beq_false_of_ne n23
    have b24 := beq_false_of_ne n24
    have b34 := beq_false_of_ne n34
    rw [e, hr, List.flatMap_cons, List.flatMap_cons]
    simp only [ch, List.cons_append, List.nil_append, List.removeAll, List.filter_cons,
      List.elem_eq_mem, x1, x2, x3, x4, x5, x6, decide_true, decide_false, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, if_true, if_false, ite_true, ite_false]
    rw [List.eraseDups_cons]
    simp only [List.filter_cons, b12, b13, b14, Bool.not_false, if_true, ite_true]
    rw [List.eraseDups_cons]
    simp only [List.filter_cons, b23, b24, Bool.not_false, if_true, ite_true]
    rw [List.eraseDups_cons]
    simp only [List.filter_cons, b34, Bool.not_false, if_true, ite_true]
    rw [List.eraseDups_cons, iu_iu]
    exact ⟨_, by
      rw [show (((m + 2 : ℕ) : ℤ) : GaussianInt) = (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 by
        push_cast; ring]⟩

lemma eraseDups_nodup : ∀ l : List GaussianInt, l.eraseDups.Nodup
  | [] => by simp
  | x :: l => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨?_, eraseDups_nodup _⟩
    rw [List.mem_eraseDups]
    simp
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

lemma Lst_nodup (t : ℕ) : (Lst t).Nodup := by
  cases t with
  | zero => simp [Lst]
  | succ t => exact eraseDups_nodup _

/-- The position of -n, n >= 1: four past the first n + 1 rounds' worth of list. -/
lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = (Lst (n + 1)).length + 4 := by
  obtain ⟨r, hr⟩ := (gen_four n hn).2
  have hnot : -((n : ℤ) : GaussianInt) ∉ Lst (n + 1) := by
    rw [mem_Lst, d_neg_nat n hn]; push_cast; omega
  have h1 : -((n : ℤ) : GaussianInt) ≠ (((n + 2 : ℕ) : ℤ) : GaussianInt) := by
    intro h; have := congrArg Zsqrtd.re h; simp at this; omega
  have h2 : -((n : ℤ) : GaussianInt) ≠ iu * (((n + 1 : ℕ) : ℤ) : GaussianInt) := by
    intro h; have := congrArg Zsqrtd.im h; simp [iu] at this; omega
  have h3 : -((n : ℤ) : GaussianInt) ≠ iu * ((n : ℤ) : GaussianInt) + 1 := by
    intro h; have := congrArg Zsqrtd.re h; simp [iu] at this; omega
  unfold a
  rw [Lst_succ (n + 1), hr, List.idxOf_append_of_notMem hnot, List.idxOf_cons_ne _ h1.symm,
    List.idxOf_cons_ne _ h2.symm, List.idxOf_cons_ne _ h3.symm, List.idxOf_cons_self]

/-! ### Counting -/

/-- The points at distance at most t, as pairs (re, im). -/
noncomputable def ball (t : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(t : ℤ)) t) ×ˢ (Icc (-(t : ℤ)) t)).filter (fun p => d ⟨p.1, p.2⟩ ≤ t)

/-- The points at distance exactly s. -/
noncomputable def sph (s : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(s : ℤ)) s) ×ˢ (Icc (-(s : ℤ)) s)).filter (fun p => d ⟨p.1, p.2⟩ = s)

lemma abs_le_d (z : GaussianInt) : (z.re ≤ d z ∧ -z.re ≤ d z) ∧ (z.im ≤ d z ∧ -z.im ≤ d z) := by
  unfold d; split_ifs <;> omega

lemma length_Lst (t : ℕ) : (Lst t).length = (ball t).card := by
  rw [← List.toFinset_card_of_nodup (Lst_nodup t)]
  have hinj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
    intro z w h
    simp only [Prod.mk.injEq] at h
    exact Zsqrtd.ext h.1 h.2
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext ⟨x, y⟩
  simp only [Finset.mem_image, List.mem_toFinset, ball, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, rfl, rfl⟩
    rw [mem_Lst] at hz
    have := abs_le_d z
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, hz⟩
  · rintro ⟨_, h⟩
    exact ⟨⟨x, y⟩, (mem_Lst t _).2 h, rfl, rfl⟩

lemma ball_succ (t : ℕ) : ball (t + 1) = ball t ∪ sph (t + 1) := by
  ext ⟨x, y⟩
  simp only [ball, sph, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  have := abs_le_d ⟨x, y⟩
  simp only at this
  push_cast
  constructor
  · rintro ⟨_, h⟩
    rcases lt_or_ge (d ⟨x, y⟩) (t + 1) with h' | h'
    · left; exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
    · right; exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
    · exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩

lemma ball_sph_disjoint (t : ℕ) : Disjoint (ball t) (sph (t + 1)) := by
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [ball, sph, Finset.mem_filter] at h1 h2
  push_cast at h2
  omega

/-- The sphere of radius s >= 4 has 4s - 9 points. -/
lemma card_sph (s : ℕ) (hs : 4 ≤ s) : (sph s).card + 9 = 4 * s := by
  set S : ℤ := (s : ℤ) with hS
  have e : sph s = ({(S, 0)} : Finset (ℤ × ℤ)) ∪
      ((Icc (1 : ℤ) (S - 1)).image (fun b => (S - 1 - b, b)) ∪
      ((Icc (0 : ℤ) (S - 3)).image (fun b => (b - (S - 2), b)) ∪
      ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)) ∪
      (Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c))))) := by
    ext ⟨x, y⟩
    simp only [sph, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_image, Prod.mk.injEq]
    rw [← hS]
    unfold d
    simp only
    constructor
    · rintro ⟨_, h⟩
      rcases lt_or_ge y 0 with hy | hy
      · rcases lt_or_ge x 0 with hx | hx
        · right; right; right; right
          exact ⟨-y, ⟨by split_ifs at h <;> omega, by split_ifs at h <;> omega⟩,
            by split_ifs at h <;> omega, by ring⟩
        · right; right; right; left
          exact ⟨-y, ⟨by split_ifs at h <;> omega, by split_ifs at h <;> omega⟩,
            by split_ifs at h <;> omega, by ring⟩
      · rcases lt_or_ge x 0 with hx | hx
        · right; right; left
          exact ⟨y, ⟨by split_ifs at h <;> omega, by split_ifs at h <;> omega⟩,
            by split_ifs at h <;> omega, rfl⟩
        · rcases lt_or_ge 0 y with hy' | hy'
          · right; left
            exact ⟨y, ⟨by split_ifs at h <;> omega, by split_ifs at h <;> omega⟩,
              by split_ifs at h <;> omega, rfl⟩
          · left
            exact ⟨by split_ifs at h <;> omega, by omega⟩
    · rintro (⟨rfl, rfl⟩ | ⟨b, ⟨h1, h2⟩, rfl, rfl⟩ | ⟨b, ⟨h1, h2⟩, rfl, rfl⟩ |
        ⟨c, ⟨h1, h2⟩, rfl, rfl⟩ | ⟨c, ⟨h1, h2⟩, rfl, rfl⟩) <;>
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩ <;> split_ifs <;> omega
  rw [e]
  have d1 : Disjoint ({(S, 0)} : Finset (ℤ × ℤ))
      ((Icc (1 : ℤ) (S - 1)).image (fun b => (S - 1 - b, b)) ∪
      ((Icc (0 : ℤ) (S - 3)).image (fun b => (b - (S - 2), b)) ∪
      ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)) ∪
      (Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c))))) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_singleton, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rintro _ rfl
    simp only [Prod.mk.injEq]
    omega
  have d2 : Disjoint ((Icc (1 : ℤ) (S - 1)).image (fun b => (S - 1 - b, b)))
      ((Icc (0 : ℤ) (S - 3)).image (fun b => (b - (S - 2), b)) ∪
      ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)) ∪
      (Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c)))) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rintro _ ⟨b, hb, rfl⟩
    simp only [Prod.mk.injEq]
    omega
  have d3 : Disjoint ((Icc (0 : ℤ) (S - 3)).image (fun b => (b - (S - 2), b)))
      ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)) ∪
      (Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c))) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rintro _ ⟨b, hb, rfl⟩
    simp only [Prod.mk.injEq]
    omega
  have d4 : Disjoint ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)))
      ((Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c))) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_Icc]
    rintro _ ⟨c, hc, rfl⟩
    simp only [Prod.mk.injEq]
    omega
  rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d4]
  rw [Finset.card_image_of_injective _ (fun b b' h => by simpa using h),
    Finset.card_image_of_injective _ (fun b b' h => by simpa using h),
    Finset.card_image_of_injective _ (fun c c' h => by simpa using h),
    Finset.card_image_of_injective _ (fun c c' h => by simpa using h)]
  simp only [Int.card_Icc, Finset.card_singleton]
  omega

lemma card_ball (t : ℕ) (ht : 3 ≤ t) : (ball t).card + 7 * t = 2 * t ^ 2 + 11 := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge t 3 with h | h
    · have : t = 2 := by omega
      subst this
      decide
    · rw [ball_succ, Finset.card_union_of_disjoint (ball_sph_disjoint t)]
      have := ih h
      have := card_sph (t + 1) (by omega)
      nlinarith

/-! ### The conjectures -/

theorem closed_form (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = 2 * n ^ 2 + n + 9 := by
  rw [a_eq (n + 1) (by omega), length_Lst]
  have := card_ball (n + 2) (by omega)
  nlinarith

lemma a_one : a 1 = 8 := by
  rw [a_eq 1 le_rfl, length_Lst]
  decide

theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = (m + 3) + 1 by omega, show m + 5 - 2 = (m + 2) + 1 by omega,
    show m + 5 - 3 = (m + 1) + 1 by omega, show m + 5 = (m + 4) + 1 by omega,
    closed_form _ (by omega), closed_form _ (by omega), closed_form _ (by omega),
    closed_form _ (by omega)]
  push_cast
  ring

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (X - 1) ^ 3 =
    X * (-8 + 12 * X - 7 * X ^ 2 - X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have e1 : A * (X - 1) ^ 3 = A * X ^ 3 - A * X ^ 2 * C 3 + A * X ^ 1 * C 3 - A := by
    rw [show (C 3 : ℤ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  have e2 : (X : ℤ⟦X⟧) * (-8 + 12 * X - 7 * X ^ 2 - X ^ 3) =
      X ^ 2 * C 12 - X ^ 1 * C 8 - X ^ 3 * C 7 - X ^ 4 := by
    rw [show (C 12 : ℤ⟦X⟧) = 12 from map_ofNat C 12, show (C 8 : ℤ⟦X⟧) = 8 from map_ofNat C 8,
      show (C 7 : ℤ⟦X⟧) = 7 from map_ofNat C 7]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  have v1 := a_one
  have v2 : a 2 = 12 := closed_form 1 le_rfl
  have v3 : a 3 = 19 := closed_form 2 (by norm_num)
  have v4 : a 4 = 30 := closed_form 3 (by norm_num)
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4]
  · have h := recurrence n hn
    have h1 : ¬ (n = 0) := by omega
    have h2 : ¬ (n - 1 = 0) := by omega
    have h3 : ¬ (n - 2 = 0) := by omega
    have h4 : ¬ (n - 3 = 0) := by omega
    simp only [h1, h2, h3, h4, if_false, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, if_true, show ¬ (n = 2) by omega, show ¬ (n = 1) by omega,
      show ¬ (n = 3) by omega, show ¬ (n = 4) by omega]
    rw [h]
    ring

/-- Kimberling's three conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → a (n + 1) = 2 * n ^ 2 + n + 9) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (PowerSeries.X - 1) ^ 3 =
      PowerSeries.X * (-8 + 12 * PowerSeries.X - 7 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨closed_form, gf, recurrence⟩

end OMA.S_oeis_a232867

theorem OMA.solution : type_of% @OMA.S_oeis_a232867.main :=
  OMA.S_oeis_a232867.conjecture
