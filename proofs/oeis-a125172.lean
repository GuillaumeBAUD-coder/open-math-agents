import OMAStatements.S_oeis_a125172

-- Problem: A125172: Triangle T(n,k) with partial column sums of the even-indexed Fibonacci numbers
-- Upstream: statements/oeis-a125172.lean (declaration OMA.S_oeis_a125172.main)
-- Credit: @timlantin (the owner of the agent is credited as the solver)
--
-- Proof sketch. Write a nonempty Dyck path as p = U q D r (first return decomposition, q and r
-- Dyck paths; Mathlib: p = nest (insidePart p) + outsidePart p). The valleys of p are those of q
-- raised by 1, then a valley at altitude 0 if r is not empty, then those of r; and p has one
-- return more than r. Hence, if r is not empty, p is nondecreasing iff q has no valley and r is
-- nondecreasing; if r is empty, iff q is nondecreasing. (This structure of nondecreasing Dyck
-- paths, a sequence of pyramids followed by a lifted path, is that of Barcucci, Del Lungo, Fezzi
-- and Pinzani, Nondecreasing Dyck paths and q-Fibonacci numbers, Discrete Math. 170 (1997),
-- cited in A121460; the explicit formula of that entry is not used.)
-- Let a(n,k) be the number of nondecreasing paths of semilength n with k returns, tot(n) the
-- number of all of them and u(n) the number with at least 2 returns. Then
--   a(n+1,1) = tot(n)                    (p = U q D),
--   a(n+1,k+2) = a(n,k+2) + a(n,k+1)     (U U q D D r from U q D r, and U D r from r),
--   u(n+1) = u(n) + tot(n) (n >= 1),  tot(n+1) = a(n+1,1) + u(n+1),
-- so tot(n+1) = F(2n+1), a(n+2,1) = F(2n+1), a(n+2,2) = 1 + F(2n). With T(n+1,2) + 1 = F(2n+1),
-- an induction on n gives a(n+1,k) + T(n,k) = T(n,k-1) for all k >= 2: for k = 2 by the values
-- above, for k >= 3 because both a and T satisfy the Pascal recurrence.

namespace OMA.P125172
open OMA.S_oeis_a125172 DyckStep DyckWord

lemma va_nil (prev : DyckStep) (h : ℤ) : valleyAltitudes prev h [] = [] := by
  rw [valleyAltitudes]

lemma va_U (prev : DyckStep) (h : ℤ) (l : List DyckStep) :
    valleyAltitudes prev h (U :: l) =
      (if prev = D then [h] else []) ++ valleyAltitudes U (h + 1) l := by
  rw [valleyAltitudes]

lemma va_D (prev : DyckStep) (h : ℤ) (l : List DyckStep) :
    valleyAltitudes prev h (D :: l) = valleyAltitudes D (h - 1) l := by
  rw [valleyAltitudes]

lemma rt_nil (h : ℤ) : returnsFrom h [] = 0 := by
  rw [returnsFrom]

lemma rt_U (h : ℤ) (l : List DyckStep) :
    returnsFrom h (U :: l) = (if h + 1 = 0 then 1 else 0) + returnsFrom (h + 1) l := by
  rw [returnsFrom]

lemma rt_D (h : ℤ) (l : List DyckStep) :
    returnsFrom h (D :: l) = (if h - 1 = 0 then 1 else 0) + returnsFrom (h - 1) l := by
  rw [returnsFrom]

/-- The height reached by a list of steps. -/
def ht (l : List DyckStep) : ℤ := (l.count U : ℤ) - (l.count D : ℤ)

lemma ht_nil : ht [] = 0 := by simp [ht]

lemma ht_U (l : List DyckStep) : ht (U :: l) = ht l + 1 := by
  unfold ht
  rw [List.count_cons_self, List.count_cons_of_ne (by decide)]
  push_cast
  ring

lemma ht_D (l : List DyckStep) : ht (D :: l) = ht l - 1 := by
  unfold ht
  rw [List.count_cons_self, List.count_cons_of_ne (by decide)]
  push_cast
  ring

lemma va_append_D (q r : List DyckStep) : ∀ (prev : DyckStep) (h : ℤ),
    valleyAltitudes prev h (q ++ D :: r) =
      valleyAltitudes prev h q ++ valleyAltitudes D (h + ht q - 1) r := by
  induction q with
  | nil =>
    intro prev h
    rw [List.nil_append, va_D, va_nil, ht_nil, add_zero, List.nil_append]
  | cons s q ih =>
    intro prev h
    cases s with
    | U =>
      have e : h + 1 + ht q - 1 = h + (ht q + 1) - 1 := by ring
      rw [List.cons_append, va_U, va_U, ih, ht_U, List.append_assoc, e]
    | D =>
      have e : h - 1 + ht q - 1 = h + (ht q - 1) - 1 := by ring
      rw [List.cons_append, va_D, va_D, ih, ht_D, e]

lemma va_shift (c : ℤ) (l : List DyckStep) : ∀ (prev : DyckStep) (h : ℤ),
    valleyAltitudes prev (h + c) l = (valleyAltitudes prev h l).map (· + c) := by
  induction l with
  | nil =>
    intro prev h
    rw [va_nil, va_nil]
    rfl
  | cons s l ih =>
    intro prev h
    cases s with
    | U =>
      have e : h + c + 1 = h + 1 + c := by ring
      rw [va_U, va_U, List.map_append, ← ih, e]
      by_cases hp : prev = D <;> simp [hp]
    | D =>
      have e : h + c - 1 = h - 1 + c := by ring
      rw [va_D, va_D, ← ih, e]

lemma rt_append_D (q r : List DyckStep) : ∀ h : ℤ,
    returnsFrom h (q ++ D :: r) =
      returnsFrom h q + ((if h + ht q - 1 = 0 then 1 else 0) + returnsFrom (h + ht q - 1) r) := by
  induction q with
  | nil =>
    intro h
    rw [List.nil_append, rt_D, rt_nil, ht_nil, add_zero, zero_add]
  | cons s q ih =>
    intro h
    cases s with
    | U =>
      have e : h + 1 + ht q - 1 = h + (ht q + 1) - 1 := by ring
      rw [List.cons_append, rt_U, rt_U, ih, ht_U, e, add_assoc]
    | D =>
      have e : h - 1 + ht q - 1 = h + (ht q - 1) - 1 := by ring
      rw [List.cons_append, rt_D, rt_D, ih, ht_D, e, add_assoc]

lemma rt_pos (l : List DyckStep) : ∀ h : ℤ, 0 < h →
    (∀ i, ((l.take i).count D : ℤ) < ((l.take i).count U : ℤ) + h) → returnsFrom h l = 0 := by
  induction l with
  | nil =>
    intro h _ _
    exact rt_nil h
  | cons s l ih =>
    intro h hh H
    cases s with
    | U =>
      rw [rt_U, if_neg (by omega), zero_add]
      apply ih (h + 1) (by omega)
      intro i
      have h3 := H (i + 1)
      rw [List.take_succ_cons, List.count_cons_self, List.count_cons_of_ne (by decide)] at h3
      push_cast at h3
      omega
    | D =>
      have h1 := H 1
      rw [List.take_succ_cons, List.take_zero, List.count_cons_self,
        List.count_cons_of_ne (by decide)] at h1
      simp at h1
      rw [rt_D, if_neg (by omega), zero_add]
      apply ih (h - 1) (by omega)
      intro i
      have h3 := H (i + 1)
      rw [List.take_succ_cons, List.count_cons_self, List.count_cons_of_ne (by decide)] at h3
      push_cast at h3
      omega

/-- The valley altitudes of a Dyck word. -/
def VA (p : DyckWord) : List ℤ := valleyAltitudes U 0 p.toList

lemma ND_iff (p : DyckWord) : IsNondecreasing p ↔ (VA p).Pairwise (· ≤ ·) := Iff.rfl

lemma toList_nest_add (q r : DyckWord) :
    (q.nest + r).toList = U :: (q.toList ++ D :: r.toList) := by
  show ([U] ++ q.toList ++ [D]) ++ r.toList = _
  simp

lemma ht_dyck (q : DyckWord) : ht q.toList = 0 := by
  unfold ht
  rw [q.count_U_eq_count_D]
  ring

lemma VA_zero : VA 0 = [] := va_nil U 0

lemma returns_zero : returns 0 = 0 := rt_nil 0

lemma VA_decomp (q r : DyckWord) :
    VA (q.nest + r) = (VA q).map (· + 1) ++ ((if r = 0 then [] else [0]) ++ VA r) := by
  unfold VA
  have e1 : (0 : ℤ) + 1 + 0 - 1 = 0 := by norm_num
  rw [toList_nest_add, va_U, if_neg (by decide), List.nil_append, va_append_D, ht_dyck, e1,
    va_shift 1 q.toList U 0]
  congr 1
  by_cases hr : r = 0
  · subst hr
    rw [if_pos rfl]
    show valleyAltitudes D 0 [] = [] ++ valleyAltitudes U 0 []
    rw [va_nil, va_nil]
    rfl
  · rw [if_neg hr]
    obtain ⟨q', r', rfl⟩ : ∃ q' r' : DyckWord, r = q'.nest + r' :=
      ⟨_, _, (nest_insidePart_add_outsidePart hr).symm⟩
    rw [toList_nest_add, va_U, va_U, if_pos rfl, if_neg (by decide)]
    rfl

lemma RET_decomp (q r : DyckWord) : returns (q.nest + r) = returns r + 1 := by
  unfold returns
  have e1 : (0 : ℤ) + 1 + 0 - 1 = 0 := by norm_num
  rw [toList_nest_add, rt_U, if_neg (by norm_num), zero_add, rt_append_D, ht_dyck,
    rt_pos q.toList (0 + 1) (by norm_num)
      (fun i => by have h5 := q.count_D_le_count_U i; omega), e1, if_pos rfl]
  omega

lemma VA_nonneg_aux (n : ℕ) : ∀ p : DyckWord, p.semilength < n → ∀ x ∈ VA p, (0 : ℤ) ≤ x := by
  induction n with
  | zero =>
    intro p hp
    omega
  | succ n ih =>
    intro p hp x hx
    by_cases h0 : p = 0
    · subst h0
      rw [VA_zero] at hx
      simp at hx
    · have h1 := semilength_insidePart_lt h0
      have h2 := semilength_outsidePart_lt h0
      rw [← nest_insidePart_add_outsidePart h0, VA_decomp] at hx
      rcases List.mem_append.mp hx with h3 | h3
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h3
        have h4 := ih p.insidePart (by omega) y hy
        omega
      · rcases List.mem_append.mp h3 with h4 | h4
        · split_ifs at h4 with hr
          · simp at h4
          · simp at h4
            omega
        · exact ih p.outsidePart (by omega) x h4

lemma VA_nonneg (p : DyckWord) : ∀ x ∈ VA p, (0 : ℤ) ≤ x :=
  VA_nonneg_aux (p.semilength + 1) p (Nat.lt_succ_self _)

lemma VA_nest (q : DyckWord) : VA q.nest = (VA q).map (· + 1) := by
  have h := VA_decomp q 0
  rw [add_zero, if_pos rfl, VA_zero, List.append_nil, List.append_nil] at h
  exact h

lemma VA_nest_eq_nil (q : DyckWord) : VA q.nest = [] ↔ VA q = [] := by
  rw [VA_nest, List.map_eq_nil_iff]

lemma VA_ne_nil (q r : DyckWord) (hr : r ≠ 0) : VA (q.nest + r) ≠ [] := by
  rw [VA_decomp, if_neg hr]
  simp

lemma ND_of_VA_nil (p : DyckWord) (h : VA p = []) : IsNondecreasing p := by
  rw [ND_iff, h]
  exact List.Pairwise.nil

lemma ND_nest (q : DyckWord) : IsNondecreasing q.nest ↔ IsNondecreasing q := by
  rw [ND_iff, ND_iff, VA_nest, List.pairwise_map]
  simp

lemma ND_nest_add (q r : DyckWord) (hr : r ≠ 0) :
    IsNondecreasing (q.nest + r) ↔ VA q = [] ∧ IsNondecreasing r := by
  rw [ND_iff, ND_iff, VA_decomp, if_neg hr, List.pairwise_append]
  constructor
  · rintro ⟨_, h2, h3⟩
    refine ⟨?_, (List.pairwise_append.mp h2).2.1⟩
    by_contra hne
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
    have h4 := h3 (y + 1) (List.mem_map.mpr ⟨y, hy, rfl⟩) 0 (by simp)
    have h5 := VA_nonneg q y hy
    omega
  · rintro ⟨h1, h2⟩
    rw [h1]
    refine ⟨by simp, ?_, by simp⟩
    rw [List.singleton_append, List.pairwise_cons]
    exact ⟨fun x hx => VA_nonneg r x hx, h2⟩

lemma ins_na (q r : DyckWord) : (q.nest + r).insidePart = q := by
  rw [insidePart_add nest_ne_zero, insidePart_nest]

lemma out_na (q r : DyckWord) : (q.nest + r).outsidePart = r := by
  rw [outsidePart_add nest_ne_zero, outsidePart_nest, zero_add]

lemma returns_pos (p : DyckWord) (hp : p ≠ 0) : 1 ≤ returns p := by
  have h := RET_decomp p.insidePart p.outsidePart
  rw [nest_insidePart_add_outsidePart hp] at h
  omega

lemma eq_zero_of_semilength (p : DyckWord) (h : p.semilength = 0) : p = 0 := by
  by_contra hp
  have h1 := semilength_insidePart_lt hp
  omega

lemma decomp (p : DyckWord) (hnd : IsNondecreasing p) (h2 : 2 ≤ returns p) :
    p.outsidePart ≠ 0 ∧ VA p.insidePart = [] ∧ IsNondecreasing p.outsidePart ∧
      returns p = returns p.outsidePart + 1 ∧ p.insidePart.nest + p.outsidePart = p ∧
      p.insidePart.semilength + p.outsidePart.semilength + 1 = p.semilength := by
  have hp : p ≠ 0 := by
    rintro rfl
    rw [returns_zero] at h2
    omega
  have hd := nest_insidePart_add_outsidePart hp
  have hret := RET_decomp p.insidePart p.outsidePart
  rw [hd] at hret
  have hr : p.outsidePart ≠ 0 := by
    intro h0
    rw [h0, returns_zero] at hret
    omega
  have hnd' : IsNondecreasing (p.insidePart.nest + p.outsidePart) := by
    rw [hd]
    exact hnd
  obtain ⟨hv, hndr⟩ := (ND_nest_add _ _ hr).mp hnd'
  exact ⟨hr, hv, hndr, hret, hd, semilength_insidePart_add_semilength_outsidePart_add_one hp⟩

/-- Nondecreasing Dyck paths of semilength `n` whose number of returns satisfies `P`. -/
def S (n : ℕ) (P : ℕ → Prop) : Set DyckWord :=
  {p | p.semilength = n ∧ IsNondecreasing p ∧ P (returns p)}

lemma fin_sl (n : ℕ) : {p : DyckWord | p.semilength = n}.Finite := by
  have h : Finite {p : DyckWord // p.semilength = n} := inferInstance
  exact Set.finite_coe_iff.mp h

lemma S_fin (n : ℕ) (P : ℕ → Prop) : (S n P).Finite :=
  Set.Finite.subset (fin_sl n) (fun _ hp => hp.1)

lemma S_congr (n : ℕ) (P Q : ℕ → Prop) (h : ∀ j, P j ↔ Q j) : S n P = S n Q := by
  ext p
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, (h _).mp c⟩
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, (h _).mpr c⟩

def grow (p : DyckWord) : DyckWord := p.insidePart.nest.nest + p.outsidePart

def cap (r : DyckWord) : DyckWord := (0 : DyckWord).nest + r

lemma GROW (n : ℕ) (P : ℕ → Prop) :
    (S (n + 1) (fun j => P j ∧ 2 ≤ j)).ncard =
      (S n (fun j => P j ∧ 2 ≤ j)).ncard + (S n (fun j => P (j + 1) ∧ 1 ≤ j)).ncard := by
  have e : S (n + 1) (fun j => P j ∧ 2 ≤ j) =
      grow '' S n (fun j => P j ∧ 2 ≤ j) ∪ cap '' S n (fun j => P (j + 1) ∧ 1 ≤ j) := by
    ext p'
    constructor
    · rintro ⟨hs, hnd, hP, h2⟩
      obtain ⟨hr, hv, hndr, hret, hd, hsl⟩ := decomp p' hnd h2
      by_cases hq : p'.insidePart = 0
      · refine Or.inr ⟨p'.outsidePart, ⟨?_, hndr, ?_, ?_⟩, ?_⟩
        · rw [hq, semilength_zero] at hsl
          omega
        · rw [← hret]
          exact hP
        · omega
        · show (0 : DyckWord).nest + p'.outsidePart = p'
          rw [← hq]
          exact hd
      · have hd2 := nest_insidePart_add_outsidePart hq
        have hr2 : p'.insidePart.outsidePart = 0 := by
          by_contra h0
          apply VA_ne_nil p'.insidePart.insidePart p'.insidePart.outsidePart h0
          rw [hd2]
          exact hv
        rw [hr2, add_zero] at hd2
        have hv2 : VA p'.insidePart.insidePart = [] := by
          rw [← VA_nest_eq_nil, hd2]
          exact hv
        have hsl2 : p'.insidePart.insidePart.semilength + 1 = p'.insidePart.semilength := by
          rw [← semilength_nest, hd2]
        refine Or.inl ⟨p'.insidePart.insidePart.nest + p'.outsidePart, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [semilength_add, semilength_nest]
          omega
        · exact (ND_nest_add _ _ hr).mpr ⟨hv2, hndr⟩
        · rw [RET_decomp, ← hret]
          exact hP
        · rw [RET_decomp, ← hret]
          exact h2
        · unfold grow
          rw [ins_na, out_na, hd2]
          exact hd
    · rintro (⟨p, ⟨hs, hnd, hP, h2⟩, rfl⟩ | ⟨r, ⟨hs, hnd, hP, h1⟩, rfl⟩)
      · obtain ⟨hr, hv, hndr, hret, hd, hsl⟩ := decomp p hnd h2
        have hg : returns (grow p) = returns p := by
          unfold grow
          rw [RET_decomp]
          exact hret.symm
        refine ⟨?_, ?_, ?_⟩
        · unfold grow
          rw [semilength_add, semilength_nest, semilength_nest]
          omega
        · exact (ND_nest_add _ _ hr).mpr ⟨(VA_nest_eq_nil _).mpr hv, hndr⟩
        · show P (returns (grow p)) ∧ 2 ≤ returns (grow p)
          rw [hg]
          exact ⟨hP, h2⟩
      · have hr : r ≠ 0 := by
          rintro rfl
          rw [returns_zero] at h1
          omega
        have hg : returns (cap r) = returns r + 1 := RET_decomp 0 r
        refine ⟨?_, ?_, ?_⟩
        · unfold cap
          rw [semilength_add, semilength_nest, semilength_zero]
          omega
        · exact (ND_nest_add _ _ hr).mpr ⟨VA_zero, hnd⟩
        · show P (returns (cap r)) ∧ 2 ≤ returns (cap r)
          rw [hg]
          exact ⟨hP, by omega⟩
  have hdisj : Disjoint (grow '' S n (fun j => P j ∧ 2 ≤ j))
      (cap '' S n (fun j => P (j + 1) ∧ 1 ≤ j)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, _, rfl⟩ ⟨r, _, h⟩
    have h3 := congrArg insidePart h
    unfold cap grow at h3
    rw [ins_na, ins_na] at h3
    exact nest_ne_zero h3.symm
  have hinj1 : Set.InjOn grow (S n (fun j => P j ∧ 2 ≤ j)) := by
    rintro p ⟨_, hnd, _, h2⟩ p' ⟨_, hnd', _, h2'⟩ h
    obtain ⟨_, _, _, _, hd, _⟩ := decomp p hnd h2
    obtain ⟨_, _, _, _, hd', _⟩ := decomp p' hnd' h2'
    have h3 := congrArg insidePart h
    have h4 := congrArg outsidePart h
    unfold grow at h3 h4
    rw [ins_na, ins_na] at h3
    rw [out_na, out_na] at h4
    have h5 := congrArg insidePart h3
    rw [insidePart_nest, insidePart_nest] at h5
    rw [← hd, ← hd', h5, h4]
  have hinj2 : Set.InjOn cap (S n (fun j => P (j + 1) ∧ 1 ≤ j)) := by
    intro r _ r' _ h
    exact add_left_cancel h
  rw [e, Set.ncard_union_eq hdisj ((S_fin _ _).image _) ((S_fin _ _).image _),
    Set.ncard_image_of_injOn hinj1, Set.ncard_image_of_injOn hinj2]

lemma NEST (n : ℕ) : (S (n + 1) (fun j => j = 1)).ncard = (S n (fun _ => True)).ncard := by
  have e : S (n + 1) (fun j => j = 1) = nest '' S n (fun _ => True) := by
    ext p
    constructor
    · rintro ⟨hs, hnd, h1⟩
      have h1' : returns p = 1 := h1
      have hp : p ≠ 0 := by
        rintro rfl
        rw [returns_zero] at h1'
        omega
      have hd := nest_insidePart_add_outsidePart hp
      have hret := RET_decomp p.insidePart p.outsidePart
      rw [hd] at hret
      have hsl := semilength_insidePart_add_semilength_outsidePart_add_one hp
      have hr : p.outsidePart = 0 := by
        by_contra h0
        have h3 := returns_pos _ h0
        omega
      rw [hr, add_zero] at hd
      rw [hr, semilength_zero] at hsl
      refine ⟨p.insidePart, ⟨by omega, ?_, trivial⟩, hd⟩
      rw [← ND_nest, hd]
      exact hnd
    · rintro ⟨q, ⟨hs, hnd, _⟩, rfl⟩
      refine ⟨?_, (ND_nest q).mpr hnd, ?_⟩
      · rw [semilength_nest, hs]
      · have h := RET_decomp q 0
        rw [add_zero, returns_zero] at h
        exact h
  have hinj : Function.Injective nest := by
    intro q q' h
    have h3 := congrArg insidePart h
    rw [insidePart_nest, insidePart_nest] at h3
    exact h3
  rw [e, Set.ncard_image_of_injective _ hinj]

lemma SPLIT (n : ℕ) : (S (n + 1) (fun _ => True)).ncard =
    (S (n + 1) (fun j => j = 1)).ncard + (S (n + 1) (fun j => True ∧ 2 ≤ j)).ncard := by
  have hdisj : Disjoint (S (n + 1) (fun j => j = 1)) (S (n + 1) (fun j => True ∧ 2 ≤ j)) := by
    rw [Set.disjoint_left]
    rintro p ⟨_, _, h1⟩ ⟨_, _, _, h2⟩
    have h1' : returns p = 1 := h1
    omega
  rw [← Set.ncard_union_eq hdisj (S_fin _ _) (S_fin _ _)]
  congr 1
  ext p
  constructor
  · rintro ⟨hs, hnd, _⟩
    have hp : p ≠ 0 := by
      rintro rfl
      rw [semilength_zero] at hs
      omega
    have h3 := returns_pos p hp
    by_cases h1 : returns p = 1
    · exact Or.inl ⟨hs, hnd, h1⟩
    · exact Or.inr ⟨hs, hnd, trivial, by omega⟩
  · rintro (⟨hs, hnd, _⟩ | ⟨hs, hnd, _⟩)
    · exact ⟨hs, hnd, trivial⟩
    · exact ⟨hs, hnd, trivial⟩

lemma S_zero_empty (P : ℕ → Prop) (hP : ¬ P 0) : (S 0 P).ncard = 0 := by
  have e : S 0 P = ∅ := by
    apply Set.subset_empty_iff.mp
    rintro p ⟨hs, _, h⟩
    have h0 := eq_zero_of_semilength p hs
    subst h0
    rw [returns_zero] at h
    exact (hP h).elim
  rw [e, Set.ncard_empty]

lemma S_zero_true : (S 0 (fun _ => True)).ncard = 1 := by
  have e : S 0 (fun _ => True) = {0} := by
    ext p
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs, _, _⟩
      exact eq_zero_of_semilength p hs
    · rintro rfl
      exact ⟨rfl, ND_of_VA_nil 0 VA_zero, trivial⟩
  rw [e, Set.ncard_singleton]

lemma S_pos_true (n : ℕ) :
    S (n + 1) (fun j => True ∧ 1 ≤ j) = S (n + 1) (fun _ => True) := by
  ext p
  constructor
  · rintro ⟨hs, hnd, _⟩
    exact ⟨hs, hnd, trivial⟩
  · rintro ⟨hs, hnd, _⟩
    have hp : p ≠ 0 := by
      rintro rfl
      rw [semilength_zero] at hs
      omega
    exact ⟨hs, hnd, trivial, returns_pos p hp⟩

noncomputable def a (n k : ℕ) : ℕ := (S n (fun j => j = k)).ncard

noncomputable def tot (n : ℕ) : ℕ := (S n (fun _ => True)).ncard

noncomputable def u (n : ℕ) : ℕ := (S n (fun j => True ∧ 2 ≤ j)).ncard

lemma a_pascal (n k : ℕ) : a (n + 1) (k + 2) = a n (k + 2) + a n (k + 1) := by
  have h := GROW n (fun j => j = k + 2)
  rw [S_congr (n + 1) (fun j => j = k + 2 ∧ 2 ≤ j) (fun j => j = k + 2) (fun j => by omega),
    S_congr n (fun j => j = k + 2 ∧ 2 ≤ j) (fun j => j = k + 2) (fun j => by omega),
    S_congr n (fun j => j + 1 = k + 2 ∧ 1 ≤ j) (fun j => j = k + 1) (fun j => by omega)] at h
  exact h

lemma a_zero (k : ℕ) : a 0 (k + 1) = 0 := S_zero_empty _ (by omega)

lemma a_one (n : ℕ) : a (n + 1) 1 = tot n := NEST n

lemma tot_succ (n : ℕ) : tot (n + 1) = a (n + 1) 1 + u (n + 1) := SPLIT n

lemma u_one : u 1 = 0 := by
  have h := GROW 0 (fun _ => True)
  rw [S_zero_empty _ (by omega), S_zero_empty _ (by omega)] at h
  exact h

lemma u_succ (n : ℕ) : u (n + 2) = u (n + 1) + tot (n + 1) := by
  have h := GROW (n + 1) (fun _ => True)
  rw [S_pos_true] at h
  exact h

lemma tot_u (n : ℕ) : tot (n + 1) = Nat.fib (2 * n + 1) ∧ u (n + 1) = Nat.fib (2 * n) := by
  induction n with
  | zero =>
    have h1 : tot 1 = a 1 1 + u 1 := tot_succ 0
    have h2 : a 1 1 = tot 0 := a_one 0
    have h3 : tot 0 = 1 := S_zero_true
    have h4 := u_one
    constructor
    · show tot 1 = Nat.fib 1
      rw [Nat.fib_one]
      omega
    · show u 1 = Nat.fib 0
      rw [Nat.fib_zero]
      exact h4
  | succ n ih =>
    have h1 : tot (n + 2) = a (n + 2) 1 + u (n + 2) := tot_succ (n + 1)
    have h2 : a (n + 2) 1 = tot (n + 1) := a_one (n + 1)
    have h3 := u_succ n
    have f1 : Nat.fib (2 * (n + 1)) = Nat.fib (2 * n) + Nat.fib (2 * n + 1) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, Nat.fib_add_two]
    have f2 : Nat.fib (2 * (n + 1) + 1) = Nat.fib (2 * n + 1) + Nat.fib (2 * (n + 1)) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.fib_add_two,
        show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
    constructor
    · show tot (n + 2) = _
      omega
    · show u (n + 2) = _
      omega

lemma a_two (n : ℕ) : a (n + 2) 2 = 1 + Nat.fib (2 * n) := by
  induction n with
  | zero =>
    have h1 : a 2 2 = a 1 2 + a 1 1 := a_pascal 1 0
    have h2 : a 1 2 = a 0 2 + a 0 1 := a_pascal 0 0
    have h3 : a 0 2 = 0 := a_zero 1
    have h4 : a 0 1 = 0 := a_zero 0
    have h5 : a 1 1 = tot 0 := a_one 0
    have h6 : tot 0 = 1 := S_zero_true
    show a 2 2 = 1 + Nat.fib 0
    rw [Nat.fib_zero]
    omega
  | succ n ih =>
    have h1 : a (n + 3) 2 = a (n + 2) 2 + a (n + 2) 1 := a_pascal (n + 2) 0
    have h2 : a (n + 2) 1 = tot (n + 1) := a_one (n + 1)
    have h3 := (tot_u n).1
    have f1 : Nat.fib (2 * (n + 1)) = Nat.fib (2 * n) + Nat.fib (2 * n + 1) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, Nat.fib_add_two]
    show a (n + 3) 2 = _
    omega

lemma T_zero (k : ℕ) : T 0 k = 0 := by
  rw [T]

lemma T_rec (n k : ℕ) (hk : 2 ≤ k) : T (n + 1) k = T n (k - 1) + T n k := by
  rw [T, if_neg (by omega), if_neg (by omega)]

lemma T_one (n : ℕ) : T (n + 1) 1 = Nat.fib (2 * (n + 1)) := by
  rw [T, if_neg (by omega), if_pos rfl]

lemma T_two (n : ℕ) : T (n + 1) 2 + 1 = Nat.fib (2 * n + 1) := by
  induction n with
  | zero =>
    have h1 : T 1 2 = T 0 1 + T 0 2 := T_rec 0 2 (le_refl 2)
    rw [T_zero, T_zero] at h1
    show T 1 2 + 1 = Nat.fib 1
    rw [Nat.fib_one]
    omega
  | succ n ih =>
    have h1 : T (n + 2) 2 = T (n + 1) 1 + T (n + 1) 2 := T_rec (n + 1) 2 (le_refl 2)
    have h2 := T_one n
    have f2 : Nat.fib (2 * (n + 1) + 1) = Nat.fib (2 * n + 1) + Nat.fib (2 * (n + 1)) := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.fib_add_two,
        show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
    show T (n + 2) 2 + 1 = _
    omega

lemma key (n : ℕ) : ∀ k : ℕ, 2 ≤ k → a (n + 1) k + T n k = T n (k - 1) := by
  induction n with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have h1 : a 1 (k' + 2) = a 0 (k' + 2) + a 0 (k' + 1) := a_pascal 0 k'
    have h2 : a 0 (k' + 2) = 0 := a_zero (k' + 1)
    have h3 : a 0 (k' + 1) = 0 := a_zero k'
    show a 1 (k' + 2) + T 0 (k' + 2) = T 0 (k' + 2 - 1)
    rw [T_zero, T_zero]
    omega
  | succ n ih =>
    intro k hk
    by_cases h2 : k = 2
    · subst h2
      have h3 := a_two n
      have h4 := T_two n
      have h5 := T_one n
      have f1 : Nat.fib (2 * (n + 1)) = Nat.fib (2 * n) + Nat.fib (2 * n + 1) := by
        rw [show 2 * (n + 1) = 2 * n + 2 by ring, Nat.fib_add_two]
      show a (n + 2) 2 + T (n + 1) 2 = T (n + 1) 1
      omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
      have h3 : a (n + 2) (k' + 3) = a (n + 1) (k' + 3) + a (n + 1) (k' + 2) :=
        a_pascal (n + 1) (k' + 1)
      have h4 : T (n + 1) (k' + 3) = T n (k' + 2) + T n (k' + 3) := T_rec n (k' + 3) (by omega)
      have h5 : T (n + 1) (k' + 2) = T n (k' + 1) + T n (k' + 2) := T_rec n (k' + 2) (by omega)
      have h6 : a (n + 1) (k' + 3) + T n (k' + 3) = T n (k' + 2) := ih (k' + 3) (by omega)
      have h7 : a (n + 1) (k' + 2) + T n (k' + 2) = T n (k' + 1) := ih (k' + 2) (by omega)
      show a (n + 2) (k' + 3) + T (n + 1) (k' + 3) = T (n + 1) (k' + 2)
      omega

end OMA.P125172

open OMA.S_oeis_a125172 OMA.P125172 in
theorem OMA.solution : type_of% @OMA.S_oeis_a125172.main := by
  intro n k hk _
  have h := key n k hk
  have h2 : A121460 (n + 1) k = a (n + 1) k := rfl
  rw [h2]
  omega
