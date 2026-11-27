import FormalConjectures.ErdosProblems.«346»

/-! Consecutive blocks separated by jumps just below the total of the
preceding terms. Alternating the offset at the jumps prevents a missing
subset sum in a tail from persisting across successive blocks. -/

open Finset Set Filter
open scoped Topology
noncomputable section
namespace BlockSums

private def total (s : Finset ℕ) := ∑ x ∈ s, x
private def rep (s : Finset ℕ) (v : ℕ) := ∃ t ⊆ s, total t = v

private lemma rep_mono {s t : Finset ℕ} {v : ℕ} (h : s ⊆ t) :
    rep s v → rep t v := fun ⟨u,hu,he⟩ => ⟨u,hu.trans h,he⟩

private lemma rep_single {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) : rep s x :=
  ⟨{x}, by simpa using hx, by simp [total]⟩

private lemma rep_pair {s : Finset ℕ} {x y : ℕ} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    rep s (x+y) :=
  ⟨{x,y}, Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy), by simp [total,hne]⟩

private lemma total_union {s t : Finset ℕ} (h : Disjoint s t) :
    total (s ∪ t) = total s + total t := Finset.sum_union h

private lemma total_sdiff {s t : Finset ℕ} (h : t ⊆ s) :
    total (s \ t) + total t = total s := sum_sdiff h

private lemma complement {s : Finset ℕ} {x : ℕ} : rep s x → rep s (total s - x) := by
  rintro ⟨t,ht,rfl⟩
  exact ⟨s \ t, sdiff_subset, by have := total_sdiff ht; omega⟩

private lemma rep_add {s t : Finset ℕ} {x y : ℕ} (hd : Disjoint s t)
    (hx : rep s x) (hy : rep t y) : rep (s ∪ t) (x+y) := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  exact ⟨a ∪ b, Finset.union_subset_union ha hb, total_union (hd.mono ha hb)⟩

private def block (b : ℕ) := Finset.Icc b (8*b)
private def extra (b k : ℕ) := total (Finset.Ioc (2*b) k)

private lemma extra_succ {b k : ℕ} (h : 2*b ≤ k) :
    extra b (k+1) = extra b k + (k+1) := by
  have he : Finset.Ioc (2*b) (k+1) = insert (k+1) (Finset.Ioc (2*b) k) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  simp [extra,total,he,add_comm]

private lemma core {b x : ℕ} (hb : 2 ≤ b) (hx : b ≤ x) (hu : x < 4*b) :
    rep (Finset.Icc b (2*b)) x := by
  by_cases h : x ≤ 2*b
  · exact rep_single (mem_Icc.mpr ⟨hx,h⟩)
  by_cases hh : x ≤ 3*b
  · convert rep_pair (s := Finset.Icc b (2*b)) (x := b) (y := x-b)
        (mem_Icc.mpr ⟨le_rfl,by omega⟩) (mem_Icc.mpr ⟨by omega,by omega⟩) (by omega) using 1; omega
  · convert rep_pair (s := Finset.Icc b (2*b)) (x := 2*b) (y := x-2*b)
        (mem_Icc.mpr ⟨by omega,le_rfl⟩) (mem_Icc.mpr ⟨by omega,by omega⟩) (by omega) using 1; omega

private lemma from_core {b : ℕ} (hb : 2 ≤ b) {k : ℕ} (hk : 2*b ≤ k) :
    k ≤ extra b k + 2*b ∧
      ∀ x, b ≤ x → x < extra b k + 4*b → rep (Finset.Icc b k) x := by
  induction k, hk using Nat.le_induction with
  | base => simpa [extra,total] using And.intro (le_refl (2*b)) (fun x => core (x := x) hb)
  | succ k hk ih =>
    rw [extra_succ hk]
    refine ⟨by omega, ?_⟩
    intro x hxl hxu
    have hs : Finset.Icc b k ⊆ Finset.Icc b (k+1) :=
      Finset.Icc_subset_Icc le_rfl (by omega)
    by_cases h : x < extra b k + 4*b
    · exact rep_mono hs (ih.2 x hxl h)
    obtain ⟨t,ht,he⟩ := ih.2 (x-(k+1)) (by omega) (by omega)
    have hnot : k+1 ∉ t := fun hm => by have := (mem_Icc.mp (ht hm)).2; omega
    refine ⟨insert (k+1) t, Finset.insert_subset (mem_Icc.mpr ⟨by omega, le_rfl⟩) (ht.trans hs), ?_⟩
    simp only [total, Finset.sum_insert hnot] at he ⊢
    omega

private lemma block_estimates {b : ℕ} (hb : 2 ≤ b) :
    10*b*b ≤ total (block b) ∧ total (block b) ≤ 2 * extra b (8*b) := by
  let lo := Finset.Icc b (2*b)
  let hi := Finset.Ioc (2*b) (8*b)
  have eq : block b = lo ∪ hi := by
    ext x
    simp only [block,lo,hi,Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hd : Disjoint lo hi := Finset.disjoint_left.mpr (fun x hx hy => by
    have := (mem_Icc.mp hx).2; have := (mem_Ioc.mp hy).1; omega)
  have hcl : lo.card = b+1 := by simp [lo,Nat.card_Icc]; omega
  have hch : hi.card = 6*b := by simp [hi,Nat.card_Ioc]; omega
  have upper : total lo ≤ (b+1)*(2*b) := by
    simpa [total,hcl] using (sum_le_sum (s := lo) (fun x hx => (mem_Icc.mp hx).2))
  have lower : (6*b)*(2*b) ≤ total hi := by
    simpa [total,hch] using (sum_le_sum (s := hi) (fun x hx => (mem_Ioc.mp hx).1.le))
  rw [eq,total_union hd]
  change _ ∧ total lo + total hi ≤ 2 * total hi
  constructor <;> nlinarith

private lemma block_interval {b x : ℕ} (hb : 2 ≤ b) (hl : b ≤ x)
    (hu : x + b ≤ total (block b)) : rep (block b) x := by
  have h := (from_core hb (k := 8*b) (by omega)).2
  have ht := (block_estimates hb).2
  by_cases hx : x < extra b (8*b) + 4*b
  · exact h _ hl hx
  · have hr := complement (s := block b) (h (total (block b)-x) (by omega) (by omega))
    simpa [Nat.sub_sub_self (by omega : x ≤ total (block b))] using hr

private def bump (j : ℕ) := if Even j then 0 else j

private def stage : ℕ → ℕ × Finset ℕ
  | 0 => (10, ∅)
  | j+1 =>
    let (b,s) := stage j
    let u := s ∪ block b
    (total u - b + bump j, u)

private abbrev base (j : ℕ) := (stage j).1
private abbrev pref (j : ℕ) := (stage j).2

private lemma pref_succ (j : ℕ) : pref (j+1) = pref j ∪ block (base j) := rfl
private lemma base_succ (j : ℕ) :
    base (j+1) = total (pref (j+1)) - base j + bump j := rfl

private lemma inv (j : ℕ) :
    2 ≤ base j ∧ j ≤ base j ∧ (∀ x ∈ pref j, x < base j) ∧ total (pref j) ≤ 2*base j := by
  induction j with
  | zero => decide
  | succ j ih =>
    obtain ⟨hb,hj,hp,ht⟩ := ih
    have hd : Disjoint (pref j) (block (base j)) :=
      Finset.disjoint_left.mpr fun x hx hy => (hp x hx).not_ge (mem_Icc.mp hy).1
    have hsum : total (pref (j+1)) = total (pref j) + total (block (base j)) := by
      rw [pref_succ,total_union hd]
    have hbig := (block_estimates hb).1
    have hquad : 10*base j ≤ total (block (base j)) := by nlinarith
    have hn := base_succ j
    refine ⟨by omega, by omega, ?_, by omega⟩
    intro x hx
    rw [pref_succ] at hx
    rcases mem_union.mp hx with h|h
    · have := hp x h; omega
    · have := (mem_Icc.mp h).2; omega

private lemma sum_step (j : ℕ) :
    total (pref (j+1)) = total (pref j) + total (block (base j)) := by
  rw [pref_succ,total_union]
  exact Finset.disjoint_left.mpr fun x hx hy => ((inv j).2.2.1 x hx).not_ge (mem_Icc.mp hy).1

private lemma grow (j : ℕ) : 9*base j*base j ≤ base (j+1) := by
  have hh := (block_estimates (inv j).1).1
  have hb := (inv j).1
  have hl : base j ≤ total (pref (j+1)) := by rw [sum_step]; nlinarith
  have := Nat.sub_add_cancel hl
  rw [base_succ]
  have := sum_step j
  nlinarith

private lemma gap (j : ℕ) : 8*base j + 2 ≤ base (j+1) := by
  have := grow j; have := (inv j).1; nlinarith

private lemma base_mono : StrictMono base :=
  strictMono_nat_of_lt_succ fun j => by have := gap j; omega

private lemma pref_mono : Monotone pref :=
  monotone_nat_of_le_succ fun j => by rw [pref_succ]; exact subset_union_left

private def domain : Set ℕ := {x | ∃ j, x ∈ block (base j)}

private lemma before {j x : ℕ} (hx : x ∈ domain) (hl : x < base j) : x ∈ pref j := by
  obtain ⟨k,hk⟩ := hx
  have hkj : k < j := by
    have := (mem_Icc.mp hk).1
    exact base_mono.lt_iff_lt.mp (by omega)
  apply pref_mono (show k+1 ≤ j by omega)
  rw [pref_succ]
  exact mem_union_right _ hk

private lemma in_domain {j x : ℕ} (h : x ∈ pref j) : x ∈ domain := by
  induction j with
  | zero => exact False.elim (Finset.notMem_empty _ h)
  | succ j ih =>
    rw [pref_succ] at h
    rcases mem_union.mp h with h|h
    · exact ih h
    · exact ⟨_,h⟩

private def tail (J : ℕ) := domain \ (pref J : Set ℕ)

private lemma restart {J j : ℕ} (hj : J ≤ j) :
    pref (j+1) \ pref J = (pref j \ pref J) ∪ block (base j) := by
  ext x
  rw [pref_succ]
  simp only [Finset.mem_sdiff,Finset.mem_union]
  have dis : x ∈ block (base j) → x ∉ pref J := fun h hx =>
    ((inv j).2.2.1 x (pref_mono hj hx)).not_ge (mem_Icc.mp h).1
  tauto

private lemma central {J j x : ℕ} (hj : J ≤ j) (hl : base j ≤ x)
    (hu : x + base j ≤ total (pref (j+1) \ pref J)) :
    rep (pref (j+1) \ pref J) x := by
  let S := pref j \ pref J
  let b := base j
  have hd : Disjoint S (block b) := Finset.disjoint_left.mpr (fun a ha hb =>
    ((inv j).2.2.1 a (mem_sdiff.mp ha).1).not_ge (mem_Icc.mp hb).1)
  rw [restart hj] at hu ⊢
  change x+b ≤ total (S ∪ block b) at hu
  rw [total_union hd] at hu
  change rep (S ∪ block b) x
  by_cases h : x+b ≤ total (block b)
  · exact rep_mono subset_union_right (block_interval (inv j).1 hl h)
  have hS : total S ≤ 2*b := by
    have := total_sdiff (pref_mono hj)
    have := (inv j).2.2.2
    dsimp [S,b]; omega
  have hb : 2 ≤ b := (inv j).1
  have high := (block_estimates hb).1
  have h4 : 4*b ≤ total (block b) := by nlinarith [Nat.mul_le_mul_left b hb]
  have hxl : b ≤ x-total S := by omega
  have hr := block_interval hb hxl (show x-total S+b ≤ total (block b) by omega)
  have hs : rep S (total S) := ⟨S,Finset.Subset.rfl,rfl⟩
  simpa [Nat.add_sub_of_le (show total S ≤ x by omega)] using rep_add hd hs hr

private lemma lift_rep {J j x : ℕ} (h : rep (pref j \ pref J) x) : x ∈ subsetSums (tail J) := by
  obtain ⟨s,hs,rfl⟩ := h
  exact ⟨s, fun a ha => ⟨in_domain (Finset.mem_sdiff.mp (hs ha)).1,
    (Finset.mem_sdiff.mp (hs ha)).2⟩, rfl⟩

/-- Complementing a missing sum in its truncated prefix gives a missing sum one
stage earlier. Their distances from the next block starts add to the total
removed at the beginning, plus the current offset. -/
private lemma back {J i x : ℕ} (hJ : J ≤ i) (hP : total (pref J) ≤ i)
    (hl : base (i+1) ≤ x) (hu : x < base (i+2)) (hx : x ∉ subsetSums (tail J)) :
    ∃ y, base i ≤ y ∧ y < base (i+1) ∧ y ∉ subsetSums (tail J) ∧
      (base (i+2)-x) + (base (i+1)-y) = total (pref J) + bump (i+1) := by
  let s := pref (i+2) \ pref J
  have hs : total s + total (pref J) = total (pref (i+2)) :=
    total_sdiff (pref_mono (by omega))
  have hb := base_succ (i+1)
  simp only [Nat.add_assoc,Nat.reduceAdd] at hb
  have hbi := (inv i).2.1
  have hg := gap i
  have hg' := gap (i+1)
  have hbu : bump (i+1) ≤ i+1 := by unfold bump; split <;> omega
  have hsum : base (i+1) ≤ total (pref (i+2)) := by
    have he := (block_estimates (inv (i+1)).1).1
    rw [sum_step]; nlinarith [(inv (i+1)).1]
  have hxs : x ≤ total s := by omega
  let y := total s-x
  have hy : y < base (i+1) := by
    by_contra! hc
    exact hx (lift_rep (central (J := J) (j := i+1) (by omega) hl
      (show x + base (i+1) ≤ total s by dsimp [y] at hc; omega)))
  have heq : (base (i+2)-x) + (base (i+1)-y) = total (pref J) + bump (i+1) := by
    dsimp [y] at *; omega
  refine ⟨y,by omega,hy,?_,heq⟩
  rintro ⟨t,ht,het⟩
  have ht' : t ⊆ s := by
    intro a ha
    have ha' := ht ha
    have hal : a ≤ y := by rw [het]; exact Finset.single_le_sum (fun n _ => Nat.zero_le n) ha
    exact Finset.mem_sdiff.mpr ⟨pref_mono (show i+1 ≤ i+2 by omega)
      (before ha'.1 (by omega)),ha'.2⟩
  have hr := complement (show rep s y from ⟨t,ht',het.symm⟩)
  have he : total s-y = x := by dsimp [y]; omega
  rw [he] at hr
  exact hx (lift_rep hr)

/-- Three consecutive deficits cannot obey the complement equations: the
middle (odd) offset exceeds the entire deleted prefix, while both even
offsets vanish. -/
private lemma no_even_holes {J k x : ℕ} (hJ : J ≤ k) (hP : total (pref J) ≤ k)
    (hp : Even (k+3)) (hl : base (k+3) ≤ x) (hu : x < base (k+4)) :
    x ∈ subsetSums (tail J) := by
  by_contra hx
  obtain ⟨y,hly,huy,hy,ey⟩ := back (i := k+2) (by omega) (by omega) hl hu hx
  obtain ⟨z,hlz,huz,hz,ez⟩ := back (i := k+1) (by omega) (by omega) hly huy hy
  obtain ⟨w,hlw,huw,hw,ew⟩ := back hJ hP hlz huz hz
  have p2 : ¬ Even (k+2) := by rw [Nat.even_iff] at *; omega
  have p1 : Even (k+1) := by rw [Nat.even_iff] at *; omega
  simp only [Nat.add_assoc,Nat.reduceAdd,bump, if_pos hp, if_pos p1, if_neg p2] at ey ez ew
  omega

private lemma tail_complete (J : ℕ) : IsAddComplete (tail J) := by
  classical
  let K := max J (total (pref J))
  refine Filter.eventually_atTop.mpr ⟨base (K+4), fun x hx => ?_⟩
  have ex : ∃ j, x < base j := ⟨x+1,by have := (inv (x+1)).2.1; omega⟩
  let m := Nat.find ex
  have hm : x < base m := Nat.find_spec ex
  have hlm : K+4 < m := base_mono.lt_iff_lt.mp (lt_of_le_of_lt hx hm)
  obtain ⟨k,hk⟩ : ∃ k, m = k+5 := ⟨m-5,by omega⟩
  have hxl : base (k+4) ≤ x := le_of_not_gt (Nat.find_min ex (show k+4 < m by omega))
  rw [hk] at hm
  have hJ : J ≤ k := by have := le_max_left J (total (pref J)); dsimp [K] at hlm; omega
  have hP : total (pref J) ≤ k := by have := le_max_right J (total (pref J)); dsimp [K] at hlm; omega
  by_cases h : Even (k+4)
  · exact no_even_holes (k := k+1) (by omega) (by omega) h hxl hm
  by_contra hn
  obtain ⟨y,hly,huy,hy,_⟩ := back (i := k+3) (by omega) (by omega) hxl hm hn
  exact hy (no_even_holes hJ hP (by rw [Nat.even_iff] at *; omega) hly huy)

private lemma destroyed {B : Set ℕ} (hs : B ⊆ domain) (hb : B.Infinite) :
    ¬ IsAddComplete (domain \ B) := by
  intro hc
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hc
  obtain ⟨t,ht,ht1⟩ := hb.exists_gt 1
  obtain ⟨y,hy,hy1⟩ := hb.exists_gt (8*(N+t+1))
  obtain ⟨j,hj⟩ := hs hy
  have hyb := Finset.mem_Icc.mp hj
  have hg := gap j
  let v := base (j+1)-1
  have hvl : N ≤ v := by dsimp [v]; omega
  obtain ⟨s,hs',he⟩ := hN v hvl
  have hss : s ⊆ pref (j+1) := by
    intro a ha
    have hal : a ≤ v := by rw [he]; exact Finset.single_le_sum (fun n _ => Nat.zero_le n) ha
    exact before (hs' ha).1 (by dsimp [v] at hal; omega)
  have hty : t ≠ y := by omega
  have hts : t ∉ s := fun h => (hs' h).2 ht
  have hys : y ∉ s := fun h => (hs' h).2 hy
  have hsub : insert t (insert y s) ⊆ pref (j+1) :=
    Finset.insert_subset (before (hs ht) (by omega))
      (Finset.insert_subset (before (hs hy) (by omega)) hss)
  have hle : total (insert t (insert y s)) ≤ total (pref (j+1)) :=
    Finset.sum_le_sum_of_subset hsub
  have hit : t ∉ insert y s := by simp [hty,hts]
  simp only [total,Finset.sum_insert hit,Finset.sum_insert hys] at hle
  have he' : v = total s := he
  change t+(y+total s) ≤ total (pref (j+1)) at hle
  have heq := base_succ j
  dsimp [v] at he'
  omega

private lemma base_mem (j : ℕ) : base j ∈ domain :=
  ⟨j,Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩

private lemma infinite_domain : domain.Infinite := Set.infinite_iff_exists_gt.mpr fun n =>
  ⟨base (n+1),base_mem _,by have := (inv (n+1)).2.1; omega⟩

private noncomputable def seq : ℕ → ℕ := Nat.nth (· ∈ domain)
private lemma seq_mono : StrictMono seq := Nat.nth_strictMono infinite_domain
private lemma seq_range : Set.range seq = domain := Nat.range_nth_of_infinite infinite_domain
private lemma seq_mem (n : ℕ) : seq n ∈ domain := seq_range ▸ Set.mem_range_self n

private lemma seq_pos (n : ℕ) : 0 < seq n := by
  obtain ⟨j,h⟩ := seq_mem n
  have := (Finset.mem_Icc.mp h).1; have := (inv j).1; omega

private lemma seq_strong : IsAddStronglyCompleteNatSeq seq := by
  intro n
  let J := seq n + 1
  apply (tail_complete J).mono
  rintro x ⟨hx,hn⟩
  have hlarge : base J ≤ x := le_of_not_gt fun h => hn (before hx h)
  rw [← seq_range] at hx
  obtain ⟨m,rfl⟩ := hx
  have hnm : n ≤ m := seq_mono.le_iff_le.mp (by have := (inv J).2.1; dsimp [J] at *; omega)
  exact ⟨m-n,congrArg seq (Nat.add_sub_of_le hnm)⟩

private lemma first_step (j : ℕ) : ∃ i, seq i = base j ∧ seq (i+1) = base j+1 := by
  obtain ⟨i,hi⟩ := seq_range.symm ▸ base_mem j
  have h : base j+1 ∈ domain := ⟨j,Finset.mem_Icc.mpr ⟨by omega,by have := (inv j).1; omega⟩⟩
  rw [← seq_range] at h
  obtain ⟨k,hk⟩ := h
  have hik : i < k := seq_mono.lt_iff_lt.mp (by omega)
  have := seq_mono.monotone (show i+1 ≤ k by omega)
  have := seq_mono (show i < i+1 by omega)
  exact ⟨i,hi,by omega⟩

private lemma last_step (j : ℕ) :
    ∃ i, seq i = 8*base j ∧ base (j+1) ≤ seq (i+1) := by
  have h : 8*base j ∈ domain := ⟨j,Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
  rw [← seq_range] at h
  obtain ⟨i,hi⟩ := h
  refine ⟨i,hi,le_of_not_gt fun hc => ?_⟩
  have hp := before (seq_mem (i+1)) hc
  rw [pref_succ] at hp
  have hn := seq_mono (show i < i+1 by omega)
  rcases Finset.mem_union.mp hp with hp|hp
  · have := (inv j).2.2.1 _ hp; omega
  · have := (Finset.mem_Icc.mp hp).2; omega

private def ratio (n : ℕ) : ℝ := seq (n+1) / (seq n : ℝ)

private lemma near_one {a : ℝ} (ha : 1 < a) : ∃ᶠ i in atTop, ratio i ≤ a := by
  obtain ⟨d,hd⟩ := exists_nat_gt (1/(a-1))
  have he := (div_lt_iff₀ (show 0 < a-1 by linarith)).mp hd
  apply frequently_atTop.mpr
  intro N
  let j := d + seq N
  obtain ⟨i,hi,hi'⟩ := first_step j
  have hj := (inv j).2.1
  have hNi : N ≤ i := seq_mono.le_iff_le.mp (by change d + seq N ≤ base j at hj; omega)
  have hd' : (d : ℝ) ≤ base j := by exact_mod_cast (show d ≤ base j by change d + seq N ≤ base j at hj; omega)
  have hb : 0 < (base j : ℝ) := by exact_mod_cast (show 0 < base j by have := (inv j).1; omega)
  refine ⟨i,hNi,?_⟩
  simp only [ratio,hi,hi',Nat.cast_add,Nat.cast_one]
  apply (div_le_iff₀ hb).mpr
  nlinarith [mul_le_mul_of_nonneg_right hd' (sub_nonneg.mpr ha.le)]

private lemma lower_ratio : liminf ratio atTop = 1 := by
  have hlow : ∀ n, 1 ≤ ratio n := by
    intro n
    have hh : (0 : ℝ) < seq n := by exact_mod_cast seq_pos n
    apply (le_div_iff₀ hh).mpr
    simpa using (show (seq n : ℝ) ≤ seq (n+1) by exact_mod_cast seq_mono.monotone (show n ≤ n+1 by omega))
  apply le_antisymm
  · by_contra! h
    obtain ⟨a,ha,ha'⟩ := exists_between h
    have hr := liminf_le_of_frequently_le (near_one ha)
      (show atTop.IsBoundedUnder (· ≥ ·) ratio from ⟨1,show ∀ᶠ n in atTop, ratio n ≥ 1 from Eventually.of_forall hlow⟩)
    linarith
  · apply le_liminf_of_le _ (Eventually.of_forall hlow)
    refine ⟨2,fun a ha => ?_⟩
    obtain ⟨n,hn,hn'⟩ := ((near_one (by norm_num : (1:ℝ) < 2)).and_eventually
      (show ∀ᶠ n in atTop, a ≤ ratio n from ha)).exists
    exact hn'.trans hn

private lemma upper_ratio : limsup (fun n => seq (n+1) / (seq n : ENNReal)) atTop = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  refine iSup_le fun d => le_limsup_of_frequently_le' (frequently_atTop.mpr fun N => ?_)
  let j := d + seq N
  obtain ⟨i,hi,hi'⟩ := last_step j
  have hj := (inv j).2.1
  have hNi : N ≤ i := seq_mono.le_iff_le.mp (by change d + seq N ≤ base j at hj; omega)
  have hdb : d ≤ base j := by change d + seq N ≤ base j at hj; omega
  have hbd : d * seq i ≤ seq (i+1) := by
    rw [hi]
    have hh := grow j
    nlinarith [Nat.mul_le_mul_right (8*base j) hdb]
  refine ⟨i,hNi,(ENNReal.le_div_iff_mul_le (Or.inl ?_) (Or.inl (by simp))).mpr ?_⟩
  · exact_mod_cast (seq_pos i).ne'
  · exact_mod_cast hbd

end BlockSums

open BlockSums in
theorem OMA.solution : type_of% @Erdos346.erdos_346.variants.example := by
  refine ⟨seq,seq_mono,seq_strong,?_,lower_ratio,upper_ratio⟩
  rw [seq_range]
  exact fun _ => destroyed
