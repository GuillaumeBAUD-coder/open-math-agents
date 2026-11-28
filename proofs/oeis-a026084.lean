import OMAStatements.S_oeis_a026084

/-! A local moment identity for unconstrained walks with steps -1, 0 and 1.
After three forced nonzero steps the endpoint-one count is a weighted sum
at displacements zero, two and four. -/

namespace Walk026084

def tri : ℕ → ℤ → ℤ
  | 0, z => if z = 0 then 1 else 0
  | t+1, z => tri t (z-1) + tri t z + tri t (z+1)

theorem mirror (t : ℕ) (z : ℤ) : tri t (-z) = tri t z := by
  induction t generalizing z with
  | zero => simp [tri]
  | succ t ih =>
    rw [tri,tri,show -z-1 = -(z+1) by ring, show -z+1 = -(z-1) by ring,
      ih (z+1),ih z,ih (z-1)]
    ring

theorem moment (t : ℕ) (z : ℤ) :
    z * tri (t+1) z = ((t : ℤ)+1) * (tri t (z-1) - tri t (z+1)) := by
  induction t generalizing z with
  | zero =>
    simp only [tri, Nat.cast_zero, zero_add, one_mul]
    split_ifs <;> simp_all <;> omega
  | succ t ih =>
    have h1 := ih (z-1)
    have h2 := ih z
    have h3 := ih (z+1)
    simp only [tri, Nat.cast_succ, sub_add_cancel, add_sub_cancel_right] at *
    linear_combination h1 + h2 + h3

def weighted (t : ℕ) : ℤ := 3 * tri t 0 + 4 * tri t 2 + tri t 4

set_option maxHeartbeats 1200000 in
theorem weighted_recurrence (k : ℕ) :
    ((k : ℤ)+8)*weighted (k+4) + 3*(-(k:ℤ)-6)*weighted (k+3) +
    (-(k:ℤ)-16)*weighted (k+2) + 3*((k:ℤ)+2)*weighted (k+1) = 0 := by
  have h1 := moment k 1
  have h2 := moment k 2
  have h3 := moment k 3
  have h4 := moment k 4
  have h5 := moment k 5
  have h6 := moment k 6
  have h7 := moment k 7
  norm_num [weighted,tri] at h1 h2 h3 h4 h5 h6 h7 ⊢
  rw [mirror k 1,mirror k 2,mirror k 3,mirror k 4]
  linear_combination 5*h1 + 5*h2 + 9*h3 + 4*h4 + 5*h5 + h6 + h7

end Walk026084

/-! A last-step bijection for integer paths with the first three steps nonzero. -/

namespace Walk026084

def choices (t : ℕ) : Finset ℤ :=
  if t ≤ 3 then {-1,1} else {-1,0,1}

structure Path (n : ℕ) (y : ℤ) where
  pos : Fin (n+1) → ℤ
  start : pos 0 = 0
  finish : pos (Fin.last n) = y
  valid : ∀ i : Fin n, pos i.succ - pos i.castSucc ∈ choices (i.val+1)

theorem eq_of_pos {n : ℕ} {z : ℤ} {a b : Path n z} (h : a.pos=b.pos) : a=b := by
  cases a; cases b; cases h; rfl

theorem heq_of_pos {n : ℕ} {x y : ℤ} {a : Path n x} {b : Path n y}
    (h : a.pos=b.pos) : HEq a b := by
  have hxy := a.finish.symm.trans ((congrFun h (Fin.last n)).trans b.finish)
  subst y
  exact heq_of_eq (eq_of_pos h)

def lastStep {n : ℕ} {y : ℤ} (p : Path (n+1) y) : ↥(choices (n+1)) :=
  ⟨y - p.pos (Fin.last n).castSucc, by
    have h := p.valid (Fin.last n)
    simpa only [Fin.succ_last, Fin.val_last, p.finish] using h⟩

def dropStep {n : ℕ} {y : ℤ} (p : Path (n+1) y) : Path n (y-(lastStep p).val) where
  pos i := p.pos i.castSucc
  start := p.start
  finish := by simp [lastStep]
  valid i := p.valid i.castSucc

def addStep {n : ℕ} {y : ℤ} (d : ↥(choices (n+1))) (p : Path n (y-d.val)) :
    Path (n+1) y where
  pos := Fin.snoc (α := fun _ => ℤ) p.pos y
  start := by
    change Fin.snoc (α := fun _ => ℤ) p.pos y (0 : Fin (n+1)).castSucc = 0
    rw [Fin.snoc_castSucc,p.start]
  finish := Fin.snoc_last _ _
  valid := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change Fin.snoc (α := fun _ => ℤ) p.pos y (Fin.last (n+1)) -
          Fin.snoc (α := fun _ => ℤ) p.pos y (Fin.last n).castSucc ∈ choices (n+1)
      simpa [p.finish] using d.property
    · change Fin.snoc (α := fun _ => ℤ) p.pos y j.succ.castSucc -
          Fin.snoc (α := fun _ => ℤ) p.pos y j.castSucc.castSucc ∈ choices (j.val+1)
      simpa only [Fin.snoc_castSucc] using p.valid j

def splitEquiv (n : ℕ) (y : ℤ) :
    Path (n+1) y ≃ (Σ d : ↥(choices (n+1)), Path n (y-d.val)) where
  toFun p := ⟨lastStep p,dropStep p⟩
  invFun a := addStep a.1 a.2
  left_inv p := by
    apply eq_of_pos
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [addStep] using p.finish.symm
    · simp [addStep,dropStep]
  right_inv := by
    rintro ⟨d,p⟩
    apply Sigma.ext
    · apply Subtype.ext
      simp [lastStep,addStep,p.finish]
    · apply heq_of_pos
      funext i
      simp [dropStep,addStep]

private theorem path_zero_eq {y : ℤ} (a b : Path 0 y) : a = b := by
  apply eq_of_pos
  funext i
  obtain rfl : i = 0 := by apply Fin.ext; omega
  exact a.start.trans b.start.symm

instance finitePath (n : ℕ) (z : ℤ) : Finite (Path n z) := by
  induction n generalizing z with
  | zero =>
    exact Finite.of_injective (fun _ : Path 0 z => ()) (fun a b _ => path_zero_eq a b)
  | succ n ih =>
    haveI (d : ↥(choices (n+1))) : Finite (Path n (z-d.val)) := ih _
    exact Finite.of_equiv _ (splitEquiv n z).symm

noncomputable def countPaths (n : ℕ) (y : ℤ) : ℤ := Nat.card (Path n y)

theorem countZero (y : ℤ) : countPaths 0 y = if y=0 then 1 else 0 := by
  by_cases h : y=0
  · subst y
    let p : Path 0 0 := ⟨fun _ => 0, rfl, rfl, fun i => Fin.elim0 i⟩
    letI : Unique (Path 0 0) := ⟨⟨p⟩,fun a => path_zero_eq a p⟩
    simp [countPaths]
  · letI : IsEmpty (Path 0 y) := ⟨fun p => h (p.finish.symm.trans p.start)⟩
    simp [countPaths,h]

theorem countStep (n : ℕ) (y : ℤ) : countPaths (n+1) y =
    if n+1 ≤ 3 then countPaths n (y-1) + countPaths n (y+1)
    else countPaths n (y-1) + countPaths n y + countPaths n (y+1) := by
  unfold countPaths
  rw [Nat.card_congr (splitEquiv n y), Nat.card_sigma, Finset.sum_coe_sort (choices (n+1)) (fun d : ℤ => Nat.card (Path n (y-d)))]
  by_cases h : n+1 ≤ 3 <;> simp [choices,h] <;> ring

end Walk026084

/-! First three nonzero steps precede the unrestricted three-choice random walk.
The sequence is due to Clark Kimberling and the recurrence to R. J. Mathar. -/

namespace Walk026084
open OMA.S_oeis_a026084

private theorem mem_choices (t : ℕ) (z : ℤ) : z ∈ choices t ↔
    (t ≤ 3 → |z|=1) ∧ (3<t → |z|≤1) := by
  rcases le_or_gt t 3 with h|h
  · simp [choices,h,not_lt_of_ge h,abs_eq (by decide : (0:ℤ)≤1),or_comm]
  · simp [choices,h.not_ge,h,abs_le]
    omega

private theorem pair_step {n : ℕ} {y : ℤ} (p : Path n y) (i j : Fin (n+1))
    (hj : j.val=i.val+1) : p.pos j-p.pos i ∈ choices j.val := by
  let k : Fin n := ⟨i.val,by omega⟩
  rw [show j=k.succ from Fin.ext hj,show i=k.castSucc from Fin.ext rfl]
  exact p.valid k

def originalEquiv (n : ℕ) : ↥(walks n) ≃ Path n 1 where
  toFun v := {
    pos := v.val
    start := v.property.1 0 rfl
    finish := v.property.2.1 _ rfl
    valid := fun i => (mem_choices _ _).mpr
      ⟨v.property.2.2.1 i.castSucc i.succ rfl,v.property.2.2.2 i.castSucc i.succ rfl⟩ }
  invFun p := ⟨p.pos, by
    refine ⟨?_,?_,fun i j h => ((mem_choices _ _).mp (pair_step p i j h)).1,
      fun i j h => ((mem_choices _ _).mp (pair_step p i j h)).2⟩
    · intro i hi
      simpa [show i=0 from Fin.ext hi] using p.start
    · intro i hi
      simpa [show i=Fin.last n from Fin.ext hi] using p.finish⟩
  left_inv p := rfl
  right_inv p := eq_of_pos rfl

theorem a_as_count (n : ℕ) : a n = countPaths n 1 :=
  congrArg Int.ofNat (Nat.card_congr (originalEquiv n))

theorem count_after_three (k : ℕ) (y : ℤ) :
    countPaths (k+3) y = tri k (y-3) + 3*tri k (y-1) +
      3*tri k (y+1) + tri k (y+3) := by
  induction k generalizing y with
  | zero =>
    norm_num [countStep,countZero,tri]
    split_ifs <;> omega
  | succ k ih =>
    rw [countStep]
    simp only [show ¬ k+3+1≤3 by omega, if_false,ih,tri]
    ring_nf

theorem a_weighted (k : ℕ) : a (k+3) = weighted k := by
  rw [a_as_count,count_after_three]
  norm_num [weighted]
  rw [mirror k 2]
  ring

theorem solution (n : ℕ) (hn : 7 ≤ n) :
    ((n : ℤ) + 1) * a n + 3 * (-(n : ℤ) + 1) * a (n - 1) + (-(n : ℤ) - 9) * a (n - 2) +
      3 * ((n : ℤ) - 5) * a (n - 3) = 0 := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
  subst n
  rw [show 7+k=k+4+3 by omega, a_weighted,
      show k+4+3-1=k+3+3 by omega, a_weighted,
      show k+4+3-2=k+2+3 by omega, a_weighted,
      show k+4+3-3=k+1+3 by omega, a_weighted]
  push_cast
  linear_combination weighted_recurrence k

end Walk026084

theorem OMA.solution : type_of% @OMA.S_oeis_a026084.main := Walk026084.solution
