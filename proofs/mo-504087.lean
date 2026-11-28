import OMAStatements.S_mo_504087

/-!
# The first missing Motzkin weight is the Conway–Guy difference

Popov's question asks whether his positive-mex rule recovers the first differences
of the Conway–Guy sequence. Capped Motzkin profiles cover a closed interval at
each height. At height zero its upper endpoint is the next difference minus one.

For exclusion, we specialize Bohman's backward elimination of signed smooth
vectors to nonnegative profiles followed by the terminal coefficient minus one.
At a first failed elimination, the remaining demand begins at zero and
increases faster than a feasible profile over the active interval. The
nonnegative heights before that interval make the two weights unequal.

Source: https://mathoverflow.net/questions/504087 . Popov announced a possible
proof on 21 November 2025. Bohman's distinct-subset-sums theorem for these sets
and his elimination method appear in Proc. Amer. Math. Soc. 124 (1996),
3627–3636, DOI 10.1090/S0002-9939-96-03653-2.
-/

namespace OMA.S_mo_504087
open Finset

theorem radius_pos {i : ℕ} (hi : 0 < i) : 0 < radius i := by
  have h : 1 ≤ Nat.sqrt (8 * i) := Nat.le_sqrt.mpr (by omega)
  unfold radius
  omega

theorem radius_block {i k : ℕ} (hk : 0 < k)
    (hl : (k - 1) * k < 2 * i) (hu : 2 * i ≤ k * (k + 1)) : radius i = k := by
  have hlow : 2 * k - 1 ≤ Nat.sqrt (8 * i) := by
    apply Nat.le_sqrt.mpr
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Nat.succ_sub_one] at hl
    have he : 2 * (t + 1) - 1 = 2*t+1 := by omega
    rw [he]
    nlinarith
  have hupp : Nat.sqrt (8 * i) < 2 * k + 1 := by
    apply Nat.sqrt_lt.mpr
    nlinarith
  unfold radius
  omega

theorem conwayGuy_strictMono : StrictMono conwayGuy := by
  intro a b hab
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    match b with
    | 0 => omega
    | 1 =>
      have : a = 0 := by omega
      subst a
      simp [conwayGuy.eq_1, conwayGuy.eq_2]
    | n + 2 =>
      have hr : 0 < radius (n + 1) := radius_pos (by omega)
      have hprev : conwayGuy (n + 1 - radius (n + 1)) < conwayGuy (n + 1) :=
        ih (n + 1) (by omega) (by omega)
      have hnext : conwayGuy (n + 1) < conwayGuy (n + 2) := by
        rw [conwayGuy.eq_3]
        omega
      by_cases he : a = n + 1
      · simpa [he] using hnext
      · exact lt_trans (ih (n+1) (by omega) (by omega)) hnext

theorem first_differences : diff 1 = 1 ∧ diff 2 = 1 := by
  have hr : radius 1 = 1 := radius_block (by decide) (by decide) (by decide)
  norm_num [diff, conwayGuy.eq_1, conwayGuy.eq_2, conwayGuy.eq_3, hr]

theorem diff_pos {i : ℕ} (hi : 0 < i) : 0 < diff i :=
  Nat.sub_pos_of_lt (conwayGuy_strictMono (by omega))

theorem sum_diff_range (i : ℕ) :
    ∑ j ∈ Finset.range i, diff (j + 1) = conwayGuy i := by
  induction i with
  | zero => simp [conwayGuy.eq_1]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [diff, Nat.add_sub_cancel]
    exact Nat.add_sub_of_le (conwayGuy_strictMono.monotone (Nat.le_succ i))

theorem diff_recurrence {i : ℕ} (hi : 0 < i) :
    diff (i + 1) = ∑ j ∈ Finset.Ico (i - radius i) i, diff (j + 1) := by
  have h := Finset.sum_range_add_sum_Ico (fun j => diff (j+1)) (Nat.sub_le i (radius i))
  rw [sum_diff_range, sum_diff_range] at h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hprev := conwayGuy_strictMono.monotone (Nat.sub_le (n+1) (radius (n+1)))
  change (conwayGuy (n+2) - conwayGuy (n+1)) = _
  rw [conwayGuy.eq_3]
  change conwayGuy (n+1-radius (n+1)) + _ = conwayGuy (n+1) at h
  omega

theorem radius_le_iff (i k : ℕ) : radius i ≤ k ↔ 2*i ≤ k*(k+1) := by
  unfold radius
  rw [show (Nat.sqrt (8*i)+1)/2 ≤ k ↔ Nat.sqrt (8*i)<2*k+1 by omega, Nat.sqrt_lt]
  constructor <;> intro h <;> nlinarith

theorem radius_monotone : Monotone radius := by
  intro i j hij
  apply (radius_le_iff ..).mpr
  have h := (radius_le_iff j (radius j)).mp le_rfl
  omega

theorem radius_le_self (i : ℕ) : radius i ≤ i := by
  apply (radius_le_iff ..).mpr
  nlinarith [Nat.le_mul_self i]

theorem radius_succ_le (i : ℕ) : radius (i+1) ≤ radius i + 1 := by
  have h := (radius_le_iff i (radius i)).mp le_rfl
  apply (radius_le_iff ..).mpr
  nlinarith

theorem radius_cutoff {i j : ℕ} (hj : j < i) :
    i ≤ j + radius j ↔ i - radius i < j := by
  have hr := radius_le_self i
  have t : ∃ d, i = j + (d+1) := by exact ⟨i-j-1, by omega⟩
  obtain ⟨d,rfl⟩ := t
  have h1 := radius_le_iff j d
  have h2 := radius_le_iff (j+(d+1)) (d+1)
  have eq : 2*j ≤ d*(d+1) ↔ 2*(j+(d+1)) ≤ (d+1)*(d+1+1) := by
    constructor <;> intro h <;> nlinarith
  omega

def lower (i h : ℕ) : ℕ := ∑ j ∈ range i, (h+(j+1)-i)*diff (j+1)
def upper (i h : ℕ) : ℕ := ∑ j ∈ range i, min (radius (j+1)) (h+i-(j+1))*diff (j+1)

theorem upper_zero_add (i : ℕ) : upper (i+1) 0 = upper i 0 +
    ∑ j ∈ range i, if i+1-radius (i+1) ≤ j then diff (j+1) else 0 := by
  unfold upper
  rw [sum_range_succ, ← sum_add_distrib]
  simp only [zero_add, Nat.sub_self, Nat.min_zero, zero_mul, add_zero]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  have hc := radius_cutoff (i := i+1) (j := j+1) (by omega)
  by_cases h : i+1-radius (i+1) ≤ j
  · rw [if_pos h]
    have hc' : i+1 ≤ j+1+radius (j+1) := hc.mpr (by omega)
    rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega),
      show i+1-(j+1) = (i-(j+1))+1 by omega, Nat.add_mul, one_mul]
  · rw [if_neg h, add_zero]
    have hc' : ¬ i+1 ≤ j+1+radius (j+1) := fun hc' => h (by have := hc.mp hc'; omega)
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]

theorem upper_zero_eq (i : ℕ) : upper i 0 + 1 = diff (i+1) := by
  induction i with
  | zero => simpa [upper] using first_differences.1.symm
  | succ i ih =>
    rw [upper_zero_add, show upper i 0 + _ + 1 = (upper i 0+1) +
      ∑ j ∈ range i, if i+1-radius (i+1) ≤ j then diff (j+1) else 0 by omega, ih,
      diff_recurrence (i := i+1) (by omega)]
    have hc : i+1-radius (i+1) ≤ i := by have := radius_pos (i := i+1) (by omega); omega
    rw [sum_Ico_succ_top hc, add_comm]
    congr 1
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega

theorem lower_next (i h : ℕ) : lower (i+1) h = lower i (h-1) + h*diff (i+1) := by
  unfold lower
  rw [sum_range_succ, show h+(i+1)-(i+1)=h by omega]
  congr 1
  apply sum_congr rfl
  intro j hj
  have := mem_range.mp hj
  rw [show h+(j+1)-(i+1) = h-1+(j+1)-i by omega]

theorem upper_next {i h : ℕ} (hh : h ≤ radius (i+1)) :
    upper (i+1) h = upper i (min (radius i) (h+1)) + h*diff (i+1) := by
  unfold upper
  rw [sum_range_succ, show h+(i+1)-(i+1)=h by omega, Nat.min_eq_right hh]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  have hr := radius_monotone (show j+1 ≤ i by omega)
  congr 1
  omega

theorem lower_top_increment {i : ℕ} (hi : 0 < i) :
    lower i (radius i) = lower i (radius i-1) + diff (i+1) := by
  rw [diff_recurrence hi]
  have hfilter : Ico (i-radius i) i = (range i).filter (fun j => i-radius i ≤ j) := by
    ext j
    simp [and_comm]
  rw [hfilter, sum_filter]
  unfold lower
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  have := mem_range.mp hj
  have := radius_pos hi
  split_ifs with h
  · rw [show radius i+(j+1)-i = (radius i-1+(j+1)-i)+1 by omega, Nat.add_mul, one_mul]
  · rw [show radius i+(j+1)-i = 0 by omega, show radius i-1+(j+1)-i=0 by omega]
    simp

def capTotal (i : ℕ) : ℕ := ∑ j ∈ range i, radius (j+1)*diff (j+1)
def blockStart (k : ℕ) : ℕ := (k-1)*k/2+1

theorem blockStart_le {i : ℕ} (hi : 0 < i) : blockStart (radius i) ≤ i := by
  have hp := radius_pos hi
  have h := radius_le_iff i (radius i-1)
  unfold blockStart
  have he : radius i-1+1=radius i := by omega
  rw [he] at h
  omega

theorem blockStart_rise {i : ℕ} (hi : 0 < i) (hr : radius i < radius (i+1)) :
    blockStart (radius i + 1) = i+1 ∧ blockStart (radius i) = i+1-radius i := by
  let k := radius i
  have hp : 0 < k := radius_pos hi
  have hs := (radius_le_iff i k).mp le_rfl
  have ht := radius_le_iff (i+1) k
  have hsmall := radius_le_self i
  change k < radius (i+1) at hr
  change k ≤ i at hsmall
  have h_up : k*(k+1) < 2*(i+1) := by omega
  change blockStart (k+1) = i+1 ∧ blockStart k = i+1-k
  unfold blockStart
  rw [Nat.add_sub_cancel]
  have he : (k-1)*k + 2*k = k*(k+1) := by
    obtain ⟨t,h⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [h, Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  omega

theorem capTop_formula {i : ℕ} (hi : 0 < i) :
    capTotal i + 1 = lower i (radius i) + diff i +
      ∑ j ∈ Ico (blockStart (radius i)) i, diff j := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with hz | hi'
    · subst i
      have r : radius 1 = 1 := radius_block (by decide) (by decide) (by decide)
      simp [capTotal, lower, blockStart, r, first_differences.1]
    · have hprev := ih hi'
      have hv : capTotal (i+1) = capTotal i + radius (i+1)*diff (i+1) :=
        sum_range_succ ..
      rw [hv, lower_next]
      have hm : radius i ≤ radius (i+1) := radius_monotone (Nat.le_succ i)
      have hstep := radius_succ_le i
      by_cases hr : radius (i+1) = radius i
      · rw [hr, sum_Ico_succ_top (blockStart_le hi')]
        have hinc := lower_top_increment hi'
        omega
      · have hu : radius (i+1) = radius i + 1 := by omega
        obtain ⟨ha,hb⟩ := blockStart_rise hi' (by omega)
        rw [hu, Nat.add_sub_cancel, ha, Ico_eq_empty_of_le le_rfl, sum_empty, add_zero]
        have hd := diff_recurrence hi'
        have hk := radius_le_self i
        have hp := radius_pos hi'
        have ha' : i+1-radius i = (i-radius i)+1 := by omega
        rw [hb,ha'] at hprev
        have hs : (∑ j ∈ Ico (i-radius i) i, diff (j+1)) =
            ∑ j ∈ Ico (i-radius i + 1) (i+1), diff j := by
          rw [sum_Ico_add']
        rw [hs, sum_Ico_succ_top (by omega)] at hd
        omega

theorem upper_top {i : ℕ} (hi : 0 < i) :
    upper i (radius i-1) + diff i = capTotal i := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  have hp : 1 ≤ radius (t+1) := radius_pos hi
  unfold upper capTotal
  rw [sum_range_succ, sum_range_succ]
  have he : ∀ j ∈ range t, min (radius (j+1)) (radius (t+1)-1+(t+1)-(j+1)) = radius (j+1) := by
    intro j hj
    have := mem_range.mp hj
    have := radius_monotone (show j+1 ≤ t+1 by omega)
    omega
  simp_rw [show radius (t+1)-1+(t+1)-(t+1) = radius (t+1)-1 by omega,
    Nat.min_eq_right (Nat.sub_le ..)]
  rw [sum_congr rfl (fun j hj => by rw [he j hj] )]
  have e : (radius (t+1)-1)*diff (t+1) + diff (t+1) = radius (t+1)*diff (t+1) := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
  simp only [Nat.succ_eq_add_one, Nat.add_assoc, e]

theorem lower_convex (i h : ℕ) : 2*lower i (h+1) ≤ lower i h + lower i (h+2) := by
  unfold lower
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro j hj
  rw [← Nat.mul_assoc, ← Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

theorem upper_concave (i h : ℕ) : upper i h + upper i (h+2) ≤ 2*upper i (h+1) := by
  unfold upper
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro j hj
  have := mem_range.mp hj
  rw [← Nat.mul_assoc, ← Nat.add_mul]
  exact Nat.mul_le_mul_right _ (by omega)

private theorem concave_nonneg {f : ℕ → ℤ} (hc : ∀ h, f h + f (h+2) ≤ 2*f (h+1))
    (h0 : 0 ≤ f 0) {b : ℕ} (hb : 0 ≤ f b) : ∀ t ≤ b, 0 ≤ f t := by
  have back : ∀ j, f j < 0 → f j ≤ f (j+1) → False := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj hj'
      have h := hc j
      change f (j+1) ≤ f (j+2) at hj'
      exact ih (by omega) (by omega)
  induction b with
  | zero => intro t ht; simpa [show t = 0 by omega] using h0
  | succ b ih =>
    have hb' : 0 ≤ f b := by
      by_contra! h
      exact back b h (by omega)
    intro t ht
    rcases Nat.eq_or_lt_of_le ht with h | h
    · simpa [h] using hb
    · exact ih hb' t (by omega)

theorem lower_zero (i : ℕ) : lower i 0 = 0 := by
  unfold lower
  apply sum_eq_zero
  intro j hj
  have := mem_range.mp hj
  simp [show j+1-i=0 by omega]

theorem diff_le_next {i : ℕ} (hi : 0 < i) : diff i ≤ diff (i+1) := by
  rw [diff_recurrence hi]
  have h := radius_pos hi
  have hmem : i-1 ∈ Ico (i-radius i) i := mem_Ico.mpr ⟨by omega,by omega⟩
  simpa [Nat.sub_add_cancel (show 1 ≤ i by omega)] using
    (single_le_sum (f := fun j => diff (j+1)) (fun _ _ => Nat.zero_le _) hmem)

theorem no_gap {i h : ℕ} (hh : h < radius i) : lower i (h+1) ≤ upper i h + 1 := by
  have hi : 0 < i := by have := radius_le_self i; omega
  let f (j : ℕ) : ℤ := (upper i j : ℤ) + 1 - (lower i (j+1) : ℤ)
  have hc : ∀ j, f j + f (j+2) ≤ 2*f (j+1) := by
    intro j
    have hl := lower_convex i (j+1)
    have hu := upper_concave i j
    change 2 * lower i (j+2) ≤ lower i (j+1) + lower i (j+3) at hl
    dsimp [f]
    change (upper i j : ℤ)+1-lower i (j+1)+((upper i (j+2):ℤ)+1-lower i (j+3)) ≤ 2*((upper i (j+1):ℤ)+1-lower i (j+2))
    omega
  have hzero : 0 ≤ f 0 := by
    have he : lower i 1 = diff i := by
      obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
      simp [lower_next, lower_zero]
    dsimp [f]
    have h := upper_zero_eq i
    have d := diff_le_next hi
    omega
  have htop : 0 ≤ f (radius i-1) := by
    have h := capTop_formula hi
    have hu := upper_top hi
    have hp := radius_pos hi
    dsimp [f]
    rw [Nat.sub_add_cancel (by omega)]
    omega
  have hres := concave_nonneg hc hzero htop h (by omega)
  dsimp [f] at hres
  omega

def realizes (i h x : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, f 0 = 0 ∧ f i = h ∧ (∀ j < i, Nat.dist (f j) (f (j+1)) ≤ 1) ∧
    x = ∑ j ∈ range i, f (j+1)*diff (j+1)

theorem realizes_zero : realizes 0 0 0 := by
  exact ⟨fun _ => 0,rfl,rfl,by simp,by simp⟩

theorem realizes_append {i t h x : ℕ} (hr : realizes i t x) (hs : Nat.dist t h ≤ 1) :
    realizes (i+1) h (x+h*diff (i+1)) := by
  obtain ⟨f,hzero,hend,hstep,hx⟩ := hr
  let g (j : ℕ) := if j=i+1 then h else f j
  refine ⟨g,by simpa [g] using hzero,by simp [g],?_,?_⟩
  · intro j hj
    by_cases he : j=i
    · subst j
      simpa [g,hend] using hs
    · simpa [g,show j ≠ i+1 by omega,he] using hstep j (by omega)
  · rw [sum_range_succ,hx]
    have he : ∀ j ∈ range i, g (j+1) = f (j+1) := by
      intro j hj
      have := mem_range.mp hj
      simp [g,show j ≠ i by omega]
    have E : (∑ j ∈ range i, g (j+1)*diff (j+1)) = ∑ j ∈ range i, f (j+1)*diff (j+1) := sum_congr rfl fun j hj => by rw [he j hj]
    rw [E]
    simp [g]

private theorem interval_union {l u : ℕ → ℕ} {a b y : ℕ} (hab : a ≤ b)
    (hgap : ∀ t, a ≤ t → t < b → l (t+1) ≤ u t + 1)
    (hal : l a ≤ y) (hbu : y ≤ u b) : ∃ t, a ≤ t ∧ t ≤ b ∧ l t ≤ y ∧ y ≤ u t := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a,le_rfl,le_rfl,hal,hbu⟩
  | succ b hab ih =>
    by_cases hy : y ≤ u b
    · obtain ⟨t,h1,h2,h3,h4⟩ := ih (fun t ht ht' => hgap t ht (by omega)) hy
      exact ⟨t,h1,by omega,h3,h4⟩
    · have h := hgap b hab (by omega)
      exact ⟨b+1,by omega,le_rfl,by omega,hbu⟩

theorem interval_realizes {i h x : ℕ} (hh : h ≤ radius i)
    (hlo : lower i h ≤ x) (hhi : x ≤ upper i h) : realizes i h x := by
  induction i generalizing h x with
  | zero =>
    have hr := radius_le_self 0
    have h0 : h=0 := by omega
    have hx : x=0 := by simpa [upper] using hhi
    simpa [h0,hx] using realizes_zero
  | succ i ih =>
    let a := h-1
    let b := min (radius i) (h+1)
    have hab : a ≤ b := by have := radius_succ_le i; dsimp [a,b]; omega
    rw [lower_next] at hlo
    rw [upper_next hh] at hhi
    let y := x-h*diff (i+1)
    have hl : lower i a ≤ y := by dsimp [a,y]; omega
    have hu : y ≤ upper i b := by dsimp [b,y]; omega
    obtain ⟨t,ht1,ht2,ht3,ht4⟩ := interval_union hab
      (l := lower i) (u := upper i) (fun t _ ht => no_gap (by dsimp [b] at ht; omega)) hl hu
    have ht : t ≤ radius i := by dsimp [b] at ht2; omega
    have hd : Nat.dist t h ≤ 1 := by dsimp [a] at ht1; dsimp [b] at ht2; unfold Nat.dist; omega
    have he : y+h*diff (i+1)=x := by dsimp [y]; omega
    exact he ▸ realizes_append (ih ht ht3 ht4) hd

theorem all_below_forbidden {n x : ℕ} (hn : 3 ≤ n) (hx : 0 < x) (hlt : x < diff n) :
    forbidden n x := by
  let i := n-1
  have hi : 0 < i := by dsimp [i]; omega
  have he : i+1=n := by dsimp [i]; omega
  have hu := upper_zero_eq i
  rw [he] at hu
  obtain ⟨f,h0,hend,hstep,hx'⟩ := interval_realizes (i:=i) (h:=0) (x:=x)
    (Nat.zero_le _) (by simp [lower_zero]) (by omega)
  have hsum : x = ∑ j ∈ Ico 1 i, f j * diff j := by
    have shift : (∑ j ∈ range i, f (j+1)*diff (j+1)) = ∑ j ∈ Ico 1 (i+1), f j*diff j := by
      rw [← Nat.Ico_zero_eq_range]
      exact sum_Ico_add' (fun j => f j*diff j) 0 i 1
    rw [shift, sum_Ico_succ_top hi, hend, zero_mul, add_zero] at hx'
    exact hx'
  refine ⟨f,h0,hend,fun j hj => hstep j (by dsimp [i]; omega),?_,hsum⟩
  by_contra! h
  have hz : (∑ j ∈ Ico 1 i, f j * diff j)=0 := by
    apply sum_eq_zero
    intro j hj
    have he := h j hj
    have : f j=0 := by omega
    simp [this]
  omega

def reach (i : ℕ) := i + radius i + 1
def energy (q : ℕ) (f : ℕ → ℕ) := ∑ j ∈ range q, f (j+1)*diff (j+1)
def demand (q n : ℕ) (r : ℕ → ℕ) (i : ℕ) :=
  ∑ j ∈ range (min n (reach i) - q), r j

theorem reach_monotone : Monotone reach := by
  intro i j hij
  have h := radius_monotone hij
  unfold reach
  omega

theorem reach_hit {i q : ℕ} (hi : i ≤ q) (hq : 0 < q) :
    q+1 ≤ reach i ↔ q-radius q < i := by
  unfold reach
  by_cases h : i=q
  · subst i
    have := radius_pos hq
    omega
  · have hcut := radius_cutoff (i:=q) (j:=i) (by omega)
    omega

theorem energy_hit (q : ℕ) (hq : 0 < q) :
    energy q (fun i => if q+1 ≤ reach i then 1 else 0) = diff (q+1) := by
  rw [diff_recurrence hq]
  have hfilter : Ico (q-radius q) q = (range q).filter (fun j => q-radius q ≤ j) := by
    ext j
    simp [and_comm]
  rw [hfilter,sum_filter]
  unfold energy
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  have hcut := reach_hit (i:=j+1) (q:=q) (by omega) hq
  by_cases h : q-radius q ≤ j
  · simp [h,hcut.mpr (by omega)]
  · simp [h,show ¬q+1 ≤ reach (j+1) from fun H => h (by have := hcut.mp H; omega)]

theorem demand_initial (q : ℕ) (i : ℕ) :
    demand q (q+1) (fun _ => 1) i = if q+1 ≤ reach i then 1 else 0 := by
  simp only [demand,sum_const,card_range,smul_eq_mul,mul_one]
  split_ifs <;> omega

def prepend (e : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => e
  | j+1 => r j

theorem demand_prepend {q n : ℕ} (hqn : q+1 ≤ n) (e : ℕ) (r : ℕ → ℕ) (i : ℕ) :
    demand q n (prepend e r) i =
      demand (q+1) n r i + (if q+1 ≤ reach i then e else 0) := by
  unfold demand
  split_ifs with h
  · have he : min n (reach i)-q = (min n (reach i)-(q+1))+1 := by omega
    rw [he,sum_range_succ']
    rfl
  · simp [show min n (reach i)-q = 0 by omega,show min n (reach i)-(q+1)=0 by omega]

theorem energy_prepend {q n : ℕ} (hqn : q+1 ≤ n) (hq : 0 < q) (e : ℕ) (r : ℕ → ℕ) :
    energy q (demand q n (prepend e r)) = energy q (demand (q+1) n r) + e*diff (q+1) := by
  rw [← energy_hit q hq]
  unfold energy
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [demand_prepend hqn]
  split_ifs <;> simp [Nat.add_mul] <;> omega

theorem energy_succ (q : ℕ) (f : ℕ → ℕ) : energy (q+1) f = energy q f + f (q+1)*diff (q+1) :=
  sum_range_succ ..

theorem path_lipschitz {f : ℕ → ℕ} {n : ℕ}
    (hs : ∀ j < n, Nat.dist (f j) (f (j+1)) ≤ 1) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    f j ≤ f i + (j-i) ∧ f i ≤ f j + (j-i) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    obtain ⟨h₁,h₂⟩ := ih (by omega)
    have h := hs j (by omega)
    unfold Nat.dist at h
    omega

theorem positive_sum_gap {a b : ℕ} (hab : a ≤ b) (r : ℕ → ℕ) (hr : ∀ j, 0 < r j) :
    (∑ j ∈ range a, r j) + (b-a) ≤ ∑ j ∈ range b, r j := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_range_succ]
    have := hr b
    omega

theorem demand_count {q n : ℕ} {r : ℕ → ℕ} (hr : ∀ j, 0 < r j) (i : ℕ) :
    min n (reach i)-q ≤ demand q n r i := by
  simpa [demand] using (positive_sum_gap (a:=0) (b:=min n (reach i)-q) (Nat.zero_le _) r hr)

theorem stop_impossible {n q : ℕ} {f r : ℕ → ℕ} (hq : 0 < q) (hqn : q ≤ n-1) (hn : 0 < n)
    (h0 : f 0=0) (hend : f (n-1)=0) (hs : ∀ j < n-1, Nat.dist (f j) (f (j+1)) ≤ 1)
    (hr : ∀ j, 0 < r j) (hE : energy q f = energy q (demand q n r))
    (hstop : demand q n r q ≤ f q) : False := by
  have bound := (path_lipschitz hs hqn le_rfl).2
  rw [hend,zero_add] at bound
  have hc := demand_count (q:=q) (n:=n) hr q
  have hnr : reach q ≤ n := by omega
  rw [Nat.min_eq_right hnr] at hc
  let z := q-radius q
  have hzq : z ≤ q := Nat.sub_le ..
  have hzreach : reach z ≤ q := by
    have hh := reach_hit hzq hq
    dsimp [z] at hh ⊢
    omega
  have hdz : demand q n r z=0 := by simp [demand,show min n (reach z)-q=0 by omega]
  have hzbound := (path_lipschitz hs hzq hqn).1
  have hp := radius_le_self q
  have hpos : 0 < f z := by unfold reach at hc; dsimp [z] at hzbound ⊢; omega
  have hzpos : 0 < z := Nat.pos_of_ne_zero fun he => by rw [he,h0] at hpos; exact Nat.lt_irrefl 0 hpos
  have le_all : ∀ i ≤ q, demand q n r i ≤ f i := by
    intro i hi
    by_cases h : i ≤ z
    · have ha := reach_monotone h
      simp [demand,show min n (reach i)-q=0 by omega]
    · have hlow : q+1 ≤ reach i := (reach_hit hi hq).mpr (by dsimp [z] at h; omega)
      have hreach := reach_monotone hi
      have hlip := (path_lipschitz hs hi hqn).1
      have hpre := positive_sum_gap (a:=reach i-q) (b:=reach q-q) (by omega) r hr
      unfold demand at hstop ⊢
      rw [Nat.min_eq_right hnr] at hstop
      rw [Nat.min_eq_right (hreach.trans hnr)]
      have hrad := radius_monotone hi
      unfold reach at hpre hlow hstop ⊢
      omega
  have hlt : energy q (demand q n r) < energy q f := by
    unfold energy
    apply sum_lt_sum
    · intro j hj
      have := mem_range.mp hj
      exact Nat.mul_le_mul_right _ (le_all (j+1) (by omega))
    · refine ⟨z-1,mem_range.mpr (by omega),?_⟩
      rw [Nat.sub_add_cancel hzpos,hdz,zero_mul]
      exact Nat.mul_pos hpos (diff_pos hzpos)
  omega

private theorem no_balanced_profile {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ)
    (h0 : f 0=0) (hend : f (n-1)=0) (hs : ∀ j < n-1, Nat.dist (f j) (f (j+1)) ≤ 1)
    {q : ℕ} (hq : 0 < q) (hqn : q ≤ n-1) (r : ℕ → ℕ) (hr : ∀ j, 0 < r j)
    (hE : energy q f = energy q (demand q n r)) : False := by
  induction q generalizing r with
  | zero => omega
  | succ q ih =>
    by_cases h : demand (q+1) n r (q+1) ≤ f (q+1)
    · exact stop_impossible hq hqn hn h0 hend hs hr hE h
    · let e := demand (q+1) n r (q+1) - f (q+1)
      have he : 0 < e := by dsimp [e]; omega
      rw [energy_succ,energy_succ] at hE
      rcases Nat.eq_zero_or_pos q with hq0 | hq'
      · subst q
        simp [energy,first_differences.1] at hE
        exact h hE.ge
      · have hr' : ∀ j, 0 < prepend e r j := by
          intro j
          cases j with
          | zero => exact he
          | succ j => exact hr j
        apply ih hq' (by omega) (prepend e r) hr'
        rw [energy_prepend (by omega) hq']
        have hsplit : demand (q+1) n r (q+1) = e+f (q+1) := by dsimp [e]; omega
        rw [hsplit,Nat.add_mul] at hE
        omega

theorem diff_not_forbidden {n : ℕ} (hn : 3 ≤ n) : ¬ forbidden n (diff n) := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rintro ⟨f,h0,hend,hstep,_,hx⟩
  have hq : 0 < q := by omega
  have hf : energy q f = diff (q+1) := by
    unfold energy
    rw [← Nat.Ico_zero_eq_range,sum_Ico_add' (fun j => f j*diff j) 0 q 1,
      show 0+1=1 by decide,sum_Ico_succ_top hq]
    change f q=0 at hend
    change diff (q+1) = ∑ j ∈ Ico 1 q, f j * diff j at hx
    rw [hend,zero_mul,add_zero,hx]
  have hd : energy q (demand q (q+1) (fun _ => 1)) = diff (q+1) := by
    have hfun : demand q (q+1) (fun _ => 1) = fun i => if q+1 ≤ reach i then 1 else 0 :=
      funext (demand_initial q)
    rw [hfun,energy_hit q hq]
  exact no_balanced_profile (Nat.zero_lt_succ q) f h0 hend
    (fun j hj => hstep j (by omega)) hq (by omega) (fun _ => 1) (by simp) (hf.trans hd.symm)

end OMA.S_mo_504087

open OMA.S_mo_504087 in
theorem OMA.solution : type_of% @OMA.S_mo_504087.main := by
  refine ⟨first_differences.1, first_differences.2, ?_⟩
  intro n hn
  exact ⟨diff_pos (by omega), diff_not_forbidden hn,
    fun _ hx hlt => all_below_forbidden hn hx hlt⟩
