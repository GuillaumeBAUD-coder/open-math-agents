import FormalConjectures.ErdosProblems.«36»

/-! Repeat each position 512 times and divide the enlarged word into 1024 equal cells.
For a uniformly chosen pair of opposite colors, let d be its difference in cell indices.
The average square-wave correlation of the two colors is nonpositive, since each
wave has total sum zero. This gives an upper bound for the first test cost by the
second moment of d. A translated quadratic supplies the second test.

A bound of 0.357 on the normalized maximum overlap forces both test expectations
above explicit thresholds. The sum of the centered and uncentered second moments
contradicts those thresholds. The two finite integer sums below certify the
deficits of the test functions on the cell grid. -/

open Finset Erdos36 Filter
open scoped BigOperators Topology

namespace OverlapLower

private def cell (b x : ℤ) : ℤ := (x-1)/b
private def tri (t : ℤ) : ℤ := 512 - 4 * min (t % 512) (512 - t % 512)
private def wave (t : ℤ) : ℤ := if t % 512 < 256 then 1 else -1

private theorem divcell_mem {b : ℤ} (hb : 0 < b) {x : ℤ} :
    cell b x ∈ Ico (0 : ℤ) 1024 ↔ x ∈ Icc 1 (1024*b) := by
  unfold cell
  rw [mem_Ico,mem_Icc,Int.le_ediv_iff_mul_le hb,Int.ediv_lt_iff_lt_mul hb,zero_mul]
  omega

private theorem sum_cells {b : ℤ} (hb : 0 < b) (F : ℤ → ℤ) :
    (∑ x ∈ Icc (1 : ℤ) (1024*b), F (cell b x)) =
      b * ∑ j ∈ Ico (0 : ℤ) 1024, F j := by
  rw [← sum_fiberwise_of_maps_to' (s := Icc (1 : ℤ) (1024*b)) (g := cell b)
    (t := Ico (0 : ℤ) 1024) (fun _ h ↦ (divcell_mem hb).mpr h) F, mul_sum]
  apply sum_congr rfl
  intro j hj
  have fiber : ((Icc (1 : ℤ) (1024*b)).filter fun x ↦ cell b x = j) =
      Ico (1+j*b) (1+(j+1)*b) := by
    ext x
    have hj' := mem_Ico.mp hj
    have hlow := mul_nonneg hj'.1 hb.le
    have hupp := mul_le_mul_of_nonneg_right (show j+1 ≤ 1024 by omega) hb.le
    rw [mem_filter, mem_Icc, mem_Ico]
    unfold cell
    rw [show (x-1)/b=j ↔ j ≤ (x-1)/b ∧ (x-1)/b < j+1 by omega,
      Int.le_ediv_iff_mul_le hb, Int.ediv_lt_iff_lt_mul hb]
    omega
  rw [fiber, sum_const, Int.card_Ico, show 1+(j+1)*b-(1+j*b)=b by ring,
    nsmul_eq_mul, Int.toNat_of_nonneg hb.le]

private theorem difference_cell {b : ℤ} (hb : 0 < b) (x y : ℤ) :
    cell b x - cell b y = (x-y)/b ∨ cell b x - cell b y = (x-y)/b + 1 := by
  unfold cell
  have hx := Int.emod_add_mul_ediv (x-1) b
  have hy := Int.emod_add_mul_ediv (y-1) b
  have hrx := Int.emod_nonneg (x-1) hb.ne'
  have hry := Int.emod_nonneg (y-1) hb.ne'
  have hrx' := Int.emod_lt_of_pos (x-1) hb
  have hry' := Int.emod_lt_of_pos (y-1) hb
  have hxy : x-y = ((x-1)%b - (y-1)%b) + b*((x-1)/b-(y-1)/b) := by
    rw [mul_sub]
    omega
  rw [hxy,Int.add_mul_ediv_left _ _ hb.ne']
  have h1 : -1 ≤ ((x-1)%b - (y-1)%b)/b := (Int.le_ediv_iff_mul_le hb).mpr (by simp; omega)
  have h2 : ((x-1)%b - (y-1)%b)/b < 1 := (Int.ediv_lt_iff_lt_mul hb).mpr (by simp; omega)
  omega

-- Costs are integer multiples of a quadratic, with one periodic correction.
private def cost1 (t : ℤ) := 5*t^2+3*512*tri t
private def cost2 (t : ℤ) := 25*t^2
private def penalty (f : ℤ → ℤ) (L q : ℤ) := max 0 (max (L-f q) (L-f (q+1)))
private def window := Ico (-1025 : ℤ) 1025

private def prefixTotal (f : ℤ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => prefixTotal f n + f ((n : ℤ)-1025)

private lemma prefixTotal_eq (f : ℤ → ℤ) (n : ℕ) :
    prefixTotal f n = ∑ q ∈ Ico (-1025 : ℤ) ((n : ℤ)-1025), f q := by
  induction n with
  | zero => simp [prefixTotal]
  | succ n ih =>
    have hs : Ico (-1025 : ℤ) ((n.succ : ℤ)-1025) =
        insert ((n : ℤ)-1025) (Ico (-1025 : ℤ) ((n : ℤ)-1025)) := by
      ext q
      simp only [mem_Ico,mem_insert,Nat.cast_succ]
      omega
    rw [hs,sum_insert (by simp),prefixTotal,ih,add_comm]

private lemma cost1_sum :
    357 * (∑ q ∈ window, penalty cost1 (8*512^2) q) ≤
      (8000-5*685) * (512:ℤ)^3 := by
  change 357 * (∑ q ∈ Ico (-1025:ℤ) ((2050:ℕ)-1025:ℤ), _) ≤ _
  rw [← prefixTotal_eq]
  set_option maxRecDepth 12000 in decide +kernel

private lemma cost2_sum :
    357 * (∑ q ∈ window, penalty cost2 (49*512^2) q) ≤
      (49000-25*652) * (512:ℤ)^3 := by
  change 357 * (∑ q ∈ Ico (-1025:ℤ) ((2050:ℕ)-1025:ℤ), _) ≤ _
  rw [← prefixTotal_eq]
  set_option maxRecDepth 12000 in decide +kernel

private lemma penalty_outside (q : ℤ) (hq : q ∉ window) :
    penalty cost1 (8*512^2) q = 0 ∧ penalty cost2 (49*512^2) q = 0 := by
  have h : q < -1025 ∨ 1025 ≤ q := by
    change q ∉ Ico (-1025 : ℤ) 1025 at hq
    rw [mem_Ico] at hq
    omega
  have htri (t : ℤ) : -512 ≤ tri t := by
    have := Int.emod_nonneg t (by decide : (512:ℤ) ≠ 0)
    have := Int.emod_lt_of_pos t (by decide : (0:ℤ) < 512)
    unfold tri
    omega
  have hs (t : ℤ) (ht : t ≤ -1024 ∨ 1024 ≤ t) : 1024^2 ≤ t^2 := by
    rcases ht with ht | ht
    · nlinarith [sq_nonneg (t+1024)]
    · nlinarith [sq_nonneg (t-1024)]
  have hp := hs q (by omega)
  have hp' := hs (q+1) (by omega)
  have hq0 := htri q
  have hq1 := htri (q+1)
  simp only [penalty,cost1,cost2,max_eq_left_iff,max_le_iff]
  constructor <;> constructor <;> nlinarith

private lemma sum_indicator {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 512) :
    ∑ r ∈ Ico (0 : ℤ) 512, (if r ∈ Ico a b then (1 : ℤ) else 0) = b-a := by
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (Ico_subset_Ico ha hb)]
  simp only [sum_const,Int.card_Ico,nsmul_eq_mul,mul_one,Int.toNat_of_nonneg (sub_nonneg.mpr hab)]

private lemma corr_interval {j : ℤ} (hj : 0 ≤ j ∧ j < 512) :
    (∑ r ∈ Ico (0 : ℤ) 512, wave (r+j) * wave r) = tri j := by
  have split_sum (a b c d : ℤ) (h0 : 0 ≤ a) (h1 : a ≤ b) (h2 : b ≤ 512)
      (h3 : 0 ≤ c) (h4 : c ≤ d) (h5 : d ≤ 512)
      (hf : ∀ r ∈ Ico (0:ℤ) 512, wave (r+j)*wave r =
        1-2*(if r ∈ Ico a b then (1:ℤ) else 0)-2*(if r ∈ Ico c d then 1 else 0)) :
      (∑ r ∈ Ico (0 : ℤ) 512, wave (r+j)*wave r) = 512-2*(b-a)-2*(d-c) := by
    rw [sum_congr rfl hf, sum_sub_distrib, sum_sub_distrib, ←mul_sum, ←mul_sum,
      sum_indicator h0 h1 h2, sum_indicator h3 h4 h5]
    norm_num [Int.card_Ico]
  have funval (r : ℤ) (hr : r ∈ Ico (0:ℤ) 512) :
      r%512 = r ∧ ((r+j)%512 = if r+j < 512 then r+j else r+j-512) := by
    have hr' := mem_Ico.mp hr
    constructor
    · exact Int.emod_eq_of_lt hr'.1 hr'.2
    · split_ifs with h
      · exact Int.emod_eq_of_lt (by omega) h
      · omega
  unfold tri
  rw [Int.emod_eq_of_lt hj.1 hj.2]
  by_cases h : j ≤ 256
  · rw [split_sum (256-j) 256 (512-j) 512 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by
        intro r hr
        obtain ⟨h1,h2⟩ := funval r hr
        have hr' := mem_Ico.mp hr
        simp only [wave,h1,h2,mem_Ico]
        split_ifs <;> omega)]
    omega
  · rw [split_sum 0 (512-j) 256 (768-j) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by
        intro r hr
        obtain ⟨h1,h2⟩ := funval r hr
        have hr' := mem_Ico.mp hr
        simp only [wave,h1,h2,mem_Ico]
        split_ifs <;> omega)]
    omega

private lemma sum_period {F : ℤ → ℤ} (hF : ∀ t, F (t%512) = F t) (v : ℤ) :
    (∑ r ∈ Ico (0:ℤ) 512, F (r+v)) = ∑ r ∈ Ico (0:ℤ) 512, F r := by
  apply sum_bij' (fun r _ ↦ (r+v)%512) (fun r _ ↦ (r-v)%512)
  · intro r hr
    exact mem_Ico.mpr ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  · intro r hr
    exact mem_Ico.mpr ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  · intro r hr
    have := mem_Ico.mp hr
    omega
  · intro r hr
    have := mem_Ico.mp hr
    omega
  · intro r hr
    exact (hF _).symm

private lemma corr_shift (u v : ℤ) :
    (∑ r ∈ Ico (0:ℤ) 512, wave (r+u)*wave (r+v)) = tri (u-v) := by
  let j := (u-v)%512
  let F := fun t ↦ wave (t+j)*wave t
  have hF (t : ℤ) : F (t%512) = F t := by
    dsimp [F,wave]
    rw [Int.emod_add_emod, Int.emod_emod]
  calc
    _ = ∑ r ∈ Ico (0:ℤ) 512, F (r+v) := by
      apply sum_congr rfl
      intro r hr
      dsimp [F,j,wave]
      rw [Int.add_emod_emod,show r+v+(u-v)=r+u by omega]
    _ = ∑ r ∈ Ico (0:ℤ) 512, F r := sum_period hF v
    _ = tri j := corr_interval ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
    _ = _ := by simp [tri,j]

private lemma wave_zero (s : ℤ) : ∑ j ∈ Ico (0:ℤ) 1024, wave (s+j) = 0 := by
  have half : (∑ j ∈ Ico (0:ℤ) 512, wave (j+s)) = 0 := by
    rw [sum_period (F:=wave) (by intro t; simp [wave])]
    change (∑ r ∈ Ico (0:ℤ) 512, if r%512<256 then (1:ℤ) else -1) = 0
    decide +kernel
  have hh (t : ℤ) : wave (512+t) = wave t := by simp [wave]
  have hu : Ico (0:ℤ) 1024 = Ico 0 512 ∪ Ico 512 1024 := by
    ext j
    simp only [mem_Ico, mem_union]
    omega
  have hd : Disjoint (Ico (0:ℤ) 512) (Ico 512 1024) := disjoint_left.mpr fun _ h1 h2 ↦
    (not_le.mpr (mem_Ico.mp h1).2) (mem_Ico.mp h2).1
  rw [hu, sum_union hd]
  have h2 : (∑ j ∈ Ico (512:ℤ) 1024, wave (s+j)) = ∑ j ∈ Ico (0:ℤ) 512, wave (j+s) := by
    refine sum_bij' (fun j _ ↦ j-512) (fun j _ ↦ j+512) ?_ ?_ ?_ ?_ ?_
    · intro j hj; have := mem_Ico.mp hj; apply mem_Ico.mpr; omega
    · intro j hj; have := mem_Ico.mp hj; apply mem_Ico.mpr; omega
    · intro j hj; omega
    · intro j hj; omega
    · intro j hj
      exact (congrArg wave (show s+j=512+(j-512+s) by omega)).trans (hh _)
  rw [h2,half]
  simpa [add_comm] using half

private lemma count_bin (A B : Finset ℤ) {b : ℤ} (hb : 0 < b) (j z : ℤ)
    (C : ℕ) (hC : ∀ k, Overlap A B k ≤ C) :
    (((A.product B).filter (fun p ↦ (p.1-p.2)/b-z=j)).card : ℤ) ≤ b*C := by
  let S := (A.product B).filter (fun p ↦ (p.1-p.2)/b-z=j)
  let T := Ico ((j+z)*b) ((j+z+1)*b)
  have hm (p : ℤ × ℤ) (hp : p ∈ S) : p.1-p.2 ∈ T := by
    have hp' := (mem_filter.mp hp).2
    change (p.1-p.2)/b-z=j at hp'
    apply mem_Ico.mpr
    exact ⟨(Int.le_ediv_iff_mul_le hb).mp (by omega),
      (Int.ediv_lt_iff_lt_mul hb).mp (by omega)⟩
  have he : S.card ≤ T.card * C := by
    rw [card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ ↦ p.1-p.2) (t:=T) hm]
    calc
      _ ≤ ∑ _k ∈ T, C := by
        apply sum_le_sum
        intro k hk
        apply le_trans (card_le_card ?_) (hC k)
        intro p hp
        obtain ⟨hp,hk'⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨(mem_filter.mp hp).1,hk'⟩
      _ = _ := by simp
  have ht : (T.card : ℤ) = b := by
    dsimp [T]
    rw [Int.card_Ico,show (j+z+1)*b-(j+z)*b=b by ring, Int.toNat_of_nonneg hb.le]
  change (S.card : ℤ) ≤ _
  rw [←ht]
  exact_mod_cast he

private lemma test_bound (A B : Finset ℤ) {b : ℤ} (hb : 0 < b) (C : ℕ)
    (hC : ∀ k, Overlap A B k ≤ C) (f : ℤ → ℤ) (L z : ℤ) (T : Finset ℤ)
    (hout : ∀ q ∉ T, penalty f L q = 0)
    (hd : ∀ x y, cell b x-cell b y=(x-y)/b ∨ cell b x-cell b y=(x-y)/b+1) :
    ((A.card:ℤ)*B.card)*L-b*C*(∑ q ∈ T, penalty f L q) ≤
      ∑ p ∈ A.product B, f (cell b p.1-cell b p.2-z) := by
  let S := A.product B
  let bin := fun p : ℤ × ℤ ↦ (p.1-p.2)/b-z
  let U := S.image bin ∪ T
  let w := penalty f L
  have hsum : (∑ p ∈ S, w (bin p)) = ∑ j ∈ U, ∑ p ∈ S with bin p = j, w j :=
    (sum_fiberwise_of_maps_to' (s:=S) (g:=bin) (t:=U) (fun p hp ↦
      mem_union_left _ (mem_image_of_mem _ hp)) w).symm
  have hupper : (∑ p ∈ S, w (bin p)) ≤ b*C*(∑ q ∈ T, w q) := by
    rw [hsum]
    calc
      _ ≤ ∑ j ∈ U, b*C*w j := by
        apply sum_le_sum
        intro j hj
        rw [sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (count_bin A B hb j z C hC) (le_max_left _ _)
      _ = ∑ j ∈ T, b*C*w j := by
        symm
        apply sum_subset (show T ⊆ U from subset_union_right)
        intro j hj hnot
        rw [show w j=0 from hout _ hnot,mul_zero]
      _ = _ := (mul_sum ..).symm
  have hdiff : ∑ p ∈ S, (L - f (cell b p.1-cell b p.2-z)) ≤ ∑ p ∈ S, w (bin p) := by
    apply sum_le_sum
    intro p hp
    obtain h | h := hd p.1 p.2
    · exact (by rw [h]; exact (le_max_left ..).trans (le_max_right ..))
    · have he : cell b p.1-cell b p.2-z=bin p+1 := by dsimp [bin]; omega
      rw [he]
      exact (le_max_right ..).trans (le_max_right ..)
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul] at hdiff
  have hc : (S.card : ℤ) = (A.card:ℤ)*B.card := by simp [S, Finset.product_eq_sprod]
  rw [hc] at hdiff
  change _ ≤ ∑ p ∈ S, _
  linarith

private lemma separable (A B : Finset ℤ) (u v : ℤ → ℤ) :
    (∑ p ∈ A.product B, u p.1*v p.2) = (∑ a ∈ A, u a)*(∑ b ∈ B, v b) := by
  rw [Finset.product_eq_sprod,sum_product,sum_mul_sum]

private lemma product_moment (A B : Finset ℤ) (u : ℤ → ℤ) (z : ℤ) :
    (∑ p ∈ A.product B, (u p.1-u p.2-z)^2) =
      B.card*(∑ a ∈ A, (u a)^2)+A.card*(∑ b ∈ B,(u b)^2)-
        2*(∑ a ∈ A,u a)*(∑ b ∈ B,u b)-
        2*z*(B.card*(∑ a ∈ A,u a)-A.card*(∑ b ∈ B,u b))+
        (A.card:ℤ)*B.card*z^2 := by
  calc
    _ = ∑ p ∈ A.product B, ((u p.1)^2*1+1*(u p.2)^2-2*(u p.1*u p.2)-
        (2*z)*(u p.1*1-1*u p.2)+z^2) := by
      apply sum_congr rfl
      intro p hp
      ring
    _ = _ := by
      rw [sum_add_distrib,sum_sub_distrib,sum_sub_distrib,sum_add_distrib,←mul_sum (A.product B) (fun p ↦ u p.1*u p.2) 2,
        ←mul_sum (A.product B) (fun p ↦ u p.1*1-1*u p.2) (2*z),
        sum_sub_distrib,separable A B (fun a ↦ (u a)^2) (fun _ ↦ 1),
        separable A B (fun _ ↦ 1) (fun a ↦ (u a)^2),separable A B u u,
        separable A B u (fun _ ↦ 1),separable A B (fun _ ↦ 1) u,sum_const]
      simp only [sum_const,nsmul_eq_mul,mul_one,card_product,Nat.cast_mul,Finset.product_eq_sprod]
      ring

-- Center at the integer part of the mean. Its rounding error is less than one cell.
private lemma moment_pair (A B : Finset ℤ) (u : ℤ → ℤ) (b n : ℤ) (hn : 0<n)
    (ha : (A.card:ℤ)=n) (hb : (B.card:ℤ)=n) (hn' : n=512*b)
    (hs : (∑ a ∈ A,u a)+(∑ a ∈ B,u a)=523776*b)
    (hsq : (∑ a ∈ A,(u a)^2)+(∑ a ∈ B,(u a)^2)=357389824*b) :
    ∃ z : ℤ, (3*(∑ p ∈ A.product B,(u p.1-u p.2)^2)+
      3*(∑ p ∈ A.product B,(u p.1-u p.2-z)^2)) ≤ (4*512^2+3)*n^2 := by
  let v := (∑ a ∈ A,u a)-(∑ a ∈ B,u a)
  let z := v/n
  refine ⟨z,?_⟩
  have hv : 0 ≤ v-z*n ∧ v-z*n < n := by
    rw [show v-z*n=v%n by dsimp [z]; rw [Int.emod_def]; ring]
    exact ⟨Int.emod_nonneg _ hn.ne',Int.emod_lt_of_pos _ hn⟩
  have hrem : (v-z*n)^2 ≤ n^2 := by
    nlinarith [mul_nonneg (show 0≤n-(v-z*n) by omega) (show 0≤n+(v-z*n) by omega)]
  have h0 := product_moment A B u 0
  simp only [sub_zero, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),add_zero] at h0
  rw [h0,product_moment A B u z,ha,hb]
  have hsum : ((∑ a ∈ A,u a)+(∑ a ∈ B,u a))^2=(523776*b)^2 := congrArg (·^2) hs
  have hsq' := congrArg (fun w : ℤ ↦ n*w) hsq
  dsimp [v] at hrem
  rw [hn'] at *
  nlinarith only [hsum,hsq',hrem]


private lemma pair_corr_nonpos (A B : Finset ℤ) {b : ℤ} (hb : 0 < b) (hd : Disjoint A B)
    (hu : A ∪ B = Icc 1 (1024*b)) :
    (∑ p ∈ A.product B, tri (cell b p.1-cell b p.2)) ≤ 0 := by
  let phase := fun r x : ℤ ↦ wave (r+cell b x)
  have zero_sum (r : ℤ) : (∑ x ∈ A, phase r x)+(∑ x ∈ B, phase r x)=0 := by
    rw [←sum_union hd,hu]
    change (∑ x ∈ Icc 1 (1024*b), (fun j ↦ wave (r+j)) (cell b x))=0
    rw [sum_cells hb (fun j ↦ wave (r+j)),wave_zero,mul_zero]
  calc
    _ = ∑ p ∈ A.product B, ∑ r ∈ Ico (0:ℤ) 512, phase r p.1*phase r p.2 := by
      exact sum_congr rfl fun p _ ↦ (corr_shift _ _).symm
    _ = ∑ r ∈ Ico (0:ℤ) 512, ∑ p ∈ A.product B, phase r p.1*phase r p.2 := sum_comm
    _ ≤ 0 := by
      apply sum_nonpos
      intro r _
      rw [separable]
      have h := zero_sum r
      nlinarith [sq_nonneg (∑ x ∈ A, phase r x),congrArg (fun v : ℤ ↦ (∑ x ∈ A,phase r x)*v) h]

private lemma sum_cost_one (A B : Finset ℤ) (b : ℤ) :
    (∑ p ∈ A.product B, cost1 (cell b p.1-cell b p.2)) =
      5*(∑ p ∈ A.product B,(cell b p.1-cell b p.2)^2)+
      3*512*(∑ p ∈ A.product B,tri (cell b p.1-cell b p.2)) := by
  simp only [cost1,sum_add_distrib,mul_sum]

private lemma min_on_blocks (A B : Finset ℤ) {b : ℤ} (hb : 0<b)
    (hd : Disjoint A B) (hu : A ∪ B = Icc 1 (1024*b))
    (ha : (A.card:ℤ)=512*b) (hc : (B.card:ℤ)=512*b) (C : ℕ)
    (hC : ∀ k, Overlap A B k ≤ C) :
    357*(512*b) < 1000*(C:ℤ) := by
  by_contra! hcontra
  let n := 512*b
  have hn : 0<n := by dsimp [n]; omega
  let u := cell b
  have total (f : ℤ → ℤ) :
      (∑ a ∈ A,f (u a))+(∑ a ∈ B,f (u a))=b*∑ i ∈ Ico (0:ℤ) 1024,f i := by
    rw [←sum_union hd,hu]
    exact sum_cells hb f
  have s1 : (∑ j ∈ Ico (0:ℤ) 1024,j) = 523776 := by decide +kernel
  have s2 : (∑ j ∈ Ico (0:ℤ) 1024,j^2) = 357389824 := by decide +kernel
  have hs := total (fun j ↦ j)
  have hsq := total (fun j ↦ j^2)
  rw [s1,mul_comm b] at hs
  rw [s2,mul_comm b] at hsq
  obtain ⟨z,hz⟩ := moment_pair A B u b n hn ha hc rfl hs hsq
  have f1 := test_bound A B hb C hC cost1 (8*512^2) 0 window
    (fun j h ↦ (penalty_outside j h).1) (difference_cell hb)
  have f2 := test_bound A B hb C hC cost2 (49*512^2) z window
    (fun j h ↦ (penalty_outside j h).2) (difference_cell hb)
  have ht := pair_corr_nonpos A B hb hd hu
  simp only [sub_zero,ha,hc,sum_cost_one] at f1
  simp only [cost2,←mul_sum,ha,hc] at f2
  have pb (f : ℤ → ℤ) (L : ℤ) : 0 ≤ ∑ q ∈ window, penalty f L q :=
    sum_nonneg fun _ _ ↦ le_max_left _ _
  have scale (s : ℤ) (hs0 : 0 ≤ s) (K : ℤ) (h : 357*s ≤ K*512^3) :
      1000*(b*(C:ℤ)*s) ≤ K*512^2*(512*b)^2 := by
    have c1 := mul_le_mul_of_nonneg_right hcontra (mul_nonneg hb.le hs0)
    have c2 := mul_le_mul_of_nonneg_right h (mul_nonneg (by decide : (0:ℤ)≤512) (sq_nonneg b))
    nlinarith only [c1,c2]
  have hb1 := scale _ (pb _ _) (8000-5*685) cost1_sum
  have hb2 := scale _ (pb _ _) (49000-25*652) cost2_sum
  change 3*(∑ p ∈ A.product B,(cell b p.1-cell b p.2)^2)+
    3*(∑ p ∈ A.product B,(cell b p.1-cell b p.2-z)^2) ≤ (4*512^2+3)*(512*b)^2 at hz
  nlinarith only [hb1,hb2,f1,f2,ht,hz,sq_pos_of_pos hb]

private def blocks (b : ℤ) (A : Finset ℤ) : Finset ℤ :=
  (A.product (Finset.Ico 0 b)).image fun p => 1 + b * p.1 + p.2

private theorem block_div {b x r : ℤ} (hb : 0 < b) (hr : 0 ≤ r ∧ r < b) :
    (1 + b * x + r - 1) / b = x := by
  rw [show 1 + b * x + r - 1 = r + b * x by omega,
    Int.add_mul_ediv_left _ _ hb.ne', Int.ediv_eq_zero_of_lt hr.1 hr.2, zero_add]

private theorem block_mod {b x r : ℤ} (hr : 0 ≤ r ∧ r < b) :
    (1 + b * x + r - 1) % b = r := by
  rw [show 1 + b * x + r - 1 = r + b * x by omega,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr.1 hr.2]

private theorem mem_blocks {b z : ℤ} (hb : 0 < b) {A : Finset ℤ} :
    z ∈ blocks b A ↔ (z - 1) / b ∈ A := by
  constructor
  · intro hz
    obtain ⟨⟨x, r⟩, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx, hr⟩ := Finset.mem_product.mp hp
    rw [block_div hb (Finset.mem_Ico.mp hr)]
    exact hx
  · intro hz
    refine Finset.mem_image.mpr ⟨((z - 1) / b, (z - 1) % b), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hz,
        Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb⟩⟩
    · change 1 + b * ((z - 1) / b) + (z - 1) % b = z
      have h := Int.emod_add_mul_ediv (z - 1) b
      omega

private theorem card_blocks {b : ℤ} (hb : 0 < b) (A : Finset ℤ) :
    (blocks b A).card = A.card * b.toNat := by
  unfold blocks
  have hInj : Set.InjOn (fun p : ℤ × ℤ => 1 + b * p.1 + p.2)
      (↑(A.product (Finset.Ico 0 b)) : Set (ℤ × ℤ)) := by
    intro p hp q hq h
    have hp' := Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_coe.mp hp)).2
    have hq' := Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_coe.mp hq)).2
    exact Prod.ext
      ((block_div hb hp').symm.trans ((congrArg (fun z : ℤ => (z - 1) / b) h).trans
        (block_div hb hq')))
      ((block_mod hp').symm.trans ((congrArg (fun z : ℤ => (z - 1) % b) h).trans
        (block_mod hq')))
  rw [Finset.card_image_of_injOn hInj, Finset.product_eq_sprod, Finset.card_product, Int.card_Ico, sub_zero]

private theorem blocks_partition {b : ℤ} (hb : 0 < b) {ones zeros : Finset ℤ}
    {L : ℤ} (hdisj : Disjoint ones zeros) (hpartition : ones ∪ zeros = Finset.Ico 0 L) :
    Disjoint (blocks b ones) (blocks b zeros) ∧
    blocks b ones ∪ blocks b zeros = Finset.Icc 1 (L * b) := by
  constructor
  · rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact Finset.disjoint_left.mp hdisj
      ((mem_blocks hb).mp hz₁) ((mem_blocks hb).mp hz₂)
  · ext z
    rw [Finset.mem_union, mem_blocks hb, mem_blocks hb, ← Finset.mem_union,
      hpartition, Finset.mem_Ico, Finset.mem_Icc,
      Int.le_ediv_iff_mul_le hb, Int.ediv_lt_iff_lt_mul hb, zero_mul]
    omega

private theorem blocks_overlap {b : ℤ} (hb : 0 < b) {ones zeros : Finset ℤ} {c : ℕ}
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c) (k : ℤ) :
    Overlap (blocks b ones) (blocks b zeros) k ≤ c * b.toNat := by
  let pairs := ((blocks b ones).product (blocks b zeros)).filter fun p => p.1 - p.2 = k
  let residue := fun p : ℤ × ℤ => (p.1 - 1) % b
  let quotients := fun p : ℤ × ℤ => ((p.1 - 1) / b, (p.2 - 1) / b)
  change pairs.card ≤ c * b.toNat
  rw [Finset.card_eq_sum_card_fiberwise (f := residue)
    (t := Finset.Ico 0 b) (fun _ _ =>
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb⟩)]
  calc
    _ ≤ ∑ _r ∈ Finset.Ico 0 b, c := by
      apply Finset.sum_le_sum
      intro r _
      -- The residue and shift determine a single difference between the block indices.
      let d := -((r - k) / b)
      have hCard : (pairs.filter fun p => residue p = r).card ≤ Overlap ones zeros d := by
        apply Finset.card_le_card_of_injOn quotients
        · intro p hp
          have ⟨hp', hr⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
          have ⟨hmem, hk⟩ := Finset.mem_filter.mp hp'
          have ⟨ha, hc⟩ := Finset.mem_product.mp hmem
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨(mem_blocks hb).mp ha, (mem_blocks hb).mp hc⟩, ?_⟩
          have h := Int.emod_add_mul_ediv (p.1 - 1) b
          change (p.1 - 1) % b = r at hr
          have hRight : p.2 - 1 = (r - k) + b * ((p.1 - 1) / b) := by omega
          change (p.1 - 1) / b - (p.2 - 1) / b = d
          rw [hRight, Int.add_mul_ediv_left _ _ hb.ne']
          dsimp [d]
          omega
        · intro p hp q hq hpq
          have ⟨hp', hrp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
          have ⟨hq', hrq⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          have hpDiff := (Finset.mem_filter.mp hp').2
          have hqDiff := (Finset.mem_filter.mp hq').2
          have hDiv : (p.1 - 1) / b = (q.1 - 1) / b := congrArg Prod.fst hpq
          have hpEd := Int.emod_add_mul_ediv (p.1 - 1) b
          have hqEd := Int.emod_add_mul_ediv (q.1 - 1) b
          change (p.1 - 1) % b = r at hrp
          change (q.1 - 1) % b = r at hrq
          rw [hDiv] at hpEd
          exact Prod.ext (by omega) (by omega)
      exact hCard.trans (word_overlap d)
    _ = c * b.toNat := by simp [Int.card_Ico, Nat.mul_comm]

private def shiftDown : ℤ ↪ ℤ where
  toFun x := x - 1
  inj' := by
    intro x y he
    change x - 1 = y - 1 at he
    omega

private theorem overlap_shiftDown (A B : Finset ℤ) (k : ℤ) :
    Overlap (A.map shiftDown) (B.map shiftDown) k = Overlap A B k := by
  unfold Overlap
  refine Finset.card_bij'
    (fun p _ => (p.1 + 1, p.2 + 1)) (fun p _ => (p.1 - 1, p.2 - 1)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hp
    obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp hpa
    obtain ⟨b, hb, heb⟩ := Finset.mem_map.mp hpb
    change a - 1 = p.1 at hea
    change b - 1 = p.2 at heb
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by
      rwa [show p.1 + 1 = a by omega], by rwa [show p.2 + 1 = b by omega]⟩, by dsimp; omega⟩
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
      Finset.mem_map.mpr ⟨p.1, ha, rfl⟩, Finset.mem_map.mpr ⟨p.2, hb, rfl⟩⟩, by dsimp; omega⟩
  · intro p _
    exact Prod.ext (by simp) (by simp)
  · intro p _
    exact Prod.ext (by simp) (by simp)

private theorem bdd_overlap (A B : Finset ℤ) : BddAbove (Set.range (Overlap A B)) := by
  use (A.product B).card
  rintro x ⟨k, rfl⟩
  exact Finset.card_filter_le _ _

private theorem exists_min_partition (m : ℕ) :
    ∃ A B : Finset ℤ, Disjoint A B ∧ A ∪ B = Finset.Icc 1 (2 * m : ℤ) ∧
      A.card = B.card ∧ MaxOverlap A B = M m := by
  let T : Set ℕ := {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B) (_union : A ∪ B = Finset.Icc 1 (2 * m : ℤ))
    (_same_card : A.card = B.card)}
  have hT : T.Nonempty := by
    refine ⟨_, Finset.Icc 1 (m : ℤ), Finset.Ioc (m : ℤ) (2 * m : ℤ), ?_, ?_, ?_, rfl⟩
    · rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨_, hz⟩ := Finset.mem_Icc.mp hz
      obtain ⟨hz', _⟩ := Finset.mem_Ioc.mp hz'
      omega
    · ext z
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    · rw [Int.card_Icc, Int.card_Ioc]
      congr 1
      omega
  obtain ⟨A, B, hd, hu, hc, he⟩ := (show M m ∈ T from csInf_mem hT)
  exact ⟨A, B, hd, hu, hc, he⟩


private lemma min_cards {A B : Finset ℤ} {n : ℕ} (hd : Disjoint A B)
    (hu : A ∪ B = Icc 1 (2*n : ℤ)) (he : A.card=B.card) : A.card=n ∧ B.card=n := by
  have h := card_union_of_disjoint hd
  rw [hu,Int.card_Icc] at h
  omega

private lemma quotient_le_one (n : ℕ) : MinOverlapQuotient n ≤ 1 := by
  obtain ⟨A,B,hd,hu,he,hm⟩ := exists_min_partition n
  have hn := (min_cards hd hu he).1
  have hover (k : ℤ) : Overlap A B k ≤ A.card := by
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (mem_product.mp (mem_filter.mp hp).1).1
    · intro p hp q hq he
      have h1 := (mem_filter.mp hp).2
      have h2 := (mem_filter.mp hq).2
      exact Prod.ext he (by omega)
  have hx : M n ≤ n := by rw [←hm,←hn]; exact ciSup_le hover
  by_cases h : n=0
  · simp [MinOverlapQuotient,h]
  · unfold MinOverlapQuotient
    apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    simpa using (show (M n:ℝ) ≤ (n:ℝ) by exact_mod_cast hx)

private theorem finite_lower {n : ℕ} (hn : 0<n) :
    (357 / 1000 : ℝ) ≤ MinOverlapQuotient n := by
  obtain ⟨A,B,hd,hu,he,hm⟩ := exists_min_partition n
  obtain ⟨hA,hB⟩ := min_cards hd hu he
  have hpart : A.map shiftDown ∪ B.map shiftDown = Finset.Ico 0 (2 * n : ℤ) := by
    rw [← Finset.map_union, hu]
    ext x
    simp only [Finset.mem_map, Finset.mem_Ico, Finset.mem_Icc]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change z - 1 = x at hzx
      omega
    · intro hx
      exact ⟨x+1,by omega,by change x+1-1=x; omega⟩
  have hb : (0:ℤ) < 512 := by decide
  have hp := blocks_partition hb ((disjoint_map shiftDown).mpr hd) hpart
  have bound (k : ℤ) : Overlap (A.map shiftDown) (B.map shiftDown) k ≤ M n := by
    rw [overlap_shiftDown, ←hm]
    exact le_ciSup (bdd_overlap A B) _
  have ha' : ((blocks 512 (A.map shiftDown)).card:ℤ)=512*n := by
    rw [card_blocks hb, card_map, hA]
    push_cast
    ring
  have hb' : ((blocks 512 (B.map shiftDown)).card:ℤ)=512*n := by
    rw [card_blocks hb, card_map, hB]
    push_cast
    ring
  have h' := min_on_blocks _ _ (by exact_mod_cast hn) hp.1
    (hp.2.trans (by congr 1; ring)) ha' hb' (M n*512) (fun k ↦ blocks_overlap hb bound k)
  push_cast at h'
  unfold MinOverlapQuotient
  apply (le_div_iff₀ (by exact_mod_cast hn)).mpr
  have hz : (357:ℤ)*n ≤ 1000*M n := by omega
  have hr : (357:ℝ)*n ≤ 1000*M n := by exact_mod_cast hz
  linarith

end OverlapLower

theorem OMA.solution : type_of% @Erdos36.minimum_overlap.variants.lower.haugland_1996 := by
  have h : (357/1000 : ℝ) ≤ Filter.atTop.liminf MinOverlapQuotient :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le _ OverlapLower.quotient_le_one)
      ((eventually_gt_atTop (0:ℕ)).mono fun _ hn ↦ OverlapLower.finite_lower hn)
  apply lt_of_lt_of_le _ h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  apply (Real.sqrt_lt' (by norm_num : 0 < (357/1000:ℝ))).mpr
  have hs : (4:ℝ)-(357/1000)^2 < Real.sqrt 15 := Real.lt_sqrt_of_sq_lt (by norm_num)
  linarith