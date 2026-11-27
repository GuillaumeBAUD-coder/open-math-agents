import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_53

/-! Finite interval estimates for Temur's continued fraction construction. -/

open Set
noncomputable section

namespace Temur

structure Prefix where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  c_nonneg : 0 ≤ c
  d_pos : 0 < d
  c_le_d : c ≤ d
  det : a*d-b*c = 1

def Prefix.eval (F : Prefix) (t : ℝ) : ℝ := (F.a*t + F.b)/(F.c*t + F.d)
def Prefix.len (F : Prefix) : ℝ := F.eval 1 - F.eval 0
def Prefix.cell (F : Prefix) : Set ℝ := Icc (F.eval 0) (F.eval 1)

open Prefix

def root : Prefix := ⟨1,0,0,1,by norm_num,by norm_num,by norm_num,by norm_num⟩

def branch : Bool → Prefix
  | false => ⟨2,3,3,5,by norm_num,by norm_num,by norm_num,by norm_num⟩
  | true => ⟨3,5,4,7,by norm_num,by norm_num,by norm_num,by norm_num⟩

lemma branch_bounds (e : Bool) :
    0 ≤ (branch e).a ∧ (branch e).a ≤ (branch e).b := by
  cases e <;> norm_num [branch]

private lemma den_pos (F : Prefix) {x : ℝ} (hx : 0 ≤ x) : 0 < F.c*x + F.d :=
  add_pos_of_nonneg_of_pos (mul_nonneg F.c_nonneg hx) F.d_pos

def Prefix.step (F : Prefix) (e : Bool) : Prefix where
  a := F.a*(branch e).a + F.b*(branch e).c
  b := F.a*(branch e).b + F.b*(branch e).d
  c := F.c*(branch e).a + F.d*(branch e).c
  d := F.c*(branch e).b + F.d*(branch e).d
  c_nonneg := add_nonneg (mul_nonneg F.c_nonneg (branch_bounds e).1)
    (mul_nonneg F.d_pos.le (branch e).c_nonneg)
  d_pos := add_pos_of_nonneg_of_pos
    (mul_nonneg F.c_nonneg ((branch_bounds e).1.trans (branch_bounds e).2))
    (mul_pos F.d_pos (branch e).d_pos)
  c_le_d := add_le_add (mul_le_mul_of_nonneg_left (branch_bounds e).2 F.c_nonneg)
    (mul_le_mul_of_nonneg_left (branch e).c_le_d F.d_pos.le)
  det := by
    calc
      _ = (F.a*F.d-F.b*F.c) * ((branch e).a*(branch e).d-(branch e).b*(branch e).c) := by ring
      _ = _ := by rw [F.det,(branch e).det,one_mul]

lemma eval_sub (F : Prefix) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    F.eval y - F.eval x = (y-x)/((F.c*x+F.d)*(F.c*y+F.d)) := by
  unfold eval
  rw [div_sub_div _ _ (den_pos F hy).ne' (den_pos F hx).ne', mul_comm (F.c*y + F.d)]
  congr 1
  · linear_combination (y-x)*F.det
  · ring

lemma len_eq (F : Prefix) : F.len = 1/(F.d*(F.c+F.d)) := by
  unfold len
  rw [eval_sub F (by norm_num) (by norm_num)]
  simp

lemma len_pos (F : Prefix) : 0 < F.len := by
  rw [len_eq]
  exact div_pos zero_lt_one (mul_pos F.d_pos (add_pos_of_nonneg_of_pos F.c_nonneg F.d_pos))

lemma eval_strict (F : Prefix) : StrictMonoOn F.eval (Ici 0) := by
  intro x hx y hy h
  have h' := eval_sub F hx hy
  have hpos : 0 < (y-x)/((F.c*x+F.d)*(F.c*y+F.d)) :=
    div_pos (sub_pos.mpr h) (mul_pos (den_pos F hx) (den_pos F hy))
  linarith

lemma branch_mem (e : Bool) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (branch e).eval t ∈ Icc (0 : ℝ) 1 := by
  have hm := (eval_strict (branch e)).monotoneOn
  have h₀ := hm (show (0:ℝ) ∈ Ici 0 by simp) (show t ∈ Ici 0 from ht.1) ht.1
  have h₁ := hm (show t ∈ Ici 0 from ht.1) (show (1:ℝ) ∈ Ici 0 by norm_num) ht.2
  have h2 : 0 ≤ (branch e).eval 0 := by cases e <;> norm_num [eval,branch]
  have h3 : (branch e).eval 1 ≤ 1 := by cases e <;> norm_num [eval,branch]
  exact ⟨h2.trans h₀,h₁.trans h3⟩

lemma step_eval (F : Prefix) (e : Bool) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (F.step e).eval t = F.eval ((branch e).eval t) := by
  let A := (branch e).a*t + (branch e).b
  let B := (branch e).c*t + (branch e).d
  have hB : B ≠ 0 := (den_pos (branch e) ht.1).ne'
  have hm (u v : ℝ) : (u*(A/B)+v)*B = u*A+v*B := by
    rw [add_mul,mul_assoc,div_mul_cancel₀ _ hB]
  calc
    _ = (F.a*A+F.b*B)/(F.c*A+F.d*B) := by
      unfold eval
      congr 1 <;> dsimp [step,A,B] <;> ring
    _ = ((F.a*(A/B)+F.b)*B)/((F.c*(A/B)+F.d)*B) := by rw [hm,hm]
    _ = _ := mul_div_mul_right _ _ hB
lemma step_subset (F : Prefix) (e : Bool) : (F.step e).cell ⊆ F.cell := by
  have h0 : (0:ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1:ℝ) ∈ Icc 0 1 := by norm_num
  have hm := (eval_strict F).monotoneOn
  intro x hx
  have hl := hm (show (0:ℝ) ∈ Ici 0 by simp)
    (show (branch e).eval 0 ∈ Ici 0 from (branch_mem e h0).1) (branch_mem e h0).1
  have hu := hm (show (branch e).eval 1 ∈ Ici 0 from (branch_mem e h1).1)
    (show (1:ℝ) ∈ Ici 0 by norm_num) (branch_mem e h1).2
  change (F.step e).eval 0 ≤ x ∧ x ≤ (F.step e).eval 1 at hx
  rw [step_eval F e h0,step_eval F e h1] at hx
  exact ⟨hl.trans hx.1,hx.2.trans hu⟩

lemma distortion (F : Prefix) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    F.len*(y-x)/2 ≤ F.eval y - F.eval x ∧ F.eval y - F.eval x ≤ 2*F.len*(y-x) := by
  have hy₀ := hx.trans hxy
  have hx₁ := hxy.trans hy
  rw [len_eq,eval_sub F hx hy₀]
  let D := (F.c*x+F.d)*(F.c*y+F.d)
  let E := F.d*(F.c+F.d)
  have hD : 0 < D := mul_pos (den_pos F hx) (den_pos F hy₀)
  have hE : 0 < E := mul_pos F.d_pos (add_pos_of_nonneg_of_pos F.c_nonneg F.d_pos)
  have hlow : E ≤ 2*D := by
    have hDD : F.d*F.d ≤ D := by
      dsimp [D]
      exact mul_le_mul (le_add_of_nonneg_left (mul_nonneg F.c_nonneg hx))
        (le_add_of_nonneg_left (mul_nonneg F.c_nonneg hy₀)) F.d_pos.le (den_pos F hx).le
    dsimp [E]
    nlinarith [mul_le_mul_of_nonneg_left F.c_le_d F.d_pos.le]
  have hhigh : D ≤ 2*E := by
    have hDD : D ≤ (F.c+F.d)*(F.c+F.d) := by
      dsimp [D]
      apply mul_le_mul
      · have := mul_le_mul_of_nonneg_left hx₁ F.c_nonneg
        linarith
      · have := mul_le_mul_of_nonneg_left hy F.c_nonneg
        linarith
      · exact (den_pos F hy₀).le
      · exact add_nonneg F.c_nonneg F.d_pos.le
    dsimp [E]
    nlinarith [mul_le_mul_of_nonneg_right F.c_le_d (add_nonneg F.c_nonneg F.d_pos.le)]
  change 1/E*(y-x)/2 ≤ (y-x)/D ∧ (y-x)/D ≤ 2*(1/E)*(y-x)
  constructor
  · have hh : (y-x)/(2*E) ≤ (y-x)/D :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hD hhigh
    convert hh using 1
    field_simp [hE.ne']
  · have hh : (y-x)/D ≤ (y-x)/(E/2) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (half_pos hE) (by linarith)
    convert hh using 1
    field_simp [hE.ne']

lemma endpoint₀_false : (branch false).eval 0 = 3/5 := by norm_num [eval,branch]
lemma endpoint₁_false : (branch false).eval 1 = 5/8 := by norm_num [eval,branch]
lemma endpoint₀_true : (branch true).eval 0 = 5/7 := by norm_num [eval,branch]
lemma endpoint₁_true : (branch true).eval 1 = 8/11 := by norm_num [eval,branch]

lemma step_len (F : Prefix) (e : Bool) :
    F.len/154 ≤ (F.step e).len ∧ (F.step e).len ≤ F.len/20 := by
  have h0 : (0:ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1:ℝ) ∈ Icc 0 1 := by norm_num
  have he : (F.step e).len = F.eval ((branch e).eval 1) - F.eval ((branch e).eval 0) := by
    unfold len
    rw [step_eval F e h0,step_eval F e h1]
  rw [he]
  cases e
  · obtain ⟨hlo,hhi⟩ := distortion F (x:=3/5) (y:=5/8) (by norm_num) (by norm_num) (by norm_num)
    rw [endpoint₀_false,endpoint₁_false]
    constructor <;> linarith only [hlo,hhi,len_pos F]
  · obtain ⟨hlo,hhi⟩ := distortion F (x:=5/7) (y:=8/11) (by norm_num) (by norm_num) (by norm_num)
    rw [endpoint₀_true,endpoint₁_true]
    constructor <;> linarith only [hlo,hhi,len_pos F]

lemma step_false_cell (F : Prefix) : (F.step false).cell =
    Icc (F.eval (3/5)) (F.eval (5/8)) := by
  unfold cell
  rw [step_eval F false (by norm_num),step_eval F false (by norm_num),
    endpoint₀_false,endpoint₁_false]

lemma step_true_cell (F : Prefix) : (F.step true).cell =
    Icc (F.eval (5/7)) (F.eval (8/11)) := by
  unfold cell
  rw [step_eval F true (by norm_num),step_eval F true (by norm_num),
    endpoint₀_true,endpoint₁_true]

def misses (F : Prefix) (q : ℕ) (δ : ℝ) : Prop :=
  ∀ x ∈ F.cell, ∀ a : ℤ, δ < |x - (a : ℝ)/q|

lemma grid_choice (F : Prefix) {q : ℕ} (hq : 0 < q) (hs : F.len ≤ 1/(q : ℝ)) :
    ∃ e : Bool, misses (F.step e) q (F.len/128) := by
  classical
  by_contra h
  push Not at h
  have hfalse := h false
  have htrue := h true
  unfold misses at hfalse htrue
  push Not at hfalse htrue
  obtain ⟨x₀,hx₀,z₀,hz₀⟩ := hfalse
  obtain ⟨x₁,hx₁,z₁,hz₁⟩ := htrue
  rw [step_false_cell] at hx₀
  rw [step_true_cell] at hx₁
  have hd₀ := (abs_le.mp hz₀)
  have hd₁ := (abs_le.mp hz₁)
  have gap := (distortion F (x:=5/8) (y:=5/7) (by norm_num) (by norm_num) (by norm_num)).1
  have left := (distortion F (x:=0) (y:=3/5) (by norm_num) (by norm_num) (by norm_num)).1
  have right := (distortion F (x:=8/11) (y:=1) (by norm_num) (by norm_num) (by norm_num)).1
  have hLt₀ : F.eval 0 < (z₀ : ℝ)/q := by linarith [hx₀.1,hd₀.2,left,len_pos F]
  have hLt₁ : (z₁ : ℝ)/q < F.eval 1 := by linarith [hx₁.2,hd₁.1,right,len_pos F]
  have hm : (z₀ : ℝ)/q < (z₁ : ℝ)/q := by
    linarith [hx₀.2,hx₁.1,hd₀.1,hd₁.2,gap,len_pos F]
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hz01 : z₀ < z₁ := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hqR).mp hm
  have hzDiff : (1:ℝ) ≤ (z₁ : ℝ) - (z₀ : ℝ) := by
    exact_mod_cast (show (1:ℤ) ≤ z₁ - z₀ by omega)
  have hweak : 1/(q : ℝ) ≤ (z₁ : ℝ)/q - (z₀ : ℝ)/q := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right hzDiff hqR.le
  exact (not_lt_of_ge (hs.trans hweak)) (by unfold len; linarith)

lemma cell_image (F : Prefix) : F.eval '' Icc 0 1 = F.cell := by
  have hc : ContinuousOn F.eval (Icc 0 1) := by
    unfold eval
    apply (by fun_prop : ContinuousOn (fun t : ℝ ↦ F.a*t + F.b) (Icc 0 1)).div
      (by fun_prop)
    exact fun x hx ↦ (den_pos F hx.1).ne'
  exact hc.image_Icc_of_monotoneOn zero_le_one
    (fun _ hx _ hy h ↦ (eval_strict F).monotoneOn hx.1 hy.1 h)

end Temur

open Filter Set
open scoped Topology

namespace Temur

open Prefix

def base (n : ℕ) := 2 + n.factorization 2
def assigned (b i : ℕ) := 2^(b-2)*(2*i+1)-1

lemma base_ge (n : ℕ) : 2 ≤ base n := by simp [base]

lemma assigned_succ (b i : ℕ) (hb : 2 ≤ b) :
    assigned b (i+1) = assigned b i + 2^(b-1) := by
  have h := pow_pos (by decide : 0 < (2 : ℕ)) (b-2)
  have h1 : 0 < 2^(b-2)*(2*i+1) := by positivity
  have he : (2:ℕ)^(b-1) = 2^(b-2)*2 := by rw [show b-1 = b-2+1 by omega, pow_succ]
  simp only [assigned,he]
  have hEq : (2:ℕ)^(b-2)*(2*(i+1)+1) = 2^(b-2)*(2*i+1) + 2^(b-2)*2 := by ring
  rw [hEq]
  omega

lemma base_assigned (b i : ℕ) (hb : 2 ≤ b) : base (assigned b i+1) = b := by
  have hne : (2:ℕ)^(b-2)*(2*i+1) ≠ 0 := by positivity
  have hv : (2*i+1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by omega)
  have he : assigned b i+1 = 2^(b-2)*(2*i+1) := by unfold assigned; omega
  rw [he,base,Nat.factorization_mul (by positivity) (by omega),Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,hv]
  omega

lemma assigned_first_le (b : ℕ) (hb : 2 ≤ b) : assigned b 0 ≤ 2^(b-1) := by
  have he : (2:ℕ)^(b-1) = 2^(b-2)*2 := by rw [show b-1 = b-2+1 by omega, pow_succ]
  simp [assigned,he]
  omega

lemma assigned_ge (b i : ℕ) (hb : 2 ≤ b) : i ≤ assigned b i := by
  induction i with
  | zero => omega
  | succ i ih =>
    have h : 0 < (2:ℕ)^(b-1) := by positivity
    rw [assigned_succ b i hb]
    omega

def gridExponent (b : ℕ) (F : Prefix) : ℕ :=
  Nat.findGreatest (fun k ↦ F.len * (b : ℝ)^k ≤ 1) ⌊1/F.len⌋₊

lemma grid_exp_good (b : ℕ) (F : Prefix) (hF : F.len ≤ 1) :
    F.len * (b : ℝ)^(gridExponent b F) ≤ 1 := by
  unfold gridExponent
  exact Nat.findGreatest_spec (P := fun k ↦ F.len * (b : ℝ)^k ≤ 1) (m := 0) (Nat.zero_le _) (by simpa using hF)

lemma grid_exp_largest {b : ℕ} (hb : 2 ≤ b) (F : Prefix) {k : ℕ}
    (h : F.len * (b : ℝ)^k ≤ 1) : k ≤ gridExponent b F := by
  apply Nat.le_findGreatest _ h
  apply Nat.le_floor
  have hPow : (k : ℝ) ≤ (b : ℝ)^k := by
    exact_mod_cast (Nat.lt_pow_self (by omega : 1 < b) (n := k)).le
  have hBound : (b : ℝ)^k ≤ 1 / F.len :=
    (le_div_iff₀ (len_pos F)).mpr (by simpa [mul_comm] using h)
  exact hPow.trans hBound

lemma admissible_grid (F : Prefix) {b : ℕ} (hb : 2 ≤ b) (hF : F.len ≤ 1) :
    ∃ e : Bool, misses (F.step e) (b^(gridExponent b F)) (F.len/128) := by
  have hp : 0 < b^(gridExponent b F) := by positivity
  apply grid_choice F hp
  apply (le_div_iff₀ (by exact_mod_cast hp : 0 < ((b^(gridExponent b F) : ℕ) : ℝ))).mpr
  simpa using grid_exp_good b F hF

def chooseBranch (b : ℕ) (F : Prefix) : Bool := by
  classical
  exact if misses (F.step false) (b^(gridExponent b F)) (F.len/128) then false else true

lemma chooseBranch_good {b : ℕ} (hb : 2 ≤ b) (F : Prefix) (hF : F.len ≤ 1) :
    misses (F.step (chooseBranch b F)) (b^(gridExponent b F)) (F.len/128) := by
  classical
  unfold chooseBranch
  split_ifs with h
  · exact h
  · obtain ⟨e,he⟩ := admissible_grid F hb hF
    cases e
    · exact (h he).elim
    · exact he

def steps : ℕ → Prefix
  | 0 => root
  | n+1 => (steps n).step (chooseBranch (base (n+1)) (steps n))

lemma root_cell : root.cell = Icc 0 1 := by simp [cell,root,eval]
lemma root_len : root.len = 1 := by norm_num [len,root,eval]

lemma steps_subset (n : ℕ) : (steps (n+1)).cell ⊆ (steps n).cell := step_subset _ _

lemma steps_antitone : Antitone (fun n ↦ (steps n).cell) :=
  antitone_nat_of_succ_le steps_subset

lemma steps_start (n : ℕ) : (steps n).cell ⊆ Icc (0 : ℝ) 1 := by
  simpa only [steps,root_cell] using steps_antitone (Nat.zero_le n)

lemma steps_len_le (n : ℕ) : (steps n).len ≤ (1/20 : ℝ)^n := by
  induction n with
  | zero => simp [steps,root_len]
  | succ n ih =>
    have h := (step_len (steps n) (chooseBranch (base (n+1)) (steps n))).2
    rw [pow_succ]
    change (steps (n+1)).len ≤ _ at h
    linarith

lemma steps_len_lower (n d : ℕ) :
    (steps n).len * (1/154 : ℝ)^d ≤ (steps (n+d)).len := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, ← mul_assoc]
    have h := (step_len (steps (n+d)) (chooseBranch (base (n+d+1)) (steps (n+d)))).1
    change (steps (n+d)).len/154 ≤ (steps (n+d+1)).len at h
    have he := mul_le_mul_of_nonneg_right ih (by norm_num : (0 : ℝ) ≤ 1/154)
    exact he.trans (by simpa [div_eq_mul_inv, Nat.add_assoc] using h)

lemma steps_len_le_one (n : ℕ) : (steps n).len ≤ 1 := by
  exact (steps_len_le n).trans (pow_le_one₀ (by norm_num) (by norm_num))

lemma cell_nonempty (F : Prefix) : F.cell.Nonempty := by
  refine ⟨F.eval 0,le_rfl,?_⟩
  have h := len_pos F
  unfold len at h
  linarith

lemma exists_intersection : ∃ ξ : ℝ, ∀ n, ξ ∈ (steps n).cell := by
  let a (n : ℕ) := (steps n).eval 0
  let A := Set.range a
  have ha (n m : ℕ) : a n ≤ (steps m).eval 1 := by
    by_cases h : m ≤ n
    · have := steps_antitone h (show a n ∈ (steps n).cell from
        ⟨le_rfl,sub_pos.mp (len_pos (steps n)) |>.le⟩)
      exact this.2
    · have hnm : n ≤ m := by omega
      have := steps_antitone hnm (show a m ∈ (steps m).cell from
        ⟨le_rfl,sub_pos.mp (len_pos (steps m)) |>.le⟩)
      exact this.1.trans (sub_pos.mp (len_pos (steps m))).le
  refine ⟨sSup A, fun n ↦ ⟨le_csSup ⟨(steps n).eval 1,?_⟩ ⟨n,rfl⟩,?_⟩⟩
  · rintro _ ⟨m,rfl⟩
    exact ha m n
  · exact csSup_le ⟨a 0,⟨0,rfl⟩⟩ (by rintro _ ⟨m,rfl⟩; exact ha m n)

end Temur

namespace Temur

open Prefix

lemma all_grids (ξ : ℝ) (hξ : ∀ n, ξ ∈ (steps n).cell) (b : ℕ) (hb : 2 ≤ b)
    (k : ℕ) (a : ℤ) : (154 : ℝ) ^ (-(2^b) : ℤ) < |(b : ℝ)^k * ξ - a| := by
  let q : ℝ := (b : ℝ)^k
  have hq : 0 < q := by dsimp [q]; positivity
  let D := 2^(b-1)
  let ok (i : ℕ) := (steps (assigned b i)).len * q ≤ 1
  have hExists : ∃ i, ok i := by
    have hlim : Tendsto (fun n : ℕ ↦ (1/20 : ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨N,hN⟩ := eventually_atTop.mp
      (hlim.eventually (gt_mem_nhds (one_div_pos.mpr hq)))
    refine ⟨N,?_⟩
    unfold ok
    apply (le_div_iff₀ hq).mp
    exact (steps_len_le _).trans (hN _ (assigned_ge b N hb)).le
  let i := Nat.find hExists
  let n := assigned b i
  have hn : (steps n).len * q ≤ 1 := Nat.find_spec hExists
  have hbase : base (n+1) = b := base_assigned b i hb
  have hBig : (1/154 : ℝ)^D ≤ q*(steps n).len := by
    by_cases hi : i = 0
    · have hnD : n ≤ D := by simpa [n,hi,D] using assigned_first_le b hb
      have hh := steps_len_lower 0 n
      simp only [steps,root_len,one_mul,zero_add] at hh
      have hqOne : 1 ≤ q := one_le_pow₀ (by exact_mod_cast (show 1 ≤ b by omega))
      calc
        _ ≤ (1/154 : ℝ)^n :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hnD
        _ ≤ (steps n).len := hh
        _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hqOne (len_pos _).le
    · obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have htlt : t < i := by omega
      have hprev : 1 < q*(steps (assigned b t)).len := by
        have h := Nat.find_min hExists htlt
        change ¬ (steps (assigned b t)).len * q ≤ 1 at h
        simpa [mul_comm] using lt_of_not_ge h
      have hnEq : n = assigned b t + D := by
        dsimp [n,D]
        rw [ht]
        exact assigned_succ b t hb
      have hh := steps_len_lower (assigned b t) D
      rw [← hnEq] at hh
      calc
        _ ≤ (q*(steps (assigned b t)).len)*(1/154 : ℝ)^D := by
          simpa using mul_le_mul_of_nonneg_right hprev.le (by positivity : 0 ≤ (1/154 : ℝ)^D)
        _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hh hq.le
  have he : k ≤ gridExponent b (steps n) := grid_exp_largest hb (steps n) hn
  let e := gridExponent b (steps n)
  let r := b^(e-k)
  have hpow : b^e = b^k*r := by
    unfold r
    rw [← pow_add,show k+(e-k)=e by omega]
  have hr : 0 < (r : ℝ) := by dsimp [r]; positivity
  have hgood := chooseBranch_good (base_ge (n+1)) (steps n) (steps_len_le_one n)
  rw [hbase] at hgood
  have hξn : ξ ∈ ((steps n).step (chooseBranch b (steps n))).cell := by
    simpa only [steps,hbase] using hξ (n+1)
  have hm := hgood ξ hξn (a*(r:ℤ))
  change (steps n).len/128 < |ξ - ((a*(r:ℤ) : ℤ) : ℝ) / ((b^e : ℕ) : ℝ)| at hm
  have hrat : ((a*(r:ℤ) : ℤ) : ℝ) / ((b^e : ℕ) : ℝ) = (a : ℝ)/q := by
    rw [hpow]
    push_cast
    exact mul_div_mul_right _ _ hr.ne'
  rw [hrat] at hm
  have hdiff : q*(ξ-(a : ℝ)/q) = q*ξ - (a : ℝ) := by field_simp [hq.ne']
  have habs : q*|ξ-(a : ℝ)/q| = |q*ξ - (a : ℝ)| := by
    rw [← hdiff,abs_mul,abs_of_pos hq]
  have hclose : q*(steps n).len/128 < |q*ξ-(a:ℝ)| := by
    rw [← habs, mul_div_assoc]
    exact mul_lt_mul_of_pos_left hm hq
  have hD : 1 ≤ D := by
    have hpos : 0 < D := by dsimp [D]; positivity
    omega
  have hExp : 2^b = D+D := by
    dsimp [D]
    nth_rw 1 [show b = b-1+1 by omega]
    rw [pow_succ]
    ring
  let v : ℝ := (1/154 : ℝ)^D
  have hv : 0 < v := by dsimp [v]; positivity
  have hv' : v < 1/128 := by
    have ht : (1/154 : ℝ)^D ≤ (1/154 : ℝ)^1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hD
    dsimp [v]
    norm_num at ht ⊢
    linarith
  have hDelta : (154 : ℝ) ^ (-(2^b) : ℤ) = v*v := by
    rw [zpow_neg, show ((2:ℤ)^b) = ((2^b:ℕ):ℤ) by norm_cast, zpow_natCast, hExp,pow_add]
    simp [v,one_div]
  change (154 : ℝ) ^ (-(2^b) : ℤ) < |q*ξ-(a : ℝ)|
  rw [hDelta]
  have hvBound : v*(1/128) ≤ q*(steps n).len/128 := by
    simpa [v,div_eq_mul_inv,one_div] using
      div_le_div_of_nonneg_right hBig (by norm_num : (0:ℝ) ≤ 128)
  exact (mul_lt_mul_of_pos_left hv' hv).trans_le (hvBound.trans hclose.le)

end Temur

namespace Temur

open Prefix GenContFract

def digitMap (a : ℤ) (x : ℝ) := ((a : ℝ)+x)⁻¹

private lemma digitMap_mem {a : ℤ} (ha : 1 ≤ a) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    digitMap a t ∈ Ioo 0 1 := by
  have haR : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have h : 1 < (a : ℝ)+t := by linarith [ht.1]
  exact ⟨inv_pos.mpr (by linarith),inv_lt_one_of_one_lt₀ h⟩

lemma branch_as_digits (e : Bool) {t : ℝ} (ht : 0 ≤ t) :
    (branch e).eval t =
      digitMap 1 (digitMap (if e then 2 else 1) (digitMap 1 (digitMap 1 t))) := by
  have h1 : 0 < 1+t := by linarith
  have h2 : 0 < 1+(1+t)⁻¹ := by positivity
  have h3 : 0 < 1+(1+(1+t)⁻¹)⁻¹ := by positivity
  have h4 : 0 < 2+(1+(1+t)⁻¹)⁻¹ := by positivity
  have h5 : (3*t+5) ≠ 0 := by positivity
  have h6 : (4*t+7) ≠ 0 := by positivity
  cases e <;> norm_num [branch,eval,digitMap] <;>
    field_simp [h1.ne',h2.ne',h3.ne',h4.ne',h5,h6] <;> ring

lemma branch_open (e : Bool) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (branch e).eval t ∈ Ioo 0 1 := by
  have hm := (eval_strict (branch e)).monotoneOn
  have hl : (branch e).eval 0 ≤ (branch e).eval t :=
    hm (by simp : (0:ℝ) ∈ Ici 0) ht.1 ht.1
  have hu : (branch e).eval t ≤ (branch e).eval 1 :=
    hm ht.1 (by norm_num : (1:ℝ) ∈ Ici 0) ht.2
  cases e
  · rw [endpoint₀_false] at hl
    rw [endpoint₁_false] at hu
    exact ⟨by linarith,by linarith⟩
  · rw [endpoint₀_true] at hl
    rw [endpoint₁_true] at hu
    exact ⟨by linarith,by linarith⟩

lemma stream_from_real_digits (ξ : ℝ) (y : ℕ → ℝ) (d : ℕ → ℤ)
    (hy : ∀ n, y n ∈ Ioo 0 1) (h0 : y 0 = ξ)
    (hrecur : ∀ n, y n = digitMap (d n) (y (n+1))) :
    Irrational ξ ∧ ∀ n, Real.partQuot ξ n = d n := by
  have hstep (n : ℕ) : IntFractPair.of ((y n)⁻¹) =
      (⟨d n,y (n+1)⟩ : IntFractPair ℝ) := by
    rw [hrecur n]
    have hrewrite : (digitMap (d n) (y (n+1)))⁻¹ = y (n+1) + (d n : ℝ) := by
      simp [digitMap,add_comm]
    rw [hrewrite]
    have hf : ⌊y (n+1)⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨(hy _).1.le,(hy _).2⟩
    simp [IntFractPair.of,Int.floor_add_intCast,hf,Int.fract_eq_self.mpr
      ⟨(hy _).1.le,(hy _).2⟩]
  have hinit : IntFractPair.stream ξ 0 = some (⟨0,y 0⟩ : IntFractPair ℝ) := by
    rw [IntFractPair.stream_zero,← h0]
    have hf : ⌊y 0⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨(hy _).1.le,(hy _).2⟩
    simp [IntFractPair.of,hf,Int.fract_eq_self.mpr ⟨(hy _).1.le,(hy _).2⟩]
  have hs (n : ℕ) : IntFractPair.stream ξ (n+1) =
      some (⟨d n,y (n+1)⟩ : IntFractPair ℝ) := by
    induction n with
    | zero =>
      rw [IntFractPair.stream_succ_of_some hinit (by exact (hy 0).1.ne'), hstep]
    | succ n ih =>
      rw [IntFractPair.stream_succ_of_some ih (by exact (hy (n+1)).1.ne'), hstep]
  have hden (n : ℕ) : (GenContFract.of ξ).partDens.get? n = some (d n : ℝ) :=
    GenContFract.partDen_eq_s_b (GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream (hs n))
  constructor
  · intro h
    rw [Set.mem_range] at h
    obtain ⟨q,hq⟩ := h
    obtain ⟨n,hn⟩ := (GenContFract.terminates_iff_rat ξ).mpr ⟨q,hq.symm⟩
    have hnone := GenContFract.terminatedAt_iff_partDen_none.mp hn
    rw [hden n] at hnone
    cases hnone
  · intro n
    simp [Real.partQuot,hden]

def bit (n : ℕ) : Bool := chooseBranch (base (n+1)) (steps n)

def digit (k : ℕ) : ℤ := if k%4 = 1 ∧ bit (k/4) then 2 else 1

lemma digit_props (ξ : ℝ) (hξ : ∀ n, ξ ∈ (steps n).cell) :
    Irrational ξ ∧ ∀ n, Real.partQuot ξ n = digit n := by
  classical
  have hpre (n : ℕ) : ∃ t ∈ Icc (0:ℝ) 1, (steps n).eval t = ξ := by
    have h := hξ n
    rw [← cell_image] at h
    exact h
  let t (n : ℕ) := (hpre n).choose
  have ht (n : ℕ) : t n ∈ Icc (0:ℝ) 1 := (hpre n).choose_spec.1
  have hv (n : ℕ) : (steps n).eval (t n) = ξ := (hpre n).choose_spec.2
  have htail (n : ℕ) : t n = (branch (bit n)).eval (t (n+1)) := by
    apply (eval_strict (steps n)).injOn (ht n).1 (branch_mem _ (ht (n+1))).1
    rw [hv]
    calc
      ξ = (steps (n+1)).eval (t (n+1)) := (hv _).symm
      _ = _ := step_eval _ _ (ht (n+1))
  have ht' (n : ℕ) : t n ∈ Ioo (0:ℝ) 1 := by rw [htail n]; exact branch_open _ (ht _)
  let z3 (n : ℕ) := digitMap 1 (t (n+1))
  let z2 (n : ℕ) := digitMap 1 (z3 n)
  let z1 (n : ℕ) := digitMap (if bit n then 2 else 1) (z2 n)
  have hz3 (n : ℕ) : z3 n ∈ Ioo (0:ℝ) 1 := digitMap_mem (by decide) (ht' _)
  have hz2 (n : ℕ) : z2 n ∈ Ioo (0:ℝ) 1 := digitMap_mem (by decide) (hz3 _)
  have hz1 (n : ℕ) : z1 n ∈ Ioo (0:ℝ) 1 := digitMap_mem (by split_ifs <;> decide) (hz2 _)
  let y (k : ℕ) : ℝ :=
    match k%4 with
    | 0 => t (k/4)
    | 1 => z1 (k/4)
    | 2 => z2 (k/4)
    | _ => z3 (k/4)
  have hy (n : ℕ) : y n ∈ Ioo (0:ℝ) 1 := by
    dsimp [y]
    split
    · exact ht' _
    · exact hz1 _
    · exact hz2 _
    · exact hz3 _
  have y0 : y 0 = ξ := by
    change t 0 = ξ
    simpa [steps,root,eval] using hv 0
  have hy0 (n : ℕ) : y (4*n) = t n := by
    simp [y,show (4*n)%4 = 0 by omega,show (4*n)/4 = n by omega]
  have hy1 (n : ℕ) : y (4*n+1) = z1 n := by
    simp [y,show (4*n+1)%4 = 1 by omega,show (4*n+1)/4 = n by omega]
  have hy2 (n : ℕ) : y (4*n+2) = z2 n := by
    simp [y,show (4*n+2)%4 = 2 by omega,show (4*n+2)/4 = n by omega]
  have hy3 (n : ℕ) : y (4*n+3) = z3 n := by
    simp [y,show (4*n+3)%4 = 3 by omega,show (4*n+3)/4 = n by omega]
  refine stream_from_real_digits ξ y digit hy y0 fun n ↦ ?_
  let i := n/4
  have hR : n%4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hrem : n%4
  · have he : n = 4*i := by dsimp [i]; have := Nat.div_add_mod n 4; omega
    rw [he,hy0,hy1]
    have hd : digit (4*i) = 1 := by simp [digit,show (4*i)%4 = 0 by omega]
    rw [hd,htail i,branch_as_digits _ (ht _).1]
  · have he : n = 4*i+1 := by dsimp [i]; have := Nat.div_add_mod n 4; omega
    rw [he,hy1,show 4*i+1+1=4*i+2 by omega,hy2]
    have hd : digit (4*i+1) = if bit i then 2 else 1 := by
      simp [digit,show (4*i+1)%4 = 1 by omega,show (4*i+1)/4 = i by omega]
    rw [hd]
  · have he : n = 4*i+2 := by dsimp [i]; have := Nat.div_add_mod n 4; omega
    rw [he,hy2,show 4*i+2+1=4*i+3 by omega,hy3]
    have hd : digit (4*i+2) = 1 := by simp [digit,show (4*i+2)%4 = 2 by omega]
    rw [hd]
  · have he : n = 4*i+3 := by dsimp [i]; have := Nat.div_add_mod n 4; omega
    rw [he,hy3,show 4*i+3+1=4*(i+1) by omega,hy0]
    have hd : digit (4*i+3) = 1 := by simp [digit,show (4*i+3)%4 = 3 by omega]
    rw [hd]

end Temur

open Filter Set SymbolicDynamics
open scoped Topology ENNReal

noncomputable section

namespace TemurEntropy

lemma alignedComplexity {α β : Type*} [Fintype β] (a : ℕ → α)
    {L : ℕ} (hL : 0 < L) (decode : β → Fin L → α) (v : ℕ → β)
    (hv : ∀ j i, decode (v j) i = a (L*j+i)) (n : ℕ) :
    blockComplexity a n ≤ (L : ℝ≥0∞) * ((Fintype.card β : ℕ) : ℝ≥0∞)^(n/L+2) := by
  let f (p : Fin L × (Fin (n/L+2) → β)) (i : Fin n) :=
    decode (p.2 ⟨(p.1+i)/L, by
      have hr := p.1.isLt
      have hi := i.isLt
      have hd := Nat.add_div_le_div_add_div_add_one (p.1 : ℕ) (i : ℕ) L
      rw [Nat.div_eq_of_lt hr, zero_add] at hd
      have hD : (i : ℕ)/L ≤ n/L := Nat.div_le_div_right hi.le
      omega⟩) ⟨(p.1+i)%L,Nat.mod_lt _ hL⟩
  have hsub : {w : Fin n → α | ∃ k, ∀ i, w i = a (k+i)} ⊆ f '' Set.univ := by
    rintro w ⟨k,hk⟩
    refine ⟨(⟨k%L,Nat.mod_lt _ hL⟩,fun j ↦ v (k/L+j)),Set.mem_univ _,?_⟩
    funext i
    simp only [f,hv,hk]
    congr 1
    rw [Nat.mul_add, add_assoc, Nat.div_add_mod]
    have h := Nat.div_add_mod k L
    omega
  have h := ENat.toENNReal_le.2 ((Set.encard_le_encard hsub).trans (Set.encard_image_le _ _))
  simpa only [blockComplexity, Set.encard_univ, ENat.card_eq_coe_fintype_card, ENat.toENNReal_mul, ENat.toENNReal_pow, ENat.toENNReal_coe,
    Fintype.card_prod,Fintype.card_pi,Fintype.card_fin,Finset.prod_const,Finset.card_univ,
    Nat.cast_mul,Nat.cast_pow] using h

lemma alignedEntropy {α β : Type*} [Fintype β] [Nonempty β] (a : ℕ → α)
    {L : ℕ} (hL : 0 < L) (decode : β → Fin L → α) (v : ℕ → β)
    (hv : ∀ j i, decode (v j) i = a (L*j+i)) :
    blockEntropy a ≤ ((Real.log (Fintype.card β) / (L : ℝ) : ℝ) : EReal) := by
  let K : ℕ := Fintype.card β
  have hK : 0 < K := Fintype.card_pos
  have hKlog : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
  let G (n : ℕ) : ℝ := Real.log K / L + (Real.log L + 2 * Real.log K) / n
  have hLim : Tendsto (fun n ↦ (G n : EReal)) atTop (𝓝 ((Real.log K / (L:ℝ) : ℝ) : EReal)) := by
    apply EReal.tendsto_coe.2
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop
      (Real.log L + 2 * Real.log K)
    simpa [G] using (tendsto_const_nhds.add h :
      Tendsto (fun n : ℕ ↦ Real.log K / L + (Real.log L + 2 * Real.log K) / n) atTop
        (𝓝 (Real.log K / L + 0)))
  unfold blockEntropy
  rw [← hLim.limsup_eq]
  apply limsup_le_limsup (hu := by isBoundedDefault) (hv := by isBoundedDefault)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hLR : 0 < (L:ℝ) := by exact_mod_cast hL
  have hh := ENNReal.log_le_log (alignedComplexity a hL decode v hv n)
  have hlog (m : ℕ) (hm : 0 < m) : (m : ℝ≥0∞).log = (Real.log m : EReal) := by
    rw [show (m : ℝ≥0∞) = ENNReal.ofReal (m : ℝ) by simp,
      ENNReal.log_ofReal_of_pos (by exact_mod_cast hm)]
  change (blockComplexity a n).log ≤ ((L : ℝ≥0∞) * (K : ℝ≥0∞)^(n/L+2)).log at hh
  rw [ENNReal.log_mul_add, ENNReal.log_pow, hlog L hL,hlog K hK,
    ← EReal.coe_coe_eq_natCast (n/L+2), ← EReal.coe_mul, ← EReal.coe_add] at hh
  refine (EReal.div_le_div_right_of_nonneg (by positivity) hh).trans ?_
  rw [← EReal.coe_coe_eq_natCast n, ← EReal.coe_div, EReal.coe_le_coe_iff]
  have hd : ((n/L : ℕ) : ℝ) ≤ (n : ℝ)/L := by
    apply (le_div_iff₀ hLR).mpr
    exact_mod_cast Nat.div_mul_le_self n L
  apply (div_le_iff₀ hnR).mpr
  have hprod := mul_le_mul_of_nonneg_right hd hKlog
  unfold G
  calc
    _ ≤ Real.log L + ((n:ℝ)/L + 2) * Real.log K := by push_cast; linarith
    _ = _ := by field_simp [hnR.ne',hLR.ne']; ring

end TemurEntropy

namespace TemurEntropy

open NormalNumber

lemma zero_block_bounds {b : ℕ} (hb : 2 ≤ b) {ξ : ℝ} (hξ : ξ ∈ Ioo 0 1)
    (k m : ℕ) (h : ∀ i < m, digitSeq b ξ (k+i) = 0) :
    ∃ a : ℤ, |(b : ℝ)^k*ξ - a| < (1/(b : ℝ))^m := by
  let F (i : ℕ) := ⌊(b : ℝ)^i*ξ⌋₊
  have hc : Int.fract ξ = ξ := Int.fract_eq_self.mpr ⟨hξ.1.le,hξ.2⟩
  have hbR : 0 < (b : ℝ) := by positivity
  have hdiv (i : ℕ) : F (i+1) / b = F i := by
    unfold F
    rw [← Nat.floor_div_natCast, pow_succ]
    have he : (b : ℝ)^i*(b : ℝ)*ξ/(b : ℝ) = (b : ℝ)^i*ξ := by
      field_simp
    rw [he]
  have hs (i : ℕ) : F (i+1) = b * F i + digitSeq b ξ i := by
    rw [digitSeq,hc]
    change F (i+1) = b*F i + F (i+1)%b
    rw [← hdiv i, Nat.div_add_mod]
  have hEq (j : ℕ) (hj : j ≤ m) : F (k+j) = b^j*F k := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show k+(j+1)=k+j+1 by omega,hs,h j (by omega),add_zero,ih (by omega),pow_succ]
      ring
  have hLo : (F (k+m) : ℝ) ≤ (b : ℝ)^(k+m)*ξ := Nat.floor_le (mul_nonneg (pow_nonneg hbR.le _) hξ.1.le)
  have hHi : (b : ℝ)^(k+m)*ξ < (F (k+m) : ℝ)+1 := Nat.lt_floor_add_one _
  rw [hEq m le_rfl] at hLo hHi
  push_cast at hLo hHi
  have hBp : 0 < (b:ℝ)^m := pow_pos hbR _
  have hFact : (b:ℝ)^(k+m)*ξ = (b:ℝ)^m*((b:ℝ)^k*ξ) := by rw [pow_add]; ring
  rw [hFact] at hLo hHi
  have hs₀ := le_of_mul_le_mul_left hLo hBp
  have hs₁ : (b:ℝ)^m * ((b:ℝ)^k*ξ - (F k : ℝ)) < 1 := by
    rw [mul_sub]
    linarith only [hHi]
  refine ⟨(F k : ℤ),?_⟩
  push_cast
  rw [abs_of_nonneg (sub_nonneg.mpr hs₀), one_div_pow]
  exact (lt_div_iff₀ hBp).mpr (by rw [mul_comm]; exact hs₁)

lemma baseEntropy_of_avoid {b : ℕ} (hb : 2 ≤ b) {ξ : ℝ} (hξ : ξ ∈ Ioo 0 1)
    {δ : ℝ} (hδ : 0 < δ) (hAvoid : ∀ k (a : ℤ), δ < |(b : ℝ)^k*ξ - a|) :
    Real.baseEntropy b ξ < (Real.log b : EReal) := by
  classical
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (show 1 < b by omega)
  have hbPos : 0 < b := by omega
  have : NeZero b := ⟨by omega⟩
  have hLim : Tendsto (fun n : ℕ ↦ (1/(b:ℝ))^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (one_div_lt_one_div_of_lt zero_lt_one hbR
      |>.trans_eq (one_div_one))
  obtain ⟨m,hm,hmδ⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (hLim.eventually (gt_mem_nhds hδ))).exists
  have hmPos : 0 < m := by omega
  let z : Fin m → Fin b := fun _ ↦ 0
  let B := {w : Fin m → Fin b // w ≠ z}
  let v (n : ℕ) : B := ⟨fun i ↦ ⟨digitSeq b ξ (m*n+i),
    Nat.mod_lt _ hbPos⟩, by
      intro h
      have hh : ∀ i < m, digitSeq b ξ (m*n+i) = 0 := by
        intro i hi
        have he := congrArg (fun f : Fin m → Fin b ↦ (f ⟨i,hi⟩ : ℕ)) h
        simpa [z] using he
      obtain ⟨a,ha⟩ := zero_block_bounds hb hξ (m*n) m hh
      exact (hAvoid (m*n) a).not_ge (ha.trans hmδ).le⟩
  have : Nonempty B := ⟨v 0⟩
  let decode (w : B) (i : Fin m) : ℕ := (w.1 i : ℕ)
  have hRun := alignedEntropy (digitSeq b ξ) hmPos decode v (by intro j i; rfl)
  have hCard : Fintype.card B < b^m := by
    have h := Fintype.card_lt_of_injective_not_surjective (f := fun w : B ↦ w.1)
      Subtype.val_injective (by intro hs; obtain ⟨w,hw⟩ := hs z; exact w.2 hw)
    simpa [Fintype.card_pi] using h
  have hCardPos : 0 < Fintype.card B := Fintype.card_pos
  have hlog : Real.log (Fintype.card B : ℝ) < Real.log ((b:ℝ)^m) :=
    Real.log_lt_log (by exact_mod_cast hCardPos) (by exact_mod_cast hCard)
  rw [Real.log_pow] at hlog
  refine hRun.trans_lt (EReal.coe_lt_coe_iff.mpr ?_)
  apply (div_lt_iff₀ (by positivity : (0:ℝ) < m)).mpr
  simpa [mul_comm] using hlog

end TemurEntropy

namespace Temur

open Prefix TemurEntropy SymbolicDynamics

theorem construction :
    ∃ ξ : ℝ, Irrational ξ ∧ ξ ∈ Ioo (0:ℝ) 1 ∧
      (∀ n : ℕ, Real.partQuot ξ n = 1 ∨ Real.partQuot ξ n = 2) ∧
      (∀ b : ℕ, 2 ≤ b → ∀ k : ℕ,
        (154 : ℝ) ^ (-(2 ^ b) : ℤ) < distToNearestInt ((b : ℝ)^k*ξ)) ∧
      Real.cfEntropy ξ ≤ ((Real.log 2 / 4 : ℝ) : EReal) ∧
      ∀ b : ℕ, 2 ≤ b → Real.baseEntropy b ξ < (Real.log b : EReal) := by
  obtain ⟨ξ,hξ⟩ := exists_intersection
  obtain ⟨hirr,hDigits⟩ := digit_props ξ hξ
  have hI : ξ ∈ Ioo (0:ℝ) 1 := by
    have hx := hξ 1
    rw [← cell_image] at hx
    obtain ⟨t,ht,he⟩ := hx
    have heq : (steps 1).eval t = (branch (bit 0)).eval t := by
      change (root.step (bit 0)).eval t = _
      rw [step_eval _ _ ht]
      simp [root,eval]
    rw [heq] at he
    exact he ▸ branch_open _ ht
  refine ⟨ξ,hirr,hI,?_,?_,?_,?_⟩
  · intro n
    rw [hDigits]
    unfold digit
    split_ifs <;> simp
  · intro b hb k
    exact all_grids ξ hξ b hb k (round ((b:ℝ)^k*ξ))
  · let decode (v : Bool) (i : Fin 4) : ℝ := if (i:ℕ)=1 ∧ v then 2 else 1
    have hf (j : ℕ) (i : Fin 4) : decode (bit j) i = Real.partQuot ξ (4*j+i) := by
      rw [hDigits]
      unfold digit decode
      have h := i.isLt
      rw [show (4*j+(i:ℕ))%4=i by omega,show (4*j+(i:ℕ))/4=j by omega]
      split_ifs <;> norm_num
    have hEntropy := alignedEntropy (Real.partQuot ξ) (by decide : 0 < 4)
      decode bit hf
    simpa [Real.cfEntropy] using hEntropy
  · intro b hb
    exact baseEntropy_of_avoid hb hI (by positivity) (all_grids ξ hξ b hb)

end Temur

theorem OMA.solution : type_of% @Bugeaud53.problem_10_53.variants.temur := Temur.construction