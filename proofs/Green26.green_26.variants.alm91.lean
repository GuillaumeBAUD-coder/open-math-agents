import FormalConjectures.GreensOpenProblems.«26»

/-! Work in the group algebra over the prime field, using finite differences
δ(v) = [v]-1. Every coordinate difference is nilpotent of order p. A
nonzero product of d differences can be witnessed in any chosen basis.
Taking each coordinate occurring in that witness once reduces the remaining
degree by at least d/p, and enlarges support by just one cube. -/

open Finset Filter Asymptotics
open scoped Pointwise
noncomputable section
namespace CubeGrowth
variable {p n : ℕ} [Fact p.Prime]
private abbrev V (p n : ℕ) := Fin n → ZMod p
private abbrev R (p n : ℕ) := AddMonoidAlgebra (ZMod p) (V p n)
private abbrev Aut (p n : ℕ) := V p n ≃ₗ[ZMod p] V p n

private def atom (v : V p n) : R p n := AddMonoidAlgebra.single v 1
private def diff (v : V p n) : R p n := atom v - 1
private def basisVec (φ : Aut p n) (i : Fin n) := φ (Pi.single i 1)

private lemma atom_zero : atom (0 : V p n) = 1 := rfl
private lemma atom_add (u v : V p n) : atom (u+v) = atom u * atom v := by simp [atom]
private lemma nilpotent (v : V p n) : diff v ^ p = 0 := by
  have h : p • v = 0 := by ext i; simp [Pi.smul_apply,nsmul_eq_mul]
  let : CharP (R p n) p := charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p
  simp only [diff,sub_pow_char,atom,AddMonoidAlgebra.single_pow,one_pow,h]
  exact sub_self _

private lemma basis_detects (φ : Aut p n) (f : R p n) (x : V p n) (hx : diff x*f ≠ 0) :
    ∃ i, diff (basisVec φ i)*f ≠ 0 := by
  by_contra! h
  let H : AddSubmonoid (V p n) := {
    carrier := {v | atom v * f = f}
    zero_mem' := by simp [atom_zero]
    add_mem' := fun {u v} hu hv => by
      change atom u*f = f at hu
      change atom v*f = f at hv
      change atom (u+v)*f = f
      rw [atom_add,mul_assoc,hv,hu] }
  have hmem (i : Fin n) : basisVec φ i ∈ H := by
    have := h i
    simpa [H,diff,sub_mul,sub_eq_zero] using this
  let y := φ.symm x
  have heq : ∑ i, (y i).val • basisVec φ i = x := by
    calc
      _ = φ (∑ i, (y i).val • Pi.single i (1 : ZMod p)) := by simp only [map_sum,map_nsmul,basisVec]
      _ = φ y := by
        congr 1
        ext j
        rw [Finset.sum_apply]
        change (∑ i, (y i).val • ((Pi.single i (1 : ZMod p) : V p n) j)) = y j
        simp [Pi.single_apply,nsmul_eq_mul]
      _ = x := φ.apply_symm_apply x
  have hall : x ∈ H := heq ▸ H.sum_mem (fun i _ => H.nsmul_mem (hmem i) _)
  exact hx (by simpa [H,diff,sub_mul,sub_eq_zero] using hall)

private def op (φ : Aut p n) (e : Fin n → ℕ) : R p n := ∏ i, diff (basisVec φ i) ^ e i
private def chain (l : List (V p n)) : R p n := (l.map diff).prod

private lemma op_inc (φ : Aut p n) (e : Fin n → ℕ) (j : Fin n) :
    op φ (fun i => e i + if i=j then 1 else 0) = diff (basisVec φ j) * op φ e := by
  classical
  simp only [op,pow_add,Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  simp [apply_ite]

/-- Replace the directions of a surviving difference by directions from an arbitrary basis. -/
private lemma coord_witness (φ : Aut p n) (l : List (V p n)) (f : R p n)
    (hl : chain l * f ≠ 0) :
    ∃ e : Fin n → ℕ, ∑ i, e i = l.length ∧ op φ e * f ≠ 0 := by
  induction l generalizing f with
  | nil => exact ⟨0,by simp,by simpa [op,chain] using hl⟩
  | cons v l ih =>
    have hh : chain l * (diff v * f) ≠ 0 := by simpa [chain,mul_left_comm,mul_assoc] using hl
    obtain ⟨e,he,ho⟩ := ih (diff v * f) hh
    obtain ⟨j,hj⟩ := basis_detects φ (op φ e * f) v (by simpa [mul_left_comm] using ho)
    refine ⟨fun i => e i + if i=j then 1 else 0,by simp [sum_add_distrib,he],?_⟩
    simpa [op_inc,mul_assoc] using hj

private lemma exp_lt (φ : Aut p n) (e : Fin n → ℕ) (f : R p n) (h : op φ e * f ≠ 0)
    (i : Fin n) : e i < p := by
  by_contra! hi
  have hz : diff (basisVec φ i)^(e i) = 0 := by
    rw [← Nat.add_sub_of_le hi,pow_add,nilpotent,zero_mul]
  have hh : op φ e = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
  exact h (by rw [hh,zero_mul])

private def witness (f : R p n) (d : ℕ) := ∃ l : List (V p n), l.length = d ∧ chain l * f ≠ 0

private lemma length_bound {f : R p n} {d : ℕ} (h : witness f d) : d ≤ n*p := by
  obtain ⟨l,rfl,hl⟩ := h
  obtain ⟨e,he,ho⟩ := coord_witness (LinearEquiv.refl (ZMod p) _) l f hl
  rw [← he]
  calc ∑ i, e i ≤ ∑ _i : Fin n, p := sum_le_sum fun i _ => (exp_lt _ _ _ ho i).le
       _ = _ := by simp

private noncomputable def deg (f : R p n) : ℕ := open Classical in Nat.findGreatest (witness f) (n*p)

private lemma deg_ge {f : R p n} {d : ℕ} (h : witness f d) : d ≤ deg f := by
  classical
  exact Nat.le_findGreatest (length_bound h) h

private lemma deg_witness {f : R p n} (hf : f ≠ 0) : witness f (deg f) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (show witness f 0 from ⟨[],rfl,by simpa [chain]⟩)

/-- Retain one occurrence of each coordinate in a maximal witness. The
remaining possible degree contracts by a factor of at most (p−1)/p. -/
private lemma coord_peel (φ : Aut p n) {f : R p n} (hf : f ≠ 0) :
    ∃ s : Finset (Fin n), let g := (∏ i ∈ s, diff (basisVec φ i))*f
      g ≠ 0 ∧ p * deg g ≤ (p-1) * deg f := by
  classical
  obtain ⟨l,hl,hw⟩ := deg_witness hf
  obtain ⟨e,he,ho⟩ := coord_witness φ l f hw
  let s := univ.filter fun i => 0 < e i
  let g := (∏ i ∈ s, diff (basisVec φ i))*f
  have hfac : op φ e = (∏ i, diff (basisVec φ i)^(e i-1)) * ∏ i ∈ s, diff (basisVec φ i) := by
    rw [op,Finset.prod_filter,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : 0 < e i
    · simp only [if_pos hi,← pow_succ,Nat.sub_add_cancel hi]
    · simp [Nat.eq_zero_of_not_pos hi]
  have hg : g ≠ 0 := by intro h; dsimp [g] at h; rw [hfac,mul_assoc,h,mul_zero] at ho; exact ho rfl
  have hcount : deg f ≤ s.card * p := by
    rw [← hl,← he]
    calc
      _ = ∑ i ∈ s, e i := by simp [s,sum_filter]; apply sum_congr rfl; intro i _; split_ifs <;> omega
      _ ≤ ∑ _i ∈ s, p := sum_le_sum fun i _ => (exp_lt _ _ _ ho i).le
      _ = _ := by simp
  obtain ⟨ls,hls,hs⟩ := deg_witness hg
  have hstep : deg g + s.card ≤ deg f := by
    apply deg_ge
    refine ⟨ls ++ s.toList.map (basisVec φ), by simp [hls], ?_⟩
    simpa [chain,List.map_append,List.prod_append,List.map_map,Finset.prod_toList,mul_assoc,g] using hs
  refine ⟨s,hg,?_⟩
  have hp := (Fact.out : Nat.Prime p).pos
  have h := Nat.mul_le_mul_left p hstep
  have hp' : p-1+1 = p := by omega
  nlinarith [show (p-1+1)*deg f = p*deg f by rw [hp']]


/-- Applying a difference once per selected coordinate shifts support only
by subset sums of those coordinates. -/
private lemma support_step (φ : Aut p n) (f : R p n) (s : Finset (Fin n)) (x : V p n)
    (hx : (((∏ i ∈ s, diff (basisVec φ i))*f).coeff x) ≠ 0) :
    ∃ t ⊆ s, f.coeff (x - ∑ i ∈ t, basisVec φ i) ≠ 0 := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => exact ⟨∅,Finset.Subset.rfl,by simpa using hx⟩
  | @insert i s hi ih =>
    let b := basisVec φ i
    let z := (∏ j ∈ s, diff (basisVec φ j))*f
    rw [Finset.prod_insert hi,mul_assoc] at hx
    change ((diff b*z).coeff x) ≠ 0 at hx
    by_cases h : z.coeff x ≠ 0
    · obtain ⟨t,ht,ht'⟩ := ih x h
      exact ⟨t,ht.trans (subset_insert ..),ht'⟩
    have h' : z.coeff (-b+x) ≠ 0 := by
      intro hh
      exact hx (by simp [diff,sub_mul,atom,not_ne_iff.mp h,hh])
    obtain ⟨t,ht,ht'⟩ := ih _ h'
    refine ⟨insert i t,insert_subset_insert _ ht,?_⟩
    rw [sum_insert (fun hm => hi (ht hm))]
    convert ht' using 2; dsimp [b]; abel

private lemma subset_sum_in_cube (φ : Aut p n) (t : Finset (Fin n)) :
    (∑ i ∈ t, basisVec φ i) ∈ φ '' Green26.StandardCube n := by
  classical
  refine ⟨∑ i ∈ t, Pi.single i (1 : ZMod p),?_,by simp only [map_sum,basisVec]⟩
  intro j
  by_cases h : j ∈ t <;> simp [Finset.sum_apply,Pi.single_apply,h]

private def rate (p : ℕ) : ℝ := 1-1/(p : ℝ)

private lemma rate_nonneg (p : ℕ) [Fact p.Prime] : 0 ≤ rate p := by
  have hp : (1:ℝ) ≤ p := by exact_mod_cast (Fact.out : Nat.Prime p).one_le
  exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hp)

private lemma build {k : ℕ} (A : Fin k → Set (V p n)) (hA : ∀ i, Green26.IsCube (A i)) :
    ∃ f : R p n, f ≠ 0 ∧ (∀ x, f.coeff x ≠ 0 → x ∈ ∑ i, A i) ∧
      (deg f : ℝ) ≤ rate p ^ k * (n*p : ℕ) := by
  classical
  induction k with
  | zero =>
    refine ⟨1,one_ne_zero,?_,?_⟩
    · intro x hx
      by_contra hn
      have hh : x ≠ 0 := by simpa using hn
      exact hx (by simp [AddMonoidAlgebra.one_def,hh])
    · simpa using (show ((deg (1 : R p n)) : ℝ) ≤ ((n*p : ℕ) : ℝ) by
        exact_mod_cast length_bound (deg_witness (one_ne_zero : (1:R p n) ≠ 0)))
  | succ k ih =>
    obtain ⟨f,hf,hfs,hfd⟩ := ih (fun i => A i.succ) (fun i => hA i.succ)
    obtain ⟨φ,hφ⟩ := hA 0
    obtain ⟨s,hg,hd⟩ := coord_peel φ hf
    let g := (∏ i ∈ s, diff (basisVec φ i))*f
    refine ⟨g,hg,?_,?_⟩
    · intro x hx
      obtain ⟨t,ht,hh⟩ := support_step φ f s x hx
      rw [Fin.sum_univ_succ,hφ]
      exact Set.mem_add.mpr ⟨_,subset_sum_in_cube φ t,_,hfs _ hh,by abel⟩
    · have hpp : 1 ≤ p := (Fact.out : p.Prime).one_le
      have hp : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      have hh : (p : ℝ)*(deg g : ℝ) ≤ (p-1 : ℕ)*(deg f : ℝ) := by exact_mod_cast hd
      rw [Nat.cast_sub hpp,Nat.cast_one] at hh
      have hgr : (deg g : ℝ) ≤ rate p * deg f := by
        rw [rate,show 1-1/(p:ℝ) = ((p:ℝ)-1)/p by field_simp]
        rw [div_mul_eq_mul_div,le_div_iff₀ hp]; linarith
      exact hgr.trans (by simpa [pow_succ,mul_left_comm,mul_comm,mul_assoc]
        using mul_le_mul_of_nonneg_left hfd (rate_nonneg p))

private lemma full_of_zero {f : R p n} (hf : f ≠ 0) (hdeg : deg f = 0) :
    ∀ x, f.coeff x ≠ 0 := by
  have hfix (v : V p n) : atom v * f = f := by
    by_contra hn
    have hw : witness f 1 := ⟨[v],rfl,by simpa [chain,diff,sub_mul,sub_eq_zero] using hn⟩
    have := deg_ge hw
    omega
  intro x hx
  apply hf
  ext y
  have hh := congrArg (fun z : R p n => z.coeff y) (hfix (y-x))
  simpa [atom,neg_sub,sub_add_cancel,hx] using hh.symm

private lemma enough {k : ℕ} (A : Fin k → Set (V p n)) (hA : ∀ i, Green26.IsCube (A i))
    (hn : 0 < n) (hk : (p:ℝ)*(Real.log n + Real.log p + 1) ≤ k) :
    ∑ i, A i = Set.univ := by
  obtain ⟨f,hf,hfs,hd⟩ := build A hA
  have hp : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hr : rate p ≤ Real.exp (-(1/(p:ℝ))) := by
    dsimp [rate]; linarith [Real.add_one_le_exp (-(1/(p:ℝ)))]
  have hpow := pow_le_pow_left₀ (rate_nonneg p) hr k
  rw [← Real.exp_nat_mul] at hpow
  have he : (k:ℝ)*(-(1/(p:ℝ))) ≤ -(Real.log n + Real.log p + 1) := by
    field_simp; nlinarith
  have hprod : rate p ^ k * ((n*p:ℕ):ℝ) < 1 := by
    calc
      _ ≤ Real.exp (-(Real.log n + Real.log p + 1)) * ((n*p:ℕ):ℝ) :=
        mul_le_mul_of_nonneg_right (hpow.trans (Real.exp_le_exp.mpr he)) (by positivity)
      _ = (Real.exp 1)⁻¹ := by
        rw [Real.exp_neg,Real.exp_add,Real.exp_add,Real.exp_log hn',Real.exp_log hp]
        push_cast; field_simp
      _ < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_exp_iff.mpr one_pos)
  have hdeg : deg f = 0 := by
    have : (deg f : ℝ) < 1 := hd.trans_lt hprod
    have hh : deg f < 1 := by exact_mod_cast this
    omega
  exact Set.eq_univ_of_forall fun x => hfs x (full_of_zero hf hdeg x)

end CubeGrowth
open CubeGrowth in
theorem OMA.solution : type_of% @Green26.green_26.variants.alm91 := by
  intro p hp
  let k (n : ℕ) := ⌈(p:ℝ)*(Real.log n + Real.log p + 1)⌉₊
  refine ⟨k,?_,?_⟩
  · have hp' : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (Fact.out : p.Prime).one_le)
    refine Asymptotics.IsBigO.of_bound ((p:ℝ)*(2+Real.log p)+1) ?_
    have hl : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    filter_upwards [hl] with n hn
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    have hc := Nat.ceil_lt_add_one (show 0 ≤ (p:ℝ)*(Real.log n + Real.log p + 1) by positivity)
    dsimp [k]
    nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)*(Real.log p + 1) by positivity) (sub_nonneg.mpr hn)]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    intro A hA
    exact enough A hA hn (Nat.le_ceil _)
