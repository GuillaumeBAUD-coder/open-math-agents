import FormalConjectures.ErdosProblems.«1085»
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-! Embed the Turán graph using circles in orthogonal coordinate planes. -/

open scoped EuclideanGeometry Finset Sym2

theorem OMA.lenz_realization (d p n : ℕ) (hp : 0 < p) (hd : 2 * p ≤ d) :
    ∃ v : Fin n ↪ (ℝ^d), ∀ i j : Fin n, (i : ℕ) % p ≠ (j : ℕ) % p → dist (v i) (v j) = 1 := by
  classical
  let a (i : Fin n) : Fin d := ⟨2 * ((i : ℕ) % p), by
    have := Nat.mod_lt (i : ℕ) hp
    omega⟩
  let b (i : Fin n) : Fin d := ⟨2 * ((i : ℕ) % p) + 1, by
    have := Nat.mod_lt (i : ℕ) hp
    omega⟩
  have hab (i j : Fin n) : a i ≠ b j := by
    intro h
    have hval := congrArg Fin.val h
    change 2 * ((i : ℕ) % p) = 2 * ((j : ℕ) % p) + 1 at hval
    omega
  have ha (i j : Fin n) : a i = a j ↔ (i : ℕ) % p = (j : ℕ) % p := by
    rw [← Fin.val_inj]
    change 2 * ((i : ℕ) % p) = 2 * ((j : ℕ) % p) ↔ _
    omega
  have hb (i j : Fin n) : b i = b j ↔ (i : ℕ) % p = (j : ℕ) % p := by
    rw [← Fin.val_inj]
    change 2 * ((i : ℕ) % p) + 1 = 2 * ((j : ℕ) % p) + 1 ↔ _
    omega
  let x (i : Fin n) : ℝ := 1 / ((i.val : ℝ) + 4)
  let y (i : Fin n) : ℝ := Real.sqrt (1 / 2 - x i ^ 2)
  have hx (i : Fin n) : 0 < x i := by
    dsimp [x]
    positivity
  have hxy (i : Fin n) : x i ^ 2 + y i ^ 2 = 1 / 2 := by
    have hbound : x i ≤ 1 / 4 := by
      have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      dsimp [x]
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    have hrad : 0 ≤ 1 / 2 - x i ^ 2 := by nlinarith [hx i]
    dsimp [y]
    rw [Real.sq_sqrt hrad]
    ring
  let v (i : Fin n) : ℝ^d :=
    WithLp.toLp 2 (fun c => if c = a i then x i else if c = b i then y i else 0)
  have hv (i : Fin n) (c : Fin d) :
      v i c = if c = a i then x i else if c = b i then y i else 0 := rfl
  have hnorm (i : Fin n) : (∑ c, (v i c) ^ 2) = 1 / 2 := by
    have hterm (c : Fin d) :
        (v i c) ^ 2 = (if c = a i then x i ^ 2 else 0) + (if c = b i then y i ^ 2 else 0) := by
      rw [hv]
      by_cases h : c = a i
      · subst c
        simp [hab]
      · by_cases h' : c = b i <;> simp [h, h', (hab i i).symm]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simpa using hxy i
  have hinj : Function.Injective v := by
    intro i j hij
    have hcoord : v i (a i) = v j (a i) := congrArg (fun z : ℝ^d => z (a i)) hij
    rw [hv, hv, if_pos rfl] at hcoord
    by_cases h : a i = a j
    · rw [if_pos h] at hcoord
      have hval : (i.val : ℝ) + 4 = (j.val : ℝ) + 4 := by
        have hc : (1 : ℝ) / ((i.val : ℝ) + 4) = 1 / ((j.val : ℝ) + 4) := hcoord
        have hm := (div_eq_div_iff (by positivity) (by positivity)).mp hc
        simpa only [one_mul] using hm.symm
      apply Fin.ext
      exact_mod_cast (add_right_cancel hval)
    · rw [if_neg h, if_neg (hab i j)] at hcoord
      exact (ne_of_gt (hx i) hcoord).elim
  refine ⟨⟨v, hinj⟩, fun i j h => ?_⟩
  change dist (v i) (v j) = 1
  have hterm (c : Fin d) : (v i c - v j c) ^ 2 = (v i c) ^ 2 + (v j c) ^ 2 := by
    by_cases hci : c = a i
    · subst c
      have hzero : v j (a i) = 0 := by
        simp [hv, (ha i j).not.mpr h, hab]
      rw [hzero]
      ring
    · by_cases hci' : c = b i
      · subst c
        have hzero : v j (b i) = 0 := by
          simp [hv, (hab j i).symm, (hb i j).not.mpr h]
        rw [hzero]
        ring
      · have hzero : v i c = 0 := by simp [hv, hci, hci']
        rw [hzero]
        ring
  have hsq : dist (v i) (v j) ^ 2 = 1 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp_rw [PiLp.sub_apply, hterm]
    rw [Finset.sum_add_distrib, hnorm i, hnorm j]
    norm_num
  nlinarith [dist_nonneg (x := v i) (y := v j)]

theorem OMA.lenz_turan_le (d p n : ℕ) (hp : 0 < p) (hd : 2 * p ≤ d) :
    (SimpleGraph.turanGraph n p).edgeFinset.card ≤ Erdos1085.f d n := by
  classical
  obtain ⟨v, hv⟩ := OMA.lenz_realization d p n hp hd
  let S : Finset (ℝ^d) := Finset.univ.map v
  have hS : S.card = n := by simp [S]
  have hedge : (SimpleGraph.turanGraph n p).edgeFinset.card ≤ unitDistNum S := by
    unfold unitDistNum
    apply Finset.card_le_card_of_injOn (Sym2.map v)
    · intro e he
      induction e using Sym2.inductionOn with
      | _ i j =>
        have hij : (i : ℕ) % p ≠ (j : ℕ) % p :=
          SimpleGraph.turanGraph_adj.mp ((SimpleGraph.mem_edgeSet (G := SimpleGraph.turanGraph n p)).mp
            ((SimpleGraph.mem_edgeFinset (G := SimpleGraph.turanGraph n p)).mp he))
        have hi : v i ∈ S := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
        have hj : v j ∈ S := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
        change s(v i, v j) ∈ _
        refine Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr ⟨hi, hj⟩, ?_⟩
        have hout := Quot.out_eq s(v i, v j)
        change s((Quot.out s(v i, v j)).1, (Quot.out s(v i, v j)).2) = s(v i, v j) at hout
        rcases Sym2.eq_iff.mp hout with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · rw [h₁, h₂]
          exact hv i j hij
        · rw [h₁, h₂, dist_comm]
          exact hv i j hij
    · exact (Sym2.map.injective v.injective).injOn
  refine hedge.trans ?_
  unfold Erdos1085.f
  refine le_ciSup₂ (f := fun (T : Finset (ℝ^d)) (_ : T.card = n) => unitDistNum T) ?_ S hS
  refine ⟨n.choose 2, ?_⟩
  intro k hk
  rcases Set.mem_iUnion.mp hk with ⟨T, hT⟩
  obtain ⟨hcard, rfl⟩ := Set.mem_range.mp hT
  simpa only [hcard] using unitDistNum_le_choose_two T

theorem OMA.lenz_turan_bound (n p : ℕ) (hp : 0 < p) :
    ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) * (n : ℝ) ^ 2 - ((p : ℝ) ^ 2 + 1) ≤
      ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) := by
  let r := n % p
  let A := (n ^ 2 - r ^ 2) * (p - 1)
  let B := 2 * p
  have hB : 0 < B := by dsimp [B]; omega
  have hrn : r ≤ n := Nat.mod_le _ _
  have hrp : r ≤ p := (Nat.mod_lt _ hp).le
  have hsub : r ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hrn _
  have hfloor : A < (A / B + 1) * B := by
    apply (Nat.div_lt_iff_lt_mul hB).mp
    omega
  have hfloorR : (A : ℝ) < ((A / B : ℕ) + (1 : ℝ)) * (B : ℝ) := by
    exact_mod_cast hfloor
  have hdiv : (A : ℝ) / (B : ℝ) - 1 ≤ ((A / B : ℕ) : ℝ) := by
    have hBR : (0 : ℝ) < B := by exact_mod_cast hB
    linarith [(div_lt_iff₀ hBR).mpr hfloorR]
  have hAr : (A : ℝ) = ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) * ((p - 1 : ℕ) : ℝ) := by
    simp only [A, Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_pow]
  have hBr : (B : ℝ) = 2 * (p : ℝ) := by simp [B]
  have hcoef : ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) ≤ 1 := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have h : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsquares : (r : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hrp 2
  have herror :
      ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) * (r : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
    calc
      _ ≤ 1 * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hsquares
  rw [hAr, hBr, sub_mul, sub_div] at hdiv
  rw [SimpleGraph.card_edgeFinset_turanGraph]
  change _ ≤ ((A / B + r.choose 2 : ℕ) : ℝ)
  push_cast
  rw [mul_div_assoc, mul_comm ((n : ℝ) ^ 2), mul_div_assoc, mul_comm ((r : ℝ) ^ 2)] at hdiv
  linarith [Nat.cast_nonneg (α := ℝ) (r.choose 2)]

theorem OMA.solution : type_of% @Erdos1085.erdos_1085.variants.lower_d4_lenz := by
  intro d hd
  let p := d / 2
  have hp : 0 < p := by dsimp [p]; omega
  have hpd : 2 * p ≤ d := by dsimp [p]; omega
  refine ⟨(p : ℝ) ^ 2 + 1, fun n => ?_⟩
  exact (OMA.lenz_turan_bound n p hp).trans (by exact_mod_cast OMA.lenz_turan_le d p n hp hpd)