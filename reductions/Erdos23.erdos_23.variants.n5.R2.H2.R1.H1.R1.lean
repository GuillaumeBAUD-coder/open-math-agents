import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H2_R1

/-!
# Structural reduction for the 22-vertex triangle-free bipartization bound

Every triangle-free graph on 22 vertices admits a 2-coloring with at most 17 monochromatic edges
(ordered sum `≤ 34`). We prove all elementary and extremal regimes directly:
* Passing to a maximal triangle-free supergraph supported on `W`;
* Minimum degree `≤ 3`: deleting a low-degree vertex reduces to the 21-vertex bound `H1` (`≤ 32`)
  plus at most `2 * (3 / 2) = 2` via `extend_color`;
* Minimum degree `≥ 9`: Andrásfai–Erdős–Sós (`9 * 5 > 2 * 22`) forces bipartiteness (`cost = 0`);
* Maximum degree `≥ 13`: the neighborhood cut leaves a triangle-free remainder on at most `8`
  vertices, which by Mantel has at most `32` ordered edges;
* High density (`S ≥ 198`, i.e. `m ≥ 99`): averaging the 22 neighborhood cuts with Cauchy–Schwarz
  gives a cut `≤ 34`, with the 9-regular equality case `S = 198` settled by Andrásfai–Erdős–Sós;
* Low density (`S ≤ 84`, i.e. `m ≤ 42`): extending the proper 2-coloring on `N(u) ∪ N(v)` for a
  maximum-degree-sum edge `uv` via greedy `extend_color` gives `cost ≤ 34`;
* `C₅`-homomorphic graphs: among five part sizes summing to `22`, some adjacent pair has product
  at most `16`, giving ordered cut at most `32`.

The remaining residual maximal triangle-free graphs on 22 vertices have `4 ≤ δ ≤ 8`, `Δ ≤ 12`,
`86 ≤ S ≤ 196`, are not homomorphic to `C₅`, and fail every neighborhood cut; they are split by
edge count into `H2` (`86 ≤ S ≤ 140`) and `H3` (`142 ≤ S ≤ 196`).
-/

-- Credit: @lettucrisp

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1_H1_R1

open Finset SimpleGraph
open OMA.R_Erdos23_erdos_23_variants_n5_R2 (erase_total extend_color)
open OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1 (unordered)
open scoped Classical

/-- Order-21 triangle-free bipartization bound (`a(21) ≤ 16`, ordered sum `≤ 32`). -/
def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 → ∀ U : Finset (Fin 25),
    U.card = 21 → ∃ c : Fin 25 → Bool,
      (∑ i ∈ U, ∑ j ∈ U, if G.Adj i j ∧ c i = c j then 1 else 0) ≤ (32 : ℕ)

/-- Residual maximal triangle-free 22-vertex graphs with `43 ≤ m ≤ 70` (`86 ≤ S ≤ 140`). -/
def H2 : Prop :=
  ∀ (W : Finset (Fin 25)), W.card = 22 → ∀ K : SimpleGraph (Fin 25),
    K.CliqueFree 3 → (∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W) →
    (∀ H : SimpleGraph (Fin 25), K ≤ H → H.CliqueFree 3 →
      (∀ i j, H.Adj i j → i ∈ W ∧ j ∈ W) → H = K) →
    86 ≤ (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0) →
    (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0) ≤ 140 →
    (∀ i ∈ W, 4 ≤ (W.filter (K.Adj i)).card) →
    (∀ i ∈ W, (W.filter (K.Adj i)).card ≤ 12) →
    (∃ i ∈ W, (W.filter (K.Adj i)).card ≤ 8) →
    (¬ ∃ f : Fin 25 → Fin 5, ∀ i ∈ W, ∀ j ∈ W, K.Adj i j → f i + 1 = f j ∨ f j + 1 = f i) →
    (∀ v ∈ W, (36 : ℕ) ≤ ∑ i ∈ W, ∑ j ∈ W,
      if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0) →
    ∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) ≤ (34 : ℕ)

/-- Residual maximal triangle-free 22-vertex graphs with `71 ≤ m ≤ 98` (`142 ≤ S ≤ 196`). -/
def H3 : Prop :=
  ∀ (W : Finset (Fin 25)), W.card = 22 → ∀ K : SimpleGraph (Fin 25),
    K.CliqueFree 3 → (∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W) →
    (∀ H : SimpleGraph (Fin 25), K ≤ H → H.CliqueFree 3 →
      (∀ i j, H.Adj i j → i ∈ W ∧ j ∈ W) → H = K) →
    142 ≤ (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0) →
    (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0) ≤ 196 →
    (∀ i ∈ W, 4 ≤ (W.filter (K.Adj i)).card) →
    (∀ i ∈ W, (W.filter (K.Adj i)).card ≤ 12) →
    (∃ i ∈ W, (W.filter (K.Adj i)).card ≤ 8) →
    (¬ ∃ f : Fin 25 → Fin 5, ∀ i ∈ W, ∀ j ∈ W, K.Adj i j → f i + 1 = f j ∨ f j + 1 = f i) →
    (∀ v ∈ W, (36 : ℕ) ≤ ∑ i ∈ W, ∑ j ∈ W,
      if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0) →
    ∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) ≤ (34 : ℕ)

lemma not_triangle {K : SimpleGraph (Fin 25)} (hcf : K.CliqueFree 3)
    {a b c : Fin 25} (hab : K.Adj a b) (hbc : K.Adj b c) (hca : K.Adj c a) : False := by
  have hne1 : a ≠ b := K.ne_of_adj hab
  have hne2 : b ≠ c := K.ne_of_adj hbc
  have hne3 : c ≠ a := K.ne_of_adj hca
  have hcl : K.IsNClique 3 ({a, b, c} : Finset (Fin 25)) := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [mem_coe, mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact absurd rfl hxy
      · exact hab
      · exact hca.symm
      · exact hab.symm
      · exact absurd rfl hxy
      · exact hbc
      · exact hca
      · exact hbc.symm
      · exact absurd rfl hxy
    · rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp [hne2]
      · simp [hne1, hne3.symm]
  exact hcf {a, b, c} hcl

lemma sq_sum_le {V : Type*} (S : Finset V) (f : V → ℕ) :
    (∑ x ∈ S, f x) ^ 2 ≤ S.card * ∑ x ∈ S, f x ^ 2 := by
  have h : (∑ x ∈ S, ∑ y ∈ S, (f x ^ 2 + f y ^ 2)) ≥ 2 * (∑ x ∈ S, f x) ^ 2 := by
    have hpair : ∀ x ∈ S, ∀ y ∈ S, 2 * (f x * f y) ≤ f x ^ 2 + f y ^ 2 := by
      intro x _ y _
      zify
      nlinarith [sq_nonneg ((f x : ℤ) - (f y : ℤ))]
    calc
      2 * (∑ x ∈ S, f x) ^ 2 = 2 * ∑ x ∈ S, ∑ y ∈ S, f x * f y := by
        rw [sq, sum_mul_sum]
      _ = ∑ x ∈ S, ∑ y ∈ S, 2 * (f x * f y) := by
        rw [mul_sum]
        exact sum_congr rfl fun x _ => mul_sum ..
      _ ≤ ∑ x ∈ S, ∑ y ∈ S, (f x ^ 2 + f y ^ 2) :=
        sum_le_sum fun x hx => sum_le_sum fun y hy => hpair x hx y hy
  have hsum : (∑ x ∈ S, ∑ y ∈ S, (f x ^ 2 + f y ^ 2)) = 2 * (S.card * ∑ x ∈ S, f x ^ 2) := by
    simp only [sum_add_distrib, sum_const, smul_eq_mul]
    rw [← mul_sum]
    ring
  omega

lemma sq_sum_strict_of_ne_const {V : Type*} (S : Finset V) (f : V → ℕ) (c : ℕ)
    (havg : ∑ x ∈ S, f x = S.card * c) (hne : ∃ x ∈ S, f x ≠ c) :
    S.card * c ^ 2 < ∑ x ∈ S, f x ^ 2 := by
  have hZ : ∑ x ∈ S, ((f x : ℤ) - (c : ℤ)) ^ 2 > 0 := by
    obtain ⟨x₀, hx₀, hne₀⟩ := hne
    have hpos : (0 : ℤ) < ((f x₀ : ℤ) - (c : ℤ)) ^ 2 := by
      have : (f x₀ : ℤ) - (c : ℤ) ≠ 0 := by omega
      positivity
    have hle : ((f x₀ : ℤ) - (c : ℤ)) ^ 2 ≤ ∑ x ∈ S, ((f x : ℤ) - (c : ℤ)) ^ 2 :=
      single_le_sum (fun x _ => sq_nonneg ((f x : ℤ) - (c : ℤ))) hx₀
    linarith
  have hexp : ∑ x ∈ S, ((f x : ℤ) - (c : ℤ)) ^ 2 =
      (∑ x ∈ S, (f x : ℤ) ^ 2) - 2 * (c : ℤ) * (∑ x ∈ S, (f x : ℤ)) + (S.card : ℤ) * (c : ℤ) ^ 2 := by
    have : ∀ x ∈ S, ((f x : ℤ) - (c : ℤ)) ^ 2 = (f x : ℤ) ^ 2 - 2 * (c : ℤ) * (f x : ℤ) + (c : ℤ) ^ 2 := by
      intro x _; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  have havgZ : (∑ x ∈ S, (f x : ℤ)) = (S.card : ℤ) * (c : ℤ) := by exact_mod_cast havg
  have hgoalZ : (S.card : ℤ) * (c : ℤ) ^ 2 < ∑ x ∈ S, (f x : ℤ) ^ 2 := by nlinarith
  exact_mod_cast hgoalZ

lemma mantel_ordered (K : SimpleGraph (Fin 25)) (hcf : K.CliqueFree 3) (R : Finset (Fin 25)) :
    2 * (∑ i ∈ R, ∑ j ∈ R, if K.Adj i j then 1 else 0) ≤ R.card ^ 2 := by
  let d (i : Fin 25) := (R.filter (K.Adj i)).card
  let E := ∑ i ∈ R, ∑ j ∈ R, if K.Adj i j then 1 else 0
  have hd : ∀ i ∈ R, d i = ∑ j ∈ R, if K.Adj i j then 1 else 0 := by
    intro i _; dsimp [d]; rw [card_filter]
  have hE : E = ∑ i ∈ R, d i := sum_congr rfl fun i hi => (hd i hi).symm
  have hadj_sum : ∀ i ∈ R, ∀ j ∈ R, K.Adj i j → d i + d j ≤ R.card := by
    intro i _ j _ hij
    have hdisj : Disjoint (R.filter (K.Adj i)) (R.filter (K.Adj j)) := by
      rw [Finset.disjoint_left]
      intro z hzi hzj
      exact not_triangle hcf hij (mem_filter.mp hzj).2 (mem_filter.mp hzi).2.symm
    have hsub : R.filter (K.Adj i) ∪ R.filter (K.Adj j) ⊆ R :=
      union_subset (filter_subset _ _) (filter_subset _ _)
    calc d i + d j = (R.filter (K.Adj i) ∪ R.filter (K.Adj j)).card :=
            (card_union_of_disjoint hdisj).symm
         _ ≤ R.card := card_le_card hsub
  have hdouble : 2 * ∑ i ∈ R, d i ^ 2 ≤ R.card * E := by
    have h1 : ∑ i ∈ R, ∑ j ∈ R, (if K.Adj i j then d i + d j else 0) ≤ R.card * E := by
      calc ∑ i ∈ R, ∑ j ∈ R, (if K.Adj i j then d i + d j else 0)
          ≤ ∑ i ∈ R, ∑ j ∈ R, (if K.Adj i j then R.card else 0) := by
              refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
              split_ifs with h
              · exact hadj_sum i hi j hj h
              · exact le_rfl
        _ = R.card * E := by
              dsimp [E]; rw [mul_sum]
              refine sum_congr rfl fun i _ => ?_
              rw [mul_sum]
              refine sum_congr rfl fun j _ => ?_
              split_ifs <;> simp
    have h2 : ∑ i ∈ R, ∑ j ∈ R, (if K.Adj i j then d i + d j else 0) = 2 * ∑ i ∈ R, d i ^ 2 := by
      have hsplit : ∀ i ∈ R, ∑ j ∈ R, (if K.Adj i j then d i + d j else 0) =
          (∑ j ∈ R, if K.Adj i j then d i else 0) + (∑ j ∈ R, if K.Adj i j then d j else 0) := by
        intro i _; rw [← sum_add_distrib]
        exact sum_congr rfl fun j _ => by split_ifs <;> omega
      rw [sum_congr rfl hsplit, sum_add_distrib]
      have hleft : (∑ i ∈ R, ∑ j ∈ R, if K.Adj i j then d i else 0) = ∑ i ∈ R, d i ^ 2 := by
        refine sum_congr rfl fun i hi => ?_
        calc (∑ j ∈ R, if K.Adj i j then d i else 0)
            = d i * (∑ j ∈ R, if K.Adj i j then 1 else 0) := by
                rw [mul_sum]; exact sum_congr rfl fun j _ => by split_ifs <;> simp
          _ = d i ^ 2 := by rw [← hd i hi, sq]
      have hright : (∑ i ∈ R, ∑ j ∈ R, if K.Adj i j then d j else 0) = ∑ j ∈ R, d j ^ 2 := by
        rw [sum_comm]
        refine sum_congr rfl fun j hj => ?_
        calc (∑ i ∈ R, if K.Adj i j then d j else 0)
            = d j * (∑ i ∈ R, if K.Adj j i then 1 else 0) := by
                rw [mul_sum]
                exact sum_congr rfl fun i _ => by rw [K.adj_comm]; split_ifs <;> simp
          _ = d j ^ 2 := by rw [← hd j hj, sq]
      rw [hleft, hright]; omega
    omega
  have hcs := sq_sum_le R d
  rw [← hE] at hcs
  change 2 * E ≤ R.card ^ 2
  by_cases hE0 : E = 0
  · rw [hE0]; exact Nat.zero_le _
  · have hmul : 2 * E ^ 2 ≤ R.card ^ 2 * E := by
      calc 2 * E ^ 2 ≤ 2 * (R.card * ∑ i ∈ R, d i ^ 2) := Nat.mul_le_mul_left 2 hcs
        _ = R.card * (2 * ∑ i ∈ R, d i ^ 2) := by ring
        _ ≤ R.card * (R.card * E) := Nat.mul_le_mul_left R.card hdouble
        _ = R.card ^ 2 * E := by ring
    have hEpos : 0 < E := Nat.pos_of_ne_zero hE0
    have : 2 * E * E ≤ R.card ^ 2 * E := by nlinarith
    exact Nat.le_of_mul_le_mul_right this hEpos

lemma nbhd_cut_eq (W : Finset (Fin 25)) (K : SimpleGraph (Fin 25)) (hcf : K.CliqueFree 3)
    (v : Fin 25) :
    (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0) =
      ∑ i ∈ W.filter (fun x => ¬ K.Adj v x), ∑ j ∈ W.filter (fun x => ¬ K.Adj v x),
        if K.Adj i j then 1 else 0 := by
  have hno : ∀ i ∈ W, ∀ j ∈ W, K.Adj i j → K.Adj v i → K.Adj v j → False :=
    fun i _ j _ hij hvi hvj => not_triangle hcf hij hvj.symm hvi
  simp only [sum_filter]
  refine sum_congr rfl fun i hi => ?_
  by_cases hvi : K.Adj v i
  · rw [if_neg (not_not.mpr hvi)]
    refine sum_eq_zero fun j hj => ?_
    by_cases hij : K.Adj i j
    · by_cases hvj : K.Adj v j
      · exact absurd (hno i hi j hj hij hvi hvj) id
      · simp [hij, hvi, hvj]
    · simp [hij]
  · rw [if_pos hvi]
    refine sum_congr rfl fun j _ => ?_
    by_cases hij : K.Adj i j <;> by_cases hvj : K.Adj v j <;> simp [hij, hvi, hvj]

lemma nbhd_cut_highdeg (W : Finset (Fin 25)) (hW : W.card = 22)
    (K : SimpleGraph (Fin 25)) (hcf : K.CliqueFree 3)
    {v : Fin 25} (hv : v ∈ W) (hdeg : 13 ≤ (W.filter (K.Adj v)).card) :
    ∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) ≤ 34 := by
  let c : Fin 25 → Bool := fun x => decide (K.Adj v x)
  refine ⟨c, ?_⟩
  have heq : (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) =
      ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0 := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp [c]
  rw [heq, nbhd_cut_eq W K hcf v]
  let R := (W.filter (fun x => ¬ K.Adj v x)).erase v
  have hvmem : v ∈ W.filter (fun x => ¬ K.Adj v x) := mem_filter.mpr ⟨hv, K.loopless.irrefl v⟩
  have hsumR : (∑ i ∈ W.filter (fun x => ¬ K.Adj v x), ∑ j ∈ W.filter (fun x => ¬ K.Adj v x),
      if K.Adj i j then 1 else 0) = ∑ i ∈ R, ∑ j ∈ R, if K.Adj i j then 1 else 0 := by
    have her := erase_total (W.filter (fun x => ¬ K.Adj v x)) hvmem
      (fun i j => if K.Adj i j then 1 else 0)
      (fun i j => by simp only [K.adj_comm])
      (by simp)
    have hzero : (∑ j ∈ R, if K.Adj v j then 1 else 0) = 0 := by
      refine sum_eq_zero fun j hj => ?_
      have hnj : ¬ K.Adj v j := (mem_filter.mp (mem_erase.mp hj).2).2
      simp [hnj]
    change _ = (∑ i ∈ R, ∑ j ∈ R, if K.Adj i j then 1 else 0) + 2 * (∑ j ∈ R, if K.Adj v j then 1 else 0) at her
    omega
  rw [hsumR]
  have hpart : (W.filter (K.Adj v)).card + (W.filter (fun x => ¬ K.Adj v x)).card = W.card := by
    rw [card_filter, card_filter, ← sum_add_distrib]
    calc (∑ x ∈ W, ((if K.Adj v x then 1 else 0) + (if ¬ K.Adj v x then 1 else 0)))
        = ∑ _x ∈ W, 1 := sum_congr rfl fun x _ => by by_cases h : K.Adj v x <;> simp [h]
      _ = W.card := by simp
  have hRcard : R.card ≤ 8 := by
    rw [card_erase_of_mem hvmem]
    omega
  have hmantel := mantel_ordered K hcf R
  have hsq : R.card ^ 2 ≤ 64 := by nlinarith
  omega

lemma nbhd_cut_identity (W : Finset (Fin 25)) (K : SimpleGraph (Fin 25)) (hcf : K.CliqueFree 3)
    (v : Fin 25) :
    (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0) +
      2 * (∑ u ∈ W, if K.Adj v u then (W.filter (K.Adj u)).card else 0) =
      ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0 := by
  have hno : ∀ i ∈ W, ∀ j ∈ W, K.Adj i j → K.Adj v i → K.Adj v j → False :=
    fun i _ j _ hij hvi hvj => not_triangle hcf hij hvj.symm hvi
  have hterm : ∀ u ∈ W, (if K.Adj v u then (W.filter (K.Adj u)).card else 0) =
      ∑ j ∈ W, if K.Adj u j ∧ K.Adj v u then 1 else 0 := by
    intro u _
    by_cases hvu : K.Adj v u
    · rw [if_pos hvu, card_filter]
      exact sum_congr rfl fun j _ => by simp [hvu]
    · simp [hvu]
  rw [sum_congr rfl hterm]
  have hswap : (∑ u ∈ W, ∑ j ∈ W, if K.Adj u j ∧ K.Adj v u then 1 else 0) =
      ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ K.Adj v j then 1 else 0 := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp only [K.adj_comm]
  have h2 : 2 * (∑ u ∈ W, ∑ j ∈ W, if K.Adj u j ∧ K.Adj v u then 1 else 0) =
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ K.Adj v i then 1 else 0) +
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ K.Adj v j then 1 else 0) := by
    rw [two_mul, ← hswap]
  rw [h2, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  by_cases hij : K.Adj i j
  · by_cases hvi : K.Adj v i <;> by_cases hvj : K.Adj v j
    · exact absurd (hno i hi j hj hij hvi hvj) id
    · simp [hij, hvi, hvj]
    · simp [hij, hvi, hvj]
    · simp [hij, hvi, hvj]
  · simp [hij]

lemma sum_nbhd_cuts (W : Finset (Fin 25)) (K : SimpleGraph (Fin 25)) (hcf : K.CliqueFree 3) :
    (∑ v ∈ W, ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0) +
      2 * (∑ u ∈ W, (W.filter (K.Adj u)).card ^ 2) =
      W.card * (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0) := by
  have hsum := sum_congr rfl fun v (_ : v ∈ W) => nbhd_cut_identity W K hcf v
  rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul] at hsum
  have hdeg2 : (∑ v ∈ W, ∑ u ∈ W, if K.Adj v u then (W.filter (K.Adj u)).card else 0) =
      ∑ u ∈ W, (W.filter (K.Adj u)).card ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    calc (∑ v ∈ W, if K.Adj v u then (W.filter (K.Adj u)).card else 0)
        = (W.filter (K.Adj u)).card * (∑ v ∈ W, if K.Adj u v then 1 else 0) := by
            rw [mul_sum]
            exact sum_congr rfl fun v _ => by rw [K.adj_comm]; split_ifs <;> simp
      _ = (W.filter (K.Adj u)).card ^ 2 := by rw [← card_filter, sq]
  rw [hdeg2] at hsum
  exact hsum

lemma even_reach_bipartite (K : SimpleGraph (Fin 25))
    (hno : ∀ L : ℕ, (hL : Odd L) → ∀ f : Fin L → Fin 25,
      ¬ ∀ i : Fin L, K.Adj (f i) (f ⟨(i.val + 1) % L, Nat.mod_lt _ hL.pos⟩)) :
    ∃ c : Fin 25 → Bool, ∀ i j : Fin 25, K.Adj i j → c i ≠ c j := by
  let WalkLen (x y : Fin 25) (k : ℕ) : Prop :=
    ∃ p : Fin (k + 1) → Fin 25, p 0 = x ∧ p ⟨k, Nat.lt_succ_self k⟩ = y ∧
      ∀ i : Fin k, K.Adj (p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
  have w_refl (x : Fin 25) : WalkLen x x 0 :=
    ⟨fun _ => x, rfl, rfl, fun i => Fin.elim0 i⟩
  have w_symm {x y : Fin 25} {k : ℕ} (h : WalkLen x y k) : WalkLen y x k := by
    obtain ⟨p, hp0, hpk, hadj⟩ := h
    refine ⟨fun i => p ⟨k - i.val, by omega⟩, ?_, ?_, ?_⟩
    · simp [hpk]
    · simp [hp0]
    · intro i
      have hlt : k - (i.val + 1) < k := by omega
      have hstep := hadj ⟨k - (i.val + 1), hlt⟩
      have heq1 : (⟨k - (i.val + 1) + 1, Nat.succ_lt_succ hlt⟩ : Fin (k + 1)) =
          ⟨k - i.val, by omega⟩ := by ext; simp; omega
      rw [heq1] at hstep
      exact hstep.symm
  have w_trans {x y z : Fin 25} {k₁ k₂ : ℕ} (h₁ : WalkLen x y k₁) (h₂ : WalkLen y z k₂) :
      WalkLen x z (k₁ + k₂) := by
    obtain ⟨p₁, hp10, hp1k, hadj1⟩ := h₁
    obtain ⟨p₂, hp20, hp2k, hadj2⟩ := h₂
    refine ⟨fun i => if h : i.val ≤ k₁ then p₁ ⟨i.val, by omega⟩ else p₂ ⟨i.val - k₁, by omega⟩,
      ?_, ?_, ?_⟩
    · simp [hp10]
    · by_cases hk2 : k₂ = 0
      · subst hk2
        have hxy : y = z := hp20.symm.trans hp2k
        simp [hp1k, hxy]
      · have : ¬ (k₁ + k₂ ≤ k₁) := by omega
        simp [this, hp2k]
    · intro i
      by_cases h1 : i.val + 1 ≤ k₁
      · have h0 : i.val ≤ k₁ := by omega
        simp only [h0, h1, ↓reduceDIte]
        exact hadj1 ⟨i.val, by omega⟩
      · by_cases h0 : i.val ≤ k₁
        · have heq : i.val = k₁ := by omega
          simp only [h0, h1, ↓reduceDIte]
          have hleft : p₁ ⟨i.val, by omega⟩ = y := by
            convert hp1k using 2; ext; exact heq
          have hright : p₂ ⟨i.val + 1 - k₁, by omega⟩ = p₂ ⟨1, by omega⟩ := by
            congr 1; ext; dsimp; omega
          rw [hleft, hright, ← hp20]
          exact hadj2 ⟨0, by omega⟩
        · simp only [h0, h1, ↓reduceDIte]
          have hlt : i.val - k₁ < k₂ := by omega
          have hstep := hadj2 ⟨i.val - k₁, hlt⟩
          have heq1 : (⟨i.val - k₁ + 1, Nat.succ_lt_succ hlt⟩ : Fin (k₂ + 1)) =
              ⟨i.val + 1 - k₁, by omega⟩ := by ext; simp; omega
          rw [heq1] at hstep
          exact hstep
  have no_even_adj {x y : Fin 25} (hxy : K.Adj x y) {k : ℕ} (heven : Even k) (hw : WalkLen x y k) :
      False := by
    obtain ⟨p, hp0, hpk, hadj⟩ := hw
    have hodd : Odd (k + 1) := heven.add_one
    refine hno (k + 1) hodd p ?_
    intro i
    by_cases hlast : i.val + 1 < k + 1
    · have hmod : (i.val + 1) % (k + 1) = i.val + 1 := Nat.mod_eq_of_lt hlast
      have hstep := hadj ⟨i.val, by omega⟩
      convert hstep using 2
      ext; exact hmod
    · have hi : i.val = k := by omega
      have hmod : (i.val + 1) % (k + 1) = 0 := by rw [hi, Nat.mod_self]
      have h1 : p i = y := by convert hpk using 2; ext; exact hi
      have h2 : p ⟨(i.val + 1) % (k + 1), Nat.mod_lt _ hodd.pos⟩ = x := by
        convert hp0 using 2; ext; exact hmod
      rw [h1, h2]
      exact hxy.symm
  let Reach (x y : Fin 25) : Prop := ∃ k, WalkLen x y k
  let comp (x : Fin 25) : Finset (Fin 25) := univ.filter (fun y => Reach x y)
  have hcomp_ne (x : Fin 25) : (comp x).Nonempty := ⟨x, mem_filter.mpr ⟨mem_univ x, 0, w_refl x⟩⟩
  let root (x : Fin 25) : Fin 25 := (comp x).min' (hcomp_ne x)
  have hroot_eq {x y : Fin 25} (hxy : K.Adj x y) : root x = root y := by
    have hcomp_eq : comp x = comp y := by
      ext z
      simp only [comp, mem_filter, mem_univ, true_and, Reach]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨1 + k, w_trans ⟨fun i => if i.val = 0 then y else x, rfl, rfl, fun i => by
          simp [hxy.symm]⟩ hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨1 + k, w_trans ⟨fun i => if i.val = 0 then x else y, rfl, rfl, fun i => by
          simp [hxy]⟩ hk⟩
    simp only [root, hcomp_eq]
  have hroot_reach (x : Fin 25) : Reach (root x) x := by
    have hmem : root x ∈ comp x := min'_mem _ _
    obtain ⟨k, hk⟩ := (mem_filter.mp hmem).2
    exact ⟨k, w_symm hk⟩
  let c (x : Fin 25) : Bool := decide (∃ k, Even k ∧ WalkLen (root x) x k)
  refine ⟨c, fun i j hij hcol => ?_⟩
  have hr : root i = root j := hroot_eq hij
  by_cases hi : ∃ k, Even k ∧ WalkLen (root i) i k
  · have hj : ∃ k, Even k ∧ WalkLen (root j) j k := by
      have hci : c i = true := by simp [c, hi]
      rw [hcol] at hci
      simpa [c] using hci
    obtain ⟨k₁, he1, hw1⟩ := hi
    obtain ⟨k₂, he2, hw2⟩ := hj
    rw [← hr] at hw2
    exact no_even_adj hij (he1.add he2) (w_trans (w_symm hw1) hw2)
  · have hj : ¬ ∃ k, Even k ∧ WalkLen (root j) j k := by
      have hci : c i = false := by simp [c, hi]
      rw [hcol] at hci
      simpa [c] using hci
    obtain ⟨k₁, hw1⟩ := hroot_reach i
    obtain ⟨k₂, hw2⟩ := hroot_reach j
    have ho1 : Odd k₁ := by
      rcases Nat.even_or_odd k₁ with h | h
      · exact absurd ⟨k₁, h, hw1⟩ hi
      · exact h
    have ho2 : Odd k₂ := by
      rcases Nat.even_or_odd k₂ with h | h
      · exact absurd ⟨k₂, h, hw2⟩ hj
      · exact h
    rw [← hr] at hw2
    exact no_even_adj hij (ho1.add_odd ho2) (w_trans (w_symm hw1) hw2)

lemma aes_bipartite_22 (W : Finset (Fin 25)) (hW : W.card = 22)
    (K : SimpleGraph (Fin 25)) (hcf : K.CliqueFree 3)
    (hsupp : ∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W)
    (hmin : ∀ i ∈ W, 9 ≤ (W.filter (K.Adj i)).card) :
    ∃ c : Fin 25 → Bool, ∀ i j : Fin 25, K.Adj i j → c i ≠ c j := by
  let HasOdd (L : ℕ) : Prop := ∃ hL : Odd L, ∃ f : Fin L → Fin 25,
    ∀ i : Fin L, K.Adj (f i) (f ⟨(i.val + 1) % L, Nat.mod_lt _ hL.pos⟩)
  by_cases hex : ∃ L, HasOdd L
  · exfalso
    let L := Nat.find hex
    have hL : HasOdd L := Nat.find_spec hex
    have hminL : ∀ M < L, ¬ HasOdd M := fun M hM => Nat.find_min hex hM
    obtain ⟨hLodd, f, hf⟩ := hL
    have hLpos : 0 < L := hLodd.pos
    have hLne1 : L ≠ 1 := by
      intro h1
      have h0 := hf ⟨0, by omega⟩
      have heq : (⟨(0 + 1) % L, Nat.mod_lt _ hLpos⟩ : Fin L) = ⟨0, by omega⟩ := by
        ext; dsimp; rw [h1]
      rw [heq] at h0
      exact K.loopless.irrefl _ h0
    have hLne3 : L ≠ 3 := by
      intro h3
      have h0 := hf ⟨0, by omega⟩
      have h1 := hf ⟨1, by omega⟩
      have h2 := hf ⟨2, by omega⟩
      have e0 : (⟨(0 + 1) % L, Nat.mod_lt _ hLpos⟩ : Fin L) = ⟨1, by omega⟩ := by
        ext; dsimp; rw [h3]
      have e1 : (⟨(1 + 1) % L, Nat.mod_lt _ hLpos⟩ : Fin L) = ⟨2, by omega⟩ := by
        ext; dsimp; rw [h3]
      have e2 : (⟨(2 + 1) % L, Nat.mod_lt _ hLpos⟩ : Fin L) = ⟨0, by omega⟩ := by
        ext; dsimp; rw [h3]
      rw [e0] at h0; rw [e1] at h1; rw [e2] at h2
      exact not_triangle hcf h0 h1 h2
    have hLge5 : 5 ≤ L := by
      obtain ⟨k, hk⟩ := hLodd
      omega
    have hdeg_on_C : ∀ v : Fin 25, ((univ : Finset (Fin L)).filter (fun i => K.Adj v (f i))).card ≤ 2 := by
      intro v
      by_contra! hgt
      have hcard3 : 3 ≤ ((univ : Finset (Fin L)).filter (fun i => K.Adj v (f i))).card := by omega
      obtain ⟨s, hs_sub, hs_card⟩ := exists_subset_card_eq hcard3
      have hs_ne : s.Nonempty := card_pos.mp (by omega)
      let a := s.min' hs_ne
      have ha_mem : a ∈ s := min'_mem s hs_ne
      let s₁ := s.erase a
      have hs1_card : s₁.card = 2 := by rw [card_erase_of_mem ha_mem, hs_card]
      have hs1_ne : s₁.Nonempty := card_pos.mp (by omega)
      let b := s₁.min' hs1_ne
      have hb_mem1 : b ∈ s₁ := min'_mem s₁ hs1_ne
      have hb_mem : b ∈ s := mem_of_mem_erase hb_mem1
      let s₂ := s₁.erase b
      have hs2_card : s₂.card = 1 := by rw [card_erase_of_mem hb_mem1, hs1_card]
      have hs2_ne : s₂.Nonempty := card_pos.mp (by omega)
      let c := s₂.min' hs2_ne
      have hc_mem2 : c ∈ s₂ := min'_mem s₂ hs2_ne
      have hc_mem1 : c ∈ s₁ := mem_of_mem_erase hc_mem2
      have hc_mem : c ∈ s := mem_of_mem_erase hc_mem1
      have hab : a.val < b.val :=
        lt_of_le_of_ne (min'_le s b hb_mem) (Fin.val_ne_of_ne (ne_of_mem_erase hb_mem1).symm)
      have hbc : b.val < c.val :=
        lt_of_le_of_ne (min'_le s₁ c hc_mem1) (Fin.val_ne_of_ne (ne_of_mem_erase hc_mem2).symm)
      have hva : K.Adj v (f a) := (mem_filter.mp (hs_sub ha_mem)).2
      have hvb : K.Adj v (f b) := (mem_filter.mp (hs_sub hb_mem)).2
      have hvc : K.Adj v (f c) := (mem_filter.mp (hs_sub hc_mem)).2
      let d₁ := b.val - a.val
      let d₂ := c.val - b.val
      let d₃ := L - (c.val - a.val)
      have hsum_d : d₁ + d₂ + d₃ = L := by omega
      have hd1_ge2 : 2 ≤ d₁ := by
        by_contra h1
        have heq : b.val = a.val + 1 := by omega
        have hadj_ab : K.Adj (f a) (f b) := by
          have hstep := hf a
          convert hstep using 2; ext; simp only [← heq, Nat.mod_eq_of_lt b.isLt]
        exact not_triangle hcf hva hadj_ab hvb.symm
      have hd2_ge2 : 2 ≤ d₂ := by
        by_contra h1
        have heq : c.val = b.val + 1 := by omega
        have hadj_bc : K.Adj (f b) (f c) := by
          have hstep := hf b
          convert hstep using 2; ext; simp only [← heq, Nat.mod_eq_of_lt c.isLt]
        exact not_triangle hcf hvb hadj_bc hvc.symm
      have hd3_ge2 : 2 ≤ d₃ := by
        by_contra h1
        have heq : (c.val + 1) % L = a.val := by
          have : c.val + 1 = L + a.val := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt a.isLt]
        have hadj_ca : K.Adj (f c) (f a) := by
          have hstep := hf c
          convert hstep using 2; ext; exact heq.symm
        exact not_triangle hcf hvc hadj_ca hva.symm
      have mk_shortcut (p q : Fin L) (d : ℕ) (hd_odd : Odd d) (hd_lt : d + 2 < L)
          (hvp : K.Adj v (f p)) (hvq : K.Adj v (f q))
          (hdist : (p.val + d) % L = q.val) : False := by
        have ho : Odd (d + 2) := by obtain ⟨m, rfl⟩ := hd_odd; exact ⟨m + 1, by omega⟩
        let g : Fin (d + 2) → Fin 25 := fun t =>
          if t.val = 0 then v else f ⟨(p.val + (t.val - 1)) % L, Nat.mod_lt _ hLpos⟩
        refine hminL (d + 2) hd_lt ⟨ho, g, fun t => ?_⟩
        by_cases ht0 : t.val = 0
        · have hmod : (t.val + 1) % (d + 2) = 1 := by rw [ht0]; exact Nat.mod_eq_of_lt (by omega)
          dsimp only [g]; rw [if_pos ht0, if_neg (by omega)]; simp only [hmod, Nat.sub_self, add_zero]
          convert hvp using 2; ext; exact Nat.mod_eq_of_lt p.isLt
        · by_cases htlast : t.val = d + 1
          · have hmod : (t.val + 1) % (d + 2) = 0 := by rw [htlast, Nat.mod_self]
            dsimp only [g]; rw [if_neg ht0, if_pos hmod]; simp only [htlast, show d + 1 - 1 = d by omega]
            have hfq : (⟨(p.val + d) % L, Nat.mod_lt _ hLpos⟩ : Fin L) = q := by ext; exact hdist
            rw [hfq]
            exact hvq.symm
          · have hlt_next : t.val + 1 < d + 2 := by omega
            have hmod : (t.val + 1) % (d + 2) = t.val + 1 := Nat.mod_eq_of_lt hlt_next
            simp only [g, ht0, ↓reduceIte, hmod, show t.val + 1 ≠ 0 by omega]
            have hstep := hf ⟨(p.val + (t.val - 1)) % L, Nat.mod_lt _ hLpos⟩
            convert hstep using 2
            ext; simp only
            rw [Nat.mod_add_mod]
            congr 1; omega
      have hodd_one : Odd d₁ ∨ Odd d₂ ∨ Odd d₃ := by
        rcases Nat.even_or_odd d₁ with ⟨m1, hm1⟩ | h1
        · rcases Nat.even_or_odd d₂ with ⟨m2, hm2⟩ | h2
          · right; right
            obtain ⟨k, hk⟩ := hLodd
            exact ⟨k - m1 - m2, by omega⟩
          · exact Or.inr (Or.inl h2)
        · exact Or.inl h1
      rcases hodd_one with ho1 | ho2 | ho3
      · exact mk_shortcut a b d₁ ho1 (by omega) hva hvb (by
          rw [show a.val + d₁ = b.val by omega, Nat.mod_eq_of_lt b.isLt])
      · exact mk_shortcut b c d₂ ho2 (by omega) hvb hvc (by
          rw [show b.val + d₂ = c.val by omega, Nat.mod_eq_of_lt c.isLt])
      · exact mk_shortcut c a d₃ ho3 (by omega) hvc hva (by
          rw [show c.val + d₃ = L + a.val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt a.isLt])
    have hfinW : ∀ i : Fin L, f i ∈ W := fun i => (hsupp _ _ (hf i)).1
    have hlow : 45 ≤ ∑ i : Fin L, (W.filter (K.Adj (f i))).card := by
      have h1 : ∑ i : Fin L, 9 ≤ ∑ i : Fin L, (W.filter (K.Adj (f i))).card :=
        sum_le_sum fun i _ => hmin (f i) (hfinW i)
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h1
      omega
    have hhigh : (∑ i : Fin L, (W.filter (K.Adj (f i))).card) ≤ 44 := by
      calc (∑ i : Fin L, (W.filter (K.Adj (f i))).card)
          = ∑ i : Fin L, ∑ v ∈ W, if K.Adj (f i) v then 1 else 0 :=
              sum_congr rfl fun i _ => by rw [card_filter]
        _ = ∑ v ∈ W, ∑ i : Fin L, if K.Adj v (f i) then 1 else 0 := by
              rw [sum_comm]
              exact sum_congr rfl fun v _ => sum_congr rfl fun i _ => by simp only [K.adj_comm]
        _ = ∑ v ∈ W, ((univ : Finset (Fin L)).filter (fun i => K.Adj v (f i))).card :=
              sum_congr rfl fun v _ => by rw [card_filter]
        _ ≤ ∑ _v ∈ W, 2 := sum_le_sum fun v _ => hdeg_on_C v
        _ = 44 := by simp [hW]
    omega
  · exact even_reach_bipartite K (fun L hL f hf => hex ⟨L, hL, f, hf⟩)

lemma dense_case_22 (W : Finset (Fin 25)) (hW : W.card = 22)
    (K : SimpleGraph (Fin 25)) (hcf : K.CliqueFree 3)
    (hsupp : ∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W)
    (hS : 198 ≤ ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0) :
    ∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) ≤ 34 := by
  let S := ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0
  let cut (v : Fin 25) := ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0
  have hsum := sum_nbhd_cuts W K hcf
  change (∑ v ∈ W, cut v) + 2 * (∑ u ∈ W, (W.filter (K.Adj u)).card ^ 2) = W.card * S at hsum
  have hdeg_sum : (∑ u ∈ W, (W.filter (K.Adj u)).card) = S :=
    sum_congr rfl fun u _ => by rw [card_filter]
  have hcs := sq_sum_le W (fun u => (W.filter (K.Adj u)).card)
  rw [hdeg_sum, hW] at hcs
  by_cases hreg : ∀ u ∈ W, (W.filter (K.Adj u)).card = 9
  · obtain ⟨c, hc⟩ := aes_bipartite_22 W hW K hcf hsupp (fun u hu => by rw [hreg u hu])
    refine ⟨c, ?_⟩
    have hzero : (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) = 0 :=
      sum_eq_zero fun i _ => sum_eq_zero fun j _ => by
        by_cases h : K.Adj i j
        · simp [h, hc i j h]
        · simp [h]
    omega
  · have hstrict : (∑ v ∈ W, cut v) < 22 * 36 := by
      by_cases h200 : 200 ≤ S
      · have h22 : 22 * (∑ v ∈ W, cut v) + 2 * S ^ 2 ≤ 22 * (22 * S) := by
          rw [hW] at hsum
          nlinarith
        have hSmax : 2 * S ≤ 22 ^ 2 := by
          have := mantel_ordered K hcf W
          rw [hW] at this
          exact this
        have : 22 * (∑ v ∈ W, cut v) < 22 * (22 * 36) := by nlinarith
        omega
      · have heven := unordered W (fun i j => if K.Adj i j then 1 else 0)
          (fun i j => by simp only [K.adj_comm]) (fun i => by simp)
        change S = 2 * _ at heven
        have hS198 : S = 198 := by omega
        push Not at hreg
        have hsq := sq_sum_strict_of_ne_const W (fun u => (W.filter (K.Adj u)).card) 9
          (by rw [hdeg_sum, hS198, hW]) hreg
        rw [hW, hS198] at hsum
        rw [hW] at hsq
        omega
    by_contra! hfail
    have hge : ∀ v ∈ W, 36 ≤ cut v := by
      intro v hv
      have hbad := hfail (fun x => decide (K.Adj v x))
      have heq : (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ decide (K.Adj v i) = decide (K.Adj v j) then 1 else 0) =
          cut v := sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp
      rw [heq] at hbad
      have hev := unordered W (fun i j => if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0)
        (fun i j => by simp only [K.adj_comm, iff_comm]) (fun i => by simp)
      change cut v = 2 * _ at hev
      omega
    have htot := sum_le_sum hge
    simp only [sum_const, hW, smul_eq_mul] at htot
    omega

lemma extendHalf_on (W : Finset (Fin 25)) (K : SimpleGraph (Fin 25))
    (U : Finset (Fin 25)) (hUW : U ⊆ W) (b : Fin 25 → Bool)
    (hb : ∀ i ∈ U, ∀ j ∈ U, K.Adj i j → b i ≠ b j) :
    ∃ f : Fin 25 → Bool,
      2 * (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ f i = f j then 1 else 0) +
        (∑ i ∈ U, ∑ j ∈ U, if K.Adj i j then 1 else 0) ≤
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0) := by
  let w (i j : Fin 25) : ℕ := if K.Adj i j then 1 else 0
  have hsym (i j : Fin 25) : w i j = w j i := by simp only [w, K.adj_comm]
  have hdiag (i : Fin 25) : w i i = 0 := by simp [w]
  have expandCost (T : Finset (Fin 25)) (g : Fin 25 → Bool) :
      (∑ i ∈ T, ∑ j ∈ T, if g i = g j then w i j else 0) =
      ∑ i ∈ T, ∑ j ∈ T, if K.Adj i j ∧ g i = g j then 1 else 0 := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases e : g i = g j <;> simp [w, e]
  have hzeroU : (∑ i ∈ U, ∑ j ∈ U, if b i = b j then w i j else 0) = 0 := by
    rw [expandCost]
    exact sum_eq_zero fun i hi => sum_eq_zero fun j hj => by
      by_cases h : K.Adj i j
      · simp [h, hb i hi j hj h]
      · simp [h]
  have step : ∀ V : Finset (Fin 25), ∃ f : Fin 25 → Bool,
      2 * (∑ i ∈ U ∪ V, ∑ j ∈ U ∪ V, if f i = f j then w i j else 0) +
        (∑ i ∈ U, ∑ j ∈ U, w i j) ≤
      (∑ i ∈ U ∪ V, ∑ j ∈ U ∪ V, w i j) := by
    intro V
    induction V using Finset.induction_on with
    | empty =>
      refine ⟨b, ?_⟩
      simp [hzeroU]
    | @insert x V _ ih =>
      obtain ⟨f, hf⟩ := ih
      by_cases hx : x ∈ U ∪ V
      · have heq : U ∪ insert x V = U ∪ V := by rw [union_insert, insert_eq_of_mem hx]
        exact ⟨f, by rwa [heq]⟩
      · let T := U ∪ insert x V
        have hxt : x ∈ T := mem_union_right _ (mem_insert_self ..)
        have her : T.erase x = U ∪ V := by
          change (U ∪ insert x V).erase x = _
          rw [union_insert, erase_insert hx]
        obtain ⟨g, hg⟩ := extend_color T hxt w hsym hdiag f
        have hinc := erase_total T hxt w hsym (hdiag x)
        rw [her] at hg hinc
        refine ⟨g, ?_⟩
        change 2 * (∑ i ∈ T, ∑ j ∈ T, if g i = g j then w i j else 0) +
            (∑ i ∈ U, ∑ j ∈ U, w i j) ≤ ∑ i ∈ T, ∑ j ∈ T, w i j
        omega
  obtain ⟨f, hf⟩ := step W
  rw [union_eq_right.mpr hUW, expandCost] at hf
  exact ⟨f, hf⟩

lemma sparse_case_22 (W : Finset (Fin 25)) (hW : W.card = 22)
    (K : SimpleGraph (Fin 25)) (hcf : K.CliqueFree 3)
    (hS : (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0) ≤ 84) :
    ∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) ≤ 34 := by
  let S := ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0
  have heven_cut : ∀ f : Fin 25 → Bool,
      Even (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ f i = f j then 1 else 0) := by
    intro f
    have h := unordered W (fun i j => if K.Adj i j ∧ f i = f j then 1 else 0)
      (fun i j => by by_cases e : f i = f j <;> simp [e, K.adj_comm, Ne.symm])
      (fun i => by simp)
    exact ⟨_, by rw [← two_mul]; exact h⟩
  by_cases h70 : S ≤ 70
  · obtain ⟨f, hf⟩ := extendHalf_on W K ∅ (empty_subset W) (fun _ => false) (by simp)
    simp only [sum_empty, add_zero] at hf
    change 2 * _ ≤ S at hf
    obtain ⟨k, hk⟩ := heven_cut f
    exact ⟨f, by omega⟩
  · have hSpos : 0 < S := by omega
    let d (i : Fin 25) := (W.filter (K.Adj i)).card
    have hdeg_sum : (∑ i ∈ W, d i) = S := sum_congr rfl fun i _ => by dsimp [d]; rw [card_filter]
    have hcs := sq_sum_le W d
    rw [hdeg_sum, hW] at hcs
    have hex_edge : ∃ u ∈ W, ∃ v ∈ W, K.Adj u v ∧ S ≤ 11 * (d u + d v) := by
      by_contra! hall
      have hbound : ∑ u ∈ W, ∑ v ∈ W, (if K.Adj u v then 11 * (d u + d v) else 0) <
          ∑ u ∈ W, ∑ v ∈ W, (if K.Adj u v then S else 0) := by
        have hle : ∀ u ∈ W, ∑ v ∈ W, (if K.Adj u v then 11 * (d u + d v) else 0) ≤
            ∑ v ∈ W, (if K.Adj u v then S else 0) := fun u hu =>
          sum_le_sum fun v hv => by
            split_ifs with h
            · exact le_of_lt (hall u hu v hv h)
            · exact le_rfl
        have hpos_pair : ∃ u ∈ W, ∃ v ∈ W, K.Adj u v := by
          by_contra! hnone
          have h0 : S = 0 := sum_eq_zero fun u hu => sum_eq_zero fun v hv => by simp [hnone u hu v hv]
          omega
        obtain ⟨u₀, hu₀, v₀, hv₀, huv₀⟩ := hpos_pair
        have hlt_u0 : (∑ v ∈ W, if K.Adj u₀ v then 11 * (d u₀ + d v) else 0) <
            ∑ v ∈ W, if K.Adj u₀ v then S else 0 :=
          sum_lt_sum (fun v hv => by split_ifs with h; exact le_of_lt (hall u₀ hu₀ v hv h); exact le_rfl)
            ⟨v₀, hv₀, by simp [huv₀, hall u₀ hu₀ v₀ hv₀ huv₀]⟩
        exact sum_lt_sum hle ⟨u₀, hu₀, hlt_u0⟩
      have hrhs : (∑ u ∈ W, ∑ v ∈ W, if K.Adj u v then S else 0) = S ^ 2 := by
        calc (∑ u ∈ W, ∑ v ∈ W, if K.Adj u v then S else 0)
            = S * S := by
                dsimp [S]; rw [mul_sum]
                refine sum_congr rfl fun u _ => ?_
                rw [mul_sum]; exact sum_congr rfl fun v _ => by split_ifs <;> simp
          _ = S ^ 2 := by ring
      have hlhs : (∑ u ∈ W, ∑ v ∈ W, if K.Adj u v then 11 * (d u + d v) else 0) =
          22 * ∑ u ∈ W, d u ^ 2 := by
        have h1 : (∑ u ∈ W, ∑ v ∈ W, if K.Adj u v then 11 * (d u + d v) else 0) =
            11 * ((∑ u ∈ W, ∑ v ∈ W, if K.Adj u v then d u else 0) +
                  (∑ u ∈ W, ∑ v ∈ W, if K.Adj u v then d v else 0)) := by
          rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun u _ => ?_
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun v _ => by split_ifs <;> ring
        have hleft : (∑ u ∈ W, ∑ v ∈ W, if K.Adj u v then d u else 0) = ∑ u ∈ W, d u ^ 2 := by
          refine sum_congr rfl fun u _ => ?_
          calc (∑ v ∈ W, if K.Adj u v then d u else 0)
              = d u * (∑ v ∈ W, if K.Adj u v then 1 else 0) := by
                  rw [mul_sum]; exact sum_congr rfl fun v _ => by split_ifs <;> simp
            _ = d u ^ 2 := by rw [← card_filter, sq]
        have hright : (∑ u ∈ W, ∑ v ∈ W, if K.Adj u v then d v else 0) = ∑ v ∈ W, d v ^ 2 := by
          rw [sum_comm]
          refine sum_congr rfl fun v _ => ?_
          calc (∑ u ∈ W, if K.Adj u v then d v else 0)
              = d v * (∑ u ∈ W, if K.Adj v u then 1 else 0) := by
                  rw [mul_sum]; exact sum_congr rfl fun u _ => by rw [K.adj_comm]; split_ifs <;> simp
            _ = d v ^ 2 := by rw [← card_filter, sq]
        rw [h1, hleft, hright]; ring
      rw [hlhs, hrhs] at hbound
      omega
    obtain ⟨u, hu, v, hv, huv, hduv⟩ := hex_edge
    let Nu := W.filter (K.Adj u)
    let Nv := W.filter (K.Adj v)
    let U := Nu ∪ Nv
    have hUW : U ⊆ W := union_subset (filter_subset _ _) (filter_subset _ _)
    have hproper : ∀ i ∈ U, ∀ j ∈ U, K.Adj i j → decide (i ∈ Nu) ≠ decide (j ∈ Nu) := by
      intro i hi j hj hij heq
      have hiff : i ∈ Nu ↔ j ∈ Nu := by simpa using heq
      by_cases hiu : i ∈ Nu
      · have hju : j ∈ Nu := hiff.mp hiu
        exact not_triangle hcf hij (mem_filter.mp hju).2.symm (mem_filter.mp hiu).2
      · have hju : j ∉ Nu := fun h => hiu (hiff.mpr h)
        have hiv : i ∈ Nv := (mem_union.mp hi).resolve_left hiu
        have hjv : j ∈ Nv := (mem_union.mp hj).resolve_left hju
        exact not_triangle hcf hij (mem_filter.mp hjv).2.symm (mem_filter.mp hiv).2
    have huU : u ∈ U := mem_union_right _ (mem_filter.mpr ⟨hu, huv.symm⟩)
    have hvU : v ∈ U := mem_union_left _ (mem_filter.mpr ⟨hv, huv⟩)
    have hne_uv : u ≠ v := K.ne_of_adj huv
    have hedgesU : 2 * (d u + d v - 1) ≤ ∑ i ∈ U, ∑ j ∈ U, if K.Adj i j then 1 else 0 := by
      have hrow_u : (∑ j ∈ U, if K.Adj u j then 1 else 0) = d u := by
        rw [← card_filter]
        congr 1; ext j
        simp only [mem_filter, Nu, Nv, U, mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact ⟨h1.1, h2⟩
          · exact ⟨h1.1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inl ⟨h1, h2⟩, h2⟩
      have hrow_v : (∑ j ∈ U, if K.Adj v j then 1 else 0) = d v := by
        rw [← card_filter]
        congr 1; ext j
        simp only [mem_filter, Nu, Nv, U, mem_union]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact ⟨h1.1, h2⟩
          · exact ⟨h1.1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr ⟨h1, h2⟩, h2⟩
      have hrow_u_erase : (∑ j ∈ U.erase v, if K.Adj u j then 1 else 0) = d u - 1 := by
        have hadd := sum_erase_add U (fun j => if K.Adj u j then 1 else 0) hvU
        rw [hrow_u, if_pos huv] at hadd
        omega
      have h1 := erase_total U hvU (fun i j => if K.Adj i j then 1 else 0)
        (fun i j => by simp only [K.adj_comm]) (by simp)
      have hu_in : u ∈ U.erase v := mem_erase.mpr ⟨hne_uv, huU⟩
      have h2 := erase_total (U.erase v) hu_in (fun i j => if K.Adj i j then 1 else 0)
        (fun i j => by simp only [K.adj_comm]) (by simp)
      have hv_row_er : (∑ j ∈ U.erase v, if K.Adj v j then 1 else 0) = d v := by
        have hadd := sum_erase_add U (fun j => if K.Adj v j then 1 else 0) hvU
        rw [hrow_v, if_neg (K.loopless.irrefl v), add_zero] at hadd
        exact hadd
      have hu_row_er : (∑ j ∈ (U.erase v).erase u, if K.Adj u j then 1 else 0) = d u - 1 := by
        have hadd := sum_erase_add (U.erase v) (fun j => if K.Adj u j then 1 else 0) hu_in
        rw [hrow_u_erase, if_neg (K.loopless.irrefl u), add_zero] at hadd
        exact hadd
      omega
    obtain ⟨f, hf⟩ := extendHalf_on W K U hUW (fun i => decide (i ∈ Nu)) hproper
    change 2 * (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ f i = f j then 1 else 0) +
        (∑ i ∈ U, ∑ j ∈ U, if K.Adj i j then 1 else 0) ≤ S at hf
    have hduv_pos : 1 ≤ d u + d v := by
      have : 0 < d u := card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, huv⟩⟩
      omega
    obtain ⟨k, hk⟩ := heven_cut f
    refine ⟨f, ?_⟩
    have hS_le : S ≤ 84 := hS
    omega

lemma c5_five_parts_22 (x0 x1 x2 x3 x4 : ℕ) (hsum : x0 + x1 + x2 + x3 + x4 = 22) :
    x0 * x1 ≤ 16 ∨ x1 * x2 ≤ 16 ∨ x2 * x3 ≤ 16 ∨ x3 * x4 ≤ 16 ∨ x4 * x0 ≤ 16 := by
  by_contra! hall
  obtain ⟨h0, h1, h2, h3, h4⟩ := hall
  have hge4 (a b c d e : ℕ) (hs : a + b + c + d + e = 22)
      (hab : 16 < a * b) (hcd : 16 < c * d) (hea : 16 < e * a) : 4 ≤ a := by
    by_contra hlt
    have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
    have hcd_sum : c + d ≤ 7 := by
      rcases hcase with rfl | rfl | rfl | rfl <;> nlinarith
    nlinarith [sq_nonneg ((c : ℤ) - (d : ℤ))]
  have ha0 : 4 ≤ x0 := hge4 x0 x1 x2 x3 x4 (by omega) h0 h2 h4
  have ha1 : 4 ≤ x1 := hge4 x1 x2 x3 x4 x0 (by omega) h1 h3 h0
  have ha2 : 4 ≤ x2 := hge4 x2 x3 x4 x0 x1 (by omega) h2 h4 h1
  have ha3 : 4 ≤ x3 := hge4 x3 x4 x0 x1 x2 (by omega) h3 h0 h2
  have ha4 : 4 ≤ x4 := hge4 x4 x0 x1 x2 x3 (by omega) h4 h1 h3
  have hadj : (x0 = 4 ∧ x1 = 4) ∨ (x1 = 4 ∧ x2 = 4) ∨ (x2 = 4 ∧ x3 = 4) ∨
      (x3 = 4 ∧ x4 = 4) ∨ (x4 = 4 ∧ x0 = 4) := by omega
  rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

lemma c5_hom_case_22 (W : Finset (Fin 25)) (hW : W.card = 22)
    (K : SimpleGraph (Fin 25)) (f : Fin 25 → Fin 5)
    (hf : ∀ i ∈ W, ∀ j ∈ W, K.Adj i j → f i + 1 = f j ∨ f j + 1 = f i) :
    ∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) ≤ 34 := by
  let a (r : Fin 5) := (W.filter (fun i => f i = r)).card
  have hsum : a 0 + a 1 + a 2 + a 3 + a 4 = 22 := by
    have htot : (∑ r : Fin 5, a r) = W.card := by
      have hbi : (∑ r : Fin 5, (W.filter (fun i => f i = r)).card) = W.card := by
        rw [← card_biUnion]
        · congr 1; ext i; simp
        · intro r _ s _ hrs
          dsimp [Function.onFun]
          rw [Finset.disjoint_left]
          intro x hxr hxs
          exact hrs ((mem_filter.mp hxr).2.symm.trans (mem_filter.mp hxs).2)
      exact hbi
    rw [Fin.sum_univ_five, hW] at htot
    exact htot
  have hsmall : ∃ r : Fin 5, a r * a (r + 1) ≤ 16 := by
    rcases c5_five_parts_22 (a 0) (a 1) (a 2) (a 3) (a 4) hsum with h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  obtain ⟨r, hr⟩ := hsmall
  let paint (e x : Fin 5) : Bool := decide (((x.val + 5 - e.val) % 5) % 2 = 0)
  have honly : ∀ e x y : Fin 5, x + 1 = y ∨ y + 1 = x → paint (e + 1) x = paint (e + 1) y →
      (x = e ∧ y = e + 1) ∨ (x = e + 1 ∧ y = e) := by decide
  refine ⟨fun i => paint (r + 1) (f i), ?_⟩
  have hbound : (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ paint (r + 1) (f i) = paint (r + 1) (f j) then 1 else 0) ≤
      (∑ i ∈ W, ∑ j ∈ W, if f i = r ∧ f j = r + 1 then 1 else 0) +
      (∑ i ∈ W, ∑ j ∈ W, if f i = r + 1 ∧ f j = r then 1 else 0) := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun i hi => ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun j hj => ?_
    by_cases h : K.Adj i j ∧ paint (r + 1) (f i) = paint (r + 1) (f j)
    · rcases honly r (f i) (f j) (hf i hi j hj h.1) h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h, if_pos ⟨h1, h2⟩]; exact Nat.le_add_right 1 _
      · rw [if_pos h, show (if f i = r + 1 ∧ f j = r then 1 else 0) = 1 from if_pos ⟨h1, h2⟩]; exact Nat.le_add_left 1 _
    · simp only [h, ↓reduceIte]; exact Nat.zero_le _
  have hprod (p q : Fin 5) : (∑ i ∈ W, ∑ j ∈ W, if f i = p ∧ f j = q then 1 else 0) = a p * a q := by
    calc (∑ i ∈ W, ∑ j ∈ W, if f i = p ∧ f j = q then 1 else 0)
        = ∑ i ∈ W, (if f i = p then 1 else 0) * (∑ j ∈ W, if f j = q then 1 else 0) := by
            refine sum_congr rfl fun i _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun j _ => by by_cases hp : f i = p <;> by_cases hq : f j = q <;> simp [hp, hq]
      _ = (∑ i ∈ W, if f i = p then 1 else 0) * (∑ j ∈ W, if f j = q then 1 else 0) := by
            rw [← sum_mul]
      _ = a p * a q := by dsimp [a]; rw [card_filter, card_filter]
  rw [hprod r (r + 1), hprod (r + 1) r] at hbound
  nlinarith

theorem main : H1 → H2 → H3 → OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1.H1 := by
  intro h21 hlowmid hhighmid G hG W hW
  let G₀ : SimpleGraph (Fin 25) :=
    { Adj := fun i j => G.Adj i j ∧ i ∈ W ∧ j ∈ W
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun i h => G.loopless.irrefl i h.1⟩ }
  have hG₀cf : G₀.CliqueFree 3 := hG.anti (show G₀ ≤ G from fun _ _ h => h.1)
  let eligible (K : SimpleGraph (Fin 25)) := K.CliqueFree 3 ∧ ∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W
  obtain ⟨K, hsub, hmax⟩ := Finite.exists_le_maximal (p := eligible) ⟨hG₀cf, fun _ _ h => h.2⟩
  have hlift : ∀ i ∈ W, ∀ j ∈ W, G.Adj i j → K.Adj i j := fun i hi j hj e => hsub ⟨e, hi, hj⟩
  have htrans : (∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) ≤ 34) →
      ∃ c : Fin 25 → Bool,
        (∑ i ∈ W, ∑ j ∈ W, if G.Adj i j ∧ c i = c j then 1 else 0) ≤ 34 := by
    rintro ⟨c, hc⟩
    refine ⟨c, le_trans ?_ hc⟩
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    by_cases h : G.Adj i j ∧ c i = c j
    · simp [h, hlift i hi j hj h.1]
    · simp [h]
  apply htrans
  have hKcf : K.CliqueFree 3 := hmax.1.1
  have hKsupp : ∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W := hmax.1.2
  have hKmax : ∀ H : SimpleGraph (Fin 25), K ≤ H → H.CliqueFree 3 →
      (∀ i j, H.Adj i j → i ∈ W ∧ j ∈ W) → H = K :=
    fun H hle hcf hsp => le_antisymm (hmax.2 ⟨hcf, hsp⟩ hle) hle
  -- Case 1: minimum degree ≤ 3, reduce to order-21 bound H1
  by_cases hlowdeg : ∃ v ∈ W, (W.filter (K.Adj v)).card ≤ 3
  · obtain ⟨v, hv, hdeg⟩ := hlowdeg
    obtain ⟨c, hc⟩ := h21 K hKcf (W.erase v) (by rw [card_erase_of_mem hv, hW])
    let w (i j : Fin 25) : ℕ := if K.Adj i j then 1 else 0
    have expandCost (U : Finset (Fin 25)) (g : Fin 25 → Bool) :
        (∑ i ∈ U, ∑ j ∈ U, if g i = g j then w i j else 0) =
        ∑ i ∈ U, ∑ j ∈ U, if K.Adj i j ∧ g i = g j then 1 else 0 :=
      sum_congr rfl fun i _ => sum_congr rfl fun j _ => by by_cases e : g i = g j <;> simp [w, e]
    obtain ⟨g, hg⟩ := extend_color W hv w (fun i j => by simp only [w, K.adj_comm])
      (fun i => by simp [w]) c
    rw [expandCost, expandCost] at hg
    have hd : (∑ j ∈ W.erase v, w v j) ≤ 3 := by
      rw [← card_filter] at *
      exact (card_le_card (filter_subset_filter _ (erase_subset _ _))).trans hdeg
    exact ⟨g, by omega⟩
  -- Case 2: maximum degree ≥ 13, Mantel on the remaining ≤ 8 vertices
  by_cases hhighdeg : ∃ v ∈ W, 13 ≤ (W.filter (K.Adj v)).card
  · obtain ⟨v, hv, hdeg⟩ := hhighdeg
    exact nbhd_cut_highdeg W hW K hKcf hv hdeg
  -- Case 3: minimum degree ≥ 9, Andrásfai–Erdős–Sós gives bipartiteness
  by_cases haes : ∀ i ∈ W, 9 ≤ (W.filter (K.Adj i)).card
  · obtain ⟨c, hc⟩ := aes_bipartite_22 W hW K hKcf hKsupp haes
    refine ⟨c, ?_⟩
    have h0 : (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) = 0 :=
      sum_eq_zero fun i _ => sum_eq_zero fun j _ => by
        by_cases h : K.Adj i j
        · simp [h, hc i j h]
        · simp [h]
    omega
  -- Case 4: C₅-homomorphic graph
  by_cases hc5 : ∃ f : Fin 25 → Fin 5, ∀ i ∈ W, ∀ j ∈ W, K.Adj i j → f i + 1 = f j ∨ f j + 1 = f i
  · obtain ⟨f, hf⟩ := hc5
    exact c5_hom_case_22 W hW K f hf
  -- Case 5: a neighborhood cut already works
  by_cases hnbhd : ∃ v ∈ W, (∑ i ∈ W, ∑ j ∈ W,
      if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0) < 36
  · obtain ⟨v, _, hvcut⟩ := hnbhd
    refine ⟨fun x => decide (K.Adj v x), ?_⟩
    have heq : (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ decide (K.Adj v i) = decide (K.Adj v j) then 1 else 0) =
        ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0 :=
      sum_congr rfl fun i _ => sum_congr rfl fun j _ => by simp
    have hev := unordered W (fun i j => if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0)
      (fun i j => by simp only [K.adj_comm, iff_comm]) (fun i => by simp)
    rw [heq]
    omega
  -- Case 6: sparse (S ≤ 84) or dense (S ≥ 198)
  let S := ∑ i ∈ W, ∑ j ∈ W, if K.Adj i j then 1 else 0
  by_cases hsparse : S ≤ 84
  · exact sparse_case_22 W hW K hKcf hsparse
  by_cases hdense : 198 ≤ S
  · exact dense_case_22 W hW K hKcf hKsupp hdense
  -- Remaining residual: 86 ≤ S ≤ 196 (even), split into H2 (≤ 140) and H3 (≥ 142)
  have hSeven := unordered W (fun i j => if K.Adj i j then 1 else 0)
    (fun i j => by simp only [K.adj_comm]) (fun i => by simp)
  change S = 2 * _ at hSeven
  have hmin4 : ∀ i ∈ W, 4 ≤ (W.filter (K.Adj i)).card := by
    intro i hi; by_contra! h; exact hlowdeg ⟨i, hi, by omega⟩
  have hmax12 : ∀ i ∈ W, (W.filter (K.Adj i)).card ≤ 12 := by
    intro i hi; by_contra! h; exact hhighdeg ⟨i, hi, by omega⟩
  have hle8 : ∃ i ∈ W, (W.filter (K.Adj i)).card ≤ 8 := by
    push Not at haes
    obtain ⟨i, hi, hlt⟩ := haes
    exact ⟨i, hi, by omega⟩
  have hnbhd36 : ∀ v ∈ W, 36 ≤ ∑ i ∈ W, ∑ j ∈ W,
      if K.Adj i j ∧ (K.Adj v i ↔ K.Adj v j) then 1 else 0 := by
    intro v hv; by_contra! h; exact hnbhd ⟨v, hv, h⟩
  by_cases hmid : S ≤ 140
  · exact hlowmid W hW K hKcf hKsupp hKmax (by omega) hmid hmin4 hmax12 hle8 hc5 hnbhd36
  · exact hhighmid W hW K hKcf hKsupp hKmax (by omega) (by omega) hmin4 hmax12 hle8 hc5 hnbhd36

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1_H1_R1
