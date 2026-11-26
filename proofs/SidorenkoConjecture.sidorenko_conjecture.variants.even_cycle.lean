import FormalConjectures.Wikipedia.SidorenkoConjecture
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
The trace estimate and its expansion as a sum over closed walks are adapted
from TheWaler's graphon proof in PR #478. For a finite host, each product in
the expansion of the adjacency matrix trace is the indicator of a cycle
homomorphism. The ordered edge count gives the numerator for $K_2$.
-/

open Finset SimpleGraph

namespace OMA.EvenCycle

private lemma matrix_pow_apply_eq_sum {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ∀ (n : ℕ) (a b : Fin N),
      (A ^ (n + 1)) a b =
        ∑ f : Fin (n + 1) → Fin N,
          if f 0 = a then (∏ i : Fin n, A (f i.castSucc) (f i.succ)) * A (f (Fin.last n)) b else 0 := by
  intro n
  induction n with
  | zero =>
    intro a b
    rw [pow_one]
    let e : (Fin 1 → Fin N) ≃ Fin N := Equiv.funUnique (Fin 1) (Fin N)
    rw [← Equiv.sum_comp e.symm]
    simp [e]
  | succ n ih =>
    intro a b
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih]
    let snocFun (f : Fin (n + 1) → Fin N) (c : Fin N) (i : Fin (n + 2)) : Fin N :=
      if h : i.1 < n + 1 then f ⟨i.1, h⟩ else c
    let e : (Fin (n + 1) → Fin N) × Fin N ≃ (Fin (n + 2) → Fin N) :=
      { toFun := fun p => snocFun p.1 p.2
        invFun := fun g => (fun i => g i.castSucc, g (Fin.last (n + 1)))
        left_inv := fun ⟨f, c⟩ => by
          ext i
          · simp only [snocFun, Fin.val_castSucc, i.2, ↓reduceDIte, Fin.eta]
          · simp only [snocFun, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
        right_inv := fun g => by
          funext i
          by_cases h : i.1 < n + 1
          · simp only [snocFun, h, ↓reduceDIte]
            rfl
          · have hlast : i = Fin.last (n + 1) := Fin.ext (by rw [Fin.val_last]; omega)
            rw [hlast]
            simp only [snocFun, Fin.val_last, lt_self_iff_false, ↓reduceDIte] }
    rw [← Equiv.sum_comp e]
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    change (if f 0 = a then (∏ i : Fin n, A (f i.castSucc) (f i.succ)) * A (f (Fin.last n)) c else 0) * A c b =
      if snocFun f c 0 = a then
        (∏ i : Fin (n + 1), A (snocFun f c i.castSucc) (snocFun f c i.succ)) *
          A (snocFun f c (Fin.last (n + 1))) b
      else 0
    have h0 : snocFun f c 0 = f 0 := by simp [snocFun]
    have hlast : snocFun f c (Fin.last (n + 1)) = c := by simp [snocFun]
    rw [h0, hlast]
    split_ifs
    · rw [Fin.prod_univ_castSucc]
      congr 1
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        have h1 : snocFun f c i.castSucc.castSucc = f i.castSucc := by
          simp only [snocFun, Fin.val_castSucc, Nat.lt_succ_of_lt i.2, ↓reduceDIte]
          rfl
        have h2 : snocFun f c i.castSucc.succ = f i.succ := by
          simp only [snocFun, Fin.val_succ, Fin.val_castSucc, Nat.succ_lt_succ i.2, ↓reduceDIte]
          rfl
        rw [h1, h2]
      · congr 1
        · simp only [snocFun, Fin.val_castSucc, Fin.val_last, lt_add_one, ↓reduceDIte]
          rfl
        · simp only [snocFun, Fin.val_succ, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
    · simp

private lemma matrix_trace_pow_succ_eq_sum {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (n : ℕ) (hn : 1 ≤ n) :
    (A ^ (n + 1)).trace = ∑ f : Fin (n + 1) → Fin N, ∏ i : Fin (n + 1), A (f i) (f (i + 1)) := by
  rw [Matrix.trace]
  simp_rw [Matrix.diag_apply, matrix_pow_apply_eq_sum A n]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hsucc : (i.castSucc : Fin (n + 1)) + 1 = i.succ := by
      apply Fin.ext
      have hi : i.1 + 1 < n + 1 := Nat.succ_lt_succ i.2
      have h1 : (1 : Fin (n + 1)).val = 1 := by
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [Fin.val_add, h1, Fin.val_castSucc, Fin.val_succ, Nat.mod_eq_of_lt hi]
    rw [hsucc]
  · have hlast : (Fin.last n : Fin (n + 1)) + 1 = 0 := by
      apply Fin.ext
      have h1 : (1 : Fin (n + 1)).val = 1 := by
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [Fin.val_add, h1, Fin.val_last, Fin.val_zero, Nat.mod_self]
    rw [hlast]

private lemma matrix_trace_pow_eq_sum {N m : ℕ} [NeZero m] (A : Matrix (Fin N) (Fin N) ℝ)
    (hm : 2 ≤ m) :
    (A ^ m).trace = ∑ f : Fin m → Fin N, ∏ i : Fin m, A (f i) (f (i + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  convert matrix_trace_pow_succ_eq_sum A n (by omega)

private lemma symmetric_matrix_trace_even_pow_ge {N k : ℕ} (hN : 1 ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    ((1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A a b) ^ (2 * k) ≤
      (A ^ (2 * k)).trace := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let U := hA.eigenvectorUnitary
  let ev : Fin N → ℝ := hA.eigenvalues
  have hspec : A = (U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal ev *
      star (U : Matrix (Fin N) (Fin N) ℝ) := by
    have h := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, U, ev] using h
  have hpow : A ^ (2 * k) =
      Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal (fun i => ev i ^ (2 * k))) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow, Matrix.diagonal_pow]
    rfl
  have htr : (A ^ (2 * k)).trace = ∑ i : Fin N, ev i ^ (2 * k) := by
    rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    have hUU : star (U : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [hUU, one_mul, Matrix.trace_diagonal]
  let v : Fin N → ℝ := fun _ => 1 / Real.sqrt (N : ℝ)
  have hvv : v ⬝ᵥ v = 1 := by
    simp only [dotProduct, v]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hNpos)
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    field_simp [hsq_ne, ne_of_gt hNpos]
    linarith
  let w : Fin N → ℝ := (star (U : Matrix (Fin N) (Fin N) ℝ)).mulVec v
  have hstar_tr : star (U : Matrix (Fin N) (Fin N) ℝ) =
      Matrix.transpose (U : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hww : ∑ i : Fin N, w i ^ 2 = 1 := by
    have hdot : w ⬝ᵥ w = 1 := by
      dsimp only [w]
      rw [Matrix.dotProduct_mulVec, hstar_tr, Matrix.vecMul_transpose,
        ← hstar_tr, Matrix.mulVec_mulVec]
      have hUU : (U : Matrix (Fin N) (Fin N) ℝ) * star (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
        Unitary.coe_mul_star_self U
      rw [hUU, Matrix.one_mulVec, hvv]
    simpa [dotProduct, sq] using hdot
  have hquad_lhs : v ⬝ᵥ (A.mulVec v) = (1 / (N : ℝ)) * ∑ a : Fin N, ∑ b : Fin N, A a b := by
    simp only [dotProduct, Matrix.mulVec, v, Finset.mul_sum]
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hNpos)
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp [hsq_ne, ne_of_gt hNpos]
    rw [Real.sq_sqrt (le_of_lt hNpos)]
    ring
  have hquad_rhs : v ⬝ᵥ (A.mulVec v) = ∑ i : Fin N, w i ^ 2 * ev i := by
    rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    have hvU : Matrix.vecMul v (U : Matrix (Fin N) (Fin N) ℝ) = w := by
      dsimp only [w]
      rw [hstar_tr, Matrix.mulVec_transpose]
    rw [hvU]
    change w ⬝ᵥ ((Matrix.diagonal ev).mulVec w) = _
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * k)) :=
    (even_two_mul k).convexOn_pow
  have hjensen := hconv.map_sum_le (t := Finset.univ) (w := fun i => w i ^ 2) (p := ev)
    (fun i _ => sq_nonneg (w i)) hww (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjensen
  have hle_tr : ∑ i : Fin N, w i ^ 2 * ev i ^ (2 * k) ≤ ∑ i : Fin N, ev i ^ (2 * k) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hw_le : w i ^ 2 ≤ 1 := by
      rw [← hww]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
    have hev_nn : 0 ≤ ev i ^ (2 * k) := (even_two_mul k).pow_nonneg (ev i)
    nlinarith
  rw [← hquad_lhs, hquad_rhs, htr]
  exact le_trans hjensen hle_tr

private lemma cycleGraph_edgeFinset_eq {m : ℕ} [NeZero m] (hm : 3 ≤ m) :
    (cycleGraph m).edgeFinset = Finset.univ.image (fun i : Fin m => s(i, i + 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_edgeFinset, mem_edgeSet, cycleGraph_adj, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h | h)
      · refine ⟨v, ?_⟩
        have huv : u = v + 1 := by rw [← h]; abel
        rw [huv, Sym2.eq_swap]
      · refine ⟨u, ?_⟩
        have hvu : v = u + 1 := by rw [← h]; abel
        rw [hvu]
    · rintro ⟨i, hi⟩
      rw [Sym2.eq_iff] at hi
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; simp
      · left; simp

private lemma cycleGraph_edgeOf_injective {m : ℕ} [NeZero m] (hm : 3 ≤ m) :
    Function.Injective (fun i : Fin m => s(i, i + 1)) := by
  intro i j hij
  rw [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have htwo : (1 : Fin m) + 1 = 0 := by
      have h : i + ((1 : Fin m) + 1) = i + 0 := by
        rw [← add_assoc, h2, h1, add_zero]
      exact add_left_cancel h
    have hval : ((1 : Fin m) + 1).val = (0 : Fin m).val := congrArg Fin.val htwo
    have h1val : (1 : Fin m).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [Fin.val_add, h1val, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hval
    omega

private lemma cycleGraph_card_edgeFinset {m : ℕ} (hm : 3 ≤ m) :
    (cycleGraph m).edgeFinset.card = m := by
  have : NeZero m := ⟨by omega⟩
  rw [cycleGraph_edgeFinset_eq hm,
    Finset.card_image_of_injective _ (cycleGraph_edgeOf_injective hm),
    Finset.card_univ, Fintype.card_fin]

private lemma cycle_hom_iff {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {W : Type} (G : SimpleGraph W) (f : Fin m → W) :
    (∀ i j, (cycleGraph m).Adj i j → G.Adj (f i) (f j)) ↔
      ∀ i, G.Adj (f i) (f (i + 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  constructor
  · intro hf i
    apply hf
    rw [cycleGraph_adj]
    exact Or.inr (by simp)
  · intro hf i j hij
    rcases cycleGraph_adj.mp hij with h | h
    · have he : i = j + 1 := by rw [← h]; abel
      rw [he]
      exact (hf j).symm
    · have he : j = i + 1 := by rw [← h]; abel
      rw [he]
      exact hf i

end OMA.EvenCycle

open OMA.EvenCycle in
theorem OMA.solution : type_of% @SidorenkoConjecture.sidorenko_conjecture.variants.even_cycle := by
  classical
  intro k hk W _ _ _ G _
  let n := Fintype.card W
  let e : W ≃ Fin n := Fintype.equivFin W
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b =>
    if G.Adj (e.symm a) (e.symm b) then 1 else 0
  have hm : 3 ≤ 2 * k := by omega
  have : NeZero (2 * k) := ⟨by omega⟩
  have hn : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : A.IsHermitian := by
    ext a b
    simp [A, G.adj_comm]
  have hrow (v : W) : (∑ w : W, if G.Adj v w then (1 : ℝ) else 0) = G.degree v := by
    rw [sum_boole, ← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
  have hsum : (∑ a : Fin n, ∑ b : Fin n, A a b) = ∑ v : W, (G.degree v : ℝ) := by
    calc
      _ = ∑ v : W, ∑ w : Fin n, A (e v) w := (Equiv.sum_comp e _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        calc
          _ = ∑ w : W, A (e v) (e w) := (Equiv.sum_comp e _).symm
          _ = _ := by simpa only [A, Matrix.of_apply, Equiv.symm_apply_apply] using hrow v
  have hEdgeDensity : homDensity (completeGraph (Fin 2)) G =
      (∑ a : Fin n, ∑ b : Fin n, A a b) / (n : ℝ) ^ 2 := by
    unfold homDensity
    rw [SidorenkoConjecture.homCount_completeGraph_fin_two_eq_two_mul_card_edgeFinset,
      hsum, ← G.sum_degrees_eq_twice_card_edges]
    simp [n]
  let P (f : Fin (2 * k) → Fin n) := ∀ i, G.Adj (e.symm (f i)) (e.symm (f (i + 1)))
  let countEquiv : (cycleGraph (2 * k) →g G) ≃ { f : Fin (2 * k) → Fin n // P f } :=
    { toFun := fun h => ⟨e ∘ h, by
        simpa only [P, Function.comp_apply, Equiv.symm_apply_apply] using
          (cycle_hom_iff (by omega) G h).mp (fun i j hij => h.map_adj hij)⟩
      invFun := fun f => ⟨e.symm ∘ f.val, by
        intro i j hij
        exact (cycle_hom_iff (by omega) G (e.symm ∘ f.val)).mpr f.property i j hij⟩
      left_inv := fun h => by
        ext i
        exact e.symm_apply_apply (h i)
      right_inv := fun f => by
        apply Subtype.ext
        funext i
        exact e.apply_symm_apply (f.val i) }
  have hcount : (homCount (cycleGraph (2 * k)) G : ℝ) = (A ^ (2 * k)).trace := by
    let decidableP : DecidablePred P := fun _ => Fintype.decidableForallFintype
    have hcard : homCount (cycleGraph (2 * k)) G = (@Finset.filter _ P decidableP univ).card := by
      unfold homCount
      calc
        _ = Fintype.card {f // P f} := Fintype.card_congr countEquiv
        _ = _ := Fintype.card_of_subtype _ (fun f => by simp)
    rw [hcard, matrix_trace_pow_eq_sum A (by omega)]
    simp only [A, Matrix.of_apply, Fintype.prod_boole]
    exact (@Finset.sum_boole _ ℝ _ P decidableP Finset.univ).symm
  have hCycleDensity : homDensity (cycleGraph (2 * k)) G =
      (A ^ (2 * k)).trace / (n : ℝ) ^ (2 * k) := by
    simp only [homDensity, hcount, Fintype.card_fin, n]
  rw [hEdgeDensity, hCycleDensity, cycleGraph_card_edgeFinset hm]
  have hmatrix := symmetric_matrix_trace_even_pow_ge (k := k) hn A hA
  have hscaled := div_le_div_of_nonneg_right hmatrix (pow_nonneg hnR.le (2 * k))
  rw [← div_pow] at hscaled
  have hnormalize :
      ((1 / (n : ℝ)) * ∑ a : Fin n, ∑ b : Fin n, A a b) / n =
        (∑ a : Fin n, ∑ b : Fin n, A a b) / (n : ℝ) ^ 2 := by
    field_simp
  rwa [hnormalize] at hscaled
