import OMAStatements.S_oeis_a209721
import Mathlib

namespace OMA.Helpers_a209721
open OMA.S_oeis_a209721

/-! Iterating a transfer matrix -/

section Gen
variable {K : ℕ} (M : Fin K → Fin K → ℤ)

def stepF (v : Fin K → ℤ) : Fin K → ℤ := fun j => ∑ i, M i j * v i

def itF : ℕ → (Fin K → ℤ) → (Fin K → ℤ)
  | 0, v => v
  | n + 1, v => stepF M (itF n v)

theorem itF_add (m n : ℕ) (v : Fin K → ℤ) : itF M (m + n) v = itF M m (itF M n v) := by
  induction m with
  | zero => simp [itF]
  | succ m ih => rw [show m + 1 + n = (m + n) + 1 by omega]; simp only [itF, ih]

theorem itF_lin (n : ℕ) (v : Fin K → ℤ) (j : Fin K) :
    itF M n v j = ∑ i, v i * itF M n (Pi.single i 1) j := by
  induction n generalizing j with
  | zero =>
    simp only [itF, Pi.single_apply]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  | succ n ih =>
    simp only [itF, stepF]
    simp_rw [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring

def stepL (v : List ℤ) : List ℤ := (List.finRange K).map fun j => ∑ i : Fin K, M i j * v.getD i 0

def itL : ℕ → List ℤ → List ℤ
  | 0, v => v
  | n + 1, v => stepL M (itL n v)

theorem getD_map_finRange (g : Fin K → ℤ) (j : Fin K) :
    ((List.finRange K).map g).getD j 0 = g j := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem itL_eq (n : ℕ) (v : List ℤ) (j : Fin K) :
    (itL M n v).getD j 0 = itF M n (fun i => v.getD i 0) j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [itL, itF, stepL, stepF]
    rw [getD_map_finRange]
    simp_rw [ih]

def basisL (i : Fin K) : List ℤ := (List.finRange K).map fun k => if k = i then 1 else 0

theorem basisL_getD (i k : Fin K) : (basisL i).getD k 0 = (Pi.single i (1 : ℤ) : Fin K → ℤ) k := by
  unfold basisL
  rw [getD_map_finRange, Pi.single_apply]

def stepR (g : Fin K → ℤ) : Fin K → ℤ := fun i => ∑ j, M i j * g j

def itR : ℕ → (Fin K → ℤ) → (Fin K → ℤ)
  | 0, g => g
  | t + 1, g => itR t (stepR M g)

theorem adj (t : ℕ) : ∀ (f v : Fin K → ℤ), ∑ j, f j * itF M t v j = ∑ i, itR M t f i * v i := by
  induction t with
  | zero => intro f v; rfl
  | succ t ih =>
    intro f v
    rw [show itR M (t + 1) f = itR M t (stepR M f) from rfl, ← ih]
    simp only [itF, stepF, stepR, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

def stepRL (g : List ℤ) : List ℤ := (List.finRange K).map fun i => ∑ j : Fin K, M i j * g.getD j 0

def itRL : ℕ → List ℤ → List ℤ
  | 0, g => g
  | t + 1, g => itRL t (stepRL M g)

theorem itRL_eq (t : ℕ) : ∀ (g : List ℤ) (i : Fin K), (itRL M t g).getD i 0 = itR M t (fun j => g.getD j 0) i := by
  induction t with
  | zero => intro g i; rfl
  | succ t ih =>
    intro g i
    rw [show itRL M (t + 1) g = itRL M t (stepRL M g) from rfl, ih]
    show itR M t _ i = itR M t (stepR M _) i
    congr 1
    funext j
    rw [stepRL, getD_map_finRange]
    rfl

/-- the row vector of the recurrence `Σ_l cs_l u(n + m + l) = 0` -/
def chkL (cs fL : List ℤ) (m : ℕ) : Bool :=
  (List.finRange K).all fun i => (∑ l ∈ Finset.range cs.length, cs.getD l 0 * (itRL M (m + l) fL).getD i 0) == 0

theorem rec_of_check (cs fL : List ℤ) (m : ℕ) (h : chkL M cs fL m = true) (v : Fin K → ℤ) (n : ℕ) :
    ∑ l ∈ Finset.range cs.length, cs.getD l 0 * (∑ j : Fin K, fL.getD (j : ℕ) 0 * itF M (n + m + l) v j) = 0 := by
  unfold chkL at h
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, itRL_eq] at h
  have e : ∀ l, ∑ j : Fin K, fL.getD (j : ℕ) 0 * itF M (n + m + l) v j =
      ∑ i, itR M (m + l) (fun j : Fin K => fL.getD (j : ℕ) 0) i * itF M n v i := by
    intro l; rw [show n + m + l = (m + l) + n by omega, itF_add, adj]
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := h i
  calc ∑ l ∈ Finset.range cs.length, cs.getD l 0 * (itR M (m + l) (fun j : Fin K => fL.getD (j : ℕ) 0) i * itF M n v i)
      = (∑ l ∈ Finset.range cs.length, cs.getD l 0 * itR M (m + l) (fun j : Fin K => fL.getD (j : ℕ) 0) i) * itF M n v i := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; ring
    _ = 0 := by rw [this, zero_mul]

end Gen

/-! Rows and the transfer matrix -/

def rowOf (i : Fin 27) : Fin 3 → Fin 3 := fun j => ⟨(i / 3 ^ (j : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem rowOf_inj : ∀ i j : Fin 27, rowOf i = rowOf j → i = j := by decide

theorem rowOf_surj : ∀ r : Fin 3 → Fin 3, ∃ i, rowOf i = r := by decide

abbrev Ok {n : ℕ} (x : Fin (n + 1) → Fin 3 → Fin 3) : Prop := ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)

def cntR (n : ℕ) (i : Fin 27) : ℕ :=
  (Finset.univ.filter fun x : Fin (n + 1) → Fin 3 → Fin 3 => Ok x ∧ x (Fin.last n) = rowOf i).card

theorem collapse (r : Fin 3 → Fin 3) (g : Fin 27 → ℕ) :
    ∑ i : Fin 27, (if r = rowOf i then g i else 0) = g (Classical.choose (rowOf_surj r)) := by
  have hc := Classical.choose_spec (rowOf_surj r)
  rw [Finset.sum_eq_single (Classical.choose (rowOf_surj r))]
  · rw [if_pos hc.symm]
  · intro i _ hi; rw [if_neg (fun h => hi (rowOf_inj _ _ (hc.trans h)).symm)]
  · simp

theorem N_cnt (n : ℕ) : N n = ∑ i, cntR n i := by
  unfold N cntR
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have := collapse (x (Fin.last n)) (fun _ => if Ok x then 1 else 0)
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : Ok x <;> by_cases h2 : x (Fin.last n) = rowOf i <;> simp [h1, h2]

theorem ok_snoc {n : ℕ} (x : Fin (n + 1) → Fin 3 → Fin 3) (r : Fin 3 → Fin 3) :
    Ok (Fin.snoc x r : Fin (n + 2) → Fin 3 → Fin 3) ↔ Ok x ∧ BlockOK (x (Fin.last n)) r := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have := h (Fin.castSucc i)
      rwa [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc] at this
    · have := h (Fin.last n)
      rwa [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] at this
  · rintro ⟨h1, h2⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]; exact h1 i'
    · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]; exact h2

def Mn (i j : Fin 27) : ℕ := if BlockOK (rowOf i) (rowOf j) then 1 else 0

def MT : List (List ℕ) := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

theorem Mn_eq : ∀ i j : Fin 27, Mn i j = (MT.getD i []).getD j 0 := by decide

def Mw (i j : Fin 27) : ℤ := (((MT.getD i []).getD j 0 : ℕ) : ℤ)

theorem cntR_succ (n : ℕ) (j : Fin 27) : cntR (n + 1) j = ∑ i, Mn i j * cntR n i := by
  unfold cntR
  simp only [Finset.card_filter]
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin 3 → Fin 3) _ _ (fun _ => rfl), Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (rowOf j)]
  · have e : ∀ x : Fin (n + 1) → Fin 3 → Fin 3,
        (if Ok ((Fin.snocEquiv fun _ => Fin 3 → Fin 3) (rowOf j, x)) ∧
            (Fin.snocEquiv fun _ => Fin 3 → Fin 3) (rowOf j, x) (Fin.last (n + 1)) = rowOf j then 1 else 0) =
          ∑ i : Fin 27, Mn i j * (if Ok x ∧ x (Fin.last n) = rowOf i then 1 else 0) := by
      intro x
      show (if Ok (Fin.snoc x (rowOf j) : Fin (n + 2) → Fin 3 → Fin 3) ∧
          (Fin.snoc x (rowOf j) : Fin (n + 2) → Fin 3 → Fin 3) (Fin.last (n + 1)) = rowOf j then 1 else 0) = _
      simp only [ok_snoc, Fin.snoc_last, and_true]
      have := collapse (x (Fin.last n)) (fun i => Mn i j * (if Ok x then 1 else 0))
      rw [show (∑ i : Fin 27, Mn i j * (if Ok x ∧ x (Fin.last n) = rowOf i then 1 else 0)) =
          ∑ i : Fin 27, (if x (Fin.last n) = rowOf i then Mn i j * (if Ok x then 1 else 0) else 0) from
        Finset.sum_congr rfl fun i _ => by
          by_cases h1 : Ok x <;> by_cases h2 : x (Fin.last n) = rowOf i <;> simp [h1, h2]]
      rw [this]
      have hc := Classical.choose_spec (rowOf_surj (x (Fin.last n)))
      unfold Mn
      rw [hc]
      by_cases h1 : Ok x
      · by_cases h3 : BlockOK (x (Fin.last n)) (rowOf j)
        · rw [if_pos ⟨h1, h3⟩, if_pos h3, if_pos h1]
        · rw [if_neg (fun h => h3 h.2), if_neg h3, zero_mul]
      · rw [if_neg (fun h => h1 h.1), if_neg h1, mul_zero]
    simp only [e, Finset.mul_sum]
    rw [Finset.sum_comm]
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    show ¬ (Ok (Fin.snoc x r : Fin (n + 2) → Fin 3 → Fin 3) ∧
      (Fin.snoc x r : Fin (n + 2) → Fin 3 → Fin 3) (Fin.last (n + 1)) = rowOf j)
    rw [Fin.snoc_last]
    exact fun h => hr h.2
  · simp

theorem cntR_zero : ∀ i : Fin 27, cntR 0 i = 1 := by decide

def onesL : List ℤ := (List.finRange 27).map fun _ => 1

theorem ones_get : ∀ i : Fin 27, onesL.getD i 0 = 1 := by decide

def v1 : Fin 27 → ℤ := fun i => onesL.getD i 0

theorem cntR_it (n : ℕ) : (fun i => (cntR n i : ℤ)) = itF Mw n v1 := by
  induction n with
  | zero => funext i; rw [cntR_zero]; show ((1 : ℕ) : ℤ) = onesL.getD i 0; rw [ones_get]; rfl
  | succ n ih =>
    funext j
    show (cntR (n + 1) j : ℤ) = ∑ i, Mw i j * itF Mw n v1 i
    rw [← ih, cntR_succ]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Mn_eq]; rfl

theorem N_it (n : ℕ) : (N n : ℤ) = ∑ j : Fin 27, onesL.getD (j : ℕ) 0 * itF Mw n v1 j := by
  rw [N_cnt]; push_cast; rw [← cntR_it]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ones_get, one_mul]

theorem chkN : chkL Mw [2, -2, -1, 1] onesL 1 = true := by decide +kernel

theorem recN (t : ℕ) : (N (t + 4) : ℤ) = N (t + 3) + 2 * N (t + 2) - 2 * N (t + 1) := by
  have := rec_of_check Mw [2, -2, -1, 1] onesL 1 chkN v1 t
  simp only [← N_it] at this
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero] at this
  simp only [List.getD_cons_zero, List.getD_cons_succ] at this
  rw [show t + 1 + 0 = t + 1 by omega, show t + 1 + 1 = t + 2 by omega, show t + 1 + 2 = t + 3 by omega,
    show t + 1 + 3 = t + 4 by omega] at this
  linarith

theorem N_val (n : ℕ) : (N n : ℤ) = ∑ j : Fin 27, onesL.getD (j : ℕ) 0 * (itL Mw n onesL).getD j 0 := by
  rw [N_it]; refine Finset.sum_congr rfl fun j _ => ?_; rw [itL_eq]; rfl

theorem N1 : (N 1 : ℤ) = 12 := by rw [N_val]; decide +kernel
theorem N2 : (N 2 : ℤ) = 16 := by rw [N_val]; decide +kernel
theorem N3 : (N 3 : ℤ) = 20 := by rw [N_val]; decide +kernel

theorem two_step : ∀ m : ℕ, 1 ≤ m → (N (m + 2) : ℤ) = 2 * N m - 4 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases (by omega : m = 1 ∨ m = 2 ∨ 3 ≤ m) with rfl | rfl | h
    · rw [N3, N1]; norm_num
    · have := recN 0; rw [N3, N2, N1] at this; rw [show 2 + 2 = 0 + 4 from rfl, this, N2]; norm_num
    · have h1 := ih (m - 2) (by omega) (by omega)
      have h2 := ih (m - 1) (by omega) (by omega)
      have r := recN (m - 2)
      rw [show m - 2 + 2 = m by omega] at h1
      rw [show m - 1 + 2 = m + 1 by omega] at h2
      rw [show m - 2 + 4 = m + 2 by omega, show m - 2 + 3 = m + 1 by omega, show m - 2 + 2 = m by omega,
        show m - 2 + 1 = m - 1 by omega] at r
      linarith

theorem closed (t : ℕ) : (N (2 * t + 1) : ℤ) = 4 * 2 ^ (t + 1) + 4 ∧ (N (2 * t + 2) : ℤ) = 12 * 2 ^ t + 4 := by
  induction t with
  | zero => exact ⟨N1, N2⟩
  | succ t ih =>
    constructor
    · rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by ring, two_step _ (by omega), ih.1, pow_succ]; ring
    · rw [show 2 * (t + 1) + 2 = (2 * t + 2) + 2 by ring, two_step _ (by omega), ih.2, pow_succ]; ring

def p (x : ℕ) : Prop := ∃ k : ℕ, x = 2 ^ k ∨ x = 3 * 2 ^ k

open Classical in
theorem gap1 (k y : ℕ) (hy : y < 2 ^ k) : p (2 ^ (k + 1) + y) ↔ y = 0 := by
  constructor
  · rintro ⟨j, hj | hj⟩
    · by_contra h0
      have h1 : 2 ^ (k + 1) < 2 ^ j := by omega
      have h2 : 2 ^ j < 2 ^ (k + 2) := by rw [pow_succ, pow_succ] at *; omega
      rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h1 h2
      omega
    · by_contra h0
      have h1 : 2 ^ (k + 1) < 3 * 2 ^ j := by omega
      have h2 : 3 * 2 ^ j < 3 * 2 ^ k := by rw [pow_succ] at *; omega
      have hj : j < k := by
        have : 2 ^ j < 2 ^ k := by omega
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
      have : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hj
      rw [pow_succ] at this h1
      omega
  · rintro rfl; exact ⟨k + 1, Or.inl (by simp)⟩

open Classical in
theorem gap2 (k y : ℕ) (hy : y < 2 ^ k) : p (3 * 2 ^ k + y) ↔ y = 0 := by
  constructor
  · rintro ⟨j, hj | hj⟩
    · by_contra h0
      have h1 : 3 * 2 ^ k < 2 ^ j := by omega
      have h2 : 2 ^ j < 2 ^ (k + 2) := by rw [pow_succ, pow_succ] at *; omega
      have h3 : 2 ^ (k + 1) < 2 ^ j := by rw [pow_succ]; omega
      rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h2 h3
      omega
    · by_contra h0
      have h1 : 3 * 2 ^ k < 3 * 2 ^ j := by omega
      have h2 : 3 * 2 ^ j < 2 ^ (k + 2) := by rw [pow_succ, pow_succ] at *; omega
      have hj : k < j := by
        have : 2 ^ k < 2 ^ j := by omega
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
      have : 2 ^ (k + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      rw [pow_succ, pow_succ] at *
      omega
  · rintro rfl; exact ⟨k, Or.inr (by simp)⟩

open Classical in
theorem count_one (q : ℕ → Prop) [DecidablePred q] (m : ℕ) (hm : 0 < m) (h : ∀ y < m, q y ↔ y = 0) :
    Nat.count q m = 1 := by
  rw [Nat.count_eq_card_filter_range]
  rw [show (Finset.range m).filter q = {0} from ?_]
  · simp
  · ext y; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact (h y h1).mp h2
    · rintro rfl; exact ⟨hm, (h 0 hm).mpr rfl⟩

open Classical in
theorem counts (k : ℕ) : Nat.count p (2 ^ (k + 1)) = 2 * k + 1 ∧ Nat.count p (3 * 2 ^ k) = 2 * k + 2 := by
  induction k with
  | zero =>
    have h0 : ¬ p 0 := by rintro ⟨j, hj | hj⟩ <;> have := pow_pos (by norm_num : 0 < 2) j <;> omega
    have h1 : p 1 := ⟨0, Or.inl rfl⟩
    have h2 : p 2 := ⟨1, Or.inl rfl⟩
    refine ⟨?_, ?_⟩
    · simp [Nat.count_succ, h0, h1]
    · simp [Nat.count_succ, h0, h1, h2]
  | succ k ih =>
    have hA : Nat.count p (3 * 2 ^ k) = Nat.count p (2 ^ (k + 1)) + 1 := by
      rw [show 3 * 2 ^ k = 2 ^ (k + 1) + 2 ^ k by rw [pow_succ]; ring, Nat.count_add]
      rw [count_one _ _ (by positivity) (fun y hy => gap1 k y hy)]
    have hB : Nat.count p (2 ^ (k + 2)) = Nat.count p (3 * 2 ^ k) + 1 := by
      rw [show 2 ^ (k + 2) = 3 * 2 ^ k + 2 ^ k by rw [pow_succ, pow_succ]; ring, Nat.count_add]
      rw [count_one _ _ (by positivity) (fun y hy => gap2 k y hy)]
    have hC : Nat.count p (3 * 2 ^ (k + 1)) = Nat.count p (2 ^ (k + 2)) + 1 := by
      rw [show 3 * 2 ^ (k + 1) = 2 ^ (k + 2) + 2 ^ (k + 1) by rw [pow_succ, pow_succ]; ring, Nat.count_add]
      rw [count_one _ _ (by positivity) (fun y hy => gap1 (k + 1) y hy)]
    rw [show k + 1 + 1 = k + 2 by ring]
    omega

theorem nth_odd (k : ℕ) : Nat.nth p (2 * k + 1) = 2 ^ (k + 1) := by
  classical
  rw [← (counts k).1]; exact Nat.nth_count ⟨k + 1, Or.inl rfl⟩

theorem nth_even (k : ℕ) : Nat.nth p (2 * k + 2) = 3 * 2 ^ k := by
  classical
  rw [← (counts k).2]; exact Nat.nth_count ⟨k, Or.inr rfl⟩


theorem A029744_eq (n : ℕ) : A029744 (n + 1) = Nat.nth p n := by
  unfold A029744 p; rfl

theorem a_hardin (n : ℕ) (hn : 4 ≤ n) : a n = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) := by
  have r := recN (n - 4)
  rw [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega, show n - 4 + 2 = n - 2 by omega,
    show n - 4 + 1 = n - 3 by omega] at r
  unfold a
  have r' : ((N n : ℤ) : ℚ) = ((N (n - 1) + 2 * N (n - 2) - 2 * N (n - 3) : ℤ) : ℚ) := by rw [r]
  push_cast at r'
  rw [r']; ring

theorem a_peterson (n : ℕ) (hn : 3 ≤ n) : a n = 2 * a (n - 2) - 1 := by
  have r := two_step (n - 2) (by omega)
  rw [show n - 2 + 2 = n by omega] at r
  unfold a
  have r' : ((N n : ℤ) : ℚ) = ((2 * N (n - 2) - 4 : ℤ) : ℚ) := by rw [r]
  push_cast at r'
  rw [r']; ring

theorem a_beck (n : ℕ) (hn : 1 ≤ n) : a n = A029744 (n + 1) + 1 := by
  rw [A029744_eq]
  unfold a
  obtain ⟨t, rfl | rfl⟩ : ∃ t, n = 2 * t + 1 ∨ n = 2 * t + 2 := ⟨(n - 1) / 2, by omega⟩
  · rw [nth_odd]
    have := (closed t).1
    have h : ((N (2 * t + 1) : ℤ) : ℚ) = ((4 * 2 ^ (t + 1) + 4 : ℤ) : ℚ) := by rw [this]
    push_cast at h ⊢
    rw [h]; ring
  · rw [nth_even]
    have := (closed t).2
    have h : ((N (2 * t + 2) : ℤ) : ℚ) = ((12 * 2 ^ t + 4 : ℤ) : ℚ) := by rw [this]
    push_cast at h ⊢
    rw [h]; ring

theorem a1 : a 1 = 3 := by
  unfold a; have h : ((N 1 : ℤ) : ℚ) = ((12 : ℤ) : ℚ) := by rw [N1]
  push_cast at h; rw [h]; norm_num
theorem a2 : a 2 = 4 := by
  unfold a; have h : ((N 2 : ℤ) : ℚ) = ((16 : ℤ) : ℚ) := by rw [N2]
  push_cast at h; rw [h]; norm_num
theorem a3 : a 3 = 5 := by
  unfold a; have h : ((N 3 : ℤ) : ℚ) = ((20 : ℤ) : ℚ) := by rw [N3]
  push_cast at h; rw [h]; norm_num

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((1 - X) * (1 - 2 * X ^ 2)) =
    X * (3 + X - 5 * X ^ 2) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, f = fun n => if n = 0 then (0 : ℚ) else a n := ⟨_, rfl⟩
  have g0 : f 0 = 0 := by simp [hf]
  have g1 : f 1 = 3 := by rw [hf]; simp only [one_ne_zero, if_false]; exact a1
  have g2 : f 2 = 4 := by rw [hf]; simp only [OfNat.ofNat_ne_zero, if_false]; exact a2
  have g3 : f 3 = 5 := by rw [hf]; simp only [OfNat.ofNat_ne_zero, if_false]; exact a3
  have grec : ∀ k, 4 ≤ k → f k = f (k - 1) + 2 * f (k - 2) - 2 * f (k - 3) := by
    intro k hk
    rw [hf]; simp only [show k ≠ 0 by omega, show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega,
      show k - 3 ≠ 0 by omega, if_false]
    exact a_hardin k hk
  rw [← hf]
  clear hf
  set F : PowerSeries ℚ := PowerSeries.mk f with hF
  have hD : F * ((1 - X) * (1 - 2 * X ^ 2)) = C (1 : ℚ) * (F * X ^ 0) - C (1 : ℚ) * (F * X ^ 1) -
      C (2 : ℚ) * (F * X ^ 2) + C (2 : ℚ) * (F * X ^ 3) := by
    simp only [map_ofNat, map_one]; ring
  have hN : (X * (3 + X - 5 * X ^ 2) : PowerSeries ℚ) = C (3 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 -
      C (5 : ℚ) * X ^ 3 := by
    simp only [map_ofNat, map_one]; ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hF, coeff_mk, Nat.sub_zero]
  rcases Nat.lt_or_ge k 4 with h | h
  · interval_cases k <;> simp [g0, g1, g2, g3] <;> norm_num
  · simp only [show 0 ≤ k by omega, show 1 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega,
      coeff_C, show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega, show k - 3 ≠ 0 by omega, if_true, if_false]
    linear_combination grec k h

end OMA.Helpers_a209721

open OMA.Helpers_a209721 in
theorem OMA.solution : type_of% @OMA.S_oeis_a209721.main :=
  ⟨a_hardin, gf, a_peterson, a_beck⟩
