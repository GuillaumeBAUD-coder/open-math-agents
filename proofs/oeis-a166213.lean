import OMAStatements.S_oeis_a166213
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finite.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# OEIS A166213: five orbit values and a weighted cone decomposition

Credit: @CubeJerry.

Rotational symmetry reduces the fifteen array entries to five orbit values.
The two essential neighborhood inequalities define a cone. Splitting its
remaining bounded coordinate into three intervals gives weighted compositions;
the last interval contributes two copies. Their geometric generating functions
prove both Colin Barker conjectures, including all initial coefficients.
-/

namespace A166213Proof
open OMA.S_oeis_a166213
open Finset

-- Five rotation orbits, with one representative from each.
def representative : Fin 5 → Cell :=
  ![⟨(0,0,4), by decide⟩, ⟨(0,1,3), by decide⟩, ⟨(0,2,2), by decide⟩,
    ⟨(0,3,1), by decide⟩, ⟨(1,1,2), by decide⟩]

def cellMap (p : Fin 5 × Fin 3) : Cell := (rot^[p.2.val]) (representative p.1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma cellMap_bijective : Function.Bijective cellMap := by decide

noncomputable def cellEquiv : (Fin 5 × Fin 3) ≃ Cell :=
  Equiv.ofBijective cellMap cellMap_bijective

lemma cellMap_zero (i : Fin 5) : cellMap (i,0) = representative i := rfl

set_option maxRecDepth 10000 in
lemma rot_cellMap : ∀ i : Fin 5, ∀ j : Fin 3,
    rot (cellMap (i,j)) = cellMap (i,j+1) := by decide

-- The array constraints after passing to its five orbit values.
def orbitValid (n : ℕ) (v : Fin 5 → Fin (n+1)) : Prop :=
  (v 0 : ℕ) + v 1 + v 2 + v 3 + v 4 ≤ n ∧
  (v 1 : ℕ) + v 3 + 2 * v 2 + 3 * v 4 ≤ n


noncomputable def inflate {n : ℕ} (v : Fin 5 → Fin (n+1)) (p : Cell) : Fin (n+1) :=
  v (cellEquiv.symm p).1

lemma inflate_cellMap {n : ℕ} (v : Fin 5 → Fin (n+1)) (i : Fin 5) (j : Fin 3) :
    inflate v (cellMap (i,j)) = v i := by
  change v (cellEquiv.symm (cellEquiv (i,j))).1 = v i
  simp

lemma inflate_symmetric {n : ℕ} (v : Fin 5 → Fin (n+1)) :
    ∀ p : Cell, inflate v (rot p) = inflate v p := by
  intro p
  obtain ⟨⟨i,j⟩,rfl⟩ := cellMap_bijective.surjective p
  rw [rot_cellMap, inflate_cellMap, inflate_cellMap]

lemma symmetric_cellMap {n : ℕ} (f : Cell → Fin (n+1))
    (hf : ∀ p, f (rot p) = f p) (i : Fin 5) (j : Fin 3) :
    f (cellMap (i,j)) = f (representative i) := by
  fin_cases j <;> simp [cellMap, Function.iterate_succ_apply', hf]

noncomputable def extract {n : ℕ} (f : Cell → Fin (n+1)) (i : Fin 5) : Fin (n+1) :=
  f (representative i)

lemma inflate_extract {n : ℕ} (f : Cell → Fin (n+1))
    (hf : ∀ p, f (rot p) = f p) : inflate (extract f) = f := by
  funext p
  obtain ⟨⟨i,j⟩,rfl⟩ := cellMap_bijective.surjective p
  rw [inflate_cellMap, symmetric_cellMap f hf]
  rfl

lemma extract_inflate {n : ℕ} (v : Fin 5 → Fin (n+1)) : extract (inflate v) = v := by
  funext i
  exact inflate_cellMap v i 0

def profileSum (v : Fin 5 → ℕ) : Fin 5 → ℕ :=
  ![v 0 + v 1 + v 3, v 0 + v 1 + v 2 + v 3 + v 4,
    v 1 + v 2 + v 3 + 2*v 4, v 0 + v 1 + v 2 + v 3 + v 4,
    v 1 + 2*v 2 + v 3 + 3*v 4]

lemma nbrSum_inflate {n : ℕ} (v : Fin 5 → Fin (n+1)) (p : Cell) :
    nbrSum (inflate v) p = ∑ i : Fin 5, ∑ j : Fin 3,
      if cellMap (i,j) = p ∨ adj p (cellMap (i,j)) then (v i : ℕ) else 0 := by
  unfold nbrSum
  rw [← cellEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change (if cellMap (i,j) = p ∨ adj p (cellMap (i,j)) then _ else _) = _
  have hh : inflate v (cellEquiv (i,j)) = v i := inflate_cellMap v i j
  rw [hh]

set_option maxHeartbeats 5000000 in
lemma nbrSum_profile {n : ℕ} (v : Fin 5 → Fin (n+1)) (i : Fin 5) (j : Fin 3) :
    nbrSum (inflate v) (cellMap (i,j)) = profileSum (fun k => v k) i := by
  rw [nbrSum_inflate]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, cellMap, representative, rot, adj, profileSum,
      Function.iterate_succ_apply'] <;> omega

lemma inflate_valid_iff {n : ℕ} (v : Fin 5 → Fin (n+1)) :
    valid n (inflate v) ↔ orbitValid n v := by
  constructor
  · intro h
    have h1 := h.2 (cellMap (1,0))
    have h4 := h.2 (cellMap (4,0))
    rw [nbrSum_profile] at h1 h4
    simpa [orbitValid, profileSum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro h1 h4
  · intro h
    refine ⟨inflate_symmetric v, ?_⟩
    intro p
    obtain ⟨⟨i,j⟩,rfl⟩ := cellMap_bijective.surjective p
    rw [nbrSum_profile]
    fin_cases i <;> simp [profileSum] <;>
      dsimp [orbitValid] at h <;> omega


instance (n : ℕ) (v : Fin 5 → Fin (n+1)) : Decidable (orbitValid n v) := by
  unfold orbitValid
  infer_instance

abbrev Orbit (n : ℕ) := {v : Fin 5 → Fin (n+1) // orbitValid n v}

noncomputable def arrayOrbitEquiv (n : ℕ) :
    {f : Cell → Fin (n+1) // valid n f} ≃ Orbit n where
  toFun f := ⟨extract f.val, (inflate_valid_iff _).mp (by rw [inflate_extract _ f.property.1]; exact f.property)⟩
  invFun v := ⟨inflate v.val, (inflate_valid_iff _).mpr v.property⟩
  left_inv f := Subtype.ext (inflate_extract f.val f.property.1)
  right_inv v := Subtype.ext (extract_inflate v.val)

lemma a_eq_card_orbit (n : ℕ) : a n = Nat.card (Orbit n) := by
  rw [a, ← Fintype.card_subtype]
  rw [Fintype.card_congr (arrayOrbitEquiv n), Nat.card_eq_fintype_card]

-- A weighted composition, with an optional initial offset.
abbrev WComp {m : ℕ} (w : Fin m → ℕ) (c n : ℕ) :=
  {v : Fin m → ℕ // c + ∑ i, w i * v i = n}

lemma wcomp_bound {m : ℕ} {w : Fin m → ℕ} {c n : ℕ}
    (hw : ∀ i, 0 < w i) (v : WComp w c n) (i : Fin m) : v.val i ≤ n := by
  have h := single_le_sum (fun j _ => Nat.zero_le (w j * v.val j)) (mem_univ i)
  have hp := v.property
  have hi := hw i
  nlinarith

lemma wcomp_finite {m : ℕ} (w : Fin m → ℕ) (c n : ℕ) (hw : ∀ i, 0 < w i) :
    Finite (WComp w c n) := by
  let f : WComp w c n → (Fin m → Fin (n+1)) :=
    fun v i => ⟨v.val i, Nat.lt_succ_of_le (wcomp_bound hw v i)⟩
  apply Finite.of_injective f
  intro v z h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

def weights1 : Fin 6 → ℕ := ![1,1,2,3,1,1]
def weights2 : Fin 6 → ℕ := ![1,1,2,2,3,1]
def weights3 : Fin 6 → ℕ := ![1,1,2,3,3,1]

lemma weights1_pos : ∀ i, 0 < weights1 i := by decide
lemma weights2_pos : ∀ i, 0 < weights2 i := by decide
lemma weights3_pos : ∀ i, 0 < weights3 i := by decide

instance (c n : ℕ) : Finite (WComp weights1 c n) := wcomp_finite _ _ _ weights1_pos
instance (c n : ℕ) : Finite (WComp weights2 c n) := wcomp_finite _ _ _ weights2_pos
instance (c n : ℕ) : Finite (WComp weights3 c n) := wcomp_finite _ _ _ weights3_pos

lemma wcomp1_eq {c n : ℕ} (v : WComp weights1 c n) :
    c + v.val 0 + v.val 1 + 2*v.val 2 + 3*v.val 3 + v.val 4 + v.val 5 = n := by
  have h := v.property
  simpa [weights1, Fin.sum_univ_succ, Nat.add_assoc] using h

lemma wcomp2_eq {c n : ℕ} (v : WComp weights2 c n) :
    c + v.val 0 + v.val 1 + 2*v.val 2 + 2*v.val 3 + 3*v.val 4 + v.val 5 = n := by
  have h := v.property
  simpa [weights2, Fin.sum_univ_succ, Nat.add_assoc] using h

lemma wcomp3_eq {c n : ℕ} (v : WComp weights3 c n) :
    c + v.val 0 + v.val 1 + 2*v.val 2 + 3*v.val 3 + 3*v.val 4 + v.val 5 = n := by
  have h := v.property
  simpa [weights3, Fin.sum_univ_succ, Nat.add_assoc] using h

-- The four branches of the cone decomposition (the third summand has two copies).
abbrev Pieces (n : ℕ) :=
  WComp weights1 0 n ⊕ (WComp weights2 2 n ⊕ (Fin 2 × WComp weights3 3 n))

def slack {n : ℕ} (v : Orbit n) : ℕ :=
  n - v.val 1 - v.val 3 - 2*v.val 2 - 3*v.val 4

lemma slack_eq {n : ℕ} (v : Orbit n) :
    slack v + v.val 1 + v.val 3 + 2*v.val 2 + 3*v.val 4 = n := by
  have h := v.property.2
  dsimp [slack]
  omega

lemma orbit_bound {n : ℕ} (v : Orbit n) : (v.val 0 : ℕ) ≤ slack v + v.val 2 + 2*v.val 4 := by
  have h := v.property.1
  have hs := slack_eq v
  omega

def splitOrbit {n : ℕ} (v : Orbit n) : Pieces n :=
  if h0 : (v.val 0 : ℕ) ≤ slack v then
    Sum.inl ⟨![(v.val 1 : ℕ),v.val 3,v.val 2,v.val 4,v.val 0,slack v-v.val 0], by
      have hs := slack_eq v
      simp [weights1, Fin.sum_univ_succ]
      omega⟩
  else if h1 : (v.val 0 : ℕ) ≤ slack v + v.val 2 then
    Sum.inr (Sum.inl ⟨![(v.val 1 : ℕ),v.val 3,v.val 0-slack v-1,
        v.val 2-(v.val 0-slack v-1)-1,v.val 4,slack v], by
      have hs := slack_eq v
      simp [weights2, Fin.sum_univ_succ]
      omega⟩)
  else
    Sum.inr (Sum.inr (⟨(v.val 0-slack v-v.val 2-1)%2, Nat.mod_lt _ (by decide)⟩,
      ⟨![(v.val 1 : ℕ),v.val 3,v.val 2,(v.val 0-slack v-v.val 2-1)/2,
        v.val 4-(v.val 0-slack v-v.val 2-1)/2-1,slack v], by
        have hs := slack_eq v
        have hb := orbit_bound v
        simp [weights3, Fin.sum_univ_succ]
        omega⟩))

def mkOrbit (n A B C D E : ℕ) (h1 : A+B+C+D+E ≤ n) (h2 : B+D+2*C+3*E ≤ n) :
    Orbit n :=
  ⟨![⟨A,by omega⟩, ⟨B,by omega⟩, ⟨C,by omega⟩, ⟨D,by omega⟩, ⟨E,by omega⟩], by
    simpa [orbitValid] using And.intro h1 h2⟩

def joinPieces {n : ℕ} : Pieces n → Orbit n
  | Sum.inl v =>
      mkOrbit n (v.val 4) (v.val 0) (v.val 2) (v.val 1) (v.val 3)
        (by have h := wcomp1_eq v; omega) (by have h := wcomp1_eq v; omega)
  | Sum.inr (Sum.inl v) =>
      mkOrbit n (v.val 5+v.val 2+1) (v.val 0) (v.val 2+v.val 3+1) (v.val 1) (v.val 4)
        (by have h := wcomp2_eq v; omega) (by have h := wcomp2_eq v; omega)
  | Sum.inr (Sum.inr (e,v)) =>
      mkOrbit n (v.val 5+v.val 2+2*v.val 3+e.val+1) (v.val 0) (v.val 2) (v.val 1)
        (v.val 3+v.val 4+1) (by have h := wcomp3_eq v; have he := e.isLt; omega)
        (by have h := wcomp3_eq v; omega)


lemma join_split {n : ℕ} (v : Orbit n) : joinPieces (splitOrbit v) = v := by
  have hs := slack_eq v
  have hb := orbit_bound v
  unfold splitOrbit
  split_ifs with h0 h1 <;>
    apply Subtype.ext <;> funext i <;> apply Fin.ext <;>
    fin_cases i <;> simp [joinPieces, mkOrbit] <;> omega

lemma slack_join1 {n : ℕ} (v : WComp weights1 0 n) :
    slack (joinPieces (Sum.inl v)) = v.val 4 + v.val 5 := by
  have h := wcomp1_eq v
  simp [slack, joinPieces, mkOrbit]
  omega

lemma slack_join2 {n : ℕ} (v : WComp weights2 2 n) :
    slack (joinPieces (Sum.inr (Sum.inl v))) = v.val 5 := by
  have h := wcomp2_eq v
  simp [slack, joinPieces, mkOrbit]
  omega

lemma slack_join3 {n : ℕ} (e : Fin 2) (v : WComp weights3 3 n) :
    slack (joinPieces (Sum.inr (Sum.inr (e,v)))) = v.val 5 := by
  have h := wcomp3_eq v
  simp [slack, joinPieces, mkOrbit]
  omega

lemma split_join1 {n : ℕ} (v : WComp weights1 0 n) :
    splitOrbit (joinPieces (Sum.inl v)) = Sum.inl v := by
  have hs := slack_join1 v
  have h0 : ((joinPieces (Sum.inl v)).val 0 : ℕ) ≤ slack (joinPieces (Sum.inl v)) := by
    simp only [hs] <;> simp [joinPieces, mkOrbit]
  rw [splitOrbit, dif_pos h0]
  apply congrArg Sum.inl
  apply Subtype.ext
  funext i
  fin_cases i <;> simp only [hs] <;> simp [joinPieces, mkOrbit]

lemma split_join2 {n : ℕ} (v : WComp weights2 2 n) :
    splitOrbit (joinPieces (Sum.inr (Sum.inl v))) = Sum.inr (Sum.inl v) := by
  have hs := slack_join2 v
  have h0 : ¬ ((joinPieces (Sum.inr (Sum.inl v))).val 0 : ℕ) ≤
      slack (joinPieces (Sum.inr (Sum.inl v))) := by
    simp only [hs] <;> simp [joinPieces, mkOrbit]
  have h1 : ((joinPieces (Sum.inr (Sum.inl v))).val 0 : ℕ) ≤
      slack (joinPieces (Sum.inr (Sum.inl v))) + (joinPieces (Sum.inr (Sum.inl v))).val 2 := by
    simp only [hs] <;> simp [joinPieces, mkOrbit]
  rw [splitOrbit, dif_neg h0, dif_pos h1]
  apply congrArg Sum.inr
  apply congrArg Sum.inl
  apply Subtype.ext
  funext i
  fin_cases i <;> simp only [hs] <;> simp [joinPieces, mkOrbit] <;> omega

lemma split_join3 {n : ℕ} (e : Fin 2) (v : WComp weights3 3 n) :
    splitOrbit (joinPieces (Sum.inr (Sum.inr (e,v)))) = Sum.inr (Sum.inr (e,v)) := by
  have hs := slack_join3 e v
  have he := e.isLt
  have h0 : ¬ ((joinPieces (Sum.inr (Sum.inr (e,v)))).val 0 : ℕ) ≤
      slack (joinPieces (Sum.inr (Sum.inr (e,v)))) := by
    simp only [hs] <;> simp [joinPieces, mkOrbit]
    omega
  have h1 : ¬ ((joinPieces (Sum.inr (Sum.inr (e,v)))).val 0 : ℕ) ≤
      slack (joinPieces (Sum.inr (Sum.inr (e,v)))) + (joinPieces (Sum.inr (Sum.inr (e,v)))).val 2 := by
    simp only [hs] <;> simp [joinPieces, mkOrbit]
    omega
  rw [splitOrbit, dif_neg h0, dif_neg h1]
  apply congrArg Sum.inr
  apply congrArg Sum.inr
  apply Prod.ext
  · apply Fin.ext
    simp only [hs] <;> simp [joinPieces, mkOrbit]
    omega
  · apply Subtype.ext
    funext i
    fin_cases i <;> simp only [hs] <;> simp [joinPieces, mkOrbit] <;> omega

def coneEquiv (n : ℕ) : Orbit n ≃ Pieces n where
  toFun := splitOrbit
  invFun := joinPieces
  left_inv := join_split
  right_inv := by
    intro z
    rcases z with v | v | ⟨e,v⟩
    · exact split_join1 v
    · exact split_join2 v
    · exact split_join3 e v

lemma a_eq_compositions (n : ℕ) :
    a n = Nat.card (WComp weights1 0 n) + Nat.card (WComp weights2 2 n) +
      2 * Nat.card (WComp weights3 3 n) := by
  rw [a_eq_card_orbit, Nat.card_congr (coneEquiv n)]
  change Nat.card (WComp weights1 0 n ⊕ (WComp weights2 2 n ⊕ (Fin 2 × WComp weights3 3 n))) = _
  rw [Nat.card_sum, Nat.card_sum, Nat.card_prod, Nat.card_fin]
  omega

-- Coefficients of products of geometric series count weighted compositions.
lemma wcomp_zero_coeff {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ)
    (G : ℕ → PowerSeries ℚ)
    (hG : ∀ d k, PowerSeries.coeff k (G d) = if d ∣ k then 1 else 0) :
    (Nat.card (WComp w 0 n) : ℚ) = PowerSeries.coeff n (∏ i, G (w i)) := by
  classical
  let D := (Finset.piAntidiag (univ : Finset (Fin m)) n).filter (fun v => ∀ i, w i ∣ v i)
  have e : WComp w 0 n ≃ {v // v ∈ D} :=
    { toFun := fun v => ⟨fun i => w i * v.val i, by
        simp only [D, mem_filter, mem_piAntidiag, mem_univ, implies_true, and_true]
        exact ⟨by simpa using v.property, fun i => dvd_mul_right _ _⟩⟩
      invFun := fun v => ⟨fun i => v.val i / w i, by
        have hv := (mem_filter.mp v.property)
        have hs := (mem_piAntidiag.mp hv.1).1
        simpa only [zero_add, Nat.mul_div_cancel' (hv.2 _)] using hs⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext i
        exact Nat.mul_div_cancel_left _ (hw i)
      right_inv := fun v => by
        apply Subtype.ext
        funext i
        exact Nat.mul_div_cancel' ((mem_filter.mp v.property).2 i) }
  have boolprod (v : Fin m → ℕ) :
      (∏ i, (if w i ∣ v i then (1 : ℚ) else 0)) = if ∀ i, w i ∣ v i then 1 else 0 := by
    by_cases h : ∀ i, w i ∣ v i
    · simp [h]
    · rw [if_neg h]
      obtain ⟨i,hi⟩ := not_forall.mp h
      exact prod_eq_zero (mem_univ i) (by simp [hi])
  calc
    (Nat.card (WComp w 0 n) : ℚ) = (D.card : ℚ) := by
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = ∑ v ∈ Finset.piAntidiag (univ : Finset (Fin m)) n,
        if ∀ i, w i ∣ v i then (1 : ℚ) else 0 := by
      simp only [D, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ = PowerSeries.coeff n (∏ i, G (w i)) := by
      rw [PowerSeries.coeff_prod]
      simp only [Finset.finsuppAntidiag, Finset.sum_map]
      simp only [hG]
      simp only [boolprod]
      change _ = ∑ x ∈ (Finset.piAntidiag (univ : Finset (Fin m)) n).attach,
        if ∀ i, w i ∣ x.val i then (1 : ℚ) else 0
      exact (Finset.sum_attach _ (fun v : Fin m → ℕ => if ∀ i, w i ∣ v i then (1 : ℚ) else 0)).symm

lemma wcomp_coeff {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (c n : ℕ)
    (G : ℕ → PowerSeries ℚ)
    (hG : ∀ d k, PowerSeries.coeff k (G d) = if d ∣ k then 1 else 0) :
    (Nat.card (WComp w c n) : ℚ) =
      PowerSeries.coeff n (PowerSeries.X^c * ∏ i, G (w i)) := by
  classical
  by_cases hc : c ≤ n
  · have e : WComp w c n ≃ WComp w 0 (n-c) :=
      { toFun := fun v => ⟨v.val, by have h := v.property; omega⟩
        invFun := fun v => ⟨v.val, by have h := v.property; omega⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, wcomp_zero_coeff w hw (n-c) G hG]
    simp only [PowerSeries.coeff_X_pow_mul', hc, if_true]
  · letI : IsEmpty (WComp w c n) := ⟨fun v => by have h := v.property; omega⟩
    simp [PowerSeries.coeff_X_pow_mul', hc]

end A166213Proof




namespace A166213Proof
open OMA.S_oeis_a166213 PowerSeries

lemma series_eq_general (G : ℕ → PowerSeries ℚ)
    (hG : ∀ d k, PowerSeries.coeff k (G d) = if d ∣ k then 1 else 0) :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      G 1 ^ 4 * G 2 * G 3 + X ^ 2 * G 1 ^ 3 * G 2 ^ 2 * G 3 +
      2 * X ^ 3 * G 1 ^ 3 * G 2 * G 3 ^ 2 := by
  have h1 : (∏ i, G (weights1 i)) = G 1^4*G 2*G 3 := by
    simp [weights1, Fin.prod_univ_succ]
    ring
  have h2 : (∏ i, G (weights2 i)) = G 1^3*G 2^2*G 3 := by
    simp [weights2, Fin.prod_univ_succ]
    ring
  have h3 : (∏ i, G (weights3 i)) = G 1^3*G 2*G 3^2 := by
    simp [weights3, Fin.prod_univ_succ]
    ring
  have split : G 1 ^ 4 * G 2 * G 3 + X ^ 2 * G 1 ^ 3 * G 2 ^ 2 * G 3 +
      2 * X ^ 3 * G 1 ^ 3 * G 2 * G 3 ^ 2 =
      X^0 * (∏ i, G (weights1 i)) + X^2 * (∏ i, G (weights2 i)) +
      C (2 : ℚ) * (X^3 * (∏ i, G (weights3 i))) := by
    rw [h1,h2,h3]
    simp only [map_ofNat, pow_zero, one_mul]
    ring
  rw [split]
  ext n
  simp only [coeff_mk, map_add, coeff_C_mul]
  rw [← wcomp_coeff weights1 weights1_pos 0 n G hG,
    ← wcomp_coeff weights2 weights2_pos 2 n G hG,
    ← wcomp_coeff weights3 weights3_pos 3 n G hG]
  rw [a_eq_compositions]
  push_cast
  rfl

end A166213Proof

namespace A166213Proof

open PowerSeries

noncomputable def geom (d : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if d ∣ n then 1 else 0)

lemma geom_mul_one_sub (d : ℕ) (hd : 0 < d) :
    geom d * (1 - X ^ d) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  simp only [geom, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hn : n = 0
  · subst n
    simp [Nat.not_le.mpr hd]
  · by_cases hdn : d ≤ n
    · have hdiv : d ∣ n - d ↔ d ∣ n := Nat.dvd_sub_iff_left hdn (dvd_refl d)
      simp [hdn, hn, hdiv]
    · have hdiv : ¬ d ∣ n := by
        intro h
        exact hdn (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h)
      simp [hdn, hn, hdiv]

lemma generating_identity :
    (geom 1 ^ 4 * geom 2 * geom 3 + X ^ 2 * geom 1 ^ 3 * geom 2 ^ 2 * geom 3 +
      2 * X ^ 3 * geom 1 ^ 3 * geom 2 * geom 3 ^ 2) *
        ((1 - X) ^ 6 * (1 + X) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 := by
  have h1 : geom 1 * (1 - X) = 1 := by
    simpa using geom_mul_one_sub 1 (by decide)
  have h2 := geom_mul_one_sub 2 (by decide)
  have h3 := geom_mul_one_sub 3 (by decide)
  have hne : (1 - X : PowerSeries ℚ) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h
    have hh := congrArg PowerSeries.constantCoeff h
    simpa using hh
  apply mul_right_cancel₀ hne
  calc
    _ = (geom 1 * (1 - X)) ^ 4 * (geom 2 * (1 - X ^ 2)) *
          (geom 3 * (1 - X ^ 3)) * ((1 - X ^ 2) * (1 - X ^ 3)) +
        X ^ 2 * (geom 1 * (1 - X)) ^ 3 * (geom 2 * (1 - X ^ 2)) ^ 2 *
          (geom 3 * (1 - X ^ 3)) * ((1 - X) * (1 - X ^ 3)) +
        2 * X ^ 3 * (geom 1 * (1 - X)) ^ 3 * (geom 2 * (1 - X ^ 2)) *
          (geom 3 * (1 - X ^ 3)) ^ 2 * ((1 - X) * (1 - X ^ 2)) := by ring
    _ = _ := by rw [h1, h2, h3]; ring

lemma coeff_nat_mul (n k : ℕ) (f : PowerSeries ℚ) :
    coeff n ((k : PowerSeries ℚ) * f) = (k : ℚ) * coeff n f := by
  have hk : (k : PowerSeries ℚ) = C (k : ℚ) := by simp
  rw [hk, PowerSeries.coeff_C_mul]

lemma recurrence_of_identity (a : ℕ → ℕ)
    (h : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 6 * (1 + X) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4) :
    ∀ n : ℕ, 11 < n →
      (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) - 3 * a (n - 4) +
        6 * a (n - 6) - 3 * a (n - 8) - 2 * a (n - 9) + a (n - 10) +
        2 * a (n - 11) - a (n - 12) := by
  intro n hn
  let f := PowerSeries.mk (fun n => (a n : ℚ))
  have hexpand : f * ((1 - X) ^ 6 * (1 + X) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      f - 2 * (f * X ^ 1) - f * X ^ 2 + 2 * (f * X ^ 3) + 3 * (f * X ^ 4) -
        6 * (f * X ^ 6) + 3 * (f * X ^ 8) + 2 * (f * X ^ 9) - f * X ^ 10 -
        2 * (f * X ^ 11) + f * X ^ 12 := by ring
  have hc := congrArg (coeff n) h
  change coeff n (f * _) = _ at hc
  rw [hexpand] at hc
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have h6 : 6 ≤ n := by omega
  have h8 : 8 ≤ n := by omega
  have h9 : 9 ≤ n := by omega
  have h10 : 10 ≤ n := by omega
  have h11 : 11 ≤ n := by omega
  have h12 : 12 ≤ n := by omega
  have e0 : n ≠ 0 := by omega
  have e1 : n ≠ 1 := by omega
  have e2 : n ≠ 2 := by omega
  have e3 : n ≠ 3 := by omega
  have e4 : n ≠ 4 := by omega
  simp only [show (2 : PowerSeries ℚ) = C (2 : ℚ) from (map_ofNat C 2).symm,
    show (3 : PowerSeries ℚ) = C (3 : ℚ) from (map_ofNat C 3).symm,
    show (4 : PowerSeries ℚ) = C (4 : ℚ) from (map_ofNat C 4).symm,
    show (6 : PowerSeries ℚ) = C (6 : ℚ) from (map_ofNat C 6).symm,
    map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_X,
    PowerSeries.coeff_one, h1, h2, h3, h4, h6, h8, h9, h10, h11, h12,
    e0, e1, e2, e3, e4, if_pos, if_false, f, PowerSeries.coeff_mk] at hc
  simp only [PowerSeries.coeff_C, if_neg (show n - 2 ≠ 0 by omega),
    if_neg (show n - 3 ≠ 0 by omega), if_neg (show n - 4 ≠ 0 by omega),
    mul_zero, zero_add, add_zero] at hc
  have hrat : (a n : ℚ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) -
      3 * a (n - 4) + 6 * a (n - 6) - 3 * a (n - 8) - 2 * a (n - 9) +
      a (n - 10) + 2 * a (n - 11) - a (n - 12) := by linarith only [hc]
  exact_mod_cast hrat

theorem finish
    (h : PowerSeries.mk (fun n => (OMA.S_oeis_a166213.a n : ℚ)) =
      geom 1 ^ 4 * geom 2 * geom 3 + X ^ 2 * geom 1 ^ 3 * geom 2 ^ 2 * geom 3 +
        2 * X ^ 3 * geom 1 ^ 3 * geom 2 * geom 3 ^ 2) :
    type_of% @OMA.S_oeis_a166213.main := by
  have hg := generating_identity
  rw [← h] at hg
  exact ⟨hg, recurrence_of_identity _ hg⟩

end A166213Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a166213.main := by
  apply A166213Proof.finish
  apply A166213Proof.series_eq_general A166213Proof.geom
  intro d k
  simp [A166213Proof.geom]
