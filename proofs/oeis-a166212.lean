import OMAStatements.S_oeis_a166212

-- Problem: A166212 rotationally symmetric triangular arrays.
-- Source: https://oeis.org/A166212
-- Credit: @CubeJerry
-- Count the four rotation orbits, evaluate the bounded sums by parity,
-- and derive the period-six quasipolynomial, recurrence, and generating function.

namespace A166212Proof
open OMA.S_oeis_a166212
open Finset

def cellMap : Fin 10 → Cell :=
  ![⟨(0,0,3), by decide⟩, ⟨(0,3,0), by decide⟩, ⟨(3,0,0), by decide⟩,
    ⟨(0,1,2), by decide⟩, ⟨(1,2,0), by decide⟩, ⟨(2,0,1), by decide⟩,
    ⟨(0,2,1), by decide⟩, ⟨(2,1,0), by decide⟩, ⟨(1,0,2), by decide⟩,
    ⟨(1,1,1), by decide⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma cellMap_bijective : Function.Bijective cellMap := by decide

noncomputable def cellEquiv : Fin 10 ≃ Cell :=
  Equiv.ofBijective cellMap cellMap_bijective

def orbitOf : Fin 10 → Fin 4 := ![0,0,0,1,1,1,2,2,2,3]
def rotateIndex : Fin 10 → Fin 10 := ![1,2,0,4,5,3,7,8,6,9]
def reprIndex : Fin 4 → Fin 10 := ![0,3,6,9]

lemma rot_cellMap (i : Fin 10) : rot (cellMap i) = cellMap (rotateIndex i) := by
  fin_cases i <;> decide

lemma orbitOf_rot (i : Fin 10) : orbitOf (rotateIndex i) = orbitOf i := by
  fin_cases i <;> decide

lemma orbitOf_repr (i : Fin 4) : orbitOf (reprIndex i) = i := by
  fin_cases i <;> decide

noncomputable def inflate {n : ℕ} (v : Fin 4 → Fin (n+1)) (p : Cell) : Fin (n+1) :=
  v (orbitOf (cellEquiv.symm p))

def extract {n : ℕ} (f : Cell → Fin (n+1)) (i : Fin 4) : Fin (n+1) :=
  f (cellMap (reprIndex i))

lemma inflate_cellMap {n : ℕ} (v : Fin 4 → Fin (n+1)) (i : Fin 10) :
    inflate v (cellMap i) = v (orbitOf i) := by
  change v (orbitOf (cellEquiv.symm (cellEquiv i))) = _
  simp

lemma extract_inflate {n : ℕ} (v : Fin 4 → Fin (n+1)) : extract (inflate v) = v := by
  funext i
  simp [extract, inflate_cellMap, orbitOf_repr]

lemma inflate_rot {n : ℕ} (v : Fin 4 → Fin (n+1)) (p : Cell) :
    inflate v (rot p) = inflate v p := by
  obtain ⟨i, rfl⟩ := cellMap_bijective.surjective p
  rw [rot_cellMap, inflate_cellMap, inflate_cellMap, orbitOf_rot]

lemma inflate_extract {n : ℕ} (f : Cell → Fin (n+1))
    (h : ∀ p, f (rot p) = f p) : inflate (extract f) = f := by
  funext p
  obtain ⟨i, rfl⟩ := cellMap_bijective.surjective p
  rw [inflate_cellMap]
  have h0 := h (cellMap 0)
  have h1 := h (cellMap 1)
  have h3 := h (cellMap 3)
  have h4 := h (cellMap 4)
  have h6 := h (cellMap 6)
  have h7 := h (cellMap 7)
  simp only [rot_cellMap] at h0 h1 h3 h4 h6 h7
  fin_cases i <;> simp_all [extract, orbitOf, reprIndex, rotateIndex]

def orbitValid (n : ℕ) (v : Fin 4 → Fin (n+1)) : Prop :=
  (v 0 : ℕ) + v 1 + 2 * v 2 + v 3 ≤ n ∧
  (v 0 : ℕ) + 2 * v 1 + v 2 + v 3 ≤ n ∧
  3 * ((v 1 : ℕ) + v 2) + v 3 ≤ n

lemma nbrSum_inflate {n : ℕ} (v : Fin 4 → Fin (n+1)) (i : Fin 10) :
    nbrSum (inflate v) (cellMap i) =
      ![(v 0 : ℕ)+v 1+v 2, (v 0 : ℕ)+v 1+v 2, (v 0 : ℕ)+v 1+v 2,
        (v 0 : ℕ)+v 1+2*v 2+v 3, (v 0 : ℕ)+v 1+2*v 2+v 3,
        (v 0 : ℕ)+v 1+2*v 2+v 3,
        (v 0 : ℕ)+2*v 1+v 2+v 3, (v 0 : ℕ)+2*v 1+v 2+v 3,
        (v 0 : ℕ)+2*v 1+v 2+v 3, 3*((v 1 : ℕ)+v 2)+v 3] i := by
  unfold nbrSum
  rw [← Equiv.sum_comp cellEquiv]
  change (∑ j : Fin 10, if cellMap j = cellMap i ∨ adj (cellMap i) (cellMap j)
    then (inflate v (cellMap j) : ℕ) else 0) = _
  simp only [inflate_cellMap]
  fin_cases i <;> norm_num [Fin.sum_univ_succ, cellMap, adj, orbitOf, Fin.ext_iff] <;> omega

lemma valid_inflate_iff {n : ℕ} (v : Fin 4 → Fin (n+1)) :
    valid n (inflate v) ↔ orbitValid n v := by
  constructor
  · intro h
    have h1 := h.2 (cellMap 3)
    have h2 := h.2 (cellMap 6)
    have h3 := h.2 (cellMap 9)
    simpa [nbrSum_inflate, orbitValid] using And.intro h1 (And.intro h2 h3)
  · intro h
    refine ⟨inflate_rot v, ?_⟩
    intro p
    obtain ⟨i, rfl⟩ := cellMap_bijective.surjective p
    rw [nbrSum_inflate]
    rcases h with ⟨h1,h2,h3⟩
    fin_cases i <;> dsimp <;> omega

noncomputable def arrayEquiv (n : ℕ) :
    {f : Cell → Fin (n+1) // valid n f} ≃
      {v : Fin 4 → Fin (n+1) // orbitValid n v} where
  toFun f := ⟨extract f.val, by
    apply (valid_inflate_iff _).mp
    rw [inflate_extract f.val f.property.1]
    exact f.property⟩
  invFun v := ⟨inflate v.val, (valid_inflate_iff _).mpr v.property⟩
  left_inv f := Subtype.ext (inflate_extract f.val f.property.1)
  right_inv v := Subtype.ext (extract_inflate v.val)

abbrev Params (n : ℕ) :=
  (s : Fin (n / 3 + 1)) × (b : Fin (s.val + 1)) ×
    (d : Fin (n - 3 * s.val + 1)) ×
      Fin (n - s.val - max b.val (s.val-b.val) - d.val + 1)

instance (n : ℕ) : Fintype (Params n) := by unfold Params; infer_instance

def paramsToValues (n : ℕ) (p : Params n) :
    {v : Fin 4 → Fin (n+1) // orbitValid n v} := by
  have hs := p.1.isLt
  have hb := p.2.1.isLt
  have hd := p.2.2.1.isLt
  have ha := p.2.2.2.isLt
  refine ⟨![⟨p.2.2.2.val, by omega⟩, ⟨p.2.1.val, by omega⟩,
    ⟨p.1.val-p.2.1.val, by omega⟩, ⟨p.2.2.1.val, by omega⟩], ?_⟩
  dsimp [orbitValid]
  omega

def valuesToParams (n : ℕ) (v : {v : Fin 4 → Fin (n+1) // orbitValid n v}) :
    Params n := by
  have h1 := v.property.1
  have h2 := v.property.2.1
  have h3 := v.property.2.2
  refine ⟨⟨(v.val 1 : ℕ)+v.val 2, by omega⟩,
    ⟨(v.val 1).val, by dsimp; omega⟩, ⟨(v.val 3).val, by dsimp; omega⟩,
    ⟨(v.val 0).val, ?_⟩⟩
  dsimp
  omega

lemma valuesToParams_paramsToValues (n : ℕ) (p : Params n) :
    valuesToParams n (paramsToValues n p) = p := by
  have extParams : ∀ p q : Params n,
      p.1.val = q.1.val → p.2.1.val = q.2.1.val →
      p.2.2.1.val = q.2.2.1.val → p.2.2.2.val = q.2.2.2.val → p = q := by
    rintro ⟨⟨ps,psh⟩,⟨pb,pbh⟩,⟨pd,pdh⟩,⟨pa,pah⟩⟩
      ⟨⟨qs,qsh⟩,⟨qb,qbh⟩,⟨qd,qdh⟩,⟨qa,qah⟩⟩ hs hb hd ha
    dsimp only at hs hb hd ha
    subst qs
    subst qb
    subst qd
    subst qa
    rfl
  apply extParams
  · change p.2.1.val + (p.1.val-p.2.1.val) = p.1.val
    have hb := p.2.1.isLt
    omega
  · rfl
  · rfl
  · rfl

lemma paramsToValues_valuesToParams (n : ℕ)
    (v : {v : Fin 4 → Fin (n+1) // orbitValid n v}) :
    paramsToValues n (valuesToParams n v) = v := by
  apply Subtype.ext
  funext i
  fin_cases i <;> apply Fin.ext <;>
    simp [paramsToValues, valuesToParams]

def paramsEquiv (n : ℕ) : Params n ≃
    {v : Fin 4 → Fin (n+1) // orbitValid n v} where
  toFun := paramsToValues n
  invFun := valuesToParams n
  left_inv := valuesToParams_paramsToValues n
  right_inv := paramsToValues_valuesToParams n

lemma count_params (n : ℕ) : a n = Fintype.card (Params n) := by
  classical
  rw [show a n = Fintype.card {f : Cell → Fin (n+1) // valid n f} by
    simp [a, Fintype.card_subtype]]
  exact Fintype.card_congr ((arrayEquiv n).trans (paramsEquiv n).symm)

lemma count_sum (n : ℕ) : a n =
    ∑ s ∈ range (n/3+1), ∑ b ∈ range (s+1),
      ∑ d ∈ range (n-3*s+1), (n-s-max b (s-b)-d+1) := by
  rw [count_params]
  simp only [Params, Fintype.card_sigma, Fintype.card_fin]
  simp_rw [show ∀ s : Fin (n/3+1), ∀ b : Fin (s.val+1),
      (∑ d : Fin (n-3*s.val+1), (n-s.val-max b.val (s.val-b.val)-d.val+1)) =
      ∑ d ∈ range (n-3*s.val+1), (n-s.val-max b.val (s.val-b.val)-d+1) by
    intro s b
    exact Fin.sum_univ_eq_sum_range (fun d => n-s.val-max b.val (s.val-b.val)-d+1) _]
  simp_rw [show ∀ s : Fin (n/3+1),
      (∑ b : Fin (s.val+1), ∑ d ∈ range (n-3*s.val+1),
        (n-s.val-max b.val (s.val-b.val)-d+1)) =
      ∑ b ∈ range (s.val+1), ∑ d ∈ range (n-3*s.val+1),
        (n-s.val-max b (s.val-b)-d+1) by
    intro s
    exact Fin.sum_univ_eq_sum_range (fun b => ∑ d ∈ range (n-3*s.val+1), (n-s.val-max b (s.val-b)-d+1)) _]
  exact Fin.sum_univ_eq_sum_range (fun s => ∑ b ∈ range (s+1), ∑ d ∈ range (n-3*s+1), (n-s-max b (s-b)-d+1)) _

end A166212Proof

namespace A166212Proof
open Finset

lemma sum_range_id_q (m : ℕ) :
    (∑ i ∈ range m, (i : ℚ)) = (m : ℚ) * (m-1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_descending (N C : ℕ) (h : N ≤ C) :
    (((∑ d ∈ range (N+1), (C-d+1)) : ℕ) : ℚ) =
      ((N : ℚ)+1)*((C : ℚ)+1) - (N : ℚ)*((N : ℚ)+1)/2 := by
  rw [Nat.cast_sum]
  calc
    (∑ d ∈ range (N+1), ((C-d+1 : ℕ) : ℚ)) =
        ∑ d ∈ range (N+1), ((C : ℚ)-(d : ℚ)+1) := by
      apply sum_congr rfl
      intro d hd
      have hdC : d ≤ C := by have := mem_range.mp hd; omega
      rw [Nat.cast_add, Nat.cast_sub hdC, Nat.cast_one]
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, sum_range_id_q]
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

lemma sum_max_even (t : ℕ) :
    (∑ b ∈ range (2*t+1), ((max b (2*t-b) : ℕ) : ℚ)) = 3*(t : ℚ)^2+2*t := by
  rw [show 2*t+1 = (t+1)+t by omega, sum_range_add]
  have hleft : (∑ b ∈ range (t+1), ((max b (2*t-b) : ℕ) : ℚ)) =
      ∑ b ∈ range (t+1), (2*(t : ℚ)-(b : ℚ)) := by
    apply sum_congr rfl
    intro b hb
    have hb' := mem_range.mp hb
    rw [max_eq_right (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hright : (∑ b ∈ range t, ((max (t+1+b) (2*t-(t+1+b)) : ℕ) : ℚ)) =
      ∑ b ∈ range t, ((t : ℚ)+1+b) := by
    apply sum_congr rfl
    intro b hb
    have hb' := mem_range.mp hb
    rw [max_eq_left (by omega)]
    push_cast
    ring
  rw [hleft, hright, sum_sub_distrib, sum_add_distrib, sum_add_distrib,
    sum_range_id_q, sum_range_id_q]
  simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

lemma sum_max_odd (t : ℕ) :
    (∑ b ∈ range (2*t+2), ((max b (2*t+1-b) : ℕ) : ℚ)) =
      3*(t : ℚ)^2+5*t+2 := by
  rw [show 2*t+2 = (t+1)+(t+1) by omega, sum_range_add]
  have hleft : (∑ b ∈ range (t+1), ((max b (2*t+1-b) : ℕ) : ℚ)) =
      ∑ b ∈ range (t+1), (2*(t : ℚ)+1-(b : ℚ)) := by
    apply sum_congr rfl
    intro b hb
    have hb' := mem_range.mp hb
    rw [max_eq_right (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hright : (∑ b ∈ range (t+1), ((max (t+1+b) (2*t+1-(t+1+b)) : ℕ) : ℚ)) =
      ∑ b ∈ range (t+1), ((t : ℚ)+1+b) := by
    apply sum_congr rfl
    intro b hb
    have hb' := mem_range.mp hb
    rw [max_eq_left (by omega)]
    push_cast
    ring
  rw [hleft, hright]
  simp only [sum_sub_distrib, sum_add_distrib, sum_range_id_q,
    sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

def rowCount (n s : ℕ) : ℕ :=
  ∑ b ∈ range (s+1), ∑ d ∈ range (n-3*s+1), (n-s-max b (s-b)-d+1)

lemma rowCount_q (n s : ℕ) (hs : 3*s ≤ n) :
    (rowCount n s : ℚ) = ((n : ℚ)-3*s+1) *
      (((s : ℚ)+1)*((n : ℚ)-s+1) -
        (∑ b ∈ range (s+1), ((max b (s-b) : ℕ) : ℚ)) -
        ((s : ℚ)+1)*((n : ℚ)-3*s)/2) := by
  unfold rowCount
  rw [Nat.cast_sum]
  calc
    _ = ∑ b ∈ range (s+1),
        (((n : ℚ)-3*s+1)*((n : ℚ)-s-(max b (s-b) : ℕ)+1) -
          ((n : ℚ)-3*s)*((n : ℚ)-3*s+1)/2) := by
      apply sum_congr rfl
      intro b hb
      have hb' := mem_range.mp hb
      have hmax : max b (s-b) ≤ s := by omega
      rw [sum_descending (n-3*s) (n-s-max b (s-b)) (by omega)]
      rw [Nat.cast_sub hs, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_sub (show max b (s-b) ≤ n-s by omega),
        Nat.cast_sub (show s ≤ n by omega)]
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum]
      simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_range,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

def evenTerm (n t : ℚ) : ℚ :=
  (n-6*t+1)*((2*t+1)*n-2*t*t+2*t+2)/2

def oddTerm (n t : ℚ) : ℚ :=
  (n-6*t-2)*((2*t+2)*n-2*t*t+2)/2

lemma rowCount_even (n t : ℕ) (ht : 6*t ≤ n) :
    (rowCount n (2*t) : ℚ) = evenTerm n t := by
  rw [rowCount_q n (2*t) (by omega), sum_max_even]
  unfold evenTerm
  push_cast
  ring

lemma rowCount_odd (n t : ℕ) (ht : 6*t+3 ≤ n) :
    (rowCount n (2*t+1) : ℚ) = oddTerm n t := by
  rw [rowCount_q n (2*t+1) (by omega)]
  rw [show 2*t+1+1 = 2*t+2 by omega, sum_max_odd]
  unfold oddTerm
  push_cast
  ring

lemma sum_evenTerm (n : ℚ) (m : ℕ) :
    (∑ t ∈ range m, evenTerm n t) =
      (m : ℚ)*(9*m^3-14*m^2*n-32*m^2+3*m*n^2+18*m*n+15*m+5*n+14)/6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    unfold evenTerm
    push_cast
    ring

lemma sum_oddTerm (n : ℚ) (m : ℕ) :
    (∑ t ∈ range m, oddTerm n t) =
      (m : ℚ)*(m+1)*(9*m^2-14*m*n-23*m+3*n^2+11*n+8)/6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    unfold oddTerm
    push_cast
    ring

lemma sum_even_odd (f : ℕ → ℚ) (m : ℕ) :
    (∑ s ∈ range (2*m), f s) =
      (∑ t ∈ range m, f (2*t)) + ∑ t ∈ range m, f (2*t+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+1+1 by omega, sum_range_succ, sum_range_succ,
      ih, sum_range_succ, sum_range_succ]
    ring

lemma sum_even_odd_one (f : ℕ → ℚ) (m : ℕ) :
    (∑ s ∈ range (2*m+1), f s) =
      (∑ t ∈ range (m+1), f (2*t)) + ∑ t ∈ range m, f (2*t+1) := by
  rw [sum_range_succ, sum_even_odd, sum_range_succ]
  ring

end A166212Proof

namespace A166212Proof
open OMA.S_oeis_a166212
open Finset

lemma count_sum_q (n : ℕ) : (a n : ℚ) =
    ∑ s ∈ range (n/3+1), (rowCount n s : ℚ) := by
  rw [count_sum, Nat.cast_sum]
  rfl

lemma count_split_low (n m : ℕ) (h : n/3 = 2*m) :
    (a n : ℚ) = (∑ t ∈ range (m+1), evenTerm n t) +
      ∑ t ∈ range m, oddTerm n t := by
  rw [count_sum_q, h, sum_even_odd_one]
  congr 1
  · apply sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    exact rowCount_even n t (by omega)
  · apply sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    exact rowCount_odd n t (by omega)

lemma count_split_high (n m : ℕ) (h : n/3 = 2*m+1) :
    (a n : ℚ) = (∑ t ∈ range (m+1), evenTerm n t) +
      ∑ t ∈ range (m+1), oddTerm n t := by
  rw [count_sum_q, h, show 2*m+1+1 = 2*(m+1) by omega, sum_even_odd]
  congr 1
  · apply sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    exact rowCount_even n t (by omega)
  · apply sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    exact rowCount_odd n t (by omega)

def countPolynomial (m : ℚ) : Fin 6 → ℚ :=
  ![11*m^4+(76/3)*m^3+21*m^2+(23/3)*m+1,
    11*m^4+(98/3)*m^3+(71/2)*m^2+(101/6)*m+3,
    11*m^4+40*m^3+52*m^2+29*m+6,
    11*m^4+(142/3)*m^3+(151/2)*m^2+(319/6)*m+14,
    11*m^4+(164/3)*m^3+101*m^2+(247/3)*m+25,
    11*m^4+62*m^3+(257/2)*m^2+(233/2)*m+39]

lemma count_formula (m : ℕ) (r : Fin 6) :
    (a (6*m+r.val) : ℚ) = countPolynomial m r := by
  fin_cases r
  all_goals dsimp only [Fin.val_mk]
  · rw [count_split_low (6*m+0) m (by omega), sum_evenTerm, sum_oddTerm]
    dsimp [countPolynomial]
    push_cast
    ring
  · rw [count_split_low (6*m+1) m (by omega), sum_evenTerm, sum_oddTerm]
    dsimp [countPolynomial]
    push_cast
    ring
  · rw [count_split_low (6*m+2) m (by omega), sum_evenTerm, sum_oddTerm]
    dsimp [countPolynomial]
    push_cast
    ring
  · rw [count_split_high (6*m+3) m (by omega), sum_evenTerm, sum_oddTerm]
    dsimp [countPolynomial]
    push_cast
    ring
  · rw [count_split_high (6*m+4) m (by omega), sum_evenTerm, sum_oddTerm]
    dsimp [countPolynomial]
    push_cast
    ring
  · rw [count_split_high (6*m+5) m (by omega), sum_evenTerm, sum_oddTerm]
    dsimp [countPolynomial]
    push_cast
    ring

lemma count_six_mul_add (m c : ℕ) :
    (a (6*m+c) : ℚ) = countPolynomial ((m+c/6 : ℕ) : ℚ) ⟨c%6, Nat.mod_lt _ (by decide)⟩ := by
  rw [show 6*m+c = 6*(m+c/6)+c%6 by omega]
  exact count_formula (m+c/6) ⟨c%6, Nat.mod_lt _ (by decide)⟩

lemma count_any (n : ℕ) :
    (a n : ℚ) = countPolynomial (n/6 : ℕ) ⟨n%6, Nat.mod_lt _ (by decide)⟩ := by
  simpa using count_six_mul_add 0 n

lemma index_sub (m c k : ℕ) (h : k ≤ c) :
    6*m+c-k = 6*m+(c-k) := by omega

lemma recurrence_tail (m : ℕ) (r : Fin 6) :
    let n := 6*m+(18+r.val)
    (a n : ℚ) = 2*a (n-1)-a (n-2)+2*a (n-3)-4*a (n-4)+
      2*a (n-5)-2*a (n-9)+4*a (n-10)-2*a (n-11)+a (n-12)-
      2*a (n-13)+a (n-14) := by
  fin_cases r <;> dsimp only [Fin.val_mk]
  all_goals norm_num [index_sub, count_six_mul_add, countPolynomial]
  all_goals ring

lemma recurrence_q (n : ℕ) (hn : 13 < n) :
    (a n : ℚ) = 2*a (n-1)-a (n-2)+2*a (n-3)-4*a (n-4)+
      2*a (n-5)-2*a (n-9)+4*a (n-10)-2*a (n-11)+a (n-12)-
      2*a (n-13)+a (n-14) := by
  by_cases h18 : 18 ≤ n
  · have he : n = 6*((n-18)/6)+(18+(n-18)%6) := by omega
    simpa only [← he] using recurrence_tail ((n-18)/6) ⟨(n-18)%6, Nat.mod_lt _ (by decide)⟩
  · interval_cases n <;> norm_num [count_any, countPolynomial]

lemma recurrence_z (n : ℕ) (hn : 13 < n) :
    (a n : ℤ) = 2*a (n-1)-a (n-2)+2*a (n-3)-4*a (n-4)+
      2*a (n-5)-2*a (n-9)+4*a (n-10)-2*a (n-11)+a (n-12)-
      2*a (n-13)+a (n-14) := by
  exact_mod_cast recurrence_q n hn

end A166212Proof

namespace A166212Proof
open OMA.S_oeis_a166212
open PowerSeries

lemma coeff_mk_mul_monomial (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X^k)) = if k ≤ n then f (n-k)*c else 0 := by
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C, coeff_mk]
  · rfl

lemma denominator_expansion :
    ((1-X)^5*(1+X)*(1-X+X^2)*(1+X+X^2)^3 : PowerSeries ℚ) =
      C 1*X^0 + C (-2)*X^1 + C 1*X^2 + C (-2)*X^3 + C 4*X^4 +
      C (-2)*X^5 + C 2*X^9 + C (-4)*X^10 + C 2*X^11 + C (-1)*X^12 +
      C 2*X^13 + C (-1)*X^14 := by
  simp only [map_one, map_neg, map_ofNat]
  ring

lemma numerator_expansion :
    (1+X+X^2+3*X^3+X^4+X^5+3*X^6 : PowerSeries ℚ) =
      C 1*X^0 + C 1*X^1 + C 1*X^2 + C 3*X^3 + C 1*X^4 + C 1*X^5 +
      C 3*X^6 := by
  simp [map_ofNat]

lemma generating_function :
    mk (fun n => (a n : ℚ)) *
      ((1-X)^5*(1+X)*(1-X+X^2)*(1+X+X^2)^3) =
      1+X+X^2+3*X^3+X^4+X^5+3*X^6 := by
  rw [denominator_expansion, numerator_expansion]
  ext n
  simp only [mul_add, map_add, coeff_mk_mul_monomial, coeff_C_mul_X_pow]
  by_cases hn : 13 < n
  · have hr := recurrence_q n hn
    simp (disch := omega) only [if_pos, if_neg]
    simp only [Nat.sub_zero]
    linarith
  · interval_cases n <;> norm_num [count_any, countPolynomial]

end A166212Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a166212.main := by
  exact ⟨A166212Proof.generating_function, A166212Proof.recurrence_z⟩
