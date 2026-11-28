import OMAStatements.S_oeis_a209725
import Mathlib

/-!
Proof of Barker's parity formulas for A209725 ((n+1) X 7 arrays over 0..2 whose 2 X 2 subblocks
have distinct clockwise edge differences).

Only 8 of the 81 blocks (p, q upper, r, s lower) are valid, and in each of them s is a function of
p, q, r (blk_det725). Hence a row v compatible with u is determined by its first entry: v is the
forced row G725 u (v 0) (compat_G725), and the sum over compatible successors is a sum over three
first entries (sum_succ725). T725 n u counts the valid arrays with n + 1 rows and top row u, with
T725 (n + 1) u = Sum over compatible v of T725 n v. Every row gets a type (no successor; one
successor which is not of type 2; two successors; one successor of type 2), and a kernel check
over the 3^7 rows shows that the successors of a row of each type have the types the closed form
needs (check725_all). Therefore T725 n u = hv725 n (type u), with values 1, 2^((n+1)/2) and
2^(n/2) for the three nonzero types. Counting the rows of each type (40, 2 and 4), the number of
valid arrays is 40 + 2 * 2^((n+1)/2) + 4 * 2^(n/2) for n ≥ 1, which gives both formulas.
-/

namespace OMA.Helpers

open OMA.S_oeis_a209725 Finset

/-- A row of the array. -/
abbrev Row725 := Fin 7 → Fin 3

/-- The block condition as a Boolean table: the eight valid blocks (p, q, r, s), with p, q the
upper row and r, s the lower row. -/
def blkC725 (p q r s : Fin 3) : Bool :=
  decide ((p.val, q.val, r.val, s.val) ∈
    [(0, 1, 2, 0), (0, 2, 1, 0), (0, 2, 2, 1), (1, 0, 0, 2), (1, 2, 2, 0), (2, 0, 0, 1),
      (2, 0, 1, 2), (2, 1, 0, 2)])

theorem blk_iff725 : ∀ p q r s : Fin 3, distinctClockwise p q r s ↔ blkC725 p q r s = true := by
  unfold distinctClockwise
  decide +kernel

/-- The lower right entry of a valid block is determined by the other three. -/
def fT725 : Fin 3 → Fin 3 → Fin 3 → Fin 3 :=
  ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![2, 0, 0], ![0, 0, 0], ![0, 0, 0]],
    ![![1, 2, 0], ![2, 0, 0], ![0, 0, 0]]]

theorem blk_det725 : ∀ p q r s : Fin 3, blkC725 p q r s = true → s = fT725 p q r := by
  decide +kernel

/-- Two consecutive rows u (upper) and v (lower) are compatible. -/
def compat725 (u v : Row725) : Prop :=
  ∀ j : Fin 6, distinctClockwise (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- The Boolean version of compat725. -/
def compatC725 (u v : Row725) : Bool :=
  (List.finRange 6).all fun j => blkC725 (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

theorem compat_iff725 (u v : Row725) : compat725 u v ↔ compatC725 u v = true := by
  unfold compat725 compatC725
  simp only [List.all_eq_true, List.mem_finRange, true_implies, blk_iff725]

instance (u v : Row725) : Decidable (compat725 u v) :=
  decidable_of_iff _ (compat_iff725 u v).symm

/-- The entries of u, extended by 0. -/
def ue725 (u : Row725) (j : ℕ) : Fin 3 := if h : j < 7 then u ⟨j, h⟩ else 0

/-- The forced lower row with first entry c. -/
def Gn725 (u : Row725) (c : Fin 3) : ℕ → Fin 3
  | 0 => c
  | j + 1 => fT725 (ue725 u j) (ue725 u (j + 1)) (Gn725 u c j)

def G725 (u : Row725) (c : Fin 3) : Row725 := fun j => Gn725 u c j.val

theorem compat_G725 {u v : Row725} (h : compat725 u v) : G725 u (v 0) = v := by
  have key : ∀ j (hj : j < 7), Gn725 u (v 0) j = v ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hb := (blk_iff725 _ _ _ _).mp (h ⟨j, by omega⟩)
      have hd : v ⟨j + 1, hj⟩ = fT725 (u ⟨j, by omega⟩) (u ⟨j + 1, hj⟩) (v ⟨j, by omega⟩) :=
        blk_det725 _ _ _ _ hb
      show fT725 (ue725 u j) (ue725 u (j + 1)) (Gn725 u (v 0) j) = v ⟨j + 1, hj⟩
      rw [ih (by omega), hd]
      unfold ue725
      rw [dif_pos (by omega), dif_pos hj]
  funext j
  exact key j.val j.isLt

theorem sum_succ725 (u : Row725) (F : Row725 → ℕ) :
    ∑ v : Row725, (if compat725 u v then F v else 0) =
      ∑ c : Fin 3, (if compat725 u (G725 u c) then F (G725 u c) else 0) := by
  have h1 : ∀ c : Fin 3, (if compat725 u (G725 u c) then F (G725 u c) else 0) =
      ∑ v : Row725, (if G725 u c = v then (if compat725 u v then F v else 0) else 0) := by
    intro c
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : compat725 u v
  · rw [Finset.sum_eq_single (v 0)]
    · rw [if_pos (compat_G725 hv)]
    · intro c _ hc
      rw [if_neg]
      intro h
      apply hc
      rw [← h]
      rfl
    · simp
  · rw [if_neg hv]
    simp

/-- The valid arrays: consecutive rows are compatible. -/
def valid725 {n : ℕ} (x : Fin (n + 1) → Row725) : Prop :=
  ∀ i : Fin n, compat725 (x i.castSucc) (x i.succ)

instance {n : ℕ} (x : Fin (n + 1) → Row725) : Decidable (valid725 x) := by
  unfold valid725
  infer_instance

theorem valid_cons725 {m : ℕ} (u : Row725) (w : Fin (m + 1) → Row725) :
    valid725 (Fin.cons u w : Fin (m + 2) → Row725) ↔ compat725 u (w 0) ∧ valid725 w := by
  unfold valid725
  rw [Fin.forall_fin_succ]
  apply and_congr
  · rfl
  · apply forall_congr'
    intro i
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]

/-- The number of valid arrays with n + 1 rows and top row u. -/
def T725 (n : ℕ) (u : Row725) : ℕ :=
  ∑ y : Fin n → Row725, if valid725 (Fin.cons u y : Fin (n + 1) → Row725) then 1 else 0

theorem T725_zero (u : Row725) : T725 0 u = 1 := by
  unfold T725
  rw [Fintype.sum_unique, if_pos]
  intro i
  exact Fin.elim0 i

theorem T725_succ (m : ℕ) (u : Row725) :
    T725 (m + 1) u = ∑ v : Row725, if compat725 u v then T725 m v else 0 := by
  unfold T725
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row725).symm _
    (fun p => if valid725 (Fin.cons u (Fin.cons p.1 p.2 : Fin (m + 1) → Row725) :
      Fin (m + 2) → Row725) then 1 else 0) (fun y => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [valid_cons725, Fin.cons_zero]
  by_cases hv : compat725 u v
  · simp [hv]
  · simp [hv]

theorem card_eq725 (n : ℕ) :
    Nat.card {A : Fin (n + 1) → Fin 7 → Fin 3 // isValid n A} = ∑ u : Row725, T725 n u := by
  show Nat.card {A : Fin (n + 1) → Row725 // valid725 A} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row725).symm _
    (fun p => if valid725 (Fin.cons p.1 p.2 : Fin (n + 1) → Row725) then 1 else 0)
    (fun y => by simp), Fintype.sum_prod_type]
  rfl

/-- The successor rows (by their first entries). -/
def scs725 (u : Row725) : List (Fin 3) := (List.finRange 3).filter fun c => compatC725 u (G725 u c)

/-- The type of a row: 0 no successor, 2 two successors, 3 one successor which has two
successors, 1 one successor which has not. -/
def ty725 (u : Row725) : ℕ :=
  match scs725 u with
  | [] => 0
  | [c] => if (scs725 (G725 u c)).length = 2 then 3 else 1
  | [_, _] => 2
  | _ => 9

/-- The types of the successors of u, as required by the type of u. -/
def allowed725 (k : ℕ) : List ℕ :=
  if k = 0 then [] else if k = 1 then [1] else if k = 2 then [3, 3] else [2]

def check725 (u : Row725) : Bool :=
  decide (ty725 u ≤ 3) && decide ((scs725 u).map (fun c => ty725 (G725 u c)) = allowed725 (ty725 u))

/-- The row with code t. -/
def rowOf725 (t : Fin (3 ^ 7)) : Row725 := fun j => ⟨t.val / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem rowOf_eq725 (t : Fin (3 ^ 7)) : rowOf725 t = finFunctionFinEquiv.symm t := by
  funext j
  apply Fin.ext
  rfl

theorem sum_rows725 (F : Row725 → ℕ) : ∑ u : Row725, F u = ∑ t : Fin (3 ^ 7), F (rowOf725 t) := by
  rw [← Equiv.sum_comp finFunctionFinEquiv.symm F]
  exact Finset.sum_congr rfl fun t _ => by rw [rowOf_eq725]

theorem check_all725 : ∀ t : Fin (3 ^ 7), check725 (rowOf725 t) = true := by
  decide +kernel

theorem check725_all (u : Row725) : check725 u = true := by
  have h := check_all725 (finFunctionFinEquiv u)
  rwa [rowOf_eq725, Equiv.symm_apply_apply] at h

/-- The closed form of the number of valid arrays with n + 1 rows and top row of type k. -/
def hv725 (n k : ℕ) : ℕ :=
  if n = 0 then 1 else if k = 1 then 1 else if k = 2 then 2 ^ ((n + 1) / 2)
    else if k = 3 then 2 ^ (n / 2) else 0

theorem hv725_step (n k : ℕ) (hk : k ≤ 3) :
    hv725 (n + 1) k = ((allowed725 k).map (hv725 n)).sum := by
  unfold allowed725 hv725
  interval_cases k
  · simp
  · by_cases hn : n = 0 <;> simp [hn]
  · by_cases hn : n = 0
    · subst hn; simp
    · simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
        show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num,
        if_false, if_true, hn, Nat.add_one_ne_zero, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      rw [show (n + 1 + 1) / 2 = n / 2 + 1 by omega, pow_succ]
      ring
  · by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

theorem sum_fin3_725 (b : Fin 3 → Bool) (g : Fin 3 → ℕ) :
    (((List.finRange 3).filter fun c => b c).map g).sum = ∑ c : Fin 3, if b c = true then g c else 0 := by
  rw [Fin.sum_univ_three]
  have e : List.finRange 3 = [0, 1, 2] := rfl
  rw [e]
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;> simp [List.filter, h0, h1, h2, add_assoc]

theorem T725_closed (n : ℕ) : ∀ u : Row725, T725 n u = hv725 n (ty725 u) := by
  induction n with
  | zero => intro u; rw [T725_zero]; rfl
  | succ n ih =>
    intro u
    rw [T725_succ, Finset.sum_congr rfl (fun v _ => by rw [ih v]), sum_succ725]
    have hc := check725_all u
    unfold check725 at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hk, he⟩ := hc
    rw [hv725_step n _ hk, ← he, List.map_map]
    unfold scs725
    rw [sum_fin3_725]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [compat_iff725, Function.comp]

theorem counts725 :
    (∑ t : Fin (3 ^ 7), if ty725 (rowOf725 t) = 1 then 1 else 0) = 40 ∧
    (∑ t : Fin (3 ^ 7), if ty725 (rowOf725 t) = 2 then 1 else 0) = 2 ∧
    (∑ t : Fin (3 ^ 7), if ty725 (rowOf725 t) = 3 then 1 else 0) = 4 := by
  decide +kernel

theorem hv725_split (n k : ℕ) (hn : n ≠ 0) :
    hv725 n k = (if k = 1 then 1 else 0) + (if k = 2 then 1 else 0) * 2 ^ ((n + 1) / 2) +
      (if k = 3 then 1 else 0) * 2 ^ (n / 2) := by
  unfold hv725
  rw [if_neg hn]
  by_cases h1 : k = 1
  · subst h1; simp
  · by_cases h2 : k = 2
    · subst h2; simp
    · by_cases h3 : k = 3
      · subst h3; simp
      · simp [h1, h2, h3]

theorem card725 (n : ℕ) (hn : n ≠ 0) :
    Nat.card {A : Fin (n + 1) → Fin 7 → Fin 3 // isValid n A} =
      40 + 2 * 2 ^ ((n + 1) / 2) + 4 * 2 ^ (n / 2) := by
  rw [card_eq725, sum_rows725]
  simp only [T725_closed n, hv725_split n _ hn]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  obtain ⟨c1, c2, c3⟩ := counts725
  rw [c1, c2, c3]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a209725.main := by
  constructor
  · intro n hn he
    obtain ⟨k, rfl⟩ := he
    have hk : 1 ≤ k := by omega
    unfold OMA.S_oeis_a209725.a
    rw [OMA.Helpers.card725 (k + k) (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show (j + 1 + (j + 1)) / 2 - 1 = j by omega, show (j + 1 + (j + 1) + 1) / 2 = j + 1 by omega,
      show (j + 1 + (j + 1)) / 2 = j + 1 by omega, pow_succ]
    omega
  · intro n hn ho
    obtain ⟨k, rfl⟩ := ho
    unfold OMA.S_oeis_a209725.a
    rw [OMA.Helpers.card725 (2 * k + 1) (by omega)]
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega, pow_succ]
    omega
