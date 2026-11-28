import OMAStatements.S_oeis_a353047
import Mathlib

namespace OMA.Helpers_a353047
open OMA.S_oeis_a353047

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

/-- the row vector of the recurrence `12 u(n) - 40 u(n+1) + 51 u(n+2) - 31 u(n+3) + 9 u(n+4) - u(n+5)`
started `m` steps in -/
def chkL (fL : List ℤ) (m : ℕ) : Bool :=
  (List.finRange K).all fun i => 12 * (itRL M m fL).getD i 0 - 40 * (itRL M (m + 1) fL).getD i 0 +
    51 * (itRL M (m + 2) fL).getD i 0 - 31 * (itRL M (m + 3) fL).getD i 0 +
    9 * (itRL M (m + 4) fL).getD i 0 - (itRL M (m + 5) fL).getD i 0 == 0

theorem rec_of_check (fL : List ℤ) (m : ℕ) (h : chkL M fL m = true) (v : Fin K → ℤ) (n : ℕ) :
    let u := fun t => ∑ j : Fin K, fL.getD (j : ℕ) 0 * itF M t v j
    12 * u (n + m) - 40 * u (n + m + 1) + 51 * u (n + m + 2) - 31 * u (n + m + 3) +
      9 * u (n + m + 4) - u (n + m + 5) = 0 := by
  intro u
  unfold chkL at h
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, itRL_eq] at h
  simp only [u]
  rw [show n + m = m + n by omega, show m + n + 1 = (m + 1) + n by omega, show m + n + 2 = (m + 2) + n by omega,
    show m + n + 3 = (m + 3) + n by omega, show m + n + 4 = (m + 4) + n by omega,
    show m + n + 5 = (m + 5) + n by omega]
  rw [itF_add M m n, itF_add M (m + 1) n, itF_add M (m + 2) n, itF_add M (m + 3) n, itF_add M (m + 4) n,
    itF_add M (m + 5) n]
  rw [adj M m, adj M (m + 1), adj M (m + 2), adj M (m + 3), adj M (m + 4), adj M (m + 5)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := h i
  linear_combination (itF M n v i) * this

end Gen

/-! Words: the automaton of seen letters and seen pairs -/

abbrev St := (Fin 3 → Bool) × (Fin 3 → Fin 3 → Bool)

/-- one letter more: `s.1 x` records that the letter `x` was seen, `s.2 x y` that the pair `xy`
was seen as a subword. -/
def dl (s : St) (c : Fin 3) : St :=
  (fun x => s.1 x || decide (x = c), fun x y => s.2 x y || (decide (y = c) && s.1 x && decide (x ≠ c)))

def st : (n : ℕ) → (Fin n → Fin 3) → St
  | 0, _ => (fun _ => false, fun _ _ => false)
  | n + 1, w => dl (st n (Fin.init w)) (w (Fin.last n))

theorem ex_succ {n : ℕ} (w : Fin (n + 1) → Fin 3) (x : Fin 3) :
    (∃ i, w i = x) ↔ (∃ i, Fin.init w i = x) ∨ w (Fin.last n) = x := by
  rw [Fin.exists_fin_succ']; rfl

theorem hs_succ {n : ℕ} (w : Fin (n + 1) → Fin 3) (x y : Fin 3) :
    HasSubword w x y ↔ HasSubword (Fin.init w) x y ∨ (w (Fin.last n) = y ∧ ∃ i, Fin.init w i = x) := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · have hi' : (i : ℕ) < n := by have := Fin.lt_def.mp hij; simp at this; omega
      left
      refine ⟨⟨i, hi'⟩, j', ?_, hi, hj⟩
      rw [Fin.lt_def]; have := Fin.lt_def.mp hij; simpa using this
    · right
      have hi' : (i : ℕ) < n := Fin.lt_def.mp hij
      exact ⟨hj, ⟨i, hi'⟩, hi⟩
  · rintro (⟨i, j, hij, hi, hj⟩ | ⟨hl, i, hi⟩)
    · exact ⟨Fin.castSucc i, Fin.castSucc j, Fin.castSucc_lt_castSucc_iff.mpr hij, hi, hj⟩
    · exact ⟨Fin.castSucc i, Fin.last n, Fin.castSucc_lt_last i, hi, hl⟩

theorem sem : ∀ (n : ℕ) (w : Fin n → Fin 3),
    (∀ x : Fin 3, (st n w).1 x = true ↔ ∃ i, w i = x) ∧
      ∀ x y : Fin 3, x ≠ y → ((st n w).2 x y = true ↔ HasSubword w x y) := by
  intro n
  induction n with
  | zero =>
    intro w
    refine ⟨fun x => ?_, fun x y _ => ?_⟩
    · simp only [st, Bool.false_eq_true, false_iff, not_exists]; intro i; exact i.elim0
    · simp only [st, Bool.false_eq_true, false_iff]; rintro ⟨i, _, _⟩; exact i.elim0
  | succ n ih =>
    intro w
    obtain ⟨h1, h2⟩ := ih (Fin.init w)
    refine ⟨fun x => ?_, fun x y hxy => ?_⟩
    · show (dl (st n (Fin.init w)) (w (Fin.last n))).1 x = true ↔ _
      rw [ex_succ, ← h1]
      simp only [dl, Bool.or_eq_true, decide_eq_true_eq]
      exact or_congr Iff.rfl eq_comm
    · show (dl (st n (Fin.init w)) (w (Fin.last n))).2 x y = true ↔ _
      rw [hs_succ, ← h2 x y hxy, ← h1]
      simp only [dl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h | ⟨⟨h, h'⟩, _⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h.symm, h'⟩
      · rintro (h | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨⟨h.symm, h'⟩, by rw [h]; exact hxy⟩

/-- states coded as (letters, pairs) bit masks; decoding -/
def dec (s : ℕ × ℕ) : St := (fun x => s.1.testBit x, fun x y => s.2.testBit (3 * x + y))

def Rl : List (ℕ × ℕ) := [(0, 0), (1, 0), (2, 0), (4, 0), (3, 2), (5, 4), (3, 8), (6, 32), (5, 64), (6, 128), (3, 10), (7, 38), (5, 68), (7, 134), (7, 44), (7, 104), (6, 160), (7, 194), (7, 200), (7, 46), (7, 110), (7, 166), (7, 198), (7, 206), (7, 108), (7, 174), (7, 234), (7, 232), (7, 202), (7, 230), (7, 236), (7, 238)]

def Rg (i : Fin 32) : St := dec (Rl.getD i (0, 0))

theorem closed : ∀ i : Fin 32, ∀ c : Fin 3, ∃ j : Fin 32, dl (Rg i) c = Rg j := by decide

theorem Rg_inj : ∀ i j : Fin 32, Rg i = Rg j → i = j := by decide

theorem reach : ∀ (n : ℕ) (w : Fin n → Fin 3), ∃ i : Fin 32, st n w = Rg i := by
  intro n
  induction n with
  | zero =>
    intro w
    refine ⟨0, ?_⟩
    show ((fun _ => false, fun _ _ => false) : St) = dec (Rl.getD 0 (0, 0))
    rw [show Rl.getD 0 (0, 0) = (0, 0) from rfl]
    simp [dec]
  | succ n ih =>
    intro w
    obtain ⟨i, hi⟩ := ih (Fin.init w)
    obtain ⟨j, hj⟩ := closed i (w (Fin.last n))
    exact ⟨j, by show dl (st n (Fin.init w)) (w (Fin.last n)) = _; rw [hi, hj]⟩

theorem acc_iff : ∀ i : Fin 32, (∀ x y : Fin 3, x ≠ y → (Rg i).2 x y = true) ↔ i = 31 := by
  decide

def cnt (n : ℕ) (i : Fin 32) : ℕ := (Finset.univ.filter (fun w : Fin n → Fin 3 => st n w = Rg i)).card

theorem a_cnt (n : ℕ) : a n = cnt n 31 := by
  unfold a cnt
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨i, hi⟩ := reach n w
  rw [hi]
  constructor
  · intro h
    have : i = 31 := (acc_iff i).mp fun x y hxy => by
      rw [← hi]; exact ((sem n w).2 x y hxy).mpr (h x y hxy)
    rw [this]
  · intro h x y hxy
    have h31 : i = 31 := Rg_inj _ _ h
    have := (acc_iff i).mpr h31 x y hxy
    rw [← hi] at this
    exact ((sem n w).2 x y hxy).mp this

def Mn (i j : Fin 32) : ℕ := (Finset.univ.filter fun c : Fin 3 => dl (Rg i) c = Rg j).card

def MT : List (List ℕ) := [[0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]]

theorem Mn_eq : ∀ i j : Fin 32, Mn i j = (MT.getD i []).getD j 0 := by decide

def Mw (i j : Fin 32) : ℤ := (((MT.getD i []).getD j 0 : ℕ) : ℤ)

theorem st_snoc (n : ℕ) (v : Fin n → Fin 3) (c : Fin 3) : st (n + 1) (Fin.snoc v c) = dl (st n v) c := by
  simp [st, Fin.init_snoc, Fin.snoc_last]

theorem cnt_succ (n : ℕ) (j : Fin 32) : cnt (n + 1) j = ∑ i, Mn i j * cnt n i := by
  unfold cnt Mn
  simp only [Finset.card_filter]
  have e : (∑ w : Fin (n + 1) → Fin 3, if st (n + 1) w = Rg j then 1 else 0) =
      ∑ c : Fin 3, ∑ v : Fin n → Fin 3, if dl (st n v) c = Rg j then 1 else 0 := by
    rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin 3) _ _ (fun _ => rfl), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun v _ => ?_
    show (if st (n + 1) (Fin.snoc v c) = Rg j then 1 else 0) = _
    rw [st_snoc]
  rw [e]
  symm
  calc ∑ i, (∑ c : Fin 3, if dl (Rg i) c = Rg j then 1 else 0) *
        (∑ v : Fin n → Fin 3, if st n v = Rg i then 1 else 0)
      = ∑ i, ∑ c : Fin 3, ∑ v : Fin n → Fin 3,
          (if dl (Rg i) c = Rg j then 1 else 0) * (if st n v = Rg i then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ c : Fin 3, ∑ v : Fin n → Fin 3, ∑ i,
          (if dl (Rg i) c = Rg j then 1 else 0) * (if st n v = Rg i then 1 else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ c : Fin 3, ∑ v : Fin n → Fin 3, if dl (st n v) c = Rg j then 1 else 0 := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun v _ => ?_
        obtain ⟨k, hk⟩ := reach n v
        rw [Finset.sum_eq_single k]
        · rw [hk]; simp
        · intro i _ hik
          have : st n v ≠ Rg i := by rw [hk]; exact fun h => hik (Rg_inj _ _ h).symm
          simp [this]
        · simp

def v0 : Fin 32 → ℤ := fun i => (basisL (0 : Fin 32)).getD i 0

theorem cnt_it (n : ℕ) : (fun i => (cnt n i : ℤ)) = itF Mw n v0 := by
  induction n with
  | zero =>
    funext i
    show ((Finset.univ.filter (fun w : Fin 0 → Fin 3 => st 0 w = Rg i)).card : ℤ) = v0 i
    rw [v0, basisL_getD, Pi.single_apply]
    have h0 : ∀ w : Fin 0 → Fin 3, st 0 w = Rg 0 := fun w => by
      show ((fun _ => false, fun _ _ => false) : St) = dec (Rl.getD 0 (0, 0))
      rw [show Rl.getD 0 (0, 0) = (0, 0) from rfl]
      simp [dec]
    by_cases hi : i = 0
    · subst hi; simp [h0]
    · have : ∀ w : Fin 0 → Fin 3, st 0 w ≠ Rg i := fun w h => hi (Rg_inj _ _ (by rw [← h, h0])).symm
      simp [this, hi]
  | succ n ih =>
    funext j
    show (cnt (n + 1) j : ℤ) = ∑ i, Mw i j * itF Mw n v0 i
    rw [← ih, cnt_succ]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Mn_eq]; rfl

def fA : Fin 32 → ℤ := fun i => if i = 31 then 1 else 0

theorem a_it (n : ℕ) : (a n : ℤ) = ∑ j, fA j * itF Mw n v0 j := by
  rw [← cnt_it, a_cnt, Finset.sum_eq_single (31 : Fin 32)]
  · simp [fA]
  · intro b _ hb; simp [fA, hb]
  · simp

def fAL : List ℤ := (List.finRange 32).map fun i => if i = 31 then 1 else 0

theorem chkA : chkL Mw fAL 1 = true := by decide +kernel

theorem recA (t : ℕ) : 12 * (a (t + 1) : ℤ) - 40 * a (t + 2) + 51 * a (t + 3) - 31 * a (t + 4) +
    9 * a (t + 5) - a (t + 6) = 0 := by
  have := rec_of_check Mw fAL 1 chkA v0 t
  have e : ∀ s, ∑ j : Fin 32, fAL.getD (j : ℕ) 0 * itF Mw s v0 j = (a s : ℤ) := fun s => by
    rw [a_it]; refine Finset.sum_congr rfl fun j _ => ?_; rw [fAL, getD_map_finRange]; rfl
  simp only [e] at this
  rw [show t + 1 + 1 = t + 2 by omega, show t + 1 + 2 = t + 3 by omega, show t + 1 + 3 = t + 4 by omega,
    show t + 1 + 4 = t + 5 by omega, show t + 1 + 5 = t + 6 by omega] at this
  exact this

theorem a_val (n : ℕ) : (a n : ℤ) = (itL Mw n (basisL (0 : Fin 32))).getD 31 0 := by
  rw [a_it, Finset.sum_eq_single (31 : Fin 32)]
  · simp only [fA, if_true, one_mul]
    exact (itL_eq Mw n (basisL 0) 31).symm
  · intro b _ hb; simp [fA, hb]
  · simp

/-! Arrays -/

def dr (r : Fin 2 → Fin 3) : ℤ := ((r 1 : ℕ) : ℤ) - ((r 0 : ℕ) : ℤ)

theorem slope_row (r : Fin 2 → Fin 3) : S_oeis_a353047.slope (fun k => ((r k : ℕ) : ℚ)) = (dr r : ℚ) := by
  unfold S_oeis_a353047.slope dr
  rw [if_neg (by norm_num)]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  push_cast
  ring

abbrev GoodR {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Prop := ∀ i j : Fin n, (j : ℕ) = i + 1 → dr (A i) ≤ dr (A j)

theorem mono {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (h : GoodR A) : ∀ i j : Fin n, i ≤ j → dr (A i) ≤ dr (A j) := by
  intro i j hij
  obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = i + k := ⟨j - i, by have := Fin.le_def.mp hij; omega⟩
  induction k generalizing j with
  | zero => have : j = i := Fin.ext (by omega); rw [this]
  | succ k ih =>
    have hj1 : (i : ℕ) + k < n := by have := j.2; omega
    have := ih ⟨i + k, hj1⟩ (Fin.le_def.mpr (by simp)) rfl
    exact this.trans (h _ _ (by simp; omega))

theorem col_le {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (h : GoodR A) :
    S_oeis_a353047.slope (fun i => ((A i 0 : ℕ) : ℚ)) ≤ S_oeis_a353047.slope (fun i => ((A i 1 : ℕ) : ℚ)) := by
  unfold S_oeis_a353047.slope
  by_cases h1 : n = 1
  · simp [h1]
  rw [if_neg h1, if_neg h1]
  apply div_le_div_of_nonneg_right
  · have hm : Monovary (fun i : Fin n => (((A i 1 : ℕ) : ℚ) - ((A i 0 : ℕ) : ℚ))) (fun i : Fin n => (((i : ℕ) : ℚ) + 1)) := by
      intro i j hij
      have : i < j := by rw [Fin.lt_def]; exact_mod_cast (by linarith : ((i : ℕ) : ℚ) < (j : ℕ))
      have := mono A h i j this.le
      unfold dr at this
      show ((A i 1 : ℕ) : ℚ) - ((A i 0 : ℕ) : ℚ) ≤ ((A j 1 : ℕ) : ℚ) - ((A j 0 : ℕ) : ℚ)
      exact_mod_cast this
    have key := hm.sum_mul_sum_le_card_mul_sum
    simp only [Fintype.card_fin] at key
    have e1 : ∑ i : Fin n, (((A i 1 : ℕ) : ℚ) - ((A i 0 : ℕ) : ℚ)) * (((i : ℕ) : ℚ) + 1) =
        ∑ i : Fin n, (((i : ℕ) : ℚ) + 1) * ((A i 1 : ℕ) : ℚ) - ∑ i : Fin n, (((i : ℕ) : ℚ) + 1) * ((A i 0 : ℕ) : ℚ) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    have e2 : ∑ i : Fin n, (((A i 1 : ℕ) : ℚ) - ((A i 0 : ℕ) : ℚ)) =
        ∑ i : Fin n, ((A i 1 : ℕ) : ℚ) - ∑ i : Fin n, ((A i 0 : ℕ) : ℚ) := Finset.sum_sub_distrib ..
    rw [e1, e2] at key
    nlinarith [key]
  · have := (monovary_self (fun i : Fin n => (((i : ℕ) : ℚ) + 1))).sum_mul_sum_le_card_mul_sum
    simp only [Fintype.card_fin] at this
    simp only [sq]
    linarith

theorem good_iff {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Good A ↔ GoodR A := by
  constructor
  · rintro ⟨h1, _⟩ i j hij
    have := h1 i j hij
    rw [slope_row, slope_row] at this
    exact_mod_cast this
  · intro h
    refine ⟨fun i j hij => ?_, col_le A h⟩
    rw [slope_row, slope_row]
    exact_mod_cast h i j hij

theorem dr_bounds (r : Fin 2 → Fin 3) : -2 ≤ dr r ∧ dr r ≤ 2 := by
  unfold dr; have h0 := (r 0).2; have h1 := (r 1).2; constructor <;> omega

def kOf (r : Fin 2 → Fin 3) : Fin 5 := ⟨(dr r + 2).toNat, by have := dr_bounds r; omega⟩

theorem kOf_eq (r : Fin 2 → Fin 3) (k : Fin 5) : dr r = (k : ℤ) - 2 ↔ k = kOf r := by
  have := dr_bounds r
  constructor
  · intro h; apply Fin.ext; simp [kOf, h]
  · intro h; subst h; simp [kOf]; omega

def mB (k : Fin 5) : ℕ := (Finset.univ.filter fun r : Fin 2 → Fin 3 => dr r = (k : ℤ) - 2).card

def cntB (n : ℕ) (k : Fin 5) : ℕ :=
  (Finset.univ.filter fun A : Fin (n + 1) → Fin 2 → Fin 3 => GoodR A ∧ dr (A (Fin.last n)) = (k : ℤ) - 2).card

theorem collapse (r : Fin 2 → Fin 3) (g : Fin 5 → ℕ) :
    ∑ k : Fin 5, (if dr r = (k : ℤ) - 2 then g k else 0) = g (kOf r) := by
  rw [Finset.sum_eq_single (kOf r)]
  · rw [if_pos ((kOf_eq r _).mpr rfl)]
  · intro k _ hk; rw [if_neg (fun h => hk ((kOf_eq r k).mp h))]
  · simp

theorem b_cnt (n : ℕ) : b (n + 1) = ∑ k, cntB n k := by
  unfold b cntB
  simp only [Finset.card_filter, good_iff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  have := collapse (A (Fin.last n)) (fun _ => if GoodR A then 1 else 0)
  rw [← this]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : GoodR A <;> by_cases h2 : dr (A (Fin.last n)) = (k : ℤ) - 2 <;> simp [h1, h2]

theorem goodR_snoc {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 3) (r : Fin 2 → Fin 3) :
    GoodR (Fin.snoc A r : Fin (n + 2) → Fin 2 → Fin 3) ↔ GoodR A ∧ dr (A (Fin.last n)) ≤ dr r := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ?_⟩
    · have := h (Fin.castSucc i) (Fin.castSucc j) (by simpa using hij)
      simpa [Fin.snoc_castSucc] using this
    · have := h (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)) (by simp)
      simpa [Fin.snoc_castSucc, Fin.snoc_last] using this
  · rintro ⟨h1, h2⟩ i j hij
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · have hi : (i : ℕ) < n + 1 := by have := j'.2; simp at hij; omega
      obtain ⟨i', rfl⟩ : ∃ i', i = Fin.castSucc i' := ⟨⟨i, hi⟩, rfl⟩
      simp only [Fin.snoc_castSucc]
      exact h1 i' j' (by simpa using hij)
    · have hi : i = Fin.castSucc (Fin.last n) := Fin.ext (by simp at hij ⊢; omega)
      subst hi
      simpa [Fin.snoc_castSucc, Fin.snoc_last] using h2

def MBn (k k' : Fin 5) : ℕ := if k ≤ k' then mB k' else 0

theorem cntB_succ (n : ℕ) (k' : Fin 5) : cntB (n + 1) k' = ∑ k, MBn k k' * cntB n k := by
  unfold cntB MBn mB
  simp only [Finset.card_filter]
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin 2 → Fin 3) _ _ (fun _ => rfl), Fintype.sum_prod_type]
  have e : ∀ (r : Fin 2 → Fin 3) (A : Fin (n + 1) → Fin 2 → Fin 3),
      (if GoodR ((Fin.snocEquiv fun _ => Fin 2 → Fin 3) (r, A)) ∧
          dr ((Fin.snocEquiv fun _ => Fin 2 → Fin 3) (r, A) (Fin.last (n + 1))) = (k' : ℤ) - 2 then 1 else 0) =
        ∑ k : Fin 5, (if k ≤ k' then (if dr r = (k' : ℤ) - 2 then 1 else 0) else 0) *
          (if GoodR A ∧ dr (A (Fin.last n)) = (k : ℤ) - 2 then 1 else 0) := by
    intro r A
    show (if GoodR (Fin.snoc A r : Fin (n + 2) → Fin 2 → Fin 3) ∧
        dr ((Fin.snoc A r : Fin (n + 2) → Fin 2 → Fin 3) (Fin.last (n + 1))) = (k' : ℤ) - 2 then 1 else 0) = _
    simp only [goodR_snoc, Fin.snoc_last]
    have := collapse (A (Fin.last n))
      (fun k => (if k ≤ k' then (if dr r = (k' : ℤ) - 2 then 1 else 0) else 0) * (if GoodR A then 1 else 0))
    rw [show (∑ k : Fin 5, (if k ≤ k' then (if dr r = (k' : ℤ) - 2 then 1 else 0) else 0) *
          (if GoodR A ∧ dr (A (Fin.last n)) = (k : ℤ) - 2 then 1 else 0)) =
        ∑ k : Fin 5, (if dr (A (Fin.last n)) = (k : ℤ) - 2 then
          (if k ≤ k' then (if dr r = (k' : ℤ) - 2 then 1 else 0) else 0) * (if GoodR A then 1 else 0) else 0) from
      Finset.sum_congr rfl fun k _ => by
        by_cases h1 : GoodR A <;> by_cases h2 : dr (A (Fin.last n)) = (k : ℤ) - 2 <;> simp [h1, h2]]
    rw [this]
    have hk : kOf (A (Fin.last n)) ≤ k' ↔ dr (A (Fin.last n)) ≤ (k' : ℤ) - 2 := by
      have := dr_bounds (A (Fin.last n)); rw [Fin.le_def]; simp only [kOf]; omega
    simp only [hk]
    by_cases h1 : GoodR A <;> by_cases h2 : dr r = (k' : ℤ) - 2 <;>
      by_cases h3 : dr (A (Fin.last n)) ≤ (k' : ℤ) - 2 <;> simp only [h1, h2, h3, and_true, and_false,
        false_and, if_true, if_false, mul_zero] <;> simp_all
  simp only [e]
  rw [show (∑ r : Fin 2 → Fin 3, ∑ A : Fin (n + 1) → Fin 2 → Fin 3, ∑ k : Fin 5,
      (if k ≤ k' then (if dr r = (k' : ℤ) - 2 then (1 : ℕ) else 0) else 0) *
        (if GoodR A ∧ dr (A (Fin.last n)) = (k : ℤ) - 2 then (1 : ℕ) else 0)) =
      ∑ k : Fin 5, (∑ r : Fin 2 → Fin 3, (if k ≤ k' then (if dr r = (k' : ℤ) - 2 then (1 : ℕ) else 0) else 0)) *
        (∑ A : Fin (n + 1) → Fin 2 → Fin 3, (if GoodR A ∧ dr (A (Fin.last n)) = (k : ℤ) - 2 then (1 : ℕ) else 0)) from by
    simp only [Finset.sum_mul_sum]
    exact (Finset.sum_congr rfl fun r _ => Finset.sum_comm).trans Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

def mBL : List ℤ := [1, 2, 3, 2, 1]

theorem mB_eq : ∀ k : Fin 5, (mB k : ℤ) = mBL.getD k 0 := by decide

theorem cntB_zero : ∀ k : Fin 5, cntB 0 k = mB k := by decide

def MB (k k' : Fin 5) : ℤ := if k ≤ k' then mBL.getD k' 0 else 0

def v1 : Fin 5 → ℤ := fun k => mBL.getD k 0

theorem cntB_it (n : ℕ) : (fun k => (cntB n k : ℤ)) = itF MB n v1 := by
  induction n with
  | zero => funext k; rw [cntB_zero, mB_eq]; rfl
  | succ n ih =>
    funext k'
    show (cntB (n + 1) k' : ℤ) = ∑ k, MB k k' * itF MB n v1 k
    rw [← ih, cntB_succ]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold MBn MB
    split_ifs
    · rw [mB_eq]
    · simp

theorem b_it (n : ℕ) : (b (n + 1) : ℤ) = ∑ k, itF MB n v1 k := by
  rw [b_cnt]; push_cast; rw [← cntB_it]

def onesL : List ℤ := [1, 1, 1, 1, 1]

theorem chkB : chkL MB onesL 0 = true := by decide +kernel

theorem recB (t : ℕ) : 12 * (b (t + 1) : ℤ) - 40 * b (t + 2) + 51 * b (t + 3) - 31 * b (t + 4) +
    9 * b (t + 5) - b (t + 6) = 0 := by
  have := rec_of_check MB onesL 0 chkB v1 t
  have e : ∀ s, ∑ j : Fin 5, onesL.getD (j : ℕ) 0 * itF MB s v1 j = (b (s + 1) : ℤ) := fun s => by
    rw [b_it]; refine Finset.sum_congr rfl fun j _ => ?_; fin_cases j <;> simp [onesL]
  simp only [e] at this
  rw [show t + 0 = t by omega] at this
  exact this

theorem b1 : (b 1 : ℤ) = 9 := by rw [b_it]; decide +kernel
theorem b2 : (b 2 : ℤ) = 50 := by rw [b_it]; decide +kernel
theorem b3 : (b 3 : ℤ) = 222 := by rw [b_it]; decide +kernel
theorem b4 : (b 4 : ℤ) = 867 := by rw [b_it]; decide +kernel
theorem b5 : (b 5 : ℤ) = 3123 := by rw [b_it]; decide +kernel
theorem a6 : (a 6 : ℤ) = 108 := by rw [a_val]; decide +kernel
theorem a7 : (a 7 : ℤ) = 600 := by rw [a_val]; decide +kernel
theorem a8 : (a 8 : ℤ) = 2664 := by rw [a_val]; decide +kernel
theorem a9 : (a 9 : ℤ) = 10404 := by rw [a_val]; decide +kernel
theorem a10 : (a 10 : ℤ) = 37476 := by rw [a_val]; decide +kernel

theorem key : ∀ n : ℕ, 1 ≤ n → (a (n + 5) : ℤ) = 12 * (b n : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n ≤ 5
    · interval_cases n
      · rw [a6, b1]; norm_num
      · rw [a7, b2]; norm_num
      · rw [a8, b3]; norm_num
      · rw [a9, b4]; norm_num
      · rw [a10, b5]; norm_num
    · have r1 := recA (n - 1)
      rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega, show n - 1 + 3 = n + 2 by omega,
        show n - 1 + 4 = n + 3 by omega, show n - 1 + 5 = n + 4 by omega, show n - 1 + 6 = n + 5 by omega] at r1
      have r2 := recB (n - 6)
      rw [show n - 6 + 1 = n - 5 by omega, show n - 6 + 2 = n - 4 by omega, show n - 6 + 3 = n - 3 by omega,
        show n - 6 + 4 = n - 2 by omega, show n - 6 + 5 = n - 1 by omega, show n - 6 + 6 = n by omega] at r2
      have i0 : (a n : ℤ) = 12 * b (n - 5) := by
        have := ih (n - 5) (by omega) (by omega); rwa [show n - 5 + 5 = n by omega] at this
      have i1 : (a (n + 1) : ℤ) = 12 * b (n - 4) := by
        have := ih (n - 4) (by omega) (by omega); rwa [show n - 4 + 5 = n + 1 by omega] at this
      have i2 : (a (n + 2) : ℤ) = 12 * b (n - 3) := by
        have := ih (n - 3) (by omega) (by omega); rwa [show n - 3 + 5 = n + 2 by omega] at this
      have i3 : (a (n + 3) : ℤ) = 12 * b (n - 2) := by
        have := ih (n - 2) (by omega) (by omega); rwa [show n - 2 + 5 = n + 3 by omega] at this
      have i4 : (a (n + 4) : ℤ) = 12 * b (n - 1) := by
        have := ih (n - 1) (by omega) (by omega); rwa [show n - 1 + 5 = n + 4 by omega] at this
      linear_combination (-1 : ℤ) * r1 + 12 * i0 - 40 * i1 + 51 * i2 - 31 * i3 + 9 * i4 + 12 * r2

end OMA.Helpers_a353047

open OMA.Helpers_a353047 in
theorem OMA.solution : type_of% @OMA.S_oeis_a353047.main := by
  intro n hn
  exact_mod_cast key n hn
