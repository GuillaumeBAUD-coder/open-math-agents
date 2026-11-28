import OMAStatements.S_oeis_a312105

namespace OMA.S_oeis_a312105






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 11

/-- Field k of the B-bit fields packed in the natural number T, as stored. The table accessors call
the kernel's natural number primitives directly: through the operators' type-class instances the
kernel decisions take more memory. -/
def tgetN (T B k : ℕ) : ℕ := Nat.mod (Nat.shiftRight T (Nat.mul B k)) (Nat.pow 2 B)

/-- Field k of the B-bit fields packed in T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := Int.subNatNat (tgetN T B k) off

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 1697950940
  | 1 => 1430699210
  | 2 => 2002099131
  | 3 => 1716956090
  | 4 => 1429585371
  | 5 => 2003212970
  | 6 => 2862049145
  | 7 => 2307426696
  | 8 => 2575792265
  | 9 => 2021104281
  | 10 => 2289469850
  | _ => 0

/-- The potential t is Ac t * x + Bc t * y + Cc s t at (x, y, s) (packed tables). -/
def Ac (i : Fin 8) : ℤ := tget 1737140614 4 8 i.val

def Bc (i : Fin 8) : ℤ := tget 3741004309 4 8 i.val

def Cc (s : Fin 11) (i : Fin 8) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The potential t at v. -/
def pot (v : V) (i : Fin 8) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest potential at v. -/
def F (v : V) : ℤ := max (max (max (max (max (max (max (pot v 0) (pot v 1)) (pot v 2)) (pot v 3)) (pot v 4)) (pot v 5)) (pot v 6)) (pot v 7)

theorem le_F0 (v : V) : pot v 0 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))))))
theorem le_F1 (v : V) : pot v 1 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))
theorem le_F2 (v : V) : pot v 2 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))
theorem le_F3 (v : V) : pot v 3 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))
theorem le_F4 (v : V) : pot v 4 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
theorem le_F5 (v : V) : pot v 5 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
theorem le_F6 (v : V) : pot v 6 ≤ F v := le_max_of_le_left (le_max_right _ _)
theorem le_F7 (v : V) : pot v 7 ≤ F v := le_max_right _ _

theorem le_F (v : V) (i : Fin 8) : pot v i ≤ F v := by
  fin_cases i
  exacts [le_F0 v, le_F1 v, le_F2 v, le_F3 v, le_F4 v, le_F5 v, le_F6 v, le_F7 v]

theorem F_le (v : V) (t : ℤ) (h0 : pot v 0 ≤ t) (h1 : pot v 1 ≤ t) (h2 : pot v 2 ≤ t) (h3 : pot v 3 ≤ t) (h4 : pot v 4 ≤ t) (h5 : pot v 5 ≤ t) (h6 : pot v 6 ≤ t) (h7 : pot v 7 ≤ t) : F v ≤ t :=
  max_le (max_le (max_le (max_le (max_le (max_le (max_le (h0) h1) h2) h3) h4) h5) h6) h7

theorem F_le_all (v : V) (t : ℤ) (h : ∀ i, pot v i ≤ t) : F v ≤ t :=
  F_le v t (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)

theorem max_ex {v : V} {a b : ℤ} (ha : ∃ i, a = pot v i) (hb : ∃ i, b = pot v i) :
    ∃ i, max a b = pot v i := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem exists_F (v : V) : ∃ i, F v = pot v i :=
  max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (⟨0, rfl⟩) ⟨1, rfl⟩) ⟨2, rfl⟩) ⟨3, rfl⟩) ⟨4, rfl⟩) ⟨5, rfl⟩) ⟨6, rfl⟩) ⟨7, rfl⟩

/-- The level of class s beyond which the far argument runs (the near box of class s covers the rest). -/
def R0N (s : Fin 11) : ℕ := tgetN 7479983605 3 s.val

def R0c (s : Fin 11) : ℤ := (R0N s : ℤ)

/-- The pairs (class s, potential t) and the classes whose rule, far, side and near checks are made;
here all of them. -/
def repB (s : Fin 11) (t : Fin 8) : Bool := decide (tgetN 309485009821345068724781055 1 (s.val * 8 + t.val) = 1)

def repC (s : Fin 11) : Bool := decide (tgetN 2047 1 s.val = 1)

/-- The change of the potential j along the edge e. -/
def dl (e : Fin 11 × Fin 11 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

/-- Along an edge e the potential j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 11 × Fin 11 × ℤ × ℤ) (j : Fin 8) :
    pot (x + e.2.2.1, y + e.2.2.2, e.2.1) j = pot (x, y, e.1) j + dl e j := by
  simp only [pot, dl]
  ring

theorem pair_of {a f b : ℤ} (hl : a ≤ f) (hf : f = b) : a ≤ b + 0 := by omega

theorem bound_of {r f b : ℤ} (hr : r < f) (hf : f = b) : r + 1 ≤ b := by omega

theorem not_pair2 {a b : ℤ} (h : ¬ a ≤ b + (-2)) : b ≤ a + 1 := by omega

/-- Three facts pot a_k ≤ pot b_k + t_k and a bound r ≤ pot i0 at (x, y, s), with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas (x y : ℤ) (s : Fin 11) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
    (hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ l0 ∧
      l1 * (Ac a1 - Ac b1) + l2 * (Ac a2 - Ac b2) + l3 * (Ac a3 - Ac b3) - l0 * Ac i0 = 0 ∧
      l1 * (Bc a1 - Bc b1) + l2 * (Bc a2 - Bc b2) + l3 * (Bc a3 - Bc b3) - l0 * Bc i0 = 0 ∧
      0 < l1 * (Cc s a1 - Cc s b1 - t1) + l2 * (Cc s a2 - Cc s b2 - t2) +
        l3 * (Cc s a3 - Cc s b3 - t3) + l0 * (r - Cc s i0))
    (h1 : pot (x, y, s) a1 ≤ pot (x, y, s) b1 + t1) (h2 : pot (x, y, s) a2 ≤ pot (x, y, s) b2 + t2)
    (h3 : pot (x, y, s) a3 ≤ pot (x, y, s) b3 + t3) (h0 : r ≤ pot (x, y, s) i0) : False := by
  obtain ⟨hl1, hl2, hl3, hl0, hx, hy, hk⟩ := hc
  have e1 := mul_le_mul_of_nonneg_left h1 hl1
  have e2 := mul_le_mul_of_nonneg_left h2 hl2
  have e3 := mul_le_mul_of_nonneg_left h3 hl3
  have e0 := mul_le_mul_of_nonneg_left h0 hl0
  have hx' : (l1 * (Ac a1 - Ac b1) + l2 * (Ac a2 - Ac b2) + l3 * (Ac a3 - Ac b3) - l0 * Ac i0) * x = 0 := by
    rw [hx, zero_mul]
  have hy' : (l1 * (Bc a1 - Bc b1) + l2 * (Bc a2 - Bc b2) + l3 * (Bc a3 - Bc b3) - l0 * Bc i0) * y = 0 := by
    rw [hy, zero_mul]
  simp only [pot] at e1 e2 e3 e0
  nlinarith [e1, e2, e3, e0, hx', hy', hk]

/-- The neighbor slots of potential t: slots 0 and 1 on the side of the previous potentials and
slots 2 and 3 on the side of the next ones, nearest first; unused slots hold t itself. -/
def nb (t : Fin 8) (k : Fin 4) : Fin 8 :=
  ⟨(tget 70231289244858540414179246151 3 0 (t.val * 4 + k.val)).toNat % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The slot k of t holds another potential. -/
def real (t : Fin 8) (k : Fin 4) : Bool := decide (nb t k ≠ t)

/-- The potential t is a facet: a slot on each side cannot both come within 1 of t beyond R0c. -/
def facetB (t : Fin 8) : Bool := decide (tget 187 1 0 t.val = 1)

/-- The potential j is neither t nor in a slot of t. -/
def nonadj (t j : Fin 8) : Bool :=
  decide (j ≠ t) && decide (j ≠ nb t 0) && decide (j ≠ nb t 1) && decide (j ≠ nb t 2) && decide (j ≠ nb t 3)

/-- Certificates of the far facts, the same for every class: for maximal potential t and a potential
j that is not a neighbor of t, the fields k1, k2, m1, m2, m0, mj of entry t * 8 + j give the facts
pot k1 ≤ pot t, pot k2 ≤ pot t, R0c s + 1 ≤ pot t and pot t ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fd (t j : Fin 8) (f : ℕ) : ℤ := tget 1900725663945210632313904646876609511373243831699599314313450579689276662872328987147309900083047644896782360812317423526505970101854249742064170092264445915219702442504415947591051854669858647357708621781291156996147029968561778452386643849753298697212792902686927768543083161710424847190149234954120989857081162756357859851748524737372218878766545864896507085081706078023104454016672188601241820752970800789850399107698590057421318298061566805187940860489147015468937680026666644373549723507673028004839819427743965385587607366630850462271922999594013560875903901647334872703534805028779988247579853198984442097434608397889822738067286254537451558184857100755627024880792822219905056993576992 6 32 ((t.val * 8 + j.val) * 6 + f)

def fk1 (t j : Fin 8) : Fin 8 := ⟨(fd t j 0).toNat % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (t j : Fin 8) : Fin 8 := ⟨(fd t j 1).toNat % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The x and y parts of the far certificate of (t, j) cancel. -/
def farXY (t j : Fin 8) : Bool :=
  decide (0 ≤ fd t j 2 ∧ 0 ≤ fd t j 3 ∧ 0 ≤ fd t j 5 ∧ 0 ≤ fd t j 4 ∧
    fd t j 2 * (Ac (fk1 t j) - Ac t) + fd t j 3 * (Ac (fk2 t j) - Ac t) + fd t j 5 * (Ac t - Ac j) -
      fd t j 4 * Ac t = 0 ∧
    fd t j 2 * (Bc (fk1 t j) - Bc t) + fd t j 3 * (Bc (fk2 t j) - Bc t) + fd t j 5 * (Bc t - Bc j) -
      fd t j 4 * Bc t = 0)

/-- The constants of the far certificate of (t, j) at class s add up to a positive number. -/
def farC (s : Fin 11) (t j : Fin 8) : Bool :=
  decide (0 < fd t j 2 * (Cc s (fk1 t j) - Cc s t - 0) + fd t j 3 * (Cc s (fk2 t j) - Cc s t - 0) +
    fd t j 5 * (Cc s t - Cc s j - 1) + fd t j 4 * (R0c s + 1 - Cc s t))

/-- The far certificates of the maximal potential t are valid. -/
def farsOK (t : Fin 8) : Bool :=
  (List.finRange 8).all fun j => !nonadj t j || (farXY t j && (List.finRange 11).all fun s => !repB s t || farC s t j)

/-- Beyond F = R0c s, a potential that is not a neighbor of a maximal potential t has slack at least 2. -/
theorem far (s : Fin 11) (t j : Fin 8) (hxy : farXY t j = true) (hc0 : farC s t j = true) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) t) (hF : R0c s < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) t + (-2) := by
  by_contra hc
  have q := of_decide_eq_true hxy
  exact farkas x y s (fk1 t j) t (fk2 t j) t t j t 0 0 1 (R0c s + 1) (fd t j 2) (fd t j 3) (fd t j 5) (fd t j 4)
    ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, of_decide_eq_true hc0⟩
    (pair_of (le_F _ _) h) (pair_of (le_F _ _) h) (not_pair2 hc) (bound_of hF h)

/-- Certificates of the side facts, the same for every class: for a facet t, entry i of t, for the
slots (0, 2), (0, 3), (1, 2), (1, 3), has fields k, mk, mL, mR, m0 for the facts pot k ≤ pot t,
pot t ≤ pot (left slot) + 1, pot t ≤ pot (right slot) + 1 and R0c s + 1 ≤ pot t. -/
def sd (t : Fin 8) (i f : ℕ) : ℤ := tget 4950000769995820968246293558368545339907475817634121553291217288419310636670457532761862181788626165012079168615490829654237807395523463420184226836458429074663053856479154978490917344694379351671902201530214493477100745208834036618042904817776207719438740669661968226244919470314079053856 6 32 ((t.val * 4 + i) * 5 + f)

def sk (t : Fin 8) (i : ℕ) : Fin 8 := ⟨(sd t i 0).toNat % 8, Nat.mod_lt _ (by norm_num)⟩

def sideXY (t : Fin 8) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 ≤ sd t i 1 ∧ 0 ≤ sd t i 2 ∧ 0 ≤ sd t i 3 ∧ 0 ≤ sd t i 4 ∧
    sd t i 1 * (Ac (sk t i) - Ac t) + sd t i 2 * (Ac t - Ac (nb t kl)) + sd t i 3 * (Ac t - Ac (nb t kr)) -
      sd t i 4 * Ac t = 0 ∧
    sd t i 1 * (Bc (sk t i) - Bc t) + sd t i 2 * (Bc t - Bc (nb t kl)) + sd t i 3 * (Bc t - Bc (nb t kr)) -
      sd t i 4 * Bc t = 0)

def sideC (s : Fin 11) (t : Fin 8) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 < sd t i 1 * (Cc s (sk t i) - Cc s t - 0) + sd t i 2 * (Cc s t - Cc s (nb t kl) - 1) +
    sd t i 3 * (Cc s t - Cc s (nb t kr) - 1) + sd t i 4 * (R0c s + 1 - Cc s t))

def sideOK (t : Fin 8) (kl kr : Fin 4) (i : ℕ) : Bool :=
  !(real t kl && real t kr) || (sideXY t kl kr i && (List.finRange 11).all fun s => !repB s t || sideC s t kl kr i)

/-- All side certificates are valid. -/
def sidesOK : Bool :=
  (List.finRange 8).all fun t =>
    !facetB t || (sideOK t 0 2 0 && sideOK t 0 3 1 && sideOK t 1 2 2 && sideOK t 1 3 3)

/-- Beyond F = R0c s, a facet t has no slot on each side within 1 of it. -/
theorem side (s : Fin 11) (t : Fin 8) (kl kr : Fin 4) (i : ℕ) (hxy : sideXY t kl kr i = true)
    (hc0 : sideC s t kl kr i = true) (x y : ℤ) (hL : pot (x, y, s) t ≤ pot (x, y, s) (nb t kl) + 1)
    (hR : pot (x, y, s) t ≤ pot (x, y, s) (nb t kr) + 1) (h : F (x, y, s) = pot (x, y, s) t)
    (hF : R0c s < F (x, y, s)) : False := by
  have q := of_decide_eq_true hxy
  exact farkas x y s (sk t i) t t (nb t kl) t (nb t kr) t 0 1 1 (R0c s + 1) (sd t i 1) (sd t i 2) (sd t i 3)
    (sd t i 4) ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, of_decide_eq_true hc0⟩
    (pair_of (le_F _ _) h) hL hR (bound_of hF h)

/-- The edges of E by position p: source and target class, cell offset, and the potential changes dl
(entry p * 8 + j). -/
def srcv (p : ℕ) : ℕ := tgetN 63853883434482808005663917874413670378128548675256320 4 p

def tgtv (p : ℕ) : ℕ := tgetN 57439449000948151680192063347040270214236566223610945 4 p

def tgtF (p : ℕ) : Fin 11 := ⟨tgtv p % 11, Nat.mod_lt _ (by norm_num)⟩

def dxv (p : ℕ) : ℤ := tget 50709131620219807462846420536568912523438848615221367 4 8 p

def dyv (p : ℕ) : ℤ := tget 51083184695529628611946247783697490750637813329852552 4 8 p

/-- dlv p j + 8, as a natural number (the rule checks compare naturals). -/
def dlvN (p : ℕ) (j : Fin 8) : ℕ := tgetN 3335155638110102329235525013236583733342467386651537388224788024634059040373574412597081916656367353794115137927063653949064159137900062843744562752493908845943063473207841625704294119489855746534261684192309962219340314169387492548086387771723432383427401725380189243192773259725430610680549422984414354921116902254155433769924065725175647211000527468206939828976365806395879984603978062090700992708000543927934325536356216 4 (p * 8 + j.val)

def dlv (p : ℕ) (j : Fin 8) : ℤ := (dlvN p j : ℤ) - 8

/-- The edge tables agree with the edges of a list l from position p on, every edge moves, and every
potential changes by at most one along every edge. -/
def dlOKl : List (Fin 11 × Fin 11 × ℤ × ℤ) → ℕ → Bool
  | [], _ => true
  | e :: l, p => decide (srcv p = e.1.val ∧ tgtv p = e.2.1.val ∧ dxv p = e.2.2.1 ∧ dyv p = e.2.2.2 ∧
        (e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1)) &&
      ((List.finRange 8).all fun j => decide (dlv p j = dl e j ∧ dl e j ≤ 1 ∧ -dl e j ≤ 1)) && dlOKl l (p + 1)

/-- The edge tables agree with E. -/
def dlOK : Bool := dlOKl E 0

/-- The slack class of a slack d ≥ 0: 2 when d ≥ 2, else d. -/
def scl (d : ℤ) : Fin 3 := if 2 ≤ d then 2 else if d = 1 then 1 else 0

theorem scl_le (d : ℤ) (hd : 0 ≤ d) : ((scl d).val : ℤ) ≤ d := by
  have e2 : ((2 : Fin 3).val : ℤ) = 2 := rfl
  have e1 : ((1 : Fin 3).val : ℤ) = 1 := rfl
  have e0 : ((0 : Fin 3).val : ℤ) = 0 := rfl
  unfold scl
  split_ifs <;> omega

theorem scl_eq (d : ℤ) (hd : 0 ≤ d) (h1 : (scl d).val ≤ 1) : d = (scl d).val := by
  have e2 : (2 : Fin 3).val = 2 := rfl
  have e1 : (1 : Fin 3).val = 1 := rfl
  have e0 : (0 : Fin 3).val = 0 := rfl
  unfold scl at *
  split_ifs at * <;> omega

/-- The pattern (c0, c1, c2, c3) of slack classes of the slots of t can occur beyond R0c: unused
slots have class 0, and a facet has no slot on each side of class at most 1. -/
def padOK (t : Fin 8) (c0 c1 c2 c3 : ℕ) : Bool :=
  (real t 0 || decide (c0 = 0)) && (real t 1 || decide (c1 = 0)) && (real t 2 || decide (c2 = 0)) &&
    (real t 3 || decide (c3 = 0))

def closeL (t : Fin 8) (c0 c1 : ℕ) : Bool := (real t 0 && decide (c0 ≤ 1)) || (real t 1 && decide (c1 ≤ 1))

def closeR (t : Fin 8) (c2 c3 : ℕ) : Bool := (real t 2 && decide (c2 ≤ 1)) || (real t 3 && decide (c3 ≤ 1))

def adm (t : Fin 8) (c0 c1 c2 c3 : ℕ) : Bool :=
  padOK t c0 c1 c2 c3 && (!facetB t || !closeL t c0 c1 || !closeR t c2 c3)

/-- Descent rules beyond F = R0c s, one word of 30 bits per class s, potential t and admissible
pattern (c0, c1, c2, c3), at position POFF t + (the rank of the pattern among the admissible patterns
of t): kind 0 names an edge by its position in E; kind 1 is a Farkas certificate: multipliers m1, m2,
m3 of the slot facts of slots k1, k2, k3 (slack ≥ c for a multiplier ≥ 0, slack ≤ c for a negative
multiplier, where c ≤ 1) and l0 ≥ 0 of the bound R0c s + 1 ≤ pot t, whose x and y parts cancel and
whose constants add up to a positive number; kind 2 is a line of slot k1 without lattice points
(modulus l0). Fields from bit 0: kind (2 bits), edge position (6), k1, k2, k3 (2 each), m1, m2, m3
(4 each, stored as value + 8), l0 (4). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 5591952003050702746443332042672043872035047956450018417713262574065814899887698821988948173084291565820874599905330505147100369941653279699998019550423174528774964676560536615438216870246995291447070487169733532756423475803953430562460559814272019196763132322276909207838960556656442815638030927936678751434202824340187950264962083995205845340668561901038526636646185839280855097578307465847486400372075897477435032069515876403298858484349160954717988768350909960193971160334919830665170598649955741967535181259499064906598747429671474994704628658847966223885557215410771530210441188157076533754101927329082128749469825184239740471757944866979578370
  | 1 => 5591953253254321582805598198866316871793356233118946342043946104901358897550039895403440014095165327342792303858635700541334603231763532849711784518213014994647422867458146540262582033111825634240599014145541108680811026348696360084228560175401537569331955981423987390665032157908808609454847417105777455848550905810067918217283417931355990078496714147052776713946229213339653064267765161581290143887076695452019674681805963592490512536194330114083418666114805033541957568358493376153594194527910151921304214708682325885253416188560803745575639581145642007378416912795042874235772446722702194238986811184739167555512583208479293855139737777389830164
  | 2 => 5591957003865178091892398294017309866156799048137053286485625268016431882473987437046056197921601094360797367878439536550768378848411529591063439774045509236219612844710801807835650506230473141175393853892327723648433004957004947560454698848109725538816547687824001429041122712765427768381686400561960300625592171792089299357195460658016469967644461330804297347038854196092577503379696527575244738124488667749706414620282672853277723786441478252070170643870741666920510611055500530813291847985045901602805777596677689330551568970635499823506115857208522658705580132480917126543084433832700194624584226610268296379626336171409023106940084582812352556
  | 3 => 5591958254068796928254664992400974197611279986476422267997238396943589752850189688612752371660045814192082628253818369327588794737159906120032576826663671078351569533113154621136617922717542622638695146884342964261191622136109433686595101505172548437588832225181972855157776461663465606950896192116076645324297572489918115684592455941363554425672283947145252133293554748844411398802959572776107061029530542190016531390728325415217661617772031477667193597682253183946301691888553408736569724308962715350901525312077411923068560522100170689418926101857958644808573636276276260858762109755146107789067900517696126600397987628126351254879521326686667266
  | 4 => 5591961379577844019160331738360135026247482332324844721694753168267642915567962308554864151165778721242474213046481517796087208892150103327044656805971687149836886384327901765596330635727375429892618133959515752013267431155207718918171760624378684312515306739171581487761104317674379911167754448748372936326260351533644093417251870101242978551787223774987341637935372337287575871801300534651250164223029699100553337159492569907718197234640762338719088136529537607287427111672120117977155403686379915507766016546997796444070902138040030719065382722810471707656258543804324558695353455597005494667274216098389705594163897470563579490220975967887818824
  | 5 => 5591963879985081691884865135127463689156444209003582684694692225491099465062858205973228861443344665976420623437748107873452587443629382051580049216446514905842527862812327380733816474631492385379209830223608663037417804593580868339416617823656772322791703387301754633877262690278625846798259226894289680710199416430275291839689906694591127825813604120919996632827972825475302495609411071069957535960054634462647650486956503366455974412065334291475884185808433193196466649123531457344401442622954422720588854352666526593775564326100059909073283538266365292868272819401136483584543863497618280792602180525794137684660331437420888462085285564033138776
  | 6 => 5591967630595938200971665230278456683519887024021689629159661444522772606537970550880213160507407961964760030348023075167141287753699681769886495580528926639205506096466744147958958042226722054437598187610838616329249475067743023615685215221465624403152853035494382124603665643680245888433978984959528868794170135630228195943817832021095528192227309273898610787249714111201430620729644772949325575334983775527052338921179871982668006299023846280106188737913424766779145071347283726977276301051814678167452476183913081374711792557254078948095312962735610319309111341654214944487859671801476677903397267788973429053573619887528236397081340042857807972
  | 7 => 5591969505901366455515065277853953180701608431530743101392146461936572172317477608697896753947083235838271045547975540776060284080026458055263956738809807519736803321117948646906849888552472101695103594268108509663313910337091518924095998877803886530199846489857808608402931827793743410747884643075704955940937736885742977519559367211551824069010921172842594753770618768733698248088050086628177226834821194294410348533641144659644133463366486740711311394269915291698553582237963326995445223152313052087308745237991361890277768176604490847343991307238471181883224964831660493407469523160489884678635403183365645841993777494274479418303165956907729008
  | 8 => 5591972006308604128239599216810673175306742969879922121526431742234738321088297994826197768092638964211607125220659072952410332531509695636296289654848984413339666922195380458620745174971382641086418319730588003370178392650783982413853774500055507203232220955036047504879920123161131110691626669449454286128984252837995891535486757946020349091719722658797225652097277156564820651774704712116958928652696957427334669298096673602001692891065518429820034483819371147366827867485112923730396698932238510979703848307708665298364622515562446058279142273007416629556199726576404544592273883241803849495378542103307341591807826754537361290587453622082208258
  | 9 => 5591975131817651219145265420580442672246772654057903518066297997628591876720454761868260575647479834299170215493092423047976273905846153651514838752130565367650926852016449064954515877995513910732027986469950889922244774586592849245953742336685612308396551288902880556708948895100969845672570203854563844517183421690413819399504559178104844793856161975408355368001450694290225570182476427936558172162784965093509164308316459711774476462659746058699495596740506759970944341069627329765668131207776399418524858921371275123752165135083009584635623584140636536598460940172692074712249625160179098415812222322781882839511469171421134445472468128728481940
  | 10 => 5591975756919460637326398769772274837974013123227588008833761419091397746400713964845345767292350094652294078169122389352202831615872233109251809714785825997344501237610662392816593937608147046739626700542358260585772825883936415657627648835356650411459283789291266129468220370904595675781316775126322295415975868758942089582687685138244291505549203598949881233038041572366939316674860273715643397917939037514985457488451085252739174986175876529627300945280612922480659895531777414848698636612405754705564465284255037767956900382984548948577287691784286785639967679040616784101358865213888945710552811199409948952785302453286589541981339954094145700
  | _ => 0

def rword (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) : ℕ :=
  tgetN (ruleT s.val) 30 (Nat.add (tgetN 271898883981632 6 t.val) (tgetN 11702359830990635455286260327561042918602710790733345921070704035585330610604292330551243271381259049272532626183744776376578393731872906923586226228332074526916802507602350113332391345985559444035054540802142607579466112416595434994034215188159002735624710677752517963120477304557450313860490513897466334585145879129165094853828900559923870195384615771932098291087378274609949252896478017863417689327194622331747977930866983296417996799800187962445236857555301745873544920347496253267609508947041841755648866967323415867797593892961726519856083518318117153563158319976487906648855841574866063961196588727001790405937065198343890079302077376473266832376080944509204459698527396984101218607034037028253990323656589312 4
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul t.val 81) c0) (Nat.mul 3 c1)) (Nat.mul 9 c2)) (Nat.mul 27 c3))))

/-- The field of B bits from bit o of the word w. -/
def fld (w o B : ℕ) : ℕ := Nat.mod (Nat.shiftRight w o) (Nat.pow 2 B)

def rk (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 0 2

def re (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 2 6

def rsl (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) (i : ℕ) : Fin 4 :=
  ⟨fld (rword s t c0 c1 c2 c3) (Nat.add 8 (Nat.mul 2 i)) 2 % 4, Nat.mod_lt _ (by norm_num)⟩

def rm (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) (i : ℕ) : ℤ := Int.subNatNat (fld (rword s t c0 c1 c2 c3) (Nat.add 14 (Nat.mul 4 i)) 4) 8

def rl0 (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) : ℤ := Int.ofNat (fld (rword s t c0 c1 c2 c3) 26 4)

/-- The class of slot k in the pattern (c0, c1, c2, c3). -/
def cv (c0 c1 c2 c3 : ℕ) (k : Fin 4) : ℕ := if k.val = 0 then c0 else if k.val = 1 then c1 else if k.val = 2 then c2 else c3

/-- The slack of the slot k below t in x and y, and its constant: pot t - pot (nb t k) at (x, y, s)
is dA t k * x + dB t k * y + dC s t k. -/
def dA (t : Fin 8) (k : Fin 4) : ℤ := Ac t - Ac (nb t k)

def dB (t : Fin 8) (k : Fin 4) : ℤ := Bc t - Bc (nb t k)

def dC (s : Fin 11) (t : Fin 8) (k : Fin 4) : ℤ := Cc s t - Cc s (nb t k)

/-- Kind 0: the edge at position re descends from class s for this pattern. -/
def ok0 (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) : Bool :=
  Nat.blt (re s t c0 c1 c2 c3) 44 && Nat.beq (srcv (re s t c0 c1 c2 c3)) s.val && Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) t) 1) 8 &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 0)) 1) (Nat.add c0 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 1)) 1) (Nat.add c1 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 2)) 1) (Nat.add c2 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 3)) 1) (Nat.add c3 8)

/-- Kind 1: the Farkas certificate over the slot facts and the bound is valid. -/
def ok1 (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) : Bool :=
    decide (0 ≤ rl0 s t c0 c1 c2 c3 ∧
      (rm s t c0 c1 c2 c3 0 < 0 → cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) ≤ 1) ∧ (rm s t c0 c1 c2 c3 1 < 0 → cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 1) ≤ 1) ∧
      (rm s t c0 c1 c2 c3 2 < 0 → cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 2) ≤ 1) ∧
      rm s t c0 c1 c2 c3 0 * dA t (rsl s t c0 c1 c2 c3 0) + rm s t c0 c1 c2 c3 1 * dA t (rsl s t c0 c1 c2 c3 1) + rm s t c0 c1 c2 c3 2 * dA t (rsl s t c0 c1 c2 c3 2) +
        rl0 s t c0 c1 c2 c3 * Ac t = 0 ∧
      rm s t c0 c1 c2 c3 0 * dB t (rsl s t c0 c1 c2 c3 0) + rm s t c0 c1 c2 c3 1 * dB t (rsl s t c0 c1 c2 c3 1) + rm s t c0 c1 c2 c3 2 * dB t (rsl s t c0 c1 c2 c3 2) +
        rl0 s t c0 c1 c2 c3 * Bc t = 0 ∧
      0 < rm s t c0 c1 c2 c3 0 * ((cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 0)) +
        rm s t c0 c1 c2 c3 1 * ((cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 1) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 1)) +
        rm s t c0 c1 c2 c3 2 * ((cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 2) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 2)) + rl0 s t c0 c1 c2 c3 * (R0c s + 1 - Cc s t))

/-- Kind 2: the line of slot k1 has no lattice points. -/
def ok2 (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) : Bool :=
  decide (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) ≤ 1 ∧ rl0 s t c0 c1 c2 c3 ∣ dA t (rsl s t c0 c1 c2 c3 0) ∧ rl0 s t c0 c1 c2 c3 ∣ dB t (rsl s t c0 c1 c2 c3 0) ∧
    ¬ rl0 s t c0 c1 c2 c3 ∣ (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 0))

def ruleOK (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) : Bool :=
  if rk s t c0 c1 c2 c3 = 0 then ok0 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 1 then ok1 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 2 then ok2 s t c0 c1 c2 c3 else false

/-- Every pattern of slack classes that can occur at the maximal potential t has a valid rule. -/
def rulesOK (t : Fin 8) : Bool :=
  (List.range 3).all fun c0 => (List.range 3).all fun c1 => (List.range 3).all fun c2 => (List.range 3).all fun c3 =>
    !adm t c0 c1 c2 c3 || (List.finRange 11).all fun s => !repB s t || ruleOK s t c0 c1 c2 c3

/-- The side certificates and the edge tables. The kernel decisions are definitions, which the
elaborator checks one after another, and the large ones come in pieces (one per potential or class):
as theorems they run in parallel and their memory adds up. -/
def tables_ok_dec : PLift (sidesOK = true ∧ dlOK = true) := ⟨by
  decide +kernel⟩

theorem tables_ok : sidesOK = true ∧ dlOK = true := tables_ok_dec.down

def farsOK0_dec : PLift (farsOK 0 = true) := ⟨by
  decide +kernel⟩

def farsOK1_dec : PLift (farsOK 1 = true) := ⟨by
  decide +kernel⟩

def farsOK2_dec : PLift (farsOK 2 = true) := ⟨by
  decide +kernel⟩

def farsOK3_dec : PLift (farsOK 3 = true) := ⟨by
  decide +kernel⟩

def farsOK4_dec : PLift (farsOK 4 = true) := ⟨by
  decide +kernel⟩

def farsOK5_dec : PLift (farsOK 5 = true) := ⟨by
  decide +kernel⟩

def farsOK6_dec : PLift (farsOK 6 = true) := ⟨by
  decide +kernel⟩

def farsOK7_dec : PLift (farsOK 7 = true) := ⟨by
  decide +kernel⟩

theorem farsOK_all (k : Fin 8) : farsOK k = true := by
  fin_cases k
  exacts [farsOK0_dec.down, farsOK1_dec.down, farsOK2_dec.down, farsOK3_dec.down, farsOK4_dec.down, farsOK5_dec.down, farsOK6_dec.down, farsOK7_dec.down]

def rulesOK0_dec : PLift (rulesOK 0 = true) := ⟨by
  decide +kernel⟩

def rulesOK1_dec : PLift (rulesOK 1 = true) := ⟨by
  decide +kernel⟩

def rulesOK2_dec : PLift (rulesOK 2 = true) := ⟨by
  decide +kernel⟩

def rulesOK3_dec : PLift (rulesOK 3 = true) := ⟨by
  decide +kernel⟩

def rulesOK4_dec : PLift (rulesOK 4 = true) := ⟨by
  decide +kernel⟩

def rulesOK5_dec : PLift (rulesOK 5 = true) := ⟨by
  decide +kernel⟩

def rulesOK6_dec : PLift (rulesOK 6 = true) := ⟨by
  decide +kernel⟩

def rulesOK7_dec : PLift (rulesOK 7 = true) := ⟨by
  decide +kernel⟩

theorem rulesOK_all (k : Fin 8) : rulesOK k = true := by
  fin_cases k
  exacts [rulesOK0_dec.down, rulesOK1_dec.down, rulesOK2_dec.down, rulesOK3_dec.down, rulesOK4_dec.down, rulesOK5_dec.down, rulesOK6_dec.down, rulesOK7_dec.down]

theorem far_ok (s : Fin 11) (t j : Fin 8) (hrep : repB s t = true) (hjt : j ≠ t) (hjn : ∀ k, j ≠ nb t k) :
    farXY t j = true ∧ farC s t j = true := by
  have h := farsOK_all t
  unfold farsOK at h
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  have hn : nonadj t j = true := by simp [nonadj, hjt, hjn]
  have h' := h j
  rw [hn] at h'
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h'
  have h2 := h'.2 s
  rw [hrep] at h2
  exact ⟨h'.1, by simpa using h2⟩

theorem side_ok (s : Fin 11) (t : Fin 8) (kl kr : Fin 4) (i : ℕ) (hrep : repB s t = true) (hsp : facetB t = true)
    (hi : (kl = 0 ∧ kr = 2 ∧ i = 0) ∨ (kl = 0 ∧ kr = 3 ∧ i = 1) ∨ (kl = 1 ∧ kr = 2 ∧ i = 2) ∨
      (kl = 1 ∧ kr = 3 ∧ i = 3))
    (hl : real t kl = true) (hr : real t kr = true) : sideXY t kl kr i = true ∧ sideC s t kl kr i = true := by
  have h := tables_ok.1
  unfold sidesOK at h
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  have h' := h t
  rw [hsp] at h'
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h'
  have key : sideOK t kl kr i = true := by
    rcases hi with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact h'.1.1.1
    · exact h'.1.1.2
    · exact h'.1.2
    · exact h'.2
  unfold sideOK at key
  rw [hl, hr] at key
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at key
  have h2 := key.2 s
  rw [hrep] at h2
  exact ⟨key.1, by simpa using h2⟩

theorem rule_ok (s : Fin 11) (t : Fin 8) (c0 c1 c2 c3 : ℕ) (hrep : repB s t = true) (h0 : c0 < 3) (h1 : c1 < 3) (h2 : c2 < 3) (h3 : c3 < 3)
    (ha : adm t c0 c1 c2 c3 = true) : ruleOK s t c0 c1 c2 c3 = true := by
  have h := rulesOK_all t
  unfold rulesOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h c0 h0 c1 h1 c2 h2 c3 h3
  rw [ha] at h'
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_finRange, forall_const] at h'
  have h4 := h' s
  rw [hrep] at h4
  simpa using h4

theorem dlOKl_spec : ∀ (l : List (Fin 11 × Fin 11 × ℤ × ℤ)) (p : ℕ), dlOKl l p = true →
    ∀ i (hi : i < l.length), (srcv (p + i) = l[i].1.val ∧ tgtv (p + i) = l[i].2.1.val ∧ dxv (p + i) = l[i].2.2.1 ∧
      dyv (p + i) = l[i].2.2.2 ∧ (l[i].2.2.1 ≠ 0 ∨ l[i].2.2.2 ≠ 0 ∨ l[i].1 ≠ l[i].2.1)) ∧
      ∀ j, dlv (p + i) j = dl l[i] j ∧ dl l[i] j ≤ 1 ∧ -dl l[i] j ≤ 1
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | e :: l, p, h, i, hi => by
    simp only [dlOKl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_const] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases i with
    | zero => exact ⟨h1, h2⟩
    | succ i =>
      have h4 := dlOKl_spec l (p + 1) h3 i (by simpa using hi)
      rw [show p + (i + 1) = p + 1 + i by omega]
      exact h4

theorem E_len : E.length = 44 := by
  decide +kernel

/-- The edge at position p of E, read from the tables. -/
theorem edge_of (p : ℕ) (hp : p < 44) : ∃ e ∈ E, e.1.val = srcv p ∧ e.2.1.val = tgtv p ∧
    e.2.2.1 = dxv p ∧ e.2.2.2 = dyv p ∧ ∀ j, dlv p j = dl e j := by
  have hp' : p < E.length := E_len ▸ hp
  obtain ⟨⟨h1, h2, h3, h4, -⟩, h5⟩ := dlOKl_spec E 0 tables_ok.2 p hp'
  simp only [Nat.zero_add] at h1 h2 h3 h4 h5
  exact ⟨E[p], List.getElem_mem hp', h1.symm, h2.symm, h3.symm, h4.symm, fun j => (h5 j).1⟩

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  intro e he j
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact ((dlOKl_spec E 0 tables_ok.2 i hi).2 j).2

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact (dlOKl_spec E 0 tables_ok.2 i hi).1.2.2.2.2

theorem adj_of_mem (e : Fin 11 × Fin 11 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

theorem lip (u w : V) (h : G.Adj u w) : F w ≤ F u + 1 := by
  rw [G, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · obtain ⟨e, he, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, s⟩ := u
    obtain ⟨x', y', s'⟩ := w
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    apply F_le_all
    intro j
    have hs := (E_step e he j).1
    have hu := le_F (x, y, e.1) j
    rw [shift x y e j]
    omega
  · obtain ⟨e, he, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, s⟩ := w
    obtain ⟨x', y', s'⟩ := u
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    apply F_le_all
    intro j
    have hs := (E_step e he j).2
    have hu := le_F (x + e.2.2.1, y + e.2.2.2, e.2.1) j
    rw [shift x y e j] at hu
    omega

theorem step_down (v w : V) (hadj : G.Adj v w) (h : ∀ j, pot w j ≤ F v - 1) : F w + 1 = F v := by
  have hw := F_le_all w (F v - 1) h
  have hl := lip w v hadj.symm
  omega

/-- Slot facts m * c ≤ m * slack for three slots and the bound R0c s + 1 ≤ pot t, with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas_slot (x y : ℤ) (s : Fin 11) (t : Fin 8) (k1 k2 k3 : Fin 4) (c1 c2 c3 m1 m2 m3 l0 : ℤ)
    (hl0 : 0 ≤ l0)
    (ha : m1 * dA t k1 + m2 * dA t k2 + m3 * dA t k3 + l0 * Ac t = 0)
    (hb : m1 * dB t k1 + m2 * dB t k2 + m3 * dB t k3 + l0 * Bc t = 0)
    (hc : 0 < m1 * (c1 - dC s t k1) + m2 * (c2 - dC s t k2) + m3 * (c3 - dC s t k3) + l0 * (R0c s + 1 - Cc s t))
    (h1 : m1 * c1 ≤ m1 * (pot (x, y, s) t - pot (x, y, s) (nb t k1)))
    (h2 : m2 * c2 ≤ m2 * (pot (x, y, s) t - pot (x, y, s) (nb t k2)))
    (h3 : m3 * c3 ≤ m3 * (pot (x, y, s) t - pot (x, y, s) (nb t k3)))
    (hF : R0c s < pot (x, y, s) t) : False := by
  have e0 := mul_le_mul_of_nonneg_left (show R0c s + 1 ≤ pot (x, y, s) t by omega) hl0
  have ha' : (m1 * dA t k1 + m2 * dA t k2 + m3 * dA t k3 + l0 * Ac t) * x = 0 := by rw [ha, zero_mul]
  have hb' : (m1 * dB t k1 + m2 * dB t k2 + m3 * dB t k3 + l0 * Bc t) * y = 0 := by rw [hb, zero_mul]
  simp only [pot, dA, dB, dC] at h1 h2 h3 e0 ha' hb' hc
  linarith

theorem dvd_contra (x y : ℤ) (a b c g : ℤ) (ha : g ∣ a) (hb : g ∣ b) (hc : ¬ g ∣ c) (e : a * x + b * y = c) :
    False :=
  hc (e ▸ dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y))

/-- Beyond F = R0c s every vertex of class s has a neighbor where F is one less. -/
theorem far_step (s : Fin 11) (t : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) t)
    (hF : R0c s < F (x, y, s)) (hrep : repB s t = true) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
  have p : ∀ k, 0 ≤ pot (x, y, s) t - pot (x, y, s) (nb t k) := fun k => by
    have := le_F (x, y, s) (nb t k)
    omega
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℕ, ∀ k, c k = (scl (pot (x, y, s) t - pot (x, y, s) (nb t k))).val :=
    ⟨_, fun _ => rfl⟩
  have c3 : ∀ k, c k < 3 := fun k => by
    rw [hc k]
    exact (scl _).isLt
  have q : ∀ k, (c k : ℤ) ≤ pot (x, y, s) t - pot (x, y, s) (nb t k) := fun k => by
    rw [hc k]
    exact scl_le _ (p k)
  have e : ∀ k, c k ≤ 1 → pot (x, y, s) t - pot (x, y, s) (nb t k) = c k := fun k hk => by
    rw [hc k] at hk ⊢
    exact scl_eq _ (p k) hk
  have hs : ∀ (m : ℤ) k, (m < 0 → c k ≤ 1) →
      m * (c k : ℤ) ≤ m * (pot (x, y, s) t - pot (x, y, s) (nb t k)) := fun m k hk => by
    by_cases hm : m < 0
    · exact le_of_eq (by rw [e k (hk hm)])
    · exact mul_le_mul_of_nonneg_left (q k) (by omega)
  have hcv : ∀ k, cv (c 0) (c 1) (c 2) (c 3) k = c k := by
    intro k
    fin_cases k <;> rfl
  have hpad : padOK t (c 0) (c 1) (c 2) (c 3) = true := by
    have hk : ∀ k, real t k = true ∨ c k = 0 := fun k => by
      by_cases hr : real t k = true
      · exact Or.inl hr
      right
      simp only [real, decide_eq_true_eq, not_not] at hr
      rw [hc k, hr, sub_self]
      rfl
    simp only [padOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hk 0, hk 1⟩, hk 2⟩, hk 3⟩
  have hadm : adm t (c 0) (c 1) (c 2) (c 3) = true := by
    unfold adm
    rw [hpad, Bool.true_and]
    cases hsp : facetB t
    · rfl
    cases hl : closeL t (c 0) (c 1)
    · rfl
    cases hr : closeR t (c 2) (c 3)
    · rfl
    exfalso
    simp only [closeL, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [closeR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hl with ⟨hl, hl1⟩ | ⟨hl, hl1⟩ <;> rcases hr with ⟨hr, hr1⟩ | ⟨hr, hr1⟩
    · obtain ⟨hxy, hc0⟩ := side_ok s t 0 2 0 hrep hsp (Or.inl ⟨rfl, rfl, rfl⟩) hl hr
      exact side s t 0 2 0 hxy hc0 x y (by have := e 0 hl1; omega) (by have := e 2 hr1; omega) h hF
    · obtain ⟨hxy, hc0⟩ := side_ok s t 0 3 1 hrep hsp (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) hl hr
      exact side s t 0 3 1 hxy hc0 x y (by have := e 0 hl1; omega) (by have := e 3 hr1; omega) h hF
    · obtain ⟨hxy, hc0⟩ := side_ok s t 1 2 2 hrep hsp (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) hl hr
      exact side s t 1 2 2 hxy hc0 x y (by have := e 1 hl1; omega) (by have := e 2 hr1; omega) h hF
    · obtain ⟨hxy, hc0⟩ := side_ok s t 1 3 3 hrep hsp (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) hl hr
      exact side s t 1 3 3 hxy hc0 x y (by have := e 1 hl1; omega) (by have := e 3 hr1; omega) h hF
  have hv := rule_ok s t (c 0) (c 1) (c 2) (c 3) hrep (c3 0) (c3 1) (c3 2) (c3 3) hadm
  unfold ruleOK at hv
  split_ifs at hv with k0 k1 k2
  · -- an edge that descends
    simp only [ok0, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, Nat.add_eq, and_assoc] at hv
    obtain ⟨hlen, hsrc, hdiN, hd0, hd1, hd2, hd3⟩ := hv
    have hdi : dlv (re s t (c 0) (c 1) (c 2) (c 3)) t ≤ -1 := by
      unfold dlv
      omega
    have hd' : ∀ k, dlvN (re s t (c 0) (c 1) (c 2) (c 3)) (nb t k) + 1 ≤ c k + 8 := by
      intro k
      fin_cases k
      exacts [hd0, hd1, hd2, hd3]
    have hdk : ∀ k, dlv (re s t (c 0) (c 1) (c 2) (c 3)) (nb t k) ≤ (c k : ℤ) - 1 := fun k => by
      have := hd' k
      unfold dlv
      omega
    obtain ⟨e, hmem, hs1, -, -, -, hdl⟩ := edge_of _ hlen
    rw [hdl] at hdi
    simp only [hdl] at hdk
    have hs' : e.1 = s := Fin.ext (hs1.trans hsrc)
    have ha := adj_of_mem e hmem x y
    rw [hs'] at ha
    refine ⟨_, ha, step_down _ _ ha (fun j => ?_)⟩
    have hsh := shift x y e j
    rw [hs'] at hsh
    rw [hsh]
    have hst := (E_step e hmem j).1
    have hj := le_F (x, y, s) j
    by_cases hjt : j = t
    · subst hjt
      omega
    by_cases hjn : ∃ k, j = nb t k
    · obtain ⟨k, rfl⟩ := hjn
      have := hdk k
      have := q k
      omega
    push Not at hjn
    have hf := far_ok s t j hrep hjt hjn
    have := far s t j hf.1 hf.2 x y h hF
    omega
  · -- a Farkas certificate over the slot facts and the bound
    simp only [ok1, decide_eq_true_eq, hcv] at hv
    obtain ⟨hl0, hn1, hn2, hn3, ha, hb, hcc⟩ := hv
    exact (farkas_slot x y s t _ _ _ _ _ _ _ _ _ _ hl0 ha hb hcc (hs _ _ hn1) (hs _ _ hn2) (hs _ _ hn3)
      (h ▸ hF)).elim
  · -- a line without lattice points
    simp only [ok2, decide_eq_true_eq, hcv] at hv
    obtain ⟨hc1, ha, hb, hcc⟩ := hv
    have e1 := e _ hc1
    simp only [pot] at e1
    exact (dvd_contra x y _ _ _ _ ha hb hcc (by simp only [dA, dB, dC]; linear_combination e1)).elim

theorem far_step' (v : V) (t : Fin 8) (h : F v = pot v t) (hF : R0c v.2.2 < F v) (hrep : repB v.2.2 t = true) :
    ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  exact far_step s t x y h hF hrep

def rep_all_dec : PLift ((∀ s t, repB s t = true) ∧ ∀ s, repC s = true) := ⟨by
  decide +kernel⟩

theorem rep_all : (∀ s t, repB s t = true) ∧ ∀ s, repC s = true := rep_all_dec.down

theorem far_desc (v : V) (hF : R0c v.2.2 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨t, ht⟩ := exists_F (x, y, s)
  exact far_step s t x y ht hF (rep_all.1 s t)

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 11) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
    (hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ lq ∧
      l1 * Ac a1 + l2 * Ac a2 + l3 * Ac a3 + lq * px = 0 ∧
      l1 * Bc a1 + l2 * Bc a2 + l3 * Bc a3 + lq * py = 0 ∧
      0 < l1 * (Cc s a1 - t) + l2 * (Cc s a2 - t) + l3 * (Cc s a3 - t) + lq * q)
    (h1 : pot (x, y, s) a1 ≤ t) (h2 : pot (x, y, s) a2 ≤ t) (h3 : pot (x, y, s) a3 ≤ t)
    (h4 : px * x + py * y + q ≤ 0) : False := by
  obtain ⟨hl1, hl2, hl3, hlq, hx, hy, hk⟩ := hc
  have e1 := mul_le_mul_of_nonneg_left h1 hl1
  have e2 := mul_le_mul_of_nonneg_left h2 hl2
  have e3 := mul_le_mul_of_nonneg_left h3 hl3
  have e4 := mul_le_mul_of_nonneg_left h4 hlq
  have hx' : (l1 * Ac a1 + l2 * Ac a2 + l3 * Ac a3 + lq * px) * x = 0 := by rw [hx, zero_mul]
  have hy' : (l1 * Bc a1 + l2 * Bc a2 + l3 * Bc a3 + lq * py) * y = 0 := by rw [hy, zero_mul]
  simp only [pot] at e1 e2 e3
  nlinarith [e1, e2, e3, e4, hx', hy', hk]

/-- The near box of class s: the cells |x| ≤ BXn s, |y| ≤ BYn s hold its vertices with F ≤ R0c s. -/
def BXn (s : Fin 11) : ℕ := tgetN 3681400603 3 s.val

def BYn (s : Fin 11) : ℕ := tgetN 1207997001 3 s.val

theorem nb_c0 : ∀ s : Fin 11, 0 < 5 * (Cc s 0 - (R0c s)) + 3 * (Cc s 7 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 16 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c0 : ∀ s : Fin 11, 0 < 5 * (Cc s 1 - (3)) + 7 * (Cc s 7 - (3)) + 0 * (Cc s 0 - (3)) + 14 * (3) := by
  decide +kernel

theorem nb_c1 : ∀ s : Fin 11, 0 < 3 * (Cc s 3 - (R0c s)) + 5 * (Cc s 4 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 16 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c1 : ∀ s : Fin 11, 0 < 3 * (Cc s 3 - (3)) + 5 * (Cc s 4 - (3)) + 0 * (Cc s 0 - (3)) + 16 * (3) := by
  decide +kernel

theorem nb_c2 : ∀ s : Fin 11, 0 < 1 * (Cc s 1 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 7 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c2 : ∀ s : Fin 11, 0 < 2 * (Cc s 2 - (3)) + 1 * (Cc s 7 - (3)) + 0 * (Cc s 0 - (3)) + 7 * (2) := by
  decide +kernel

theorem nb_c3 : ∀ s : Fin 11, 0 < 1 * (Cc s 5 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 7 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c3 : ∀ s : Fin 11, 0 < 1 * (Cc s 5 - (3)) + 0 * (Cc s 0 - (3)) + 0 * (Cc s 0 - (3)) + 7 * (2) := by
  decide +kernel

theorem nn_c : ∀ s : Fin 11, 0 < 2 * (Cc s 3 - (-1)) + 2 * (Cc s 7 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * (0) := by
  decide +kernel

/-- Every vertex of class s with F at most R0c s lies in the near box of class s. -/
theorem near_box (x y : ℤ) (s : Fin 11) (hF : F (x, y, s) ≤ R0c s) :
    -(BXn s : ℤ) ≤ x ∧ x ≤ BXn s ∧ -(BYn s : ℤ) ≤ y ∧ y ≤ BYn s := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 7 0 (R0c s) 5 3 0 (1) (0) ((BXn s : ℤ) + 1) 16 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 4 0 (R0c s) 3 5 0 (-1) (0) ((BXn s : ℤ) + 1) 16 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 1 0 0 (R0c s) 1 0 0 (0) (1) ((BYn s : ℤ) + 1) 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 0 0 (R0c s) 1 0 0 (0) (-1) ((BYn s : ℤ) + 1) 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c3 s⟩ (u _) (u _) (u _) (by omega)

/-- Every vertex with F at most 3 lies in the cells |x| ≤ 2, |y| ≤ 1. -/
theorem small_box (x y : ℤ) (s : Fin 11) (hF : F (x, y, s) ≤ 3) :
    -2 ≤ x ∧ x ≤ 2 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 1 7 0 (3) 5 7 0 (1) (0) (3) 14 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 4 0 (3) 3 5 0 (-1) (0) (3) 16 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 7 0 (3) 2 1 0 (0) (1) (2) 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 0 0 (3) 1 0 0 (0) (-1) (2) 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 3 7 0 (-1) 2 2 0 (0) (0) (0) 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nn_c s⟩ (u _) (u _) (u _) (by norm_num)

/-- The vertices near v0 where the graph distance is not the largest potential, with the distance. -/
def O : List (V × ℤ) :=
  [((0, 0, 7), 0),
    ((0, 0, 9), 1)]

/-- The cells (x, y) of the vertices of O. -/
def obox (x y : ℤ) : Bool := decide (0 ≤ x ∧ x ≤ 0 ∧ 0 ≤ y ∧ y ≤ 0)

/-- The distance formula: the value listed in O, and the largest potential off O. -/
def fv (v : V) : ℤ :=
  if obox v.1 v.2.1 then ((O.find? fun o => decide (o.1 = v)).map Prod.snd).getD (F v) else F v

theorem fv_out (x y : ℤ) (s : Fin 11) (h : ¬ obox x y = true) : fv (x, y, s) = F (x, y, s) := by
  unfold fv
  rw [if_neg h]

theorem fv_of (v : V) (h : ∀ o ∈ O, o.1 ≠ v) : fv v = F v := by
  have hn : O.find? (fun o => decide (o.1 = v)) = none := by
    rw [List.find?_eq_none]
    intro o ho
    simpa using h o ho
  unfold fv
  split_ifs
  · simp [hn]
  · rfl

/-- The vertices of O have F and fv below 3 and fv nonnegative, and fv changes by at most one
along the edges at the vertices of O. -/
def O_ok_dec : PLift (∀ o ∈ O, F o.1 < 3 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 3 ∧ ∀ e ∈ E,
    (e.1 = o.1.2.2 → fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) + 1) ∧
    (e.2.1 = o.1.2.2 → fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) + 1)) := ⟨by
  decide +kernel⟩

theorem O_ok : ∀ o ∈ O, F o.1 < 3 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 3 ∧ ∀ e ∈ E,
    (e.1 = o.1.2.2 → fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) + 1) ∧
    (e.2.1 = o.1.2.2 → fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) + 1) := O_ok_dec.down

theorem adj_cases (u w : V) (h : G.Adj u w) : ∃ e ∈ E,
    (e.1 = u.2.2 ∧ w = (u.1 + e.2.2.1, u.2.1 + e.2.2.2, e.2.1)) ∨
    (e.2.1 = u.2.2 ∧ w = (u.1 - e.2.2.1, u.2.1 - e.2.2.2, e.1)) := by
  rw [G, SimpleGraph.fromRel_adj] at h
  obtain ⟨x, y, s⟩ := u
  obtain ⟨x', y', s'⟩ := w
  obtain ⟨-, ⟨e, he, h1, h2, h3, h4⟩ | ⟨e, he, h1, h2, h3, h4⟩⟩ := h
  · simp only at h1 h2 h3 h4
    exact ⟨e, he, Or.inl ⟨h1.symm, by rw [h2, h3, h4]⟩⟩
  · simp only at h1 h2 h3 h4
    refine ⟨e, he, Or.inr ⟨h2.symm, ?_⟩⟩
    rw [h1, h3, h4]
    simp

theorem lip_fv (u w : V) (h : G.Adj u w) : fv w ≤ fv u + 1 := by
  by_cases hu : ∃ o ∈ O, o.1 = u
  · obtain ⟨o, ho, rfl⟩ := hu
    obtain ⟨-, -, -, hO⟩ := O_ok o ho
    obtain ⟨e, he, ⟨h1, rfl⟩ | ⟨h1, rfl⟩⟩ := adj_cases o.1 w h
    · exact ((hO e he).1 h1).1
    · exact ((hO e he).2 h1).1
  by_cases hw : ∃ o ∈ O, o.1 = w
  · obtain ⟨o, ho, rfl⟩ := hw
    obtain ⟨-, -, -, hO⟩ := O_ok o ho
    obtain ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := adj_cases o.1 u h.symm
    · rw [h2]
      exact ((hO e he).1 h1).2
    · rw [h2]
      exact ((hO e he).2 h1).2
  push Not at hu hw
  rw [fv_of u hu, fv_of w hw]
  exact lip u w h

theorem fv_nonneg (v : V) : 0 ≤ fv v := by
  by_cases hv : ∃ o ∈ O, o.1 = v
  · obtain ⟨o, ho, rfl⟩ := hv
    exact (O_ok o ho).2.1
  push Not at hv
  rw [fv_of v hv]
  exact F_nonneg v

def R0c_ge_dec : PLift (∀ s, 3 ≤ R0c s) := ⟨by
  decide +kernel⟩

theorem R0c_ge : ∀ s, 3 ≤ R0c s := R0c_ge_dec.down

/-- The near check computes the potentials as differences of natural numbers: at the cell (a, b) of
the near box of class s, pot = potP - potQ. -/
def apN (i : Fin 8) : ℕ := tgetN 9280 3 i.val

def amN (i : Fin 8) : ℕ := tgetN 4456450 3 i.val

def bpN (i : Fin 8) : ℕ := tgetN 12300288 3 i.val

def bmN (i : Fin 8) : ℕ := tgetN 3003 3 i.val

def kpN (s : Fin 11) (i : Fin 8) : ℕ := tgetN 573377138150441359350829870667185068642248787280229492086699177754687046835341040592918005009241788651469 4 (Nat.add (Nat.mul s.val 8) i.val)

def kmN (s : Fin 11) (i : Fin 8) : ℕ := tgetN 126974279104632281746673738366819765522274509221700591781025992515504460658113577890969471026970562985984 4 (Nat.add (Nat.mul s.val 8) i.val)

def pqOK : Bool :=
  (List.finRange 8).all fun i => decide ((apN i : ℤ) - amN i = Ac i ∧ (bpN i : ℤ) - bmN i = Bc i) &&
    (List.finRange 11).all fun s => decide ((kpN s i : ℤ) - kmN s i = Cc s i - Ac i * BXn s - Bc i * BYn s)

def pq_ok_dec : PLift (pqOK = true) := ⟨by
  decide +kernel⟩

theorem pq_ok : pqOK = true := pq_ok_dec.down

def potP (s : Fin 11) (a b : ℕ) (i : Fin 8) : ℕ :=
  Nat.add (Nat.add (Nat.mul (apN i) a) (Nat.mul (bpN i) b)) (kpN s i)

def potQ (s : Fin 11) (a b : ℕ) (i : Fin 8) : ℕ :=
  Nat.add (Nat.add (Nat.mul (amN i) a) (Nat.mul (bmN i) b)) (kmN s i)

theorem potPQ_val (s : Fin 11) (a b : ℕ) (i : Fin 8) :
    (potP s a b i : ℤ) - potQ s a b i = pot ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) i := by
  have h := pq_ok
  unfold pqOK at h
  simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, decide_eq_true_eq, forall_const] at h
  obtain ⟨⟨hA, hB⟩, hK⟩ := h i
  have hK' := hK s
  simp only [potP, potQ, pot, Nat.add_eq, Nat.mul_eq]
  push_cast
  linear_combination (a : ℤ) * hA + (b : ℤ) * hB + hK'

/-- The larger of the differences p.1 - p.2 and q.1 - q.2, as a pair. -/
def pmax (p q : ℕ × ℕ) : ℕ × ℕ := cond (Nat.ble (Nat.add p.1 q.2) (Nat.add q.1 p.2)) q p

theorem pmax_val (p q : ℕ × ℕ) :
    ((pmax p q).1 : ℤ) - (pmax p q).2 = max ((p.1 : ℤ) - p.2) ((q.1 : ℤ) - q.2) := by
  unfold pmax
  cases h : Nat.ble (Nat.add p.1 q.2) (Nat.add q.1 p.2)
  · have h' : ¬ Nat.add p.1 q.2 ≤ Nat.add q.1 p.2 := fun hc =>
      absurd (Nat.ble_eq_true_of_le hc) (by rw [h]; decide)
    simp only [cond_false, Nat.add_eq] at h' ⊢
    omega
  · have h' := Nat.le_of_ble_eq_true h
    simp only [cond_true, Nat.add_eq] at h' ⊢
    omega

/-- F at the cell (a, b) of the near box of class s, and at the end of the edge at position p from
there, as pairs. -/
def FP (s : Fin 11) (a b : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax ((potP s a b 0, potQ s a b 0)) (potP s a b 1, potQ s a b 1)) (potP s a b 2, potQ s a b 2)) (potP s a b 3, potQ s a b 3)) (potP s a b 4, potQ s a b 4)) (potP s a b 5, potQ s a b 5)) (potP s a b 6, potQ s a b 6)) (potP s a b 7, potQ s a b 7)

def FPn (s : Fin 11) (a b p : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax ((Nat.add (potP s a b 0) (dlvN p 0), Nat.add (potQ s a b 0) 8)) (Nat.add (potP s a b 1) (dlvN p 1), Nat.add (potQ s a b 1) 8)) (Nat.add (potP s a b 2) (dlvN p 2), Nat.add (potQ s a b 2) 8)) (Nat.add (potP s a b 3) (dlvN p 3), Nat.add (potQ s a b 3) 8)) (Nat.add (potP s a b 4) (dlvN p 4), Nat.add (potQ s a b 4) 8)) (Nat.add (potP s a b 5) (dlvN p 5), Nat.add (potQ s a b 5) 8)) (Nat.add (potP s a b 6) (dlvN p 6), Nat.add (potQ s a b 6) 8)) (Nat.add (potP s a b 7) (dlvN p 7), Nat.add (potQ s a b 7) 8)

theorem FP_val (s : Fin 11) (a b : ℕ) :
    ((FP s a b).1 : ℤ) - (FP s a b).2 = F ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) := by
  simp only [FP, F, pmax_val, potPQ_val]

theorem FPn_val (s : Fin 11) (a b p : ℕ) (hp : p < 44) (hs : srcv p = s.val) :
    ((FPn s a b p).1 : ℤ) - (FPn s a b p).2 = F ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  obtain ⟨e, -, h1, h2, h3, h4, h5⟩ := edge_of p hp
  have hs' : e.1 = s := Fin.ext (h1.trans hs)
  have ht' : e.2.1 = tgtF p := Fin.ext (by
    show e.2.1.val = tgtv p % 11
    rw [← h2, Nat.mod_eq_of_lt e.2.1.isLt])
  have key : ∀ i, ((Nat.add (potP s a b i) (dlvN p i) : ℕ) : ℤ) - (Nat.add (potQ s a b i) 8 : ℕ) =
      pot ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) i := by
    intro i
    have hsh := shift ((a : ℤ) - BXn s) ((b : ℤ) - BYn s) e i
    rw [hs', ht', h3, h4] at hsh
    rw [hsh, ← potPQ_val, ← h5 i]
    simp only [dlv, Nat.add_eq]
    push_cast
    ring
  simp only [FPn, F, pmax_val, key]

/-- fv at the cell (a, b) of the near box of class s, and at the end of the edge at position p from
there: by the pairs off the cells of O. -/
def fvN (s : Fin 11) (a b : ℕ) : ℤ :=
  if obox ((a : ℤ) - BXn s) ((b : ℤ) - BYn s) then fv ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s)
  else Int.subNatNat (FP s a b).1 (FP s a b).2

def fvNn (s : Fin 11) (a b p : ℕ) : ℤ :=
  if obox ((a : ℤ) - BXn s + dxv p) ((b : ℤ) - BYn s + dyv p) then
    fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p)
  else Int.subNatNat (FPn s a b p).1 (FPn s a b p).2

theorem fvN_eq (s : Fin 11) (a b : ℕ) : fvN s a b = fv ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) := by
  unfold fvN
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FP_val, Int.subNatNat_eq_coe]

theorem fvNn_eq (s : Fin 11) (a b p : ℕ) (hp : p < 44) (hs : srcv p = s.val) :
    fvNn s a b p = fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  unfold fvNn
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FPn_val s a b p hp hs, Int.subNatNat_eq_coe]

/-- For each class s and each cell of its near box with F at most R0c s, other than v0, the position
in E of an edge along which fv decreases. -/
def nearT (s : ℕ) : ℕ :=
  match s with
  | 0 => 1329233066445345446524407081947103232
  | 1 => 35494354019773016084420531060736
  | 2 => 2836604631440874248749200618626545811980288
  | 3 => 66948033972685295807585354514432
  | 4 => 21267730330220019228949364389156225024
  | 5 => 103234689565247068132866284060672
  | 6 => 1815067078656
  | 7 => 2024490002334
  | 8 => 2303738914944
  | 9 => 768645408899126916765819779741124928
  | 10 => 851742758036518345574508629663416320
  | _ => 0

def nearE (s : Fin 11) (a b : ℕ) : ℕ := tgetN (nearT s.val) 6 (a * (2 * BYn s + 1) + b)

/-- The near check of class s. -/
def nearOK (s : Fin 11) : Bool :=
  !repC s || (List.range (2 * BXn s + 1)).all fun a => (List.range (2 * BYn s + 1)).all fun b =>
    Nat.blt (Nat.add (R0N s) (FP s a b).2) (FP s a b).1 ||
      (Nat.beq a (BXn s) && Nat.beq b (BYn s) && Nat.beq s.val 7) ||
      (Nat.blt (nearE s a b) 44 && Nat.beq (srcv (nearE s a b)) s.val &&
        decide (fvNn s a b (nearE s a b) + 1 = fvN s a b))

def nearOK0_dec : PLift (nearOK 0 = true) := ⟨by
  decide +kernel⟩

def nearOK1_dec : PLift (nearOK 1 = true) := ⟨by
  decide +kernel⟩

def nearOK2_dec : PLift (nearOK 2 = true) := ⟨by
  decide +kernel⟩

def nearOK3_dec : PLift (nearOK 3 = true) := ⟨by
  decide +kernel⟩

def nearOK4_dec : PLift (nearOK 4 = true) := ⟨by
  decide +kernel⟩

def nearOK5_dec : PLift (nearOK 5 = true) := ⟨by
  decide +kernel⟩

def nearOK6_dec : PLift (nearOK 6 = true) := ⟨by
  decide +kernel⟩

def nearOK7_dec : PLift (nearOK 7 = true) := ⟨by
  decide +kernel⟩

def nearOK8_dec : PLift (nearOK 8 = true) := ⟨by
  decide +kernel⟩

def nearOK9_dec : PLift (nearOK 9 = true) := ⟨by
  decide +kernel⟩

def nearOK10_dec : PLift (nearOK 10 = true) := ⟨by
  decide +kernel⟩

theorem nearOK_all (k : Fin 11) : nearOK k = true := by
  fin_cases k
  exacts [nearOK0_dec.down, nearOK1_dec.down, nearOK2_dec.down, nearOK3_dec.down, nearOK4_dec.down, nearOK5_dec.down, nearOK6_dec.down, nearOK7_dec.down, nearOK8_dec.down, nearOK9_dec.down, nearOK10_dec.down]

/-- Every vertex of a checked class s with F at most R0c s, other than v0, has a neighbor where fv is
one less. -/
theorem near_desc_rep (v : V) (hF : F v ≤ R0c v.2.2) (hv : v ≠ v0) (hrep : repC v.2.2 = true) :
    ∃ w, G.Adj v w ∧ fv w + 1 = fv v := by
  obtain ⟨x, y, s⟩ := v
  change F (x, y, s) ≤ R0c s at hF
  change repC s = true at hrep
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h1 := nearOK_all s
  unfold nearOK at h1
  rw [hrep] at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h' := h1 (x + BXn s).toNat (by omega) (y + BYn s).toNat (by omega)
  have ex : (((x + BXn s).toNat : ℕ) : ℤ) - BXn s = x := by omega
  have ey : (((y + BYn s).toNat : ℕ) : ℤ) - BYn s = y := by omega
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at h'
  rcases h' with (h2 | ⟨⟨h2, h3⟩, h4⟩) | ⟨⟨hlt, hs⟩, hfe⟩
  · have hv' := FP_val s (x + BXn s).toNat (y + BYn s).toNat
    rw [ex, ey] at hv'
    have hr : R0c s = (R0N s : ℤ) := rfl
    omega
  · exfalso
    apply hv
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    have hs0 : s = 7 := Fin.ext h4
    rw [hx0, hy0, hs0]
    rfl
  · rw [fvNn_eq _ _ _ _ hlt hs, fvN_eq, ex, ey] at hfe
    obtain ⟨e, hmem, h1, h2, h3, h4, -⟩ := edge_of _ hlt
    have ha := adj_of_mem e hmem x y
    have hs' : e.1 = s := Fin.ext (h1.trans hs)
    have ht' : e.2.1 = tgtF (nearE s (x + BXn s).toNat (y + BYn s).toNat) := Fin.ext (by
      show e.2.1.val = tgtv (nearE s (x + BXn s).toNat (y + BYn s).toNat) % 11
      rw [← h2, Nat.mod_eq_of_lt e.2.1.isLt])
    rw [hs', ht', h3, h4] at ha
    exact ⟨_, ha, hfe⟩

theorem near_desc (v : V) (hF : F v ≤ R0c v.2.2) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ fv w + 1 = fv v :=
  near_desc_rep v hF hv (rep_all.2 v.2.2)

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ fv w + 1 = fv v := by
  by_cases hF : F v ≤ R0c v.2.2
  · exact near_desc v hF hv
  have hge := R0c_ge v.2.2
  have hvO : ∀ o ∈ O, o.1 ≠ v := fun o ho he => by
    have := (O_ok o ho).1
    rw [he] at this
    omega
  obtain ⟨w, hw, he⟩ := far_desc v (by omega)
  have hwO : ∀ o ∈ O, o.1 ≠ w := fun o ho hw' => by
    have := (O_ok o ho).1
    rw [hw'] at this
    omega
  exact ⟨w, hw, by rw [fv_of v hvO, fv_of w hwO]; exact he⟩

theorem dist_eq_of_potential {W : Type*} (H : SimpleGraph W) (w0 : W) (f : W → ℕ)
    (h0 : f w0 = 0) (hlip : ∀ u w, H.Adj u w → f w ≤ f u + 1)
    (hdesc : ∀ v, v ≠ w0 → ∃ w, H.Adj v w ∧ f w + 1 = f v) (v : W) :
    H.dist w0 v = f v := by
  have up : ∀ n, ∀ v, f v = n → ∃ p : H.Walk w0 v, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro v hv
      by_cases hv0 : v = w0
      · subst hv0
        exact ⟨SimpleGraph.Walk.nil, rfl⟩
      · obtain ⟨w, -, hw⟩ := hdesc v hv0
        omega
    | succ n ih =>
      intro v hv
      have hv0 : v ≠ w0 := by
        rintro rfl
        omega
      obtain ⟨w, hvw, hw⟩ := hdesc v hv0
      obtain ⟨p, hp⟩ := ih w (by omega)
      exact ⟨p.concat hvw.symm, by rw [SimpleGraph.Walk.length_concat, hp]⟩
  have low : ∀ (u : W) (p : H.Walk u v), f v ≤ f u + p.length := by
    intro u p
    induction p with
    | nil => simp
    | cons h p ih =>
      rw [SimpleGraph.Walk.length_cons]
      have := hlip _ _ h
      omega
  obtain ⟨p, hp⟩ := up (f v) v rfl
  apply le_antisymm
  · exact (H.dist_le p).trans hp.le
  · obtain ⟨q, hq⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist (G := H) ⟨p⟩
    have := low w0 q
    omega

/-- The graph distance from v0 is fv: the value listed in O, and the largest potential off O. -/
theorem dist_eq (v : V) : G.dist v0 v = (fv v).toNat := by
  apply dist_eq_of_potential G v0 (fun v => (fv v).toNat)
  · show (fv v0).toNat = 0
    decide +kernel
  · intro u w h
    have := lip_fv u w h
    have := fv_nonneg w
    have := fv_nonneg u
    show (fv w).toNat ≤ (fv u).toNat + 1
    omega
  · intro v hv
    obtain ⟨w, hw, he⟩ := desc v hv
    refine ⟨w, hw, ?_⟩
    have := fv_nonneg w
    show (fv w).toNat + 1 = (fv v).toNat
    omega

/-- Off the list O the graph distance from v0 is the largest potential. -/
theorem dist_eq_F (v : V) (hv : ∀ o ∈ O, o.1 ≠ v) : G.dist v0 v = (F v).toNat := by
  rw [dist_eq v, fv_of v hv]

/-- From n = 3 on, the coordination sequence counts the level set F = n. -/
theorem a_eq_F (n : ℕ) (hn : 3 ≤ n) : a n = Set.ncard {v : V | (F v).toNat = n} := by
  unfold a
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [dist_eq v]
  by_cases hv : ∃ o ∈ O, o.1 = v
  · obtain ⟨o, ho, rfl⟩ := hv
    obtain ⟨h1, h2, h3, -⟩ := O_ok o ho
    omega
  push Not at hv
  rw [fv_of v hv]

/-- The cells |x| ≤ 2, |y| ≤ 1, every class. -/
def boxF : Finset V :=
  (Finset.range 5 ×ˢ Finset.range 3 ×ˢ (Finset.univ : Finset (Fin 11))).map
    ⟨fun p => ((p.1 : ℤ) - 2, (p.2.1 : ℤ) - 1, p.2.2), fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (Prod.ext (by omega) h.2.2)⟩

theorem mem_boxF (v : V) (h : (fv v).toNat ≤ 3) : v ∈ boxF := by
  obtain ⟨x, y, s⟩ := v
  have hb : F (x, y, s) ≤ 3 := by
    by_cases hv : ∃ o ∈ O, o.1 = (x, y, s)
    · obtain ⟨o, ho, he⟩ := hv
      have := (O_ok o ho).1
      rw [he] at this
      omega
    push Not at hv
    rw [fv_of _ hv] at h
    have := F_nonneg (x, y, s)
    omega
  obtain ⟨h1, h2, h3, h4⟩ := small_box x y s hb
  rw [boxF, Finset.mem_map]
  refine ⟨((x + 2).toNat, (y + 1).toNat, s), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    omega
  · show ((((x + 2).toNat : ℕ) : ℤ) - 2, (((y + 1).toNat : ℕ) : ℤ) - 1, s) = (x, y, s)
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨by omega, by omega, rfl⟩

/-- Up to n = 3, a n counts the cells of the box where fv = n. -/
theorem a_small (n : ℕ) (hn : n ≤ 3) : a n = (boxF.filter fun v => (fv v).toNat = n).card := by
  unfold a
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Finset.coe_filter]
  rw [dist_eq v]
  constructor
  · intro h
    exact ⟨mem_boxF v (by omega), h⟩
  · rintro ⟨-, h⟩
    exact h

/-- The coordination sequence below n = 3. -/
theorem small_vals : (List.range 3).map a = [1, 4, 8] := by
  rw [List.map_congr_left (fun n hn => a_small n (by rw [List.mem_range] at hn; omega))]
  decide +kernel


/-! ## Counting the spheres

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. The
gradient of facet i is gc i times the primitive vector (Ap i, Bp i), so the points of class s with
pot_i = n lie on the line Ap i x + Bp i y = c with c = lev s i n, and only when gc i divides
n - Cc s i. That line is par s i c u = (al i c + Bp i u, be i c - Ap i u), and potential j is
ka i j c + Dm i j u + Cc s j there (`pot_par`). The previous facet bounds u from above, the next one
from below, and for n ≥ 4 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 14 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T (a table entry plus its offset). -/
def ctabN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

def gcV (k : ℕ) : ℕ := ctabN 2593401 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 8) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 346320 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 8) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 3162050643 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 6

def Bp (i : Fin 8) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 8720595 3 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 2

def al (i : Fin 8) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 39440 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 8) : ℤ := beN i.val

theorem prim : ∀ i : Fin 8, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 8) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 8) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 8, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 11) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 11) (i j : Fin 8) (c u : ℤ) :
    pot (par s i c u) j = ka i j * c + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 8) :
    v = par v.2.2 i (Ap i * v.1 + Bp i * v.2.1) (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := (prim i).2.2.2
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb
  · linear_combination (-y) * hb

theorem pot_lev (v : V) (i : Fin 8) : pot v i = gc i * (Ap i * v.1 + Bp i * v.2.1) + Cc v.2.2 i := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  simp only [pot]
  rw [h1, h2]
  ring

theorem par_inj (s : Fin 11) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
  intro u u' h
  simp only [par, Prod.mk.injEq] at h
  have hb := (prim i).2.2.2
  have h1 : Bp i * (u - u') = 0 := by linarith [h.1]
  have h2 : Ap i * (u - u') = 0 := by linarith [h.2.1]
  have h3 : (u - u') = (u - u') * (al i * Ap i + be i * Bp i) := by rw [hb, mul_one]
  have : u - u' = 0 := by
    rw [h3]
    linear_combination (al i) * h2 + (be i) * h1
  linarith

/-- Some facet attains the maximum. -/
theorem F_attained (v : V) : ∃ k : Fin 8, pot v k = F v := by
  by_contra hne
  have h : ∀ k, pot v k ≤ F v - 1 := fun k => by
    have h1 := le_F v k
    have h2 : pot v k ≠ F v := fun e => hne ⟨k, e⟩
    omega
  have := F_le v (F v - 1) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)
  omega

/-- The first facet attaining the maximum. -/
noncomputable def fi (v : V) : Fin 8 := Fin.find (fun k => pot v k = F v) (F_attained v)

theorem fi_spec (v : V) : pot v (fi v) = F v ∧ ∀ j, j < fi v → pot v j < F v :=
  ⟨Fin.find_spec (F_attained v), fun j hj =>
    lt_of_le_of_ne (le_F v j) (Fin.find_min (F_attained v) hj)⟩

theorem fi_iff (v : V) (i : Fin 8) : fi v = i ↔ pot v i = F v ∧ ∀ j, j < i → pot v j < F v := by
  constructor
  · rintro rfl
    exact fi_spec v
  · rintro ⟨h1, h2⟩
    obtain ⟨g1, g2⟩ := fi_spec v
    rcases lt_trichotomy (fi v) i with h | h | h
    · exact absurd g1 (ne_of_lt (h2 _ h))
    · exact h
    · exact absurd h1 (ne_of_lt (g2 _ h))

theorem ite01 (c : Prop) [Decidable c] : (0 : ℤ) ≤ (if c then 1 else 0) ∧ (if c then 1 else 0 : ℤ) ≤ 1 := by
  split_ifs <;> norm_num

/-- On the sphere F = n, the first maximal facet is i exactly when potential i is n and every
potential j is at most n - [j < i]. -/
theorem piece_iff (v : V) (i : Fin 8) (n : ℤ) :
    (F v = n ∧ fi v = i) ↔ (pot v i = n ∧ ∀ j, pot v j ≤ n - (if j < i then 1 else 0)) := by
  rw [fi_iff]
  constructor
  · rintro ⟨rfl, h1, h2⟩
    refine ⟨h1, fun j => ?_⟩
    split_ifs with hj
    · have := h2 j hj
      omega
    · have := le_F v j
      omega
  · rintro ⟨h1, h2⟩
    have h3 : ∀ j, pot v j ≤ n := fun j => le_trans (h2 j) (sub_le_self n (ite01 _).1)
    have hF : F v = n := le_antisymm (F_le_all v n h3) (h1 ▸ le_F v i)
    refine ⟨hF, hF ▸ h1, fun j hj => ?_⟩
    have := h2 j
    rw [if_pos hj] at this
    omega

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (4 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 162987246945370814444402843728026948640286487860704695312120859838204625447815284355588227072 5 k

def cf1N (k : ℕ) : ℤ := (cf1V k : ℤ)

def cf1 (i : Fin 8) (j : Fin 8) : ℤ := cf1N (j.val + 8 * i.val)

def cf2V (k : ℕ) : ℕ := ctabN 5351872932789603181762479755355980489399624803426564409944996637966372608 4 k

def cf2N (k : ℕ) : ℤ := (cf2V k : ℤ)

def cf2 (i : Fin 8) (j : Fin 8) : ℤ := cf2N (j.val + 8 * i.val)

def cf3V (k : ℕ) : ℕ := ctabN 35476701661997291196103899152642124651726038237345061595384060346606116352 4 k

def cf3N (k : ℕ) : ℤ := (cf3V k : ℤ)

def cf3 (i : Fin 8) (j : Fin 8) : ℤ := cf3N (j.val + 8 * i.val)

def cf0V (k : ℕ) : ℕ := ctabN 220855885620441854753989178312657126319759412138259933541345197683779072 4 k

def cf0N (k : ℕ) : ℤ := (cf0V k : ℤ)

def cf0 (i : Fin 8) (j : Fin 8) : ℤ := cf0N (j.val + 8 * i.val)


/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The class constants Cc s i, packed for the kernel. -/
def cTV (k : ℕ) : ℕ := ctabN 3055479026944875531362612490753814036882076185563904026002465393450837888884620031823147530154966132029865 4 k

def cTN (k : ℕ) : ℤ := (cTV k : ℤ) - 5

def cT (s : Fin 11) (i : Fin 8) : ℤ := cTN (i.val + 8 * s.val)

theorem cT_eq : ∀ s : Fin 11, ∀ i : Fin 8, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 11) (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (4 - cT s i)

instance (i j : Fin 8) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 8, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

/-- certC in natural numbers, for the kernel: Cc = cTV - 5, the negative terms moved across; the
previous facet of i is (i + 7) % 8, the next one (i + 1) % 8. -/
def certNat (s i j : ℕ) : Bool :=
  Nat.blt ((cf1V (j + 8 * i) + cf2V (j + 8 * i) + cf0V (j + 8 * i)) * cTV (i + 8 * s) +
      cf3V (j + 8 * i) * cTV (j + 8 * s))
    (cf1V (j + 8 * i) * (cTV ((i + 7) % 8 + 8 * s) + (if (i + 7) % 8 < i then 1 else 0)) +
      cf2V (j + 8 * i) * (cTV ((i + 1) % 8 + 8 * s) + (if (i + 1) % 8 < i then 1 else 0)) +
      cf3V (j + 8 * i) * cTV (i + 8 * s) + cf0V (j + 8 * i) * 9)

def certOK : Bool :=
  (List.range 11).all fun s => (List.range 8).all fun i => (List.range 8).all fun j =>
    nearB i j || certNat s i j

theorem certOK_eq : certOK = true := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 8, (i - 1).val = (i.val + 7) % 8 := by decide +kernel

theorem fin_next : ∀ i : Fin 8, (i + 1).val = (i.val + 1) % 8 := by decide +kernel

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 11) (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  have hn : nearB i.val j.val = false := by
    have n1 : j.val ≠ i.val := fun h => e2 (Fin.ext h)
    have n2 : j.val ≠ (i.val + 1) % 8 := fun h => e3 (Fin.ext (h.trans a2.symm))
    have n3 : j.val ≠ (i.val + 7) % 8 := fun h => e1 (Fin.ext (h.trans a1.symm))
    simp only [nearB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨n1, n2⟩, n3⟩
  have hc := certOK_eq
  unfold certOK at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have hk := hc s.val s.isLt i.val i.isLt j.val j.isLt
  rw [hn, Bool.false_or] at hk
  simp only [certNat, Nat.blt_eq] at hk
  have ck := (Nat.cast_lt (α := ℤ)).mpr hk
  show 0 < cf1 i j * (cT s (i - 1) - cT s i + (if i - 1 < i then 1 else 0)) +
    cf2 i j * (cT s (i + 1) - cT s i + (if i + 1 < i then 1 else 0)) +
    cf3 i j * (cT s i - cT s j) + cf0 i j * (4 - cT s i)
  simp only [cf1, cf2, cf3, cf0, cf1N, cf2N, cf3N, cf0N, cT, cTN, Fin.lt_def, a1, a2]
  push_cast at ck ⊢
  ring_nf at ck ⊢
  linarith

theorem farkas4 (v : V) (h i k j : Fin 8) (e1 e2 r l1 l2 l3 l0 : ℤ)
    (hl : 0 ≤ l1 ∧ 0 ≤ l2 ∧ 0 ≤ l3 ∧ 0 ≤ l0)
    (hx : l1 * (Ac h - Ac i) + l2 * (Ac k - Ac i) + l3 * (Ac i - Ac j) - l0 * Ac i = 0)
    (hy : l1 * (Bc h - Bc i) + l2 * (Bc k - Bc i) + l3 * (Bc i - Bc j) - l0 * Bc i = 0)
    (hc : 0 < l1 * (Cc v.2.2 h - Cc v.2.2 i + e1) + l2 * (Cc v.2.2 k - Cc v.2.2 i + e2) +
      l3 * (Cc v.2.2 i - Cc v.2.2 j) + l0 * (r - Cc v.2.2 i))
    (f1 : pot v h ≤ pot v i - e1) (f2 : pot v k ≤ pot v i - e2) (f3 : pot v i ≤ pot v j)
    (f0 : r ≤ pot v i) : False := by
  have g1 := mul_nonpos_of_nonneg_of_nonpos hl.1 (show pot v h - pot v i + e1 ≤ 0 by linarith)
  have g2 := mul_nonpos_of_nonneg_of_nonpos hl.2.1 (show pot v k - pot v i + e2 ≤ 0 by linarith)
  have g3 := mul_nonpos_of_nonneg_of_nonpos hl.2.2.1 (show pot v i - pot v j ≤ 0 by linarith)
  have g0 := mul_nonpos_of_nonneg_of_nonpos hl.2.2.2 (show r - pot v i ≤ 0 by linarith)
  have e : l1 * (pot v h - pot v i + e1) + l2 * (pot v k - pot v i + e2) +
      l3 * (pot v i - pot v j) + l0 * (r - pot v i) =
      l1 * (Cc v.2.2 h - Cc v.2.2 i + e1) + l2 * (Cc v.2.2 k - Cc v.2.2 i + e2) +
        l3 * (Cc v.2.2 i - Cc v.2.2 j) + l0 * (r - Cc v.2.2 i) := by
    simp only [pot]
    linear_combination v.1 * hx + v.2.1 * hy
  linarith

/-- The level of the line of facet i through the points of class s with pot_i = n. -/
def lev (s : Fin 11) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 11) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 11) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 11) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 11) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 11) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 11) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 11) (i : Fin 8) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 8) : ka i i = gc i := by
  obtain ⟨h1, h2, -, hb⟩ := prim i
  rw [ka, h1, h2]
  linear_combination (gc i) * hb

theorem Dm_self (i : Fin 8) : Dm i i = 0 := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  rw [Dm, h1, h2]
  ring

theorem pot_par_self (s : Fin 11) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 4 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 11) (i : Fin 8) (n u : ℤ) (hn : 4 ≤ n)
    (hd : (n - Cc s i) % gc i = 0) (h1 : lo s i n ≤ u) (h2 : u ≤ hi s i n) :
    ∀ j, pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) := by
  have hi' := pot_par_self s i n u hd
  have hh := (pot_le_iff s i (i - 1) n u).2 ((le_hi_iff s i n u).1 h2)
  have hk := (pot_le_iff s i (i + 1) n u).2 ((lo_le_iff s i n u).1 h1)
  intro j
  by_cases e1 : j = i - 1
  · rw [e1]; exact hh
  by_cases e2 : j = i
  · simp only [e2, hi', lt_irrefl, if_false, sub_zero, le_refl]
  by_cases e3 : j = i + 1
  · rw [e3]; exact hk
  obtain ⟨c1, c2, c3, c0, cx, cy⟩ := certG_ok i j e1 e2 e3
  have cc := certC_ok s i j e1 e2 e3
  simp only [certC, cT_eq] at cc
  by_contra hne
  have f3 : pot (par s i (lev s i n) u) i ≤ pot (par s i (lev s i n) u) j := by
    have := (ite01 (j < i)).2
    rw [hi']
    linarith [not_le.1 hne]
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 4 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ
    (Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 11, ∀ j : Fin 8, -5 ≤ Cc s j ∧ Cc s j ≤ 5 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 3 * Ac 3 + 5 * Ac 4 = 16 ∧ 3 * Bc 3 + 5 * Bc 4 = 0 ∧
    5 * Ac 0 + 3 * Ac 7 = (-16) ∧ 5 * Bc 0 + 3 * Bc 7 = 0 ∧
    1 * Ac 5 + 0 * Ac 5 = 0 ∧ 1 * Bc 5 + 0 * Bc 5 = 7 ∧
    1 * Ac 1 + 0 * Ac 1 = 0 ∧ 1 * Bc 1 + 0 * Bc 1 = (-7) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 11) :
    16 * x ≤ 8 * F (x, y, s) + 40 ∧
    16 * (-x) ≤ 8 * F (x, y, s) + 40 ∧
    7 * y ≤ 1 * F (x, y, s) + 5 ∧
    7 * (-y) ≤ 1 * F (x, y, s) + 5 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 3 * pot (x, y, s) 3 + 5 * pot (x, y, s) 4 =
      16 * x + 3 * Cc s 3 + 5 * Cc s 4 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 3
  have r0 := le_F (x, y, s) 4
  have k0 := Cbound s 3
  have l0 := Cbound s 4
  have e1 : 5 * pot (x, y, s) 0 + 3 * pot (x, y, s) 7 =
      16 * (-x) + 5 * Cc s 0 + 3 * Cc s 7 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 7
  have k1 := Cbound s 0
  have l1 := Cbound s 7
  have e2 : 1 * pot (x, y, s) 5 + 0 * pot (x, y, s) 5 =
      7 * y + 1 * Cc s 5 + 0 * Cc s 5 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 5
  have r2 := le_F (x, y, s) 5
  have k2 := Cbound s 5
  have l2 := Cbound s 5
  have e3 : 1 * pot (x, y, s) 1 + 0 * pot (x, y, s) 1 =
      7 * (-y) + 1 * Cc s 1 + 0 * Cc s 1 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 1
  have r3 := le_F (x, y, s) 1
  have k3 := Cbound s 1
  have l3 := Cbound s 1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 11) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 11) (i : Fin 8) (n : ℤ) (hn : 4 ≤ n) :
    PF s i n = if (n - Cc s i) % gc i = 0 then
      (Finset.Icc (lo s i n) (hi s i n)).image (par s i (lev s i n)) else ∅ := by
  split_ifs with hd
  · ext v
    simp only [PF, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨-, hs, hv⟩
      obtain ⟨h1, h2⟩ := (piece_iff v i n).1 hv
      have hl : lev s i n = Ap i * v.1 + Bp i * v.2.1 := by
        rw [lev, ← h1, pot_lev, hs, Int.add_sub_cancel,
          Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
      have hv' := par_inv v i
      rw [hs, ← hl] at hv'
      refine ⟨be i * v.1 - al i * v.2.1, ⟨?_, ?_⟩, hv'.symm⟩
      · rw [lo_le_iff, ← pot_le_iff, ← hv']
        exact h2 (i + 1)
      · rw [le_hi_iff, ← pot_le_iff, ← hv']
        exact h2 (i - 1)
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      have hp := par_piece s i n u hn hd h1 h2
      have hv := (piece_iff (par s i (lev s i n) u) i n).2 ⟨pot_par_self s i n u hd, hp⟩
      exact ⟨mem_Bx _ n (le_of_eq hv.1), rfl, hv⟩
  · rw [PF]
    apply Finset.filter_false_of_mem
    rintro v - ⟨hs, hv⟩
    obtain ⟨h1, -⟩ := (piece_iff v i n).1 hv
    apply hd
    rw [← hs, ← h1, pot_lev, Int.add_sub_cancel, Int.mul_emod_right]

/-- The length of the piece (s, i) at level n, as an integer. -/
def inner (s : Fin 11) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 11) (i : Fin 8) (n : ℤ) (hn : 4 ≤ n) :
    (PF s i n).card = (inner s i n).toNat := by
  rw [piece_eq s i n hn, inner]
  split_ifs
  · rw [Finset.card_image_of_injective _ (par_inj s i _), Int.card_Icc]
  · rfl

/-- The number of points with F = n. -/
noncomputable def cnt (n : ℤ) : ℕ := Set.ncard {v : V | F v = n}

theorem cnt_eq_card (n : ℤ) : cnt n = ((Bx n).filter (fun v => F v = n)).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Finset.coe_filter]
  exact ⟨fun h => ⟨mem_Bx v n (le_of_eq h), h⟩, fun h => h.2⟩

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 11 × Fin 8, (PF p.1 p.2 n).card := by
  rw [cnt_eq_card, Finset.card_eq_sum_card_fiberwise (f := fun v => (v.2.2, fi v))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [PF, Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro v _
  constructor
  · rintro ⟨h1, h2⟩
    rw [← h2]
    exact ⟨rfl, h1, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, by rw [h1, h3]⟩

/-- The closed form of the sphere size: the sum of the piece lengths. -/
def S (n : ℤ) : ℤ := ∑ p : Fin 11 × Fin 8, inner p.1 p.2 n

/-! Shifting n by 14 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 3996053038 4 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 8) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 145557677 4 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 6

def mh (i : Fin 8) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 3565212800 4 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 6

def mk (i : Fin 8) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 8, (14 : ℤ) = gc i * Lq i ∧
    14 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    14 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 11) (i : Fin 8) (n : ℤ) :
    inner s i (n + 14) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 14 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 14 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 14) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 14) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 14) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 7 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 11 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 14) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqV (k : ℕ) : ℕ := ctabN 16580559 3 k

def lgqN (k : ℕ) : ℤ := (lgqV k : ℤ)

def lgq (i : Fin 8) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 8, (7 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 7 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 7 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 8, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 8 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 8) = 0 then mhN (c % 8) + mkN (c % 8) else 0

theorem gsN_eq (s : Fin 11) (i : Fin 8) (n : ℤ) :
    gsN (i.val + 8 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 8 * s.val) % 8 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (11 * 8)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhV (k : ℕ) : ℕ := ctabN 75170939 4 k

def uhN (k : ℕ) : ℤ := (uhV k : ℤ) - 3

def uh (i : Fin 8) : ℤ := uhN i.val

def dhV (k : ℕ) : ℕ := ctabN 248118484048 5 k

def dhN (k : ℕ) : ℤ := (dhV k : ℤ)

def dh (i : Fin 8) : ℤ := dhN i.val

def ukV (k : ℕ) : ℕ := ctabN 3849381232 4 k

def ukN (k : ℕ) : ℤ := (ukV k : ℤ) - 6

def uk (i : Fin 8) : ℤ := ukN i.val

def dkV (k : ℕ) : ℕ := ctabN 557320772654 5 k

def dkN (k : ℕ) : ℤ := (dkV k : ℤ)

def dk (i : Fin 8) : ℤ := dkN i.val

def vhV (k : ℕ) : ℕ := ctabN 3707384701212411681846513686447227294521687567005672118908072663483745917553656056499303840572535309616509 4 k

def vhN (k : ℕ) : ℤ := (vhV k : ℤ) - 7

def vh (s : Fin 11) (i : Fin 8) : ℤ := vhN (i.val + 8 * s.val)

def vkV (k : ℕ) : ℕ := ctabN 2558711772295477942406590388432477402332656374900367771014581551997713281300613341389808349465294375803270 4 k

def vkN (k : ℕ) : ℤ := (vkV k : ℤ) - 7

def vk (s : Fin 11) (i : Fin 8) : ℤ := vkN (i.val + 8 * s.val)

def levT (s : Fin 11) (i : Fin 8) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 11) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_facet : ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧
    uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) := by
  decide +kernel

theorem tab_class : ∀ s : Fin 11, ∀ i : Fin 8,
    vh s i = cT s i - cT s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    vk s i = cT s i - cT s (i + 1) - (if i + 1 < i then 1 else 0) := by
  decide +kernel

theorem tab_ok (s : Fin 11) (i : Fin 8) : uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  obtain ⟨f1, f2, f3, f4⟩ := tab_facet i
  obtain ⟨c1, c2⟩ := tab_class s i
  simp only [cT_eq] at c1 c2
  exact ⟨f1, c1, f2, f3, c2, f4⟩

theorem inner_eq (s : Fin 11) (i : Fin 8) (n : ℤ) : inner s i n = innerT s i n := by
  have hl : levT s i n = lev s i n := by rw [levT, lev, cT_eq]
  rw [inner, innerT, cT_eq, hl]
  split_ifs with hd
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := tab_ok s i
    have hc := lev_mul s i n hd
    have r1 : Rb s i (i - 1) n = uh i * lev s i n + vh s i := by
      rw [e1, e2, Rb]; linear_combination (-1 : ℤ) * hc
    have r2 : Rb s i (i + 1) n = uk i * lev s i n + vk s i := by
      rw [e4, e5, Rb]; linear_combination (-1 : ℤ) * hc
    rw [hi, lo, r1, r2, e3, e6]
    ring
  · rfl

/-- The closed form in table form. -/
def ST (n : ℤ) : ℤ := ∑ p : Fin 11 × Fin 8, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 8 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 8) = 0 then
    (uhN (c % 8) * ((n - cTN c) / gcN (c % 8)) + vhN c) / dhN (c % 8) +
      (ukN (c % 8) * ((n - cTN c) / gcN (c % 8)) + vkN c) / dkN (c % 8) + 1
  else 0

theorem innerN_eq (s : Fin 11) (i : Fin 8) (n : ℤ) :
    innerN (i.val + 8 * s.val) n = innerT s i n := by
  have hi := i.isLt
  have h : (i.val + 8 * s.val) % 8 = i.val := by omega
  rw [innerN, h]
  rfl

theorem sum_range_list (f : ℕ → ℤ) (N : ℕ) :
    ∑ c ∈ Finset.range N, f c = ((List.range N).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The closed form over the indices of the pieces. -/
def STN (n : ℤ) : ℤ := ((List.range (11 * 8)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 11 × Fin 8 => innerT q.1 q.2 n)
    (fun c : Fin (11 * 8) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (11 * 8), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 11 × Fin 8 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (11 * 8) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (11 * 8), sum_range_list]

/-- The closed form's tables, packed: the steps, the values on one period from 3 and below 3. -/
def dtabV (k : ℕ) : ℕ := ctabN 2164168456159 6 k

def tblV (k : ℕ) : ℕ := ctabN 2787994592397 6 k

def initV (k : ℕ) : ℕ := ctabN 2113 4 k

/-- The step of the closed form at residue t mod 7. -/
def dv (t : ℕ) : ℕ := dtabV (t % 7)

/-- The sequence in closed form: b(n + 7) = b(n) + dv (n - 3) for n ≥ 3. -/
def b (n : ℕ) : ℕ :=
  if n < 3 then initV n else dv (n - 3) * ((n - 3) / 7) + tblV ((n - 3) % 7)

theorem b_step (n : ℕ) (hn : 3 ≤ n) : b (n + 7) = b n + dv (n - 3) := by
  rw [b, b, if_neg (show ¬ (n + 7 < 3) by omega), if_neg (show ¬ (n < 3) by omega),
    show n + 7 - 3 = n - 3 + 7 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 7)]
  ring

theorem b_shift (n : ℕ) (hn : 3 ≤ n) : b (n + 14) = b n + 2 * dv (n - 3) := by
  rw [b, b, if_neg (show ¬ (n + 14 < 3) by omega), if_neg (show ¬ (n < 3) by omega),
    show n + 14 - 3 = n - 3 + 7 * 2 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 7)]
  ring

/-- b on the residue class of 3 + j mod 7. -/
theorem b_res (k j : ℕ) (hj : j < 7) : b (7 * k + (3 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (7 * k + (3 + j) < 3) by omega),
    show 7 * k + (3 + j) - 3 = j + 7 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 7), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The growth of S over one period at each residue mod 7. -/
def GsT : List ℤ := [68, 62, 62, 62, 62, 62, 62]

theorem Gs_tab : ∀ r : ℕ, r < 7 → GsN (r : ℤ) = GsT.getD r 0 := by
  decide +kernel

/-- The growth of b over 14 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 7 → 2 * (dv t : ℤ) = GsT.getD ((3 + t) % 7) 0 := by
  decide +kernel

theorem grow (n : ℕ) (_hn : 3 ≤ n) : 2 * (dv (n - 3) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 3) % 7) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 3) % 7) = dv (n - 3) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 7 ∣ 7)]
  have e2 : (3 + (n - 3) % 7) % 7 = n % 7 := by omega
  rw [e1, e2, ← Gs_tab (n % 7) (Nat.mod_lt _ (by norm_num)), ← Gs_eq_GsN] at h1
  rw [h1]
  have e3 : (((n % 7 : ℕ) : ℤ) + 7 * ((n / 7 : ℕ) : ℤ)) = n := by omega
  rw [← e3, Gs_periodic]

/-- One kernel pass over n = 4, ..., 17: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 14 →
    ((List.range (11 * 8)).all fun c => decide (0 ≤ innerN c (4 + (r : ℤ)))) = true ∧
      STN (4 + (r : ℤ)) = b (4 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 4 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 11) (i : Fin 8) (n : ℤ) (hn : 4 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 4 + t := ⟨(n - 4).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 14
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 8 * s.val < 11 * 8 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 14) (by omega) (by omega)
      have e : (4 : ℤ) + t = (4 + (t - 14 : ℕ)) + 14 := by
        push_cast [Nat.cast_sub (by omega : 14 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 4 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 4 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 18
    · obtain ⟨r, rfl⟩ : ∃ r, n = 4 + r := ⟨n - 4, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 14) (by omega) (by omega)
      have h2 := S_shift ((n - 14 : ℕ) : ℤ)
      have h3 := b_shift (n - 14) (by omega)
      have h4 := grow (n - 14) (by omega)
      rw [show n - 14 + 14 = n by omega] at h3
      rw [show ((n - 14 : ℕ) : ℤ) + 14 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 3 lie in the box -4 ≤ x ≤ 4, -1 ≤ y ≤ 1 (`small_box`), and
the kernel checks that those of the box are the 26 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 11) (h : F (x, y, s) ≤ 3) :
    -4 ≤ x ∧ x ≤ 4 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 3, with their values of F. -/
def smallV : List (V × ℤ) :=
  [((0, 0, 7), 1), ((0, 0, 8), 1), ((1, 0, 6), 1), ((1, 0, 8), 1), (((-1), 0, 7), 2), ((0, 0, 5), 2), ((0, 0, 6), 2), ((0, 0, 9), 2), ((0, 0, 10), 2), ((1, 0, 7), 2), ((1, 0, 10), 2), ((1, 1, 0), 2), ((1, 1, 4), 2), (((-1), 0, 8), 3), (((-1), 0, 9), 3), ((0, 0, 2), 3), ((0, 0, 3), 3), ((0, 1, 0), 3), ((0, 1, 1), 3), ((0, 1, 4), 3), ((1, 0, 5), 3), ((1, 0, 9), 3), ((1, 1, 1), 3), ((2, 0, 6), 3), ((2, 0, 8), 3), ((2, 1, 0), 3)]

def smallL : List V := smallV.map Prod.fst

theorem smallV_ok : (smallV.all fun q => decide (F q.1 = q.2)) = true := by
  decide +kernel

/-- The potentials, packed: Ac = ATV - 2, Bc = BTV - 7. -/
def ATV (k : ℕ) : ℕ := ctabN 346320 3 k

def ATN (k : ℕ) : ℤ := (ATV k : ℤ) - 2

def AT (i : Fin 8) : ℤ := ATN i.val

def BTV (k : ℕ) : ℕ := ctabN 3454673156 4 k

def BTN (k : ℕ) : ℤ := (BTV k : ℤ) - 7

def BT (i : Fin 8) : ℤ := BTN i.val

theorem AB_eq : ∀ i : Fin 8, AT i = Ac i ∧ BT i = Bc i := by
  decide +kernel

/-- Some potential exceeds 3 at the box point ((a : ℤ) - 4, (b : ℤ) - 1, s), in natural
numbers: the negative terms moved across. -/
def bigNat (a b s : ℕ) : Bool :=
  (List.range 8).any fun i =>
    Nat.blt (8 + ATV i * 4 + 2 * a + BTV i * 1 + 7 * b)
      (ATV i * a + 8 + BTV i * b + 7 + cTV (i + 8 * s))

theorem big_pot (a b : ℕ) (s : Fin 11) (h : bigNat a b s.val = true) :
    (3 : ℤ) < F ((a : ℤ) - 4, (b : ℤ) - 1, s) := by
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  have hl := (Nat.cast_lt (α := ℤ)).mpr (Nat.blt_eq.mp hb)
  have hp := le_F ((a : ℤ) - 4, (b : ℤ) - 1, s) ⟨i, hi⟩
  obtain ⟨eA, eB⟩ := AB_eq ⟨i, hi⟩
  have e3 := cT_eq s ⟨i, hi⟩
  simp only [pot] at hp
  rw [← eA, ← eB, ← e3] at hp
  simp only [AT, BT, ATN, BTN, cT, cTN] at hp
  push_cast at hl hp
  ring_nf at hl hp ⊢
  linarith

def smallOK : Bool :=
  (List.range 9).all fun a => (List.range 3).all fun b => (List.finRange 11).all fun s =>
    bigNat a b s.val || decide (((a : ℤ) - 4, (b : ℤ) - 1, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 3) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 4).toNat (by omega) (y + 1).toNat (by omega) s
  have ex : (((x + 4).toNat : ℕ) : ℤ) - 4 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h1 | h1
  · have := big_pot _ _ s h1
    rw [ex, ey] at this
    omega
  · rw [ex, ey] at h1
    exact h1

theorem cnt_small (n : ℤ) (hn : n ≤ 3) :
    cnt n = (((smallV.filter (fun q => decide (q.2 = n))).map Prod.fst).toFinset).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext v
  have hv := smallV_ok
  simp only [List.all_eq_true, decide_eq_true_eq] at hv
  simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (small_mem v (by omega))
    exact ⟨q, ⟨hq, by rw [← hv q hq]; exact h⟩, rfl⟩
  · rintro ⟨q, ⟨hq, h2⟩, rfl⟩
    rw [hv q hq]
    exact h2

/-- The small spheres from 3 on, in closed form. -/
theorem small_ok : ∀ n : ℕ, 3 ≤ n → n < 4 →
    (((smallV.filter (fun q => decide (q.2 = (n : ℤ)))).map Prod.fst).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n from n = 3 on (`a_eq_cnt`, from `a_eq_F`), and `small_vals`
lists the terms below 3. The terms from 3 to 3 are counted in `smallL`, those from 4 on
are S(n), and all agree with the closed form b (`a_eq_b`). The step from n to n + 7, the closed form
per residue (`a_closed`), the controls, the recurrence and the g.f. follow, their base cases checked by
the kernel on b. -/

theorem a_eq_cnt (n : ℕ) (hn : 3 ≤ n) : a n = cnt n := by
  rw [a_eq_F n hn, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt n (by omega)]
  exact cnt_eq_S n (by exact_mod_cast hn)

theorem a_lt_R0 (n : ℕ) (hn : n < 3) : a n = b n := by
  have h : (List.range 3).map a = (List.range 3).map b := by
    rw [small_vals]
    decide +kernel
  exact List.map_inj_left.1 h n (List.mem_range.2 hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 3 ∨ (3 ≤ n ∧ n < 4) ∨ 4 ≤ n by omega) with h | ⟨h1, h2⟩ | h
  · exact a_lt_R0 n h
  · rw [a_eq_cnt n h1, cnt_small _ (by omega)]
    exact small_ok n h1 h2
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 7) = a(n) + dv (n - 3) for n ≥ 3. -/
theorem a_step (n : ℕ) (hn : 3 ≤ n) : a (n + 7) = a n + dv (n - 3) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-- The steps and the values on one period, by the kernel. -/
theorem closed_vals : dv 0 = 31 ∧ tblV 0 = 13 ∧ dv 1 = 31 ∧ tblV 1 = 18 ∧ dv 2 = 31 ∧ tblV 2 = 22 ∧ dv 3 = 31 ∧ tblV 3 = 27 ∧ dv 4 = 34 ∧ tblV 4 = 33 ∧ dv 5 = 31 ∧ tblV 5 = 36 ∧ dv 6 = 31 ∧ tblV 6 = 40 := by
  decide +kernel

/-- The closed form per residue of n mod 7, for n ≥ 3. -/
theorem a_closed (k : ℕ) :
    a (7 * k + 3) = 31 * k + 13 ∧
    a (7 * k + 4) = 31 * k + 18 ∧
    a (7 * k + 5) = 31 * k + 22 ∧
    a (7 * k + 6) = 31 * k + 27 ∧
    a (7 * k + 7) = 34 * k + 33 ∧
    a (7 * k + 8) = 31 * k + 36 ∧
    a (7 * k + 9) = 31 * k + 40 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := closed_vals
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 7 * k + 3 = 7 * k + (3 + 0) from rfl, b_res k 0 (by norm_num), c0, c1]
  · rw [show 7 * k + 4 = 7 * k + (3 + 1) from rfl, b_res k 1 (by norm_num), c2, c3]
  · rw [show 7 * k + 5 = 7 * k + (3 + 2) from rfl, b_res k 2 (by norm_num), c4, c5]
  · rw [show 7 * k + 6 = 7 * k + (3 + 3) from rfl, b_res k 3 (by norm_num), c6, c7]
  · rw [show 7 * k + 7 = 7 * k + (3 + 4) from rfl, b_res k 4 (by norm_num), c8, c9]
  · rw [show 7 * k + 8 = 7 * k + (3 + 5) from rfl, b_res k 5 (by norm_num), c10, c11]
  · rw [show 7 * k + 9 = 7 * k + (3 + 6) from rfl, b_res k 6 (by norm_num), c12, c13]

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 13, 18, 22, 27, 33, 36, 40, 44, 49, 53, 58, 67, 67, 71, 75, 80, 84, 89, 101, 98, 102, 106, 111, 115, 120, 135, 129, 133, 137, 142, 146, 151, 169, 160, 164, 168, 173, 177, 182, 203, 191, 195, 199, 204, 208, 213, 237] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 7 → (dv (t + 14) : ℤ) = 2 * (dv (t + 7) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 14) : ℤ) = 2 * (dv (t + 7) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 7 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 7, e 14]
  exact drec_base (t % 7) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 7 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 7 → (b (q + 17) : ℤ) = 2 * b (q + 10) - b (q + 3) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 17) : ℤ) = 2 * b (q + 10) - b (q + 3) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 7 ∨ 7 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 7 := ⟨q - 7, by omega⟩
      have h0 : (b (v + 17) : ℤ) = 2 * b (v + 10) - b (v + 3) := ih (v + 0) (by omega)
      have s3 : b (v + 10) = b (v + 3) + dv (v + 0) := by
        have h := b_step (v + 3) (by omega)
        rw [show v + 3 + 7 = v + 10 by omega,
          show v + 3 - 3 = v + 0 by omega] at h
        exact h
      have s10 : b (v + 17) = b (v + 10) + dv (v + 7) := by
        have h := b_step (v + 10) (by omega)
        rw [show v + 10 + 7 = v + 17 by omega,
          show v + 10 - 3 = v + 7 by omega] at h
        exact h
      have s17 : b (v + 24) = b (v + 17) + dv (v + 14) := by
        have h := b_step (v + 17) (by omega)
        rw [show v + 17 + 7 = v + 24 by omega,
          show v + 17 - 3 = v + 14 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 24) : ℤ) = 2 * b (v + 17) - b (v + 10)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 16 < n → (a n : ℤ) = 2 * a (n - 7) - a (n - 14) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 17 := ⟨n - 17, by omega⟩
  rw [show q + 17 - 7 = q + 10 by omega, show q + 17 - 14 = q + 3 by omega]
  simp only [a_eq_b]
  exact b_recur q

/-- The coefficients of the g.f. below 17, by the kernel. -/
theorem gf_base : ∀ n : ℕ, n < 17 → 1 * (b n : ℤ) - 2 * (if 7 ≤ n then (b (n - 7) : ℤ) else 0) + 1 * (if 14 ≤ n then (b (n - 14) : ℤ) else 0) = (if n = 0 then (1 : ℤ) else 0) + (if n = 1 then (1 : ℤ) else 0) * 4 + (if n = 2 then (1 : ℤ) else 0) * 8 + (if n = 3 then (1 : ℤ) else 0) * 13 + (if n = 4 then (1 : ℤ) else 0) * 18 + (if n = 5 then (1 : ℤ) else 0) * 22 + (if n = 6 then (1 : ℤ) else 0) * 27 + (if n = 7 then (1 : ℤ) else 0) * 31 + (if n = 8 then (1 : ℤ) else 0) * 28 + (if n = 9 then (1 : ℤ) else 0) * 24 + (if n = 10 then (1 : ℤ) else 0) * 18 + (if n = 11 then (1 : ℤ) else 0) * 13 + (if n = 12 then (1 : ℤ) else 0) * 9 + (if n = 13 then (1 : ℤ) else 0) * 4 + (if n = 14 then (1 : ℤ) else 0) * 2 - (if n = 15 then (1 : ℤ) else 0) * 1 - (if n = 16 then (1 : ℤ) else 0) * 1 := by
  decide +kernel

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - 2 * X ^ 7 + 1) =
      -X ^ 16 - X ^ 15 + 2 * X ^ 14 + 4 * X ^ 13 + 9 * X ^ 12 + 13 * X ^ 11 + 18 * X ^ 10 + 24 * X ^ 9 + 28 * X ^ 8 + 31 * X ^ 7 + 27 * X ^ 6 + 22 * X ^ 5 + 18 * X ^ 4 + 13 * X ^ 3 + 8 * X ^ 2 + 4 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (X ^ 14 - 2 * X ^ 7 + 1) = C 1 * A - C 2 * (A * X ^ 7) + C 1 * (A * X ^ 14) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : (-X ^ 16 - X ^ 15 + 2 * X ^ 14 + 4 * X ^ 13 + 9 * X ^ 12 + 13 * X ^ 11 + 18 * X ^ 10 + 24 * X ^ 9 + 28 * X ^ 8 + 31 * X ^ 7 + 27 * X ^ 6 + 22 * X ^ 5 + 18 * X ^ 4 + 13 * X ^ 3 + 8 * X ^ 2 + 4 * X + 1 : ℚ⟦X⟧) = C 1 + X ^ 1 * C 4 + X ^ 2 * C 8 + X ^ 3 * C 13 + X ^ 4 * C 18 + X ^ 5 * C 22 + X ^ 6 * C 27 + X ^ 7 * C 31 + X ^ 8 * C 28 + X ^ 9 * C 24 + X ^ 10 * C 18 + X ^ 11 * C 13 + X ^ 12 * C 9 + X ^ 13 * C 4 + X ^ 14 * C 2 - X ^ 15 * C 1 - X ^ 16 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 17 with hn | hn
  · have h := congrArg (fun z : ℤ => (z : ℚ)) (gf_base n hn)
    push_cast at h
    linarith
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 17 := ⟨n - 17, by omega⟩
    have h : (b (q + 17) : ℤ) = 2 * b (q + 10) - b (q + 3) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 17 - 7 = q + 10 by omega, show q + 17 - 14 = q + 3 by omega, show 7 ≤ q + 17 by omega, show 14 ≤ q + 17 by omega, show ¬ q + 17 = 0 by omega, show ¬ q + 17 = 1 by omega, show ¬ q + 17 = 2 by omega, show ¬ q + 17 = 3 by omega, show ¬ q + 17 = 4 by omega, show ¬ q + 17 = 5 by omega, show ¬ q + 17 = 6 by omega, show ¬ q + 17 = 7 by omega, show ¬ q + 17 = 8 by omega, show ¬ q + 17 = 9 by omega, show ¬ q + 17 = 10 by omega, show ¬ q + 17 = 11 by omega, show ¬ q + 17 = 12 by omega, show ¬ q + 17 = 13 by omega, show ¬ q + 17 = 14 by omega, show ¬ q + 17 = 15 by omega, show ¬ q + 17 = 16 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - 2 * X ^ 7 + 1) =
      -X ^ 16 - X ^ 15 + 2 * X ^ 14 + 4 * X ^ 13 + 9 * X ^ 12 + 13 * X ^ 11 + 18 * X ^ 10 + 24 * X ^ 9 + 28 * X ^ 8 + 31 * X ^ 7 + 27 * X ^ 6 + 22 * X ^ 5 + 18 * X ^ 4 + 13 * X ^ 3 + 8 * X ^ 2 + 4 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 16 < n → (a n : ℤ) = 2 * a (n - 7) - a (n - 14) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 13, 18, 22, 27, 33, 36, 40, 44, 49, 53, 58, 67, 67, 71, 75, 80, 84, 89, 101, 98, 102, 106, 111, 115, 120, 135, 129, 133, 137, 142, 146, 151, 169, 160, 164, 168, 173, 177, 182, 203, 191, 195, 199, 204, 208, 213, 237] := Count.controls

/-- The step a(n + 7) = a(n) + Count.dv (n - 3) for n ≥ 3. -/
theorem a_step (n : ℕ) (hn : 3 ≤ n) : a (n + 7) = a n + Count.dv (n - 3) := Count.a_step n hn

/-- The closed form per residue of n mod 7, for n ≥ 3. -/
theorem a_closed (k : ℕ) :
    a (7 * k + 3) = 31 * k + 13 ∧
    a (7 * k + 4) = 31 * k + 18 ∧
    a (7 * k + 5) = 31 * k + 22 ∧
    a (7 * k + 6) = 31 * k + 27 ∧
    a (7 * k + 7) = 34 * k + 33 ∧
    a (7 * k + 8) = 31 * k + 36 ∧
    a (7 * k + 9) = 31 * k + 40 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - 2 * X ^ 7 + 1) =
      -X ^ 16 - X ^ 15 + 2 * X ^ 14 + 4 * X ^ 13 + 9 * X ^ 12 + 13 * X ^ 11 + 18 * X ^ 10 + 24 * X ^ 9 + 28 * X ^ 8 + 31 * X ^ 7 + 27 * X ^ 6 + 22 * X ^ 5 + 18 * X ^ 4 + 13 * X ^ 3 + 8 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = 2 * a (n - 7) - a (n - 14) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a312105

theorem OMA.solution : type_of% @OMA.S_oeis_a312105.main :=
  OMA.S_oeis_a312105.conjecture
