import OMAStatements.S_oeis_a310289

namespace OMA.S_oeis_a310289






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 9

/-- Field k of the B-bit fields packed in the natural number T, as stored. The table accessors call
the kernel's natural number primitives directly: through the operators' type-class instances the
kernel decisions take more memory. -/
def tgetN (T B k : ℕ) : ℕ := Nat.mod (Nat.shiftRight T (Nat.mul B k)) (Nat.pow 2 B)

/-- Field k of the B-bit fields packed in T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := Int.subNatNat (tgetN T B k) off

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 723845286024
  | 1 => 650580302199
  | 2 => 587013523013
  | 3 => 586727196502
  | 4 => 659992180327
  | 5 => 514000197188
  | 6 => 509133760613
  | 7 => 582147086438
  | 8 => 513713870677
  | _ => 0

/-- The potential t is Ac t * x + Bc t * y + Cc s t at (x, y, s) (packed tables). -/
def Ac (i : Fin 10) : ℤ := tget 367114566005 4 8 i.val

def Bc (i : Fin 10) : ℤ := tget 596139074630 4 8 i.val

def Cc (s : Fin 9) (i : Fin 10) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The potential t at v. -/
def pot (v : V) (i : Fin 10) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest potential at v. -/
def F (v : V) : ℤ := max (max (max (max (max (max (max (max (max (pot v 0) (pot v 1)) (pot v 2)) (pot v 3)) (pot v 4)) (pot v 5)) (pot v 6)) (pot v 7)) (pot v 8)) (pot v 9)

theorem le_F0 (v : V) : pot v 0 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))))))))
theorem le_F1 (v : V) : pot v 1 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))))
theorem le_F2 (v : V) : pot v 2 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))))
theorem le_F3 (v : V) : pot v 3 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))
theorem le_F4 (v : V) : pot v 4 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))
theorem le_F5 (v : V) : pot v 5 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))
theorem le_F6 (v : V) : pot v 6 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
theorem le_F7 (v : V) : pot v 7 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
theorem le_F8 (v : V) : pot v 8 ≤ F v := le_max_of_le_left (le_max_right _ _)
theorem le_F9 (v : V) : pot v 9 ≤ F v := le_max_right _ _

theorem le_F (v : V) (i : Fin 10) : pot v i ≤ F v := by
  fin_cases i
  exacts [le_F0 v, le_F1 v, le_F2 v, le_F3 v, le_F4 v, le_F5 v, le_F6 v, le_F7 v, le_F8 v, le_F9 v]

theorem F_le (v : V) (t : ℤ) (h0 : pot v 0 ≤ t) (h1 : pot v 1 ≤ t) (h2 : pot v 2 ≤ t) (h3 : pot v 3 ≤ t) (h4 : pot v 4 ≤ t) (h5 : pot v 5 ≤ t) (h6 : pot v 6 ≤ t) (h7 : pot v 7 ≤ t) (h8 : pot v 8 ≤ t) (h9 : pot v 9 ≤ t) : F v ≤ t :=
  max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9

theorem F_le_all (v : V) (t : ℤ) (h : ∀ i, pot v i ≤ t) : F v ≤ t :=
  F_le v t (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9)

theorem max_ex {v : V} {a b : ℤ} (ha : ∃ i, a = pot v i) (hb : ∃ i, b = pot v i) :
    ∃ i, max a b = pot v i := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem exists_F (v : V) : ∃ i, F v = pot v i :=
  max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (⟨0, rfl⟩) ⟨1, rfl⟩) ⟨2, rfl⟩) ⟨3, rfl⟩) ⟨4, rfl⟩) ⟨5, rfl⟩) ⟨6, rfl⟩) ⟨7, rfl⟩) ⟨8, rfl⟩) ⟨9, rfl⟩

/-- The level of class s beyond which the far argument runs (the near box of class s covers the rest). -/
def R0N (s : Fin 9) : ℕ := tgetN 41231686057 4 s.val

def R0c (s : Fin 9) : ℤ := (R0N s : ℤ)

/-- The pairs (class s, potential t) and the classes whose rule, far, side and near checks are made;
the others follow by the symmetry sig. -/
def repB (s : Fin 9) (t : Fin 10) : Bool := decide (tgetN 656446721203136865494400543 1 (s.val * 10 + t.val) = 1)

def repC (s : Fin 9) : Bool := decide (tgetN 319 1 s.val = 1)

/-- A symmetry of order 2 of the graph that fixes v0 and permutes the potentials:
(x, y, s) ↦ (1 x + 0 y + tauX s, 0 x + (-1) y + tauY s, piS s), and potential t goes to rhoP t. -/
def piS (s : Fin 9) : Fin 9 := ⟨tgetN 34987063056 4 s.val % 9, Nat.mod_lt _ (by norm_num)⟩

def tauX (s : Fin 9) : ℤ := tget 36650387592 4 8 s.val

def tauY (s : Fin 9) : ℤ := tget 32069089160 4 8 s.val

def rhoP (t : Fin 10) : Fin 10 := ⟨tgetN 618780710520 4 t.val % 10, Nat.mod_lt _ (by norm_num)⟩

def sig (v : V) : V :=
  (1 * v.1 + 0 * v.2.1 + tauX v.2.2, 0 * v.1 + (-1) * v.2.1 + tauY v.2.2, piS v.2.2)

/-- The change of the potential j along the edge e. -/
def dl (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 10) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

/-- Along an edge e the potential j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 10) :
    pot (x + e.2.2.1, y + e.2.2.2, e.2.1) j = pot (x, y, e.1) j + dl e j := by
  simp only [pot, dl]
  ring

theorem pair_of {a f b : ℤ} (hl : a ≤ f) (hf : f = b) : a ≤ b + 0 := by omega

theorem bound_of {r f b : ℤ} (hr : r < f) (hf : f = b) : r + 1 ≤ b := by omega

theorem not_pair2 {a b : ℤ} (h : ¬ a ≤ b + (-2)) : b ≤ a + 1 := by omega

/-- Three facts pot a_k ≤ pot b_k + t_k and a bound r ≤ pot i0 at (x, y, s), with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas (x y : ℤ) (s : Fin 9) (a1 b1 a2 b2 a3 b3 i0 : Fin 10) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
def nb (t : Fin 10) (k : Fin 4) : Fin 10 :=
  ⟨(tget 825496364750223879328017494777994392052920484105 4 0 (t.val * 4 + k.val)).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The slot k of t holds another potential. -/
def real (t : Fin 10) (k : Fin 4) : Bool := decide (nb t k ≠ t)

/-- The potential t is a facet: a slot on each side cannot both come within 1 of t beyond R0c. -/
def facetB (t : Fin 10) : Bool := decide (tget 495 1 0 t.val = 1)

/-- The potential j is neither t nor in a slot of t. -/
def nonadj (t j : Fin 10) : Bool :=
  decide (j ≠ t) && decide (j ≠ nb t 0) && decide (j ≠ nb t 1) && decide (j ≠ nb t 2) && decide (j ≠ nb t 3)

/-- Certificates of the far facts, the same for every class: for maximal potential t and a potential
j that is not a neighbor of t, the fields k1, k2, m1, m2, m0, mj of entry t * 10 + j give the facts
pot k1 ≤ pot t, pot k2 ≤ pot t, R0c s + 1 ≤ pot t and pot t ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fd (t j : Fin 10) (f : ℕ) : ℤ := tget 2592948070776861252424657397584662940238632094478103165051387703754954586051478445537195168911434884067840518680967337399342325537467790248278778733102530334214068212551152170484260234384465583499434315193426824917371878862750745354296858053810037304049099444339148064853743247837140244833989376966938226410742393023268871988376716618646978059580804517564574808776060076541439476247340431480806148256586566965717486420994822867213472785873593117088996749727043326274814944912605329148611932366612162488099221842576450699796950567164896850926719298405632141231955944019615545661595461150719194876228624602959854094772885093333041030248535071957088819975668980162056829948257614119937124509634769572859999630758786798477816061302068409908489218704348976939988570403348183322052130732677007890880652155764370655084908320563754908766766089871942827850346371371923519782311182864749319094999125455751118797573251982269868240466387990186266572054717443848737265916162574776959776351089486468513976371452385647880213315520594242239734310714281427591268166569329483589125103519509171052611616 6 32 ((t.val * 10 + j.val) * 6 + f)

def fk1 (t j : Fin 10) : Fin 10 := ⟨(fd t j 0).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

def fk2 (t j : Fin 10) : Fin 10 := ⟨(fd t j 1).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The x and y parts of the far certificate of (t, j) cancel. -/
def farXY (t j : Fin 10) : Bool :=
  decide (0 ≤ fd t j 2 ∧ 0 ≤ fd t j 3 ∧ 0 ≤ fd t j 5 ∧ 0 ≤ fd t j 4 ∧
    fd t j 2 * (Ac (fk1 t j) - Ac t) + fd t j 3 * (Ac (fk2 t j) - Ac t) + fd t j 5 * (Ac t - Ac j) -
      fd t j 4 * Ac t = 0 ∧
    fd t j 2 * (Bc (fk1 t j) - Bc t) + fd t j 3 * (Bc (fk2 t j) - Bc t) + fd t j 5 * (Bc t - Bc j) -
      fd t j 4 * Bc t = 0)

/-- The constants of the far certificate of (t, j) at class s add up to a positive number. -/
def farC (s : Fin 9) (t j : Fin 10) : Bool :=
  decide (0 < fd t j 2 * (Cc s (fk1 t j) - Cc s t - 0) + fd t j 3 * (Cc s (fk2 t j) - Cc s t - 0) +
    fd t j 5 * (Cc s t - Cc s j - 1) + fd t j 4 * (R0c s + 1 - Cc s t))

/-- The far certificates of the maximal potential t are valid. -/
def farsOK (t : Fin 10) : Bool :=
  (List.finRange 10).all fun j => !nonadj t j || (farXY t j && (List.finRange 9).all fun s => !repB s t || farC s t j)

/-- Beyond F = R0c s, a potential that is not a neighbor of a maximal potential t has slack at least 2. -/
theorem far (s : Fin 9) (t j : Fin 10) (hxy : farXY t j = true) (hc0 : farC s t j = true) (x y : ℤ)
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
def sd (t : Fin 10) (i f : ℕ) : ℤ := tget 5530367004832347462959613156438719022252411931383399294419484658147889496440320529508106258311396798923617025373144591036919543502297520061480271708856392588005367327757449145772079240240340960970537427096555235688647838688258275178999824987652530332284773591730761143701850268342486534922881595042320 5 16 ((t.val * 4 + i) * 5 + f)

def sk (t : Fin 10) (i : ℕ) : Fin 10 := ⟨(sd t i 0).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

def sideXY (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 ≤ sd t i 1 ∧ 0 ≤ sd t i 2 ∧ 0 ≤ sd t i 3 ∧ 0 ≤ sd t i 4 ∧
    sd t i 1 * (Ac (sk t i) - Ac t) + sd t i 2 * (Ac t - Ac (nb t kl)) + sd t i 3 * (Ac t - Ac (nb t kr)) -
      sd t i 4 * Ac t = 0 ∧
    sd t i 1 * (Bc (sk t i) - Bc t) + sd t i 2 * (Bc t - Bc (nb t kl)) + sd t i 3 * (Bc t - Bc (nb t kr)) -
      sd t i 4 * Bc t = 0)

def sideC (s : Fin 9) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 < sd t i 1 * (Cc s (sk t i) - Cc s t - 0) + sd t i 2 * (Cc s t - Cc s (nb t kl) - 1) +
    sd t i 3 * (Cc s t - Cc s (nb t kr) - 1) + sd t i 4 * (R0c s + 1 - Cc s t))

def sideOK (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  !(real t kl && real t kr) || (sideXY t kl kr i && (List.finRange 9).all fun s => !repB s t || sideC s t kl kr i)

/-- All side certificates are valid. -/
def sidesOK : Bool :=
  (List.finRange 10).all fun t =>
    !facetB t || (sideOK t 0 2 0 && sideOK t 0 3 1 && sideOK t 1 2 2 && sideOK t 1 3 3)

/-- Beyond F = R0c s, a facet t has no slot on each side within 1 of it. -/
theorem side (s : Fin 9) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) (hxy : sideXY t kl kr i = true)
    (hc0 : sideC s t kl kr i = true) (x y : ℤ) (hL : pot (x, y, s) t ≤ pot (x, y, s) (nb t kl) + 1)
    (hR : pot (x, y, s) t ≤ pot (x, y, s) (nb t kr) + 1) (h : F (x, y, s) = pot (x, y, s) t)
    (hF : R0c s < F (x, y, s)) : False := by
  have q := of_decide_eq_true hxy
  exact farkas x y s (sk t i) t t (nb t kl) t (nb t kr) t 0 1 1 (R0c s + 1) (sd t i 1) (sd t i 2) (sd t i 3)
    (sd t i 4) ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, of_decide_eq_true hc0⟩
    (pair_of (le_F _ _) h) hL hR (bound_of hF h)

/-- The edges of E by position p: source and target class, cell offset, and the potential changes dl
(entry p * 10 + j). -/
def srcv (p : ℕ) : ℕ := tgetN 11893730683933113775218432623137950171992064 4 p

def tgtv (p : ℕ) : ℕ := tgetN 10307900616941190063983878923336910546011729 4 p

def tgtF (p : ℕ) : Fin 9 := ⟨tgtv p % 9, Nat.mod_lt _ (by norm_num)⟩

def dxv (p : ℕ) : ℤ := tget 11894071054916591876407680188079467376707448 4 8 p

def dyv (p : ℕ) : ℤ := tget 11893730772549665675490438778561995798448248 4 8 p

/-- dlv p j + 8, as a natural number (the rule checks compare naturals). -/
def dlvN (p : ℕ) (j : Fin 10) : ℕ := tgetN 18118771286192688405232669693850208732059570426751425341748595679497902350279074539813316744479113312344614456444280441612684130517741897812035803166357570918585721939197220829658176990861865038811557067293422912882498653819117514891404109210317150387844829784371716628484527497137721282525396046771612250388255950874956685998414401094192158557685447891768428152164047623575310353826571863842510833258006860721751193496131596157819255 4 (p * 10 + j.val)

def dlv (p : ℕ) (j : Fin 10) : ℤ := (dlvN p j : ℤ) - 8

/-- The edge tables agree with the edges of a list l from position p on, every edge moves, and every
potential changes by at most one along every edge. -/
def dlOKl : List (Fin 9 × Fin 9 × ℤ × ℤ) → ℕ → Bool
  | [], _ => true
  | e :: l, p => decide (srcv p = e.1.val ∧ tgtv p = e.2.1.val ∧ dxv p = e.2.2.1 ∧ dyv p = e.2.2.2 ∧
        (e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1)) &&
      ((List.finRange 10).all fun j => decide (dlv p j = dl e j ∧ dl e j ≤ 1 ∧ -dl e j ≤ 1)) && dlOKl l (p + 1)

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
def padOK (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  (real t 0 || decide (c0 = 0)) && (real t 1 || decide (c1 = 0)) && (real t 2 || decide (c2 = 0)) &&
    (real t 3 || decide (c3 = 0))

def closeL (t : Fin 10) (c0 c1 : ℕ) : Bool := (real t 0 && decide (c0 ≤ 1)) || (real t 1 && decide (c1 ≤ 1))

def closeR (t : Fin 10) (c2 c3 : ℕ) : Bool := (real t 2 && decide (c2 ≤ 1)) || (real t 3 && decide (c3 ≤ 1))

def adm (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  padOK t c0 c1 c2 c3 && (!facetB t || !closeL t c0 c1 || !closeR t c2 c3)

/-- Descent rules beyond F = R0c s, one word of 28 bits per class s, potential t and admissible
pattern (c0, c1, c2, c3), at position POFF t + (the rank of the pattern among the admissible patterns
of t): kind 0 names an edge by its position in E; kind 1 is a Farkas certificate: multipliers m1, m2,
m3 of the slot facts of slots k1, k2, k3 (slack ≥ c for a multiplier ≥ 0, slack ≤ c for a negative
multiplier, where c ≤ 1) and l0 ≥ 0 of the bound R0c s + 1 ≤ pot t, whose x and y parts cancel and
whose constants add up to a positive number; kind 2 is a line of slot k1 without lattice points
(modulus l0). Fields from bit 0: kind (2 bits), edge position (6), k1, k2, k3 (2 each), m1, m2, m3
(4 each, stored as value + 8), l0 (2). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 99436459978466434564096920034702290480077880191476123394796258555358576588179280797841669006757233951435572873226897781072376772123187439205276702960694506793535933072222634259780522204151380047378192912907558590530379872009456137207613765543062659763049874794876270367318128904099296581442807505684718652550208308274310574645617898083588682950148937992914826541590770517612861764169252712521095362278553825313607053860201906558217513062952321583967202126067139281762426048159504201285632
  | 1 => 99436504440883077293550905383099026464031885205695388270467796123297708855189406830804960000675316540863147737445342554292794581594106020316856581299911216169403242567618416588743834636726563681496132195477750195862678427500790302244675608282925847951908307215104537686880015602964782681943974645890184027884493822684835827268971107707292348227017804951047584698937595949536816832574198975645513691725037367464763518606742225833016559194354664182840083801051425674015722249525193158557716
  | 2 => 99436548903299720023004890731495762447985890219914653146079914902172903939241505517465207598565740759711897768706944253458165597297293226482167159523799648312424174700588411013871960353888403285103013729132586027549513776373796891346388501566726687938607718213285830916954599542485858104222530458202774373532938592474989954475763120086157107323367847730812775395037219938537045340808352065164973364048697974657690779310954942398279914813845052851427255912375940138862569350604017033675266
  | 3 => 99436604481320523434822372416991682427928396487688734240632200118931858533655395947262703144786760639709656297631847742843595077768691997542794376328658320003389548277764793991228344823050505940116683222633878378192821563891519641137401257851222458585630967536446914714926485556166291958359555709242264100268828504630732136257854970240033590224107793996072917094318788477071077864547831710758674169207196122052311402106858723226344194965131913076858572116371112224651978899357814264823848
  | 4 => 99436615596924684117185868754090866423916897741243550459542657162283649452538174035679705770789031923423047330278382355287534947433730809722603428126193997942609057139729575509032023486042746393404259400305133746474547847882447602978154141874927058497189118108312821502209057439465820420838574290713811185830578160967140587129108423897534515328500895466366546917842411234236003872607840923645534977482610992176336375197874549590301201773530412576898771308112935879050579401765909401043000
  | 5 => 99436682290549648211366846776685970399847905262573444658083725715636821328826091232296738894164426299247631586105491028890535507573464392922859544175366864918523760905732089385806551355547990769778820336846193667774253803666532646363988197636302556453409929659310472271827029930056416541239061567464385723924377324127475693764982279035792335890204948071240156351706251638868095767652985734437676399100055501333997161404449753269034104178823309330895383717750192056960732086594152714862664
  | 6 => 99436459978466434564096920034702290480077880191476123394796258555358576588179280797841669006757233951435572873226897781072376772123187439205276702960694506793535933072222634259780522204151380047378192912907558590530379872009456137207613765543062659762642891490572062363413967899720943357523820773703276465526110559492920167691967324092666476533978916630448735438491757890342357039068601661116667717830770479961620399546313606891649218569746436973892709071110911965489510476509541686181888
  | 7 => 99436459978466434564096920034702290480077880191476123394796258555358576588179280797841669006757233951435572873226897781072376772123187439205276702960694506793535933072222634259780522204151380047378192912907558590530379872009456137207613765543062659762642891490572062363413967899720943357523820773703276465526110559492920167691967324092666476533978916630448735438491757890342357039068601661116667717830770479961620399546313606891649218569746436973892709071110911965489510476509541686181888
  | 8 => 99436815677799576399728802821876178351709920305230242399930883942615885992428179627185753038829915030264085917916005379278452601404429428959166360481836200848560216655095642829498239419903074552580630598387730375545620959719150916111706054301609856866979397797303591837218841164437019123508645733058887070857854166065227002520979345600891812770415927065574599363834742158356731459039988897982233611176745719438976414880480226594157866368800731979555414903657248748191750988803911169736836
  | _ => 0

def rword (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ :=
  tgetN (ruleT s.val) 28 (Nat.add (tgetN 895264317694058816 6 t.val) (tgetN 650557212750267116677091687183996953177527761286267287404137087967152798875770576621929837119060310966947670039330481740408643608896329646099023059343514241876135629082383129380153670932726265706239833193469055377629906773730583161709112404348927079164090897302906847586658703642441020477439982314521674776503024202345665426839065215173213438954699893384480738351909065094658668910116362965504228952312772270248636897012170605620934968661073413731734706668908281614981184676672373668641447593136125878540327852923920394029953334139071164187257512950429462237242825785565012212063642048011281277159321116564837687430027881159097643297963654589406059910296219140155455656512207602422092373780767814964564027388177864468517620095219091890719485985338100459855170600573308063471919486683356875791485134414313934136573524494931260021586225531466695065822275539170012627530092281258405343496917280926929518592 4
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul t.val 81) c0) (Nat.mul 3 c1)) (Nat.mul 9 c2)) (Nat.mul 27 c3))))

/-- The field of B bits from bit o of the word w. -/
def fld (w o B : ℕ) : ℕ := Nat.mod (Nat.shiftRight w o) (Nat.pow 2 B)

def rk (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 0 2

def re (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 2 6

def rsl (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (i : ℕ) : Fin 4 :=
  ⟨fld (rword s t c0 c1 c2 c3) (Nat.add 8 (Nat.mul 2 i)) 2 % 4, Nat.mod_lt _ (by norm_num)⟩

def rm (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (i : ℕ) : ℤ := Int.subNatNat (fld (rword s t c0 c1 c2 c3) (Nat.add 14 (Nat.mul 4 i)) 4) 8

def rl0 (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℤ := Int.ofNat (fld (rword s t c0 c1 c2 c3) 26 2)

/-- The class of slot k in the pattern (c0, c1, c2, c3). -/
def cv (c0 c1 c2 c3 : ℕ) (k : Fin 4) : ℕ := if k.val = 0 then c0 else if k.val = 1 then c1 else if k.val = 2 then c2 else c3

/-- The slack of the slot k below t in x and y, and its constant: pot t - pot (nb t k) at (x, y, s)
is dA t k * x + dB t k * y + dC s t k. -/
def dA (t : Fin 10) (k : Fin 4) : ℤ := Ac t - Ac (nb t k)

def dB (t : Fin 10) (k : Fin 4) : ℤ := Bc t - Bc (nb t k)

def dC (s : Fin 9) (t : Fin 10) (k : Fin 4) : ℤ := Cc s t - Cc s (nb t k)

/-- Kind 0: the edge at position re descends from class s for this pattern. -/
def ok0 (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  Nat.blt (re s t c0 c1 c2 c3) 36 && Nat.beq (srcv (re s t c0 c1 c2 c3)) s.val && Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) t) 1) 8 &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 0)) 1) (Nat.add c0 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 1)) 1) (Nat.add c1 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 2)) 1) (Nat.add c2 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 3)) 1) (Nat.add c3 8)

/-- Kind 1: the Farkas certificate over the slot facts and the bound is valid. -/
def ok1 (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
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
def ok2 (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  decide (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) ≤ 1 ∧ rl0 s t c0 c1 c2 c3 ∣ dA t (rsl s t c0 c1 c2 c3 0) ∧ rl0 s t c0 c1 c2 c3 ∣ dB t (rsl s t c0 c1 c2 c3 0) ∧
    ¬ rl0 s t c0 c1 c2 c3 ∣ (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 0))

def ruleOK (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  if rk s t c0 c1 c2 c3 = 0 then ok0 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 1 then ok1 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 2 then ok2 s t c0 c1 c2 c3 else false

/-- Every pattern of slack classes that can occur at the maximal potential t has a valid rule. -/
def rulesOK (t : Fin 10) : Bool :=
  (List.range 3).all fun c0 => (List.range 3).all fun c1 => (List.range 3).all fun c2 => (List.range 3).all fun c3 =>
    !adm t c0 c1 c2 c3 || (List.finRange 9).all fun s => !repB s t || ruleOK s t c0 c1 c2 c3

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

def farsOK8_dec : PLift (farsOK 8 = true) := ⟨by
  decide +kernel⟩

def farsOK9_dec : PLift (farsOK 9 = true) := ⟨by
  decide +kernel⟩

theorem farsOK_all (k : Fin 10) : farsOK k = true := by
  fin_cases k
  exacts [farsOK0_dec.down, farsOK1_dec.down, farsOK2_dec.down, farsOK3_dec.down, farsOK4_dec.down, farsOK5_dec.down, farsOK6_dec.down, farsOK7_dec.down, farsOK8_dec.down, farsOK9_dec.down]

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

def rulesOK8_dec : PLift (rulesOK 8 = true) := ⟨by
  decide +kernel⟩

def rulesOK9_dec : PLift (rulesOK 9 = true) := ⟨by
  decide +kernel⟩

theorem rulesOK_all (k : Fin 10) : rulesOK k = true := by
  fin_cases k
  exacts [rulesOK0_dec.down, rulesOK1_dec.down, rulesOK2_dec.down, rulesOK3_dec.down, rulesOK4_dec.down, rulesOK5_dec.down, rulesOK6_dec.down, rulesOK7_dec.down, rulesOK8_dec.down, rulesOK9_dec.down]

theorem far_ok (s : Fin 9) (t j : Fin 10) (hrep : repB s t = true) (hjt : j ≠ t) (hjn : ∀ k, j ≠ nb t k) :
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

theorem side_ok (s : Fin 9) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) (hrep : repB s t = true) (hsp : facetB t = true)
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

theorem rule_ok (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (hrep : repB s t = true) (h0 : c0 < 3) (h1 : c1 < 3) (h2 : c2 < 3) (h3 : c3 < 3)
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

theorem dlOKl_spec : ∀ (l : List (Fin 9 × Fin 9 × ℤ × ℤ)) (p : ℕ), dlOKl l p = true →
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

theorem E_len : E.length = 36 := by
  decide +kernel

/-- The edge at position p of E, read from the tables. -/
theorem edge_of (p : ℕ) (hp : p < 36) : ∃ e ∈ E, e.1.val = srcv p ∧ e.2.1.val = tgtv p ∧
    e.2.2.1 = dxv p ∧ e.2.2.2 = dyv p ∧ ∀ j, dlv p j = dl e j := by
  have hp' : p < E.length := E_len ▸ hp
  obtain ⟨⟨h1, h2, h3, h4, -⟩, h5⟩ := dlOKl_spec E 0 tables_ok.2 p hp'
  simp only [Nat.zero_add] at h1 h2 h3 h4 h5
  exact ⟨E[p], List.getElem_mem hp', h1.symm, h2.symm, h3.symm, h4.symm, fun j => (h5 j).1⟩

theorem E_step : ∀ e ∈ E, ∀ j : Fin 10, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  intro e he j
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact ((dlOKl_spec E 0 tables_ok.2 i hi).2 j).2

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact (dlOKl_spec E 0 tables_ok.2 i hi).1.2.2.2.2

theorem adj_of_mem (e : Fin 9 × Fin 9 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
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
theorem farkas_slot (x y : ℤ) (s : Fin 9) (t : Fin 10) (k1 k2 k3 : Fin 4) (c1 c2 c3 m1 m2 m3 l0 : ℤ)
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
theorem far_step (s : Fin 9) (t : Fin 10) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) t)
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

theorem far_step' (v : V) (t : Fin 10) (h : F v = pot v t) (hF : R0c v.2.2 < F v) (hrep : repB v.2.2 t = true) :
    ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  exact far_step s t x y h hF hrep

/-- The symmetry maps the edge table onto itself, is an involution, permutes the potentials with F
invariant, keeps R0c, fixes v0, and every pair and class has its checked representative. -/
def sym_ok_dec : PLift ((∀ e ∈ E, (piS e.1, piS e.2.1, 1 * e.2.2.1 + 0 * e.2.2.2 + tauX e.2.1 - tauX e.1,
      0 * e.2.2.1 + (-1) * e.2.2.2 + tauY e.2.1 - tauY e.1) ∈ E) ∧
    (∀ s, piS (piS s) = s ∧ 1 * tauX s + 0 * tauY s + tauX (piS s) = 0 ∧
      0 * tauX s + (-1) * tauY s + tauY (piS s) = 0 ∧ R0c (piS s) = R0c s ∧
      (repC s = true ∨ repC (piS s) = true)) ∧
    (∀ t, rhoP (rhoP t) = t ∧ Ac (rhoP t) * 1 + Bc (rhoP t) * 0 = Ac t ∧
      Ac (rhoP t) * 0 + Bc (rhoP t) * (-1) = Bc t) ∧
    (∀ s t, Ac (rhoP t) * tauX s + Bc (rhoP t) * tauY s + Cc (piS s) (rhoP t) = Cc s t ∧
      (repB s t = true ∨ repB (piS s) (rhoP t) = true)) ∧
    sig v0 = v0) := ⟨by
  decide +kernel⟩

theorem sym_ok : (∀ e ∈ E, (piS e.1, piS e.2.1, 1 * e.2.2.1 + 0 * e.2.2.2 + tauX e.2.1 - tauX e.1,
      0 * e.2.2.1 + (-1) * e.2.2.2 + tauY e.2.1 - tauY e.1) ∈ E) ∧
    (∀ s, piS (piS s) = s ∧ 1 * tauX s + 0 * tauY s + tauX (piS s) = 0 ∧
      0 * tauX s + (-1) * tauY s + tauY (piS s) = 0 ∧ R0c (piS s) = R0c s ∧
      (repC s = true ∨ repC (piS s) = true)) ∧
    (∀ t, rhoP (rhoP t) = t ∧ Ac (rhoP t) * 1 + Bc (rhoP t) * 0 = Ac t ∧
      Ac (rhoP t) * 0 + Bc (rhoP t) * (-1) = Bc t) ∧
    (∀ s t, Ac (rhoP t) * tauX s + Bc (rhoP t) * tauY s + Cc (piS s) (rhoP t) = Cc s t ∧
      (repB s t = true ∨ repB (piS s) (rhoP t) = true)) ∧
    sig v0 = v0 := sym_ok_dec.down

theorem sig_sig (v : V) : sig (sig v) = v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨h1, h2, h3, -, -⟩ := sym_ok.2.1 s
  simp only [sig, Prod.mk.injEq]
  exact ⟨by linear_combination h2, by linear_combination h3, h1⟩

theorem sig_inj {u w : V} (h : sig u = sig w) : u = w := by
  rw [← sig_sig u, ← sig_sig w, h]

theorem sig_adj (u w : V) (h : G.Adj u w) : G.Adj (sig u) (sig w) := by
  rw [G, SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨hne, h | h⟩ := h
  · refine ⟨fun e => hne (sig_inj e), Or.inl ?_⟩
    obtain ⟨e, he, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, s⟩ := u
    obtain ⟨x', y', s'⟩ := w
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact ⟨_, sym_ok.1 e he, rfl, rfl, by simp only [sig]; ring, by simp only [sig]; ring⟩
  · refine ⟨fun e => hne (sig_inj e), Or.inr ?_⟩
    obtain ⟨e, he, h1, h2, h3, h4⟩ := h
    obtain ⟨x, y, s⟩ := w
    obtain ⟨x', y', s'⟩ := u
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact ⟨_, sym_ok.1 e he, rfl, rfl, by simp only [sig]; ring, by simp only [sig]; ring⟩

theorem sig_pot (v : V) (t : Fin 10) : pot (sig v) (rhoP t) = pot v t := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨-, ha, hb⟩ := sym_ok.2.2.1 t
  obtain ⟨hc, -⟩ := sym_ok.2.2.2.1 s t
  simp only [pot, sig]
  linear_combination x * ha + y * hb + hc

theorem sig_F (v : V) : F (sig v) = F v := by
  apply le_antisymm
  · apply F_le_all
    intro t
    have h := sig_pot v (rhoP t)
    rw [(sym_ok.2.2.1 t).1] at h
    rw [h]
    exact le_F v (rhoP t)
  · apply F_le_all
    intro t
    rw [← sig_pot v t]
    exact le_F (sig v) (rhoP t)

theorem far_desc (v : V) (hF : R0c v.2.2 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨t, ht⟩ := exists_F (x, y, s)
  rcases (sym_ok.2.2.2.1 s t).2 with hr | hr
  · exact far_step s t x y ht hF hr
  · obtain ⟨w, hw, he⟩ := far_step' (sig (x, y, s)) (rhoP t) (by rw [sig_F, sig_pot]; exact ht)
      (by rw [sig_F]; show R0c (piS s) < F (x, y, s); rw [(sym_ok.2.1 s).2.2.2.1]; exact hF) hr
    refine ⟨sig w, ?_, ?_⟩
    · have := sig_adj _ _ hw
      rwa [sig_sig] at this
    · rw [sig_F]
      rw [sig_F] at he
      exact he

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 9) (a1 a2 a3 : Fin 10) (t l1 l2 l3 px py q lq : ℤ)
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
def BXn (s : Fin 9) : ℕ := tgetN 261886 2 s.val

def BYn (s : Fin 9) : ℕ := tgetN 175802 2 s.val

theorem nb_c0 : ∀ s : Fin 9, 0 < 1 * (Cc s 9 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 3 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c0 : ∀ s : Fin 9, 0 < 1 * (Cc s 9 - (7)) + 0 * (Cc s 0 - (7)) + 0 * (Cc s 0 - (7)) + 3 * (3) := by
  decide +kernel

theorem nb_c1 : ∀ s : Fin 9, 0 < 1 * (Cc s 4 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 3 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c1 : ∀ s : Fin 9, 0 < 1 * (Cc s 4 - (7)) + 0 * (Cc s 0 - (7)) + 0 * (Cc s 0 - (7)) + 3 * (3) := by
  decide +kernel

theorem nb_c2 : ∀ s : Fin 9, 0 < 1 * (Cc s 1 - (R0c s)) + 1 * (Cc s 2 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 8 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c2 : ∀ s : Fin 9, 0 < 3 * (Cc s 2 - (7)) + 1 * (Cc s 9 - (7)) + 0 * (Cc s 0 - (7)) + 12 * (3) := by
  decide +kernel

theorem nb_c3 : ∀ s : Fin 9, 0 < 3 * (Cc s 6 - (R0c s)) + 1 * (Cc s 8 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 14 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c3 : ∀ s : Fin 9, 0 < 3 * (Cc s 6 - (7)) + 1 * (Cc s 9 - (7)) + 0 * (Cc s 0 - (7)) + 12 * (3) := by
  decide +kernel

theorem nn_c : ∀ s : Fin 9, 0 < 3 * (Cc s 4 - (-1)) + 3 * (Cc s 9 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * (0) := by
  decide +kernel

/-- Every vertex of class s with F at most R0c s lies in the near box of class s. -/
theorem near_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ R0c s) :
    -(BXn s : ℤ) ≤ x ∧ x ≤ BXn s ∧ -(BYn s : ℤ) ≤ y ∧ y ≤ BYn s := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 9 0 0 (R0c s) 1 0 0 (1) (0) ((BXn s : ℤ) + 1) 3 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 0 0 (R0c s) 1 0 0 (-1) (0) ((BXn s : ℤ) + 1) 3 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 1 2 0 (R0c s) 1 1 0 (0) (1) ((BYn s : ℤ) + 1) 8 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 6 8 0 (R0c s) 3 1 0 (0) (-1) ((BYn s : ℤ) + 1) 14 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c3 s⟩ (u _) (u _) (u _) (by omega)

/-- Every vertex with F at most 7 lies in the cells |x| ≤ 2, |y| ≤ 2. -/
theorem small_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ 7) :
    -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 9 0 0 (7) 1 0 0 (1) (0) (3) 3 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 0 0 (7) 1 0 0 (-1) (0) (3) 3 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 9 0 (7) 3 1 0 (0) (1) (3) 12 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 6 9 0 (7) 3 1 0 (0) (-1) (3) 12 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 4 9 0 (-1) 3 3 0 (0) (0) (0) 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nn_c s⟩ (u _) (u _) (u _) (by norm_num)

/-- The vertices near v0 where the graph distance is not the largest potential, with the distance. -/
def O : List (V × ℤ) :=
  [((0, 0, 0), 0),
    (((-1), (-1), 5), 1),
    (((-1), 0, 6), 1),
    ((0, 0, 1), 1),
    (((-1), (-1), 2), 2),
    (((-1), 0, 7), 2),
    ((0, (-1), 2), 2),
    ((0, 0, 7), 2),
    (((-1), 0, 1), 3),
    ((0, (-1), 5), 3),
    ((0, 0, 6), 3),
    (((-1), 0, 0), 4),
    ((1, 0, 0), 4),
    ((1, 0, 1), 5)]

/-- The cells (x, y) of the vertices of O. -/
def obox (x y : ℤ) : Bool := decide ((-1) ≤ x ∧ x ≤ 1 ∧ (-1) ≤ y ∧ y ≤ 0)

/-- The distance formula: the value listed in O, and the largest potential off O. -/
def fv (v : V) : ℤ :=
  if obox v.1 v.2.1 then ((O.find? fun o => decide (o.1 = v)).map Prod.snd).getD (F v) else F v

theorem fv_out (x y : ℤ) (s : Fin 9) (h : ¬ obox x y = true) : fv (x, y, s) = F (x, y, s) := by
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

/-- The vertex o of O has F and fv below 7 and fv nonnegative, and fv changes by at most one
along the edges at o. -/
def OokB (o : V × ℤ) : Bool :=
  decide (F o.1 < 7 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 7) && E.all fun e =>
    (!decide (e.1 = o.1.2.2) || decide (fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) + 1)) &&
    (!decide (e.2.1 = o.1.2.2) || decide (fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) + 1))

/-- The check of entry k of O, one definition per entry. -/
def Ook (k : ℕ) : Bool := OokB (O.getD k ((0, 0, 0), 0))

def Ook0_dec : PLift (Ook 0 = true) := ⟨by
  decide +kernel⟩

def Ook1_dec : PLift (Ook 1 = true) := ⟨by
  decide +kernel⟩

def Ook2_dec : PLift (Ook 2 = true) := ⟨by
  decide +kernel⟩

def Ook3_dec : PLift (Ook 3 = true) := ⟨by
  decide +kernel⟩

def Ook4_dec : PLift (Ook 4 = true) := ⟨by
  decide +kernel⟩

def Ook5_dec : PLift (Ook 5 = true) := ⟨by
  decide +kernel⟩

def Ook6_dec : PLift (Ook 6 = true) := ⟨by
  decide +kernel⟩

def Ook7_dec : PLift (Ook 7 = true) := ⟨by
  decide +kernel⟩

def Ook8_dec : PLift (Ook 8 = true) := ⟨by
  decide +kernel⟩

def Ook9_dec : PLift (Ook 9 = true) := ⟨by
  decide +kernel⟩

def Ook10_dec : PLift (Ook 10 = true) := ⟨by
  decide +kernel⟩

def Ook11_dec : PLift (Ook 11 = true) := ⟨by
  decide +kernel⟩

def Ook12_dec : PLift (Ook 12 = true) := ⟨by
  decide +kernel⟩

def Ook13_dec : PLift (Ook 13 = true) := ⟨by
  decide +kernel⟩

theorem Ook_all (k : Fin 14) : Ook k = true := by
  fin_cases k
  exacts [Ook0_dec.down, Ook1_dec.down, Ook2_dec.down, Ook3_dec.down, Ook4_dec.down, Ook5_dec.down, Ook6_dec.down, Ook7_dec.down, Ook8_dec.down, Ook9_dec.down, Ook10_dec.down, Ook11_dec.down, Ook12_dec.down, Ook13_dec.down]

theorem O_len : O.length = 14 := by
  decide +kernel

/-- The vertices of O have F and fv below 7 and fv nonnegative, and fv changes by at most one
along the edges at the vertices of O. -/
theorem O_ok : ∀ o ∈ O, F o.1 < 7 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 7 ∧ ∀ e ∈ E,
    (e.1 = o.1.2.2 → fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) + 1) ∧
    (e.2.1 = o.1.2.2 → fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) + 1) := by
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  have h := Ook_all ⟨i, O_len ▸ hi⟩
  change Ook i = true at h
  unfold Ook OokB at h
  rw [List.getD_eq_getElem _ _ hi] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    List.all_eq_true] at h
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun e he => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · exact (h4 e he).1.resolve_left (not_not.2 hc)
  · exact (h4 e he).2.resolve_left (not_not.2 hc)

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

def R0c_ge_dec : PLift (∀ s, 7 ≤ R0c s) := ⟨by
  decide +kernel⟩

theorem R0c_ge : ∀ s, 7 ≤ R0c s := R0c_ge_dec.down

/-- The near check computes the potentials as differences of natural numbers: at the cell (a, b) of
the near box of class s, pot = potP - potQ. -/
def apN (i : Fin 10) : ℕ := tgetN 374336 3 i.val

def amN (i : Fin 10) : ℕ := tgetN 455081995 3 i.val

def bpN (i : Fin 10) : ℕ := tgetN 43057152 3 i.val

def bmN (i : Fin 10) : ℕ := tgetN 1314 3 i.val

def kpN (s : Fin 9) (i : Fin 10) : ℕ := tgetN 1210967271726009561378541448564345398640970501636893329947405433057664431371610797515374451791238989441140394 4 (Nat.add (Nat.mul s.val 10) i.val)

def kmN (s : Fin 9) (i : Fin 10) : ℕ := tgetN 2603458290703445639780717831438168895134471519195703425842474662420869043969405255060500284821910084395008 4 (Nat.add (Nat.mul s.val 10) i.val)

def pqOK : Bool :=
  (List.finRange 10).all fun i => decide ((apN i : ℤ) - amN i = Ac i ∧ (bpN i : ℤ) - bmN i = Bc i) &&
    (List.finRange 9).all fun s => decide ((kpN s i : ℤ) - kmN s i = Cc s i - Ac i * BXn s - Bc i * BYn s)

def pq_ok_dec : PLift (pqOK = true) := ⟨by
  decide +kernel⟩

theorem pq_ok : pqOK = true := pq_ok_dec.down

def potP (s : Fin 9) (a b : ℕ) (i : Fin 10) : ℕ :=
  Nat.add (Nat.add (Nat.mul (apN i) a) (Nat.mul (bpN i) b)) (kpN s i)

def potQ (s : Fin 9) (a b : ℕ) (i : Fin 10) : ℕ :=
  Nat.add (Nat.add (Nat.mul (amN i) a) (Nat.mul (bmN i) b)) (kmN s i)

theorem potPQ_val (s : Fin 9) (a b : ℕ) (i : Fin 10) :
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
def FP (s : Fin 9) (a b : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax ((potP s a b 0, potQ s a b 0)) (potP s a b 1, potQ s a b 1)) (potP s a b 2, potQ s a b 2)) (potP s a b 3, potQ s a b 3)) (potP s a b 4, potQ s a b 4)) (potP s a b 5, potQ s a b 5)) (potP s a b 6, potQ s a b 6)) (potP s a b 7, potQ s a b 7)) (potP s a b 8, potQ s a b 8)) (potP s a b 9, potQ s a b 9)

def FPn (s : Fin 9) (a b p : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax ((Nat.add (potP s a b 0) (dlvN p 0), Nat.add (potQ s a b 0) 8)) (Nat.add (potP s a b 1) (dlvN p 1), Nat.add (potQ s a b 1) 8)) (Nat.add (potP s a b 2) (dlvN p 2), Nat.add (potQ s a b 2) 8)) (Nat.add (potP s a b 3) (dlvN p 3), Nat.add (potQ s a b 3) 8)) (Nat.add (potP s a b 4) (dlvN p 4), Nat.add (potQ s a b 4) 8)) (Nat.add (potP s a b 5) (dlvN p 5), Nat.add (potQ s a b 5) 8)) (Nat.add (potP s a b 6) (dlvN p 6), Nat.add (potQ s a b 6) 8)) (Nat.add (potP s a b 7) (dlvN p 7), Nat.add (potQ s a b 7) 8)) (Nat.add (potP s a b 8) (dlvN p 8), Nat.add (potQ s a b 8) 8)) (Nat.add (potP s a b 9) (dlvN p 9), Nat.add (potQ s a b 9) 8)

theorem FP_val (s : Fin 9) (a b : ℕ) :
    ((FP s a b).1 : ℤ) - (FP s a b).2 = F ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) := by
  simp only [FP, F, pmax_val, potPQ_val]

theorem FPn_val (s : Fin 9) (a b p : ℕ) (hp : p < 36) (hs : srcv p = s.val) :
    ((FPn s a b p).1 : ℤ) - (FPn s a b p).2 = F ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  obtain ⟨e, -, h1, h2, h3, h4, h5⟩ := edge_of p hp
  have hs' : e.1 = s := Fin.ext (h1.trans hs)
  have ht' : e.2.1 = tgtF p := Fin.ext (by
    show e.2.1.val = tgtv p % 9
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
def fvN (s : Fin 9) (a b : ℕ) : ℤ :=
  if obox ((a : ℤ) - BXn s) ((b : ℤ) - BYn s) then fv ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s)
  else Int.subNatNat (FP s a b).1 (FP s a b).2

def fvNn (s : Fin 9) (a b p : ℕ) : ℤ :=
  if obox ((a : ℤ) - BXn s + dxv p) ((b : ℤ) - BYn s + dyv p) then
    fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p)
  else Int.subNatNat (FPn s a b p).1 (FPn s a b p).2

theorem fvN_eq (s : Fin 9) (a b : ℕ) : fvN s a b = fv ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) := by
  unfold fvN
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FP_val, Int.subNatNat_eq_coe]

theorem fvNn_eq (s : Fin 9) (a b p : ℕ) (hp : p < 36) (hs : srcv p = s.val) :
    fvNn s a b p = fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  unfold fvNn
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FPn_val s a b p hp hs, Int.subNatNat_eq_coe]

/-- For each class s and each cell of its near box with F at most R0c s, other than v0, the position
in E of an edge along which fv decreases. -/
def nearT (s : ℕ) : ℕ :=
  match s with
  | 0 => 354063823880174013282592985512942839529472
  | 1 => 1140245376639279663636984097135988532166565915803968
  | 2 => 3066693933433020885438099950176535979072130955665932393482217095987200
  | 3 => 65310858312004074148038999278734569212694721778496
  | 4 => 5669209247189135303053903161219954662499214
  | 5 => 133712223395732383329417309021113331623190417613371835761792
  | 6 => 0
  | 7 => 0
  | 8 => 184057874818537747097523289527381708938854732531712
  | _ => 0

def nearE (s : Fin 9) (a b : ℕ) : ℕ := tgetN (nearT s.val) 6 (a * (2 * BYn s + 1) + b)

/-- The near check of class s. -/
def nearOK (s : Fin 9) : Bool :=
  !repC s || (List.range (2 * BXn s + 1)).all fun a => (List.range (2 * BYn s + 1)).all fun b =>
    Nat.blt (Nat.add (R0N s) (FP s a b).2) (FP s a b).1 ||
      (Nat.beq a (BXn s) && Nat.beq b (BYn s) && Nat.beq s.val 0) ||
      (Nat.blt (nearE s a b) 36 && Nat.beq (srcv (nearE s a b)) s.val &&
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

theorem nearOK_all (k : Fin 9) : nearOK k = true := by
  fin_cases k
  exacts [nearOK0_dec.down, nearOK1_dec.down, nearOK2_dec.down, nearOK3_dec.down, nearOK4_dec.down, nearOK5_dec.down, nearOK6_dec.down, nearOK7_dec.down, nearOK8_dec.down]

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
    have hs0 : s = 0 := Fin.ext h4
    rw [hx0, hy0, hs0]
    rfl
  · rw [fvNn_eq _ _ _ _ hlt hs, fvN_eq, ex, ey] at hfe
    obtain ⟨e, hmem, h1, h2, h3, h4, -⟩ := edge_of _ hlt
    have ha := adj_of_mem e hmem x y
    have hs' : e.1 = s := Fin.ext (h1.trans hs)
    have ht' : e.2.1 = tgtF (nearE s (x + BXn s).toNat (y + BYn s).toNat) := Fin.ext (by
      show e.2.1.val = tgtv (nearE s (x + BXn s).toNat (y + BYn s).toNat) % 9
      rw [← h2, Nat.mod_eq_of_lt e.2.1.isLt])
    rw [hs', ht', h3, h4] at ha
    exact ⟨_, ha, hfe⟩

/-- The image of entry k of O under sig is in O, with the same fv; one definition per entry. -/
def symOk (k : ℕ) : Bool :=
  O.any (fun o' => decide (o'.1 = sig (O.getD k ((0, 0, 0), 0)).1)) &&
    decide (fv (sig (O.getD k ((0, 0, 0), 0)).1) = fv (O.getD k ((0, 0, 0), 0)).1)

def symOk0_dec : PLift (symOk 0 = true) := ⟨by
  decide +kernel⟩

def symOk1_dec : PLift (symOk 1 = true) := ⟨by
  decide +kernel⟩

def symOk2_dec : PLift (symOk 2 = true) := ⟨by
  decide +kernel⟩

def symOk3_dec : PLift (symOk 3 = true) := ⟨by
  decide +kernel⟩

def symOk4_dec : PLift (symOk 4 = true) := ⟨by
  decide +kernel⟩

def symOk5_dec : PLift (symOk 5 = true) := ⟨by
  decide +kernel⟩

def symOk6_dec : PLift (symOk 6 = true) := ⟨by
  decide +kernel⟩

def symOk7_dec : PLift (symOk 7 = true) := ⟨by
  decide +kernel⟩

def symOk8_dec : PLift (symOk 8 = true) := ⟨by
  decide +kernel⟩

def symOk9_dec : PLift (symOk 9 = true) := ⟨by
  decide +kernel⟩

def symOk10_dec : PLift (symOk 10 = true) := ⟨by
  decide +kernel⟩

def symOk11_dec : PLift (symOk 11 = true) := ⟨by
  decide +kernel⟩

def symOk12_dec : PLift (symOk 12 = true) := ⟨by
  decide +kernel⟩

def symOk13_dec : PLift (symOk 13 = true) := ⟨by
  decide +kernel⟩

theorem symOk_all (k : Fin 14) : symOk k = true := by
  fin_cases k
  exacts [symOk0_dec.down, symOk1_dec.down, symOk2_dec.down, symOk3_dec.down, symOk4_dec.down, symOk5_dec.down, symOk6_dec.down, symOk7_dec.down, symOk8_dec.down, symOk9_dec.down, symOk10_dec.down, symOk11_dec.down, symOk12_dec.down, symOk13_dec.down]

theorem sym_O : ∀ o ∈ O, (∃ o' ∈ O, o'.1 = sig o.1) ∧ fv (sig o.1) = fv o.1 := by
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  have h := symOk_all ⟨i, O_len ▸ hi⟩
  change symOk i = true at h
  unfold symOk at h
  rw [List.getD_eq_getElem _ _ hi] at h
  simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  exact h

theorem sig_fv (v : V) : fv (sig v) = fv v := by
  by_cases hv : ∃ o ∈ O, o.1 = v
  · obtain ⟨o, ho, rfl⟩ := hv
    exact (sym_O o ho).2
  push Not at hv
  have hs : ∀ o ∈ O, o.1 ≠ sig v := by
    intro o ho he
    obtain ⟨o', ho', he'⟩ := (sym_O o ho).1
    apply hv o' ho'
    rw [he', he, sig_sig]
  rw [fv_of _ hs, fv_of _ hv, sig_F]

theorem near_desc (v : V) (hF : F v ≤ R0c v.2.2) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ fv w + 1 = fv v := by
  rcases (sym_ok.2.1 v.2.2).2.2.2.2 with hr | hr
  · exact near_desc_rep v hF hv hr
  · have hu : F (sig v) ≤ R0c (sig v).2.2 := by
      rw [sig_F]
      show F v ≤ R0c (piS v.2.2)
      rw [(sym_ok.2.1 v.2.2).2.2.2.1]
      exact hF
    have huv : sig v ≠ v0 := fun h => hv (by rw [← sig_sig v, h, sym_ok.2.2.2.2])
    obtain ⟨w, hw, he⟩ := near_desc_rep (sig v) hu huv hr
    refine ⟨sig w, ?_, ?_⟩
    · have := sig_adj _ _ hw
      rwa [sig_sig] at this
    · rw [sig_fv]
      rw [sig_fv] at he
      exact he

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

/-- From n = 7 on, the coordination sequence counts the level set F = n. -/
theorem a_eq_F (n : ℕ) (hn : 7 ≤ n) : a n = Set.ncard {v : V | (F v).toNat = n} := by
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

/-- The cells |x| ≤ 2, |y| ≤ 2 of class s. -/
def boxS (s : Fin 9) : Finset V :=
  (Finset.range 5 ×ˢ Finset.range 5).map
    ⟨fun p => ((p.1 : ℤ) - 2, (p.2 : ℤ) - 2, s), fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)⟩

theorem boxS_cls (s : Fin 9) (v : V) (h : v ∈ boxS s) : v.2.2 = s := by
  rw [boxS, Finset.mem_map] at h
  obtain ⟨p, -, rfl⟩ := h
  rfl

theorem mem_boxS (v : V) (h : (fv v).toNat ≤ 7) : v ∈ boxS v.2.2 := by
  obtain ⟨x, y, s⟩ := v
  have hb : F (x, y, s) ≤ 7 := by
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
  rw [boxS, Finset.mem_map]
  refine ⟨((x + 2).toNat, (y + 2).toNat), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range]
    omega
  · show ((((x + 2).toNat : ℕ) : ℤ) - 2, (((y + 2).toNat : ℕ) : ℤ) - 2, s) = (x, y, s)
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨by omega, by omega, rfl⟩

/-- Up to n = 7, a n counts the cells of the boxes where fv = n. -/
theorem a_small (n : ℕ) (hn : n ≤ 7) : a n = ∑ s : Fin 9, ((boxS s).filter fun v => (fv v).toNat = n).card := by
  have hd : ((Finset.univ : Finset (Fin 9)) : Set (Fin 9)).PairwiseDisjoint
      fun s => (boxS s).filter fun v => (fv v).toNat = n := by
    intro s _ t _ hst
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact hst ((boxS_cls s v (Finset.mem_filter.1 hv).1).symm.trans (boxS_cls t v (Finset.mem_filter.1 hv').1))
  rw [← Finset.card_biUnion hd]
  unfold a
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_biUnion, dist_eq v]
  constructor
  · intro h
    exact ⟨v.2.2, Finset.mem_univ _, Finset.mem_filter.2 ⟨mem_boxS v (by omega), h⟩⟩
  · rintro ⟨s, -, hs⟩
    exact (Finset.mem_filter.1 hs).2

/-- The number of vertices of class s at distance n, for n < 7. -/
def smallT (s : Fin 9) (n : ℕ) : ℕ := tgetN 417270042017642857602194773123571369007216292371009519617 3 (Nat.add (Nat.mul s.val 7) n)

/-- The kernel's count of the cells of the box of class s by fv. -/
def smallOK (s : Fin 9) : Bool :=
  (List.range 7).all fun n => decide (((boxS s).filter fun v => (fv v).toNat = n).card = smallT s n)

def smallOK0_dec : PLift (smallOK 0 = true) := ⟨by
  decide +kernel⟩

def smallOK1_dec : PLift (smallOK 1 = true) := ⟨by
  decide +kernel⟩

def smallOK2_dec : PLift (smallOK 2 = true) := ⟨by
  decide +kernel⟩

def smallOK3_dec : PLift (smallOK 3 = true) := ⟨by
  decide +kernel⟩

def smallOK4_dec : PLift (smallOK 4 = true) := ⟨by
  decide +kernel⟩

def smallOK5_dec : PLift (smallOK 5 = true) := ⟨by
  decide +kernel⟩

def smallOK6_dec : PLift (smallOK 6 = true) := ⟨by
  decide +kernel⟩

def smallOK7_dec : PLift (smallOK 7 = true) := ⟨by
  decide +kernel⟩

def smallOK8_dec : PLift (smallOK 8 = true) := ⟨by
  decide +kernel⟩

theorem smallOK_all (k : Fin 9) : smallOK k = true := by
  fin_cases k
  exacts [smallOK0_dec.down, smallOK1_dec.down, smallOK2_dec.down, smallOK3_dec.down, smallOK4_dec.down, smallOK5_dec.down, smallOK6_dec.down, smallOK7_dec.down, smallOK8_dec.down]

/-- The coordination sequence below n = 7. -/
theorem small_vals : (List.range 7).map a = [1, 3, 8, 13, 14, 19, 26] := by
  have hc : ∀ n ∈ List.range 7, a n = ∑ s : Fin 9, smallT s n := by
    intro n hn
    rw [List.mem_range] at hn
    rw [a_small n (by omega)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have h := smallOK_all s
    unfold smallOK at h
    rw [List.all_eq_true] at h
    exact of_decide_eq_true (h n (List.mem_range.2 hn))
  rw [List.map_congr_left hc]
  decide +kernel


/-! ## Counting the spheres

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. The
gradient of facet i is gc i times the primitive vector (Ap i, Bp i), so the points of class s with
pot_i = n lie on the line Ap i x + Bp i y = c with c = lev s i n, and only when gc i divides
n - Cc s i. That line is par s i c u = (al i c + Bp i u, be i c - Ap i u), and potential j is
ka i j c + Dm i j u + Cc s j there (`pot_par`). The previous facet bounds u from above, the next one
from below, and for n ≥ 7 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 60 moves every quotient by an integer (`inner_shift`,
`S_shift`). The kernel checks run over natural numbers in loops by the recursor of ℕ (`allR`,
`sumR`, `maxR`), on tables packed into natural numbers (`ctabN`). The section lives in the namespace
`Count`; `gf`, `recur`, `controls`, `a_step` and `a_closed` are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T. -/
def ctabN (T B k : ℕ) : ℕ := Nat.mod (Nat.shiftRight T (Nat.mul B k)) (Nat.pow 2 B)

/-- f 0 && ... && f (n - 1), by the recursor of ℕ: the kernel's cheapest loop. -/
noncomputable def allR (n : ℕ) (f : ℕ → Bool) : Bool := Nat.rec true (fun k acc => f k && acc) n

theorem allR_iff (n : ℕ) (f : ℕ → Bool) : allR n f = true ↔ ∀ k, k < n → f k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ n ih =>
    show (f n && allR n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h2 k h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

/-- f 0 + ... + f (n - 1), by the recursor of ℕ. -/
noncomputable def sumR (n : ℕ) (f : ℕ → ℕ) : ℕ := Nat.rec 0 (fun k acc => Nat.add (f k) acc) n

theorem sumR_eq (n : ℕ) (f : ℕ → ℕ) : sumR n f = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.add (f n) (sumR n f) = _
    rw [Finset.sum_range_succ, ← ih, Nat.add_eq, Nat.add_comm]

/-- The largest of f 0, ..., f (n - 1), and 0 for n = 0, by the recursor of ℕ. -/
noncomputable def maxR (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec 0 (fun k acc => cond (Nat.ble (f k) acc) acc (f k)) n

theorem maxR_succ (n : ℕ) (f : ℕ → ℕ) : maxR (n + 1) f = max (f n) (maxR n f) := by
  show cond (Nat.ble (f n) (maxR n f)) (maxR n f) (f n) = _
  cases hb : Nat.ble (f n) (maxR n f)
  · have h : ¬ f n ≤ maxR n f := fun h => by
      rw [Nat.ble_eq_true_of_le h] at hb
      exact Bool.noConfusion hb
    exact (max_eq_left (not_le.mp h).le).symm
  · exact (max_eq_right (Nat.le_of_ble_eq_true hb)).symm

theorem maxR_le (n : ℕ) (f : ℕ → ℕ) (c : ℕ) (h : ∀ k, k < n → f k ≤ c) : maxR n f ≤ c := by
  induction n with
  | zero => exact Nat.zero_le c
  | succ n ih =>
    rw [maxR_succ]
    exact max_le (h n (Nat.lt_succ_self n)) (ih (fun k hk => h k (Nat.lt_succ_of_lt hk)))

theorem le_maxR (n : ℕ) (f : ℕ → ℕ) (k : ℕ) (hk : k < n) : f k ≤ maxR n f := by
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    rw [maxR_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · exact le_trans (ih h) (le_max_right _ _)
    · rw [h]
      exact le_max_left _ _

theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl

theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl

/-- f a && ... && f (a + w - 1): one piece of a kernel check. -/
noncomputable def allI (a w : ℕ) (f : ℕ → Bool) : Bool := allR w fun t => f (Nat.add a t)

theorem allI_get (a w : ℕ) (f : ℕ → Bool) (h : allI a w f = true) (k : ℕ) (h1 : a ≤ k)
    (h2 : k < a + w) : f k = true := by
  have := (allR_iff _ _).1 h (k - a) (by omega)
  rwa [Nat.add_eq, Nat.add_sub_cancel' h1] at this

/-- The potential tables of the distance part as natural numbers. -/
def AW (i : ℕ) : ℕ := tgetN 367114566005 4 i

def BW (i : ℕ) : ℕ := tgetN 596139074630 4 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem A_W (i : Fin 10) : Ac i = (AW i.val : ℤ) - 8 := by rw [Ac, tget, Int.subNatNat_eq_coe]; rfl

theorem B_W (i : Fin 10) : Bc i = (BW i.val : ℤ) - 8 := by rw [Bc, tget, Int.subNatNat_eq_coe]; rfl

theorem C_W (s : Fin 9) (i : Fin 10) : Cc s i = (CW s.val i.val : ℤ) - 8 := by rw [Cc, tget, Int.subNatNat_eq_coe]; rfl

def gcV (k : ℕ) : ℕ := ctabN 874325 2 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 10) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 273894672 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 3

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 302935973890 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 4

def Bp (i : Fin 10) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 141856 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 10) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 340304019 3 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 2

def be (i : Fin 10) : ℤ := beN i.val

def primK : PLift (∀ i : Fin 10, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧ al i * Ap i + be i * Bp i = 1) :=
  ⟨by decide +kernel⟩

theorem prim : ∀ i : Fin 10, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧ al i * Ap i + be i * Bp i = 1 := primK.down

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 10) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 10) : ℤ := Ac j * al i + Bc j * be i

def orientK : PLift (∀ i : Fin 10, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0) :=
  ⟨by decide +kernel⟩

theorem orient : ∀ i : Fin 10, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := orientK.down

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 9) (i : Fin 10) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 9) (i j : Fin 10) (c u : ℤ) :
    pot (par s i c u) j = ka i j * c + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 10) :
    v = par v.2.2 i (Ap i * v.1 + Bp i * v.2.1) (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := (prim i).2.2.2
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb
  · linear_combination (-y) * hb

theorem pot_lev (v : V) (i : Fin 10) : pot v i = gc i * (Ap i * v.1 + Bp i * v.2.1) + Cc v.2.2 i := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  simp only [pot]
  rw [h1, h2]
  ring

theorem par_inj (s : Fin 9) (i : Fin 10) (c : ℤ) : Function.Injective (par s i c) := by
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
theorem F_attained (v : V) : ∃ k : Fin 10, pot v k = F v := by
  by_contra hne
  have h : ∀ k, pot v k ≤ F v - 1 := fun k => by
    have h1 := le_F v k
    have h2 : pot v k ≠ F v := fun e => hne ⟨k, e⟩
    omega
  have := F_le v (F v - 1) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9)
  omega

/-- The first facet attaining the maximum. -/
noncomputable def fi (v : V) : Fin 10 := Fin.find (fun k => pot v k = F v) (F_attained v)

theorem fi_spec (v : V) : pot v (fi v) = F v ∧ ∀ j, j < fi v → pot v j < F v :=
  ⟨Fin.find_spec (F_attained v), fun j hj =>
    lt_of_le_of_ne (le_F v j) (Fin.find_min (F_attained v) hj)⟩

theorem fi_iff (v : V) (i : Fin 10) : fi v = i ↔ pot v i = F v ∧ ∀ j, j < i → pot v j < F v := by
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
theorem piece_iff (v : V) (i : Fin 10) (n : ℤ) :
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

/-- The previous and the next facet around the growth polygon, and [i - 1 < i], [i + 1 < i]. -/
def prevF (i : ℕ) : ℕ := Nat.mod (Nat.add i 9) 10

def nextF (i : ℕ) : ℕ := Nat.mod (Nat.add i 1) 10

def ehV (k : ℕ) : ℕ := ctabN 1022 1 k

def ekV (k : ℕ) : ℕ := ctabN 512 1 k

def fin_prevK : PLift (∀ i : Fin 10, (i - 1).val = prevF i.val ∧ (if i - 1 < i then (1 : ℤ) else 0) = (ehV i.val : ℤ)) :=
  ⟨by decide +kernel⟩

theorem fin_prev : ∀ i : Fin 10, (i - 1).val = prevF i.val ∧ (if i - 1 < i then (1 : ℤ) else 0) = (ehV i.val : ℤ) := fin_prevK.down

def fin_nextK : PLift (∀ i : Fin 10, (i + 1).val = nextF i.val ∧ (if i + 1 < i then (1 : ℤ) else 0) = (ekV i.val : ℤ)) :=
  ⟨by decide +kernel⟩

theorem fin_next : ∀ i : Fin 10, (i + 1).val = nextF i.val ∧ (if i + 1 < i then (1 : ℤ) else 0) = (ekV i.val : ℤ) := fin_nextK.down

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (7 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 26917620171801678162540362749915072927129991792449316979055308325786535722686733805176320 3 k

def cf2V (k : ℕ) : ℕ := ctabN 1790898551451896168037885841591128564929797858320534892548826164786002139616721254336 3 k

def cf3V (k : ℕ) : ℕ := ctabN 13499044579879268431028967130923493679188213408730975557084041441510057315707874898645824 3 k

def cf0V (k : ℕ) : ℕ := ctabN 10088795578754518217675539011748950456084916450192906087454082306827181860610584002756736 3 k

def cf1 (i j : Fin 10) : ℤ := (cf1V (j.val + 10 * i.val) : ℤ)

def cf2 (i j : Fin 10) : ℤ := (cf2V (j.val + 10 * i.val) : ℤ)

def cf3 (i j : Fin 10) : ℤ := (cf3V (j.val + 10 * i.val) : ℤ)

def cf0 (i j : Fin 10) : ℤ := (cf0V (j.val + 10 * i.val) : ℤ)

/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 9) (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (7 - Cc s i)

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := Nat.beq j i || Nat.beq j (nextF i) || Nat.beq j (prevF i)

/-- certG in natural numbers: Ac = AW - 8, Bc = BW - 8, the negative terms moved across. -/
def certGN (i j : ℕ) : Bool :=
  Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (AW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (AW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (AW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 8))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 10 i))) (cf2V (Nat.add j (Nat.mul 10 i)))) (cf0V (Nat.add j (Nat.mul 10 i)))) (AW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (AW j))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (BW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (BW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (BW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 8))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 10 i))) (cf2V (Nat.add j (Nat.mul 10 i)))) (cf0V (Nat.add j (Nat.mul 10 i)))) (BW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (BW j)))

/-- certC in natural numbers: Cc = CW - 8, the negative terms moved across. -/
def certCN (s i j : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 10 i))) (cf2V (Nat.add j (Nat.mul 10 i)))) (cf0V (Nat.add j (Nat.mul 10 i)))) (CW s i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (CW s j)))
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 15))

def certGK : PLift ((allR 10 fun i => allR 10 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 10 fun i => allR 10 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 9 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 9) : certS s = true := by
  exact allI_get _ _ _ certCK0.down s (by omega) (by omega)

theorem beq_ff (x y : ℕ) (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem near_false (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    nearB i.val j.val = false := by
  obtain ⟨a1, -⟩ := fin_prev i
  obtain ⟨b1, -⟩ := fin_next i
  have n1 : j.val ≠ i.val := fun h => e2 (Fin.ext h)
  have n2 : j.val ≠ nextF i.val := fun h => e3 (Fin.ext (h.trans b1.symm))
  have n3 : j.val ≠ prevF i.val := fun h => e1 (Fin.ext (h.trans a1.symm))
  rw [nearB, beq_ff _ _ n1, beq_ff _ _ n2, beq_ff _ _ n3]
  rfl

/-- The gradient parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certG_ok (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) : certG i j := by
  obtain ⟨a1, -⟩ := fin_prev i
  obtain ⟨b1, -⟩ := fin_next i
  have hk := (allR_iff _ _).1 ((allR_iff _ _).1 certGK.down i.val i.isLt) j.val j.isLt
  rw [near_false i j e1 e2 e3, Bool.false_or] at hk
  simp only [certGN, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hk
  obtain ⟨hA, hB⟩ := hk
  have cA := congrArg (Nat.cast : ℕ → ℤ) hA
  have cB := congrArg (Nat.cast : ℕ → ℤ) hB
  push_cast at cA cB
  simp only [certG, cf1, cf2, cf3, cf0, A_W, B_W, a1, b1]
  refine ⟨by positivity, by positivity, by positivity, by positivity, by linear_combination cA,
    by linear_combination cB⟩

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 9) (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  obtain ⟨a1, a2⟩ := fin_prev i
  obtain ⟨b1, b2⟩ := fin_next i
  have hk := (allR_iff _ _).1 ((allR_iff _ _).1 (cert_ok s.val s.isLt) i.val i.isLt) j.val j.isLt
  rw [near_false i j e1 e2 e3, Bool.false_or] at hk
  simp only [certCN, Nat.blt_eq, Nat.add_eq, Nat.mul_eq] at hk
  have ck := (Nat.cast_lt (α := ℤ)).mpr hk
  push_cast at ck
  simp only [certC, cf1, cf2, cf3, cf0, a2, b2, C_W, a1, b1]
  ring_nf at ck ⊢
  linarith

theorem farkas4 (v : V) (h i k j : Fin 10) (e1 e2 r l1 l2 l3 l0 : ℤ)
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
def lev (s : Fin 9) (i : Fin 10) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 9) (i : Fin 10) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 9) (i j : Fin 10) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 9) (i : Fin 10) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 9) (i : Fin 10) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 9) (i j : Fin 10) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 9) (i : Fin 10) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 9) (i : Fin 10) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 10) : ka i i = gc i := by
  obtain ⟨h1, h2, -, hb⟩ := prim i
  rw [ka, h1, h2]
  linear_combination (gc i) * hb

theorem Dm_self (i : Fin 10) : Dm i i = 0 := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  rw [Dm, h1, h2]
  ring

theorem pot_par_self (s : Fin 9) (i : Fin 10) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 7 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 9) (i : Fin 10) (n u : ℤ) (hn : 7 ≤ n)
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
  simp only [certC] at cc
  by_contra hne
  have f3 : pot (par s i (lev s i n) u) i ≤ pot (par s i (lev s i n) u) j := by
    have := (ite01 (j < i)).2
    rw [hi']
    linarith [not_le.1 hne]
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 7 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-4, 4]: a natural-number check. -/
def cbK : PLift ((allR 9 fun s => allR 10 fun i => Nat.ble (CW s i) 12 && Nat.ble 8 (Nat.add (CW s i) 4)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 9) (j : Fin 10) : -4 ≤ Cc s j ∧ Cc s j ≤ 4 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 4)) (1 * n + 4) ×ˢ
    (Finset.Icc (-(1 * n + 4)) (1 * n + 4) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (1 * Ac 3 + 1 * Ac 5 = 6 ∧ 1 * Bc 3 + 1 * Bc 5 = 0 ∧
    1 * Ac 0 + 1 * Ac 8 = (-6) ∧ 1 * Bc 0 + 1 * Bc 8 = 0 ∧
    1 * Ac 6 + 1 * Ac 7 = 0 ∧ 1 * Bc 6 + 1 * Bc 7 = 8 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-8)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 1 * Ac 3 + 1 * Ac 5 = 6 ∧ 1 * Bc 3 + 1 * Bc 5 = 0 ∧
    1 * Ac 0 + 1 * Ac 8 = (-6) ∧ 1 * Bc 0 + 1 * Bc 8 = 0 ∧
    1 * Ac 6 + 1 * Ac 7 = 0 ∧ 1 * Bc 6 + 1 * Bc 7 = 8 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-8) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 9) :
    6 * x ≤ 2 * F (x, y, s) + 8 ∧
    6 * (-x) ≤ 2 * F (x, y, s) + 8 ∧
    8 * y ≤ 2 * F (x, y, s) + 8 ∧
    8 * (-y) ≤ 2 * F (x, y, s) + 8 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 3 + 1 * pot (x, y, s) 5 =
      6 * x + 1 * Cc s 3 + 1 * Cc s 5 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 3
  have r0 := le_F (x, y, s) 5
  have k0 := Cbound s 3
  have l0 := Cbound s 5
  have e1 : 1 * pot (x, y, s) 0 + 1 * pot (x, y, s) 8 =
      6 * (-x) + 1 * Cc s 0 + 1 * Cc s 8 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 8
  have k1 := Cbound s 0
  have l1 := Cbound s 8
  have e2 : 1 * pot (x, y, s) 6 + 1 * pot (x, y, s) 7 =
      8 * y + 1 * Cc s 6 + 1 * Cc s 7 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 6
  have r2 := le_F (x, y, s) 7
  have k2 := Cbound s 6
  have l2 := Cbound s 7
  have e3 : 1 * pot (x, y, s) 1 + 1 * pot (x, y, s) 2 =
      8 * (-y) + 1 * Cc s 1 + 1 * Cc s 2 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 1
  have r3 := le_F (x, y, s) 2
  have k3 := Cbound s 1
  have l3 := Cbound s 2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 9) (i : Fin 10) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 9) (i : Fin 10) (n : ℤ) (hn : 7 ≤ n) :
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
def inner (s : Fin 9) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 9) (i : Fin 10) (n : ℤ) (hn : 7 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 9 × Fin 10, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 10, inner p.1 p.2 n

/-! Shifting n by 60 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 377444539527581500 6 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 648744313764918800 6 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 36

def mh (i : Fin 10) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 230811375198275300 6 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 12

def mk (i : Fin 10) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 10, (60 : ℤ) = gc i * Lq i ∧ 60 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 60 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 10, (60 : ℤ) = gc i * Lq i ∧ 60 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 60 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 9) (i : Fin 10) (n : ℤ) :
    inner s i (n + 60) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 60 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 60 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 60) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 60) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 60) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 9 × Fin 10, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 60) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 60 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 60 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 7 + r with r < 60: the level is QQ - 0 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 32800 2 k

def uhMV (k : ℕ) : ℕ := ctabN 101256210 3 k

def ukPV (k : ℕ) : ℕ := ctabN 67766292 3 k

def ukMV (k : ℕ) : ℕ := ctabN 32800 2 k

def dhV (k : ℕ) : ℕ := ctabN 182710347942 4 k

def dkV (k : ℕ) : ℕ := ctabN 166037973642 4 k

def mhkV (k : ℕ) : ℕ := ctabN 74320092 3 k

def uh (i : Fin 10) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 10) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 10) : ℤ := dhV i.val

def dk (i : Fin 10) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 766622280585019295180521257944043381382679836735570432 2 (Nat.add i (Nat.mul 10 s))

def QQ (s i : ℕ) : ℕ := ctabN 370552526340885238058820195047437451634112506353262541116534913704232049312561253935850837564980791918819191 4 (Nat.add i (Nat.mul 10 s))

def AH (s i : ℕ) : ℕ := ctabN 117209329093814757807361366776529688408268799757525791467091418482081215346762050637715314502664626579103589033926452984951007945667746 5 (Nat.add i (Nat.mul 10 s))

def AK (s i : ℕ) : ℕ := ctabN 84356832546218385667936359457620185393190255132655490836726412232094363473594108275508068027591673275001436514927105492034044830600179449448893108415569859208092 6 (Nat.add i (Nat.mul 10 s))

def WH (s i : ℕ) : ℕ := ctabN 93144437252382133268140759041797880739954799811714381748919443456770365710361259595493473732901907261453112366231082908469382675069210068684012482893226541581207 6 (Nat.add i (Nat.mul 10 s))

def WK (s i : ℕ) : ℕ := ctabN 7453878157352569897178617961347674178933976812380936061173452363685274958583465867536855570832100069215744 4 (Nat.add i (Nat.mul 10 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 9 fun s => allR 10 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq 15 (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 9) (i : Fin 10) :
    PP s.val i.val < gcV i.val ∧
    (7 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 0) + PP s.val i.val ∧
    (AH s.val i.val : ℤ) = uh i * ((QQ s.val i.val : ℤ) - 0) +
      (Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0)) + dh i * WH s.val i.val -
      (uhMV i.val : ℤ) * LqV i.val ∧
    (AK s.val i.val : ℤ) = uk i * ((QQ s.val i.val : ℤ) - 0) +
      (Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0)) + dk i * WK s.val i.val -
      (ukMV i.val : ℤ) * LqV i.val := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 pieceOK_eq s.val s.isLt) i.val i.isLt
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨a1, a2⟩ := fin_prev i
  obtain ⟨b1, b2⟩ := fin_next i
  have c2 := congrArg (Nat.cast : ℕ → ℤ) h2
  have c3 := congrArg (Nat.cast : ℕ → ℤ) h3
  have c4 := congrArg (Nat.cast : ℕ → ℤ) h4
  push_cast at c2 c3 c4
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [C_W, show gc i = ((gcV i.val : ℕ) : ℤ) from rfl]
    linear_combination c2
  · rw [a2, C_W, C_W, a1, show uh i = (uhPV i.val : ℤ) - uhMV i.val from rfl,
      show dh i = ((dhV i.val : ℕ) : ℤ) from rfl]
    linear_combination c3
  · rw [b2, C_W, C_W, b1, show uk i = (ukPV i.val : ℤ) - ukMV i.val from rfl,
      show dk i = ((dkV i.val : ℕ) : ℤ) from rfl]
    linear_combination c4

/-- Piece (s, i) at n = 7 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 7 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 9) (i : Fin 10) (r : ℕ) :
    ((7 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (7 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 0) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 9) (i : Fin 10) (r : ℕ) (hr : r < 60) :
    inner s i ((7 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (60 : ℤ) = gc i * Lq i := (shift_ok i).1
  rw [inner, innerZ]
  by_cases hd : divN s.val i.val r = true
  · rw [if_pos ((div_nat s i r).2 hd), if_pos hd]
    have hg0 : 0 < gcV i.val := by
      have := (prim i).2.2.1
      rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl] at this
      exact_mod_cast this
    have hd' : (PP s.val i.val + r) % gcV i.val = 0 := by
      simpa only [divN, Nat.beq_eq, Nat.add_eq, nmod] using hd
    have hτ : tauN s.val i.val r ≤ LqV i.val := by
      have h2 : 60 = gcV i.val * LqV i.val := by
        rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, show Lq i = ((LqV i.val : ℕ) : ℤ) from rfl] at hL
        exact_mod_cast hL
      simp only [tauN, Nat.add_eq, ndiv]
      apply Nat.lt_succ_iff.1
      rw [Nat.div_lt_iff_lt_mul hg0, Nat.succ_eq_add_one]
      nlinarith
    have hτg : ((PP s.val i.val : ℕ) : ℤ) + r = gc i * (tauN s.val i.val r : ℤ) := by
      have := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd')
      simp only [tauN, Nat.add_eq, ndiv]
      rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl]
      exact_mod_cast this.symm
    have hl : lev s i ((7 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r := by
      rw [lev, show (7 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((7 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((7 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
        (numK s.val i.val r : ℤ) := by
      simp only [numK, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hkb]
      simp only [uk, dk] at hAk ⊢
      linear_combination hQ + hτg - hAk
    have dh0 : 0 < dhV i.val := by
      have : (0 : ℤ) < dhV i.val := by rw [show ((dhV i.val : ℕ) : ℤ) = dh i from rfl, f2]; exact o1
      exact_mod_cast this
    have dk0 : 0 < dkV i.val := by
      have : (0 : ℤ) < dkV i.val := by rw [show ((dkV i.val : ℕ) : ℤ) = dk i from rfl, f4]; linarith
      exact_mod_cast this
    rw [hi, lo, ← f2, ← f4, show dh i = ((dhV i.val : ℕ) : ℤ) from rfl,
      show dk i = ((dkV i.val : ℕ) : ℤ) from rfl, ediv_shift _ _ _ _ dh0 kh, ediv_shift _ _ _ _ dk0 kk]
    simp only [lenN, wN, Nat.add_eq, ndiv]
    push_cast
    ring
  · rw [if_neg (fun h => hd ((div_nat s i r).1 h)), if_neg hd]

def dtabV (k : ℕ) : ℕ := ctabN 3085022096782862911012401968266187878622144046868912666731402171865073247774827201060067207733333242087358378990566544979030940671296658420333820 8 k

def tblV (k : ℕ) : ℕ := ctabN 1964986856015792335635758276309878691603316961541360555767510919787423523427297315579639893688926774016173649699031387614916207547566713920472436423006731141137437 9 k

def initV (k : ℕ) : ℕ := ctabN 28569935969 5 k

/-- The step of the closed form at residue t mod 60. -/
def dv (t : ℕ) : ℕ := dtabV (t % 60)

/-- The sequence in closed form: b(n + 60) = b(n) + dv (n - 7) for n ≥ 7. -/
def b (n : ℕ) : ℕ :=
  if n < 7 then initV n else dv (n - 7) * ((n - 7) / 60) + tblV ((n - 7) % 60)

theorem b_step (n : ℕ) (hn : 7 ≤ n) : b (n + 60) = b n + dv (n - 7) := by
  rw [b, b, if_neg (show ¬ (n + 60 < 7) by omega), if_neg (show ¬ (n < 7) by omega),
    show n + 60 - 7 = n - 7 + 60 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 60)]
  ring

theorem b_shift (n : ℕ) (hn : 7 ≤ n) : b (n + 60) = b n + 1 * dv (n - 7) := by
  rw [b, b, if_neg (show ¬ (n + 60 < 7) by omega), if_neg (show ¬ (n < 7) by omega),
    show n + 60 - 7 = n - 7 + 60 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 60)]
  ring

/-- b on the residue class of 7 + j mod 60. -/
theorem b_res (k j : ℕ) (hj : j < 60) : b (60 * k + (7 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (60 * k + (7 + j) < 7) by omega),
    show 60 * k + (7 + j) - 7 = j + 60 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 60), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 7 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 60 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 9 fun s => allR 10 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 9 fun s => sumR 10 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 7 r)) &&
    Nat.beq (sumR 9 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 1 (dv (Nat.add 0 r)))

/-! The window n = 7, ..., 66, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 16 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 16 16 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 32 16 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK3 : PLift (allI 48 12 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 60) :
    (∀ s, s < 9 → ∀ i, i < 10 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 9 fun s => sumR 10 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (7 + r) ∧
    (sumR 9 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0) = 1 * dv (0 + r) := by
  have h : periodR r = true := by
    rcases (show r < 16 ∨ (16 ≤ r ∧ r < 32) ∨ (32 ≤ r ∧ r < 48) ∨ 48 ≤ r by omega) with h | h | h | h
    · exact allI_get _ _ _ periodK0.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK1.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK2.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK3.down r (by omega) (by omega)
  simp only [periodR, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun s hs i hi hd => ?_, h2, h3⟩
  have h4 := (allR_iff _ _).1 ((allR_iff _ _).1 h1 s hs) i hi
  rw [hd] at h4
  simpa using h4

theorem innerZ_eq (s i r : ℕ) (hs : s < 9) (hi : i < 10) (hr : r < 60) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 9 fun s => sumR 10 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 9 × Fin 10, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 10 fun i => f s i : ℕ) : ℤ)) 9]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 10]

theorem S_window (r : ℕ) (hr : r < 60) : S ((7 : ℤ) + r) = b (7 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 60) : Gs ((7 : ℤ) + r) = ((1 * dv (0 + r) : ℕ) : ℤ) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.2
  rw [sumR2] at h
  rw [← h, Gs]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rcases Bool.eq_false_or_eq_true (divN q.1.val q.2.val r) with hd | hd
  · rw [if_pos ((div_nat q.1 q.2 r).2 hd), hd, cond_true, (tab_facet q.2).2.2.2.2]
  · rw [if_neg (fun h' => by
      have := (div_nat q.1 q.2 r).1 h'
      rw [hd] at this
      exact Bool.noConfusion this), hd]
    rfl

/-- Every piece length is nonnegative from n = 7 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 9) (i : Fin 10) (n : ℤ) (hn : 7 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 7 + t := ⟨(n - 7).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 60
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 60) (by omega) (by omega)
      have e : (7 : ℤ) + t = (7 + (t - 60 : ℕ)) + 60 := by
        push_cast [Nat.cast_sub (by omega : 60 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 7 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 60 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 7 ≤ n) : (1 : ℤ) * (dv (n - 7) : ℤ) = Gs n := by
  have hr : (n - 7) % 60 < 60 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((7 : ℤ) + (((n - 7) % 60 : ℕ) : ℤ)) + 60 * (((n - 7) / 60 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 7) = dv (0 + (n - 7) % 60) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 7 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 67
    · obtain ⟨r, rfl⟩ : ∃ r, n = 7 + r := ⟨n - 7, by omega⟩
      push_cast
      exact S_window r (by omega)
    · have h1 := ih (n - 60) (by omega) (by omega)
      have h2 := S_shift ((n - 60 : ℕ) : ℤ)
      have h3 := b_shift (n - 60) (by omega)
      have h4 := grow (n - 60) (by omega)
      rw [show n - 60 + 60 = n by omega] at h3
      rw [show ((n - 60 : ℕ) : ℤ) + 60 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The coordination sequence

`a n` counts the level set F = n from n = 7 on (`a_eq_cnt`, from `a_eq_F`), and `small_vals`
lists the terms below 7. The terms from 7 to 6 are counted in the box, those from 7 on
are S(n), and all agree with the closed form b (`a_eq_b`). The step from n to n + 60, the closed form
per residue (`a_closed`), the controls, the recurrence and the g.f. follow, their base cases checked by
the kernel on b. -/

theorem a_eq_cnt (n : ℕ) (hn : 7 ≤ n) : a n = cnt n := by
  rw [a_eq_F n hn, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 7 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt n (by omega)]
  exact cnt_eq_S n (by exact_mod_cast hn)

def smallR0K : PLift ((List.range 7).map b = [1, 3, 8, 13, 14, 19, 26]) :=
  ⟨by decide +kernel⟩

theorem a_lt_R0 (n : ℕ) (hn : n < 7) : a n = b n := by
  have h : (List.range 7).map a = (List.range 7).map b := by
    rw [small_vals]
    exact smallR0K.down.symm
  exact List.map_inj_left.1 h n (List.mem_range.2 hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 7 ∨ 7 ≤ n by omega) with h | h
  · exact a_lt_R0 n h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

def dconst_baseK : PLift (∀ r : ℕ, r < 60 → dtabV r = 252) :=
  ⟨by decide +kernel⟩

theorem dconst_base : ∀ r : ℕ, r < 60 → dtabV r = 252 := dconst_baseK.down

theorem dv_const : ∀ t : ℕ, dv t = 252 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 60) = a(n) + 252 for n ≥ 7. -/
theorem a_step (n : ℕ) (hn : 7 ≤ n) : a (n + 60) = a n + 252 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 252 ∧ tblV 0 = 29 ∧ dv 1 = 252 ∧ tblV 1 = 34 ∧ dv 2 = 252 ∧ tblV 2 = 37 ∧ dv 3 = 252 ∧ tblV 3 = 41 ∧ dv 4 = 252 ∧ tblV 4 = 48 ∧ dv 5 = 252 ∧ tblV 5 = 51 ∧ dv 6 = 252 ∧ tblV 6 = 53 ∧ dv 7 = 252 ∧ tblV 7 = 58) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 252 ∧ tblV 8 = 65 ∧ dv 9 = 252 ∧ tblV 9 = 67 ∧ dv 10 = 252 ∧ tblV 10 = 70 ∧ dv 11 = 252 ∧ tblV 11 = 77 ∧ dv 12 = 252 ∧ tblV 12 = 79 ∧ dv 13 = 252 ∧ tblV 13 = 84 ∧ dv 14 = 252 ∧ tblV 14 = 89 ∧ dv 15 = 252 ∧ tblV 15 = 91) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 252 ∧ tblV 16 = 98 ∧ dv 17 = 252 ∧ tblV 17 = 101 ∧ dv 18 = 252 ∧ tblV 18 = 103 ∧ dv 19 = 252 ∧ tblV 19 = 110 ∧ dv 20 = 252 ∧ tblV 20 = 115 ∧ dv 21 = 252 ∧ tblV 21 = 117 ∧ dv 22 = 252 ∧ tblV 22 = 120 ∧ dv 23 = 252 ∧ tblV 23 = 127) :=
  ⟨by decide +kernel⟩

def closedK3 : PLift (dv 24 = 252 ∧ tblV 24 = 131 ∧ dv 25 = 252 ∧ tblV 25 = 134 ∧ dv 26 = 252 ∧ tblV 26 = 139 ∧ dv 27 = 252 ∧ tblV 27 = 141 ∧ dv 28 = 252 ∧ tblV 28 = 148 ∧ dv 29 = 252 ∧ tblV 29 = 153 ∧ dv 30 = 252 ∧ tblV 30 = 153 ∧ dv 31 = 252 ∧ tblV 31 = 160) :=
  ⟨by decide +kernel⟩

def closedK4 : PLift (dv 32 = 252 ∧ tblV 32 = 165 ∧ dv 33 = 252 ∧ tblV 33 = 167 ∧ dv 34 = 252 ∧ tblV 34 = 172 ∧ dv 35 = 252 ∧ tblV 35 = 177 ∧ dv 36 = 252 ∧ tblV 36 = 181 ∧ dv 37 = 252 ∧ tblV 37 = 184 ∧ dv 38 = 252 ∧ tblV 38 = 189 ∧ dv 39 = 252 ∧ tblV 39 = 193) :=
  ⟨by decide +kernel⟩

def closedK5 : PLift (dv 40 = 252 ∧ tblV 40 = 198 ∧ dv 41 = 252 ∧ tblV 41 = 203 ∧ dv 42 = 252 ∧ tblV 42 = 203 ∧ dv 43 = 252 ∧ tblV 43 = 210 ∧ dv 44 = 252 ∧ tblV 44 = 217 ∧ dv 45 = 252 ∧ tblV 45 = 217 ∧ dv 46 = 252 ∧ tblV 46 = 222 ∧ dv 47 = 252 ∧ tblV 47 = 227) :=
  ⟨by decide +kernel⟩

def closedK6 : PLift (dv 48 = 252 ∧ tblV 48 = 231 ∧ dv 49 = 252 ∧ tblV 49 = 236 ∧ dv 50 = 252 ∧ tblV 50 = 239 ∧ dv 51 = 252 ∧ tblV 51 = 243 ∧ dv 52 = 252 ∧ tblV 52 = 248 ∧ dv 53 = 252 ∧ tblV 53 = 253 ∧ dv 54 = 252 ∧ tblV 54 = 255 ∧ dv 55 = 252 ∧ tblV 55 = 260) :=
  ⟨by decide +kernel⟩

def closedK7 : PLift (dv 56 = 252 ∧ tblV 56 = 267 ∧ dv 57 = 252 ∧ tblV 57 = 267 ∧ dv 58 = 252 ∧ tblV 58 = 272 ∧ dv 59 = 252 ∧ tblV 59 = 279) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (60 * k + 7) = 252 * k + 29 ∧
    a (60 * k + 8) = 252 * k + 34 ∧
    a (60 * k + 9) = 252 * k + 37 ∧
    a (60 * k + 10) = 252 * k + 41 ∧
    a (60 * k + 11) = 252 * k + 48 ∧
    a (60 * k + 12) = 252 * k + 51 ∧
    a (60 * k + 13) = 252 * k + 53 ∧
    a (60 * k + 14) = 252 * k + 58 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 60 * k + 7 = 60 * k + (7 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 60 * k + 8 = 60 * k + (7 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 60 * k + 9 = 60 * k + (7 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 60 * k + 10 = 60 * k + (7 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 60 * k + 11 = 60 * k + (7 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 60 * k + 12 = 60 * k + (7 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 60 * k + 13 = 60 * k + (7 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 60 * k + 14 = 60 * k + (7 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (60 * k + 15) = 252 * k + 65 ∧
    a (60 * k + 16) = 252 * k + 67 ∧
    a (60 * k + 17) = 252 * k + 70 ∧
    a (60 * k + 18) = 252 * k + 77 ∧
    a (60 * k + 19) = 252 * k + 79 ∧
    a (60 * k + 20) = 252 * k + 84 ∧
    a (60 * k + 21) = 252 * k + 89 ∧
    a (60 * k + 22) = 252 * k + 91 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 60 * k + 15 = 60 * k + (7 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 60 * k + 16 = 60 * k + (7 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 60 * k + 17 = 60 * k + (7 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 60 * k + 18 = 60 * k + (7 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 60 * k + 19 = 60 * k + (7 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 60 * k + 20 = 60 * k + (7 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 60 * k + 21 = 60 * k + (7 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 60 * k + 22 = 60 * k + (7 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (60 * k + 23) = 252 * k + 98 ∧
    a (60 * k + 24) = 252 * k + 101 ∧
    a (60 * k + 25) = 252 * k + 103 ∧
    a (60 * k + 26) = 252 * k + 110 ∧
    a (60 * k + 27) = 252 * k + 115 ∧
    a (60 * k + 28) = 252 * k + 117 ∧
    a (60 * k + 29) = 252 * k + 120 ∧
    a (60 * k + 30) = 252 * k + 127 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 60 * k + 23 = 60 * k + (7 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 60 * k + 24 = 60 * k + (7 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 60 * k + 25 = 60 * k + (7 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 60 * k + 26 = 60 * k + (7 + 19) from rfl, b_res k 19 (by decide), c38, c39]
  · rw [show 60 * k + 27 = 60 * k + (7 + 20) from rfl, b_res k 20 (by decide), c40, c41]
  · rw [show 60 * k + 28 = 60 * k + (7 + 21) from rfl, b_res k 21 (by decide), c42, c43]
  · rw [show 60 * k + 29 = 60 * k + (7 + 22) from rfl, b_res k 22 (by decide), c44, c45]
  · rw [show 60 * k + 30 = 60 * k + (7 + 23) from rfl, b_res k 23 (by decide), c46, c47]

theorem a_closed3 (k : ℕ) :
    a (60 * k + 31) = 252 * k + 131 ∧
    a (60 * k + 32) = 252 * k + 134 ∧
    a (60 * k + 33) = 252 * k + 139 ∧
    a (60 * k + 34) = 252 * k + 141 ∧
    a (60 * k + 35) = 252 * k + 148 ∧
    a (60 * k + 36) = 252 * k + 153 ∧
    a (60 * k + 37) = 252 * k + 153 ∧
    a (60 * k + 38) = 252 * k + 160 := by
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := closedK3.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 60 * k + 31 = 60 * k + (7 + 24) from rfl, b_res k 24 (by decide), c48, c49]
  · rw [show 60 * k + 32 = 60 * k + (7 + 25) from rfl, b_res k 25 (by decide), c50, c51]
  · rw [show 60 * k + 33 = 60 * k + (7 + 26) from rfl, b_res k 26 (by decide), c52, c53]
  · rw [show 60 * k + 34 = 60 * k + (7 + 27) from rfl, b_res k 27 (by decide), c54, c55]
  · rw [show 60 * k + 35 = 60 * k + (7 + 28) from rfl, b_res k 28 (by decide), c56, c57]
  · rw [show 60 * k + 36 = 60 * k + (7 + 29) from rfl, b_res k 29 (by decide), c58, c59]
  · rw [show 60 * k + 37 = 60 * k + (7 + 30) from rfl, b_res k 30 (by decide), c60, c61]
  · rw [show 60 * k + 38 = 60 * k + (7 + 31) from rfl, b_res k 31 (by decide), c62, c63]

theorem a_closed4 (k : ℕ) :
    a (60 * k + 39) = 252 * k + 165 ∧
    a (60 * k + 40) = 252 * k + 167 ∧
    a (60 * k + 41) = 252 * k + 172 ∧
    a (60 * k + 42) = 252 * k + 177 ∧
    a (60 * k + 43) = 252 * k + 181 ∧
    a (60 * k + 44) = 252 * k + 184 ∧
    a (60 * k + 45) = 252 * k + 189 ∧
    a (60 * k + 46) = 252 * k + 193 := by
  obtain ⟨c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79⟩ := closedK4.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 60 * k + 39 = 60 * k + (7 + 32) from rfl, b_res k 32 (by decide), c64, c65]
  · rw [show 60 * k + 40 = 60 * k + (7 + 33) from rfl, b_res k 33 (by decide), c66, c67]
  · rw [show 60 * k + 41 = 60 * k + (7 + 34) from rfl, b_res k 34 (by decide), c68, c69]
  · rw [show 60 * k + 42 = 60 * k + (7 + 35) from rfl, b_res k 35 (by decide), c70, c71]
  · rw [show 60 * k + 43 = 60 * k + (7 + 36) from rfl, b_res k 36 (by decide), c72, c73]
  · rw [show 60 * k + 44 = 60 * k + (7 + 37) from rfl, b_res k 37 (by decide), c74, c75]
  · rw [show 60 * k + 45 = 60 * k + (7 + 38) from rfl, b_res k 38 (by decide), c76, c77]
  · rw [show 60 * k + 46 = 60 * k + (7 + 39) from rfl, b_res k 39 (by decide), c78, c79]

theorem a_closed5 (k : ℕ) :
    a (60 * k + 47) = 252 * k + 198 ∧
    a (60 * k + 48) = 252 * k + 203 ∧
    a (60 * k + 49) = 252 * k + 203 ∧
    a (60 * k + 50) = 252 * k + 210 ∧
    a (60 * k + 51) = 252 * k + 217 ∧
    a (60 * k + 52) = 252 * k + 217 ∧
    a (60 * k + 53) = 252 * k + 222 ∧
    a (60 * k + 54) = 252 * k + 227 := by
  obtain ⟨c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95⟩ := closedK5.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 60 * k + 47 = 60 * k + (7 + 40) from rfl, b_res k 40 (by decide), c80, c81]
  · rw [show 60 * k + 48 = 60 * k + (7 + 41) from rfl, b_res k 41 (by decide), c82, c83]
  · rw [show 60 * k + 49 = 60 * k + (7 + 42) from rfl, b_res k 42 (by decide), c84, c85]
  · rw [show 60 * k + 50 = 60 * k + (7 + 43) from rfl, b_res k 43 (by decide), c86, c87]
  · rw [show 60 * k + 51 = 60 * k + (7 + 44) from rfl, b_res k 44 (by decide), c88, c89]
  · rw [show 60 * k + 52 = 60 * k + (7 + 45) from rfl, b_res k 45 (by decide), c90, c91]
  · rw [show 60 * k + 53 = 60 * k + (7 + 46) from rfl, b_res k 46 (by decide), c92, c93]
  · rw [show 60 * k + 54 = 60 * k + (7 + 47) from rfl, b_res k 47 (by decide), c94, c95]

theorem a_closed6 (k : ℕ) :
    a (60 * k + 55) = 252 * k + 231 ∧
    a (60 * k + 56) = 252 * k + 236 ∧
    a (60 * k + 57) = 252 * k + 239 ∧
    a (60 * k + 58) = 252 * k + 243 ∧
    a (60 * k + 59) = 252 * k + 248 ∧
    a (60 * k + 60) = 252 * k + 253 ∧
    a (60 * k + 61) = 252 * k + 255 ∧
    a (60 * k + 62) = 252 * k + 260 := by
  obtain ⟨c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111⟩ := closedK6.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 60 * k + 55 = 60 * k + (7 + 48) from rfl, b_res k 48 (by decide), c96, c97]
  · rw [show 60 * k + 56 = 60 * k + (7 + 49) from rfl, b_res k 49 (by decide), c98, c99]
  · rw [show 60 * k + 57 = 60 * k + (7 + 50) from rfl, b_res k 50 (by decide), c100, c101]
  · rw [show 60 * k + 58 = 60 * k + (7 + 51) from rfl, b_res k 51 (by decide), c102, c103]
  · rw [show 60 * k + 59 = 60 * k + (7 + 52) from rfl, b_res k 52 (by decide), c104, c105]
  · rw [show 60 * k + 60 = 60 * k + (7 + 53) from rfl, b_res k 53 (by decide), c106, c107]
  · rw [show 60 * k + 61 = 60 * k + (7 + 54) from rfl, b_res k 54 (by decide), c108, c109]
  · rw [show 60 * k + 62 = 60 * k + (7 + 55) from rfl, b_res k 55 (by decide), c110, c111]

theorem a_closed7 (k : ℕ) :
    a (60 * k + 63) = 252 * k + 267 ∧
    a (60 * k + 64) = 252 * k + 267 ∧
    a (60 * k + 65) = 252 * k + 272 ∧
    a (60 * k + 66) = 252 * k + 279 := by
  obtain ⟨c112, c113, c114, c115, c116, c117, c118, c119⟩ := closedK7.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 60 * k + 63 = 60 * k + (7 + 56) from rfl, b_res k 56 (by decide), c112, c113]
  · rw [show 60 * k + 64 = 60 * k + (7 + 57) from rfl, b_res k 57 (by decide), c114, c115]
  · rw [show 60 * k + 65 = 60 * k + (7 + 58) from rfl, b_res k 58 (by decide), c116, c117]
  · rw [show 60 * k + 66 = 60 * k + (7 + 59) from rfl, b_res k 59 (by decide), c118, c119]

/-- The closed form per residue of n mod 60, for n ≥ 7. -/
theorem a_closed (k : ℕ) :
    a (60 * k + 7) = 252 * k + 29 ∧
    a (60 * k + 8) = 252 * k + 34 ∧
    a (60 * k + 9) = 252 * k + 37 ∧
    a (60 * k + 10) = 252 * k + 41 ∧
    a (60 * k + 11) = 252 * k + 48 ∧
    a (60 * k + 12) = 252 * k + 51 ∧
    a (60 * k + 13) = 252 * k + 53 ∧
    a (60 * k + 14) = 252 * k + 58 ∧
    a (60 * k + 15) = 252 * k + 65 ∧
    a (60 * k + 16) = 252 * k + 67 ∧
    a (60 * k + 17) = 252 * k + 70 ∧
    a (60 * k + 18) = 252 * k + 77 ∧
    a (60 * k + 19) = 252 * k + 79 ∧
    a (60 * k + 20) = 252 * k + 84 ∧
    a (60 * k + 21) = 252 * k + 89 ∧
    a (60 * k + 22) = 252 * k + 91 ∧
    a (60 * k + 23) = 252 * k + 98 ∧
    a (60 * k + 24) = 252 * k + 101 ∧
    a (60 * k + 25) = 252 * k + 103 ∧
    a (60 * k + 26) = 252 * k + 110 ∧
    a (60 * k + 27) = 252 * k + 115 ∧
    a (60 * k + 28) = 252 * k + 117 ∧
    a (60 * k + 29) = 252 * k + 120 ∧
    a (60 * k + 30) = 252 * k + 127 ∧
    a (60 * k + 31) = 252 * k + 131 ∧
    a (60 * k + 32) = 252 * k + 134 ∧
    a (60 * k + 33) = 252 * k + 139 ∧
    a (60 * k + 34) = 252 * k + 141 ∧
    a (60 * k + 35) = 252 * k + 148 ∧
    a (60 * k + 36) = 252 * k + 153 ∧
    a (60 * k + 37) = 252 * k + 153 ∧
    a (60 * k + 38) = 252 * k + 160 ∧
    a (60 * k + 39) = 252 * k + 165 ∧
    a (60 * k + 40) = 252 * k + 167 ∧
    a (60 * k + 41) = 252 * k + 172 ∧
    a (60 * k + 42) = 252 * k + 177 ∧
    a (60 * k + 43) = 252 * k + 181 ∧
    a (60 * k + 44) = 252 * k + 184 ∧
    a (60 * k + 45) = 252 * k + 189 ∧
    a (60 * k + 46) = 252 * k + 193 ∧
    a (60 * k + 47) = 252 * k + 198 ∧
    a (60 * k + 48) = 252 * k + 203 ∧
    a (60 * k + 49) = 252 * k + 203 ∧
    a (60 * k + 50) = 252 * k + 210 ∧
    a (60 * k + 51) = 252 * k + 217 ∧
    a (60 * k + 52) = 252 * k + 217 ∧
    a (60 * k + 53) = 252 * k + 222 ∧
    a (60 * k + 54) = 252 * k + 227 ∧
    a (60 * k + 55) = 252 * k + 231 ∧
    a (60 * k + 56) = 252 * k + 236 ∧
    a (60 * k + 57) = 252 * k + 239 ∧
    a (60 * k + 58) = 252 * k + 243 ∧
    a (60 * k + 59) = 252 * k + 248 ∧
    a (60 * k + 60) = 252 * k + 253 ∧
    a (60 * k + 61) = 252 * k + 255 ∧
    a (60 * k + 62) = 252 * k + 260 ∧
    a (60 * k + 63) = 252 * k + 267 ∧
    a (60 * k + 64) = 252 * k + 267 ∧
    a (60 * k + 65) = 252 * k + 272 ∧
    a (60 * k + 66) = 252 * k + 279 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15⟩ := a_closed1 k
  obtain ⟨x16, x17, x18, x19, x20, x21, x22, x23⟩ := a_closed2 k
  obtain ⟨x24, x25, x26, x27, x28, x29, x30, x31⟩ := a_closed3 k
  obtain ⟨x32, x33, x34, x35, x36, x37, x38, x39⟩ := a_closed4 k
  obtain ⟨x40, x41, x42, x43, x44, x45, x46, x47⟩ := a_closed5 k
  obtain ⟨x48, x49, x50, x51, x52, x53, x54, x55⟩ := a_closed6 k
  obtain ⟨x56, x57, x58, x59⟩ := a_closed7 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59⟩

def controlsK : PLift ((List.range 50).map b = [1, 3, 8, 13, 14, 19, 26, 29, 34, 37, 41, 48, 51, 53, 58, 65, 67, 70, 77, 79, 84, 89, 91, 98, 101, 103, 110, 115, 117, 120, 127, 131, 134, 139, 141, 148, 153, 153, 160, 165, 167, 172, 177, 181, 184, 189, 193, 198, 203, 203]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 3, 8, 13, 14, 19, 26, 29, 34, 37, 41, 48, 51, 53, 58, 65, 67, 70, 77, 79, 84, 89, 91, 98, 101, 103, 110, 115, 117, 120, 127, 131, 134, 139, 141, 148, 153, 153, 160, 165, 167, 172, 177, 181, 184, 189, 193, 198, 203, 203] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 60 → dv (t + 10) + dv (t + 8) + dv (t + 2) + dv (t + 0) = dv (t + 7) + 2 * dv (t + 5) + dv (t + 3)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 60 → dv (t + 10) + dv (t + 8) + dv (t + 2) + dv (t + 0) = dv (t + 7) + 2 * dv (t + 5) + dv (t + 3) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 10) : ℤ) = -(dv (t + 8) : ℤ) + (dv (t + 7) : ℤ) + 2 * (dv (t + 5) : ℤ) + (dv (t + 3) : ℤ) - (dv (t + 2) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 60 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 2, e 3, e 5, e 7, e 8, e 10]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 60) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 60 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 60 → b (q + 17) + b (q + 15) + b (q + 9) + b (q + 7) = b (q + 14) + 2 * b (q + 12) + b (q + 10)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 60 → b (q + 17) + b (q + 15) + b (q + 9) + b (q + 7) = b (q + 14) + 2 * b (q + 12) + b (q + 10) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 17) : ℤ) = -b (q + 15) + b (q + 14) + 2 * b (q + 12) + b (q + 10) - b (q + 9) - b (q + 7) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 60 ∨ 60 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 60 := ⟨q - 60, by omega⟩
      have h0 : (b (v + 17) : ℤ) = -b (v + 15) + b (v + 14) + 2 * b (v + 12) + b (v + 10) - b (v + 9) - b (v + 7) := ih (v + 0) (by omega)
      have hd := drec v
      have s7 : (b (v + 67) : ℤ) = b (v + 7) + dv (v + 0) := by
        have h := b_step (v + 7) (le_trans (by decide : 7 ≤ 7) (Nat.le_add_left _ v))
        rw [show v + 7 + 60 = v + 67 from Nat.add_assoc _ _ _,
          show v + 7 - 7 = v + 0 from Nat.add_sub_assoc (by decide : 7 ≤ 7) v] at h
        exact_mod_cast h
      have s9 : (b (v + 69) : ℤ) = b (v + 9) + dv (v + 2) := by
        have h := b_step (v + 9) (le_trans (by decide : 7 ≤ 9) (Nat.le_add_left _ v))
        rw [show v + 9 + 60 = v + 69 from Nat.add_assoc _ _ _,
          show v + 9 - 7 = v + 2 from Nat.add_sub_assoc (by decide : 7 ≤ 9) v] at h
        exact_mod_cast h
      have s10 : (b (v + 70) : ℤ) = b (v + 10) + dv (v + 3) := by
        have h := b_step (v + 10) (le_trans (by decide : 7 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 60 = v + 70 from Nat.add_assoc _ _ _,
          show v + 10 - 7 = v + 3 from Nat.add_sub_assoc (by decide : 7 ≤ 10) v] at h
        exact_mod_cast h
      have s12 : (b (v + 72) : ℤ) = b (v + 12) + dv (v + 5) := by
        have h := b_step (v + 12) (le_trans (by decide : 7 ≤ 12) (Nat.le_add_left _ v))
        rw [show v + 12 + 60 = v + 72 from Nat.add_assoc _ _ _,
          show v + 12 - 7 = v + 5 from Nat.add_sub_assoc (by decide : 7 ≤ 12) v] at h
        exact_mod_cast h
      have s14 : (b (v + 74) : ℤ) = b (v + 14) + dv (v + 7) := by
        have h := b_step (v + 14) (le_trans (by decide : 7 ≤ 14) (Nat.le_add_left _ v))
        rw [show v + 14 + 60 = v + 74 from Nat.add_assoc _ _ _,
          show v + 14 - 7 = v + 7 from Nat.add_sub_assoc (by decide : 7 ≤ 14) v] at h
        exact_mod_cast h
      have s15 : (b (v + 75) : ℤ) = b (v + 15) + dv (v + 8) := by
        have h := b_step (v + 15) (le_trans (by decide : 7 ≤ 15) (Nat.le_add_left _ v))
        rw [show v + 15 + 60 = v + 75 from Nat.add_assoc _ _ _,
          show v + 15 - 7 = v + 8 from Nat.add_sub_assoc (by decide : 7 ≤ 15) v] at h
        exact_mod_cast h
      have s17 : (b (v + 77) : ℤ) = b (v + 17) + dv (v + 10) := by
        have h := b_step (v + 17) (le_trans (by decide : 7 ≤ 17) (Nat.le_add_left _ v))
        rw [show v + 17 + 60 = v + 77 from Nat.add_assoc _ _ _,
          show v + 17 - 7 = v + 10 from Nat.add_sub_assoc (by decide : 7 ≤ 17) v] at h
        exact_mod_cast h
      show (b (v + 77) : ℤ) = -b (v + 75) + b (v + 74) + 2 * b (v + 72) + b (v + 70) - b (v + 69) - b (v + 67)
      linear_combination s17 - (-1) * s15 - (1) * s14 - (2) * s12 - (1) * s10 - (-1) * s9 - (-1) * s7 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 16 < n → (a n : ℤ) = -a (n - 2) + a (n - 3) + 2 * a (n - 5) + a (n - 7) - a (n - 8) - a (n - 10) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 17 := ⟨n - 17, by omega⟩
  rw [show q + 17 - 2 = q + 15 from Nat.add_sub_assoc (by decide : 2 ≤ 17) q, show q + 17 - 3 = q + 14 from Nat.add_sub_assoc (by decide : 3 ≤ 17) q, show q + 17 - 5 = q + 12 from Nat.add_sub_assoc (by decide : 5 ≤ 17) q, show q + 17 - 7 = q + 10 from Nat.add_sub_assoc (by decide : 7 ≤ 17) q, show q + 17 - 8 = q + 9 from Nat.add_sub_assoc (by decide : 8 ≤ 17) q, show q + 17 - 10 = q + 7 from Nat.add_sub_assoc (by decide : 10 ≤ 17) q]
  simp only [a_eq_b]
  exact b_recur q

/-- b (n - k) for k ≤ n, and [n = j]: the shapes of the coefficients of the g.f. -/
def bk (n k : ℕ) : ℕ := cond (Nat.ble k n) (b (Nat.sub n k)) 0

def ind (n j : ℕ) : ℕ := cond (Nat.beq n j) 1 0

theorem cast_bk (n k : ℕ) : ((bk n k : ℕ) : ℚ) = if k ≤ n then ((b (n - k) : ℕ) : ℚ) else 0 := by
  rw [bk]
  by_cases h : k ≤ n
  · rw [if_pos h, Nat.ble_eq_true_of_le h]
    rfl
  · rw [if_neg h]
    cases hb : Nat.ble k n
    · simp
    · exact absurd (Nat.le_of_ble_eq_true hb) h

theorem cast_ind (n j : ℕ) : ((ind n j : ℕ) : ℚ) = if n = j then 1 else 0 := by
  rw [ind]
  by_cases h : n = j
  · subst h
    rw [Nat.beq_refl, if_pos rfl]
    simp
  · rw [if_neg h, beq_ff _ _ h]
    simp

/-- The coefficients of A * DEN and NUM agree below 17, in natural numbers (negative terms moved
across). -/
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (b n) (bk n 2)) (bk n 8)) (bk n 10)) (Nat.mul 2 (ind n 13))) (Nat.mul 2 (ind n 14))) (ind n 15)) (ind n 16)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (bk n 3) (Nat.mul 2 (bk n 5))) (bk n 7)) (ind n 0)) (Nat.mul 3 (ind n 1))) (Nat.mul 9 (ind n 2))) (Nat.mul 15 (ind n 3))) (Nat.mul 19 (ind n 4))) (Nat.mul 22 (ind n 5))) (Nat.mul 21 (ind n 6))) (Nat.mul 17 (ind n 7))) (Nat.mul 13 (ind n 8))) (Nat.mul 7 (ind n 9))) (Nat.mul 4 (ind n 10))) (ind n 11)

def gfK : PLift ((allR 17 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 17, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 17) :
    1 * (b (n) : ℚ) + 1 * (if 2 ≤ n then (b (n - 2) : ℚ) else 0) - 1 * (if 3 ≤ n then (b (n - 3) : ℚ) else 0) - 2 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) - 1 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) + 1 * (if 8 ≤ n then (b (n - 8) : ℚ) else 0) + 1 * (if 10 ≤ n then (b (n - 10) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 3 + (if n = 2 then (1 : ℚ) else 0) * 9 + (if n = 3 then (1 : ℚ) else 0) * 15 + (if n = 4 then (1 : ℚ) else 0) * 19 + (if n = 5 then (1 : ℚ) else 0) * 22 + (if n = 6 then (1 : ℚ) else 0) * 21 + (if n = 7 then (1 : ℚ) else 0) * 17 + (if n = 8 then (1 : ℚ) else 0) * 13 + (if n = 9 then (1 : ℚ) else 0) * 7 + (if n = 10 then (1 : ℚ) else 0) * 4 + (if n = 11 then (1 : ℚ) else 0) * 1 - (if n = 13 then (1 : ℚ) else 0) * 2 - (if n = 14 then (1 : ℚ) else 0) * 2 - (if n = 15 then (1 : ℚ) else 0) * 1 - (if n = 16 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 17 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 17) : ℚ) + 1 * (if 2 ≤ q + 17 then (b (q + 17 - 2) : ℚ) else 0) - 1 * (if 3 ≤ q + 17 then (b (q + 17 - 3) : ℚ) else 0) - 2 * (if 5 ≤ q + 17 then (b (q + 17 - 5) : ℚ) else 0) - 1 * (if 7 ≤ q + 17 then (b (q + 17 - 7) : ℚ) else 0) + 1 * (if 8 ≤ q + 17 then (b (q + 17 - 8) : ℚ) else 0) + 1 * (if 10 ≤ q + 17 then (b (q + 17 - 10) : ℚ) else 0) =
      (if q + 17 = 0 then (1 : ℚ) else 0) * 1 + (if q + 17 = 1 then (1 : ℚ) else 0) * 3 + (if q + 17 = 2 then (1 : ℚ) else 0) * 9 + (if q + 17 = 3 then (1 : ℚ) else 0) * 15 + (if q + 17 = 4 then (1 : ℚ) else 0) * 19 + (if q + 17 = 5 then (1 : ℚ) else 0) * 22 + (if q + 17 = 6 then (1 : ℚ) else 0) * 21 + (if q + 17 = 7 then (1 : ℚ) else 0) * 17 + (if q + 17 = 8 then (1 : ℚ) else 0) * 13 + (if q + 17 = 9 then (1 : ℚ) else 0) * 7 + (if q + 17 = 10 then (1 : ℚ) else 0) * 4 + (if q + 17 = 11 then (1 : ℚ) else 0) * 1 - (if q + 17 = 13 then (1 : ℚ) else 0) * 2 - (if q + 17 = 14 then (1 : ℚ) else 0) * 2 - (if q + 17 = 15 then (1 : ℚ) else 0) * 1 - (if q + 17 = 16 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 17) : ℤ) = -b (q + 15) + b (q + 14) + 2 * b (q + 12) + b (q + 10) - b (q + 9) - b (q + 7) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 17 - 2 = q + 15 from Nat.add_sub_assoc (by decide : 2 ≤ 17) q, show q + 17 - 3 = q + 14 from Nat.add_sub_assoc (by decide : 3 ≤ 17) q, show q + 17 - 5 = q + 12 from Nat.add_sub_assoc (by decide : 5 ≤ 17) q, show q + 17 - 7 = q + 10 from Nat.add_sub_assoc (by decide : 7 ≤ 17) q, show q + 17 - 8 = q + 9 from Nat.add_sub_assoc (by decide : 8 ≤ 17) q, show q + 17 - 10 = q + 7 from Nat.add_sub_assoc (by decide : 10 ≤ 17) q, show 2 ≤ q + 17 from le_trans (by decide : 2 ≤ 17) (Nat.le_add_left 17 q), show 3 ≤ q + 17 from le_trans (by decide : 3 ≤ 17) (Nat.le_add_left 17 q), show 5 ≤ q + 17 from le_trans (by decide : 5 ≤ 17) (Nat.le_add_left 17 q), show 7 ≤ q + 17 from le_trans (by decide : 7 ≤ 17) (Nat.le_add_left 17 q), show 8 ≤ q + 17 from le_trans (by decide : 8 ≤ 17) (Nat.le_add_left 17 q), show 10 ≤ q + 17 from le_trans (by decide : 10 ≤ 17) (Nat.le_add_left 17 q), show ¬ q + 17 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 14 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 14 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 15 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 15 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 16 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 16 < 17) (Nat.le_add_left 17 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * (X ^ 10 + X ^ 8 - X ^ 7 - 2 * X ^ 5 - X ^ 3 + X ^ 2 + 1) = C 1 * A + C 1 * (A * X ^ 2) - C 1 * (A * X ^ 3) - C 2 * (A * X ^ 5) - C 1 * (A * X ^ 7) + C 1 * (A * X ^ 8) + C 1 * (A * X ^ 10) := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (-X ^ 16 - X ^ 15 - 2 * X ^ 14 - 2 * X ^ 13 + X ^ 11 + 4 * X ^ 10 + 7 * X ^ 9 + 13 * X ^ 8 + 17 * X ^ 7 + 21 * X ^ 6 + 22 * X ^ 5 + 19 * X ^ 4 + 15 * X ^ 3 + 9 * X ^ 2 + 3 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 3 + X ^ 2 * C 9 + X ^ 3 * C 15 + X ^ 4 * C 19 + X ^ 5 * C 22 + X ^ 6 * C 21 + X ^ 7 * C 17 + X ^ 8 * C 13 + X ^ 9 * C 7 + X ^ 10 * C 4 + X ^ 11 * C 1 - X ^ 13 * C 2 - X ^ 14 * C 2 - X ^ 15 * C 1 - X ^ 16 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 + X ^ 8 - X ^ 7 - 2 * X ^ 5 - X ^ 3 + X ^ 2 + 1) =
      -X ^ 16 - X ^ 15 - 2 * X ^ 14 - 2 * X ^ 13 + X ^ 11 + 4 * X ^ 10 + 7 * X ^ 9 + 13 * X ^ 8 + 17 * X ^ 7 + 21 * X ^ 6 + 22 * X ^ 5 + 19 * X ^ 4 + 15 * X ^ 3 + 9 * X ^ 2 + 3 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  rw [gf_den A, gf_num]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 17 with hn | hn
  · linarith [gf_low n hn]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 17 := ⟨n - 17, by omega⟩
    linarith [gf_high q]

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 + X ^ 8 - X ^ 7 - 2 * X ^ 5 - X ^ 3 + X ^ 2 + 1) =
      -X ^ 16 - X ^ 15 - 2 * X ^ 14 - 2 * X ^ 13 + X ^ 11 + 4 * X ^ 10 + 7 * X ^ 9 + 13 * X ^ 8 + 17 * X ^ 7 + 21 * X ^ 6 + 22 * X ^ 5 + 19 * X ^ 4 + 15 * X ^ 3 + 9 * X ^ 2 + 3 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 16 < n → (a n : ℤ) = -a (n - 2) + a (n - 3) + 2 * a (n - 5) + a (n - 7) - a (n - 8) - a (n - 10) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 3, 8, 13, 14, 19, 26, 29, 34, 37, 41, 48, 51, 53, 58, 65, 67, 70, 77, 79, 84, 89, 91, 98, 101, 103, 110, 115, 117, 120, 127, 131, 134, 139, 141, 148, 153, 153, 160, 165, 167, 172, 177, 181, 184, 189, 193, 198, 203, 203] := Count.controls

/-- The step a(n + 60) = a(n) + 252 for n ≥ 7. -/
theorem a_step (n : ℕ) (hn : 7 ≤ n) : a (n + 60) = a n + 252 := Count.a_step n hn

/-- The closed form per residue of n mod 60, for n ≥ 7. -/
theorem a_closed (k : ℕ) :
    a (60 * k + 7) = 252 * k + 29 ∧
    a (60 * k + 8) = 252 * k + 34 ∧
    a (60 * k + 9) = 252 * k + 37 ∧
    a (60 * k + 10) = 252 * k + 41 ∧
    a (60 * k + 11) = 252 * k + 48 ∧
    a (60 * k + 12) = 252 * k + 51 ∧
    a (60 * k + 13) = 252 * k + 53 ∧
    a (60 * k + 14) = 252 * k + 58 ∧
    a (60 * k + 15) = 252 * k + 65 ∧
    a (60 * k + 16) = 252 * k + 67 ∧
    a (60 * k + 17) = 252 * k + 70 ∧
    a (60 * k + 18) = 252 * k + 77 ∧
    a (60 * k + 19) = 252 * k + 79 ∧
    a (60 * k + 20) = 252 * k + 84 ∧
    a (60 * k + 21) = 252 * k + 89 ∧
    a (60 * k + 22) = 252 * k + 91 ∧
    a (60 * k + 23) = 252 * k + 98 ∧
    a (60 * k + 24) = 252 * k + 101 ∧
    a (60 * k + 25) = 252 * k + 103 ∧
    a (60 * k + 26) = 252 * k + 110 ∧
    a (60 * k + 27) = 252 * k + 115 ∧
    a (60 * k + 28) = 252 * k + 117 ∧
    a (60 * k + 29) = 252 * k + 120 ∧
    a (60 * k + 30) = 252 * k + 127 ∧
    a (60 * k + 31) = 252 * k + 131 ∧
    a (60 * k + 32) = 252 * k + 134 ∧
    a (60 * k + 33) = 252 * k + 139 ∧
    a (60 * k + 34) = 252 * k + 141 ∧
    a (60 * k + 35) = 252 * k + 148 ∧
    a (60 * k + 36) = 252 * k + 153 ∧
    a (60 * k + 37) = 252 * k + 153 ∧
    a (60 * k + 38) = 252 * k + 160 ∧
    a (60 * k + 39) = 252 * k + 165 ∧
    a (60 * k + 40) = 252 * k + 167 ∧
    a (60 * k + 41) = 252 * k + 172 ∧
    a (60 * k + 42) = 252 * k + 177 ∧
    a (60 * k + 43) = 252 * k + 181 ∧
    a (60 * k + 44) = 252 * k + 184 ∧
    a (60 * k + 45) = 252 * k + 189 ∧
    a (60 * k + 46) = 252 * k + 193 ∧
    a (60 * k + 47) = 252 * k + 198 ∧
    a (60 * k + 48) = 252 * k + 203 ∧
    a (60 * k + 49) = 252 * k + 203 ∧
    a (60 * k + 50) = 252 * k + 210 ∧
    a (60 * k + 51) = 252 * k + 217 ∧
    a (60 * k + 52) = 252 * k + 217 ∧
    a (60 * k + 53) = 252 * k + 222 ∧
    a (60 * k + 54) = 252 * k + 227 ∧
    a (60 * k + 55) = 252 * k + 231 ∧
    a (60 * k + 56) = 252 * k + 236 ∧
    a (60 * k + 57) = 252 * k + 239 ∧
    a (60 * k + 58) = 252 * k + 243 ∧
    a (60 * k + 59) = 252 * k + 248 ∧
    a (60 * k + 60) = 252 * k + 253 ∧
    a (60 * k + 61) = 252 * k + 255 ∧
    a (60 * k + 62) = 252 * k + 260 ∧
    a (60 * k + 63) = 252 * k + 267 ∧
    a (60 * k + 64) = 252 * k + 267 ∧
    a (60 * k + 65) = 252 * k + 272 ∧
    a (60 * k + 66) = 252 * k + 279 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 + X ^ 8 - X ^ 7 - 2 * X ^ 5 - X ^ 3 + X ^ 2 + 1) =
      -X ^ 16 - X ^ 15 - 2 * X ^ 14 - 2 * X ^ 13 + X ^ 11 + 4 * X ^ 10 + 7 * X ^ 9 + 13 * X ^ 8 + 17 * X ^ 7 + 21 * X ^ 6 + 22 * X ^ 5 + 19 * X ^ 4 + 15 * X ^ 3 + 9 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = -a (n - 2) + a (n - 3) + 2 * a (n - 5) + a (n - 7) - a (n - 8) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a310289

theorem OMA.solution : type_of% @OMA.S_oeis_a310289.main :=
  OMA.S_oeis_a310289.conjecture
