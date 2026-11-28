import OMAStatements.S_oeis_a315135

namespace OMA.S_oeis_a315135






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 7

/-- Field k of the B-bit fields packed in the natural number T, as stored. The table accessors call
the kernel's natural number primitives directly: through the operators' type-class instances the
kernel decisions take more memory. -/
def tgetN (T B k : ℕ) : ℕ := Nat.mod (Nat.shiftRight T (Nat.mul B k)) (Nat.pow 2 B)

/-- Field k of the B-bit fields packed in T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := Int.subNatNat (tgetN T B k) off

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 504213650617
  | 1 => 435512064936
  | 2 => 508812700311
  | 3 => 582094461592
  | 4 => 517973051511
  | 5 => 513392875911
  | 6 => 586674637192
  | _ => 0

/-- The potential t is Ac t * x + Bc t * y + Cc s t at (x, y, s) (packed tables). -/
def Ac (i : Fin 10) : ℤ := tget 444691290230 4 8 i.val

def Bc (i : Fin 10) : ℤ := tget 673447363655 4 8 i.val

def Cc (s : Fin 7) (i : Fin 10) : ℤ := tget (CcT s.val) 4 8 i.val

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
def R0N (s : Fin 7) : ℕ := tgetN 107378823 4 s.val

def R0c (s : Fin 7) : ℤ := (R0N s : ℤ)

/-- The pairs (class s, potential t) and the classes whose rule, far, side and near checks are made;
the others follow by the symmetry sig. -/
def repB (s : Fin 7) (t : Fin 10) : Bool := decide (tgetN 35741691443208519679 1 (s.val * 10 + t.val) = 1)

def repC (s : Fin 7) : Bool := decide (tgetN 83 1 s.val = 1)

/-- A symmetry of order 2 of the graph that fixes v0 and permutes the potentials:
(x, y, s) ↦ ((-1) x + 0 y + tauX s, 0 x + (-1) y + tauY s, piS s), and potential t goes to rhoP t. -/
def piS (s : Fin 7) : Fin 7 := ⟨tgetN 1724499 3 s.val % 7, Nat.mod_lt _ (by norm_num)⟩

def tauX (s : Fin 7) : ℤ := tget 142051192 4 8 s.val

def tauY (s : Fin 7) : ℤ := tget 143169945 4 8 s.val

def rhoP (t : Fin 10) : Fin 10 := ⟨tgetN 288317081445 4 t.val % 10, Nat.mod_lt _ (by norm_num)⟩

def sig (v : V) : V :=
  ((-1) * v.1 + 0 * v.2.1 + tauX v.2.2, 0 * v.1 + (-1) * v.2.1 + tauY v.2.2, piS v.2.2)

/-- The change of the potential j along the edge e. -/
def dl (e : Fin 7 × Fin 7 × ℤ × ℤ) (j : Fin 10) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

/-- Along an edge e the potential j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 7 × Fin 7 × ℤ × ℤ) (j : Fin 10) :
    pot (x + e.2.2.1, y + e.2.2.2, e.2.1) j = pot (x, y, e.1) j + dl e j := by
  simp only [pot, dl]
  ring

theorem pair_of {a f b : ℤ} (hl : a ≤ f) (hf : f = b) : a ≤ b + 0 := by omega

theorem bound_of {r f b : ℤ} (hr : r < f) (hf : f = b) : r + 1 ≤ b := by omega

theorem not_pair2 {a b : ℤ} (h : ¬ a ≤ b + (-2)) : b ≤ a + 1 := by omega

/-- Three facts pot a_k ≤ pot b_k + t_k and a bound r ≤ pot i0 at (x, y, s), with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas (x y : ℤ) (s : Fin 7) (a1 b1 a2 b2 a3 b3 i0 : Fin 10) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
  ⟨(tget 825496353861188786895093980803451513349660999945 4 0 (t.val * 4 + k.val)).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The slot k of t holds another potential. -/
def real (t : Fin 10) (k : Fin 4) : Bool := decide (nb t k ≠ t)

/-- The potential t is a facet: a slot on each side cannot both come within 1 of t beyond R0c. -/
def facetB (t : Fin 10) : Bool := decide (tget 891 1 0 t.val = 1)

/-- The potential j is neither t nor in a slot of t. -/
def nonadj (t j : Fin 10) : Bool :=
  decide (j ≠ t) && decide (j ≠ nb t 0) && decide (j ≠ nb t 1) && decide (j ≠ nb t 2) && decide (j ≠ nb t 3)

/-- Certificates of the far facts, the same for every class: for maximal potential t and a potential
j that is not a neighbor of t, the fields k1, k2, m1, m2, m0, mj of entry t * 10 + j give the facts
pot k1 ≤ pot t, pot k2 ≤ pot t, R0c s + 1 ≤ pot t and pot t ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fd (t j : Fin 10) (f : ℕ) : ℤ := tget 634958411437995962523809259442763501260588514817751222485153457003724254970795360238039282375541984748249332199434360330957211586282682351541898712371913708440174018354224502248077502775193395370213030298163102944299090987752313978180014873148277121221747278986273250068693378753883466925295660609817126799461374619519804112162367252010504310425186531700678677846469898205348041178423549233060140523604821642515231520518567461940712033763733388483350242107803435354166069514735935434733580657544482408884546126076717310448281930478452083057407763633119567618296455033678781685792350168022493921629744988137079232093109641825821562397592299943686101495395333655284257889687715339180761431427471369609978252643700985306779617707439082595949608306490859724680362437404955991121689350058192680040602210501005418631884374218773914594784580064459803062222018723889427784221853712663511840366452697194216047120 5 16 ((t.val * 10 + j.val) * 6 + f)

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
def farC (s : Fin 7) (t j : Fin 10) : Bool :=
  decide (0 < fd t j 2 * (Cc s (fk1 t j) - Cc s t - 0) + fd t j 3 * (Cc s (fk2 t j) - Cc s t - 0) +
    fd t j 5 * (Cc s t - Cc s j - 1) + fd t j 4 * (R0c s + 1 - Cc s t))

/-- The far certificates of the maximal potential t are valid. -/
def farsOK (t : Fin 10) : Bool :=
  (List.finRange 10).all fun j => !nonadj t j || (farXY t j && (List.finRange 7).all fun s => !repB s t || farC s t j)

/-- Beyond F = R0c s, a potential that is not a neighbor of a maximal potential t has slack at least 2. -/
theorem far (s : Fin 7) (t j : Fin 10) (hxy : farXY t j = true) (hc0 : farC s t j = true) (x y : ℤ)
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
def sd (t : Fin 10) (i f : ℕ) : ℤ := tget 5530367004832347462959632856609406771244068697897096301452968286888202787698845352887198647725599754278732522181821120718401346654854158178811011795139616922948509471147255340504582126210069182446783470535938074693481846760137187877233672021420195575733780261515630372170563863108370038040249659710992 5 16 ((t.val * 4 + i) * 5 + f)

def sk (t : Fin 10) (i : ℕ) : Fin 10 := ⟨(sd t i 0).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

def sideXY (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 ≤ sd t i 1 ∧ 0 ≤ sd t i 2 ∧ 0 ≤ sd t i 3 ∧ 0 ≤ sd t i 4 ∧
    sd t i 1 * (Ac (sk t i) - Ac t) + sd t i 2 * (Ac t - Ac (nb t kl)) + sd t i 3 * (Ac t - Ac (nb t kr)) -
      sd t i 4 * Ac t = 0 ∧
    sd t i 1 * (Bc (sk t i) - Bc t) + sd t i 2 * (Bc t - Bc (nb t kl)) + sd t i 3 * (Bc t - Bc (nb t kr)) -
      sd t i 4 * Bc t = 0)

def sideC (s : Fin 7) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 < sd t i 1 * (Cc s (sk t i) - Cc s t - 0) + sd t i 2 * (Cc s t - Cc s (nb t kl) - 1) +
    sd t i 3 * (Cc s t - Cc s (nb t kr) - 1) + sd t i 4 * (R0c s + 1 - Cc s t))

def sideOK (t : Fin 10) (kl kr : Fin 4) (i : ℕ) : Bool :=
  !(real t kl && real t kr) || (sideXY t kl kr i && (List.finRange 7).all fun s => !repB s t || sideC s t kl kr i)

/-- All side certificates are valid. -/
def sidesOK : Bool :=
  (List.finRange 10).all fun t =>
    !facetB t || (sideOK t 0 2 0 && sideOK t 0 3 1 && sideOK t 1 2 2 && sideOK t 1 3 3)

/-- Beyond F = R0c s, a facet t has no slot on each side within 1 of it. -/
theorem side (s : Fin 7) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) (hxy : sideXY t kl kr i = true)
    (hc0 : sideC s t kl kr i = true) (x y : ℤ) (hL : pot (x, y, s) t ≤ pot (x, y, s) (nb t kl) + 1)
    (hR : pot (x, y, s) t ≤ pot (x, y, s) (nb t kr) + 1) (h : F (x, y, s) = pot (x, y, s) t)
    (hF : R0c s < F (x, y, s)) : False := by
  have q := of_decide_eq_true hxy
  exact farkas x y s (sk t i) t t (nb t kl) t (nb t kr) t 0 1 1 (R0c s + 1) (sd t i 1) (sd t i 2) (sd t i 3)
    (sd t i 4) ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, of_decide_eq_true hc0⟩
    (pair_of (le_F _ _) h) hL hR (bound_of hF h)

/-- The edges of E by position p: source and target class, cell offset, and the potential changes dl
(entry p * 10 + j). -/
def srcv (p : ℕ) : ℕ := tgetN 278158583429399812974406168510464 3 p

def tgtv (p : ℕ) : ℕ := tgetN 231060087669360036377568907127049 3 p

def tgtF (p : ℕ) : Fin 7 := ⟨tgtv p % 7, Nat.mod_lt _ (by norm_num)⟩

def dxv (p : ℕ) : ℤ := tget 11806278287348021588372236712720552113506183 4 8 p

def dyv (p : ℕ) : ℤ := tget 11893732101777661461690795365709595265169288 4 8 p

/-- dlv p j + 8, as a natural number (the rule checks compare naturals). -/
def dlvN (p : ℕ) (j : Fin 10) : ℕ := tgetN 14197655377093742691302043070563288417295116738886569904970919525815818141358812840211726777985611195355802620263817314307148642095716903843893675036156281927066885236740674575453626929892858107487952256859445608327995623281675822390201808900952256106809116238765654848513211284955614881950763769302599402860410090838360280870187066356245832587866038632196544828905020574782027295123747726443008989951033212262323851933252211313178505 4 (p * 10 + j.val)

def dlv (p : ℕ) (j : Fin 10) : ℤ := (dlvN p j : ℤ) - 8

/-- The edge tables agree with the edges of a list l from position p on, every edge moves, and every
potential changes by at most one along every edge. -/
def dlOKl : List (Fin 7 × Fin 7 × ℤ × ℤ) → ℕ → Bool
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

/-- Descent rules beyond F = R0c s, one word of 27 bits per class s, potential t and admissible
pattern (c0, c1, c2, c3), at position POFF t + (the rank of the pattern among the admissible patterns
of t): kind 0 names an edge by its position in E; kind 1 is a Farkas certificate: multipliers m1, m2,
m3 of the slot facts of slots k1, k2, k3 (slack ≥ c for a multiplier ≥ 0, slack ≤ c for a negative
multiplier, where c ≤ 1) and l0 ≥ 0 of the bound R0c s + 1 ≤ pot t, whose x and y parts cancel and
whose constants add up to a positive number; kind 2 is a line of slot k1 without lattice points
(modulus l0). Fields from bit 0: kind (2 bits), edge position (6), k1, k2, k3 (2 each), m1, m2, m3
(4 each, stored as value + 8), l0 (1). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 805885129797919266737425552067001170741463068712931269563320278261808255517098326154110329384713637359952222779145678702906876081668814331494254729656457955392654306877033671782582604841018663978582535560025836520590226456415256681025262168242620728428136071194626938478460161423585748163453783376358210168318288307476718460816183021795008021297245464102290245877802979632674598633344411545372722789836088140424247406609850481815965675316894617734222131030322173608948685865471899323496885094902618134035340607450383188317212451664484800506385907460165497229537845962074791038653921656951009253915626565216497333804947710183933491844876845513953835910846938605551620
  | 1 => 805885580231246357523436901235094133598287207616103867242208352575252281484030942052164132256945425531973394890159340154343419310418803040196242943089638254943727452977366140569713226457997336186413230968575451080352084989524920717649696886428936533110975693129482374575711433735539513045182102062005861816246967233050853221688297840066952334550929019606766673613405210706884918698783294796127293769262837186864814085388875422346119536522011442130847477327723696821508651057766104523658068201946228452178151421802985619935853894187600960569934179622100521694643396375008956747564838161891393037610353296880086323786950848675389231083765095096600419565680377049776156
  | 2 => 805885039711253848580211280278652926783727583829037532733646841217883438556037547589925990259672575127381771139981508874105338209602371121047099798202431635984983886155419943943643333598135067789673630931405236613056338413298084563284161448432672632098355900434151763393620751147649071319324895497655879129982045319291359764531164164680716310450341857060486795727486905168314664016366867274998943106788204345197450018618140541535744779084091499106437741515140665118938590917449863614543674397321954116837843546937900811585092587876966085888406041901115585382430931332680860894989161645921852396348625979132817768579034880980587334858347344846814024150464265927655424
  | 3 => 805885039711253848580211280278652926783727583829037532733646841217883438556037547589925990259672575127381771139981508874105338209602371121047099798202431635984983886155419943943643333598135067789673630931405236613056338413298084563284161448432672632098355900434151763393620751147649071319324895497655879129982045319291359764531164164680716310450341857060486795727486905168314664016366867274998943106788204345197450018618140541535744779084091499106437741515140665118938590917449863614543674397321954116837843546937900811585092587876966085888406041901115585382430931332680860894989161645921852396348625979132817768579034880980587334858347344846814024150464265927655424
  | 4 => 805886751357896793567112416565266167340450820989376377359303622330198932642963734610103312153714745949391582075084137879351566404382624374181784954703992076631866898846583162842535787080812116130877734684172274882661843069758126843075576389498719220657552814835396113443130663776166696196312229747079947963362628859918613536592003519968232189508595352712675332257514160411677466601968149857883548813163881117789859912170686330187406184363467619776494855213416540519636925046862900222404876174156318389061967473603889892098423629716871847169319835823583117657679255567922278324142141122491259646140616287535767400152764560350835463631414591112882702203778162866913356
  | 5 => 805885039711253848580211280278652926783727583829037532733646841217883438556037547589925990259672575127381771139981508874105338209602371121047099798202431635984983886155419943943643333598135067789673630931405236613056338413298084563284161448432672632098355900434151763393620751147649071319324895497655879129982045319291359764531164164680716310450341857060486795727486905168314664016366867274998943106788204345197450018618140541535744779084091499106437741515140665118938590917449863614543674397321954116837843546937900811585092587876966085888406041901115585382430931332680860894989161645921852396348625979132817768579034880980587334858347344846814024150464265927655424
  | 6 => 805885039711253848580211280278652926783727583829037532733646841217883438556037547589925990259672575127381771139981508874105338209602371121047099798202431635984983886155419943943643333598135067789673630931405236613056338413298084563284161448432672632098355900434151763393620751147649071319324895497655879129982045319291359764531164164680717968529613304202320345041416371298142703766381012928810198810721177154454029698392498301850208054358725386449101003399292560175322413284705121495950571892647550534550379602674026468631671307307729775824905149569781148763491819152858269940892258520599723202299450133783463385540062235486459679924816026325789133961725529597018244
  | _ => 0

def rword (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ :=
  tgetN (ruleT s.val) 27 (Nat.add (tgetN 714987739920271147648 7 t.val) (tgetN 322575460059966508561762482396552517479486814299071266810360780372062002754845725830683566477695253398671554513958221213324459313525799668549103257387972026759114847901380699003422482732070807074929223638249001645737082905034475868373300520664494997321538980095067865825906471861739006931298263628310825496918672605896339769482979213369308015163741992711795236107690832059462021889797633286906243267521934830485149286592246179652996084679410268020376458300612335680982136111240204889483490560559983918173470258036667756435945852040587190637916167084564484840761856911735100678119827207060688470307825399583479447303917839643032474856310715511837478674280493706012681460654966565935049243794914975785114412988105593907889672455287186172816558281912331449970133217430980494246929653778651061489466239176772350688254590180397501567831135567060096439153642846524933576615355833629854269719118787510683041792 4
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul t.val 81) c0) (Nat.mul 3 c1)) (Nat.mul 9 c2)) (Nat.mul 27 c3))))

/-- The field of B bits from bit o of the word w. -/
def fld (w o B : ℕ) : ℕ := Nat.mod (Nat.shiftRight w o) (Nat.pow 2 B)

def rk (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 0 2

def re (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 2 6

def rsl (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (i : ℕ) : Fin 4 :=
  ⟨fld (rword s t c0 c1 c2 c3) (Nat.add 8 (Nat.mul 2 i)) 2 % 4, Nat.mod_lt _ (by norm_num)⟩

def rm (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (i : ℕ) : ℤ := Int.subNatNat (fld (rword s t c0 c1 c2 c3) (Nat.add 14 (Nat.mul 4 i)) 4) 8

def rl0 (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℤ := Int.ofNat (fld (rword s t c0 c1 c2 c3) 26 1)

/-- The class of slot k in the pattern (c0, c1, c2, c3). -/
def cv (c0 c1 c2 c3 : ℕ) (k : Fin 4) : ℕ := if k.val = 0 then c0 else if k.val = 1 then c1 else if k.val = 2 then c2 else c3

/-- The slack of the slot k below t in x and y, and its constant: pot t - pot (nb t k) at (x, y, s)
is dA t k * x + dB t k * y + dC s t k. -/
def dA (t : Fin 10) (k : Fin 4) : ℤ := Ac t - Ac (nb t k)

def dB (t : Fin 10) (k : Fin 4) : ℤ := Bc t - Bc (nb t k)

def dC (s : Fin 7) (t : Fin 10) (k : Fin 4) : ℤ := Cc s t - Cc s (nb t k)

/-- Kind 0: the edge at position re descends from class s for this pattern. -/
def ok0 (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  Nat.blt (re s t c0 c1 c2 c3) 36 && Nat.beq (srcv (re s t c0 c1 c2 c3)) s.val && Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) t) 1) 8 &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 0)) 1) (Nat.add c0 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 1)) 1) (Nat.add c1 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 2)) 1) (Nat.add c2 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 3)) 1) (Nat.add c3 8)

/-- Kind 1: the Farkas certificate over the slot facts and the bound is valid. -/
def ok1 (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
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
def ok2 (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  decide (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) ≤ 1 ∧ rl0 s t c0 c1 c2 c3 ∣ dA t (rsl s t c0 c1 c2 c3 0) ∧ rl0 s t c0 c1 c2 c3 ∣ dB t (rsl s t c0 c1 c2 c3 0) ∧
    ¬ rl0 s t c0 c1 c2 c3 ∣ (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 0))

def ruleOK (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  if rk s t c0 c1 c2 c3 = 0 then ok0 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 1 then ok1 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 2 then ok2 s t c0 c1 c2 c3 else false

/-- Every pattern of slack classes that can occur at the maximal potential t has a valid rule. -/
def rulesOK (t : Fin 10) : Bool :=
  (List.range 3).all fun c0 => (List.range 3).all fun c1 => (List.range 3).all fun c2 => (List.range 3).all fun c3 =>
    !adm t c0 c1 c2 c3 || (List.finRange 7).all fun s => !repB s t || ruleOK s t c0 c1 c2 c3

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

theorem far_ok (s : Fin 7) (t j : Fin 10) (hrep : repB s t = true) (hjt : j ≠ t) (hjn : ∀ k, j ≠ nb t k) :
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

theorem side_ok (s : Fin 7) (t : Fin 10) (kl kr : Fin 4) (i : ℕ) (hrep : repB s t = true) (hsp : facetB t = true)
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

theorem rule_ok (s : Fin 7) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (hrep : repB s t = true) (h0 : c0 < 3) (h1 : c1 < 3) (h2 : c2 < 3) (h3 : c3 < 3)
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

theorem dlOKl_spec : ∀ (l : List (Fin 7 × Fin 7 × ℤ × ℤ)) (p : ℕ), dlOKl l p = true →
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

theorem adj_of_mem (e : Fin 7 × Fin 7 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
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
theorem farkas_slot (x y : ℤ) (s : Fin 7) (t : Fin 10) (k1 k2 k3 : Fin 4) (c1 c2 c3 m1 m2 m3 l0 : ℤ)
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
theorem far_step (s : Fin 7) (t : Fin 10) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) t)
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
def sym_ok_dec : PLift ((∀ e ∈ E, (piS e.1, piS e.2.1, (-1) * e.2.2.1 + 0 * e.2.2.2 + tauX e.2.1 - tauX e.1,
      0 * e.2.2.1 + (-1) * e.2.2.2 + tauY e.2.1 - tauY e.1) ∈ E) ∧
    (∀ s, piS (piS s) = s ∧ (-1) * tauX s + 0 * tauY s + tauX (piS s) = 0 ∧
      0 * tauX s + (-1) * tauY s + tauY (piS s) = 0 ∧ R0c (piS s) = R0c s ∧
      (repC s = true ∨ repC (piS s) = true)) ∧
    (∀ t, rhoP (rhoP t) = t ∧ Ac (rhoP t) * (-1) + Bc (rhoP t) * 0 = Ac t ∧
      Ac (rhoP t) * 0 + Bc (rhoP t) * (-1) = Bc t) ∧
    (∀ s t, Ac (rhoP t) * tauX s + Bc (rhoP t) * tauY s + Cc (piS s) (rhoP t) = Cc s t ∧
      (repB s t = true ∨ repB (piS s) (rhoP t) = true)) ∧
    sig v0 = v0) := ⟨by
  decide +kernel⟩

theorem sym_ok : (∀ e ∈ E, (piS e.1, piS e.2.1, (-1) * e.2.2.1 + 0 * e.2.2.2 + tauX e.2.1 - tauX e.1,
      0 * e.2.2.1 + (-1) * e.2.2.2 + tauY e.2.1 - tauY e.1) ∈ E) ∧
    (∀ s, piS (piS s) = s ∧ (-1) * tauX s + 0 * tauY s + tauX (piS s) = 0 ∧
      0 * tauX s + (-1) * tauY s + tauY (piS s) = 0 ∧ R0c (piS s) = R0c s ∧
      (repC s = true ∨ repC (piS s) = true)) ∧
    (∀ t, rhoP (rhoP t) = t ∧ Ac (rhoP t) * (-1) + Bc (rhoP t) * 0 = Ac t ∧
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
theorem farkas_ub (x y : ℤ) (s : Fin 7) (a1 a2 a3 : Fin 10) (t l1 l2 l3 px py q lq : ℤ)
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
def BXn (s : Fin 7) : ℕ := tgetN 898851 3 s.val

def BYn (s : Fin 7) : ℕ := tgetN 299666 3 s.val

theorem nb_c0 : ∀ s : Fin 7, 0 < 1 * (Cc s 0 - (R0c s)) + 1 * (Cc s 9 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 4 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c0 : ∀ s : Fin 7, 0 < 1 * (Cc s 3 - (3)) + 4 * (Cc s 9 - (3)) + 0 * (Cc s 0 - (3)) + 7 * (3) := by
  decide +kernel

theorem nb_c1 : ∀ s : Fin 7, 0 < 1 * (Cc s 4 - (R0c s)) + 1 * (Cc s 5 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 4 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c1 : ∀ s : Fin 7, 0 < 4 * (Cc s 4 - (3)) + 1 * (Cc s 8 - (3)) + 0 * (Cc s 0 - (3)) + 7 * (3) := by
  decide +kernel

theorem nb_c2 : ∀ s : Fin 7, 0 < 1 * (Cc s 2 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 4 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c2 : ∀ s : Fin 7, 0 < 2 * (Cc s 3 - (3)) + 1 * (Cc s 9 - (3)) + 0 * (Cc s 0 - (3)) + 7 * (2) := by
  decide +kernel

theorem nb_c3 : ∀ s : Fin 7, 0 < 1 * (Cc s 7 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 4 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c3 : ∀ s : Fin 7, 0 < 1 * (Cc s 7 - (3)) + 0 * (Cc s 0 - (3)) + 0 * (Cc s 0 - (3)) + 4 * (2) := by
  decide +kernel

theorem nn_c : ∀ s : Fin 7, 0 < 2 * (Cc s 4 - (-1)) + 2 * (Cc s 9 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * (0) := by
  decide +kernel

/-- Every vertex of class s with F at most R0c s lies in the near box of class s. -/
theorem near_box (x y : ℤ) (s : Fin 7) (hF : F (x, y, s) ≤ R0c s) :
    -(BXn s : ℤ) ≤ x ∧ x ≤ BXn s ∧ -(BYn s : ℤ) ≤ y ∧ y ≤ BYn s := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 9 0 (R0c s) 1 1 0 (1) (0) ((BXn s : ℤ) + 1) 4 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 5 0 (R0c s) 1 1 0 (-1) (0) ((BXn s : ℤ) + 1) 4 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 0 0 (R0c s) 1 0 0 (0) (1) ((BYn s : ℤ) + 1) 4 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 7 0 0 (R0c s) 1 0 0 (0) (-1) ((BYn s : ℤ) + 1) 4 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c3 s⟩ (u _) (u _) (u _) (by omega)

/-- Every vertex with F at most 3 lies in the cells |x| ≤ 2, |y| ≤ 1. -/
theorem small_box (x y : ℤ) (s : Fin 7) (hF : F (x, y, s) ≤ 3) :
    -2 ≤ x ∧ x ≤ 2 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 3 9 0 (3) 1 4 0 (1) (0) (3) 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 8 0 (3) 4 1 0 (-1) (0) (3) 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 9 0 (3) 2 1 0 (0) (1) (2) 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 7 0 0 (3) 1 0 0 (0) (-1) (2) 4 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 4 9 0 (-1) 2 2 0 (0) (0) (0) 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nn_c s⟩ (u _) (u _) (u _) (by norm_num)

/-- The vertices near v0 where the graph distance is not the largest potential, with the distance. -/
def O : List (V × ℤ) :=
  [((0, 0, 6), 0),
    ((0, 0, 3), 1),
    ((0, 1, 0), 1)]

/-- The cells (x, y) of the vertices of O. -/
def obox (x y : ℤ) : Bool := decide (0 ≤ x ∧ x ≤ 0 ∧ 0 ≤ y ∧ y ≤ 1)

/-- The distance formula: the value listed in O, and the largest potential off O. -/
def fv (v : V) : ℤ :=
  if obox v.1 v.2.1 then ((O.find? fun o => decide (o.1 = v)).map Prod.snd).getD (F v) else F v

theorem fv_out (x y : ℤ) (s : Fin 7) (h : ¬ obox x y = true) : fv (x, y, s) = F (x, y, s) := by
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
def apN (i : Fin 10) : ℕ := tgetN 336384 3 i.val

def amN (i : Fin 10) : ℕ := tgetN 285212682 3 i.val

def bpN (i : Fin 10) : ℕ := tgetN 210796544 3 i.val

def bmN (i : Fin 10) : ℕ := tgetN 6433 3 i.val

def kpN (s : Fin 7) (i : Fin 10) : ℕ := tgetN 607084038529806667401159270603927663191560830012386447134999060411996792329286487273 4 (Nat.add (Nat.mul s.val 10) i.val)

def kmN (s : Fin 7) (i : Fin 10) : ℕ := tgetN 9232450651174660389843708637172653456717646654642654810458683549932489893693554688 4 (Nat.add (Nat.mul s.val 10) i.val)

def pqOK : Bool :=
  (List.finRange 10).all fun i => decide ((apN i : ℤ) - amN i = Ac i ∧ (bpN i : ℤ) - bmN i = Bc i) &&
    (List.finRange 7).all fun s => decide ((kpN s i : ℤ) - kmN s i = Cc s i - Ac i * BXn s - Bc i * BYn s)

def pq_ok_dec : PLift (pqOK = true) := ⟨by
  decide +kernel⟩

theorem pq_ok : pqOK = true := pq_ok_dec.down

def potP (s : Fin 7) (a b : ℕ) (i : Fin 10) : ℕ :=
  Nat.add (Nat.add (Nat.mul (apN i) a) (Nat.mul (bpN i) b)) (kpN s i)

def potQ (s : Fin 7) (a b : ℕ) (i : Fin 10) : ℕ :=
  Nat.add (Nat.add (Nat.mul (amN i) a) (Nat.mul (bmN i) b)) (kmN s i)

theorem potPQ_val (s : Fin 7) (a b : ℕ) (i : Fin 10) :
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
def FP (s : Fin 7) (a b : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax ((potP s a b 0, potQ s a b 0)) (potP s a b 1, potQ s a b 1)) (potP s a b 2, potQ s a b 2)) (potP s a b 3, potQ s a b 3)) (potP s a b 4, potQ s a b 4)) (potP s a b 5, potQ s a b 5)) (potP s a b 6, potQ s a b 6)) (potP s a b 7, potQ s a b 7)) (potP s a b 8, potQ s a b 8)) (potP s a b 9, potQ s a b 9)

def FPn (s : Fin 7) (a b p : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax ((Nat.add (potP s a b 0) (dlvN p 0), Nat.add (potQ s a b 0) 8)) (Nat.add (potP s a b 1) (dlvN p 1), Nat.add (potQ s a b 1) 8)) (Nat.add (potP s a b 2) (dlvN p 2), Nat.add (potQ s a b 2) 8)) (Nat.add (potP s a b 3) (dlvN p 3), Nat.add (potQ s a b 3) 8)) (Nat.add (potP s a b 4) (dlvN p 4), Nat.add (potQ s a b 4) 8)) (Nat.add (potP s a b 5) (dlvN p 5), Nat.add (potQ s a b 5) 8)) (Nat.add (potP s a b 6) (dlvN p 6), Nat.add (potQ s a b 6) 8)) (Nat.add (potP s a b 7) (dlvN p 7), Nat.add (potQ s a b 7) 8)) (Nat.add (potP s a b 8) (dlvN p 8), Nat.add (potQ s a b 8) 8)) (Nat.add (potP s a b 9) (dlvN p 9), Nat.add (potQ s a b 9) 8)

theorem FP_val (s : Fin 7) (a b : ℕ) :
    ((FP s a b).1 : ℤ) - (FP s a b).2 = F ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) := by
  simp only [FP, F, pmax_val, potPQ_val]

theorem FPn_val (s : Fin 7) (a b p : ℕ) (hp : p < 36) (hs : srcv p = s.val) :
    ((FPn s a b p).1 : ℤ) - (FPn s a b p).2 = F ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  obtain ⟨e, -, h1, h2, h3, h4, h5⟩ := edge_of p hp
  have hs' : e.1 = s := Fin.ext (h1.trans hs)
  have ht' : e.2.1 = tgtF p := Fin.ext (by
    show e.2.1.val = tgtv p % 7
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
def fvN (s : Fin 7) (a b : ℕ) : ℤ :=
  if obox ((a : ℤ) - BXn s) ((b : ℤ) - BYn s) then fv ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s)
  else Int.subNatNat (FP s a b).1 (FP s a b).2

def fvNn (s : Fin 7) (a b p : ℕ) : ℤ :=
  if obox ((a : ℤ) - BXn s + dxv p) ((b : ℤ) - BYn s + dyv p) then
    fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p)
  else Int.subNatNat (FPn s a b p).1 (FPn s a b p).2

theorem fvN_eq (s : Fin 7) (a b : ℕ) : fvN s a b = fv ((a : ℤ) - BXn s, (b : ℤ) - BYn s, s) := by
  unfold fvN
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FP_val, Int.subNatNat_eq_coe]

theorem fvNn_eq (s : Fin 7) (a b p : ℕ) (hp : p < 36) (hs : srcv p = s.val) :
    fvNn s a b p = fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  unfold fvNn
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FPn_val s a b p hp hs, Int.subNatNat_eq_coe]

/-- For each class s and each cell of its near box with F at most R0c s, other than v0, the position
in E of an edge along which fv decreases. -/
def nearT (s : ℕ) : ℕ :=
  match s with
  | 0 => 47890485697357415551050121996543773791804287057399808
  | 1 => 2190495797301091209675086126353578882605619683116101446463874726912000
  | 2 => 0
  | 3 => 0
  | 4 => 1448801571783327471309561791699
  | 5 => 0
  | 6 => 664773759615730443943729605639669824
  | _ => 0

def nearE (s : Fin 7) (a b : ℕ) : ℕ := tgetN (nearT s.val) 6 (a * (2 * BYn s + 1) + b)

/-- The near check of class s. -/
def nearOK (s : Fin 7) : Bool :=
  !repC s || (List.range (2 * BXn s + 1)).all fun a => (List.range (2 * BYn s + 1)).all fun b =>
    Nat.blt (Nat.add (R0N s) (FP s a b).2) (FP s a b).1 ||
      (Nat.beq a (BXn s) && Nat.beq b (BYn s) && Nat.beq s.val 6) ||
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

theorem nearOK_all (k : Fin 7) : nearOK k = true := by
  fin_cases k
  exacts [nearOK0_dec.down, nearOK1_dec.down, nearOK2_dec.down, nearOK3_dec.down, nearOK4_dec.down, nearOK5_dec.down, nearOK6_dec.down]

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
    have hs0 : s = 6 := Fin.ext h4
    rw [hx0, hy0, hs0]
    rfl
  · rw [fvNn_eq _ _ _ _ hlt hs, fvN_eq, ex, ey] at hfe
    obtain ⟨e, hmem, h1, h2, h3, h4, -⟩ := edge_of _ hlt
    have ha := adj_of_mem e hmem x y
    have hs' : e.1 = s := Fin.ext (h1.trans hs)
    have ht' : e.2.1 = tgtF (nearE s (x + BXn s).toNat (y + BYn s).toNat) := Fin.ext (by
      show e.2.1.val = tgtv (nearE s (x + BXn s).toNat (y + BYn s).toNat) % 7
      rw [← h2, Nat.mod_eq_of_lt e.2.1.isLt])
    rw [hs', ht', h3, h4] at ha
    exact ⟨_, ha, hfe⟩

def sym_O_dec : PLift (∀ o ∈ O, (∃ o' ∈ O, o'.1 = sig o.1) ∧ fv (sig o.1) = fv o.1) := ⟨by
  decide +kernel⟩

theorem sym_O : ∀ o ∈ O, (∃ o' ∈ O, o'.1 = sig o.1) ∧ fv (sig o.1) = fv o.1 := sym_O_dec.down

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
  (Finset.range 5 ×ˢ Finset.range 3 ×ˢ (Finset.univ : Finset (Fin 7))).map
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

/-- The kernel's count of the cells of the box by fv, as a definition (checked before the elaborator
goes on, like the other large decisions). -/
def small_dec : PLift ((List.range 3).map (fun n => (boxF.filter fun v => (fv v).toNat = n).card) = [1, 6, 10]) := ⟨by
  decide +kernel⟩

/-- The coordination sequence below n = 3. -/
theorem small_vals : (List.range 3).map a = [1, 6, 10] := by
  rw [List.map_congr_left (fun n hn => a_small n (by rw [List.mem_range] at hn; omega))]
  exact small_dec.down


/-! ## Counting the spheres

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. The
gradient of facet i is gc i times the primitive vector (Ap i, Bp i), so the points of class s with
pot_i = n lie on the line Ap i x + Bp i y = c with c = lev s i n, and only when gc i divides
n - Cc s i. That line is par s i c u = (al i c + Bp i u, be i c - Ap i u), and potential j is
ka i j c + Dm i j u + Cc s j there (`pot_par`). The previous facet bounds u from above, the next one
from below, and for n ≥ 4 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 28 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T (a table entry plus its offset). -/
def ctabN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

def gcV (k : ℕ) : ℕ := ctabN 159683337 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 10) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 21907080 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 379438957315 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 4

def Bp (i : Fin 10) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 288145 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 10) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 628804 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 10) : ℤ := beN i.val

theorem prim : ∀ i : Fin 10, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 10) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 10) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 10, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 7) (i : Fin 10) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 7) (i j : Fin 10) (c u : ℤ) :
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

theorem par_inj (s : Fin 7) (i : Fin 10) (c : ℤ) : Function.Injective (par s i c) := by
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

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (4 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 2649813813175548789807571290706495702743583162008902233631055742449971672320599138372337568075271784010226122489143296 4 k

def cf1N (k : ℕ) : ℤ := (cf1V k : ℤ)

def cf1 (i : Fin 10) (j : Fin 10) : ℤ := cf1N (j.val + 10 * i.val)

def cf2V (k : ℕ) : ℕ := ctabN 2024346758513229860657893744554514051049652971640713125145969809056480163759830484022947291305703167049746785885247488 4 k

def cf2N (k : ℕ) : ℤ := (cf2V k : ℤ)

def cf2 (i : Fin 10) (j : Fin 10) : ℤ := cf2N (j.val + 10 * i.val)

def cf3V (k : ℕ) : ℕ := ctabN 8525539027975803831604903215932122936999199784091947347014581164755479704646521163655104 3 k

def cf3N (k : ℕ) : ℤ := (cf3V k : ℤ)

def cf3 (i : Fin 10) (j : Fin 10) : ℤ := cf3N (j.val + 10 * i.val)

def cf0V (k : ℕ) : ℕ := ctabN 15662767952745840206721393524903395904863094942695429675128843218331378832784621118656 3 k

def cf0N (k : ℕ) : ℤ := (cf0V k : ℤ)

def cf0 (i : Fin 10) (j : Fin 10) : ℤ := cf0N (j.val + 10 * i.val)


/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The class constants Cc s i, packed for the kernel. -/
def cTV (k : ℕ) : ℕ := ctabN 708430212804724291722695461607948231115563160210620016142405108 3 k

def cTN (k : ℕ) : ℤ := (cTV k : ℤ) - 3

def cT (s : Fin 7) (i : Fin 10) : ℤ := cTN (i.val + 10 * s.val)

theorem cT_eq : ∀ s : Fin 7, ∀ i : Fin 10, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 7) (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (4 - cT s i)

instance (i j : Fin 10) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 10, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 10 || j == (i + 9) % 10

/-- certC in natural numbers, for the kernel: Cc = cTV - 3, the negative terms moved across; the
previous facet of i is (i + 9) % 10, the next one (i + 1) % 10. -/
def certNat (s i j : ℕ) : Bool :=
  Nat.blt ((cf1V (j + 10 * i) + cf2V (j + 10 * i) + cf0V (j + 10 * i)) * cTV (i + 10 * s) +
      cf3V (j + 10 * i) * cTV (j + 10 * s))
    (cf1V (j + 10 * i) * (cTV ((i + 9) % 10 + 10 * s) + (if (i + 9) % 10 < i then 1 else 0)) +
      cf2V (j + 10 * i) * (cTV ((i + 1) % 10 + 10 * s) + (if (i + 1) % 10 < i then 1 else 0)) +
      cf3V (j + 10 * i) * cTV (i + 10 * s) + cf0V (j + 10 * i) * 7)

def certOK : Bool :=
  (List.range 7).all fun s => (List.range 10).all fun i => (List.range 10).all fun j =>
    nearB i j || certNat s i j

theorem certOK_eq : certOK = true := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 10, (i - 1).val = (i.val + 9) % 10 := by decide +kernel

theorem fin_next : ∀ i : Fin 10, (i + 1).val = (i.val + 1) % 10 := by decide +kernel

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 7) (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  have hn : nearB i.val j.val = false := by
    have n1 : j.val ≠ i.val := fun h => e2 (Fin.ext h)
    have n2 : j.val ≠ (i.val + 1) % 10 := fun h => e3 (Fin.ext (h.trans a2.symm))
    have n3 : j.val ≠ (i.val + 9) % 10 := fun h => e1 (Fin.ext (h.trans a1.symm))
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
def lev (s : Fin 7) (i : Fin 10) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 7) (i : Fin 10) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 7) (i j : Fin 10) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 7) (i : Fin 10) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 7) (i : Fin 10) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 7) (i j : Fin 10) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 7) (i : Fin 10) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 7) (i : Fin 10) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 7) (i : Fin 10) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 4 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 7) (i : Fin 10) (n u : ℤ) (hn : 4 ≤ n)
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
  Finset.Icc (-(1 * n + 4)) (1 * n + 4) ×ˢ
    (Finset.Icc (-(1 * n + 4)) (1 * n + 4) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 7, ∀ j : Fin 10, -4 ≤ Cc s j ∧ Cc s j ≤ 4 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 1 * Ac 4 + 1 * Ac 5 = 4 ∧ 1 * Bc 4 + 1 * Bc 5 = 0 ∧
    1 * Ac 0 + 1 * Ac 9 = (-4) ∧ 1 * Bc 0 + 1 * Bc 9 = 0 ∧
    1 * Ac 6 + 1 * Ac 8 = 0 ∧ 1 * Bc 6 + 1 * Bc 8 = 8 ∧
    1 * Ac 1 + 1 * Ac 3 = 0 ∧ 1 * Bc 1 + 1 * Bc 3 = (-8) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 7) :
    4 * x ≤ 2 * F (x, y, s) + 8 ∧
    4 * (-x) ≤ 2 * F (x, y, s) + 8 ∧
    8 * y ≤ 2 * F (x, y, s) + 8 ∧
    8 * (-y) ≤ 2 * F (x, y, s) + 8 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 4 + 1 * pot (x, y, s) 5 =
      4 * x + 1 * Cc s 4 + 1 * Cc s 5 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 4
  have r0 := le_F (x, y, s) 5
  have k0 := Cbound s 4
  have l0 := Cbound s 5
  have e1 : 1 * pot (x, y, s) 0 + 1 * pot (x, y, s) 9 =
      4 * (-x) + 1 * Cc s 0 + 1 * Cc s 9 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 9
  have k1 := Cbound s 0
  have l1 := Cbound s 9
  have e2 : 1 * pot (x, y, s) 6 + 1 * pot (x, y, s) 8 =
      8 * y + 1 * Cc s 6 + 1 * Cc s 8 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 6
  have r2 := le_F (x, y, s) 8
  have k2 := Cbound s 6
  have l2 := Cbound s 8
  have e3 : 1 * pot (x, y, s) 1 + 1 * pot (x, y, s) 3 =
      8 * (-y) + 1 * Cc s 1 + 1 * Cc s 3 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 1
  have r3 := le_F (x, y, s) 3
  have k3 := Cbound s 1
  have l3 := Cbound s 3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 7) (i : Fin 10) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 7) (i : Fin 10) (n : ℤ) (hn : 4 ≤ n) :
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
def inner (s : Fin 7) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 7) (i : Fin 10) (n : ℤ) (hn : 4 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 7 × Fin 10, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 7 × Fin 10, inner p.1 p.2 n

/-! Shifting n by 28 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 1016220296814492 5 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 21312500773146 5 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 12

def mh (i : Fin 10) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 924022512824928 5 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 12

def mk (i : Fin 10) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 10, (28 : ℤ) = gc i * Lq i ∧
    28 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    28 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 7) (i : Fin 10) (n : ℤ) :
    inner s i (n + 28) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 28 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 28 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 28) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 28) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 28) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 4 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 7 × Fin 10, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 28) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqV (k : ℕ) : ℕ := ctabN 607275108 3 k

def lgqN (k : ℕ) : ℤ := (lgqV k : ℤ)

def lgq (i : Fin 10) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 10, (4 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 4 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 4 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 10, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 10 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 10) = 0 then mhN (c % 10) + mkN (c % 10) else 0

theorem gsN_eq (s : Fin 7) (i : Fin 10) (n : ℤ) :
    gsN (i.val + 10 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 10 * s.val) % 10 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (7 * 10)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhV (k : ℕ) : ℕ := ctabN 74090709 3 k

def uhN (k : ℕ) : ℤ := (uhV k : ℤ) - 3

def uh (i : Fin 10) : ℤ := uhN i.val

def dhV (k : ℕ) : ℕ := ctabN 1010727036 3 k

def dhN (k : ℕ) : ℤ := (dhV k : ℤ)

def dh (i : Fin 10) : ℤ := dhN i.val

def ukV (k : ℕ) : ℕ := ctabN 712004832 3 k

def ukN (k : ℕ) : ℤ := (ukV k : ℤ) - 3

def uk (i : Fin 10) : ℤ := ukN i.val

def dkV (k : ℕ) : ℕ := ctabN 657706599 3 k

def dkN (k : ℕ) : ℤ := (dkV k : ℤ)

def dk (i : Fin 10) : ℤ := dkN i.val

def vhV (k : ℕ) : ℕ := ctabN 447646341565178383591849635368644199762450580864531554239513317 3 k

def vhN (k : ℕ) : ℤ := (vhV k : ℤ) - 3

def vh (s : Fin 7) (i : Fin 10) : ℤ := vhN (i.val + 10 * s.val)

def vkV (k : ℕ) : ℕ := ctabN 502340396395476180639311911089449110648836202943667776061627153 3 k

def vkN (k : ℕ) : ℤ := (vkV k : ℤ) - 3

def vk (s : Fin 7) (i : Fin 10) : ℤ := vkN (i.val + 10 * s.val)

def levT (s : Fin 7) (i : Fin 10) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 7) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_facet : ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧
    uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) := by
  decide +kernel

theorem tab_class : ∀ s : Fin 7, ∀ i : Fin 10,
    vh s i = cT s i - cT s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    vk s i = cT s i - cT s (i + 1) - (if i + 1 < i then 1 else 0) := by
  decide +kernel

theorem tab_ok (s : Fin 7) (i : Fin 10) : uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  obtain ⟨f1, f2, f3, f4⟩ := tab_facet i
  obtain ⟨c1, c2⟩ := tab_class s i
  simp only [cT_eq] at c1 c2
  exact ⟨f1, c1, f2, f3, c2, f4⟩

theorem inner_eq (s : Fin 7) (i : Fin 10) (n : ℤ) : inner s i n = innerT s i n := by
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
def ST (n : ℤ) : ℤ := ∑ p : Fin 7 × Fin 10, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 10 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 10) = 0 then
    (uhN (c % 10) * ((n - cTN c) / gcN (c % 10)) + vhN c) / dhN (c % 10) +
      (ukN (c % 10) * ((n - cTN c) / gcN (c % 10)) + vkN c) / dkN (c % 10) + 1
  else 0

theorem innerN_eq (s : Fin 7) (i : Fin 10) (n : ℤ) :
    innerN (i.val + 10 * s.val) n = innerT s i n := by
  have hi := i.isLt
  have h : (i.val + 10 * s.val) % 10 = i.val := by omega
  rw [innerN, h]
  rfl

theorem sum_range_list (f : ℕ → ℤ) (N : ℕ) :
    ∑ c ∈ Finset.range N, f c = ((List.range N).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The closed form over the indices of the pieces. -/
def STN (n : ℤ) : ℤ := ((List.range (7 * 10)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 7 × Fin 10 => innerT q.1 q.2 n)
    (fun c : Fin (7 * 10) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (7 * 10), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 7 × Fin 10 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (7 * 10) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (7 * 10), sum_range_list]

/-- The closed form's tables, packed: the steps, the values on one period from 3 and below 3. -/
def dtabV (k : ℕ) : ℕ := ctabN 676500 5 k

def tblV (k : ℕ) : ℕ := ctabN 8496396 6 k

def initV (k : ℕ) : ℕ := ctabN 2657 4 k

/-- The step of the closed form at residue t mod 4. -/
def dv (t : ℕ) : ℕ := dtabV (t % 4)

/-- The sequence in closed form: b(n + 4) = b(n) + dv (n - 3) for n ≥ 3. -/
def b (n : ℕ) : ℕ :=
  if n < 3 then initV n else dv (n - 3) * ((n - 3) / 4) + tblV ((n - 3) % 4)

theorem b_step (n : ℕ) (hn : 3 ≤ n) : b (n + 4) = b n + dv (n - 3) := by
  rw [b, b, if_neg (show ¬ (n + 4 < 3) by omega), if_neg (show ¬ (n < 3) by omega),
    show n + 4 - 3 = n - 3 + 4 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 4)]
  ring

theorem b_shift (n : ℕ) (hn : 3 ≤ n) : b (n + 28) = b n + 7 * dv (n - 3) := by
  rw [b, b, if_neg (show ¬ (n + 28 < 3) by omega), if_neg (show ¬ (n < 3) by omega),
    show n + 28 - 3 = n - 3 + 4 * 7 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 4)]
  ring

/-- b on the residue class of 3 + j mod 4. -/
theorem b_res (k j : ℕ) (hj : j < 4) : b (4 * k + (3 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (4 * k + (3 + j) < 3) by omega),
    show 4 * k + (3 + j) - 3 = j + 4 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 4), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The growth of S over one period at each residue mod 4. -/
def GsT : List ℤ := [140, 140, 140, 140]

theorem Gs_tab : ∀ r : ℕ, r < 4 → GsN (r : ℤ) = GsT.getD r 0 := by
  decide +kernel

/-- The growth of b over 28 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 4 → 7 * (dv t : ℤ) = GsT.getD ((3 + t) % 4) 0 := by
  decide +kernel

theorem grow (n : ℕ) (_hn : 3 ≤ n) : 7 * (dv (n - 3) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 3) % 4) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 3) % 4) = dv (n - 3) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 4)]
  have e2 : (3 + (n - 3) % 4) % 4 = n % 4 := by omega
  rw [e1, e2, ← Gs_tab (n % 4) (Nat.mod_lt _ (by norm_num)), ← Gs_eq_GsN] at h1
  rw [h1]
  have e3 : (((n % 4 : ℕ) : ℤ) + 4 * ((n / 4 : ℕ) : ℤ)) = n := by omega
  rw [← e3, Gs_periodic]

/-- One kernel pass over n = 4, ..., 31: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 28 →
    ((List.range (7 * 10)).all fun c => decide (0 ≤ innerN c (4 + (r : ℤ)))) = true ∧
      STN (4 + (r : ℤ)) = b (4 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 4 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 7) (i : Fin 10) (n : ℤ) (hn : 4 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 4 + t := ⟨(n - 4).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 28
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 10 * s.val < 7 * 10 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 28) (by omega) (by omega)
      have e : (4 : ℤ) + t = (4 + (t - 28 : ℕ)) + 28 := by
        push_cast [Nat.cast_sub (by omega : 28 ≤ t)]; ring
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
    by_cases h : n < 32
    · obtain ⟨r, rfl⟩ : ∃ r, n = 4 + r := ⟨n - 4, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 28) (by omega) (by omega)
      have h2 := S_shift ((n - 28 : ℕ) : ℤ)
      have h3 := b_shift (n - 28) (by omega)
      have h4 := grow (n - 28) (by omega)
      rw [show n - 28 + 28 = n by omega] at h3
      rw [show ((n - 28 : ℕ) : ℤ) + 28 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 3 lie in the box -3 ≤ x ≤ 3, -1 ≤ y ≤ 1 (`small_box`), and
the kernel checks that those of the box are the 29 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 7) (h : F (x, y, s) ≤ 3) :
    -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 3, with their values of F. -/
def smallV : List (V × ℤ) :=
  [(((-1), 0, 4), 1), (((-1), 0, 5), 1), ((0, 0, 4), 1), ((0, 0, 5), 1), ((0, 0, 6), 1), (((-1), 0, 2), 2), (((-1), 0, 3), 2), (((-1), 0, 6), 2), (((-1), 1, 0), 2), (((-1), 1, 1), 2), ((0, 0, 2), 2), ((0, 0, 3), 2), ((0, 1, 0), 2), ((0, 1, 1), 2), ((1, 0, 3), 2), ((1, 0, 6), 2), ((1, 1, 0), 2), (((-2), 0, 2), 3), (((-2), 0, 4), 3), (((-2), 0, 5), 3), (((-2), 1, 1), 3), (((-1), 0, 1), 3), (((-1), 1, 2), 3), ((0, 0, 1), 3), ((0, 1, 2), 3), ((1, 0, 2), 3), ((1, 0, 4), 3), ((1, 0, 5), 3), ((1, 1, 1), 3)]

def smallL : List V := smallV.map Prod.fst

theorem smallV_ok : (smallV.all fun q => decide (F q.1 = q.2)) = true := by
  decide +kernel

/-- The potentials, packed: Ac = ATV - 2, Bc = BTV - 4. -/
def ATV (k : ℕ) : ℕ := ctabN 21907080 3 k

def ATN (k : ℕ) : ℤ := (ATV k : ℤ) - 2

def AT (i : Fin 10) : ℤ := ATN i.val

def BTV (k : ℕ) : ℕ := ctabN 380244262915 4 k

def BTN (k : ℕ) : ℤ := (BTV k : ℤ) - 4

def BT (i : Fin 10) : ℤ := BTN i.val

theorem AB_eq : ∀ i : Fin 10, AT i = Ac i ∧ BT i = Bc i := by
  decide +kernel

/-- Some potential exceeds 3 at the box point ((a : ℤ) - 3, (b : ℤ) - 1, s), in natural
numbers: the negative terms moved across. -/
def bigNat (a b s : ℕ) : Bool :=
  (List.range 10).any fun i =>
    Nat.blt (6 + ATV i * 3 + 2 * a + BTV i * 1 + 4 * b)
      (ATV i * a + 6 + BTV i * b + 4 + cTV (i + 10 * s))

theorem big_pot (a b : ℕ) (s : Fin 7) (h : bigNat a b s.val = true) :
    (3 : ℤ) < F ((a : ℤ) - 3, (b : ℤ) - 1, s) := by
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  have hl := (Nat.cast_lt (α := ℤ)).mpr (Nat.blt_eq.mp hb)
  have hp := le_F ((a : ℤ) - 3, (b : ℤ) - 1, s) ⟨i, hi⟩
  obtain ⟨eA, eB⟩ := AB_eq ⟨i, hi⟩
  have e3 := cT_eq s ⟨i, hi⟩
  simp only [pot] at hp
  rw [← eA, ← eB, ← e3] at hp
  simp only [AT, BT, ATN, BTN, cT, cTN] at hp
  push_cast at hl hp
  ring_nf at hl hp ⊢
  linarith

def smallOK : Bool :=
  (List.range 7).all fun a => (List.range 3).all fun b => (List.finRange 7).all fun s =>
    bigNat a b s.val || decide (((a : ℤ) - 3, (b : ℤ) - 1, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 3) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 3).toNat (by omega) (y + 1).toNat (by omega) s
  have ex : (((x + 3).toNat : ℕ) : ℤ) - 3 = x := by omega
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
are S(n), and all agree with the closed form b (`a_eq_b`). The step from n to n + 4, the closed form
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

theorem dconst_base : ∀ r : ℕ, r < 4 → dtabV r = 20 := by
  decide +kernel
theorem dv_const : ∀ t : ℕ, dv t = 20 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 4) = a(n) + 20 for n ≥ 3. -/
theorem a_step (n : ℕ) (hn : 3 ≤ n) : a (n + 4) = a n + 20 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-- The steps and the values on one period, by the kernel. -/
theorem closed_vals : dv 0 = 20 ∧ tblV 0 = 12 ∧ dv 1 = 20 ∧ tblV 1 = 20 ∧ dv 2 = 20 ∧ tblV 2 = 26 ∧ dv 3 = 20 ∧ tblV 3 = 32 := by
  decide +kernel

/-- The closed form per residue of n mod 4, for n ≥ 3. -/
theorem a_closed (k : ℕ) :
    a (4 * k + 3) = 20 * k + 12 ∧
    a (4 * k + 4) = 20 * k + 20 ∧
    a (4 * k + 5) = 20 * k + 26 ∧
    a (4 * k + 6) = 20 * k + 32 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := closed_vals
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 4 * k + 3 = 4 * k + (3 + 0) from rfl, b_res k 0 (by norm_num), c0, c1]
  · rw [show 4 * k + 4 = 4 * k + (3 + 1) from rfl, b_res k 1 (by norm_num), c2, c3]
  · rw [show 4 * k + 5 = 4 * k + (3 + 2) from rfl, b_res k 2 (by norm_num), c4, c5]
  · rw [show 4 * k + 6 = 4 * k + (3 + 3) from rfl, b_res k 3 (by norm_num), c6, c7]

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 6, 10, 12, 20, 26, 32, 32, 40, 46, 52, 52, 60, 66, 72, 72, 80, 86, 92, 92, 100, 106, 112, 112, 120, 126, 132, 132, 140, 146, 152, 152, 160, 166, 172, 172, 180, 186, 192, 192, 200, 206, 212, 212, 220, 226, 232, 232, 240, 246] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 4 → (dv (t + 5) : ℤ) = (dv (t + 4) : ℤ) + (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 5) : ℤ) = (dv (t + 4) : ℤ) + (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 4 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 4, e 5]
  exact drec_base (t % 4) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 4 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 4 → (b (q + 8) : ℤ) = b (q + 7) + b (q + 4) - b (q + 3) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 8) : ℤ) = b (q + 7) + b (q + 4) - b (q + 3) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 4 ∨ 4 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 4 := ⟨q - 4, by omega⟩
      have h0 : (b (v + 8) : ℤ) = b (v + 7) + b (v + 4) - b (v + 3) := ih (v + 0) (by omega)
      have s3 : b (v + 7) = b (v + 3) + dv (v + 0) := by
        have h := b_step (v + 3) (by omega)
        rw [show v + 3 + 4 = v + 7 by omega,
          show v + 3 - 3 = v + 0 by omega] at h
        exact h
      have s4 : b (v + 8) = b (v + 4) + dv (v + 1) := by
        have h := b_step (v + 4) (by omega)
        rw [show v + 4 + 4 = v + 8 by omega,
          show v + 4 - 3 = v + 1 by omega] at h
        exact h
      have s7 : b (v + 11) = b (v + 7) + dv (v + 4) := by
        have h := b_step (v + 7) (by omega)
        rw [show v + 7 + 4 = v + 11 by omega,
          show v + 7 - 3 = v + 4 by omega] at h
        exact h
      have s8 : b (v + 12) = b (v + 8) + dv (v + 5) := by
        have h := b_step (v + 8) (by omega)
        rw [show v + 8 + 4 = v + 12 by omega,
          show v + 8 - 3 = v + 5 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 12) : ℤ) = b (v + 11) + b (v + 8) - b (v + 7)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 7 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 8 := ⟨n - 8, by omega⟩
  rw [show q + 8 - 1 = q + 7 by omega, show q + 8 - 4 = q + 4 by omega, show q + 8 - 5 = q + 3 by omega]
  simp only [a_eq_b]
  exact b_recur q

/-- The coefficients of the g.f. below 8, by the kernel. -/
theorem gf_base : ∀ n : ℕ, n < 8 → 1 * (b n : ℤ) - 1 * (if 1 ≤ n then (b (n - 1) : ℤ) else 0) - 1 * (if 4 ≤ n then (b (n - 4) : ℤ) else 0) + 1 * (if 5 ≤ n then (b (n - 5) : ℤ) else 0) = (if n = 0 then (1 : ℤ) else 0) + (if n = 1 then (1 : ℤ) else 0) * 5 + (if n = 2 then (1 : ℤ) else 0) * 4 + (if n = 3 then (1 : ℤ) else 0) * 2 + (if n = 4 then (1 : ℤ) else 0) * 7 + (if n = 5 then (1 : ℤ) else 0) * 1 + (if n = 6 then (1 : ℤ) else 0) * 2 - (if n = 7 then (1 : ℤ) else 0) * 2 := by
  decide +kernel

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 5 - X ^ 4 - X + 1) =
      -2 * X ^ 7 + 2 * X ^ 6 + X ^ 5 + 7 * X ^ 4 + 2 * X ^ 3 + 4 * X ^ 2 + 5 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (X ^ 5 - X ^ 4 - X + 1) = C 1 * A - C 1 * (A * X ^ 1) - C 1 * (A * X ^ 4) + C 1 * (A * X ^ 5) := by
    simp only [map_one]
    ring
  have e2 : (-2 * X ^ 7 + 2 * X ^ 6 + X ^ 5 + 7 * X ^ 4 + 2 * X ^ 3 + 4 * X ^ 2 + 5 * X + 1 : ℚ⟦X⟧) = C 1 + X ^ 1 * C 5 + X ^ 2 * C 4 + X ^ 3 * C 2 + X ^ 4 * C 7 + X ^ 5 * C 1 + X ^ 6 * C 2 - X ^ 7 * C 2 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · have h := congrArg (fun z : ℤ => (z : ℚ)) (gf_base n hn)
    push_cast at h
    linarith
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 8 := ⟨n - 8, by omega⟩
    have h : (b (q + 8) : ℤ) = b (q + 7) + b (q + 4) - b (q + 3) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 8 - 1 = q + 7 by omega, show q + 8 - 4 = q + 4 by omega, show q + 8 - 5 = q + 3 by omega, show 1 ≤ q + 8 by omega, show 4 ≤ q + 8 by omega, show 5 ≤ q + 8 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 8 = 1 by omega, show ¬ q + 8 = 2 by omega, show ¬ q + 8 = 3 by omega, show ¬ q + 8 = 4 by omega, show ¬ q + 8 = 5 by omega, show ¬ q + 8 = 6 by omega, show ¬ q + 8 = 7 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 5 - X ^ 4 - X + 1) =
      -2 * X ^ 7 + 2 * X ^ 6 + X ^ 5 + 7 * X ^ 4 + 2 * X ^ 3 + 4 * X ^ 2 + 5 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 7 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 6, 10, 12, 20, 26, 32, 32, 40, 46, 52, 52, 60, 66, 72, 72, 80, 86, 92, 92, 100, 106, 112, 112, 120, 126, 132, 132, 140, 146, 152, 152, 160, 166, 172, 172, 180, 186, 192, 192, 200, 206, 212, 212, 220, 226, 232, 232, 240, 246] := Count.controls

/-- The step a(n + 4) = a(n) + 20 for n ≥ 3. -/
theorem a_step (n : ℕ) (hn : 3 ≤ n) : a (n + 4) = a n + 20 := Count.a_step n hn

/-- The closed form per residue of n mod 4, for n ≥ 3. -/
theorem a_closed (k : ℕ) :
    a (4 * k + 3) = 20 * k + 12 ∧
    a (4 * k + 4) = 20 * k + 20 ∧
    a (4 * k + 5) = 20 * k + 26 ∧
    a (4 * k + 6) = 20 * k + 32 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 5 - X ^ 4 - X + 1) =
      -2 * X ^ 7 + 2 * X ^ 6 + X ^ 5 + 7 * X ^ 4 + 2 * X ^ 3 + 4 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a315135

theorem OMA.solution : type_of% @OMA.S_oeis_a315135.main :=
  OMA.S_oeis_a315135.conjecture
