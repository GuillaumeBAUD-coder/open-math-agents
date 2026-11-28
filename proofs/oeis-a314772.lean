import OMAStatements.S_oeis_a314772

namespace OMA.S_oeis_a314772






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
  | 0 => 507968601308
  | 1 => 439536499642
  | 2 => 585832639163
  | 3 => 512836086458
  | 4 => 439250242763
  | 5 => 586118896042
  | 6 => 659419531417
  | 7 => 590717950104
  | 8 => 517417314729
  | _ => 0

/-- The potential t is Ac t * x + Bc t * y + Cc s t at (x, y, s) (packed tables). -/
def Ac (i : Fin 10) : ℤ := tget 444691290230 4 8 i.val

def Bc (i : Fin 10) : ℤ := tget 811156718405 4 8 i.val

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
def R0N (s : Fin 9) : ℕ := tgetN 50073283209 4 s.val

def R0c (s : Fin 9) : ℤ := (R0N s : ℤ)

/-- The pairs (class s, potential t) and the classes whose rule, far, side and near checks are made;
the others follow by the symmetry sig. -/
def repB (s : Fin 9) (t : Fin 10) : Bool := decide (tgetN 279534847580315505103446015 1 (s.val * 10 + t.val) = 1)

def repC (s : Fin 9) : Bool := decide (tgetN 487 1 s.val = 1)

/-- A symmetry of order 2 of the graph that fixes v0 and permutes the potentials:
(x, y, s) ↦ ((-1) x + 0 y + tauX s, 0 x + 1 y + tauY s, piS s), and potential t goes to rhoP t. -/
def piS (s : Fin 9) : Fin 9 := ⟨tgetN 36344701716 4 s.val % 9, Nat.mod_lt _ (by norm_num)⟩

def tauX (s : Fin 9) : ℤ := tget 36668283273 4 8 s.val

def tauY (s : Fin 9) : ℤ := tget 36650387592 4 8 s.val

def rhoP (t : Fin 10) : Fin 10 := ⟨tgetN 371389895220 4 t.val % 10, Nat.mod_lt _ (by norm_num)⟩

def sig (v : V) : V :=
  ((-1) * v.1 + 0 * v.2.1 + tauX v.2.2, 0 * v.1 + 1 * v.2.1 + tauY v.2.2, piS v.2.2)

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
  ⟨(tget 824782740946240041763036064966065761418585579785 4 0 (t.val * 4 + k.val)).toNat % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The slot k of t holds another potential. -/
def real (t : Fin 10) (k : Fin 4) : Bool := decide (nb t k ≠ t)

/-- The potential t is a facet: a slot on each side cannot both come within 1 of t beyond R0c. -/
def facetB (t : Fin 10) : Bool := decide (tget 693 1 0 t.val = 1)

/-- The potential j is neither t nor in a slot of t. -/
def nonadj (t j : Fin 10) : Bool :=
  decide (j ≠ t) && decide (j ≠ nb t 0) && decide (j ≠ nb t 1) && decide (j ≠ nb t 2) && decide (j ≠ nb t 3)

/-- Certificates of the far facts, the same for every class: for maximal potential t and a potential
j that is not a neighbor of t, the fields k1, k2, m1, m2, m0, mj of entry t * 10 + j give the facts
pot k1 ≤ pot t, pot k2 ≤ pot t, R0c s + 1 ≤ pot t and pot t ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fd (t j : Fin 10) (f : ℕ) : ℤ := tget 2592948070776861252424554997621985703996536870448948041280383484568358013580580049242395963633428626816160190562048576536867712256122092535896148070462305155714980662702804850728257504434834518852941918547800051644532288039437648001805958267935782055108314003371512588086005279439710924679025360684512635689486596319306280372242638857557852819387010411846725513994311101903003782266511743191391783411506205269566031062241078707750019404790696474763000898387579448481134181681495275284136272403934777273981958253783042203847679563562961140746842579539246618616516626891504830913837785483223191128317143220336380038137997978453376224882390734460647309286105974234882461390360921754653325686231883390123238859863923977494015807536469371647410187635333580280579201582210940037078813979118527133109013096839796701671400006872678979459074213373327262495330654483588119823799691110884795672657230270627658828731580479508885281955214878460915174103462715543817939401251889972651392182271449017404949800266525862466010409905402188317338444767584086653711100351588918914501257890732093447735328 6 32 ((t.val * 10 + j.val) * 6 + f)

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
def sd (t : Fin 10) (i f : ℕ) : ℤ := tget 5530367127818295939001584539507006106606744275606870528756640041277472872217765437130878364443452120888836143788445470257621061670314713927100590067276864076819769731980658021018155209081829377115325054986992346569716840981756346994741862821037807685721846222098030223932324504591561320777036017325584 5 16 ((t.val * 4 + i) * 5 + f)

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
def srcv (p : ℕ) : ℕ := tgetN 51083178605933665575248835775560707259037945869369344 4 p

def tgtv (p : ℕ) : ℕ := tgetN 43896432317156303952660312810408255385714857274205249 4 p

def tgtF (p : ℕ) : Fin 9 := ⟨tgtv p % 9, Nat.mod_lt _ (by norm_num)⟩

def dxv (p : ℕ) : ℤ := tget 51457420815437368120167722972792889763684948645480567 4 8 p

def dyv (p : ℕ) : ℤ := tget 51083184697010538885089565358230860409596525888895112 4 8 p

/-- dlv p j + 8, as a natural number (the rule checks compare naturals). -/
def dlvN (p : ℕ) (j : Fin 10) : ℕ := tgetN 38989128425701719942148118317882854600948960496615026893010167077568682583900071374150128669052679718679289768342466891096161490560954274365348388980569399928807807419177993407537434225622276697133630246849580756314673941095088207751975813246343963287158004420237582224027480802400201870801577160645587338781059469294419948543241026159755935516509150058921323424441822019962742500408147685722385917033317475017502974263616936547950835286513899799239213004427788510873950379791790136111344531175650379602943313997558958533466617720 4 (p * 10 + j.val)

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

/-- Descent rules beyond F = R0c s, one word of 29 bits per class s, potential t and admissible
pattern (c0, c1, c2, c3), at position POFF t + (the rank of the pattern among the admissible patterns
of t): kind 0 names an edge by its position in E; kind 1 is a Farkas certificate: multipliers m1, m2,
m3 of the slot facts of slots k1, k2, k3 (slack ≥ c for a multiplier ≥ 0, slack ≤ c for a negative
multiplier, where c ≤ 1) and l0 ≥ 0 of the bound R0c s + 1 ≤ pot t, whose x and y parts cancel and
whose constants add up to a positive number; kind 2 is a line of slot k1 without lattice points
(modulus l0). Fields from bit 0: kind (2 bits), edge position (6), k1, k2, k3 (2 each), m1, m2, m3
(4 each, stored as value + 8), l0 (3). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 10689772486671243422269458404731670501962250721765225852021953087909173599620688736963913869494606244001575925871198354521080581278922529720656003822142034203491025205982386558442019704318527291068038630124983043618420204718721653685213542338697047342641480738877222208514688864348285746268684240729848918638311917043968710660017619892802900128973411579658845347676840793912977922426813469552847972218454444694759202647380796502655306221055320638001756373575222506085499246337518165119177935208203514194416546170388943105338237740793947486852906033559978445192455197817630963496624102936097641603095492690841108430840927913806751944334304110446030838242787019185943434067114703805134658394065671247230109547182441492309590320552794999907024588885736485367195316077824847285687749859985898510081505136409793544374372998981178479130432939096419502635339863065552530549358368772419155070590500389072958216892921273016227280608375555903123144692764080657361573419276138714300726112305616864679988737
  | 1 => 10689770096737953565204944524322205226296318640416117364668819182654931398855238510731740695905674690683011364840024806872928274800634370002153482853712754514068096968175329115825734889909476118899936235815435172519183216884284933671922803327854503115905551307101168376066750866589822041848977845604181728232421281140206194146764607914972558599504503977807337792735398134834656983150263101912546387613062521954174162799100318008223475157475146700622096773386859138862306695099895818170177536740413267396141309070092863201640794795604177014673004976866803497493908797291016910430032647165732660486149149029300415670703530583801696659251463860871397175572341097669571381671437706509667458877129342322499638573364322482364142219934854525242425545009582248775540670452831171918488616617019625003614326994281421578025659911630830863621991635665817187651727107523819586740413548808419988069854516673492604288650085734317906076374888402157326086009704234858944335147888789561305279989485904301326991384
  | 2 => 10689783241371047779059748064270695080627700778120489510973516738641916286144587075378246937990362832727238478801682015680418927509016265764608228793076771997418892764492325018368438987797866683680516038307074180088886797459622595407538582335379729025859071617304483786840323609242490936498381235668505945155690250398893515107073285655620723143137460584086033858753596031723631769830056756713931535318498209180180269155986085679523226189122288831410181002161759973276177731118600976659951954129538056993183376695533437531992231173322452168164852222935199061307199548366679372950448765087380083806590392254447460804815536131717188807862167420790216537279211402200940154919685462631246764013714996718885007544108699398288698166228367196363421133854623978972587724320709698708224073262459451495905313767916501110700740665897355784116486772054178857950883291563910144441356514338826608331960086494126975984390719790046410855460006893847648781657842626084224011497146620393480382580610594092355813424
  | 3 => 10689770096737953565204944524322205226296318640416117364668819182654931398855238510731740695905674690683011364840024806872928274800634370002153482853712754514068096968175329115825733380078600836170347071497348944121016629785128259496390716209210326729633549279498880002815470542324310309731348704525968960882870818945728266546935382639931007085564693977052622581020440274498681754423485044537935903998771182835970305298796559602541793535938836915864794537170765036787222901300244838967273127533999175271103413981548099406161720040102686833145755696488220541041179960943450826845413047733455132401998344001754034090544153936030150735685220447125818004337285470525216889800559074290346201689691570262591555284549771027955204950756907602766778761743688291814804384082965178109786246164025070897178177240136657103017478567123621076585755966423105751414643109545875997242333224939753809593339372662847497760903711001465683543266792268696439092474030561999778751608624792701288999360525159199540379648
  | 4 => 10689770096737953565204944524322205226296318640416117364668819182654931398855238510731740695905674690683011364840024806872928274800634370002153482853712754514068096968175329115825733380078600836170347071497348944121016629785128259496390716209210326729633549279498880002815470542324310309731348704525968960882870818945728266546935382639931007085564693977052622581020440274498681754423485044537935903998771182835970305298796559602541793535938836915864794537170765036787222901300244838967273127533999175271103413981548099406161720040102686833145755696488220541041179960943450826845413047733455132401998344001754034090544153936030150735685220447125818004337285470525216889800559074290346201689691570262591555284549771027955204950756907602766778761743688291814804384082965178109786246164025070897178177240136657103017478567123621076585755966423105751414643109545875997242333224939753809593339372662847497760903711001465683543266792268696439092474030561999778751608624792701288999360525159199540379648
  | 5 => 10689770096737953565204944524322205226296318640416117364668819182654931398855238510731740695905674690683011364840024806872928274800634370002153482853712754514068096968175329115825740627266802193272359973983181681189969023461897116408099084011094445446583831645327811519732431633044830523391932333782160947100576174214938930991087403558695293369165519045182392853946897858079950724034644968494766409408748665336774176403647561961861897902341669208899259870397190541042525413490502440071409001175629251709061673686467387185863105802888550923655107374628764071902069621096318278696914540227843746323329434648983277783862106261167471216946284480339350858585728140116457523390499138369907612828675992203949028890787371728786261898888187188314035264119330882106430025191297151024192314297658330048600755044804995778516804415348811146192716842479400570635165796253095427095599532740598751244185545886644886324732011809782994692046741713979608484641052040602126004983439181964581071459904256169054699624
  | 6 => 10689770096737953565204944524322205226296318640416117364668819182654931398855238510731740695905674690683011364840024806872928274800634370002153482853712754514068096968175329115825742741030027589093780403874882896168413471617621366340680691286643980072360997335361249878637142466830543379677704434679452873676130266888725014819707505006148020740928954990555000749358748092287117367231276407748986638383115134120598739648330112184192601115896972955559853565804833335633785877791232566295947924654999663612856902482604944303308593777728118898162948956622955872730522948481477258400104679924521384970484748605659191696132543894033247528841553017778161929798740538780234469403558107966747157432851326450675053825953981096080601462189288892425361218308265689308266991644376119788408235675824521513858581543102175145960096030105186617545523343917910614453173319594674265437392224118080699649447841928117517573885231358919569180373611878123978995502384529848104656977285063894113661315091546069178384504
  | 7 => 10689770096737953565204944524322205226296318640416117364668819182654931398855238510731740695905674690683011364840024806872928274800634370002153482853712754514068096968175329115825744854793252984915200833766584111146857919773345616273262298562193514698138163025394688237693649030428725040633333147939916983016543690617788796687752799344131239635691641596656457902095205849094576225550111243246135684207542483537434958993293265251260665039653585154064589423514593451520361761952080402574887556669611589675408159131283924806435904261689808068587456955035665036223852960759325700482181105891090322003788533084693372263895009307378750853706369106567217239450343229344758786649674516764482206816197817016183139513008527121269923110060609829419116436112668938844777252706547206267127635754807255667799520476028625500486084919732400260343388445018070652576040277789661745395406867838469899226506162925490194986323411262933832188123967623641366397061292273003794208815675138090136682865806433134332477576
  | 8 => 10689770096737953565204944524322205226296318640416117364668819182654931398855238510731740695905674690683011364840024806872928274800634370002153482853712754514068096968175329115825745156759428041461118038036827141858064269509877651977929424583152217428249946873321939809559806307740888986822726578483772337905024348999051275330663641432918668955421605487919641104423973492297981078593256571935076176235836598984393965646109440950637141892981664181526893240628229193690344997342956399008886031570854879871516087290075841944656748149455074923830615083930521467143972844279670896642976093842396854542399641447719451999343980564381269617852864394794200880732112493441753286481730223357466687465109114230486491738539365421229757164412414327271534597285860744356581009807794610156488462144033808401578684697026276547413294537024229764286284687128474326645767845615934824491011061986122338492880985525795897757051149501564944096252020840049714388675587563318165190569418179138772285832325229832843690156
  | _ => 0

def rword (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ :=
  tgetN (ruleT s.val) 29 (Nat.add (tgetN 956824381820114371968 7 t.val) (tgetN 2515467447984275792325541382460174940913700259461398881218637967810349733285177004367862527758029326465596510826481326817564593845899160076358820018417113464120121993437105451051232087846616517638882387691346971711431700696550571251197393482462920740217783095387981546100677021269837380289988538987517906784060361267536506022703812112735443618748707818212553305454991690061969613373571103320689602745685737610363870063092445711259029114651120065750451042334419465659705299718463021511402405792515444368703310184688077131690766932545607055730219570238333084722410971206362593412199054894844292940280542959072700211905035880938514384363984330429908187041143040229845988691961151161910076887266326203139765896541428734850884933227034945177400092984139356045754660591799788884922427371691177639011515686793050877898714429271548789556072361604298201169322760003506394365391609360049623616536838801598137711290660840601747212766243332931424164159618336066847120702446069214108731480615685897435224531688932650350555360632479103122222554102517744233653258015129007050901282200978419557603884630187933896746473608893012231676018245485925142364160 5
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul t.val 81) c0) (Nat.mul 3 c1)) (Nat.mul 9 c2)) (Nat.mul 27 c3))))

/-- The field of B bits from bit o of the word w. -/
def fld (w o B : ℕ) : ℕ := Nat.mod (Nat.shiftRight w o) (Nat.pow 2 B)

def rk (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 0 2

def re (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 2 6

def rsl (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (i : ℕ) : Fin 4 :=
  ⟨fld (rword s t c0 c1 c2 c3) (Nat.add 8 (Nat.mul 2 i)) 2 % 4, Nat.mod_lt _ (by norm_num)⟩

def rm (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) (i : ℕ) : ℤ := Int.subNatNat (fld (rword s t c0 c1 c2 c3) (Nat.add 14 (Nat.mul 4 i)) 4) 8

def rl0 (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : ℤ := Int.ofNat (fld (rword s t c0 c1 c2 c3) 26 3)

/-- The class of slot k in the pattern (c0, c1, c2, c3). -/
def cv (c0 c1 c2 c3 : ℕ) (k : Fin 4) : ℕ := if k.val = 0 then c0 else if k.val = 1 then c1 else if k.val = 2 then c2 else c3

/-- The slack of the slot k below t in x and y, and its constant: pot t - pot (nb t k) at (x, y, s)
is dA t k * x + dB t k * y + dC s t k. -/
def dA (t : Fin 10) (k : Fin 4) : ℤ := Ac t - Ac (nb t k)

def dB (t : Fin 10) (k : Fin 4) : ℤ := Bc t - Bc (nb t k)

def dC (s : Fin 9) (t : Fin 10) (k : Fin 4) : ℤ := Cc s t - Cc s (nb t k)

/-- Kind 0: the edge at position re descends from class s for this pattern. -/
def ok0 (s : Fin 9) (t : Fin 10) (c0 c1 c2 c3 : ℕ) : Bool :=
  Nat.blt (re s t c0 c1 c2 c3) 44 && Nat.beq (srcv (re s t c0 c1 c2 c3)) s.val && Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) t) 1) 8 &&
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

theorem E_len : E.length = 44 := by
  decide +kernel

/-- The edge at position p of E, read from the tables. -/
theorem edge_of (p : ℕ) (hp : p < 44) : ∃ e ∈ E, e.1.val = srcv p ∧ e.2.1.val = tgtv p ∧
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
def sym_ok_dec : PLift ((∀ e ∈ E, (piS e.1, piS e.2.1, (-1) * e.2.2.1 + 0 * e.2.2.2 + tauX e.2.1 - tauX e.1,
      0 * e.2.2.1 + 1 * e.2.2.2 + tauY e.2.1 - tauY e.1) ∈ E) ∧
    (∀ s, piS (piS s) = s ∧ (-1) * tauX s + 0 * tauY s + tauX (piS s) = 0 ∧
      0 * tauX s + 1 * tauY s + tauY (piS s) = 0 ∧ R0c (piS s) = R0c s ∧
      (repC s = true ∨ repC (piS s) = true)) ∧
    (∀ t, rhoP (rhoP t) = t ∧ Ac (rhoP t) * (-1) + Bc (rhoP t) * 0 = Ac t ∧
      Ac (rhoP t) * 0 + Bc (rhoP t) * 1 = Bc t) ∧
    (∀ s t, Ac (rhoP t) * tauX s + Bc (rhoP t) * tauY s + Cc (piS s) (rhoP t) = Cc s t ∧
      (repB s t = true ∨ repB (piS s) (rhoP t) = true)) ∧
    sig v0 = v0) := ⟨by
  decide +kernel⟩

theorem sym_ok : (∀ e ∈ E, (piS e.1, piS e.2.1, (-1) * e.2.2.1 + 0 * e.2.2.2 + tauX e.2.1 - tauX e.1,
      0 * e.2.2.1 + 1 * e.2.2.2 + tauY e.2.1 - tauY e.1) ∈ E) ∧
    (∀ s, piS (piS s) = s ∧ (-1) * tauX s + 0 * tauY s + tauX (piS s) = 0 ∧
      0 * tauX s + 1 * tauY s + tauY (piS s) = 0 ∧ R0c (piS s) = R0c s ∧
      (repC s = true ∨ repC (piS s) = true)) ∧
    (∀ t, rhoP (rhoP t) = t ∧ Ac (rhoP t) * (-1) + Bc (rhoP t) * 0 = Ac t ∧
      Ac (rhoP t) * 0 + Bc (rhoP t) * 1 = Bc t) ∧
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
def BXn (s : Fin 9) : ℕ := tgetN 95603557 3 s.val

def BYn (s : Fin 9) : ℕ := tgetN 38085778 3 s.val

theorem nb_c0 : ∀ s : Fin 9, 0 < 3 * (Cc s 0 - (R0c s)) + 3 * (Cc s 9 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 12 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c0 : ∀ s : Fin 9, 0 < 3 * (Cc s 1 - (4)) + 4 * (Cc s 9 - (4)) + 0 * (Cc s 0 - (4)) + 11 * (3) := by
  decide +kernel

theorem nb_c1 : ∀ s : Fin 9, 0 < 3 * (Cc s 4 - (R0c s)) + 3 * (Cc s 5 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 12 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c1 : ∀ s : Fin 9, 0 < 3 * (Cc s 4 - (4)) + 3 * (Cc s 5 - (4)) + 0 * (Cc s 0 - (4)) + 12 * (3) := by
  decide +kernel

theorem nb_c2 : ∀ s : Fin 9, 0 < 1 * (Cc s 2 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 5 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c2 : ∀ s : Fin 9, 0 < 1 * (Cc s 2 - (4)) + 0 * (Cc s 0 - (4)) + 0 * (Cc s 0 - (4)) + 5 * (2) := by
  decide +kernel

theorem nb_c3 : ∀ s : Fin 9, 0 < 1 * (Cc s 7 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 5 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c3 : ∀ s : Fin 9, 0 < 1 * (Cc s 7 - (4)) + 0 * (Cc s 0 - (4)) + 0 * (Cc s 0 - (4)) + 5 * (2) := by
  decide +kernel

theorem nn_c : ∀ s : Fin 9, 0 < 2 * (Cc s 4 - (-1)) + 2 * (Cc s 9 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * (0) := by
  decide +kernel

/-- Every vertex of class s with F at most R0c s lies in the near box of class s. -/
theorem near_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ R0c s) :
    -(BXn s : ℤ) ≤ x ∧ x ≤ BXn s ∧ -(BYn s : ℤ) ≤ y ∧ y ≤ BYn s := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 9 0 (R0c s) 3 3 0 (1) (0) ((BXn s : ℤ) + 1) 12 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 5 0 (R0c s) 3 3 0 (-1) (0) ((BXn s : ℤ) + 1) 12 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 0 0 (R0c s) 1 0 0 (0) (1) ((BYn s : ℤ) + 1) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 7 0 0 (R0c s) 1 0 0 (0) (-1) ((BYn s : ℤ) + 1) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c3 s⟩ (u _) (u _) (u _) (by omega)

/-- Every vertex with F at most 4 lies in the cells |x| ≤ 2, |y| ≤ 1. -/
theorem small_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ 4) :
    -2 ≤ x ∧ x ≤ 2 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 1 9 0 (4) 3 4 0 (1) (0) (3) 11 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 5 0 (4) 3 3 0 (-1) (0) (3) 12 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 0 0 (4) 1 0 0 (0) (1) (2) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 7 0 0 (4) 1 0 0 (0) (-1) (2) 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 4 9 0 (-1) 2 2 0 (0) (0) (0) 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nn_c s⟩ (u _) (u _) (u _) (by norm_num)

/-- The vertices near v0 where the graph distance is not the largest potential, with the distance. -/
def O : List (V × ℤ) :=
  [((0, 0, 7), 0),
    ((0, 0, 8), 1),
    ((0, 1, 4), 1),
    ((1, 1, 0), 1),
    ((0, 0, 3), 2),
    ((1, 0, 2), 2)]

/-- The cells (x, y) of the vertices of O. -/
def obox (x y : ℤ) : Bool := decide (0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)

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

/-- The vertices of O have F and fv below 4 and fv nonnegative, and fv changes by at most one
along the edges at the vertices of O. -/
def O_ok_dec : PLift (∀ o ∈ O, F o.1 < 4 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 4 ∧ ∀ e ∈ E,
    (e.1 = o.1.2.2 → fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 + e.2.2.1, o.1.2.1 + e.2.2.2, e.2.1) + 1) ∧
    (e.2.1 = o.1.2.2 → fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) ≤ fv o.1 + 1 ∧
      fv o.1 ≤ fv (o.1.1 - e.2.2.1, o.1.2.1 - e.2.2.2, e.1) + 1)) := ⟨by
  decide +kernel⟩

theorem O_ok : ∀ o ∈ O, F o.1 < 4 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 4 ∧ ∀ e ∈ E,
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

def R0c_ge_dec : PLift (∀ s, 4 ≤ R0c s) := ⟨by
  decide +kernel⟩

theorem R0c_ge : ∀ s, 4 ≤ R0c s := R0c_ge_dec.down

/-- The near check computes the potentials as differences of natural numbers: at the cell (a, b) of
the near box of class s, pot = potP - potQ. -/
def apN (i : Fin 10) : ℕ := tgetN 336384 3 i.val

def amN (i : Fin 10) : ℕ := tgetN 285212682 3 i.val

def bpN (i : Fin 10) : ℕ := tgetN 481394688 3 i.val

def bmN (i : Fin 10) : ℕ := tgetN 14691 3 i.val

def kpN (s : Fin 9) (i : Fin 10) : ℕ := tgetN 272564522064298567579170749237236521239042886116401299669036183959087252730946992339771348832224201351900909201303118167736374995925588 5 (Nat.add (Nat.mul s.val 10) i.val)

def kmN (s : Fin 9) (i : Fin 10) : ℕ := tgetN 9531146842523992712129298542305930022568100020554432503695135677840172865921333919479647816295697027408826936459095575324087752327168 5 (Nat.add (Nat.mul s.val 10) i.val)

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

theorem FPn_val (s : Fin 9) (a b p : ℕ) (hp : p < 44) (hs : srcv p = s.val) :
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

theorem fvNn_eq (s : Fin 9) (a b p : ℕ) (hp : p < 44) (hs : srcv p = s.val) :
    fvNn s a b p = fv ((a : ℤ) - BXn s + dxv p, (b : ℤ) - BYn s + dyv p, tgtF p) := by
  unfold fvNn
  split_ifs with h
  · rfl
  · rw [fv_out _ _ _ h, ← FPn_val s a b p hp hs, Int.subNatNat_eq_coe]

/-- For each class s and each cell of its near box with F at most R0c s, other than v0, the position
in E of an edge along which fv decreases. -/
def nearT (s : ℕ) : ℕ :=
  match s with
  | 0 => 533996759477550787114485298438325699502582700676711961202848048414941423261650668705258292641792
  | 1 => 3498053289008681173771147320923262980791494861667264551990564443127808
  | 2 => 4889407828966324389886453222142191205405870854626972091485608859406055617622757010717630177214464
  | 3 => 0
  | 4 => 0
  | 5 => 12137795249933498653511830015455313630524401170507031433412476422008800406700650257186816
  | 6 => 45682904823545530827513064852441460360049852416
  | 7 => 300373177206122317755855717800348664495775680905917024757317427551590153917633367088926308847616
  | 8 => 342091693933236614639145546639286888097701458510894240794833952843944496751838284720536515944448
  | _ => 0

def nearE (s : Fin 9) (a b : ℕ) : ℕ := tgetN (nearT s.val) 6 (a * (2 * BYn s + 1) + b)

/-- The near check of class s. -/
def nearOK (s : Fin 9) : Bool :=
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
    have hs0 : s = 7 := Fin.ext h4
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

/-- From n = 4 on, the coordination sequence counts the level set F = n. -/
theorem a_eq_F (n : ℕ) (hn : 4 ≤ n) : a n = Set.ncard {v : V | (F v).toNat = n} := by
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
  (Finset.range 5 ×ˢ Finset.range 3 ×ˢ (Finset.univ : Finset (Fin 9))).map
    ⟨fun p => ((p.1 : ℤ) - 2, (p.2.1 : ℤ) - 1, p.2.2), fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (Prod.ext (by omega) h.2.2)⟩

theorem mem_boxF (v : V) (h : (fv v).toNat ≤ 4) : v ∈ boxF := by
  obtain ⟨x, y, s⟩ := v
  have hb : F (x, y, s) ≤ 4 := by
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

/-- Up to n = 4, a n counts the cells of the box where fv = n. -/
theorem a_small (n : ℕ) (hn : n ≤ 4) : a n = (boxF.filter fun v => (fv v).toNat = n).card := by
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
def small_dec : PLift ((List.range 4).map (fun n => (boxF.filter fun v => (fv v).toNat = n).card) = [1, 5, 9, 13]) := ⟨by
  decide +kernel⟩

/-- The coordination sequence below n = 4. -/
theorem small_vals : (List.range 4).map a = [1, 5, 9, 13] := by
  rw [List.map_congr_left (fun n hn => a_small n (by rw [List.mem_range] at hn; omega))]
  exact small_dec.down


/-! ## Counting the spheres

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. The
gradient of facet i is gc i times the primitive vector (Ap i, Bp i), so the points of class s with
pot_i = n lie on the line Ap i x + Bp i y = c with c = lev s i n, and only when gc i divides
n - Cc s i. That line is par s i c u = (al i c + Bp i u, be i c - Ap i u), and potential j is
ka i j c + Dm i j u + Cc s j there (`pot_par`). The previous facet bounds u from above, the next one
from below, and for n ≥ 7 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 10 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T (a table entry plus its offset). -/
def ctabN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

def gcV (k : ℕ) : ℕ := ctabN 161780553 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 10) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 21907080 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 516879876865 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 4

def Bp (i : Fin 10) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 549010 2 k

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

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (7 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 1645124055465003459955804924579573590112642395349797332513794811726086349964582936024618995315837350218617444316086272 4 k

def cf1N (k : ℕ) : ℤ := (cf1V k : ℤ)

def cf1 (i : Fin 10) (j : Fin 10) : ℤ := cf1N (j.val + 10 * i.val)

def cf2V (k : ℕ) : ℕ := ctabN 44378511564270246094161258119394948170381068867502011262554781112297613828851495621824257243764893924510510604923392 4 k

def cf2N (k : ℕ) : ℤ := (cf2V k : ℤ)

def cf2 (i : Fin 10) (j : Fin 10) : ℤ := cf2N (j.val + 10 * i.val)

def cf3V (k : ℕ) : ℕ := ctabN 5668146277401674875495107977562554701566168698812518515516347714127622968315552566655552 3 k

def cf3N (k : ℕ) : ℤ := (cf3V k : ℤ)

def cf3 (i : Fin 10) (j : Fin 10) : ℤ := cf3N (j.val + 10 * i.val)

def cf0V (k : ℕ) : ℕ := ctabN 307828173490261525510526647887215110336523147726029795961967230334877731278634310566060130880228652325113916563456 4 k

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
def cTV (k : ℕ) : ℕ := ctabN 478918654350278735736580332039045134466813517065220238235837576842531485482736329634490400358589076355774616 4 k

def cTN (k : ℕ) : ℤ := (cTV k : ℤ) - 4

def cT (s : Fin 9) (i : Fin 10) : ℤ := cTN (i.val + 10 * s.val)

theorem cT_eq : ∀ s : Fin 9, ∀ i : Fin 10, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 9) (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (7 - cT s i)

instance (i j : Fin 10) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 10, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 10 || j == (i + 9) % 10

/-- certC in natural numbers, for the kernel: Cc = cTV - 4, the negative terms moved across; the
previous facet of i is (i + 9) % 10, the next one (i + 1) % 10. -/
def certNat (s i j : ℕ) : Bool :=
  Nat.blt ((cf1V (j + 10 * i) + cf2V (j + 10 * i) + cf0V (j + 10 * i)) * cTV (i + 10 * s) +
      cf3V (j + 10 * i) * cTV (j + 10 * s))
    (cf1V (j + 10 * i) * (cTV ((i + 9) % 10 + 10 * s) + (if (i + 9) % 10 < i then 1 else 0)) +
      cf2V (j + 10 * i) * (cTV ((i + 1) % 10 + 10 * s) + (if (i + 1) % 10 < i then 1 else 0)) +
      cf3V (j + 10 * i) * cTV (i + 10 * s) + cf0V (j + 10 * i) * 11)

def certOK : Bool :=
  (List.range 9).all fun s => (List.range 10).all fun i => (List.range 10).all fun j =>
    nearB i j || certNat s i j

theorem certOK_eq : certOK = true := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 10, (i - 1).val = (i.val + 9) % 10 := by decide +kernel

theorem fin_next : ∀ i : Fin 10, (i + 1).val = (i.val + 1) % 10 := by decide +kernel

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 9) (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
    cf3 i j * (cT s i - cT s j) + cf0 i j * (7 - cT s i)
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
  simp only [certC, cT_eq] at cc
  by_contra hne
  have f3 : pot (par s i (lev s i n) u) i ≤ pot (par s i (lev s i n) u) j := by
    have := (ite01 (j < i)).2
    rw [hi']
    linarith [not_le.1 hne]
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 7 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ
    (Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 9, ∀ j : Fin 10, -5 ≤ Cc s j ∧ Cc s j ≤ 5 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 1 * Ac 4 + 1 * Ac 5 = 4 ∧ 1 * Bc 4 + 1 * Bc 5 = 0 ∧
    1 * Ac 0 + 1 * Ac 9 = (-4) ∧ 1 * Bc 0 + 1 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 5 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-5) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 9) :
    4 * x ≤ 2 * F (x, y, s) + 10 ∧
    4 * (-x) ≤ 2 * F (x, y, s) + 10 ∧
    5 * y ≤ 1 * F (x, y, s) + 5 ∧
    5 * (-y) ≤ 1 * F (x, y, s) + 5 := by
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
  have e2 : 1 * pot (x, y, s) 7 + 0 * pot (x, y, s) 7 =
      5 * y + 1 * Cc s 7 + 0 * Cc s 7 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 7
  have r2 := le_F (x, y, s) 7
  have k2 := Cbound s 7
  have l2 := Cbound s 7
  have e3 : 1 * pot (x, y, s) 2 + 0 * pot (x, y, s) 2 =
      5 * (-y) + 1 * Cc s 2 + 0 * Cc s 2 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 2
  have r3 := le_F (x, y, s) 2
  have k3 := Cbound s 2
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

/-! Shifting n by 10 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 730860266154 4 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 27423434281 4 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 4

def mh (i : Fin 10) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 628777100896 4 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 4

def mk (i : Fin 10) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 10, (10 : ℤ) = gc i * Lq i ∧
    10 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    10 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 9) (i : Fin 10) (n : ℤ) :
    inner s i (n + 10) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 10 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 10 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 10) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 10) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 10) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 5 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 9 × Fin 10, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 10) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqV (k : ℕ) : ℕ := ctabN 758569581 3 k

def lgqN (k : ℕ) : ℤ := (lgqV k : ℤ)

def lgq (i : Fin 10) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 10, (5 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 5 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 5 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 10, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 10 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 10) = 0 then mhN (c % 10) + mkN (c % 10) else 0

theorem gsN_eq (s : Fin 9) (i : Fin 10) (n : ℤ) :
    gsN (i.val + 10 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 10 * s.val) % 10 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (9 * 10)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhV (k : ℕ) : ℕ := ctabN 13715387160 4 k

def uhN (k : ℕ) : ℤ := (uhV k : ℤ) - 2

def uh (i : Fin 10) : ℤ := uhN i.val

def dhV (k : ℕ) : ℕ := ctabN 365437473116 4 k

def dhN (k : ℕ) : ℤ := (dhV k : ℤ)

def dh (i : Fin 10) : ℤ := dhN i.val

def ukV (k : ℕ) : ℕ := ctabN 554906948400 4 k

def ukN (k : ℕ) : ℤ := (ukV k : ℤ) - 2

def uk (i : Fin 10) : ℤ := ukN i.val

def dkV (k : ℕ) : ℕ := ctabN 846466928981 4 k

def dkN (k : ℕ) : ℤ := (dkV k : ℤ)

def dk (i : Fin 10) : ℤ := dkN i.val

def vhV (k : ℕ) : ℕ := ctabN 644695460662868364321409380881354235787220016867508113525010108884029358007621379773787464372600742133056619 4 k

def vhN (k : ℕ) : ℤ := (vhV k : ℤ) - 6

def vh (s : Fin 9) (i : Fin 10) : ℤ := vhN (i.val + 10 * s.val)

def vkV (k : ℕ) : ℕ := ctabN 507699803022732145450280833372726710810039987941114708720472110900016051844358731734493878680361113048811381 4 k

def vkN (k : ℕ) : ℤ := (vkV k : ℤ) - 6

def vk (s : Fin 9) (i : Fin 10) : ℤ := vkN (i.val + 10 * s.val)

def levT (s : Fin 9) (i : Fin 10) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 9) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_facet : ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧
    uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) := by
  decide +kernel

theorem tab_class : ∀ s : Fin 9, ∀ i : Fin 10,
    vh s i = cT s i - cT s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    vk s i = cT s i - cT s (i + 1) - (if i + 1 < i then 1 else 0) := by
  decide +kernel

theorem tab_ok (s : Fin 9) (i : Fin 10) : uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  obtain ⟨f1, f2, f3, f4⟩ := tab_facet i
  obtain ⟨c1, c2⟩ := tab_class s i
  simp only [cT_eq] at c1 c2
  exact ⟨f1, c1, f2, f3, c2, f4⟩

theorem inner_eq (s : Fin 9) (i : Fin 10) (n : ℤ) : inner s i n = innerT s i n := by
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
def ST (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 10, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 10 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 10) = 0 then
    (uhN (c % 10) * ((n - cTN c) / gcN (c % 10)) + vhN c) / dhN (c % 10) +
      (ukN (c % 10) * ((n - cTN c) / gcN (c % 10)) + vkN c) / dkN (c % 10) + 1
  else 0

theorem innerN_eq (s : Fin 9) (i : Fin 10) (n : ℤ) :
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
def STN (n : ℤ) : ℤ := ((List.range (9 * 10)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 9 × Fin 10 => innerT q.1 q.2 n)
    (fun c : Fin (9 * 10) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (9 * 10), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 9 × Fin 10 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (9 * 10) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (9 * 10), sum_range_list]

/-- The closed form's tables, packed: the steps, the values on one period from 4 and below 4. -/
def dtabV (k : ℕ) : ℕ := ctabN 25979738 5 k

def tblV (k : ℕ) : ℕ := ctabN 663615123 6 k

def initV (k : ℕ) : ℕ := ctabN 55633 4 k

/-- The step of the closed form at residue t mod 5. -/
def dv (t : ℕ) : ℕ := dtabV (t % 5)

/-- The sequence in closed form: b(n + 5) = b(n) + dv (n - 4) for n ≥ 4. -/
def b (n : ℕ) : ℕ :=
  if n < 4 then initV n else dv (n - 4) * ((n - 4) / 5) + tblV ((n - 4) % 5)

theorem b_step (n : ℕ) (hn : 4 ≤ n) : b (n + 5) = b n + dv (n - 4) := by
  rw [b, b, if_neg (show ¬ (n + 5 < 4) by omega), if_neg (show ¬ (n < 4) by omega),
    show n + 5 - 4 = n - 4 + 5 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 5)]
  ring

theorem b_shift (n : ℕ) (hn : 4 ≤ n) : b (n + 10) = b n + 2 * dv (n - 4) := by
  rw [b, b, if_neg (show ¬ (n + 10 < 4) by omega), if_neg (show ¬ (n < 4) by omega),
    show n + 10 - 4 = n - 4 + 5 * 2 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 5)]
  ring

/-- b on the residue class of 4 + j mod 5. -/
theorem b_res (k j : ℕ) (hj : j < 5) : b (5 * k + (4 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (5 * k + (4 + j) < 4) by omega),
    show 5 * k + (4 + j) - 4 = j + 5 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 5), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The growth of S over one period at each residue mod 5. -/
def GsT : List ℤ := [52, 52, 48, 48, 52]

theorem Gs_tab : ∀ r : ℕ, r < 5 → GsN (r : ℤ) = GsT.getD r 0 := by
  decide +kernel

/-- The growth of b over 10 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 5 → 2 * (dv t : ℤ) = GsT.getD ((4 + t) % 5) 0 := by
  decide +kernel

theorem grow (n : ℕ) (_hn : 4 ≤ n) : 2 * (dv (n - 4) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 4) % 5) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 4) % 5) = dv (n - 4) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 5 ∣ 5)]
  have e2 : (4 + (n - 4) % 5) % 5 = n % 5 := by omega
  rw [e1, e2, ← Gs_tab (n % 5) (Nat.mod_lt _ (by norm_num)), ← Gs_eq_GsN] at h1
  rw [h1]
  have e3 : (((n % 5 : ℕ) : ℤ) + 5 * ((n / 5 : ℕ) : ℤ)) = n := by omega
  rw [← e3, Gs_periodic]

/-- One kernel pass over n = 7, ..., 16: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 10 →
    ((List.range (9 * 10)).all fun c => decide (0 ≤ innerN c (7 + (r : ℤ)))) = true ∧
      STN (7 + (r : ℤ)) = b (7 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 7 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 9) (i : Fin 10) (n : ℤ) (hn : 7 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 7 + t := ⟨(n - 7).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 10
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 10 * s.val < 9 * 10 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 10) (by omega) (by omega)
      have e : (7 : ℤ) + t = (7 + (t - 10 : ℕ)) + 10 := by
        push_cast [Nat.cast_sub (by omega : 10 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 7 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 7 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 17
    · obtain ⟨r, rfl⟩ : ∃ r, n = 7 + r := ⟨n - 7, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 10) (by omega) (by omega)
      have h2 := S_shift ((n - 10 : ℕ) : ℤ)
      have h3 := b_shift (n - 10) (by omega)
      have h4 := grow (n - 10) (by omega)
      rw [show n - 10 + 10 = n by omega] at h3
      rw [show ((n - 10 : ℕ) : ℤ) + 10 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 6 lie in the box -5 ≤ x ≤ 5, -2 ≤ y ≤ 2 (`small_box`), and
the kernel checks that those of the box are the 104 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 9) (h : F (x, y, s) ≤ 6) :
    -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 6, with their values of F. -/
def smallV : List (V × ℤ) :=
  [((0, 0, 6), 1), ((0, 0, 7), 1), ((1, 0, 6), 1), (((-1), 0, 7), 2), ((0, 0, 5), 2), ((0, 0, 8), 2), ((0, 1, 0), 2), ((0, 1, 1), 2), ((0, 1, 4), 2), ((1, 0, 5), 2), ((1, 0, 7), 2), ((1, 1, 0), 2), ((1, 1, 4), 2), (((-1), 0, 6), 3), (((-1), 0, 8), 3), (((-1), 1, 1), 3), (((-1), 1, 4), 3), ((0, 0, 1), 3), ((0, 0, 2), 3), ((0, 0, 3), 3), ((0, 1, 3), 3), ((1, 0, 2), 3), ((1, 0, 3), 3), ((1, 0, 8), 3), ((1, 1, 1), 3), ((1, 1, 2), 3), ((2, 0, 6), 3), ((2, 1, 0), 3), (((-2), 0, 7), 4), (((-1), 0, 1), 4), (((-1), 0, 3), 4), (((-1), 0, 5), 4), (((-1), 1, 0), 4), (((-1), 1, 3), 4), ((0, 0, 4), 4), ((0, 1, 2), 4), ((0, 1, 5), 4), ((0, 1, 8), 4), ((1, 0, 0), 4), ((1, 0, 1), 4), ((1, 1, 3), 4), ((1, 1, 5), 4), ((2, 0, 2), 4), ((2, 0, 5), 4), ((2, 0, 7), 4), ((2, 1, 2), 4), ((2, 1, 4), 4), (((-2), 0, 6), 5), (((-2), 0, 8), 5), (((-2), 1, 1), 5), (((-2), 1, 4), 5), (((-1), 0, 2), 5), (((-1), 0, 4), 5), (((-1), 1, 2), 5), (((-1), 1, 5), 5), (((-1), 1, 8), 5), ((0, (-1), 6), 5), ((0, (-1), 7), 5), ((0, 0, 0), 5), ((0, 1, 6), 5), ((0, 1, 7), 5), ((1, (-1), 6), 5), ((1, 0, 4), 5), ((1, 1, 6), 5), ((1, 1, 8), 5), ((2, 0, 0), 5), ((2, 0, 3), 5), ((2, 0, 8), 5), ((2, 1, 1), 5), ((2, 1, 3), 5), ((2, 1, 5), 5), ((3, 0, 6), 5), ((3, 1, 0), 5), (((-3), 0, 7), 6), (((-2), 0, 1), 6), (((-2), 0, 3), 6), (((-2), 0, 5), 6), (((-2), 1, 0), 6), (((-2), 1, 3), 6), (((-2), 1, 8), 6), (((-1), (-1), 6), 6), (((-1), (-1), 7), 6), (((-1), 0, 0), 6), (((-1), 1, 6), 6), (((-1), 1, 7), 6), ((0, (-1), 5), 6), ((0, (-1), 8), 6), ((0, 2, 0), 6), ((0, 2, 4), 6), ((1, (-1), 5), 6), ((1, (-1), 7), 6), ((1, 1, 7), 6), ((1, 2, 0), 6), ((1, 2, 4), 6), ((2, (-1), 6), 6), ((2, 0, 1), 6), ((2, 0, 4), 6), ((2, 1, 6), 6), ((2, 1, 8), 6), ((3, 0, 2), 6), ((3, 0, 5), 6), ((3, 0, 7), 6), ((3, 1, 2), 6), ((3, 1, 4), 6)]

def smallL : List V := smallV.map Prod.fst

theorem smallV_ok : (smallV.all fun q => decide (F q.1 = q.2)) = true := by
  decide +kernel

/-- The potentials, packed: Ac = ATV - 2, Bc = BTV - 5. -/
def ATV (k : ℕ) : ℕ := ctabN 21907080 3 k

def ATN (k : ℕ) : ℤ := (ATV k : ℤ) - 2

def AT (i : Fin 10) : ℤ := ATN i.val

def BTV (k : ℕ) : ℕ := ctabN 591254392850 4 k

def BTN (k : ℕ) : ℤ := (BTV k : ℤ) - 5

def BT (i : Fin 10) : ℤ := BTN i.val

theorem AB_eq : ∀ i : Fin 10, AT i = Ac i ∧ BT i = Bc i := by
  decide +kernel

/-- Some potential exceeds 6 at the box point ((a : ℤ) - 5, (b : ℤ) - 2, s), in natural
numbers: the negative terms moved across. -/
def bigNat (a b s : ℕ) : Bool :=
  (List.range 10).any fun i =>
    Nat.blt (10 + ATV i * 5 + 2 * a + BTV i * 2 + 5 * b)
      (ATV i * a + 10 + BTV i * b + 10 + cTV (i + 10 * s))

theorem big_pot (a b : ℕ) (s : Fin 9) (h : bigNat a b s.val = true) :
    (6 : ℤ) < F ((a : ℤ) - 5, (b : ℤ) - 2, s) := by
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  have hl := (Nat.cast_lt (α := ℤ)).mpr (Nat.blt_eq.mp hb)
  have hp := le_F ((a : ℤ) - 5, (b : ℤ) - 2, s) ⟨i, hi⟩
  obtain ⟨eA, eB⟩ := AB_eq ⟨i, hi⟩
  have e3 := cT_eq s ⟨i, hi⟩
  simp only [pot] at hp
  rw [← eA, ← eB, ← e3] at hp
  simp only [AT, BT, ATN, BTN, cT, cTN] at hp
  push_cast at hl hp
  ring_nf at hl hp ⊢
  linarith

def smallOK : Bool :=
  (List.range 11).all fun a => (List.range 5).all fun b => (List.finRange 9).all fun s =>
    bigNat a b s.val || decide (((a : ℤ) - 5, (b : ℤ) - 2, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 6) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 5).toNat (by omega) (y + 2).toNat (by omega) s
  have ex : (((x + 5).toNat : ℕ) : ℤ) - 5 = x := by omega
  have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h1 | h1
  · have := big_pot _ _ s h1
    rw [ex, ey] at this
    omega
  · rw [ex, ey] at h1
    exact h1

theorem cnt_small (n : ℤ) (hn : n ≤ 6) :
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

/-- The small spheres from 4 on, in closed form. -/
theorem small_ok : ∀ n : ℕ, 4 ≤ n → n < 7 →
    (((smallV.filter (fun q => decide (q.2 = (n : ℤ)))).map Prod.fst).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n from n = 4 on (`a_eq_cnt`, from `a_eq_F`), and `small_vals`
lists the terms below 4. The terms from 4 to 6 are counted in `smallL`, those from 7 on
are S(n), and all agree with the closed form b (`a_eq_b`). The step from n to n + 5, the closed form
per residue (`a_closed`), the controls, the recurrence and the g.f. follow, their base cases checked by
the kernel on b. -/

theorem a_eq_cnt (n : ℕ) (hn : 4 ≤ n) : a n = cnt n := by
  rw [a_eq_F n hn, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 7 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt n (by omega)]
  exact cnt_eq_S n (by exact_mod_cast hn)

theorem a_lt_R0 (n : ℕ) (hn : n < 4) : a n = b n := by
  have h : (List.range 4).map a = (List.range 4).map b := by
    rw [small_vals]
    decide +kernel
  exact List.map_inj_left.1 h n (List.mem_range.2 hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 4 ∨ (4 ≤ n ∧ n < 7) ∨ 7 ≤ n by omega) with h | ⟨h1, h2⟩ | h
  · exact a_lt_R0 n h
  · rw [a_eq_cnt n h1, cnt_small _ (by omega)]
    exact small_ok n h1 h2
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 5) = a(n) + dv (n - 4) for n ≥ 4. -/
theorem a_step (n : ℕ) (hn : 4 ≤ n) : a (n + 5) = a n + dv (n - 4) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-- The steps and the values on one period, by the kernel. -/
theorem closed_vals : dv 0 = 26 ∧ tblV 0 = 19 ∧ dv 1 = 26 ∧ tblV 1 = 26 ∧ dv 2 = 26 ∧ tblV 2 = 31 ∧ dv 3 = 24 ∧ tblV 3 = 35 ∧ dv 4 = 24 ∧ tblV 4 = 39 := by
  decide +kernel

/-- The closed form per residue of n mod 5, for n ≥ 4. -/
theorem a_closed (k : ℕ) :
    a (5 * k + 4) = 26 * k + 19 ∧
    a (5 * k + 5) = 26 * k + 26 ∧
    a (5 * k + 6) = 26 * k + 31 ∧
    a (5 * k + 7) = 24 * k + 35 ∧
    a (5 * k + 8) = 24 * k + 39 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := closed_vals
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show 5 * k + 4 = 5 * k + (4 + 0) from rfl, b_res k 0 (by norm_num), c0, c1]
  · rw [show 5 * k + 5 = 5 * k + (4 + 1) from rfl, b_res k 1 (by norm_num), c2, c3]
  · rw [show 5 * k + 6 = 5 * k + (4 + 2) from rfl, b_res k 2 (by norm_num), c4, c5]
  · rw [show 5 * k + 7 = 5 * k + (4 + 3) from rfl, b_res k 3 (by norm_num), c6, c7]
  · rw [show 5 * k + 8 = 5 * k + (4 + 4) from rfl, b_res k 4 (by norm_num), c8, c9]

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 9, 13, 19, 26, 31, 35, 39, 45, 52, 57, 59, 63, 71, 78, 83, 83, 87, 97, 104, 109, 107, 111, 123, 130, 135, 131, 135, 149, 156, 161, 155, 159, 175, 182, 187, 179, 183, 201, 208, 213, 203, 207, 227, 234, 239, 227, 231, 253] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 5 → (dv (t + 10) : ℤ) = 2 * (dv (t + 5) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 10) : ℤ) = 2 * (dv (t + 5) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 5 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 5, e 10]
  exact drec_base (t % 5) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 5 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 5 → (b (q + 14) : ℤ) = 2 * b (q + 9) - b (q + 4) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 14) : ℤ) = 2 * b (q + 9) - b (q + 4) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 5 ∨ 5 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 5 := ⟨q - 5, by omega⟩
      have h0 : (b (v + 14) : ℤ) = 2 * b (v + 9) - b (v + 4) := ih (v + 0) (by omega)
      have s4 : b (v + 9) = b (v + 4) + dv (v + 0) := by
        have h := b_step (v + 4) (by omega)
        rw [show v + 4 + 5 = v + 9 by omega,
          show v + 4 - 4 = v + 0 by omega] at h
        exact h
      have s9 : b (v + 14) = b (v + 9) + dv (v + 5) := by
        have h := b_step (v + 9) (by omega)
        rw [show v + 9 + 5 = v + 14 by omega,
          show v + 9 - 4 = v + 5 by omega] at h
        exact h
      have s14 : b (v + 19) = b (v + 14) + dv (v + 10) := by
        have h := b_step (v + 14) (by omega)
        rw [show v + 14 + 5 = v + 19 by omega,
          show v + 14 - 4 = v + 10 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 19) : ℤ) = 2 * b (v + 14) - b (v + 9)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 13 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 14 := ⟨n - 14, by omega⟩
  rw [show q + 14 - 5 = q + 9 by omega, show q + 14 - 10 = q + 4 by omega]
  simp only [a_eq_b]
  exact b_recur q

/-- The coefficients of the g.f. below 14, by the kernel. -/
theorem gf_base : ∀ n : ℕ, n < 14 → 1 * (b n : ℤ) - 2 * (if 5 ≤ n then (b (n - 5) : ℤ) else 0) + 1 * (if 10 ≤ n then (b (n - 10) : ℤ) else 0) = (if n = 0 then (1 : ℤ) else 0) + (if n = 1 then (1 : ℤ) else 0) * 5 + (if n = 2 then (1 : ℤ) else 0) * 9 + (if n = 3 then (1 : ℤ) else 0) * 13 + (if n = 4 then (1 : ℤ) else 0) * 19 + (if n = 5 then (1 : ℤ) else 0) * 24 + (if n = 6 then (1 : ℤ) else 0) * 21 + (if n = 7 then (1 : ℤ) else 0) * 17 + (if n = 8 then (1 : ℤ) else 0) * 13 + (if n = 9 then (1 : ℤ) else 0) * 7 + (if n = 10 then (1 : ℤ) else 0) * 1 - (if n = 12 then (1 : ℤ) else 0) * 2 - (if n = 13 then (1 : ℤ) else 0) * 2 := by
  decide +kernel

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      -2 * X ^ 13 - 2 * X ^ 12 + X ^ 10 + 7 * X ^ 9 + 13 * X ^ 8 + 17 * X ^ 7 + 21 * X ^ 6 + 24 * X ^ 5 + 19 * X ^ 4 + 13 * X ^ 3 + 9 * X ^ 2 + 5 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * (X ^ 10 - 2 * X ^ 5 + 1) = C 1 * A - C 2 * (A * X ^ 5) + C 1 * (A * X ^ 10) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : (-2 * X ^ 13 - 2 * X ^ 12 + X ^ 10 + 7 * X ^ 9 + 13 * X ^ 8 + 17 * X ^ 7 + 21 * X ^ 6 + 24 * X ^ 5 + 19 * X ^ 4 + 13 * X ^ 3 + 9 * X ^ 2 + 5 * X + 1 : ℚ⟦X⟧) = C 1 + X ^ 1 * C 5 + X ^ 2 * C 9 + X ^ 3 * C 13 + X ^ 4 * C 19 + X ^ 5 * C 24 + X ^ 6 * C 21 + X ^ 7 * C 17 + X ^ 8 * C 13 + X ^ 9 * C 7 + X ^ 10 * C 1 - X ^ 12 * C 2 - X ^ 13 * C 2 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 14 with hn | hn
  · have h := congrArg (fun z : ℤ => (z : ℚ)) (gf_base n hn)
    push_cast at h
    linarith
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 14 := ⟨n - 14, by omega⟩
    have h : (b (q + 14) : ℤ) = 2 * b (q + 9) - b (q + 4) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 14 - 5 = q + 9 by omega, show q + 14 - 10 = q + 4 by omega, show 5 ≤ q + 14 by omega, show 10 ≤ q + 14 by omega, show ¬ q + 14 = 0 by omega, show ¬ q + 14 = 1 by omega, show ¬ q + 14 = 2 by omega, show ¬ q + 14 = 3 by omega, show ¬ q + 14 = 4 by omega, show ¬ q + 14 = 5 by omega, show ¬ q + 14 = 6 by omega, show ¬ q + 14 = 7 by omega, show ¬ q + 14 = 8 by omega, show ¬ q + 14 = 9 by omega, show ¬ q + 14 = 10 by omega, show ¬ q + 14 = 12 by omega, show ¬ q + 14 = 13 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      -2 * X ^ 13 - 2 * X ^ 12 + X ^ 10 + 7 * X ^ 9 + 13 * X ^ 8 + 17 * X ^ 7 + 21 * X ^ 6 + 24 * X ^ 5 + 19 * X ^ 4 + 13 * X ^ 3 + 9 * X ^ 2 + 5 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 13 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 9, 13, 19, 26, 31, 35, 39, 45, 52, 57, 59, 63, 71, 78, 83, 83, 87, 97, 104, 109, 107, 111, 123, 130, 135, 131, 135, 149, 156, 161, 155, 159, 175, 182, 187, 179, 183, 201, 208, 213, 203, 207, 227, 234, 239, 227, 231, 253] := Count.controls

/-- The step a(n + 5) = a(n) + Count.dv (n - 4) for n ≥ 4. -/
theorem a_step (n : ℕ) (hn : 4 ≤ n) : a (n + 5) = a n + Count.dv (n - 4) := Count.a_step n hn

/-- The closed form per residue of n mod 5, for n ≥ 4. -/
theorem a_closed (k : ℕ) :
    a (5 * k + 4) = 26 * k + 19 ∧
    a (5 * k + 5) = 26 * k + 26 ∧
    a (5 * k + 6) = 26 * k + 31 ∧
    a (5 * k + 7) = 24 * k + 35 ∧
    a (5 * k + 8) = 24 * k + 39 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 10 - 2 * X ^ 5 + 1) =
      -2 * X ^ 13 - 2 * X ^ 12 + X ^ 10 + 7 * X ^ 9 + 13 * X ^ 8 + 17 * X ^ 7 + 21 * X ^ 6 + 24 * X ^ 5 + 19 * X ^ 4 + 13 * X ^ 3 + 9 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 2 * a (n - 5) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a314772

theorem OMA.solution : type_of% @OMA.S_oeis_a314772.main :=
  OMA.S_oeis_a314772.conjecture
