import OMAStatements.S_oeis_a311007

namespace OMA.S_oeis_a311007






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
  | 0 => 150037812845498
  | 1 => 131281976994473
  | 2 => 151293067294599
  | 3 => 151219767707800
  | 4 => 169975603558825
  | 5 => 133700899141494
  | 6 => 113763376863639
  | 7 => 132454788274584
  | 8 => 132528087861383
  | _ => 0

/-- The potential t is Ac t * x + Bc t * y + Cc s t at (x, y, s) (packed tables). -/
def Ac (i : Fin 12) : ℤ := tget 95080572163941 4 8 i.val

def Bc (i : Fin 12) : ℤ := tget 188895788876886 4 8 i.val

def Cc (s : Fin 9) (i : Fin 12) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The potential t at v. -/
def pot (v : V) (i : Fin 12) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest potential at v. -/
def F (v : V) : ℤ := max (max (max (max (max (max (max (max (max (max (max (pot v 0) (pot v 1)) (pot v 2)) (pot v 3)) (pot v 4)) (pot v 5)) (pot v 6)) (pot v 7)) (pot v 8)) (pot v 9)) (pot v 10)) (pot v 11)

theorem le_F0 (v : V) : pot v 0 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))))))))))
theorem le_F1 (v : V) : pot v 1 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))))))
theorem le_F2 (v : V) : pot v 2 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))))))
theorem le_F3 (v : V) : pot v 3 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))))
theorem le_F4 (v : V) : pot v 4 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))))
theorem le_F5 (v : V) : pot v 5 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))))
theorem le_F6 (v : V) : pot v 6 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))))
theorem le_F7 (v : V) : pot v 7 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))
theorem le_F8 (v : V) : pot v 8 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
theorem le_F9 (v : V) : pot v 9 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
theorem le_F10 (v : V) : pot v 10 ≤ F v := le_max_of_le_left (le_max_right _ _)
theorem le_F11 (v : V) : pot v 11 ≤ F v := le_max_right _ _

theorem le_F (v : V) (i : Fin 12) : pot v i ≤ F v := by
  fin_cases i
  exacts [le_F0 v, le_F1 v, le_F2 v, le_F3 v, le_F4 v, le_F5 v, le_F6 v, le_F7 v, le_F8 v, le_F9 v, le_F10 v, le_F11 v]

theorem F_le (v : V) (t : ℤ) (h0 : pot v 0 ≤ t) (h1 : pot v 1 ≤ t) (h2 : pot v 2 ≤ t) (h3 : pot v 3 ≤ t) (h4 : pot v 4 ≤ t) (h5 : pot v 5 ≤ t) (h6 : pot v 6 ≤ t) (h7 : pot v 7 ≤ t) (h8 : pot v 8 ≤ t) (h9 : pot v 9 ≤ t) (h10 : pot v 10 ≤ t) (h11 : pot v 11 ≤ t) : F v ≤ t :=
  max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

theorem F_le_all (v : V) (t : ℤ) (h : ∀ i, pot v i ≤ t) : F v ≤ t :=
  F_le v t (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11)

theorem max_ex {v : V} {a b : ℤ} (ha : ∃ i, a = pot v i) (hb : ∃ i, b = pot v i) :
    ∃ i, max a b = pot v i := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem exists_F (v : V) : ∃ i, F v = pot v i :=
  max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (max_ex (⟨0, rfl⟩) ⟨1, rfl⟩) ⟨2, rfl⟩) ⟨3, rfl⟩) ⟨4, rfl⟩) ⟨5, rfl⟩) ⟨6, rfl⟩) ⟨7, rfl⟩) ⟨8, rfl⟩) ⟨9, rfl⟩) ⟨10, rfl⟩) ⟨11, rfl⟩

/-- The level of class s beyond which the far argument runs (the near box of class s covers the rest). -/
def R0N (s : Fin 9) : ℕ := tgetN 46135159692 4 s.val

def R0c (s : Fin 9) : ℤ := (R0N s : ℤ)

/-- The pairs (class s, potential t) and the classes whose rule, far, side and near checks are made;
the others follow by the symmetry sig. -/
def repB (s : Fin 9) (t : Fin 12) : Bool := decide (tgetN 4991374243119884567079870001215 1 (s.val * 12 + t.val) = 1)

def repC (s : Fin 9) : Bool := decide (tgetN 319 1 s.val = 1)

/-- A symmetry of order 2 of the graph that fixes v0 and permutes the potentials:
(x, y, s) ↦ (1 x + 0 y + tauX s, 0 x + (-1) y + tauY s, piS s), and potential t goes to rhoP t. -/
def piS (s : Fin 9) : Fin 9 := ⟨tgetN 34987063056 4 s.val % 9, Nat.mod_lt _ (by norm_num)⟩

def tauX (s : Fin 9) : ℤ := tget 36650387592 4 8 s.val

def tauY (s : Fin 9) : ℤ := tget 36650387609 4 8 s.val

def rhoP (t : Fin 12) : Fin 12 := ⟨tgetN 1250999896491 4 t.val % 12, Nat.mod_lt _ (by norm_num)⟩

def sig (v : V) : V :=
  (1 * v.1 + 0 * v.2.1 + tauX v.2.2, 0 * v.1 + (-1) * v.2.1 + tauY v.2.2, piS v.2.2)

/-- The change of the potential j along the edge e. -/
def dl (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 12) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

/-- Along an edge e the potential j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 12) :
    pot (x + e.2.2.1, y + e.2.2.2, e.2.1) j = pot (x, y, e.1) j + dl e j := by
  simp only [pot, dl]
  ring

theorem pair_of {a f b : ℤ} (hl : a ≤ f) (hf : f = b) : a ≤ b + 0 := by omega

theorem bound_of {r f b : ℤ} (hr : r < f) (hf : f = b) : r + 1 ≤ b := by omega

theorem not_pair2 {a b : ℤ} (h : ¬ a ≤ b + (-2)) : b ≤ a + 1 := by omega

/-- Three facts pot a_k ≤ pot b_k + t_k and a bound r ≤ pot i0 at (x, y, s), with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas (x y : ℤ) (s : Fin 9) (a1 b1 a2 b2 a3 b3 i0 : Fin 12) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
def nb (t : Fin 12) (k : Fin 4) : Fin 12 :=
  ⟨(tget 4330321939413903678163334826434413442067052390274506432779 4 0 (t.val * 4 + k.val)).toNat % 12, Nat.mod_lt _ (by norm_num)⟩

/-- The slot k of t holds another potential. -/
def real (t : Fin 12) (k : Fin 4) : Bool := decide (nb t k ≠ t)

/-- The potential t is a facet: a slot on each side cannot both come within 1 of t beyond R0c. -/
def facetB (t : Fin 12) : Bool := decide (tget 2925 1 0 t.val = 1)

/-- The potential j is neither t nor in a slot of t. -/
def nonadj (t j : Fin 12) : Bool :=
  decide (j ≠ t) && decide (j ≠ nb t 0) && decide (j ≠ nb t 1) && decide (j ≠ nb t 2) && decide (j ≠ nb t 3)

/-- Certificates of the far facts, the same for every class: for maximal potential t and a potential
j that is not a neighbor of t, the fields k1, k2, m1, m2, m0, mj of entry t * 12 + j give the facts
pot k1 ≤ pot t, pot k2 ≤ pot t, R0c s + 1 ≤ pot t and pot t ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fd (t j : Fin 12) (f : ℕ) : ℤ := tget 1759166519567235271548216725855753019509390840819600004666870213465242185007405846075097381211443507514533830410646152815715285904284461185608872823471847941919887155515233638856225230355229848364463819283858813111717223959234956908633617160855757373194134501005058629821214128189280770179266886318331013818981043032030044859835850846578634606593857527617190368620856919436313485586766142104752953797099453249527740642794362281511766750098039610998452872284463092065443324345219071815860261674508814184156097001081187698653870838960265496700449542082124271065346068679271884334388759382933751065636402155293134230991550937487945487265504576993232246837094559427123872540471411910201772003336211320847563509041368367738975166536011506939774573644161683180430902967958232891773033201656889784815095379836204747553996170369642300802018893897844247121662150994502525090422138294169052157335342482188697988466420328666611676839364831268028756691351803853520422141185899818299180710510427661567163693675545374427833443672529373818684193669955884703972293341158720586243432981506393960808365829763475213117492865383048198282736491862988889019500017984544963712005412546601881682967398939296493297513538669965568669060712457627190831534079188437513433002154081972007144390614409025399044072145930410800913357792253801171102102395331782015946523369623266541912927797874404609907314103564774167413726329102990802359401941037750233464572164837718293700833309421796619824687733526931239054276318150989123753502823323906550655199139180507336548812624823539983509846816327712 6 32 ((t.val * 12 + j.val) * 6 + f)

def fk1 (t j : Fin 12) : Fin 12 := ⟨(fd t j 0).toNat % 12, Nat.mod_lt _ (by norm_num)⟩

def fk2 (t j : Fin 12) : Fin 12 := ⟨(fd t j 1).toNat % 12, Nat.mod_lt _ (by norm_num)⟩

/-- The x and y parts of the far certificate of (t, j) cancel. -/
def farXY (t j : Fin 12) : Bool :=
  decide (0 ≤ fd t j 2 ∧ 0 ≤ fd t j 3 ∧ 0 ≤ fd t j 5 ∧ 0 ≤ fd t j 4 ∧
    fd t j 2 * (Ac (fk1 t j) - Ac t) + fd t j 3 * (Ac (fk2 t j) - Ac t) + fd t j 5 * (Ac t - Ac j) -
      fd t j 4 * Ac t = 0 ∧
    fd t j 2 * (Bc (fk1 t j) - Bc t) + fd t j 3 * (Bc (fk2 t j) - Bc t) + fd t j 5 * (Bc t - Bc j) -
      fd t j 4 * Bc t = 0)

/-- The constants of the far certificate of (t, j) at class s add up to a positive number. -/
def farC (s : Fin 9) (t j : Fin 12) : Bool :=
  decide (0 < fd t j 2 * (Cc s (fk1 t j) - Cc s t - 0) + fd t j 3 * (Cc s (fk2 t j) - Cc s t - 0) +
    fd t j 5 * (Cc s t - Cc s j - 1) + fd t j 4 * (R0c s + 1 - Cc s t))

/-- The far certificates of the maximal potential t are valid. -/
def farsOK (t : Fin 12) : Bool :=
  (List.finRange 12).all fun j => !nonadj t j || (farXY t j && (List.finRange 9).all fun s => !repB s t || farC s t j)

/-- Beyond F = R0c s, a potential that is not a neighbor of a maximal potential t has slack at least 2. -/
theorem far (s : Fin 9) (t j : Fin 12) (hxy : farXY t j = true) (hc0 : farC s t j = true) (x y : ℤ)
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
def sd (t : Fin 12) (i f : ℕ) : ℤ := tget 8886957272266737882938328747367917008267156132666738162500314429985170432191449387577036451369582503953596722355574327079787871193153869687693334516154237088164437532677742483106849003806401159616729080069240028459778576742264076933097447341289178289764410968357473741976036596059050685255567452913036040338102813255688289178455558890067818991793583721154500112 5 16 ((t.val * 4 + i) * 5 + f)

def sk (t : Fin 12) (i : ℕ) : Fin 12 := ⟨(sd t i 0).toNat % 12, Nat.mod_lt _ (by norm_num)⟩

def sideXY (t : Fin 12) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 ≤ sd t i 1 ∧ 0 ≤ sd t i 2 ∧ 0 ≤ sd t i 3 ∧ 0 ≤ sd t i 4 ∧
    sd t i 1 * (Ac (sk t i) - Ac t) + sd t i 2 * (Ac t - Ac (nb t kl)) + sd t i 3 * (Ac t - Ac (nb t kr)) -
      sd t i 4 * Ac t = 0 ∧
    sd t i 1 * (Bc (sk t i) - Bc t) + sd t i 2 * (Bc t - Bc (nb t kl)) + sd t i 3 * (Bc t - Bc (nb t kr)) -
      sd t i 4 * Bc t = 0)

def sideC (s : Fin 9) (t : Fin 12) (kl kr : Fin 4) (i : ℕ) : Bool :=
  decide (0 < sd t i 1 * (Cc s (sk t i) - Cc s t - 0) + sd t i 2 * (Cc s t - Cc s (nb t kl) - 1) +
    sd t i 3 * (Cc s t - Cc s (nb t kr) - 1) + sd t i 4 * (R0c s + 1 - Cc s t))

def sideOK (t : Fin 12) (kl kr : Fin 4) (i : ℕ) : Bool :=
  !(real t kl && real t kr) || (sideXY t kl kr i && (List.finRange 9).all fun s => !repB s t || sideC s t kl kr i)

/-- All side certificates are valid. -/
def sidesOK : Bool :=
  (List.finRange 12).all fun t =>
    !facetB t || (sideOK t 0 2 0 && sideOK t 0 3 1 && sideOK t 1 2 2 && sideOK t 1 3 3)

/-- Beyond F = R0c s, a facet t has no slot on each side within 1 of it. -/
theorem side (s : Fin 9) (t : Fin 12) (kl kr : Fin 4) (i : ℕ) (hxy : sideXY t kl kr i = true)
    (hc0 : sideC s t kl kr i = true) (x y : ℤ) (hL : pot (x, y, s) t ≤ pot (x, y, s) (nb t kl) + 1)
    (hR : pot (x, y, s) t ≤ pot (x, y, s) (nb t kr) + 1) (h : F (x, y, s) = pot (x, y, s) t)
    (hF : R0c s < F (x, y, s)) : False := by
  have q := of_decide_eq_true hxy
  exact farkas x y s (sk t i) t t (nb t kl) t (nb t kr) t 0 1 1 (R0c s + 1) (sd t i 1) (sd t i 2) (sd t i 3)
    (sd t i 4) ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2, of_decide_eq_true hc0⟩
    (pair_of (le_F _ _) h) hL hR (bound_of hF h)

/-- The edges of E by position p: source and target class, cell offset, and the potential changes dl
(entry p * 12 + j). -/
def srcv (p : ℕ) : ℕ := tgetN 11893730683933113775218432623137950171992064 4 p

def tgtv (p : ℕ) : ℕ := tgetN 10307900616941190063983878923336910546011729 4 p

def tgtF (p : ℕ) : Fin 9 := ⟨tgtv p % 9, Nat.mod_lt _ (by norm_num)⟩

def dxv (p : ℕ) : ℤ := tget 11894071054916591876407680188079467376707448 4 8 p

def dyv (p : ℕ) : ℤ := tget 11893730772549665675490438778561995798448248 4 8 p

/-- dlv p j + 8, as a natural number (the rule checks compare naturals). -/
def dlvN (p : ℕ) (j : Fin 12) : ℕ := tgetN 8065274054148453934173199115124279174406368994181444474381767900249164663635068230318442015607209737777180376149276734408662951311640485425151807139752292782849981842438413790112238477463470363006052439362216128981171345232548948535186541853859593547266821721305269413524406038797718647741122603773186043808038981862811956960135954528952323607892949391458074080465658498520695697731875556430014327367311403587120534635193285618763874332793509447421551721810676733710209462474567979025786768071634285881178271536662550391 4 (p * 12 + j.val)

def dlv (p : ℕ) (j : Fin 12) : ℤ := (dlvN p j : ℤ) - 8

/-- The edge tables agree with the edges of a list l from position p on, every edge moves, and every
potential changes by at most one along every edge. -/
def dlOKl : List (Fin 9 × Fin 9 × ℤ × ℤ) → ℕ → Bool
  | [], _ => true
  | e :: l, p => decide (srcv p = e.1.val ∧ tgtv p = e.2.1.val ∧ dxv p = e.2.2.1 ∧ dyv p = e.2.2.2 ∧
        (e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1)) &&
      ((List.finRange 12).all fun j => decide (dlv p j = dl e j ∧ dl e j ≤ 1 ∧ -dl e j ≤ 1)) && dlOKl l (p + 1)

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
def padOK (t : Fin 12) (c0 c1 c2 c3 : ℕ) : Bool :=
  (real t 0 || decide (c0 = 0)) && (real t 1 || decide (c1 = 0)) && (real t 2 || decide (c2 = 0)) &&
    (real t 3 || decide (c3 = 0))

def closeL (t : Fin 12) (c0 c1 : ℕ) : Bool := (real t 0 && decide (c0 ≤ 1)) || (real t 1 && decide (c1 ≤ 1))

def closeR (t : Fin 12) (c2 c3 : ℕ) : Bool := (real t 2 && decide (c2 ≤ 1)) || (real t 3 && decide (c3 ≤ 1))

def adm (t : Fin 12) (c0 c1 c2 c3 : ℕ) : Bool :=
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
  | 0 => 21265084243945108417682886677109855144724163627653712796805082029758650252755505220115223756328417085918711290039194128099949813438654865832628767883009269083134982243435547036740486389778387576953022511791076826928601710081957879877924847882482082057650575443891489903343354611831178977574748693687706760056775219140162063470789096175374975563698954411886711343900196636900293029942614699636651267709495324939182000486270670279668139203921407165832122458589990725347244426164164518924605802488817951108125837533827931731394171796056855510707363940981610087243387072289521202011171914045251559966647870309893613480278650158364142946861650440505052011759159563273710225767508093748827544232364390401879179459446566298814811951398218724361036835035885428410046162042864009596784938109949638970208098074475239238696255291439777490051287269000669411551926119904957640508437625359303203927455531237351916107462426027587166052738981744410389761863990952283359420308928055170228404706469611940128091859036482610892710272056771643815162865058743955944571839993964371178816854639339284594688
  | 1 => 21265084243945108417682886677109855144724163627653712796805082029758650252755505220115223756328417085918711290039194128099949813438654865832628767883009269083134982243435547036740486389778387576953022511791076826928601710081957879877924847882482082057650575443891489903343354611831178977574748693687706760056775219140162063470789096175374975563698954411886711343900196636900293029942614699636651267709495324939182000486270670279668139203921407165832122458589990725347244426164164518924605802488817951108125837533827931731394171796056855510707363941114693007388282403302161230338250820847686440720485219992065752974227863747481241257756196349843222896392338111460382471676278537514648528848189291088682215945485162037007971567098877099605601681050703587748241241236456629872942896635331807063367180598865082622716995031673526855490392461033688118118783717108982970947176586196472013109208342720211700455246891244293769099812200285388229268714441076079939742230367437956402881607346149758635080903381871535396975316312818909895436178983262157511843359313112654014211944895864478236692
  | 2 => 21265103261054844660947491209671663038317954743166899881712012981767876866743631876890426733988165991494315014447258340121178271098277212809188827932044509263052927905208551825972665893766683430437016585181307702376848524241268368045011267774967965975408668254536355081619930090052282183203645682364115456899380593778827567210331753811025926828997236078847515890257431348868296881716994210266746653168696986491651185910452214274528028190819708787503627877865764675633661128472522478856337656555542571158636792026431173881489860611490266738588297254884531058723526614805065835588422674263655705252109453623973928718200518269501934911160457150493714845184021448023655348542759643039824914236325448486786149840204982474752313565933162801368958762736068703559419901487609516529846262192141735982281740163581751800965446814646882878498687530423427280379113055922343175978772187075310902069515196501408532079529856778539957285477869464338151133916565319953625412607313815954420290471998442714180320666588246104466481422645235816609064434700379381722271486783380562406734322314538909601281
  | 3 => 21265084243945108417682886677109855144724163627653712796805082029758650252755505220115223756328417085918711290039194128099949813438654865832628767883009269083134982243435547036740486389778387576953022511791076826928601710081957879877924847882482082057650575443891489903343354611831178977574748693687706760056775219140162063470789096175374975563698954411886711343900196636900293029942614699636651267709495324939182000486270670279668139203921407165832122458589990725347244426164164518924605802488817951108125837533827931731394171796056855510707363942179356368547445051403281456954882075267165486751184017449442868925821572460418063661434267113132712054688351806431841134599425786174784722882064118703535560429321703899159387278781700086119243623778568509461594374634320303822289379358274794894964919455290974282071480799739182359135870049708506117824742952818533579431070318744618842158367845154294909296414141687157333146578779086148492406930508985820229565944883670913009894493348456574067187201840532750397917486493520090309786693930386296573244843930316185945565059105929245622312
  | 4 => 21265084243945108417682886677109855144724163627653712796805082029758650252755505220115223756328417085918711290039194128099949813438654865832628767883009269083134982243435547036740486389778387576953022511791076826928601710081957879877924847882482082057650575443891489903343354611831178977574748693687706760056775219140162063470789096175374975563698954411886711343900196636900293029942614699636651267709495324939182000486270670279668139203921407165832122458589990725347244426164164518924605802488817951108125837533827931731394171796056855510707363942711688049127026375453841570263197702476905009766533416178131426901618426816886474863273436293995288942703887878126729621142059041233289113014904007729404617020696744179484633501543776282769407920310786803818803043586233223631239420433001111122384173629832975594782395244484072057315494053662086969558867188748760033217120657662933245069610372737004038437129706150657186774971637737639714674170835403943324769315889040996457747560358082120671624976102831312215588025594554181403284283051107233280879734232324945413908255950287562473528
  | 5 => 21265131786719449025844377390122722853270213924565440430914292492127971878629789690234503854928279952955162613535759831513282004590149265689499553320077279218860539127936494490775377187835954633534539536501395855358926225058972059771413425600636760894033266526656154986005195911605567929572233893306245570398766170013212790847132123371007470671202578246321276160039068410150718913777113311859590150583603102835668964181214359010441887848181126718450750144203143552247685140883419224087875519523308237659650346976242478397076831579732373396061499366954624809735608674765531774766334439797747253330628874753513671016972586450482826373815329050119590601925831654017625543140190506974384842801366191243422112192564828843963592954390511675182734238307276335075211080736686926208944969115307761692774188869177889176010044796148010513562244814072041499990616131399410257264291983578864314488715666525569118035825421910565516188117602698475683386076946070424393780278689508019507791011020036966550954132707078421931245323247820717655831810008776092492949867517545921925483109424820564131912
  | 6 => 21265084243945108417682886677109855144724163627653712796805082029758650252755505220115223756328417085918711290039194128099949813438654865832628767883009269083134982243435547036740486389778387576953022511791076826928601710081957879877924847882482082057650575443891489903343354611831178977574748693687706760056775219140162063470789096175374975563698954411886711343900196636900293029942614699636651267709495324939182000486270670279668139203921407165832122458589990725347244426164164518924605802488817951108125837533827931731394171796056855510707363940715444246953596410264241145357014100440381798458973170945549334492380222980129932856376919813609617733194298794858607658699857142831822499578994509898724843143123004532970357712445958430460154684860789264705850449731158683247208529178374986592482216463860327986055364068278032251972815864169072356396532851847758924027680124388910225968124954063083995533299023536068570360641015067037103542269764760386371067209584984221105300157824672884351364522255552281161675366710787145113519138011883424950261227178740744828854849672875593564160
  | 7 => 21265084243945108417682886677109855144724163627653712796805082029758650252755505220115223756328417085918711290039194128099949813438654865832628767883009269083134982243435547036740486389778387576953022511791076826928601710081957879877924847882482082057650575443891489903343354611831178977574748693687706760056775219140162063470789096175374975563698954411886711343900196636900293029942614699636651267709495324939182000486270670279668139203921407165832122458589990725347244426164164518924605802488817951108125837533827931731394171796056855510707363940715444246953596410264241145357014100440381798458973170945549334492380222980129932856376919813609617733194298794858607658699857142831822499578994509898724843143123004532970357712445958430460154684860789264705850449731158683247208529178374986592482216463860327986055364068278032251972815864169072356396532851847758924027680124388910225968124954063083995533299023536068570360641015067037103542269764760386371067209584984221105300157824672884351364522255552281161675366710787145113519138011883424950261227178740744828854849672875593564160
  | 8 => 21265084243945108417682886677109855144724163627653712796805082029758650252755505220115223756328417085918711290039194128099949813438654865832628767883009269083134982243435547036740486389778387576953022511791076826928601710081957879877924847882482082057650575443891489903343354611831178977574748693687706760056775219140162063470789096175374975563698954411886711343900196636900293029942614699636651267709495324939182000486270670279668139203921407165832122458589990725347244426164164518924605802488817951108125837533827931731394171796056855510707363944707931851300456340643441995169381304513428221074093661410713519310856630653643016870169752075554492061934388211005979737244118552153751025815910117738745026099626055636509599516891756435598681733724830225057232696525581274224806839098603618665928117891722395489364795210168925071081539952299613691239760065360822163533457667491681171744437730866319138017567241076436987555943106645651812393795471023605494681741442935286560040366637399346774420964925864624481195155750862807568274450640187442635690847269588090793573062039640796692612
  | _ => 0

def rword (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) : ℕ :=
  tgetN (ruleT s.val) 29 (Nat.add (tgetN 17199722454303175642252672 7 t.val) (tgetN 15964224571115421144928839939672489631550259749949850312931456762042178461833071736086020535037060546088497629734598867147935763748541676391996774974439048148975560169247848951501974653382516724865461984141945838187902599486138216695426992195442916538923506238111694801605368917722172907527490055434002062816306665813151169210417861663373244651186801399754685910948196803683078840773825189675012167858002393656057335253436554673560179901376146858543632956134149937338020178184186750182882157996277531935241554540995267258950444363512506951296749774276872147067982549788162608588608145995914259578071993776074449444040809150738194419463225211466890877542967821313843751382775402965140996103613478328997072957102104714709136023527894458504259316339736359438077383059274997849715721406746476076035618142302273014465737169204005781406697492896513916975676633978240465340688643219424795467479532437281190263978147864018756070789534037511095517607701762991871248621505061273569218789699124091412066579019977602276625930985791899911724890516128109538633151710182540244947464850231167838528872430393116970486595584 4
    (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul t.val 81) c0) (Nat.mul 3 c1)) (Nat.mul 9 c2)) (Nat.mul 27 c3))))

/-- The field of B bits from bit o of the word w. -/
def fld (w o B : ℕ) : ℕ := Nat.mod (Nat.shiftRight w o) (Nat.pow 2 B)

def rk (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 0 2

def re (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) : ℕ := fld (rword s t c0 c1 c2 c3) 2 6

def rsl (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) (i : ℕ) : Fin 4 :=
  ⟨fld (rword s t c0 c1 c2 c3) (Nat.add 8 (Nat.mul 2 i)) 2 % 4, Nat.mod_lt _ (by norm_num)⟩

def rm (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) (i : ℕ) : ℤ := Int.subNatNat (fld (rword s t c0 c1 c2 c3) (Nat.add 14 (Nat.mul 4 i)) 4) 8

def rl0 (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) : ℤ := Int.ofNat (fld (rword s t c0 c1 c2 c3) 26 3)

/-- The class of slot k in the pattern (c0, c1, c2, c3). -/
def cv (c0 c1 c2 c3 : ℕ) (k : Fin 4) : ℕ := if k.val = 0 then c0 else if k.val = 1 then c1 else if k.val = 2 then c2 else c3

/-- The slack of the slot k below t in x and y, and its constant: pot t - pot (nb t k) at (x, y, s)
is dA t k * x + dB t k * y + dC s t k. -/
def dA (t : Fin 12) (k : Fin 4) : ℤ := Ac t - Ac (nb t k)

def dB (t : Fin 12) (k : Fin 4) : ℤ := Bc t - Bc (nb t k)

def dC (s : Fin 9) (t : Fin 12) (k : Fin 4) : ℤ := Cc s t - Cc s (nb t k)

/-- Kind 0: the edge at position re descends from class s for this pattern. -/
def ok0 (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) : Bool :=
  Nat.blt (re s t c0 c1 c2 c3) 36 && Nat.beq (srcv (re s t c0 c1 c2 c3)) s.val && Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) t) 1) 8 &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 0)) 1) (Nat.add c0 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 1)) 1) (Nat.add c1 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 2)) 1) (Nat.add c2 8) &&
    Nat.ble (Nat.add (dlvN (re s t c0 c1 c2 c3) (nb t 3)) 1) (Nat.add c3 8)

/-- Kind 1: the Farkas certificate over the slot facts and the bound is valid. -/
def ok1 (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) : Bool :=
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
def ok2 (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) : Bool :=
  decide (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) ≤ 1 ∧ rl0 s t c0 c1 c2 c3 ∣ dA t (rsl s t c0 c1 c2 c3 0) ∧ rl0 s t c0 c1 c2 c3 ∣ dB t (rsl s t c0 c1 c2 c3 0) ∧
    ¬ rl0 s t c0 c1 c2 c3 ∣ (cv c0 c1 c2 c3 (rsl s t c0 c1 c2 c3 0) : ℤ) - dC s t (rsl s t c0 c1 c2 c3 0))

def ruleOK (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) : Bool :=
  if rk s t c0 c1 c2 c3 = 0 then ok0 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 1 then ok1 s t c0 c1 c2 c3 else if rk s t c0 c1 c2 c3 = 2 then ok2 s t c0 c1 c2 c3 else false

/-- Every pattern of slack classes that can occur at the maximal potential t has a valid rule. -/
def rulesOK (t : Fin 12) : Bool :=
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

def farsOK10_dec : PLift (farsOK 10 = true) := ⟨by
  decide +kernel⟩

def farsOK11_dec : PLift (farsOK 11 = true) := ⟨by
  decide +kernel⟩

theorem farsOK_all (k : Fin 12) : farsOK k = true := by
  fin_cases k
  exacts [farsOK0_dec.down, farsOK1_dec.down, farsOK2_dec.down, farsOK3_dec.down, farsOK4_dec.down, farsOK5_dec.down, farsOK6_dec.down, farsOK7_dec.down, farsOK8_dec.down, farsOK9_dec.down, farsOK10_dec.down, farsOK11_dec.down]

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

def rulesOK10_dec : PLift (rulesOK 10 = true) := ⟨by
  decide +kernel⟩

def rulesOK11_dec : PLift (rulesOK 11 = true) := ⟨by
  decide +kernel⟩

theorem rulesOK_all (k : Fin 12) : rulesOK k = true := by
  fin_cases k
  exacts [rulesOK0_dec.down, rulesOK1_dec.down, rulesOK2_dec.down, rulesOK3_dec.down, rulesOK4_dec.down, rulesOK5_dec.down, rulesOK6_dec.down, rulesOK7_dec.down, rulesOK8_dec.down, rulesOK9_dec.down, rulesOK10_dec.down, rulesOK11_dec.down]

theorem far_ok (s : Fin 9) (t j : Fin 12) (hrep : repB s t = true) (hjt : j ≠ t) (hjn : ∀ k, j ≠ nb t k) :
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

theorem side_ok (s : Fin 9) (t : Fin 12) (kl kr : Fin 4) (i : ℕ) (hrep : repB s t = true) (hsp : facetB t = true)
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

theorem rule_ok (s : Fin 9) (t : Fin 12) (c0 c1 c2 c3 : ℕ) (hrep : repB s t = true) (h0 : c0 < 3) (h1 : c1 < 3) (h2 : c2 < 3) (h3 : c3 < 3)
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

theorem E_step : ∀ e ∈ E, ∀ j : Fin 12, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
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
theorem farkas_slot (x y : ℤ) (s : Fin 9) (t : Fin 12) (k1 k2 k3 : Fin 4) (c1 c2 c3 m1 m2 m3 l0 : ℤ)
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
theorem far_step (s : Fin 9) (t : Fin 12) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) t)
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

theorem far_step' (v : V) (t : Fin 12) (h : F v = pot v t) (hF : R0c v.2.2 < F v) (hrep : repB v.2.2 t = true) :
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

theorem sig_pot (v : V) (t : Fin 12) : pot (sig v) (rhoP t) = pot v t := by
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
theorem farkas_ub (x y : ℤ) (s : Fin 9) (a1 a2 a3 : Fin 12) (t l1 l2 l3 px py q lq : ℤ)
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
def BXn (s : Fin 9) : ℕ := tgetN 57824980 3 s.val

def BYn (s : Fin 9) : ℕ := tgetN 40744147 3 s.val

theorem nb_c0 : ∀ s : Fin 9, 0 < 2 * (Cc s 0 - (R0c s)) + 2 * (Cc s 11 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 12 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c0 : ∀ s : Fin 9, 0 < 2 * (Cc s 1 - (4)) + 3 * (Cc s 11 - (4)) + 0 * (Cc s 0 - (4)) + 13 * (2) := by
  decide +kernel

theorem nb_c1 : ∀ s : Fin 9, 0 < 2 * (Cc s 5 - (R0c s)) + 2 * (Cc s 6 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 12 * ((BXn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c1 : ∀ s : Fin 9, 0 < 3 * (Cc s 5 - (4)) + 2 * (Cc s 7 - (4)) + 0 * (Cc s 0 - (4)) + 13 * (2) := by
  decide +kernel

theorem nb_c2 : ∀ s : Fin 9, 0 < 3 * (Cc s 2 - (R0c s)) + 1 * (Cc s 5 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 14 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c2 : ∀ s : Fin 9, 0 < 3 * (Cc s 2 - (4)) + 1 * (Cc s 6 - (4)) + 0 * (Cc s 0 - (4)) + 10 * (2) := by
  decide +kernel

theorem nb_c3 : ∀ s : Fin 9, 0 < 2 * (Cc s 8 - (R0c s)) + 1 * (Cc s 10 - (R0c s)) + 0 * (Cc s 0 - (R0c s)) + 11 * ((BYn s : ℤ) + 1) := by
  decide +kernel

theorem sb_c3 : ∀ s : Fin 9, 0 < 3 * (Cc s 8 - (4)) + 1 * (Cc s 11 - (4)) + 0 * (Cc s 0 - (4)) + 14 * (2) := by
  decide +kernel

theorem nn_c : ∀ s : Fin 9, 0 < 3 * (Cc s 5 - (-1)) + 3 * (Cc s 11 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * (0) := by
  decide +kernel

/-- Every vertex of class s with F at most R0c s lies in the near box of class s. -/
theorem near_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ R0c s) :
    -(BXn s : ℤ) ≤ x ∧ x ≤ BXn s ∧ -(BYn s : ℤ) ≤ y ∧ y ≤ BYn s := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 11 0 (R0c s) 2 2 0 (1) (0) ((BXn s : ℤ) + 1) 12 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 6 0 (R0c s) 2 2 0 (-1) (0) ((BXn s : ℤ) + 1) 12 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 5 0 (R0c s) 3 1 0 (0) (1) ((BYn s : ℤ) + 1) 14 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 8 10 0 (R0c s) 2 1 0 (0) (-1) ((BYn s : ℤ) + 1) 11 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nb_c3 s⟩ (u _) (u _) (u _) (by omega)

/-- Every vertex with F at most 4 lies in the cells |x| ≤ 1, |y| ≤ 1. -/
theorem small_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ 4) :
    -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 1 11 0 (4) 2 3 0 (1) (0) (2) 13 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 7 0 (4) 3 2 0 (-1) (0) (2) 13 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 6 0 (4) 3 1 0 (0) (1) (2) 10 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 8 11 0 (4) 3 1 0 (0) (-1) (2) 14 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, sb_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 5 11 0 (-1) 3 3 0 (0) (0) (0) 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, nn_c s⟩ (u _) (u _) (u _) (by norm_num)

/-- The vertices near v0 where the graph distance is not the largest potential, with the distance. -/
def O : List (V × ℤ) :=
  [((0, 0, 3), 0),
    ((0, 0, 2), 1),
    ((0, 0, 4), 1),
    ((0, 0, 7), 1),
    (((-1), 0, 5), 2),
    (((-1), 0, 6), 2)]

/-- The cells (x, y) of the vertices of O. -/
def obox (x y : ℤ) : Bool := decide ((-1) ≤ x ∧ x ≤ 0 ∧ 0 ≤ y ∧ y ≤ 0)

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

/-- The vertex o of O has F and fv below 4 and fv nonnegative, and fv changes by at most one
along the edges at o. -/
def OokB (o : V × ℤ) : Bool :=
  decide (F o.1 < 4 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 4) && E.all fun e =>
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

theorem Ook_all (k : Fin 6) : Ook k = true := by
  fin_cases k
  exacts [Ook0_dec.down, Ook1_dec.down, Ook2_dec.down, Ook3_dec.down, Ook4_dec.down, Ook5_dec.down]

theorem O_len : O.length = 6 := by
  decide +kernel

/-- The vertices of O have F and fv below 4 and fv nonnegative, and fv changes by at most one
along the edges at the vertices of O. -/
theorem O_ok : ∀ o ∈ O, F o.1 < 4 ∧ 0 ≤ fv o.1 ∧ fv o.1 < 4 ∧ ∀ e ∈ E,
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

def R0c_ge_dec : PLift (∀ s, 4 ≤ R0c s) := ⟨by
  decide +kernel⟩

theorem R0c_ge : ∀ s, 4 ≤ R0c s := R0c_ge_dec.down

/-- The near check computes the potentials as differences of natural numbers: at the cell (a, b) of
the near box of class s, pot = potP - potQ. -/
def apN (i : Fin 12) : ℕ := tgetN 21864960 3 i.val

def amN (i : Fin 12) : ℕ := tgetN 28051505235 3 i.val

def bpN (i : Fin 12) : ℕ := tgetN 21011890176 3 i.val

def bmN (i : Fin 12) : ℕ := tgetN 80154 3 i.val

def kpN (s : Fin 9) (i : Fin 12) : ℕ := tgetN 449891379458140895954639733685097473498685443314033663738264859770559835986046101346736831658997082390166178811659426289747621164142176059441673256638715577814676 5 (Nat.add (Nat.mul s.val 12) i.val)

def kmN (s : Fin 9) (i : Fin 12) : ℕ := tgetN 588160729456789727820676300016421674764830716037389729237104128235358605132863485651757820216670696428590829419926702513542696133025482590374696999663930703872 5 (Nat.add (Nat.mul s.val 12) i.val)

def pqOK : Bool :=
  (List.finRange 12).all fun i => decide ((apN i : ℤ) - amN i = Ac i ∧ (bpN i : ℤ) - bmN i = Bc i) &&
    (List.finRange 9).all fun s => decide ((kpN s i : ℤ) - kmN s i = Cc s i - Ac i * BXn s - Bc i * BYn s)

def pq_ok_dec : PLift (pqOK = true) := ⟨by
  decide +kernel⟩

theorem pq_ok : pqOK = true := pq_ok_dec.down

def potP (s : Fin 9) (a b : ℕ) (i : Fin 12) : ℕ :=
  Nat.add (Nat.add (Nat.mul (apN i) a) (Nat.mul (bpN i) b)) (kpN s i)

def potQ (s : Fin 9) (a b : ℕ) (i : Fin 12) : ℕ :=
  Nat.add (Nat.add (Nat.mul (amN i) a) (Nat.mul (bmN i) b)) (kmN s i)

theorem potPQ_val (s : Fin 9) (a b : ℕ) (i : Fin 12) :
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
  pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax ((potP s a b 0, potQ s a b 0)) (potP s a b 1, potQ s a b 1)) (potP s a b 2, potQ s a b 2)) (potP s a b 3, potQ s a b 3)) (potP s a b 4, potQ s a b 4)) (potP s a b 5, potQ s a b 5)) (potP s a b 6, potQ s a b 6)) (potP s a b 7, potQ s a b 7)) (potP s a b 8, potQ s a b 8)) (potP s a b 9, potQ s a b 9)) (potP s a b 10, potQ s a b 10)) (potP s a b 11, potQ s a b 11)

def FPn (s : Fin 9) (a b p : ℕ) : ℕ × ℕ :=
  pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax (pmax ((Nat.add (potP s a b 0) (dlvN p 0), Nat.add (potQ s a b 0) 8)) (Nat.add (potP s a b 1) (dlvN p 1), Nat.add (potQ s a b 1) 8)) (Nat.add (potP s a b 2) (dlvN p 2), Nat.add (potQ s a b 2) 8)) (Nat.add (potP s a b 3) (dlvN p 3), Nat.add (potQ s a b 3) 8)) (Nat.add (potP s a b 4) (dlvN p 4), Nat.add (potQ s a b 4) 8)) (Nat.add (potP s a b 5) (dlvN p 5), Nat.add (potQ s a b 5) 8)) (Nat.add (potP s a b 6) (dlvN p 6), Nat.add (potQ s a b 6) 8)) (Nat.add (potP s a b 7) (dlvN p 7), Nat.add (potQ s a b 7) 8)) (Nat.add (potP s a b 8) (dlvN p 8), Nat.add (potQ s a b 8) 8)) (Nat.add (potP s a b 9) (dlvN p 9), Nat.add (potQ s a b 9) 8)) (Nat.add (potP s a b 10) (dlvN p 10), Nat.add (potQ s a b 10) 8)) (Nat.add (potP s a b 11) (dlvN p 11), Nat.add (potQ s a b 11) 8)

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
  | 0 => 2421934538520242253734569976385432300746385527145682414698863135607262658483193879316398006063556300640354304
  | 1 => 1061681048089895539693381159185828451209216
  | 2 => 13457819779714146980442578333843980059575943570043239851228596839721045370756694016
  | 3 => 69048123270153202746132738209015510100539153005602941227008
  | 4 => 12066658508981831727506679675057980688224264241438597780549840615527947121560767883233893784547096355047205001857661949206908041691136
  | 5 => 10306945744359328395518660090531440196475578566621269074175753660090171333535245430201588431003648
  | 6 => 0
  | 7 => 0
  | 8 => 194590165579431409029157181085705332132739989447646078175232
  | _ => 0

def nearE (s : Fin 9) (a b : ℕ) : ℕ := tgetN (nearT s.val) 6 (a * (2 * BYn s + 1) + b)

/-- The near check of class s. -/
def nearOK (s : Fin 9) : Bool :=
  !repC s || (List.range (2 * BXn s + 1)).all fun a => (List.range (2 * BYn s + 1)).all fun b =>
    Nat.blt (Nat.add (R0N s) (FP s a b).2) (FP s a b).1 ||
      (Nat.beq a (BXn s) && Nat.beq b (BYn s) && Nat.beq s.val 3) ||
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
    have hs0 : s = 3 := Fin.ext h4
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

theorem symOk_all (k : Fin 6) : symOk k = true := by
  fin_cases k
  exacts [symOk0_dec.down, symOk1_dec.down, symOk2_dec.down, symOk3_dec.down, symOk4_dec.down, symOk5_dec.down]

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

/-- The cells |x| ≤ 1, |y| ≤ 1 of class s. -/
def boxS (s : Fin 9) : Finset V :=
  (Finset.range 3 ×ˢ Finset.range 3).map
    ⟨fun p => ((p.1 : ℤ) - 1, (p.2 : ℤ) - 1, s), fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)⟩

theorem boxS_cls (s : Fin 9) (v : V) (h : v ∈ boxS s) : v.2.2 = s := by
  rw [boxS, Finset.mem_map] at h
  obtain ⟨p, -, rfl⟩ := h
  rfl

theorem mem_boxS (v : V) (h : (fv v).toNat ≤ 4) : v ∈ boxS v.2.2 := by
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
  rw [boxS, Finset.mem_map]
  refine ⟨((x + 1).toNat, (y + 1).toNat), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range]
    omega
  · show ((((x + 1).toNat : ℕ) : ℤ) - 1, (((y + 1).toNat : ℕ) : ℤ) - 1, s) = (x, y, s)
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨by omega, by omega, rfl⟩

/-- Up to n = 4, a n counts the cells of the boxes where fv = n. -/
theorem a_small (n : ℕ) (hn : n ≤ 4) : a n = ∑ s : Fin 9, ((boxS s).filter fun v => (fv v).toNat = n).card := by
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

/-- The number of vertices of class s at distance n, for n < 4. -/
def smallT (s : Fin 9) (n : ℕ) : ℕ := tgetN 5724390088771013160225278003200 3 (Nat.add (Nat.mul s.val 4) n)

/-- The kernel's count of the cells of the box of class s by fv. -/
def smallOK (s : Fin 9) : Bool :=
  (List.range 4).all fun n => decide (((boxS s).filter fun v => (fv v).toNat = n).card = smallT s n)

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

/-- The coordination sequence below n = 4. -/
theorem small_vals : (List.range 4).map a = [1, 4, 8, 10] := by
  have hc : ∀ n ∈ List.range 4, a n = ∑ s : Fin 9, smallT s n := by
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
from below, and for n ≥ 9 the other facets lie below by Farkas certificates (`certG_ok`,
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
def AW (i : ℕ) : ℕ := tgetN 95080572163941 4 i

def BW (i : ℕ) : ℕ := tgetN 188895788876886 4 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem A_W (i : Fin 12) : Ac i = (AW i.val : ℤ) - 8 := by rw [Ac, tget, Int.subNatNat_eq_coe]; rfl

theorem B_W (i : Fin 12) : Bc i = (BW i.val : ℤ) - 8 := by rw [Bc, tget, Int.subNatNat_eq_coe]; rfl

theorem C_W (s : Fin 9) (i : Fin 12) : Cc s i = (CW s.val i.val : ℤ) - 8 := by rw [Cc, tget, Int.subNatNat_eq_coe]; rfl

def gcV (k : ℕ) : ℕ := ctabN 4095 1 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 12) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 1421564040 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 3

def Ap (i : Fin 12) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 113835795087378 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 4

def Bp (i : Fin 12) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 10625160 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 12) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 37889512587 3 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 2

def be (i : Fin 12) : ℤ := beN i.val

def primK : PLift (∀ i : Fin 12, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧ al i * Ap i + be i * Bp i = 1) :=
  ⟨by decide +kernel⟩

theorem prim : ∀ i : Fin 12, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧ al i * Ap i + be i * Bp i = 1 := primK.down

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 12) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 12) : ℤ := Ac j * al i + Bc j * be i

def orientK : PLift (∀ i : Fin 12, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0) :=
  ⟨by decide +kernel⟩

theorem orient : ∀ i : Fin 12, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := orientK.down

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 9) (i : Fin 12) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 9) (i j : Fin 12) (c u : ℤ) :
    pot (par s i c u) j = ka i j * c + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 12) :
    v = par v.2.2 i (Ap i * v.1 + Bp i * v.2.1) (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := (prim i).2.2.2
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb
  · linear_combination (-y) * hb

theorem pot_lev (v : V) (i : Fin 12) : pot v i = gc i * (Ap i * v.1 + Bp i * v.2.1) + Cc v.2.2 i := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  simp only [pot]
  rw [h1, h2]
  ring

theorem par_inj (s : Fin 9) (i : Fin 12) (c : ℤ) : Function.Injective (par s i c) := by
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
theorem F_attained (v : V) : ∃ k : Fin 12, pot v k = F v := by
  by_contra hne
  have h : ∀ k, pot v k ≤ F v - 1 := fun k => by
    have h1 := le_F v k
    have h2 : pot v k ≠ F v := fun e => hne ⟨k, e⟩
    omega
  have := F_le v (F v - 1) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11)
  omega

/-- The first facet attaining the maximum. -/
noncomputable def fi (v : V) : Fin 12 := Fin.find (fun k => pot v k = F v) (F_attained v)

theorem fi_spec (v : V) : pot v (fi v) = F v ∧ ∀ j, j < fi v → pot v j < F v :=
  ⟨Fin.find_spec (F_attained v), fun j hj =>
    lt_of_le_of_ne (le_F v j) (Fin.find_min (F_attained v) hj)⟩

theorem fi_iff (v : V) (i : Fin 12) : fi v = i ↔ pot v i = F v ∧ ∀ j, j < i → pot v j < F v := by
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
theorem piece_iff (v : V) (i : Fin 12) (n : ℤ) :
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
def prevF (i : ℕ) : ℕ := Nat.mod (Nat.add i 11) 12

def nextF (i : ℕ) : ℕ := Nat.mod (Nat.add i 1) 12

def ehV (k : ℕ) : ℕ := ctabN 4094 1 k

def ekV (k : ℕ) : ℕ := ctabN 2048 1 k

def fin_prevK : PLift (∀ i : Fin 12, (i - 1).val = prevF i.val ∧ (if i - 1 < i then (1 : ℤ) else 0) = (ehV i.val : ℤ)) :=
  ⟨by decide +kernel⟩

theorem fin_prev : ∀ i : Fin 12, (i - 1).val = prevF i.val ∧ (if i - 1 < i then (1 : ℤ) else 0) = (ehV i.val : ℤ) := fin_prevK.down

def fin_nextK : PLift (∀ i : Fin 12, (i + 1).val = nextF i.val ∧ (if i + 1 < i then (1 : ℤ) else 0) = (ekV i.val : ℤ)) :=
  ⟨by decide +kernel⟩

theorem fin_next : ∀ i : Fin 12, (i + 1).val = nextF i.val ∧ (if i + 1 < i then (1 : ℤ) else 0) = (ekV i.val : ℤ) := fin_nextK.down

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (9 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 152315369871305631014814271202912247765063966424013418534347999208776610253401288972896838450907901701050188567251446973710420206787943424018433612762209139469679294746624 4 k

def cf2V (k : ℕ) : ℕ := ctabN 4054367616745490340016585821218382506352928380916387472756701460903773842786457259007853120120872652783922697965973968388251806658226079007057482580924081457136530719232 4 k

def cf3V (k : ℕ) : ℕ := ctabN 68197724380847315425638977378886389849462597344856059180494630824538946783629477101320717553554578829217932773218043445511487569235220457641133393363250639935528704745728 4 k

def cf0V (k : ℕ) : ℕ := ctabN 1842755090275382039973847241761788103428512025066078264707441576703377021569321631022187399245461667679425056624914350984134645460145083158286498789174509487184150528 4 k

def cf1 (i j : Fin 12) : ℤ := (cf1V (j.val + 12 * i.val) : ℤ)

def cf2 (i j : Fin 12) : ℤ := (cf2V (j.val + 12 * i.val) : ℤ)

def cf3 (i j : Fin 12) : ℤ := (cf3V (j.val + 12 * i.val) : ℤ)

def cf0 (i j : Fin 12) : ℤ := (cf0V (j.val + 12 * i.val) : ℤ)

/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 12) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 9) (i j : Fin 12) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (9 - Cc s i)

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := Nat.beq j i || Nat.beq j (nextF i) || Nat.beq j (prevF i)

/-- certG in natural numbers: Ac = AW - 8, Bc = BW - 8, the negative terms moved across. -/
def certGN (i j : ℕ) : Bool :=
  Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 12 i))) (AW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 12 i))) (AW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 12 i))) (AW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 12 i))) 8))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 12 i))) (cf2V (Nat.add j (Nat.mul 12 i)))) (cf0V (Nat.add j (Nat.mul 12 i)))) (AW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 12 i))) (AW j))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 12 i))) (BW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 12 i))) (BW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 12 i))) (BW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 12 i))) 8))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 12 i))) (cf2V (Nat.add j (Nat.mul 12 i)))) (cf0V (Nat.add j (Nat.mul 12 i)))) (BW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 12 i))) (BW j)))

/-- certC in natural numbers: Cc = CW - 8, the negative terms moved across. -/
def certCN (s i j : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 12 i))) (cf2V (Nat.add j (Nat.mul 12 i)))) (cf0V (Nat.add j (Nat.mul 12 i)))) (CW s i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 12 i))) (CW s j)))
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 12 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 12 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 12 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 12 i))) 17))

def certGK : PLift ((allR 12 fun i => allR 12 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 12 fun i => allR 12 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 9 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 9) : certS s = true := by
  exact allI_get _ _ _ certCK0.down s (by omega) (by omega)

theorem beq_ff (x y : ℕ) (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem near_false (i j : Fin 12) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
theorem certG_ok (i j : Fin 12) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) : certG i j := by
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
theorem certC_ok (s : Fin 9) (i j : Fin 12) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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

theorem farkas4 (v : V) (h i k j : Fin 12) (e1 e2 r l1 l2 l3 l0 : ℤ)
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
def lev (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 9) (i : Fin 12) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 9) (i j : Fin 12) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 9) (i j : Fin 12) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 9) (i : Fin 12) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 9) (i : Fin 12) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 12) : ka i i = gc i := by
  obtain ⟨h1, h2, -, hb⟩ := prim i
  rw [ka, h1, h2]
  linear_combination (gc i) * hb

theorem Dm_self (i : Fin 12) : Dm i i = 0 := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  rw [Dm, h1, h2]
  ring

theorem pot_par_self (s : Fin 9) (i : Fin 12) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 9 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 9) (i : Fin 12) (n u : ℤ) (hn : 9 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 9 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-3, 3]: a natural-number check. -/
def cbK : PLift ((allR 9 fun s => allR 12 fun i => Nat.ble (CW s i) 11 && Nat.ble 8 (Nat.add (CW s i) 3)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 9) (j : Fin 12) : -3 ≤ Cc s j ∧ Cc s j ≤ 3 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 3)) (1 * n + 3) ×ˢ
    (Finset.Icc (-(1 * n + 3)) (1 * n + 3) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (1 * Ac 5 + 1 * Ac 6 = 6 ∧ 1 * Bc 5 + 1 * Bc 6 = 0 ∧
    1 * Ac 0 + 1 * Ac 11 = (-6) ∧ 1 * Bc 0 + 1 * Bc 11 = 0 ∧
    1 * Ac 8 + 1 * Ac 9 = 0 ∧ 1 * Bc 8 + 1 * Bc 9 = 8 ∧
    1 * Ac 2 + 1 * Ac 3 = 0 ∧ 1 * Bc 2 + 1 * Bc 3 = (-8)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 1 * Ac 5 + 1 * Ac 6 = 6 ∧ 1 * Bc 5 + 1 * Bc 6 = 0 ∧
    1 * Ac 0 + 1 * Ac 11 = (-6) ∧ 1 * Bc 0 + 1 * Bc 11 = 0 ∧
    1 * Ac 8 + 1 * Ac 9 = 0 ∧ 1 * Bc 8 + 1 * Bc 9 = 8 ∧
    1 * Ac 2 + 1 * Ac 3 = 0 ∧ 1 * Bc 2 + 1 * Bc 3 = (-8) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 9) :
    6 * x ≤ 2 * F (x, y, s) + 6 ∧
    6 * (-x) ≤ 2 * F (x, y, s) + 6 ∧
    8 * y ≤ 2 * F (x, y, s) + 6 ∧
    8 * (-y) ≤ 2 * F (x, y, s) + 6 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 5 + 1 * pot (x, y, s) 6 =
      6 * x + 1 * Cc s 5 + 1 * Cc s 6 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 5
  have r0 := le_F (x, y, s) 6
  have k0 := Cbound s 5
  have l0 := Cbound s 6
  have e1 : 1 * pot (x, y, s) 0 + 1 * pot (x, y, s) 11 =
      6 * (-x) + 1 * Cc s 0 + 1 * Cc s 11 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 11
  have k1 := Cbound s 0
  have l1 := Cbound s 11
  have e2 : 1 * pot (x, y, s) 8 + 1 * pot (x, y, s) 9 =
      8 * y + 1 * Cc s 8 + 1 * Cc s 9 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 8
  have r2 := le_F (x, y, s) 9
  have k2 := Cbound s 8
  have l2 := Cbound s 9
  have e3 : 1 * pot (x, y, s) 2 + 1 * pot (x, y, s) 3 =
      8 * (-y) + 1 * Cc s 2 + 1 * Cc s 3 := by
    simp only [pot]; linear_combination x * p7 + y * p8
  have q3 := le_F (x, y, s) 2
  have r3 := le_F (x, y, s) 3
  have k3 := Cbound s 2
  have l3 := Cbound s 3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_Bx (v : V) (n : ℤ) (h : F v ≤ n) : v ∈ Bx n := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  have h0 := F_nonneg (x, y, s)
  simp only [Bx, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  omega

/-- The piece of the sphere F = n with class s and first maximal facet i. -/
noncomputable def PF (s : Fin 9) (i : Fin 12) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 9) (i : Fin 12) (n : ℤ) (hn : 9 ≤ n) :
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
def inner (s : Fin 9) (i : Fin 12) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 9) (i : Fin 12) (n : ℤ) (hn : 9 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 9 × Fin 12, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 12, inner p.1 p.2 n

/-! Shifting n by 60 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 4497491888447281155900 6 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 12) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 14760812761223892752 6 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 36

def mh (i : Fin 12) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 9728188445635397043208240 7 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 24

def mk (i : Fin 12) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 12, (60 : ℤ) = gc i * Lq i ∧ 60 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 60 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 12, (60 : ℤ) = gc i * Lq i ∧ 60 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 60 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 9) (i : Fin 12) (n : ℤ) :
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
  ∑ q : Fin 9 × Fin 12, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

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
the window start, n = 9 + r with r < 60: the level is QQ - 0 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 557192 2 k

def uhMV (k : ℕ) : ℕ := ctabN 27935219780 3 k

def ukPV (k : ℕ) : ℕ := ctabN 142945143620098 4 k

def ukMV (k : ℕ) : ℕ := ctabN 294984 2 k

def dhV (k : ℕ) : ℕ := ctabN 94031268119900 4 k

def dkV (k : ℕ) : ℕ := ctabN 216983186790485 4 k

def mhkV (k : ℕ) : ℕ := ctabN 34813904580 3 k

def uh (i : Fin 12) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 12) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 12) : ℤ := dhV i.val

def dk (i : Fin 12) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 12, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 12, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 0 1 (Nat.add i (Nat.mul 12 s))

def QQ (s i : ℕ) : ℕ := ctabN 7347563407570483891031444627301609674819281848827158290915481094027512160113657448524260743325208928250967891953977527439984199271 4 (Nat.add i (Nat.mul 12 s))

def AH (s i : ℕ) : ℕ := ctabN 342815884559244303109130443122063139040680063077456927344521059592640621390563759801393416088510201866455596530367568574198080106594226857793042059269513147747722 5 (Nat.add i (Nat.mul 12 s))

def AK (s i : ℕ) : ℕ := ctabN 234374025879633892340273968200091047416189398069997898736037806069233067803520081103750616257557092516566243961166025026534213310287434144517625289444857917552865290999343329077142851650588438669620343436393690586197129984967053 7 (Nat.add i (Nat.mul 12 s))

def WH (s i : ℕ) : ℕ := ctabN 792725101973563428619192273856454929828829328302624294936689847485560789811200397517137835440114810010219525860741408645109894194623433926392522168564887942405911962949943475554497792171525070871 6 (Nat.add i (Nat.mul 12 s))

def WK (s i : ℕ) : ℕ := ctabN 1540610763817029656216727035859497307486309174984333017194470414632980439533883342238070416143370304587775437003618186212467354258128968507822958622507044111200 5 (Nat.add i (Nat.mul 12 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 9 fun s => allR 12 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq 17 (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 9) (i : Fin 12) :
    PP s.val i.val < gcV i.val ∧
    (9 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 0) + PP s.val i.val ∧
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

/-- Piece (s, i) at n = 9 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 9 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 9) (i : Fin 12) (r : ℕ) :
    ((9 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (9 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 0) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 9) (i : Fin 12) (r : ℕ) (hr : r < 60) :
    inner s i ((9 : ℤ) + r) = innerZ s.val i.val r := by
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
    have hl : lev s i ((9 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r := by
      rw [lev, show (9 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((9 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((9 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 921881199151856468449311188436251164617300 7 k

def tblV (k : ℕ) : ℕ := ctabN 1053402992176841427638451052270455173286672 7 k

def initV (k : ℕ) : ℕ := ctabN 43073 4 k

/-- The step of the closed form at residue t mod 20. -/
def dv (t : ℕ) : ℕ := dtabV (t % 20)

/-- The sequence in closed form: b(n + 20) = b(n) + dv (n - 4) for n ≥ 4. -/
def b (n : ℕ) : ℕ :=
  if n < 4 then initV n else dv (n - 4) * ((n - 4) / 20) + tblV ((n - 4) % 20)

theorem b_step (n : ℕ) (hn : 4 ≤ n) : b (n + 20) = b n + dv (n - 4) := by
  rw [b, b, if_neg (show ¬ (n + 20 < 4) by omega), if_neg (show ¬ (n < 4) by omega),
    show n + 20 - 4 = n - 4 + 20 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 20)]
  ring

theorem b_shift (n : ℕ) (hn : 4 ≤ n) : b (n + 60) = b n + 3 * dv (n - 4) := by
  rw [b, b, if_neg (show ¬ (n + 60 < 4) by omega), if_neg (show ¬ (n < 4) by omega),
    show n + 60 - 4 = n - 4 + 20 * 3 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 20)]
  ring

/-- b on the residue class of 4 + j mod 20. -/
theorem b_res (k j : ℕ) (hj : j < 20) : b (20 * k + (4 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (20 * k + (4 + j) < 4) by omega),
    show 20 * k + (4 + j) - 4 = j + 20 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 20), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 9 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 60 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 9 fun s => allR 12 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 9 fun s => sumR 12 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 9 r)) &&
    Nat.beq (sumR 9 fun s => sumR 12 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 3 (dv (Nat.add 5 r)))

/-! The window n = 9, ..., 68, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 13 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 26 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK3 : PLift (allI 39 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK4 : PLift (allI 52 8 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 60) :
    (∀ s, s < 9 → ∀ i, i < 12 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 9 fun s => sumR 12 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (9 + r) ∧
    (sumR 9 fun s => sumR 12 fun i => cond (divN s i r) (mhkV i) 0) = 3 * dv (5 + r) := by
  have h : periodR r = true := by
    rcases (show r < 13 ∨ (13 ≤ r ∧ r < 26) ∨ (26 ≤ r ∧ r < 39) ∨ (39 ≤ r ∧ r < 52) ∨ 52 ≤ r by omega) with h | h | h | h | h
    · exact allI_get _ _ _ periodK0.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK1.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK2.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK3.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK4.down r (by omega) (by omega)
  simp only [periodR, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun s hs i hi hd => ?_, h2, h3⟩
  have h4 := (allR_iff _ _).1 ((allR_iff _ _).1 h1 s hs) i hi
  rw [hd] at h4
  simpa using h4

theorem innerZ_eq (s i r : ℕ) (hs : s < 9) (hi : i < 12) (hr : r < 60) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 9 fun s => sumR 12 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 9 × Fin 12, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 12 fun i => f s i : ℕ) : ℤ)) 9]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 12]

theorem S_window (r : ℕ) (hr : r < 60) : S ((9 : ℤ) + r) = b (9 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 60) : Gs ((9 : ℤ) + r) = ((3 * dv (5 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 9 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 9) (i : Fin 12) (n : ℤ) (hn : 9 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 9 + t := ⟨(n - 9).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 60
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 60) (by omega) (by omega)
      have e : (9 : ℤ) + t = (9 + (t - 60 : ℕ)) + 60 := by
        push_cast [Nat.cast_sub (by omega : 60 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 9 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 60 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 9 ≤ n) : (3 : ℤ) * (dv (n - 4) : ℤ) = Gs n := by
  have hr : (n - 9) % 60 < 60 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((9 : ℤ) + (((n - 9) % 60 : ℕ) : ℤ)) + 60 * (((n - 9) / 60 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 4) = dv (5 + (n - 9) % 60) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 9 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 69
    · obtain ⟨r, rfl⟩ : ∃ r, n = 9 + r := ⟨n - 9, by omega⟩
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

/-! ## The small spheres

The points with F ≤ 8 lie in the box -3 ≤ x ≤ 3, -2 ≤ y ≤ 2 (`small_box`). In natural-number
coordinates a = x + 3, b = y + 2 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 9) (h : F (x, y, s) ≤ 8) :
    -3 ≤ x ∧ x ≤ 3 ∧ -2 ≤ y ∧ y ≤ 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 3, (b : ℤ) - 2, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 40) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 3) (Nat.mul (BW i) 2)) 8) (Nat.add (Nat.mul 8 a) (Nat.mul 8 b))

theorem pot_box (a b : ℕ) (s : Fin 9) (i : Fin 12) :
    pot ((a : ℤ) - 3, (b : ℤ) - 2, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 12 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 9) : F ((a : ℤ) - 3, (b : ℤ) - 2, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 3, (b : ℤ) - 2, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 3, (b : ℤ) - 2, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 12 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 12 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 3, (b : ℤ) - 2, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 3, (b : ℤ) - 2, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 3, (b : ℤ) - 2, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 7 fun a => sumR 5 fun b => sumR 9 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 4 .. 8, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 4 5 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 4 ≤ n) (h2 : n < 9) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 9) : V := ((q.1 : ℤ) - 3, (q.2.1 : ℤ) - 2, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 8) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 7 ×ˢ (Finset.range 5 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 9 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 3).toNat, (y + 2).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 3).toNat (y + 2).toNat s
        rw [show (((x + 3).toNat : ℕ) : ℤ) - 3 = x by omega,
          show (((y + 2).toNat : ℕ) : ℤ) - 2 = y by omega, h] at e
        exact_mod_cast e.symm
      · simp only [ib, Prod.mk.injEq]
        exact ⟨by omega, by omega, by trivial⟩
    · rintro ⟨a, b, s', ⟨-, hF⟩, he⟩
      rw [← he, ib, F_FN, hF]
  rw [cnt, hs, Set.ncard_coe_finset, Finset.card_image_of_injective _ ib_inj, Finset.card_filter,
    Finset.sum_product, cntB, sumR_eq]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_product, sumR_eq]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 9]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n from n = 4 on (`a_eq_cnt`, from `a_eq_F`), and `small_vals`
lists the terms below 4. The terms from 4 to 8 are counted in the box, those from 9 on
are S(n), and all agree with the closed form b (`a_eq_b`). The step from n to n + 20, the closed form
per residue (`a_closed`), the controls, the recurrence and the g.f. follow, their base cases checked by
the kernel on b. -/

theorem a_eq_cnt (n : ℕ) (hn : 4 ≤ n) : a n = cnt n := by
  rw [a_eq_F n hn, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 9 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt n (by omega)]
  exact cnt_eq_S n (by exact_mod_cast hn)

def smallR0K : PLift ((List.range 4).map b = [1, 4, 8, 10]) :=
  ⟨by decide +kernel⟩

theorem a_lt_R0 (n : ℕ) (hn : n < 4) : a n = b n := by
  have h : (List.range 4).map a = (List.range 4).map b := by
    rw [small_vals]
    exact smallR0K.down.symm
  exact List.map_inj_left.1 h n (List.mem_range.2 hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 4 ∨ (4 ≤ n ∧ n < 9) ∨ 9 ≤ n by omega) with h | ⟨h1, h2⟩ | h
  · exact a_lt_R0 n h
  · rw [a_eq_cnt n h1, cnt_small _ (by omega)]
    exact small_eq n h1 h2
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

def dconst_baseK : PLift (∀ r : ℕ, r < 20 → dtabV r = 84) :=
  ⟨by decide +kernel⟩

theorem dconst_base : ∀ r : ℕ, r < 20 → dtabV r = 84 := dconst_baseK.down

theorem dv_const : ∀ t : ℕ, dv t = 84 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 20) = a(n) + 84 for n ≥ 4. -/
theorem a_step (n : ℕ) (hn : 4 ≤ n) : a (n + 20) = a n + 84 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 84 ∧ tblV 0 = 16 ∧ dv 1 = 84 ∧ tblV 1 = 22 ∧ dv 2 = 84 ∧ tblV 2 = 24 ∧ dv 3 = 84 ∧ tblV 3 = 30 ∧ dv 4 = 84 ∧ tblV 4 = 34 ∧ dv 5 = 84 ∧ tblV 5 = 38 ∧ dv 6 = 84 ∧ tblV 6 = 42 ∧ dv 7 = 84 ∧ tblV 7 = 44) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 84 ∧ tblV 8 = 52 ∧ dv 9 = 84 ∧ tblV 9 = 56 ∧ dv 10 = 84 ∧ tblV 10 = 58 ∧ dv 11 = 84 ∧ tblV 11 = 62 ∧ dv 12 = 84 ∧ tblV 12 = 66 ∧ dv 13 = 84 ∧ tblV 13 = 74 ∧ dv 14 = 84 ∧ tblV 14 = 76 ∧ dv 15 = 84 ∧ tblV 15 = 78) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 84 ∧ tblV 16 = 84 ∧ dv 17 = 84 ∧ tblV 17 = 88 ∧ dv 18 = 84 ∧ tblV 18 = 94 ∧ dv 19 = 84 ∧ tblV 19 = 96) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (20 * k + 4) = 84 * k + 16 ∧
    a (20 * k + 5) = 84 * k + 22 ∧
    a (20 * k + 6) = 84 * k + 24 ∧
    a (20 * k + 7) = 84 * k + 30 ∧
    a (20 * k + 8) = 84 * k + 34 ∧
    a (20 * k + 9) = 84 * k + 38 ∧
    a (20 * k + 10) = 84 * k + 42 ∧
    a (20 * k + 11) = 84 * k + 44 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 20 * k + 4 = 20 * k + (4 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 20 * k + 5 = 20 * k + (4 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 20 * k + 6 = 20 * k + (4 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 20 * k + 7 = 20 * k + (4 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 20 * k + 8 = 20 * k + (4 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 20 * k + 9 = 20 * k + (4 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 20 * k + 10 = 20 * k + (4 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 20 * k + 11 = 20 * k + (4 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (20 * k + 12) = 84 * k + 52 ∧
    a (20 * k + 13) = 84 * k + 56 ∧
    a (20 * k + 14) = 84 * k + 58 ∧
    a (20 * k + 15) = 84 * k + 62 ∧
    a (20 * k + 16) = 84 * k + 66 ∧
    a (20 * k + 17) = 84 * k + 74 ∧
    a (20 * k + 18) = 84 * k + 76 ∧
    a (20 * k + 19) = 84 * k + 78 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 20 * k + 12 = 20 * k + (4 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 20 * k + 13 = 20 * k + (4 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 20 * k + 14 = 20 * k + (4 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 20 * k + 15 = 20 * k + (4 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 20 * k + 16 = 20 * k + (4 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 20 * k + 17 = 20 * k + (4 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 20 * k + 18 = 20 * k + (4 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 20 * k + 19 = 20 * k + (4 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (20 * k + 20) = 84 * k + 84 ∧
    a (20 * k + 21) = 84 * k + 88 ∧
    a (20 * k + 22) = 84 * k + 94 ∧
    a (20 * k + 23) = 84 * k + 96 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 20 * k + 20 = 20 * k + (4 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 20 * k + 21 = 20 * k + (4 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 20 * k + 22 = 20 * k + (4 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 20 * k + 23 = 20 * k + (4 + 19) from rfl, b_res k 19 (by decide), c38, c39]

/-- The closed form per residue of n mod 20, for n ≥ 4. -/
theorem a_closed (k : ℕ) :
    a (20 * k + 4) = 84 * k + 16 ∧
    a (20 * k + 5) = 84 * k + 22 ∧
    a (20 * k + 6) = 84 * k + 24 ∧
    a (20 * k + 7) = 84 * k + 30 ∧
    a (20 * k + 8) = 84 * k + 34 ∧
    a (20 * k + 9) = 84 * k + 38 ∧
    a (20 * k + 10) = 84 * k + 42 ∧
    a (20 * k + 11) = 84 * k + 44 ∧
    a (20 * k + 12) = 84 * k + 52 ∧
    a (20 * k + 13) = 84 * k + 56 ∧
    a (20 * k + 14) = 84 * k + 58 ∧
    a (20 * k + 15) = 84 * k + 62 ∧
    a (20 * k + 16) = 84 * k + 66 ∧
    a (20 * k + 17) = 84 * k + 74 ∧
    a (20 * k + 18) = 84 * k + 76 ∧
    a (20 * k + 19) = 84 * k + 78 ∧
    a (20 * k + 20) = 84 * k + 84 ∧
    a (20 * k + 21) = 84 * k + 88 ∧
    a (20 * k + 22) = 84 * k + 94 ∧
    a (20 * k + 23) = 84 * k + 96 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15⟩ := a_closed1 k
  obtain ⟨x16, x17, x18, x19⟩ := a_closed2 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19⟩

def controlsK : PLift ((List.range 50).map b = [1, 4, 8, 10, 16, 22, 24, 30, 34, 38, 42, 44, 52, 56, 58, 62, 66, 74, 76, 78, 84, 88, 94, 96, 100, 106, 108, 114, 118, 122, 126, 128, 136, 140, 142, 146, 150, 158, 160, 162, 168, 172, 178, 180, 184, 190, 192, 198, 202, 206]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 10, 16, 22, 24, 30, 34, 38, 42, 44, 52, 56, 58, 62, 66, 74, 76, 78, 84, 88, 94, 96, 100, 106, 108, 114, 118, 122, 126, 128, 136, 140, 142, 146, 150, 158, 160, 162, 168, 172, 178, 180, 184, 190, 192, 198, 202, 206] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 20 → dv (t + 8) + dv (t + 6) + dv (t + 2) + dv (t + 0) = dv (t + 7) + dv (t + 5) + dv (t + 3) + dv (t + 1)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 20 → dv (t + 8) + dv (t + 6) + dv (t + 2) + dv (t + 0) = dv (t + 7) + dv (t + 5) + dv (t + 3) + dv (t + 1) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 8) : ℤ) = (dv (t + 7) : ℤ) - (dv (t + 6) : ℤ) + (dv (t + 5) : ℤ) + (dv (t + 3) : ℤ) - (dv (t + 2) : ℤ) + (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 20 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 5, e 6, e 7, e 8]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 20) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 20 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 20 → b (q + 12) + b (q + 10) + b (q + 6) + b (q + 4) = b (q + 11) + b (q + 9) + b (q + 7) + b (q + 5)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 20 → b (q + 12) + b (q + 10) + b (q + 6) + b (q + 4) = b (q + 11) + b (q + 9) + b (q + 7) + b (q + 5) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 12) : ℤ) = b (q + 11) - b (q + 10) + b (q + 9) + b (q + 7) - b (q + 6) + b (q + 5) - b (q + 4) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 20 ∨ 20 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 20 := ⟨q - 20, by omega⟩
      have h0 : (b (v + 12) : ℤ) = b (v + 11) - b (v + 10) + b (v + 9) + b (v + 7) - b (v + 6) + b (v + 5) - b (v + 4) := ih (v + 0) (by omega)
      have hd := drec v
      have s4 : (b (v + 24) : ℤ) = b (v + 4) + dv (v + 0) := by
        have h := b_step (v + 4) (le_trans (by decide : 4 ≤ 4) (Nat.le_add_left _ v))
        rw [show v + 4 + 20 = v + 24 from Nat.add_assoc _ _ _,
          show v + 4 - 4 = v + 0 from Nat.add_sub_assoc (by decide : 4 ≤ 4) v] at h
        exact_mod_cast h
      have s5 : (b (v + 25) : ℤ) = b (v + 5) + dv (v + 1) := by
        have h := b_step (v + 5) (le_trans (by decide : 4 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 20 = v + 25 from Nat.add_assoc _ _ _,
          show v + 5 - 4 = v + 1 from Nat.add_sub_assoc (by decide : 4 ≤ 5) v] at h
        exact_mod_cast h
      have s6 : (b (v + 26) : ℤ) = b (v + 6) + dv (v + 2) := by
        have h := b_step (v + 6) (le_trans (by decide : 4 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 20 = v + 26 from Nat.add_assoc _ _ _,
          show v + 6 - 4 = v + 2 from Nat.add_sub_assoc (by decide : 4 ≤ 6) v] at h
        exact_mod_cast h
      have s7 : (b (v + 27) : ℤ) = b (v + 7) + dv (v + 3) := by
        have h := b_step (v + 7) (le_trans (by decide : 4 ≤ 7) (Nat.le_add_left _ v))
        rw [show v + 7 + 20 = v + 27 from Nat.add_assoc _ _ _,
          show v + 7 - 4 = v + 3 from Nat.add_sub_assoc (by decide : 4 ≤ 7) v] at h
        exact_mod_cast h
      have s9 : (b (v + 29) : ℤ) = b (v + 9) + dv (v + 5) := by
        have h := b_step (v + 9) (le_trans (by decide : 4 ≤ 9) (Nat.le_add_left _ v))
        rw [show v + 9 + 20 = v + 29 from Nat.add_assoc _ _ _,
          show v + 9 - 4 = v + 5 from Nat.add_sub_assoc (by decide : 4 ≤ 9) v] at h
        exact_mod_cast h
      have s10 : (b (v + 30) : ℤ) = b (v + 10) + dv (v + 6) := by
        have h := b_step (v + 10) (le_trans (by decide : 4 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 20 = v + 30 from Nat.add_assoc _ _ _,
          show v + 10 - 4 = v + 6 from Nat.add_sub_assoc (by decide : 4 ≤ 10) v] at h
        exact_mod_cast h
      have s11 : (b (v + 31) : ℤ) = b (v + 11) + dv (v + 7) := by
        have h := b_step (v + 11) (le_trans (by decide : 4 ≤ 11) (Nat.le_add_left _ v))
        rw [show v + 11 + 20 = v + 31 from Nat.add_assoc _ _ _,
          show v + 11 - 4 = v + 7 from Nat.add_sub_assoc (by decide : 4 ≤ 11) v] at h
        exact_mod_cast h
      have s12 : (b (v + 32) : ℤ) = b (v + 12) + dv (v + 8) := by
        have h := b_step (v + 12) (le_trans (by decide : 4 ≤ 12) (Nat.le_add_left _ v))
        rw [show v + 12 + 20 = v + 32 from Nat.add_assoc _ _ _,
          show v + 12 - 4 = v + 8 from Nat.add_sub_assoc (by decide : 4 ≤ 12) v] at h
        exact_mod_cast h
      show (b (v + 32) : ℤ) = b (v + 31) - b (v + 30) + b (v + 29) + b (v + 27) - b (v + 26) + b (v + 25) - b (v + 24)
      linear_combination s12 - (1) * s11 - (-1) * s10 - (1) * s9 - (1) * s7 - (-1) * s6 - (1) * s5 - (-1) * s4 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 11 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 5) - a (n - 6) + a (n - 7) - a (n - 8) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 12 := ⟨n - 12, by omega⟩
  rw [show q + 12 - 1 = q + 11 from Nat.add_sub_assoc (by decide : 1 ≤ 12) q, show q + 12 - 2 = q + 10 from Nat.add_sub_assoc (by decide : 2 ≤ 12) q, show q + 12 - 3 = q + 9 from Nat.add_sub_assoc (by decide : 3 ≤ 12) q, show q + 12 - 5 = q + 7 from Nat.add_sub_assoc (by decide : 5 ≤ 12) q, show q + 12 - 6 = q + 6 from Nat.add_sub_assoc (by decide : 6 ≤ 12) q, show q + 12 - 7 = q + 5 from Nat.add_sub_assoc (by decide : 7 ≤ 12) q, show q + 12 - 8 = q + 4 from Nat.add_sub_assoc (by decide : 8 ≤ 12) q]
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

/-- The coefficients of A * DEN and NUM agree below 12, in natural numbers (negative terms moved
across). -/
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (b n) (bk n 2)) (bk n 6)) (bk n 8)) (Nat.mul 2 (ind n 11))

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (bk n 1) (bk n 3)) (bk n 5)) (bk n 7)) (ind n 0)) (Nat.mul 3 (ind n 1))) (Nat.mul 5 (ind n 2))) (Nat.mul 5 (ind n 3))) (Nat.mul 10 (ind n 4))) (Nat.mul 7 (ind n 5))) (Nat.mul 5 (ind n 6))) (Nat.mul 7 (ind n 7))) (ind n 8)

def gfK : PLift ((allR 12 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 12, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 12) :
    1 * (b (n) : ℚ) - 1 * (if 1 ≤ n then (b (n - 1) : ℚ) else 0) + 1 * (if 2 ≤ n then (b (n - 2) : ℚ) else 0) - 1 * (if 3 ≤ n then (b (n - 3) : ℚ) else 0) - 1 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) + 1 * (if 6 ≤ n then (b (n - 6) : ℚ) else 0) - 1 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) + 1 * (if 8 ≤ n then (b (n - 8) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 3 + (if n = 2 then (1 : ℚ) else 0) * 5 + (if n = 3 then (1 : ℚ) else 0) * 5 + (if n = 4 then (1 : ℚ) else 0) * 10 + (if n = 5 then (1 : ℚ) else 0) * 7 + (if n = 6 then (1 : ℚ) else 0) * 5 + (if n = 7 then (1 : ℚ) else 0) * 7 + (if n = 8 then (1 : ℚ) else 0) * 1 - (if n = 11 then (1 : ℚ) else 0) * 2 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 12 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 12) : ℚ) - 1 * (if 1 ≤ q + 12 then (b (q + 12 - 1) : ℚ) else 0) + 1 * (if 2 ≤ q + 12 then (b (q + 12 - 2) : ℚ) else 0) - 1 * (if 3 ≤ q + 12 then (b (q + 12 - 3) : ℚ) else 0) - 1 * (if 5 ≤ q + 12 then (b (q + 12 - 5) : ℚ) else 0) + 1 * (if 6 ≤ q + 12 then (b (q + 12 - 6) : ℚ) else 0) - 1 * (if 7 ≤ q + 12 then (b (q + 12 - 7) : ℚ) else 0) + 1 * (if 8 ≤ q + 12 then (b (q + 12 - 8) : ℚ) else 0) =
      (if q + 12 = 0 then (1 : ℚ) else 0) * 1 + (if q + 12 = 1 then (1 : ℚ) else 0) * 3 + (if q + 12 = 2 then (1 : ℚ) else 0) * 5 + (if q + 12 = 3 then (1 : ℚ) else 0) * 5 + (if q + 12 = 4 then (1 : ℚ) else 0) * 10 + (if q + 12 = 5 then (1 : ℚ) else 0) * 7 + (if q + 12 = 6 then (1 : ℚ) else 0) * 5 + (if q + 12 = 7 then (1 : ℚ) else 0) * 7 + (if q + 12 = 8 then (1 : ℚ) else 0) * 1 - (if q + 12 = 11 then (1 : ℚ) else 0) * 2 := by
  have h : (b (q + 12) : ℤ) = b (q + 11) - b (q + 10) + b (q + 9) + b (q + 7) - b (q + 6) + b (q + 5) - b (q + 4) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 12 - 1 = q + 11 from Nat.add_sub_assoc (by decide : 1 ≤ 12) q, show q + 12 - 2 = q + 10 from Nat.add_sub_assoc (by decide : 2 ≤ 12) q, show q + 12 - 3 = q + 9 from Nat.add_sub_assoc (by decide : 3 ≤ 12) q, show q + 12 - 5 = q + 7 from Nat.add_sub_assoc (by decide : 5 ≤ 12) q, show q + 12 - 6 = q + 6 from Nat.add_sub_assoc (by decide : 6 ≤ 12) q, show q + 12 - 7 = q + 5 from Nat.add_sub_assoc (by decide : 7 ≤ 12) q, show q + 12 - 8 = q + 4 from Nat.add_sub_assoc (by decide : 8 ≤ 12) q, show 1 ≤ q + 12 from le_trans (by decide : 1 ≤ 12) (Nat.le_add_left 12 q), show 2 ≤ q + 12 from le_trans (by decide : 2 ≤ 12) (Nat.le_add_left 12 q), show 3 ≤ q + 12 from le_trans (by decide : 3 ≤ 12) (Nat.le_add_left 12 q), show 5 ≤ q + 12 from le_trans (by decide : 5 ≤ 12) (Nat.le_add_left 12 q), show 6 ≤ q + 12 from le_trans (by decide : 6 ≤ 12) (Nat.le_add_left 12 q), show 7 ≤ q + 12 from le_trans (by decide : 7 ≤ 12) (Nat.le_add_left 12 q), show 8 ≤ q + 12 from le_trans (by decide : 8 ≤ 12) (Nat.le_add_left 12 q), show ¬ q + 12 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 12) (Nat.le_add_left 12 q)), show ¬ q + 12 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 12) (Nat.le_add_left 12 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) = C 1 * A - C 1 * (A * X ^ 1) + C 1 * (A * X ^ 2) - C 1 * (A * X ^ 3) - C 1 * (A * X ^ 5) + C 1 * (A * X ^ 6) - C 1 * (A * X ^ 7) + C 1 * (A * X ^ 8) := by
  simp only [map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (-2 * X ^ 11 + X ^ 8 + 7 * X ^ 7 + 5 * X ^ 6 + 7 * X ^ 5 + 10 * X ^ 4 + 5 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 3 + X ^ 2 * C 5 + X ^ 3 * C 5 + X ^ 4 * C 10 + X ^ 5 * C 7 + X ^ 6 * C 5 + X ^ 7 * C 7 + X ^ 8 * C 1 - X ^ 11 * C 2 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -2 * X ^ 11 + X ^ 8 + 7 * X ^ 7 + 5 * X ^ 6 + 7 * X ^ 5 + 10 * X ^ 4 + 5 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  rw [gf_den A, gf_num]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 12 with hn | hn
  · linarith [gf_low n hn]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 12 := ⟨n - 12, by omega⟩
    linarith [gf_high q]

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -2 * X ^ 11 + X ^ 8 + 7 * X ^ 7 + 5 * X ^ 6 + 7 * X ^ 5 + 10 * X ^ 4 + 5 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 11 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 5) - a (n - 6) + a (n - 7) - a (n - 8) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 10, 16, 22, 24, 30, 34, 38, 42, 44, 52, 56, 58, 62, 66, 74, 76, 78, 84, 88, 94, 96, 100, 106, 108, 114, 118, 122, 126, 128, 136, 140, 142, 146, 150, 158, 160, 162, 168, 172, 178, 180, 184, 190, 192, 198, 202, 206] := Count.controls

/-- The step a(n + 20) = a(n) + 84 for n ≥ 4. -/
theorem a_step (n : ℕ) (hn : 4 ≤ n) : a (n + 20) = a n + 84 := Count.a_step n hn

/-- The closed form per residue of n mod 20, for n ≥ 4. -/
theorem a_closed (k : ℕ) :
    a (20 * k + 4) = 84 * k + 16 ∧
    a (20 * k + 5) = 84 * k + 22 ∧
    a (20 * k + 6) = 84 * k + 24 ∧
    a (20 * k + 7) = 84 * k + 30 ∧
    a (20 * k + 8) = 84 * k + 34 ∧
    a (20 * k + 9) = 84 * k + 38 ∧
    a (20 * k + 10) = 84 * k + 42 ∧
    a (20 * k + 11) = 84 * k + 44 ∧
    a (20 * k + 12) = 84 * k + 52 ∧
    a (20 * k + 13) = 84 * k + 56 ∧
    a (20 * k + 14) = 84 * k + 58 ∧
    a (20 * k + 15) = 84 * k + 62 ∧
    a (20 * k + 16) = 84 * k + 66 ∧
    a (20 * k + 17) = 84 * k + 74 ∧
    a (20 * k + 18) = 84 * k + 76 ∧
    a (20 * k + 19) = 84 * k + 78 ∧
    a (20 * k + 20) = 84 * k + 84 ∧
    a (20 * k + 21) = 84 * k + 88 ∧
    a (20 * k + 22) = 84 * k + 94 ∧
    a (20 * k + 23) = 84 * k + 96 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      -2 * X ^ 11 + X ^ 8 + 7 * X ^ 7 + 5 * X ^ 6 + 7 * X ^ 5 + 10 * X ^ 4 + 5 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 5) - a (n - 6) + a (n - 7) - a (n - 8) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a311007

theorem OMA.solution : type_of% @OMA.S_oeis_a311007.main :=
  OMA.S_oeis_a311007.conjecture
