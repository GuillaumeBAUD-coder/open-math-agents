import OMAStatements.S_oeis_a314740

namespace OMA.S_oeis_a314740






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 10

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 484919890
  | 1 => 519554609
  | 2 => 554189328
  | 3 => 729460011
  | 4 => 555270639
  | 5 => 694858059
  | 6 => 589905358
  | 7 => 693776748
  | 8 => 624540077
  | 9 => 659174796
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 6) : ℤ := tget 520668687 5 16 i.val

def Bc (i : Fin 6) : ℤ := tget 833364168 5 16 i.val

def Cc (s : Fin 10) (i : Fin 6) : ℤ := tget (CcT s.val) 5 16 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 16. -/
def AcN (i : ℕ) : ℕ := tgetN 520668687 5 i

def BcN (i : ℕ) : ℕ := tgetN 833364168 5 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem Ac_eq (i : Fin 6) : Ac i = (AcN i.val : ℤ) - 16 := rfl

theorem Bc_eq (i : Fin 6) : Bc i = (BcN i.val : ℤ) - 16 := rfl

theorem Cc_eq (s : Fin 10) (i : Fin 6) : Cc s i = (CcN s.val i.val : ℤ) - 16 := rfl


/-- The potential of facet i at v (facets in angular order around the growth polygon). -/
def pot (v : V) (i : Fin 6) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest facet potential at v. -/
def F (v : V) : ℤ := max (max (max (max (max (pot v 0) (pot v 1)) (pot v 2)) (pot v 3)) (pot v 4)) (pot v 5)

theorem le_F0 (v : V) : pot v 0 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_refl _)))))
theorem le_F1 (v : V) : pot v 1 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))))
theorem le_F2 (v : V) : pot v 2 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
theorem le_F3 (v : V) : pot v 3 ≤ F v := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
theorem le_F4 (v : V) : pot v 4 ≤ F v := le_max_of_le_left (le_max_right _ _)
theorem le_F5 (v : V) : pot v 5 ≤ F v := le_max_right _ _

theorem le_F (v : V) (i : Fin 6) : pot v i ≤ F v := by
  fin_cases i
  exacts [le_F0 v, le_F1 v, le_F2 v, le_F3 v, le_F4 v, le_F5 v]

theorem F_le (v : V) (t : ℤ) (h0 : pot v 0 ≤ t) (h1 : pot v 1 ≤ t) (h2 : pot v 2 ≤ t) (h3 : pot v 3 ≤ t) (h4 : pot v 4 ≤ t) (h5 : pot v 5 ≤ t) : F v ≤ t :=
  max_le (max_le (max_le (max_le (max_le (h0) h1) h2) h3) h4) h5

theorem F_le_all (v : V) (t : ℤ) (h : ∀ i, pot v i ≤ t) : F v ≤ t :=
  F_le v t (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)

theorem max_ex {v : V} {a b : ℤ} (ha : ∃ i, a = pot v i) (hb : ∃ i, b = pot v i) :
    ∃ i, max a b = pot v i := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem exists_F (v : V) : ∃ i, F v = pot v i :=
  max_ex (max_ex (max_ex (max_ex (max_ex (⟨0, rfl⟩) ⟨1, rfl⟩) ⟨2, rfl⟩) ⟨3, rfl⟩) ⟨4, rfl⟩) ⟨5, rfl⟩

/-- A statement about every vertex class follows from the statements about each class. -/
theorem cls (P : Fin 10 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 10 × Fin 10 × ℤ × ℤ) (j : Fin 6) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 6, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 10 × Fin 10 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 10 × Fin 10 × ℤ × ℤ) (j : Fin 6) :
    pot (x + e.2.2.1, y + e.2.2.2, e.2.1) j = pot (x, y, e.1) j + dl e j := by
  simp only [pot, dl]
  ring

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

theorem pair_of {a f b : ℤ} (hl : a ≤ f) (hf : f = b) : a ≤ b + 0 := by omega

theorem bound_of {r f b : ℤ} (hr : r < f) (hf : f = b) : r + 1 ≤ b := by omega

theorem not_pair2 {a b : ℤ} (h : ¬ a ≤ b + (-2)) : b ≤ a + 1 := by omega

/-- Three facts pot a_k ≤ pot b_k + t_k and a bound r ≤ pot i0 at (x, y, s), with multipliers
whose x and y parts cancel and whose constants add up to a positive number, cannot hold together. -/
theorem farkas (x y : ℤ) (s : Fin 10) (a1 b1 a2 b2 a3 b3 i0 : Fin 6) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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

/-- Certificates of the far facts, the same for every class: for maximal facet i and a facet j not
adjacent to i, the fields k1, k2, m1, m2, m0, mj of entry i * 6 + j give the facts pot k1 ≤ pot i,
pot k2 ≤ pot i, 6 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 3555181554390901260363092478901997535234252773478197715040300844848580844235645749480313351133702716070656115519088888966584380927787745747353095839830869233704747051765648607531802596526176391261586114955641070808584397356335349890280665216343004987568064040591326220566207397633889748080308251573237055488 5 ((i * 6 + j) * 6 + f)

def fd (i j : Fin 6) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 6) : Fin 6 := ⟨fdN i.val j.val 0 % 6, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 6) : Fin 6 := ⟨fdN i.val j.val 1 % 6, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 6) : ℤ := fd i j 2

def fm2 (i j : Fin 6) : ℤ := fd i j 3

def fm0 (i j : Fin 6) : ℤ := fd i j 4

def fmj (i j : Fin 6) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 6 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 3766260642138538433957731297779899259963041339088359718912 4 p

def dstv (p : ℕ) : ℕ := tgetN 3764524986007514167234959095960020591979318963722070798592 4 p

def dxv (p : ℕ) : ℕ := tgetN 41577764345515970684176654680 2 p

def dyv (p : ℕ) : ℕ := tgetN 26409387504754779197915092245 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 28817835507908199362229389736112652844880612246724641866883517835983143973680985653453775260404342564314100354458205816212629851963937589251081726748414076585227101530487208490257981827945795948824196693424250100665935845655884063292349615787658140359259605692209298420989568951638592932272889018157122078113590724064337857806622673335666056132489 4 (p * 6 + j)

def dlv (p : ℕ) (j : Fin 6) : ℤ := (dlvN p j.val : ℤ) - 8

theorem dlv_neg (p : ℕ) (j : Fin 6) (h : dlvN p j.val + 1 ≤ 8) : dlv p j ≤ -1 := by
  unfold dlv
  omega

theorem dlv_le (p : ℕ) (j : Fin 6) (c : ℕ) (h : dlvN p j.val + 1 ≤ c + 8) : dlv p j ≤ (c : ℤ) - 1 := by
  unfold dlv
  omega

/-- The next and the previous facet around the growth polygon. -/
def nxt (i : Fin 6) : Fin 6 := ⟨(i.val + 1) % 6, Nat.mod_lt _ (by norm_num)⟩

def prv (i : Fin 6) : Fin 6 := ⟨(i.val + 5) % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The facets i and j are not equal and not adjacent sides of the growth polygon. -/
def nonadj (i j : Fin 6) : Prop := j ≠ i ∧ j ≠ nxt i ∧ j ≠ prv i

instance : DecidableRel nonadj := fun i j => by unfold nonadj; infer_instance

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 16). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 6) + fdN i j 3 * AcN (fdN i j 1 % 6) + fdN i j 5 * AcN i + fdN i j 4 * 16 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 6) + fdN i j 3 * BcN (fdN i j 1 % 6) + fdN i j 5 * BcN i + fdN i j 4 * 16 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * BcN i + fdN i j 5 * BcN j)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farCN (s i j : ℕ) : Bool :=
  Nat.blt ((fdN i j 2 + fdN i j 3 + fdN i j 4) * CcN s i + fdN i j 5 * (CcN s j + 1))
    (fdN i j 2 * CcN s (fdN i j 0 % 6) + fdN i j 3 * CcN s (fdN i j 1 % 6) + fdN i j 5 * CcN s i +
      fdN i j 4 * 22)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 6 || j == (i + 5) % 6

def farOK : Bool := (List.range 6).all fun i => (List.range 6).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 10).all fun s => (List.range 6).all fun i => (List.range 6).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 16, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 48).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 6).all fun j =>
      dlvN p j + 1 * AcN j + 16 * dxv p + 1 * BcN j + 16 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 32 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 10) (i j : Fin 6) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (6 - Cc s i)

/-- Beyond F = 5, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 10) (i j : Fin 6) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 5 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 6 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
    (pair_of (le_F _ _) h) (pair_of (le_F _ _) h) (not_pair2 hc') (bound_of hF h)

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

/-- Descent rules beyond F = 5, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 5 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 27441409769286496413787773648033720253434573439081505276040907407026416778859990767656352249405646758301878480032292102084523912089294999157564617020531956605676936984912901287693518555279782368719890069220129434683098436305318961974626069335774919000493957828055552672060499370046353859022113998706967727774150629801262696988281893619899917979701733670547718915892049514429281909416339830232663662554496645402712672435816597419186248715408805972455531355087601597062835934478512154176065202182718236153108300521672283811172903993791916453562518918994492759541024026944928958777698628091354588090001813077901474521112546355611839329445582447852565682914972536388902692477960937807937
  | 1 => 27441409774040960512837172396865107372381658964757582033613658365655109862962043676386040388936894407732572160144295187155261183848101354548410272105248249179861469578934679646738529585566194472504725852450199990795726402313141165992267697333100480216250058253228742058593281830227522355855072878919372150343286597088611906397879898396495725272227653291176740580684101632634712325344936836621546852932714700939547058822712133611661541887102432813088953563132920989326414668481805392556680393630702994558148426984561893464364063522799329369104998194485306897299355391830003005540689166609985967339252556585332133466424171949944208539925810781025368792899999434856259253386900954947649
  | 2 => 27441409780380245978236370728640290416133357766285243856298369544182008797656166512747770721961388394294744047840326290749404158310135677416495945757290250887137826619260702713642850311932592689104114961217452577315153520170707846406046031538530175523716495559365802290604867256838965938336032658657504744759928042074399916346901207250301420750841506259789984272148167514990041029104766316311759589554281767720503309874872978560025924812573878257887619055818370170319890803958252223845403189143235344007369077039834359215720754275370619467466026309297357006504431567685916212320382338787335231281504055345285412779260985935242892647274650562226383723277723985174744110223224477065281
  | 3 => 27441409791473995542684967809246860906565519244428321655437396531837992351177777417105769542090796481268916613497150491197124527071764048390805106448956456316467753636661312145894700807150503196352282720260850269629916672380361804494570039237333249630865272256851785328808903096265340778760101870880047071923156036202668611404301837114004315784848043638637000429819958439006720955876968166155514049891986293786605046169530830462424468121176568876182758010638024558225110495211613199511868284096347031511241372134725194002391025468324723361002996194029938096007711806346543632968513165346963679882183104905643586329211675268326216118420739396136238307635959015567079695708646773366849
  | 4 => 27441409797813281008084166141022043786450529470449054897417192318192526712083878217079315112218269033069683447722796688885381181318196137297986785979478720121454202122518332312636406600876046428159110170780818462246819963572537364511484859981667239190022308952563662406873476697723780409981778613236695164998268821868668609214563395680389715536857662822226168191499480238728422378695101475332614971161582493484696863014129935241894474978023552222695579883291083845494590363792419568392017300076719152098761022623358199526200995659940554751568857809858249939482609691466103033978011895138213379751124075760552599682875626659306283842337209386387517728035009981559522373070461720600641
  | 5 => 27441409808907030572532763221628614276882690948629391667820352272786964432180955386066019023525467243786073068549271125792147501959551887884409922082813590170010817707146406256720265996818174625145361430623059025964782346457947762782361890474966133457393138818251794672328579416926416488154898655697614742851426425022969361921585427685232441086843795831977590719533339526630484633487838249097560206379997649355937606894338446053257499600505995450310725553222540951314799001510675601705009342897234552980867909461910713597394834656676559308938475407029883568608384536934625927204618476340967136466984408579003663241478817800385944372469828890949258127011904168837213563233551084953665
  | 6 => 27441409813661494671582161970460001395829776474305468425393103231448228204800311403646854970339981823746146458244489584618654774235815872473945732430510759850338701080972323814890534125356183326250907782245528656542145888922932918578382286117036075887915291416585368508665690746549044746361071502282700865447295628249786968579263078732781322013564234345009513652334513397355516723843871084685376456817508869192876292567706784535405095853318063954440692920860180086582750650895728043155869203671829968462353734070153968799243404806915057701886413533904673478962014957399121440810978201514917148909077303010475697338321338972946965833990909987526756508040994287050753121752607121219649
  | 7 => 27441409824755244236030759051066571886261937952448546224532130219104211778547480812393518552102440664256215300414835339060350206402995378333141572659047348218686330498496491812016234351061512287684523894588703349905569322892116815771263573418268755117873017510433621348255557890254667133059259369168130807331672233041424589664570510022712554997749025104824938842225934563589590672920972760732384501491627589415574138024686324051511703958044215772261765896871934354681016662084033299343261443568062298108319274983141670668915090079089252285955516180921556439458468045213407332679682817742612468063527889719091482239591210567718103632760282477013125516635799687863861356842588925337665
  | 8 => 27441409829509708335080157799897959005209023478124622982104881177765475541535618494551180802901216790151576177484567343604012210390901679644159916560615764118529593681787381482151335941272178867749380554163660122840713683566849619612828121630610314156581384681928019088694654313077653702563470951628032351488899240714256993451816350867295560710098866766542622880994678103243838483243444783910908298371426536494207986065704644904902517439804316410981388663951083725485285043861297103395544727688280758024035856904390798933195141320561349034998979669672420111627078783626768814919093815476889621537007201580533122887080205782148068751616949670127311594097392227928550669098889587728449
  | 9 => 27441409839018636533178955297560733570836571680416115716131947945555823943576802749093776302437957769994834009028613998995226672083953163946288427038678766679444129242276416082507817030821776192648464217314539002619854360353199640233495622938754857117781040641133609436712032452994819076284910621235231243113861408192939008375348314148004103928019646199088010482445356567683071939362574558524795079283813083286948460100082637901540022196002978747971582083346808304407490782543713955704407607157647090857896929575572672723174433172741879250724738061445108252981263417321934792475142336428794232544601003948629817231130422238162596077607776406539810254340897050295289620326001377812545
  | _ => 0

def rd (s : Fin 10) (i : Fin 6) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 10) (i : Fin 6) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 10) (i : Fin 6) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 10) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 10) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 10) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 10) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 10) (i : Fin 6) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 48 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 5)
  else if rk s i c1 c2 = 2 then
    decide (c1.val ≤ 1 ∧ rg s i c1 c2 ∣ Ac i - Ac (nxt i) ∧ rg s i c1 c2 ∣ Bc i - Bc (nxt i) ∧
      ¬ rg s i c1 c2 ∣ (c1.val : ℤ) - (Cc s i - Cc s (nxt i)))
  else if rk s i c1 c2 = 3 then
    decide (c2.val ≤ 1 ∧ rg s i c1 c2 ∣ Ac i - Ac (prv i) ∧ rg s i c1 c2 ∣ Bc i - Bc (prv i) ∧
      ¬ rg s i c1 c2 ∣ (c2.val : ℤ) - (Cc s i - Cc s (prv i)))
  else false

/-- All the tables: the far certificates for non-adjacent facets, the edge tables and the descent
rules. -/
theorem tables_ok : farOK = true ∧ farCOK = true ∧ dlOK = true ∧ (∀ s i c1 c2, ruleOK s i c1 c2 = true) := by
  decide +kernel

/-- The far certificates hold in the integers: the natural-number checks moved across. -/
theorem far_cert (s : Fin 10) (i j : Fin 6) (hij : nonadj i j) : farCert s i j := by
  have hn : nearB i.val j.val = false := by
    obtain ⟨h1, h2, h3⟩ := hij
    have e1 : j.val ≠ i.val := fun h => h1 (Fin.ext h)
    have e2 : j.val ≠ (i.val + 1) % 6 := fun h => h2 (Fin.ext h)
    have e3 : j.val ≠ (i.val + 5) % 6 := fun h => h3 (Fin.ext h)
    simp only [nearB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨e1, e2⟩, e3⟩
  have hxy := tables_ok.1
  have hc := tables_ok.2.1
  unfold farOK at hxy
  unfold farCOK at hc
  simp only [List.all_eq_true, List.mem_range] at hxy hc
  have hx := hxy i.val i.isLt j.val j.isLt
  have hk := hc s.val s.isLt i.val i.isLt j.val j.isLt
  rw [hn, Bool.false_or] at hx hk
  simp only [farXYN, Bool.and_eq_true, beq_iff_eq] at hx
  simp only [farCN, Nat.blt_eq] at hk
  obtain ⟨hA, hB⟩ := hx
  have cA := congrArg (Nat.cast : ℕ → ℤ) hA
  have cB := congrArg (Nat.cast : ℕ → ℤ) hB
  have ck := (Nat.cast_lt (α := ℤ)).mpr hk
  push_cast at cA cB ck
  simp only [farCert, fm1, fm2, fmj, fm0, fd, Ac_eq, Bc_eq, Cc_eq, fk1, fk2]
  refine ⟨by positivity, by positivity, by positivity, by positivity, by linear_combination cA,
    by linear_combination cB, ?_⟩
  ring_nf at ck ⊢
  linarith

theorem edge_at (p : ℕ) (hp : p < 48) :
    srcv p = (E.getD p (0, 0, 0, 0)).1.val ∧ ∀ j, dlv p j = dl (E.getD p (0, 0, 0, 0)) j := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h p hp
  refine ⟨h1.symm, fun j => ?_⟩
  have hN := congrArg (Nat.cast : ℕ → ℤ) (h5 j.val j.isLt)
  push_cast at hN
  generalize E.getD p (0, 0, 0, 0) = e at h1 h2 h3 h4 ⊢
  obtain ⟨s1, s2, dx, dy⟩ := e
  simp only at h1 h2 h3 h4
  have ex : dx = (dxv p : ℤ) - 1 := by omega
  have ey : dy = (dyv p : ℤ) - 1 := by omega
  subst ex ey
  simp only [dlv, dl, Ac_eq, Bc_eq, Cc_eq, h1, h2]
  linear_combination hN

theorem edge_tab (p : ℕ) (hp : p < 48) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 10) (i : Fin 6) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 5)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 5 < pot (x, y, s) i) : False := by
  have m1 : u1 * (pot (x, y, s) i - pot (x, y, s) (nxt i)) = u1 * c1 := by rw [e1]
  have m2 : u2 * (pot (x, y, s) i - pot (x, y, s) (prv i)) = u2 * c2 := by rw [e2]
  have key := mul_lt_mul_of_pos_left hF hu0
  have ha' : (u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i))) * x = u0 * Ac i * x := by rw [ha]
  have hb' : (u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i))) * y = u0 * Bc i * y := by rw [hb]
  simp only [pot] at m1 m2 key
  nlinarith [ha', hb', m1, m2, key, hc]

theorem dvd_contra (x y : ℤ) (a b c g : ℤ) (ha : g ∣ a) (hb : g ∣ b) (hc : ¬ g ∣ c) (e : a * x + b * y = c) :
    False :=
  hc (e ▸ dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y))

/-- Beyond F = 5 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 10) (i : Fin 6) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 5 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
  have p1 : 0 ≤ pot (x, y, s) i - pot (x, y, s) (nxt i) := by have := le_F (x, y, s) (nxt i); omega
  have p2 : 0 ≤ pot (x, y, s) i - pot (x, y, s) (prv i) := by have := le_F (x, y, s) (prv i); omega
  have hv := tables_ok.2.2.2 s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
    (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))
  have q1 := scl_le _ p1
  have q2 := scl_le _ p2
  unfold ruleOK at hv
  split_ifs at hv with k0 k1 k2 k3
  · -- an edge that descends
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hlen, hsrc, hdi, hdn, hdp⟩ := hv
    have hdi := dlv_neg _ _ hdi
    have hdn := dlv_le _ _ _ hdn
    have hdp := dlv_le _ _ _ hdp
    obtain ⟨hs0, hdl⟩ := edge_at _ hlen
    have hmem : E.getD (re s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
        (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))) (0, 0, 0, 0) ∈ E := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    rw [hdl] at hdi hdn hdp
    rw [hs0] at hsrc
    generalize E.getD (re s i (scl (pot (x, y, s) i - pot (x, y, s) (nxt i)))
        (scl (pot (x, y, s) i - pot (x, y, s) (prv i)))) (0, 0, 0, 0) = e at hmem hsrc hdi hdn hdp
    have hs : e.1 = s := Fin.ext hsrc
    have ha := adj_of_mem e hmem x y
    rw [hs] at ha
    refine ⟨_, ha, step_down _ _ ha (fun j => ?_)⟩
    have hsh := shift x y e j
    rw [hs] at hsh
    rw [hsh]
    have hst := (E_step e hmem j).1
    have hj := le_F (x, y, s) j
    by_cases hji : j = i
    · subst hji
      omega
    by_cases hjn : j = nxt i
    · subst hjn
      omega
    by_cases hjp : j = prv i
    · subst hjp
      omega
    have hna : nonadj i j := ⟨hji, hjn, hjp⟩
    have := far s i j (far_cert s i j hna) x y h hF
    omega
  · -- a corner point within F ≤ 5
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc1, hc2, hu0, ha, hb, hc⟩ := hv
    exact (point_contra x y s i _ _ _ _ _ hu0 ha hb hc (scl_eq _ p1 hc1) (scl_eq _ p2 hc2) (h ▸ hF)).elim
  · -- the line of the next facet has no lattice point
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc1, ha, hb, hc⟩ := hv
    have e1 := scl_eq _ p1 hc1
    generalize scl (pot (x, y, s) i - pot (x, y, s) (nxt i)) = c at e1 ha hb hc
    simp only [pot] at e1
    exact (dvd_contra x y _ _ _ _ ha hb hc (by linear_combination e1)).elim
  · -- the line of the previous facet has no lattice point
    simp only [decide_eq_true_eq] at hv
    obtain ⟨hc2, ha, hb, hc⟩ := hv
    have e2 := scl_eq _ p2 hc2
    generalize scl (pot (x, y, s) i - pot (x, y, s) (prv i)) = c at e2 ha hb hc
    simp only [pot] at e2
    exact (dvd_contra x y _ _ _ _ ha hb hc (by linear_combination e2)).elim

theorem far_desc (v : V) (hF : 5 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 10) (a1 a2 a3 : Fin 6) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 10, 0 < 8 * (Cc s 0 - 5) + 8 * (Cc s 5 - 5) + 0 * (Cc s 0 - 5) + 16 * 6 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 10, 0 < 8 * (Cc s 2 - 5) + 8 * (Cc s 3 - 5) + 0 * (Cc s 0 - 5) + 16 * 6 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 10, 0 < 1 * (Cc s 1 - 5) + 0 * (Cc s 0 - 5) + 0 * (Cc s 0 - 5) + 10 * 2 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 10, 0 < 1 * (Cc s 4 - 5) + 0 * (Cc s 0 - 5) + 0 * (Cc s 0 - 5) + 10 * 2 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 10, 0 < 1 * (Cc s 2 - (-1)) + 1 * (Cc s 5 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 5 lies in the cells |x| ≤ 5, |y| ≤ 1 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 10) (hF : F (x, y, s) ≤ 5) :
    -5 ≤ x ∧ x ≤ 5 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 5 0 5 8 8 0 1 0 6 16 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 3 0 5 8 8 0 (-1) 0 6 16 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 1 0 0 5 1 0 0 0 1 2 10 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 0 0 5 1 0 0 0 (-1) 2 10 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 2 5 0 (-1) 1 1 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 5, b - 1) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 3036647579176240699358504476147987567160527915576191376655578942877305190109809830854624518668852427579676051178531207313737997090239519794825879082356920476794024704916285193736938225474415686057789751934193169766264112793491970667307415713009097140173689244690282668355597836393937768229610218162080952494340992661255219339003242344816040214904025342679010985005940281088226174571111922700736042604508722394726511513414376849934413377650629072198494886371910431945876658193556326883201531139620179819858630695264441509547948243004368011593596526519829374502436864 >>> (6 * ((a * 3 + b) * 10 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 5, b - 1) and class s, potential i plus
15 + 1 a + 10 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 6) : ℕ :=
  tgetN 1116192 5 i.val * a + tgetN 625543170 5 i.val * b + tgetN 973167704131134882902233802216121525049238602405585646554322477718602577950202893062656894 5 (s * 6 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)

theorem fnt_tab : ∀ s : Fin 10, ∀ i : Fin 6, (tgetN 1116192 5 i.val : ℤ) = Ac i + 1 ∧
    (tgetN 625543170 5 i.val : ℤ) = Bc i + 10 ∧
    (tgetN 973167704131134882902233802216121525049238602405585646554322477718602577950202893062656894 5 (s.val * 6 + i.val) : ℤ) = Cc s i - Ac i * 5 - Bc i * 1 + 15 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 10) (i : Fin 6) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 5, (b : ℤ) - 1, s) i + (15 + 1 * a + 10 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 10) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 5, (b : ℤ) - 1, s) + (15 + 1 * a + 10 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 5, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (1 + 10) 1 = FN + 1 dx' + 10 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 11).all fun a => (List.range 3).all fun b => (List.range 10).all fun s =>
    Nat.blt (20 + 1 * a + 10 * b) (FN a b s) || (a == 5 && b == 1 && s == 2) ||
      (Nat.blt (hint a b s) 48 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 11 ==
          FN a b s + 1 * dxv (hint a b s) + 10 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 5) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 5).toNat (by omega) (y + 1).toNat (by omega) s.val s.isLt
  have ex : (((x + 5).toNat : ℕ) : ℤ) - 5 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  generalize (x + 5).toNat = a at h' ex
  generalize (y + 1).toNat = b at h' ey
  have fv := FN_eq a b s
  rw [ex, ey] at fv
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at h'
  rcases h' with (h1 | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨⟨⟨hlen, hs⟩, hdx⟩, hdy⟩, hfe⟩
  · have c1 := (Nat.cast_lt (α := ℤ)).mpr h1
    push_cast at c1
    omega
  · exfalso
    apply hv
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    have hs0 : s = 2 := Fin.ext (by rw [h3]; rfl)
    subst hx0 hy0 hs0
    rfl
  · obtain ⟨e1, e2, e3, e4⟩ := edge_tab _ hlen
    have he : E.getD (hint a b s.val) (0, 0, 0, 0) ∈ E := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    rw [← e2] at hfe
    generalize E.getD (hint a b s.val) (0, 0, 0, 0) = e at he e1 e2 e3 e4 hfe
    obtain ⟨s1, s2, dx, dy⟩ := e
    simp only at e1 e2 e3 e4 hfe
    have hs1 : s1 = s := Fin.ext (e1.trans hs)
    have ha := adj_of_mem _ he x y
    simp only at ha
    rw [hs1] at ha
    refine ⟨_, ha, ?_⟩
    have fw := FN_eq (a + dxv (hint a b s.val) - 1) (b + dyv (hint a b s.val) - 1) s2
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 5 = x + dx := by omega
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 1 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 5
  · exact near_desc v hF hv
  · exact far_desc v (by omega)

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

/-- The graph distance from v0 is the largest facet potential. -/
theorem dist_eq (v : V) : G.dist v0 v = (F v).toNat := by
  apply dist_eq_of_potential G v0 (fun v => (F v).toNat)
  · show (F v0).toNat = 0
    decide
  · intro u w h
    have := lip u w h
    have := F_nonneg w
    have := F_nonneg u
    show (F w).toNat ≤ (F u).toNat + 1
    omega
  · intro v hv
    obtain ⟨w, hw, he⟩ := desc v hv
    refine ⟨w, hw, ?_⟩
    have := F_nonneg w
    show (F w).toNat + 1 = (F v).toNat
    omega


/-! ## Counting the spheres

The sphere F = n splits into pieces: class s and the first facet i attaining the maximum. The
gradient of facet i is gc i times the primitive vector (Ap i, Bp i), so the points of class s with
pot_i = n lie on the line Ap i x + Bp i y = c with c = lev s i n, and only when gc i divides
n - Cc s i. That line is par s i c u = (al i c + Bp i u, be i c - Ap i u), and potential j is
ka i j c + Dm i j u + Cc s j there (`pot_par`). The previous facet bounds u from above, the next one
from below, and for n ≥ 4 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 10 moves every quotient by an integer (`inner_shift`,
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
def AW (i : ℕ) : ℕ := tgetN 520668687 5 i

def BW (i : ℕ) : ℕ := tgetN 833364168 5 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem A_W (i : Fin 6) : Ac i = (AW i.val : ℤ) - 16 := rfl

theorem B_W (i : Fin 6) : Bc i = (BW i.val : ℤ) - 16 := rfl

theorem C_W (s : Fin 10) (i : Fin 6) : Cc s i = (CW s.val i.val : ℤ) - 16 := rfl

def gcV (k : ℕ) : ℕ := ctabN 1708449 4 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 6) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 420 2 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 1

def Ap (i : Fin 6) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 546832608 5 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 8

def Bp (i : Fin 6) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 420 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 6) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 1617 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 6) : ℤ := beN i.val

def primK : PLift (∀ i : Fin 6, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧ al i * Ap i + be i * Bp i = 1) :=
  ⟨by decide +kernel⟩

theorem prim : ∀ i : Fin 6, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧ al i * Ap i + be i * Bp i = 1 := primK.down

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 6) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 6) : ℤ := Ac j * al i + Bc j * be i

def orientK : PLift (∀ i : Fin 6, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0) :=
  ⟨by decide +kernel⟩

theorem orient : ∀ i : Fin 6, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := orientK.down

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 10) (i : Fin 6) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 10) (i j : Fin 6) (c u : ℤ) :
    pot (par s i c u) j = ka i j * c + Dm i j * u + Cc s j := by
  simp only [pot, par, ka, Dm]
  ring

theorem par_inv (v : V) (i : Fin 6) :
    v = par v.2.2 i (Ap i * v.1 + Bp i * v.2.1) (be i * v.1 - al i * v.2.1) := by
  obtain ⟨x, y, s⟩ := v
  have hb := (prim i).2.2.2
  simp only [par, Prod.mk.injEq, and_true]
  constructor
  · linear_combination (-x) * hb
  · linear_combination (-y) * hb

theorem pot_lev (v : V) (i : Fin 6) : pot v i = gc i * (Ap i * v.1 + Bp i * v.2.1) + Cc v.2.2 i := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  simp only [pot]
  rw [h1, h2]
  ring

theorem par_inj (s : Fin 10) (i : Fin 6) (c : ℤ) : Function.Injective (par s i c) := by
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
theorem F_attained (v : V) : ∃ k : Fin 6, pot v k = F v := by
  by_contra hne
  have h : ∀ k, pot v k ≤ F v - 1 := fun k => by
    have h1 := le_F v k
    have h2 : pot v k ≠ F v := fun e => hne ⟨k, e⟩
    omega
  have := F_le v (F v - 1) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)
  omega

/-- The first facet attaining the maximum. -/
noncomputable def fi (v : V) : Fin 6 := Fin.find (fun k => pot v k = F v) (F_attained v)

theorem fi_spec (v : V) : pot v (fi v) = F v ∧ ∀ j, j < fi v → pot v j < F v :=
  ⟨Fin.find_spec (F_attained v), fun j hj =>
    lt_of_le_of_ne (le_F v j) (Fin.find_min (F_attained v) hj)⟩

theorem fi_iff (v : V) (i : Fin 6) : fi v = i ↔ pot v i = F v ∧ ∀ j, j < i → pot v j < F v := by
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
theorem piece_iff (v : V) (i : Fin 6) (n : ℤ) :
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
def prevF (i : ℕ) : ℕ := Nat.mod (Nat.add i 5) 6

def nextF (i : ℕ) : ℕ := Nat.mod (Nat.add i 1) 6

def ehV (k : ℕ) : ℕ := ctabN 62 1 k

def ekV (k : ℕ) : ℕ := ctabN 32 1 k

def fin_prevK : PLift (∀ i : Fin 6, (i - 1).val = prevF i.val ∧ (if i - 1 < i then (1 : ℤ) else 0) = (ehV i.val : ℤ)) :=
  ⟨by decide +kernel⟩

theorem fin_prev : ∀ i : Fin 6, (i - 1).val = prevF i.val ∧ (if i - 1 < i then (1 : ℤ) else 0) = (ehV i.val : ℤ) := fin_prevK.down

def fin_nextK : PLift (∀ i : Fin 6, (i + 1).val = nextF i.val ∧ (if i + 1 < i then (1 : ℤ) else 0) = (ekV i.val : ℤ)) :=
  ⟨by decide +kernel⟩

theorem fin_next : ∀ i : Fin 6, (i + 1).val = nextF i.val ∧ (if i + 1 < i then (1 : ℤ) else 0) = (ekV i.val : ℤ) := fin_nextK.down

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (4 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 46363472594469142231438190094869774794752 4 k

def cf2V (k : ℕ) : ℕ := ctabN 7252268006285485048924996820060449277952 4 k

def cf3V (k : ℕ) : ℕ := ctabN 23224271584528191712180292971511121712384 4 k

def cf0V (k : ℕ) : ℕ := ctabN 43585392903270349183090623521280 4 k

def cf1 (i j : Fin 6) : ℤ := (cf1V (j.val + 6 * i.val) : ℤ)

def cf2 (i j : Fin 6) : ℤ := (cf2V (j.val + 6 * i.val) : ℤ)

def cf3 (i j : Fin 6) : ℤ := (cf3V (j.val + 6 * i.val) : ℤ)

def cf0 (i j : Fin 6) : ℤ := (cf0V (j.val + 6 * i.val) : ℤ)

/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 6) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 10) (i j : Fin 6) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (4 - Cc s i)

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := Nat.beq j i || Nat.beq j (nextF i) || Nat.beq j (prevF i)

/-- certG in natural numbers: Ac = AW - 16, Bc = BW - 16, the negative terms moved across. -/
def certGN (i j : ℕ) : Bool :=
  Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 6 i))) (AW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 6 i))) (AW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (AW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 6 i))) 16))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 6 i))) (cf2V (Nat.add j (Nat.mul 6 i)))) (cf0V (Nat.add j (Nat.mul 6 i)))) (AW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (AW j))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 6 i))) (BW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 6 i))) (BW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (BW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 6 i))) 16))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 6 i))) (cf2V (Nat.add j (Nat.mul 6 i)))) (cf0V (Nat.add j (Nat.mul 6 i)))) (BW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (BW j)))

/-- certC in natural numbers: Cc = CW - 16, the negative terms moved across. -/
def certCN (s i j : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 6 i))) (cf2V (Nat.add j (Nat.mul 6 i)))) (cf0V (Nat.add j (Nat.mul 6 i)))) (CW s i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (CW s j)))
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 6 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 6 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 6 i))) 20))

def certGK : PLift ((allR 6 fun i => allR 6 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 6 fun i => allR 6 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 10 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 10) : certS s = true := by
  exact allI_get _ _ _ certCK0.down s (by omega) (by omega)

theorem beq_ff (x y : ℕ) (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem near_false (i j : Fin 6) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
theorem certG_ok (i j : Fin 6) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) : certG i j := by
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
theorem certC_ok (s : Fin 10) (i j : Fin 6) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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

theorem farkas4 (v : V) (h i k j : Fin 6) (e1 e2 r l1 l2 l3 l0 : ℤ)
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
def lev (s : Fin 10) (i : Fin 6) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 10) (i : Fin 6) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 10) (i j : Fin 6) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 10) (i : Fin 6) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 10) (i : Fin 6) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 10) (i j : Fin 6) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 10) (i : Fin 6) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 10) (i : Fin 6) (n u : ℤ) :
    lo s i n ≤ u ↔ Dm i (i + 1) * u ≤ Rb s i (i + 1) n := by
  have hd : 0 < -Dm i (i + 1) := by linarith [(orient i).2]
  rw [lo, neg_le, Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> linarith

theorem ka_self (i : Fin 6) : ka i i = gc i := by
  obtain ⟨h1, h2, -, hb⟩ := prim i
  rw [ka, h1, h2]
  linear_combination (gc i) * hb

theorem Dm_self (i : Fin 6) : Dm i i = 0 := by
  obtain ⟨h1, h2, -, -⟩ := prim i
  rw [Dm, h1, h2]
  ring

theorem pot_par_self (s : Fin 10) (i : Fin 6) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 4 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 10) (i : Fin 6) (n u : ℤ) (hn : 4 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 4 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-7, 7]: a natural-number check. -/
def cbK : PLift ((allR 10 fun s => allR 6 fun i => Nat.ble (CW s i) 23 && Nat.ble 16 (Nat.add (CW s i) 7)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 10) (j : Fin 6) : -7 ≤ Cc s j ∧ Cc s j ≤ 7 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 7)) (1 * n + 7) ×ˢ
    (Finset.Icc (-(1 * n + 7)) (1 * n + 7) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (1 * Ac 2 + 1 * Ac 3 = 2 ∧ 1 * Bc 2 + 1 * Bc 3 = 0 ∧
    1 * Ac 0 + 1 * Ac 5 = (-2) ∧ 1 * Bc 0 + 1 * Bc 5 = 0 ∧
    1 * Ac 4 + 0 * Ac 4 = 0 ∧ 1 * Bc 4 + 0 * Bc 4 = 10 ∧
    1 * Ac 1 + 0 * Ac 1 = 0 ∧ 1 * Bc 1 + 0 * Bc 1 = (-10)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 1 * Ac 2 + 1 * Ac 3 = 2 ∧ 1 * Bc 2 + 1 * Bc 3 = 0 ∧
    1 * Ac 0 + 1 * Ac 5 = (-2) ∧ 1 * Bc 0 + 1 * Bc 5 = 0 ∧
    1 * Ac 4 + 0 * Ac 4 = 0 ∧ 1 * Bc 4 + 0 * Bc 4 = 10 ∧
    1 * Ac 1 + 0 * Ac 1 = 0 ∧ 1 * Bc 1 + 0 * Bc 1 = (-10) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 10) :
    2 * x ≤ 2 * F (x, y, s) + 14 ∧
    2 * (-x) ≤ 2 * F (x, y, s) + 14 ∧
    10 * y ≤ 1 * F (x, y, s) + 7 ∧
    10 * (-y) ≤ 1 * F (x, y, s) + 7 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 2 + 1 * pot (x, y, s) 3 =
      2 * x + 1 * Cc s 2 + 1 * Cc s 3 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 2
  have r0 := le_F (x, y, s) 3
  have k0 := Cbound s 2
  have l0 := Cbound s 3
  have e1 : 1 * pot (x, y, s) 0 + 1 * pot (x, y, s) 5 =
      2 * (-x) + 1 * Cc s 0 + 1 * Cc s 5 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 5
  have k1 := Cbound s 0
  have l1 := Cbound s 5
  have e2 : 1 * pot (x, y, s) 4 + 0 * pot (x, y, s) 4 =
      10 * y + 1 * Cc s 4 + 0 * Cc s 4 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 4
  have r2 := le_F (x, y, s) 4
  have k2 := Cbound s 4
  have l2 := Cbound s 4
  have e3 : 1 * pot (x, y, s) 1 + 0 * pot (x, y, s) 1 =
      10 * (-y) + 1 * Cc s 1 + 0 * Cc s 1 := by
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
noncomputable def PF (s : Fin 10) (i : Fin 6) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 10) (i : Fin 6) (n : ℤ) (hn : 4 ≤ n) :
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
def inner (s : Fin 10) (i : Fin 6) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 10) (i : Fin 6) (n : ℤ) (hn : 4 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 10 × Fin 6, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 10 × Fin 6, inner p.1 p.2 n

/-! Shifting n by 10 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 10594842 4 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 6) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 1560 2 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ)

def mh (i : Fin 6) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 585 2 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ)

def mk (i : Fin 6) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 6, (10 : ℤ) = gc i * Lq i ∧ 10 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 10 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 6, (10 : ℤ) = gc i * Lq i ∧ 10 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 10 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 10) (i : Fin 6) (n : ℤ) :
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

/-- The growth of S over one period. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 10 × Fin 6, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 10) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 10 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 10 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 4 + r with r < 10: the level is QQ - 1 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 1560 2 k

def uhMV (k : ℕ) : ℕ := ctabN 0 1 k

def ukPV (k : ℕ) : ℕ := ctabN 585 2 k

def ukMV (k : ℕ) : ℕ := ctabN 0 1 k

def dhV (k : ℕ) : ℕ := ctabN 337127472 5 k

def dkV (k : ℕ) : ℕ := ctabN 538263594 5 k

def mhkV (k : ℕ) : ℕ := ctabN 49761 3 k

def uh (i : Fin 6) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 6) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 6) : ℤ := dhV i.val

def dk (i : Fin 6) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 6, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 6, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 13480385412970777799758483240521816519792699617901226484218559070240 4 (Nat.add i (Nat.mul 6 s))

def QQ (s i : ℕ) : ℕ := ctabN 228407321191644390345441978406422517410113065340947497587336960623604499 4 (Nat.add i (Nat.mul 6 s))

def AH (s i : ℕ) : ℕ := ctabN 996629296367740579568955401506814131741676198971647466240533104541348100 4 (Nat.add i (Nat.mul 6 s))

def AK (s i : ℕ) : ℕ := ctabN 669712904439905475767688190618911293466922283365727269166855074461279234 4 (Nat.add i (Nat.mul 6 s))

def WH (s i : ℕ) : ℕ := ctabN 417027049887375137548035437159006532 2 (Nat.add i (Nat.mul 6 s))

def WK (s i : ℕ) : ℕ := ctabN 109907607618193440 1 (Nat.add i (Nat.mul 6 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 10 fun s => allR 6 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq (Nat.add 20 (gcV i)) (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (uhPV i)) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (uhMV i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (ukPV i)) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (ukMV i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 10) (i : Fin 6) :
    PP s.val i.val < gcV i.val ∧
    (4 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 1) + PP s.val i.val ∧
    (AH s.val i.val : ℤ) = uh i * ((QQ s.val i.val : ℤ) - 1) +
      (Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0)) + dh i * WH s.val i.val -
      (uhMV i.val : ℤ) * LqV i.val ∧
    (AK s.val i.val : ℤ) = uk i * ((QQ s.val i.val : ℤ) - 1) +
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

/-- Piece (s, i) at n = 4 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 4 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 10) (i : Fin 6) (r : ℕ) :
    ((4 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (4 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 1) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 10) (i : Fin 6) (r : ℕ) (hr : r < 10) :
    inner s i ((4 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (10 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 10 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((4 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 1) + tauN s.val i.val r := by
      rw [lev, show (4 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 1) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((4 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((4 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 878416384462359600 6 k

def tblV (k : ℕ) : ℕ := ctabN 876968514068992581 6 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 10. -/
def dv (t : ℕ) : ℕ := dtabV (t % 10)

/-- The sequence in closed form: b(n + 10) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 10) + tblV ((n - 1) % 10)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 10) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 10 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 10 - 1 = n - 1 + 10 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 10)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 10) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 10 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 10 - 1 = n - 1 + 10 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 10)]
  ring

/-- b on the residue class of 1 + j mod 10. -/
theorem b_res (k j : ℕ) (hj : j < 10) : b (10 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (10 * k + (1 + j) < 1) by omega),
    show 10 * k + (1 + j) - 1 = j + 10 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 10), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 4 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 10 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 10 fun s => allR 6 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 10 fun s => sumR 6 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 4 r)) &&
    Nat.beq (sumR 10 fun s => sumR 6 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 1 (dv (Nat.add 3 r)))

/-! The window n = 4, ..., 13, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 10 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 10) :
    (∀ s, s < 10 → ∀ i, i < 6 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 10 fun s => sumR 6 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (4 + r) ∧
    (sumR 10 fun s => sumR 6 fun i => cond (divN s i r) (mhkV i) 0) = 1 * dv (3 + r) := by
  have h : periodR r = true := by
    exact allI_get _ _ _ periodK0.down r (by omega) (by omega)
  simp only [periodR, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun s hs i hi hd => ?_, h2, h3⟩
  have h4 := (allR_iff _ _).1 ((allR_iff _ _).1 h1 s hs) i hi
  rw [hd] at h4
  simpa using h4

theorem innerZ_eq (s i r : ℕ) (hs : s < 10) (hi : i < 6) (hr : r < 10) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 10 fun s => sumR 6 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 10 × Fin 6, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 6 fun i => f s i : ℕ) : ℤ)) 10]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 6]

theorem S_window (r : ℕ) (hr : r < 10) : S ((4 : ℤ) + r) = b (4 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 10) : Gs ((4 : ℤ) + r) = ((1 * dv (3 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 4 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 10) (i : Fin 6) (n : ℤ) (hn : 4 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 4 + t := ⟨(n - 4).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 10
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 10) (by omega) (by omega)
      have e : (4 : ℤ) + t = (4 + (t - 10 : ℕ)) + 10 := by
        push_cast [Nat.cast_sub (by omega : 10 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 4 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 10 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 4 ≤ n) : (1 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 4) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((4 : ℤ) + (((n - 4) % 10 : ℕ) : ℤ)) + 10 * (((n - 4) / 10 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (3 + (n - 4) % 10) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 4 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 14
    · obtain ⟨r, rfl⟩ : ∃ r, n = 4 + r := ⟨n - 4, by omega⟩
      push_cast
      exact S_window r (by omega)
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

The points with F ≤ 3 lie in the box -10 ≤ x ≤ 10, -1 ≤ y ≤ 1 (`small_box`). In natural-number
coordinates a = x + 10, b = y + 1 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 10) (h : F (x, y, s) ≤ 3) :
    -10 ≤ x ∧ x ≤ 10 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 10, (b : ℤ) - 1, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 176) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 10) (BW i)) 16) (Nat.add (Nat.mul 16 a) (Nat.mul 16 b))

theorem pot_box (a b : ℕ) (s : Fin 10) (i : Fin 6) :
    pot ((a : ℤ) - 10, (b : ℤ) - 1, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 6 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 10) : F ((a : ℤ) - 10, (b : ℤ) - 1, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 10, (b : ℤ) - 1, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 10, (b : ℤ) - 1, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 6 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 6 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 10, (b : ℤ) - 1, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 10, (b : ℤ) - 1, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 10, (b : ℤ) - 1, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 21 fun a => sumR 3 fun b => sumR 10 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 0 .. 3, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 0 4 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 4) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 10) : V := ((q.1 : ℤ) - 10, (q.2.1 : ℤ) - 1, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 3) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 21 ×ˢ (Finset.range 3 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 10 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 10).toNat, (y + 1).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 10).toNat (y + 1).toNat s
        rw [show (((x + 10).toNat : ℕ) : ℤ) - 10 = x by omega,
          show (((y + 1).toNat : ℕ) : ℤ) - 1 = y by omega, h] at e
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 10]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 4 are counted in the
box, those from 4 on are S(n), and both agree with the closed form b (`a_eq_b`). The step from n to
n + 10, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 4 ∨ 4 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_eq n (by omega) h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

def dconst_baseK : PLift (∀ r : ℕ, r < 10 → dtabV r = 48) :=
  ⟨by decide +kernel⟩

theorem dconst_base : ∀ r : ℕ, r < 10 → dtabV r = 48 := dconst_baseK.down

theorem dv_const : ∀ t : ℕ, dv t = 48 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 10) = a(n) + 48 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 10) = a n + 48 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 48 ∧ tblV 0 = 5 ∧ dv 1 = 48 ∧ tblV 1 = 9 ∧ dv 2 = 48 ∧ tblV 2 = 13 ∧ dv 3 = 48 ∧ tblV 3 = 18 ∧ dv 4 = 48 ∧ tblV 4 = 24 ∧ dv 5 = 48 ∧ tblV 5 = 30 ∧ dv 6 = 48 ∧ tblV 6 = 35 ∧ dv 7 = 48 ∧ tblV 7 = 39) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 48 ∧ tblV 8 = 43 ∧ dv 9 = 48 ∧ tblV 9 = 48) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (10 * k + 1) = 48 * k + 5 ∧
    a (10 * k + 2) = 48 * k + 9 ∧
    a (10 * k + 3) = 48 * k + 13 ∧
    a (10 * k + 4) = 48 * k + 18 ∧
    a (10 * k + 5) = 48 * k + 24 ∧
    a (10 * k + 6) = 48 * k + 30 ∧
    a (10 * k + 7) = 48 * k + 35 ∧
    a (10 * k + 8) = 48 * k + 39 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 10 * k + 1 = 10 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 10 * k + 2 = 10 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 10 * k + 3 = 10 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 10 * k + 4 = 10 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 10 * k + 5 = 10 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 10 * k + 6 = 10 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 10 * k + 7 = 10 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 10 * k + 8 = 10 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (10 * k + 9) = 48 * k + 43 ∧
    a (10 * k + 10) = 48 * k + 48 := by
  obtain ⟨c16, c17, c18, c19⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_⟩
  · rw [show 10 * k + 9 = 10 * k + (1 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 10 * k + 10 = 10 * k + (1 + 9) from rfl, b_res k 9 (by decide), c18, c19]

/-- The closed form per residue of n mod 10, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (10 * k + 1) = 48 * k + 5 ∧
    a (10 * k + 2) = 48 * k + 9 ∧
    a (10 * k + 3) = 48 * k + 13 ∧
    a (10 * k + 4) = 48 * k + 18 ∧
    a (10 * k + 5) = 48 * k + 24 ∧
    a (10 * k + 6) = 48 * k + 30 ∧
    a (10 * k + 7) = 48 * k + 35 ∧
    a (10 * k + 8) = 48 * k + 39 ∧
    a (10 * k + 9) = 48 * k + 43 ∧
    a (10 * k + 10) = 48 * k + 48 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9⟩ := a_closed1 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9⟩

def controlsK : PLift ((List.range 50).map b = [1, 5, 9, 13, 18, 24, 30, 35, 39, 43, 48, 53, 57, 61, 66, 72, 78, 83, 87, 91, 96, 101, 105, 109, 114, 120, 126, 131, 135, 139, 144, 149, 153, 157, 162, 168, 174, 179, 183, 187, 192, 197, 201, 205, 210, 216, 222, 227, 231, 235]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 9, 13, 18, 24, 30, 35, 39, 43, 48, 53, 57, 61, 66, 72, 78, 83, 87, 91, 96, 101, 105, 109, 114, 120, 126, 131, 135, 139, 144, 149, 153, 157, 162, 168, 174, 179, 183, 187, 192, 197, 201, 205, 210, 216, 222, 227, 231, 235] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 10 → dv (t + 10) + 2 * dv (t + 8) + 2 * dv (t + 6) + 2 * dv (t + 4) + 2 * dv (t + 2) + dv (t + 0) = 2 * dv (t + 9) + 2 * dv (t + 7) + 2 * dv (t + 5) + 2 * dv (t + 3) + 2 * dv (t + 1)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 10 → dv (t + 10) + 2 * dv (t + 8) + 2 * dv (t + 6) + 2 * dv (t + 4) + 2 * dv (t + 2) + dv (t + 0) = 2 * dv (t + 9) + 2 * dv (t + 7) + 2 * dv (t + 5) + 2 * dv (t + 3) + 2 * dv (t + 1) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 10) : ℤ) = 2 * (dv (t + 9) : ℤ) - 2 * (dv (t + 8) : ℤ) + 2 * (dv (t + 7) : ℤ) - 2 * (dv (t + 6) : ℤ) + 2 * (dv (t + 5) : ℤ) - 2 * (dv (t + 4) : ℤ) + 2 * (dv (t + 3) : ℤ) - 2 * (dv (t + 2) : ℤ) + 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 10 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 10) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 10 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 10 → b (q + 11) + 2 * b (q + 9) + 2 * b (q + 7) + 2 * b (q + 5) + 2 * b (q + 3) + b (q + 1) = 2 * b (q + 10) + 2 * b (q + 8) + 2 * b (q + 6) + 2 * b (q + 4) + 2 * b (q + 2)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 10 → b (q + 11) + 2 * b (q + 9) + 2 * b (q + 7) + 2 * b (q + 5) + 2 * b (q + 3) + b (q + 1) = 2 * b (q + 10) + 2 * b (q + 8) + 2 * b (q + 6) + 2 * b (q + 4) + 2 * b (q + 2) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 11) : ℤ) = 2 * b (q + 10) - 2 * b (q + 9) + 2 * b (q + 8) - 2 * b (q + 7) + 2 * b (q + 6) - 2 * b (q + 5) + 2 * b (q + 4) - 2 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 10 ∨ 10 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 10 := ⟨q - 10, by omega⟩
      have h0 : (b (v + 11) : ℤ) = 2 * b (v + 10) - 2 * b (v + 9) + 2 * b (v + 8) - 2 * b (v + 7) + 2 * b (v + 6) - 2 * b (v + 5) + 2 * b (v + 4) - 2 * b (v + 3) + 2 * b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 11) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 10 = v + 11 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s2 : (b (v + 12) : ℤ) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (le_trans (by decide : 1 ≤ 2) (Nat.le_add_left _ v))
        rw [show v + 2 + 10 = v + 12 from Nat.add_assoc _ _ _,
          show v + 2 - 1 = v + 1 from Nat.add_sub_assoc (by decide : 1 ≤ 2) v] at h
        exact_mod_cast h
      have s3 : (b (v + 13) : ℤ) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (le_trans (by decide : 1 ≤ 3) (Nat.le_add_left _ v))
        rw [show v + 3 + 10 = v + 13 from Nat.add_assoc _ _ _,
          show v + 3 - 1 = v + 2 from Nat.add_sub_assoc (by decide : 1 ≤ 3) v] at h
        exact_mod_cast h
      have s4 : (b (v + 14) : ℤ) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (le_trans (by decide : 1 ≤ 4) (Nat.le_add_left _ v))
        rw [show v + 4 + 10 = v + 14 from Nat.add_assoc _ _ _,
          show v + 4 - 1 = v + 3 from Nat.add_sub_assoc (by decide : 1 ≤ 4) v] at h
        exact_mod_cast h
      have s5 : (b (v + 15) : ℤ) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (le_trans (by decide : 1 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 10 = v + 15 from Nat.add_assoc _ _ _,
          show v + 5 - 1 = v + 4 from Nat.add_sub_assoc (by decide : 1 ≤ 5) v] at h
        exact_mod_cast h
      have s6 : (b (v + 16) : ℤ) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (le_trans (by decide : 1 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 10 = v + 16 from Nat.add_assoc _ _ _,
          show v + 6 - 1 = v + 5 from Nat.add_sub_assoc (by decide : 1 ≤ 6) v] at h
        exact_mod_cast h
      have s7 : (b (v + 17) : ℤ) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (le_trans (by decide : 1 ≤ 7) (Nat.le_add_left _ v))
        rw [show v + 7 + 10 = v + 17 from Nat.add_assoc _ _ _,
          show v + 7 - 1 = v + 6 from Nat.add_sub_assoc (by decide : 1 ≤ 7) v] at h
        exact_mod_cast h
      have s8 : (b (v + 18) : ℤ) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (le_trans (by decide : 1 ≤ 8) (Nat.le_add_left _ v))
        rw [show v + 8 + 10 = v + 18 from Nat.add_assoc _ _ _,
          show v + 8 - 1 = v + 7 from Nat.add_sub_assoc (by decide : 1 ≤ 8) v] at h
        exact_mod_cast h
      have s9 : (b (v + 19) : ℤ) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (le_trans (by decide : 1 ≤ 9) (Nat.le_add_left _ v))
        rw [show v + 9 + 10 = v + 19 from Nat.add_assoc _ _ _,
          show v + 9 - 1 = v + 8 from Nat.add_sub_assoc (by decide : 1 ≤ 9) v] at h
        exact_mod_cast h
      have s10 : (b (v + 20) : ℤ) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (le_trans (by decide : 1 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 10 = v + 20 from Nat.add_assoc _ _ _,
          show v + 10 - 1 = v + 9 from Nat.add_sub_assoc (by decide : 1 ≤ 10) v] at h
        exact_mod_cast h
      have s11 : (b (v + 21) : ℤ) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (le_trans (by decide : 1 ≤ 11) (Nat.le_add_left _ v))
        rw [show v + 11 + 10 = v + 21 from Nat.add_assoc _ _ _,
          show v + 11 - 1 = v + 10 from Nat.add_sub_assoc (by decide : 1 ≤ 11) v] at h
        exact_mod_cast h
      show (b (v + 21) : ℤ) = 2 * b (v + 20) - 2 * b (v + 19) + 2 * b (v + 18) - 2 * b (v + 17) + 2 * b (v + 16) - 2 * b (v + 15) + 2 * b (v + 14) - 2 * b (v + 13) + 2 * b (v + 12) - b (v + 11)
      linear_combination s11 - (2) * s10 - (-2) * s9 - (2) * s8 - (-2) * s7 - (2) * s6 - (-2) * s5 - (2) * s4 - (-2) * s3 - (2) * s2 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  rw [show q + 11 - 1 = q + 10 from Nat.add_sub_assoc (by decide : 1 ≤ 11) q, show q + 11 - 2 = q + 9 from Nat.add_sub_assoc (by decide : 2 ≤ 11) q, show q + 11 - 3 = q + 8 from Nat.add_sub_assoc (by decide : 3 ≤ 11) q, show q + 11 - 4 = q + 7 from Nat.add_sub_assoc (by decide : 4 ≤ 11) q, show q + 11 - 5 = q + 6 from Nat.add_sub_assoc (by decide : 5 ≤ 11) q, show q + 11 - 6 = q + 5 from Nat.add_sub_assoc (by decide : 6 ≤ 11) q, show q + 11 - 7 = q + 4 from Nat.add_sub_assoc (by decide : 7 ≤ 11) q, show q + 11 - 8 = q + 3 from Nat.add_sub_assoc (by decide : 8 ≤ 11) q, show q + 11 - 9 = q + 2 from Nat.add_sub_assoc (by decide : 9 ≤ 11) q, show q + 11 - 10 = q + 1 from Nat.add_sub_assoc (by decide : 10 ≤ 11) q]
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

/-- The coefficients of A * DEN and NUM agree below 11, in natural numbers (negative terms moved
across). -/
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (b n) (Nat.mul 2 (bk n 2))) (Nat.mul 2 (bk n 4))) (Nat.mul 2 (bk n 6))) (Nat.mul 2 (bk n 8))) (bk n 10)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 2 (bk n 1)) (Nat.mul 2 (bk n 3))) (Nat.mul 2 (bk n 5))) (Nat.mul 2 (bk n 7))) (Nat.mul 2 (bk n 9))) (ind n 0)) (Nat.mul 3 (ind n 1))) (ind n 2)) (Nat.mul 3 (ind n 3))) (Nat.mul 2 (ind n 4))) (Nat.mul 4 (ind n 5))) (Nat.mul 2 (ind n 6))) (Nat.mul 3 (ind n 7))) (ind n 8)) (Nat.mul 3 (ind n 9))) (ind n 10)

def gfK : PLift ((allR 11 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 11, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 11) :
    1 * (b (n) : ℚ) - 2 * (if 1 ≤ n then (b (n - 1) : ℚ) else 0) + 2 * (if 2 ≤ n then (b (n - 2) : ℚ) else 0) - 2 * (if 3 ≤ n then (b (n - 3) : ℚ) else 0) + 2 * (if 4 ≤ n then (b (n - 4) : ℚ) else 0) - 2 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) + 2 * (if 6 ≤ n then (b (n - 6) : ℚ) else 0) - 2 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) + 2 * (if 8 ≤ n then (b (n - 8) : ℚ) else 0) - 2 * (if 9 ≤ n then (b (n - 9) : ℚ) else 0) + 1 * (if 10 ≤ n then (b (n - 10) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 3 + (if n = 2 then (1 : ℚ) else 0) * 1 + (if n = 3 then (1 : ℚ) else 0) * 3 + (if n = 4 then (1 : ℚ) else 0) * 2 + (if n = 5 then (1 : ℚ) else 0) * 4 + (if n = 6 then (1 : ℚ) else 0) * 2 + (if n = 7 then (1 : ℚ) else 0) * 3 + (if n = 8 then (1 : ℚ) else 0) * 1 + (if n = 9 then (1 : ℚ) else 0) * 3 + (if n = 10 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 11 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 11) : ℚ) - 2 * (if 1 ≤ q + 11 then (b (q + 11 - 1) : ℚ) else 0) + 2 * (if 2 ≤ q + 11 then (b (q + 11 - 2) : ℚ) else 0) - 2 * (if 3 ≤ q + 11 then (b (q + 11 - 3) : ℚ) else 0) + 2 * (if 4 ≤ q + 11 then (b (q + 11 - 4) : ℚ) else 0) - 2 * (if 5 ≤ q + 11 then (b (q + 11 - 5) : ℚ) else 0) + 2 * (if 6 ≤ q + 11 then (b (q + 11 - 6) : ℚ) else 0) - 2 * (if 7 ≤ q + 11 then (b (q + 11 - 7) : ℚ) else 0) + 2 * (if 8 ≤ q + 11 then (b (q + 11 - 8) : ℚ) else 0) - 2 * (if 9 ≤ q + 11 then (b (q + 11 - 9) : ℚ) else 0) + 1 * (if 10 ≤ q + 11 then (b (q + 11 - 10) : ℚ) else 0) =
      (if q + 11 = 0 then (1 : ℚ) else 0) * 1 + (if q + 11 = 1 then (1 : ℚ) else 0) * 3 + (if q + 11 = 2 then (1 : ℚ) else 0) * 1 + (if q + 11 = 3 then (1 : ℚ) else 0) * 3 + (if q + 11 = 4 then (1 : ℚ) else 0) * 2 + (if q + 11 = 5 then (1 : ℚ) else 0) * 4 + (if q + 11 = 6 then (1 : ℚ) else 0) * 2 + (if q + 11 = 7 then (1 : ℚ) else 0) * 3 + (if q + 11 = 8 then (1 : ℚ) else 0) * 1 + (if q + 11 = 9 then (1 : ℚ) else 0) * 3 + (if q + 11 = 10 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 11) : ℤ) = 2 * b (q + 10) - 2 * b (q + 9) + 2 * b (q + 8) - 2 * b (q + 7) + 2 * b (q + 6) - 2 * b (q + 5) + 2 * b (q + 4) - 2 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 11 - 1 = q + 10 from Nat.add_sub_assoc (by decide : 1 ≤ 11) q, show q + 11 - 2 = q + 9 from Nat.add_sub_assoc (by decide : 2 ≤ 11) q, show q + 11 - 3 = q + 8 from Nat.add_sub_assoc (by decide : 3 ≤ 11) q, show q + 11 - 4 = q + 7 from Nat.add_sub_assoc (by decide : 4 ≤ 11) q, show q + 11 - 5 = q + 6 from Nat.add_sub_assoc (by decide : 5 ≤ 11) q, show q + 11 - 6 = q + 5 from Nat.add_sub_assoc (by decide : 6 ≤ 11) q, show q + 11 - 7 = q + 4 from Nat.add_sub_assoc (by decide : 7 ≤ 11) q, show q + 11 - 8 = q + 3 from Nat.add_sub_assoc (by decide : 8 ≤ 11) q, show q + 11 - 9 = q + 2 from Nat.add_sub_assoc (by decide : 9 ≤ 11) q, show q + 11 - 10 = q + 1 from Nat.add_sub_assoc (by decide : 10 ≤ 11) q, show 1 ≤ q + 11 from le_trans (by decide : 1 ≤ 11) (Nat.le_add_left 11 q), show 2 ≤ q + 11 from le_trans (by decide : 2 ≤ 11) (Nat.le_add_left 11 q), show 3 ≤ q + 11 from le_trans (by decide : 3 ≤ 11) (Nat.le_add_left 11 q), show 4 ≤ q + 11 from le_trans (by decide : 4 ≤ 11) (Nat.le_add_left 11 q), show 5 ≤ q + 11 from le_trans (by decide : 5 ≤ 11) (Nat.le_add_left 11 q), show 6 ≤ q + 11 from le_trans (by decide : 6 ≤ 11) (Nat.le_add_left 11 q), show 7 ≤ q + 11 from le_trans (by decide : 7 ≤ 11) (Nat.le_add_left 11 q), show 8 ≤ q + 11 from le_trans (by decide : 8 ≤ 11) (Nat.le_add_left 11 q), show 9 ≤ q + 11 from le_trans (by decide : 9 ≤ 11) (Nat.le_add_left 11 q), show 10 ≤ q + 11 from le_trans (by decide : 10 ≤ 11) (Nat.le_add_left 11 q), show ¬ q + 11 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 11) (Nat.le_add_left 11 q)), show ¬ q + 11 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 11) (Nat.le_add_left 11 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * ((X - 1) ^ 2 * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) = C 1 * A - C 2 * (A * X ^ 1) + C 2 * (A * X ^ 2) - C 2 * (A * X ^ 3) + C 2 * (A * X ^ 4) - C 2 * (A * X ^ 5) + C 2 * (A * X ^ 6) - C 2 * (A * X ^ 7) + C 2 * (A * X ^ 8) - C 2 * (A * X ^ 9) + C 1 * (A * X ^ 10) := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (X ^ 10 + 3 * X ^ 9 + X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + 4 * X ^ 5 + 2 * X ^ 4 + 3 * X ^ 3 + X ^ 2 + 3 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 3 + X ^ 2 * C 1 + X ^ 3 * C 3 + X ^ 4 * C 2 + X ^ 5 * C 4 + X ^ 6 * C 2 + X ^ 7 * C 3 + X ^ 8 * C 1 + X ^ 9 * C 3 + X ^ 10 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 10 + 3 * X ^ 9 + X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + 4 * X ^ 5 + 2 * X ^ 4 + 3 * X ^ 3 + X ^ 2 + 3 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  rw [gf_den A, gf_num]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · linarith [gf_low n hn]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    linarith [gf_high q]

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 10 + 3 * X ^ 9 + X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + 4 * X ^ 5 + 2 * X ^ 4 + 3 * X ^ 3 + X ^ 2 + 3 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 9, 13, 18, 24, 30, 35, 39, 43, 48, 53, 57, 61, 66, 72, 78, 83, 87, 91, 96, 101, 105, 109, 114, 120, 126, 131, 135, 139, 144, 149, 153, 157, 162, 168, 174, 179, 183, 187, 192, 197, 201, 205, 210, 216, 222, 227, 231, 235] := Count.controls

/-- The step a(n + 10) = a(n) + 48 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 10) = a n + 48 := Count.a_step n hn

/-- The closed form per residue of n mod 10, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (10 * k + 1) = 48 * k + 5 ∧
    a (10 * k + 2) = 48 * k + 9 ∧
    a (10 * k + 3) = 48 * k + 13 ∧
    a (10 * k + 4) = 48 * k + 18 ∧
    a (10 * k + 5) = 48 * k + 24 ∧
    a (10 * k + 6) = 48 * k + 30 ∧
    a (10 * k + 7) = 48 * k + 35 ∧
    a (10 * k + 8) = 48 * k + 39 ∧
    a (10 * k + 9) = 48 * k + 43 ∧
    a (10 * k + 10) = 48 * k + 48 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 10 + 3 * X ^ 9 + X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + 4 * X ^ 5 + 2 * X ^ 4 + 3 * X ^ 3 + X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a314740

theorem OMA.solution : type_of% @OMA.S_oeis_a314740.main :=
  OMA.S_oeis_a314740.conjecture
