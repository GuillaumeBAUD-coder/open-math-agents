import OMAStatements.S_oeis_a313685

namespace OMA.S_oeis_a313685






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 8

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 448155316
  | 1 => 623458766
  | 2 => 588824047
  | 3 => 449269394
  | 4 => 554189328
  | 5 => 483904113
  | 6 => 519587376
  | 7 => 518506065
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 6) : ℤ := tget 520668687 5 16 i.val

def Bc (i : Fin 6) : ℤ := tget 764127497 5 16 i.val

def Cc (s : Fin 8) (i : Fin 6) : ℤ := tget (CcT s.val) 5 16 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 16. -/
def AcN (i : ℕ) : ℕ := tgetN 520668687 5 i

def BcN (i : ℕ) : ℕ := tgetN 764127497 5 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem Ac_eq (i : Fin 6) : Ac i = (AcN i.val : ℤ) - 16 := rfl

theorem Bc_eq (i : Fin 6) : Bc i = (BcN i.val : ℤ) - 16 := rfl

theorem Cc_eq (s : Fin 8) (i : Fin 6) : Cc s i = (CcN s.val i.val : ℤ) - 16 := rfl


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
theorem cls (P : Fin 8 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 8 × Fin 8 × ℤ × ℤ) (j : Fin 6) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 6, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 8 × Fin 8 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 8 × Fin 8 × ℤ × ℤ) (j : Fin 6) :
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
theorem farkas (x y : ℤ) (s : Fin 8) (a1 b1 a2 b2 a3 b3 i0 : Fin 6) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
pot k2 ≤ pot i, 8 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 2841953280189506142577999812573309209193127514053639511261349168866941011495954894732311106294116889219041662645343960513616903424224955420462580197030312901516015471344591976710431492577636285908299230990353385999086007868799237654200696222988171419671705739523877662526681482155668427026252378873620594688 5 ((i * 6 + j) * 6 + f)

def fd (i j : Fin 6) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 6) : Fin 6 := ⟨fdN i.val j.val 0 % 6, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 6) : Fin 6 := ⟨fdN i.val j.val 1 % 6, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 6) : ℤ := fd i j 2

def fm2 (i j : Fin 6) : ℤ := fd i j 3

def fm0 (i j : Fin 6) : ℤ := fd i j 4

def fmj (i j : Fin 6) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 6 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 20769176115787202665137009401827328 3 p

def dstv (p : ℕ) : ℕ := tgetN 20722125723358903772291282168481344 3 p

def dxv (p : ℕ) : ℕ := tgetN 39044306426313043960088 2 p

def dyv (p : ℕ) : ℕ := tgetN 25185954575304774473285 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 16310316881627124052120374180220831795666441387419654883780860796741686404164315672769818644773461966288678881138775549029079673733386131814805280346564553293144363749005661538761535732881321218898902824214167051120964691392891413356390890180080951095872866742464547017750409 4 (p * 6 + j)

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
      fdN i j 4 * 24)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 6 || j == (i + 5) % 6

def farOK : Bool := (List.range 6).all fun i => (List.range 6).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 8).all fun s => (List.range 6).all fun i => (List.range 6).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 16, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 38).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 6).all fun j =>
      dlvN p j + 1 * AcN j + 16 * dxv p + 1 * BcN j + 16 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 32 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 8) (i j : Fin 6) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (8 - Cc s i)

/-- Beyond F = 7, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 8) (i j : Fin 6) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 7 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 8 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 7, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 7 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 27441409769286496413787773648033720171501229151328040985688449710934127466440935443234242195864690545356082936800530971406795643799506538609066705103932692552380401127031335467642510743376221474814106656508916533507835254832695625809694152593572257619810742621324479285677397838185391806934150815236347291133335413878015027378113506672203879944159377581179041721452664741074542651159312829727801384697075078829263315993517736244285885468464316296621378613868317248669716619198942707195212396704150626605297477599884407472651674331448382273311896461419648334941729974883149618650625727516078897232716775479206312294854913383518345060356260407484006576092413550742259785810953318391873
  | 1 => 27441409777210603245536771562752698976190852653237618264044338684092751134808588988686405112145308028558797796420569850899474361877049442194173797168985194686475847427438864301272911651334219245563343042467982266657119152154653976326917070350359376754143789253995804575691879621449696285035350539909013034154137220110250039814390142739460999292426693785154103690534273640987449511757700591255746776962305995235310057578796470524185228666311961947478730623846767275784779842378686919190856357328022012142800925829942502744044553020988813849868800168827807675438338778977338114940872355588145258376262521517341101893448971600967118540077626290431753159903744215218215064182898082144321
  | 2 => 27441409783549888710935969894527882019942551454765280086729049862619650069502711825048135445169802015120969684116600954493617336339083765062259470821027196393752204467764887368177232377700617462162732151235234853176546270012220656740695404555789072061610226560132864807703465048061139867516310319647145628570778665096038049763411451593266694771040546753767347381998339523342778215517530070945959513583873062155842734977995614671984197300906462930095008921083128731345793599564914543286726566934602327967473774963637234797625247626447330383113826623134906328504364309468397064584118601172934247427434480945364072112952518324647559707128042163471975194326303391569334083121411068747841
  | 3 => 27441409786719531443635569060415473459885056567812905678983080722702800707788366876424019741046202921932678498553583692187741736821014210471185801563001964322407799449904147418203610336569713650806460220610417829189783694202545263801208995276832134666937053252923980980498025574489415781892437575504100007138178034137618253039325709652562363187946035024400993146306415945934983356854586144614204450706065112816587367948119671697049592798412401115243419794475792483714523230489442263394829896168963047122866902100150651582228409257378824852952807064611528214949511681668808351592782408332170652602658940145121391686581205812484760694749627016365461125928313157113711154427689241370689
  | 4 => 27441409796228459641734366558078248189379293345574068022450929915733166555087735045004019400663888507409887495328091026959705941338943721049664730350917449342136006934291183271963619058081326295397335126133112299416348225585112306083052747513045003617025910469472656071765530879183131151991468696146163729835904696660422324399699400087902818806313244710256183095313962049710043497918160214970724727369778572674363131868438908997923373725604786091952331351122399707542371262325434573577122082539848386718824915506336609126965793594144930157297114559240622111920258887878276502464922617269328672583246603709573349844693512889725269532914353395535908791521723558958630098630133245239361
  | 5 => 27441409800982923740783765306909635308326378871250144780023680874388323310850143258237912990351314391697565245869653675274563429360591436924378567280096468163779602790637699318738331970894109638155085715336736148858494709382070294732210247239048949108736537191732366502524092784365163842474597079914898344575621285355641275424623654573625178014827204203780791452100564181234472940314202473917183108104591013274380173887591350269966477441830778025760941566315631990926275287221555931226654959701943184018241477682067264444774111438378443008938166383124528563449052806386629572673283445042685192659356779125803654315673744351534324531732426894782124056302266590227612459164691464413249
  | 6 => 27441409813661494671582161970460001559696465049775138034833885656682138636090913013964268882098559269927043950380211661554728916226731560543269545984774583195679071004776277382789184247748997724190413836495321055751213899662698264370844598750677887443553777030872665415285207199844206861386265480963731400764175085480723074916982990659130944108308996903596773385027343137333807175529030297912770883857789928269866359458548183054712824853092321300668923016368508035405152246466986573294890403223311862005648093725243589329073897740923910812897555760750046809125172237848037280165980147788891288821583103604521215189949925930807120077988447360447664546393307547558868705684002660638785
  | 7 => 27441409820000780136981360302235184439581475275795871276813681443036672996997013813938252429328416204196579441108350519524375941277155220304047926245089309904858990194455263987176136021516784825014020817032353415998082003125220379892637829098120345008913327219095907808752514840589650829935083574272024286014878298717494012721541597889805443078906326689048916901886022526033923592137753407343752160335372964849039939750778118710642051914376085698071967338593250337153477126054619103576912878653458075199841030242224246110697005959941800053361680738062702656835340336599196197428399078883052142262834493806199778954465256394068535170243178969995685707085143235589291983265411850526785
  | _ => 0

def rd (s : Fin 8) (i : Fin 6) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 8) (i : Fin 6) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 8) (i : Fin 6) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 8) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 8) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 8) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 8) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 8) (i : Fin 6) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 38 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 7)
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
theorem far_cert (s : Fin 8) (i j : Fin 6) (hij : nonadj i j) : farCert s i j := by
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

theorem edge_at (p : ℕ) (hp : p < 38) :
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

theorem edge_tab (p : ℕ) (hp : p < 38) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 8) (i : Fin 6) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 7)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 7 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 7 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 8) (i : Fin 6) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 7 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 7
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

theorem far_desc (v : V) (hF : 7 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 8) (a1 a2 a3 : Fin 6) (t l1 l2 l3 px py q lq : ℤ)
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

theorem near_box0 (x y : ℤ) (hF : F (x, y, 0) ≤ 7) : -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 0) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 0 0 5 0 7 6 7 0 1 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 2 3 0 7 7 6 0 (-1) 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 1 0 0 7 1 0 0 0 1 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 0 4 0 0 7 1 0 0 0 (-1) 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg0 (x y : ℤ) : 0 ≤ F (x, y, 0) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 0) k).trans (show F (x, y, 0) ≤ -1 by omega)
  exact farkas_ub x y 0 2 5 0 (-1) 1 1 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box1 (x y : ℤ) (hF : F (x, y, 1) ≤ 7) : -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 1) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 1 0 5 0 7 6 7 0 1 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 2 3 0 7 7 6 0 (-1) 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 1 0 0 7 1 0 0 0 1 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 1 4 0 0 7 1 0 0 0 (-1) 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg1 (x y : ℤ) : 0 ≤ F (x, y, 1) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 1) k).trans (show F (x, y, 1) ≤ -1 by omega)
  exact farkas_ub x y 1 2 5 0 (-1) 1 1 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box2 (x y : ℤ) (hF : F (x, y, 2) ≤ 7) : -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 2) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 2 0 5 0 7 6 7 0 1 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 2 3 0 7 7 6 0 (-1) 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 1 0 0 7 1 0 0 0 1 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 2 4 0 0 7 1 0 0 0 (-1) 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg2 (x y : ℤ) : 0 ≤ F (x, y, 2) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 2) k).trans (show F (x, y, 2) ≤ -1 by omega)
  exact farkas_ub x y 2 2 5 0 (-1) 1 1 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box3 (x y : ℤ) (hF : F (x, y, 3) ≤ 7) : -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 3) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 3 0 5 0 7 6 7 0 1 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 2 3 0 7 7 6 0 (-1) 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 1 0 0 7 1 0 0 0 1 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 3 4 0 0 7 1 0 0 0 (-1) 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg3 (x y : ℤ) : 0 ≤ F (x, y, 3) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 3) k).trans (show F (x, y, 3) ≤ -1 by omega)
  exact farkas_ub x y 3 2 5 0 (-1) 1 1 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box4 (x y : ℤ) (hF : F (x, y, 4) ≤ 7) : -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 4) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 4 0 5 0 7 6 7 0 1 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 2 3 0 7 7 6 0 (-1) 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 1 0 0 7 1 0 0 0 1 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 4 4 0 0 7 1 0 0 0 (-1) 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg4 (x y : ℤ) : 0 ≤ F (x, y, 4) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 4) k).trans (show F (x, y, 4) ≤ -1 by omega)
  exact farkas_ub x y 4 2 5 0 (-1) 1 1 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box5 (x y : ℤ) (hF : F (x, y, 5) ≤ 7) : -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 5) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 5 0 5 0 7 6 7 0 1 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 2 3 0 7 7 6 0 (-1) 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 1 0 0 7 1 0 0 0 1 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 5 4 0 0 7 1 0 0 0 (-1) 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg5 (x y : ℤ) : 0 ≤ F (x, y, 5) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 5) k).trans (show F (x, y, 5) ≤ -1 by omega)
  exact farkas_ub x y 5 2 5 0 (-1) 1 1 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box6 (x y : ℤ) (hF : F (x, y, 6) ≤ 7) : -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 6) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 6 0 5 0 7 6 7 0 1 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 2 3 0 7 7 6 0 (-1) 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 1 0 0 7 1 0 0 0 1 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 6 4 0 0 7 1 0 0 0 (-1) 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg6 (x y : ℤ) : 0 ≤ F (x, y, 6) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 6) k).trans (show F (x, y, 6) ≤ -1 by omega)
  exact farkas_ub x y 6 2 5 0 (-1) 1 1 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

theorem near_box7 (x y : ℤ) (hF : F (x, y, 7) ≤ 7) : -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, 7) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y 7 0 5 0 7 6 7 0 1 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 2 3 0 7 7 6 0 (-1) 0 8 13 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 1 0 0 7 1 0 0 0 1 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y 7 4 0 0 7 1 0 0 0 (-1) 2 8 (by decide +kernel) (u _) (u _) (u _) (by omega)

theorem F_nonneg7 (x y : ℤ) : 0 ≤ F (x, y, 7) := by
  by_contra hc
  have u := fun k => (le_F (x, y, 7) k).trans (show F (x, y, 7) ≤ -1 by omega)
  exact farkas_ub x y 7 2 5 0 (-1) 1 1 0 0 0 0 0 (by decide +kernel) (u _) (u _) (u _) (by norm_num)

/-- Every vertex with F at most 7 lies in the cells |x| ≤ 7, |y| ≤ 1. -/
theorem near_box (x y : ℤ) (s : Fin 8) (hF : F (x, y, s) ≤ 7) :
    -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1 :=
  cls (fun s => F (x, y, s) ≤ 7 → -7 ≤ x ∧ x ≤ 7 ∧ -1 ≤ y ∧ y ≤ 1)
    (near_box0 x y) (near_box1 x y) (near_box2 x y) (near_box3 x y) (near_box4 x y) (near_box5 x y) (near_box6 x y) (near_box7 x y) s hF

theorem F_nonneg (v : V) : 0 ≤ F v :=
  cls (fun s => 0 ≤ F (v.1, v.2.1, s)) (F_nonneg0 v.1 v.2.1) (F_nonneg1 v.1 v.2.1) (F_nonneg2 v.1 v.2.1) (F_nonneg3 v.1 v.2.1) (F_nonneg4 v.1 v.2.1) (F_nonneg5 v.1 v.2.1) (F_nonneg6 v.1 v.2.1) (F_nonneg7 v.1 v.2.1) v.2.2

/-- For the cell (a - 7, b - 1) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 604059707155338686316438977939116466173980588843387486160138014123413353637902130091888766861366877025890790240506231552474559371320225343046640832252413850567686618260493118172691575851249753174497384499605677943793472944162115298658493434610267336863135978876946047690328316447431042074949619945890947919337394052241375969140500738224771265711738031845792292278518335834799361475637317428586740686386831671560471636003507694825990480070773289679126472478934041072748464032725786006460705026456733843209241492648558611717542136770691689404527275589707406264487677237230824640370186869994447495969200310942570746228795678788681728 >>> (6 * ((a * 3 + b) * 8 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 7, b - 1) and class s, potential i plus
18 + 1 a + 8 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 6) : ℕ :=
  tgetN 1116192 5 i.val * a + tgetN 487032833 5 i.val * b + tgetN 140849732878669362211697181135535608632802961638840513489167076195964302869702262212580 6 (s * 6 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)

theorem fnt_tab : ∀ s : Fin 8, ∀ i : Fin 6, (tgetN 1116192 5 i.val : ℤ) = Ac i + 1 ∧
    (tgetN 487032833 5 i.val : ℤ) = Bc i + 8 ∧
    (tgetN 140849732878669362211697181135535608632802961638840513489167076195964302869702262212580 6 (s.val * 6 + i.val) : ℤ) = Cc s i - Ac i * 7 - Bc i * 1 + 18 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 8) (i : Fin 6) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 7, (b : ℤ) - 1, s) i + (18 + 1 * a + 8 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 8) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 7, (b : ℤ) - 1, s) + (18 + 1 * a + 8 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 7, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (1 + 8) 1 = FN + 1 dx' + 8 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 15).all fun a => (List.range 3).all fun b => (List.range 8).all fun s =>
    Nat.blt (25 + 1 * a + 8 * b) (FN a b s) || (a == 7 && b == 1 && s == 4) ||
      (Nat.blt (hint a b s) 38 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 9 ==
          FN a b s + 1 * dxv (hint a b s) + 8 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 7) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 7).toNat (by omega) (y + 1).toNat (by omega) s.val s.isLt
  have ex : (((x + 7).toNat : ℕ) : ℤ) - 7 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  generalize (x + 7).toNat = a at h' ex
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
    have hs0 : s = 4 := Fin.ext (by rw [h3]; rfl)
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
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 7 = x + dx := by omega
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 1 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 7
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
from below, and for n ≥ 6 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 8 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T (a table entry plus its offset). -/
def ctabN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

def gcV (k : ℕ) : ℕ := ctabN 1577345 4 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 6) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 420 2 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 1

def Ap (i : Fin 6) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 14213472 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 7

def Bp (i : Fin 6) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 420 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 6) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 1617 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 6) : ℤ := beN i.val

theorem prim : ∀ i : Fin 6, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 6) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 6) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 6, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 8) (i : Fin 6) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 8) (i j : Fin 6) (c u : ℤ) :
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

theorem par_inj (s : Fin 8) (i : Fin 6) (c : ℤ) : Function.Injective (par s i c) := by
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

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (6 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 70906338369885198733053227312746603217152 4 k

def cf1N (k : ℕ) : ℤ := (cf1V k : ℤ)

def cf1 (i : Fin 6) (j : Fin 6) : ℤ := cf1N (j.val + 6 * i.val)

def cf2V (k : ℕ) : ℕ := ctabN 5614659176588140829149550993497745919232 4 k

def cf2N (k : ℕ) : ℤ := (cf2V k : ℤ)

def cf2 (i : Fin 6) (j : Fin 6) : ℤ := cf2N (j.val + 6 * i.val)

def cf3V (k : ℕ) : ℕ := ctabN 38600781039624497772553341552202890024704 4 k

def cf3N (k : ℕ) : ℤ := (cf3V k : ℤ)

def cf3 (i : Fin 6) (j : Fin 6) : ℤ := cf3N (j.val + 6 * i.val)

def cf0V (k : ℕ) : ℕ := ctabN 115299399442094621072 2 k

def cf0N (k : ℕ) : ℤ := (cf0V k : ℤ)

def cf0 (i : Fin 6) (j : Fin 6) : ℤ := cf0N (j.val + 6 * i.val)


/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 6) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The class constants Cc s i, packed for the kernel. -/
def cTV (k : ℕ) : ℕ := ctabN 1649584136716322911841023374948863815391184106978984073385 4 k

def cTN (k : ℕ) : ℤ := (cTV k : ℤ) - 5

def cT (s : Fin 8) (i : Fin 6) : ℤ := cTN (i.val + 6 * s.val)

theorem cT_eq : ∀ s : Fin 8, ∀ i : Fin 6, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 8) (i j : Fin 6) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (6 - cT s i)

instance (i j : Fin 6) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 6, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 6 || j == (i + 5) % 6

/-- certC in natural numbers, for the kernel: Cc = cTV - 5, the negative terms moved across; the
previous facet of i is (i + 5) % 6, the next one (i + 1) % 6. -/
def certNat (s i j : ℕ) : Bool :=
  Nat.blt ((cf1V (j + 6 * i) + cf2V (j + 6 * i) + cf0V (j + 6 * i)) * cTV (i + 6 * s) +
      cf3V (j + 6 * i) * cTV (j + 6 * s))
    (cf1V (j + 6 * i) * (cTV ((i + 5) % 6 + 6 * s) + (if (i + 5) % 6 < i then 1 else 0)) +
      cf2V (j + 6 * i) * (cTV ((i + 1) % 6 + 6 * s) + (if (i + 1) % 6 < i then 1 else 0)) +
      cf3V (j + 6 * i) * cTV (i + 6 * s) + cf0V (j + 6 * i) * 11)

def certOK : Bool :=
  (List.range 8).all fun s => (List.range 6).all fun i => (List.range 6).all fun j =>
    nearB i j || certNat s i j

theorem certOK_eq : certOK = true := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 6, (i - 1).val = (i.val + 5) % 6 := by decide +kernel

theorem fin_next : ∀ i : Fin 6, (i + 1).val = (i.val + 1) % 6 := by decide +kernel

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 8) (i j : Fin 6) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  have hn : nearB i.val j.val = false := by
    have n1 : j.val ≠ i.val := fun h => e2 (Fin.ext h)
    have n2 : j.val ≠ (i.val + 1) % 6 := fun h => e3 (Fin.ext (h.trans a2.symm))
    have n3 : j.val ≠ (i.val + 5) % 6 := fun h => e1 (Fin.ext (h.trans a1.symm))
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
    cf3 i j * (cT s i - cT s j) + cf0 i j * (6 - cT s i)
  simp only [cf1, cf2, cf3, cf0, cf1N, cf2N, cf3N, cf0N, cT, cTN, Fin.lt_def, a1, a2]
  push_cast at ck ⊢
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
def lev (s : Fin 8) (i : Fin 6) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 8) (i : Fin 6) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 8) (i j : Fin 6) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 8) (i : Fin 6) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 8) (i : Fin 6) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 8) (i j : Fin 6) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 8) (i : Fin 6) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 8) (i : Fin 6) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 8) (i : Fin 6) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 6 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 8) (i : Fin 6) (n u : ℤ) (hn : 6 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 6 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ
    (Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 8, ∀ j : Fin 6, -5 ≤ Cc s j ∧ Cc s j ≤ 5 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 7 * Ac 2 + 6 * Ac 3 = 13 ∧ 7 * Bc 2 + 6 * Bc 3 = 0 ∧
    6 * Ac 0 + 7 * Ac 5 = (-13) ∧ 6 * Bc 0 + 7 * Bc 5 = 0 ∧
    1 * Ac 4 + 0 * Ac 4 = 0 ∧ 1 * Bc 4 + 0 * Bc 4 = 8 ∧
    1 * Ac 1 + 0 * Ac 1 = 0 ∧ 1 * Bc 1 + 0 * Bc 1 = (-8) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 8) :
    13 * x ≤ 13 * F (x, y, s) + 65 ∧
    13 * (-x) ≤ 13 * F (x, y, s) + 65 ∧
    8 * y ≤ 1 * F (x, y, s) + 5 ∧
    8 * (-y) ≤ 1 * F (x, y, s) + 5 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 7 * pot (x, y, s) 2 + 6 * pot (x, y, s) 3 =
      13 * x + 7 * Cc s 2 + 6 * Cc s 3 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 2
  have r0 := le_F (x, y, s) 3
  have k0 := Cbound s 2
  have l0 := Cbound s 3
  have e1 : 6 * pot (x, y, s) 0 + 7 * pot (x, y, s) 5 =
      13 * (-x) + 6 * Cc s 0 + 7 * Cc s 5 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 5
  have k1 := Cbound s 0
  have l1 := Cbound s 5
  have e2 : 1 * pot (x, y, s) 4 + 0 * pot (x, y, s) 4 =
      8 * y + 1 * Cc s 4 + 0 * Cc s 4 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 4
  have r2 := le_F (x, y, s) 4
  have k2 := Cbound s 4
  have l2 := Cbound s 4
  have e3 : 1 * pot (x, y, s) 1 + 0 * pot (x, y, s) 1 =
      8 * (-y) + 1 * Cc s 1 + 0 * Cc s 1 := by
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
noncomputable def PF (s : Fin 8) (i : Fin 6) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 8) (i : Fin 6) (n : ℤ) (hn : 6 ≤ n) :
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
def inner (s : Fin 8) (i : Fin 6) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 8) (i : Fin 6) (n : ℤ) (hn : 6 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 8 × Fin 6, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 8 × Fin 6, inner p.1 p.2 n

/-! Shifting n by 8 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 8488984 4 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 6) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 54 1 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ)

def mh (i : Fin 6) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 585 2 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ)

def mk (i : Fin 6) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 6, (8 : ℤ) = gc i * Lq i ∧
    8 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    8 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 8) (i : Fin 6) (n : ℤ) :
    inner s i (n + 8) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 8 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 8 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 8) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 8) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 8) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 8 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 8 × Fin 6, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 8) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqV (k : ℕ) : ℕ := ctabN 8488984 4 k

def lgqN (k : ℕ) : ℤ := (lgqV k : ℤ)

def lgq (i : Fin 6) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 6, (8 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 8 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 8 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 6, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 6 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 6) = 0 then mhN (c % 6) + mkN (c % 6) else 0

theorem gsN_eq (s : Fin 8) (i : Fin 6) (n : ℤ) :
    gsN (i.val + 6 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 6 * s.val) % 6 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (8 * 6)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhV (k : ℕ) : ℕ := ctabN 54 1 k

def uhN (k : ℕ) : ℤ := (uhV k : ℤ)

def uh (i : Fin 6) : ℤ := uhN i.val

def dhV (k : ℕ) : ℕ := ctabN 8509469 4 k

def dhN (k : ℕ) : ℤ := (dhV k : ℤ)

def dh (i : Fin 6) : ℤ := dhN i.val

def ukV (k : ℕ) : ℕ := ctabN 585 2 k

def ukN (k : ℕ) : ℤ := (ukV k : ℤ)

def uk (i : Fin 6) : ℤ := ukN i.val

def dkV (k : ℕ) : ℕ := ctabN 13733144 4 k

def dkN (k : ℕ) : ℤ := (dkV k : ℤ)

def dk (i : Fin 6) : ℤ := dkN i.val

def vhV (k : ℕ) : ℕ := ctabN 3293959408126749557566310210066835049293228135798522905999 4 k

def vhN (k : ℕ) : ℤ := (vhV k : ℤ) - 8

def vh (s : Fin 8) (i : Fin 6) : ℤ := vhN (i.val + 6 * s.val)

def vkV (k : ℕ) : ℕ := ctabN 2148040711146106848792072750729213219959797996401988116391 4 k

def vkN (k : ℕ) : ℤ := (vkV k : ℤ) - 8

def vk (s : Fin 8) (i : Fin 6) : ℤ := vkN (i.val + 6 * s.val)

def levT (s : Fin 8) (i : Fin 6) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 8) (i : Fin 6) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_facet : ∀ i : Fin 6, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧
    uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) := by
  decide +kernel

theorem tab_class : ∀ s : Fin 8, ∀ i : Fin 6,
    vh s i = cT s i - cT s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    vk s i = cT s i - cT s (i + 1) - (if i + 1 < i then 1 else 0) := by
  decide +kernel

theorem tab_ok (s : Fin 8) (i : Fin 6) : uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  obtain ⟨f1, f2, f3, f4⟩ := tab_facet i
  obtain ⟨c1, c2⟩ := tab_class s i
  simp only [cT_eq] at c1 c2
  exact ⟨f1, c1, f2, f3, c2, f4⟩

theorem inner_eq (s : Fin 8) (i : Fin 6) (n : ℤ) : inner s i n = innerT s i n := by
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
def ST (n : ℤ) : ℤ := ∑ p : Fin 8 × Fin 6, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 6 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 6) = 0 then
    (uhN (c % 6) * ((n - cTN c) / gcN (c % 6)) + vhN c) / dhN (c % 6) +
      (ukN (c % 6) * ((n - cTN c) / gcN (c % 6)) + vkN c) / dkN (c % 6) + 1
  else 0

theorem innerN_eq (s : Fin 8) (i : Fin 6) (n : ℤ) :
    innerN (i.val + 6 * s.val) n = innerT s i n := by
  have hi := i.isLt
  have h : (i.val + 6 * s.val) % 6 = i.val := by omega
  rw [innerN, h]
  rfl

theorem sum_range_list (f : ℕ → ℤ) (N : ℕ) :
    ∑ c ∈ Finset.range N, f c = ((List.range N).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The closed form over the indices of the pieces. -/
def STN (n : ℤ) : ℤ := ((List.range (8 * 6)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 8 × Fin 6 => innerT q.1 q.2 n)
    (fun c : Fin (8 * 6) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (8 * 6), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 8 × Fin 6 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (8 * 6) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (8 * 6), sum_range_list]

/-- The closed form's tables, packed: the steps, the values on one period from 1 and below 1. -/
def dtabV (k : ℕ) : ℕ := ctabN 169778557381030 6 k

def tblV (k : ℕ) : ℕ := ctabN 169423965844101 6 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 8. -/
def dv (t : ℕ) : ℕ := dtabV (t % 8)

/-- The sequence in closed form: b(n + 8) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 8) + tblV ((n - 1) % 8)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 8) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 8 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 8 - 1 = n - 1 + 8 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 8)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 8) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 8 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 8 - 1 = n - 1 + 8 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 8)]
  ring

/-- b on the residue class of 1 + j mod 8. -/
theorem b_res (k j : ℕ) (hj : j < 8) : b (8 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (8 * k + (1 + j) < 1) by omega),
    show 8 * k + (1 + j) - 1 = j + 8 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 8), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The growth of S over one period at each residue mod 8. -/
def GsT : List ℤ := [38, 38, 38, 38, 38, 38, 38, 38]

theorem Gs_tab : ∀ r : ℕ, r < 8 → GsN (r : ℤ) = GsT.getD r 0 := by
  decide +kernel

/-- The growth of b over 8 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 8 → 1 * (dv t : ℤ) = GsT.getD ((1 + t) % 8) 0 := by
  decide +kernel

theorem grow (n : ℕ) (_hn : 1 ≤ n) : 1 * (dv (n - 1) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 1) % 8) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 1) % 8) = dv (n - 1) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 8 ∣ 8)]
  have e2 : (1 + (n - 1) % 8) % 8 = n % 8 := by omega
  rw [e1, e2, ← Gs_tab (n % 8) (Nat.mod_lt _ (by norm_num)), ← Gs_eq_GsN] at h1
  rw [h1]
  have e3 : (((n % 8 : ℕ) : ℤ) + 8 * ((n / 8 : ℕ) : ℤ)) = n := by omega
  rw [← e3, Gs_periodic]

/-- One kernel pass over n = 6, ..., 13: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 8 →
    ((List.range (8 * 6)).all fun c => decide (0 ≤ innerN c (6 + (r : ℤ)))) = true ∧
      STN (6 + (r : ℤ)) = b (6 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 6 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 8) (i : Fin 6) (n : ℤ) (hn : 6 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 6 + t := ⟨(n - 6).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 8
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 6 * s.val < 8 * 6 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 8) (by omega) (by omega)
      have e : (6 : ℤ) + t = (6 + (t - 8 : ℕ)) + 8 := by
        push_cast [Nat.cast_sub (by omega : 8 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 6 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 6 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 14
    · obtain ⟨r, rfl⟩ : ∃ r, n = 6 + r := ⟨n - 6, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 8) (by omega) (by omega)
      have h2 := S_shift ((n - 8 : ℕ) : ℤ)
      have h3 := b_shift (n - 8) (by omega)
      have h4 := grow (n - 8) (by omega)
      rw [show n - 8 + 8 = n by omega] at h3
      rw [show ((n - 8 : ℕ) : ℤ) + 8 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 5 lie in the box -10 ≤ x ≤ 10, -1 ≤ y ≤ 1 (`small_box`), and
the kernel checks that those of the box are the 73 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 8) (h : F (x, y, s) ≤ 5) :
    -10 ≤ x ∧ x ≤ 10 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 5, with their values of F. -/
def smallV : List (V × ℤ) :=
  [((0, 0, 4), 0), (((-1), 0, 4), 1), (((-1), 0, 6), 1), ((0, 0, 2), 1), ((0, 0, 6), 1), ((1, 0, 4), 1), (((-2), 0, 4), 2), (((-2), 0, 6), 2), (((-1), 0, 2), 2), (((-1), 0, 7), 2), ((0, 0, 1), 2), ((0, 0, 7), 2), ((1, 0, 2), 2), ((1, 0, 6), 2), ((1, 0, 7), 2), ((2, 0, 4), 2), (((-3), 0, 4), 3), (((-3), 0, 6), 3), (((-2), 0, 2), 3), (((-2), 0, 5), 3), (((-2), 0, 7), 3), (((-1), 0, 1), 3), (((-1), 0, 5), 3), ((0, 0, 5), 3), ((0, 1, 0), 3), ((1, 0, 1), 3), ((1, 0, 5), 3), ((2, 0, 2), 3), ((2, 0, 6), 3), ((2, 0, 7), 3), ((3, 0, 4), 3), (((-4), 0, 4), 4), (((-4), 0, 6), 4), (((-3), 0, 2), 4), (((-3), 0, 5), 4), (((-3), 0, 7), 4), (((-2), 0, 1), 4), (((-2), 0, 3), 4), (((-1), 0, 3), 4), (((-1), 1, 0), 4), (((-1), 1, 3), 4), ((0, 0, 3), 4), ((1, 0, 3), 4), ((1, 1, 0), 4), ((2, 0, 1), 4), ((2, 0, 5), 4), ((3, 0, 2), 4), ((3, 0, 6), 4), ((3, 0, 7), 4), ((4, 0, 4), 4), (((-5), 0, 4), 5), (((-5), 0, 6), 5), (((-4), 0, 2), 5), (((-4), 0, 5), 5), (((-4), 0, 7), 5), (((-3), 0, 1), 5), (((-3), 0, 3), 5), (((-2), 1, 0), 5), (((-2), 1, 3), 5), (((-1), 0, 0), 5), (((-1), 1, 5), 5), ((0, 0, 0), 5), ((0, 1, 3), 5), ((1, 0, 0), 5), ((2, 0, 0), 5), ((2, 0, 3), 5), ((2, 1, 0), 5), ((3, 0, 1), 5), ((3, 0, 5), 5), ((4, 0, 2), 5), ((4, 0, 6), 5), ((4, 0, 7), 5), ((5, 0, 4), 5)]

def smallL : List V := smallV.map Prod.fst

theorem smallV_ok : (smallV.all fun q => decide (F q.1 = q.2)) = true := by
  decide +kernel

/-- The potentials, packed: Ac = ATV - 1, Bc = BTV - 8. -/
def ATV (k : ℕ) : ℕ := ctabN 420 2 k

def ATN (k : ℕ) : ℤ := (ATV k : ℤ) - 1

def AT (i : Fin 6) : ℤ := ATN i.val

def BTV (k : ℕ) : ℕ := ctabN 487032833 5 k

def BTN (k : ℕ) : ℤ := (BTV k : ℤ) - 8

def BT (i : Fin 6) : ℤ := BTN i.val

theorem AB_eq : ∀ i : Fin 6, AT i = Ac i ∧ BT i = Bc i := by
  decide +kernel

/-- Some potential exceeds 5 at the box point ((a : ℤ) - 10, (b : ℤ) - 1, s), in natural
numbers: the negative terms moved across. -/
def bigNat (a b s : ℕ) : Bool :=
  (List.range 6).any fun i =>
    Nat.blt (10 + ATV i * 10 + 1 * a + BTV i * 1 + 8 * b)
      (ATV i * a + 10 + BTV i * b + 8 + cTV (i + 6 * s))

theorem big_pot (a b : ℕ) (s : Fin 8) (h : bigNat a b s.val = true) :
    (5 : ℤ) < F ((a : ℤ) - 10, (b : ℤ) - 1, s) := by
  obtain ⟨i, hi, hb⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hi
  have hl := (Nat.cast_lt (α := ℤ)).mpr (Nat.blt_eq.mp hb)
  have hp := le_F ((a : ℤ) - 10, (b : ℤ) - 1, s) ⟨i, hi⟩
  obtain ⟨eA, eB⟩ := AB_eq ⟨i, hi⟩
  have e3 := cT_eq s ⟨i, hi⟩
  simp only [pot] at hp
  rw [← eA, ← eB, ← e3] at hp
  simp only [AT, BT, ATN, BTN, cT, cTN] at hp
  push_cast at hl hp
  ring_nf at hl hp ⊢
  linarith

def smallOK : Bool :=
  (List.range 21).all fun a => (List.range 3).all fun b => (List.finRange 8).all fun s =>
    bigNat a b s.val || decide (((a : ℤ) - 10, (b : ℤ) - 1, s) ∈ smallL)

theorem smallOK_eq : smallOK = true := by
  decide +kernel

theorem small_mem (v : V) (hF : F v ≤ 5) : v ∈ smallL := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s hF
  have h := smallOK_eq
  unfold smallOK at h
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, forall_const] at h
  have h' := h (x + 10).toNat (by omega) (y + 1).toNat (by omega) s
  have ex : (((x + 10).toNat : ℕ) : ℤ) - 10 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h1 | h1
  · have := big_pot _ _ s h1
    rw [ex, ey] at this
    omega
  · rw [ex, ey] at h1
    exact h1

theorem cnt_small (n : ℤ) (hn : n ≤ 5) :
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

/-- The small spheres in closed form. -/
theorem small_ok : ∀ n : ℕ, n < 6 →
    (((smallV.filter (fun q => decide (q.2 = (n : ℤ)))).map Prod.fst).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 6 are counted in
`smallL`, those from 6 on are S(n), and both agree with the closed form b (`a_eq_b`). The step
from n to n + 8, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f.
follow, their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 6 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 6 ∨ 6 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_ok n h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

theorem dconst_base : ∀ r : ℕ, r < 8 → dtabV r = 38 := by
  decide +kernel
theorem dv_const : ∀ t : ℕ, dv t = 38 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 8) = a(n) + 38 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 8) = a n + 38 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-- The steps and the values on one period, by the kernel. -/
theorem closed_vals : dv 0 = 38 ∧ tblV 0 = 5 ∧ dv 1 = 38 ∧ tblV 1 = 10 ∧ dv 2 = 38 ∧ tblV 2 = 15 ∧ dv 3 = 38 ∧ tblV 3 = 19 ∧ dv 4 = 38 ∧ tblV 4 = 23 ∧ dv 5 = 38 ∧ tblV 5 = 28 ∧ dv 6 = 38 ∧ tblV 6 = 33 ∧ dv 7 = 38 ∧ tblV 7 = 38 := by
  decide +kernel

/-- The closed form per residue of n mod 8, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (8 * k + 1) = 38 * k + 5 ∧
    a (8 * k + 2) = 38 * k + 10 ∧
    a (8 * k + 3) = 38 * k + 15 ∧
    a (8 * k + 4) = 38 * k + 19 ∧
    a (8 * k + 5) = 38 * k + 23 ∧
    a (8 * k + 6) = 38 * k + 28 ∧
    a (8 * k + 7) = 38 * k + 33 ∧
    a (8 * k + 8) = 38 * k + 38 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closed_vals
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 8 * k + 1 = 8 * k + (1 + 0) from rfl, b_res k 0 (by norm_num), c0, c1]
  · rw [show 8 * k + 2 = 8 * k + (1 + 1) from rfl, b_res k 1 (by norm_num), c2, c3]
  · rw [show 8 * k + 3 = 8 * k + (1 + 2) from rfl, b_res k 2 (by norm_num), c4, c5]
  · rw [show 8 * k + 4 = 8 * k + (1 + 3) from rfl, b_res k 3 (by norm_num), c6, c7]
  · rw [show 8 * k + 5 = 8 * k + (1 + 4) from rfl, b_res k 4 (by norm_num), c8, c9]
  · rw [show 8 * k + 6 = 8 * k + (1 + 5) from rfl, b_res k 5 (by norm_num), c10, c11]
  · rw [show 8 * k + 7 = 8 * k + (1 + 6) from rfl, b_res k 6 (by norm_num), c12, c13]
  · rw [show 8 * k + 8 = 8 * k + (1 + 7) from rfl, b_res k 7 (by norm_num), c14, c15]

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 15, 19, 23, 28, 33, 38, 43, 48, 53, 57, 61, 66, 71, 76, 81, 86, 91, 95, 99, 104, 109, 114, 119, 124, 129, 133, 137, 142, 147, 152, 157, 162, 167, 171, 175, 180, 185, 190, 195, 200, 205, 209, 213, 218, 223, 228, 233] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 8 → (dv (t + 8) : ℤ) = 2 * (dv (t + 7) : ℤ) - 2 * (dv (t + 6) : ℤ) + 2 * (dv (t + 5) : ℤ) - 2 * (dv (t + 4) : ℤ) + 2 * (dv (t + 3) : ℤ) - 2 * (dv (t + 2) : ℤ) + 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 8) : ℤ) = 2 * (dv (t + 7) : ℤ) - 2 * (dv (t + 6) : ℤ) + 2 * (dv (t + 5) : ℤ) - 2 * (dv (t + 4) : ℤ) + 2 * (dv (t + 3) : ℤ) - 2 * (dv (t + 2) : ℤ) + 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 8 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8]
  exact drec_base (t % 8) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 8 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 8 → (b (q + 9) : ℤ) = 2 * b (q + 8) - 2 * b (q + 7) + 2 * b (q + 6) - 2 * b (q + 5) + 2 * b (q + 4) - 2 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 9) : ℤ) = 2 * b (q + 8) - 2 * b (q + 7) + 2 * b (q + 6) - 2 * b (q + 5) + 2 * b (q + 4) - 2 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 8 ∨ 8 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 8 := ⟨q - 8, by omega⟩
      have h0 : (b (v + 9) : ℤ) = 2 * b (v + 8) - 2 * b (v + 7) + 2 * b (v + 6) - 2 * b (v + 5) + 2 * b (v + 4) - 2 * b (v + 3) + 2 * b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have s1 : b (v + 9) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (by omega)
        rw [show v + 1 + 8 = v + 9 by omega,
          show v + 1 - 1 = v + 0 by omega] at h
        exact h
      have s2 : b (v + 10) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (by omega)
        rw [show v + 2 + 8 = v + 10 by omega,
          show v + 2 - 1 = v + 1 by omega] at h
        exact h
      have s3 : b (v + 11) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (by omega)
        rw [show v + 3 + 8 = v + 11 by omega,
          show v + 3 - 1 = v + 2 by omega] at h
        exact h
      have s4 : b (v + 12) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (by omega)
        rw [show v + 4 + 8 = v + 12 by omega,
          show v + 4 - 1 = v + 3 by omega] at h
        exact h
      have s5 : b (v + 13) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (by omega)
        rw [show v + 5 + 8 = v + 13 by omega,
          show v + 5 - 1 = v + 4 by omega] at h
        exact h
      have s6 : b (v + 14) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (by omega)
        rw [show v + 6 + 8 = v + 14 by omega,
          show v + 6 - 1 = v + 5 by omega] at h
        exact h
      have s7 : b (v + 15) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (by omega)
        rw [show v + 7 + 8 = v + 15 by omega,
          show v + 7 - 1 = v + 6 by omega] at h
        exact h
      have s8 : b (v + 16) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (by omega)
        rw [show v + 8 + 8 = v + 16 by omega,
          show v + 8 - 1 = v + 7 by omega] at h
        exact h
      have s9 : b (v + 17) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (by omega)
        rw [show v + 9 + 8 = v + 17 by omega,
          show v + 9 - 1 = v + 8 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 17) : ℤ) = 2 * b (v + 16) - 2 * b (v + 15) + 2 * b (v + 14) - 2 * b (v + 13) + 2 * b (v + 12) - 2 * b (v + 11) + 2 * b (v + 10) - b (v + 9)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - a (n - 8) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
  rw [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega]
  simp only [a_eq_b]
  exact b_recur q

/-- The coefficients of the g.f. below 9, by the kernel. -/
theorem gf_base : ∀ n : ℕ, n < 9 → 1 * (b n : ℤ) - 2 * (if 1 ≤ n then (b (n - 1) : ℤ) else 0) + 2 * (if 2 ≤ n then (b (n - 2) : ℤ) else 0) - 2 * (if 3 ≤ n then (b (n - 3) : ℤ) else 0) + 2 * (if 4 ≤ n then (b (n - 4) : ℤ) else 0) - 2 * (if 5 ≤ n then (b (n - 5) : ℤ) else 0) + 2 * (if 6 ≤ n then (b (n - 6) : ℤ) else 0) - 2 * (if 7 ≤ n then (b (n - 7) : ℤ) else 0) + 1 * (if 8 ≤ n then (b (n - 8) : ℤ) else 0) = (if n = 0 then (1 : ℤ) else 0) + (if n = 1 then (1 : ℤ) else 0) * 3 + (if n = 2 then (1 : ℤ) else 0) * 2 + (if n = 3 then (1 : ℤ) else 0) * 3 + (if n = 4 then (1 : ℤ) else 0) * 1 + (if n = 5 then (1 : ℤ) else 0) * 3 + (if n = 6 then (1 : ℤ) else 0) * 2 + (if n = 7 then (1 : ℤ) else 0) * 3 + (if n = 8 then (1 : ℤ) else 0) * 1 := by
  decide +kernel

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1)) =
      X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + 3 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + 3 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1)) = C 1 * A - C 2 * (A * X ^ 1) + C 2 * (A * X ^ 2) - C 2 * (A * X ^ 3) + C 2 * (A * X ^ 4) - C 2 * (A * X ^ 5) + C 2 * (A * X ^ 6) - C 2 * (A * X ^ 7) + C 1 * (A * X ^ 8) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : (X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + 3 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + 3 * X + 1 : ℚ⟦X⟧) = C 1 + X ^ 1 * C 3 + X ^ 2 * C 2 + X ^ 3 * C 3 + X ^ 4 * C 1 + X ^ 5 * C 3 + X ^ 6 * C 2 + X ^ 7 * C 3 + X ^ 8 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · have h := congrArg (fun z : ℤ => (z : ℚ)) (gf_base n hn)
    push_cast at h
    linarith
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have h : (b (q + 9) : ℤ) = 2 * b (q + 8) - 2 * b (q + 7) + 2 * b (q + 6) - 2 * b (q + 5) + 2 * b (q + 4) - 2 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega, show 1 ≤ q + 9 by omega, show 2 ≤ q + 9 by omega, show 3 ≤ q + 9 by omega, show 4 ≤ q + 9 by omega, show 5 ≤ q + 9 by omega, show 6 ≤ q + 9 by omega, show 7 ≤ q + 9 by omega, show 8 ≤ q + 9 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega, show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 4 by omega, show ¬ q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1)) =
      X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + 3 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + 3 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - a (n - 8) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 15, 19, 23, 28, 33, 38, 43, 48, 53, 57, 61, 66, 71, 76, 81, 86, 91, 95, 99, 104, 109, 114, 119, 124, 129, 133, 137, 142, 147, 152, 157, 162, 167, 171, 175, 180, 185, 190, 195, 200, 205, 209, 213, 218, 223, 228, 233] := Count.controls

/-- The step a(n + 8) = a(n) + 38 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 8) = a n + 38 := Count.a_step n hn

/-- The closed form per residue of n mod 8, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (8 * k + 1) = 38 * k + 5 ∧
    a (8 * k + 2) = 38 * k + 10 ∧
    a (8 * k + 3) = 38 * k + 15 ∧
    a (8 * k + 4) = 38 * k + 19 ∧
    a (8 * k + 5) = 38 * k + 23 ∧
    a (8 * k + 6) = 38 * k + 28 ∧
    a (8 * k + 7) = 38 * k + 33 ∧
    a (8 * k + 8) = 38 * k + 38 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1)) =
      X ^ 8 + 3 * X ^ 7 + 2 * X ^ 6 + 3 * X ^ 5 + X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) - 2 * a (n - 4) + 2 * a (n - 5) - 2 * a (n - 6) + 2 * a (n - 7) - a (n - 8) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a313685

theorem OMA.solution : type_of% @OMA.S_oeis_a313685.main :=
  OMA.S_oeis_a313685.conjecture
