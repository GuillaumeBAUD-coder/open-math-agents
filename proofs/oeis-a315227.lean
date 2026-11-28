import OMAStatements.S_oeis_a315227

namespace OMA.S_oeis_a315227






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 12

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 4349163
  | 1 => 3374553
  | 2 => 5532618
  | 3 => 4488393
  | 4 => 3304938
  | 5 => 6650553
  | 6 => 5606328
  | 7 => 8947848
  | 8 => 7903623
  | 9 => 6720168
  | 10 => 7834008
  | 11 => 6789783
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 6) : ℤ := tget 6859398 4 8 i.val

def Bc (i : Fin 6) : ℤ := tget 14660373 4 8 i.val

def Cc (s : Fin 12) (i : Fin 6) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 6859398 4 i

def BcN (i : ℕ) : ℕ := tgetN 14660373 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 6) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 6) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 12) (i : Fin 6) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


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
theorem cls (P : Fin 12 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 12 × Fin 12 × ℤ × ℤ) (j : Fin 6) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 6, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 12 × Fin 12 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 12 × Fin 12 × ℤ × ℤ) (j : Fin 6) :
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
theorem farkas (x y : ℤ) (s : Fin 12) (a1 b1 a2 b2 a3 b3 i0 : Fin 6) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
pot k2 ≤ pot i, 2 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 5047407301450220463292548339460771763156510379595267701041373116892003334605795434636884120624286959784299801602345355162677481100693607828042880386567418394520599502311822440707790824874479852912418142359567485171400735715402502131022990708689305363466879121117712816563492038977230690671285461447908261888 5 ((i * 6 + j) * 6 + f)

def fd (i j : Fin 6) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 6) : Fin 6 := ⟨fdN i.val j.val 0 % 6, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 6) : Fin 6 := ⟨fdN i.val j.val 1 % 6, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 6) : ℤ := fd i j 2

def fm2 (i j : Fin 6) : ℤ := fd i j 3

def fm0 (i j : Fin 6) : ℤ := fd i j 4

def fmj (i j : Fin 6) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 6 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 19770625841841587286312964107108736770661838708656281551753014411264 4 p

def dstv (p : ℕ) : ℕ := tgetN 17965817574804236160627125168195969304250791476731453375090965115969 4 p

def dxv (p : ℕ) : ℕ := tgetN 3033593524201926831907433066096720 2 p

def dyv (p : ℕ) : ℕ := tgetN 1730765619535226806526539145237525 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 180892485276778552324637808172972781342337872594163328598538118813842347668680452393744794125467462867672235512307528833547291205406527947055759359764356340064057278016359000635942462181061690387786461106447129878451466689067815891348179337086154113987567663872153180356603841976225410046406697414950712265111674417604546176403341708613424815503119306116052318703049368589881601543708514928628658821760888 4 (p * 6 + j)

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

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 8). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 6) + fdN i j 3 * AcN (fdN i j 1 % 6) + fdN i j 5 * AcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 6) + fdN i j 3 * BcN (fdN i j 1 % 6) + fdN i j 5 * BcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * BcN i + fdN i j 5 * BcN j)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farCN (s i j : ℕ) : Bool :=
  Nat.blt ((fdN i j 2 + fdN i j 3 + fdN i j 4) * CcN s i + fdN i j 5 * (CcN s j + 1))
    (fdN i j 2 * CcN s (fdN i j 0 % 6) + fdN i j 3 * CcN s (fdN i j 1 % 6) + fdN i j 5 * CcN s i +
      fdN i j 4 * 10)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 6 || j == (i + 5) % 6

def farOK : Bool := (List.range 6).all fun i => (List.range 6).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 12).all fun s => (List.range 6).all fun i => (List.range 6).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 56).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 6).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 12) (i j : Fin 6) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (2 - Cc s i)

/-- Beyond F = 1, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 12) (i j : Fin 6) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 1 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 2 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 1, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 1 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 27441409770871317780137573230977515932439153851709956441359627505539388512081039677601074045737880435229702360356959625349155930312065018870143463539779354653318215452531408947541424956255425399797246245614210515695911399860082577858266348104013190251326105974032436029717962708026943085371111184173940601003934694687737244886326368403266332253315181785261106743894279259704837273452624794733770507380630457242982971174335346871421347003731448879390798201006902603998649823725815266930494054329765429234151741402536375693521136585025448583276703819355728875875371624207221562181287873623508780960201598169158300172609953928513625062471962181879497867343991024272787318273594933649473
  | 1 => 27441409775625781879186971979808903133319583665102238518020703193348380427171212894552070715629402564025847215874939338587496033508523042357100580658205177586743970517745145923353246471335128653689355569940757499995339655595163113153472721580854543301245879786916861706405506001713830518696331332550484501180024658917609838608390423090298268272840394870825871283264363068728450171518856568978858722942264906250760007374052042301587244908148375914212043970909218915126922552936289884032586590288136360378857189404241358645420239305850134528103731949280185091808910553167165449455258017051604920759462596241735738047695316046024387661754989843402745805479512784658894475741292951511105
  | 2 => 27441409785134710077285769521459306070576850263570802642215078548991137383735465790291046331378209329404643811002611635839261784856585981443571397694915364444731794648436040288206136706646389257892092914715169439061067633197049468123936848635809503133031327336481449853674884174151761500315887579371387325006852682996267078883013024085653410741670813457006966281551919808906083805032202906305923069713848436044601417095070296680492690630808985425797863992574241520293595348113647439511350956946634746668975738008493704642836236492547231103994350376516720906477998296164584419567868631909616356253095319425198893662563351679569458961905559454759054147632298601073911634887249054933057
  | 3 => 27441409788304352809985368643359269220822981268157562163390125550402178304263962961282815395072084980787598114400036846275361876836375990154462587535263788712453498259283097588102126041877042660054805739314067988455615084358632416682373771325182168536653548688468117284382616662242413263415516038234771748163640907384154479451831133821656948114949117873206110336478905347550477546201509001809571120498570710758869553342137617097387240032126191064774335262875103333294011441493146708428973338912761442532313120935321472614363293397422709700706709124889858662047528117677909646184916116906765112829378573842401110360529503136361510203122991754731420254475768808877051946645779358425153
  | 4 => 27441409796228459641734366558078248271312637633327532312803387611819348843907989730282965509866739106837988646364934514478692481558463269932920067745184425776951791087666260345686733318155246168601559738153415253881551215489007751586772011402096319888106851365096779200513878112323632893498975234607411556348513409266302686345908198405171443075882319326935894858161556960379763552088872028713281334402350937138871401807149546762699889549207310038617910469402503408140891670903086190079560747182814257332693380393473613303787735570122824638270598599921893912228934540837973428526634664152206972449562445588901100066201795196962002915220751636851369988071825898809797026450342247931969
  | 5 => 27441409802567745107133564889853431069264303571632060235694858669026155562203975213680320123552926195375626306997920297961482049277366926659431710989705441309960399962142643601900777857299626866860008820896689776189480524960440711423491293378367984325830232144783304606665935320358037492218949766933741366486051366023339583488193494411702616865338544515348075483440714979153773843274873011894868489539581543245160530675271819823758354358905520217515154698177095132499936836766847996260292616426164858096759367760314831370916001327725638176859339497537309241500912851687658726836024055545973197044278740459189234919620313506618359380706070632533641994200969742082104431049201027391553
  | 6 => 27441409808907030572532763221628614113016002373159722058379569847553054496898098050042050456577420181937798194693951401555625023739401249527517384641747443017236757002468666668805098583666025083459397929663942362708907642818007391837269627583797679633296669450920364838677520746969481074699909546671873960902692811009127593437214803265508312343952397483961319174904780673007323658465249931980049437096006216236017213995753310830119680224402145346310293916412679140799330356138620116342808119908077999510797078916943745795003424651727997823938986880324047051636842748949059072987306050593811178336561594910182938255925229195905628977674740212866301671789390378544800990241588616896577
  | 7 => 27441409820000780136981360302235184521514819563549335567166139139122855285817268499216322584326498038687143279140208686480584314086739839261211580326104004604212305105716674168958926854409772153668649883907707919912351026806006642123861565228251317398813729919796098725091595975344520084574629395932540400892696699544948450889580123649454685377121392524296393278992850421246813029929763901025298866473308637599290987461526807967480317972691448772151909605957895091327630946118716527277309659856544051555339130106390913035391470134672725698018153731397867307606469114162901296160674485866347579793456334855962935801504974684548687626779879667203071346641127471111487288668039832412225
  | 8 => 27441409829509708335080157799897959169075712053594292591545663602999385982457438440291768410675532690397257975771083288391710761722226160812302693240393466519831754282248949765297303098059237408820992379939591481862515710174843454521703414564984061819495882481842505766106056992733026765764528285903893729310741623548982147965562109797431809773313209222625967004030722541409419910305587008242248406155567036511805365723058906419532575291112633860734046920831065995041938182159599179841503188350447660475151313587001629123354804230642968694772115596572300976834005658851791132193192510218506433381172214324419183146173529013915305050402492690755275480739254466575393278506458624041025
  | 9 => 27441409835848993800479356131673142048960722279615025833525459389353920343364009514588247254032486800083659549943486127515049731497397325572003478747212768653806931578577550219140435216587017243304917175925751354722483654158749086057910160300643323335667255714073918322397522719426667556540478012206104896635230504887954043079812699958090048411733308760724317711243424808879617903514484813005664139655061142259973732638174081083389144397063940004325337895651914291305943992528352082897513358438883829220922822393859252188283017387099903796205454157132442521793752228750074785251183599750376023923074504703543339735767608596773270225842903903086419971703162850351937220057605759836225
  | 10 => 27441409843773100632228354046392120853650345781524603111881348362512544016546801953429063745091491952433095925929511592714071342388428206725023364547424039686422475391434299595147670502163937652944824634989188826044883509493508618153805918242702208603936748648550597078643919291586398193829104603133947310403461207805334543199488111440289387832442496392361550760072407018317734566529772614910320004878600384285613574715605450746547785962501850369825563332857441111598616323704390031452760810007658627518572788129436611866240418270444290843516597355616782750344371634914594405888947546820550674929599164542024854970763533327215859093240930109997215761032568310406844218769916162220097
  | 11 => 27441409854866850196676951170986315946778388419222653916238762882959287819681111489666092027349707937860934607900222524798594246550693165706361191710114193165250334622190090991484696977268302267804831249246763599059581987171291700199434859152891605236793358918076305934703048128594232563959526064733737789360420607478209983898580891840506018862728013924781787286962603164898617964040941097032454602906538175500114877420185770813961751015945943845196221331166155688589928223661725093074936635677320044370196258306277733974758768802215631278241575925557151891119649135511126754796051942348827123735393713732302256235554688758321876052525716016457879137301177025100506807425371026497601
  | _ => 0

def rd (s : Fin 12) (i : Fin 6) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 12) (i : Fin 6) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 12) (i : Fin 6) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 12) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 12) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 12) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 12) (i : Fin 6) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 12) (i : Fin 6) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 56 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 1)
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
theorem far_cert (s : Fin 12) (i j : Fin 6) (hij : nonadj i j) : farCert s i j := by
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

theorem edge_at (p : ℕ) (hp : p < 56) :
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

theorem edge_tab (p : ℕ) (hp : p < 56) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 12) (i : Fin 6) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 1)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 1 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 1 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 12) (i : Fin 6) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 1 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 1
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

theorem far_desc (v : V) (hF : 1 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 12) (a1 a2 a3 : Fin 6) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 12, 0 < 5 * (Cc s 1 - 1) + 7 * (Cc s 5 - 1) + 0 * (Cc s 0 - 1) + 14 * 2 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 12, 0 < 7 * (Cc s 2 - 1) + 5 * (Cc s 4 - 1) + 0 * (Cc s 0 - 1) + 14 * 2 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 12, 0 < 1 * (Cc s 1 - 1) + 0 * (Cc s 0 - 1) + 0 * (Cc s 0 - 1) + 7 * 2 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 12, 0 < 1 * (Cc s 4 - 1) + 0 * (Cc s 0 - 1) + 0 * (Cc s 0 - 1) + 7 * 2 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 12, 0 < 2 * (Cc s 2 - (-1)) + 2 * (Cc s 5 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 1 lies in the cells |x| ≤ 1, |y| ≤ 1 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 12) (hF : F (x, y, s) ≤ 1) :
    -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 1 5 0 1 5 7 0 1 0 2 14 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 4 0 1 7 5 0 (-1) 0 2 14 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 1 0 0 1 1 0 0 0 1 2 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 0 0 1 1 0 0 0 (-1) 2 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 2 5 0 (-1) 2 2 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 1, b - 1) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 788040130999897886044728980339838580690996217410677616367416645422415009171406647822793209591476119662243648372736000 >>> (6 * ((a * 3 + b) * 12 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 1, b - 1) and class s, potential i plus
13 + 2 a + 7 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 6) : ℕ :=
  tgetN 148512 4 i.val * a + tgetN 13541892 4 i.val * b + tgetN 599290008306679513192727134278489475982659214212182236838427219903985860201325858214845522625135128082568021 5 (s * 6 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)

theorem fnt_tab : ∀ s : Fin 12, ∀ i : Fin 6, (tgetN 148512 4 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 13541892 4 i.val : ℤ) = Bc i + 7 ∧
    (tgetN 599290008306679513192727134278489475982659214212182236838427219903985860201325858214845522625135128082568021 5 (s.val * 6 + i.val) : ℤ) = Cc s i - Ac i * 1 - Bc i * 1 + 13 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 12) (i : Fin 6) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 1, (b : ℤ) - 1, s) i + (13 + 2 * a + 7 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 12) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 1, (b : ℤ) - 1, s) + (13 + 2 * a + 7 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 1, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 7) 1 = FN + 2 dx' + 7 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 3).all fun a => (List.range 3).all fun b => (List.range 12).all fun s =>
    Nat.blt (14 + 2 * a + 7 * b) (FN a b s) || (a == 1 && b == 1 && s == 7) ||
      (Nat.blt (hint a b s) 56 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 9 ==
          FN a b s + 2 * dxv (hint a b s) + 7 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 1) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 1).toNat (by omega) (y + 1).toNat (by omega) s.val s.isLt
  have ex : (((x + 1).toNat : ℕ) : ℤ) - 1 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  generalize (x + 1).toNat = a at h' ex
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
    have hs0 : s = 7 := Fin.ext (by rw [h3]; rfl)
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
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 1 = x + dx := by omega
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 1 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 1
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
from below, and for n ≥ 1 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 14 moves every quotient by an integer (`inner_shift`,
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
def AW (i : ℕ) : ℕ := tgetN 6859398 4 i

def BW (i : ℕ) : ℕ := tgetN 14660373 4 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem A_W (i : Fin 6) : Ac i = (AW i.val : ℤ) - 8 := rfl

theorem B_W (i : Fin 6) : Bc i = (BW i.val : ℤ) - 8 := rfl

theorem C_W (s : Fin 12) (i : Fin 6) : Cc s i = (CW s.val i.val : ℤ) - 8 := rfl

def gcV (k : ℕ) : ℕ := ctabN 62073 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 6) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 10512 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 6) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 10911810 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 5

def Bp (i : Fin 6) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 139795 3 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 2

def al (i : Fin 6) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 2688 2 k

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
def par (s : Fin 12) (i : Fin 6) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 12) (i j : Fin 6) (c u : ℤ) :
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

theorem par_inj (s : Fin 12) (i : Fin 6) (c : ℤ) : Function.Injective (par s i c) := by
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
(pot_i ≤ pot_j) plus cf0 times (1 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 46363472644155103808812013495393486045440 4 k

def cf2V (k : ℕ) : ℕ := ctabN 18864403806776930245517650072073341634560 4 k

def cf3V (k : ℕ) : ℕ := ctabN 2891828968921045774159958795136 3 k

def cf0V (k : ℕ) : ℕ := ctabN 1180591620717411321088 3 k

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
def certC (s : Fin 12) (i j : Fin 6) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (1 - Cc s i)

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := Nat.beq j i || Nat.beq j (nextF i) || Nat.beq j (prevF i)

/-- certG in natural numbers: Ac = AW - 8, Bc = BW - 8, the negative terms moved across. -/
def certGN (i j : ℕ) : Bool :=
  Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 6 i))) (AW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 6 i))) (AW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (AW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 6 i))) 8))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 6 i))) (cf2V (Nat.add j (Nat.mul 6 i)))) (cf0V (Nat.add j (Nat.mul 6 i)))) (AW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (AW j))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 6 i))) (BW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 6 i))) (BW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (BW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 6 i))) 8))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 6 i))) (cf2V (Nat.add j (Nat.mul 6 i)))) (cf0V (Nat.add j (Nat.mul 6 i)))) (BW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (BW j)))

/-- certC in natural numbers: Cc = CW - 8, the negative terms moved across. -/
def certCN (s i j : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 6 i))) (cf2V (Nat.add j (Nat.mul 6 i)))) (cf0V (Nat.add j (Nat.mul 6 i)))) (CW s i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (CW s j)))
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 6 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 6 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 6 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 6 i))) 9))

def certGK : PLift ((allR 6 fun i => allR 6 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 6 fun i => allR 6 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 12 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 12) : certS s = true := by
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
theorem certC_ok (s : Fin 12) (i j : Fin 6) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
def lev (s : Fin 12) (i : Fin 6) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 12) (i : Fin 6) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 12) (i j : Fin 6) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 12) (i : Fin 6) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 12) (i : Fin 6) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 12) (i j : Fin 6) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 12) (i : Fin 6) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 12) (i : Fin 6) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 12) (i : Fin 6) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 1 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 12) (i : Fin 6) (n u : ℤ) (hn : 1 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 1 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-6, 6]: a natural-number check. -/
def cbK : PLift ((allR 12 fun s => allR 6 fun i => Nat.ble (CW s i) 14 && Nat.ble 8 (Nat.add (CW s i) 6)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 12) (j : Fin 6) : -6 ≤ Cc s j ∧ Cc s j ≤ 6 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 6)) (1 * n + 6) ×ˢ
    (Finset.Icc (-(1 * n + 6)) (1 * n + 6) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (3 * Ac 2 + 5 * Ac 3 = 16 ∧ 3 * Bc 2 + 5 * Bc 3 = 0 ∧
    5 * Ac 0 + 3 * Ac 5 = (-16) ∧ 5 * Bc 0 + 3 * Bc 5 = 0 ∧
    1 * Ac 4 + 0 * Ac 4 = 0 ∧ 1 * Bc 4 + 0 * Bc 4 = 7 ∧
    1 * Ac 1 + 0 * Ac 1 = 0 ∧ 1 * Bc 1 + 0 * Bc 1 = (-7)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 3 * Ac 2 + 5 * Ac 3 = 16 ∧ 3 * Bc 2 + 5 * Bc 3 = 0 ∧
    5 * Ac 0 + 3 * Ac 5 = (-16) ∧ 5 * Bc 0 + 3 * Bc 5 = 0 ∧
    1 * Ac 4 + 0 * Ac 4 = 0 ∧ 1 * Bc 4 + 0 * Bc 4 = 7 ∧
    1 * Ac 1 + 0 * Ac 1 = 0 ∧ 1 * Bc 1 + 0 * Bc 1 = (-7) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 12) :
    16 * x ≤ 8 * F (x, y, s) + 48 ∧
    16 * (-x) ≤ 8 * F (x, y, s) + 48 ∧
    7 * y ≤ 1 * F (x, y, s) + 6 ∧
    7 * (-y) ≤ 1 * F (x, y, s) + 6 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 3 * pot (x, y, s) 2 + 5 * pot (x, y, s) 3 =
      16 * x + 3 * Cc s 2 + 5 * Cc s 3 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 2
  have r0 := le_F (x, y, s) 3
  have k0 := Cbound s 2
  have l0 := Cbound s 3
  have e1 : 5 * pot (x, y, s) 0 + 3 * pot (x, y, s) 5 =
      16 * (-x) + 5 * Cc s 0 + 3 * Cc s 5 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 5
  have k1 := Cbound s 0
  have l1 := Cbound s 5
  have e2 : 1 * pot (x, y, s) 4 + 0 * pot (x, y, s) 4 =
      7 * y + 1 * Cc s 4 + 0 * Cc s 4 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 4
  have r2 := le_F (x, y, s) 4
  have k2 := Cbound s 4
  have l2 := Cbound s 4
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
noncomputable def PF (s : Fin 12) (i : Fin 6) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 12) (i : Fin 6) (n : ℤ) (hn : 1 ≤ n) :
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
def inner (s : Fin 12) (i : Fin 6) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 12) (i : Fin 6) (n : ℤ) (hn : 1 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 12 × Fin 6, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 12 × Fin 6, inner p.1 p.2 n

/-! Shifting n by 14 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 14872110 4 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 6) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 708781 4 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 6

def mh (i : Fin 6) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 14159232 4 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 6

def mk (i : Fin 6) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 6, (14 : ℤ) = gc i * Lq i ∧ 14 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 14 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 6, (14 : ℤ) = gc i * Lq i ∧ 14 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 14 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 12) (i : Fin 6) (n : ℤ) :
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

/-- The growth of S over one period. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 12 × Fin 6, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 14) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 14 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 14 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 1 + r with r < 14: the level is QQ - 4 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 294984 4 k

def uhMV (k : ℕ) : ℕ := ctabN 196992 3 k

def ukPV (k : ℕ) : ℕ := ctabN 8521760 4 k

def ukMV (k : ℕ) : ℕ := ctabN 3078 3 k

def dhV (k : ℕ) : ℕ := ctabN 472397904 5 k

def dkV (k : ℕ) : ℕ := ctabN 539443278 5 k

def mhkV (k : ℕ) : ℕ := ctabN 57969 3 k

def uh (i : Fin 6) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 6) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 6) : ℤ := dhV i.val

def dk (i : Fin 6) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 6, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 6, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 3291021668917999285986529540097441362623239129744718751229542416 3 (Nat.add i (Nat.mul 6 s))

def QQ (s i : ℕ) : ℕ := ctabN 225860110983886825769117501868225973471322776110762340005144048769608882877072126869810 4 (Nat.add i (Nat.mul 6 s))

def AH (s i : ℕ) : ℕ := ctabN 590446095666461834613329669444446345034467046227427103561151689178642194514357061329137174899839505487627271 5 (Nat.add i (Nat.mul 6 s))

def AK (s i : ℕ) : ℕ := ctabN 3815219089696318814683249064313014368931156204744856467655678909484556581081155540464504698985765913153770725244425706746568044553 6 (Nat.add i (Nat.mul 6 s))

def WH (s i : ℕ) : ℕ := ctabN 252713917184943598960576413695552440732717068864171061210836267214531783937504324879633 4 (Nat.add i (Nat.mul 6 s))

def WK (s i : ℕ) : ℕ := ctabN 736771219437744493212326044046900095755128020796395132760407987668532948907923112454 4 (Nat.add i (Nat.mul 6 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 12 fun s => allR 6 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq (Nat.add 9 (Nat.mul (gcV i) 4)) (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (Nat.mul (uhPV i) 4)) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (Nat.mul (uhMV i) 4)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (Nat.mul (ukPV i) 4)) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (Nat.mul (ukMV i) 4)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 12) (i : Fin 6) :
    PP s.val i.val < gcV i.val ∧
    (1 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 4) + PP s.val i.val ∧
    (AH s.val i.val : ℤ) = uh i * ((QQ s.val i.val : ℤ) - 4) +
      (Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0)) + dh i * WH s.val i.val -
      (uhMV i.val : ℤ) * LqV i.val ∧
    (AK s.val i.val : ℤ) = uk i * ((QQ s.val i.val : ℤ) - 4) +
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

/-- Piece (s, i) at n = 1 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 1 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 12) (i : Fin 6) (r : ℕ) :
    ((1 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (1 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 4) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 12) (i : Fin 6) (r : ℕ) (hr : r < 14) :
    inner s i ((1 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (14 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 14 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((1 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 4) + tauN s.val i.val r := by
      rw [lev, show (1 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 4) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((1 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((1 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 2513068771236 6 k

def tblV (k : ℕ) : ℕ := ctabN 2506454786694 6 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 7. -/
def dv (t : ℕ) : ℕ := dtabV (t % 7)

/-- The sequence in closed form: b(n + 7) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 7) + tblV ((n - 1) % 7)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 7) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 7 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 7 - 1 = n - 1 + 7 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 7)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 14) = b n + 2 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 14 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 14 - 1 = n - 1 + 7 * 2 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 7)]
  ring

/-- b on the residue class of 1 + j mod 7. -/
theorem b_res (k j : ℕ) (hj : j < 7) : b (7 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (7 * k + (1 + j) < 1) by omega),
    show 7 * k + (1 + j) - 1 = j + 7 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 7), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 1 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 14 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 12 fun s => allR 6 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 12 fun s => sumR 6 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 1 r)) &&
    Nat.beq (sumR 12 fun s => sumR 6 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 2 (dv (Nat.add 0 r)))

/-! The window n = 1, ..., 14, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 14 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 14) :
    (∀ s, s < 12 → ∀ i, i < 6 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 12 fun s => sumR 6 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (1 + r) ∧
    (sumR 12 fun s => sumR 6 fun i => cond (divN s i r) (mhkV i) 0) = 2 * dv (0 + r) := by
  have h : periodR r = true := by
    exact allI_get _ _ _ periodK0.down r (by omega) (by omega)
  simp only [periodR, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun s hs i hi hd => ?_, h2, h3⟩
  have h4 := (allR_iff _ _).1 ((allR_iff _ _).1 h1 s hs) i hi
  rw [hd] at h4
  simpa using h4

theorem innerZ_eq (s i r : ℕ) (hs : s < 12) (hi : i < 6) (hr : r < 14) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 12 fun s => sumR 6 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 12 × Fin 6, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 6 fun i => f s i : ℕ) : ℤ)) 12]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 6]

theorem S_window (r : ℕ) (hr : r < 14) : S ((1 : ℤ) + r) = b (1 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 14) : Gs ((1 : ℤ) + r) = ((2 * dv (0 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 1 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 12) (i : Fin 6) (n : ℤ) (hn : 1 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 1 + t := ⟨(n - 1).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 14
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 14) (by omega) (by omega)
      have e : (1 : ℤ) + t = (1 + (t - 14 : ℕ)) + 14 := by
        push_cast [Nat.cast_sub (by omega : 14 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 1 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 14 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 1) % 14 < 14 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((1 : ℤ) + (((n - 1) % 14 : ℕ) : ℤ)) + 14 * (((n - 1) / 14 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (0 + (n - 1) % 14) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 1 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 15
    · obtain ⟨r, rfl⟩ : ∃ r, n = 1 + r := ⟨n - 1, by omega⟩
      push_cast
      exact S_window r (by omega)
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

The points with F ≤ 0 lie in the box -3 ≤ x ≤ 3, -0 ≤ y ≤ 0 (`small_box`). In natural-number
coordinates a = x + 3, b = y + 0 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 12) (h : F (x, y, s) ≤ 0) :
    -3 ≤ x ∧ x ≤ 3 ∧ -0 ≤ y ∧ y ≤ 0 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 3, (b : ℤ) - 0, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 24) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (AW i) 3) 8) (Nat.add (Nat.mul 8 a) (Nat.mul 8 b))

theorem pot_box (a b : ℕ) (s : Fin 12) (i : Fin 6) :
    pot ((a : ℤ) - 3, (b : ℤ) - 0, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 6 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 12) : F ((a : ℤ) - 3, (b : ℤ) - 0, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 3, (b : ℤ) - 0, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 3, (b : ℤ) - 0, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 6 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 6 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 3, (b : ℤ) - 0, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 3, (b : ℤ) - 0, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 3, (b : ℤ) - 0, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 7 fun a => sumR 1 fun b => sumR 12 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 0 .. 0, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 0 1 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 1) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 12) : V := ((q.1 : ℤ) - 3, (q.2.1 : ℤ) - 0, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 0) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 7 ×ˢ (Finset.range 1 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 12 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 3).toNat, (y + 0).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 3).toNat (y + 0).toNat s
        rw [show (((x + 3).toNat : ℕ) : ℤ) - 3 = x by omega,
          show (((y + 0).toNat : ℕ) : ℤ) - 0 = y by omega, h] at e
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 12]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 1 are counted in the
box, those from 1 on are S(n), and both agree with the closed form b (`a_eq_b`). The step from n to
n + 7, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 1 ∨ 1 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_eq n (by omega) h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 7) = a(n) + dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 7) = a n + dv (n - 1) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 36 ∧ tblV 0 = 6 ∧ dv 1 = 30 ∧ tblV 1 = 10 ∧ dv 2 = 36 ∧ tblV 2 = 14 ∧ dv 3 = 36 ∧ tblV 3 = 22 ∧ dv 4 = 30 ∧ tblV 4 = 20 ∧ dv 5 = 36 ∧ tblV 5 = 30 ∧ dv 6 = 36 ∧ tblV 6 = 36) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (7 * k + 1) = 36 * k + 6 ∧
    a (7 * k + 2) = 30 * k + 10 ∧
    a (7 * k + 3) = 36 * k + 14 ∧
    a (7 * k + 4) = 36 * k + 22 ∧
    a (7 * k + 5) = 30 * k + 20 ∧
    a (7 * k + 6) = 36 * k + 30 ∧
    a (7 * k + 7) = 36 * k + 36 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 7 * k + 1 = 7 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 7 * k + 2 = 7 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 7 * k + 3 = 7 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 7 * k + 4 = 7 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 7 * k + 5 = 7 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 7 * k + 6 = 7 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 7 * k + 7 = 7 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]

/-- The closed form per residue of n mod 7, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (7 * k + 1) = 36 * k + 6 ∧
    a (7 * k + 2) = 30 * k + 10 ∧
    a (7 * k + 3) = 36 * k + 14 ∧
    a (7 * k + 4) = 36 * k + 22 ∧
    a (7 * k + 5) = 30 * k + 20 ∧
    a (7 * k + 6) = 36 * k + 30 ∧
    a (7 * k + 7) = 36 * k + 36 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6⟩ := a_closed0 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6⟩

def controlsK : PLift ((List.range 50).map b = [1, 6, 10, 14, 22, 20, 30, 36, 42, 40, 50, 58, 50, 66, 72, 78, 70, 86, 94, 80, 102, 108, 114, 100, 122, 130, 110, 138, 144, 150, 130, 158, 166, 140, 174, 180, 186, 160, 194, 202, 170, 210, 216, 222, 190, 230, 238, 200, 246, 252]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 6, 10, 14, 22, 20, 30, 36, 42, 40, 50, 58, 50, 66, 72, 78, 70, 86, 94, 80, 102, 108, 114, 100, 122, 130, 110, 138, 144, 150, 130, 158, 166, 140, 174, 180, 186, 160, 194, 202, 170, 210, 216, 222, 190, 230, 238, 200, 246, 252] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 7 → dv (t + 14) + dv (t + 0) = 2 * dv (t + 7)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 7 → dv (t + 14) + dv (t + 0) = 2 * dv (t + 7) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 14) : ℤ) = 2 * (dv (t + 7) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 7 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 7, e 14]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 7) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 7 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 7 → b (q + 15) + b (q + 1) = 2 * b (q + 8)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 7 → b (q + 15) + b (q + 1) = 2 * b (q + 8) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 15) : ℤ) = 2 * b (q + 8) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 7 ∨ 7 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 7 := ⟨q - 7, by omega⟩
      have h0 : (b (v + 15) : ℤ) = 2 * b (v + 8) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 8) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 7 = v + 8 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s8 : (b (v + 15) : ℤ) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (le_trans (by decide : 1 ≤ 8) (Nat.le_add_left _ v))
        rw [show v + 8 + 7 = v + 15 from Nat.add_assoc _ _ _,
          show v + 8 - 1 = v + 7 from Nat.add_sub_assoc (by decide : 1 ≤ 8) v] at h
        exact_mod_cast h
      have s15 : (b (v + 22) : ℤ) = b (v + 15) + dv (v + 14) := by
        have h := b_step (v + 15) (le_trans (by decide : 1 ≤ 15) (Nat.le_add_left _ v))
        rw [show v + 15 + 7 = v + 22 from Nat.add_assoc _ _ _,
          show v + 15 - 1 = v + 14 from Nat.add_sub_assoc (by decide : 1 ≤ 15) v] at h
        exact_mod_cast h
      show (b (v + 22) : ℤ) = 2 * b (v + 15) - b (v + 8)
      linear_combination s15 - (2) * s8 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 7) - a (n - 14) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 15 := ⟨n - 15, by omega⟩
  rw [show q + 15 - 7 = q + 8 from Nat.add_sub_assoc (by decide : 7 ≤ 15) q, show q + 15 - 14 = q + 1 from Nat.add_sub_assoc (by decide : 14 ≤ 15) q]
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

/-- The coefficients of A * DEN and NUM agree below 15, in natural numbers (negative terms moved
across). -/
def gfL (n : ℕ) : ℕ := Nat.add (b n) (bk n 14)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 2 (bk n 7)) (ind n 0)) (Nat.mul 6 (ind n 1))) (Nat.mul 10 (ind n 2))) (Nat.mul 14 (ind n 3))) (Nat.mul 22 (ind n 4))) (Nat.mul 20 (ind n 5))) (Nat.mul 30 (ind n 6))) (Nat.mul 34 (ind n 7))) (Nat.mul 30 (ind n 8))) (Nat.mul 20 (ind n 9))) (Nat.mul 22 (ind n 10))) (Nat.mul 14 (ind n 11))) (Nat.mul 10 (ind n 12))) (Nat.mul 6 (ind n 13))) (ind n 14)

def gfK : PLift ((allR 15 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 15, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 15) :
    1 * (b (n) : ℚ) - 2 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) + 1 * (if 14 ≤ n then (b (n - 14) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 6 + (if n = 2 then (1 : ℚ) else 0) * 10 + (if n = 3 then (1 : ℚ) else 0) * 14 + (if n = 4 then (1 : ℚ) else 0) * 22 + (if n = 5 then (1 : ℚ) else 0) * 20 + (if n = 6 then (1 : ℚ) else 0) * 30 + (if n = 7 then (1 : ℚ) else 0) * 34 + (if n = 8 then (1 : ℚ) else 0) * 30 + (if n = 9 then (1 : ℚ) else 0) * 20 + (if n = 10 then (1 : ℚ) else 0) * 22 + (if n = 11 then (1 : ℚ) else 0) * 14 + (if n = 12 then (1 : ℚ) else 0) * 10 + (if n = 13 then (1 : ℚ) else 0) * 6 + (if n = 14 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 15 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 15) : ℚ) - 2 * (if 7 ≤ q + 15 then (b (q + 15 - 7) : ℚ) else 0) + 1 * (if 14 ≤ q + 15 then (b (q + 15 - 14) : ℚ) else 0) =
      (if q + 15 = 0 then (1 : ℚ) else 0) * 1 + (if q + 15 = 1 then (1 : ℚ) else 0) * 6 + (if q + 15 = 2 then (1 : ℚ) else 0) * 10 + (if q + 15 = 3 then (1 : ℚ) else 0) * 14 + (if q + 15 = 4 then (1 : ℚ) else 0) * 22 + (if q + 15 = 5 then (1 : ℚ) else 0) * 20 + (if q + 15 = 6 then (1 : ℚ) else 0) * 30 + (if q + 15 = 7 then (1 : ℚ) else 0) * 34 + (if q + 15 = 8 then (1 : ℚ) else 0) * 30 + (if q + 15 = 9 then (1 : ℚ) else 0) * 20 + (if q + 15 = 10 then (1 : ℚ) else 0) * 22 + (if q + 15 = 11 then (1 : ℚ) else 0) * 14 + (if q + 15 = 12 then (1 : ℚ) else 0) * 10 + (if q + 15 = 13 then (1 : ℚ) else 0) * 6 + (if q + 15 = 14 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 15) : ℤ) = 2 * b (q + 8) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 15 - 7 = q + 8 from Nat.add_sub_assoc (by decide : 7 ≤ 15) q, show q + 15 - 14 = q + 1 from Nat.add_sub_assoc (by decide : 14 ≤ 15) q, show 7 ≤ q + 15 from le_trans (by decide : 7 ≤ 15) (Nat.le_add_left 15 q), show 14 ≤ q + 15 from le_trans (by decide : 14 ≤ 15) (Nat.le_add_left 15 q), show ¬ q + 15 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 14 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 14 < 15) (Nat.le_add_left 15 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * (X ^ 14 - 2 * X ^ 7 + 1) = C 1 * A - C 2 * (A * X ^ 7) + C 1 * (A * X ^ 14) := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (X ^ 14 + 6 * X ^ 13 + 10 * X ^ 12 + 14 * X ^ 11 + 22 * X ^ 10 + 20 * X ^ 9 + 30 * X ^ 8 + 34 * X ^ 7 + 30 * X ^ 6 + 20 * X ^ 5 + 22 * X ^ 4 + 14 * X ^ 3 + 10 * X ^ 2 + 6 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 6 + X ^ 2 * C 10 + X ^ 3 * C 14 + X ^ 4 * C 22 + X ^ 5 * C 20 + X ^ 6 * C 30 + X ^ 7 * C 34 + X ^ 8 * C 30 + X ^ 9 * C 20 + X ^ 10 * C 22 + X ^ 11 * C 14 + X ^ 12 * C 10 + X ^ 13 * C 6 + X ^ 14 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - 2 * X ^ 7 + 1) =
      X ^ 14 + 6 * X ^ 13 + 10 * X ^ 12 + 14 * X ^ 11 + 22 * X ^ 10 + 20 * X ^ 9 + 30 * X ^ 8 + 34 * X ^ 7 + 30 * X ^ 6 + 20 * X ^ 5 + 22 * X ^ 4 + 14 * X ^ 3 + 10 * X ^ 2 + 6 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  rw [gf_den A, gf_num]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 15 with hn | hn
  · linarith [gf_low n hn]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 15 := ⟨n - 15, by omega⟩
    linarith [gf_high q]

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - 2 * X ^ 7 + 1) =
      X ^ 14 + 6 * X ^ 13 + 10 * X ^ 12 + 14 * X ^ 11 + 22 * X ^ 10 + 20 * X ^ 9 + 30 * X ^ 8 + 34 * X ^ 7 + 30 * X ^ 6 + 20 * X ^ 5 + 22 * X ^ 4 + 14 * X ^ 3 + 10 * X ^ 2 + 6 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 7) - a (n - 14) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 6, 10, 14, 22, 20, 30, 36, 42, 40, 50, 58, 50, 66, 72, 78, 70, 86, 94, 80, 102, 108, 114, 100, 122, 130, 110, 138, 144, 150, 130, 158, 166, 140, 174, 180, 186, 160, 194, 202, 170, 210, 216, 222, 190, 230, 238, 200, 246, 252] := Count.controls

/-- The step a(n + 7) = a(n) + Count.dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 7) = a n + Count.dv (n - 1) := Count.a_step n hn

/-- The closed form per residue of n mod 7, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (7 * k + 1) = 36 * k + 6 ∧
    a (7 * k + 2) = 30 * k + 10 ∧
    a (7 * k + 3) = 36 * k + 14 ∧
    a (7 * k + 4) = 36 * k + 22 ∧
    a (7 * k + 5) = 30 * k + 20 ∧
    a (7 * k + 6) = 36 * k + 30 ∧
    a (7 * k + 7) = 36 * k + 36 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 - 2 * X ^ 7 + 1) =
      X ^ 14 + 6 * X ^ 13 + 10 * X ^ 12 + 14 * X ^ 11 + 22 * X ^ 10 + 20 * X ^ 9 + 30 * X ^ 8 + 34 * X ^ 7 + 30 * X ^ 6 + 20 * X ^ 5 + 22 * X ^ 4 + 14 * X ^ 3 + 10 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 7) - a (n - 14) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a315227

theorem OMA.solution : type_of% @OMA.S_oeis_a315227.main :=
  OMA.S_oeis_a315227.conjecture
