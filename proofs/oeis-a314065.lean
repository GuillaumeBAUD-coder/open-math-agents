import OMAStatements.S_oeis_a314065

namespace OMA.S_oeis_a314065






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 8

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 2557900954
  | 1 => 2575792009
  | 2 => 2290649224
  | 3 => 2612688214
  | 4 => 2593683064
  | 5 => 2308540279
  | 6 => 2611574119
  | 7 => 2326431334
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 1738189174 4 8 i.val

def Bc (i : Fin 8) : ℤ := tget 2630579269 4 8 i.val

def Cc (s : Fin 8) (i : Fin 8) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 1738189174 4 i

def BcN (i : ℕ) : ℕ := tgetN 2630579269 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 8) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 8) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 8) (i : Fin 8) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


/-- The potential of facet i at v (facets in angular order around the growth polygon). -/
def pot (v : V) (i : Fin 8) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest facet potential at v. -/
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

/-- A statement about every vertex class follows from the statements about each class. -/
theorem cls (P : Fin 8 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 8 × Fin 8 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
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
theorem shift (x y : ℤ) (e : Fin 8 × Fin 8 × ℤ × ℤ) (j : Fin 8) :
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
theorem farkas (x y : ℤ) (s : Fin 8) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
adjacent to i, the fields k1, k2, m1, m2, m0, mj of entry i * 8 + j give the facts pot k1 ≤ pot i,
pot k2 ≤ pot i, 7 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 3948313361144661085594174185073597059369822783825624201950102486988154338757594142830336765682861842445221038537391066784772769615527195466065465234658890531448143581646645766718780133603516446358276912376514583251902111358959221440237500719211062108396346600608128974288098467653416142617997389503112197808544602319732827691165938510165602715138185184560538703224388991560686495621237208443507156972224475355112412172597645307367062306499481042944 4 ((i * 8 + j) * 6 + f)

def fd (i j : Fin 8) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 0 % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 1 % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 8 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 1329222200633889426802228800763756544 3 p

def dstv (p : ℕ) : ℕ := tgetN 1135976911050153093791170613884774097 3 p

def dxv (p : ℕ) : ℕ := tgetN 709855380512733726328129 2 p

def dyv (p : ℕ) : ℕ := tgetN 402976426126403479884805 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 9806222209153402365563318118313204776934303050398361952987171148190579372314153812731584251651638359385052878471537441850758277925617957225879778907942023112777564774027559813591492209544136464491561908033227875836826478527978270582546278609098521777153500039974465023963617314005873513479921933391497436565789288255552408921288741074810393088829987950062018367422561498212564685391735 4 (p * 8 + j)

def dlv (p : ℕ) (j : Fin 8) : ℤ := (dlvN p j.val : ℤ) - 8

theorem dlv_neg (p : ℕ) (j : Fin 8) (h : dlvN p j.val + 1 ≤ 8) : dlv p j ≤ -1 := by
  unfold dlv
  omega

theorem dlv_le (p : ℕ) (j : Fin 8) (c : ℕ) (h : dlvN p j.val + 1 ≤ c + 8) : dlv p j ≤ (c : ℤ) - 1 := by
  unfold dlv
  omega

/-- The next and the previous facet around the growth polygon. -/
def nxt (i : Fin 8) : Fin 8 := ⟨(i.val + 1) % 8, Nat.mod_lt _ (by norm_num)⟩

def prv (i : Fin 8) : Fin 8 := ⟨(i.val + 7) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The facets i and j are not equal and not adjacent sides of the growth polygon. -/
def nonadj (i j : Fin 8) : Prop := j ≠ i ∧ j ≠ nxt i ∧ j ≠ prv i

instance : DecidableRel nonadj := fun i j => by unfold nonadj; infer_instance

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 8). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 8) + fdN i j 3 * AcN (fdN i j 1 % 8) + fdN i j 5 * AcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 8) + fdN i j 3 * BcN (fdN i j 1 % 8) + fdN i j 5 * BcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * BcN i + fdN i j 5 * BcN j)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farCN (s i j : ℕ) : Bool :=
  Nat.blt ((fdN i j 2 + fdN i j 3 + fdN i j 4) * CcN s i + fdN i j 5 * (CcN s j + 1))
    (fdN i j 2 * CcN s (fdN i j 0 % 8) + fdN i j 3 * CcN s (fdN i j 1 % 8) + fdN i j 5 * CcN s i +
      fdN i j 4 * 15)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

def farOK : Bool := (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 8).all fun s => (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 40).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 8).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 8) (i j : Fin 8) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (7 - Cc s i)

/-- Beyond F = 6, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 8) (i j : Fin 8) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 6 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 7 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 6, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 6 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 10401192663568270608655559001636779019304442313327286684226287025007274000679886702031474723018389940855082601802595758680547285254148828922754695564121113342588615501320402840496108385989518303271708485085713444958760819182223956544734765368725606754596977674643585241086678748785888388708015234221504750101305787741863723028220475622967617132675883961463367681512324920192581387416372661581743343573207914420271960438549815872154792593911064789605379863375812752849163776652045513946419885246313134884860108940403007686510987408122295896914758735072303424907974110186739518654268176489520383026754344538187100057957718384248809825466644976946530867443212040528193386941328239360470687857700776993198743268533611760475013160971198744361671216490429890116796699503844240418772173412545883100338485198247557180307130024083568995440656116561162611074976971919667687108432378192318136031198598166424136915728080961
  | 1 => 10401192665971067331627037320553474804971185942954076720397723477986980809783239541679596553208000897307441662035706907861340376776590722665183022579549554554799276419928889358662945225954743237166332637536778897050005032375038991650153541549326598820550341447860669606494825471797693416376304042059545808872559259632896853581865521229992378272498684434559605194398272954655786903981949798169156058080436412230412629984591465087510260200713369167778348721031613838157263947543297671250421903683587926210676840968805612657376973422275068421615334265390984921309706360936299802233808509843098294580242994512116748954880380267253828139793903557823881081558135467150247384365734449593133141660779324291804440117719763917936598163433938981252039749289134685924662937239059961086035315026278490889584488556769722068864184743878339750158832112873879479924709530706507952041157179239746095058176546329364403924723966017
  | 2 => 10401192667773164873855646059740996644221243665174169247526300817721760916610754171415853933510234796714396106432584708676515011423749625382566679671865786117761982589119857041020465760241925131514899486263842481109008798046169155301027985050044977002812763766297141851558685845096929458375187050230434610750531099050781582387544035878890544117783645489885610857752728963415705330557603525768375334793891955229674683360329076447871477671149654782063120897706961916729135104971584614532014550531115954752747236031946663479576562527300380249789175229026366462568458245421145939521917609096011054318704045115350836520723870839924652654954325694916906563223510298430737525372348439552818714760709349314880837692312401667245999550816062202954878903133941815404332720618257789438471014424974029951637999978461024893019507522555813607810394287363065003866285995671888878472219596136682471628883754328424038619287660096
  | 3 => 10401192671377359958312863538116040415887618413403560400718902620601333921079162112911466819185567029228507239304204541087054109081325274533266211346095845948451643913529102254796249950278908145643325911524439332715094153665966458477442221561842100542221675301480662975242194529166519469995474391178570723395446459281810539616349341903064303765411015550306371004938295354019276149652422837303379384603439184861858802941033798370763355379310993597986146388644553648037983734765140907745910470618107802107050169986306463017179156118179658387145689436305738239630417631927177268835769857118743933163012244219377723648502802359837125809117549974225038152346097334956812022186847107401499247548794194284865048619405094211983032439908576814113452534587248367650914314102150530588981881209485428102117978249890743345136379628788563847681865468524463275155515130589562560045217059217862195358692928144103612480253601856
  | 4 => 10401192674981555042770081016491084001221474554054539356040610176660881343920812690360053416419041984003788137909873717289321787775743577304932379002922812690152221654692480835226016166080402659937795376202483202273815413176228930889588098879523503548073645055514366461480700293841932439839757225625406900706620759161696527333754672297738355221478444242039030175583396293816561859928801784814755591486945850725847391277719533029609940352448424509942607775169619751730470418631343457413345743796508680941292114051466397903705754863994245782634698359444009904502363626815937903068131853966725197959216071288132691233110246801477006569165272886507882614955030822737669217438798529069710757904252978574475420180521034993951488670728600962613762441648400214729250872293644434320940480042450053475026539694937108266679480990288113303560095128158358392117545202343673597855990558145551115586273731475945804323852787777
  | 5 => 10401192676783652584998689755678605840471532276274631883169187516395661450748327320096393800551288724444566875137908569530526217564379358604853478081136146668796639600172391508488702868186953763375935609474049661116128378272370741605353800114461797616216799291764852408090259455662258601148172085573373499756163838817438348672562812396176833845124110972295326936345593058866936456054108736259322720690660513487034181346538468004430872248215000242432824547086820869409432153213056697022753385994737886507197065470286461017521500442998051522985095255240031094238654483839516111539917517123704110507735494290348907336102606241612837918107451282648021468369620707700954805983102062930789962734457163944469516348515489655747466866875317536034870407575908614708940790780317866908804835357551798776431951871395861662493989457123481022630883192204680918001707961597154732602499823987801333171680456544153935724860681792
  | 6 => 10401192682189945211684515973241171358221705442934909464554919535600001771230871209304418906987874853360865318609207164831706916575065861016731864141621419198434577842503354016476472918180930198154965567135046646452863717817180882281135744743681027330092287941637323945469400151477323658610519772478095774173869958784736266335265993151935136780662252088022570160531494965145181824686283374131235218212153401522195200312221987383289684473836468783674015018480024482576491918847521591798773465715920458231051099269188469636855062538893409909940121895500678082398424845316273935491944607930927221968084562298477228154762387811840855778953862197557150491072937926933810576546583139445226330113752461575346534351728818230077026594574916815092333301701088098505885868151941011494389655959060149903113127409081504970083808417828708333102912682184575553663370380907177546354528714080522112520153767492270524167753965633
  | 7 => 10401192683391343573170255132699519251055077257748304482640637762089855175782547629128728833572718854688554290731761057996663223221331554423676985325177574192177783912327359056959950409883874014445412509168653307007075172011081927773336340631329101101423444942431311775942013007303387591084099794953052274342905003021452017580544086384955749897666494010812778584112841613861573678648897397202684664074484951112751332720262288566686022120608480063762116461537138202314903310002488371534182753015681225638175003439798650379796516070727700891601503535559256059613363620088585350529576064060965553739291748981834262753489108225571397458898615376312335317310807185699389769585358107576787393374881108825176070107176710919413860823247825242701885376933118452900196779795190061699470755419855522493069907867119284264419459216687164719555967724602299643377051175799005699082854107966555636341131588558872096006032339904
  | _ => 0

def rd (s : Fin 8) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 8) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 8) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 8) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 8) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 8) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 8) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 8) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 40 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 6)
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
theorem far_cert (s : Fin 8) (i j : Fin 8) (hij : nonadj i j) : farCert s i j := by
  have hn : nearB i.val j.val = false := by
    obtain ⟨h1, h2, h3⟩ := hij
    have e1 : j.val ≠ i.val := fun h => h1 (Fin.ext h)
    have e2 : j.val ≠ (i.val + 1) % 8 := fun h => h2 (Fin.ext h)
    have e3 : j.val ≠ (i.val + 7) % 8 := fun h => h3 (Fin.ext h)
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

theorem edge_at (p : ℕ) (hp : p < 40) :
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

theorem edge_tab (p : ℕ) (hp : p < 40) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 8) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 6)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 6 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 6 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 8) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 6 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 6
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

theorem far_desc (v : V) (hF : 6 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 8) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 8, 0 < 1 * (Cc s 1 - 6) + 4 * (Cc s 7 - 6) + 0 * (Cc s 0 - 6) + 9 * 4 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 8, 0 < 4 * (Cc s 3 - 6) + 1 * (Cc s 5 - 6) + 0 * (Cc s 0 - 6) + 9 * 4 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 8, 0 < 2 * (Cc s 1 - 6) + 1 * (Cc s 3 - 6) + 0 * (Cc s 0 - 6) + 9 * 3 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 8, 0 < 2 * (Cc s 5 - 6) + 1 * (Cc s 7 - 6) + 0 * (Cc s 0 - 6) + 9 * 3 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 8, 0 < 2 * (Cc s 3 - (-1)) + 2 * (Cc s 7 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 6 lies in the cells |x| ≤ 3, |y| ≤ 2 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 8) (hF : F (x, y, s) ≤ 6) :
    -3 ≤ x ∧ x ≤ 3 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 1 7 0 6 1 4 0 1 0 4 9 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 5 0 6 4 1 0 (-1) 0 4 9 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 1 3 0 6 2 1 0 0 1 3 9 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 7 0 6 2 1 0 0 (-1) 3 9 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 3 7 0 (-1) 2 2 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 3, b - 2) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 808876171303415998404169784294046518664130891289307207035630707907999261922554956349808623292766783263686855863844741338660436520050394218696486068115832652208972937799026966697072216060917466207192780200094760031616500080209256461715095560705179089178016788800821210704520737534388270879973305880293623463735065012932655690790339219924546756485605978827983634423571683623773712601419846162410448969729194601237198830601946886075077201786170788834602305311136179428524032 >>> (6 * ((a * 5 + b) * 8 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 3, b - 2) and class s, potential i plus
14 + 2 a + 4 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 8) : ℕ :=
  tgetN 20202256 4 i.val * a + tgetN 1485254657 4 i.val * b + tgetN 1224772626712389994667989760041303024518900885522971870580074486655936050960672779084186383601500 5 (s * 8 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)

theorem fnt_tab : ∀ s : Fin 8, ∀ i : Fin 8, (tgetN 20202256 4 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 1485254657 4 i.val : ℤ) = Bc i + 4 ∧
    (tgetN 1224772626712389994667989760041303024518900885522971870580074486655936050960672779084186383601500 5 (s.val * 8 + i.val) : ℤ) = Cc s i - Ac i * 3 - Bc i * 2 + 14 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 8) (i : Fin 8) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 3, (b : ℤ) - 2, s) i + (14 + 2 * a + 4 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 8) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 3, (b : ℤ) - 2, s) + (14 + 2 * a + 4 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 6, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 4) 1 = FN + 2 dx' + 4 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 7).all fun a => (List.range 5).all fun b => (List.range 8).all fun s =>
    Nat.blt (20 + 2 * a + 4 * b) (FN a b s) || (a == 3 && b == 2 && s == 2) ||
      (Nat.blt (hint a b s) 40 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 6 ==
          FN a b s + 2 * dxv (hint a b s) + 4 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 6) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 3).toNat (by omega) (y + 2).toNat (by omega) s.val s.isLt
  have ex : (((x + 3).toNat : ℕ) : ℤ) - 3 = x := by omega
  have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by omega
  generalize (x + 3).toNat = a at h' ex
  generalize (y + 2).toNat = b at h' ey
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
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 3 = x + dx := by omega
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 2 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 6
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
from below, and for n ≥ 3 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 140 moves every quotient by an integer (`inner_shift`,
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
def AW (i : ℕ) : ℕ := tgetN 1738189174 4 i

def BW (i : ℕ) : ℕ := tgetN 2630579269 4 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem A_W (i : Fin 8) : Ac i = (AW i.val : ℤ) - 8 := rfl

theorem B_W (i : Fin 8) : Bc i = (BW i.val : ℤ) - 8 := rfl

theorem C_W (s : Fin 8) (i : Fin 8) : Cc s i = (CW s.val i.val : ℤ) - 8 := rfl

def gcV (k : ℕ) : ℕ := ctabN 255 1 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 8) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 379080 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 8) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 1485254657 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 4

def Bp (i : Fin 8) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 18530 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 8) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 38420 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 8) : ℤ := beN i.val

def primK : PLift (∀ i : Fin 8, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧ al i * Ap i + be i * Bp i = 1) :=
  ⟨by decide +kernel⟩

theorem prim : ∀ i : Fin 8, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧ al i * Ap i + be i * Bp i = 1 := primK.down

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 8) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 8) : ℤ := Ac j * al i + Bc j * be i

def orientK : PLift (∀ i : Fin 8, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0) :=
  ⟨by decide +kernel⟩

theorem orient : ∀ i : Fin 8, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := orientK.down

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 8) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 8) (i j : Fin 8) (c u : ℤ) :
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

theorem par_inj (s : Fin 8) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
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

/-- The previous and the next facet around the growth polygon, and [i - 1 < i], [i + 1 < i]. -/
def prevF (i : ℕ) : ℕ := Nat.mod (Nat.add i 7) 8

def nextF (i : ℕ) : ℕ := Nat.mod (Nat.add i 1) 8

def ehV (k : ℕ) : ℕ := ctabN 254 1 k

def ekV (k : ℕ) : ℕ := ctabN 128 1 k

def fin_prevK : PLift (∀ i : Fin 8, (i - 1).val = prevF i.val ∧ (if i - 1 < i then (1 : ℤ) else 0) = (ehV i.val : ℤ)) :=
  ⟨by decide +kernel⟩

theorem fin_prev : ∀ i : Fin 8, (i - 1).val = prevF i.val ∧ (if i - 1 < i then (1 : ℤ) else 0) = (ehV i.val : ℤ) := fin_prevK.down

def fin_nextK : PLift (∀ i : Fin 8, (i + 1).val = nextF i.val ∧ (if i + 1 < i then (1 : ℤ) else 0) = (ekV i.val : ℤ)) :=
  ⟨by decide +kernel⟩

theorem fin_next : ∀ i : Fin 8, (i + 1).val = nextF i.val ∧ (if i + 1 < i then (1 : ℤ) else 0) = (ekV i.val : ℤ) := fin_nextK.down

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (3 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 183793936576416554582207322294022072868908345142873032255682572169249824768 4 k

def cf2V (k : ℕ) : ℕ := ctabN 93692069376516044557679061567890458320361384780745098337197368019484969728 4 k

def cf3V (k : ℕ) : ℕ := ctabN 60197462997167273658747236012665899351874803848969581693658348014592406784 4 k

def cf0V (k : ℕ) : ℕ := ctabN 383123888472381034884244224236940654082666457449178240 3 k

def cf1 (i j : Fin 8) : ℤ := (cf1V (j.val + 8 * i.val) : ℤ)

def cf2 (i j : Fin 8) : ℤ := (cf2V (j.val + 8 * i.val) : ℤ)

def cf3 (i j : Fin 8) : ℤ := (cf3V (j.val + 8 * i.val) : ℤ)

def cf0 (i j : Fin 8) : ℤ := (cf0V (j.val + 8 * i.val) : ℤ)

/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 8) (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (3 - Cc s i)

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := Nat.beq j i || Nat.beq j (nextF i) || Nat.beq j (prevF i)

/-- certG in natural numbers: Ac = AW - 8, Bc = BW - 8, the negative terms moved across. -/
def certGN (i j : ℕ) : Bool :=
  Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 8 i))) (AW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 8 i))) (AW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (AW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 8 i))) 8))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 8 i))) (cf2V (Nat.add j (Nat.mul 8 i)))) (cf0V (Nat.add j (Nat.mul 8 i)))) (AW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (AW j))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 8 i))) (BW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 8 i))) (BW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (BW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 8 i))) 8))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 8 i))) (cf2V (Nat.add j (Nat.mul 8 i)))) (cf0V (Nat.add j (Nat.mul 8 i)))) (BW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (BW j)))

/-- certC in natural numbers: Cc = CW - 8, the negative terms moved across. -/
def certCN (s i j : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 8 i))) (cf2V (Nat.add j (Nat.mul 8 i)))) (cf0V (Nat.add j (Nat.mul 8 i)))) (CW s i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (CW s j)))
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 8 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 8 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 8 i))) 11))

def certGK : PLift ((allR 8 fun i => allR 8 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 8 fun i => allR 8 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 8 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 8) : certS s = true := by
  exact allI_get _ _ _ certCK0.down s (by omega) (by omega)

theorem beq_ff (x y : ℕ) (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem near_false (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
theorem certG_ok (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) : certG i j := by
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
theorem certC_ok (s : Fin 8) (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
def lev (s : Fin 8) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 8) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 8) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 8) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 8) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 8) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 8) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 8) (i : Fin 8) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 8) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 3 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 8) (i : Fin 8) (n u : ℤ) (hn : 3 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 3 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-3, 3]: a natural-number check. -/
def cbK : PLift ((allR 8 fun s => allR 8 fun i => Nat.ble (CW s i) 11 && Nat.ble 8 (Nat.add (CW s i) 3)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 8) (j : Fin 8) : -3 ≤ Cc s j ∧ Cc s j ≤ 3 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 3)) (1 * n + 3) ×ˢ
    (Finset.Icc (-(1 * n + 3)) (1 * n + 3) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (3 * Ac 3 + 1 * Ac 4 = 8 ∧ 3 * Bc 3 + 1 * Bc 4 = 0 ∧
    1 * Ac 0 + 3 * Ac 7 = (-8) ∧ 1 * Bc 0 + 3 * Bc 7 = 0 ∧
    1 * Ac 5 + 1 * Ac 6 = 0 ∧ 1 * Bc 5 + 1 * Bc 6 = 8 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-8)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 3 * Ac 3 + 1 * Ac 4 = 8 ∧ 3 * Bc 3 + 1 * Bc 4 = 0 ∧
    1 * Ac 0 + 3 * Ac 7 = (-8) ∧ 1 * Bc 0 + 3 * Bc 7 = 0 ∧
    1 * Ac 5 + 1 * Ac 6 = 0 ∧ 1 * Bc 5 + 1 * Bc 6 = 8 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-8) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 8) :
    8 * x ≤ 4 * F (x, y, s) + 12 ∧
    8 * (-x) ≤ 4 * F (x, y, s) + 12 ∧
    8 * y ≤ 2 * F (x, y, s) + 6 ∧
    8 * (-y) ≤ 2 * F (x, y, s) + 6 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 3 * pot (x, y, s) 3 + 1 * pot (x, y, s) 4 =
      8 * x + 3 * Cc s 3 + 1 * Cc s 4 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 3
  have r0 := le_F (x, y, s) 4
  have k0 := Cbound s 3
  have l0 := Cbound s 4
  have e1 : 1 * pot (x, y, s) 0 + 3 * pot (x, y, s) 7 =
      8 * (-x) + 1 * Cc s 0 + 3 * Cc s 7 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 7
  have k1 := Cbound s 0
  have l1 := Cbound s 7
  have e2 : 1 * pot (x, y, s) 5 + 1 * pot (x, y, s) 6 =
      8 * y + 1 * Cc s 5 + 1 * Cc s 6 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 5
  have r2 := le_F (x, y, s) 6
  have k2 := Cbound s 5
  have l2 := Cbound s 6
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
noncomputable def PF (s : Fin 8) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 8) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) :
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
def inner (s : Fin 8) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 8) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 8 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 8 × Fin 8, inner p.1 p.2 n

/-! Shifting n by 140 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 10127624197330734220 8 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 8) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 26775865511583874 8 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 60

def mh (i : Fin 8) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 71093150806519168 7 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 56

def mk (i : Fin 8) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 8, (140 : ℤ) = gc i * Lq i ∧ 140 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 140 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 8, (140 : ℤ) = gc i * Lq i ∧ 140 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 140 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 8) (i : Fin 8) (n : ℤ) :
    inner s i (n + 140) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 140 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 140 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 140) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 140) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 140) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
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
  ∑ q : Fin 8 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 140) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 140 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 140 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 3 + r with r < 140: the level is QQ - 0 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 540804 3 k

def uhMV (k : ℕ) : ℕ := ctabN 50372 2 k

def ukPV (k : ℕ) : ℕ := ctabN 8456208 3 k

def ukMV (k : ℕ) : ℕ := ctabN 4626 2 k

def dhV (k : ℕ) : ℕ := ctabN 2019063896 4 k

def dkV (k : ℕ) : ℕ := ctabN 2273675141 4 k

def mhkV (k : ℕ) : ℕ := ctabN 2944315262 4 k

def uh (i : Fin 8) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 8) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 8) : ℤ := dhV i.val

def dk (i : Fin 8) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 0 1 (Nat.add i (Nat.mul 8 s))

def QQ (s i : ℕ) : ℕ := ctabN 2466496668298801198719551395977140067320240274224725252305 3 (Nat.add i (Nat.mul 8 s))

def AH (s i : ℕ) : ℕ := ctabN 135791255350248704752802645597305278109505031267230083696601804207311750565437647928025237426213 5 (Nat.add i (Nat.mul 8 s))

def AK (s i : ℕ) : ℕ := ctabN 869967776788997525340928045018544804760956574668674177629509265655826765356862932030130359932068 5 (Nat.add i (Nat.mul 8 s))

def WH (s i : ℕ) : ℕ := ctabN 38175054673210312027617485467465443367596731843611827721485773518780905193161770002705965399611586946302125744326464 6 (Nat.add i (Nat.mul 8 s))

def WK (s i : ℕ) : ℕ := ctabN 192526487357038019152453128899849925209221078050852559798591793942250064061386974572511329545247802140671185342521 6 (Nat.add i (Nat.mul 8 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 8 fun s => allR 8 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq 11 (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 8) (i : Fin 8) :
    PP s.val i.val < gcV i.val ∧
    (3 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 0) + PP s.val i.val ∧
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

/-- Piece (s, i) at n = 3 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 3 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 8) (i : Fin 8) (r : ℕ) :
    ((3 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (3 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 0) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 8) (i : Fin 8) (r : ℕ) (hr : r < 140) :
    inner s i ((3 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (140 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 140 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((3 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r := by
      rw [lev, show (3 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((3 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((3 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 1401768926155035878624239179825597956165501405433700674158170523105719170501013190840 8 k

def tblV (k : ℕ) : ℕ := ctabN 1401619431744086854164553782052830997430985255406648372782278288475414544992904874757 8 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 35. -/
def dv (t : ℕ) : ℕ := dtabV (t % 35)

/-- The sequence in closed form: b(n + 35) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 35) + tblV ((n - 1) % 35)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 35) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 35 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 35 - 1 = n - 1 + 35 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 35)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 140) = b n + 4 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 140 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 140 - 1 = n - 1 + 35 * 4 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 35)]
  ring

/-- b on the residue class of 1 + j mod 35. -/
theorem b_res (k j : ℕ) (hj : j < 35) : b (35 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (35 * k + (1 + j) < 1) by omega),
    show 35 * k + (1 + j) - 1 = j + 35 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 35), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 3 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 140 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 8 fun s => allR 8 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 8 fun s => sumR 8 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 3 r)) &&
    Nat.beq (sumR 8 fun s => sumR 8 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 4 (dv (Nat.add 2 r)))

/-! The window n = 3, ..., 142, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 23 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 23 23 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 46 23 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK3 : PLift (allI 69 23 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK4 : PLift (allI 92 23 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK5 : PLift (allI 115 23 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK6 : PLift (allI 138 2 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 140) :
    (∀ s, s < 8 → ∀ i, i < 8 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 8 fun s => sumR 8 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (3 + r) ∧
    (sumR 8 fun s => sumR 8 fun i => cond (divN s i r) (mhkV i) 0) = 4 * dv (2 + r) := by
  have h : periodR r = true := by
    rcases (show r < 23 ∨ (23 ≤ r ∧ r < 46) ∨ (46 ≤ r ∧ r < 69) ∨ (69 ≤ r ∧ r < 92) ∨ (92 ≤ r ∧ r < 115) ∨ (115 ≤ r ∧ r < 138) ∨ 138 ≤ r by omega) with h | h | h | h | h | h | h
    · exact allI_get _ _ _ periodK0.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK1.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK2.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK3.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK4.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK5.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK6.down r (by omega) (by omega)
  simp only [periodR, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun s hs i hi hd => ?_, h2, h3⟩
  have h4 := (allR_iff _ _).1 ((allR_iff _ _).1 h1 s hs) i hi
  rw [hd] at h4
  simpa using h4

theorem innerZ_eq (s i r : ℕ) (hs : s < 8) (hi : i < 8) (hr : r < 140) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 8 fun s => sumR 8 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 8 × Fin 8, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 8 fun i => f s i : ℕ) : ℤ)) 8]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 8]

theorem S_window (r : ℕ) (hr : r < 140) : S ((3 : ℤ) + r) = b (3 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 140) : Gs ((3 : ℤ) + r) = ((4 * dv (2 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 3 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 8) (i : Fin 8) (n : ℤ) (hn : 3 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 3 + t := ⟨(n - 3).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 140
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 140) (by omega) (by omega)
      have e : (3 : ℤ) + t = (3 + (t - 140 : ℕ)) + 140 := by
        push_cast [Nat.cast_sub (by omega : 140 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 3 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 140 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 3 ≤ n) : (4 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 3) % 140 < 140 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((3 : ℤ) + (((n - 3) % 140 : ℕ) : ℤ)) + 140 * (((n - 3) / 140 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (2 + (n - 3) % 140) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 3 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 143
    · obtain ⟨r, rfl⟩ : ∃ r, n = 3 + r := ⟨n - 3, by omega⟩
      push_cast
      exact S_window r (by omega)
    · have h1 := ih (n - 140) (by omega) (by omega)
      have h2 := S_shift ((n - 140 : ℕ) : ℤ)
      have h3 := b_shift (n - 140) (by omega)
      have h4 := grow (n - 140) (by omega)
      rw [show n - 140 + 140 = n by omega] at h3
      rw [show ((n - 140 : ℕ) : ℤ) + 140 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 2 lie in the box -2 ≤ x ≤ 2, -1 ≤ y ≤ 1 (`small_box`). In natural-number
coordinates a = x + 2, b = y + 1 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 8) (h : F (x, y, s) ≤ 2) :
    -2 ≤ x ∧ x ≤ 2 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 2, (b : ℤ) - 1, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 24) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 2) (BW i)) 8) (Nat.add (Nat.mul 8 a) (Nat.mul 8 b))

theorem pot_box (a b : ℕ) (s : Fin 8) (i : Fin 8) :
    pot ((a : ℤ) - 2, (b : ℤ) - 1, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 8 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 8) : F ((a : ℤ) - 2, (b : ℤ) - 1, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 2, (b : ℤ) - 1, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 2, (b : ℤ) - 1, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 8 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 8 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 2, (b : ℤ) - 1, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 2, (b : ℤ) - 1, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 2, (b : ℤ) - 1, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 5 fun a => sumR 3 fun b => sumR 8 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 0 .. 2, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 0 3 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 3) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 8) : V := ((q.1 : ℤ) - 2, (q.2.1 : ℤ) - 1, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 2) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 5 ×ˢ (Finset.range 3 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 8 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 2).toNat, (y + 1).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 2).toNat (y + 1).toNat s
        rw [show (((x + 2).toNat : ℕ) : ℤ) - 2 = x by omega,
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 8]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 3 are counted in the
box, those from 3 on are S(n), and both agree with the closed form b (`a_eq_b`). The step from n to
n + 35, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 3 ∨ 3 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_eq n (by omega) h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

def dconst_baseK : PLift (∀ r : ℕ, r < 35 → dtabV r = 184) :=
  ⟨by decide +kernel⟩

theorem dconst_base : ∀ r : ℕ, r < 35 → dtabV r = 184 := dconst_baseK.down

theorem dv_const : ∀ t : ℕ, dv t = 184 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 35) = a(n) + 184 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 35) = a n + 184 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 184 ∧ tblV 0 = 5 ∧ dv 1 = 184 ∧ tblV 1 = 11 ∧ dv 2 = 184 ∧ tblV 2 = 15 ∧ dv 3 = 184 ∧ tblV 3 = 22 ∧ dv 4 = 184 ∧ tblV 4 = 26 ∧ dv 5 = 184 ∧ tblV 5 = 31 ∧ dv 6 = 184 ∧ tblV 6 = 37 ∧ dv 7 = 184 ∧ tblV 7 = 42) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 184 ∧ tblV 8 = 48 ∧ dv 9 = 184 ∧ tblV 9 = 52 ∧ dv 10 = 184 ∧ tblV 10 = 58 ∧ dv 11 = 184 ∧ tblV 11 = 63 ∧ dv 12 = 184 ∧ tblV 12 = 68 ∧ dv 13 = 184 ∧ tblV 13 = 74 ∧ dv 14 = 184 ∧ tblV 14 = 79 ∧ dv 15 = 184 ∧ tblV 15 = 84) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 184 ∧ tblV 16 = 89 ∧ dv 17 = 184 ∧ tblV 17 = 95 ∧ dv 18 = 184 ∧ tblV 18 = 100 ∧ dv 19 = 184 ∧ tblV 19 = 105 ∧ dv 20 = 184 ∧ tblV 20 = 110 ∧ dv 21 = 184 ∧ tblV 21 = 116 ∧ dv 22 = 184 ∧ tblV 22 = 121 ∧ dv 23 = 184 ∧ tblV 23 = 126) :=
  ⟨by decide +kernel⟩

def closedK3 : PLift (dv 24 = 184 ∧ tblV 24 = 132 ∧ dv 25 = 184 ∧ tblV 25 = 136 ∧ dv 26 = 184 ∧ tblV 26 = 142 ∧ dv 27 = 184 ∧ tblV 27 = 147 ∧ dv 28 = 184 ∧ tblV 28 = 153 ∧ dv 29 = 184 ∧ tblV 29 = 158 ∧ dv 30 = 184 ∧ tblV 30 = 162 ∧ dv 31 = 184 ∧ tblV 31 = 169) :=
  ⟨by decide +kernel⟩

def closedK4 : PLift (dv 32 = 184 ∧ tblV 32 = 173 ∧ dv 33 = 184 ∧ tblV 33 = 179 ∧ dv 34 = 184 ∧ tblV 34 = 184) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (35 * k + 1) = 184 * k + 5 ∧
    a (35 * k + 2) = 184 * k + 11 ∧
    a (35 * k + 3) = 184 * k + 15 ∧
    a (35 * k + 4) = 184 * k + 22 ∧
    a (35 * k + 5) = 184 * k + 26 ∧
    a (35 * k + 6) = 184 * k + 31 ∧
    a (35 * k + 7) = 184 * k + 37 ∧
    a (35 * k + 8) = 184 * k + 42 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 35 * k + 1 = 35 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 35 * k + 2 = 35 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 35 * k + 3 = 35 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 35 * k + 4 = 35 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 35 * k + 5 = 35 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 35 * k + 6 = 35 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 35 * k + 7 = 35 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 35 * k + 8 = 35 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (35 * k + 9) = 184 * k + 48 ∧
    a (35 * k + 10) = 184 * k + 52 ∧
    a (35 * k + 11) = 184 * k + 58 ∧
    a (35 * k + 12) = 184 * k + 63 ∧
    a (35 * k + 13) = 184 * k + 68 ∧
    a (35 * k + 14) = 184 * k + 74 ∧
    a (35 * k + 15) = 184 * k + 79 ∧
    a (35 * k + 16) = 184 * k + 84 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 35 * k + 9 = 35 * k + (1 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 35 * k + 10 = 35 * k + (1 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 35 * k + 11 = 35 * k + (1 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 35 * k + 12 = 35 * k + (1 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 35 * k + 13 = 35 * k + (1 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 35 * k + 14 = 35 * k + (1 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 35 * k + 15 = 35 * k + (1 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 35 * k + 16 = 35 * k + (1 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (35 * k + 17) = 184 * k + 89 ∧
    a (35 * k + 18) = 184 * k + 95 ∧
    a (35 * k + 19) = 184 * k + 100 ∧
    a (35 * k + 20) = 184 * k + 105 ∧
    a (35 * k + 21) = 184 * k + 110 ∧
    a (35 * k + 22) = 184 * k + 116 ∧
    a (35 * k + 23) = 184 * k + 121 ∧
    a (35 * k + 24) = 184 * k + 126 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 35 * k + 17 = 35 * k + (1 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 35 * k + 18 = 35 * k + (1 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 35 * k + 19 = 35 * k + (1 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 35 * k + 20 = 35 * k + (1 + 19) from rfl, b_res k 19 (by decide), c38, c39]
  · rw [show 35 * k + 21 = 35 * k + (1 + 20) from rfl, b_res k 20 (by decide), c40, c41]
  · rw [show 35 * k + 22 = 35 * k + (1 + 21) from rfl, b_res k 21 (by decide), c42, c43]
  · rw [show 35 * k + 23 = 35 * k + (1 + 22) from rfl, b_res k 22 (by decide), c44, c45]
  · rw [show 35 * k + 24 = 35 * k + (1 + 23) from rfl, b_res k 23 (by decide), c46, c47]

theorem a_closed3 (k : ℕ) :
    a (35 * k + 25) = 184 * k + 132 ∧
    a (35 * k + 26) = 184 * k + 136 ∧
    a (35 * k + 27) = 184 * k + 142 ∧
    a (35 * k + 28) = 184 * k + 147 ∧
    a (35 * k + 29) = 184 * k + 153 ∧
    a (35 * k + 30) = 184 * k + 158 ∧
    a (35 * k + 31) = 184 * k + 162 ∧
    a (35 * k + 32) = 184 * k + 169 := by
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := closedK3.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 35 * k + 25 = 35 * k + (1 + 24) from rfl, b_res k 24 (by decide), c48, c49]
  · rw [show 35 * k + 26 = 35 * k + (1 + 25) from rfl, b_res k 25 (by decide), c50, c51]
  · rw [show 35 * k + 27 = 35 * k + (1 + 26) from rfl, b_res k 26 (by decide), c52, c53]
  · rw [show 35 * k + 28 = 35 * k + (1 + 27) from rfl, b_res k 27 (by decide), c54, c55]
  · rw [show 35 * k + 29 = 35 * k + (1 + 28) from rfl, b_res k 28 (by decide), c56, c57]
  · rw [show 35 * k + 30 = 35 * k + (1 + 29) from rfl, b_res k 29 (by decide), c58, c59]
  · rw [show 35 * k + 31 = 35 * k + (1 + 30) from rfl, b_res k 30 (by decide), c60, c61]
  · rw [show 35 * k + 32 = 35 * k + (1 + 31) from rfl, b_res k 31 (by decide), c62, c63]

theorem a_closed4 (k : ℕ) :
    a (35 * k + 33) = 184 * k + 173 ∧
    a (35 * k + 34) = 184 * k + 179 ∧
    a (35 * k + 35) = 184 * k + 184 := by
  obtain ⟨c64, c65, c66, c67, c68, c69⟩ := closedK4.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_⟩
  · rw [show 35 * k + 33 = 35 * k + (1 + 32) from rfl, b_res k 32 (by decide), c64, c65]
  · rw [show 35 * k + 34 = 35 * k + (1 + 33) from rfl, b_res k 33 (by decide), c66, c67]
  · rw [show 35 * k + 35 = 35 * k + (1 + 34) from rfl, b_res k 34 (by decide), c68, c69]

/-- The closed form per residue of n mod 35, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (35 * k + 1) = 184 * k + 5 ∧
    a (35 * k + 2) = 184 * k + 11 ∧
    a (35 * k + 3) = 184 * k + 15 ∧
    a (35 * k + 4) = 184 * k + 22 ∧
    a (35 * k + 5) = 184 * k + 26 ∧
    a (35 * k + 6) = 184 * k + 31 ∧
    a (35 * k + 7) = 184 * k + 37 ∧
    a (35 * k + 8) = 184 * k + 42 ∧
    a (35 * k + 9) = 184 * k + 48 ∧
    a (35 * k + 10) = 184 * k + 52 ∧
    a (35 * k + 11) = 184 * k + 58 ∧
    a (35 * k + 12) = 184 * k + 63 ∧
    a (35 * k + 13) = 184 * k + 68 ∧
    a (35 * k + 14) = 184 * k + 74 ∧
    a (35 * k + 15) = 184 * k + 79 ∧
    a (35 * k + 16) = 184 * k + 84 ∧
    a (35 * k + 17) = 184 * k + 89 ∧
    a (35 * k + 18) = 184 * k + 95 ∧
    a (35 * k + 19) = 184 * k + 100 ∧
    a (35 * k + 20) = 184 * k + 105 ∧
    a (35 * k + 21) = 184 * k + 110 ∧
    a (35 * k + 22) = 184 * k + 116 ∧
    a (35 * k + 23) = 184 * k + 121 ∧
    a (35 * k + 24) = 184 * k + 126 ∧
    a (35 * k + 25) = 184 * k + 132 ∧
    a (35 * k + 26) = 184 * k + 136 ∧
    a (35 * k + 27) = 184 * k + 142 ∧
    a (35 * k + 28) = 184 * k + 147 ∧
    a (35 * k + 29) = 184 * k + 153 ∧
    a (35 * k + 30) = 184 * k + 158 ∧
    a (35 * k + 31) = 184 * k + 162 ∧
    a (35 * k + 32) = 184 * k + 169 ∧
    a (35 * k + 33) = 184 * k + 173 ∧
    a (35 * k + 34) = 184 * k + 179 ∧
    a (35 * k + 35) = 184 * k + 184 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15⟩ := a_closed1 k
  obtain ⟨x16, x17, x18, x19, x20, x21, x22, x23⟩ := a_closed2 k
  obtain ⟨x24, x25, x26, x27, x28, x29, x30, x31⟩ := a_closed3 k
  obtain ⟨x32, x33, x34⟩ := a_closed4 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34⟩

def controlsK : PLift ((List.range 50).map b = [1, 5, 11, 15, 22, 26, 31, 37, 42, 48, 52, 58, 63, 68, 74, 79, 84, 89, 95, 100, 105, 110, 116, 121, 126, 132, 136, 142, 147, 153, 158, 162, 169, 173, 179, 184, 189, 195, 199, 206, 210, 215, 221, 226, 232, 236, 242, 247, 252, 258]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 11, 15, 22, 26, 31, 37, 42, 48, 52, 58, 63, 68, 74, 79, 84, 89, 95, 100, 105, 110, 116, 121, 126, 132, 136, 142, 147, 153, 158, 162, 169, 173, 179, 184, 189, 195, 199, 206, 210, 215, 221, 226, 232, 236, 242, 247, 252, 258] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 35 → dv (t + 12) + dv (t + 0) = dv (t + 7) + dv (t + 5)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 35 → dv (t + 12) + dv (t + 0) = dv (t + 7) + dv (t + 5) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 12) : ℤ) = (dv (t + 7) : ℤ) + (dv (t + 5) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 35 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 5, e 7, e 12]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 35) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 35 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 35 → b (q + 13) + b (q + 1) = b (q + 8) + b (q + 6)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 35 → b (q + 13) + b (q + 1) = b (q + 8) + b (q + 6) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 13) : ℤ) = b (q + 8) + b (q + 6) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 35 ∨ 35 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 35 := ⟨q - 35, by omega⟩
      have h0 : (b (v + 13) : ℤ) = b (v + 8) + b (v + 6) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 36) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 35 = v + 36 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s6 : (b (v + 41) : ℤ) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (le_trans (by decide : 1 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 35 = v + 41 from Nat.add_assoc _ _ _,
          show v + 6 - 1 = v + 5 from Nat.add_sub_assoc (by decide : 1 ≤ 6) v] at h
        exact_mod_cast h
      have s8 : (b (v + 43) : ℤ) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (le_trans (by decide : 1 ≤ 8) (Nat.le_add_left _ v))
        rw [show v + 8 + 35 = v + 43 from Nat.add_assoc _ _ _,
          show v + 8 - 1 = v + 7 from Nat.add_sub_assoc (by decide : 1 ≤ 8) v] at h
        exact_mod_cast h
      have s13 : (b (v + 48) : ℤ) = b (v + 13) + dv (v + 12) := by
        have h := b_step (v + 13) (le_trans (by decide : 1 ≤ 13) (Nat.le_add_left _ v))
        rw [show v + 13 + 35 = v + 48 from Nat.add_assoc _ _ _,
          show v + 13 - 1 = v + 12 from Nat.add_sub_assoc (by decide : 1 ≤ 13) v] at h
        exact_mod_cast h
      show (b (v + 48) : ℤ) = b (v + 43) + b (v + 41) - b (v + 36)
      linear_combination s13 - (1) * s8 - (1) * s6 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 5) + a (n - 7) - a (n - 12) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 13 := ⟨n - 13, by omega⟩
  rw [show q + 13 - 5 = q + 8 from Nat.add_sub_assoc (by decide : 5 ≤ 13) q, show q + 13 - 7 = q + 6 from Nat.add_sub_assoc (by decide : 7 ≤ 13) q, show q + 13 - 12 = q + 1 from Nat.add_sub_assoc (by decide : 12 ≤ 13) q]
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

/-- The coefficients of A * DEN and NUM agree below 13, in natural numbers (negative terms moved
across). -/
def gfL (n : ℕ) : ℕ := Nat.add (b n) (bk n 12)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (bk n 5) (bk n 7)) (ind n 0)) (Nat.mul 5 (ind n 1))) (Nat.mul 11 (ind n 2))) (Nat.mul 15 (ind n 3))) (Nat.mul 22 (ind n 4))) (Nat.mul 25 (ind n 5))) (Nat.mul 26 (ind n 6))) (Nat.mul 25 (ind n 7))) (Nat.mul 22 (ind n 8))) (Nat.mul 15 (ind n 9))) (Nat.mul 11 (ind n 10))) (Nat.mul 5 (ind n 11))) (ind n 12)

def gfK : PLift ((allR 13 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 13, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 13) :
    1 * (b (n) : ℚ) - 1 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) - 1 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) + 1 * (if 12 ≤ n then (b (n - 12) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 5 + (if n = 2 then (1 : ℚ) else 0) * 11 + (if n = 3 then (1 : ℚ) else 0) * 15 + (if n = 4 then (1 : ℚ) else 0) * 22 + (if n = 5 then (1 : ℚ) else 0) * 25 + (if n = 6 then (1 : ℚ) else 0) * 26 + (if n = 7 then (1 : ℚ) else 0) * 25 + (if n = 8 then (1 : ℚ) else 0) * 22 + (if n = 9 then (1 : ℚ) else 0) * 15 + (if n = 10 then (1 : ℚ) else 0) * 11 + (if n = 11 then (1 : ℚ) else 0) * 5 + (if n = 12 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 13 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 13) : ℚ) - 1 * (if 5 ≤ q + 13 then (b (q + 13 - 5) : ℚ) else 0) - 1 * (if 7 ≤ q + 13 then (b (q + 13 - 7) : ℚ) else 0) + 1 * (if 12 ≤ q + 13 then (b (q + 13 - 12) : ℚ) else 0) =
      (if q + 13 = 0 then (1 : ℚ) else 0) * 1 + (if q + 13 = 1 then (1 : ℚ) else 0) * 5 + (if q + 13 = 2 then (1 : ℚ) else 0) * 11 + (if q + 13 = 3 then (1 : ℚ) else 0) * 15 + (if q + 13 = 4 then (1 : ℚ) else 0) * 22 + (if q + 13 = 5 then (1 : ℚ) else 0) * 25 + (if q + 13 = 6 then (1 : ℚ) else 0) * 26 + (if q + 13 = 7 then (1 : ℚ) else 0) * 25 + (if q + 13 = 8 then (1 : ℚ) else 0) * 22 + (if q + 13 = 9 then (1 : ℚ) else 0) * 15 + (if q + 13 = 10 then (1 : ℚ) else 0) * 11 + (if q + 13 = 11 then (1 : ℚ) else 0) * 5 + (if q + 13 = 12 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 13) : ℤ) = b (q + 8) + b (q + 6) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 13 - 5 = q + 8 from Nat.add_sub_assoc (by decide : 5 ≤ 13) q, show q + 13 - 7 = q + 6 from Nat.add_sub_assoc (by decide : 7 ≤ 13) q, show q + 13 - 12 = q + 1 from Nat.add_sub_assoc (by decide : 12 ≤ 13) q, show 5 ≤ q + 13 from le_trans (by decide : 5 ≤ 13) (Nat.le_add_left 13 q), show 7 ≤ q + 13 from le_trans (by decide : 7 ≤ 13) (Nat.le_add_left 13 q), show 12 ≤ q + 13 from le_trans (by decide : 12 ≤ 13) (Nat.le_add_left 13 q), show ¬ q + 13 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 13) (Nat.le_add_left 13 q)), show ¬ q + 13 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 13) (Nat.le_add_left 13 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * (X ^ 12 - X ^ 7 - X ^ 5 + 1) = C 1 * A - C 1 * (A * X ^ 5) - C 1 * (A * X ^ 7) + C 1 * (A * X ^ 12) := by
  simp only [map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (X ^ 12 + 5 * X ^ 11 + 11 * X ^ 10 + 15 * X ^ 9 + 22 * X ^ 8 + 25 * X ^ 7 + 26 * X ^ 6 + 25 * X ^ 5 + 22 * X ^ 4 + 15 * X ^ 3 + 11 * X ^ 2 + 5 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 5 + X ^ 2 * C 11 + X ^ 3 * C 15 + X ^ 4 * C 22 + X ^ 5 * C 25 + X ^ 6 * C 26 + X ^ 7 * C 25 + X ^ 8 * C 22 + X ^ 9 * C 15 + X ^ 10 * C 11 + X ^ 11 * C 5 + X ^ 12 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 12 - X ^ 7 - X ^ 5 + 1) =
      X ^ 12 + 5 * X ^ 11 + 11 * X ^ 10 + 15 * X ^ 9 + 22 * X ^ 8 + 25 * X ^ 7 + 26 * X ^ 6 + 25 * X ^ 5 + 22 * X ^ 4 + 15 * X ^ 3 + 11 * X ^ 2 + 5 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  rw [gf_den A, gf_num]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 13 with hn | hn
  · linarith [gf_low n hn]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 13 := ⟨n - 13, by omega⟩
    linarith [gf_high q]

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 12 - X ^ 7 - X ^ 5 + 1) =
      X ^ 12 + 5 * X ^ 11 + 11 * X ^ 10 + 15 * X ^ 9 + 22 * X ^ 8 + 25 * X ^ 7 + 26 * X ^ 6 + 25 * X ^ 5 + 22 * X ^ 4 + 15 * X ^ 3 + 11 * X ^ 2 + 5 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 5) + a (n - 7) - a (n - 12) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 11, 15, 22, 26, 31, 37, 42, 48, 52, 58, 63, 68, 74, 79, 84, 89, 95, 100, 105, 110, 116, 121, 126, 132, 136, 142, 147, 153, 158, 162, 169, 173, 179, 184, 189, 195, 199, 206, 210, 215, 221, 226, 232, 236, 242, 247, 252, 258] := Count.controls

/-- The step a(n + 35) = a(n) + 184 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 35) = a n + 184 := Count.a_step n hn

/-- The closed form per residue of n mod 35, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (35 * k + 1) = 184 * k + 5 ∧
    a (35 * k + 2) = 184 * k + 11 ∧
    a (35 * k + 3) = 184 * k + 15 ∧
    a (35 * k + 4) = 184 * k + 22 ∧
    a (35 * k + 5) = 184 * k + 26 ∧
    a (35 * k + 6) = 184 * k + 31 ∧
    a (35 * k + 7) = 184 * k + 37 ∧
    a (35 * k + 8) = 184 * k + 42 ∧
    a (35 * k + 9) = 184 * k + 48 ∧
    a (35 * k + 10) = 184 * k + 52 ∧
    a (35 * k + 11) = 184 * k + 58 ∧
    a (35 * k + 12) = 184 * k + 63 ∧
    a (35 * k + 13) = 184 * k + 68 ∧
    a (35 * k + 14) = 184 * k + 74 ∧
    a (35 * k + 15) = 184 * k + 79 ∧
    a (35 * k + 16) = 184 * k + 84 ∧
    a (35 * k + 17) = 184 * k + 89 ∧
    a (35 * k + 18) = 184 * k + 95 ∧
    a (35 * k + 19) = 184 * k + 100 ∧
    a (35 * k + 20) = 184 * k + 105 ∧
    a (35 * k + 21) = 184 * k + 110 ∧
    a (35 * k + 22) = 184 * k + 116 ∧
    a (35 * k + 23) = 184 * k + 121 ∧
    a (35 * k + 24) = 184 * k + 126 ∧
    a (35 * k + 25) = 184 * k + 132 ∧
    a (35 * k + 26) = 184 * k + 136 ∧
    a (35 * k + 27) = 184 * k + 142 ∧
    a (35 * k + 28) = 184 * k + 147 ∧
    a (35 * k + 29) = 184 * k + 153 ∧
    a (35 * k + 30) = 184 * k + 158 ∧
    a (35 * k + 31) = 184 * k + 162 ∧
    a (35 * k + 32) = 184 * k + 169 ∧
    a (35 * k + 33) = 184 * k + 173 ∧
    a (35 * k + 34) = 184 * k + 179 ∧
    a (35 * k + 35) = 184 * k + 184 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 12 - X ^ 7 - X ^ 5 + 1) =
      X ^ 12 + 5 * X ^ 11 + 11 * X ^ 10 + 15 * X ^ 9 + 22 * X ^ 8 + 25 * X ^ 7 + 26 * X ^ 6 + 25 * X ^ 5 + 22 * X ^ 4 + 15 * X ^ 3 + 11 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 5) + a (n - 7) - a (n - 12) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a314065

theorem OMA.solution : type_of% @OMA.S_oeis_a314065.main :=
  OMA.S_oeis_a314065.conjecture
