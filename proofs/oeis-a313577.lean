import OMAStatements.S_oeis_a313577

namespace OMA.S_oeis_a313577






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 12

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 655107786905
  | 1 => 596140123205
  | 2 => 522839487830
  | 3 => 591272638055
  | 4 => 449842939205
  | 5 => 523143574580
  | 6 => 586406201480
  | 7 => 518259312230
  | 8 => 445262763605
  | 9 => 513409652855
  | 10 => 444976502630
  | 11 => 586692462455
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 10) : ℤ := tget 371694741605 4 8 i.val

def Bc (i : Fin 10) : ℤ := tget 600720298805 4 8 i.val

def Cc (s : Fin 12) (i : Fin 10) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 371694741605 4 i

def BcN (i : ℕ) : ℕ := tgetN 600720298805 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 10) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 10) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 12) (i : Fin 10) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


/-- The potential of facet i at v (facets in angular order around the growth polygon). -/
def pot (v : V) (i : Fin 10) : ℤ := Ac i * v.1 + Bc i * v.2.1 + Cc v.2.2 i

/-- The largest facet potential at v. -/
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

/-- A statement about every vertex class follows from the statements about each class. -/
theorem cls (P : Fin 12 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 12 × Fin 12 × ℤ × ℤ) (j : Fin 10) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 10, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
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
theorem shift (x y : ℤ) (e : Fin 12 × Fin 12 × ℤ × ℤ) (j : Fin 10) :
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
theorem farkas (x y : ℤ) (s : Fin 12) (a1 b1 a2 b2 a3 b3 i0 : Fin 10) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
adjacent to i, the fields k1, k2, m1, m2, m0, mj of entry i * 10 + j give the facts pot k1 ≤ pot i,
pot k2 ≤ pot i, 8 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 304293274289739054663731331924665016771534336790186617685394298476593479448328079623600937429679795807210431453218681315589332667667480640464605339040559690057019577296478222168795725715913799055795963902666706719557995882236582115811988183883553149231749997222644813768968423560468792830061095482438861845818021771012232622345229507798716468270169251740138503091729843960386444080578160039448972882489386329511192612132552783265031868919587351684152566622488358220055446356614667529587723983774295106031803518791699397908771118364952277718237182701229437700164180469386807786114019495100496136705479394574303863105846266849180523157398032795406680119254470149254005996873490812674772421010821937278822708493975516049306728838428193512612331073059084046905760600371364266765867912268486558559850457236884001344571344735836732766584228331716320166416421861708702819579584419330208563200 5 ((i * 10 + j) * 6 + f)

def fd (i j : Fin 10) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 0 % 10, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 1 % 10, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 10) : ℤ := fd i j 2

def fm2 (i j : Fin 10) : ℤ := fd i j 3

def fm0 (i j : Fin 10) : ℤ := fd i j 4

def fmj (i j : Fin 10) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 10 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 19770625841841587309696990304401854233925011115948758154008301928448 4 p

def dstv (p : ℕ) : ℕ := tgetN 16056103163310691213025056747532895888864931442916997104890683233873 4 p

def dxv (p : ℕ) : ℕ := tgetN 1406271830703319366676009272562705 2 p

def dyv (p : ℕ) : ℕ := tgetN 1730765600168796078805192231246160 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 94669977555292567665627078329608512017553410693294177301651694356143111636086066425505981001922030433376677493468191012663488880828615267034753557112458266711036931883052582440545394298892360503358438078977805014810420459236210712478551431023083809609185915344450384898718230380822672012682741222469441434076071084191136533033710052580371180457734540488808150859598013993478851972892033266537726453238635709641129435995816557441006916032807690091833372150347801019707856392854766174805131889351435441911466932519480122290490285670385522195661518056880846269072757300776151026085473602273973922284473321914317302741256327411555677635572538030841557792105157522356097414437255 4 (p * 10 + j)

def dlv (p : ℕ) (j : Fin 10) : ℤ := (dlvN p j.val : ℤ) - 8

theorem dlv_neg (p : ℕ) (j : Fin 10) (h : dlvN p j.val + 1 ≤ 8) : dlv p j ≤ -1 := by
  unfold dlv
  omega

theorem dlv_le (p : ℕ) (j : Fin 10) (c : ℕ) (h : dlvN p j.val + 1 ≤ c + 8) : dlv p j ≤ (c : ℤ) - 1 := by
  unfold dlv
  omega

/-- The next and the previous facet around the growth polygon. -/
def nxt (i : Fin 10) : Fin 10 := ⟨(i.val + 1) % 10, Nat.mod_lt _ (by norm_num)⟩

def prv (i : Fin 10) : Fin 10 := ⟨(i.val + 9) % 10, Nat.mod_lt _ (by norm_num)⟩

/-- The facets i and j are not equal and not adjacent sides of the growth polygon. -/
def nonadj (i j : Fin 10) : Prop := j ≠ i ∧ j ≠ nxt i ∧ j ≠ prv i

instance : DecidableRel nonadj := fun i j => by unfold nonadj; infer_instance

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 8). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 10) + fdN i j 3 * AcN (fdN i j 1 % 10) + fdN i j 5 * AcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 10) + fdN i j 3 * BcN (fdN i j 1 % 10) + fdN i j 5 * BcN i + fdN i j 4 * 8 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * BcN i + fdN i j 5 * BcN j)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farCN (s i j : ℕ) : Bool :=
  Nat.blt ((fdN i j 2 + fdN i j 3 + fdN i j 4) * CcN s i + fdN i j 5 * (CcN s j + 1))
    (fdN i j 2 * CcN s (fdN i j 0 % 10) + fdN i j 3 * CcN s (fdN i j 1 % 10) + fdN i j 5 * CcN s i +
      fdN i j 4 * 16)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 10 || j == (i + 9) % 10

def farOK : Bool := (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 12).all fun s => (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 56).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 10).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 12) (i j : Fin 10) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (8 - Cc s i)

/-- Beyond F = 7, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 12) (i j : Fin 10) (hc : farCert s i j) (x y : ℤ)
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
  | 0 => 3942392526586267560749522354203469798744170920706916008405334897295684589865888037835268714504975584063352994989071255607513350652364062924283113865669346223199530755635364343827615736957073398405193317622039613125449801378510354331189981100566277068887852903570787211551368833077816431369490462877509303799698400064769987815973802411439114764218608962875143466629177707083184894259635056249858171171250247690230736791995360246063451073145965982752330514541301293456499544087952066713404257042405741643926180596002860092141150674199114520447662330966148521896105860244313096431608855773994170305527826849064101973718010959736638533864373552802216169819957199112383448886094167321238282709039354235135891495835527072208025934353856641313877546529512153038168892125365981974522755784333228381912362816816720066388200857080513571730416100783914940445024085082738766342686543656271891172037301622670867403732154304868903237141155921454362821041695063190046637027874967840865762885356114596067187278369020759566056285244391032162262344253036794929661169505483100315784980041674512721685312864639566365350027102291851554374315057696019852566848
  | 1 => 3942392527952375489656043790012109967969929714840695087970558986893811504524904467448649398721561400956493743770952476718029462756244000542970467508538972633751323185833076505166846003052836655871649265952722886019726421930526484870297944138106985827592926668810858352313908893617855205580681162365131740736553491756531964353820724041905236333026706765814317887496529599075902607055106781817645346271486806884825349494025780383782576723442251470138217394492727656506802705294706142438867384312204610728848844647848567985860803391488346677160675045119730660986454220906229708956240617389135009301202117154990960129564442103041990676308518110663952426502624467860255908274422438479309671971355850204215241588791370974765848970553568177967029710522583972257682819482397555981449375835937076042556581518840593378376674395741885262997636067124783978081833093645571426674297890890932054459248943205069736513132777470497157821222061199129194767412782175943431517480796110294590577919106998498050746511563802267674537588575821274346251058105858565408665613297369703735628945352431136168688256677002593582267721260582610561657762403930126343480256
  | 2 => 3942392529090798763744811653185976775658062043280604217140613877610400040148157017847476109910231548760939708962127925826124472369734040093634628293545732648388488266598292579605199301851217497296849597769672393642823848798197257666820336422165225498878661202738843668550737516706433254969402954445672538627340060105852860818446697447902184863743472437606367743159675036335062429016831945562302821385731253598367591778569477745145270846660095009231934941897623453564817514344318174781971218767212985938258024606860568094528417703024728134311748113434128630849182683284464291966008843514814964526386319999550055636096709806910578459423482711547730082381555938794907300474224923626486705345464551947339260071415335702447842727941838998600190145219858850892100355812067001584752813847983691190265495419530309277594036967857804288626954409692674659268577077653337055511798107419252476742168650791993575243285474591206758271282008647747796867625482607229027719741226583865107613038611180966033468046127684690989733290162378572004541509303930945745351981260901613579801444193727994383347191011377720531150678327225796415336785871018585633072576
  | 3 => 3942392529546168073380318798455523522275356504786543588272998403835425081891580737112562960663348607414434746129606694335819249552529609937711580648760189126653714559394227884669479859446415283697194060176190068806289991781107796592511662261345523649438163092175170774800802998121809544108519825020494686657733833746385565836663363054954925186072996037906125040715648980677815086259913152320895938669470162693476316088240487720245122658957003944267019291067101648284190886547753989510949361965760016812002384432746398796964248775144449976134590037817198842776593542326224587528773835947990211649402238523105177340615779748888933707787787123025191635350488305586859523811944777698974870039237787231663432710820589237306016498003086235429960681291780070703627155651813545946756418531347071266143385325432532888570570376507524741144543336538835852580415683893294903798242563706718396858103420778201455123968199150601996049847769913019647898355427185366339580142278618740123396083846821420915750929195254634696251701076584073392706664094032763025819546981141649162468512233248357629920392834950296863526582815040302227064549171360978630092480
  | 4 => 3942392530912276002286840234264163667959073768788741096220816772384738549444352639674536033841326795813730046397078231439659833618730387125890275150150080061309400005227667915077469910105297879908537996349703584602493097222201190183014562659564009298817898478473103200632570217654601611863915187017731030409189514877102940934421599377257319536944566094225305925069644261140638082485985950852660915442337302471014701406483348186291206297398931691082703575257310278796900051831886100319864037464038461681294669135381063052783783137003455813618574397254241472356370175381582419369003503682256651772398910407196717243253191244971291381989044197191347803440812582034863283071087069204980420674184905610597152423022180951895202500305539709882595389621625817348155425003372376901162938363207229377542705397211866565587012719029184873489630233904787501000596723614112248657872852187770281244198260775254467162928262467822413028051770483794620251916288487918571989235862602049118860921282522958868026898815735029553318089555614054433077845696407089378672369460426919402854291182304334785436812117207428435778601799704778979303561475390697746096193
  | 5 => 3942392531595329966740100952168483776113994695983197577238226660457446998271369959042242250516215292714522489316864742547018470493709175436589894690649370649424920169222866724967104035657629391844318575453160618576755001677599136388345100327266374116290982936356890535170445177649393681584401851542372395999888848302619250965640286979836255668977503524247134671025610036056901563498108606926368313132445470664810092857380013735443557462925381622427137465364131123276947497492098523732616450311775771148465931348026108572922682008870402863106320197761629005796533502583121627026953445841082387558398693484665263388271139007174528073975588178640859289690287181580644970846230716225197613859691327921617494768067515000021971519416266426581948008694240511564916403265457604249245975653931730021899430680715320300072239445575973469552032469331670956416768184890871266665516734899857672335204250150765027576363254112590063054259775378234867198069399970723734814861623236005449391118814218248039972858133605183565768111683871568146653300766204421766351719743283311959317482031726625030194477902806286316334785809425590369867749240532257404365632
  | 6 => 3942392532961437895646622387977123921797711959985395085186045029005869372402572714229978448263808948748119176011397325254886745199588124417890331849167657596618292298644348824446855430157419547756302786138007025031444681143351794893481490675665532350183027100728405835538309643395199580138520085468003758693618205589020081803009325414884584457400811723897379098897122869603386850831261800486023076143189870099522220334470077492816029867391664082454681549003653606382255769605563291186633474256445384996563095256355096213497933229546117150291868586617703254120393173509557541009848628717115785399516377517939797971512551080683156269924791903147422257101587391888399398340997659245436961614254347208864086428343552268708360462385103829195352695575521435208889982187286242851630383143685204762459861315411506131751569511945785097330941762085467960398327928955459119494752665576282512257415654667708658060800309249696948336353210876634041427003895581266565865965630445439892398707422738248073492173281815565717618089979638713667082001823893137839687995878315540358687521337999123929877659471316313810894396698035387332447125924319298914889280
  | 7 => 3942392534099861169735390251150990729485844288427980634611171838239830940712694977871890900720743478156113136908241266263346715804473994432337657149260266566199915818757801977894504133917582686405985541559599097458347642483457832955312444289531114345802254709234473973390179003233464853413532083921120885411533567839582564748102423240458443669842810089602544579978548649699760741262376151909004000315505905141062732948001841760971495945614439267822288317506615974492311096874550350718974623643107624476799245716244477622788290294859297808526397791438996395945555834620092918555243690400670649201158164367911637941316140727051176936215185346319862230134094174646867152606425058868342978090512535893006650569833633439900241698527440668167258326829724695958103499978584224392411008307303546679717014149099141506104950880174378121004806187551235542912235128130196752038879607792229203386826158326597587832840499585681469739653426894509334634468304551065415325593088492540071803300693352704783634390209442780156047982405159670858020481038464565689705091936971007279696523239322777210068989455110238087986804986174708295316938629932477722931392
  | 8 => 3942392534782915134188650969055310861182806745751342266990915528843088710537517963673682111735590689581504419063830015081044350013940590741459606002553887763980117765511083369111121582885713510326812453260538584510283404749289310462573273307709901583557010609032270450955485637873338776286551607335903423875792658998310601715872181471786572664942957470329278649827695311797061793648819296964537183299373223729445228679138977258965026230732606272241464934789362634709107749900379761090730908172515622602708519274629788768695851489552477208604595080987696125867957875412927833455831227226552581269136253267708095926274529377983124336248148692256058465913238740584738080767232609419238641485948285154536384346615681600177553493011486567528411715226375064165254566454911570854547183612980431343978743944808194068901631234602375419590129379181844355924727205033935423692031285681706770722948096776365555448555479214418387247107781865613375235224738170085289566986468367428472749641793519657988230730959440472364706379607730191161248358080619272484370791814701533082275092118367848245326896839976650163117663109170780071034638100595170379575872
  | 9 => 3942392535921338408277418832229177621786856013936117513691374733014169450008890599698950824651838725208903474343191571876882077053470341464593304005883733445404071292270350849999705891032624573354762248392299717027629052761840372976355439741109622407718029281746750933961631491952922901325932389463645365875917126471341584767085773206786876992738680714565305926095080011576401030681834510096288651440513603548660313678848703218966182534912720083277493851149894576077418026544042299178086511469583178105764471847470610427105347275984530835250327888121202616783216353131216277276317178829342532487248062482621991061398174747842447717657802798618112485044971240451688165685406450136723817005268119313644649629028360361501119071196797097142923196826423361285191425818618689574302815237035266200744726212859045754029946661746437234977476540258999940866024530578283824947926805476399137652757231424614100858147438933220528118239034848039330475467200351247956115024718970669301622715448431236625099426557439179649256593729938945566451311211050883317105293199647490245402261519296358965205081783428285868014976700161554778428721875586832512595520
  | 10 => 3942392537287446337183940268037817791012614808067220173001526904094923331981037316069245767600160160498496227419404301087033228165954448619497493133648391434728161548236652395696709603305644029259647464865670996508487954432282403389189239033343797958824047734018650386302096425713436262365654402073494321034001513138343690439873848715105657554178243347263179070215819874696699446117294012031414455395214404247816611237803425828250740939951807313734995703800839813135891202658549978088593911967515602331127924107138410706713245279291693655117038822404143451777408695112414568666498753285600472549606740119579761556821491925516811736808629752808589748879502540328020363816048351026658932200058155127872755772712283320588122831129997012490116712054515911287559249572951933961275503705795942966382921965157406021101073782785210283214035994664569871101285768039536446787477838150127100107698231794414406922598437025754439387392470860565194916922163386446315849607713297630025445712407443060146703428508703899666874854521232028574222094475664158409501543125894101865748129493483024419656577098821392845338473495251455890157030760173375281324097
  | 11 => 3942392538653554266090461703846457983780415132327227983674012877707117628372558846247862580318824842678396908006767683143377042659229211527910024855821019606267760132128400899123334508898802961927497155224265684885083721578726595982660613563631025830825376228643881188086388282236713966353558730769456059969338211521870304756465996615248455088655265274902295585451857020748435718012838804809666292408013317630767685441827231288223578998118228070452844084319899743517642014479543750310846123233144284412837583154601648581333069216708368681127015541633724279716738577955902348983541308902754896960806730174748934726027197422295590667886264680049874701498797808782666466991726918047792982190620395611076326233346645031854466175381436906606242152985887349683378469821495413493972553137443276660783559366999572691599483991531587312542735912053114344756061253415163961492541419508124125136281326059146288325645854827017818203613661863469470726147529321034050490421022208506526497427371755228990941448552232786728245647771504724325674401420795506902616107489161154225465724206132838567716853625302817624346125008423740057402658922758953031973568
  | _ => 0

def rd (s : Fin 12) (i : Fin 10) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 12) (i : Fin 10) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 12) (i : Fin 10) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 12) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 12) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 12) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 12) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 12) (i : Fin 10) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 56 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
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
theorem far_cert (s : Fin 12) (i j : Fin 10) (hij : nonadj i j) : farCert s i j := by
  have hn : nearB i.val j.val = false := by
    obtain ⟨h1, h2, h3⟩ := hij
    have e1 : j.val ≠ i.val := fun h => h1 (Fin.ext h)
    have e2 : j.val ≠ (i.val + 1) % 10 := fun h => h2 (Fin.ext h)
    have e3 : j.val ≠ (i.val + 9) % 10 := fun h => h3 (Fin.ext h)
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

theorem point_contra (x y : ℤ) (s : Fin 12) (i : Fin 10) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
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
theorem far_step (s : Fin 12) (i : Fin 10) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
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
theorem farkas_ub (x y : ℤ) (s : Fin 12) (a1 a2 a3 : Fin 10) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 12, 0 < 1 * (Cc s 9 - 7) + 0 * (Cc s 0 - 7) + 0 * (Cc s 0 - 7) + 3 * 4 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 12, 0 < 1 * (Cc s 4 - 7) + 0 * (Cc s 0 - 7) + 0 * (Cc s 0 - 7) + 3 * 4 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 12, 0 < 1 * (Cc s 2 - 7) + 0 * (Cc s 0 - 7) + 0 * (Cc s 0 - 7) + 5 * 3 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 12, 0 < 1 * (Cc s 7 - 7) + 0 * (Cc s 0 - 7) + 0 * (Cc s 0 - 7) + 5 * 3 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 12, 0 < 3 * (Cc s 4 - (-1)) + 3 * (Cc s 9 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 7 lies in the cells |x| ≤ 3, |y| ≤ 2 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 12) (hF : F (x, y, s) ≤ 7) :
    -3 ≤ x ∧ x ≤ 3 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 9 0 0 7 1 0 0 1 0 4 3 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 0 0 7 1 0 0 (-1) 0 4 3 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 0 0 7 1 0 0 0 1 3 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 7 0 0 7 1 0 0 0 (-1) 3 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 4 9 0 (-1) 3 3 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 3, b - 2) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 6114800569540627327374434377576196464002842170049627733065101901409523317280197935993234341213800930239998586953170077506248013887268267487005787824811149787940189221689093601108524831276959679578677921981003957590463297802219994502957035938403581677651212147156944151632865878158636301573677251365709601462288252746017734806571148212832036288969956957905413693024982406577848118799452518191676081242317946165291893355024543307366035231429507972407164781849996655016379664481542777823532352355400221923308209254604049725956473034408307089447951922725284995114897686696532550676580166300997526990508011814912 >>> (6 * ((a * 5 + b) * 12 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 3, b - 2) and class s, potential i plus
17 + 3 a + 5 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 10) : ℕ :=
  tgetN 5190865680 4 i.val * a + tgetN 380817973250 4 i.val * b + tgetN 2263794841269058307390765872756186797180088569810498303355874121746048091989577138022559919855416787100134369268667527907575705450554880929635918576963365906141357031263669625343539686494744322136610923906301656676513 6 (s * 10 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)) (fnt a b s 8)) (fnt a b s 9)

theorem fnt_tab : ∀ s : Fin 12, ∀ i : Fin 10, (tgetN 5190865680 4 i.val : ℤ) = Ac i + 3 ∧
    (tgetN 380817973250 4 i.val : ℤ) = Bc i + 5 ∧
    (tgetN 2263794841269058307390765872756186797180088569810498303355874121746048091989577138022559919855416787100134369268667527907575705450554880929635918576963365906141357031263669625343539686494744322136610923906301656676513 6 (s.val * 10 + i.val) : ℤ) = Cc s i - Ac i * 3 - Bc i * 2 + 17 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 12) (i : Fin 10) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 3, (b : ℤ) - 2, s) i + (17 + 3 * a + 5 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 12) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 3, (b : ℤ) - 2, s) + (17 + 3 * a + 5 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 7, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (3 + 5) 1 = FN + 3 dx' + 5 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 7).all fun a => (List.range 5).all fun b => (List.range 12).all fun s =>
    Nat.blt (24 + 3 * a + 5 * b) (FN a b s) || (a == 3 && b == 2 && s == 6) ||
      (Nat.blt (hint a b s) 56 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 8 ==
          FN a b s + 3 * dxv (hint a b s) + 5 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 7) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
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
    have hs0 : s = 6 := Fin.ext (by rw [h3]; rfl)
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
from below, and for n ≥ 5 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 45 moves every quotient by an integer (`inner_shift`,
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
def AW (i : ℕ) : ℕ := tgetN 371694741605 4 i

def BW (i : ℕ) : ℕ := tgetN 600720298805 4 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem A_W (i : Fin 10) : Ac i = (AW i.val : ℤ) - 8 := rfl

theorem B_W (i : Fin 10) : Bc i = (BW i.val : ℤ) - 8 := rfl

theorem C_W (s : Fin 12) (i : Fin 10) : Cc s i = (CW s.val i.val : ℤ) - 8 := rfl

def gcV (k : ℕ) : ℕ := ctabN 430289739 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 10) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 139573377 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 379742135300 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 5

def Bp (i : Fin 10) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 188822178 3 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 2

def al (i : Fin 10) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 436480 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

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
def par (s : Fin 12) (i : Fin 10) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 12) (i j : Fin 10) (c u : ℤ) :
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

theorem par_inj (s : Fin 12) (i : Fin 10) (c : ℤ) : Function.Injective (par s i c) := by
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
(pot_i ≤ pot_j) plus cf0 times (5 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 4026411747455086090312759376939307436827222905185870056138736564422989803622918799555285603762546221349563033366696192 4 k

def cf2V (k : ℕ) : ℕ := ctabN 674791409022497951107138489414615771303751003806504249694710279670063685010226774918761288258149052385322483828614656 4 k

def cf3V (k : ℕ) : ℕ := ctabN 13499044580407686670997897879646642440409683835535270803325223774259949340400760381544128 3 k

def cf0V (k : ℕ) : ℕ := ctabN 5549613118278411477996492753250616835455865093369722515769568303155017117740616563103296 3 k

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
def certC (s : Fin 12) (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (5 - Cc s i)

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
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 13))

def certGK : PLift ((allR 10 fun i => allR 10 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 10 fun i => allR 10 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 12 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 12) : certS s = true := by
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
theorem certC_ok (s : Fin 12) (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
def lev (s : Fin 12) (i : Fin 10) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 12) (i : Fin 10) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 12) (i j : Fin 10) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 12) (i : Fin 10) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 12) (i : Fin 10) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 12) (i j : Fin 10) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 12) (i : Fin 10) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 12) (i : Fin 10) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 12) (i : Fin 10) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 5 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 12) (i : Fin 10) (n u : ℤ) (hn : 5 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 5 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-5, 5]: a natural-number check. -/
def cbK : PLift ((allR 12 fun s => allR 10 fun i => Nat.ble (CW s i) 13 && Nat.ble 8 (Nat.add (CW s i) 5)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 12) (j : Fin 10) : -5 ≤ Cc s j ∧ Cc s j ≤ 5 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ
    (Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (1 * Ac 4 + 0 * Ac 4 = 3 ∧ 1 * Bc 4 + 0 * Bc 4 = 0 ∧
    1 * Ac 9 + 0 * Ac 9 = (-3) ∧ 1 * Bc 9 + 0 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 5 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-5)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 1 * Ac 4 + 0 * Ac 4 = 3 ∧ 1 * Bc 4 + 0 * Bc 4 = 0 ∧
    1 * Ac 9 + 0 * Ac 9 = (-3) ∧ 1 * Bc 9 + 0 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 5 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-5) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 12) :
    3 * x ≤ 1 * F (x, y, s) + 5 ∧
    3 * (-x) ≤ 1 * F (x, y, s) + 5 ∧
    5 * y ≤ 1 * F (x, y, s) + 5 ∧
    5 * (-y) ≤ 1 * F (x, y, s) + 5 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 4 + 0 * pot (x, y, s) 4 =
      3 * x + 1 * Cc s 4 + 0 * Cc s 4 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 4
  have r0 := le_F (x, y, s) 4
  have k0 := Cbound s 4
  have l0 := Cbound s 4
  have e1 : 1 * pot (x, y, s) 9 + 0 * pot (x, y, s) 9 =
      3 * (-x) + 1 * Cc s 9 + 0 * Cc s 9 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 9
  have r1 := le_F (x, y, s) 9
  have k1 := Cbound s 9
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
noncomputable def PF (s : Fin 12) (i : Fin 10) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 12) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) :
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
def inner (s : Fin 12) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 12) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 12 × Fin 10, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 12 × Fin 10, inner p.1 p.2 n

/-! Shifting n by 45 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 282925042758884175 6 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 414412977714833825 6 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 18

def mh (i : Fin 10) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 335073978443477000 6 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 18

def mk (i : Fin 10) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 10, (45 : ℤ) = gc i * Lq i ∧ 45 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 45 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 10, (45 : ℤ) = gc i * Lq i ∧ 45 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 45 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 12) (i : Fin 10) (n : ℤ) :
    inner s i (n + 45) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 45 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 45 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 45) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 45) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 45) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
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
  ∑ q : Fin 12 × Fin 10, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 45) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 45 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 45 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 5 + r with r < 45: the level is QQ - 0 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 135368739 3 k

def uhMV (k : ℕ) : ℕ := ctabN 67110912 3 k

def ukPV (k : ℕ) : ℕ := ctabN 71305344 3 k

def ukMV (k : ℕ) : ℕ := ctabN 1114146 3 k

def dhV (k : ℕ) : ℕ := ctabN 249799352979 4 k

def dkV (k : ℕ) : ℕ := ctabN 245521158819 4 k

def mhkV (k : ℕ) : ℕ := ctabN 354642372901 4 k

def uh (i : Fin 10) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 10) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 10) : ℤ := dhV i.val

def dk (i : Fin 10) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 605573364685606746639094343166929172518288572949305376558871461015192355257283460540033122351218381497040897 3 (Nat.add i (Nat.mul 10 s))

def QQ (s i : ℕ) : ℕ := ctabN 256274694533379815555572878135513737336102926516016224785469215454339720501137959904776430308016454069446166287277949973943797527723678279815489 4 (Nat.add i (Nat.mul 10 s))

def AH (s i : ℕ) : ℕ := ctabN 10798745657966024706359523839667203338984473732147880098574587952191561262730192578510246504424334374739733538760747877599219293376612908844842244498691041019568568492186407448033369814119996108946682946181568660419 6 (Nat.add i (Nat.mul 10 s))

def AK (s i : ℕ) : ℕ := ctabN 81187822080056408384323355176839685137566227169216911324813825277274319324160845135077333885179238766543236548737520104450648382605515990410485576511210382323156928455093688895649 5 (Nat.add i (Nat.mul 10 s))

def WH (s i : ℕ) : ℕ := ctabN 85224122837106457933266461908317598148557071860114887685192565320222558764463121735510491771388993407963761277977972695657613533270620239948027784525301666479412830861475684451328 5 (Nat.add i (Nat.mul 10 s))

def WK (s i : ℕ) : ℕ := ctabN 80509912738022750246927188923250510432415417386659850672677373905760860624477206758630154190436143262933689346510005936611123926124495302727722671146932948665092422881161249419 5 (Nat.add i (Nat.mul 10 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 12 fun s => allR 10 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq 13 (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 12) (i : Fin 10) :
    PP s.val i.val < gcV i.val ∧
    (5 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 0) + PP s.val i.val ∧
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

/-- Piece (s, i) at n = 5 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 5 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 12) (i : Fin 10) (r : ℕ) :
    ((5 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (5 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 0) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 12) (i : Fin 10) (r : ℕ) (hr : r < 45) :
    inner s i ((5 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (45 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 45 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((5 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r := by
      rw [lev, show (5 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((5 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((5 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 2117646998650942018086964526690902834228326476394158971637211693886120408922837176208619967927413313334271444 8 k

def tblV (k : ℕ) : ℕ := ctabN 2117466411534933100055285850351493943617471595948120133256568913447308916564382932477034892834346261701069317 8 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 45. -/
def dv (t : ℕ) : ℕ := dtabV (t % 45)

/-- The sequence in closed form: b(n + 45) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 45) + tblV ((n - 1) % 45)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 45) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 45 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 45 - 1 = n - 1 + 45 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 45)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 45) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 45 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 45 - 1 = n - 1 + 45 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 45)]
  ring

/-- b on the residue class of 1 + j mod 45. -/
theorem b_res (k j : ℕ) (hj : j < 45) : b (45 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (45 * k + (1 + j) < 1) by omega),
    show 45 * k + (1 + j) - 1 = j + 45 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 45), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 5 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 45 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 12 fun s => allR 10 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 12 fun s => sumR 10 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 5 r)) &&
    Nat.beq (sumR 12 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 1 (dv (Nat.add 4 r)))

/-! The window n = 5, ..., 49, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 12 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 12 12 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 24 12 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK3 : PLift (allI 36 9 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 45) :
    (∀ s, s < 12 → ∀ i, i < 10 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 12 fun s => sumR 10 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (5 + r) ∧
    (sumR 12 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0) = 1 * dv (4 + r) := by
  have h : periodR r = true := by
    rcases (show r < 12 ∨ (12 ≤ r ∧ r < 24) ∨ (24 ≤ r ∧ r < 36) ∨ 36 ≤ r by omega) with h | h | h | h
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

theorem innerZ_eq (s i r : ℕ) (hs : s < 12) (hi : i < 10) (hr : r < 45) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 12 fun s => sumR 10 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 12 × Fin 10, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 10 fun i => f s i : ℕ) : ℤ)) 12]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 10]

theorem S_window (r : ℕ) (hr : r < 45) : S ((5 : ℤ) + r) = b (5 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 45) : Gs ((5 : ℤ) + r) = ((1 * dv (4 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 5 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 12) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 5 + t := ⟨(n - 5).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 45
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 45) (by omega) (by omega)
      have e : (5 : ℤ) + t = (5 + (t - 45 : ℕ)) + 45 := by
        push_cast [Nat.cast_sub (by omega : 45 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 5 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 45 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 5 ≤ n) : (1 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 5) % 45 < 45 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((5 : ℤ) + (((n - 5) % 45 : ℕ) : ℤ)) + 45 * (((n - 5) / 45 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (4 + (n - 5) % 45) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 5 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 50
    · obtain ⟨r, rfl⟩ : ∃ r, n = 5 + r := ⟨n - 5, by omega⟩
      push_cast
      exact S_window r (by omega)
    · have h1 := ih (n - 45) (by omega) (by omega)
      have h2 := S_shift ((n - 45 : ℕ) : ℤ)
      have h3 := b_shift (n - 45) (by omega)
      have h4 := grow (n - 45) (by omega)
      rw [show n - 45 + 45 = n by omega] at h3
      rw [show ((n - 45 : ℕ) : ℤ) + 45 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 4 lie in the box -3 ≤ x ≤ 3, -1 ≤ y ≤ 1 (`small_box`). In natural-number
coordinates a = x + 3, b = y + 1 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 12) (h : F (x, y, s) ≤ 4) :
    -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 3, (b : ℤ) - 1, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 32) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 3) (BW i)) 8) (Nat.add (Nat.mul 8 a) (Nat.mul 8 b))

theorem pot_box (a b : ℕ) (s : Fin 12) (i : Fin 10) :
    pot ((a : ℤ) - 3, (b : ℤ) - 1, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 10 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 12) : F ((a : ℤ) - 3, (b : ℤ) - 1, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 3, (b : ℤ) - 1, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 3, (b : ℤ) - 1, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 10 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 10 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 3, (b : ℤ) - 1, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 3, (b : ℤ) - 1, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 3, (b : ℤ) - 1, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 7 fun a => sumR 3 fun b => sumR 12 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 0 .. 4, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 0 5 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 5) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 12) : V := ((q.1 : ℤ) - 3, (q.2.1 : ℤ) - 1, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 4) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 7 ×ˢ (Finset.range 3 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 12 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 3).toNat, (y + 1).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 3).toNat (y + 1).toNat s
        rw [show (((x + 3).toNat : ℕ) : ℤ) - 3 = x by omega,
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 12]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 5 are counted in the
box, those from 5 on are S(n), and both agree with the closed form b (`a_eq_b`). The step from n to
n + 45, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 5 ∨ 5 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_eq n (by omega) h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 45) = a(n) + dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 45) = a n + dv (n - 1) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 212 ∧ tblV 0 = 5 ∧ dv 1 = 221 ∧ tblV 1 = 10 ∧ dv 2 = 221 ∧ tblV 2 = 14 ∧ dv 3 = 212 ∧ tblV 3 = 19 ∧ dv 4 = 230 ∧ tblV 4 = 25 ∧ dv 5 = 212 ∧ tblV 5 = 29 ∧ dv 6 = 221 ∧ tblV 6 = 35 ∧ dv 7 = 221 ∧ tblV 7 = 39) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 212 ∧ tblV 8 = 42 ∧ dv 9 = 230 ∧ tblV 9 = 51 ∧ dv 10 = 212 ∧ tblV 10 = 52 ∧ dv 11 = 221 ∧ tblV 11 = 59 ∧ dv 12 = 221 ∧ tblV 12 = 64 ∧ dv 13 = 212 ∧ tblV 13 = 65 ∧ dv 14 = 230 ∧ tblV 14 = 77 ∧ dv 15 = 212 ∧ tblV 15 = 76) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 221 ∧ tblV 16 = 84 ∧ dv 17 = 221 ∧ tblV 17 = 88 ∧ dv 18 = 212 ∧ tblV 18 = 89 ∧ dv 19 = 230 ∧ tblV 19 = 102 ∧ dv 20 = 212 ∧ tblV 20 = 99 ∧ dv 21 = 221 ∧ tblV 21 = 109 ∧ dv 22 = 221 ∧ tblV 22 = 112 ∧ dv 23 = 212 ∧ tblV 23 = 113) :=
  ⟨by decide +kernel⟩

def closedK3 : PLift (dv 24 = 230 ∧ tblV 24 = 128 ∧ dv 25 = 212 ∧ tblV 25 = 123 ∧ dv 26 = 221 ∧ tblV 26 = 133 ∧ dv 27 = 221 ∧ tblV 27 = 137 ∧ dv 28 = 212 ∧ tblV 28 = 136 ∧ dv 29 = 230 ∧ tblV 29 = 153 ∧ dv 30 = 212 ∧ tblV 30 = 147 ∧ dv 31 = 221 ∧ tblV 31 = 157) :=
  ⟨by decide +kernel⟩

def closedK4 : PLift (dv 32 = 221 ∧ tblV 32 = 162 ∧ dv 33 = 212 ∧ tblV 33 = 160 ∧ dv 34 = 230 ∧ tblV 34 = 179 ∧ dv 35 = 212 ∧ tblV 35 = 170 ∧ dv 36 = 221 ∧ tblV 36 = 182 ∧ dv 37 = 221 ∧ tblV 37 = 186 ∧ dv 38 = 212 ∧ tblV 38 = 183 ∧ dv 39 = 230 ∧ tblV 39 = 205) :=
  ⟨by decide +kernel⟩

def closedK5 : PLift (dv 40 = 212 ∧ tblV 40 = 193 ∧ dv 41 = 221 ∧ tblV 41 = 207 ∧ dv 42 = 221 ∧ tblV 42 = 211 ∧ dv 43 = 212 ∧ tblV 43 = 207 ∧ dv 44 = 230 ∧ tblV 44 = 230) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (45 * k + 1) = 212 * k + 5 ∧
    a (45 * k + 2) = 221 * k + 10 ∧
    a (45 * k + 3) = 221 * k + 14 ∧
    a (45 * k + 4) = 212 * k + 19 ∧
    a (45 * k + 5) = 230 * k + 25 ∧
    a (45 * k + 6) = 212 * k + 29 ∧
    a (45 * k + 7) = 221 * k + 35 ∧
    a (45 * k + 8) = 221 * k + 39 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 45 * k + 1 = 45 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 45 * k + 2 = 45 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 45 * k + 3 = 45 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 45 * k + 4 = 45 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 45 * k + 5 = 45 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 45 * k + 6 = 45 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 45 * k + 7 = 45 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 45 * k + 8 = 45 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (45 * k + 9) = 212 * k + 42 ∧
    a (45 * k + 10) = 230 * k + 51 ∧
    a (45 * k + 11) = 212 * k + 52 ∧
    a (45 * k + 12) = 221 * k + 59 ∧
    a (45 * k + 13) = 221 * k + 64 ∧
    a (45 * k + 14) = 212 * k + 65 ∧
    a (45 * k + 15) = 230 * k + 77 ∧
    a (45 * k + 16) = 212 * k + 76 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 45 * k + 9 = 45 * k + (1 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 45 * k + 10 = 45 * k + (1 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 45 * k + 11 = 45 * k + (1 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 45 * k + 12 = 45 * k + (1 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 45 * k + 13 = 45 * k + (1 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 45 * k + 14 = 45 * k + (1 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 45 * k + 15 = 45 * k + (1 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 45 * k + 16 = 45 * k + (1 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (45 * k + 17) = 221 * k + 84 ∧
    a (45 * k + 18) = 221 * k + 88 ∧
    a (45 * k + 19) = 212 * k + 89 ∧
    a (45 * k + 20) = 230 * k + 102 ∧
    a (45 * k + 21) = 212 * k + 99 ∧
    a (45 * k + 22) = 221 * k + 109 ∧
    a (45 * k + 23) = 221 * k + 112 ∧
    a (45 * k + 24) = 212 * k + 113 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 45 * k + 17 = 45 * k + (1 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 45 * k + 18 = 45 * k + (1 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 45 * k + 19 = 45 * k + (1 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 45 * k + 20 = 45 * k + (1 + 19) from rfl, b_res k 19 (by decide), c38, c39]
  · rw [show 45 * k + 21 = 45 * k + (1 + 20) from rfl, b_res k 20 (by decide), c40, c41]
  · rw [show 45 * k + 22 = 45 * k + (1 + 21) from rfl, b_res k 21 (by decide), c42, c43]
  · rw [show 45 * k + 23 = 45 * k + (1 + 22) from rfl, b_res k 22 (by decide), c44, c45]
  · rw [show 45 * k + 24 = 45 * k + (1 + 23) from rfl, b_res k 23 (by decide), c46, c47]

theorem a_closed3 (k : ℕ) :
    a (45 * k + 25) = 230 * k + 128 ∧
    a (45 * k + 26) = 212 * k + 123 ∧
    a (45 * k + 27) = 221 * k + 133 ∧
    a (45 * k + 28) = 221 * k + 137 ∧
    a (45 * k + 29) = 212 * k + 136 ∧
    a (45 * k + 30) = 230 * k + 153 ∧
    a (45 * k + 31) = 212 * k + 147 ∧
    a (45 * k + 32) = 221 * k + 157 := by
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := closedK3.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 45 * k + 25 = 45 * k + (1 + 24) from rfl, b_res k 24 (by decide), c48, c49]
  · rw [show 45 * k + 26 = 45 * k + (1 + 25) from rfl, b_res k 25 (by decide), c50, c51]
  · rw [show 45 * k + 27 = 45 * k + (1 + 26) from rfl, b_res k 26 (by decide), c52, c53]
  · rw [show 45 * k + 28 = 45 * k + (1 + 27) from rfl, b_res k 27 (by decide), c54, c55]
  · rw [show 45 * k + 29 = 45 * k + (1 + 28) from rfl, b_res k 28 (by decide), c56, c57]
  · rw [show 45 * k + 30 = 45 * k + (1 + 29) from rfl, b_res k 29 (by decide), c58, c59]
  · rw [show 45 * k + 31 = 45 * k + (1 + 30) from rfl, b_res k 30 (by decide), c60, c61]
  · rw [show 45 * k + 32 = 45 * k + (1 + 31) from rfl, b_res k 31 (by decide), c62, c63]

theorem a_closed4 (k : ℕ) :
    a (45 * k + 33) = 221 * k + 162 ∧
    a (45 * k + 34) = 212 * k + 160 ∧
    a (45 * k + 35) = 230 * k + 179 ∧
    a (45 * k + 36) = 212 * k + 170 ∧
    a (45 * k + 37) = 221 * k + 182 ∧
    a (45 * k + 38) = 221 * k + 186 ∧
    a (45 * k + 39) = 212 * k + 183 ∧
    a (45 * k + 40) = 230 * k + 205 := by
  obtain ⟨c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79⟩ := closedK4.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 45 * k + 33 = 45 * k + (1 + 32) from rfl, b_res k 32 (by decide), c64, c65]
  · rw [show 45 * k + 34 = 45 * k + (1 + 33) from rfl, b_res k 33 (by decide), c66, c67]
  · rw [show 45 * k + 35 = 45 * k + (1 + 34) from rfl, b_res k 34 (by decide), c68, c69]
  · rw [show 45 * k + 36 = 45 * k + (1 + 35) from rfl, b_res k 35 (by decide), c70, c71]
  · rw [show 45 * k + 37 = 45 * k + (1 + 36) from rfl, b_res k 36 (by decide), c72, c73]
  · rw [show 45 * k + 38 = 45 * k + (1 + 37) from rfl, b_res k 37 (by decide), c74, c75]
  · rw [show 45 * k + 39 = 45 * k + (1 + 38) from rfl, b_res k 38 (by decide), c76, c77]
  · rw [show 45 * k + 40 = 45 * k + (1 + 39) from rfl, b_res k 39 (by decide), c78, c79]

theorem a_closed5 (k : ℕ) :
    a (45 * k + 41) = 212 * k + 193 ∧
    a (45 * k + 42) = 221 * k + 207 ∧
    a (45 * k + 43) = 221 * k + 211 ∧
    a (45 * k + 44) = 212 * k + 207 ∧
    a (45 * k + 45) = 230 * k + 230 := by
  obtain ⟨c80, c81, c82, c83, c84, c85, c86, c87, c88, c89⟩ := closedK5.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show 45 * k + 41 = 45 * k + (1 + 40) from rfl, b_res k 40 (by decide), c80, c81]
  · rw [show 45 * k + 42 = 45 * k + (1 + 41) from rfl, b_res k 41 (by decide), c82, c83]
  · rw [show 45 * k + 43 = 45 * k + (1 + 42) from rfl, b_res k 42 (by decide), c84, c85]
  · rw [show 45 * k + 44 = 45 * k + (1 + 43) from rfl, b_res k 43 (by decide), c86, c87]
  · rw [show 45 * k + 45 = 45 * k + (1 + 44) from rfl, b_res k 44 (by decide), c88, c89]

/-- The closed form per residue of n mod 45, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (45 * k + 1) = 212 * k + 5 ∧
    a (45 * k + 2) = 221 * k + 10 ∧
    a (45 * k + 3) = 221 * k + 14 ∧
    a (45 * k + 4) = 212 * k + 19 ∧
    a (45 * k + 5) = 230 * k + 25 ∧
    a (45 * k + 6) = 212 * k + 29 ∧
    a (45 * k + 7) = 221 * k + 35 ∧
    a (45 * k + 8) = 221 * k + 39 ∧
    a (45 * k + 9) = 212 * k + 42 ∧
    a (45 * k + 10) = 230 * k + 51 ∧
    a (45 * k + 11) = 212 * k + 52 ∧
    a (45 * k + 12) = 221 * k + 59 ∧
    a (45 * k + 13) = 221 * k + 64 ∧
    a (45 * k + 14) = 212 * k + 65 ∧
    a (45 * k + 15) = 230 * k + 77 ∧
    a (45 * k + 16) = 212 * k + 76 ∧
    a (45 * k + 17) = 221 * k + 84 ∧
    a (45 * k + 18) = 221 * k + 88 ∧
    a (45 * k + 19) = 212 * k + 89 ∧
    a (45 * k + 20) = 230 * k + 102 ∧
    a (45 * k + 21) = 212 * k + 99 ∧
    a (45 * k + 22) = 221 * k + 109 ∧
    a (45 * k + 23) = 221 * k + 112 ∧
    a (45 * k + 24) = 212 * k + 113 ∧
    a (45 * k + 25) = 230 * k + 128 ∧
    a (45 * k + 26) = 212 * k + 123 ∧
    a (45 * k + 27) = 221 * k + 133 ∧
    a (45 * k + 28) = 221 * k + 137 ∧
    a (45 * k + 29) = 212 * k + 136 ∧
    a (45 * k + 30) = 230 * k + 153 ∧
    a (45 * k + 31) = 212 * k + 147 ∧
    a (45 * k + 32) = 221 * k + 157 ∧
    a (45 * k + 33) = 221 * k + 162 ∧
    a (45 * k + 34) = 212 * k + 160 ∧
    a (45 * k + 35) = 230 * k + 179 ∧
    a (45 * k + 36) = 212 * k + 170 ∧
    a (45 * k + 37) = 221 * k + 182 ∧
    a (45 * k + 38) = 221 * k + 186 ∧
    a (45 * k + 39) = 212 * k + 183 ∧
    a (45 * k + 40) = 230 * k + 205 ∧
    a (45 * k + 41) = 212 * k + 193 ∧
    a (45 * k + 42) = 221 * k + 207 ∧
    a (45 * k + 43) = 221 * k + 211 ∧
    a (45 * k + 44) = 212 * k + 207 ∧
    a (45 * k + 45) = 230 * k + 230 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15⟩ := a_closed1 k
  obtain ⟨x16, x17, x18, x19, x20, x21, x22, x23⟩ := a_closed2 k
  obtain ⟨x24, x25, x26, x27, x28, x29, x30, x31⟩ := a_closed3 k
  obtain ⟨x32, x33, x34, x35, x36, x37, x38, x39⟩ := a_closed4 k
  obtain ⟨x40, x41, x42, x43, x44⟩ := a_closed5 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44⟩

def controlsK : PLift ((List.range 50).map b = [1, 5, 10, 14, 19, 25, 29, 35, 39, 42, 51, 52, 59, 64, 65, 77, 76, 84, 88, 89, 102, 99, 109, 112, 113, 128, 123, 133, 137, 136, 153, 147, 157, 162, 160, 179, 170, 182, 186, 183, 205, 193, 207, 211, 207, 230, 217, 231, 235, 231]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 14, 19, 25, 29, 35, 39, 42, 51, 52, 59, 64, 65, 77, 76, 84, 88, 89, 102, 99, 109, 112, 113, 128, 123, 133, 137, 136, 153, 147, 157, 162, 160, 179, 170, 182, 186, 183, 205, 193, 207, 211, 207, 230, 217, 231, 235, 231] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 45 → dv (t + 18) + dv (t + 17) + dv (t + 16) + dv (t + 15) + dv (t + 14) + dv (t + 4) + dv (t + 3) + dv (t + 2) + dv (t + 1) + dv (t + 0) = dv (t + 13) + dv (t + 12) + dv (t + 11) + dv (t + 10) + 2 * dv (t + 9) + dv (t + 8) + dv (t + 7) + dv (t + 6) + dv (t + 5)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 45 → dv (t + 18) + dv (t + 17) + dv (t + 16) + dv (t + 15) + dv (t + 14) + dv (t + 4) + dv (t + 3) + dv (t + 2) + dv (t + 1) + dv (t + 0) = dv (t + 13) + dv (t + 12) + dv (t + 11) + dv (t + 10) + 2 * dv (t + 9) + dv (t + 8) + dv (t + 7) + dv (t + 6) + dv (t + 5) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 18) : ℤ) = -(dv (t + 17) : ℤ) - (dv (t + 16) : ℤ) - (dv (t + 15) : ℤ) - (dv (t + 14) : ℤ) + (dv (t + 13) : ℤ) + (dv (t + 12) : ℤ) + (dv (t + 11) : ℤ) + (dv (t + 10) : ℤ) + 2 * (dv (t + 9) : ℤ) + (dv (t + 8) : ℤ) + (dv (t + 7) : ℤ) + (dv (t + 6) : ℤ) + (dv (t + 5) : ℤ) - (dv (t + 4) : ℤ) - (dv (t + 3) : ℤ) - (dv (t + 2) : ℤ) - (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 45 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10, e 11, e 12, e 13, e 14, e 15, e 16, e 17, e 18]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 45) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 45 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 45 → b (q + 19) + b (q + 18) + b (q + 17) + b (q + 16) + b (q + 15) + b (q + 5) + b (q + 4) + b (q + 3) + b (q + 2) + b (q + 1) = b (q + 14) + b (q + 13) + b (q + 12) + b (q + 11) + 2 * b (q + 10) + b (q + 9) + b (q + 8) + b (q + 7) + b (q + 6)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 45 → b (q + 19) + b (q + 18) + b (q + 17) + b (q + 16) + b (q + 15) + b (q + 5) + b (q + 4) + b (q + 3) + b (q + 2) + b (q + 1) = b (q + 14) + b (q + 13) + b (q + 12) + b (q + 11) + 2 * b (q + 10) + b (q + 9) + b (q + 8) + b (q + 7) + b (q + 6) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 19) : ℤ) = -b (q + 18) - b (q + 17) - b (q + 16) - b (q + 15) + b (q + 14) + b (q + 13) + b (q + 12) + b (q + 11) + 2 * b (q + 10) + b (q + 9) + b (q + 8) + b (q + 7) + b (q + 6) - b (q + 5) - b (q + 4) - b (q + 3) - b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 45 ∨ 45 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 45 := ⟨q - 45, by omega⟩
      have h0 : (b (v + 19) : ℤ) = -b (v + 18) - b (v + 17) - b (v + 16) - b (v + 15) + b (v + 14) + b (v + 13) + b (v + 12) + b (v + 11) + 2 * b (v + 10) + b (v + 9) + b (v + 8) + b (v + 7) + b (v + 6) - b (v + 5) - b (v + 4) - b (v + 3) - b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 46) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 45 = v + 46 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s2 : (b (v + 47) : ℤ) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (le_trans (by decide : 1 ≤ 2) (Nat.le_add_left _ v))
        rw [show v + 2 + 45 = v + 47 from Nat.add_assoc _ _ _,
          show v + 2 - 1 = v + 1 from Nat.add_sub_assoc (by decide : 1 ≤ 2) v] at h
        exact_mod_cast h
      have s3 : (b (v + 48) : ℤ) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (le_trans (by decide : 1 ≤ 3) (Nat.le_add_left _ v))
        rw [show v + 3 + 45 = v + 48 from Nat.add_assoc _ _ _,
          show v + 3 - 1 = v + 2 from Nat.add_sub_assoc (by decide : 1 ≤ 3) v] at h
        exact_mod_cast h
      have s4 : (b (v + 49) : ℤ) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (le_trans (by decide : 1 ≤ 4) (Nat.le_add_left _ v))
        rw [show v + 4 + 45 = v + 49 from Nat.add_assoc _ _ _,
          show v + 4 - 1 = v + 3 from Nat.add_sub_assoc (by decide : 1 ≤ 4) v] at h
        exact_mod_cast h
      have s5 : (b (v + 50) : ℤ) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (le_trans (by decide : 1 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 45 = v + 50 from Nat.add_assoc _ _ _,
          show v + 5 - 1 = v + 4 from Nat.add_sub_assoc (by decide : 1 ≤ 5) v] at h
        exact_mod_cast h
      have s6 : (b (v + 51) : ℤ) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (le_trans (by decide : 1 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 45 = v + 51 from Nat.add_assoc _ _ _,
          show v + 6 - 1 = v + 5 from Nat.add_sub_assoc (by decide : 1 ≤ 6) v] at h
        exact_mod_cast h
      have s7 : (b (v + 52) : ℤ) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (le_trans (by decide : 1 ≤ 7) (Nat.le_add_left _ v))
        rw [show v + 7 + 45 = v + 52 from Nat.add_assoc _ _ _,
          show v + 7 - 1 = v + 6 from Nat.add_sub_assoc (by decide : 1 ≤ 7) v] at h
        exact_mod_cast h
      have s8 : (b (v + 53) : ℤ) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (le_trans (by decide : 1 ≤ 8) (Nat.le_add_left _ v))
        rw [show v + 8 + 45 = v + 53 from Nat.add_assoc _ _ _,
          show v + 8 - 1 = v + 7 from Nat.add_sub_assoc (by decide : 1 ≤ 8) v] at h
        exact_mod_cast h
      have s9 : (b (v + 54) : ℤ) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (le_trans (by decide : 1 ≤ 9) (Nat.le_add_left _ v))
        rw [show v + 9 + 45 = v + 54 from Nat.add_assoc _ _ _,
          show v + 9 - 1 = v + 8 from Nat.add_sub_assoc (by decide : 1 ≤ 9) v] at h
        exact_mod_cast h
      have s10 : (b (v + 55) : ℤ) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (le_trans (by decide : 1 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 45 = v + 55 from Nat.add_assoc _ _ _,
          show v + 10 - 1 = v + 9 from Nat.add_sub_assoc (by decide : 1 ≤ 10) v] at h
        exact_mod_cast h
      have s11 : (b (v + 56) : ℤ) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (le_trans (by decide : 1 ≤ 11) (Nat.le_add_left _ v))
        rw [show v + 11 + 45 = v + 56 from Nat.add_assoc _ _ _,
          show v + 11 - 1 = v + 10 from Nat.add_sub_assoc (by decide : 1 ≤ 11) v] at h
        exact_mod_cast h
      have s12 : (b (v + 57) : ℤ) = b (v + 12) + dv (v + 11) := by
        have h := b_step (v + 12) (le_trans (by decide : 1 ≤ 12) (Nat.le_add_left _ v))
        rw [show v + 12 + 45 = v + 57 from Nat.add_assoc _ _ _,
          show v + 12 - 1 = v + 11 from Nat.add_sub_assoc (by decide : 1 ≤ 12) v] at h
        exact_mod_cast h
      have s13 : (b (v + 58) : ℤ) = b (v + 13) + dv (v + 12) := by
        have h := b_step (v + 13) (le_trans (by decide : 1 ≤ 13) (Nat.le_add_left _ v))
        rw [show v + 13 + 45 = v + 58 from Nat.add_assoc _ _ _,
          show v + 13 - 1 = v + 12 from Nat.add_sub_assoc (by decide : 1 ≤ 13) v] at h
        exact_mod_cast h
      have s14 : (b (v + 59) : ℤ) = b (v + 14) + dv (v + 13) := by
        have h := b_step (v + 14) (le_trans (by decide : 1 ≤ 14) (Nat.le_add_left _ v))
        rw [show v + 14 + 45 = v + 59 from Nat.add_assoc _ _ _,
          show v + 14 - 1 = v + 13 from Nat.add_sub_assoc (by decide : 1 ≤ 14) v] at h
        exact_mod_cast h
      have s15 : (b (v + 60) : ℤ) = b (v + 15) + dv (v + 14) := by
        have h := b_step (v + 15) (le_trans (by decide : 1 ≤ 15) (Nat.le_add_left _ v))
        rw [show v + 15 + 45 = v + 60 from Nat.add_assoc _ _ _,
          show v + 15 - 1 = v + 14 from Nat.add_sub_assoc (by decide : 1 ≤ 15) v] at h
        exact_mod_cast h
      have s16 : (b (v + 61) : ℤ) = b (v + 16) + dv (v + 15) := by
        have h := b_step (v + 16) (le_trans (by decide : 1 ≤ 16) (Nat.le_add_left _ v))
        rw [show v + 16 + 45 = v + 61 from Nat.add_assoc _ _ _,
          show v + 16 - 1 = v + 15 from Nat.add_sub_assoc (by decide : 1 ≤ 16) v] at h
        exact_mod_cast h
      have s17 : (b (v + 62) : ℤ) = b (v + 17) + dv (v + 16) := by
        have h := b_step (v + 17) (le_trans (by decide : 1 ≤ 17) (Nat.le_add_left _ v))
        rw [show v + 17 + 45 = v + 62 from Nat.add_assoc _ _ _,
          show v + 17 - 1 = v + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) v] at h
        exact_mod_cast h
      have s18 : (b (v + 63) : ℤ) = b (v + 18) + dv (v + 17) := by
        have h := b_step (v + 18) (le_trans (by decide : 1 ≤ 18) (Nat.le_add_left _ v))
        rw [show v + 18 + 45 = v + 63 from Nat.add_assoc _ _ _,
          show v + 18 - 1 = v + 17 from Nat.add_sub_assoc (by decide : 1 ≤ 18) v] at h
        exact_mod_cast h
      have s19 : (b (v + 64) : ℤ) = b (v + 19) + dv (v + 18) := by
        have h := b_step (v + 19) (le_trans (by decide : 1 ≤ 19) (Nat.le_add_left _ v))
        rw [show v + 19 + 45 = v + 64 from Nat.add_assoc _ _ _,
          show v + 19 - 1 = v + 18 from Nat.add_sub_assoc (by decide : 1 ≤ 19) v] at h
        exact_mod_cast h
      show (b (v + 64) : ℤ) = -b (v + 63) - b (v + 62) - b (v + 61) - b (v + 60) + b (v + 59) + b (v + 58) + b (v + 57) + b (v + 56) + 2 * b (v + 55) + b (v + 54) + b (v + 53) + b (v + 52) + b (v + 51) - b (v + 50) - b (v + 49) - b (v + 48) - b (v + 47) - b (v + 46)
      linear_combination s19 - (-1) * s18 - (-1) * s17 - (-1) * s16 - (-1) * s15 - (1) * s14 - (1) * s13 - (1) * s12 - (1) * s11 - (2) * s10 - (1) * s9 - (1) * s8 - (1) * s7 - (1) * s6 - (-1) * s5 - (-1) * s4 - (-1) * s3 - (-1) * s2 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 18 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) - a (n - 3) - a (n - 4) + a (n - 5) + a (n - 6) + a (n - 7) + a (n - 8) + 2 * a (n - 9) + a (n - 10) + a (n - 11) + a (n - 12) + a (n - 13) - a (n - 14) - a (n - 15) - a (n - 16) - a (n - 17) - a (n - 18) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 19 := ⟨n - 19, by omega⟩
  rw [show q + 19 - 1 = q + 18 from Nat.add_sub_assoc (by decide : 1 ≤ 19) q, show q + 19 - 2 = q + 17 from Nat.add_sub_assoc (by decide : 2 ≤ 19) q, show q + 19 - 3 = q + 16 from Nat.add_sub_assoc (by decide : 3 ≤ 19) q, show q + 19 - 4 = q + 15 from Nat.add_sub_assoc (by decide : 4 ≤ 19) q, show q + 19 - 5 = q + 14 from Nat.add_sub_assoc (by decide : 5 ≤ 19) q, show q + 19 - 6 = q + 13 from Nat.add_sub_assoc (by decide : 6 ≤ 19) q, show q + 19 - 7 = q + 12 from Nat.add_sub_assoc (by decide : 7 ≤ 19) q, show q + 19 - 8 = q + 11 from Nat.add_sub_assoc (by decide : 8 ≤ 19) q, show q + 19 - 9 = q + 10 from Nat.add_sub_assoc (by decide : 9 ≤ 19) q, show q + 19 - 10 = q + 9 from Nat.add_sub_assoc (by decide : 10 ≤ 19) q, show q + 19 - 11 = q + 8 from Nat.add_sub_assoc (by decide : 11 ≤ 19) q, show q + 19 - 12 = q + 7 from Nat.add_sub_assoc (by decide : 12 ≤ 19) q, show q + 19 - 13 = q + 6 from Nat.add_sub_assoc (by decide : 13 ≤ 19) q, show q + 19 - 14 = q + 5 from Nat.add_sub_assoc (by decide : 14 ≤ 19) q, show q + 19 - 15 = q + 4 from Nat.add_sub_assoc (by decide : 15 ≤ 19) q, show q + 19 - 16 = q + 3 from Nat.add_sub_assoc (by decide : 16 ≤ 19) q, show q + 19 - 17 = q + 2 from Nat.add_sub_assoc (by decide : 17 ≤ 19) q, show q + 19 - 18 = q + 1 from Nat.add_sub_assoc (by decide : 18 ≤ 19) q]
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

/-- The coefficients of A * DEN and NUM agree below 19, in natural numbers (negative terms moved
across). -/
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (b n) (bk n 1)) (bk n 2)) (bk n 3)) (bk n 4)) (bk n 14)) (bk n 15)) (bk n 16)) (bk n 17)) (bk n 18)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (bk n 5) (bk n 6)) (bk n 7)) (bk n 8)) (Nat.mul 2 (bk n 9))) (bk n 10)) (bk n 11)) (bk n 12)) (bk n 13)) (ind n 0)) (Nat.mul 6 (ind n 1))) (Nat.mul 16 (ind n 2))) (Nat.mul 30 (ind n 3))) (Nat.mul 49 (ind n 4))) (Nat.mul 72 (ind n 5))) (Nat.mul 91 (ind n 6))) (Nat.mul 106 (ind n 7))) (Nat.mul 117 (ind n 8))) (Nat.mul 120 (ind n 9))) (Nat.mul 117 (ind n 10))) (Nat.mul 106 (ind n 11))) (Nat.mul 91 (ind n 12))) (Nat.mul 72 (ind n 13))) (Nat.mul 49 (ind n 14))) (Nat.mul 30 (ind n 15))) (Nat.mul 16 (ind n 16))) (Nat.mul 6 (ind n 17))) (ind n 18)

def gfK : PLift ((allR 19 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 19, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 19) :
    1 * (b (n) : ℚ) + 1 * (if 1 ≤ n then (b (n - 1) : ℚ) else 0) + 1 * (if 2 ≤ n then (b (n - 2) : ℚ) else 0) + 1 * (if 3 ≤ n then (b (n - 3) : ℚ) else 0) + 1 * (if 4 ≤ n then (b (n - 4) : ℚ) else 0) - 1 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) - 1 * (if 6 ≤ n then (b (n - 6) : ℚ) else 0) - 1 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) - 1 * (if 8 ≤ n then (b (n - 8) : ℚ) else 0) - 2 * (if 9 ≤ n then (b (n - 9) : ℚ) else 0) - 1 * (if 10 ≤ n then (b (n - 10) : ℚ) else 0) - 1 * (if 11 ≤ n then (b (n - 11) : ℚ) else 0) - 1 * (if 12 ≤ n then (b (n - 12) : ℚ) else 0) - 1 * (if 13 ≤ n then (b (n - 13) : ℚ) else 0) + 1 * (if 14 ≤ n then (b (n - 14) : ℚ) else 0) + 1 * (if 15 ≤ n then (b (n - 15) : ℚ) else 0) + 1 * (if 16 ≤ n then (b (n - 16) : ℚ) else 0) + 1 * (if 17 ≤ n then (b (n - 17) : ℚ) else 0) + 1 * (if 18 ≤ n then (b (n - 18) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 6 + (if n = 2 then (1 : ℚ) else 0) * 16 + (if n = 3 then (1 : ℚ) else 0) * 30 + (if n = 4 then (1 : ℚ) else 0) * 49 + (if n = 5 then (1 : ℚ) else 0) * 72 + (if n = 6 then (1 : ℚ) else 0) * 91 + (if n = 7 then (1 : ℚ) else 0) * 106 + (if n = 8 then (1 : ℚ) else 0) * 117 + (if n = 9 then (1 : ℚ) else 0) * 120 + (if n = 10 then (1 : ℚ) else 0) * 117 + (if n = 11 then (1 : ℚ) else 0) * 106 + (if n = 12 then (1 : ℚ) else 0) * 91 + (if n = 13 then (1 : ℚ) else 0) * 72 + (if n = 14 then (1 : ℚ) else 0) * 49 + (if n = 15 then (1 : ℚ) else 0) * 30 + (if n = 16 then (1 : ℚ) else 0) * 16 + (if n = 17 then (1 : ℚ) else 0) * 6 + (if n = 18 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 19 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 19) : ℚ) + 1 * (if 1 ≤ q + 19 then (b (q + 19 - 1) : ℚ) else 0) + 1 * (if 2 ≤ q + 19 then (b (q + 19 - 2) : ℚ) else 0) + 1 * (if 3 ≤ q + 19 then (b (q + 19 - 3) : ℚ) else 0) + 1 * (if 4 ≤ q + 19 then (b (q + 19 - 4) : ℚ) else 0) - 1 * (if 5 ≤ q + 19 then (b (q + 19 - 5) : ℚ) else 0) - 1 * (if 6 ≤ q + 19 then (b (q + 19 - 6) : ℚ) else 0) - 1 * (if 7 ≤ q + 19 then (b (q + 19 - 7) : ℚ) else 0) - 1 * (if 8 ≤ q + 19 then (b (q + 19 - 8) : ℚ) else 0) - 2 * (if 9 ≤ q + 19 then (b (q + 19 - 9) : ℚ) else 0) - 1 * (if 10 ≤ q + 19 then (b (q + 19 - 10) : ℚ) else 0) - 1 * (if 11 ≤ q + 19 then (b (q + 19 - 11) : ℚ) else 0) - 1 * (if 12 ≤ q + 19 then (b (q + 19 - 12) : ℚ) else 0) - 1 * (if 13 ≤ q + 19 then (b (q + 19 - 13) : ℚ) else 0) + 1 * (if 14 ≤ q + 19 then (b (q + 19 - 14) : ℚ) else 0) + 1 * (if 15 ≤ q + 19 then (b (q + 19 - 15) : ℚ) else 0) + 1 * (if 16 ≤ q + 19 then (b (q + 19 - 16) : ℚ) else 0) + 1 * (if 17 ≤ q + 19 then (b (q + 19 - 17) : ℚ) else 0) + 1 * (if 18 ≤ q + 19 then (b (q + 19 - 18) : ℚ) else 0) =
      (if q + 19 = 0 then (1 : ℚ) else 0) * 1 + (if q + 19 = 1 then (1 : ℚ) else 0) * 6 + (if q + 19 = 2 then (1 : ℚ) else 0) * 16 + (if q + 19 = 3 then (1 : ℚ) else 0) * 30 + (if q + 19 = 4 then (1 : ℚ) else 0) * 49 + (if q + 19 = 5 then (1 : ℚ) else 0) * 72 + (if q + 19 = 6 then (1 : ℚ) else 0) * 91 + (if q + 19 = 7 then (1 : ℚ) else 0) * 106 + (if q + 19 = 8 then (1 : ℚ) else 0) * 117 + (if q + 19 = 9 then (1 : ℚ) else 0) * 120 + (if q + 19 = 10 then (1 : ℚ) else 0) * 117 + (if q + 19 = 11 then (1 : ℚ) else 0) * 106 + (if q + 19 = 12 then (1 : ℚ) else 0) * 91 + (if q + 19 = 13 then (1 : ℚ) else 0) * 72 + (if q + 19 = 14 then (1 : ℚ) else 0) * 49 + (if q + 19 = 15 then (1 : ℚ) else 0) * 30 + (if q + 19 = 16 then (1 : ℚ) else 0) * 16 + (if q + 19 = 17 then (1 : ℚ) else 0) * 6 + (if q + 19 = 18 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 19) : ℤ) = -b (q + 18) - b (q + 17) - b (q + 16) - b (q + 15) + b (q + 14) + b (q + 13) + b (q + 12) + b (q + 11) + 2 * b (q + 10) + b (q + 9) + b (q + 8) + b (q + 7) + b (q + 6) - b (q + 5) - b (q + 4) - b (q + 3) - b (q + 2) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 19 - 1 = q + 18 from Nat.add_sub_assoc (by decide : 1 ≤ 19) q, show q + 19 - 2 = q + 17 from Nat.add_sub_assoc (by decide : 2 ≤ 19) q, show q + 19 - 3 = q + 16 from Nat.add_sub_assoc (by decide : 3 ≤ 19) q, show q + 19 - 4 = q + 15 from Nat.add_sub_assoc (by decide : 4 ≤ 19) q, show q + 19 - 5 = q + 14 from Nat.add_sub_assoc (by decide : 5 ≤ 19) q, show q + 19 - 6 = q + 13 from Nat.add_sub_assoc (by decide : 6 ≤ 19) q, show q + 19 - 7 = q + 12 from Nat.add_sub_assoc (by decide : 7 ≤ 19) q, show q + 19 - 8 = q + 11 from Nat.add_sub_assoc (by decide : 8 ≤ 19) q, show q + 19 - 9 = q + 10 from Nat.add_sub_assoc (by decide : 9 ≤ 19) q, show q + 19 - 10 = q + 9 from Nat.add_sub_assoc (by decide : 10 ≤ 19) q, show q + 19 - 11 = q + 8 from Nat.add_sub_assoc (by decide : 11 ≤ 19) q, show q + 19 - 12 = q + 7 from Nat.add_sub_assoc (by decide : 12 ≤ 19) q, show q + 19 - 13 = q + 6 from Nat.add_sub_assoc (by decide : 13 ≤ 19) q, show q + 19 - 14 = q + 5 from Nat.add_sub_assoc (by decide : 14 ≤ 19) q, show q + 19 - 15 = q + 4 from Nat.add_sub_assoc (by decide : 15 ≤ 19) q, show q + 19 - 16 = q + 3 from Nat.add_sub_assoc (by decide : 16 ≤ 19) q, show q + 19 - 17 = q + 2 from Nat.add_sub_assoc (by decide : 17 ≤ 19) q, show q + 19 - 18 = q + 1 from Nat.add_sub_assoc (by decide : 18 ≤ 19) q, show 1 ≤ q + 19 from le_trans (by decide : 1 ≤ 19) (Nat.le_add_left 19 q), show 2 ≤ q + 19 from le_trans (by decide : 2 ≤ 19) (Nat.le_add_left 19 q), show 3 ≤ q + 19 from le_trans (by decide : 3 ≤ 19) (Nat.le_add_left 19 q), show 4 ≤ q + 19 from le_trans (by decide : 4 ≤ 19) (Nat.le_add_left 19 q), show 5 ≤ q + 19 from le_trans (by decide : 5 ≤ 19) (Nat.le_add_left 19 q), show 6 ≤ q + 19 from le_trans (by decide : 6 ≤ 19) (Nat.le_add_left 19 q), show 7 ≤ q + 19 from le_trans (by decide : 7 ≤ 19) (Nat.le_add_left 19 q), show 8 ≤ q + 19 from le_trans (by decide : 8 ≤ 19) (Nat.le_add_left 19 q), show 9 ≤ q + 19 from le_trans (by decide : 9 ≤ 19) (Nat.le_add_left 19 q), show 10 ≤ q + 19 from le_trans (by decide : 10 ≤ 19) (Nat.le_add_left 19 q), show 11 ≤ q + 19 from le_trans (by decide : 11 ≤ 19) (Nat.le_add_left 19 q), show 12 ≤ q + 19 from le_trans (by decide : 12 ≤ 19) (Nat.le_add_left 19 q), show 13 ≤ q + 19 from le_trans (by decide : 13 ≤ 19) (Nat.le_add_left 19 q), show 14 ≤ q + 19 from le_trans (by decide : 14 ≤ 19) (Nat.le_add_left 19 q), show 15 ≤ q + 19 from le_trans (by decide : 15 ≤ 19) (Nat.le_add_left 19 q), show 16 ≤ q + 19 from le_trans (by decide : 16 ≤ 19) (Nat.le_add_left 19 q), show 17 ≤ q + 19 from le_trans (by decide : 17 ≤ 19) (Nat.le_add_left 19 q), show 18 ≤ q + 19 from le_trans (by decide : 18 ≤ 19) (Nat.le_add_left 19 q), show ¬ q + 19 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 14 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 14 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 15 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 15 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 16 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 16 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 17 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 17 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 18 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 18 < 19) (Nat.le_add_left 19 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 6 + X ^ 3 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) = C 1 * A + C 1 * (A * X ^ 1) + C 1 * (A * X ^ 2) + C 1 * (A * X ^ 3) + C 1 * (A * X ^ 4) - C 1 * (A * X ^ 5) - C 1 * (A * X ^ 6) - C 1 * (A * X ^ 7) - C 1 * (A * X ^ 8) - C 2 * (A * X ^ 9) - C 1 * (A * X ^ 10) - C 1 * (A * X ^ 11) - C 1 * (A * X ^ 12) - C 1 * (A * X ^ 13) + C 1 * (A * X ^ 14) + C 1 * (A * X ^ 15) + C 1 * (A * X ^ 16) + C 1 * (A * X ^ 17) + C 1 * (A * X ^ 18) := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : ((X + 1) ^ 2 * (X ^ 16 + 4 * X ^ 15 + 7 * X ^ 14 + 12 * X ^ 13 + 18 * X ^ 12 + 24 * X ^ 11 + 25 * X ^ 10 + 32 * X ^ 9 + 28 * X ^ 8 + 32 * X ^ 7 + 25 * X ^ 6 + 24 * X ^ 5 + 18 * X ^ 4 + 12 * X ^ 3 + 7 * X ^ 2 + 4 * X + 1) : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 6 + X ^ 2 * C 16 + X ^ 3 * C 30 + X ^ 4 * C 49 + X ^ 5 * C 72 + X ^ 6 * C 91 + X ^ 7 * C 106 + X ^ 8 * C 117 + X ^ 9 * C 120 + X ^ 10 * C 117 + X ^ 11 * C 106 + X ^ 12 * C 91 + X ^ 13 * C 72 + X ^ 14 * C 49 + X ^ 15 * C 30 + X ^ 16 * C 16 + X ^ 17 * C 6 + X ^ 18 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 6 + X ^ 3 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      (X + 1) ^ 2 * (X ^ 16 + 4 * X ^ 15 + 7 * X ^ 14 + 12 * X ^ 13 + 18 * X ^ 12 + 24 * X ^ 11 + 25 * X ^ 10 + 32 * X ^ 9 + 28 * X ^ 8 + 32 * X ^ 7 + 25 * X ^ 6 + 24 * X ^ 5 + 18 * X ^ 4 + 12 * X ^ 3 + 7 * X ^ 2 + 4 * X + 1) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  rw [gf_den A, gf_num]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 19 with hn | hn
  · linarith [gf_low n hn]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 19 := ⟨n - 19, by omega⟩
    linarith [gf_high q]

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 6 + X ^ 3 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      (X + 1) ^ 2 * (X ^ 16 + 4 * X ^ 15 + 7 * X ^ 14 + 12 * X ^ 13 + 18 * X ^ 12 + 24 * X ^ 11 + 25 * X ^ 10 + 32 * X ^ 9 + 28 * X ^ 8 + 32 * X ^ 7 + 25 * X ^ 6 + 24 * X ^ 5 + 18 * X ^ 4 + 12 * X ^ 3 + 7 * X ^ 2 + 4 * X + 1) := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 18 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) - a (n - 3) - a (n - 4) + a (n - 5) + a (n - 6) + a (n - 7) + a (n - 8) + 2 * a (n - 9) + a (n - 10) + a (n - 11) + a (n - 12) + a (n - 13) - a (n - 14) - a (n - 15) - a (n - 16) - a (n - 17) - a (n - 18) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 14, 19, 25, 29, 35, 39, 42, 51, 52, 59, 64, 65, 77, 76, 84, 88, 89, 102, 99, 109, 112, 113, 128, 123, 133, 137, 136, 153, 147, 157, 162, 160, 179, 170, 182, 186, 183, 205, 193, 207, 211, 207, 230, 217, 231, 235, 231] := Count.controls

/-- The step a(n + 45) = a(n) + Count.dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 45) = a n + Count.dv (n - 1) := Count.a_step n hn

/-- The closed form per residue of n mod 45, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (45 * k + 1) = 212 * k + 5 ∧
    a (45 * k + 2) = 221 * k + 10 ∧
    a (45 * k + 3) = 221 * k + 14 ∧
    a (45 * k + 4) = 212 * k + 19 ∧
    a (45 * k + 5) = 230 * k + 25 ∧
    a (45 * k + 6) = 212 * k + 29 ∧
    a (45 * k + 7) = 221 * k + 35 ∧
    a (45 * k + 8) = 221 * k + 39 ∧
    a (45 * k + 9) = 212 * k + 42 ∧
    a (45 * k + 10) = 230 * k + 51 ∧
    a (45 * k + 11) = 212 * k + 52 ∧
    a (45 * k + 12) = 221 * k + 59 ∧
    a (45 * k + 13) = 221 * k + 64 ∧
    a (45 * k + 14) = 212 * k + 65 ∧
    a (45 * k + 15) = 230 * k + 77 ∧
    a (45 * k + 16) = 212 * k + 76 ∧
    a (45 * k + 17) = 221 * k + 84 ∧
    a (45 * k + 18) = 221 * k + 88 ∧
    a (45 * k + 19) = 212 * k + 89 ∧
    a (45 * k + 20) = 230 * k + 102 ∧
    a (45 * k + 21) = 212 * k + 99 ∧
    a (45 * k + 22) = 221 * k + 109 ∧
    a (45 * k + 23) = 221 * k + 112 ∧
    a (45 * k + 24) = 212 * k + 113 ∧
    a (45 * k + 25) = 230 * k + 128 ∧
    a (45 * k + 26) = 212 * k + 123 ∧
    a (45 * k + 27) = 221 * k + 133 ∧
    a (45 * k + 28) = 221 * k + 137 ∧
    a (45 * k + 29) = 212 * k + 136 ∧
    a (45 * k + 30) = 230 * k + 153 ∧
    a (45 * k + 31) = 212 * k + 147 ∧
    a (45 * k + 32) = 221 * k + 157 ∧
    a (45 * k + 33) = 221 * k + 162 ∧
    a (45 * k + 34) = 212 * k + 160 ∧
    a (45 * k + 35) = 230 * k + 179 ∧
    a (45 * k + 36) = 212 * k + 170 ∧
    a (45 * k + 37) = 221 * k + 182 ∧
    a (45 * k + 38) = 221 * k + 186 ∧
    a (45 * k + 39) = 212 * k + 183 ∧
    a (45 * k + 40) = 230 * k + 205 ∧
    a (45 * k + 41) = 212 * k + 193 ∧
    a (45 * k + 42) = 221 * k + 207 ∧
    a (45 * k + 43) = 221 * k + 211 ∧
    a (45 * k + 44) = 212 * k + 207 ∧
    a (45 * k + 45) = 230 * k + 230 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 6 + X ^ 3 + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      (X + 1) ^ 2 * (X ^ 16 + 4 * X ^ 15 + 7 * X ^ 14 + 12 * X ^ 13 + 18 * X ^ 12 + 24 * X ^ 11 + 25 * X ^ 10 + 32 * X ^ 9 + 28 * X ^ 8 + 32 * X ^ 7 + 25 * X ^ 6 + 24 * X ^ 5 + 18 * X ^ 4 + 12 * X ^ 3 + 7 * X ^ 2 + 4 * X + 1) ∧
    ∀ n : ℕ, 18 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) - a (n - 3) - a (n - 4) + a (n - 5) + a (n - 6) + a (n - 7) + a (n - 8) + 2 * a (n - 9) + a (n - 10) + a (n - 11) + a (n - 12) + a (n - 13) - a (n - 14) - a (n - 15) - a (n - 16) - a (n - 17) - a (n - 18) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a313577

theorem OMA.solution : type_of% @OMA.S_oeis_a313577.main :=
  OMA.S_oeis_a313577.conjecture
