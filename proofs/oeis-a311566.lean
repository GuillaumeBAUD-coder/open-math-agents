import OMAStatements.S_oeis_a311566

namespace OMA.S_oeis_a311566






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 11

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 503675731130
  | 1 => 435242581161
  | 2 => 361960819880
  | 3 => 586406201480
  | 4 => 654839351705
  | 5 => 513409652855
  | 6 => 508255906730
  | 7 => 366540995480
  | 8 => 513123391880
  | 9 => 581556542105
  | 10 => 439841630855
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 10) : ℤ := tget 371694741605 4 8 i.val

def Bc (i : Fin 10) : ℤ := tget 884152218455 4 8 i.val

def Cc (s : Fin 11) (i : Fin 10) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 371694741605 4 i

def BcN (i : ℕ) : ℕ := tgetN 884152218455 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 10) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 10) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 11) (i : Fin 10) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


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
theorem cls (P : Fin 11 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 11 × Fin 11 × ℤ × ℤ) (j : Fin 10) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 10, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 11 × Fin 11 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 11 × Fin 11 × ℤ × ℤ) (j : Fin 10) :
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
theorem farkas (x y : ℤ) (s : Fin 11) (a1 b1 a2 b2 a3 b3 i0 : Fin 10) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
pot k2 ≤ pot i, 11 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 235518174148674213381639943948268925864004044893808300125752846147435058575322336256133389587345429911259083816308604728899881172114233901505334190773272946883960994188145855630352469130777958615281514038497592375392488086129350514717749542025104174773089175175889119173623963710945316519401884164050857432048588321064276070222732184980985811860009019789104708815661689829225291068892613390480426622128783418878494385883330142564324103725077856335912340210600456576997330218140086378983825390320509935455054336772640170507388169621833155687165211257846921169116146863086396934196122843396268253897910076036461480943227925635210072122722027716784513578085059080152598309608917730854087141366324606375204193577055980771722172191370658909005215846860215530831332166621854138703364719265304888543353314842306567512498349678762697111008172313772086703036117701211420194364510466727269629952 5 ((i * 10 + j) * 6 + f)

def fd (i j : Fin 10) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 0 % 10, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 1 % 10, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 10) : ℤ := fd i j 2

def fm2 (i j : Fin 10) : ℤ := fd i j 3

def fm0 (i j : Fin 10) : ℤ := fd i j 4

def fmj (i j : Fin 10) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 10 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 63853883434482808005663917874413670378128548675256320 4 p

def dstv (p : ℕ) : ℕ := tgetN 57040447257024937934934765588026490738718538838598945 4 p

def dxv (p : ℕ) : ℕ := tgetN 181439617908931899923256641 2 p

def dyv (p : ℕ) : ℕ := tgetN 103161669940449455768950085 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 30342864090352716558865103263840000574024767604747464176563765321128889904282313130100601459079059098909868840774632601188407231826933063661385561749879083670049510298118740261408328635551161809332044764544207835200206005375244205091498058413464896958603648991475609119940321765301549943096772106775445105978750239916622850999931924055271785813566453257251219352949266781607410264574257006149134249873407360306760892425351666861409528895719003026655742392896266132058592963756209238436584589406712453523853800823874903560328677495 4 (p * 10 + j)

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
      fdN i j 4 * 19)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 10 || j == (i + 9) % 10

def farOK : Bool := (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 11).all fun s => (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 44).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 10).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 11) (i j : Fin 10) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (11 - Cc s i)

/-- Beyond F = 10, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 11) (i j : Fin 10) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 10 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 11 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 10, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 10 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 3942392526586267560749522354203469822286212450835821159767668699828610023556620882579089032788520447843540642151504867396785005147234276999069365123571950725805381497091818882293276101086788505688088200677135847081665945343251741135395875635687801661241159020328522119900924266849588367528711907722286398424056989113384218117753547820151495065008432207285325605647745056578336746687366444779316388320803092660742535218052794546149020902409715850553390321196497168306214339594528466461958390512977599864819265296095763629854606262347326675898193897620154111672178103219417576431175593991147744526696820443099644615947725098308349635044586822237500172612499861568695121547775507763993569575592087302573213632747211784101534165636894158747943365561888637805656627740304483537485952766427380664796847337976266479704274809310601739156994658272679222239331147652962307122613208318235760741583642988539042104118262085072683220202975995962057665295577437672999398136048159388491835099287216380451157959239722794843062429653044265776144798042181204387394360223897399336825340690422358453264819920929639417962613915990622734295099343908845917315136
  | 1 => 3942392527724690834838290217377336606432303249149501557830461706529646158176010301477181166961910113471346955885915196615972951432986779819442893151059013022702127926580707388893366835153974577748178759392477500356250668705797416397459607225919131123368285167792147879882912826866367094768015972719163981962435824185341552429254657842998142708117958865940203092712527653009809364347921636911017319846731155390123872131852427849362792678341675081723743830310219934422796628069866724308013246943017551189824528836700292395621525798311722003554739300028981902648423198781525819397672185672560015687675883112449191075654495222970970748852638027880403436111747475923505970338376132388413576956089499762719173990490780480635842763702994789460688037714193487393564458990342032220070652458892835110579125602511436225858930663381553209132263225678860858483154366725598644306064349682798883836826473021546733649121714190962733682576212684962177551986000449169097308886507624353900942072979058982272816792562935156030307130568482893640978485436295440770425527559830663032216942105728022775444431739860834655239447760862919298891237277441824037807040
  | 2 => 3942392528407744799291550935281656691045182646215052887485537792070023099162083659662328638436070831116143332424021561221048711901360409956538760722331052034970173698914260289198679791794038294028146640960079089913955422591875391610707237456292347973456517391512207250737477013085205153991045827598070384421915138121480056489139808018471294748835705932458662596416039443139289929254633792502317021403751738946558862913214014338874310396682178206398980135716582728828848721370762800830895684044658825071030408990249135302853209161481860472441599442232236386081236943737262568956790987717427672143480101693935744038933112408942856881352731892439771603280008846079488329301856240378547802343429971477492279240501687096456954221734161496276146045890203913599554689349303701272413111541806855014773528262945954053852821132294959908142532238134768165318811684359527776317982783800629727091664444859196144013587633376676662617519707722451638259507118250607356475151756286276203597042436678716868113365884266900392690119046821360705384303317497088756001974097383924980762312739834947687435779869013950440114319549387241046497115813118125578134592
  | 3 => 3942392529773852728198072371090296860270941440346155546795689963150776981134230376032623581384392266405736085500234290431200232838107670230730495864779532728090046569165498406644649960769358204902640862831935125981304346639766997103487861529135020630133049675984265150937162805261661587200880869927494607125622629132342176849858467706990276405368552386116929270102935446380592177377629283118561321268250834074236555133958815458818451519503239083760714414479318065656243560752829793833494780137798816672499090637084119635066976790145889788403223314971747191379093061586468249213975398772185147032636880239684804052507384882691149730959178148656521937630006537449326250649568251443714154342752105054393937530926908957970086059607967676331005149822239174556821767791616489251759831100042212950633177245195885641220676376851256988256142704047705689239267262707372290515807187603763767342706132125295939482466473797780211581685913144003564692851543812045446892836088755845128601976671697154056586481901611985880682876871111719736142402703139888188186787135270725399747322749949666252941572091382647164797420694318413883931332974844267295942464
  | 4 => 3942392530229222037833579516359843606888235901852094917928074489375802022877654095297710432137509325059248578959332425926263327221990589168525534612224505645942858927649031819839511179832752976918575100386136131805030008082717865049597192049101373377752651404171446972216781507073783208376204975703388775482291588558507269635935353361076845511921795364088769321056371958378087993007987486798430432078651137187191518046440718422901870462320348669947163799507098973926348441477401877652425794756589363127929804788794188561409110660883352518157312454157311360135782066602176735148694194824959405135664186212732394835552952230402521323638324834241337410317296321434145201460586050540222761809977110672699710038479548094621310792208691881992040080325128979227753099975964166674132557885294081488981160583490998765490652194017101680282036639130449029758753368831546173675629054233010960299099312436950906313100487899943403560441394002060610811482792512111711600735777950657612999242919365197081129973716843660221745933130788265924614184635826251815826628120823794934455943837236794120065463766666642795517016309718950906590012463511216495536192
  | 5 => 3942392531595329966740100952168483752571953165854292425875892857925115490430425997859683505315487513458526422935184596044735594087104017262986142721383880141010958307794873742116920569023438587514329261411966316940973617618573427422776338695195230177227905674510275029475133886052090910892215318543706427692600313371765036677464973136031231782115577261193271133385094420612680956488985484395889818109796475128738421052298271449897085017491917571079378014345043929926907992682770785460191687327827006145483553974558188019647612738877395297297777169887979955326577872341477593805634250927928000435462874793987332172797046049131367769343815718207600903928123811245658667935314097701613864453828825356233126084335887741718868759604587095654000894346621082095560254448480014600687010126014628925536498338909236673858849985290705037522676826726958928858898235392841135753726312740884927564834554477032270308723441194505823624865651257646322590891137538474168827047873865520028389653771789729343731641587560383707297844140876148380206994238801408460381213290794168106351674356987060803523738506674546854162924670469967839345622081931124155867201
  | 6 => 3942392532278383931193361670072803837184832562919843755530968943465492431416499356044830976789648231103322799473290960649810984731214494280794464277933857516916733996077142997407404771239278840150511521075744292692964149579473555504583758537045547860728768800523118487964369039252264239055177336870680354161567312439765434985384672590362610150726572643157084566968512803419265577509143871534937288018126916128909958296455297933638069873826702564519419244029459904476119976655998383941284878129117745266358000058134228730008995935926477253151477811635409444323387400750323136338220954153041578383351773740192457232222985435651121802401445032270315625921259602442943906688326753019832748506160112334838396631657461260398743874766930589117431183843875476440727084441470849583422502713745708245276014568897383012669078275682222630321119730227128379926340988145187231639167926093562294071961485906646899004813883105721377184959574269999542283307990550167234259282043710953926320566972861029937883201859419881949719067183983590804991949208625430611159804754244391832965406642617262725080798673825684240564611275982414971535235614065446186377281
  | 7 => 3942392533416807205282129533246670644872964891362429304956095752699453999726621619686743429246582760511316760370134901658270585511837211175954243563323524316419331167022486042473155869436180019493496962846182179923765016906747408056172942223303220431245470237299787559970882232894176165828227827731441733423593519518195649846858492128352672685033469049892021528082555425016885264861130363209935499909104441394427417960187541602956188467934439183044119039840921416206882807986951383768798769749983359441757058736239738109373288247433125380561811868258765209002643194163011747947332414230833233861078396854949159863767241164678736531928763091478171194935336332178179783349749597959630018290763139611470352996516118743417346249706488751114224677641994965346464087053288441396405733396195344129582252660861285820684616218595896785123693912914717434996443442767126320626933006282562764595464281038345090422649271502345768822376741355181240774311305747273095330084943975499693329986131340249925908904450820447783606165910582652545315305785075352704210689880206338759317188157239738643990462057208123413993709380384027258365551581861860974014272
  | 8 => 3942392534555230479370897396420537452561097219805014854381222561933415568036743883328655881703517289919310721266978842666730556116723081190401568863397013819717710952252765659287873424335381653806091410015104823741055872669519788795077367582231339907468357128164176722506228808194923203208095321354887332725483887785789346331288072467441938641613824729944119000380816132597345931912727388869718308978940067702997050417837709268934556332056009274507096942396638191889873156099565953232815843469971894509222538880288071737802715611670810311606413111355222585604821018696715676378127581038035384571401011886043044830928245570688777438635043811854578010291199041815747456630828134349146006849893198567418515031948866592884524153315397172012615458094200182404785373842803216867266650263570413834540651192972083420361838803753151806626152074549078859345265772377536932402629794448447513354735971440990550439860946329030771884642332027426768966954729719198107691983346283588218328242465831707668655300389055081636088562506985578447590642232843916132803458273704433770026427926082744152255124377985339025910446056169943370476945863902142783545409
  | 9 => 3942392535010599789006404541690084175636350151184725494406345204145858242337783904375767353372424079005134522894051174236326394125912772779520280216032084573226589659381321992728330185125613051032956900402166293386802542249487443654798313702248897797465457111894521128153875042990109288720802525080021965706095778970609516419783373709282437796134892221827691419495056946796485111463396488620207909520681016100399124418168838567321858884376407129248892316956504050393728739949069422827944922842903006348873200778970022283006692936928217183878994828143500789939446017825054937455709428778591940645946052577203317038140439959077579254713669760065454829744192958397892751986777632617884352943366541816546832128991368217365758029483878641648108492224868010023149200244276819137711418647008938961875334251572401102426766485725927030706203666863225667201776716526629952705380244318150101187346009453668785419114353035826290997083322492054779137734536417798354421634426308164897665226062507088279931498325639676590424166930188600024395624745504504033717458283793916720293129974944529195115312613521522352746611300751429298828707817644231704458048
  | 10 => 3942392535921338408277418832229177621786856013941470354201518570048915515382630026185122307188367488415999465754528555677611259387735696153584541006668666481418179207513778327887432638690626753527420776551945904852648072980807575393769742186749496410928069995743921763032088999177531196432989702204883687870582386127442825310793247586415667016120057177281652570530273326475702011382591483703812572810401482838199157313704090834912205166331141043593623247455512464891071004228126734309706160336753998577687580473386287817112120308988621599909662182740792093968612560139314354200419821385871105134710625789933143898031206327538030121863362712322540458437830547333559132112615789619358076170380951146601949857556723147945319599683644499409665967945681208497645358421044448929243349113288917962101007318052216379295716415010204793596472932341497634812170116211571631878883599978282364324877931655579837153279648931058943611856006352333258570764106507941080495649996382328786484338699119361703872966081238079893538605629949975103603649499991377514542597742006643011319057170177262945142772157350282526343645534104419285907315444044193365767616
  | _ => 0

def rd (s : Fin 11) (i : Fin 10) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 11) (i : Fin 10) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 11) (i : Fin 10) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 11) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 11) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 11) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 11) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 11) (i : Fin 10) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 44 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 10)
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
theorem far_cert (s : Fin 11) (i j : Fin 10) (hij : nonadj i j) : farCert s i j := by
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

theorem edge_at (p : ℕ) (hp : p < 44) :
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

theorem edge_tab (p : ℕ) (hp : p < 44) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 11) (i : Fin 10) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 10)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 10 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 10 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 11) (i : Fin 10) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 10 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 10
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

theorem far_desc (v : V) (hF : 10 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 11) (a1 a2 a3 : Fin 10) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 11, 0 < 4 * (Cc s 0 - 10) + 1 * (Cc s 9 - 10) + 0 * (Cc s 0 - 10) + 15 * 4 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 11, 0 < 1 * (Cc s 4 - 10) + 4 * (Cc s 5 - 10) + 0 * (Cc s 0 - 10) + 15 * 4 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 11, 0 < 1 * (Cc s 2 - 10) + 0 * (Cc s 0 - 10) + 0 * (Cc s 0 - 10) + 5 * 3 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 11, 0 < 1 * (Cc s 7 - 10) + 0 * (Cc s 0 - 10) + 0 * (Cc s 0 - 10) + 5 * 3 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 11, 0 < 3 * (Cc s 4 - (-1)) + 3 * (Cc s 9 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 10 lies in the cells |x| ≤ 3, |y| ≤ 2 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 11) (hF : F (x, y, s) ≤ 10) :
    -3 ≤ x ∧ x ≤ 3 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 9 0 10 4 1 0 1 0 4 15 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 5 0 10 1 4 0 (-1) 0 4 15 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 0 0 10 1 0 0 0 1 3 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 7 0 0 10 1 0 0 0 (-1) 3 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 4 9 0 (-1) 3 3 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 3, b - 2) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 5353050687039279439191647408296454942499921543023610543006690521255882542368452594358956971135148093944116499829218890430329054894654078889889289114168274302049160262963059394757157743613504327376753072560712263554396770384679103581430660151377080032393844354480789659499058422507790477499182775423825966742757009748665730488325182747715509556890697265558527874272034880238048947468209677867178398445796351801822032407339845504070362447725527273442285723413207090900474038097739668961330371198440354027889886788979488764295572839576976486939376022715794773302838600415951936519202271954904647061614372118376065931213592778821033207005689446177413774834730787712507012608681518272964722688 >>> (6 * ((a * 5 + b) * 11 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 3, b - 2) and class s, potential i plus
15 + 3 a + 5 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 10) : ℕ :=
  tgetN 5190865680 4 i.val * a + tgetN 664249892900 4 i.val * b + tgetN 1645151452596909538370587106429721652076773080046781989714880555350569619121836191878612319684743558811315945969465831244077713235101013538551262353526512481763817436 5 (s * 10 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)) (fnt a b s 8)) (fnt a b s 9)

theorem fnt_tab : ∀ s : Fin 11, ∀ i : Fin 10, (tgetN 5190865680 4 i.val : ℤ) = Ac i + 3 ∧
    (tgetN 664249892900 4 i.val : ℤ) = Bc i + 5 ∧
    (tgetN 1645151452596909538370587106429721652076773080046781989714880555350569619121836191878612319684743558811315945969465831244077713235101013538551262353526512481763817436 5 (s.val * 10 + i.val) : ℤ) = Cc s i - Ac i * 3 - Bc i * 2 + 15 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 11) (i : Fin 10) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 3, (b : ℤ) - 2, s) i + (15 + 3 * a + 5 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 11) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 3, (b : ℤ) - 2, s) + (15 + 3 * a + 5 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 10, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (3 + 5) 1 = FN + 3 dx' + 5 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 7).all fun a => (List.range 5).all fun b => (List.range 11).all fun s =>
    Nat.blt (25 + 3 * a + 5 * b) (FN a b s) || (a == 3 && b == 2 && s == 3) ||
      (Nat.blt (hint a b s) 44 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 8 ==
          FN a b s + 3 * dxv (hint a b s) + 5 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 10) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
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
    have hs0 : s = 3 := Fin.ext (by rw [h3]; rfl)
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
  by_cases hF : F v ≤ 10
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
from below, and for n ≥ 6 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 105 moves every quotient by an integer (`inner_shift`,
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

def BW (i : ℕ) : ℕ := tgetN 884152218455 4 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem A_W (i : Fin 10) : Ac i = (AW i.val : ℤ) - 8 := rfl

theorem B_W (i : Fin 10) : Bc i = (BW i.val : ℤ) - 8 := rfl

theorem C_W (s : Fin 11) (i : Fin 10) : Cc s i = (CW s.val i.val : ℤ) - 8 := rfl

def gcV (k : ℕ) : ℕ := ctabN 161780553 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 10) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 24603336 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 3

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 663176152100 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 5

def Bp (i : Fin 10) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 474288282 3 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 2

def al (i : Fin 10) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 698368 2 k

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
def par (s : Fin 11) (i : Fin 10) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 11) (i j : Fin 10) (c u : ℤ) :
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

theorem par_inj (s : Fin 11) (i : Fin 10) (c : ℤ) : Function.Injective (par s i c) := by
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
(pot_i ≤ pot_j) plus cf0 times (6 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 9769350384460394661641995367835183067855859514945255860381632655664621134769469690929461035981510330948805489730981888 4 k

def cf2V (k : ℕ) : ℕ := ctabN 1310184832553448392511609177481646294524069037909420750760984776601674962009325424239632840588758952402705747243138816 4 k

def cf3V (k : ℕ) : ℕ := ctabN 3238535908777800003991072194406289355683659212399426778858202964360407694638561857404556603302907405946620529199032064 4 k

def cf0V (k : ℕ) : ℕ := ctabN 8759744759314709777794376712767254581853746558362898758496 2 k

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
def certC (s : Fin 11) (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (6 - Cc s i)

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
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 14))

def certGK : PLift ((allR 10 fun i => allR 10 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 10 fun i => allR 10 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 11 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 11) : certS s = true := by
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
theorem certC_ok (s : Fin 11) (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
def lev (s : Fin 11) (i : Fin 10) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 11) (i : Fin 10) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 11) (i j : Fin 10) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 11) (i : Fin 10) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 11) (i : Fin 10) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 11) (i j : Fin 10) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 11) (i : Fin 10) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 11) (i : Fin 10) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 11) (i : Fin 10) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 6 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 11) (i : Fin 10) (n u : ℤ) (hn : 6 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 6 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-4, 4]: a natural-number check. -/
def cbK : PLift ((allR 11 fun s => allR 10 fun i => Nat.ble (CW s i) 12 && Nat.ble 8 (Nat.add (CW s i) 4)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 11) (j : Fin 10) : -4 ≤ Cc s j ∧ Cc s j ≤ 4 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 4)) (1 * n + 4) ×ˢ
    (Finset.Icc (-(1 * n + 4)) (1 * n + 4) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (1 * Ac 4 + 4 * Ac 5 = 15 ∧ 1 * Bc 4 + 4 * Bc 5 = 0 ∧
    4 * Ac 0 + 1 * Ac 9 = (-15) ∧ 4 * Bc 0 + 1 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 5 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-5)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 1 * Ac 4 + 4 * Ac 5 = 15 ∧ 1 * Bc 4 + 4 * Bc 5 = 0 ∧
    4 * Ac 0 + 1 * Ac 9 = (-15) ∧ 4 * Bc 0 + 1 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 5 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-5) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 11) :
    15 * x ≤ 5 * F (x, y, s) + 20 ∧
    15 * (-x) ≤ 5 * F (x, y, s) + 20 ∧
    5 * y ≤ 1 * F (x, y, s) + 4 ∧
    5 * (-y) ≤ 1 * F (x, y, s) + 4 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 4 + 4 * pot (x, y, s) 5 =
      15 * x + 1 * Cc s 4 + 4 * Cc s 5 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 4
  have r0 := le_F (x, y, s) 5
  have k0 := Cbound s 4
  have l0 := Cbound s 5
  have e1 : 4 * pot (x, y, s) 0 + 1 * pot (x, y, s) 9 =
      15 * (-x) + 4 * Cc s 0 + 1 * Cc s 9 := by
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
noncomputable def PF (s : Fin 11) (i : Fin 10) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 11) (i : Fin 10) (n : ℤ) (hn : 6 ≤ n) :
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
def inner (s : Fin 11) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 11) (i : Fin 10) (n : ℤ) (hn : 6 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 11 × Fin 10, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 11 × Fin 10, inner p.1 p.2 n

/-! Shifting n by 105 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 976032398623818216681 7 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 110716315568291441613 7 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 42

def mh (i : Fin 10) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 716492301850330693644 7 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 42

def mk (i : Fin 10) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 10, (105 : ℤ) = gc i * Lq i ∧ 105 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 105 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 10, (105 : ℤ) = gc i * Lq i ∧ 105 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 105 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 11) (i : Fin 10) (n : ℤ) :
    inner s i (n + 105) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 105 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 105 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 105) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 105) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 105) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
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
  ∑ q : Fin 11 × Fin 10, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 105) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 105 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 105 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 6 + r with r < 105: the level is QQ - 0 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 5144733 3 k

def uhMV (k : ℕ) : ℕ := ctabN 335554560 3 k

def ukPV (k : ℕ) : ℕ := ctabN 721442304 3 k

def ukMV (k : ℕ) : ℕ := ctabN 1114146 3 k

def dhV (k : ℕ) : ℕ := ctabN 524656550527 4 k

def dkV (k : ℕ) : ℕ := ctabN 1061569917607 4 k

def mhkV (k : ℕ) : ℕ := ctabN 179945344193637 5 k

def uh (i : Fin 10) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 10) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 10) : ℤ := dhV i.val

def dk (i : Fin 10) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 12816443708671645471276844528102494459846337235380950059132611888640903593046981872714648196743296 3 (Nat.add i (Nat.mul 10 s))

def QQ (s i : ℕ) : ℕ := ctabN 1509299676731223795799061324267689703784102168328520038421311785319600999019381640567707317920483361479278215361348235253624340820020 4 (Nat.add i (Nat.mul 10 s))

def AH (s i : ℕ) : ℕ := ctabN 307202916934420663502523662764875882281860761035999520999442214427882666786864743291940499073965847869435431385778389734136860885435992493671681098042435836497695724474488925604400514950080585269847 6 (Nat.add i (Nat.mul 10 s))

def AK (s i : ℕ) : ℕ := ctabN 2868572969134177457522860178572561095766373572573033524872673316065620575575158293541072602872668068208078828439773232016571431120298328254466593862034413760025117713406582828259222204180539980386757 6 (Nat.add i (Nat.mul 10 s))

def WH (s i : ℕ) : ℕ := ctabN 2520529446362233109681140287826333036242065747279965295017546814993876005031513982072689153379371568485132544484530956365632753766353001303772480858077003826531428075083397409869069470601613386186752 6 (Nat.add i (Nat.mul 10 s))

def WK (s i : ℕ) : ℕ := ctabN 12974440518450656532243843213642463627251211527522888468935220522426032071098052114725460617449100159748946243183373737057264455727225736768294680431553039403222801730444992742278710062995213088 6 (Nat.add i (Nat.mul 10 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 11 fun s => allR 10 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq 14 (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 11) (i : Fin 10) :
    PP s.val i.val < gcV i.val ∧
    (6 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 0) + PP s.val i.val ∧
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

/-- Piece (s, i) at n = 6 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 6 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 11) (i : Fin 10) (r : ℕ) :
    ((6 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (6 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 0) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 11) (i : Fin 10) (r : ℕ) (hr : r < 105) :
    inner s i ((6 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (105 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 105 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((6 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r := by
      rw [lev, show (6 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((6 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((6 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 253777003574756039264025141079382101939901522186066919389610217274897366870516296989903361592145492507786716380757936503351906593573974869134834183645490340061390879503181616896846719791468759680587452097755738529612345994368244931393516366832801679220141957089581068139750857429455796 9 k

def tblV (k : ℕ) : ℕ := ctabN 253772447776260053594687978529462068057446509174447045782944798325039475767026977968659373805829318233718329842611214144833169645795450774357552798534801533092650482631110816630370149567599620378112776096510273347140797126467519268402200135696893348078757624122227459831406779266240516 9 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 105. -/
def dv (t : ℕ) : ℕ := dtabV (t % 105)

/-- The sequence in closed form: b(n + 105) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 105) + tblV ((n - 1) % 105)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 105) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 105 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 105 - 1 = n - 1 + 105 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 105)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 105) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 105 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 105 - 1 = n - 1 + 105 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 105)]
  ring

/-- b on the residue class of 1 + j mod 105. -/
theorem b_res (k j : ℕ) (hj : j < 105) : b (105 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (105 * k + (1 + j) < 1) by omega),
    show 105 * k + (1 + j) - 1 = j + 105 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 105), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 6 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 105 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 11 fun s => allR 10 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 11 fun s => sumR 10 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 6 r)) &&
    Nat.beq (sumR 11 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 1 (dv (Nat.add 5 r)))

/-! The window n = 6, ..., 110, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 13 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 26 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK3 : PLift (allI 39 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK4 : PLift (allI 52 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK5 : PLift (allI 65 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK6 : PLift (allI 78 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK7 : PLift (allI 91 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK8 : PLift (allI 104 1 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 105) :
    (∀ s, s < 11 → ∀ i, i < 10 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 11 fun s => sumR 10 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (6 + r) ∧
    (sumR 11 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0) = 1 * dv (5 + r) := by
  have h : periodR r = true := by
    rcases (show r < 13 ∨ (13 ≤ r ∧ r < 26) ∨ (26 ≤ r ∧ r < 39) ∨ (39 ≤ r ∧ r < 52) ∨ (52 ≤ r ∧ r < 65) ∨ (65 ≤ r ∧ r < 78) ∨ (78 ≤ r ∧ r < 91) ∨ (91 ≤ r ∧ r < 104) ∨ 104 ≤ r by omega) with h | h | h | h | h | h | h | h | h
    · exact allI_get _ _ _ periodK0.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK1.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK2.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK3.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK4.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK5.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK6.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK7.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK8.down r (by omega) (by omega)
  simp only [periodR, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun s hs i hi hd => ?_, h2, h3⟩
  have h4 := (allR_iff _ _).1 ((allR_iff _ _).1 h1 s hs) i hi
  rw [hd] at h4
  simpa using h4

theorem innerZ_eq (s i r : ℕ) (hs : s < 11) (hi : i < 10) (hr : r < 105) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 11 fun s => sumR 10 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 11 × Fin 10, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 10 fun i => f s i : ℕ) : ℤ)) 11]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 10]

theorem S_window (r : ℕ) (hr : r < 105) : S ((6 : ℤ) + r) = b (6 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 105) : Gs ((6 : ℤ) + r) = ((1 * dv (5 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 6 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 11) (i : Fin 10) (n : ℤ) (hn : 6 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 6 + t := ⟨(n - 6).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 105
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 105) (by omega) (by omega)
      have e : (6 : ℤ) + t = (6 + (t - 105 : ℕ)) + 105 := by
        push_cast [Nat.cast_sub (by omega : 105 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 6 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 105 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 6 ≤ n) : (1 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 6) % 105 < 105 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((6 : ℤ) + (((n - 6) % 105 : ℕ) : ℤ)) + 105 * (((n - 6) / 105 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (5 + (n - 6) % 105) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 6 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 111
    · obtain ⟨r, rfl⟩ : ∃ r, n = 6 + r := ⟨n - 6, by omega⟩
      push_cast
      exact S_window r (by omega)
    · have h1 := ih (n - 105) (by omega) (by omega)
      have h2 := S_shift ((n - 105 : ℕ) : ℤ)
      have h3 := b_shift (n - 105) (by omega)
      have h4 := grow (n - 105) (by omega)
      rw [show n - 105 + 105 = n by omega] at h3
      rw [show ((n - 105 : ℕ) : ℤ) + 105 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 5 lie in the box -3 ≤ x ≤ 3, -1 ≤ y ≤ 1 (`small_box`). In natural-number
coordinates a = x + 3, b = y + 1 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 11) (h : F (x, y, s) ≤ 5) :
    -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 3, (b : ℤ) - 1, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 32) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 3) (BW i)) 8) (Nat.add (Nat.mul 8 a) (Nat.mul 8 b))

theorem pot_box (a b : ℕ) (s : Fin 11) (i : Fin 10) :
    pot ((a : ℤ) - 3, (b : ℤ) - 1, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 10 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 11) : F ((a : ℤ) - 3, (b : ℤ) - 1, s) = (FN a b s.val : ℤ) := by
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
  sumR 7 fun a => sumR 3 fun b => sumR 11 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 0 .. 5, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 0 6 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 6) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 11) : V := ((q.1 : ℤ) - 3, (q.2.1 : ℤ) - 1, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 5) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 7 ×ˢ (Finset.range 3 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 11 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 11]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 6 are counted in the
box, those from 6 on are S(n), and both agree with the closed form b (`a_eq_b`). The step from n to
n + 105, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
their base cases checked by the kernel on b. -/

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
    exact small_eq n (by omega) h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 105) = a(n) + dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 105) = a n + dv (n - 1) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 436 ∧ tblV 0 = 4 ∧ dv 1 = 457 ∧ tblV 1 = 8 ∧ dv 2 = 436 ∧ tblV 2 = 12 ∧ dv 3 = 457 ∧ tblV 3 = 18 ∧ dv 4 = 436 ∧ tblV 4 = 21 ∧ dv 5 = 436 ∧ tblV 5 = 25 ∧ dv 6 = 457 ∧ tblV 6 = 31 ∧ dv 7 = 436 ∧ tblV 7 = 32) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 457 ∧ tblV 8 = 39 ∧ dv 9 = 436 ∧ tblV 9 = 42 ∧ dv 10 = 436 ∧ tblV 10 = 45 ∧ dv 11 = 457 ∧ tblV 11 = 53 ∧ dv 12 = 436 ∧ tblV 12 = 54 ∧ dv 13 = 457 ∧ tblV 13 = 61 ∧ dv 14 = 436 ∧ tblV 14 = 62 ∧ dv 15 = 436 ∧ tblV 15 = 66) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 457 ∧ tblV 16 = 74 ∧ dv 17 = 436 ∧ tblV 17 = 74 ∧ dv 18 = 457 ∧ tblV 18 = 84 ∧ dv 19 = 436 ∧ tblV 19 = 83 ∧ dv 20 = 436 ∧ tblV 20 = 87 ∧ dv 21 = 457 ∧ tblV 21 = 96 ∧ dv 22 = 436 ∧ tblV 22 = 94 ∧ dv 23 = 457 ∧ tblV 23 = 105) :=
  ⟨by decide +kernel⟩

def closedK3 : PLift (dv 24 = 436 ∧ tblV 24 = 104 ∧ dv 25 = 436 ∧ tblV 25 = 108 ∧ dv 26 = 457 ∧ tblV 26 = 118 ∧ dv 27 = 436 ∧ tblV 27 = 116 ∧ dv 28 = 457 ∧ tblV 28 = 126 ∧ dv 29 = 436 ∧ tblV 29 = 124 ∧ dv 30 = 436 ∧ tblV 30 = 129 ∧ dv 31 = 457 ∧ tblV 31 = 139) :=
  ⟨by decide +kernel⟩

def closedK4 : PLift (dv 32 = 436 ∧ tblV 32 = 137 ∧ dv 33 = 457 ∧ tblV 33 = 149 ∧ dv 34 = 436 ∧ tblV 34 = 145 ∧ dv 35 = 436 ∧ tblV 35 = 149 ∧ dv 36 = 457 ∧ tblV 36 = 161 ∧ dv 37 = 436 ∧ tblV 37 = 157 ∧ dv 38 = 457 ∧ tblV 38 = 170 ∧ dv 39 = 436 ∧ tblV 39 = 167) :=
  ⟨by decide +kernel⟩

def closedK5 : PLift (dv 40 = 436 ∧ tblV 40 = 170 ∧ dv 41 = 457 ∧ tblV 41 = 183 ∧ dv 42 = 436 ∧ tblV 42 = 178 ∧ dv 43 = 457 ∧ tblV 43 = 191 ∧ dv 44 = 436 ∧ tblV 44 = 187 ∧ dv 45 = 436 ∧ tblV 45 = 191 ∧ dv 46 = 457 ∧ tblV 46 = 205 ∧ dv 47 = 436 ∧ tblV 47 = 199) :=
  ⟨by decide +kernel⟩

def closedK6 : PLift (dv 48 = 457 ∧ tblV 48 = 214 ∧ dv 49 = 436 ∧ tblV 49 = 207 ∧ dv 50 = 436 ∧ tblV 50 = 211 ∧ dv 51 = 457 ∧ tblV 51 = 227 ∧ dv 52 = 436 ∧ tblV 52 = 219 ∧ dv 53 = 457 ∧ tblV 53 = 236 ∧ dv 54 = 436 ∧ tblV 54 = 229 ∧ dv 55 = 436 ∧ tblV 55 = 232) :=
  ⟨by decide +kernel⟩

def closedK7 : PLift (dv 56 = 457 ∧ tblV 56 = 248 ∧ dv 57 = 436 ∧ tblV 57 = 240 ∧ dv 58 = 457 ∧ tblV 58 = 257 ∧ dv 59 = 436 ∧ tblV 59 = 249 ∧ dv 60 = 436 ∧ tblV 60 = 254 ∧ dv 61 = 457 ∧ tblV 61 = 270 ∧ dv 62 = 436 ∧ tblV 62 = 261 ∧ dv 63 = 457 ∧ tblV 63 = 279) :=
  ⟨by decide +kernel⟩

def closedK8 : PLift (dv 64 = 436 ∧ tblV 64 = 269 ∧ dv 65 = 436 ∧ tblV 65 = 274 ∧ dv 66 = 457 ∧ tblV 66 = 292 ∧ dv 67 = 436 ∧ tblV 67 = 282 ∧ dv 68 = 457 ∧ tblV 68 = 301 ∧ dv 69 = 436 ∧ tblV 69 = 291 ∧ dv 70 = 436 ∧ tblV 70 = 294 ∧ dv 71 = 457 ∧ tblV 71 = 313) :=
  ⟨by decide +kernel⟩

def closedK9 : PLift (dv 72 = 436 ∧ tblV 72 = 303 ∧ dv 73 = 457 ∧ tblV 73 = 322 ∧ dv 74 = 436 ∧ tblV 74 = 312 ∧ dv 75 = 436 ∧ tblV 75 = 316 ∧ dv 76 = 457 ∧ tblV 76 = 335 ∧ dv 77 = 436 ∧ tblV 77 = 323 ∧ dv 78 = 457 ∧ tblV 78 = 344 ∧ dv 79 = 436 ∧ tblV 79 = 332) :=
  ⟨by decide +kernel⟩

def closedK10 : PLift (dv 80 = 436 ∧ tblV 80 = 336 ∧ dv 81 = 457 ∧ tblV 81 = 358 ∧ dv 82 = 436 ∧ tblV 82 = 344 ∧ dv 83 = 457 ∧ tblV 83 = 366 ∧ dv 84 = 436 ∧ tblV 84 = 353 ∧ dv 85 = 436 ∧ tblV 85 = 356 ∧ dv 86 = 457 ∧ tblV 86 = 379 ∧ dv 87 = 436 ∧ tblV 87 = 365) :=
  ⟨by decide +kernel⟩

def closedK11 : PLift (dv 88 = 457 ∧ tblV 88 = 388 ∧ dv 89 = 436 ∧ tblV 89 = 374 ∧ dv 90 = 436 ∧ tblV 90 = 378 ∧ dv 91 = 457 ∧ tblV 91 = 400 ∧ dv 92 = 436 ∧ tblV 92 = 385 ∧ dv 93 = 457 ∧ tblV 93 = 410 ∧ dv 94 = 436 ∧ tblV 94 = 394 ∧ dv 95 = 436 ∧ tblV 95 = 399) :=
  ⟨by decide +kernel⟩

def closedK12 : PLift (dv 96 = 457 ∧ tblV 96 = 423 ∧ dv 97 = 436 ∧ tblV 97 = 406 ∧ dv 98 = 457 ∧ tblV 98 = 431 ∧ dv 99 = 436 ∧ tblV 99 = 415 ∧ dv 100 = 436 ∧ tblV 100 = 419 ∧ dv 101 = 457 ∧ tblV 101 = 444 ∧ dv 102 = 436 ∧ tblV 102 = 428 ∧ dv 103 = 457 ∧ tblV 103 = 453) :=
  ⟨by decide +kernel⟩

def closedK13 : PLift (dv 104 = 436 ∧ tblV 104 = 436) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (105 * k + 1) = 436 * k + 4 ∧
    a (105 * k + 2) = 457 * k + 8 ∧
    a (105 * k + 3) = 436 * k + 12 ∧
    a (105 * k + 4) = 457 * k + 18 ∧
    a (105 * k + 5) = 436 * k + 21 ∧
    a (105 * k + 6) = 436 * k + 25 ∧
    a (105 * k + 7) = 457 * k + 31 ∧
    a (105 * k + 8) = 436 * k + 32 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 1 = 105 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 105 * k + 2 = 105 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 105 * k + 3 = 105 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 105 * k + 4 = 105 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 105 * k + 5 = 105 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 105 * k + 6 = 105 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 105 * k + 7 = 105 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 105 * k + 8 = 105 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (105 * k + 9) = 457 * k + 39 ∧
    a (105 * k + 10) = 436 * k + 42 ∧
    a (105 * k + 11) = 436 * k + 45 ∧
    a (105 * k + 12) = 457 * k + 53 ∧
    a (105 * k + 13) = 436 * k + 54 ∧
    a (105 * k + 14) = 457 * k + 61 ∧
    a (105 * k + 15) = 436 * k + 62 ∧
    a (105 * k + 16) = 436 * k + 66 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 9 = 105 * k + (1 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 105 * k + 10 = 105 * k + (1 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 105 * k + 11 = 105 * k + (1 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 105 * k + 12 = 105 * k + (1 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 105 * k + 13 = 105 * k + (1 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 105 * k + 14 = 105 * k + (1 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 105 * k + 15 = 105 * k + (1 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 105 * k + 16 = 105 * k + (1 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (105 * k + 17) = 457 * k + 74 ∧
    a (105 * k + 18) = 436 * k + 74 ∧
    a (105 * k + 19) = 457 * k + 84 ∧
    a (105 * k + 20) = 436 * k + 83 ∧
    a (105 * k + 21) = 436 * k + 87 ∧
    a (105 * k + 22) = 457 * k + 96 ∧
    a (105 * k + 23) = 436 * k + 94 ∧
    a (105 * k + 24) = 457 * k + 105 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 17 = 105 * k + (1 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 105 * k + 18 = 105 * k + (1 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 105 * k + 19 = 105 * k + (1 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 105 * k + 20 = 105 * k + (1 + 19) from rfl, b_res k 19 (by decide), c38, c39]
  · rw [show 105 * k + 21 = 105 * k + (1 + 20) from rfl, b_res k 20 (by decide), c40, c41]
  · rw [show 105 * k + 22 = 105 * k + (1 + 21) from rfl, b_res k 21 (by decide), c42, c43]
  · rw [show 105 * k + 23 = 105 * k + (1 + 22) from rfl, b_res k 22 (by decide), c44, c45]
  · rw [show 105 * k + 24 = 105 * k + (1 + 23) from rfl, b_res k 23 (by decide), c46, c47]

theorem a_closed3 (k : ℕ) :
    a (105 * k + 25) = 436 * k + 104 ∧
    a (105 * k + 26) = 436 * k + 108 ∧
    a (105 * k + 27) = 457 * k + 118 ∧
    a (105 * k + 28) = 436 * k + 116 ∧
    a (105 * k + 29) = 457 * k + 126 ∧
    a (105 * k + 30) = 436 * k + 124 ∧
    a (105 * k + 31) = 436 * k + 129 ∧
    a (105 * k + 32) = 457 * k + 139 := by
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := closedK3.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 25 = 105 * k + (1 + 24) from rfl, b_res k 24 (by decide), c48, c49]
  · rw [show 105 * k + 26 = 105 * k + (1 + 25) from rfl, b_res k 25 (by decide), c50, c51]
  · rw [show 105 * k + 27 = 105 * k + (1 + 26) from rfl, b_res k 26 (by decide), c52, c53]
  · rw [show 105 * k + 28 = 105 * k + (1 + 27) from rfl, b_res k 27 (by decide), c54, c55]
  · rw [show 105 * k + 29 = 105 * k + (1 + 28) from rfl, b_res k 28 (by decide), c56, c57]
  · rw [show 105 * k + 30 = 105 * k + (1 + 29) from rfl, b_res k 29 (by decide), c58, c59]
  · rw [show 105 * k + 31 = 105 * k + (1 + 30) from rfl, b_res k 30 (by decide), c60, c61]
  · rw [show 105 * k + 32 = 105 * k + (1 + 31) from rfl, b_res k 31 (by decide), c62, c63]

theorem a_closed4 (k : ℕ) :
    a (105 * k + 33) = 436 * k + 137 ∧
    a (105 * k + 34) = 457 * k + 149 ∧
    a (105 * k + 35) = 436 * k + 145 ∧
    a (105 * k + 36) = 436 * k + 149 ∧
    a (105 * k + 37) = 457 * k + 161 ∧
    a (105 * k + 38) = 436 * k + 157 ∧
    a (105 * k + 39) = 457 * k + 170 ∧
    a (105 * k + 40) = 436 * k + 167 := by
  obtain ⟨c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79⟩ := closedK4.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 33 = 105 * k + (1 + 32) from rfl, b_res k 32 (by decide), c64, c65]
  · rw [show 105 * k + 34 = 105 * k + (1 + 33) from rfl, b_res k 33 (by decide), c66, c67]
  · rw [show 105 * k + 35 = 105 * k + (1 + 34) from rfl, b_res k 34 (by decide), c68, c69]
  · rw [show 105 * k + 36 = 105 * k + (1 + 35) from rfl, b_res k 35 (by decide), c70, c71]
  · rw [show 105 * k + 37 = 105 * k + (1 + 36) from rfl, b_res k 36 (by decide), c72, c73]
  · rw [show 105 * k + 38 = 105 * k + (1 + 37) from rfl, b_res k 37 (by decide), c74, c75]
  · rw [show 105 * k + 39 = 105 * k + (1 + 38) from rfl, b_res k 38 (by decide), c76, c77]
  · rw [show 105 * k + 40 = 105 * k + (1 + 39) from rfl, b_res k 39 (by decide), c78, c79]

theorem a_closed5 (k : ℕ) :
    a (105 * k + 41) = 436 * k + 170 ∧
    a (105 * k + 42) = 457 * k + 183 ∧
    a (105 * k + 43) = 436 * k + 178 ∧
    a (105 * k + 44) = 457 * k + 191 ∧
    a (105 * k + 45) = 436 * k + 187 ∧
    a (105 * k + 46) = 436 * k + 191 ∧
    a (105 * k + 47) = 457 * k + 205 ∧
    a (105 * k + 48) = 436 * k + 199 := by
  obtain ⟨c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95⟩ := closedK5.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 41 = 105 * k + (1 + 40) from rfl, b_res k 40 (by decide), c80, c81]
  · rw [show 105 * k + 42 = 105 * k + (1 + 41) from rfl, b_res k 41 (by decide), c82, c83]
  · rw [show 105 * k + 43 = 105 * k + (1 + 42) from rfl, b_res k 42 (by decide), c84, c85]
  · rw [show 105 * k + 44 = 105 * k + (1 + 43) from rfl, b_res k 43 (by decide), c86, c87]
  · rw [show 105 * k + 45 = 105 * k + (1 + 44) from rfl, b_res k 44 (by decide), c88, c89]
  · rw [show 105 * k + 46 = 105 * k + (1 + 45) from rfl, b_res k 45 (by decide), c90, c91]
  · rw [show 105 * k + 47 = 105 * k + (1 + 46) from rfl, b_res k 46 (by decide), c92, c93]
  · rw [show 105 * k + 48 = 105 * k + (1 + 47) from rfl, b_res k 47 (by decide), c94, c95]

theorem a_closed6 (k : ℕ) :
    a (105 * k + 49) = 457 * k + 214 ∧
    a (105 * k + 50) = 436 * k + 207 ∧
    a (105 * k + 51) = 436 * k + 211 ∧
    a (105 * k + 52) = 457 * k + 227 ∧
    a (105 * k + 53) = 436 * k + 219 ∧
    a (105 * k + 54) = 457 * k + 236 ∧
    a (105 * k + 55) = 436 * k + 229 ∧
    a (105 * k + 56) = 436 * k + 232 := by
  obtain ⟨c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111⟩ := closedK6.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 49 = 105 * k + (1 + 48) from rfl, b_res k 48 (by decide), c96, c97]
  · rw [show 105 * k + 50 = 105 * k + (1 + 49) from rfl, b_res k 49 (by decide), c98, c99]
  · rw [show 105 * k + 51 = 105 * k + (1 + 50) from rfl, b_res k 50 (by decide), c100, c101]
  · rw [show 105 * k + 52 = 105 * k + (1 + 51) from rfl, b_res k 51 (by decide), c102, c103]
  · rw [show 105 * k + 53 = 105 * k + (1 + 52) from rfl, b_res k 52 (by decide), c104, c105]
  · rw [show 105 * k + 54 = 105 * k + (1 + 53) from rfl, b_res k 53 (by decide), c106, c107]
  · rw [show 105 * k + 55 = 105 * k + (1 + 54) from rfl, b_res k 54 (by decide), c108, c109]
  · rw [show 105 * k + 56 = 105 * k + (1 + 55) from rfl, b_res k 55 (by decide), c110, c111]

theorem a_closed7 (k : ℕ) :
    a (105 * k + 57) = 457 * k + 248 ∧
    a (105 * k + 58) = 436 * k + 240 ∧
    a (105 * k + 59) = 457 * k + 257 ∧
    a (105 * k + 60) = 436 * k + 249 ∧
    a (105 * k + 61) = 436 * k + 254 ∧
    a (105 * k + 62) = 457 * k + 270 ∧
    a (105 * k + 63) = 436 * k + 261 ∧
    a (105 * k + 64) = 457 * k + 279 := by
  obtain ⟨c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127⟩ := closedK7.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 57 = 105 * k + (1 + 56) from rfl, b_res k 56 (by decide), c112, c113]
  · rw [show 105 * k + 58 = 105 * k + (1 + 57) from rfl, b_res k 57 (by decide), c114, c115]
  · rw [show 105 * k + 59 = 105 * k + (1 + 58) from rfl, b_res k 58 (by decide), c116, c117]
  · rw [show 105 * k + 60 = 105 * k + (1 + 59) from rfl, b_res k 59 (by decide), c118, c119]
  · rw [show 105 * k + 61 = 105 * k + (1 + 60) from rfl, b_res k 60 (by decide), c120, c121]
  · rw [show 105 * k + 62 = 105 * k + (1 + 61) from rfl, b_res k 61 (by decide), c122, c123]
  · rw [show 105 * k + 63 = 105 * k + (1 + 62) from rfl, b_res k 62 (by decide), c124, c125]
  · rw [show 105 * k + 64 = 105 * k + (1 + 63) from rfl, b_res k 63 (by decide), c126, c127]

theorem a_closed8 (k : ℕ) :
    a (105 * k + 65) = 436 * k + 269 ∧
    a (105 * k + 66) = 436 * k + 274 ∧
    a (105 * k + 67) = 457 * k + 292 ∧
    a (105 * k + 68) = 436 * k + 282 ∧
    a (105 * k + 69) = 457 * k + 301 ∧
    a (105 * k + 70) = 436 * k + 291 ∧
    a (105 * k + 71) = 436 * k + 294 ∧
    a (105 * k + 72) = 457 * k + 313 := by
  obtain ⟨c128, c129, c130, c131, c132, c133, c134, c135, c136, c137, c138, c139, c140, c141, c142, c143⟩ := closedK8.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 65 = 105 * k + (1 + 64) from rfl, b_res k 64 (by decide), c128, c129]
  · rw [show 105 * k + 66 = 105 * k + (1 + 65) from rfl, b_res k 65 (by decide), c130, c131]
  · rw [show 105 * k + 67 = 105 * k + (1 + 66) from rfl, b_res k 66 (by decide), c132, c133]
  · rw [show 105 * k + 68 = 105 * k + (1 + 67) from rfl, b_res k 67 (by decide), c134, c135]
  · rw [show 105 * k + 69 = 105 * k + (1 + 68) from rfl, b_res k 68 (by decide), c136, c137]
  · rw [show 105 * k + 70 = 105 * k + (1 + 69) from rfl, b_res k 69 (by decide), c138, c139]
  · rw [show 105 * k + 71 = 105 * k + (1 + 70) from rfl, b_res k 70 (by decide), c140, c141]
  · rw [show 105 * k + 72 = 105 * k + (1 + 71) from rfl, b_res k 71 (by decide), c142, c143]

theorem a_closed9 (k : ℕ) :
    a (105 * k + 73) = 436 * k + 303 ∧
    a (105 * k + 74) = 457 * k + 322 ∧
    a (105 * k + 75) = 436 * k + 312 ∧
    a (105 * k + 76) = 436 * k + 316 ∧
    a (105 * k + 77) = 457 * k + 335 ∧
    a (105 * k + 78) = 436 * k + 323 ∧
    a (105 * k + 79) = 457 * k + 344 ∧
    a (105 * k + 80) = 436 * k + 332 := by
  obtain ⟨c144, c145, c146, c147, c148, c149, c150, c151, c152, c153, c154, c155, c156, c157, c158, c159⟩ := closedK9.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 73 = 105 * k + (1 + 72) from rfl, b_res k 72 (by decide), c144, c145]
  · rw [show 105 * k + 74 = 105 * k + (1 + 73) from rfl, b_res k 73 (by decide), c146, c147]
  · rw [show 105 * k + 75 = 105 * k + (1 + 74) from rfl, b_res k 74 (by decide), c148, c149]
  · rw [show 105 * k + 76 = 105 * k + (1 + 75) from rfl, b_res k 75 (by decide), c150, c151]
  · rw [show 105 * k + 77 = 105 * k + (1 + 76) from rfl, b_res k 76 (by decide), c152, c153]
  · rw [show 105 * k + 78 = 105 * k + (1 + 77) from rfl, b_res k 77 (by decide), c154, c155]
  · rw [show 105 * k + 79 = 105 * k + (1 + 78) from rfl, b_res k 78 (by decide), c156, c157]
  · rw [show 105 * k + 80 = 105 * k + (1 + 79) from rfl, b_res k 79 (by decide), c158, c159]

theorem a_closed10 (k : ℕ) :
    a (105 * k + 81) = 436 * k + 336 ∧
    a (105 * k + 82) = 457 * k + 358 ∧
    a (105 * k + 83) = 436 * k + 344 ∧
    a (105 * k + 84) = 457 * k + 366 ∧
    a (105 * k + 85) = 436 * k + 353 ∧
    a (105 * k + 86) = 436 * k + 356 ∧
    a (105 * k + 87) = 457 * k + 379 ∧
    a (105 * k + 88) = 436 * k + 365 := by
  obtain ⟨c160, c161, c162, c163, c164, c165, c166, c167, c168, c169, c170, c171, c172, c173, c174, c175⟩ := closedK10.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 81 = 105 * k + (1 + 80) from rfl, b_res k 80 (by decide), c160, c161]
  · rw [show 105 * k + 82 = 105 * k + (1 + 81) from rfl, b_res k 81 (by decide), c162, c163]
  · rw [show 105 * k + 83 = 105 * k + (1 + 82) from rfl, b_res k 82 (by decide), c164, c165]
  · rw [show 105 * k + 84 = 105 * k + (1 + 83) from rfl, b_res k 83 (by decide), c166, c167]
  · rw [show 105 * k + 85 = 105 * k + (1 + 84) from rfl, b_res k 84 (by decide), c168, c169]
  · rw [show 105 * k + 86 = 105 * k + (1 + 85) from rfl, b_res k 85 (by decide), c170, c171]
  · rw [show 105 * k + 87 = 105 * k + (1 + 86) from rfl, b_res k 86 (by decide), c172, c173]
  · rw [show 105 * k + 88 = 105 * k + (1 + 87) from rfl, b_res k 87 (by decide), c174, c175]

theorem a_closed11 (k : ℕ) :
    a (105 * k + 89) = 457 * k + 388 ∧
    a (105 * k + 90) = 436 * k + 374 ∧
    a (105 * k + 91) = 436 * k + 378 ∧
    a (105 * k + 92) = 457 * k + 400 ∧
    a (105 * k + 93) = 436 * k + 385 ∧
    a (105 * k + 94) = 457 * k + 410 ∧
    a (105 * k + 95) = 436 * k + 394 ∧
    a (105 * k + 96) = 436 * k + 399 := by
  obtain ⟨c176, c177, c178, c179, c180, c181, c182, c183, c184, c185, c186, c187, c188, c189, c190, c191⟩ := closedK11.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 89 = 105 * k + (1 + 88) from rfl, b_res k 88 (by decide), c176, c177]
  · rw [show 105 * k + 90 = 105 * k + (1 + 89) from rfl, b_res k 89 (by decide), c178, c179]
  · rw [show 105 * k + 91 = 105 * k + (1 + 90) from rfl, b_res k 90 (by decide), c180, c181]
  · rw [show 105 * k + 92 = 105 * k + (1 + 91) from rfl, b_res k 91 (by decide), c182, c183]
  · rw [show 105 * k + 93 = 105 * k + (1 + 92) from rfl, b_res k 92 (by decide), c184, c185]
  · rw [show 105 * k + 94 = 105 * k + (1 + 93) from rfl, b_res k 93 (by decide), c186, c187]
  · rw [show 105 * k + 95 = 105 * k + (1 + 94) from rfl, b_res k 94 (by decide), c188, c189]
  · rw [show 105 * k + 96 = 105 * k + (1 + 95) from rfl, b_res k 95 (by decide), c190, c191]

theorem a_closed12 (k : ℕ) :
    a (105 * k + 97) = 457 * k + 423 ∧
    a (105 * k + 98) = 436 * k + 406 ∧
    a (105 * k + 99) = 457 * k + 431 ∧
    a (105 * k + 100) = 436 * k + 415 ∧
    a (105 * k + 101) = 436 * k + 419 ∧
    a (105 * k + 102) = 457 * k + 444 ∧
    a (105 * k + 103) = 436 * k + 428 ∧
    a (105 * k + 104) = 457 * k + 453 := by
  obtain ⟨c192, c193, c194, c195, c196, c197, c198, c199, c200, c201, c202, c203, c204, c205, c206, c207⟩ := closedK12.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 105 * k + 97 = 105 * k + (1 + 96) from rfl, b_res k 96 (by decide), c192, c193]
  · rw [show 105 * k + 98 = 105 * k + (1 + 97) from rfl, b_res k 97 (by decide), c194, c195]
  · rw [show 105 * k + 99 = 105 * k + (1 + 98) from rfl, b_res k 98 (by decide), c196, c197]
  · rw [show 105 * k + 100 = 105 * k + (1 + 99) from rfl, b_res k 99 (by decide), c198, c199]
  · rw [show 105 * k + 101 = 105 * k + (1 + 100) from rfl, b_res k 100 (by decide), c200, c201]
  · rw [show 105 * k + 102 = 105 * k + (1 + 101) from rfl, b_res k 101 (by decide), c202, c203]
  · rw [show 105 * k + 103 = 105 * k + (1 + 102) from rfl, b_res k 102 (by decide), c204, c205]
  · rw [show 105 * k + 104 = 105 * k + (1 + 103) from rfl, b_res k 103 (by decide), c206, c207]

theorem a_closed13 (k : ℕ) :
    a (105 * k + 105) = 436 * k + 436 := by
  obtain ⟨c208, c209⟩ := closedK13.down
  simp only [a_eq_b]
  rw [show 105 * k + 105 = 105 * k + (1 + 104) from rfl, b_res k 104 (by decide), c208, c209]

/-- The closed form per residue of n mod 105, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (105 * k + 1) = 436 * k + 4 ∧
    a (105 * k + 2) = 457 * k + 8 ∧
    a (105 * k + 3) = 436 * k + 12 ∧
    a (105 * k + 4) = 457 * k + 18 ∧
    a (105 * k + 5) = 436 * k + 21 ∧
    a (105 * k + 6) = 436 * k + 25 ∧
    a (105 * k + 7) = 457 * k + 31 ∧
    a (105 * k + 8) = 436 * k + 32 ∧
    a (105 * k + 9) = 457 * k + 39 ∧
    a (105 * k + 10) = 436 * k + 42 ∧
    a (105 * k + 11) = 436 * k + 45 ∧
    a (105 * k + 12) = 457 * k + 53 ∧
    a (105 * k + 13) = 436 * k + 54 ∧
    a (105 * k + 14) = 457 * k + 61 ∧
    a (105 * k + 15) = 436 * k + 62 ∧
    a (105 * k + 16) = 436 * k + 66 ∧
    a (105 * k + 17) = 457 * k + 74 ∧
    a (105 * k + 18) = 436 * k + 74 ∧
    a (105 * k + 19) = 457 * k + 84 ∧
    a (105 * k + 20) = 436 * k + 83 ∧
    a (105 * k + 21) = 436 * k + 87 ∧
    a (105 * k + 22) = 457 * k + 96 ∧
    a (105 * k + 23) = 436 * k + 94 ∧
    a (105 * k + 24) = 457 * k + 105 ∧
    a (105 * k + 25) = 436 * k + 104 ∧
    a (105 * k + 26) = 436 * k + 108 ∧
    a (105 * k + 27) = 457 * k + 118 ∧
    a (105 * k + 28) = 436 * k + 116 ∧
    a (105 * k + 29) = 457 * k + 126 ∧
    a (105 * k + 30) = 436 * k + 124 ∧
    a (105 * k + 31) = 436 * k + 129 ∧
    a (105 * k + 32) = 457 * k + 139 ∧
    a (105 * k + 33) = 436 * k + 137 ∧
    a (105 * k + 34) = 457 * k + 149 ∧
    a (105 * k + 35) = 436 * k + 145 ∧
    a (105 * k + 36) = 436 * k + 149 ∧
    a (105 * k + 37) = 457 * k + 161 ∧
    a (105 * k + 38) = 436 * k + 157 ∧
    a (105 * k + 39) = 457 * k + 170 ∧
    a (105 * k + 40) = 436 * k + 167 ∧
    a (105 * k + 41) = 436 * k + 170 ∧
    a (105 * k + 42) = 457 * k + 183 ∧
    a (105 * k + 43) = 436 * k + 178 ∧
    a (105 * k + 44) = 457 * k + 191 ∧
    a (105 * k + 45) = 436 * k + 187 ∧
    a (105 * k + 46) = 436 * k + 191 ∧
    a (105 * k + 47) = 457 * k + 205 ∧
    a (105 * k + 48) = 436 * k + 199 ∧
    a (105 * k + 49) = 457 * k + 214 ∧
    a (105 * k + 50) = 436 * k + 207 ∧
    a (105 * k + 51) = 436 * k + 211 ∧
    a (105 * k + 52) = 457 * k + 227 ∧
    a (105 * k + 53) = 436 * k + 219 ∧
    a (105 * k + 54) = 457 * k + 236 ∧
    a (105 * k + 55) = 436 * k + 229 ∧
    a (105 * k + 56) = 436 * k + 232 ∧
    a (105 * k + 57) = 457 * k + 248 ∧
    a (105 * k + 58) = 436 * k + 240 ∧
    a (105 * k + 59) = 457 * k + 257 ∧
    a (105 * k + 60) = 436 * k + 249 ∧
    a (105 * k + 61) = 436 * k + 254 ∧
    a (105 * k + 62) = 457 * k + 270 ∧
    a (105 * k + 63) = 436 * k + 261 ∧
    a (105 * k + 64) = 457 * k + 279 ∧
    a (105 * k + 65) = 436 * k + 269 ∧
    a (105 * k + 66) = 436 * k + 274 ∧
    a (105 * k + 67) = 457 * k + 292 ∧
    a (105 * k + 68) = 436 * k + 282 ∧
    a (105 * k + 69) = 457 * k + 301 ∧
    a (105 * k + 70) = 436 * k + 291 ∧
    a (105 * k + 71) = 436 * k + 294 ∧
    a (105 * k + 72) = 457 * k + 313 ∧
    a (105 * k + 73) = 436 * k + 303 ∧
    a (105 * k + 74) = 457 * k + 322 ∧
    a (105 * k + 75) = 436 * k + 312 ∧
    a (105 * k + 76) = 436 * k + 316 ∧
    a (105 * k + 77) = 457 * k + 335 ∧
    a (105 * k + 78) = 436 * k + 323 ∧
    a (105 * k + 79) = 457 * k + 344 ∧
    a (105 * k + 80) = 436 * k + 332 ∧
    a (105 * k + 81) = 436 * k + 336 ∧
    a (105 * k + 82) = 457 * k + 358 ∧
    a (105 * k + 83) = 436 * k + 344 ∧
    a (105 * k + 84) = 457 * k + 366 ∧
    a (105 * k + 85) = 436 * k + 353 ∧
    a (105 * k + 86) = 436 * k + 356 ∧
    a (105 * k + 87) = 457 * k + 379 ∧
    a (105 * k + 88) = 436 * k + 365 ∧
    a (105 * k + 89) = 457 * k + 388 ∧
    a (105 * k + 90) = 436 * k + 374 ∧
    a (105 * k + 91) = 436 * k + 378 ∧
    a (105 * k + 92) = 457 * k + 400 ∧
    a (105 * k + 93) = 436 * k + 385 ∧
    a (105 * k + 94) = 457 * k + 410 ∧
    a (105 * k + 95) = 436 * k + 394 ∧
    a (105 * k + 96) = 436 * k + 399 ∧
    a (105 * k + 97) = 457 * k + 423 ∧
    a (105 * k + 98) = 436 * k + 406 ∧
    a (105 * k + 99) = 457 * k + 431 ∧
    a (105 * k + 100) = 436 * k + 415 ∧
    a (105 * k + 101) = 436 * k + 419 ∧
    a (105 * k + 102) = 457 * k + 444 ∧
    a (105 * k + 103) = 436 * k + 428 ∧
    a (105 * k + 104) = 457 * k + 453 ∧
    a (105 * k + 105) = 436 * k + 436 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15⟩ := a_closed1 k
  obtain ⟨x16, x17, x18, x19, x20, x21, x22, x23⟩ := a_closed2 k
  obtain ⟨x24, x25, x26, x27, x28, x29, x30, x31⟩ := a_closed3 k
  obtain ⟨x32, x33, x34, x35, x36, x37, x38, x39⟩ := a_closed4 k
  obtain ⟨x40, x41, x42, x43, x44, x45, x46, x47⟩ := a_closed5 k
  obtain ⟨x48, x49, x50, x51, x52, x53, x54, x55⟩ := a_closed6 k
  obtain ⟨x56, x57, x58, x59, x60, x61, x62, x63⟩ := a_closed7 k
  obtain ⟨x64, x65, x66, x67, x68, x69, x70, x71⟩ := a_closed8 k
  obtain ⟨x72, x73, x74, x75, x76, x77, x78, x79⟩ := a_closed9 k
  obtain ⟨x80, x81, x82, x83, x84, x85, x86, x87⟩ := a_closed10 k
  obtain ⟨x88, x89, x90, x91, x92, x93, x94, x95⟩ := a_closed11 k
  obtain ⟨x96, x97, x98, x99, x100, x101, x102, x103⟩ := a_closed12 k
  have x104 := a_closed13 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63, x64, x65, x66, x67, x68, x69, x70, x71, x72, x73, x74, x75, x76, x77, x78, x79, x80, x81, x82, x83, x84, x85, x86, x87, x88, x89, x90, x91, x92, x93, x94, x95, x96, x97, x98, x99, x100, x101, x102, x103, x104⟩

def controlsK : PLift ((List.range 50).map b = [1, 4, 8, 12, 18, 21, 25, 31, 32, 39, 42, 45, 53, 54, 61, 62, 66, 74, 74, 84, 83, 87, 96, 94, 105, 104, 108, 118, 116, 126, 124, 129, 139, 137, 149, 145, 149, 161, 157, 170, 167, 170, 183, 178, 191, 187, 191, 205, 199, 214]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 12, 18, 21, 25, 31, 32, 39, 42, 45, 53, 54, 61, 62, 66, 74, 74, 84, 83, 87, 96, 94, 105, 104, 108, 118, 116, 126, 124, 129, 139, 137, 149, 145, 149, 161, 157, 170, 167, 170, 183, 178, 191, 187, 191, 205, 199, 214] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 105 → dv (t + 18) + 2 * dv (t + 17) + 3 * dv (t + 16) + 3 * dv (t + 15) + 3 * dv (t + 14) + dv (t + 13) + dv (t + 5) + 3 * dv (t + 4) + 3 * dv (t + 3) + 3 * dv (t + 2) + 2 * dv (t + 1) + dv (t + 0) = dv (t + 12) + 4 * dv (t + 11) + 5 * dv (t + 10) + 6 * dv (t + 9) + 5 * dv (t + 8) + 4 * dv (t + 7) + dv (t + 6)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 105 → dv (t + 18) + 2 * dv (t + 17) + 3 * dv (t + 16) + 3 * dv (t + 15) + 3 * dv (t + 14) + dv (t + 13) + dv (t + 5) + 3 * dv (t + 4) + 3 * dv (t + 3) + 3 * dv (t + 2) + 2 * dv (t + 1) + dv (t + 0) = dv (t + 12) + 4 * dv (t + 11) + 5 * dv (t + 10) + 6 * dv (t + 9) + 5 * dv (t + 8) + 4 * dv (t + 7) + dv (t + 6) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 18) : ℤ) = -2 * (dv (t + 17) : ℤ) - 3 * (dv (t + 16) : ℤ) - 3 * (dv (t + 15) : ℤ) - 3 * (dv (t + 14) : ℤ) - (dv (t + 13) : ℤ) + (dv (t + 12) : ℤ) + 4 * (dv (t + 11) : ℤ) + 5 * (dv (t + 10) : ℤ) + 6 * (dv (t + 9) : ℤ) + 5 * (dv (t + 8) : ℤ) + 4 * (dv (t + 7) : ℤ) + (dv (t + 6) : ℤ) - (dv (t + 5) : ℤ) - 3 * (dv (t + 4) : ℤ) - 3 * (dv (t + 3) : ℤ) - 3 * (dv (t + 2) : ℤ) - 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 105 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10, e 11, e 12, e 13, e 14, e 15, e 16, e 17, e 18]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 105) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 105 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 105 → b (q + 19) + 2 * b (q + 18) + 3 * b (q + 17) + 3 * b (q + 16) + 3 * b (q + 15) + b (q + 14) + b (q + 6) + 3 * b (q + 5) + 3 * b (q + 4) + 3 * b (q + 3) + 2 * b (q + 2) + b (q + 1) = b (q + 13) + 4 * b (q + 12) + 5 * b (q + 11) + 6 * b (q + 10) + 5 * b (q + 9) + 4 * b (q + 8) + b (q + 7)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 105 → b (q + 19) + 2 * b (q + 18) + 3 * b (q + 17) + 3 * b (q + 16) + 3 * b (q + 15) + b (q + 14) + b (q + 6) + 3 * b (q + 5) + 3 * b (q + 4) + 3 * b (q + 3) + 2 * b (q + 2) + b (q + 1) = b (q + 13) + 4 * b (q + 12) + 5 * b (q + 11) + 6 * b (q + 10) + 5 * b (q + 9) + 4 * b (q + 8) + b (q + 7) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 19) : ℤ) = -2 * b (q + 18) - 3 * b (q + 17) - 3 * b (q + 16) - 3 * b (q + 15) - b (q + 14) + b (q + 13) + 4 * b (q + 12) + 5 * b (q + 11) + 6 * b (q + 10) + 5 * b (q + 9) + 4 * b (q + 8) + b (q + 7) - b (q + 6) - 3 * b (q + 5) - 3 * b (q + 4) - 3 * b (q + 3) - 2 * b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 105 ∨ 105 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 105 := ⟨q - 105, by omega⟩
      have h0 : (b (v + 19) : ℤ) = -2 * b (v + 18) - 3 * b (v + 17) - 3 * b (v + 16) - 3 * b (v + 15) - b (v + 14) + b (v + 13) + 4 * b (v + 12) + 5 * b (v + 11) + 6 * b (v + 10) + 5 * b (v + 9) + 4 * b (v + 8) + b (v + 7) - b (v + 6) - 3 * b (v + 5) - 3 * b (v + 4) - 3 * b (v + 3) - 2 * b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 106) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 105 = v + 106 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s2 : (b (v + 107) : ℤ) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (le_trans (by decide : 1 ≤ 2) (Nat.le_add_left _ v))
        rw [show v + 2 + 105 = v + 107 from Nat.add_assoc _ _ _,
          show v + 2 - 1 = v + 1 from Nat.add_sub_assoc (by decide : 1 ≤ 2) v] at h
        exact_mod_cast h
      have s3 : (b (v + 108) : ℤ) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (le_trans (by decide : 1 ≤ 3) (Nat.le_add_left _ v))
        rw [show v + 3 + 105 = v + 108 from Nat.add_assoc _ _ _,
          show v + 3 - 1 = v + 2 from Nat.add_sub_assoc (by decide : 1 ≤ 3) v] at h
        exact_mod_cast h
      have s4 : (b (v + 109) : ℤ) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (le_trans (by decide : 1 ≤ 4) (Nat.le_add_left _ v))
        rw [show v + 4 + 105 = v + 109 from Nat.add_assoc _ _ _,
          show v + 4 - 1 = v + 3 from Nat.add_sub_assoc (by decide : 1 ≤ 4) v] at h
        exact_mod_cast h
      have s5 : (b (v + 110) : ℤ) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (le_trans (by decide : 1 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 105 = v + 110 from Nat.add_assoc _ _ _,
          show v + 5 - 1 = v + 4 from Nat.add_sub_assoc (by decide : 1 ≤ 5) v] at h
        exact_mod_cast h
      have s6 : (b (v + 111) : ℤ) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (le_trans (by decide : 1 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 105 = v + 111 from Nat.add_assoc _ _ _,
          show v + 6 - 1 = v + 5 from Nat.add_sub_assoc (by decide : 1 ≤ 6) v] at h
        exact_mod_cast h
      have s7 : (b (v + 112) : ℤ) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (le_trans (by decide : 1 ≤ 7) (Nat.le_add_left _ v))
        rw [show v + 7 + 105 = v + 112 from Nat.add_assoc _ _ _,
          show v + 7 - 1 = v + 6 from Nat.add_sub_assoc (by decide : 1 ≤ 7) v] at h
        exact_mod_cast h
      have s8 : (b (v + 113) : ℤ) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (le_trans (by decide : 1 ≤ 8) (Nat.le_add_left _ v))
        rw [show v + 8 + 105 = v + 113 from Nat.add_assoc _ _ _,
          show v + 8 - 1 = v + 7 from Nat.add_sub_assoc (by decide : 1 ≤ 8) v] at h
        exact_mod_cast h
      have s9 : (b (v + 114) : ℤ) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (le_trans (by decide : 1 ≤ 9) (Nat.le_add_left _ v))
        rw [show v + 9 + 105 = v + 114 from Nat.add_assoc _ _ _,
          show v + 9 - 1 = v + 8 from Nat.add_sub_assoc (by decide : 1 ≤ 9) v] at h
        exact_mod_cast h
      have s10 : (b (v + 115) : ℤ) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (le_trans (by decide : 1 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 105 = v + 115 from Nat.add_assoc _ _ _,
          show v + 10 - 1 = v + 9 from Nat.add_sub_assoc (by decide : 1 ≤ 10) v] at h
        exact_mod_cast h
      have s11 : (b (v + 116) : ℤ) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (le_trans (by decide : 1 ≤ 11) (Nat.le_add_left _ v))
        rw [show v + 11 + 105 = v + 116 from Nat.add_assoc _ _ _,
          show v + 11 - 1 = v + 10 from Nat.add_sub_assoc (by decide : 1 ≤ 11) v] at h
        exact_mod_cast h
      have s12 : (b (v + 117) : ℤ) = b (v + 12) + dv (v + 11) := by
        have h := b_step (v + 12) (le_trans (by decide : 1 ≤ 12) (Nat.le_add_left _ v))
        rw [show v + 12 + 105 = v + 117 from Nat.add_assoc _ _ _,
          show v + 12 - 1 = v + 11 from Nat.add_sub_assoc (by decide : 1 ≤ 12) v] at h
        exact_mod_cast h
      have s13 : (b (v + 118) : ℤ) = b (v + 13) + dv (v + 12) := by
        have h := b_step (v + 13) (le_trans (by decide : 1 ≤ 13) (Nat.le_add_left _ v))
        rw [show v + 13 + 105 = v + 118 from Nat.add_assoc _ _ _,
          show v + 13 - 1 = v + 12 from Nat.add_sub_assoc (by decide : 1 ≤ 13) v] at h
        exact_mod_cast h
      have s14 : (b (v + 119) : ℤ) = b (v + 14) + dv (v + 13) := by
        have h := b_step (v + 14) (le_trans (by decide : 1 ≤ 14) (Nat.le_add_left _ v))
        rw [show v + 14 + 105 = v + 119 from Nat.add_assoc _ _ _,
          show v + 14 - 1 = v + 13 from Nat.add_sub_assoc (by decide : 1 ≤ 14) v] at h
        exact_mod_cast h
      have s15 : (b (v + 120) : ℤ) = b (v + 15) + dv (v + 14) := by
        have h := b_step (v + 15) (le_trans (by decide : 1 ≤ 15) (Nat.le_add_left _ v))
        rw [show v + 15 + 105 = v + 120 from Nat.add_assoc _ _ _,
          show v + 15 - 1 = v + 14 from Nat.add_sub_assoc (by decide : 1 ≤ 15) v] at h
        exact_mod_cast h
      have s16 : (b (v + 121) : ℤ) = b (v + 16) + dv (v + 15) := by
        have h := b_step (v + 16) (le_trans (by decide : 1 ≤ 16) (Nat.le_add_left _ v))
        rw [show v + 16 + 105 = v + 121 from Nat.add_assoc _ _ _,
          show v + 16 - 1 = v + 15 from Nat.add_sub_assoc (by decide : 1 ≤ 16) v] at h
        exact_mod_cast h
      have s17 : (b (v + 122) : ℤ) = b (v + 17) + dv (v + 16) := by
        have h := b_step (v + 17) (le_trans (by decide : 1 ≤ 17) (Nat.le_add_left _ v))
        rw [show v + 17 + 105 = v + 122 from Nat.add_assoc _ _ _,
          show v + 17 - 1 = v + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) v] at h
        exact_mod_cast h
      have s18 : (b (v + 123) : ℤ) = b (v + 18) + dv (v + 17) := by
        have h := b_step (v + 18) (le_trans (by decide : 1 ≤ 18) (Nat.le_add_left _ v))
        rw [show v + 18 + 105 = v + 123 from Nat.add_assoc _ _ _,
          show v + 18 - 1 = v + 17 from Nat.add_sub_assoc (by decide : 1 ≤ 18) v] at h
        exact_mod_cast h
      have s19 : (b (v + 124) : ℤ) = b (v + 19) + dv (v + 18) := by
        have h := b_step (v + 19) (le_trans (by decide : 1 ≤ 19) (Nat.le_add_left _ v))
        rw [show v + 19 + 105 = v + 124 from Nat.add_assoc _ _ _,
          show v + 19 - 1 = v + 18 from Nat.add_sub_assoc (by decide : 1 ≤ 19) v] at h
        exact_mod_cast h
      show (b (v + 124) : ℤ) = -2 * b (v + 123) - 3 * b (v + 122) - 3 * b (v + 121) - 3 * b (v + 120) - b (v + 119) + b (v + 118) + 4 * b (v + 117) + 5 * b (v + 116) + 6 * b (v + 115) + 5 * b (v + 114) + 4 * b (v + 113) + b (v + 112) - b (v + 111) - 3 * b (v + 110) - 3 * b (v + 109) - 3 * b (v + 108) - 2 * b (v + 107) - b (v + 106)
      linear_combination s19 - (-2) * s18 - (-3) * s17 - (-3) * s16 - (-3) * s15 - (-1) * s14 - (1) * s13 - (4) * s12 - (5) * s11 - (6) * s10 - (5) * s9 - (4) * s8 - (1) * s7 - (-1) * s6 - (-3) * s5 - (-3) * s4 - (-3) * s3 - (-2) * s2 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 18 < n → (a n : ℤ) = -2 * a (n - 1) - 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) - a (n - 5) + a (n - 6) + 4 * a (n - 7) + 5 * a (n - 8) + 6 * a (n - 9) + 5 * a (n - 10) + 4 * a (n - 11) + a (n - 12) - a (n - 13) - 3 * a (n - 14) - 3 * a (n - 15) - 3 * a (n - 16) - 2 * a (n - 17) - a (n - 18) := by
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
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (b n) (Nat.mul 2 (bk n 1))) (Nat.mul 3 (bk n 2))) (Nat.mul 3 (bk n 3))) (Nat.mul 3 (bk n 4))) (bk n 5)) (bk n 13)) (Nat.mul 3 (bk n 14))) (Nat.mul 3 (bk n 15))) (Nat.mul 3 (bk n 16))) (Nat.mul 2 (bk n 17))) (bk n 18)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (bk n 6) (Nat.mul 4 (bk n 7))) (Nat.mul 5 (bk n 8))) (Nat.mul 6 (bk n 9))) (Nat.mul 5 (bk n 10))) (Nat.mul 4 (bk n 11))) (bk n 12)) (ind n 0)) (Nat.mul 6 (ind n 1))) (Nat.mul 19 (ind n 2))) (Nat.mul 43 (ind n 3))) (Nat.mul 81 (ind n 4))) (Nat.mul 130 (ind n 5))) (Nat.mul 184 (ind n 6))) (Nat.mul 234 (ind n 7))) (Nat.mul 269 (ind n 8))) (Nat.mul 282 (ind n 9))) (Nat.mul 270 (ind n 10))) (Nat.mul 235 (ind n 11))) (Nat.mul 185 (ind n 12))) (Nat.mul 131 (ind n 13))) (Nat.mul 82 (ind n 14))) (Nat.mul 44 (ind n 15))) (Nat.mul 19 (ind n 16))) (Nat.mul 6 (ind n 17))) (ind n 18)

def gfK : PLift ((allR 19 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 19, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 19) :
    1 * (b (n) : ℚ) + 2 * (if 1 ≤ n then (b (n - 1) : ℚ) else 0) + 3 * (if 2 ≤ n then (b (n - 2) : ℚ) else 0) + 3 * (if 3 ≤ n then (b (n - 3) : ℚ) else 0) + 3 * (if 4 ≤ n then (b (n - 4) : ℚ) else 0) + 1 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) - 1 * (if 6 ≤ n then (b (n - 6) : ℚ) else 0) - 4 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) - 5 * (if 8 ≤ n then (b (n - 8) : ℚ) else 0) - 6 * (if 9 ≤ n then (b (n - 9) : ℚ) else 0) - 5 * (if 10 ≤ n then (b (n - 10) : ℚ) else 0) - 4 * (if 11 ≤ n then (b (n - 11) : ℚ) else 0) - 1 * (if 12 ≤ n then (b (n - 12) : ℚ) else 0) + 1 * (if 13 ≤ n then (b (n - 13) : ℚ) else 0) + 3 * (if 14 ≤ n then (b (n - 14) : ℚ) else 0) + 3 * (if 15 ≤ n then (b (n - 15) : ℚ) else 0) + 3 * (if 16 ≤ n then (b (n - 16) : ℚ) else 0) + 2 * (if 17 ≤ n then (b (n - 17) : ℚ) else 0) + 1 * (if 18 ≤ n then (b (n - 18) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 6 + (if n = 2 then (1 : ℚ) else 0) * 19 + (if n = 3 then (1 : ℚ) else 0) * 43 + (if n = 4 then (1 : ℚ) else 0) * 81 + (if n = 5 then (1 : ℚ) else 0) * 130 + (if n = 6 then (1 : ℚ) else 0) * 184 + (if n = 7 then (1 : ℚ) else 0) * 234 + (if n = 8 then (1 : ℚ) else 0) * 269 + (if n = 9 then (1 : ℚ) else 0) * 282 + (if n = 10 then (1 : ℚ) else 0) * 270 + (if n = 11 then (1 : ℚ) else 0) * 235 + (if n = 12 then (1 : ℚ) else 0) * 185 + (if n = 13 then (1 : ℚ) else 0) * 131 + (if n = 14 then (1 : ℚ) else 0) * 82 + (if n = 15 then (1 : ℚ) else 0) * 44 + (if n = 16 then (1 : ℚ) else 0) * 19 + (if n = 17 then (1 : ℚ) else 0) * 6 + (if n = 18 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 19 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 19) : ℚ) + 2 * (if 1 ≤ q + 19 then (b (q + 19 - 1) : ℚ) else 0) + 3 * (if 2 ≤ q + 19 then (b (q + 19 - 2) : ℚ) else 0) + 3 * (if 3 ≤ q + 19 then (b (q + 19 - 3) : ℚ) else 0) + 3 * (if 4 ≤ q + 19 then (b (q + 19 - 4) : ℚ) else 0) + 1 * (if 5 ≤ q + 19 then (b (q + 19 - 5) : ℚ) else 0) - 1 * (if 6 ≤ q + 19 then (b (q + 19 - 6) : ℚ) else 0) - 4 * (if 7 ≤ q + 19 then (b (q + 19 - 7) : ℚ) else 0) - 5 * (if 8 ≤ q + 19 then (b (q + 19 - 8) : ℚ) else 0) - 6 * (if 9 ≤ q + 19 then (b (q + 19 - 9) : ℚ) else 0) - 5 * (if 10 ≤ q + 19 then (b (q + 19 - 10) : ℚ) else 0) - 4 * (if 11 ≤ q + 19 then (b (q + 19 - 11) : ℚ) else 0) - 1 * (if 12 ≤ q + 19 then (b (q + 19 - 12) : ℚ) else 0) + 1 * (if 13 ≤ q + 19 then (b (q + 19 - 13) : ℚ) else 0) + 3 * (if 14 ≤ q + 19 then (b (q + 19 - 14) : ℚ) else 0) + 3 * (if 15 ≤ q + 19 then (b (q + 19 - 15) : ℚ) else 0) + 3 * (if 16 ≤ q + 19 then (b (q + 19 - 16) : ℚ) else 0) + 2 * (if 17 ≤ q + 19 then (b (q + 19 - 17) : ℚ) else 0) + 1 * (if 18 ≤ q + 19 then (b (q + 19 - 18) : ℚ) else 0) =
      (if q + 19 = 0 then (1 : ℚ) else 0) * 1 + (if q + 19 = 1 then (1 : ℚ) else 0) * 6 + (if q + 19 = 2 then (1 : ℚ) else 0) * 19 + (if q + 19 = 3 then (1 : ℚ) else 0) * 43 + (if q + 19 = 4 then (1 : ℚ) else 0) * 81 + (if q + 19 = 5 then (1 : ℚ) else 0) * 130 + (if q + 19 = 6 then (1 : ℚ) else 0) * 184 + (if q + 19 = 7 then (1 : ℚ) else 0) * 234 + (if q + 19 = 8 then (1 : ℚ) else 0) * 269 + (if q + 19 = 9 then (1 : ℚ) else 0) * 282 + (if q + 19 = 10 then (1 : ℚ) else 0) * 270 + (if q + 19 = 11 then (1 : ℚ) else 0) * 235 + (if q + 19 = 12 then (1 : ℚ) else 0) * 185 + (if q + 19 = 13 then (1 : ℚ) else 0) * 131 + (if q + 19 = 14 then (1 : ℚ) else 0) * 82 + (if q + 19 = 15 then (1 : ℚ) else 0) * 44 + (if q + 19 = 16 then (1 : ℚ) else 0) * 19 + (if q + 19 = 17 then (1 : ℚ) else 0) * 6 + (if q + 19 = 18 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 19) : ℤ) = -2 * b (q + 18) - 3 * b (q + 17) - 3 * b (q + 16) - 3 * b (q + 15) - b (q + 14) + b (q + 13) + 4 * b (q + 12) + 5 * b (q + 11) + 6 * b (q + 10) + 5 * b (q + 9) + 4 * b (q + 8) + b (q + 7) - b (q + 6) - 3 * b (q + 5) - 3 * b (q + 4) - 3 * b (q + 3) - 2 * b (q + 2) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 19 - 1 = q + 18 from Nat.add_sub_assoc (by decide : 1 ≤ 19) q, show q + 19 - 2 = q + 17 from Nat.add_sub_assoc (by decide : 2 ≤ 19) q, show q + 19 - 3 = q + 16 from Nat.add_sub_assoc (by decide : 3 ≤ 19) q, show q + 19 - 4 = q + 15 from Nat.add_sub_assoc (by decide : 4 ≤ 19) q, show q + 19 - 5 = q + 14 from Nat.add_sub_assoc (by decide : 5 ≤ 19) q, show q + 19 - 6 = q + 13 from Nat.add_sub_assoc (by decide : 6 ≤ 19) q, show q + 19 - 7 = q + 12 from Nat.add_sub_assoc (by decide : 7 ≤ 19) q, show q + 19 - 8 = q + 11 from Nat.add_sub_assoc (by decide : 8 ≤ 19) q, show q + 19 - 9 = q + 10 from Nat.add_sub_assoc (by decide : 9 ≤ 19) q, show q + 19 - 10 = q + 9 from Nat.add_sub_assoc (by decide : 10 ≤ 19) q, show q + 19 - 11 = q + 8 from Nat.add_sub_assoc (by decide : 11 ≤ 19) q, show q + 19 - 12 = q + 7 from Nat.add_sub_assoc (by decide : 12 ≤ 19) q, show q + 19 - 13 = q + 6 from Nat.add_sub_assoc (by decide : 13 ≤ 19) q, show q + 19 - 14 = q + 5 from Nat.add_sub_assoc (by decide : 14 ≤ 19) q, show q + 19 - 15 = q + 4 from Nat.add_sub_assoc (by decide : 15 ≤ 19) q, show q + 19 - 16 = q + 3 from Nat.add_sub_assoc (by decide : 16 ≤ 19) q, show q + 19 - 17 = q + 2 from Nat.add_sub_assoc (by decide : 17 ≤ 19) q, show q + 19 - 18 = q + 1 from Nat.add_sub_assoc (by decide : 18 ≤ 19) q, show 1 ≤ q + 19 from le_trans (by decide : 1 ≤ 19) (Nat.le_add_left 19 q), show 2 ≤ q + 19 from le_trans (by decide : 2 ≤ 19) (Nat.le_add_left 19 q), show 3 ≤ q + 19 from le_trans (by decide : 3 ≤ 19) (Nat.le_add_left 19 q), show 4 ≤ q + 19 from le_trans (by decide : 4 ≤ 19) (Nat.le_add_left 19 q), show 5 ≤ q + 19 from le_trans (by decide : 5 ≤ 19) (Nat.le_add_left 19 q), show 6 ≤ q + 19 from le_trans (by decide : 6 ≤ 19) (Nat.le_add_left 19 q), show 7 ≤ q + 19 from le_trans (by decide : 7 ≤ 19) (Nat.le_add_left 19 q), show 8 ≤ q + 19 from le_trans (by decide : 8 ≤ 19) (Nat.le_add_left 19 q), show 9 ≤ q + 19 from le_trans (by decide : 9 ≤ 19) (Nat.le_add_left 19 q), show 10 ≤ q + 19 from le_trans (by decide : 10 ≤ 19) (Nat.le_add_left 19 q), show 11 ≤ q + 19 from le_trans (by decide : 11 ≤ 19) (Nat.le_add_left 19 q), show 12 ≤ q + 19 from le_trans (by decide : 12 ≤ 19) (Nat.le_add_left 19 q), show 13 ≤ q + 19 from le_trans (by decide : 13 ≤ 19) (Nat.le_add_left 19 q), show 14 ≤ q + 19 from le_trans (by decide : 14 ≤ 19) (Nat.le_add_left 19 q), show 15 ≤ q + 19 from le_trans (by decide : 15 ≤ 19) (Nat.le_add_left 19 q), show 16 ≤ q + 19 from le_trans (by decide : 16 ≤ 19) (Nat.le_add_left 19 q), show 17 ≤ q + 19 from le_trans (by decide : 17 ≤ 19) (Nat.le_add_left 19 q), show 18 ≤ q + 19 from le_trans (by decide : 18 ≤ 19) (Nat.le_add_left 19 q), show ¬ q + 19 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 14 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 14 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 15 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 15 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 16 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 16 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 17 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 17 < 19) (Nat.le_add_left 19 q)), show ¬ q + 19 = 18 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 18 < 19) (Nat.le_add_left 19 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2 * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) = C 1 * A + C 2 * (A * X ^ 1) + C 3 * (A * X ^ 2) + C 3 * (A * X ^ 3) + C 3 * (A * X ^ 4) + C 1 * (A * X ^ 5) - C 1 * (A * X ^ 6) - C 4 * (A * X ^ 7) - C 5 * (A * X ^ 8) - C 6 * (A * X ^ 9) - C 5 * (A * X ^ 10) - C 4 * (A * X ^ 11) - C 1 * (A * X ^ 12) + C 1 * (A * X ^ 13) + C 3 * (A * X ^ 14) + C 3 * (A * X ^ 15) + C 3 * (A * X ^ 16) + C 2 * (A * X ^ 17) + C 1 * (A * X ^ 18) := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : ((X + 1) * (X ^ 17 + 5 * X ^ 16 + 14 * X ^ 15 + 30 * X ^ 14 + 52 * X ^ 13 + 79 * X ^ 12 + 106 * X ^ 11 + 129 * X ^ 10 + 141 * X ^ 9 + 141 * X ^ 8 + 128 * X ^ 7 + 106 * X ^ 6 + 78 * X ^ 5 + 52 * X ^ 4 + 29 * X ^ 3 + 14 * X ^ 2 + 5 * X + 1) : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 6 + X ^ 2 * C 19 + X ^ 3 * C 43 + X ^ 4 * C 81 + X ^ 5 * C 130 + X ^ 6 * C 184 + X ^ 7 * C 234 + X ^ 8 * C 269 + X ^ 9 * C 282 + X ^ 10 * C 270 + X ^ 11 * C 235 + X ^ 12 * C 185 + X ^ 13 * C 131 + X ^ 14 * C 82 + X ^ 15 * C 44 + X ^ 16 * C 19 + X ^ 17 * C 6 + X ^ 18 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2 * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      (X + 1) * (X ^ 17 + 5 * X ^ 16 + 14 * X ^ 15 + 30 * X ^ 14 + 52 * X ^ 13 + 79 * X ^ 12 + 106 * X ^ 11 + 129 * X ^ 10 + 141 * X ^ 9 + 141 * X ^ 8 + 128 * X ^ 7 + 106 * X ^ 6 + 78 * X ^ 5 + 52 * X ^ 4 + 29 * X ^ 3 + 14 * X ^ 2 + 5 * X + 1) := by
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
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2 * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      (X + 1) * (X ^ 17 + 5 * X ^ 16 + 14 * X ^ 15 + 30 * X ^ 14 + 52 * X ^ 13 + 79 * X ^ 12 + 106 * X ^ 11 + 129 * X ^ 10 + 141 * X ^ 9 + 141 * X ^ 8 + 128 * X ^ 7 + 106 * X ^ 6 + 78 * X ^ 5 + 52 * X ^ 4 + 29 * X ^ 3 + 14 * X ^ 2 + 5 * X + 1) := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 18 < n → (a n : ℤ) = -2 * a (n - 1) - 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) - a (n - 5) + a (n - 6) + 4 * a (n - 7) + 5 * a (n - 8) + 6 * a (n - 9) + 5 * a (n - 10) + 4 * a (n - 11) + a (n - 12) - a (n - 13) - 3 * a (n - 14) - 3 * a (n - 15) - 3 * a (n - 16) - 2 * a (n - 17) - a (n - 18) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 12, 18, 21, 25, 31, 32, 39, 42, 45, 53, 54, 61, 62, 66, 74, 74, 84, 83, 87, 96, 94, 105, 104, 108, 118, 116, 126, 124, 129, 139, 137, 149, 145, 149, 161, 157, 170, 167, 170, 183, 178, 191, 187, 191, 205, 199, 214] := Count.controls

/-- The step a(n + 105) = a(n) + Count.dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 105) = a n + Count.dv (n - 1) := Count.a_step n hn

/-- The closed form per residue of n mod 105, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (105 * k + 1) = 436 * k + 4 ∧
    a (105 * k + 2) = 457 * k + 8 ∧
    a (105 * k + 3) = 436 * k + 12 ∧
    a (105 * k + 4) = 457 * k + 18 ∧
    a (105 * k + 5) = 436 * k + 21 ∧
    a (105 * k + 6) = 436 * k + 25 ∧
    a (105 * k + 7) = 457 * k + 31 ∧
    a (105 * k + 8) = 436 * k + 32 ∧
    a (105 * k + 9) = 457 * k + 39 ∧
    a (105 * k + 10) = 436 * k + 42 ∧
    a (105 * k + 11) = 436 * k + 45 ∧
    a (105 * k + 12) = 457 * k + 53 ∧
    a (105 * k + 13) = 436 * k + 54 ∧
    a (105 * k + 14) = 457 * k + 61 ∧
    a (105 * k + 15) = 436 * k + 62 ∧
    a (105 * k + 16) = 436 * k + 66 ∧
    a (105 * k + 17) = 457 * k + 74 ∧
    a (105 * k + 18) = 436 * k + 74 ∧
    a (105 * k + 19) = 457 * k + 84 ∧
    a (105 * k + 20) = 436 * k + 83 ∧
    a (105 * k + 21) = 436 * k + 87 ∧
    a (105 * k + 22) = 457 * k + 96 ∧
    a (105 * k + 23) = 436 * k + 94 ∧
    a (105 * k + 24) = 457 * k + 105 ∧
    a (105 * k + 25) = 436 * k + 104 ∧
    a (105 * k + 26) = 436 * k + 108 ∧
    a (105 * k + 27) = 457 * k + 118 ∧
    a (105 * k + 28) = 436 * k + 116 ∧
    a (105 * k + 29) = 457 * k + 126 ∧
    a (105 * k + 30) = 436 * k + 124 ∧
    a (105 * k + 31) = 436 * k + 129 ∧
    a (105 * k + 32) = 457 * k + 139 ∧
    a (105 * k + 33) = 436 * k + 137 ∧
    a (105 * k + 34) = 457 * k + 149 ∧
    a (105 * k + 35) = 436 * k + 145 ∧
    a (105 * k + 36) = 436 * k + 149 ∧
    a (105 * k + 37) = 457 * k + 161 ∧
    a (105 * k + 38) = 436 * k + 157 ∧
    a (105 * k + 39) = 457 * k + 170 ∧
    a (105 * k + 40) = 436 * k + 167 ∧
    a (105 * k + 41) = 436 * k + 170 ∧
    a (105 * k + 42) = 457 * k + 183 ∧
    a (105 * k + 43) = 436 * k + 178 ∧
    a (105 * k + 44) = 457 * k + 191 ∧
    a (105 * k + 45) = 436 * k + 187 ∧
    a (105 * k + 46) = 436 * k + 191 ∧
    a (105 * k + 47) = 457 * k + 205 ∧
    a (105 * k + 48) = 436 * k + 199 ∧
    a (105 * k + 49) = 457 * k + 214 ∧
    a (105 * k + 50) = 436 * k + 207 ∧
    a (105 * k + 51) = 436 * k + 211 ∧
    a (105 * k + 52) = 457 * k + 227 ∧
    a (105 * k + 53) = 436 * k + 219 ∧
    a (105 * k + 54) = 457 * k + 236 ∧
    a (105 * k + 55) = 436 * k + 229 ∧
    a (105 * k + 56) = 436 * k + 232 ∧
    a (105 * k + 57) = 457 * k + 248 ∧
    a (105 * k + 58) = 436 * k + 240 ∧
    a (105 * k + 59) = 457 * k + 257 ∧
    a (105 * k + 60) = 436 * k + 249 ∧
    a (105 * k + 61) = 436 * k + 254 ∧
    a (105 * k + 62) = 457 * k + 270 ∧
    a (105 * k + 63) = 436 * k + 261 ∧
    a (105 * k + 64) = 457 * k + 279 ∧
    a (105 * k + 65) = 436 * k + 269 ∧
    a (105 * k + 66) = 436 * k + 274 ∧
    a (105 * k + 67) = 457 * k + 292 ∧
    a (105 * k + 68) = 436 * k + 282 ∧
    a (105 * k + 69) = 457 * k + 301 ∧
    a (105 * k + 70) = 436 * k + 291 ∧
    a (105 * k + 71) = 436 * k + 294 ∧
    a (105 * k + 72) = 457 * k + 313 ∧
    a (105 * k + 73) = 436 * k + 303 ∧
    a (105 * k + 74) = 457 * k + 322 ∧
    a (105 * k + 75) = 436 * k + 312 ∧
    a (105 * k + 76) = 436 * k + 316 ∧
    a (105 * k + 77) = 457 * k + 335 ∧
    a (105 * k + 78) = 436 * k + 323 ∧
    a (105 * k + 79) = 457 * k + 344 ∧
    a (105 * k + 80) = 436 * k + 332 ∧
    a (105 * k + 81) = 436 * k + 336 ∧
    a (105 * k + 82) = 457 * k + 358 ∧
    a (105 * k + 83) = 436 * k + 344 ∧
    a (105 * k + 84) = 457 * k + 366 ∧
    a (105 * k + 85) = 436 * k + 353 ∧
    a (105 * k + 86) = 436 * k + 356 ∧
    a (105 * k + 87) = 457 * k + 379 ∧
    a (105 * k + 88) = 436 * k + 365 ∧
    a (105 * k + 89) = 457 * k + 388 ∧
    a (105 * k + 90) = 436 * k + 374 ∧
    a (105 * k + 91) = 436 * k + 378 ∧
    a (105 * k + 92) = 457 * k + 400 ∧
    a (105 * k + 93) = 436 * k + 385 ∧
    a (105 * k + 94) = 457 * k + 410 ∧
    a (105 * k + 95) = 436 * k + 394 ∧
    a (105 * k + 96) = 436 * k + 399 ∧
    a (105 * k + 97) = 457 * k + 423 ∧
    a (105 * k + 98) = 436 * k + 406 ∧
    a (105 * k + 99) = 457 * k + 431 ∧
    a (105 * k + 100) = 436 * k + 415 ∧
    a (105 * k + 101) = 436 * k + 419 ∧
    a (105 * k + 102) = 457 * k + 444 ∧
    a (105 * k + 103) = 436 * k + 428 ∧
    a (105 * k + 104) = 457 * k + 453 ∧
    a (105 * k + 105) = 436 * k + 436 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2 * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      (X + 1) * (X ^ 17 + 5 * X ^ 16 + 14 * X ^ 15 + 30 * X ^ 14 + 52 * X ^ 13 + 79 * X ^ 12 + 106 * X ^ 11 + 129 * X ^ 10 + 141 * X ^ 9 + 141 * X ^ 8 + 128 * X ^ 7 + 106 * X ^ 6 + 78 * X ^ 5 + 52 * X ^ 4 + 29 * X ^ 3 + 14 * X ^ 2 + 5 * X + 1) ∧
    ∀ n : ℕ, 18 < n → (a n : ℤ) = -2 * a (n - 1) - 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) - a (n - 5) + a (n - 6) + 4 * a (n - 7) + 5 * a (n - 8) + 6 * a (n - 9) + 5 * a (n - 10) + 4 * a (n - 11) + a (n - 12) - a (n - 13) - 3 * a (n - 14) - 3 * a (n - 15) - 3 * a (n - 16) - 2 * a (n - 17) - a (n - 18) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a311566

theorem OMA.solution : type_of% @OMA.S_oeis_a311566.main :=
  OMA.S_oeis_a311566.conjecture
