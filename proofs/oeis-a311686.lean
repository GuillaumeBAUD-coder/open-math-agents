import OMAStatements.S_oeis_a311686

namespace OMA.S_oeis_a311686






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 13

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 493161633525
  | 1 => 494269977300
  | 2 => 458871133875
  | 3 => 602957921775
  | 4 => 638356765200
  | 5 => 529736978100
  | 6 => 530845321875
  | 7 => 495446478450
  | 8 => 567489872400
  | 9 => 602888715825
  | 10 => 566313371250
  | 11 => 530914527825
  | 12 => 601780372050
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 497732371950 5 16 i.val

def Bc (i : Fin 8) : ℤ := tget 748152004875 5 16 i.val

def Cc (s : Fin 13) (i : Fin 8) : ℤ := tget (CcT s.val) 5 16 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 16. -/
def AcN (i : ℕ) : ℕ := tgetN 497732371950 5 i

def BcN (i : ℕ) : ℕ := tgetN 748152004875 5 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem Ac_eq (i : Fin 8) : Ac i = (AcN i.val : ℤ) - 16 := rfl

theorem Bc_eq (i : Fin 8) : Bc i = (BcN i.val : ℤ) - 16 := rfl

theorem Cc_eq (s : Fin 13) (i : Fin 8) : Cc s i = (CcN s.val i.val : ℤ) - 16 := rfl


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
theorem cls (P : Fin 13 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 13 × Fin 13 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 13 × Fin 13 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 13 × Fin 13 × ℤ × ℤ) (j : Fin 8) :
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
theorem farkas (x y : ℤ) (s : Fin 13) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
def fdN (i j f : ℕ) : ℕ := tgetN 28800508060654141103654814231236201457762219908131088440524054018883846907191264059272220281858501340074079646974898915623015858474304413856325653320991134452145962464518255899277172248504570861443384127675684577029952710470826942611279497985188501802374571440990397780824801080652011753420611153358037723661750562223921772899196043083192162297478190680660818093808847214771298010354398064714631397642324638259865556865539895012454903723975870664771962893164033754134114284555944721814405233454299119434317350390696056256527853514473137863555052534873005752320 5 ((i * 8 + j) * 6 + f)

def fd (i j : Fin 8) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 0 % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 1 % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 8 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 329100492984406687130405816123081566282143932431956013975928832 4 p

def dstv (p : ℕ) : ℕ := tgetN 299849564793179708213632114046426792138107176259808654054671137 4 p

def dxv (p : ℕ) : ℕ := tgetN 1635726585459968050883251818817 2 p

def dyv (p : ℕ) : ℕ := tgetN 6760803201217223474653395506437 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 434016410798450779536573267754801443853585268763577461890172300344032936051114121745206331669579139733777793577796723331961444929813295875039017758111815408707028297702442446991276142370049035999380047714584268808394350914783714893065060821772421674461584722936716270537934481204061145776295444920079243140481500389024584062314330129690484522838799780621835872082835747269218396638250700614812995821704435277259931713150746493670234138826375200328191234195775033002613704874947795496457730183424214903 4 (p * 8 + j)

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

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 16). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 8) + fdN i j 3 * AcN (fdN i j 1 % 8) + fdN i j 5 * AcN i + fdN i j 4 * 16 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 8) + fdN i j 3 * BcN (fdN i j 1 % 8) + fdN i j 5 * BcN i + fdN i j 4 * 16 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * BcN i + fdN i j 5 * BcN j)

/-- The constants of the far certificate of (i, j) at class s add up to a positive number. -/
def farCN (s i j : ℕ) : Bool :=
  Nat.blt ((fdN i j 2 + fdN i j 3 + fdN i j 4) * CcN s i + fdN i j 5 * (CcN s j + 1))
    (fdN i j 2 * CcN s (fdN i j 0 % 8) + fdN i j 3 * CcN s (fdN i j 1 % 8) + fdN i j 5 * CcN s i +
      fdN i j 4 * 23)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

def farOK : Bool := (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 13).all fun s => (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 16, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 52).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 8).all fun j =>
      dlvN p j + 1 * AcN j + 16 * dxv p + 1 * BcN j + 16 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 32 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 13) (i j : Fin 8) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (7 - Cc s i)

/-- Beyond F = 6, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 13) (i j : Fin 8) (hc : farCert s i j) (x y : ℤ)
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
  | 0 => 10401192663568270608655559001636779019304442313327286684226287025007274000680109513740819392891383325819775622793353649799082720693137109798210450456689426279470077722527204474033910917191603151660984659449365396523632532694587578893522120242009266858107443683032643926304455261725662722301626997615617398948728740112647088040396164182939895118863291140259310392522922736358167022494925316320344655996049501366207930232886680100635463892365718034806202044968079144338888776718921326517430618552065959683111684022492296738660849514666579037255349529949259120033961302232609387832341372455218058121794624270195024222649925050465249655255855672586490802866325782417500237786149266704512021265065998423922695635608924246629095454488195816104363735154140796632201253776490194471981464100403514867476095908446101563149958832007351273497975257755191666368397608432925526091932132003733173573243493824478755614130249793
  | 1 => 10401192665370368150884167740824300858554500035547379211354864364742054107507401331767566095660598158194351896977429120566141616043313865689199732151324670679109080070944649926892073829946365942314901788292789925335177659840602187141770697339119608934413427756117377750196235224701592537160628417826331001534619140146778588664010386948088083292284069439063012932805799782309880560822302498709474175523733451453207606357790035223050880201137678025519639467389425858453807592384706115547590404182204015111657695522882556482301521602783575302925413693128817960220033113043060260821163601504824790602194159522734220418169874512211700822669322286046018045786756843439539251594525456639699513311137473835356669462675410244341069550984469215526628080850033101466685144961167037968378127246567672526942907825124210611744632901614771175563837246273734632791380628479529533229115837804481265144511157942317703865232794432
  | 2 => 10401192666571766512369906900282648751387871850360774229440582591231907512059077751591793018415429318488271417965144556941323538448131276678197587778009576424428850397390834079976409236572435697989851699713535828686404706523277512964865830692034387842591114404155647112797231401720649749008135607939805402248802687518734953188154644948463733122546313084192300002183912095140826130241970036173083839814536433957217587782087521220229492900673732905062583684176166136568534814781564117703846357722729020990552017167612850412171701164090068479831412104192630670359448641313067094422881458512987594848273629538763610675392211717052833583810234455893353232770664783673254335078739014266061703057812137589696897016983760022937598823684514568087027717899148110289053282899446235411959680938591326495312493302729660616667443653603362908725779575145489454354206491314105399995452947951257664856916995157816474566716104769
  | 3 => 10401192670175961596827124378657692460943407062730694650009552978512581204348610208033564427824899156786731260560991243448657650329821648417054852063654880026453326628668833835790564986166351478279727570027105107267718439966737863928547778412837626490555831891300788942283484055553280990458559918410194580455836330583468359755480694943540471456443695042766924744469617648699422904492409122889004565089825652399996992644220739368948997338627891904195267363715181181019922231555849022804606072452481521011115198425494677393040671537533603034750907526798833230644290352498445196858155204099129251056194736472198486517759739809100177008118396960482252528433597410467792964218665832406249110032023889853942710149279564591196966533777908887049686099976850280143525248625577842017729706522743749693104902552887996469641156055784367087863788915822750969389183804009583547972226250815217628168531963705400963320664891457
  | 4 => 10401192672578758319798602697574388215554730924427749319869173723681174534817459850711931586229431027551429077676762568108528696253301683784353759648256882480174250909590825232615195354857026576089815787449401338305770123001918579462416535413082737785399115715931320710423786671708603467207271296593818357094173050087491932180468742655927902721848158235993637813770453124881781627000281717940740138149334328689783471863453469626617250571809591343472798189527727922826270990470418315940140349500677207836141835026748683011179890671941451520924632963676366460511624877075238887041339581872856201566413684524271379208406846926437018713019545858976583224297836356927555965646732229166271810245824592763819891948572521138253081646748743823544574348781349775070185403675286904457165674622148346403868584287638672641154202265607111399154122356319190128921999454000429965610974292304281772165294979195848543622222850368
  | 5 => 10401192673780156681284341857032736108388102739241144337954891950171027939369359082243926106087011593167288649487200457352644604616036890529177655789658412243445761794685505481286285536613771429910989766855907954649832096914040602435276791749495488734043523712041918271194571721748363797984541112823166939670978216871653922556882950698346230098676974704929172372982718693740153405757088019140473451955950615306700545309447634956092360819381612737765134545013276431698239976189942978526122632212893490634160429957431908263329024452760501814412678362730943361010657737458903464022041482736916049514895699171840989505284390660898565895477626292606772306195776164300640515832184039523049203653015765561216288224845021217134939645673986577541540786658393448688638764193957238055741312293889157904507465984901513280498644818349865140279793146140511913055737369641237347416697789380023685174824699185921116633547743297
  | 6 => 10401192677384351765741559335407779786888218183681329392212046629640588153024165530008175246608652940456147198142984866470116830708851005208865540715822348192913007050629438562309501750113911839343518773180395665020493430746688297901843690882863396851534987452897609789655911569198303034582907952316070545732038090706432566970846455954784535737865018829200571610339339955658761606503502612409941376162270150433319195265503216846143780720906078051085544110322337974729126319791341218706480336021841673786145437071304787898425643182421917970213966103303593707531850389201821597717295188027364363847352736920385919122222129597618990572243582268417138239840980792495058981763003798234103579474441697174302280374186037548751673068507544480455721585719239955274133043086640740322213283791513782451040159269674177556582440940342651130113013812605278077491486830097708317671534460081262733429656548308646285562449243456
  | 7 => 10401192678585750127227298494866127679721589998494724410297764856130441557575841949832402169363484100750066719044876354152481730551680723621513055494448535557849112783127138713560495676021381609025264244612815184851762513321073617450090374322852288178490217857320467979247620214711108805130204498394913036988599810120658793569158084856512633876722221903331842532496836516088458400384886380312242756224835908896406649297012835016568457329589181613521421306813611426002759179368747895679886150276836969705204459373575312352719360319190013753354075190555126890092047614295863471910033674013557504748533829560283373330165668040175918561547562178815520355071390261947031690944636741393302088618182017195299807251449862079581937187785309307030237455747971605191647183247515145205993526103900403996970234311146222149249994002446768909348147158764516586027638803997475160481816197726218025576522200128889102221482205249
  | 8 => 10401192682189945211684515973241171389277125210864644830866735243403339368168664103312284289671522013328697099690662640470702985440958965374009062766474087754425715192326996496370581637076070376913749844520116481540029373464231544246814391552905604173181521263281482728175145991101388753972088067805128762046326543216853155642967268261800559970293796333038605495762315707190406148680471164886248725307743210349539940354647039934324787184590058061606996983678586774443624447892283722796377661023372698805332593087379097434409047181995879231069107731752194353586780993731070529927017251428028565522646766335807229130995177319072751975408270947907482695403278121332422530524828628013540100365718808255159208114964711166212076557226832111975109443801536759062466761472337987916902623831664613748296414855169913109952879371158263119123263776113549707187841136195453580277886280480945519632415776282655204394698874945
  | 9 => 10401192684592741934655994292157867143888449072561699500726355988579708580334224048952540737177485809813224378842318314012503910918838823304019568212754559993978177889275613868032623275024572473118432772337398392892665556332348274699727625974764938256818504457733084502584732624541109015310813048636844045923492372716762704161191395554899965452310120359336389298615610169468475916390237588392679459469237865341964308159497159954765893906794803863616694003195492106331419978614361511932932491110575339539377075459745027634911139258548774096102667661210873060217804226953311571385804809497006801991863990796589326373191348077958731678311422175716596560322756759415557657458480971661063998289840104746139732995386217512725710039357389543666713261530620565376989437071168468175976328057295694624564076880456830403075602946619933000734450551590275511356454275101714420652821344293956877632435759479574809200821285696
  | 10 => 10401192685794140296141733451616215036721820887389216888682210603592170672549635360179568168686086861834723095435729291508219985476628838384455674941286108404217856025491235573831631610136397003926944116456578737451467219314261462512197233380059219515878456857344656491738142073994187901506418536646365114333662655550438777269344478689375375523960572769100831435815798306681199049514216565720931407183538848752945229261844966785991030369838741565742205503082216510759639418571909256467588922125076303402278599047130104207894129683222032680190100556294300169724614704981966245160173422827370764214870940729858845118766995236006509347976295971479495286257421675254955783642161382476512133992140484160889522710926422215229001467048094977812895163199775779228782310591215446206557622759942184495511555191402960101719425790198565565187415502264736390447834283382139785326296826411006722925916534295242182094306161984
  | 11 => 10401192688196937019113211770532910822388564517016006924853647056579653352033002647908557644480632695564581061618852449080550316922030162234083750845514347018253273098626156586289505299920211064917010648332890739738106272186136946367080675052116502530571004500719298258460681264402763660397310006005225694880873232708684392284346479191274587620958952934692036657401320937711033170563089241178395155468947836262052862247094935439685602662073972586711738132617646883011920178781674908422098296769297443009898743087774711596235663051296943408020270280824579443477170097488542765860906352392532229874156646016107218735190249695326012600234846399920482165198263184705820414322061494261220936156024435034798218424173100465797346115485232847929974428569446975724110377525303239257281306299370604729181866259013649619127690862314863484002420136690312109043495617515575447726330719051130061678618329263522540282178773057
  | 12 => 10401192691801132103570429248907954500888679961442069609240665347518829007644505379602349717608708535545252814241047764800105030882331620500144928703056047908882301025778014546753778159729524785974083616109158017907696286055914414893591795485348856490946196056345933398698446496997923830990581670152628400745518812030335580721624697244559568572085414780952576114762730170168267007710745071847681435982817636698826774342251473783857516779792333021996967430326906472722454624385674297340012402608994286304032258733655515868323797703228395460531122150008756594673716370222665603388667632580150559018465210123069959198595070513217014297490752046370109792498463980138680653593906744058782833656766457272034546740955030435679175439385681558609402360556324688658624517497548014600893615127388129850501990463977436916243523018592843086030516267396983917923316613103889289862209941294959683165992119037938652745175474241
  | _ => 0

def rd (s : Fin 13) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 13) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 13) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 13) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 13) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 13) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 13) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 13) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 52 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
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
theorem far_cert (s : Fin 13) (i j : Fin 8) (hij : nonadj i j) : farCert s i j := by
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

theorem edge_at (p : ℕ) (hp : p < 52) :
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

theorem edge_tab (p : ℕ) (hp : p < 52) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 13) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
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
theorem far_step (s : Fin 13) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
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
theorem farkas_ub (x y : ℤ) (s : Fin 13) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 13, 0 < 5 * (Cc s 1 - 6) + 8 * (Cc s 7 - 6) + 0 * (Cc s 0 - 6) + 21 * 4 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 13, 0 < 5 * (Cc s 3 - 6) + 5 * (Cc s 4 - 6) + 0 * (Cc s 0 - 6) + 20 * 4 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 13, 0 < 2 * (Cc s 2 - 6) + 1 * (Cc s 7 - 6) + 0 * (Cc s 0 - 6) + 11 * 2 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 13, 0 < 2 * (Cc s 5 - 6) + 1 * (Cc s 7 - 6) + 0 * (Cc s 0 - 6) + 21 * 2 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 13, 0 < 2 * (Cc s 3 - (-1)) + 2 * (Cc s 7 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 6 lies in the cells |x| ≤ 3, |y| ≤ 1 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 13) (hF : F (x, y, s) ≤ 6) :
    -3 ≤ x ∧ x ≤ 3 ∧ -1 ≤ y ∧ y ≤ 1 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 1 7 0 6 5 8 0 1 0 4 21 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 4 0 6 5 5 0 (-1) 0 4 20 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 7 0 6 2 1 0 0 1 2 11 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 7 0 6 2 1 0 0 (-1) 2 21 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 3 7 0 (-1) 2 2 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 3, b - 1) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 111211828672515961534639327741586225713499712276551905870307755298770007286588097842417505442946461414636478025173303177649145800269571523477711019781206138604918835729233289901515065741034219159132363649009426521111949629340301484589013413534845781063768891665644984095499815049130837996931421781396983814218675499280194524293787645231448868576458622394796358032544589771475614824357505285189002300386434315422703249512412669380691302184874896222255080223459481112018944 >>> (6 * ((a * 3 + b) * 13 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 3, b - 1) and class s, potential i plus
18 + 2 a + 8 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 8) : ℕ :=
  tgetN 1178733600 5 i.val * a + tgetN 464407068675 5 i.val * b + tgetN 21977715244524277469989639677658816199436037219743861171618369230035389824528892243290525809296461304477427133204921856424721019898687631356392069799085255004048709218500277874231180380450 6 (s * 8 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)

theorem fnt_tab : ∀ s : Fin 13, ∀ i : Fin 8, (tgetN 1178733600 5 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 464407068675 5 i.val : ℤ) = Bc i + 8 ∧
    (tgetN 21977715244524277469989639677658816199436037219743861171618369230035389824528892243290525809296461304477427133204921856424721019898687631356392069799085255004048709218500277874231180380450 6 (s.val * 8 + i.val) : ℤ) = Cc s i - Ac i * 3 - Bc i * 1 + 18 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 13) (i : Fin 8) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 3, (b : ℤ) - 1, s) i + (18 + 2 * a + 8 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 13) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 3, (b : ℤ) - 1, s) + (18 + 2 * a + 8 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 6, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 8) 1 = FN + 2 dx' + 8 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 7).all fun a => (List.range 3).all fun b => (List.range 13).all fun s =>
    Nat.blt (24 + 2 * a + 8 * b) (FN a b s) || (a == 3 && b == 1 && s == 8) ||
      (Nat.blt (hint a b s) 52 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 10 ==
          FN a b s + 2 * dxv (hint a b s) + 8 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 6) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 3).toNat (by omega) (y + 1).toNat (by omega) s.val s.isLt
  have ex : (((x + 3).toNat : ℕ) : ℤ) - 3 = x := by omega
  have ey : (((y + 1).toNat : ℕ) : ℤ) - 1 = y := by omega
  generalize (x + 3).toNat = a at h' ex
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
    have hs0 : s = 8 := Fin.ext (by rw [h3]; rfl)
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
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 1 = y + dy := by omega
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
from below, and for n ≥ 4 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 88 moves every quotient by an integer (`inner_shift`,
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
def AW (i : ℕ) : ℕ := tgetN 497732371950 5 i

def BW (i : ℕ) : ℕ := tgetN 748152004875 5 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem A_W (i : Fin 8) : Ac i = (AW i.val : ℤ) - 16 := rfl

theorem B_W (i : Fin 8) : Bc i = (BW i.val : ℤ) - 16 := rfl

theorem C_W (s : Fin 13) (i : Fin 8) : Cc s i = (CW s.val i.val : ℤ) - 16 := rfl

def gcV (k : ℕ) : ℕ := ctabN 255 1 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 8) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 379080 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 8) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 464407068675 5 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 8

def Bp (i : Fin 8) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 8749260 3 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 2

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
def par (s : Fin 13) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 13) (i j : Fin 8) (c u : ℤ) :
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

theorem par_inj (s : Fin 13) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
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
(pot_i ≤ pot_j) plus cf0 times (4 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 1019821285873698983479774322328363506643757245407083840162478204688535698545571387916012323840 5 k

def cf2V (k : ℕ) : ℕ := ctabN 208500280248621522779006241644866084001110132539317388506192783315001377707984110165932264448 5 k

def cf3V (k : ℕ) : ℕ := ctabN 336439480258273469795839107839096303927936173375442929705075848018115208231359200174156293120 5 k

def cf0V (k : ℕ) : ℕ := ctabN 11583286806757128054001794171264846447745246294589950454860684255969073801924608 5 k

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
def certC (s : Fin 13) (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (4 - Cc s i)

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := Nat.beq j i || Nat.beq j (nextF i) || Nat.beq j (prevF i)

/-- certG in natural numbers: Ac = AW - 16, Bc = BW - 16, the negative terms moved across. -/
def certGN (i j : ℕ) : Bool :=
  Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 8 i))) (AW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 8 i))) (AW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (AW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 8 i))) 16))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 8 i))) (cf2V (Nat.add j (Nat.mul 8 i)))) (cf0V (Nat.add j (Nat.mul 8 i)))) (AW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (AW j))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 8 i))) (BW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 8 i))) (BW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (BW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 8 i))) 16))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 8 i))) (cf2V (Nat.add j (Nat.mul 8 i)))) (cf0V (Nat.add j (Nat.mul 8 i)))) (BW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (BW j)))

/-- certC in natural numbers: Cc = CW - 16, the negative terms moved across. -/
def certCN (s i j : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 8 i))) (cf2V (Nat.add j (Nat.mul 8 i)))) (cf0V (Nat.add j (Nat.mul 8 i)))) (CW s i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (CW s j)))
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 8 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 8 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 8 i))) 20))

def certGK : PLift ((allR 8 fun i => allR 8 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 8 fun i => allR 8 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 13 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 13) : certS s = true := by
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
theorem certC_ok (s : Fin 13) (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
def lev (s : Fin 13) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 13) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 13) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 13) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 13) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 13) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 13) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 13) (i : Fin 8) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 13) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 4 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 13) (i : Fin 8) (n u : ℤ) (hn : 4 ≤ n)
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
def cbK : PLift ((allR 13 fun s => allR 8 fun i => Nat.ble (CW s i) 23 && Nat.ble 16 (Nat.add (CW s i) 7)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 13) (j : Fin 8) : -7 ≤ Cc s j ∧ Cc s j ≤ 7 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 7)) (1 * n + 7) ×ˢ
    (Finset.Icc (-(1 * n + 7)) (1 * n + 7) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (1 * Ac 3 + 1 * Ac 4 = 4 ∧ 1 * Bc 3 + 1 * Bc 4 = 0 ∧
    1 * Ac 0 + 1 * Ac 7 = (-4) ∧ 1 * Bc 0 + 1 * Bc 7 = 0 ∧
    1 * Ac 5 + 1 * Ac 6 = 0 ∧ 1 * Bc 5 + 1 * Bc 6 = 16 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-16)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 1 * Ac 3 + 1 * Ac 4 = 4 ∧ 1 * Bc 3 + 1 * Bc 4 = 0 ∧
    1 * Ac 0 + 1 * Ac 7 = (-4) ∧ 1 * Bc 0 + 1 * Bc 7 = 0 ∧
    1 * Ac 5 + 1 * Ac 6 = 0 ∧ 1 * Bc 5 + 1 * Bc 6 = 16 ∧
    1 * Ac 1 + 1 * Ac 2 = 0 ∧ 1 * Bc 1 + 1 * Bc 2 = (-16) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 13) :
    4 * x ≤ 2 * F (x, y, s) + 14 ∧
    4 * (-x) ≤ 2 * F (x, y, s) + 14 ∧
    16 * y ≤ 2 * F (x, y, s) + 14 ∧
    16 * (-y) ≤ 2 * F (x, y, s) + 14 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 3 + 1 * pot (x, y, s) 4 =
      4 * x + 1 * Cc s 3 + 1 * Cc s 4 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 3
  have r0 := le_F (x, y, s) 4
  have k0 := Cbound s 3
  have l0 := Cbound s 4
  have e1 : 1 * pot (x, y, s) 0 + 1 * pot (x, y, s) 7 =
      4 * (-x) + 1 * Cc s 0 + 1 * Cc s 7 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 7
  have k1 := Cbound s 0
  have l1 := Cbound s 7
  have e2 : 1 * pot (x, y, s) 5 + 1 * pot (x, y, s) 6 =
      16 * y + 1 * Cc s 5 + 1 * Cc s 6 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 5
  have r2 := le_F (x, y, s) 6
  have k2 := Cbound s 5
  have l2 := Cbound s 6
  have e3 : 1 * pot (x, y, s) 1 + 1 * pot (x, y, s) 2 =
      16 * (-y) + 1 * Cc s 1 + 1 * Cc s 2 := by
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
noncomputable def PF (s : Fin 13) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 13) (i : Fin 8) (n : ℤ) (hn : 4 ≤ n) :
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
def inner (s : Fin 13) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 13) (i : Fin 8) (n : ℤ) (hn : 4 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 13 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 13 × Fin 8, inner p.1 p.2 n

/-! Shifting n by 88 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 49929671459351640 7 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 8) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 225422433112148 7 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 40

def mh (i : Fin 8) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 47430286099093888 7 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 40

def mk (i : Fin 8) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 8, (88 : ℤ) = gc i * Lq i ∧ 88 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 88 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 8, (88 : ℤ) = gc i * Lq i ∧ 88 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 88 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 13) (i : Fin 8) (n : ℤ) :
    inner s i (n + 88) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 88 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 88 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 88) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 88) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 88) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
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
  ∑ q : Fin 13 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 88) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 88 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 88 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 4 + r with r < 88: the level is QQ - 3 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 34210314 4 k

def uhMV (k : ℕ) : ℕ := ctabN 10521096 3 k

def ukPV (k : ℕ) : ℕ := ctabN 2686492704 4 k

def ukMV (k : ℕ) : ℕ := ctabN 282693 3 k

def dhV (k : ℕ) : ℕ := ctabN 395527438708 5 k

def dkV (k : ℕ) : ℕ := ctabN 699554999819 5 k

def mhkV (k : ℕ) : ℕ := ctabN 9291996 3 k

def uh (i : Fin 8) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 8) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 8) : ℤ := dhV i.val

def dk (i : Fin 8) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 0 1 (Nat.add i (Nat.mul 8 s))

def QQ (s i : ℕ) : ℕ := ctabN 68485214120425431156605486121242235758148776957399706513644147501765958684455597477624473851882164884892283291904474918703618 4 (Nat.add i (Nat.mul 8 s))

def AH (s i : ℕ) : ℕ := ctabN 77997768808585036757448277371457029324277272153495109380582976264428612991877569014930730210024404146420113119758919780479812838828626481514878305748423892518205831296610126693119347868676076501103391096129725820748305 7 (Nat.add i (Nat.mul 8 s))

def AK (s i : ℕ) : ℕ := ctabN 30562227008061447907014718845823446779357867053491391189953603482261514048776578809203613572963356833617259956316145662428969553024866154722050757612070232189361807490500486004665207243523 6 (Nat.add i (Nat.mul 8 s))

def WH (s i : ℕ) : ℕ := ctabN 45688758499193115549607954702775061150488691777988830656846471259319910885618289235045442916237486433450479747507059444185606973801629039229448876551174116001030629117262417164488738869761 6 (Nat.add i (Nat.mul 8 s))

def WK (s i : ℕ) : ℕ := ctabN 153146180228419817569269620960699128049651351940610825953138711417670157351376211068496080949650480438831848944747253210208226346247680342859285548210464840579818346330872786473250226280 6 (Nat.add i (Nat.mul 8 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 13 fun s => allR 8 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq (Nat.add 20 (Nat.mul (gcV i) 3)) (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (Nat.mul (uhPV i) 3)) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (Nat.mul (uhMV i) 3)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (Nat.mul (ukPV i) 3)) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (Nat.mul (ukMV i) 3)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 13) (i : Fin 8) :
    PP s.val i.val < gcV i.val ∧
    (4 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 3) + PP s.val i.val ∧
    (AH s.val i.val : ℤ) = uh i * ((QQ s.val i.val : ℤ) - 3) +
      (Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0)) + dh i * WH s.val i.val -
      (uhMV i.val : ℤ) * LqV i.val ∧
    (AK s.val i.val : ℤ) = uk i * ((QQ s.val i.val : ℤ) - 3) +
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

theorem div_nat (s : Fin 13) (i : Fin 8) (r : ℕ) :
    ((4 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (4 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 3) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 13) (i : Fin 8) (r : ℕ) (hr : r < 88) :
    inner s i ((4 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (88 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 88 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((4 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 3) + tauN s.val i.val r := by
      rw [lev, show (4 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 3) + tauN s.val i.val r) by
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

def dtabV (k : ℕ) : ℕ := ctabN 18553978516146854786609176643702130000616836085211217055897121479651644711393239925038231723315540620645995042319056533774947436109493096328065845179858902097439436758065537084764558586655304435247548204145232411336040180754964468489967980 9 k

def tblV (k : ℕ) : ℕ := ctabN 18553579514057834156790845310900966339624811119894989485280273896246124290454781778998722489816591480951153111561404370216978891040533741852767737221798410592874450730099870538775257639505729793488830411439618149227952185736620131541585924 9 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 88. -/
def dv (t : ℕ) : ℕ := dtabV (t % 88)

/-- The sequence in closed form: b(n + 88) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 88) + tblV ((n - 1) % 88)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 88) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 88 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 88 - 1 = n - 1 + 88 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 88)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 88) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 88 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 88 - 1 = n - 1 + 88 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 88)]
  ring

/-- b on the residue class of 1 + j mod 88. -/
theorem b_res (k j : ℕ) (hj : j < 88) : b (88 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (88 * k + (1 + j) < 1) by omega),
    show 88 * k + (1 + j) - 1 = j + 88 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 88), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 4 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 88 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 13 fun s => allR 8 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 13 fun s => sumR 8 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 4 r)) &&
    Nat.beq (sumR 13 fun s => sumR 8 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 1 (dv (Nat.add 3 r)))

/-! The window n = 4, ..., 91, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 14 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 14 14 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 28 14 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK3 : PLift (allI 42 14 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK4 : PLift (allI 56 14 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK5 : PLift (allI 70 14 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK6 : PLift (allI 84 4 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 88) :
    (∀ s, s < 13 → ∀ i, i < 8 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 13 fun s => sumR 8 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (4 + r) ∧
    (sumR 13 fun s => sumR 8 fun i => cond (divN s i r) (mhkV i) 0) = 1 * dv (3 + r) := by
  have h : periodR r = true := by
    rcases (show r < 14 ∨ (14 ≤ r ∧ r < 28) ∨ (28 ≤ r ∧ r < 42) ∨ (42 ≤ r ∧ r < 56) ∨ (56 ≤ r ∧ r < 70) ∨ (70 ≤ r ∧ r < 84) ∨ 84 ≤ r by omega) with h | h | h | h | h | h | h
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

theorem innerZ_eq (s i r : ℕ) (hs : s < 13) (hi : i < 8) (hr : r < 88) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 13 fun s => sumR 8 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 13 × Fin 8, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 8 fun i => f s i : ℕ) : ℤ)) 13]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 8]

theorem S_window (r : ℕ) (hr : r < 88) : S ((4 : ℤ) + r) = b (4 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 88) : Gs ((4 : ℤ) + r) = ((1 * dv (3 + r) : ℕ) : ℤ) := by
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
theorem inner_nonneg (s : Fin 13) (i : Fin 8) (n : ℤ) (hn : 4 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 4 + t := ⟨(n - 4).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 88
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 88) (by omega) (by omega)
      have e : (4 : ℤ) + t = (4 + (t - 88 : ℕ)) + 88 := by
        push_cast [Nat.cast_sub (by omega : 88 ≤ t)]; ring
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

/-- The growth of b over 88 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 4 ≤ n) : (1 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 4) % 88 < 88 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((4 : ℤ) + (((n - 4) % 88 : ℕ) : ℤ)) + 88 * (((n - 4) / 88 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (3 + (n - 4) % 88) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 4 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 92
    · obtain ⟨r, rfl⟩ : ∃ r, n = 4 + r := ⟨n - 4, by omega⟩
      push_cast
      exact S_window r (by omega)
    · have h1 := ih (n - 88) (by omega) (by omega)
      have h2 := S_shift ((n - 88 : ℕ) : ℤ)
      have h3 := b_shift (n - 88) (by omega)
      have h4 := grow (n - 88) (by omega)
      rw [show n - 88 + 88 = n by omega] at h3
      rw [show ((n - 88 : ℕ) : ℤ) + 88 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 3 lie in the box -5 ≤ x ≤ 5, -1 ≤ y ≤ 1 (`small_box`). In natural-number
coordinates a = x + 5, b = y + 1 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 13) (h : F (x, y, s) ≤ 3) :
    -5 ≤ x ∧ x ≤ 5 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 5, (b : ℤ) - 1, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 96) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 5) (BW i)) 16) (Nat.add (Nat.mul 16 a) (Nat.mul 16 b))

theorem pot_box (a b : ℕ) (s : Fin 13) (i : Fin 8) :
    pot ((a : ℤ) - 5, (b : ℤ) - 1, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 8 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 13) : F ((a : ℤ) - 5, (b : ℤ) - 1, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 5, (b : ℤ) - 1, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 5, (b : ℤ) - 1, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 8 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 8 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 5, (b : ℤ) - 1, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 5, (b : ℤ) - 1, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 5, (b : ℤ) - 1, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 11 fun a => sumR 3 fun b => sumR 13 fun s => cond (Nat.beq (FN a b s) f) 1 0

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
def ib (q : ℕ × ℕ × Fin 13) : V := ((q.1 : ℤ) - 5, (q.2.1 : ℤ) - 1, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 3) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 11 ×ˢ (Finset.range 3 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 13 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 5).toNat, (y + 1).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 5).toNat (y + 1).toNat s
        rw [show (((x + 5).toNat : ℕ) : ℤ) - 5 = x by omega,
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 13]
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
n + 88, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
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

def dconst_baseK : PLift (∀ r : ℕ, r < 88 → dtabV r = 364) :=
  ⟨by decide +kernel⟩

theorem dconst_base : ∀ r : ℕ, r < 88 → dtabV r = 364 := dconst_baseK.down

theorem dv_const : ∀ t : ℕ, dv t = 364 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 88) = a(n) + 364 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 88) = a n + 364 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 364 ∧ tblV 0 = 4 ∧ dv 1 = 364 ∧ tblV 1 = 8 ∧ dv 2 = 364 ∧ tblV 2 = 13 ∧ dv 3 = 364 ∧ tblV 3 = 16 ∧ dv 4 = 364 ∧ tblV 4 = 20 ∧ dv 5 = 364 ∧ tblV 5 = 25 ∧ dv 6 = 364 ∧ tblV 6 = 29 ∧ dv 7 = 364 ∧ tblV 7 = 33) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 364 ∧ tblV 8 = 38 ∧ dv 9 = 364 ∧ tblV 9 = 42 ∧ dv 10 = 364 ∧ tblV 10 = 46 ∧ dv 11 = 364 ∧ tblV 11 = 49 ∧ dv 12 = 364 ∧ tblV 12 = 53 ∧ dv 13 = 364 ∧ tblV 13 = 58 ∧ dv 14 = 364 ∧ tblV 14 = 61 ∧ dv 15 = 364 ∧ tblV 15 = 66) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 364 ∧ tblV 16 = 71 ∧ dv 17 = 364 ∧ tblV 17 = 75 ∧ dv 18 = 364 ∧ tblV 18 = 79 ∧ dv 19 = 364 ∧ tblV 19 = 83 ∧ dv 20 = 364 ∧ tblV 20 = 87 ∧ dv 21 = 364 ∧ tblV 21 = 91 ∧ dv 22 = 364 ∧ tblV 22 = 94 ∧ dv 23 = 364 ∧ tblV 23 = 99) :=
  ⟨by decide +kernel⟩

def closedK3 : PLift (dv 24 = 364 ∧ tblV 24 = 104 ∧ dv 25 = 364 ∧ tblV 25 = 107 ∧ dv 26 = 364 ∧ tblV 26 = 112 ∧ dv 27 = 364 ∧ tblV 27 = 116 ∧ dv 28 = 364 ∧ tblV 28 = 120 ∧ dv 29 = 364 ∧ tblV 29 = 124 ∧ dv 30 = 364 ∧ tblV 30 = 128 ∧ dv 31 = 364 ∧ tblV 31 = 133) :=
  ⟨by decide +kernel⟩

def closedK4 : PLift (dv 32 = 364 ∧ tblV 32 = 137 ∧ dv 33 = 364 ∧ tblV 33 = 140 ∧ dv 34 = 364 ∧ tblV 34 = 145 ∧ dv 35 = 364 ∧ tblV 35 = 149 ∧ dv 36 = 364 ∧ tblV 36 = 152 ∧ dv 37 = 364 ∧ tblV 37 = 157 ∧ dv 38 = 364 ∧ tblV 38 = 161 ∧ dv 39 = 364 ∧ tblV 39 = 166) :=
  ⟨by decide +kernel⟩

def closedK5 : PLift (dv 40 = 364 ∧ tblV 40 = 170 ∧ dv 41 = 364 ∧ tblV 41 = 174 ∧ dv 42 = 364 ∧ tblV 42 = 179 ∧ dv 43 = 364 ∧ tblV 43 = 182 ∧ dv 44 = 364 ∧ tblV 44 = 185 ∧ dv 45 = 364 ∧ tblV 45 = 190 ∧ dv 46 = 364 ∧ tblV 46 = 194 ∧ dv 47 = 364 ∧ tblV 47 = 198) :=
  ⟨by decide +kernel⟩

def closedK6 : PLift (dv 48 = 364 ∧ tblV 48 = 203 ∧ dv 49 = 364 ∧ tblV 49 = 207 ∧ dv 50 = 364 ∧ tblV 50 = 212 ∧ dv 51 = 364 ∧ tblV 51 = 215 ∧ dv 52 = 364 ∧ tblV 52 = 219 ∧ dv 53 = 364 ∧ tblV 53 = 224 ∧ dv 54 = 364 ∧ tblV 54 = 227 ∧ dv 55 = 364 ∧ tblV 55 = 231) :=
  ⟨by decide +kernel⟩

def closedK7 : PLift (dv 56 = 364 ∧ tblV 56 = 236 ∧ dv 57 = 364 ∧ tblV 57 = 240 ∧ dv 58 = 364 ∧ tblV 58 = 244 ∧ dv 59 = 364 ∧ tblV 59 = 248 ∧ dv 60 = 364 ∧ tblV 60 = 252 ∧ dv 61 = 364 ∧ tblV 61 = 257 ∧ dv 62 = 364 ∧ tblV 62 = 260 ∧ dv 63 = 364 ∧ tblV 63 = 265) :=
  ⟨by decide +kernel⟩

def closedK8 : PLift (dv 64 = 364 ∧ tblV 64 = 270 ∧ dv 65 = 364 ∧ tblV 65 = 273 ∧ dv 66 = 364 ∧ tblV 66 = 277 ∧ dv 67 = 364 ∧ tblV 67 = 281 ∧ dv 68 = 364 ∧ tblV 68 = 285 ∧ dv 69 = 364 ∧ tblV 69 = 289 ∧ dv 70 = 364 ∧ tblV 70 = 293 ∧ dv 71 = 364 ∧ tblV 71 = 298) :=
  ⟨by decide +kernel⟩

def closedK9 : PLift (dv 72 = 364 ∧ tblV 72 = 303 ∧ dv 73 = 364 ∧ tblV 73 = 306 ∧ dv 74 = 364 ∧ tblV 74 = 311 ∧ dv 75 = 364 ∧ tblV 75 = 315 ∧ dv 76 = 364 ∧ tblV 76 = 318 ∧ dv 77 = 364 ∧ tblV 77 = 322 ∧ dv 78 = 364 ∧ tblV 78 = 326 ∧ dv 79 = 364 ∧ tblV 79 = 331) :=
  ⟨by decide +kernel⟩

def closedK10 : PLift (dv 80 = 364 ∧ tblV 80 = 335 ∧ dv 81 = 364 ∧ tblV 81 = 339 ∧ dv 82 = 364 ∧ tblV 82 = 344 ∧ dv 83 = 364 ∧ tblV 83 = 348 ∧ dv 84 = 364 ∧ tblV 84 = 351 ∧ dv 85 = 364 ∧ tblV 85 = 356 ∧ dv 86 = 364 ∧ tblV 86 = 360 ∧ dv 87 = 364 ∧ tblV 87 = 364) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (88 * k + 1) = 364 * k + 4 ∧
    a (88 * k + 2) = 364 * k + 8 ∧
    a (88 * k + 3) = 364 * k + 13 ∧
    a (88 * k + 4) = 364 * k + 16 ∧
    a (88 * k + 5) = 364 * k + 20 ∧
    a (88 * k + 6) = 364 * k + 25 ∧
    a (88 * k + 7) = 364 * k + 29 ∧
    a (88 * k + 8) = 364 * k + 33 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 1 = 88 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 88 * k + 2 = 88 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 88 * k + 3 = 88 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 88 * k + 4 = 88 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 88 * k + 5 = 88 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 88 * k + 6 = 88 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 88 * k + 7 = 88 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 88 * k + 8 = 88 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (88 * k + 9) = 364 * k + 38 ∧
    a (88 * k + 10) = 364 * k + 42 ∧
    a (88 * k + 11) = 364 * k + 46 ∧
    a (88 * k + 12) = 364 * k + 49 ∧
    a (88 * k + 13) = 364 * k + 53 ∧
    a (88 * k + 14) = 364 * k + 58 ∧
    a (88 * k + 15) = 364 * k + 61 ∧
    a (88 * k + 16) = 364 * k + 66 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 9 = 88 * k + (1 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 88 * k + 10 = 88 * k + (1 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 88 * k + 11 = 88 * k + (1 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 88 * k + 12 = 88 * k + (1 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 88 * k + 13 = 88 * k + (1 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 88 * k + 14 = 88 * k + (1 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 88 * k + 15 = 88 * k + (1 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 88 * k + 16 = 88 * k + (1 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (88 * k + 17) = 364 * k + 71 ∧
    a (88 * k + 18) = 364 * k + 75 ∧
    a (88 * k + 19) = 364 * k + 79 ∧
    a (88 * k + 20) = 364 * k + 83 ∧
    a (88 * k + 21) = 364 * k + 87 ∧
    a (88 * k + 22) = 364 * k + 91 ∧
    a (88 * k + 23) = 364 * k + 94 ∧
    a (88 * k + 24) = 364 * k + 99 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 17 = 88 * k + (1 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 88 * k + 18 = 88 * k + (1 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 88 * k + 19 = 88 * k + (1 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 88 * k + 20 = 88 * k + (1 + 19) from rfl, b_res k 19 (by decide), c38, c39]
  · rw [show 88 * k + 21 = 88 * k + (1 + 20) from rfl, b_res k 20 (by decide), c40, c41]
  · rw [show 88 * k + 22 = 88 * k + (1 + 21) from rfl, b_res k 21 (by decide), c42, c43]
  · rw [show 88 * k + 23 = 88 * k + (1 + 22) from rfl, b_res k 22 (by decide), c44, c45]
  · rw [show 88 * k + 24 = 88 * k + (1 + 23) from rfl, b_res k 23 (by decide), c46, c47]

theorem a_closed3 (k : ℕ) :
    a (88 * k + 25) = 364 * k + 104 ∧
    a (88 * k + 26) = 364 * k + 107 ∧
    a (88 * k + 27) = 364 * k + 112 ∧
    a (88 * k + 28) = 364 * k + 116 ∧
    a (88 * k + 29) = 364 * k + 120 ∧
    a (88 * k + 30) = 364 * k + 124 ∧
    a (88 * k + 31) = 364 * k + 128 ∧
    a (88 * k + 32) = 364 * k + 133 := by
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := closedK3.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 25 = 88 * k + (1 + 24) from rfl, b_res k 24 (by decide), c48, c49]
  · rw [show 88 * k + 26 = 88 * k + (1 + 25) from rfl, b_res k 25 (by decide), c50, c51]
  · rw [show 88 * k + 27 = 88 * k + (1 + 26) from rfl, b_res k 26 (by decide), c52, c53]
  · rw [show 88 * k + 28 = 88 * k + (1 + 27) from rfl, b_res k 27 (by decide), c54, c55]
  · rw [show 88 * k + 29 = 88 * k + (1 + 28) from rfl, b_res k 28 (by decide), c56, c57]
  · rw [show 88 * k + 30 = 88 * k + (1 + 29) from rfl, b_res k 29 (by decide), c58, c59]
  · rw [show 88 * k + 31 = 88 * k + (1 + 30) from rfl, b_res k 30 (by decide), c60, c61]
  · rw [show 88 * k + 32 = 88 * k + (1 + 31) from rfl, b_res k 31 (by decide), c62, c63]

theorem a_closed4 (k : ℕ) :
    a (88 * k + 33) = 364 * k + 137 ∧
    a (88 * k + 34) = 364 * k + 140 ∧
    a (88 * k + 35) = 364 * k + 145 ∧
    a (88 * k + 36) = 364 * k + 149 ∧
    a (88 * k + 37) = 364 * k + 152 ∧
    a (88 * k + 38) = 364 * k + 157 ∧
    a (88 * k + 39) = 364 * k + 161 ∧
    a (88 * k + 40) = 364 * k + 166 := by
  obtain ⟨c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79⟩ := closedK4.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 33 = 88 * k + (1 + 32) from rfl, b_res k 32 (by decide), c64, c65]
  · rw [show 88 * k + 34 = 88 * k + (1 + 33) from rfl, b_res k 33 (by decide), c66, c67]
  · rw [show 88 * k + 35 = 88 * k + (1 + 34) from rfl, b_res k 34 (by decide), c68, c69]
  · rw [show 88 * k + 36 = 88 * k + (1 + 35) from rfl, b_res k 35 (by decide), c70, c71]
  · rw [show 88 * k + 37 = 88 * k + (1 + 36) from rfl, b_res k 36 (by decide), c72, c73]
  · rw [show 88 * k + 38 = 88 * k + (1 + 37) from rfl, b_res k 37 (by decide), c74, c75]
  · rw [show 88 * k + 39 = 88 * k + (1 + 38) from rfl, b_res k 38 (by decide), c76, c77]
  · rw [show 88 * k + 40 = 88 * k + (1 + 39) from rfl, b_res k 39 (by decide), c78, c79]

theorem a_closed5 (k : ℕ) :
    a (88 * k + 41) = 364 * k + 170 ∧
    a (88 * k + 42) = 364 * k + 174 ∧
    a (88 * k + 43) = 364 * k + 179 ∧
    a (88 * k + 44) = 364 * k + 182 ∧
    a (88 * k + 45) = 364 * k + 185 ∧
    a (88 * k + 46) = 364 * k + 190 ∧
    a (88 * k + 47) = 364 * k + 194 ∧
    a (88 * k + 48) = 364 * k + 198 := by
  obtain ⟨c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95⟩ := closedK5.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 41 = 88 * k + (1 + 40) from rfl, b_res k 40 (by decide), c80, c81]
  · rw [show 88 * k + 42 = 88 * k + (1 + 41) from rfl, b_res k 41 (by decide), c82, c83]
  · rw [show 88 * k + 43 = 88 * k + (1 + 42) from rfl, b_res k 42 (by decide), c84, c85]
  · rw [show 88 * k + 44 = 88 * k + (1 + 43) from rfl, b_res k 43 (by decide), c86, c87]
  · rw [show 88 * k + 45 = 88 * k + (1 + 44) from rfl, b_res k 44 (by decide), c88, c89]
  · rw [show 88 * k + 46 = 88 * k + (1 + 45) from rfl, b_res k 45 (by decide), c90, c91]
  · rw [show 88 * k + 47 = 88 * k + (1 + 46) from rfl, b_res k 46 (by decide), c92, c93]
  · rw [show 88 * k + 48 = 88 * k + (1 + 47) from rfl, b_res k 47 (by decide), c94, c95]

theorem a_closed6 (k : ℕ) :
    a (88 * k + 49) = 364 * k + 203 ∧
    a (88 * k + 50) = 364 * k + 207 ∧
    a (88 * k + 51) = 364 * k + 212 ∧
    a (88 * k + 52) = 364 * k + 215 ∧
    a (88 * k + 53) = 364 * k + 219 ∧
    a (88 * k + 54) = 364 * k + 224 ∧
    a (88 * k + 55) = 364 * k + 227 ∧
    a (88 * k + 56) = 364 * k + 231 := by
  obtain ⟨c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111⟩ := closedK6.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 49 = 88 * k + (1 + 48) from rfl, b_res k 48 (by decide), c96, c97]
  · rw [show 88 * k + 50 = 88 * k + (1 + 49) from rfl, b_res k 49 (by decide), c98, c99]
  · rw [show 88 * k + 51 = 88 * k + (1 + 50) from rfl, b_res k 50 (by decide), c100, c101]
  · rw [show 88 * k + 52 = 88 * k + (1 + 51) from rfl, b_res k 51 (by decide), c102, c103]
  · rw [show 88 * k + 53 = 88 * k + (1 + 52) from rfl, b_res k 52 (by decide), c104, c105]
  · rw [show 88 * k + 54 = 88 * k + (1 + 53) from rfl, b_res k 53 (by decide), c106, c107]
  · rw [show 88 * k + 55 = 88 * k + (1 + 54) from rfl, b_res k 54 (by decide), c108, c109]
  · rw [show 88 * k + 56 = 88 * k + (1 + 55) from rfl, b_res k 55 (by decide), c110, c111]

theorem a_closed7 (k : ℕ) :
    a (88 * k + 57) = 364 * k + 236 ∧
    a (88 * k + 58) = 364 * k + 240 ∧
    a (88 * k + 59) = 364 * k + 244 ∧
    a (88 * k + 60) = 364 * k + 248 ∧
    a (88 * k + 61) = 364 * k + 252 ∧
    a (88 * k + 62) = 364 * k + 257 ∧
    a (88 * k + 63) = 364 * k + 260 ∧
    a (88 * k + 64) = 364 * k + 265 := by
  obtain ⟨c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127⟩ := closedK7.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 57 = 88 * k + (1 + 56) from rfl, b_res k 56 (by decide), c112, c113]
  · rw [show 88 * k + 58 = 88 * k + (1 + 57) from rfl, b_res k 57 (by decide), c114, c115]
  · rw [show 88 * k + 59 = 88 * k + (1 + 58) from rfl, b_res k 58 (by decide), c116, c117]
  · rw [show 88 * k + 60 = 88 * k + (1 + 59) from rfl, b_res k 59 (by decide), c118, c119]
  · rw [show 88 * k + 61 = 88 * k + (1 + 60) from rfl, b_res k 60 (by decide), c120, c121]
  · rw [show 88 * k + 62 = 88 * k + (1 + 61) from rfl, b_res k 61 (by decide), c122, c123]
  · rw [show 88 * k + 63 = 88 * k + (1 + 62) from rfl, b_res k 62 (by decide), c124, c125]
  · rw [show 88 * k + 64 = 88 * k + (1 + 63) from rfl, b_res k 63 (by decide), c126, c127]

theorem a_closed8 (k : ℕ) :
    a (88 * k + 65) = 364 * k + 270 ∧
    a (88 * k + 66) = 364 * k + 273 ∧
    a (88 * k + 67) = 364 * k + 277 ∧
    a (88 * k + 68) = 364 * k + 281 ∧
    a (88 * k + 69) = 364 * k + 285 ∧
    a (88 * k + 70) = 364 * k + 289 ∧
    a (88 * k + 71) = 364 * k + 293 ∧
    a (88 * k + 72) = 364 * k + 298 := by
  obtain ⟨c128, c129, c130, c131, c132, c133, c134, c135, c136, c137, c138, c139, c140, c141, c142, c143⟩ := closedK8.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 65 = 88 * k + (1 + 64) from rfl, b_res k 64 (by decide), c128, c129]
  · rw [show 88 * k + 66 = 88 * k + (1 + 65) from rfl, b_res k 65 (by decide), c130, c131]
  · rw [show 88 * k + 67 = 88 * k + (1 + 66) from rfl, b_res k 66 (by decide), c132, c133]
  · rw [show 88 * k + 68 = 88 * k + (1 + 67) from rfl, b_res k 67 (by decide), c134, c135]
  · rw [show 88 * k + 69 = 88 * k + (1 + 68) from rfl, b_res k 68 (by decide), c136, c137]
  · rw [show 88 * k + 70 = 88 * k + (1 + 69) from rfl, b_res k 69 (by decide), c138, c139]
  · rw [show 88 * k + 71 = 88 * k + (1 + 70) from rfl, b_res k 70 (by decide), c140, c141]
  · rw [show 88 * k + 72 = 88 * k + (1 + 71) from rfl, b_res k 71 (by decide), c142, c143]

theorem a_closed9 (k : ℕ) :
    a (88 * k + 73) = 364 * k + 303 ∧
    a (88 * k + 74) = 364 * k + 306 ∧
    a (88 * k + 75) = 364 * k + 311 ∧
    a (88 * k + 76) = 364 * k + 315 ∧
    a (88 * k + 77) = 364 * k + 318 ∧
    a (88 * k + 78) = 364 * k + 322 ∧
    a (88 * k + 79) = 364 * k + 326 ∧
    a (88 * k + 80) = 364 * k + 331 := by
  obtain ⟨c144, c145, c146, c147, c148, c149, c150, c151, c152, c153, c154, c155, c156, c157, c158, c159⟩ := closedK9.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 73 = 88 * k + (1 + 72) from rfl, b_res k 72 (by decide), c144, c145]
  · rw [show 88 * k + 74 = 88 * k + (1 + 73) from rfl, b_res k 73 (by decide), c146, c147]
  · rw [show 88 * k + 75 = 88 * k + (1 + 74) from rfl, b_res k 74 (by decide), c148, c149]
  · rw [show 88 * k + 76 = 88 * k + (1 + 75) from rfl, b_res k 75 (by decide), c150, c151]
  · rw [show 88 * k + 77 = 88 * k + (1 + 76) from rfl, b_res k 76 (by decide), c152, c153]
  · rw [show 88 * k + 78 = 88 * k + (1 + 77) from rfl, b_res k 77 (by decide), c154, c155]
  · rw [show 88 * k + 79 = 88 * k + (1 + 78) from rfl, b_res k 78 (by decide), c156, c157]
  · rw [show 88 * k + 80 = 88 * k + (1 + 79) from rfl, b_res k 79 (by decide), c158, c159]

theorem a_closed10 (k : ℕ) :
    a (88 * k + 81) = 364 * k + 335 ∧
    a (88 * k + 82) = 364 * k + 339 ∧
    a (88 * k + 83) = 364 * k + 344 ∧
    a (88 * k + 84) = 364 * k + 348 ∧
    a (88 * k + 85) = 364 * k + 351 ∧
    a (88 * k + 86) = 364 * k + 356 ∧
    a (88 * k + 87) = 364 * k + 360 ∧
    a (88 * k + 88) = 364 * k + 364 := by
  obtain ⟨c160, c161, c162, c163, c164, c165, c166, c167, c168, c169, c170, c171, c172, c173, c174, c175⟩ := closedK10.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 88 * k + 81 = 88 * k + (1 + 80) from rfl, b_res k 80 (by decide), c160, c161]
  · rw [show 88 * k + 82 = 88 * k + (1 + 81) from rfl, b_res k 81 (by decide), c162, c163]
  · rw [show 88 * k + 83 = 88 * k + (1 + 82) from rfl, b_res k 82 (by decide), c164, c165]
  · rw [show 88 * k + 84 = 88 * k + (1 + 83) from rfl, b_res k 83 (by decide), c166, c167]
  · rw [show 88 * k + 85 = 88 * k + (1 + 84) from rfl, b_res k 84 (by decide), c168, c169]
  · rw [show 88 * k + 86 = 88 * k + (1 + 85) from rfl, b_res k 85 (by decide), c170, c171]
  · rw [show 88 * k + 87 = 88 * k + (1 + 86) from rfl, b_res k 86 (by decide), c172, c173]
  · rw [show 88 * k + 88 = 88 * k + (1 + 87) from rfl, b_res k 87 (by decide), c174, c175]

/-- The closed form per residue of n mod 88, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (88 * k + 1) = 364 * k + 4 ∧
    a (88 * k + 2) = 364 * k + 8 ∧
    a (88 * k + 3) = 364 * k + 13 ∧
    a (88 * k + 4) = 364 * k + 16 ∧
    a (88 * k + 5) = 364 * k + 20 ∧
    a (88 * k + 6) = 364 * k + 25 ∧
    a (88 * k + 7) = 364 * k + 29 ∧
    a (88 * k + 8) = 364 * k + 33 ∧
    a (88 * k + 9) = 364 * k + 38 ∧
    a (88 * k + 10) = 364 * k + 42 ∧
    a (88 * k + 11) = 364 * k + 46 ∧
    a (88 * k + 12) = 364 * k + 49 ∧
    a (88 * k + 13) = 364 * k + 53 ∧
    a (88 * k + 14) = 364 * k + 58 ∧
    a (88 * k + 15) = 364 * k + 61 ∧
    a (88 * k + 16) = 364 * k + 66 ∧
    a (88 * k + 17) = 364 * k + 71 ∧
    a (88 * k + 18) = 364 * k + 75 ∧
    a (88 * k + 19) = 364 * k + 79 ∧
    a (88 * k + 20) = 364 * k + 83 ∧
    a (88 * k + 21) = 364 * k + 87 ∧
    a (88 * k + 22) = 364 * k + 91 ∧
    a (88 * k + 23) = 364 * k + 94 ∧
    a (88 * k + 24) = 364 * k + 99 ∧
    a (88 * k + 25) = 364 * k + 104 ∧
    a (88 * k + 26) = 364 * k + 107 ∧
    a (88 * k + 27) = 364 * k + 112 ∧
    a (88 * k + 28) = 364 * k + 116 ∧
    a (88 * k + 29) = 364 * k + 120 ∧
    a (88 * k + 30) = 364 * k + 124 ∧
    a (88 * k + 31) = 364 * k + 128 ∧
    a (88 * k + 32) = 364 * k + 133 ∧
    a (88 * k + 33) = 364 * k + 137 ∧
    a (88 * k + 34) = 364 * k + 140 ∧
    a (88 * k + 35) = 364 * k + 145 ∧
    a (88 * k + 36) = 364 * k + 149 ∧
    a (88 * k + 37) = 364 * k + 152 ∧
    a (88 * k + 38) = 364 * k + 157 ∧
    a (88 * k + 39) = 364 * k + 161 ∧
    a (88 * k + 40) = 364 * k + 166 ∧
    a (88 * k + 41) = 364 * k + 170 ∧
    a (88 * k + 42) = 364 * k + 174 ∧
    a (88 * k + 43) = 364 * k + 179 ∧
    a (88 * k + 44) = 364 * k + 182 ∧
    a (88 * k + 45) = 364 * k + 185 ∧
    a (88 * k + 46) = 364 * k + 190 ∧
    a (88 * k + 47) = 364 * k + 194 ∧
    a (88 * k + 48) = 364 * k + 198 ∧
    a (88 * k + 49) = 364 * k + 203 ∧
    a (88 * k + 50) = 364 * k + 207 ∧
    a (88 * k + 51) = 364 * k + 212 ∧
    a (88 * k + 52) = 364 * k + 215 ∧
    a (88 * k + 53) = 364 * k + 219 ∧
    a (88 * k + 54) = 364 * k + 224 ∧
    a (88 * k + 55) = 364 * k + 227 ∧
    a (88 * k + 56) = 364 * k + 231 ∧
    a (88 * k + 57) = 364 * k + 236 ∧
    a (88 * k + 58) = 364 * k + 240 ∧
    a (88 * k + 59) = 364 * k + 244 ∧
    a (88 * k + 60) = 364 * k + 248 ∧
    a (88 * k + 61) = 364 * k + 252 ∧
    a (88 * k + 62) = 364 * k + 257 ∧
    a (88 * k + 63) = 364 * k + 260 ∧
    a (88 * k + 64) = 364 * k + 265 ∧
    a (88 * k + 65) = 364 * k + 270 ∧
    a (88 * k + 66) = 364 * k + 273 ∧
    a (88 * k + 67) = 364 * k + 277 ∧
    a (88 * k + 68) = 364 * k + 281 ∧
    a (88 * k + 69) = 364 * k + 285 ∧
    a (88 * k + 70) = 364 * k + 289 ∧
    a (88 * k + 71) = 364 * k + 293 ∧
    a (88 * k + 72) = 364 * k + 298 ∧
    a (88 * k + 73) = 364 * k + 303 ∧
    a (88 * k + 74) = 364 * k + 306 ∧
    a (88 * k + 75) = 364 * k + 311 ∧
    a (88 * k + 76) = 364 * k + 315 ∧
    a (88 * k + 77) = 364 * k + 318 ∧
    a (88 * k + 78) = 364 * k + 322 ∧
    a (88 * k + 79) = 364 * k + 326 ∧
    a (88 * k + 80) = 364 * k + 331 ∧
    a (88 * k + 81) = 364 * k + 335 ∧
    a (88 * k + 82) = 364 * k + 339 ∧
    a (88 * k + 83) = 364 * k + 344 ∧
    a (88 * k + 84) = 364 * k + 348 ∧
    a (88 * k + 85) = 364 * k + 351 ∧
    a (88 * k + 86) = 364 * k + 356 ∧
    a (88 * k + 87) = 364 * k + 360 ∧
    a (88 * k + 88) = 364 * k + 364 := by
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
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63, x64, x65, x66, x67, x68, x69, x70, x71, x72, x73, x74, x75, x76, x77, x78, x79, x80, x81, x82, x83, x84, x85, x86, x87⟩

def controlsK : PLift ((List.range 50).map b = [1, 4, 8, 13, 16, 20, 25, 29, 33, 38, 42, 46, 49, 53, 58, 61, 66, 71, 75, 79, 83, 87, 91, 94, 99, 104, 107, 112, 116, 120, 124, 128, 133, 137, 140, 145, 149, 152, 157, 161, 166, 170, 174, 179, 182, 185, 190, 194, 198, 203]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 13, 16, 20, 25, 29, 33, 38, 42, 46, 49, 53, 58, 61, 66, 71, 75, 79, 83, 87, 91, 94, 99, 104, 107, 112, 116, 120, 124, 128, 133, 137, 140, 145, 149, 152, 157, 161, 166, 170, 174, 179, 182, 185, 190, 194, 198, 203] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 88 → dv (t + 16) + dv (t + 12) + dv (t + 4) + dv (t + 0) = dv (t + 15) + dv (t + 11) + dv (t + 5) + dv (t + 1)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 88 → dv (t + 16) + dv (t + 12) + dv (t + 4) + dv (t + 0) = dv (t + 15) + dv (t + 11) + dv (t + 5) + dv (t + 1) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 16) : ℤ) = (dv (t + 15) : ℤ) - (dv (t + 12) : ℤ) + (dv (t + 11) : ℤ) + (dv (t + 5) : ℤ) - (dv (t + 4) : ℤ) + (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 88 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 4, e 5, e 11, e 12, e 15, e 16]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 88) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 88 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 88 → b (q + 17) + b (q + 13) + b (q + 5) + b (q + 1) = b (q + 16) + b (q + 12) + b (q + 6) + b (q + 2)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 88 → b (q + 17) + b (q + 13) + b (q + 5) + b (q + 1) = b (q + 16) + b (q + 12) + b (q + 6) + b (q + 2) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 17) : ℤ) = b (q + 16) - b (q + 13) + b (q + 12) + b (q + 6) - b (q + 5) + b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 88 ∨ 88 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 88 := ⟨q - 88, by omega⟩
      have h0 : (b (v + 17) : ℤ) = b (v + 16) - b (v + 13) + b (v + 12) + b (v + 6) - b (v + 5) + b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 89) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 88 = v + 89 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s2 : (b (v + 90) : ℤ) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (le_trans (by decide : 1 ≤ 2) (Nat.le_add_left _ v))
        rw [show v + 2 + 88 = v + 90 from Nat.add_assoc _ _ _,
          show v + 2 - 1 = v + 1 from Nat.add_sub_assoc (by decide : 1 ≤ 2) v] at h
        exact_mod_cast h
      have s5 : (b (v + 93) : ℤ) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (le_trans (by decide : 1 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 88 = v + 93 from Nat.add_assoc _ _ _,
          show v + 5 - 1 = v + 4 from Nat.add_sub_assoc (by decide : 1 ≤ 5) v] at h
        exact_mod_cast h
      have s6 : (b (v + 94) : ℤ) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (le_trans (by decide : 1 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 88 = v + 94 from Nat.add_assoc _ _ _,
          show v + 6 - 1 = v + 5 from Nat.add_sub_assoc (by decide : 1 ≤ 6) v] at h
        exact_mod_cast h
      have s12 : (b (v + 100) : ℤ) = b (v + 12) + dv (v + 11) := by
        have h := b_step (v + 12) (le_trans (by decide : 1 ≤ 12) (Nat.le_add_left _ v))
        rw [show v + 12 + 88 = v + 100 from Nat.add_assoc _ _ _,
          show v + 12 - 1 = v + 11 from Nat.add_sub_assoc (by decide : 1 ≤ 12) v] at h
        exact_mod_cast h
      have s13 : (b (v + 101) : ℤ) = b (v + 13) + dv (v + 12) := by
        have h := b_step (v + 13) (le_trans (by decide : 1 ≤ 13) (Nat.le_add_left _ v))
        rw [show v + 13 + 88 = v + 101 from Nat.add_assoc _ _ _,
          show v + 13 - 1 = v + 12 from Nat.add_sub_assoc (by decide : 1 ≤ 13) v] at h
        exact_mod_cast h
      have s16 : (b (v + 104) : ℤ) = b (v + 16) + dv (v + 15) := by
        have h := b_step (v + 16) (le_trans (by decide : 1 ≤ 16) (Nat.le_add_left _ v))
        rw [show v + 16 + 88 = v + 104 from Nat.add_assoc _ _ _,
          show v + 16 - 1 = v + 15 from Nat.add_sub_assoc (by decide : 1 ≤ 16) v] at h
        exact_mod_cast h
      have s17 : (b (v + 105) : ℤ) = b (v + 17) + dv (v + 16) := by
        have h := b_step (v + 17) (le_trans (by decide : 1 ≤ 17) (Nat.le_add_left _ v))
        rw [show v + 17 + 88 = v + 105 from Nat.add_assoc _ _ _,
          show v + 17 - 1 = v + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) v] at h
        exact_mod_cast h
      show (b (v + 105) : ℤ) = b (v + 104) - b (v + 101) + b (v + 100) + b (v + 94) - b (v + 93) + b (v + 90) - b (v + 89)
      linear_combination s17 - (1) * s16 - (-1) * s13 - (1) * s12 - (1) * s6 - (-1) * s5 - (1) * s2 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 16 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + a (n - 5) + a (n - 11) - a (n - 12) + a (n - 15) - a (n - 16) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 17 := ⟨n - 17, by omega⟩
  rw [show q + 17 - 1 = q + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) q, show q + 17 - 4 = q + 13 from Nat.add_sub_assoc (by decide : 4 ≤ 17) q, show q + 17 - 5 = q + 12 from Nat.add_sub_assoc (by decide : 5 ≤ 17) q, show q + 17 - 11 = q + 6 from Nat.add_sub_assoc (by decide : 11 ≤ 17) q, show q + 17 - 12 = q + 5 from Nat.add_sub_assoc (by decide : 12 ≤ 17) q, show q + 17 - 15 = q + 2 from Nat.add_sub_assoc (by decide : 15 ≤ 17) q, show q + 17 - 16 = q + 1 from Nat.add_sub_assoc (by decide : 16 ≤ 17) q]
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
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (b n) (bk n 4)) (bk n 12)) (bk n 16)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (bk n 1) (bk n 5)) (bk n 11)) (bk n 15)) (ind n 0)) (Nat.mul 3 (ind n 1))) (Nat.mul 4 (ind n 2))) (Nat.mul 5 (ind n 3))) (Nat.mul 4 (ind n 4))) (Nat.mul 7 (ind n 5))) (Nat.mul 9 (ind n 6))) (Nat.mul 9 (ind n 7))) (Nat.mul 7 (ind n 8))) (Nat.mul 9 (ind n 9))) (Nat.mul 9 (ind n 10))) (Nat.mul 7 (ind n 11))) (Nat.mul 4 (ind n 12))) (Nat.mul 5 (ind n 13))) (Nat.mul 4 (ind n 14))) (Nat.mul 3 (ind n 15))) (ind n 16)

def gfK : PLift ((allR 17 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 17, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 17) :
    1 * (b (n) : ℚ) - 1 * (if 1 ≤ n then (b (n - 1) : ℚ) else 0) + 1 * (if 4 ≤ n then (b (n - 4) : ℚ) else 0) - 1 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) - 1 * (if 11 ≤ n then (b (n - 11) : ℚ) else 0) + 1 * (if 12 ≤ n then (b (n - 12) : ℚ) else 0) - 1 * (if 15 ≤ n then (b (n - 15) : ℚ) else 0) + 1 * (if 16 ≤ n then (b (n - 16) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 3 + (if n = 2 then (1 : ℚ) else 0) * 4 + (if n = 3 then (1 : ℚ) else 0) * 5 + (if n = 4 then (1 : ℚ) else 0) * 4 + (if n = 5 then (1 : ℚ) else 0) * 7 + (if n = 6 then (1 : ℚ) else 0) * 9 + (if n = 7 then (1 : ℚ) else 0) * 9 + (if n = 8 then (1 : ℚ) else 0) * 7 + (if n = 9 then (1 : ℚ) else 0) * 9 + (if n = 10 then (1 : ℚ) else 0) * 9 + (if n = 11 then (1 : ℚ) else 0) * 7 + (if n = 12 then (1 : ℚ) else 0) * 4 + (if n = 13 then (1 : ℚ) else 0) * 5 + (if n = 14 then (1 : ℚ) else 0) * 4 + (if n = 15 then (1 : ℚ) else 0) * 3 + (if n = 16 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 17 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 17) : ℚ) - 1 * (if 1 ≤ q + 17 then (b (q + 17 - 1) : ℚ) else 0) + 1 * (if 4 ≤ q + 17 then (b (q + 17 - 4) : ℚ) else 0) - 1 * (if 5 ≤ q + 17 then (b (q + 17 - 5) : ℚ) else 0) - 1 * (if 11 ≤ q + 17 then (b (q + 17 - 11) : ℚ) else 0) + 1 * (if 12 ≤ q + 17 then (b (q + 17 - 12) : ℚ) else 0) - 1 * (if 15 ≤ q + 17 then (b (q + 17 - 15) : ℚ) else 0) + 1 * (if 16 ≤ q + 17 then (b (q + 17 - 16) : ℚ) else 0) =
      (if q + 17 = 0 then (1 : ℚ) else 0) * 1 + (if q + 17 = 1 then (1 : ℚ) else 0) * 3 + (if q + 17 = 2 then (1 : ℚ) else 0) * 4 + (if q + 17 = 3 then (1 : ℚ) else 0) * 5 + (if q + 17 = 4 then (1 : ℚ) else 0) * 4 + (if q + 17 = 5 then (1 : ℚ) else 0) * 7 + (if q + 17 = 6 then (1 : ℚ) else 0) * 9 + (if q + 17 = 7 then (1 : ℚ) else 0) * 9 + (if q + 17 = 8 then (1 : ℚ) else 0) * 7 + (if q + 17 = 9 then (1 : ℚ) else 0) * 9 + (if q + 17 = 10 then (1 : ℚ) else 0) * 9 + (if q + 17 = 11 then (1 : ℚ) else 0) * 7 + (if q + 17 = 12 then (1 : ℚ) else 0) * 4 + (if q + 17 = 13 then (1 : ℚ) else 0) * 5 + (if q + 17 = 14 then (1 : ℚ) else 0) * 4 + (if q + 17 = 15 then (1 : ℚ) else 0) * 3 + (if q + 17 = 16 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 17) : ℤ) = b (q + 16) - b (q + 13) + b (q + 12) + b (q + 6) - b (q + 5) + b (q + 2) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 17 - 1 = q + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) q, show q + 17 - 4 = q + 13 from Nat.add_sub_assoc (by decide : 4 ≤ 17) q, show q + 17 - 5 = q + 12 from Nat.add_sub_assoc (by decide : 5 ≤ 17) q, show q + 17 - 11 = q + 6 from Nat.add_sub_assoc (by decide : 11 ≤ 17) q, show q + 17 - 12 = q + 5 from Nat.add_sub_assoc (by decide : 12 ≤ 17) q, show q + 17 - 15 = q + 2 from Nat.add_sub_assoc (by decide : 15 ≤ 17) q, show q + 17 - 16 = q + 1 from Nat.add_sub_assoc (by decide : 16 ≤ 17) q, show 1 ≤ q + 17 from le_trans (by decide : 1 ≤ 17) (Nat.le_add_left 17 q), show 4 ≤ q + 17 from le_trans (by decide : 4 ≤ 17) (Nat.le_add_left 17 q), show 5 ≤ q + 17 from le_trans (by decide : 5 ≤ 17) (Nat.le_add_left 17 q), show 11 ≤ q + 17 from le_trans (by decide : 11 ≤ 17) (Nat.le_add_left 17 q), show 12 ≤ q + 17 from le_trans (by decide : 12 ≤ 17) (Nat.le_add_left 17 q), show 15 ≤ q + 17 from le_trans (by decide : 15 ≤ 17) (Nat.le_add_left 17 q), show 16 ≤ q + 17 from le_trans (by decide : 16 ≤ 17) (Nat.le_add_left 17 q), show ¬ q + 17 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 14 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 14 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 15 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 15 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 16 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 16 < 17) (Nat.le_add_left 17 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * (X ^ 16 - X ^ 15 + X ^ 12 - X ^ 11 - X ^ 5 + X ^ 4 - X + 1) = C 1 * A - C 1 * (A * X ^ 1) + C 1 * (A * X ^ 4) - C 1 * (A * X ^ 5) - C 1 * (A * X ^ 11) + C 1 * (A * X ^ 12) - C 1 * (A * X ^ 15) + C 1 * (A * X ^ 16) := by
  simp only [map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (X ^ 16 + 3 * X ^ 15 + 4 * X ^ 14 + 5 * X ^ 13 + 4 * X ^ 12 + 7 * X ^ 11 + 9 * X ^ 10 + 9 * X ^ 9 + 7 * X ^ 8 + 9 * X ^ 7 + 9 * X ^ 6 + 7 * X ^ 5 + 4 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 3 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 3 + X ^ 2 * C 4 + X ^ 3 * C 5 + X ^ 4 * C 4 + X ^ 5 * C 7 + X ^ 6 * C 9 + X ^ 7 * C 9 + X ^ 8 * C 7 + X ^ 9 * C 9 + X ^ 10 * C 9 + X ^ 11 * C 7 + X ^ 12 * C 4 + X ^ 13 * C 5 + X ^ 14 * C 4 + X ^ 15 * C 3 + X ^ 16 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 16 - X ^ 15 + X ^ 12 - X ^ 11 - X ^ 5 + X ^ 4 - X + 1) =
      X ^ 16 + 3 * X ^ 15 + 4 * X ^ 14 + 5 * X ^ 13 + 4 * X ^ 12 + 7 * X ^ 11 + 9 * X ^ 10 + 9 * X ^ 9 + 7 * X ^ 8 + 9 * X ^ 7 + 9 * X ^ 6 + 7 * X ^ 5 + 4 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 3 * X + 1 := by
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
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 16 - X ^ 15 + X ^ 12 - X ^ 11 - X ^ 5 + X ^ 4 - X + 1) =
      X ^ 16 + 3 * X ^ 15 + 4 * X ^ 14 + 5 * X ^ 13 + 4 * X ^ 12 + 7 * X ^ 11 + 9 * X ^ 10 + 9 * X ^ 9 + 7 * X ^ 8 + 9 * X ^ 7 + 9 * X ^ 6 + 7 * X ^ 5 + 4 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 3 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 16 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + a (n - 5) + a (n - 11) - a (n - 12) + a (n - 15) - a (n - 16) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 13, 16, 20, 25, 29, 33, 38, 42, 46, 49, 53, 58, 61, 66, 71, 75, 79, 83, 87, 91, 94, 99, 104, 107, 112, 116, 120, 124, 128, 133, 137, 140, 145, 149, 152, 157, 161, 166, 170, 174, 179, 182, 185, 190, 194, 198, 203] := Count.controls

/-- The step a(n + 88) = a(n) + 364 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 88) = a n + 364 := Count.a_step n hn

/-- The closed form per residue of n mod 88, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (88 * k + 1) = 364 * k + 4 ∧
    a (88 * k + 2) = 364 * k + 8 ∧
    a (88 * k + 3) = 364 * k + 13 ∧
    a (88 * k + 4) = 364 * k + 16 ∧
    a (88 * k + 5) = 364 * k + 20 ∧
    a (88 * k + 6) = 364 * k + 25 ∧
    a (88 * k + 7) = 364 * k + 29 ∧
    a (88 * k + 8) = 364 * k + 33 ∧
    a (88 * k + 9) = 364 * k + 38 ∧
    a (88 * k + 10) = 364 * k + 42 ∧
    a (88 * k + 11) = 364 * k + 46 ∧
    a (88 * k + 12) = 364 * k + 49 ∧
    a (88 * k + 13) = 364 * k + 53 ∧
    a (88 * k + 14) = 364 * k + 58 ∧
    a (88 * k + 15) = 364 * k + 61 ∧
    a (88 * k + 16) = 364 * k + 66 ∧
    a (88 * k + 17) = 364 * k + 71 ∧
    a (88 * k + 18) = 364 * k + 75 ∧
    a (88 * k + 19) = 364 * k + 79 ∧
    a (88 * k + 20) = 364 * k + 83 ∧
    a (88 * k + 21) = 364 * k + 87 ∧
    a (88 * k + 22) = 364 * k + 91 ∧
    a (88 * k + 23) = 364 * k + 94 ∧
    a (88 * k + 24) = 364 * k + 99 ∧
    a (88 * k + 25) = 364 * k + 104 ∧
    a (88 * k + 26) = 364 * k + 107 ∧
    a (88 * k + 27) = 364 * k + 112 ∧
    a (88 * k + 28) = 364 * k + 116 ∧
    a (88 * k + 29) = 364 * k + 120 ∧
    a (88 * k + 30) = 364 * k + 124 ∧
    a (88 * k + 31) = 364 * k + 128 ∧
    a (88 * k + 32) = 364 * k + 133 ∧
    a (88 * k + 33) = 364 * k + 137 ∧
    a (88 * k + 34) = 364 * k + 140 ∧
    a (88 * k + 35) = 364 * k + 145 ∧
    a (88 * k + 36) = 364 * k + 149 ∧
    a (88 * k + 37) = 364 * k + 152 ∧
    a (88 * k + 38) = 364 * k + 157 ∧
    a (88 * k + 39) = 364 * k + 161 ∧
    a (88 * k + 40) = 364 * k + 166 ∧
    a (88 * k + 41) = 364 * k + 170 ∧
    a (88 * k + 42) = 364 * k + 174 ∧
    a (88 * k + 43) = 364 * k + 179 ∧
    a (88 * k + 44) = 364 * k + 182 ∧
    a (88 * k + 45) = 364 * k + 185 ∧
    a (88 * k + 46) = 364 * k + 190 ∧
    a (88 * k + 47) = 364 * k + 194 ∧
    a (88 * k + 48) = 364 * k + 198 ∧
    a (88 * k + 49) = 364 * k + 203 ∧
    a (88 * k + 50) = 364 * k + 207 ∧
    a (88 * k + 51) = 364 * k + 212 ∧
    a (88 * k + 52) = 364 * k + 215 ∧
    a (88 * k + 53) = 364 * k + 219 ∧
    a (88 * k + 54) = 364 * k + 224 ∧
    a (88 * k + 55) = 364 * k + 227 ∧
    a (88 * k + 56) = 364 * k + 231 ∧
    a (88 * k + 57) = 364 * k + 236 ∧
    a (88 * k + 58) = 364 * k + 240 ∧
    a (88 * k + 59) = 364 * k + 244 ∧
    a (88 * k + 60) = 364 * k + 248 ∧
    a (88 * k + 61) = 364 * k + 252 ∧
    a (88 * k + 62) = 364 * k + 257 ∧
    a (88 * k + 63) = 364 * k + 260 ∧
    a (88 * k + 64) = 364 * k + 265 ∧
    a (88 * k + 65) = 364 * k + 270 ∧
    a (88 * k + 66) = 364 * k + 273 ∧
    a (88 * k + 67) = 364 * k + 277 ∧
    a (88 * k + 68) = 364 * k + 281 ∧
    a (88 * k + 69) = 364 * k + 285 ∧
    a (88 * k + 70) = 364 * k + 289 ∧
    a (88 * k + 71) = 364 * k + 293 ∧
    a (88 * k + 72) = 364 * k + 298 ∧
    a (88 * k + 73) = 364 * k + 303 ∧
    a (88 * k + 74) = 364 * k + 306 ∧
    a (88 * k + 75) = 364 * k + 311 ∧
    a (88 * k + 76) = 364 * k + 315 ∧
    a (88 * k + 77) = 364 * k + 318 ∧
    a (88 * k + 78) = 364 * k + 322 ∧
    a (88 * k + 79) = 364 * k + 326 ∧
    a (88 * k + 80) = 364 * k + 331 ∧
    a (88 * k + 81) = 364 * k + 335 ∧
    a (88 * k + 82) = 364 * k + 339 ∧
    a (88 * k + 83) = 364 * k + 344 ∧
    a (88 * k + 84) = 364 * k + 348 ∧
    a (88 * k + 85) = 364 * k + 351 ∧
    a (88 * k + 86) = 364 * k + 356 ∧
    a (88 * k + 87) = 364 * k + 360 ∧
    a (88 * k + 88) = 364 * k + 364 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 16 - X ^ 15 + X ^ 12 - X ^ 11 - X ^ 5 + X ^ 4 - X + 1) =
      X ^ 16 + 3 * X ^ 15 + 4 * X ^ 14 + 5 * X ^ 13 + 4 * X ^ 12 + 7 * X ^ 11 + 9 * X ^ 10 + 9 * X ^ 9 + 7 * X ^ 8 + 9 * X ^ 7 + 9 * X ^ 6 + 7 * X ^ 5 + 4 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 3 * X + 1 ∧
    ∀ n : ℕ, 16 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + a (n - 5) + a (n - 11) - a (n - 12) + a (n - 15) - a (n - 16) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a311686

theorem OMA.solution : type_of% @OMA.S_oeis_a311686.main :=
  OMA.S_oeis_a311686.conjecture
