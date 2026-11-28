import OMAStatements.S_oeis_a313965

namespace OMA.S_oeis_a313965






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 9

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 2540009899
  | 1 => 2272758169
  | 2 => 2290649224
  | 3 => 2559015049
  | 4 => 2254867114
  | 5 => 2845271929
  | 6 => 2863162984
  | 7 => 2578020199
  | 8 => 2576906104
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 1737140614 4 8 i.val

def Bc (i : Fin 8) : ℤ := tget 2900059189 4 8 i.val

def Cc (s : Fin 9) (i : Fin 8) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 1737140614 4 i

def BcN (i : ℕ) : ℕ := tgetN 2900059189 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 8) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 8) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 9) (i : Fin 8) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


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
theorem cls (P : Fin 9 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 9 × Fin 9 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 9 × Fin 9 × ℤ × ℤ) (j : Fin 8) :
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
theorem farkas (x y : ℤ) (s : Fin 9) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
pot k2 ≤ pot i, 15 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 15526435221012291673611629532933937318408283662834968789951382263559360971784514930892047842927476547938168366362850234401290128266737187368857445515961404896035644830622628803306544481403741626627285900892846305305968223539654212200651893606252164709131099277322782177115955170187435575375273079452023101955245792227123172650576132164006505217465413436326488247558651584374257508302900647887449887482623596490579369977210233493866123965354413157950153843224967503611878830853458518196818528422968947454351433783971331654020929179036976517289650679686610550784 5 ((i * 8 + j) * 6 + f)

def fd (i j : Fin 8) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 0 % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 1 % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 8 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 3347787567263266976881909371121323964252467596480075530240 4 p

def dstv (p : ℕ) : ℕ := tgetN 2901511867355872552642262562938124767982701212688248693825 4 p

def dxv (p : ℕ) : ℕ := tgetN 27648616676212654221986977872 2 p

def dyv (p : ℕ) : ℕ := tgetN 26409411122351713108178064405 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 1286125185152896766221014680707070265330377149238364749396818577517886461985441783292312583042570303571134284415109647585228314335820753407019861105417604667171345613675352242482453478356343935841475754910172990098892604904386537857271361540765879211910305829519481713667923034732717317581615579212130024043156754009529327493402651282317461964633103182892295978936628574502056931749875505038676440785399853757251623018553635695077576542821728456587523814216726392 4 (p * 8 + j)

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
      fdN i j 4 * 23)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

def farOK : Bool := (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 9).all fun s => (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 48).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 8).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 9) (i j : Fin 8) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (15 - Cc s i)

/-- Beyond F = 14, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 9) (i j : Fin 8) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 14 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 15 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 14, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 14 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 10401192662967571427912689421907605072887756405920589175183427911762347298404048492119444265470987201741992836744317971385348524520871971946771405135896229466898419152336163408725236989981141008420277635841333157943840127128804323810691468490893163226948723814278803916733191341989932619145142173400025950975746514928153373310461940990948097438755818385086926792071161369268877812282328521448765830887768092070350405707878084005583095551693368707914668275057447055042731108791977767396313494375377952419170207812244338810028238367699067322457495882041445665761367699930745365886332593761831289566034414202289065795383290727648507892030032388637121324855237196229801442314492500956173213564306113805746814463628367518189507109387676520930101703561407299661162666359269859318264766474685012894094664089887930879788409298413557246629218804129723908757195548185888579343853954677656189252842122522354209853086539841
  | 1 => 10401192664769668970141298161095126912137814128140681702312005251497127405231674527709918108112070351056776135618571031042599483965140469318394798156371797972226962246131096163887977620759168952610581427317172471726998895785863903231945989815281634689518744429344371198901355487495076865026762389665285101943453155916969529351131202857160016871709001345138136668339027827313512202382135280846499343389088015030134126960222717415045987686577037356816514796089074233492165768472307247795717006693892735961203629447769172255918157365216504148401409286237354051122801099310613394487580805490051307066182927225012190418722944216095351978285683380666936268560027199430163600371107978159179776918654017207001031654910530234016592301495644750148158876584593808175573825651895951011153128933560030617787021989257009227036348164824093516181217313595323621823104783599826983199630648912823612585721004720317986522895917121
  | 2 => 10401192668373864054598515639470170590637929572580866756569159930966687618886592381327718383397611853759800722268818057042135419709698150569116184292449090057560061815865847085746430809988252416572056034514300045109687727384829333144876947352241782750178683129959325886022233144359645387997476917585121281921405258747969596782405505485438475576764831972382997605868565475942004275224139226653797423428585492634624982698999736259091821083212937665983010783057156488554251784306393549633804036429634724200301431347700364868252588119667231137540645494069940993174098219557875622919206545317735297216770848476973792079891573877136889083311178543929301138472062948721130916229715208112629541374024673106855932777529411161598940658926137400443184902145117195729642641061490992532919130057387878489444750732262440993114360202208496580849729838158464264727888799209491365273167211590743501890027595030796628536142766145
  | 3 => 10401192670175961596827124378657692429887987294800959283697737270701467725714107011063975763699845753166764306006497786726352466889046893288486546648699089298454676417998941193713054745291378258017728399523852173601090544652478562886713505862160948687042466121617663023607383775291512361122206269104346544780045770672261170975614319581737909494149484971584411318406286745057606224401926313003964930456171976174027637457488753786247318863945451955636381659285586829188028875520142292092519653253142844258581580495779950990117989656854153299263564052153071418046788801661707112971233531964842076755992843168773494811844973931194857337859415384548300077122353745362531365506461664907302839595556067550446158721503664853631815202560948904523567963322439765698806866176290256380196393679564263155175351641956531964223940510311515128989339009862607791185465013516839100149946960021046293257335797869156829758066171969
  | 4 => 10401192673780156681284341857032736201554362043030350436890339073581040730182514952559588649375177985680875438878117619136891564546622542439186078323080477479424840127158324813314012369593765749793941001385610979432032777143917393155020414192653452584834249377011834900113454417414277091725887179296512613588542252673270018289051492203642503242305200077013760454051919199603078221077505487449374171912197322617101949254052916544327045148324090089210179345548207931963388041746141682790790249873049557654546731594623168250409913626396603575627247874569272622209444940691735348368673218049876247933377244569801625863771165648999850177759187649224926851438217825707466092786064066705202982514307078982893457194984931566680320672864381674835673063614340109294121692712884942605059234617998730099658884689340243483480397943668150114902759404142866829701973537170281115041933914962342944434972163879758991105199349825
  | 5 => 10401192676783652584998689755678605840471532276274631883169187516395661450748327320096476804381301565478400307391400301083774596671934385136910449136824570357482077686654705267844878089392142876453206963758167084224715506461587776638221790721647659705117078278463975477356311553458031964287856178620803326893763447589174297399421085605091160197052554019773413690787448504230774710258026966853806664531769985825141274235817045680592378525070489625936813864988706255937211096000405595050491234666343332896425312498268992205902260179607538540992482255302350830972453809497891725978415364754987984990255065346713504455961168762578376578248404108534647802326203549713166056734636679091082253742075126539922099579862089646241159469301782907253453242756083623471584199675641053470946273862761445602684164087229344148372273166299817705443806326581909845385680313309122832805832052862940829378055064288667275238560669761
  | 6 => 10401192682189945211684515973241171358221705442934909464554919535600001771230871209304418906987874853360865318609207164831706916575065861016731864141621419198434577842503354016476472918180930198154965567135046646452863629306516035787310543062204351180368441574128245836232845037610896138258152252705441770807380721786987551897994710460692223221609373293350078088273833237274901720519492350847389799908481483600473755752319879775122770996724573679146320310834969749157237484788661691988327498605261832759243408687748451826446201218376492987071675020612913445397021082422885063025434129017495694474724793822566522014415263426027644877739738561420208113021852920584043915083097887854508969713523709632326238253081296905131858781289308422023933566779438276619873810668144506569538365164787088611064449503252405731010699878655445481058349692894132164355734735907233280838522623544192622542427398780438636472835416129
  | 7 => 10401192684592741934655994292157867143888449072561699500726355988579708580334224048952706744837511491880918667302175943379742297413306229620465107908425840258558991280882506754013958472630113351260223453402987400999519912809833888268982958219142429090121346277787568033695180694594415175906279662464688315162388672891168719189204328559330280153937124762012196570068838446678424562813045496547937007401021506787388906071591720489557964550113496039702739447352084880061553469239197884226286135252989976192360450046541039102913257666196695566636847646394349621522910640706194872564290568327837359799038569300578063749486248145658707095133203772966828489539724906361134224929501483883801836379461401177616685378419781156258150414647268558801010831896956342390670832827748007077128436779364867463952822068863313042190507709032993246450833591893222772616636804241774443037461425015036866362078262877991703699883466817
  | 8 => 10401192686995538657627472611074562929555192702188489536897792441559415389437576888600911578857135289367056317774878094334149193425147348916956166258176029771606374107299161933050899944607987858876232709557306508518024537058053370795293352433055863953036390127579191727884828877098741141784648693002009229647496597182586273713909190181569477120517463785468589879800898652658496700818035674183643923364287394924824611311695870678914323304221607674344606369535059014246846467531689550918619438247262893763527260264147909079021724660130164654607816124399293762547324498389240824851671192470286409704020661596079028517907959041532731128435215661166799282264571266788954711564985159382401666088594276144933594902597002896413815842965066267357085078137892269500546204436043017894911373629744193240215841783947282644595691612668472581295196199937574164271403454171064943958958624948931303676366621978804558019695910977
  | _ => 0

def rd (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 9) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 48 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 14)
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
theorem far_cert (s : Fin 9) (i j : Fin 8) (hij : nonadj i j) : farCert s i j := by
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

theorem point_contra (x y : ℤ) (s : Fin 9) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 14)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 14 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 14 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 9) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 14 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 14
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

theorem far_desc (v : V) (hF : 14 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 9) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 9, 0 < 2 * (Cc s 0 - 14) + 3 * (Cc s 7 - 14) + 0 * (Cc s 0 - 14) + 10 * 8 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 9, 0 < 3 * (Cc s 3 - 14) + 2 * (Cc s 4 - 14) + 0 * (Cc s 0 - 14) + 10 * 8 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 9, 0 < 1 * (Cc s 1 - 14) + 0 * (Cc s 0 - 14) + 0 * (Cc s 0 - 14) + 5 * 4 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 9, 0 < 1 * (Cc s 5 - 14) + 0 * (Cc s 0 - 14) + 0 * (Cc s 0 - 14) + 5 * 4 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 9, 0 < 2 * (Cc s 3 - (-1)) + 2 * (Cc s 7 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 14 lies in the cells |x| ≤ 7, |y| ≤ 3 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 9) (hF : F (x, y, s) ≤ 14) :
    -7 ≤ x ∧ x ≤ 7 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 7 0 14 2 3 0 1 0 8 10 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 4 0 14 3 2 0 (-1) 0 8 10 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 1 0 0 14 1 0 0 0 1 4 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 0 0 14 1 0 0 0 (-1) 4 5 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 3 7 0 (-1) 2 2 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 7, b - 3) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 197902830419973538407471051623998272714841984284651934631852948854359178722500486640849320520112251731978156331557280012117566189278312446105379651716472662761785265214914637132104482700050380468880935201023939230013158478689095467820884498719981669636564324804338022467609553767606924744336430966447408010117127076195048846074129653776276835293874872326017361341424779236229818037534747821414971008133510280575813505409794782145323480467669133555052615507673643714173796440644631423506364897165329176504456253222999899455997256898688474979002156376903128037980854955071182757581345250563660700692582778837090974392024384091629221191810594595971683416233229269011134304512843458269730791732766130969611221432048190242923867606718370823697545929236978570427858931329704118637338769347606946815989601574998648786005632056012187109495934479447352807145380685715317387696647484428682688614282377277032790884184943554033781172696446308699101585451714271029097544025386299262849326308393727177581489311026575976112536580842429876680089377871584433337961266578549173268053954676850040147241131900301254521699966259454809639871539165476234927528090342355224062897764595757771019995684464989498478151452320412675343766718900223466754336208209745324002045366108110591811028548382046969515702938985136207362911389279789384172233890665701768513375453578382482311261756515330430082429404320769899509655643371757748086750984411176744211910006086098969880025846167045009740240717820449068190104994072911016048236002732009500858276534755736768065819666863190167107565877661946523175373377193494353312230570042879451611110441603070242000308466162768824950982706516816052617216 >>> (6 * ((a * 7 + b) * 9 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 7, b - 3) and class s, potential i plus
26 + 2 a + 5 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 8) : ℕ :=
  tgetN 19153696 4 i.val * a + tgetN 2041065730 4 i.val * b + tgetN 6125293886038378495803489705632646985919198195799933796623279870639097769216611276474717599951918158861812990033206958824368769780 6 (s * 8 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)

theorem fnt_tab : ∀ s : Fin 9, ∀ i : Fin 8, (tgetN 19153696 4 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 2041065730 4 i.val : ℤ) = Bc i + 5 ∧
    (tgetN 6125293886038378495803489705632646985919198195799933796623279870639097769216611276474717599951918158861812990033206958824368769780 6 (s.val * 8 + i.val) : ℤ) = Cc s i - Ac i * 7 - Bc i * 3 + 26 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 9) (i : Fin 8) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 7, (b : ℤ) - 3, s) i + (26 + 2 * a + 5 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 9) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 7, (b : ℤ) - 3, s) + (26 + 2 * a + 5 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 14, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 5) 1 = FN + 2 dx' + 5 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 15).all fun a => (List.range 7).all fun b => (List.range 9).all fun s =>
    Nat.blt (40 + 2 * a + 5 * b) (FN a b s) || (a == 7 && b == 3 && s == 2) ||
      (Nat.blt (hint a b s) 48 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 7 ==
          FN a b s + 2 * dxv (hint a b s) + 5 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 14) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 7).toNat (by omega) (y + 3).toNat (by omega) s.val s.isLt
  have ex : (((x + 7).toNat : ℕ) : ℤ) - 7 = x := by omega
  have ey : (((y + 3).toNat : ℕ) : ℤ) - 3 = y := by omega
  generalize (x + 7).toNat = a at h' ex
  generalize (y + 3).toNat = b at h' ey
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
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 7 = x + dx := by omega
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 3 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 14
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
from below, and for n ≥ 9 the other facets lie below by Farkas certificates (`cf1` .. `cf0`: the
gradient part is checked once by `certG_ok`, the constant part for every class by `certC_ok`). So
each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor quotients
(`cnt_eq_S`), and shifting n by 30 moves every quotient by an integer (`inner_shift`, `S_shift`).
The tables are fields of natural numbers (`ctab`), which the kernel reads in constant time. The
section lives in the namespace `Count`; `gf`, `recur`, `controls` and `a_step` (and `a_closed` for
a short period) are restated after it. -/

namespace Count

/-- Field k of the B-bit fields packed in T (a table entry plus its offset). -/
def ctabN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

def gcV (k : ℕ) : ℕ := ctabN 4625513 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 8) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 2442960 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 8) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 1482108977 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 4

def Bp (i : Fin 8) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 17510 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 8) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 39440 2 k

def beN (k : ℕ) : ℤ := (beV k : ℤ) - 1

def be (i : Fin 8) : ℤ := beN i.val

theorem prim : ∀ i : Fin 8, Ac i = gc i * Ap i ∧ Bc i = gc i * Bp i ∧ 0 < gc i ∧
    al i * Ap i + be i * Bp i = 1 := by
  decide +kernel

/-- Potential j changes by Dm i j along the line of facet i, per lattice step. -/
def Dm (i j : Fin 8) : ℤ := Ac j * Bp i - Bc j * Ap i

def ka (i j : Fin 8) : ℤ := Ac j * al i + Bc j * be i

theorem orient : ∀ i : Fin 8, 0 < Dm i (i - 1) ∧ Dm i (i + 1) < 0 := by decide +kernel

/-- The point with parameter u on the line Ap i x + Bp i y = c, in class s. -/
def par (s : Fin 9) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 9) (i j : Fin 8) (c u : ℤ) :
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

theorem par_inj (s : Fin 9) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
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

/-! The Farkas multipliers (cf1, cf2, cf3, cf0) of the facet pair (i, j): cf1 times
(pot_(i-1) ≤ pot_i - [i-1 < i]) plus cf2 times (pot_(i+1) ≤ pot_i - [i+1 < i]) plus cf3 times
(pot_i ≤ pot_j) plus cf0 times (9 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 300412313239787302556888959881226766626142336860720729382050660432548462592 4 k

def cf1N (k : ℕ) : ℤ := (cf1V k : ℤ)

def cf1 (i : Fin 8) (j : Fin 8) : ℤ := cf1N (j.val + 8 * i.val)

def cf2V (k : ℕ) : ℕ := ctabN 33611936069765612401138218792634549406614365608484791820418126011172920064 4 k

def cf2N (k : ℕ) : ℤ := (cf2V k : ℤ)

def cf2 (i : Fin 8) (j : Fin 8) : ℤ := cf2N (j.val + 8 * i.val)

def cf3V (k : ℕ) : ℕ := ctabN 146779870916780397236025302483350295943049426111062454637308694424835922432 4 k

def cf3N (k : ℕ) : ℤ := (cf3V k : ℤ)

def cf3 (i : Fin 8) (j : Fin 8) : ℤ := cf3N (j.val + 8 * i.val)

def cf0V (k : ℕ) : ℕ := ctabN 1942557838715315632215201868560024861082851036196283136 3 k

def cf0N (k : ℕ) : ℤ := (cf0V k : ℤ)

def cf0 (i : Fin 8) (j : Fin 8) : ℤ := cf0N (j.val + 8 * i.val)


/-- The class-independent part of the certificate of (i, j): nonnegative multipliers whose
combination of the gradients vanishes. -/
def certG (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 ≤ cf1 i j ∧ 0 ≤ cf2 i j ∧ 0 ≤ cf3 i j ∧ 0 ≤ cf0 i j ∧
    cf1 i j * (Ac h - Ac i) + cf2 i j * (Ac k - Ac i) + cf3 i j * (Ac i - Ac j) - cf0 i j * Ac i = 0 ∧
    cf1 i j * (Bc h - Bc i) + cf2 i j * (Bc k - Bc i) + cf3 i j * (Bc i - Bc j) - cf0 i j * Bc i = 0

/-- The class constants Cc s i, packed for the kernel. -/
def cTV (k : ℕ) : ℕ := ctabN 60145403453215142654410403906081669838790710841009438264843076910 3 k

def cTN (k : ℕ) : ℤ := (cTV k : ℤ) - 3

def cT (s : Fin 9) (i : Fin 8) : ℤ := cTN (i.val + 8 * s.val)

theorem cT_eq : ∀ s : Fin 9, ∀ i : Fin 8, cT s i = Cc s i := by
  decide +kernel

/-- The part of the certificate of (i, j) for class s: the combination of the constants is positive. -/
def certC (s : Fin 9) (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (cT s h - cT s i + (if h < i then 1 else 0)) +
    cf2 i j * (cT s k - cT s i + (if k < i then 1 else 0)) + cf3 i j * (cT s i - cT s j) +
    cf0 i j * (9 - cT s i)

instance (i j : Fin 8) : Decidable (certG i j) := by
  unfold certG; infer_instance

theorem certG_ok : ∀ i j : Fin 8, j ≠ i - 1 → j ≠ i → j ≠ i + 1 → certG i j := by
  decide +kernel

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

/-- certC in natural numbers, for the kernel: Cc = cTV - 3, the negative terms moved across; the
previous facet of i is (i + 7) % 8, the next one (i + 1) % 8. -/
def certNat (s i j : ℕ) : Bool :=
  Nat.blt ((cf1V (j + 8 * i) + cf2V (j + 8 * i) + cf0V (j + 8 * i)) * cTV (i + 8 * s) +
      cf3V (j + 8 * i) * cTV (j + 8 * s))
    (cf1V (j + 8 * i) * (cTV ((i + 7) % 8 + 8 * s) + (if (i + 7) % 8 < i then 1 else 0)) +
      cf2V (j + 8 * i) * (cTV ((i + 1) % 8 + 8 * s) + (if (i + 1) % 8 < i then 1 else 0)) +
      cf3V (j + 8 * i) * cTV (i + 8 * s) + cf0V (j + 8 * i) * 12)

def certOK : Bool :=
  (List.range 9).all fun s => (List.range 8).all fun i => (List.range 8).all fun j =>
    nearB i j || certNat s i j

theorem certOK_eq : certOK = true := by
  decide +kernel

theorem fin_prev : ∀ i : Fin 8, (i - 1).val = (i.val + 7) % 8 := by decide +kernel

theorem fin_next : ∀ i : Fin 8, (i + 1).val = (i.val + 1) % 8 := by decide +kernel

/-- The constant parts of the certificates hold in the integers: the natural-number check moved
across. -/
theorem certC_ok (s : Fin 9) (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
    certC s i j := by
  have a1 := fin_prev i
  have a2 := fin_next i
  have hn : nearB i.val j.val = false := by
    have n1 : j.val ≠ i.val := fun h => e2 (Fin.ext h)
    have n2 : j.val ≠ (i.val + 1) % 8 := fun h => e3 (Fin.ext (h.trans a2.symm))
    have n3 : j.val ≠ (i.val + 7) % 8 := fun h => e1 (Fin.ext (h.trans a1.symm))
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
    cf3 i j * (cT s i - cT s j) + cf0 i j * (9 - cT s i)
  simp only [cf1, cf2, cf3, cf0, cf1N, cf2N, cf3N, cf0N, cT, cTN, Fin.lt_def, a1, a2]
  push_cast at ck ⊢
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
def lev (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 9) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 9) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 9) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 9) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 9) (i : Fin 8) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 9) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 9 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 9) (i : Fin 8) (n u : ℤ) (hn : 9 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 9 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 3)) (1 * n + 3) ×ˢ
    (Finset.Icc (-(1 * n + 3)) (1 * n + 3) ×ˢ Finset.univ)

theorem Cbound : ∀ s : Fin 9, ∀ j : Fin 8, -3 ≤ Cc s j ∧ Cc s j ≤ 3 := by decide +kernel

/-- Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/
theorem box_pairs : 3 * Ac 3 + 2 * Ac 4 = 10 ∧ 3 * Bc 3 + 2 * Bc 4 = 0 ∧
    2 * Ac 0 + 3 * Ac 7 = (-10) ∧ 2 * Bc 0 + 3 * Bc 7 = 0 ∧
    1 * Ac 5 + 0 * Ac 5 = 0 ∧ 1 * Bc 5 + 0 * Bc 5 = 5 ∧
    1 * Ac 1 + 0 * Ac 1 = 0 ∧ 1 * Bc 1 + 0 * Bc 1 = (-5) := by
  decide +kernel

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 9) :
    10 * x ≤ 5 * F (x, y, s) + 15 ∧
    10 * (-x) ≤ 5 * F (x, y, s) + 15 ∧
    5 * y ≤ 1 * F (x, y, s) + 3 ∧
    5 * (-y) ≤ 1 * F (x, y, s) + 3 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 3 * pot (x, y, s) 3 + 2 * pot (x, y, s) 4 =
      10 * x + 3 * Cc s 3 + 2 * Cc s 4 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 3
  have r0 := le_F (x, y, s) 4
  have k0 := Cbound s 3
  have l0 := Cbound s 4
  have e1 : 2 * pot (x, y, s) 0 + 3 * pot (x, y, s) 7 =
      10 * (-x) + 2 * Cc s 0 + 3 * Cc s 7 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 7
  have k1 := Cbound s 0
  have l1 := Cbound s 7
  have e2 : 1 * pot (x, y, s) 5 + 0 * pot (x, y, s) 5 =
      5 * y + 1 * Cc s 5 + 0 * Cc s 5 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 5
  have r2 := le_F (x, y, s) 5
  have k2 := Cbound s 5
  have l2 := Cbound s 5
  have e3 : 1 * pot (x, y, s) 1 + 0 * pot (x, y, s) 1 =
      5 * (-y) + 1 * Cc s 1 + 0 * Cc s 1 := by
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
noncomputable def PF (s : Fin 9) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 9) (i : Fin 8) (n : ℤ) (hn : 9 ≤ n) :
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
def inner (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 9) (i : Fin 8) (n : ℤ) (hn : 9 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 9 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 8, inner p.1 p.2 n

/-! Shifting n by 30 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 547841636574 5 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 8) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 17742971417 5 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 10

def mh (i : Fin 8) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 935834000960 5 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 12

def mk (i : Fin 8) : ℤ := mkN i.val

theorem shift_ok : ∀ i : Fin 8, (30 : ℤ) = gc i * Lq i ∧
    30 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧
    30 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := by
  decide +kernel

theorem inner_shift (s : Fin 9) (i : Fin 8) (n : ℤ) :
    inner s i (n + 30) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 30 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 30 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 30) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 30) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 30) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
    rw [← e2]; simp only [Rb, hl]; ring
  rw [inner, inner, hm]
  split_ifs
  · simp only [hi, lo, r1, r2]
    rw [Int.add_mul_ediv_left _ _ (ne_of_gt (orient i).1),
      Int.add_mul_ediv_left _ _ (ne_of_gt (show 0 < -Dm i (i + 1) by linarith [(orient i).2]))]
    ring
  · ring

/-- The growth of S over one period, from the residue of n mod 10 = gc i * lgq i. -/
def Gs (n : ℤ) : ℤ :=
  ∑ q : Fin 9 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 30) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

def lgqV (k : ℕ) : ℕ := ctabN 1512725034 4 k

def lgqN (k : ℕ) : ℤ := (lgqV k : ℤ)

def lgq (i : Fin 8) : ℤ := lgqN i.val

theorem lg_ok : ∀ i : Fin 8, (10 : ℤ) = gc i * lgq i := by
  decide +kernel

theorem Gs_periodic (x q : ℤ) : Gs (x + 10 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 10 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (lgq r.2 * q) := by
    linear_combination q * lg_ok r.2
  rw [e, Int.add_mul_emod_self_left]

theorem mhk_nonneg : ∀ i : Fin 8, 0 ≤ mh i + mk i := by decide +kernel

/-- The growth of the piece with index c = i + 8 s, read by the kernel from the tables. -/
def gsN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 8) = 0 then mhN (c % 8) + mkN (c % 8) else 0

theorem gsN_eq (s : Fin 9) (i : Fin 8) (n : ℤ) :
    gsN (i.val + 8 * s.val) n = (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  have hi := i.isLt
  have h : (i.val + 8 * s.val) % 8 = i.val := by omega
  rw [gsN, h, ← cT_eq]
  rfl

def GsN (n : ℤ) : ℤ := ((List.range (9 * 8)).map fun c => gsN c n).sum

/-! The piece length in table form, for the kernel: on a level with points, inner s i n is
(uh i c + vh s i) / dh i + (uk i c + vk s i) / dk i + 1 with c = lev s i n. -/

def uhV (k : ℕ) : ℕ := ctabN 946407 3 k

def uhN (k : ℕ) : ℤ := (uhV k : ℤ) - 2

def uh (i : Fin 8) : ℤ := uhN i.val

def dhV (k : ℕ) : ℕ := ctabN 891958570 4 k

def dhN (k : ℕ) : ℤ := (dhV k : ℤ)

def dh (i : Fin 8) : ℤ := dhN i.val

def ukV (k : ℕ) : ℕ := ctabN 2471531344 4 k

def ukN (k : ℕ) : ℤ := (ukV k : ℤ) - 4

def uk (i : Fin 8) : ℤ := ukN i.val

def dkV (k : ℕ) : ℕ := ctabN 1444566554 4 k

def dkN (k : ℕ) : ℤ := (dkV k : ℤ)

def dk (i : Fin 8) : ℤ := dkN i.val

def vhV (k : ℕ) : ℕ := ctabN 30320574969841570942888669303683010203843430399875143786537254989 3 k

def vhN (k : ℕ) : ℤ := (vhV k : ℤ) - 3

def vh (s : Fin 9) (i : Fin 8) : ℤ := vhN (i.val + 8 * s.val)

def vkV (k : ℕ) : ℕ := ctabN 45104921473809071522361737075997725538459887003079451188264250212 3 k

def vkN (k : ℕ) : ℤ := (vkV k : ℤ) - 3

def vk (s : Fin 9) (i : Fin 8) : ℤ := vkN (i.val + 8 * s.val)

def levT (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ := (n - cT s i) / gc i

def innerT (s : Fin 9) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - cT s i) % gc i = 0 then
    (uh i * levT s i n + vh s i) / dh i + (uk i * levT s i n + vk s i) / dk i + 1 else 0

theorem tab_facet : ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧
    uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) := by
  decide +kernel

theorem tab_class : ∀ s : Fin 9, ∀ i : Fin 8,
    vh s i = cT s i - cT s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    vk s i = cT s i - cT s (i + 1) - (if i + 1 < i then 1 else 0) := by
  decide +kernel

theorem tab_ok (s : Fin 9) (i : Fin 8) : uh i = gc i - ka i (i - 1) ∧
    vh s i = Cc s i - Cc s (i - 1) - (if i - 1 < i then 1 else 0) ∧
    dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧
    vk s i = Cc s i - Cc s (i + 1) - (if i + 1 < i then 1 else 0) ∧
    dk i = -Dm i (i + 1) := by
  obtain ⟨f1, f2, f3, f4⟩ := tab_facet i
  obtain ⟨c1, c2⟩ := tab_class s i
  simp only [cT_eq] at c1 c2
  exact ⟨f1, c1, f2, f3, c2, f4⟩

theorem inner_eq (s : Fin 9) (i : Fin 8) (n : ℤ) : inner s i n = innerT s i n := by
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
def ST (n : ℤ) : ℤ := ∑ p : Fin 9 × Fin 8, innerT p.1 p.2 n

theorem S_eq_ST (n : ℤ) : S n = ST n := by
  simp only [S, ST, inner_eq]

/-- The piece length with index c = i + 8 s, read by the kernel from the tables directly. -/
def innerN (c : ℕ) (n : ℤ) : ℤ :=
  if (n - cTN c) % gcN (c % 8) = 0 then
    (uhN (c % 8) * ((n - cTN c) / gcN (c % 8)) + vhN c) / dhN (c % 8) +
      (ukN (c % 8) * ((n - cTN c) / gcN (c % 8)) + vkN c) / dkN (c % 8) + 1
  else 0

theorem innerN_eq (s : Fin 9) (i : Fin 8) (n : ℤ) :
    innerN (i.val + 8 * s.val) n = innerT s i n := by
  have hi := i.isLt
  have h : (i.val + 8 * s.val) % 8 = i.val := by omega
  rw [innerN, h]
  rfl

theorem sum_range_list (f : ℕ → ℤ) (N : ℕ) :
    ∑ c ∈ Finset.range N, f c = ((List.range N).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

/-- The closed form over the indices of the pieces. -/
def STN (n : ℤ) : ℤ := ((List.range (9 * 8)).map fun c => innerN c n).sum

theorem ST_eq_STN (n : ℤ) : ST n = STN n := by
  rw [ST, STN, Fintype.sum_equiv finProdFinEquiv (fun q : Fin 9 × Fin 8 => innerT q.1 q.2 n)
    (fun c : Fin (9 * 8) => innerN c.val n) (fun q => (innerN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => innerN c n) (9 * 8), sum_range_list]

theorem Gs_eq_GsN (n : ℤ) : Gs n = GsN n := by
  rw [Gs, GsN, Fintype.sum_equiv finProdFinEquiv
    (fun q : Fin 9 × Fin 8 => if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)
    (fun c : Fin (9 * 8) => gsN c.val n) (fun q => (gsN_eq q.1 q.2 n).symm),
    Fin.sum_univ_eq_sum_range (fun c => gsN c n) (9 * 8), sum_range_list]

/-- The closed form's tables, packed: the steps, the values on one period from 1 and below 1. -/
def dtabV (k : ℕ) : ℕ := ctabN 1177304920225804522931586424509983951612757686767665113043465490460093076 8 k

def tblV (k : ℕ) : ℕ := ctabN 1177169060342241746766219028647176174107701212888630755378517996246993413 8 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 30. -/
def dv (t : ℕ) : ℕ := dtabV (t % 30)

/-- The sequence in closed form: b(n + 30) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 30) + tblV ((n - 1) % 30)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 30) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 30 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 30 - 1 = n - 1 + 30 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 30)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 30) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 30 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 30 - 1 = n - 1 + 30 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 30)]
  ring

/-- b on the residue class of 1 + j mod 30. -/
theorem b_res (k j : ℕ) (hj : j < 30) : b (30 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (30 * k + (1 + j) < 1) by omega),
    show 30 * k + (1 + j) - 1 = j + 30 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 30), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The growth of S over one period at each residue mod 10. -/
def GsT : List ℤ := [170, 148, 170, 160, 158, 160, 158, 160, 170, 148]

theorem Gs_tab : ∀ r : ℕ, r < 10 → GsN (r : ℤ) = GsT.getD r 0 := by
  decide +kernel

/-- The growth of b over 30 terms is that of S, on one period of the residues. -/
theorem grow_base : ∀ t : ℕ, t < 30 → 1 * (dv t : ℤ) = GsT.getD ((1 + t) % 10) 0 := by
  decide +kernel

theorem grow (n : ℕ) (_hn : 1 ≤ n) : 1 * (dv (n - 1) : ℤ) = Gs n := by
  have h1 := grow_base ((n - 1) % 30) (Nat.mod_lt _ (by norm_num))
  have e1 : dv ((n - 1) % 30) = dv (n - 1) := by
    rw [dv, dv, Nat.mod_mod_of_dvd _ (by norm_num : 30 ∣ 30)]
  have e2 : (1 + (n - 1) % 30) % 10 = n % 10 := by omega
  rw [e1, e2, ← Gs_tab (n % 10) (Nat.mod_lt _ (by norm_num)), ← Gs_eq_GsN] at h1
  rw [h1]
  have e3 : (((n % 10 : ℕ) : ℤ) + 10 * ((n / 10 : ℕ) : ℤ)) = n := by omega
  rw [← e3, Gs_periodic]

/-- One kernel pass over n = 9, ..., 38: every piece length is nonnegative and the
closed form agrees with b. -/
theorem period_ok : ∀ r : ℕ, r < 30 →
    ((List.range (9 * 8)).all fun c => decide (0 ≤ innerN c (9 + (r : ℤ)))) = true ∧
      STN (9 + (r : ℤ)) = b (9 + r) := by
  decide +kernel

/-- Every piece length is nonnegative from n = 9 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 9) (i : Fin 8) (n : ℤ) (hn : 9 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 9 + t := ⟨(n - 9).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 30
    · rw [inner_eq, ← innerN_eq]
      have hc : i.val + 8 * s.val < 9 * 8 := by
        have := i.isLt
        have := s.isLt
        omega
      exact of_decide_eq_true (List.all_eq_true.1 (period_ok t ht).1 _ (List.mem_range.2 hc))
    · have := ih (t - 30) (by omega) (by omega)
      have e : (9 : ℤ) + t = (9 + (t - 30 : ℕ)) + 30 := by
        push_cast [Nat.cast_sub (by omega : 30 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos := mhk_nonneg i
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 9 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

theorem S_eq_b (n : ℕ) (hn : 9 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 39
    · obtain ⟨r, rfl⟩ : ∃ r, n = 9 + r := ⟨n - 9, by omega⟩
      rw [S_eq_ST, ST_eq_STN]
      push_cast
      exact (period_ok r (by omega)).2
    · have h1 := ih (n - 30) (by omega) (by omega)
      have h2 := S_shift ((n - 30 : ℕ) : ℤ)
      have h3 := b_shift (n - 30) (by omega)
      have h4 := grow (n - 30) (by omega)
      rw [show n - 30 + 30 = n by omega] at h3
      rw [show ((n - 30 : ℕ) : ℤ) + 30 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 8 lie in the box -5 ≤ x ≤ 5, -2 ≤ y ≤ 2 (`small_box`), and
the kernel checks that those of the box are the 195 points of `smallL` (`smallOK_eq`). -/

theorem small_box (x y : ℤ) (s : Fin 9) (h : F (x, y, s) ≤ 8) :
    -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- The points with F ≤ 8, with their values of F. -/
def smallV : List (V × ℤ) :=
  [((0, 0, 2), 0), ((0, 0, 1), 1), ((0, 0, 3), 1), ((0, 0, 8), 1), ((1, 0, 3), 1), ((1, 0, 5), 1), (((-1), 0, 2), 2), ((0, 0, 4), 2), ((0, 0, 5), 2), ((0, 0, 6), 2), ((0, 0, 7), 2), ((1, 0, 0), 2), ((1, 0, 1), 2), ((1, 0, 2), 2), ((1, 0, 6), 2), ((1, 0, 8), 2), (((-1), 0, 1), 3), (((-1), 0, 3), 3), (((-1), 0, 7), 3), (((-1), 0, 8), 3), ((0, (-1), 6), 3), ((0, (-1), 7), 3), ((0, 0, 0), 3), ((0, 1, 0), 3), ((0, 1, 4), 3), ((1, (-1), 6), 3), ((1, 0, 4), 3), ((1, 0, 7), 3), ((1, 1, 0), 3), ((1, 1, 4), 3), ((2, 0, 0), 3), ((2, 0, 3), 3), ((2, 0, 5), 3), (((-2), 0, 2), 4), (((-1), (-1), 7), 4), (((-1), 0, 4), 4), (((-1), 0, 5), 4), (((-1), 0, 6), 4), (((-1), 1, 1), 4), (((-1), 1, 4), 4), ((0, (-1), 5), 4), ((0, (-1), 8), 4), ((0, 1, 1), 4), ((1, (-1), 5), 4), ((1, (-1), 7), 4), ((1, (-1), 8), 4), ((1, 1, 1), 4), ((2, (-1), 6), 4), ((2, 0, 1), 4), ((2, 0, 2), 4), ((2, 0, 4), 4), ((2, 0, 6), 4), ((2, 0, 8), 4), ((2, 1, 0), 4), (((-2), 0, 1), 5), (((-2), 0, 3), 5), (((-2), 0, 7), 5), (((-2), 0, 8), 5), (((-1), (-1), 2), 5), (((-1), (-1), 6), 5), (((-1), (-1), 8), 5), (((-1), 0, 0), 5), (((-1), 1, 0), 5), (((-1), 1, 2), 5), (((-1), 1, 3), 5), ((0, (-1), 2), 5), ((0, (-1), 3), 5), ((0, 1, 2), 5), ((0, 1, 3), 5), ((1, (-1), 2), 5), ((1, (-1), 3), 5), ((1, 1, 2), 5), ((1, 1, 3), 5), ((2, (-1), 5), 5), ((2, (-1), 7), 5), ((2, (-1), 8), 5), ((2, 0, 7), 5), ((2, 1, 4), 5), ((3, 0, 0), 5), ((3, 0, 3), 5), ((3, 0, 5), 5), (((-3), 0, 2), 6), (((-2), (-1), 7), 6), (((-2), 0, 4), 6), (((-2), 0, 5), 6), (((-2), 0, 6), 6), (((-2), 1, 1), 6), (((-2), 1, 2), 6), (((-2), 1, 4), 6), (((-1), (-1), 1), 6), (((-1), (-1), 3), 6), (((-1), (-1), 5), 6), (((-1), 1, 5), 6), (((-1), 1, 8), 6), ((0, (-1), 1), 6), ((0, 1, 5), 6), ((0, 1, 8), 6), ((1, (-1), 1), 6), ((1, 1, 5), 6), ((1, 1, 8), 6), ((2, (-1), 2), 6), ((2, (-1), 3), 6), ((2, 1, 1), 6), ((2, 1, 3), 6), ((2, 1, 5), 6), ((3, (-1), 5), 6), ((3, (-1), 6), 6), ((3, 0, 1), 6), ((3, 0, 2), 6), ((3, 0, 4), 6), ((3, 0, 6), 6), ((3, 0, 8), 6), ((3, 1, 0), 6), (((-3), 0, 1), 7), (((-3), 0, 3), 7), (((-3), 0, 7), 7), (((-3), 0, 8), 7), (((-2), (-1), 2), 7), (((-2), (-1), 6), 7), (((-2), (-1), 8), 7), (((-2), 0, 0), 7), (((-2), 1, 0), 7), (((-2), 1, 3), 7), (((-2), 1, 7), 7), (((-2), 1, 8), 7), (((-1), (-1), 4), 7), (((-1), 1, 6), 7), (((-1), 1, 7), 7), ((0, (-1), 0), 7), ((0, (-1), 4), 7), ((0, 1, 6), 7), ((0, 1, 7), 7), ((1, (-1), 0), 7), ((1, (-1), 4), 7), ((1, 1, 6), 7), ((1, 1, 7), 7), ((2, (-1), 0), 7), ((2, (-1), 1), 7), ((2, 1, 2), 7), ((2, 1, 6), 7), ((2, 1, 8), 7), ((3, (-1), 3), 7), ((3, (-1), 7), 7), ((3, (-1), 8), 7), ((3, 0, 7), 7), ((3, 1, 4), 7), ((4, 0, 0), 7), ((4, 0, 3), 7), ((4, 0, 5), 7), (((-4), 0, 2), 8), (((-3), (-1), 7), 8), (((-3), 0, 4), 8), (((-3), 0, 5), 8), (((-3), 0, 6), 8), (((-3), 1, 1), 8), (((-3), 1, 2), 8), (((-3), 1, 4), 8), (((-2), (-1), 1), 8), (((-2), (-1), 3), 8), (((-2), (-1), 5), 8), (((-2), 1, 5), 8), (((-2), 1, 6), 8), (((-2), 2, 4), 8), (((-1), (-2), 6), 8), (((-1), (-2), 7), 8), (((-1), (-1), 0), 8), (((-1), 2, 0), 8), (((-1), 2, 4), 8), ((0, (-2), 6), 8), ((0, (-2), 7), 8), ((0, 2, 0), 8), ((0, 2, 4), 8), ((1, (-2), 6), 8), ((1, (-2), 7), 8), ((1, 2, 0), 8), ((1, 2, 4), 8), ((2, (-2), 6), 8), ((2, (-1), 4), 8), ((2, 1, 7), 8), ((2, 2, 0), 8), ((2, 2, 4), 8), ((3, (-1), 0), 8), ((3, (-1), 1), 8), ((3, (-1), 2), 8), ((3, 1, 1), 8), ((3, 1, 3), 8), ((3, 1, 5), 8), ((4, (-1), 5), 8), ((4, (-1), 6), 8), ((4, 0, 1), 8), ((4, 0, 2), 8), ((4, 0, 4), 8), ((4, 0, 6), 8), ((4, 0, 8), 8), ((4, 1, 0), 8)]

def smallL : List V := smallV.map Prod.fst

theorem smallV_ok : (smallV.all fun q => decide (F q.1 = q.2)) = true := by
  decide +kernel

/-- The potentials, packed: Ac = ATV - 2, Bc = BTV - 5. -/
def ATV (k : ℕ) : ℕ := ctabN 346320 3 k

def ATN (k : ℕ) : ℤ := (ATV k : ℤ) - 2

def AT (i : Fin 8) : ℤ := ATN i.val

def BTV (k : ℕ) : ℕ := ctabN 2041065730 4 k

def BTN (k : ℕ) : ℤ := (BTV k : ℤ) - 5

def BT (i : Fin 8) : ℤ := BTN i.val

theorem AB_eq : ∀ i : Fin 8, AT i = Ac i ∧ BT i = Bc i := by
  decide +kernel

/-- Some potential exceeds 8 at the box point ((a : ℤ) - 5, (b : ℤ) - 2, s), in natural
numbers: the negative terms moved across. -/
def bigNat (a b s : ℕ) : Bool :=
  (List.range 8).any fun i =>
    Nat.blt (11 + ATV i * 5 + 2 * a + BTV i * 2 + 5 * b)
      (ATV i * a + 10 + BTV i * b + 10 + cTV (i + 8 * s))

theorem big_pot (a b : ℕ) (s : Fin 9) (h : bigNat a b s.val = true) :
    (8 : ℤ) < F ((a : ℤ) - 5, (b : ℤ) - 2, s) := by
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

theorem small_mem (v : V) (hF : F v ≤ 8) : v ∈ smallL := by
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

theorem cnt_small (n : ℤ) (hn : n ≤ 8) :
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
theorem small_ok : ∀ n : ℕ, n < 9 →
    (((smallV.filter (fun q => decide (q.2 = (n : ℤ)))).map Prod.fst).toFinset).card = b n := by
  decide +kernel

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 9 are counted in
`smallL`, those from 9 on are S(n), and both agree with the closed form b (`a_eq_b`). The step
from n to n + 30, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f.
follow, their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 9 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 9 ∨ 9 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_ok n h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 30) = a(n) + dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 30) = a n + dv (n - 1) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-- The steps and the values on one period, by the kernel. -/
theorem closed_vals : dv 0 = 148 ∧ tblV 0 = 5 ∧ dv 1 = 170 ∧ tblV 1 = 10 ∧ dv 2 = 160 ∧ tblV 2 = 17 ∧ dv 3 = 158 ∧ tblV 3 = 21 ∧ dv 4 = 160 ∧ tblV 4 = 27 ∧ dv 5 = 158 ∧ tblV 5 = 32 ∧ dv 6 = 160 ∧ tblV 6 = 36 ∧ dv 7 = 170 ∧ tblV 7 = 46 ∧ dv 8 = 148 ∧ tblV 8 = 44 ∧ dv 9 = 170 ∧ tblV 9 = 57 ∧ dv 10 = 148 ∧ tblV 10 = 55 ∧ dv 11 = 170 ∧ tblV 11 = 67 ∧ dv 12 = 160 ∧ tblV 12 = 70 ∧ dv 13 = 158 ∧ tblV 13 = 73 ∧ dv 14 = 160 ∧ tblV 14 = 80 ∧ dv 15 = 158 ∧ tblV 15 = 85 ∧ dv 16 = 160 ∧ tblV 16 = 90 ∧ dv 17 = 170 ∧ tblV 17 = 103 ∧ dv 18 = 148 ∧ tblV 18 = 93 ∧ dv 19 = 170 ∧ tblV 19 = 113 ∧ dv 20 = 148 ∧ tblV 20 = 104 ∧ dv 21 = 170 ∧ tblV 21 = 124 ∧ dv 22 = 160 ∧ tblV 22 = 124 ∧ dv 23 = 158 ∧ tblV 23 = 126 ∧ dv 24 = 160 ∧ tblV 24 = 133 ∧ dv 25 = 158 ∧ tblV 25 = 137 ∧ dv 26 = 160 ∧ tblV 26 = 143 ∧ dv 27 = 170 ∧ tblV 27 = 160 ∧ dv 28 = 148 ∧ tblV 28 = 143 ∧ dv 29 = 170 ∧ tblV 29 = 170 := by
  decide +kernel

/-- The closed form per residue of n mod 30, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (30 * k + 1) = 148 * k + 5 ∧
    a (30 * k + 2) = 170 * k + 10 ∧
    a (30 * k + 3) = 160 * k + 17 ∧
    a (30 * k + 4) = 158 * k + 21 ∧
    a (30 * k + 5) = 160 * k + 27 ∧
    a (30 * k + 6) = 158 * k + 32 ∧
    a (30 * k + 7) = 160 * k + 36 ∧
    a (30 * k + 8) = 170 * k + 46 ∧
    a (30 * k + 9) = 148 * k + 44 ∧
    a (30 * k + 10) = 170 * k + 57 ∧
    a (30 * k + 11) = 148 * k + 55 ∧
    a (30 * k + 12) = 170 * k + 67 ∧
    a (30 * k + 13) = 160 * k + 70 ∧
    a (30 * k + 14) = 158 * k + 73 ∧
    a (30 * k + 15) = 160 * k + 80 ∧
    a (30 * k + 16) = 158 * k + 85 ∧
    a (30 * k + 17) = 160 * k + 90 ∧
    a (30 * k + 18) = 170 * k + 103 ∧
    a (30 * k + 19) = 148 * k + 93 ∧
    a (30 * k + 20) = 170 * k + 113 ∧
    a (30 * k + 21) = 148 * k + 104 ∧
    a (30 * k + 22) = 170 * k + 124 ∧
    a (30 * k + 23) = 160 * k + 124 ∧
    a (30 * k + 24) = 158 * k + 126 ∧
    a (30 * k + 25) = 160 * k + 133 ∧
    a (30 * k + 26) = 158 * k + 137 ∧
    a (30 * k + 27) = 160 * k + 143 ∧
    a (30 * k + 28) = 170 * k + 160 ∧
    a (30 * k + 29) = 148 * k + 143 ∧
    a (30 * k + 30) = 170 * k + 170 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59⟩ := closed_vals
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 30 * k + 1 = 30 * k + (1 + 0) from rfl, b_res k 0 (by norm_num), c0, c1]
  · rw [show 30 * k + 2 = 30 * k + (1 + 1) from rfl, b_res k 1 (by norm_num), c2, c3]
  · rw [show 30 * k + 3 = 30 * k + (1 + 2) from rfl, b_res k 2 (by norm_num), c4, c5]
  · rw [show 30 * k + 4 = 30 * k + (1 + 3) from rfl, b_res k 3 (by norm_num), c6, c7]
  · rw [show 30 * k + 5 = 30 * k + (1 + 4) from rfl, b_res k 4 (by norm_num), c8, c9]
  · rw [show 30 * k + 6 = 30 * k + (1 + 5) from rfl, b_res k 5 (by norm_num), c10, c11]
  · rw [show 30 * k + 7 = 30 * k + (1 + 6) from rfl, b_res k 6 (by norm_num), c12, c13]
  · rw [show 30 * k + 8 = 30 * k + (1 + 7) from rfl, b_res k 7 (by norm_num), c14, c15]
  · rw [show 30 * k + 9 = 30 * k + (1 + 8) from rfl, b_res k 8 (by norm_num), c16, c17]
  · rw [show 30 * k + 10 = 30 * k + (1 + 9) from rfl, b_res k 9 (by norm_num), c18, c19]
  · rw [show 30 * k + 11 = 30 * k + (1 + 10) from rfl, b_res k 10 (by norm_num), c20, c21]
  · rw [show 30 * k + 12 = 30 * k + (1 + 11) from rfl, b_res k 11 (by norm_num), c22, c23]
  · rw [show 30 * k + 13 = 30 * k + (1 + 12) from rfl, b_res k 12 (by norm_num), c24, c25]
  · rw [show 30 * k + 14 = 30 * k + (1 + 13) from rfl, b_res k 13 (by norm_num), c26, c27]
  · rw [show 30 * k + 15 = 30 * k + (1 + 14) from rfl, b_res k 14 (by norm_num), c28, c29]
  · rw [show 30 * k + 16 = 30 * k + (1 + 15) from rfl, b_res k 15 (by norm_num), c30, c31]
  · rw [show 30 * k + 17 = 30 * k + (1 + 16) from rfl, b_res k 16 (by norm_num), c32, c33]
  · rw [show 30 * k + 18 = 30 * k + (1 + 17) from rfl, b_res k 17 (by norm_num), c34, c35]
  · rw [show 30 * k + 19 = 30 * k + (1 + 18) from rfl, b_res k 18 (by norm_num), c36, c37]
  · rw [show 30 * k + 20 = 30 * k + (1 + 19) from rfl, b_res k 19 (by norm_num), c38, c39]
  · rw [show 30 * k + 21 = 30 * k + (1 + 20) from rfl, b_res k 20 (by norm_num), c40, c41]
  · rw [show 30 * k + 22 = 30 * k + (1 + 21) from rfl, b_res k 21 (by norm_num), c42, c43]
  · rw [show 30 * k + 23 = 30 * k + (1 + 22) from rfl, b_res k 22 (by norm_num), c44, c45]
  · rw [show 30 * k + 24 = 30 * k + (1 + 23) from rfl, b_res k 23 (by norm_num), c46, c47]
  · rw [show 30 * k + 25 = 30 * k + (1 + 24) from rfl, b_res k 24 (by norm_num), c48, c49]
  · rw [show 30 * k + 26 = 30 * k + (1 + 25) from rfl, b_res k 25 (by norm_num), c50, c51]
  · rw [show 30 * k + 27 = 30 * k + (1 + 26) from rfl, b_res k 26 (by norm_num), c52, c53]
  · rw [show 30 * k + 28 = 30 * k + (1 + 27) from rfl, b_res k 27 (by norm_num), c54, c55]
  · rw [show 30 * k + 29 = 30 * k + (1 + 28) from rfl, b_res k 28 (by norm_num), c56, c57]
  · rw [show 30 * k + 30 = 30 * k + (1 + 29) from rfl, b_res k 29 (by norm_num), c58, c59]

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 17, 21, 27, 32, 36, 46, 44, 57, 55, 67, 70, 73, 80, 85, 90, 103, 93, 113, 104, 124, 124, 126, 133, 137, 143, 160, 143, 170, 153, 180, 177, 179, 187, 190, 196, 216, 192, 227, 203, 237, 230, 231, 240, 243, 250, 273, 241] := by
  rw [show a = b from funext a_eq_b]
  decide +kernel

/-- The steps satisfy the recurrence, on one period of the residues. -/
theorem drec_base : ∀ t : ℕ, t < 30 → (dv (t + 14) : ℤ) = -(dv (t + 13) : ℤ) - (dv (t + 11) : ℤ) - (dv (t + 10) : ℤ) + 2 * (dv (t + 9) : ℤ) + 2 * (dv (t + 8) : ℤ) + 2 * (dv (t + 6) : ℤ) + 2 * (dv (t + 5) : ℤ) - (dv (t + 4) : ℤ) - (dv (t + 3) : ℤ) - (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  decide +kernel

theorem drec (t : ℕ) : (dv (t + 14) : ℤ) = -(dv (t + 13) : ℤ) - (dv (t + 11) : ℤ) - (dv (t + 10) : ℤ) + 2 * (dv (t + 9) : ℤ) + 2 * (dv (t + 8) : ℤ) + 2 * (dv (t + 6) : ℤ) + 2 * (dv (t + 5) : ℤ) - (dv (t + 4) : ℤ) - (dv (t + 3) : ℤ) - (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 30 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 3, e 4, e 5, e 6, e 8, e 9, e 10, e 11, e 13, e 14]
  exact drec_base (t % 30) (Nat.mod_lt _ (by norm_num))

/-- The recurrence on its first 30 terms, by the kernel. -/
theorem recur_base : ∀ q : ℕ, q < 30 → (b (q + 15) : ℤ) = -b (q + 14) - b (q + 12) - b (q + 11) + 2 * b (q + 10) + 2 * b (q + 9) + 2 * b (q + 7) + 2 * b (q + 6) - b (q + 5) - b (q + 4) - b (q + 2) - b (q + 1) := by
  decide +kernel

theorem b_recur (q : ℕ) : (b (q + 15) : ℤ) = -b (q + 14) - b (q + 12) - b (q + 11) + 2 * b (q + 10) + 2 * b (q + 9) + 2 * b (q + 7) + 2 * b (q + 6) - b (q + 5) - b (q + 4) - b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 30 ∨ 30 ≤ q by omega) with hq | hq
    · exact recur_base q hq
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 30 := ⟨q - 30, by omega⟩
      have h0 : (b (v + 15) : ℤ) = -b (v + 14) - b (v + 12) - b (v + 11) + 2 * b (v + 10) + 2 * b (v + 9) + 2 * b (v + 7) + 2 * b (v + 6) - b (v + 5) - b (v + 4) - b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have s1 : b (v + 31) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (by omega)
        rw [show v + 1 + 30 = v + 31 by omega,
          show v + 1 - 1 = v + 0 by omega] at h
        exact h
      have s2 : b (v + 32) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (by omega)
        rw [show v + 2 + 30 = v + 32 by omega,
          show v + 2 - 1 = v + 1 by omega] at h
        exact h
      have s4 : b (v + 34) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (by omega)
        rw [show v + 4 + 30 = v + 34 by omega,
          show v + 4 - 1 = v + 3 by omega] at h
        exact h
      have s5 : b (v + 35) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (by omega)
        rw [show v + 5 + 30 = v + 35 by omega,
          show v + 5 - 1 = v + 4 by omega] at h
        exact h
      have s6 : b (v + 36) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (by omega)
        rw [show v + 6 + 30 = v + 36 by omega,
          show v + 6 - 1 = v + 5 by omega] at h
        exact h
      have s7 : b (v + 37) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (by omega)
        rw [show v + 7 + 30 = v + 37 by omega,
          show v + 7 - 1 = v + 6 by omega] at h
        exact h
      have s9 : b (v + 39) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (by omega)
        rw [show v + 9 + 30 = v + 39 by omega,
          show v + 9 - 1 = v + 8 by omega] at h
        exact h
      have s10 : b (v + 40) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (by omega)
        rw [show v + 10 + 30 = v + 40 by omega,
          show v + 10 - 1 = v + 9 by omega] at h
        exact h
      have s11 : b (v + 41) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (by omega)
        rw [show v + 11 + 30 = v + 41 by omega,
          show v + 11 - 1 = v + 10 by omega] at h
        exact h
      have s12 : b (v + 42) = b (v + 12) + dv (v + 11) := by
        have h := b_step (v + 12) (by omega)
        rw [show v + 12 + 30 = v + 42 by omega,
          show v + 12 - 1 = v + 11 by omega] at h
        exact h
      have s14 : b (v + 44) = b (v + 14) + dv (v + 13) := by
        have h := b_step (v + 14) (by omega)
        rw [show v + 14 + 30 = v + 44 by omega,
          show v + 14 - 1 = v + 13 by omega] at h
        exact h
      have s15 : b (v + 45) = b (v + 15) + dv (v + 14) := by
        have h := b_step (v + 15) (by omega)
        rw [show v + 15 + 30 = v + 45 by omega,
          show v + 15 - 1 = v + 14 by omega] at h
        exact h
      have hd := drec v
      show (b (v + 45) : ℤ) = -b (v + 44) - b (v + 42) - b (v + 41) + 2 * b (v + 40) + 2 * b (v + 39) + 2 * b (v + 37) + 2 * b (v + 36) - b (v + 35) - b (v + 34) - b (v + 32) - b (v + 31)
      omega

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 14 < n → (a n : ℤ) = -a (n - 1) - a (n - 3) - a (n - 4) + 2 * a (n - 5) + 2 * a (n - 6) + 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) - a (n - 11) - a (n - 13) - a (n - 14) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 15 := ⟨n - 15, by omega⟩
  rw [show q + 15 - 1 = q + 14 by omega, show q + 15 - 3 = q + 12 by omega, show q + 15 - 4 = q + 11 by omega, show q + 15 - 5 = q + 10 by omega, show q + 15 - 6 = q + 9 by omega, show q + 15 - 8 = q + 7 by omega, show q + 15 - 9 = q + 6 by omega, show q + 15 - 10 = q + 5 by omega, show q + 15 - 11 = q + 4 by omega, show q + 15 - 13 = q + 2 by omega, show q + 15 - 14 = q + 1 by omega]
  simp only [a_eq_b]
  exact b_recur q

/-- The coefficients of the g.f. below 15, by the kernel. -/
theorem gf_base : ∀ n : ℕ, n < 15 → 1 * (b n : ℤ) + 1 * (if 1 ≤ n then (b (n - 1) : ℤ) else 0) + 1 * (if 3 ≤ n then (b (n - 3) : ℤ) else 0) + 1 * (if 4 ≤ n then (b (n - 4) : ℤ) else 0) - 2 * (if 5 ≤ n then (b (n - 5) : ℤ) else 0) - 2 * (if 6 ≤ n then (b (n - 6) : ℤ) else 0) - 2 * (if 8 ≤ n then (b (n - 8) : ℤ) else 0) - 2 * (if 9 ≤ n then (b (n - 9) : ℤ) else 0) + 1 * (if 10 ≤ n then (b (n - 10) : ℤ) else 0) + 1 * (if 11 ≤ n then (b (n - 11) : ℤ) else 0) + 1 * (if 13 ≤ n then (b (n - 13) : ℤ) else 0) + 1 * (if 14 ≤ n then (b (n - 14) : ℤ) else 0) = (if n = 0 then (1 : ℤ) else 0) + (if n = 1 then (1 : ℤ) else 0) * 6 + (if n = 2 then (1 : ℤ) else 0) * 15 + (if n = 3 then (1 : ℤ) else 0) * 28 + (if n = 4 then (1 : ℤ) else 0) * 44 + (if n = 5 then (1 : ℤ) else 0) * 61 + (if n = 6 then (1 : ℤ) else 0) * 74 + (if n = 7 then (1 : ℤ) else 0) * 76 + (if n = 8 then (1 : ℤ) else 0) * 74 + (if n = 9 then (1 : ℤ) else 0) * 61 + (if n = 10 then (1 : ℤ) else 0) * 44 + (if n = 11 then (1 : ℤ) else 0) * 28 + (if n = 12 then (1 : ℤ) else 0) * 15 + (if n = 13 then (1 : ℤ) else 0) * 6 + (if n = 14 then (1 : ℤ) else 0) * 1 := by
  decide +kernel

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X + 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      X ^ 14 + 6 * X ^ 13 + 15 * X ^ 12 + 28 * X ^ 11 + 44 * X ^ 10 + 61 * X ^ 9 + 74 * X ^ 8 + 76 * X ^ 7 + 74 * X ^ 6 + 61 * X ^ 5 + 44 * X ^ 4 + 28 * X ^ 3 + 15 * X ^ 2 + 6 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have e1 : A * ((X - 1) ^ 2 * (X + 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) = C 1 * A + C 1 * (A * X ^ 1) + C 1 * (A * X ^ 3) + C 1 * (A * X ^ 4) - C 2 * (A * X ^ 5) - C 2 * (A * X ^ 6) - C 2 * (A * X ^ 8) - C 2 * (A * X ^ 9) + C 1 * (A * X ^ 10) + C 1 * (A * X ^ 11) + C 1 * (A * X ^ 13) + C 1 * (A * X ^ 14) := by
    simp only [map_ofNat, map_one]
    ring
  have e2 : (X ^ 14 + 6 * X ^ 13 + 15 * X ^ 12 + 28 * X ^ 11 + 44 * X ^ 10 + 61 * X ^ 9 + 74 * X ^ 8 + 76 * X ^ 7 + 74 * X ^ 6 + 61 * X ^ 5 + 44 * X ^ 4 + 28 * X ^ 3 + 15 * X ^ 2 + 6 * X + 1 : ℚ⟦X⟧) = C 1 + X ^ 1 * C 6 + X ^ 2 * C 15 + X ^ 3 * C 28 + X ^ 4 * C 44 + X ^ 5 * C 61 + X ^ 6 * C 74 + X ^ 7 * C 76 + X ^ 8 * C 74 + X ^ 9 * C 61 + X ^ 10 * C 44 + X ^ 11 * C 28 + X ^ 12 * C 15 + X ^ 13 * C 6 + X ^ 14 * C 1 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    coeff_C, hc]
  rcases Nat.lt_or_ge n 15 with hn | hn
  · have h := congrArg (fun z : ℤ => (z : ℚ)) (gf_base n hn)
    push_cast at h
    linarith
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 15 := ⟨n - 15, by omega⟩
    have h : (b (q + 15) : ℤ) = -b (q + 14) - b (q + 12) - b (q + 11) + 2 * b (q + 10) + 2 * b (q + 9) + 2 * b (q + 7) + 2 * b (q + 6) - b (q + 5) - b (q + 4) - b (q + 2) - b (q + 1) := b_recur (q + 0)
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    simp only [show q + 15 - 1 = q + 14 by omega, show q + 15 - 3 = q + 12 by omega, show q + 15 - 4 = q + 11 by omega, show q + 15 - 5 = q + 10 by omega, show q + 15 - 6 = q + 9 by omega, show q + 15 - 8 = q + 7 by omega, show q + 15 - 9 = q + 6 by omega, show q + 15 - 10 = q + 5 by omega, show q + 15 - 11 = q + 4 by omega, show q + 15 - 13 = q + 2 by omega, show q + 15 - 14 = q + 1 by omega, show 1 ≤ q + 15 by omega, show 3 ≤ q + 15 by omega, show 4 ≤ q + 15 by omega, show 5 ≤ q + 15 by omega, show 6 ≤ q + 15 by omega, show 8 ≤ q + 15 by omega, show 9 ≤ q + 15 by omega, show 10 ≤ q + 15 by omega, show 11 ≤ q + 15 by omega, show 13 ≤ q + 15 by omega, show 14 ≤ q + 15 by omega, show ¬ q + 15 = 0 by omega, show ¬ q + 15 = 1 by omega, show ¬ q + 15 = 2 by omega, show ¬ q + 15 = 3 by omega, show ¬ q + 15 = 4 by omega, show ¬ q + 15 = 5 by omega, show ¬ q + 15 = 6 by omega, show ¬ q + 15 = 7 by omega, show ¬ q + 15 = 8 by omega, show ¬ q + 15 = 9 by omega, show ¬ q + 15 = 10 by omega, show ¬ q + 15 = 11 by omega, show ¬ q + 15 = 12 by omega, show ¬ q + 15 = 13 by omega, show ¬ q + 15 = 14 by omega, if_true, if_false]
    linear_combination (1) * hq

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X + 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      X ^ 14 + 6 * X ^ 13 + 15 * X ^ 12 + 28 * X ^ 11 + 44 * X ^ 10 + 61 * X ^ 9 + 74 * X ^ 8 + 76 * X ^ 7 + 74 * X ^ 6 + 61 * X ^ 5 + 44 * X ^ 4 + 28 * X ^ 3 + 15 * X ^ 2 + 6 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 14 < n → (a n : ℤ) = -a (n - 1) - a (n - 3) - a (n - 4) + 2 * a (n - 5) + 2 * a (n - 6) + 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) - a (n - 11) - a (n - 13) - a (n - 14) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 10, 17, 21, 27, 32, 36, 46, 44, 57, 55, 67, 70, 73, 80, 85, 90, 103, 93, 113, 104, 124, 124, 126, 133, 137, 143, 160, 143, 170, 153, 180, 177, 179, 187, 190, 196, 216, 192, 227, 203, 237, 230, 231, 240, 243, 250, 273, 241] := Count.controls

/-- The step a(n + 30) = a(n) + Count.dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 30) = a n + Count.dv (n - 1) := Count.a_step n hn

/-- The closed form per residue of n mod 30, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (30 * k + 1) = 148 * k + 5 ∧
    a (30 * k + 2) = 170 * k + 10 ∧
    a (30 * k + 3) = 160 * k + 17 ∧
    a (30 * k + 4) = 158 * k + 21 ∧
    a (30 * k + 5) = 160 * k + 27 ∧
    a (30 * k + 6) = 158 * k + 32 ∧
    a (30 * k + 7) = 160 * k + 36 ∧
    a (30 * k + 8) = 170 * k + 46 ∧
    a (30 * k + 9) = 148 * k + 44 ∧
    a (30 * k + 10) = 170 * k + 57 ∧
    a (30 * k + 11) = 148 * k + 55 ∧
    a (30 * k + 12) = 170 * k + 67 ∧
    a (30 * k + 13) = 160 * k + 70 ∧
    a (30 * k + 14) = 158 * k + 73 ∧
    a (30 * k + 15) = 160 * k + 80 ∧
    a (30 * k + 16) = 158 * k + 85 ∧
    a (30 * k + 17) = 160 * k + 90 ∧
    a (30 * k + 18) = 170 * k + 103 ∧
    a (30 * k + 19) = 148 * k + 93 ∧
    a (30 * k + 20) = 170 * k + 113 ∧
    a (30 * k + 21) = 148 * k + 104 ∧
    a (30 * k + 22) = 170 * k + 124 ∧
    a (30 * k + 23) = 160 * k + 124 ∧
    a (30 * k + 24) = 158 * k + 126 ∧
    a (30 * k + 25) = 160 * k + 133 ∧
    a (30 * k + 26) = 158 * k + 137 ∧
    a (30 * k + 27) = 160 * k + 143 ∧
    a (30 * k + 28) = 170 * k + 160 ∧
    a (30 * k + 29) = 148 * k + 143 ∧
    a (30 * k + 30) = 170 * k + 170 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X + 1) ^ 2 * (X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      X ^ 14 + 6 * X ^ 13 + 15 * X ^ 12 + 28 * X ^ 11 + 44 * X ^ 10 + 61 * X ^ 9 + 74 * X ^ 8 + 76 * X ^ 7 + 74 * X ^ 6 + 61 * X ^ 5 + 44 * X ^ 4 + 28 * X ^ 3 + 15 * X ^ 2 + 6 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = -a (n - 1) - a (n - 3) - a (n - 4) + 2 * a (n - 5) + 2 * a (n - 6) + 2 * a (n - 8) + 2 * a (n - 9) - a (n - 10) - a (n - 11) - a (n - 13) - a (n - 14) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a313965

theorem OMA.solution : type_of% @OMA.S_oeis_a313965.main :=
  OMA.S_oeis_a313965.conjecture
