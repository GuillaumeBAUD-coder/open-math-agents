import OMAStatements.S_oeis_a311533

namespace OMA.S_oeis_a311533






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 12

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 581520890555
  | 1 => 952603194471
  | 2 => 883884835926
  | 3 => 513105566105
  | 4 => 586102114730
  | 5 => 879303607655
  | 6 => 586406201480
  | 7 => 659402750105
  | 8 => 806004020855
  | 9 => 874722383480
  | 10 => 659706836855
  | 11 => 732703385480
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 10) : ℤ := tget 444691290230 4 8 i.val

def Bc (i : Fin 10) : ℤ := tget 1030771314980 4 8 i.val

def Cc (s : Fin 12) (i : Fin 10) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 444691290230 4 i

def BcN (i : ℕ) : ℕ := tgetN 1030771314980 4 i

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
pot k2 ≤ pot i, 18 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 267820612648692256457106339714296828754943996416307972769396979000029667879916427627488448900084125985620538386064584665026105024639886341162970409227030426393770001586197929274858096196402226641621475395353548786321484458969647837365862330904760929981040296201533366508711229940570880629392821274052101716284139618024074214565760188884726665739875077248662694418884207406600533897667267248686869875017989664392406204658400003427312415284169043280016937488896661543565374033606778519373165695649196362935751909867945790887771619396175805007403638460116558306767740323377221365982151670493065094624487398076769774175710700735068620528642992407546023782779683612276159442393873059958003825865096517125204106473600021452017908547744800390521420467772314889700367726106258667118602019375651004052785584158776604410887486022976692108402781868324762156713567106210180074890139127226466041856 5 ((i * 10 + j) * 6 + f)

def fd (i j : Fin 10) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 0 % 10, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 1 % 10, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 10) : ℤ := fd i j 2

def fm2 (i j : Fin 10) : ℤ := fd i j 3

def fm0 (i j : Fin 10) : ℤ := fd i j 4

def fmj (i j : Fin 10) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 10 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 4603201553788044023048243150031418729641189595612533817344 4 p

def dstv (p : ℕ) : ℕ := tgetN 4181388487474994151924262225297344348597881279222355346209 4 p

def dxv (p : ℕ) : ℕ := tgetN 21539513477290396132191916353 2 p

def dyv (p : ℕ) : ℕ := tgetN 26409387504754779197848049232 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 44346145549359194939558776105933281120999555251670471696977292964953938276986259646106708922899335787926867914330002273241547093082702878821865533442424430243159883838484340900935154351762483784336489431942547344166812824923466710068564375265119633711392066837445400569776379877050876976024153287182090583477798319349237267321191937075274064928179540726767669406474396207152206389993682171127754443497248383798062261327022208392234717602586781705327222974112253872529924312821522147363553977893152475926288886340530694854564063891352159131506315536826913843021247791725277714840 4 (p * 10 + j)

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
      fdN i j 4 * 26)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 10 || j == (i + 9) % 10

def farOK : Bool := (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 12).all fun s => (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 48).all fun p =>
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
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (18 - Cc s i)

/-- Beyond F = 17, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 12) (i j : Fin 10) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 17 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 18 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 17, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 17 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 3942392526586267560749522354203469798744170920706916008405334897295684589865972490767475902433908602968418602354007320727315022032931406033402781287526539944039226699188725026430377587398139164069435753224338106605520371639902007962262338152860815467785737774446270269211343064909992797652679515289806216443949900678443066749197362324911623699917078694432403756452571527954030370979591158142577821540877911553959017670630895456447959296104132346725533763952739257221600450328520487898864218694641908976048389395888119707916452176262384823648397894835876311847236232625884710457442846273331367826893766447226698319611993664060124648778802162767516561951905138476192689023456104990649352199469805538184499492637386947517089829984588313829317308905104002963790162261899079161672452635716203468242373266603229226260534876606752899550439607998235921531781383095384703138668377513572393670215938703097561135587540931420119649397063540467496340952891014067959258602541351831040246960650125896843617589682761578516889270631349962586378616351889916626480310920137335305832887943802288630353794317831491782766771338561109907478763609832616522752065
  | 1 => 3942392527952375489656043790012109979740950479902471243396653969642158679047722161109724592338468642798129119364427725905959932340487180840408356894890907218533571160654797704517142492882645472875067428327431662078094645578975778248069484413007925981079077538060423338257197230612141457682448280148547872032351180133062213251521702705184266155834771568169320961521607254244416981371913551585947025011786904392682571452740683396782434115754977530320751082337599308897727467707523411569220790180344804330580002246118966733688778114722983047112748134309420890848371190503866086338945438686015523207801356222788238440149053160108846274307052418433927230249213262719390576730562429407205279379420602898562987939854378363711059354899377741853139255731477716838993069604465478280910049224980451245774354966600029255128963749526132812719802068203025074613582454026041890363808296405375427671767150962869339576442331173959920848777998858801304644165758677866263920558573769484807787795720876171029131950455572976644519139002769018216118125406935132722512216220838902962768285355131384853623909740765510379212844068693244351474834503356399053972288
  | 2 => 3942392528863114108927058080551203414120435577592087107255588515763607726486132565119093619418844642879340916782759137624432552213609496714602672436467799288487968832409223970592049082211837261428252509415584816196663658667026980051879648136139251803783937324318296242963706057633253211561318998668490115049380271551675785096206473364354778384054864990529688565036484985240874793651024721231085104596513092648229471314386133982581229203779237084591298004974276319992762241929089568014062933183281950239815038300829087110119290510394557722564434507274616400384970312320952466090425840688090413968863107570138639352573031007032507993307092858729899837645403858994782814469635393645508933396873909953141882358660621708041013394081836590616486999470309004154268849446666157463631029771270659881376993185636282368160140236485582084432345504771150819056208081013689871822142607894901211881106183384262082827287671053028442552599734217702179328401145985006441653564435495038227130157268862019745018638114880383766030283178660424396785085329332009109863342047542233133745163153889676653789664459251091782959864975108532897866491522386200326643777
  | 3 => 3942392529318483418562565225820750137195688508969121327025639239457192353810181470575921522739423722362626196321668095375075852187751432822080035942489643762026677076078773626519710047909821279318189394816584049683214225451554399128178916325979427483962524661753738563203400808871990266251623868623283285442116781903954406590949275915182640771790302281701799950603915506505762432446606785540394981862721157897685231166336262063828888331971708941117285356188282108202018118644554179528675957659740269524438025630452296293829382188095491036399860635044552049477948571415998735633787773638821484068010070258354095274810661948227238745797953201679226175911776344681823992743307749612218692310086101016242856321198851646845217355714273156058480914143937585543745122726719756129076172696483038651524930098172633191735107174223956395737678686478445413658960820614286087299066186616235787888155370475881602380395646174917281861872881759372446362054001032903837562798552006904689332308629542475528454364800353607783870772213404896830503925935675638953136255414280142865914081978949786179314083040377685248690805550626095363868412338875885507911745
  | 4 => 3942392530684591347469086661629390306421447303100223986335791410537946235782328186946153543349939889932131254217709443237967173814079537508283227263704501293817315342468726162566386777061316734100722897198646493983352930000362248320745037260865780337265163270293676957028373440661141555743132852625661672932679908363682693708194398801130324567856288345976038051334573156651691182526062871327448999017456314188997554366580200581845140263873229204118672082529106636148471869144098834375820694598318562815373049924812625446299383622305908434146286985362597468241879775324930626997302928796612071738267962930404684229837510321086655324412163594152269772247384765502708405162858549471598657463200891824728784234324401141722146342723016557921795431007571280749806254393031722581137275323711789159952114920700117587497340945618902145829604738222893740709234108840239033866184599936823067097243119050106822107892955520745044812069746858711942880582963980206376548967257023877722102368978198150752720653358438450097163695591466157079620798122663849291570051659160803404867401272536394997441265745573711121144375963345225741026866172978562281253184
  | 5 => 3942392531595329966740100952168483752571953165854292425875892857925115490430510450791198547528562587443008477035499229839519043548302621872354047188313511410561876414972499729227329106682048635996397569230232933822310622805662702686164639059444778261409376529082053146239580617824682702897181557818071828112128077964513722329967697137323980783323826188580276972649526110013440074989193455818718615085933366511752177025014047049880370049541438547870236683435671575199303608462112164529637648962396603740947715031737367608712333418489166025729098469720984155785115580108029384342546983323398122128637558403910131614178020849264533434585265153143807448136630728726889158425862201510316632211042746122644954196574832311108196837892558082189213173719864755140119805343716317239604195926311726616363366814817511947859022294197764628400538935073340336923290227399724225306674757375539689277207893805715469998856363107004480542432571574595469843271848969549570067435235119569462761068085642703642224786288868642021689736215070318064869681041177320770970527480866635455842770065202757066766325778783447751217578362586614760095988652861108532879425
  | 6 => 3942392532050699276375608097438030475647206097236679486156087418656393442198011491875471097202875054430739899768933972247786324541164351959517319902367019594462799438531586319215408124857973382441091024569231765621056206850566784139746639063946947410611405985636633041084423649358780772591854873281325602348764644832469920493216471816020593787676538474385741494485014429221465785600088343482879658841500616390556197390586541005024183984207598410452207515744656616017878505581017435848182928105132984771995419497219076009906868300486843026993250142719750766205397687279595243380862397894887522014519478094051826253787748130222622093344320521645032085017377421726290389327228643179623564740543423156655119006676322694041263973915276592111525560530968842902842880695828297321749679800932530569588923896704391288187196306817263735674005342299052939293241160801836264743320206029705320189688802695065775141973462186164019730815241168614244701484365166097123028101328912577290719995526404904872780843647638260902106309426530972682534240768645615558643478011307961022635413608955514696431619220822163075530371750412445147050605295785115638898753
  | 7 => 3942392532961437895646622387977123921797711959990747925696188866040615437776312140716149930800337711955215167422734309055616297358116632226169114864655532802711426563055886410716479783378683687235658627948807398052565817929861214021468712699014205937818038812916042597895318740601823549442288651129403569206594891900582114619912101249156632992705198305148623718540507024266218260604228408473056077671843095830658312966452906636878448504238576406965227677793770719708080696426187853069479492635234195938330368205847839387609841809411272082981737860853230568298661100219650474967849790527989879155088321209276392006888136937236023041108472824973365018078154661820810312804262081936528782767398937710439628832282506987619866687827573425989536748866842485997206124880232770982310521229004839799198186158383846667469754541633015045834394785804575110775695892518781732611220143720711738394887269489183821596588722987348002665726432051488171905977809328329979397723028290741734845668533742856355256981630343256745668297758139761608459562592628880214726793984258335251812090583010720136662324388632974953341501701837537601927490486886759540993856
  | 8 => 3942392534327545824553143823785764091023470754116497744496197200086623254374719430600273391212130384037711929087610054465038635960598537811369613006338199926100435252946870586907654353556962922274582629913686674904507815948915245368566369634741521305272257107913510546057854939542383745212493592204714725977407828760881474231010235950858205125689240359550498586096689614970929405193986155276025573157842567387895015636294411121340719451165395153845788365542301839293596745274101780326711027838804401710198475995834690674117105915576936680127055679964241162459274031221029150783368300268136066194880616694229745762258355899162786319184893543285575301428508509148043850482565111087836971182098721152572294872400552583113299948744874978249125424747640160002361353586110528965989149033971356376781131824840362260482901985333653932499340009911680219976924150550402192758692900850433583674201392086108430259843565307390029686929738796966334985371863943726854546448088567547402891959085559009038720355773046215618743744091559549489833270768707916292786491726082585568299696014026539968296656802930001468575715450216791444060434206077427108557120
  | 9 => 3942392535238284443824158114324857548944997381935018759717465548742459973503521916833951802868731006032826957320815618395497463821562917077513807909389951677911673392456723441115039113615591661410666215732061271906172304863631549324000742996325761654669321969381695562140197606424068936939583942230739289463492307518259827867436811503690722998486948241237418866677085188747026524660321125667541743584985439228199467198908303097827243591158688491885696616737613723814824013270563789772699760960695807588503750760119842608051308695190967390863800190272665506604876157835865157098780669552130413163538257703068359008621637700885376612195312224750780942465845284068572377846400948530676522134351068598661003904850928032223517720642901500746446959671423684731993728978899618815513572646620837976368015614095772920688458354889371224295306250497922490986316710299749950684716320518240519797855124963252126831010899387607111123230533441142128655038831146054718858468447778063247797069404234164722327353352298144846214905473328235899148522219445465094736492361934553243315847325472367684782821307718455507426502842694162755187055622372200094703681
  | 10 => 3942392535693653753459665259594404260249229548255629664571565126722443491125021818606008883982756003475874027637629612622695907967212816159145384862144833513083185331453593085730159243898143064335890212765129457202053471222360630770872862548028987788138561616619587286368765304112003867913216714672445822806367025454758523023541677089425318007241842002199079160087900236247937568499336703057657103880849705212673533197070526312509665017911715185789928408652202051622908228334999945965328926430674589799583235154796601731382940548443894333333325934428069985623218687471247819224494364427693606972694052351564374070917152121395458157709788698706936731646283316555375476786802013004497842438717435641637306753906576807066172207711015243187475730173572776045393840480304244677974362262739638106250927001838105242031464566325615369494865744225184925433737137736466372441702092605569167134750882864858156991328252855030943267335587845292243397116621913745308430297520814444339689011687979820800636280937676568710155450640423298381485288252576681741031783240114968278155225960015758683783354087481059162771992604664771547125950883033027026690113
  | 11 => 3942392536604392372730679550133497706399735411009698104111666574106665489055573097613355519930792587664343837998303412183051611023242003635176027078304492812268413335144284662187212245868249303388085459820366445408444173136451468693115929188658984291223136564946821074952065391320080671615880270166530727524026679324542706105596795531519244718499908826575377771743053848436772183024874769637348426700557052311472425201687178644727971056376794588425286159712471438977162954898117203544735497027393639844649724492388956796495334646738768246049689255052855442360293686889958288171683453631425101589748002847042439618210364623076016393809796345332704744700022913214263499286135110845934576252275328132737456512270114333668389305874801926749576800026783807714353346395643899715525988279649258607635855554566723816439278556772432953897137005329443424651636511485609172086323467615075959869865143240063107131021894894045951903536735657029659814917880683342761983666953733325109055649722972384103204832898416139486391666428931012698767409298858540495521279051624099178317455187701617622244493325021059679892842761457953716815973057227797237348288
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
    decide (re s i c1 c2 < 48 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 17)
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

theorem point_contra (x y : ℤ) (s : Fin 12) (i : Fin 10) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 17)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 17 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 17 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 12) (i : Fin 10) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 17 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 17
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

theorem far_desc (v : V) (hF : 17 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
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

theorem box_c0 : ∀ s : Fin 12, 0 < 6 * (Cc s 0 - 17) + 4 * (Cc s 9 - 17) + 0 * (Cc s 0 - 17) + 20 * 10 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 12, 0 < 4 * (Cc s 4 - 17) + 6 * (Cc s 5 - 17) + 0 * (Cc s 0 - 17) + 20 * 10 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 12, 0 < 1 * (Cc s 2 - 17) + 0 * (Cc s 0 - 17) + 0 * (Cc s 0 - 17) + 7 * 4 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 12, 0 < 1 * (Cc s 7 - 17) + 0 * (Cc s 0 - 17) + 0 * (Cc s 0 - 17) + 7 * 4 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 12, 0 < 2 * (Cc s 4 - (-1)) + 2 * (Cc s 9 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 17 lies in the cells |x| ≤ 9, |y| ≤ 3 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 12) (hF : F (x, y, s) ≤ 17) :
    -9 ≤ x ∧ x ≤ 9 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 9 0 17 6 4 0 1 0 10 20 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 5 0 17 4 6 0 (-1) 0 10 20 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 0 0 17 1 0 0 0 1 4 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 7 0 0 17 1 0 0 0 (-1) 4 7 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 4 9 0 (-1) 2 2 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 9, b - 3) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 118102079026206979235149555051607588072249863104743857699359829337421656711270050101187693900229081630181316273629631279459842785000836995893185295357534160993770765224485474145140918592872610434523070117668910984894195132031842022193862740102380046409943620320234825360652408799487983806915908503738583787404037238313510785828680565946508990564840589953867974007082362462799456640437845955149567998424411389138367331855007631672314335895470115908033551807636024928292827364586970360969732261937931070574002763605454880046629495326711789997715223286800402959688216351239704542958714591712300798318797066760324068478722695895691846066151751612438072576710228992106766169105675509428796685931896196719822625343483027049409244736544500561329429446559144912944624305692993104532126018872133643265826377101146931041161119597099562585425515818119816095833949889229039752357067426742051889416569104927998394487932941640759798712336189597111652819730779956217518177078365711024280478600635671923276443507382398458310247786521308205431535197884182430104997051439801825011865697771472407957398710967534252346279301999407378668252662734119370681406332785747357238080608784475387589169665756373043822346171240120386572305191107301258968855741010738041930479445941554750770715753408745107441343324349304675536554608708648194244173067130513145749641331268702384688555772203179806710613192808033110050217567508982922672810469791723273321529006558993727890933284145322505206305358738772488838515855548269891925798633390591984098287354578399710778467660778333471346123616592743794909837116471409179974835168021742043767589775977769058215580405846218406092303132389905442746514027912541927209617852497735084326769551023681803986325719020310955721028271447966755504590494897167113866215070203422751551841560882396820732468652270857779652081065733237120579631588555442160324277861890914239602812259086054098040278045484007509234487604648167521787372333354497232085998880551483246148959385772612713149775309894232177337777692315111010578231401973741317579937109119001183567227773366583277503708807628511554441415918931070399521235050197716708025238293934958496314173737630983350945457158284467191123649077972289523983691960074265665890248332475677710670168398241828011144314725747359785203165098603280703907863852397679183224853764387537108665561132849785914041915285390774170989265734232719318173253891791868563488239349409630175336497684692389295993563416065028138041681860802818756392931417372575931048784090052591896863874111020615253804714841001024268282488039173256998699175463050741004006807421272085166914167141480121846658982637829580465753141410490809283874108980604124417025503586968659678005518905444627657813440614736351779388516680177728440659187481823933043511163987761189053188116170961963406011387950667101238198272 >>> (6 * ((a * 7 + b) * 12 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 9, b - 3) and class s, potential i plus
33 + 2 a + 7 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 10) : ℕ :=
  tgetN 4886639120 4 i.val * a + tgetN 957470539795 4 i.val * b + tgetN 2015060992433806687267872449282179741286140257874715507300543887420193517427341356824598594047274588900085175212970298593624568133403861873827081211763780109846229293075927974408992705786901094158265859661891279063445294465423424934536171239526301048770 7 (s * 10 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)) (fnt a b s 8)) (fnt a b s 9)

theorem fnt_tab : ∀ s : Fin 12, ∀ i : Fin 10, (tgetN 4886639120 4 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 957470539795 4 i.val : ℤ) = Bc i + 7 ∧
    (tgetN 2015060992433806687267872449282179741286140257874715507300543887420193517427341356824598594047274588900085175212970298593624568133403861873827081211763780109846229293075927974408992705786901094158265859661891279063445294465423424934536171239526301048770 7 (s.val * 10 + i.val) : ℤ) = Cc s i - Ac i * 9 - Bc i * 3 + 33 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 12) (i : Fin 10) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 9, (b : ℤ) - 3, s) i + (33 + 2 * a + 7 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 12) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 9, (b : ℤ) - 3, s) + (33 + 2 * a + 7 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 17, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 7) 1 = FN + 2 dx' + 7 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 19).all fun a => (List.range 7).all fun b => (List.range 12).all fun s =>
    Nat.blt (50 + 2 * a + 7 * b) (FN a b s) || (a == 9 && b == 3 && s == 6) ||
      (Nat.blt (hint a b s) 48 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 9 ==
          FN a b s + 2 * dxv (hint a b s) + 7 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 17) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 9).toNat (by omega) (y + 3).toNat (by omega) s.val s.isLt
  have ex : (((x + 9).toNat : ℕ) : ℤ) - 9 = x := by omega
  have ey : (((y + 3).toNat : ℕ) : ℤ) - 3 = y := by omega
  generalize (x + 9).toNat = a at h' ex
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
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 9 = x + dx := by omega
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 3 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 17
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
from below, and for n ≥ 10 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 56 moves every quotient by an integer (`inner_shift`,
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
def AW (i : ℕ) : ℕ := tgetN 444691290230 4 i

def BW (i : ℕ) : ℕ := tgetN 1030771314980 4 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem A_W (i : Fin 10) : Ac i = (AW i.val : ℤ) - 8 := rfl

theorem B_W (i : Fin 10) : Bc i = (BW i.val : ℤ) - 8 := rfl

theorem C_W (s : Fin 12) (i : Fin 10) : Cc s i = (CW s.val i.val : ℤ) - 8 := rfl

def gcV (k : ℕ) : ℕ := ctabN 300229578 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 10) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 27280 2 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 1

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 749699597845 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 7

def Bp (i : Fin 10) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 27280 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 10) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 365893 2 k

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
(pot_i ≤ pot_j) plus cf0 times (10 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 1449467552926698133954594916883337342142424164882893826162219980313786216540035434084270959873243499569251840562275919639790700583174299919192195072 5 k

def cf2V (k : ℕ) : ℕ := ctabN 3219693847976194559265544259936952902107512013490736781753863858701555992976944425795268820260352838602500597146952282205881307437713557734045696 5 k

def cf3V (k : ℕ) : ℕ := ctabN 5287440907370579001086007939576043189148774167215714396320816180497136608621325477321031306280070853881595439434917888 4 k

def cf0V (k : ℕ) : ℕ := ctabN 4554602394991041871279424909715415614214462964416046057978971919584178556191385672028736 3 k

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
    cf0 i j * (10 - Cc s i)

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
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 18))

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

/-- From n = 10 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 12) (i : Fin 10) (n u : ℤ) (hn : 10 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 10 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
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

def box_pairsK : PLift (2 * Ac 4 + 3 * Ac 5 = 10 ∧ 2 * Bc 4 + 3 * Bc 5 = 0 ∧
    3 * Ac 0 + 2 * Ac 9 = (-10) ∧ 3 * Bc 0 + 2 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 7 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-7)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 2 * Ac 4 + 3 * Ac 5 = 10 ∧ 2 * Bc 4 + 3 * Bc 5 = 0 ∧
    3 * Ac 0 + 2 * Ac 9 = (-10) ∧ 3 * Bc 0 + 2 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 7 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-7) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 12) :
    10 * x ≤ 5 * F (x, y, s) + 25 ∧
    10 * (-x) ≤ 5 * F (x, y, s) + 25 ∧
    7 * y ≤ 1 * F (x, y, s) + 5 ∧
    7 * (-y) ≤ 1 * F (x, y, s) + 5 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 2 * pot (x, y, s) 4 + 3 * pot (x, y, s) 5 =
      10 * x + 2 * Cc s 4 + 3 * Cc s 5 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 4
  have r0 := le_F (x, y, s) 5
  have k0 := Cbound s 4
  have l0 := Cbound s 5
  have e1 : 3 * pot (x, y, s) 0 + 2 * pot (x, y, s) 9 =
      10 * (-x) + 3 * Cc s 0 + 2 * Cc s 9 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 9
  have k1 := Cbound s 0
  have l1 := Cbound s 9
  have e2 : 1 * pot (x, y, s) 7 + 0 * pot (x, y, s) 7 =
      7 * y + 1 * Cc s 7 + 0 * Cc s 7 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 7
  have r2 := le_F (x, y, s) 7
  have k2 := Cbound s 7
  have l2 := Cbound s 7
  have e3 : 1 * pot (x, y, s) 2 + 0 * pot (x, y, s) 2 =
      7 * (-y) + 1 * Cc s 2 + 0 * Cc s 2 := by
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

theorem piece_eq (s : Fin 12) (i : Fin 10) (n : ℤ) (hn : 10 ≤ n) :
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

theorem card_piece (s : Fin 12) (i : Fin 10) (n : ℤ) (hn : 10 ≤ n) :
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

/-! Shifting n by 56 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 520204820173327900 6 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 1030532038407 4 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 7

def mh (i : Fin 10) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 483182184446 4 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 7

def mk (i : Fin 10) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 10, (56 : ℤ) = gc i * Lq i ∧ 56 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 56 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 10, (56 : ℤ) = gc i * Lq i ∧ 56 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 56 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 12) (i : Fin 10) (n : ℤ) :
    inner s i (n + 56) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 56 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 56 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 56) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 56) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 56) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
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

theorem S_shift (n : ℤ) : S (n + 56) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 56 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 56 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 10 + r with r < 56: the level is QQ - 0 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 924 1 k

def uhMV (k : ℕ) : ℕ := ctabN 66 1 k

def ukPV (k : ℕ) : ℕ := ctabN 99 1 k

def ukMV (k : ℕ) : ℕ := ctabN 264 1 k

def dhV (k : ℕ) : ℕ := ctabN 305356108170 4 k

def dkV (k : ℕ) : ℕ := ctabN 721945264500 4 k

def mhkV (k : ℕ) : ℕ := ctabN 487503370263 4 k

def uh (i : Fin 10) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 10) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 10) : ℤ := dhV i.val

def dk (i : Fin 10) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 9174554682171736055512759492150085791604785131170935788865031462818668837257888163828822202479439421407297 3 (Nat.add i (Nat.mul 10 s))

def QQ (s i : ℕ) : ℕ := ctabN 879246409275403041369964388173938135448686655436468617114313096876730114395544034039025322431547315136967169687758103712131411919709332360761715 4 (Nat.add i (Nat.mul 10 s))

def AH (s i : ℕ) : ℕ := ctabN 683886835566617328767674073140164657504865098651988997085690329574222296979913983781639013097675851343504652844073473543014436049288333474623491 4 (Nat.add i (Nat.mul 10 s))

def AK (s i : ℕ) : ℕ := ctabN 195554413299919636690038498111798199445712053878870404902969424446354186645129200049018163279149259801119468270310078465025352730717721888752003 4 (Nat.add i (Nat.mul 10 s))

def WH (s i : ℕ) : ℕ := ctabN 428708062244042424327007591721707829483487519936251962058994926892542698512159216324552795913327441788431111241407539314601371972024656724352 4 (Nat.add i (Nat.mul 10 s))

def WK (s i : ℕ) : ℕ := ctabN 98317078575131282137706599098765117183113795242116864376998755714292731386943714291162737841875611797919832728391182977861710575935670800384000 4 (Nat.add i (Nat.mul 10 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 12 fun s => allR 10 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq 18 (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 12) (i : Fin 10) :
    PP s.val i.val < gcV i.val ∧
    (10 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 0) + PP s.val i.val ∧
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

/-- Piece (s, i) at n = 10 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 10 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 12) (i : Fin 10) (r : ℕ) :
    ((10 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (10 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 0) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 12) (i : Fin 10) (r : ℕ) (hr : r < 56) :
    inner s i ((10 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (56 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 56 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((10 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r := by
      rw [lev, show (10 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((10 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((10 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 706885940783844382933939573449202347247891963338101547964709751039374670569628059336060687182251339895302899766864585942549402703950072 8 k

def tblV (k : ℕ) : ℕ := ctabN 706841229273739968330412600018758104236048121677811117936018728626015142461354092527746680028770595203037890280749291213540905750104068 8 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 56. -/
def dv (t : ℕ) : ℕ := dtabV (t % 56)

/-- The sequence in closed form: b(n + 56) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 56) + tblV ((n - 1) % 56)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 56) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 56 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 56 - 1 = n - 1 + 56 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 56)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 56) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 56 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 56 - 1 = n - 1 + 56 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 56)]
  ring

/-- b on the residue class of 1 + j mod 56. -/
theorem b_res (k j : ℕ) (hj : j < 56) : b (56 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (56 * k + (1 + j) < 1) by omega),
    show 56 * k + (1 + j) - 1 = j + 56 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 56), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 10 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 56 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 12 fun s => allR 10 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 12 fun s => sumR 10 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 10 r)) &&
    Nat.beq (sumR 12 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 1 (dv (Nat.add 9 r)))

/-! The window n = 10, ..., 65, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 12 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 12 12 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 24 12 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK3 : PLift (allI 36 12 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK4 : PLift (allI 48 8 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 56) :
    (∀ s, s < 12 → ∀ i, i < 10 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 12 fun s => sumR 10 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (10 + r) ∧
    (sumR 12 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0) = 1 * dv (9 + r) := by
  have h : periodR r = true := by
    rcases (show r < 12 ∨ (12 ≤ r ∧ r < 24) ∨ (24 ≤ r ∧ r < 36) ∨ (36 ≤ r ∧ r < 48) ∨ 48 ≤ r by omega) with h | h | h | h | h
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

theorem innerZ_eq (s i r : ℕ) (hs : s < 12) (hi : i < 10) (hr : r < 56) :
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

theorem S_window (r : ℕ) (hr : r < 56) : S ((10 : ℤ) + r) = b (10 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 56) : Gs ((10 : ℤ) + r) = ((1 * dv (9 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 10 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 12) (i : Fin 10) (n : ℤ) (hn : 10 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 10 + t := ⟨(n - 10).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 56
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 56) (by omega) (by omega)
      have e : (10 : ℤ) + t = (10 + (t - 56 : ℕ)) + 56 := by
        push_cast [Nat.cast_sub (by omega : 56 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 10 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 56 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 10 ≤ n) : (1 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 10) % 56 < 56 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((10 : ℤ) + (((n - 10) % 56 : ℕ) : ℤ)) + 56 * (((n - 10) / 56 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (9 + (n - 10) % 56) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 10 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 66
    · obtain ⟨r, rfl⟩ : ∃ r, n = 10 + r := ⟨n - 10, by omega⟩
      push_cast
      exact S_window r (by omega)
    · have h1 := ih (n - 56) (by omega) (by omega)
      have h2 := S_shift ((n - 56 : ℕ) : ℤ)
      have h3 := b_shift (n - 56) (by omega)
      have h4 := grow (n - 56) (by omega)
      rw [show n - 56 + 56 = n by omega] at h3
      rw [show ((n - 56 : ℕ) : ℤ) + 56 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 9 lie in the box -7 ≤ x ≤ 7, -2 ≤ y ≤ 2 (`small_box`). In natural-number
coordinates a = x + 7, b = y + 2 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 12) (h : F (x, y, s) ≤ 9) :
    -7 ≤ x ∧ x ≤ 7 ∧ -2 ≤ y ∧ y ≤ 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 7, (b : ℤ) - 2, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 72) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 7) (Nat.mul (BW i) 2)) 8) (Nat.add (Nat.mul 8 a) (Nat.mul 8 b))

theorem pot_box (a b : ℕ) (s : Fin 12) (i : Fin 10) :
    pot ((a : ℤ) - 7, (b : ℤ) - 2, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 10 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 12) : F ((a : ℤ) - 7, (b : ℤ) - 2, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 7, (b : ℤ) - 2, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 7, (b : ℤ) - 2, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 10 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 10 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 7, (b : ℤ) - 2, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 7, (b : ℤ) - 2, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 7, (b : ℤ) - 2, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 15 fun a => sumR 5 fun b => sumR 12 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 0 .. 9, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 0 10 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 10) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 12) : V := ((q.1 : ℤ) - 7, (q.2.1 : ℤ) - 2, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 9) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 15 ×ˢ (Finset.range 5 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 12 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 7).toNat, (y + 2).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 7).toNat (y + 2).toNat s
        rw [show (((x + 7).toNat : ℕ) : ℤ) - 7 = x by omega,
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 12]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 10 are counted in the
box, those from 10 on are S(n), and both agree with the closed form b (`a_eq_b`). The step from n to
n + 56, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 10 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 10 ∨ 10 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_eq n (by omega) h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 56) = a(n) + dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 56) = a n + dv (n - 1) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 248 ∧ tblV 0 = 4 ∧ dv 1 = 240 ∧ tblV 1 = 8 ∧ dv 2 = 240 ∧ tblV 2 = 12 ∧ dv 3 = 240 ∧ tblV 3 = 17 ∧ dv 4 = 240 ∧ tblV 4 = 22 ∧ dv 5 = 248 ∧ tblV 5 = 27 ∧ dv 6 = 248 ∧ tblV 6 = 32 ∧ dv 7 = 248 ∧ tblV 7 = 36) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 240 ∧ tblV 8 = 38 ∧ dv 9 = 240 ∧ tblV 9 = 41 ∧ dv 10 = 240 ∧ tblV 10 = 46 ∧ dv 11 = 240 ∧ tblV 11 = 52 ∧ dv 12 = 248 ∧ tblV 12 = 58 ∧ dv 13 = 248 ∧ tblV 13 = 63 ∧ dv 14 = 248 ∧ tblV 14 = 68 ∧ dv 15 = 240 ∧ tblV 15 = 69) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 240 ∧ tblV 16 = 71 ∧ dv 17 = 240 ∧ tblV 17 = 75 ∧ dv 18 = 240 ∧ tblV 18 = 81 ∧ dv 19 = 248 ∧ tblV 19 = 89 ∧ dv 20 = 248 ∧ tblV 20 = 94 ∧ dv 21 = 248 ∧ tblV 21 = 99 ∧ dv 22 = 240 ∧ tblV 22 = 100 ∧ dv 23 = 240 ∧ tblV 23 = 102) :=
  ⟨by decide +kernel⟩

def closedK3 : PLift (dv 24 = 240 ∧ tblV 24 = 105 ∧ dv 25 = 240 ∧ tblV 25 = 110 ∧ dv 26 = 248 ∧ tblV 26 = 119 ∧ dv 27 = 248 ∧ tblV 27 = 125 ∧ dv 28 = 248 ∧ tblV 28 = 130 ∧ dv 29 = 240 ∧ tblV 29 = 130 ∧ dv 30 = 240 ∧ tblV 30 = 133 ∧ dv 31 = 240 ∧ tblV 31 = 136) :=
  ⟨by decide +kernel⟩

def closedK4 : PLift (dv 32 = 240 ∧ tblV 32 = 140 ∧ dv 33 = 248 ∧ tblV 33 = 149 ∧ dv 34 = 248 ∧ tblV 34 = 155 ∧ dv 35 = 248 ∧ tblV 35 = 161 ∧ dv 36 = 240 ∧ tblV 36 = 160 ∧ dv 37 = 240 ∧ tblV 37 = 163 ∧ dv 38 = 240 ∧ tblV 38 = 167 ∧ dv 39 = 240 ∧ tblV 39 = 171) :=
  ⟨by decide +kernel⟩

def closedK5 : PLift (dv 40 = 248 ∧ tblV 40 = 180 ∧ dv 41 = 248 ∧ tblV 41 = 185 ∧ dv 42 = 248 ∧ tblV 42 = 191 ∧ dv 43 = 240 ∧ tblV 43 = 190 ∧ dv 44 = 240 ∧ tblV 44 = 193 ∧ dv 45 = 240 ∧ tblV 45 = 197 ∧ dv 46 = 240 ∧ tblV 46 = 202 ∧ dv 47 = 248 ∧ tblV 47 = 212) :=
  ⟨by decide +kernel⟩

def closedK6 : PLift (dv 48 = 248 ∧ tblV 48 = 216 ∧ dv 49 = 248 ∧ tblV 49 = 221 ∧ dv 50 = 240 ∧ tblV 50 = 219 ∧ dv 51 = 240 ∧ tblV 51 = 223 ∧ dv 52 = 240 ∧ tblV 52 = 227 ∧ dv 53 = 240 ∧ tblV 53 = 232 ∧ dv 54 = 248 ∧ tblV 54 = 244 ∧ dv 55 = 248 ∧ tblV 55 = 248) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (56 * k + 1) = 248 * k + 4 ∧
    a (56 * k + 2) = 240 * k + 8 ∧
    a (56 * k + 3) = 240 * k + 12 ∧
    a (56 * k + 4) = 240 * k + 17 ∧
    a (56 * k + 5) = 240 * k + 22 ∧
    a (56 * k + 6) = 248 * k + 27 ∧
    a (56 * k + 7) = 248 * k + 32 ∧
    a (56 * k + 8) = 248 * k + 36 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 56 * k + 1 = 56 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 56 * k + 2 = 56 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 56 * k + 3 = 56 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 56 * k + 4 = 56 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 56 * k + 5 = 56 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 56 * k + 6 = 56 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 56 * k + 7 = 56 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 56 * k + 8 = 56 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (56 * k + 9) = 240 * k + 38 ∧
    a (56 * k + 10) = 240 * k + 41 ∧
    a (56 * k + 11) = 240 * k + 46 ∧
    a (56 * k + 12) = 240 * k + 52 ∧
    a (56 * k + 13) = 248 * k + 58 ∧
    a (56 * k + 14) = 248 * k + 63 ∧
    a (56 * k + 15) = 248 * k + 68 ∧
    a (56 * k + 16) = 240 * k + 69 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 56 * k + 9 = 56 * k + (1 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 56 * k + 10 = 56 * k + (1 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 56 * k + 11 = 56 * k + (1 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 56 * k + 12 = 56 * k + (1 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 56 * k + 13 = 56 * k + (1 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 56 * k + 14 = 56 * k + (1 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 56 * k + 15 = 56 * k + (1 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 56 * k + 16 = 56 * k + (1 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (56 * k + 17) = 240 * k + 71 ∧
    a (56 * k + 18) = 240 * k + 75 ∧
    a (56 * k + 19) = 240 * k + 81 ∧
    a (56 * k + 20) = 248 * k + 89 ∧
    a (56 * k + 21) = 248 * k + 94 ∧
    a (56 * k + 22) = 248 * k + 99 ∧
    a (56 * k + 23) = 240 * k + 100 ∧
    a (56 * k + 24) = 240 * k + 102 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 56 * k + 17 = 56 * k + (1 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 56 * k + 18 = 56 * k + (1 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 56 * k + 19 = 56 * k + (1 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 56 * k + 20 = 56 * k + (1 + 19) from rfl, b_res k 19 (by decide), c38, c39]
  · rw [show 56 * k + 21 = 56 * k + (1 + 20) from rfl, b_res k 20 (by decide), c40, c41]
  · rw [show 56 * k + 22 = 56 * k + (1 + 21) from rfl, b_res k 21 (by decide), c42, c43]
  · rw [show 56 * k + 23 = 56 * k + (1 + 22) from rfl, b_res k 22 (by decide), c44, c45]
  · rw [show 56 * k + 24 = 56 * k + (1 + 23) from rfl, b_res k 23 (by decide), c46, c47]

theorem a_closed3 (k : ℕ) :
    a (56 * k + 25) = 240 * k + 105 ∧
    a (56 * k + 26) = 240 * k + 110 ∧
    a (56 * k + 27) = 248 * k + 119 ∧
    a (56 * k + 28) = 248 * k + 125 ∧
    a (56 * k + 29) = 248 * k + 130 ∧
    a (56 * k + 30) = 240 * k + 130 ∧
    a (56 * k + 31) = 240 * k + 133 ∧
    a (56 * k + 32) = 240 * k + 136 := by
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := closedK3.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 56 * k + 25 = 56 * k + (1 + 24) from rfl, b_res k 24 (by decide), c48, c49]
  · rw [show 56 * k + 26 = 56 * k + (1 + 25) from rfl, b_res k 25 (by decide), c50, c51]
  · rw [show 56 * k + 27 = 56 * k + (1 + 26) from rfl, b_res k 26 (by decide), c52, c53]
  · rw [show 56 * k + 28 = 56 * k + (1 + 27) from rfl, b_res k 27 (by decide), c54, c55]
  · rw [show 56 * k + 29 = 56 * k + (1 + 28) from rfl, b_res k 28 (by decide), c56, c57]
  · rw [show 56 * k + 30 = 56 * k + (1 + 29) from rfl, b_res k 29 (by decide), c58, c59]
  · rw [show 56 * k + 31 = 56 * k + (1 + 30) from rfl, b_res k 30 (by decide), c60, c61]
  · rw [show 56 * k + 32 = 56 * k + (1 + 31) from rfl, b_res k 31 (by decide), c62, c63]

theorem a_closed4 (k : ℕ) :
    a (56 * k + 33) = 240 * k + 140 ∧
    a (56 * k + 34) = 248 * k + 149 ∧
    a (56 * k + 35) = 248 * k + 155 ∧
    a (56 * k + 36) = 248 * k + 161 ∧
    a (56 * k + 37) = 240 * k + 160 ∧
    a (56 * k + 38) = 240 * k + 163 ∧
    a (56 * k + 39) = 240 * k + 167 ∧
    a (56 * k + 40) = 240 * k + 171 := by
  obtain ⟨c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79⟩ := closedK4.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 56 * k + 33 = 56 * k + (1 + 32) from rfl, b_res k 32 (by decide), c64, c65]
  · rw [show 56 * k + 34 = 56 * k + (1 + 33) from rfl, b_res k 33 (by decide), c66, c67]
  · rw [show 56 * k + 35 = 56 * k + (1 + 34) from rfl, b_res k 34 (by decide), c68, c69]
  · rw [show 56 * k + 36 = 56 * k + (1 + 35) from rfl, b_res k 35 (by decide), c70, c71]
  · rw [show 56 * k + 37 = 56 * k + (1 + 36) from rfl, b_res k 36 (by decide), c72, c73]
  · rw [show 56 * k + 38 = 56 * k + (1 + 37) from rfl, b_res k 37 (by decide), c74, c75]
  · rw [show 56 * k + 39 = 56 * k + (1 + 38) from rfl, b_res k 38 (by decide), c76, c77]
  · rw [show 56 * k + 40 = 56 * k + (1 + 39) from rfl, b_res k 39 (by decide), c78, c79]

theorem a_closed5 (k : ℕ) :
    a (56 * k + 41) = 248 * k + 180 ∧
    a (56 * k + 42) = 248 * k + 185 ∧
    a (56 * k + 43) = 248 * k + 191 ∧
    a (56 * k + 44) = 240 * k + 190 ∧
    a (56 * k + 45) = 240 * k + 193 ∧
    a (56 * k + 46) = 240 * k + 197 ∧
    a (56 * k + 47) = 240 * k + 202 ∧
    a (56 * k + 48) = 248 * k + 212 := by
  obtain ⟨c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95⟩ := closedK5.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 56 * k + 41 = 56 * k + (1 + 40) from rfl, b_res k 40 (by decide), c80, c81]
  · rw [show 56 * k + 42 = 56 * k + (1 + 41) from rfl, b_res k 41 (by decide), c82, c83]
  · rw [show 56 * k + 43 = 56 * k + (1 + 42) from rfl, b_res k 42 (by decide), c84, c85]
  · rw [show 56 * k + 44 = 56 * k + (1 + 43) from rfl, b_res k 43 (by decide), c86, c87]
  · rw [show 56 * k + 45 = 56 * k + (1 + 44) from rfl, b_res k 44 (by decide), c88, c89]
  · rw [show 56 * k + 46 = 56 * k + (1 + 45) from rfl, b_res k 45 (by decide), c90, c91]
  · rw [show 56 * k + 47 = 56 * k + (1 + 46) from rfl, b_res k 46 (by decide), c92, c93]
  · rw [show 56 * k + 48 = 56 * k + (1 + 47) from rfl, b_res k 47 (by decide), c94, c95]

theorem a_closed6 (k : ℕ) :
    a (56 * k + 49) = 248 * k + 216 ∧
    a (56 * k + 50) = 248 * k + 221 ∧
    a (56 * k + 51) = 240 * k + 219 ∧
    a (56 * k + 52) = 240 * k + 223 ∧
    a (56 * k + 53) = 240 * k + 227 ∧
    a (56 * k + 54) = 240 * k + 232 ∧
    a (56 * k + 55) = 248 * k + 244 ∧
    a (56 * k + 56) = 248 * k + 248 := by
  obtain ⟨c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111⟩ := closedK6.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 56 * k + 49 = 56 * k + (1 + 48) from rfl, b_res k 48 (by decide), c96, c97]
  · rw [show 56 * k + 50 = 56 * k + (1 + 49) from rfl, b_res k 49 (by decide), c98, c99]
  · rw [show 56 * k + 51 = 56 * k + (1 + 50) from rfl, b_res k 50 (by decide), c100, c101]
  · rw [show 56 * k + 52 = 56 * k + (1 + 51) from rfl, b_res k 51 (by decide), c102, c103]
  · rw [show 56 * k + 53 = 56 * k + (1 + 52) from rfl, b_res k 52 (by decide), c104, c105]
  · rw [show 56 * k + 54 = 56 * k + (1 + 53) from rfl, b_res k 53 (by decide), c106, c107]
  · rw [show 56 * k + 55 = 56 * k + (1 + 54) from rfl, b_res k 54 (by decide), c108, c109]
  · rw [show 56 * k + 56 = 56 * k + (1 + 55) from rfl, b_res k 55 (by decide), c110, c111]

/-- The closed form per residue of n mod 56, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (56 * k + 1) = 248 * k + 4 ∧
    a (56 * k + 2) = 240 * k + 8 ∧
    a (56 * k + 3) = 240 * k + 12 ∧
    a (56 * k + 4) = 240 * k + 17 ∧
    a (56 * k + 5) = 240 * k + 22 ∧
    a (56 * k + 6) = 248 * k + 27 ∧
    a (56 * k + 7) = 248 * k + 32 ∧
    a (56 * k + 8) = 248 * k + 36 ∧
    a (56 * k + 9) = 240 * k + 38 ∧
    a (56 * k + 10) = 240 * k + 41 ∧
    a (56 * k + 11) = 240 * k + 46 ∧
    a (56 * k + 12) = 240 * k + 52 ∧
    a (56 * k + 13) = 248 * k + 58 ∧
    a (56 * k + 14) = 248 * k + 63 ∧
    a (56 * k + 15) = 248 * k + 68 ∧
    a (56 * k + 16) = 240 * k + 69 ∧
    a (56 * k + 17) = 240 * k + 71 ∧
    a (56 * k + 18) = 240 * k + 75 ∧
    a (56 * k + 19) = 240 * k + 81 ∧
    a (56 * k + 20) = 248 * k + 89 ∧
    a (56 * k + 21) = 248 * k + 94 ∧
    a (56 * k + 22) = 248 * k + 99 ∧
    a (56 * k + 23) = 240 * k + 100 ∧
    a (56 * k + 24) = 240 * k + 102 ∧
    a (56 * k + 25) = 240 * k + 105 ∧
    a (56 * k + 26) = 240 * k + 110 ∧
    a (56 * k + 27) = 248 * k + 119 ∧
    a (56 * k + 28) = 248 * k + 125 ∧
    a (56 * k + 29) = 248 * k + 130 ∧
    a (56 * k + 30) = 240 * k + 130 ∧
    a (56 * k + 31) = 240 * k + 133 ∧
    a (56 * k + 32) = 240 * k + 136 ∧
    a (56 * k + 33) = 240 * k + 140 ∧
    a (56 * k + 34) = 248 * k + 149 ∧
    a (56 * k + 35) = 248 * k + 155 ∧
    a (56 * k + 36) = 248 * k + 161 ∧
    a (56 * k + 37) = 240 * k + 160 ∧
    a (56 * k + 38) = 240 * k + 163 ∧
    a (56 * k + 39) = 240 * k + 167 ∧
    a (56 * k + 40) = 240 * k + 171 ∧
    a (56 * k + 41) = 248 * k + 180 ∧
    a (56 * k + 42) = 248 * k + 185 ∧
    a (56 * k + 43) = 248 * k + 191 ∧
    a (56 * k + 44) = 240 * k + 190 ∧
    a (56 * k + 45) = 240 * k + 193 ∧
    a (56 * k + 46) = 240 * k + 197 ∧
    a (56 * k + 47) = 240 * k + 202 ∧
    a (56 * k + 48) = 248 * k + 212 ∧
    a (56 * k + 49) = 248 * k + 216 ∧
    a (56 * k + 50) = 248 * k + 221 ∧
    a (56 * k + 51) = 240 * k + 219 ∧
    a (56 * k + 52) = 240 * k + 223 ∧
    a (56 * k + 53) = 240 * k + 227 ∧
    a (56 * k + 54) = 240 * k + 232 ∧
    a (56 * k + 55) = 248 * k + 244 ∧
    a (56 * k + 56) = 248 * k + 248 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15⟩ := a_closed1 k
  obtain ⟨x16, x17, x18, x19, x20, x21, x22, x23⟩ := a_closed2 k
  obtain ⟨x24, x25, x26, x27, x28, x29, x30, x31⟩ := a_closed3 k
  obtain ⟨x32, x33, x34, x35, x36, x37, x38, x39⟩ := a_closed4 k
  obtain ⟨x40, x41, x42, x43, x44, x45, x46, x47⟩ := a_closed5 k
  obtain ⟨x48, x49, x50, x51, x52, x53, x54, x55⟩ := a_closed6 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55⟩

def controlsK : PLift ((List.range 50).map b = [1, 4, 8, 12, 17, 22, 27, 32, 36, 38, 41, 46, 52, 58, 63, 68, 69, 71, 75, 81, 89, 94, 99, 100, 102, 105, 110, 119, 125, 130, 130, 133, 136, 140, 149, 155, 161, 160, 163, 167, 171, 180, 185, 191, 190, 193, 197, 202, 212, 216]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 12, 17, 22, 27, 32, 36, 38, 41, 46, 52, 58, 63, 68, 69, 71, 75, 81, 89, 94, 99, 100, 102, 105, 110, 119, 125, 130, 130, 133, 136, 140, 149, 155, 161, 160, 163, 167, 171, 180, 185, 191, 190, 193, 197, 202, 212, 216] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 56 → dv (t + 20) + dv (t + 18) + dv (t + 16) + dv (t + 14) + dv (t + 6) + dv (t + 4) + dv (t + 2) + dv (t + 0) = 2 * dv (t + 13) + 2 * dv (t + 11) + 2 * dv (t + 9) + 2 * dv (t + 7)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 56 → dv (t + 20) + dv (t + 18) + dv (t + 16) + dv (t + 14) + dv (t + 6) + dv (t + 4) + dv (t + 2) + dv (t + 0) = 2 * dv (t + 13) + 2 * dv (t + 11) + 2 * dv (t + 9) + 2 * dv (t + 7) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 20) : ℤ) = -(dv (t + 18) : ℤ) - (dv (t + 16) : ℤ) - (dv (t + 14) : ℤ) + 2 * (dv (t + 13) : ℤ) + 2 * (dv (t + 11) : ℤ) + 2 * (dv (t + 9) : ℤ) + 2 * (dv (t + 7) : ℤ) - (dv (t + 6) : ℤ) - (dv (t + 4) : ℤ) - (dv (t + 2) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 56 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 2, e 4, e 6, e 7, e 9, e 11, e 13, e 14, e 16, e 18, e 20]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 56) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 56 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 56 → b (q + 21) + b (q + 19) + b (q + 17) + b (q + 15) + b (q + 7) + b (q + 5) + b (q + 3) + b (q + 1) = 2 * b (q + 14) + 2 * b (q + 12) + 2 * b (q + 10) + 2 * b (q + 8)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 56 → b (q + 21) + b (q + 19) + b (q + 17) + b (q + 15) + b (q + 7) + b (q + 5) + b (q + 3) + b (q + 1) = 2 * b (q + 14) + 2 * b (q + 12) + 2 * b (q + 10) + 2 * b (q + 8) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 21) : ℤ) = -b (q + 19) - b (q + 17) - b (q + 15) + 2 * b (q + 14) + 2 * b (q + 12) + 2 * b (q + 10) + 2 * b (q + 8) - b (q + 7) - b (q + 5) - b (q + 3) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 56 ∨ 56 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 56 := ⟨q - 56, by omega⟩
      have h0 : (b (v + 21) : ℤ) = -b (v + 19) - b (v + 17) - b (v + 15) + 2 * b (v + 14) + 2 * b (v + 12) + 2 * b (v + 10) + 2 * b (v + 8) - b (v + 7) - b (v + 5) - b (v + 3) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 57) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 56 = v + 57 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s3 : (b (v + 59) : ℤ) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (le_trans (by decide : 1 ≤ 3) (Nat.le_add_left _ v))
        rw [show v + 3 + 56 = v + 59 from Nat.add_assoc _ _ _,
          show v + 3 - 1 = v + 2 from Nat.add_sub_assoc (by decide : 1 ≤ 3) v] at h
        exact_mod_cast h
      have s5 : (b (v + 61) : ℤ) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (le_trans (by decide : 1 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 56 = v + 61 from Nat.add_assoc _ _ _,
          show v + 5 - 1 = v + 4 from Nat.add_sub_assoc (by decide : 1 ≤ 5) v] at h
        exact_mod_cast h
      have s7 : (b (v + 63) : ℤ) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (le_trans (by decide : 1 ≤ 7) (Nat.le_add_left _ v))
        rw [show v + 7 + 56 = v + 63 from Nat.add_assoc _ _ _,
          show v + 7 - 1 = v + 6 from Nat.add_sub_assoc (by decide : 1 ≤ 7) v] at h
        exact_mod_cast h
      have s8 : (b (v + 64) : ℤ) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (le_trans (by decide : 1 ≤ 8) (Nat.le_add_left _ v))
        rw [show v + 8 + 56 = v + 64 from Nat.add_assoc _ _ _,
          show v + 8 - 1 = v + 7 from Nat.add_sub_assoc (by decide : 1 ≤ 8) v] at h
        exact_mod_cast h
      have s10 : (b (v + 66) : ℤ) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (le_trans (by decide : 1 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 56 = v + 66 from Nat.add_assoc _ _ _,
          show v + 10 - 1 = v + 9 from Nat.add_sub_assoc (by decide : 1 ≤ 10) v] at h
        exact_mod_cast h
      have s12 : (b (v + 68) : ℤ) = b (v + 12) + dv (v + 11) := by
        have h := b_step (v + 12) (le_trans (by decide : 1 ≤ 12) (Nat.le_add_left _ v))
        rw [show v + 12 + 56 = v + 68 from Nat.add_assoc _ _ _,
          show v + 12 - 1 = v + 11 from Nat.add_sub_assoc (by decide : 1 ≤ 12) v] at h
        exact_mod_cast h
      have s14 : (b (v + 70) : ℤ) = b (v + 14) + dv (v + 13) := by
        have h := b_step (v + 14) (le_trans (by decide : 1 ≤ 14) (Nat.le_add_left _ v))
        rw [show v + 14 + 56 = v + 70 from Nat.add_assoc _ _ _,
          show v + 14 - 1 = v + 13 from Nat.add_sub_assoc (by decide : 1 ≤ 14) v] at h
        exact_mod_cast h
      have s15 : (b (v + 71) : ℤ) = b (v + 15) + dv (v + 14) := by
        have h := b_step (v + 15) (le_trans (by decide : 1 ≤ 15) (Nat.le_add_left _ v))
        rw [show v + 15 + 56 = v + 71 from Nat.add_assoc _ _ _,
          show v + 15 - 1 = v + 14 from Nat.add_sub_assoc (by decide : 1 ≤ 15) v] at h
        exact_mod_cast h
      have s17 : (b (v + 73) : ℤ) = b (v + 17) + dv (v + 16) := by
        have h := b_step (v + 17) (le_trans (by decide : 1 ≤ 17) (Nat.le_add_left _ v))
        rw [show v + 17 + 56 = v + 73 from Nat.add_assoc _ _ _,
          show v + 17 - 1 = v + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) v] at h
        exact_mod_cast h
      have s19 : (b (v + 75) : ℤ) = b (v + 19) + dv (v + 18) := by
        have h := b_step (v + 19) (le_trans (by decide : 1 ≤ 19) (Nat.le_add_left _ v))
        rw [show v + 19 + 56 = v + 75 from Nat.add_assoc _ _ _,
          show v + 19 - 1 = v + 18 from Nat.add_sub_assoc (by decide : 1 ≤ 19) v] at h
        exact_mod_cast h
      have s21 : (b (v + 77) : ℤ) = b (v + 21) + dv (v + 20) := by
        have h := b_step (v + 21) (le_trans (by decide : 1 ≤ 21) (Nat.le_add_left _ v))
        rw [show v + 21 + 56 = v + 77 from Nat.add_assoc _ _ _,
          show v + 21 - 1 = v + 20 from Nat.add_sub_assoc (by decide : 1 ≤ 21) v] at h
        exact_mod_cast h
      show (b (v + 77) : ℤ) = -b (v + 75) - b (v + 73) - b (v + 71) + 2 * b (v + 70) + 2 * b (v + 68) + 2 * b (v + 66) + 2 * b (v + 64) - b (v + 63) - b (v + 61) - b (v + 59) - b (v + 57)
      linear_combination s21 - (-1) * s19 - (-1) * s17 - (-1) * s15 - (2) * s14 - (2) * s12 - (2) * s10 - (2) * s8 - (-1) * s7 - (-1) * s5 - (-1) * s3 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 20 < n → (a n : ℤ) = -a (n - 2) - a (n - 4) - a (n - 6) + 2 * a (n - 7) + 2 * a (n - 9) + 2 * a (n - 11) + 2 * a (n - 13) - a (n - 14) - a (n - 16) - a (n - 18) - a (n - 20) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 21 := ⟨n - 21, by omega⟩
  rw [show q + 21 - 2 = q + 19 from Nat.add_sub_assoc (by decide : 2 ≤ 21) q, show q + 21 - 4 = q + 17 from Nat.add_sub_assoc (by decide : 4 ≤ 21) q, show q + 21 - 6 = q + 15 from Nat.add_sub_assoc (by decide : 6 ≤ 21) q, show q + 21 - 7 = q + 14 from Nat.add_sub_assoc (by decide : 7 ≤ 21) q, show q + 21 - 9 = q + 12 from Nat.add_sub_assoc (by decide : 9 ≤ 21) q, show q + 21 - 11 = q + 10 from Nat.add_sub_assoc (by decide : 11 ≤ 21) q, show q + 21 - 13 = q + 8 from Nat.add_sub_assoc (by decide : 13 ≤ 21) q, show q + 21 - 14 = q + 7 from Nat.add_sub_assoc (by decide : 14 ≤ 21) q, show q + 21 - 16 = q + 5 from Nat.add_sub_assoc (by decide : 16 ≤ 21) q, show q + 21 - 18 = q + 3 from Nat.add_sub_assoc (by decide : 18 ≤ 21) q, show q + 21 - 20 = q + 1 from Nat.add_sub_assoc (by decide : 20 ≤ 21) q]
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

/-- The coefficients of A * DEN and NUM agree below 21, in natural numbers (negative terms moved
across). -/
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (b n) (bk n 2)) (bk n 4)) (bk n 6)) (bk n 14)) (bk n 16)) (bk n 18)) (bk n 20)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 2 (bk n 7)) (Nat.mul 2 (bk n 9))) (Nat.mul 2 (bk n 11))) (Nat.mul 2 (bk n 13))) (ind n 0)) (Nat.mul 4 (ind n 1))) (Nat.mul 9 (ind n 2))) (Nat.mul 16 (ind n 3))) (Nat.mul 26 (ind n 4))) (Nat.mul 38 (ind n 5))) (Nat.mul 53 (ind n 6))) (Nat.mul 68 (ind n 7))) (Nat.mul 80 (ind n 8))) (Nat.mul 86 (ind n 9))) (Nat.mul 89 (ind n 10))) (Nat.mul 86 (ind n 11))) (Nat.mul 80 (ind n 12))) (Nat.mul 68 (ind n 13))) (Nat.mul 53 (ind n 14))) (Nat.mul 38 (ind n 15))) (Nat.mul 26 (ind n 16))) (Nat.mul 17 (ind n 17))) (Nat.mul 9 (ind n 18))) (Nat.mul 4 (ind n 19))) (ind n 20)

def gfK : PLift ((allR 21 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 21, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 21) :
    1 * (b (n) : ℚ) + 1 * (if 2 ≤ n then (b (n - 2) : ℚ) else 0) + 1 * (if 4 ≤ n then (b (n - 4) : ℚ) else 0) + 1 * (if 6 ≤ n then (b (n - 6) : ℚ) else 0) - 2 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) - 2 * (if 9 ≤ n then (b (n - 9) : ℚ) else 0) - 2 * (if 11 ≤ n then (b (n - 11) : ℚ) else 0) - 2 * (if 13 ≤ n then (b (n - 13) : ℚ) else 0) + 1 * (if 14 ≤ n then (b (n - 14) : ℚ) else 0) + 1 * (if 16 ≤ n then (b (n - 16) : ℚ) else 0) + 1 * (if 18 ≤ n then (b (n - 18) : ℚ) else 0) + 1 * (if 20 ≤ n then (b (n - 20) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 4 + (if n = 2 then (1 : ℚ) else 0) * 9 + (if n = 3 then (1 : ℚ) else 0) * 16 + (if n = 4 then (1 : ℚ) else 0) * 26 + (if n = 5 then (1 : ℚ) else 0) * 38 + (if n = 6 then (1 : ℚ) else 0) * 53 + (if n = 7 then (1 : ℚ) else 0) * 68 + (if n = 8 then (1 : ℚ) else 0) * 80 + (if n = 9 then (1 : ℚ) else 0) * 86 + (if n = 10 then (1 : ℚ) else 0) * 89 + (if n = 11 then (1 : ℚ) else 0) * 86 + (if n = 12 then (1 : ℚ) else 0) * 80 + (if n = 13 then (1 : ℚ) else 0) * 68 + (if n = 14 then (1 : ℚ) else 0) * 53 + (if n = 15 then (1 : ℚ) else 0) * 38 + (if n = 16 then (1 : ℚ) else 0) * 26 + (if n = 17 then (1 : ℚ) else 0) * 17 + (if n = 18 then (1 : ℚ) else 0) * 9 + (if n = 19 then (1 : ℚ) else 0) * 4 + (if n = 20 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 21 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 21) : ℚ) + 1 * (if 2 ≤ q + 21 then (b (q + 21 - 2) : ℚ) else 0) + 1 * (if 4 ≤ q + 21 then (b (q + 21 - 4) : ℚ) else 0) + 1 * (if 6 ≤ q + 21 then (b (q + 21 - 6) : ℚ) else 0) - 2 * (if 7 ≤ q + 21 then (b (q + 21 - 7) : ℚ) else 0) - 2 * (if 9 ≤ q + 21 then (b (q + 21 - 9) : ℚ) else 0) - 2 * (if 11 ≤ q + 21 then (b (q + 21 - 11) : ℚ) else 0) - 2 * (if 13 ≤ q + 21 then (b (q + 21 - 13) : ℚ) else 0) + 1 * (if 14 ≤ q + 21 then (b (q + 21 - 14) : ℚ) else 0) + 1 * (if 16 ≤ q + 21 then (b (q + 21 - 16) : ℚ) else 0) + 1 * (if 18 ≤ q + 21 then (b (q + 21 - 18) : ℚ) else 0) + 1 * (if 20 ≤ q + 21 then (b (q + 21 - 20) : ℚ) else 0) =
      (if q + 21 = 0 then (1 : ℚ) else 0) * 1 + (if q + 21 = 1 then (1 : ℚ) else 0) * 4 + (if q + 21 = 2 then (1 : ℚ) else 0) * 9 + (if q + 21 = 3 then (1 : ℚ) else 0) * 16 + (if q + 21 = 4 then (1 : ℚ) else 0) * 26 + (if q + 21 = 5 then (1 : ℚ) else 0) * 38 + (if q + 21 = 6 then (1 : ℚ) else 0) * 53 + (if q + 21 = 7 then (1 : ℚ) else 0) * 68 + (if q + 21 = 8 then (1 : ℚ) else 0) * 80 + (if q + 21 = 9 then (1 : ℚ) else 0) * 86 + (if q + 21 = 10 then (1 : ℚ) else 0) * 89 + (if q + 21 = 11 then (1 : ℚ) else 0) * 86 + (if q + 21 = 12 then (1 : ℚ) else 0) * 80 + (if q + 21 = 13 then (1 : ℚ) else 0) * 68 + (if q + 21 = 14 then (1 : ℚ) else 0) * 53 + (if q + 21 = 15 then (1 : ℚ) else 0) * 38 + (if q + 21 = 16 then (1 : ℚ) else 0) * 26 + (if q + 21 = 17 then (1 : ℚ) else 0) * 17 + (if q + 21 = 18 then (1 : ℚ) else 0) * 9 + (if q + 21 = 19 then (1 : ℚ) else 0) * 4 + (if q + 21 = 20 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 21) : ℤ) = -b (q + 19) - b (q + 17) - b (q + 15) + 2 * b (q + 14) + 2 * b (q + 12) + 2 * b (q + 10) + 2 * b (q + 8) - b (q + 7) - b (q + 5) - b (q + 3) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 21 - 2 = q + 19 from Nat.add_sub_assoc (by decide : 2 ≤ 21) q, show q + 21 - 4 = q + 17 from Nat.add_sub_assoc (by decide : 4 ≤ 21) q, show q + 21 - 6 = q + 15 from Nat.add_sub_assoc (by decide : 6 ≤ 21) q, show q + 21 - 7 = q + 14 from Nat.add_sub_assoc (by decide : 7 ≤ 21) q, show q + 21 - 9 = q + 12 from Nat.add_sub_assoc (by decide : 9 ≤ 21) q, show q + 21 - 11 = q + 10 from Nat.add_sub_assoc (by decide : 11 ≤ 21) q, show q + 21 - 13 = q + 8 from Nat.add_sub_assoc (by decide : 13 ≤ 21) q, show q + 21 - 14 = q + 7 from Nat.add_sub_assoc (by decide : 14 ≤ 21) q, show q + 21 - 16 = q + 5 from Nat.add_sub_assoc (by decide : 16 ≤ 21) q, show q + 21 - 18 = q + 3 from Nat.add_sub_assoc (by decide : 18 ≤ 21) q, show q + 21 - 20 = q + 1 from Nat.add_sub_assoc (by decide : 20 ≤ 21) q, show 2 ≤ q + 21 from le_trans (by decide : 2 ≤ 21) (Nat.le_add_left 21 q), show 4 ≤ q + 21 from le_trans (by decide : 4 ≤ 21) (Nat.le_add_left 21 q), show 6 ≤ q + 21 from le_trans (by decide : 6 ≤ 21) (Nat.le_add_left 21 q), show 7 ≤ q + 21 from le_trans (by decide : 7 ≤ 21) (Nat.le_add_left 21 q), show 9 ≤ q + 21 from le_trans (by decide : 9 ≤ 21) (Nat.le_add_left 21 q), show 11 ≤ q + 21 from le_trans (by decide : 11 ≤ 21) (Nat.le_add_left 21 q), show 13 ≤ q + 21 from le_trans (by decide : 13 ≤ 21) (Nat.le_add_left 21 q), show 14 ≤ q + 21 from le_trans (by decide : 14 ≤ 21) (Nat.le_add_left 21 q), show 16 ≤ q + 21 from le_trans (by decide : 16 ≤ 21) (Nat.le_add_left 21 q), show 18 ≤ q + 21 from le_trans (by decide : 18 ≤ 21) (Nat.le_add_left 21 q), show 20 ≤ q + 21 from le_trans (by decide : 20 ≤ 21) (Nat.le_add_left 21 q), show ¬ q + 21 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 14 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 14 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 15 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 15 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 16 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 16 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 17 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 17 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 18 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 18 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 19 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 19 < 21) (Nat.le_add_left 21 q)), show ¬ q + 21 = 20 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 20 < 21) (Nat.le_add_left 21 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) = C 1 * A + C 1 * (A * X ^ 2) + C 1 * (A * X ^ 4) + C 1 * (A * X ^ 6) - C 2 * (A * X ^ 7) - C 2 * (A * X ^ 9) - C 2 * (A * X ^ 11) - C 2 * (A * X ^ 13) + C 1 * (A * X ^ 14) + C 1 * (A * X ^ 16) + C 1 * (A * X ^ 18) + C 1 * (A * X ^ 20) := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (X ^ 20 + 4 * X ^ 19 + 9 * X ^ 18 + 17 * X ^ 17 + 26 * X ^ 16 + 38 * X ^ 15 + 53 * X ^ 14 + 68 * X ^ 13 + 80 * X ^ 12 + 86 * X ^ 11 + 89 * X ^ 10 + 86 * X ^ 9 + 80 * X ^ 8 + 68 * X ^ 7 + 53 * X ^ 6 + 38 * X ^ 5 + 26 * X ^ 4 + 16 * X ^ 3 + 9 * X ^ 2 + 4 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 4 + X ^ 2 * C 9 + X ^ 3 * C 16 + X ^ 4 * C 26 + X ^ 5 * C 38 + X ^ 6 * C 53 + X ^ 7 * C 68 + X ^ 8 * C 80 + X ^ 9 * C 86 + X ^ 10 * C 89 + X ^ 11 * C 86 + X ^ 12 * C 80 + X ^ 13 * C 68 + X ^ 14 * C 53 + X ^ 15 * C 38 + X ^ 16 * C 26 + X ^ 17 * C 17 + X ^ 18 * C 9 + X ^ 19 * C 4 + X ^ 20 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      X ^ 20 + 4 * X ^ 19 + 9 * X ^ 18 + 17 * X ^ 17 + 26 * X ^ 16 + 38 * X ^ 15 + 53 * X ^ 14 + 68 * X ^ 13 + 80 * X ^ 12 + 86 * X ^ 11 + 89 * X ^ 10 + 86 * X ^ 9 + 80 * X ^ 8 + 68 * X ^ 7 + 53 * X ^ 6 + 38 * X ^ 5 + 26 * X ^ 4 + 16 * X ^ 3 + 9 * X ^ 2 + 4 * X + 1 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  rw [gf_den A, gf_num]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 21 with hn | hn
  · linarith [gf_low n hn]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 21 := ⟨n - 21, by omega⟩
    linarith [gf_high q]

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      X ^ 20 + 4 * X ^ 19 + 9 * X ^ 18 + 17 * X ^ 17 + 26 * X ^ 16 + 38 * X ^ 15 + 53 * X ^ 14 + 68 * X ^ 13 + 80 * X ^ 12 + 86 * X ^ 11 + 89 * X ^ 10 + 86 * X ^ 9 + 80 * X ^ 8 + 68 * X ^ 7 + 53 * X ^ 6 + 38 * X ^ 5 + 26 * X ^ 4 + 16 * X ^ 3 + 9 * X ^ 2 + 4 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 20 < n → (a n : ℤ) = -a (n - 2) - a (n - 4) - a (n - 6) + 2 * a (n - 7) + 2 * a (n - 9) + 2 * a (n - 11) + 2 * a (n - 13) - a (n - 14) - a (n - 16) - a (n - 18) - a (n - 20) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 12, 17, 22, 27, 32, 36, 38, 41, 46, 52, 58, 63, 68, 69, 71, 75, 81, 89, 94, 99, 100, 102, 105, 110, 119, 125, 130, 130, 133, 136, 140, 149, 155, 161, 160, 163, 167, 171, 180, 185, 191, 190, 193, 197, 202, 212, 216] := Count.controls

/-- The step a(n + 56) = a(n) + Count.dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 56) = a n + Count.dv (n - 1) := Count.a_step n hn

/-- The closed form per residue of n mod 56, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (56 * k + 1) = 248 * k + 4 ∧
    a (56 * k + 2) = 240 * k + 8 ∧
    a (56 * k + 3) = 240 * k + 12 ∧
    a (56 * k + 4) = 240 * k + 17 ∧
    a (56 * k + 5) = 240 * k + 22 ∧
    a (56 * k + 6) = 248 * k + 27 ∧
    a (56 * k + 7) = 248 * k + 32 ∧
    a (56 * k + 8) = 248 * k + 36 ∧
    a (56 * k + 9) = 240 * k + 38 ∧
    a (56 * k + 10) = 240 * k + 41 ∧
    a (56 * k + 11) = 240 * k + 46 ∧
    a (56 * k + 12) = 240 * k + 52 ∧
    a (56 * k + 13) = 248 * k + 58 ∧
    a (56 * k + 14) = 248 * k + 63 ∧
    a (56 * k + 15) = 248 * k + 68 ∧
    a (56 * k + 16) = 240 * k + 69 ∧
    a (56 * k + 17) = 240 * k + 71 ∧
    a (56 * k + 18) = 240 * k + 75 ∧
    a (56 * k + 19) = 240 * k + 81 ∧
    a (56 * k + 20) = 248 * k + 89 ∧
    a (56 * k + 21) = 248 * k + 94 ∧
    a (56 * k + 22) = 248 * k + 99 ∧
    a (56 * k + 23) = 240 * k + 100 ∧
    a (56 * k + 24) = 240 * k + 102 ∧
    a (56 * k + 25) = 240 * k + 105 ∧
    a (56 * k + 26) = 240 * k + 110 ∧
    a (56 * k + 27) = 248 * k + 119 ∧
    a (56 * k + 28) = 248 * k + 125 ∧
    a (56 * k + 29) = 248 * k + 130 ∧
    a (56 * k + 30) = 240 * k + 130 ∧
    a (56 * k + 31) = 240 * k + 133 ∧
    a (56 * k + 32) = 240 * k + 136 ∧
    a (56 * k + 33) = 240 * k + 140 ∧
    a (56 * k + 34) = 248 * k + 149 ∧
    a (56 * k + 35) = 248 * k + 155 ∧
    a (56 * k + 36) = 248 * k + 161 ∧
    a (56 * k + 37) = 240 * k + 160 ∧
    a (56 * k + 38) = 240 * k + 163 ∧
    a (56 * k + 39) = 240 * k + 167 ∧
    a (56 * k + 40) = 240 * k + 171 ∧
    a (56 * k + 41) = 248 * k + 180 ∧
    a (56 * k + 42) = 248 * k + 185 ∧
    a (56 * k + 43) = 248 * k + 191 ∧
    a (56 * k + 44) = 240 * k + 190 ∧
    a (56 * k + 45) = 240 * k + 193 ∧
    a (56 * k + 46) = 240 * k + 197 ∧
    a (56 * k + 47) = 240 * k + 202 ∧
    a (56 * k + 48) = 248 * k + 212 ∧
    a (56 * k + 49) = 248 * k + 216 ∧
    a (56 * k + 50) = 248 * k + 221 ∧
    a (56 * k + 51) = 240 * k + 219 ∧
    a (56 * k + 52) = 240 * k + 223 ∧
    a (56 * k + 53) = 240 * k + 227 ∧
    a (56 * k + 54) = 240 * k + 232 ∧
    a (56 * k + 55) = 248 * k + 244 ∧
    a (56 * k + 56) = 248 * k + 248 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ^ 2) =
      X ^ 20 + 4 * X ^ 19 + 9 * X ^ 18 + 17 * X ^ 17 + 26 * X ^ 16 + 38 * X ^ 15 + 53 * X ^ 14 + 68 * X ^ 13 + 80 * X ^ 12 + 86 * X ^ 11 + 89 * X ^ 10 + 86 * X ^ 9 + 80 * X ^ 8 + 68 * X ^ 7 + 53 * X ^ 6 + 38 * X ^ 5 + 26 * X ^ 4 + 16 * X ^ 3 + 9 * X ^ 2 + 4 * X + 1 ∧
    ∀ n : ℕ, 20 < n → (a n : ℤ) = -a (n - 2) - a (n - 4) - a (n - 6) + 2 * a (n - 7) + 2 * a (n - 9) + 2 * a (n - 11) + 2 * a (n - 13) - a (n - 14) - a (n - 16) - a (n - 18) - a (n - 20) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a311533

theorem OMA.solution : type_of% @OMA.S_oeis_a311533.main :=
  OMA.S_oeis_a311533.conjecture
