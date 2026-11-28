import OMAStatements.S_oeis_a310100

namespace OMA.S_oeis_a310100






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 10

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 581109629338128
  | 1 => 693506873304397
  | 2 => 657188664486220
  | 3 => 545960725331439
  | 4 => 620869314817389
  | 5 => 656052578562446
  | 6 => 582280075000270
  | 7 => 618598283819471
  | 8 => 619734369743245
  | 9 => 583415020074414
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 10) : ℤ := tget 509642516513262 5 16 i.val

def Bc (i : Fin 10) : ℤ := tget 729826222973228 5 16 i.val

def Cc (s : Fin 10) (i : Fin 10) : ℤ := tget (CcT s.val) 5 16 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 16. -/
def AcN (i : ℕ) : ℕ := tgetN 509642516513262 5 i

def BcN (i : ℕ) : ℕ := tgetN 729826222973228 5 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem Ac_eq (i : Fin 10) : Ac i = (AcN i.val : ℤ) - 16 := rfl

theorem Bc_eq (i : Fin 10) : Bc i = (BcN i.val : ℤ) - 16 := rfl

theorem Cc_eq (s : Fin 10) (i : Fin 10) : Cc s i = (CcN s.val i.val : ℤ) - 16 := rfl


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
theorem cls (P : Fin 10 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 10 × Fin 10 × ℤ × ℤ) (j : Fin 10) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 10, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
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
theorem shift (x y : ℤ) (e : Fin 10 × Fin 10 × ℤ × ℤ) (j : Fin 10) :
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
theorem farkas (x y : ℤ) (s : Fin 10) (a1 b1 a2 b2 a3 b3 i0 : Fin 10) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
pot k2 ≤ pot i, 10 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 335555701065943968300859695387056753752746883467424881159670238102816393033650725251197374217227112394789840671398119843455487673557311839258520506913407851985351916793400787620433056864812747614896414387957027799853770899481986484349399405294319481311281148102990403402189202983765365403972336780703156014933565795124616223219796468354725593235422305406030625721547046658983960610069049975562078370457342451074236993798853399088493540329460814410458575886207040295757941086130070736802959144805283365489990127526604423335023222488011185755243916103885861955965878006515699048938769740322304366462431478158661075467075015674166881029928490001404835869037512708325069433701838756480029159382198780578342367134320857354326514556872494715992536634119366783544010934293049637293195003704718215895937411972078614739629158467898316025549179788258749802306063926661856705314776751070578212864 5 ((i * 10 + j) * 6 + f)

def fd (i j : Fin 10) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 0 % 10, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 10) : Fin 10 := ⟨fdN i.val j.val 1 % 10, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 10) : ℤ := fd i j 2

def fm2 (i j : Fin 10) : ℤ := fd i j 3

def fm0 (i j : Fin 10) : ℤ := fd i j 4

def fmj (i j : Fin 10) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 10 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 13380424433281087416496780994647965687681024 4 p

def dstv (p : ℕ) : ℕ := tgetN 11800510414319948919215106743532544642384689 4 p

def dxv (p : ℕ) : ℕ := tgetN 1870418220085345096785 2 p

def dyv (p : ℕ) : ℕ := tgetN 1574122160956548404628 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 18253448064066519758491960068430312069180472056242603054070539300409106147599911597988937265511810663458478335790781817037669412122781356410998546306796849361834447531622527540227543589192242263809279676281631757033638198575995160242813932452524629037047559875278320500509615066384864965260738981155877037820311727984608756866174003882212018033797997753656226200633310452738370053112221578182070608091259357488103925223816861304068505 4 (p * 10 + j)

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

/-- The x and y parts of the far certificate of (i, j) cancel, in natural numbers (Ac = AcN - 16). -/
def farXYN (i j : ℕ) : Bool :=
  (fdN i j 2 * AcN (fdN i j 0 % 10) + fdN i j 3 * AcN (fdN i j 1 % 10) + fdN i j 5 * AcN i + fdN i j 4 * 16 ==
      (fdN i j 2 + fdN i j 3 + fdN i j 4) * AcN i + fdN i j 5 * AcN j) &&
    (fdN i j 2 * BcN (fdN i j 0 % 10) + fdN i j 3 * BcN (fdN i j 1 % 10) + fdN i j 5 * BcN i + fdN i j 4 * 16 ==
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
  (List.range 10).all fun s => (List.range 10).all fun i => (List.range 10).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 16, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 36).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 10).all fun j =>
      dlvN p j + 1 * AcN j + 16 * dxv p + 1 * BcN j + 16 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 32 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 10) (i j : Fin 10) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (10 - Cc s i)

/-- Beyond F = 9, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 10) (i j : Fin 10) (hc : farCert s i j) (x y : ℤ)
    (h : F (x, y, s) = pot (x, y, s) i) (hF : 9 < F (x, y, s)) :
    pot (x, y, s) j ≤ pot (x, y, s) i + (-2) := by
  by_contra hc'
  exact farkas x y s (fk1 i j) i (fk2 i j) i i j i 0 0 1 10 (fm1 i j) (fm2 i j) (fmj i j) (fm0 i j) hc
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

/-- Descent rules beyond F = 9, for class s, maximal facet i and the slack classes c1, c2 of the
next and the previous facet: kind 0 names an edge by its position in E; kind 1 is a corner point
within F ≤ 9 (multipliers mu1, mu2, mu0); kinds 2 and 3 are a line of the next or the previous
facet without lattice points (modulus g). -/
def ruleT (s : ℕ) : ℕ :=
  match s with
  | 0 => 3942392526586267560749522354203469798744170920712268848915478734332788528856822701011692477722821025943290505703671164318974525357065147229655749957258788962283223488904900932317961482398393226276767074654388468530901675127363410833360267554416443286440693683798734174901970110158323022082634345824968673800206421602860232956001328548270981432561784051937418852996810481229582404258443126571086309412832211328068742584684688573645242295399555949907891583356458766670785287605659205849272452914711513083156676460153052295122781459469740709463790207602977408768136313948795071063997816755861973175927476339784986757793167467525368087052592795927827640866365217429508875182582565719554760932305227988466238865298963050081254554459621871831420155585224290729252096825260532498719429614483707435896268223210976409905083387471413986533016789178020187848171067741154162028089655956036794004910231376072328321146061964339437212012631668778471433973596445130890021593323559677372028169046246055815783495261458250783256473592222887291637943680983001193472053130753052134906171736955812481169831634553220009946259337451798964836347504231217521238336
  | 1 => 3942392527724690834838290217377336606432303249149501557830461706529646158176010301477181166961910113471346955885915196615972951432986779819442893151059013022702127926580707388893366835153974577748178759392477500356250668705797416397459607225919131123368285167792147879882912826866367094768015972719163981962435824185341552429254657824857843639132518948294087668542630969182691071672395832880664470921624366639963980052418380905014202839120500119671125163038189410218563507250270556142060386301800908355466592310282973378655052515981997430236388298193183550360634392095977300246107905252042795823903265032988969187666053533111879552577429072768896390617255398492794380403948824704117267364527865373027305036920130819196485487100374247987996416446477656940330294064976427022600894336288150723580476228816798392258758627311764981645564356013068996455038774657724709321806100452294318646844317293559423334370979037539141005391487175150685661615563293430460326101893848787582689569451717539540976534565342406115096814009571264099217780701651572484137977769085874145036284465252269154510070384973892462197239361673687279853835473930131023863873
  | 2 => 3942392528180060144473797362646883341278576945590988353281679331491308865496735745763653080328616723824066123820448601247058700701858870486525719363389012387402355883163307226107415604512454062389891677087406667423729949225965986553286714719671771510158333750162956806546039062075687595713890494809696827992897723229626277989601112062553521115229695316826436564409861580871211190005576752372730202633624860838291926648127671192172923907629692019373801097859730773726356942721453564513063183598194872364665821978236395945877329752807809231910211547117866853554047907918823316520224271703189326515718796480141395751401925362451157688384822715563105456101674830101429677503848061911620358974249864531434534533138284985447517385649352327455716177553815323374483044512038427256557165587252263255943665626657413613195264318329178402887286517760242341265208550016899243971524145996546656900543222855599015086280835927964714541480153953396609808135475792120856986815710968952560324103151698221929756242774499839118434533057159926590438159532199304386779459560042768422468084198722581313759605357625046343070626145828348720316553372178224014959552
  | 3 => 3942392528863114108927058080551203414120435577592087107255588515763607726486132565119093619418844642879340916782759137624432552213609496714602672436448679822204725097526050433959117933350875757091164201162915387587051536033084478463729233951971165920718297161187486020320132157087793112841362530825117873756277168118749518079593560262265142961381829925628073653154012382447280499599863458207114635776992518692109509766749261141609496781406222485135017348385925786463076261921887094296194152389626632242032927317547603269018584151541845481578333933414223664186700695415175609742853903410352973012659744023831219830674620294245159531693078717084957137751622636859586238083868786376314830978155381414246671966156773598132648673436009160098043772819190276533731135527199581330888046589983625749002844046321793627633378932800067452314701027671522636995108917238182937273391534949933245957349628448329243454829295734771156371376035338810078913572814502379431239165048603076213446280121374546733047368044911551146042468400010194578738649053843794930476784902531865846527068874156102462644303687886458945654980883503702500792368666987353290842177
  | 4 => 3942392529773852728198072371090296860270941440346155546795689963150776981134230376032623581384392266405736085500234290431200232838107670230730495864779532728090046569165498406644649960769358204902640862831935125981304358156226127302818200665479898228094199370302006038317878396713011955587248088921285892012726771544042421083805476581164421557616097191248980285385914236066711074647091216536238203283924871692606076952561700956786482726450668317580395450350535285935001118083517397043083695900482363620385981737552586674138793563915146051622758558032405341373290492100893304707617344248185833538764462751979018686635024287053493286828799537090216417153603438883202365880941710692883586879382037266247006827222687130764681899421224421228852789788375408654409317735866247111002842345649704937709798847812774098626240894585711901859273299949822521500310710445458556060701304141010422960324848877756284851838109326428541823951935164747607116718848663981414493678193458623130630712668335386309081666714823083872658852450350576466001741386558341683416465866169673002425711226025249011399923513133177713456653845193334883914668630614180954906689
  | 5 => 3942392530456906692651333088994616968425862367540612027813099851222594336539678548026092922628896230940829914847081847142586930177027783453839404077033683633689304826384155247456218440282013218497405797087201521371706429598442419983627701558578091995317639493035472467113145701214854722875941199353365978663425300838440501117326187933066949091970500566842687924255788185499779041936494106001496556855456104770855949146718279903495028706143766764033780714465919651738752415152769410942488274258449068090381947276172385950197563030383438973820503804417488547517950458844446324358130207388499438844888251686400147142458605456383186999943036893541222320652602542964591336813598493355747132303474247322801266871419130507366698881745701246343113622087612947525291270127838911005267656067737498893236436459081727554971608952887546402597347058282107901101493524866316954818336181717387788265844452645445809191087998043185221863256352135901692311271825929441369132053258675896098311290324501379942322183279164534317956873753128171334687659521667298680226889265492044001993306735115160874227709514182035371676724897581407235678972710325141826971840
  | 6 => 3942392531139960657104593806898937029496700234482611046615985971268634799329958073030321343608707465147037475518254619232194422315936123975731517388380813700368199373666989012632752529951414491580911613882420775366009743454398237874296429746197831915984339162029705287506841553438104709843985545724070196434596024628642696786345774757949808655826065491691905499605899523282809187014461068494992794977877396809076548949346806606391063428062929754712627875402123108795504949895220477924242884775327326607641977851250512147178552213406316152930969451819432735343228043738355594491845000726771605768664859163338560054974088091073089654744114236233624058237703838569150079289942710126193234750872097854533741365562156750079290844339952351015975458045325854761715833336954558478943111549402070374788772246224103391420953430475828160735341651060264129259894744399064893936387840314079993035034265280504262952446226087433814614372821156398917023642789225036698110417743383253465319287093355944392115393449850470473240580366253019435148648837355026534765602017467369397485177450746745543070783091065394027772856134967430169204941568276226603232064
  | 7 => 3942392532278383931193361670072803837184832562919843755530968943465492431416499356044830976789648231103322799473290960649811354555477647400082010292617680220712516610362079569156371227941579295120120526474229049279454138014945664662538114130127270312768333141373500441631790147752071167061402205142979549137801199918973415030610267574487040928129762857630031606988156622241048783382266334186465130343096974848546098909741901851395378608263389581526693904429134915196614525936736708758595450653103803901731932339341492940109179058221389635604170839077344005664899605372770538233084175291138869235624026556960790781235967633634328859934423483918812699749455323554018538798784424676923502758149043576599572712311150658804015626225986908146671585455387956775798816131433264822479419168742004192058516128001407383108782867514819997110868899292181000544144957145275197771730237026246398246450164790027308440418485726648075219016472190615875670917776067725514371060331233418667694610703531740887975526443012203841872020012377467093779498589658160220381637875713186309940160437775117056174939700207555233235130175976235699938381849845903081352640
  | 8 => 3942392533416807205282129533246670656643985656426881880637262653967532076540841423585076276097386128908375139107219574397261582204560493744512851909179340836200078150639708518469425309198428517489657897199643820284104227802056037650363301240220368434133526050128573586041641221847436536639444374693663579022445766709276111394497225203684172421983618972544096208010313979232421990174997385585222661033426824141450903967489106929830618210192571894899247833712244767169784554354449027399279180237903057917823918577998474775741466119834870991897467677966790479115403397176817918462248533269735403997366786727228005043159984079531037491230072371914771336078714244412017062227312227979254603865601760696186610988942776103328254463819982163615800831076275369397376604572578276850980556289288277155624481739868750064369494896183331498106518728502293307837918460527747925150416109809106538602793651261844050576359591737641591953728516936668182842037074006748253215324184019108295232712322948457614995935557959589587009615335894092376656282262241158683077615130974771980082510659668352299835835452899623809449814124176207521411169679936469580394304
  | 9 => 3942392534327545824553143823785764091023470754116497744496197200086623254374719430600273391212130384037711929087610054465037896312072231572794520976951435052225626289493823906776790291291400507998276310864047733121915711075018641695497630637224840930815508764541392525198177444481488924024383120944284760124889305344281845363330568909116117823754071927152281942532860009948149331168356493529309629045960760705974131908426454124163758009279428714728851742293586162696930756274475911029952780280534796107207086613641022575337693307193124760916247939400312485293179056367328527472787139142992840983843193653116219050409723454403810856630142655855614018833592874237665983742367063369990510411040206950857077929147758029698857264225317090735788224421302467486936518834360464425606774997858117178543318486189398473283229013130619244346280299732489250754516687865337748405727666815592458809781160753390563501436976002639583338128952743349224133224273201528577518206335668767501951610489347848349120490510866252433758161125789959533654452039092652425912881057584992904012919760622391762760674733358777456687245957702366657334537180691020362555457
  | _ => 0

def rd (s : Fin 10) (i : Fin 10) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 10) (i : Fin 10) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 10) (i : Fin 10) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 10) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 10) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 10) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 10) (i : Fin 10) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 10) (i : Fin 10) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 36 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
      dlvN (re s i c1 c2) (nxt i).val + 1 ≤ c1.val + 8 ∧ dlvN (re s i c1 c2) (prv i).val + 1 ≤ c2.val + 8)
  else if rk s i c1 c2 = 1 then
    decide (c1.val ≤ 1 ∧ c2.val ≤ 1 ∧ 0 < r0 s i c1 c2 ∧
      r1 s i c1 c2 * (Ac i - Ac (nxt i)) + r2 s i c1 c2 * (Ac i - Ac (prv i)) = r0 s i c1 c2 * Ac i ∧
      r1 s i c1 c2 * (Bc i - Bc (nxt i)) + r2 s i c1 c2 * (Bc i - Bc (prv i)) = r0 s i c1 c2 * Bc i ∧
      r1 s i c1 c2 * ((c1.val : ℤ) - (Cc s i - Cc s (nxt i))) +
        r2 s i c1 c2 * ((c2.val : ℤ) - (Cc s i - Cc s (prv i))) + r0 s i c1 c2 * Cc s i ≤ r0 s i c1 c2 * 9)
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
theorem far_cert (s : Fin 10) (i j : Fin 10) (hij : nonadj i j) : farCert s i j := by
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

theorem edge_at (p : ℕ) (hp : p < 36) :
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

theorem edge_tab (p : ℕ) (hp : p < 36) :
    (E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ) := by
  have h := tables_ok.2.2.1
  unfold dlOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h p hp).1

theorem point_contra (x y : ℤ) (s : Fin 10) (i : Fin 10) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
    (ha : u1 * (Ac i - Ac (nxt i)) + u2 * (Ac i - Ac (prv i)) = u0 * Ac i)
    (hb : u1 * (Bc i - Bc (nxt i)) + u2 * (Bc i - Bc (prv i)) = u0 * Bc i)
    (hc : u1 * (c1 - (Cc s i - Cc s (nxt i))) + u2 * (c2 - (Cc s i - Cc s (prv i))) + u0 * Cc s i ≤ u0 * 9)
    (e1 : pot (x, y, s) i - pot (x, y, s) (nxt i) = c1) (e2 : pot (x, y, s) i - pot (x, y, s) (prv i) = c2)
    (hF : 9 < pot (x, y, s) i) : False := by
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

/-- Beyond F = 9 every vertex has a neighbor where F is one less. -/
theorem far_step (s : Fin 10) (i : Fin 10) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
    (hF : 9 < F (x, y, s)) : ∃ w, G.Adj (x, y, s) w ∧ F w + 1 = F (x, y, s) := by
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
  · -- a corner point within F ≤ 9
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

theorem far_desc (v : V) (hF : 9 < F v) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨i, hi⟩ := exists_F (x, y, s)
  exact far_step s i x y hi hF

/-- Three bounds pot a_k ≤ t and one linear fact px x + py y + q ≤ 0 at (x, y, s), with
multipliers whose x and y parts cancel and whose constants add up to a positive number, cannot
hold together. -/
theorem farkas_ub (x y : ℤ) (s : Fin 10) (a1 a2 a3 : Fin 10) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 10, 0 < 4 * (Cc s 0 - 9) + 4 * (Cc s 9 - 9) + 0 * (Cc s 0 - 9) + 16 * 6 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 10, 0 < 7 * (Cc s 4 - 9) + 4 * (Cc s 6 - 9) + 0 * (Cc s 0 - 9) + 18 * 6 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 10, 0 < 1 * (Cc s 2 - 9) + 0 * (Cc s 0 - 9) + 0 * (Cc s 0 - 9) + 8 * 3 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 10, 0 < 1 * (Cc s 7 - 9) + 0 * (Cc s 0 - 9) + 0 * (Cc s 0 - 9) + 8 * 3 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 10, 0 < 2 * (Cc s 4 - (-1)) + 2 * (Cc s 9 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 9 lies in the cells |x| ≤ 5, |y| ≤ 2 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 10) (hF : F (x, y, s) ≤ 9) :
    -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 9 0 9 4 4 0 1 0 6 16 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 4 6 0 9 7 4 0 (-1) 0 6 18 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 0 0 9 1 0 0 0 1 3 8 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 7 0 0 9 1 0 0 0 (-1) 3 8 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 4 9 0 (-1) 2 2 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 5, b - 2) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 84734221114757256434504731341547793447522007548975363132282939715633567973483844660785959033865709181936107382082180972139523267506500977223553853284089100681584002550299696002400724952900202861226287911866968023955629712463800666174070510547220036203422420692812208667472769248348882899490449801447881287756212153222310400364187852137359320772837609629764096306408387167280938387119162782131335902281189679847911543912668343581631687261428236755633822808418526097608575871973681371477509194219926686878801537427523678863948089920589137825216856637997487744868947497253150866097691738454498898338857728545691560275103310277026021886340108451675146469410195201891339940709661376338704252118487598652696771105538182784114691639058598868929267340355666264285610690872989237339336689911528055627461609930389138311431437330879513679542531670463250829361930449065082880 >>> (6 * ((a * 5 + b) * 10 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 5, b - 2) and class s, potential i plus
19 + 2 a + 8 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 10) : ℕ :=
  tgetN 1171590842400 5 i.val * a + tgetN 439271408304164 5 i.val * b + tgetN 1373812309442792978964211422973673676781763893355539526697391863211037821025603674444406839995056661433674847870035638668495082028441723132478204504753128656335081001928969526852005 6 (s * 10 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)) (fnt a b s 8)) (fnt a b s 9)

theorem fnt_tab : ∀ s : Fin 10, ∀ i : Fin 10, (tgetN 1171590842400 5 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 439271408304164 5 i.val : ℤ) = Bc i + 8 ∧
    (tgetN 1373812309442792978964211422973673676781763893355539526697391863211037821025603674444406839995056661433674847870035638668495082028441723132478204504753128656335081001928969526852005 6 (s.val * 10 + i.val) : ℤ) = Cc s i - Ac i * 5 - Bc i * 2 + 19 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 10) (i : Fin 10) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 5, (b : ℤ) - 2, s) i + (19 + 2 * a + 8 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 10) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 5, (b : ℤ) - 2, s) + (19 + 2 * a + 8 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 9, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 8) 1 = FN + 2 dx' + 8 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 11).all fun a => (List.range 5).all fun b => (List.range 10).all fun s =>
    Nat.blt (28 + 2 * a + 8 * b) (FN a b s) || (a == 5 && b == 2 && s == 0) ||
      (Nat.blt (hint a b s) 36 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 10 ==
          FN a b s + 2 * dxv (hint a b s) + 8 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 9) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  obtain ⟨x, y, s⟩ := v
  obtain ⟨hx1, hx2, hy1, hy2⟩ := near_box x y s hF
  have h := nearOK_eq
  unfold nearOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (x + 5).toNat (by omega) (y + 2).toNat (by omega) s.val s.isLt
  have ex : (((x + 5).toNat : ℕ) : ℤ) - 5 = x := by omega
  have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by omega
  generalize (x + 5).toNat = a at h' ex
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
    have hs0 : s = 0 := Fin.ext (by rw [h3]; rfl)
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
    have cw2 : (((b + dyv (hint a b s.val) - 1 : ℕ) : ℤ)) - 2 = y + dy := by omega
    rw [cw1, cw2] at fw
    have cf := congrArg (Nat.cast : ℕ → ℤ) hfe
    push_cast at cf
    omega

theorem desc (v : V) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
  by_cases hF : F v ≤ 9
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
quotients (`cnt_eq_S`), and shifting n by 40 moves every quotient by an integer (`inner_shift`,
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
def AW (i : ℕ) : ℕ := tgetN 509642516513262 5 i

def BW (i : ℕ) : ℕ := tgetN 729826222973228 5 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem A_W (i : Fin 10) : Ac i = (AW i.val : ℤ) - 16 := rfl

theorem B_W (i : Fin 10) : Bc i = (BW i.val : ℤ) - 16 := rfl

theorem C_W (s : Fin 10) (i : Fin 10) : Cc s i = (CW s.val i.val : ℤ) - 16 := rfl

def gcV (k : ℕ) : ℕ := ctabN 143900416018 4 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 10) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 27280 2 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 1

def Ap (i : Fin 10) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 680996963845 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 7

def Bp (i : Fin 10) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 551056 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 10) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 627781 2 k

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
def par (s : Fin 10) (i : Fin 10) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 10) (i j : Fin 10) (c u : ℤ) :
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

theorem par_inj (s : Fin 10) (i : Fin 10) (c : ℤ) : Function.Injective (par s i c) := by
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

def cf1V (k : ℕ) : ℕ := ctabN 5339029594970769155768870001232702009027812838877052597888657532165292787818724186410079111916390181999629737314619392 4 k

def cf2V (k : ℕ) : ℕ := ctabN 677270831186294784598088659964976355911773667202625168866722389636255811959560930163492807171860947988817513126852608 4 k

def cf3V (k : ℕ) : ℕ := ctabN 17540524376543371092934224170702913501669941373139683646872353395015222441551377736709952 3 k

def cf0V (k : ℕ) : ℕ := ctabN 7092389955401369837438771032310427106797582370032322701904 2 k

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
def certC (s : Fin 10) (i j : Fin 10) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (5 - Cc s i)

/-- j is i or a neighbour of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := Nat.beq j i || Nat.beq j (nextF i) || Nat.beq j (prevF i)

/-- certG in natural numbers: Ac = AW - 16, Bc = BW - 16, the negative terms moved across. -/
def certGN (i j : ℕ) : Bool :=
  Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (AW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (AW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (AW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 16))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 10 i))) (cf2V (Nat.add j (Nat.mul 10 i)))) (cf0V (Nat.add j (Nat.mul 10 i)))) (AW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (AW j))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (BW (prevF i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (BW (nextF i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (BW i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 16))
      (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 10 i))) (cf2V (Nat.add j (Nat.mul 10 i)))) (cf0V (Nat.add j (Nat.mul 10 i)))) (BW i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (BW j)))

/-- certC in natural numbers: Cc = CW - 16, the negative terms moved across. -/
def certCN (s i j : ℕ) : Bool :=
  Nat.blt (Nat.add (Nat.mul (Nat.add (Nat.add (cf1V (Nat.add j (Nat.mul 10 i))) (cf2V (Nat.add j (Nat.mul 10 i)))) (cf0V (Nat.add j (Nat.mul 10 i)))) (CW s i)) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (CW s j)))
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 10 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 10 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 10 i))) 21))

def certGK : PLift ((allR 10 fun i => allR 10 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 10 fun i => allR 10 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 10 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 10) : certS s = true := by
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
theorem certC_ok (s : Fin 10) (i j : Fin 10) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
def lev (s : Fin 10) (i : Fin 10) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 10) (i : Fin 10) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 10) (i j : Fin 10) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 10) (i : Fin 10) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 10) (i : Fin 10) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 10) (i j : Fin 10) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 10) (i : Fin 10) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 10) (i : Fin 10) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 10) (i : Fin 10) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 5 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 10) (i : Fin 10) (n u : ℤ) (hn : 5 ≤ n)
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

/-- The class constants lie in [-7, 7]: a natural-number check. -/
def cbK : PLift ((allR 10 fun s => allR 10 fun i => Nat.ble (CW s i) 23 && Nat.ble 16 (Nat.add (CW s i) 7)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 10) (j : Fin 10) : -7 ≤ Cc s j ∧ Cc s j ≤ 7 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 7)) (1 * n + 7) ×ˢ
    (Finset.Icc (-(1 * n + 7)) (1 * n + 7) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (1 * Ac 4 + 1 * Ac 5 = 4 ∧ 1 * Bc 4 + 1 * Bc 5 = 0 ∧
    1 * Ac 0 + 1 * Ac 9 = (-4) ∧ 1 * Bc 0 + 1 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 8 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-8)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 1 * Ac 4 + 1 * Ac 5 = 4 ∧ 1 * Bc 4 + 1 * Bc 5 = 0 ∧
    1 * Ac 0 + 1 * Ac 9 = (-4) ∧ 1 * Bc 0 + 1 * Bc 9 = 0 ∧
    1 * Ac 7 + 0 * Ac 7 = 0 ∧ 1 * Bc 7 + 0 * Bc 7 = 8 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-8) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 10) :
    4 * x ≤ 2 * F (x, y, s) + 14 ∧
    4 * (-x) ≤ 2 * F (x, y, s) + 14 ∧
    8 * y ≤ 1 * F (x, y, s) + 7 ∧
    8 * (-y) ≤ 1 * F (x, y, s) + 7 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 1 * pot (x, y, s) 4 + 1 * pot (x, y, s) 5 =
      4 * x + 1 * Cc s 4 + 1 * Cc s 5 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 4
  have r0 := le_F (x, y, s) 5
  have k0 := Cbound s 4
  have l0 := Cbound s 5
  have e1 : 1 * pot (x, y, s) 0 + 1 * pot (x, y, s) 9 =
      4 * (-x) + 1 * Cc s 0 + 1 * Cc s 9 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 9
  have k1 := Cbound s 0
  have l1 := Cbound s 9
  have e2 : 1 * pot (x, y, s) 7 + 0 * pot (x, y, s) 7 =
      8 * y + 1 * Cc s 7 + 0 * Cc s 7 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 7
  have r2 := le_F (x, y, s) 7
  have k2 := Cbound s 7
  have l2 := Cbound s 7
  have e3 : 1 * pot (x, y, s) 2 + 0 * pot (x, y, s) 2 =
      8 * (-y) + 1 * Cc s 2 + 0 * Cc s 2 := by
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
noncomputable def PF (s : Fin 10) (i : Fin 10) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 10) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) :
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
def inner (s : Fin 10) (i : Fin 10) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 10) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 10 × Fin 10, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 10 × Fin 10, inner p.1 p.2 n

/-! Shifting n by 40 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 371571730090580500 6 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 10) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 23824721171856 5 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 16

def mh (i : Fin 10) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 844744125064488 5 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 4

def mk (i : Fin 10) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 10, (40 : ℤ) = gc i * Lq i ∧ 40 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 40 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 10, (40 : ℤ) = gc i * Lq i ∧ 40 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 40 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 10) (i : Fin 10) (n : ℤ) :
    inner s i (n + 40) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 40 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 40 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 40) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 40) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 40) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
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
  ∑ q : Fin 10 × Fin 10, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 40) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 40 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 40 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 5 + r with r < 40: the level is QQ - 1 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 396 1 k

def uhMV (k : ℕ) : ℕ := ctabN 537149448 3 k

def ukPV (k : ℕ) : ℕ := ctabN 550042599697 4 k

def ukMV (k : ℕ) : ℕ := ctabN 264 1 k

def dhV (k : ℕ) : ℕ := ctabN 378402079144 4 k

def dkV (k : ℕ) : ℕ := ctabN 593113948549 4 k

def mhkV (k : ℕ) : ℕ := ctabN 281878469140 4 k

def uh (i : Fin 10) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 10) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 10) : ℤ := dhV i.val

def dk (i : Fin 10) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 10, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 262656606805330523309492221288324557303518033693616425422081643383410702511894180933964097 3 (Nat.add i (Nat.mul 10 s))

def QQ (s i : ℕ) : ℕ := ctabN 525273610104719446534054744782036166100195017979251606206837561588185627187122514243056076586720187805120944166902391139 4 (Nat.add i (Nat.mul 10 s))

def AH (s i : ℕ) : ℕ := ctabN 655967590877314332885179707174052075312282255502463989805172649061797216209430794923025702792458352139016366096280272960 4 (Nat.add i (Nat.mul 10 s))

def AK (s i : ℕ) : ℕ := ctabN 1767864977311430101813906763195082265318418254021981444286657887230622225162753754559972739827542807764297418473016442461538045005972597851365535023266 5 (Nat.add i (Nat.mul 10 s))

def WH (s i : ℕ) : ℕ := ctabN 1943691233009651973539250241949419004413655292642574517862053981871050691437725302249671608579754111134786039755879976668442819480871670936940394316960 5 (Nat.add i (Nat.mul 10 s))

def WK (s i : ℕ) : ℕ := ctabN 159148292441937912457936374395407232460924505838442293821225154878212133297769634672413184 3 (Nat.add i (Nat.mul 10 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 10 fun s => allR 10 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq (Nat.add 21 (gcV i)) (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (uhPV i)) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (uhMV i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (ukPV i)) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (ukMV i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 10) (i : Fin 10) :
    PP s.val i.val < gcV i.val ∧
    (5 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 1) + PP s.val i.val ∧
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

theorem div_nat (s : Fin 10) (i : Fin 10) (r : ℕ) :
    ((5 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (5 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 1) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 10) (i : Fin 10) (r : ℕ) (hr : r < 40) :
    inner s i ((5 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (40 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 40 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((5 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 1) + tauN s.val i.val r := by
      rw [lev, show (5 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 1) + tauN s.val i.val r) by
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

def dtabV (k : ℕ) : ℕ := ctabN 993176550300 5 k

def tblV (k : ℕ) : ℕ := ctabN 989708397763 5 k

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

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 40) = b n + 5 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 40 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 40 - 1 = n - 1 + 8 * 5 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 8)]
  ring

/-- b on the residue class of 1 + j mod 8. -/
theorem b_res (k j : ℕ) (hj : j < 8) : b (8 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (8 * k + (1 + j) < 1) by omega),
    show 8 * k + (1 + j) - 1 = j + 8 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 8), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 5 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 40 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 10 fun s => allR 10 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 10 fun s => sumR 10 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 5 r)) &&
    Nat.beq (sumR 10 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 5 (dv (Nat.add 4 r)))

/-! The window n = 5, ..., 44, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 15 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 15 15 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 30 10 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 40) :
    (∀ s, s < 10 → ∀ i, i < 10 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 10 fun s => sumR 10 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (5 + r) ∧
    (sumR 10 fun s => sumR 10 fun i => cond (divN s i r) (mhkV i) 0) = 5 * dv (4 + r) := by
  have h : periodR r = true := by
    rcases (show r < 15 ∨ (15 ≤ r ∧ r < 30) ∨ 30 ≤ r by omega) with h | h | h
    · exact allI_get _ _ _ periodK0.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK1.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK2.down r (by omega) (by omega)
  simp only [periodR, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun s hs i hi hd => ?_, h2, h3⟩
  have h4 := (allR_iff _ _).1 ((allR_iff _ _).1 h1 s hs) i hi
  rw [hd] at h4
  simpa using h4

theorem innerZ_eq (s i r : ℕ) (hs : s < 10) (hi : i < 10) (hr : r < 40) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 10 fun s => sumR 10 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 10 × Fin 10, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 10 fun i => f s i : ℕ) : ℤ)) 10]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 10]

theorem S_window (r : ℕ) (hr : r < 40) : S ((5 : ℤ) + r) = b (5 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 40) : Gs ((5 : ℤ) + r) = ((5 * dv (4 + r) : ℕ) : ℤ) := by
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
theorem inner_nonneg (s : Fin 10) (i : Fin 10) (n : ℤ) (hn : 5 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 5 + t := ⟨(n - 5).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 40
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 40) (by omega) (by omega)
      have e : (5 : ℤ) + t = (5 + (t - 40 : ℕ)) + 40 := by
        push_cast [Nat.cast_sub (by omega : 40 ≤ t)]; ring
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

/-- The growth of b over 40 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 5 ≤ n) : (5 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 5) % 40 < 40 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((5 : ℤ) + (((n - 5) % 40 : ℕ) : ℤ)) + 40 * (((n - 5) / 40 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (4 + (n - 5) % 40) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 5 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 45
    · obtain ⟨r, rfl⟩ : ∃ r, n = 5 + r := ⟨n - 5, by omega⟩
      push_cast
      exact S_window r (by omega)
    · have h1 := ih (n - 40) (by omega) (by omega)
      have h2 := S_shift ((n - 40 : ℕ) : ℤ)
      have h3 := b_shift (n - 40) (by omega)
      have h4 := grow (n - 40) (by omega)
      rw [show n - 40 + 40 = n by omega] at h3
      rw [show ((n - 40 : ℕ) : ℤ) + 40 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 4 lie in the box -5 ≤ x ≤ 5, -1 ≤ y ≤ 1 (`small_box`). In natural-number
coordinates a = x + 5, b = y + 1 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 10) (h : F (x, y, s) ≤ 4) :
    -5 ≤ x ∧ x ≤ 5 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 5, (b : ℤ) - 1, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 96) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 5) (BW i)) 16) (Nat.add (Nat.mul 16 a) (Nat.mul 16 b))

theorem pot_box (a b : ℕ) (s : Fin 10) (i : Fin 10) :
    pot ((a : ℤ) - 5, (b : ℤ) - 1, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 10 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 10) : F ((a : ℤ) - 5, (b : ℤ) - 1, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 5, (b : ℤ) - 1, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 5, (b : ℤ) - 1, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 10 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 10 fun i => PtN i a b s.val - NtN i a b) ≤
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
  sumR 11 fun a => sumR 3 fun b => sumR 10 fun s => cond (Nat.beq (FN a b s) f) 1 0

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
def ib (q : ℕ × ℕ × Fin 10) : V := ((q.1 : ℤ) - 5, (q.2.1 : ℤ) - 1, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 4) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 11 ×ˢ (Finset.range 3 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 10 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 10]
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
n + 8, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
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

/-- The step a(n + 8) = a(n) + dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 8) = a n + dv (n - 1) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 28 ∧ tblV 0 = 3 ∧ dv 1 = 28 ∧ tblV 1 = 6 ∧ dv 2 = 30 ∧ tblV 2 = 11 ∧ dv 3 = 30 ∧ tblV 3 = 15 ∧ dv 4 = 30 ∧ tblV 4 = 19 ∧ dv 5 = 30 ∧ tblV 5 = 23 ∧ dv 6 = 28 ∧ tblV 6 = 25 ∧ dv 7 = 28 ∧ tblV 7 = 28) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (8 * k + 1) = 28 * k + 3 ∧
    a (8 * k + 2) = 28 * k + 6 ∧
    a (8 * k + 3) = 30 * k + 11 ∧
    a (8 * k + 4) = 30 * k + 15 ∧
    a (8 * k + 5) = 30 * k + 19 ∧
    a (8 * k + 6) = 30 * k + 23 ∧
    a (8 * k + 7) = 28 * k + 25 ∧
    a (8 * k + 8) = 28 * k + 28 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 8 * k + 1 = 8 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 8 * k + 2 = 8 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 8 * k + 3 = 8 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 8 * k + 4 = 8 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 8 * k + 5 = 8 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 8 * k + 6 = 8 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 8 * k + 7 = 8 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 8 * k + 8 = 8 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

/-- The closed form per residue of n mod 8, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (8 * k + 1) = 28 * k + 3 ∧
    a (8 * k + 2) = 28 * k + 6 ∧
    a (8 * k + 3) = 30 * k + 11 ∧
    a (8 * k + 4) = 30 * k + 15 ∧
    a (8 * k + 5) = 30 * k + 19 ∧
    a (8 * k + 6) = 30 * k + 23 ∧
    a (8 * k + 7) = 28 * k + 25 ∧
    a (8 * k + 8) = 28 * k + 28 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩

def controlsK : PLift ((List.range 50).map b = [1, 3, 6, 11, 15, 19, 23, 25, 28, 31, 34, 41, 45, 49, 53, 53, 56, 59, 62, 71, 75, 79, 83, 81, 84, 87, 90, 101, 105, 109, 113, 109, 112, 115, 118, 131, 135, 139, 143, 137, 140, 143, 146, 161, 165, 169, 173, 165, 168, 171]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 3, 6, 11, 15, 19, 23, 25, 28, 31, 34, 41, 45, 49, 53, 53, 56, 59, 62, 71, 75, 79, 83, 81, 84, 87, 90, 101, 105, 109, 113, 109, 112, 115, 118, 131, 135, 139, 143, 137, 140, 143, 146, 161, 165, 169, 173, 165, 168, 171] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 8 → dv (t + 13) + dv (t + 9) + dv (t + 4) + dv (t + 0) = dv (t + 12) + dv (t + 8) + dv (t + 5) + dv (t + 1)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 8 → dv (t + 13) + dv (t + 9) + dv (t + 4) + dv (t + 0) = dv (t + 12) + dv (t + 8) + dv (t + 5) + dv (t + 1) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 13) : ℤ) = (dv (t + 12) : ℤ) - (dv (t + 9) : ℤ) + (dv (t + 8) : ℤ) + (dv (t + 5) : ℤ) - (dv (t + 4) : ℤ) + (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 8 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 4, e 5, e 8, e 9, e 12, e 13]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 8) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 8 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 8 → b (q + 14) + b (q + 10) + b (q + 5) + b (q + 1) = b (q + 13) + b (q + 9) + b (q + 6) + b (q + 2)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 8 → b (q + 14) + b (q + 10) + b (q + 5) + b (q + 1) = b (q + 13) + b (q + 9) + b (q + 6) + b (q + 2) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 14) : ℤ) = b (q + 13) - b (q + 10) + b (q + 9) + b (q + 6) - b (q + 5) + b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 8 ∨ 8 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 8 := ⟨q - 8, by omega⟩
      have h0 : (b (v + 14) : ℤ) = b (v + 13) - b (v + 10) + b (v + 9) + b (v + 6) - b (v + 5) + b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 9) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 8 = v + 9 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s2 : (b (v + 10) : ℤ) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (le_trans (by decide : 1 ≤ 2) (Nat.le_add_left _ v))
        rw [show v + 2 + 8 = v + 10 from Nat.add_assoc _ _ _,
          show v + 2 - 1 = v + 1 from Nat.add_sub_assoc (by decide : 1 ≤ 2) v] at h
        exact_mod_cast h
      have s5 : (b (v + 13) : ℤ) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (le_trans (by decide : 1 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 8 = v + 13 from Nat.add_assoc _ _ _,
          show v + 5 - 1 = v + 4 from Nat.add_sub_assoc (by decide : 1 ≤ 5) v] at h
        exact_mod_cast h
      have s6 : (b (v + 14) : ℤ) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (le_trans (by decide : 1 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 8 = v + 14 from Nat.add_assoc _ _ _,
          show v + 6 - 1 = v + 5 from Nat.add_sub_assoc (by decide : 1 ≤ 6) v] at h
        exact_mod_cast h
      have s9 : (b (v + 17) : ℤ) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (le_trans (by decide : 1 ≤ 9) (Nat.le_add_left _ v))
        rw [show v + 9 + 8 = v + 17 from Nat.add_assoc _ _ _,
          show v + 9 - 1 = v + 8 from Nat.add_sub_assoc (by decide : 1 ≤ 9) v] at h
        exact_mod_cast h
      have s10 : (b (v + 18) : ℤ) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (le_trans (by decide : 1 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 8 = v + 18 from Nat.add_assoc _ _ _,
          show v + 10 - 1 = v + 9 from Nat.add_sub_assoc (by decide : 1 ≤ 10) v] at h
        exact_mod_cast h
      have s13 : (b (v + 21) : ℤ) = b (v + 13) + dv (v + 12) := by
        have h := b_step (v + 13) (le_trans (by decide : 1 ≤ 13) (Nat.le_add_left _ v))
        rw [show v + 13 + 8 = v + 21 from Nat.add_assoc _ _ _,
          show v + 13 - 1 = v + 12 from Nat.add_sub_assoc (by decide : 1 ≤ 13) v] at h
        exact_mod_cast h
      have s14 : (b (v + 22) : ℤ) = b (v + 14) + dv (v + 13) := by
        have h := b_step (v + 14) (le_trans (by decide : 1 ≤ 14) (Nat.le_add_left _ v))
        rw [show v + 14 + 8 = v + 22 from Nat.add_assoc _ _ _,
          show v + 14 - 1 = v + 13 from Nat.add_sub_assoc (by decide : 1 ≤ 14) v] at h
        exact_mod_cast h
      show (b (v + 22) : ℤ) = b (v + 21) - b (v + 18) + b (v + 17) + b (v + 14) - b (v + 13) + b (v + 10) - b (v + 9)
      linear_combination s14 - (1) * s13 - (-1) * s10 - (1) * s9 - (1) * s6 - (-1) * s5 - (1) * s2 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 13 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + a (n - 5) + a (n - 8) - a (n - 9) + a (n - 12) - a (n - 13) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 14 := ⟨n - 14, by omega⟩
  rw [show q + 14 - 1 = q + 13 from Nat.add_sub_assoc (by decide : 1 ≤ 14) q, show q + 14 - 4 = q + 10 from Nat.add_sub_assoc (by decide : 4 ≤ 14) q, show q + 14 - 5 = q + 9 from Nat.add_sub_assoc (by decide : 5 ≤ 14) q, show q + 14 - 8 = q + 6 from Nat.add_sub_assoc (by decide : 8 ≤ 14) q, show q + 14 - 9 = q + 5 from Nat.add_sub_assoc (by decide : 9 ≤ 14) q, show q + 14 - 12 = q + 2 from Nat.add_sub_assoc (by decide : 12 ≤ 14) q, show q + 14 - 13 = q + 1 from Nat.add_sub_assoc (by decide : 13 ≤ 14) q]
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

/-- The coefficients of A * DEN and NUM agree below 14, in natural numbers (negative terms moved
across). -/
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (b n) (bk n 4)) (bk n 9)) (bk n 13)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (bk n 1) (bk n 5)) (bk n 8)) (bk n 12)) (ind n 0)) (Nat.mul 2 (ind n 1))) (Nat.mul 3 (ind n 2))) (Nat.mul 5 (ind n 3))) (Nat.mul 5 (ind n 4))) (Nat.mul 6 (ind n 5))) (Nat.mul 7 (ind n 6))) (Nat.mul 7 (ind n 7))) (Nat.mul 6 (ind n 8))) (Nat.mul 5 (ind n 9))) (Nat.mul 4 (ind n 10))) (Nat.mul 4 (ind n 11))) (Nat.mul 2 (ind n 12))) (ind n 13)

def gfK : PLift ((allR 14 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 14, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 14) :
    1 * (b (n) : ℚ) - 1 * (if 1 ≤ n then (b (n - 1) : ℚ) else 0) + 1 * (if 4 ≤ n then (b (n - 4) : ℚ) else 0) - 1 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) - 1 * (if 8 ≤ n then (b (n - 8) : ℚ) else 0) + 1 * (if 9 ≤ n then (b (n - 9) : ℚ) else 0) - 1 * (if 12 ≤ n then (b (n - 12) : ℚ) else 0) + 1 * (if 13 ≤ n then (b (n - 13) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 2 + (if n = 2 then (1 : ℚ) else 0) * 3 + (if n = 3 then (1 : ℚ) else 0) * 5 + (if n = 4 then (1 : ℚ) else 0) * 5 + (if n = 5 then (1 : ℚ) else 0) * 6 + (if n = 6 then (1 : ℚ) else 0) * 7 + (if n = 7 then (1 : ℚ) else 0) * 7 + (if n = 8 then (1 : ℚ) else 0) * 6 + (if n = 9 then (1 : ℚ) else 0) * 5 + (if n = 10 then (1 : ℚ) else 0) * 4 + (if n = 11 then (1 : ℚ) else 0) * 4 + (if n = 12 then (1 : ℚ) else 0) * 2 + (if n = 13 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 14 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 14) : ℚ) - 1 * (if 1 ≤ q + 14 then (b (q + 14 - 1) : ℚ) else 0) + 1 * (if 4 ≤ q + 14 then (b (q + 14 - 4) : ℚ) else 0) - 1 * (if 5 ≤ q + 14 then (b (q + 14 - 5) : ℚ) else 0) - 1 * (if 8 ≤ q + 14 then (b (q + 14 - 8) : ℚ) else 0) + 1 * (if 9 ≤ q + 14 then (b (q + 14 - 9) : ℚ) else 0) - 1 * (if 12 ≤ q + 14 then (b (q + 14 - 12) : ℚ) else 0) + 1 * (if 13 ≤ q + 14 then (b (q + 14 - 13) : ℚ) else 0) =
      (if q + 14 = 0 then (1 : ℚ) else 0) * 1 + (if q + 14 = 1 then (1 : ℚ) else 0) * 2 + (if q + 14 = 2 then (1 : ℚ) else 0) * 3 + (if q + 14 = 3 then (1 : ℚ) else 0) * 5 + (if q + 14 = 4 then (1 : ℚ) else 0) * 5 + (if q + 14 = 5 then (1 : ℚ) else 0) * 6 + (if q + 14 = 6 then (1 : ℚ) else 0) * 7 + (if q + 14 = 7 then (1 : ℚ) else 0) * 7 + (if q + 14 = 8 then (1 : ℚ) else 0) * 6 + (if q + 14 = 9 then (1 : ℚ) else 0) * 5 + (if q + 14 = 10 then (1 : ℚ) else 0) * 4 + (if q + 14 = 11 then (1 : ℚ) else 0) * 4 + (if q + 14 = 12 then (1 : ℚ) else 0) * 2 + (if q + 14 = 13 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 14) : ℤ) = b (q + 13) - b (q + 10) + b (q + 9) + b (q + 6) - b (q + 5) + b (q + 2) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 14 - 1 = q + 13 from Nat.add_sub_assoc (by decide : 1 ≤ 14) q, show q + 14 - 4 = q + 10 from Nat.add_sub_assoc (by decide : 4 ≤ 14) q, show q + 14 - 5 = q + 9 from Nat.add_sub_assoc (by decide : 5 ≤ 14) q, show q + 14 - 8 = q + 6 from Nat.add_sub_assoc (by decide : 8 ≤ 14) q, show q + 14 - 9 = q + 5 from Nat.add_sub_assoc (by decide : 9 ≤ 14) q, show q + 14 - 12 = q + 2 from Nat.add_sub_assoc (by decide : 12 ≤ 14) q, show q + 14 - 13 = q + 1 from Nat.add_sub_assoc (by decide : 13 ≤ 14) q, show 1 ≤ q + 14 from le_trans (by decide : 1 ≤ 14) (Nat.le_add_left 14 q), show 4 ≤ q + 14 from le_trans (by decide : 4 ≤ 14) (Nat.le_add_left 14 q), show 5 ≤ q + 14 from le_trans (by decide : 5 ≤ 14) (Nat.le_add_left 14 q), show 8 ≤ q + 14 from le_trans (by decide : 8 ≤ 14) (Nat.le_add_left 14 q), show 9 ≤ q + 14 from le_trans (by decide : 9 ≤ 14) (Nat.le_add_left 14 q), show 12 ≤ q + 14 from le_trans (by decide : 12 ≤ 14) (Nat.le_add_left 14 q), show 13 ≤ q + 14 from le_trans (by decide : 13 ≤ 14) (Nat.le_add_left 14 q), show ¬ q + 14 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 14) (Nat.le_add_left 14 q)), show ¬ q + 14 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 14) (Nat.le_add_left 14 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X ^ 4) ^ 2) = C 1 * A - C 1 * (A * X ^ 1) + C 1 * (A * X ^ 4) - C 1 * (A * X ^ 5) - C 1 * (A * X ^ 8) + C 1 * (A * X ^ 9) - C 1 * (A * X ^ 12) + C 1 * (A * X ^ 13) := by
  simp only [map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (1 + 2 * X + 3 * X ^ 2 + 5 * X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 + 7 * X ^ 6 + 7 * X ^ 7 + 6 * X ^ 8 + 5 * X ^ 9 + 4 * X ^ 10 + 4 * X ^ 11 + 2 * X ^ 12 + X ^ 13 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 2 + X ^ 2 * C 3 + X ^ 3 * C 5 + X ^ 4 * C 5 + X ^ 5 * C 6 + X ^ 6 * C 7 + X ^ 7 * C 7 + X ^ 8 * C 6 + X ^ 9 * C 5 + X ^ 10 * C 4 + X ^ 11 * C 4 + X ^ 12 * C 2 + X ^ 13 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X ^ 4) ^ 2) =
      1 + 2 * X + 3 * X ^ 2 + 5 * X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 + 7 * X ^ 6 + 7 * X ^ 7 + 6 * X ^ 8 + 5 * X ^ 9 + 4 * X ^ 10 + 4 * X ^ 11 + 2 * X ^ 12 + X ^ 13 := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  rw [gf_den A, gf_num]
  ext n
  have hc : ∀ k, coeff k A = (b k : ℚ) := fun k => by rw [hA, coeff_mk, a_eq_b]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 14 with hn | hn
  · linarith [gf_low n hn]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 14 := ⟨n - 14, by omega⟩
    linarith [gf_high q]

end Count

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X ^ 4) ^ 2) =
      1 + 2 * X + 3 * X ^ 2 + 5 * X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 + 7 * X ^ 6 + 7 * X ^ 7 + 6 * X ^ 8 + 5 * X ^ 9 + 4 * X ^ 10 + 4 * X ^ 11 + 2 * X ^ 12 + X ^ 13 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 13 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + a (n - 5) + a (n - 8) - a (n - 9) + a (n - 12) - a (n - 13) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 3, 6, 11, 15, 19, 23, 25, 28, 31, 34, 41, 45, 49, 53, 53, 56, 59, 62, 71, 75, 79, 83, 81, 84, 87, 90, 101, 105, 109, 113, 109, 112, 115, 118, 131, 135, 139, 143, 137, 140, 143, 146, 161, 165, 169, 173, 165, 168, 171] := Count.controls

/-- The step a(n + 8) = a(n) + Count.dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 8) = a n + Count.dv (n - 1) := Count.a_step n hn

/-- The closed form per residue of n mod 8, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (8 * k + 1) = 28 * k + 3 ∧
    a (8 * k + 2) = 28 * k + 6 ∧
    a (8 * k + 3) = 30 * k + 11 ∧
    a (8 * k + 4) = 30 * k + 15 ∧
    a (8 * k + 5) = 30 * k + 19 ∧
    a (8 * k + 6) = 30 * k + 23 ∧
    a (8 * k + 7) = 28 * k + 25 ∧
    a (8 * k + 8) = 28 * k + 28 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X ^ 4) ^ 2) =
      1 + 2 * X + 3 * X ^ 2 + 5 * X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 + 7 * X ^ 6 + 7 * X ^ 7 + 6 * X ^ 8 + 5 * X ^ 9 + 4 * X ^ 10 + 4 * X ^ 11 + 2 * X ^ 12 + X ^ 13 ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = a (n - 1) - a (n - 4) + a (n - 5) + a (n - 8) - a (n - 9) + a (n - 12) - a (n - 13) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a310100

theorem OMA.solution : type_of% @OMA.S_oeis_a310100.main :=
  OMA.S_oeis_a310100.conjecture
