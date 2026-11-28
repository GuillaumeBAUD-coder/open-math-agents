import OMAStatements.S_oeis_a314929

namespace OMA.S_oeis_a314929






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 10

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 2290649224
  | 1 => 2041223014
  | 2 => 2594797159
  | 3 => 2327479910
  | 4 => 2023331959
  | 5 => 2881119574
  | 6 => 2613802325
  | 7 => 3185267509
  | 8 => 2916901684
  | 9 => 2899010629
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 1754966134 4 8 i.val

def Bc (i : Fin 8) : ℤ := tget 3470475829 4 8 i.val

def Cc (s : Fin 10) (i : Fin 8) : ℤ := tget (CcT s.val) 4 8 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 8. -/
def AcN (i : ℕ) : ℕ := tgetN 1754966134 4 i

def BcN (i : ℕ) : ℕ := tgetN 3470475829 4 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem Ac_eq (i : Fin 8) : Ac i = (AcN i.val : ℤ) - 8 := rfl

theorem Bc_eq (i : Fin 8) : Bc i = (BcN i.val : ℤ) - 8 := rfl

theorem Cc_eq (s : Fin 10) (i : Fin 8) : Cc s i = (CcN s.val i.val : ℤ) - 8 := rfl


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
theorem cls (P : Fin 10 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 10 × Fin 10 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
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
theorem shift (x y : ℤ) (e : Fin 10 × Fin 10 × ℤ × ℤ) (j : Fin 8) :
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
theorem farkas (x y : ℤ) (s : Fin 10) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
def fdN (i j f : ℕ) : ℕ := tgetN 31213268825068950337471045517902808692069003415960753011122533428764585666183798305632219932275246534072409382339317292259174754743794544874529202786938039189475947406454855556652821242599245999926822257549910617057582434367523897271605080590912028680522536906885606312840743165120088397179647504267254936986220246315991486031501563545020616076337271932497997754020794770470528360110051449861351318719493725681376264700702743900668027738338980542734378002096357753037104547656588011485540772538119509968329836125976454070730231430214911004405278785611354865664 5 ((i * 8 + j) * 6 + f)

def fd (i j : Fin 8) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 0 % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 1 % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 8 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 57468485348935423601299703775791025837499710249631744 4 p

def dstv (p : ℕ) : ℕ := tgetN 50657972896849638298404770331095616839129930452726849 4 p

def dxv (p : ℕ) : ℕ := tgetN 103238390021038209352427600 2 p

def dyv (p : ℕ) : ℕ := tgetN 103167578663153968774206485 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 3807250831500617092366453716358165248999942581295570260079919151316820650907465322604989969081520603815268425916635720640669622915251499472416905682142261905766065709190682231633675832409160400907916954301193254838308522231570381672695690937094851542015738363266093432308605611470327796033543732445689685606587068108276370457351727923130492725403846725674812600111774136688693846061573793624802023549119148515215011416143736 4 (p * 8 + j)

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
  (List.range 10).all fun s => (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 8, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 44).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 8).all fun j =>
      dlvN p j + 1 * AcN j + 8 * dxv p + 1 * BcN j + 8 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 16 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 10) (i j : Fin 8) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (15 - Cc s i)

/-- Beyond F = 14, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 10) (i j : Fin 8) (hc : farCert s i j) (x y : ℤ)
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
  | 0 => 10401192662967571427912689421907605103943176173850324541495243619565684895341841386127309648154634361709860193843622229353549509312786907130153197077059181969641476379304969577555034988595512292499942896582396545417291374401601629539817116342359919810447216527415263580814085008973378957702442845943526098354890793547218600367825291516266196166477252369983051222676242440478969167810133948221870631350585130712051613629308987665668243192401072506696324080953567376583482602509453551293261588538508953898993149495492635681765638983772931543869115228901135375831084061905666919019712408618451632870970684716392339637249760160605357690801996766924458404061905844856534190409554357645795738115397703288071692745842934009255139807476943395502665914188646517053730755898573572856562234363342475757899488485238420419351902481860880910774136381525004925848039986532944574202152495718559325228334801905356627609123823936
  | 1 => 10401192664769668970141298161095126912137814128140681702312005251497127405231719090051836585274772295306060746616510749021630735984012584647464793778084513112757517157405807466698042332058704709646779955480063581630368896857206332197117822849363561894190241298704208926296064412702447928128424287782941742462321320977151754643678255097800557981676207722585603163488500917360620574048182661505152632793262800337955089627840584525601562755232538237010855680118667572432180028717403579032079434346081004334645325944865903715140240323115165591634604099898487062459141648991046421253835737932274508700278000186797751320714412349434576739627094657857257885296019776900105424402881184728854123408734603228295924337016833081958482361207047299128690030926400982266154761395602657417067529673434495168643330473175515634363287981963849634780506073831038401999214477590998304929487836425652553979372785431082374898222604353
  | 2 => 10401192668373864054598515656142921783107438904195109475211423697908311151743067297586053995804751664017042941920579937413807902024658906236431436688199325143097241534515270573125188539275283126983660177405476970371847656390457822739085490309933666425391257669756343415061808564832457281163782268810217107233687352079385733964225543846530472741844437381033045684505936144495927349094619465084001849961076106838335307316114705878235949140624042527777361383695702525262593906408976353682268574844998476406862916422618015046623207337128090248825468258380473207234239233556518145553821245145252506168515429843796240719802689168489309022520593892469399400915373165599149362761640967780663358732968344253065986252859012019172296765187412693828578670133603052803790013449648587490857199266865380463879682769076504129632753075693299669451074095947980810938989232199046808527056506502400755166457988376766455201196646465
  | 3 => 10401192669575262416084254798928518483471301387394261774654878157456541023438268801151945306152443014053755819115607970664812717711525695279475337363956302253045262869730924598016364689650626056442295900972428716727959660737668116696086039874582996773359808410753061708709160601855289266969961783889964224158755209455469818437171192537006024041672390317676075244731155192629342275480296579733118087552883844721017853685976403692003567564670640989552135691609255932902206234864509673653405301116686832437493550292301286504485623937428765250383418370487268035535275491935529079683320858528880760637327394683311273037599652254351909643443022008353268932334504586922661043481765323812834787522038098182090075801317839742034521402496333709569683982463277554166356581148609863586518811160802259749075041590417420555758646569725926260069015611515510199508923858620381581843187456199321565763045231587994636091160274880
  | 4 => 10401192672578758319798602697574388308720990228216955418804620847091187325630838532735527734280372507454777186933241213214792930058591105002256678303805416723782768285064280449117322525657324876185819282759522699137224145850159278591422215130055892807732948892955264056424256535461521755367956387121726929016807719136596137491980189578551784660485781389239170174531966305827511055402828496612942464696918890862660515291994865321723553342101246973763971784732382186415736878908528199691201226286193159795300933725688080065255487216444487962825664415550328294793168446958871159714623668692952066813682795753540515454431582730957837390836147800725432620906162375472343559104326152060800595443213196857324293254250760099147402944956313638823733952991780182555256915715975783187841004186551434104600017653704509856674025412637098524340307239418740495960976110936659337195491942195224855989287187343622406895299698753
  | 5 => 10401192674981555042770081016491084001221474554068661725910746565194292371203816280986094420629425585751337708087542313319683816121072051424081398796030299998576345033162561197430219464422013391230571135903274643059873640902037384431881375342705488010658329244181538947009875463456540502674927282980807897335848381532947265058310074094736509737098524215897064058282192763969986731041294367363351165824165187350819541423370052148379676361012027010306180706926478629476853785766354378207895946289489060387858433460733284685529736620224192661830335883924623031635232872277689523033801136974152455809243600889309623674908366123074363315491714510530902147689982359189606166359283558455634504031368441761292016852596347437559137346281032705487383147764040292064179529589493030501228380292935640346831124985555561623361605985277511580117851619761812230391575870813773190669647103719383894675222018883242581220109033537
  | 6 => 10401192677384351765741559335407779786888218183695451762082183018173999178846950300649568296819488535953061676572250901771628673765781362104160396850323263912665028511693494024226164655668890289170013894913721396038072258779633528983734385707874599188900582567613431315385885868445557367578162471535438397965522842766559061754483861652726830952162710980898329809423599241047029122033849686263975741481893355872591761006284488831800424305867562319812656832025085966321342773436264156292871579559687473275459083191830256732977728542977277060211964931713432561577722162494711680971444405409124767277734181610461260686443905538445172888135564508881590463834776790602559490010091835212073415680832279049912186836927940029370765115931877169190115480925663128928941794276303486095162407762787119315280358891043518635658128993856797165170687144022961060695742701650572293316483623235707379931970217350032996537050607168
  | 7 => 10401192681589246030941646393511997442860439303457947321823876130158412665892825893400253832124119274215642910517206515030844707073288549892292172037489125843016048948946195624335311158319576962055570282309225562731976985639283316632467237646208843003180484233929451064151958510079919290964326670735313834000858758875771834060615016948130571076830672456848651468661726420946979214352775563423471907903662605512626659083025865515094546624974433502795482400775506015906455299508129589792521659053754710275050352893380686628134317222420788159698263424841505157197258929761310235114672612075221797185341866354630133957142304396668659567015888497415581599916219547289051811690286948840895747876689428371604592834249853446063024766601168447898329313466931808985858913031864800013167249861188329373421887961401125207193377835680243381799883539945882736214406007728654082362442867072177923918939142422275729585308147777
  | 8 => 10401192684592741934655994308830617497861624670073087328949595644831216995870290826998511017126152300941476443329464991402609855152418672156732259134897906790750873441982059136410801768384668628824710371525353396171258880037426261389054697465776645320029316289552925602645112741961284857953017323452321433653399121039130142914891806411561383888560030617623592473345435026796597411785979435720989317355309499775117541577606495847439160794763192728910612796319117955491656250535576157779465041816002452947023304229422333376214592151477719802772727161533143789644320320944619244158253193084474978034196084252575994771768415396389645913313208779029049067771014236831400822546709979816166056929231152415254314937897132409199496576379656241887437218917737766399705879662568698115243847566794045461937161539243709250354365527398712541945416120400114372372933630251976643436480537956314918347231030334956811439456662336
  | 9 => 10401192686394839476884603031345388983138506794781792027854933328314488687161894646881944919100808626159617744321127517958582271798233493531873103925451350157719719060177605808438238013474367360441573981754262801926396126633433645155408864695047350333635228446364057972878155256940105700936478935328821527278365620788708880375522246591931454839932893432317689412226796642710325384528287653293881670831611053406831620346510887256181863076261491630170200559150330827101046839546703031072761115643321414358717689031748344658824909131012775361978213737060870078748390951833303296656675917416825329141575267828390176250352754986016649928481497934484437213984713817765567352250468768113458898140289882811514066543223558233758712153406449316353139594086373937641690180462015743492191021742433365387481633747817712074662898773435808608056032007491428403026865162460690693007989964477358198838544272686007292022603620417
  | _ => 0

def rd (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 10) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 44 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
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
theorem far_cert (s : Fin 10) (i j : Fin 8) (hij : nonadj i j) : farCert s i j := by
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

theorem point_contra (x y : ℤ) (s : Fin 10) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
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
theorem far_step (s : Fin 10) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
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
theorem farkas_ub (x y : ℤ) (s : Fin 10) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 10, 0 < 4 * (Cc s 0 - 14) + 3 * (Cc s 7 - 14) + 0 * (Cc s 0 - 14) + 14 * 8 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 10, 0 < 3 * (Cc s 3 - 14) + 4 * (Cc s 4 - 14) + 0 * (Cc s 0 - 14) + 14 * 8 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 10, 0 < 1 * (Cc s 2 - 14) + 0 * (Cc s 0 - 14) + 0 * (Cc s 0 - 14) + 6 * 4 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 10, 0 < 1 * (Cc s 6 - 14) + 0 * (Cc s 0 - 14) + 0 * (Cc s 0 - 14) + 6 * 4 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 10, 0 < 2 * (Cc s 3 - (-1)) + 2 * (Cc s 7 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 14 lies in the cells |x| ≤ 7, |y| ≤ 3 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 10) (hF : F (x, y, s) ≤ 14) :
    -7 ≤ x ∧ x ≤ 7 ∧ -3 ≤ y ∧ y ≤ 3 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 7 0 14 4 3 0 1 0 8 14 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 4 0 14 3 4 0 (-1) 0 8 14 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 2 0 0 14 1 0 0 0 1 4 6 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 6 0 0 14 1 0 0 0 (-1) 4 6 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 3 7 0 (-1) 2 2 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 7, b - 3) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 1744912780928401837351003174435999455459140139581657028597684687245190452991106977349182447909801835858309888764538180375186786313550356134536536104386127322666349304108132073231643708901277958216630298096789172215212699112066577142582119984804707546577755759425391411267170269215289684746033404109253387500158196424664991306834208304807950393304396274563457394899470103464688575622416818563949984013491465103631299738064537666958779431292024703854207930624893186644941280483627957320245985861362538339239240736795882991510196915661636096641042446158281169157430045515382021508160631113205465904875913910631539173515965737558187697414072768564630531349115880847457264689637744917084166616203036716628120508501142196314430897924120982509086243217952635603469288681818808425083573683881681032082136912671373663273346043761603096346638587442450924368401176457952743066350435225465952457423442449349734213041023220804928691246443323259338775991838999559819494809066319441712789160197736618238373239915393122514220554829192238622581151102786697345437312991964176269151399128090953195144764723173076571547620324818700168435983804059485986487255609847189798295088729199186639844527038140611118858519325260539601139599622339412003438565160635104108160744285629613609342068062770211411598648357082715056869090913734170204787568036634432913935055781608889283930441720920272511517513018026578961385346984700728815566296968624652748799080840266146910970049510809903631706843266566579193988328206706870167501003749107484566542581299752614238843638137923772137340890912937514871414109148811645269664414486601597180773501544522687583998922433897107106749208319798790903229422422323403583180984564012789711033343853821997307072641710000718358366460070480180287644225112845441987525749826609078049029299101753851387107820219502903634622939136 >>> (6 * ((a * 7 + b) * 10 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 7, b - 3) and class s, potential i plus
23 + 2 a + 6 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 8) : ℕ :=
  tgetN 36979216 4 i.val * a + tgetN 2897813523 4 i.val * b + tgetN 1323907138234637833284707562731132171721881066364533656726820032491555787858891350257312863127843853678676247179584275428560482728357947399117678 6 (s * 8 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)

theorem fnt_tab : ∀ s : Fin 10, ∀ i : Fin 8, (tgetN 36979216 4 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 2897813523 4 i.val : ℤ) = Bc i + 6 ∧
    (tgetN 1323907138234637833284707562731132171721881066364533656726820032491555787858891350257312863127843853678676247179584275428560482728357947399117678 6 (s.val * 8 + i.val) : ℤ) = Cc s i - Ac i * 7 - Bc i * 3 + 23 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 10) (i : Fin 8) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 7, (b : ℤ) - 3, s) i + (23 + 2 * a + 6 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 10) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 7, (b : ℤ) - 3, s) + (23 + 2 * a + 6 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 14, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 6) 1 = FN + 2 dx' + 6 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 15).all fun a => (List.range 7).all fun b => (List.range 10).all fun s =>
    Nat.blt (37 + 2 * a + 6 * b) (FN a b s) || (a == 7 && b == 3 && s == 0) ||
      (Nat.blt (hint a b s) 44 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 8 ==
          FN a b s + 2 * dxv (hint a b s) + 6 * dyv (hint a b s))

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
from below, and for n ≥ 8 the other facets lie below by Farkas certificates (`certG_ok`,
`certC_ok`). So each piece is an interval of integers (`piece_eq`), the sphere size is a sum of floor
quotients (`cnt_eq_S`), and shifting n by 42 moves every quotient by an integer (`inner_shift`,
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
def AW (i : ℕ) : ℕ := tgetN 1754966134 4 i

def BW (i : ℕ) : ℕ := tgetN 3470475829 4 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 4 i

theorem A_W (i : Fin 8) : Ac i = (AW i.val : ℤ) - 8 := rfl

theorem B_W (i : Fin 8) : Bc i = (BW i.val : ℤ) - 8 := rfl

theorem C_W (s : Fin 10) (i : Fin 8) : Cc s i = (CW s.val i.val : ℤ) - 8 := rfl

def gcV (k : ℕ) : ℕ := ctabN 5805449 3 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 8) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 2737800 3 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 2

def Ap (i : Fin 8) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 1990734850 4 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 5

def Bp (i : Fin 8) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 38930 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 8) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 42500 2 k

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
def par (s : Fin 10) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 10) (i j : Fin 8) (c u : ℤ) :
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

theorem par_inj (s : Fin 10) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
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
(pot_i ≤ pot_j) plus cf0 times (8 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 211048501542786846406344821692227353345596800102426861521421121544470396928 4 k

def cf2V (k : ℕ) : ℕ := ctabN 4238534975690703112361492206665517410063859771901587432531996222657932288 4 k

def cf3V (k : ℕ) : ℕ := ctabN 80557783555921800249024976640429675424616315007799202752 3 k

def cf0V (k : ℕ) : ℕ := ctabN 58423714184728803932619295233805583840747977790757394715302427156936790272 4 k

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
def certC (s : Fin 10) (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (8 - Cc s i)

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
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 8 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 8 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 8 i))) 16))

def certGK : PLift ((allR 8 fun i => allR 8 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 8 fun i => allR 8 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 10 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 10) : certS s = true := by
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
theorem certC_ok (s : Fin 10) (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
def lev (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 10) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 10) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 10) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 10) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 10) (i : Fin 8) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 10) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 8 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 10) (i : Fin 8) (n u : ℤ) (hn : 8 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 8 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-5, 5]: a natural-number check. -/
def cbK : PLift ((allR 10 fun s => allR 8 fun i => Nat.ble (CW s i) 13 && Nat.ble 8 (Nat.add (CW s i) 5)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 10) (j : Fin 8) : -5 ≤ Cc s j ∧ Cc s j ≤ 5 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ
    (Finset.Icc (-(1 * n + 5)) (1 * n + 5) ×ˢ Finset.univ)

/-! Weighted pairs of facets whose gradients add up to a multiple of an axis direction. -/

def box_pairsK : PLift (3 * Ac 3 + 4 * Ac 4 = 14 ∧ 3 * Bc 3 + 4 * Bc 4 = 0 ∧
    4 * Ac 0 + 3 * Ac 7 = (-14) ∧ 4 * Bc 0 + 3 * Bc 7 = 0 ∧
    1 * Ac 6 + 0 * Ac 6 = 0 ∧ 1 * Bc 6 + 0 * Bc 6 = 6 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-6)) :=
  ⟨by decide +kernel⟩

theorem box_pairs : 3 * Ac 3 + 4 * Ac 4 = 14 ∧ 3 * Bc 3 + 4 * Bc 4 = 0 ∧
    4 * Ac 0 + 3 * Ac 7 = (-14) ∧ 4 * Bc 0 + 3 * Bc 7 = 0 ∧
    1 * Ac 6 + 0 * Ac 6 = 0 ∧ 1 * Bc 6 + 0 * Bc 6 = 6 ∧
    1 * Ac 2 + 0 * Ac 2 = 0 ∧ 1 * Bc 2 + 0 * Bc 2 = (-6) := box_pairsK.down

/-- Each weighted pair of facets bounds one coordinate by F. -/
theorem coord_le (x y : ℤ) (s : Fin 10) :
    14 * x ≤ 7 * F (x, y, s) + 35 ∧
    14 * (-x) ≤ 7 * F (x, y, s) + 35 ∧
    6 * y ≤ 1 * F (x, y, s) + 5 ∧
    6 * (-y) ≤ 1 * F (x, y, s) + 5 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := box_pairs
  have e0 : 3 * pot (x, y, s) 3 + 4 * pot (x, y, s) 4 =
      14 * x + 3 * Cc s 3 + 4 * Cc s 4 := by
    simp only [pot]; linear_combination x * p1 + y * p2
  have q0 := le_F (x, y, s) 3
  have r0 := le_F (x, y, s) 4
  have k0 := Cbound s 3
  have l0 := Cbound s 4
  have e1 : 4 * pot (x, y, s) 0 + 3 * pot (x, y, s) 7 =
      14 * (-x) + 4 * Cc s 0 + 3 * Cc s 7 := by
    simp only [pot]; linear_combination x * p3 + y * p4
  have q1 := le_F (x, y, s) 0
  have r1 := le_F (x, y, s) 7
  have k1 := Cbound s 0
  have l1 := Cbound s 7
  have e2 : 1 * pot (x, y, s) 6 + 0 * pot (x, y, s) 6 =
      6 * y + 1 * Cc s 6 + 0 * Cc s 6 := by
    simp only [pot]; linear_combination x * p5 + y * p6
  have q2 := le_F (x, y, s) 6
  have r2 := le_F (x, y, s) 6
  have k2 := Cbound s 6
  have l2 := Cbound s 6
  have e3 : 1 * pot (x, y, s) 2 + 0 * pot (x, y, s) 2 =
      6 * (-y) + 1 * Cc s 2 + 0 * Cc s 2 := by
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
noncomputable def PF (s : Fin 10) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 10) (i : Fin 8) (n : ℤ) (hn : 8 ≤ n) :
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
def inner (s : Fin 10) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 10) (i : Fin 8) (n : ℤ) (hn : 8 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 10 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 10 × Fin 8, inner p.1 p.2 n

/-! Shifting n by 42 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 92885820406442 6 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 8) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 1452286235171 6 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 14

def mh (i : Fin 8) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 173268654724672 6 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 18

def mk (i : Fin 8) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 8, (42 : ℤ) = gc i * Lq i ∧ 42 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 42 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 8, (42 : ℤ) = gc i * Lq i ∧ 42 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 42 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 10) (i : Fin 8) (n : ℤ) :
    inner s i (n + 42) = inner s i n + (if (n - Cc s i) % gc i = 0 then mh i + mk i else 0) := by
  obtain ⟨e0, e1, e2⟩ := shift_ok i
  have hg := (prim i).2.2.1
  have hx : n + 42 - Cc s i = (n - Cc s i) + gc i * Lq i := by linear_combination e0
  have hm : (n + 42 - Cc s i) % gc i = (n - Cc s i) % gc i := by
    rw [hx, Int.add_mul_emod_self_left]
  have hl : lev s i (n + 42) = lev s i n + Lq i := by
    rw [lev, lev, hx, Int.add_mul_ediv_left _ _ (ne_of_gt hg)]
  have r1 : Rb s i (i - 1) (n + 42) = Rb s i (i - 1) n + Dm i (i - 1) * mh i := by
    rw [← e1]; simp only [Rb, hl]; ring
  have r2 : Rb s i (i + 1) (n + 42) = Rb s i (i + 1) n + (-Dm i (i + 1)) * mk i := by
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
  ∑ q : Fin 10 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

theorem S_shift (n : ℤ) : S (n + 42) = S n + Gs n := by
  simp only [S, Gs, inner_shift, Finset.sum_add_distrib]

theorem Gs_periodic (x q : ℤ) : Gs (x + 42 * q) = Gs x := by
  simp only [Gs]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have e : x + 42 * q - Cc r.1 r.2 = (x - Cc r.1 r.2) + gc r.2 * (Lq r.2 * q) := by
    linear_combination q * (shift_ok r.2).1
  rw [e, Int.add_mul_emod_self_left]

/-! ## The period in natural numbers

On the line of facet i a piece length is (uh i c + vh)/dh i + (uk i c + vk)/dk i + 1 at level c. From
the window start, n = 8 + r with r < 42: the level is QQ - 0 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 290887 3 k

def uhMV (k : ℕ) : ℕ := ctabN 8423432 3 k

def ukPV (k : ℕ) : ℕ := ctabN 15240840 3 k

def ukMV (k : ℕ) : ℕ := ctabN 771 2 k

def dhV (k : ℕ) : ℕ := ctabN 1635672446 4 k

def dkV (k : ℕ) : ℕ := ctabN 15433399 3 k

def mhkV (k : ℕ) : ℕ := ctabN 2115206675 4 k

def uh (i : Fin 8) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 8) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 8) : ℤ := dhV i.val

def dk (i : Fin 8) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 110427946485565506166082939491351233825865695505884236488198792090747008 3 (Nat.add i (Nat.mul 8 s))

def QQ (s i : ℕ) : ℕ := ctabN 402756997812684786158120891747956475169915921311159369588089360681957549575422944330986828611976 4 (Nat.add i (Nat.mul 8 s))

def AH (s i : ℕ) : ℕ := ctabN 88458191883472721513279349487415499147623443468601868532453872025777292502994005640506513651964310965843579859610005968957938527684165049241817752571778697197239927480 7 (Nat.add i (Nat.mul 8 s))

def AK (s i : ℕ) : ℕ := ctabN 2022756017656960407792048361676166325032923693475253691796999684949942978248865106529085823648712738561782860191059806468 5 (Nat.add i (Nat.mul 8 s))

def WH (s i : ℕ) : ℕ := ctabN 1374894990046246660455793404166281836965889048780252360557471277225080076024314446344655100245796103478259817583936569600 5 (Nat.add i (Nat.mul 8 s))

def WK (s i : ℕ) : ℕ := ctabN 51715187149291952708251782277684484462250841587893375941764055175242353068206846252470340919410827569349115894562838 5 (Nat.add i (Nat.mul 8 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 10 fun s => allR 8 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq 16 (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 10) (i : Fin 8) :
    PP s.val i.val < gcV i.val ∧
    (8 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 0) + PP s.val i.val ∧
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

/-- Piece (s, i) at n = 8 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 8 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 10) (i : Fin 8) (r : ℕ) :
    ((8 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (8 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 0) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 10) (i : Fin 8) (r : ℕ) (hr : r < 42) :
    inner s i ((8 : ℤ) + r) = innerZ s.val i.val r := by
  obtain ⟨hP, hQ, hAh, hAk⟩ := piece_facts s i
  obtain ⟨f1, f2, f3, f4, -⟩ := tab_facet i
  obtain ⟨o1, o2⟩ := orient i
  have hL : (42 : ℤ) = gc i * Lq i := (shift_ok i).1
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
      have h2 : 42 = gcV i.val * LqV i.val := by
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
    have hl : lev s i ((8 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r := by
      rw [lev, show (8 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((8 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((8 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 113055130566109766951944978336523238294919431251738462261192025615824604025616355170107190850924495040 8 k

def tblV (k : ℕ) : ℕ := ctabN 113044366735211030500634803169479433529698455348334169983241190605781221739806456016319339821561415941 8 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 42. -/
def dv (t : ℕ) : ℕ := dtabV (t % 42)

/-- The sequence in closed form: b(n + 42) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 42) + tblV ((n - 1) % 42)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 42) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 42 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 42 - 1 = n - 1 + 42 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 42)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 42) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 42 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 42 - 1 = n - 1 + 42 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 42)]
  ring

/-- b on the residue class of 1 + j mod 42. -/
theorem b_res (k j : ℕ) (hj : j < 42) : b (42 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (42 * k + (1 + j) < 1) by omega),
    show 42 * k + (1 + j) - 1 = j + 42 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 42), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 8 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 42 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 10 fun s => allR 8 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 10 fun s => sumR 8 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 8 r)) &&
    Nat.beq (sumR 10 fun s => sumR 8 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 1 (dv (Nat.add 7 r)))

/-! The window n = 8, ..., 49, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 18 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 18 18 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 36 6 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 42) :
    (∀ s, s < 10 → ∀ i, i < 8 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 10 fun s => sumR 8 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (8 + r) ∧
    (sumR 10 fun s => sumR 8 fun i => cond (divN s i r) (mhkV i) 0) = 1 * dv (7 + r) := by
  have h : periodR r = true := by
    rcases (show r < 18 ∨ (18 ≤ r ∧ r < 36) ∨ 36 ≤ r by omega) with h | h | h
    · exact allI_get _ _ _ periodK0.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK1.down r (by omega) (by omega)
    · exact allI_get _ _ _ periodK2.down r (by omega) (by omega)
  simp only [periodR, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun s hs i hi hd => ?_, h2, h3⟩
  have h4 := (allR_iff _ _).1 ((allR_iff _ _).1 h1 s hs) i hi
  rw [hd] at h4
  simpa using h4

theorem innerZ_eq (s i r : ℕ) (hs : s < 10) (hi : i < 8) (hr : r < 42) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 10 fun s => sumR 8 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 10 × Fin 8, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 8 fun i => f s i : ℕ) : ℤ)) 10]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 8]

theorem S_window (r : ℕ) (hr : r < 42) : S ((8 : ℤ) + r) = b (8 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 42) : Gs ((8 : ℤ) + r) = ((1 * dv (7 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 8 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 10) (i : Fin 8) (n : ℤ) (hn : 8 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 8 + t := ⟨(n - 8).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 42
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 42) (by omega) (by omega)
      have e : (8 : ℤ) + t = (8 + (t - 42 : ℕ)) + 42 := by
        push_cast [Nat.cast_sub (by omega : 42 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 8 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 42 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 8 ≤ n) : (1 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 8) % 42 < 42 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((8 : ℤ) + (((n - 8) % 42 : ℕ) : ℤ)) + 42 * (((n - 8) / 42 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (7 + (n - 8) % 42) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 8 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 50
    · obtain ⟨r, rfl⟩ : ∃ r, n = 8 + r := ⟨n - 8, by omega⟩
      push_cast
      exact S_window r (by omega)
    · have h1 := ih (n - 42) (by omega) (by omega)
      have h2 := S_shift ((n - 42 : ℕ) : ℤ)
      have h3 := b_shift (n - 42) (by omega)
      have h4 := grow (n - 42) (by omega)
      rw [show n - 42 + 42 = n by omega] at h3
      rw [show ((n - 42 : ℕ) : ℤ) + 42 = n by omega] at h2
      rw [h2, h1, h3]
      push_cast
      linarith

/-! ## The small spheres

The points with F ≤ 7 lie in the box -6 ≤ x ≤ 6, -2 ≤ y ≤ 2 (`small_box`). In natural-number
coordinates a = x + 6, b = y + 2 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 10) (h : F (x, y, s) ≤ 7) :
    -6 ≤ x ∧ x ≤ 6 ∧ -2 ≤ y ∧ y ≤ 2 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 6, (b : ℤ) - 2, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 64) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 6) (Nat.mul (BW i) 2)) 8) (Nat.add (Nat.mul 8 a) (Nat.mul 8 b))

theorem pot_box (a b : ℕ) (s : Fin 10) (i : Fin 8) :
    pot ((a : ℤ) - 6, (b : ℤ) - 2, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 8 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 10) : F ((a : ℤ) - 6, (b : ℤ) - 2, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 6, (b : ℤ) - 2, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 6, (b : ℤ) - 2, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 8 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 8 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 6, (b : ℤ) - 2, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 6, (b : ℤ) - 2, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 6, (b : ℤ) - 2, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 13 fun a => sumR 5 fun b => sumR 10 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 0 .. 7, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 0 8 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 8) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 10) : V := ((q.1 : ℤ) - 6, (q.2.1 : ℤ) - 2, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 7) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 13 ×ˢ (Finset.range 5 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 10 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 6).toNat, (y + 2).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 6).toNat (y + 2).toNat s
        rw [show (((x + 6).toNat : ℕ) : ℤ) - 6 = x by omega,
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 10]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 8 are counted in the
box, those from 8 on are S(n), and both agree with the closed form b (`a_eq_b`). The step from n to
n + 42, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 8 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 8 ∨ 8 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_eq n (by omega) h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

/-- The step a(n + 42) = a(n) + dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 42) = a n + dv (n - 1) := by
  rw [a_eq_b, a_eq_b]
  exact b_step n hn

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 192 ∧ tblV 0 = 5 ∧ dv 1 = 192 ∧ tblV 1 = 9 ∧ dv 2 = 206 ∧ tblV 2 = 14 ∧ dv 3 = 192 ∧ tblV 3 = 20 ∧ dv 4 = 192 ∧ tblV 4 = 21 ∧ dv 5 = 206 ∧ tblV 5 = 30 ∧ dv 6 = 192 ∧ tblV 6 = 33 ∧ dv 7 = 192 ∧ tblV 7 = 35) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 206 ∧ tblV 8 = 44 ∧ dv 9 = 192 ∧ tblV 9 = 46 ∧ dv 10 = 192 ∧ tblV 10 = 51 ∧ dv 11 = 206 ∧ tblV 11 = 58 ∧ dv 12 = 192 ∧ tblV 12 = 61 ∧ dv 13 = 192 ∧ tblV 13 = 63 ∧ dv 14 = 206 ∧ tblV 14 = 72 ∧ dv 15 = 192 ∧ tblV 15 = 74) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 192 ∧ tblV 16 = 77 ∧ dv 17 = 206 ∧ tblV 17 = 90 ∧ dv 18 = 192 ∧ tblV 18 = 87 ∧ dv 19 = 192 ∧ tblV 19 = 91 ∧ dv 20 = 206 ∧ tblV 20 = 102 ∧ dv 21 = 192 ∧ tblV 21 = 100 ∧ dv 22 = 192 ∧ tblV 22 = 105 ∧ dv 23 = 206 ∧ tblV 23 = 118) :=
  ⟨by decide +kernel⟩

def closedK3 : PLift (dv 24 = 192 ∧ tblV 24 = 117 ∧ dv 25 = 192 ∧ tblV 25 = 117 ∧ dv 26 = 206 ∧ tblV 26 = 132 ∧ dv 27 = 192 ∧ tblV 27 = 128 ∧ dv 28 = 192 ∧ tblV 28 = 131 ∧ dv 29 = 206 ∧ tblV 29 = 148 ∧ dv 30 = 192 ∧ tblV 30 = 143 ∧ dv 31 = 192 ∧ tblV 31 = 147) :=
  ⟨by decide +kernel⟩

def closedK4 : PLift (dv 32 = 206 ∧ tblV 32 = 160 ∧ dv 33 = 192 ∧ tblV 33 = 156 ∧ dv 34 = 192 ∧ tblV 34 = 159 ∧ dv 35 = 206 ∧ tblV 35 = 176 ∧ dv 36 = 192 ∧ tblV 36 = 171 ∧ dv 37 = 192 ∧ tblV 37 = 173 ∧ dv 38 = 206 ∧ tblV 38 = 192 ∧ dv 39 = 192 ∧ tblV 39 = 182) :=
  ⟨by decide +kernel⟩

def closedK5 : PLift (dv 40 = 192 ∧ tblV 40 = 187 ∧ dv 41 = 206 ∧ tblV 41 = 206) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (42 * k + 1) = 192 * k + 5 ∧
    a (42 * k + 2) = 192 * k + 9 ∧
    a (42 * k + 3) = 206 * k + 14 ∧
    a (42 * k + 4) = 192 * k + 20 ∧
    a (42 * k + 5) = 192 * k + 21 ∧
    a (42 * k + 6) = 206 * k + 30 ∧
    a (42 * k + 7) = 192 * k + 33 ∧
    a (42 * k + 8) = 192 * k + 35 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 42 * k + 1 = 42 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 42 * k + 2 = 42 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 42 * k + 3 = 42 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 42 * k + 4 = 42 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 42 * k + 5 = 42 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 42 * k + 6 = 42 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 42 * k + 7 = 42 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 42 * k + 8 = 42 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (42 * k + 9) = 206 * k + 44 ∧
    a (42 * k + 10) = 192 * k + 46 ∧
    a (42 * k + 11) = 192 * k + 51 ∧
    a (42 * k + 12) = 206 * k + 58 ∧
    a (42 * k + 13) = 192 * k + 61 ∧
    a (42 * k + 14) = 192 * k + 63 ∧
    a (42 * k + 15) = 206 * k + 72 ∧
    a (42 * k + 16) = 192 * k + 74 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 42 * k + 9 = 42 * k + (1 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 42 * k + 10 = 42 * k + (1 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 42 * k + 11 = 42 * k + (1 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 42 * k + 12 = 42 * k + (1 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 42 * k + 13 = 42 * k + (1 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 42 * k + 14 = 42 * k + (1 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 42 * k + 15 = 42 * k + (1 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 42 * k + 16 = 42 * k + (1 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (42 * k + 17) = 192 * k + 77 ∧
    a (42 * k + 18) = 206 * k + 90 ∧
    a (42 * k + 19) = 192 * k + 87 ∧
    a (42 * k + 20) = 192 * k + 91 ∧
    a (42 * k + 21) = 206 * k + 102 ∧
    a (42 * k + 22) = 192 * k + 100 ∧
    a (42 * k + 23) = 192 * k + 105 ∧
    a (42 * k + 24) = 206 * k + 118 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 42 * k + 17 = 42 * k + (1 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 42 * k + 18 = 42 * k + (1 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 42 * k + 19 = 42 * k + (1 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 42 * k + 20 = 42 * k + (1 + 19) from rfl, b_res k 19 (by decide), c38, c39]
  · rw [show 42 * k + 21 = 42 * k + (1 + 20) from rfl, b_res k 20 (by decide), c40, c41]
  · rw [show 42 * k + 22 = 42 * k + (1 + 21) from rfl, b_res k 21 (by decide), c42, c43]
  · rw [show 42 * k + 23 = 42 * k + (1 + 22) from rfl, b_res k 22 (by decide), c44, c45]
  · rw [show 42 * k + 24 = 42 * k + (1 + 23) from rfl, b_res k 23 (by decide), c46, c47]

theorem a_closed3 (k : ℕ) :
    a (42 * k + 25) = 192 * k + 117 ∧
    a (42 * k + 26) = 192 * k + 117 ∧
    a (42 * k + 27) = 206 * k + 132 ∧
    a (42 * k + 28) = 192 * k + 128 ∧
    a (42 * k + 29) = 192 * k + 131 ∧
    a (42 * k + 30) = 206 * k + 148 ∧
    a (42 * k + 31) = 192 * k + 143 ∧
    a (42 * k + 32) = 192 * k + 147 := by
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := closedK3.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 42 * k + 25 = 42 * k + (1 + 24) from rfl, b_res k 24 (by decide), c48, c49]
  · rw [show 42 * k + 26 = 42 * k + (1 + 25) from rfl, b_res k 25 (by decide), c50, c51]
  · rw [show 42 * k + 27 = 42 * k + (1 + 26) from rfl, b_res k 26 (by decide), c52, c53]
  · rw [show 42 * k + 28 = 42 * k + (1 + 27) from rfl, b_res k 27 (by decide), c54, c55]
  · rw [show 42 * k + 29 = 42 * k + (1 + 28) from rfl, b_res k 28 (by decide), c56, c57]
  · rw [show 42 * k + 30 = 42 * k + (1 + 29) from rfl, b_res k 29 (by decide), c58, c59]
  · rw [show 42 * k + 31 = 42 * k + (1 + 30) from rfl, b_res k 30 (by decide), c60, c61]
  · rw [show 42 * k + 32 = 42 * k + (1 + 31) from rfl, b_res k 31 (by decide), c62, c63]

theorem a_closed4 (k : ℕ) :
    a (42 * k + 33) = 206 * k + 160 ∧
    a (42 * k + 34) = 192 * k + 156 ∧
    a (42 * k + 35) = 192 * k + 159 ∧
    a (42 * k + 36) = 206 * k + 176 ∧
    a (42 * k + 37) = 192 * k + 171 ∧
    a (42 * k + 38) = 192 * k + 173 ∧
    a (42 * k + 39) = 206 * k + 192 ∧
    a (42 * k + 40) = 192 * k + 182 := by
  obtain ⟨c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79⟩ := closedK4.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 42 * k + 33 = 42 * k + (1 + 32) from rfl, b_res k 32 (by decide), c64, c65]
  · rw [show 42 * k + 34 = 42 * k + (1 + 33) from rfl, b_res k 33 (by decide), c66, c67]
  · rw [show 42 * k + 35 = 42 * k + (1 + 34) from rfl, b_res k 34 (by decide), c68, c69]
  · rw [show 42 * k + 36 = 42 * k + (1 + 35) from rfl, b_res k 35 (by decide), c70, c71]
  · rw [show 42 * k + 37 = 42 * k + (1 + 36) from rfl, b_res k 36 (by decide), c72, c73]
  · rw [show 42 * k + 38 = 42 * k + (1 + 37) from rfl, b_res k 37 (by decide), c74, c75]
  · rw [show 42 * k + 39 = 42 * k + (1 + 38) from rfl, b_res k 38 (by decide), c76, c77]
  · rw [show 42 * k + 40 = 42 * k + (1 + 39) from rfl, b_res k 39 (by decide), c78, c79]

theorem a_closed5 (k : ℕ) :
    a (42 * k + 41) = 192 * k + 187 ∧
    a (42 * k + 42) = 206 * k + 206 := by
  obtain ⟨c80, c81, c82, c83⟩ := closedK5.down
  simp only [a_eq_b]
  refine ⟨?_, ?_⟩
  · rw [show 42 * k + 41 = 42 * k + (1 + 40) from rfl, b_res k 40 (by decide), c80, c81]
  · rw [show 42 * k + 42 = 42 * k + (1 + 41) from rfl, b_res k 41 (by decide), c82, c83]

/-- The closed form per residue of n mod 42, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (42 * k + 1) = 192 * k + 5 ∧
    a (42 * k + 2) = 192 * k + 9 ∧
    a (42 * k + 3) = 206 * k + 14 ∧
    a (42 * k + 4) = 192 * k + 20 ∧
    a (42 * k + 5) = 192 * k + 21 ∧
    a (42 * k + 6) = 206 * k + 30 ∧
    a (42 * k + 7) = 192 * k + 33 ∧
    a (42 * k + 8) = 192 * k + 35 ∧
    a (42 * k + 9) = 206 * k + 44 ∧
    a (42 * k + 10) = 192 * k + 46 ∧
    a (42 * k + 11) = 192 * k + 51 ∧
    a (42 * k + 12) = 206 * k + 58 ∧
    a (42 * k + 13) = 192 * k + 61 ∧
    a (42 * k + 14) = 192 * k + 63 ∧
    a (42 * k + 15) = 206 * k + 72 ∧
    a (42 * k + 16) = 192 * k + 74 ∧
    a (42 * k + 17) = 192 * k + 77 ∧
    a (42 * k + 18) = 206 * k + 90 ∧
    a (42 * k + 19) = 192 * k + 87 ∧
    a (42 * k + 20) = 192 * k + 91 ∧
    a (42 * k + 21) = 206 * k + 102 ∧
    a (42 * k + 22) = 192 * k + 100 ∧
    a (42 * k + 23) = 192 * k + 105 ∧
    a (42 * k + 24) = 206 * k + 118 ∧
    a (42 * k + 25) = 192 * k + 117 ∧
    a (42 * k + 26) = 192 * k + 117 ∧
    a (42 * k + 27) = 206 * k + 132 ∧
    a (42 * k + 28) = 192 * k + 128 ∧
    a (42 * k + 29) = 192 * k + 131 ∧
    a (42 * k + 30) = 206 * k + 148 ∧
    a (42 * k + 31) = 192 * k + 143 ∧
    a (42 * k + 32) = 192 * k + 147 ∧
    a (42 * k + 33) = 206 * k + 160 ∧
    a (42 * k + 34) = 192 * k + 156 ∧
    a (42 * k + 35) = 192 * k + 159 ∧
    a (42 * k + 36) = 206 * k + 176 ∧
    a (42 * k + 37) = 192 * k + 171 ∧
    a (42 * k + 38) = 192 * k + 173 ∧
    a (42 * k + 39) = 206 * k + 192 ∧
    a (42 * k + 40) = 192 * k + 182 ∧
    a (42 * k + 41) = 192 * k + 187 ∧
    a (42 * k + 42) = 206 * k + 206 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15⟩ := a_closed1 k
  obtain ⟨x16, x17, x18, x19, x20, x21, x22, x23⟩ := a_closed2 k
  obtain ⟨x24, x25, x26, x27, x28, x29, x30, x31⟩ := a_closed3 k
  obtain ⟨x32, x33, x34, x35, x36, x37, x38, x39⟩ := a_closed4 k
  obtain ⟨x40, x41⟩ := a_closed5 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41⟩

def controlsK : PLift ((List.range 50).map b = [1, 5, 9, 14, 20, 21, 30, 33, 35, 44, 46, 51, 58, 61, 63, 72, 74, 77, 90, 87, 91, 102, 100, 105, 118, 117, 117, 132, 128, 131, 148, 143, 147, 160, 156, 159, 176, 171, 173, 192, 182, 187, 206, 197, 201, 220, 212, 213, 236, 225]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 9, 14, 20, 21, 30, 33, 35, 44, 46, 51, 58, 61, 63, 72, 74, 77, 90, 87, 91, 102, 100, 105, 118, 117, 117, 132, 128, 131, 148, 143, 147, 160, 156, 159, 176, 171, 173, 192, 182, 187, 206, 197, 201, 220, 212, 213, 236, 225] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 42 → dv (t + 14) + dv (t + 12) + dv (t + 10) + dv (t + 4) + dv (t + 2) + dv (t + 0) = dv (t + 11) + dv (t + 9) + 2 * dv (t + 7) + dv (t + 5) + dv (t + 3)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 42 → dv (t + 14) + dv (t + 12) + dv (t + 10) + dv (t + 4) + dv (t + 2) + dv (t + 0) = dv (t + 11) + dv (t + 9) + 2 * dv (t + 7) + dv (t + 5) + dv (t + 3) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 14) : ℤ) = -(dv (t + 12) : ℤ) + (dv (t + 11) : ℤ) - (dv (t + 10) : ℤ) + (dv (t + 9) : ℤ) + 2 * (dv (t + 7) : ℤ) + (dv (t + 5) : ℤ) - (dv (t + 4) : ℤ) + (dv (t + 3) : ℤ) - (dv (t + 2) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 42 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 2, e 3, e 4, e 5, e 7, e 9, e 10, e 11, e 12, e 14]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 42) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 42 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 42 → b (q + 15) + b (q + 13) + b (q + 11) + b (q + 5) + b (q + 3) + b (q + 1) = b (q + 12) + b (q + 10) + 2 * b (q + 8) + b (q + 6) + b (q + 4)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 42 → b (q + 15) + b (q + 13) + b (q + 11) + b (q + 5) + b (q + 3) + b (q + 1) = b (q + 12) + b (q + 10) + 2 * b (q + 8) + b (q + 6) + b (q + 4) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 15) : ℤ) = -b (q + 13) + b (q + 12) - b (q + 11) + b (q + 10) + 2 * b (q + 8) + b (q + 6) - b (q + 5) + b (q + 4) - b (q + 3) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 42 ∨ 42 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 42 := ⟨q - 42, by omega⟩
      have h0 : (b (v + 15) : ℤ) = -b (v + 13) + b (v + 12) - b (v + 11) + b (v + 10) + 2 * b (v + 8) + b (v + 6) - b (v + 5) + b (v + 4) - b (v + 3) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 43) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 42 = v + 43 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s3 : (b (v + 45) : ℤ) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (le_trans (by decide : 1 ≤ 3) (Nat.le_add_left _ v))
        rw [show v + 3 + 42 = v + 45 from Nat.add_assoc _ _ _,
          show v + 3 - 1 = v + 2 from Nat.add_sub_assoc (by decide : 1 ≤ 3) v] at h
        exact_mod_cast h
      have s4 : (b (v + 46) : ℤ) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (le_trans (by decide : 1 ≤ 4) (Nat.le_add_left _ v))
        rw [show v + 4 + 42 = v + 46 from Nat.add_assoc _ _ _,
          show v + 4 - 1 = v + 3 from Nat.add_sub_assoc (by decide : 1 ≤ 4) v] at h
        exact_mod_cast h
      have s5 : (b (v + 47) : ℤ) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (le_trans (by decide : 1 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 42 = v + 47 from Nat.add_assoc _ _ _,
          show v + 5 - 1 = v + 4 from Nat.add_sub_assoc (by decide : 1 ≤ 5) v] at h
        exact_mod_cast h
      have s6 : (b (v + 48) : ℤ) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (le_trans (by decide : 1 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 42 = v + 48 from Nat.add_assoc _ _ _,
          show v + 6 - 1 = v + 5 from Nat.add_sub_assoc (by decide : 1 ≤ 6) v] at h
        exact_mod_cast h
      have s8 : (b (v + 50) : ℤ) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (le_trans (by decide : 1 ≤ 8) (Nat.le_add_left _ v))
        rw [show v + 8 + 42 = v + 50 from Nat.add_assoc _ _ _,
          show v + 8 - 1 = v + 7 from Nat.add_sub_assoc (by decide : 1 ≤ 8) v] at h
        exact_mod_cast h
      have s10 : (b (v + 52) : ℤ) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (le_trans (by decide : 1 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 42 = v + 52 from Nat.add_assoc _ _ _,
          show v + 10 - 1 = v + 9 from Nat.add_sub_assoc (by decide : 1 ≤ 10) v] at h
        exact_mod_cast h
      have s11 : (b (v + 53) : ℤ) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (le_trans (by decide : 1 ≤ 11) (Nat.le_add_left _ v))
        rw [show v + 11 + 42 = v + 53 from Nat.add_assoc _ _ _,
          show v + 11 - 1 = v + 10 from Nat.add_sub_assoc (by decide : 1 ≤ 11) v] at h
        exact_mod_cast h
      have s12 : (b (v + 54) : ℤ) = b (v + 12) + dv (v + 11) := by
        have h := b_step (v + 12) (le_trans (by decide : 1 ≤ 12) (Nat.le_add_left _ v))
        rw [show v + 12 + 42 = v + 54 from Nat.add_assoc _ _ _,
          show v + 12 - 1 = v + 11 from Nat.add_sub_assoc (by decide : 1 ≤ 12) v] at h
        exact_mod_cast h
      have s13 : (b (v + 55) : ℤ) = b (v + 13) + dv (v + 12) := by
        have h := b_step (v + 13) (le_trans (by decide : 1 ≤ 13) (Nat.le_add_left _ v))
        rw [show v + 13 + 42 = v + 55 from Nat.add_assoc _ _ _,
          show v + 13 - 1 = v + 12 from Nat.add_sub_assoc (by decide : 1 ≤ 13) v] at h
        exact_mod_cast h
      have s15 : (b (v + 57) : ℤ) = b (v + 15) + dv (v + 14) := by
        have h := b_step (v + 15) (le_trans (by decide : 1 ≤ 15) (Nat.le_add_left _ v))
        rw [show v + 15 + 42 = v + 57 from Nat.add_assoc _ _ _,
          show v + 15 - 1 = v + 14 from Nat.add_sub_assoc (by decide : 1 ≤ 15) v] at h
        exact_mod_cast h
      show (b (v + 57) : ℤ) = -b (v + 55) + b (v + 54) - b (v + 53) + b (v + 52) + 2 * b (v + 50) + b (v + 48) - b (v + 47) + b (v + 46) - b (v + 45) - b (v + 43)
      linear_combination s15 - (-1) * s13 - (1) * s12 - (-1) * s11 - (1) * s10 - (2) * s8 - (1) * s6 - (-1) * s5 - (1) * s4 - (-1) * s3 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 14 < n → (a n : ℤ) = -a (n - 2) + a (n - 3) - a (n - 4) + a (n - 5) + 2 * a (n - 7) + a (n - 9) - a (n - 10) + a (n - 11) - a (n - 12) - a (n - 14) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 15 := ⟨n - 15, by omega⟩
  rw [show q + 15 - 2 = q + 13 from Nat.add_sub_assoc (by decide : 2 ≤ 15) q, show q + 15 - 3 = q + 12 from Nat.add_sub_assoc (by decide : 3 ≤ 15) q, show q + 15 - 4 = q + 11 from Nat.add_sub_assoc (by decide : 4 ≤ 15) q, show q + 15 - 5 = q + 10 from Nat.add_sub_assoc (by decide : 5 ≤ 15) q, show q + 15 - 7 = q + 8 from Nat.add_sub_assoc (by decide : 7 ≤ 15) q, show q + 15 - 9 = q + 6 from Nat.add_sub_assoc (by decide : 9 ≤ 15) q, show q + 15 - 10 = q + 5 from Nat.add_sub_assoc (by decide : 10 ≤ 15) q, show q + 15 - 11 = q + 4 from Nat.add_sub_assoc (by decide : 11 ≤ 15) q, show q + 15 - 12 = q + 3 from Nat.add_sub_assoc (by decide : 12 ≤ 15) q, show q + 15 - 14 = q + 1 from Nat.add_sub_assoc (by decide : 14 ≤ 15) q]
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
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (b n) (bk n 2)) (bk n 4)) (bk n 10)) (bk n 12)) (bk n 14)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (bk n 3) (bk n 5)) (Nat.mul 2 (bk n 7))) (bk n 9)) (bk n 11)) (ind n 0)) (Nat.mul 5 (ind n 1))) (Nat.mul 10 (ind n 2))) (Nat.mul 18 (ind n 3))) (Nat.mul 25 (ind n 4))) (Nat.mul 30 (ind n 5))) (Nat.mul 40 (ind n 6))) (Nat.mul 37 (ind n 7))) (Nat.mul 40 (ind n 8))) (Nat.mul 29 (ind n 9))) (Nat.mul 25 (ind n 10))) (Nat.mul 18 (ind n 11))) (Nat.mul 11 (ind n 12))) (Nat.mul 5 (ind n 13))) (ind n 14)

def gfK : PLift ((allR 15 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 15, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 15) :
    1 * (b (n) : ℚ) + 1 * (if 2 ≤ n then (b (n - 2) : ℚ) else 0) - 1 * (if 3 ≤ n then (b (n - 3) : ℚ) else 0) + 1 * (if 4 ≤ n then (b (n - 4) : ℚ) else 0) - 1 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) - 2 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) - 1 * (if 9 ≤ n then (b (n - 9) : ℚ) else 0) + 1 * (if 10 ≤ n then (b (n - 10) : ℚ) else 0) - 1 * (if 11 ≤ n then (b (n - 11) : ℚ) else 0) + 1 * (if 12 ≤ n then (b (n - 12) : ℚ) else 0) + 1 * (if 14 ≤ n then (b (n - 14) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 5 + (if n = 2 then (1 : ℚ) else 0) * 10 + (if n = 3 then (1 : ℚ) else 0) * 18 + (if n = 4 then (1 : ℚ) else 0) * 25 + (if n = 5 then (1 : ℚ) else 0) * 30 + (if n = 6 then (1 : ℚ) else 0) * 40 + (if n = 7 then (1 : ℚ) else 0) * 37 + (if n = 8 then (1 : ℚ) else 0) * 40 + (if n = 9 then (1 : ℚ) else 0) * 29 + (if n = 10 then (1 : ℚ) else 0) * 25 + (if n = 11 then (1 : ℚ) else 0) * 18 + (if n = 12 then (1 : ℚ) else 0) * 11 + (if n = 13 then (1 : ℚ) else 0) * 5 + (if n = 14 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 15 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 15) : ℚ) + 1 * (if 2 ≤ q + 15 then (b (q + 15 - 2) : ℚ) else 0) - 1 * (if 3 ≤ q + 15 then (b (q + 15 - 3) : ℚ) else 0) + 1 * (if 4 ≤ q + 15 then (b (q + 15 - 4) : ℚ) else 0) - 1 * (if 5 ≤ q + 15 then (b (q + 15 - 5) : ℚ) else 0) - 2 * (if 7 ≤ q + 15 then (b (q + 15 - 7) : ℚ) else 0) - 1 * (if 9 ≤ q + 15 then (b (q + 15 - 9) : ℚ) else 0) + 1 * (if 10 ≤ q + 15 then (b (q + 15 - 10) : ℚ) else 0) - 1 * (if 11 ≤ q + 15 then (b (q + 15 - 11) : ℚ) else 0) + 1 * (if 12 ≤ q + 15 then (b (q + 15 - 12) : ℚ) else 0) + 1 * (if 14 ≤ q + 15 then (b (q + 15 - 14) : ℚ) else 0) =
      (if q + 15 = 0 then (1 : ℚ) else 0) * 1 + (if q + 15 = 1 then (1 : ℚ) else 0) * 5 + (if q + 15 = 2 then (1 : ℚ) else 0) * 10 + (if q + 15 = 3 then (1 : ℚ) else 0) * 18 + (if q + 15 = 4 then (1 : ℚ) else 0) * 25 + (if q + 15 = 5 then (1 : ℚ) else 0) * 30 + (if q + 15 = 6 then (1 : ℚ) else 0) * 40 + (if q + 15 = 7 then (1 : ℚ) else 0) * 37 + (if q + 15 = 8 then (1 : ℚ) else 0) * 40 + (if q + 15 = 9 then (1 : ℚ) else 0) * 29 + (if q + 15 = 10 then (1 : ℚ) else 0) * 25 + (if q + 15 = 11 then (1 : ℚ) else 0) * 18 + (if q + 15 = 12 then (1 : ℚ) else 0) * 11 + (if q + 15 = 13 then (1 : ℚ) else 0) * 5 + (if q + 15 = 14 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 15) : ℤ) = -b (q + 13) + b (q + 12) - b (q + 11) + b (q + 10) + 2 * b (q + 8) + b (q + 6) - b (q + 5) + b (q + 4) - b (q + 3) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 15 - 2 = q + 13 from Nat.add_sub_assoc (by decide : 2 ≤ 15) q, show q + 15 - 3 = q + 12 from Nat.add_sub_assoc (by decide : 3 ≤ 15) q, show q + 15 - 4 = q + 11 from Nat.add_sub_assoc (by decide : 4 ≤ 15) q, show q + 15 - 5 = q + 10 from Nat.add_sub_assoc (by decide : 5 ≤ 15) q, show q + 15 - 7 = q + 8 from Nat.add_sub_assoc (by decide : 7 ≤ 15) q, show q + 15 - 9 = q + 6 from Nat.add_sub_assoc (by decide : 9 ≤ 15) q, show q + 15 - 10 = q + 5 from Nat.add_sub_assoc (by decide : 10 ≤ 15) q, show q + 15 - 11 = q + 4 from Nat.add_sub_assoc (by decide : 11 ≤ 15) q, show q + 15 - 12 = q + 3 from Nat.add_sub_assoc (by decide : 12 ≤ 15) q, show q + 15 - 14 = q + 1 from Nat.add_sub_assoc (by decide : 14 ≤ 15) q, show 2 ≤ q + 15 from le_trans (by decide : 2 ≤ 15) (Nat.le_add_left 15 q), show 3 ≤ q + 15 from le_trans (by decide : 3 ≤ 15) (Nat.le_add_left 15 q), show 4 ≤ q + 15 from le_trans (by decide : 4 ≤ 15) (Nat.le_add_left 15 q), show 5 ≤ q + 15 from le_trans (by decide : 5 ≤ 15) (Nat.le_add_left 15 q), show 7 ≤ q + 15 from le_trans (by decide : 7 ≤ 15) (Nat.le_add_left 15 q), show 9 ≤ q + 15 from le_trans (by decide : 9 ≤ 15) (Nat.le_add_left 15 q), show 10 ≤ q + 15 from le_trans (by decide : 10 ≤ 15) (Nat.le_add_left 15 q), show 11 ≤ q + 15 from le_trans (by decide : 11 ≤ 15) (Nat.le_add_left 15 q), show 12 ≤ q + 15 from le_trans (by decide : 12 ≤ 15) (Nat.le_add_left 15 q), show 14 ≤ q + 15 from le_trans (by decide : 14 ≤ 15) (Nat.le_add_left 15 q), show ¬ q + 15 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 15) (Nat.le_add_left 15 q)), show ¬ q + 15 = 14 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 14 < 15) (Nat.le_add_left 15 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * (X ^ 14 + X ^ 12 - X ^ 11 + X ^ 10 - X ^ 9 - 2 * X ^ 7 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 + 1) = C 1 * A + C 1 * (A * X ^ 2) - C 1 * (A * X ^ 3) + C 1 * (A * X ^ 4) - C 1 * (A * X ^ 5) - C 2 * (A * X ^ 7) - C 1 * (A * X ^ 9) + C 1 * (A * X ^ 10) - C 1 * (A * X ^ 11) + C 1 * (A * X ^ 12) + C 1 * (A * X ^ 14) := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (X ^ 14 + 5 * X ^ 13 + 11 * X ^ 12 + 18 * X ^ 11 + 25 * X ^ 10 + 29 * X ^ 9 + 40 * X ^ 8 + 37 * X ^ 7 + 40 * X ^ 6 + 30 * X ^ 5 + 25 * X ^ 4 + 18 * X ^ 3 + 10 * X ^ 2 + 5 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 5 + X ^ 2 * C 10 + X ^ 3 * C 18 + X ^ 4 * C 25 + X ^ 5 * C 30 + X ^ 6 * C 40 + X ^ 7 * C 37 + X ^ 8 * C 40 + X ^ 9 * C 29 + X ^ 10 * C 25 + X ^ 11 * C 18 + X ^ 12 * C 11 + X ^ 13 * C 5 + X ^ 14 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 + X ^ 12 - X ^ 11 + X ^ 10 - X ^ 9 - 2 * X ^ 7 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 + 1) =
      X ^ 14 + 5 * X ^ 13 + 11 * X ^ 12 + 18 * X ^ 11 + 25 * X ^ 10 + 29 * X ^ 9 + 40 * X ^ 8 + 37 * X ^ 7 + 40 * X ^ 6 + 30 * X ^ 5 + 25 * X ^ 4 + 18 * X ^ 3 + 10 * X ^ 2 + 5 * X + 1 := by
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
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 + X ^ 12 - X ^ 11 + X ^ 10 - X ^ 9 - 2 * X ^ 7 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 + 1) =
      X ^ 14 + 5 * X ^ 13 + 11 * X ^ 12 + 18 * X ^ 11 + 25 * X ^ 10 + 29 * X ^ 9 + 40 * X ^ 8 + 37 * X ^ 7 + 40 * X ^ 6 + 30 * X ^ 5 + 25 * X ^ 4 + 18 * X ^ 3 + 10 * X ^ 2 + 5 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 14 < n → (a n : ℤ) = -a (n - 2) + a (n - 3) - a (n - 4) + a (n - 5) + 2 * a (n - 7) + a (n - 9) - a (n - 10) + a (n - 11) - a (n - 12) - a (n - 14) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 5, 9, 14, 20, 21, 30, 33, 35, 44, 46, 51, 58, 61, 63, 72, 74, 77, 90, 87, 91, 102, 100, 105, 118, 117, 117, 132, 128, 131, 148, 143, 147, 160, 156, 159, 176, 171, 173, 192, 182, 187, 206, 197, 201, 220, 212, 213, 236, 225] := Count.controls

/-- The step a(n + 42) = a(n) + Count.dv (n - 1) for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 42) = a n + Count.dv (n - 1) := Count.a_step n hn

/-- The closed form per residue of n mod 42, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (42 * k + 1) = 192 * k + 5 ∧
    a (42 * k + 2) = 192 * k + 9 ∧
    a (42 * k + 3) = 206 * k + 14 ∧
    a (42 * k + 4) = 192 * k + 20 ∧
    a (42 * k + 5) = 192 * k + 21 ∧
    a (42 * k + 6) = 206 * k + 30 ∧
    a (42 * k + 7) = 192 * k + 33 ∧
    a (42 * k + 8) = 192 * k + 35 ∧
    a (42 * k + 9) = 206 * k + 44 ∧
    a (42 * k + 10) = 192 * k + 46 ∧
    a (42 * k + 11) = 192 * k + 51 ∧
    a (42 * k + 12) = 206 * k + 58 ∧
    a (42 * k + 13) = 192 * k + 61 ∧
    a (42 * k + 14) = 192 * k + 63 ∧
    a (42 * k + 15) = 206 * k + 72 ∧
    a (42 * k + 16) = 192 * k + 74 ∧
    a (42 * k + 17) = 192 * k + 77 ∧
    a (42 * k + 18) = 206 * k + 90 ∧
    a (42 * k + 19) = 192 * k + 87 ∧
    a (42 * k + 20) = 192 * k + 91 ∧
    a (42 * k + 21) = 206 * k + 102 ∧
    a (42 * k + 22) = 192 * k + 100 ∧
    a (42 * k + 23) = 192 * k + 105 ∧
    a (42 * k + 24) = 206 * k + 118 ∧
    a (42 * k + 25) = 192 * k + 117 ∧
    a (42 * k + 26) = 192 * k + 117 ∧
    a (42 * k + 27) = 206 * k + 132 ∧
    a (42 * k + 28) = 192 * k + 128 ∧
    a (42 * k + 29) = 192 * k + 131 ∧
    a (42 * k + 30) = 206 * k + 148 ∧
    a (42 * k + 31) = 192 * k + 143 ∧
    a (42 * k + 32) = 192 * k + 147 ∧
    a (42 * k + 33) = 206 * k + 160 ∧
    a (42 * k + 34) = 192 * k + 156 ∧
    a (42 * k + 35) = 192 * k + 159 ∧
    a (42 * k + 36) = 206 * k + 176 ∧
    a (42 * k + 37) = 192 * k + 171 ∧
    a (42 * k + 38) = 192 * k + 173 ∧
    a (42 * k + 39) = 206 * k + 192 ∧
    a (42 * k + 40) = 192 * k + 182 ∧
    a (42 * k + 41) = 192 * k + 187 ∧
    a (42 * k + 42) = 206 * k + 206 := Count.a_closed k

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 14 + X ^ 12 - X ^ 11 + X ^ 10 - X ^ 9 - 2 * X ^ 7 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 + 1) =
      X ^ 14 + 5 * X ^ 13 + 11 * X ^ 12 + 18 * X ^ 11 + 25 * X ^ 10 + 29 * X ^ 9 + 40 * X ^ 8 + 37 * X ^ 7 + 40 * X ^ 6 + 30 * X ^ 5 + 25 * X ^ 4 + 18 * X ^ 3 + 10 * X ^ 2 + 5 * X + 1 ∧
    ∀ n : ℕ, 14 < n → (a n : ℤ) = -a (n - 2) + a (n - 3) - a (n - 4) + a (n - 5) + 2 * a (n - 7) + a (n - 9) - a (n - 10) + a (n - 11) - a (n - 12) - a (n - 14) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a314929

theorem OMA.solution : type_of% @OMA.S_oeis_a314929.main :=
  OMA.S_oeis_a314929.conjecture
