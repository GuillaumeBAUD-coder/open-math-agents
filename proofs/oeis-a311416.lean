import OMAStatements.S_oeis_a311416

namespace OMA.S_oeis_a311416






/-- The vertex of class s in the cell (x, y) of the translation lattice is (x, y, s). -/
abbrev V := ℤ × ℤ × Fin 14

/-- Field k of the B-bit fields packed in the natural number T. -/
def tgetN (T B k : ℕ) : ℕ := T >>> (B * k) % 2 ^ B

/-- Field k of the B-bit fields packed in the natural number T, each stored as value + off. -/
def tget (T B off k : ℕ) : ℤ := (tgetN T B k : ℤ) - (off : ℤ)

def CcT (s : ℕ) : ℕ :=
  match s with
  | 0 => 567420666450
  | 1 => 711577708875
  | 2 => 745868208525
  | 3 => 710469365100
  | 4 => 532021823025
  | 5 => 710400159150
  | 6 => 675001315725
  | 7 => 567489872400
  | 8 => 602888715825
  | 9 => 638425971150
  | 10 => 639534314925
  | 11 => 673824814575
  | 12 => 602957921775
  | 13 => 638356765200
  | _ => 0

/-- The potential of facet i is Ac i * x + Bc i * y + Cc s i at (x, y, s) (packed tables, which
the kernel reads in constant time). -/
def Ac (i : Fin 8) : ℤ := tget 497732371950 5 16 i.val

def Bc (i : Fin 8) : ℤ := tget 782512759050 5 16 i.val

def Cc (s : Fin 14) (i : Fin 8) : ℤ := tget (CcT s.val) 5 16 i.val

/-- The same tables in natural numbers, for the kernel checks: each value is stored as value + 16. -/
def AcN (i : ℕ) : ℕ := tgetN 497732371950 5 i

def BcN (i : ℕ) : ℕ := tgetN 782512759050 5 i

def CcN (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem Ac_eq (i : Fin 8) : Ac i = (AcN i.val : ℤ) - 16 := rfl

theorem Bc_eq (i : Fin 8) : Bc i = (BcN i.val : ℤ) - 16 := rfl

theorem Cc_eq (s : Fin 14) (i : Fin 8) : Cc s i = (CcN s.val i.val : ℤ) - 16 := rfl


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
theorem cls (P : Fin 14 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) : ∀ s, P s := by
  intro s
  fin_cases s
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

/-- The change of the potential of facet j along the edge e. -/
def dl (e : Fin 14 × Fin 14 × ℤ × ℤ) (j : Fin 8) : ℤ := Ac j * e.2.2.1 + Bc j * e.2.2.2 + Cc e.2.1 j - Cc e.1 j

theorem E_step : ∀ e ∈ E, ∀ j : Fin 8, dl e j ≤ 1 ∧ -dl e j ≤ 1 := by
  decide +kernel

theorem E_move : ∀ e ∈ E, e.2.2.1 ≠ 0 ∨ e.2.2.2 ≠ 0 ∨ e.1 ≠ e.2.1 := by
  decide +kernel

theorem adj_of_mem (e : Fin 14 × Fin 14 × ℤ × ℤ) (he : e ∈ E) (x y : ℤ) :
    G.Adj (x, y, e.1) (x + e.2.2.1, y + e.2.2.2, e.2.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨e, he, rfl, rfl, rfl, rfl⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  rcases E_move e he with h' | h' | h' <;> omega

/-- Along an edge e the potential of facet j changes by dl e j. -/
theorem shift (x y : ℤ) (e : Fin 14 × Fin 14 × ℤ × ℤ) (j : Fin 8) :
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
theorem farkas (x y : ℤ) (s : Fin 14) (a1 b1 a2 b2 a3 b3 i0 : Fin 8) (t1 t2 t3 r l1 l2 l3 l0 : ℤ)
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
pot k2 ≤ pot i, 11 ≤ pot i and pot i ≤ pot j + 1 with multipliers m1, m2, m0, mj. -/
def fdN (i j f : ℕ) : ℕ := tgetN 124589052130638596552697102011239196301021820072575545262988694242261562782084636774841799468156448384213034662444916895379606022884069130900503785707065129111848063496859417614823731495204333616265572909357840701356521779115062259942002303013404621510258675533719472625798117728888636412332529587552020076549141488937384037409846146072256940776126037147679816334972531341558598133625294083204307026996532058283533080928072626325391577357430147135503020239496447448998908308187702913108554707171618722205949978235781667593081475620290687317522860524487497710822465593975559608529063247942446567707351040731318169084118566729469083258475563879359999459032946482752815890432 6 ((i * 8 + j) * 6 + f)

def fd (i j : Fin 8) (f : ℕ) : ℤ := (fdN i.val j.val f : ℤ)

def fk1 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 0 % 8, Nat.mod_lt _ (by norm_num)⟩

def fk2 (i j : Fin 8) : Fin 8 := ⟨fdN i.val j.val 1 % 8, Nat.mod_lt _ (by norm_num)⟩

def fm1 (i j : Fin 8) : ℤ := fd i j 2

def fm2 (i j : Fin 8) : ℤ := fd i j 3

def fm0 (i j : Fin 8) : ℤ := fd i j 4

def fmj (i j : Fin 8) : ℤ := fd i j 5

/-- The edges of E by position p, in natural numbers: source and target class, dx + 1, dy + 1, and
the potential changes dl + 8 at entry p * 8 + j. -/
def srcv (p : ℕ) : ℕ := tgetN 23365259686036119300756076571243582239442394384030040830666712612864 4 p

def dstv (p : ℕ) : ℕ := tgetN 21559756796532653145196147937442184485298956527247861857819769734209 4 p

def dxv (p : ℕ) : ℕ := tgetN 1411312485664591946517698646661712 2 p

def dyv (p : ℕ) : ℕ := tgetN 1730765619511609209510096723613268 2 p

def dlvN (p j : ℕ) : ℕ := tgetN 130389745253981058356223087819284295073290654868589338280999454738350706819611616286589393501518751254984674259401787791004475599941811007055097952504933478666896156064227716631555295898251278020525201225578859895873509729441302867246826174192072094083153138220544835835276186927061284112308226303828014772017225613339746245345333872967896788677679702167547850926226928311030662792035739703731966751809090962465488917901073760688861003289500573131782048726429422627173085448059620562085634924883695356410309123193933635407946691493460674969 4 (p * 8 + j)

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
      fdN i j 4 * 27)

/-- j is i or a neighbor of i around the growth polygon. -/
def nearB (i j : ℕ) : Bool := j == i || j == (i + 1) % 8 || j == (i + 7) % 8

def farOK : Bool := (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farXYN i j

def farCOK : Bool :=
  (List.range 14).all fun s => (List.range 8).all fun i => (List.range 8).all fun j => nearB i j || farCN s i j

/-- The edge tables agree with E; dl in natural numbers, moved across (Ac = AcN - 16, dx = dxv - 1). -/
def dlOK : Bool :=
  (List.range 56).all fun p =>
    decide ((E.getD p (0, 0, 0, 0)).1.val = srcv p ∧ (E.getD p (0, 0, 0, 0)).2.1.val = dstv p ∧
      (E.getD p (0, 0, 0, 0)).2.2.1 + 1 = (dxv p : ℤ) ∧ (E.getD p (0, 0, 0, 0)).2.2.2 + 1 = (dyv p : ℤ)) &&
    (List.range 8).all fun j =>
      dlvN p j + 1 * AcN j + 16 * dxv p + 1 * BcN j + 16 * dyv p + CcN (srcv p) j ==
        AcN j * dxv p + BcN j * dyv p + 32 + CcN (dstv p) j + 8

/-- The far certificate of (i, j) at class s, in the integers. -/
def farCert (s : Fin 14) (i j : Fin 8) : Prop :=
  0 ≤ fm1 i j ∧ 0 ≤ fm2 i j ∧ 0 ≤ fmj i j ∧ 0 ≤ fm0 i j ∧
    fm1 i j * (Ac (fk1 i j) - Ac i) + fm2 i j * (Ac (fk2 i j) - Ac i) + fmj i j * (Ac i - Ac j) - fm0 i j * Ac i = 0 ∧
    fm1 i j * (Bc (fk1 i j) - Bc i) + fm2 i j * (Bc (fk2 i j) - Bc i) + fmj i j * (Bc i - Bc j) - fm0 i j * Bc i = 0 ∧
    0 < fm1 i j * (Cc s (fk1 i j) - Cc s i - 0) + fm2 i j * (Cc s (fk2 i j) - Cc s i - 0) +
      fmj i j * (Cc s i - Cc s j - 1) + fm0 i j * (11 - Cc s i)

/-- Beyond F = 10, a facet that is not adjacent to a maximal facet i has slack at least 2. -/
theorem far (s : Fin 14) (i j : Fin 8) (hc : farCert s i j) (x y : ℤ)
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
  | 0 => 10401192662967571427912689421907605072887756405920589175183427911762347298404048492119444265470987201741992836744317971385346573110206437785266570438425135176348294675007692199808588245912856762909178391315139699163771726548544527186417731447675753804923258649440414270490223216407439821139604068404289563739706523309554160767591479704489577986784781810982027096561610406168448294652861540900193589310600769470747085128385491230035329972020403752276415249281757677499943873757015303250519775822005194865260954735788501076760830282094051330900690207486525798311022988132389466487113916710182069718016523321179755329878753756061776131343449225107393806790664059507817905809330770353039782584801804112594739996703694712723169006257338892433704488727398785983794470469916674069934703099349063894306145834589204964654668184835205604534432374175130218410926600605740918927764637956913088549285815274189874874975002944
  | 1 => 10401192664769668970141298161095126912137814128140681702312005251497127405231830495906632777211792983158730879897075216905873710645021449175318635340637808992913745105252792442963067658493198902226334651577391898460615805159602084888697212883539478896479986240191655379569836527002916636258056817614165697825524732013497025265187898236973249915056600469238796607976680361776450819571940653425058644317706894821501113847595842578379929215626676778752470182973577114778384978667771109296474444062982095130205560556141868503056934089364880715262198671093869359764813539914456608068910051936146839638080608286294241001477974570972943021861568672788399237065665135098646963867259171304164773686748021823214458013976926029152876351487565582817381871893614599963194616048841130217518157037143058417776365536106652631623588487103192191586449473680929096786948443472150014319393404240406657068413529851582631596801794113
  | 2 => 10401192667773164873855646059740996644221243665174169247526300817721760916610754171415687925850209114646710957210540269746938610387086827976487436222457811474652680117716909778448224186790008217278368993494359042186404586574561517590070135033281327967419757732280239642046379278979343752198004012967923215611534515513506607551192039678406175427926149833792901236539524406813391599945470550893844788043584339665470881157259141427488636579435583584110034155235531864899096666478985682169850016134350721176557851458487252962320777923558479411766891321346360712606430889696171327410632343277211097546446414723143950621808907980917409044269796320554477266887377161783394236303080292504972065878931721328015584768226806842949250633340517211438078670005395352290024262100755086208051549213859264934760681658237693009725322402207617493730083992542751141508273975931285655652366243891391084668791180013735614266534274368
  | 3 => 10401192670175961596827124378657692460943407062730694650009552978514136232256138819209921258484099633113716703403183096418776453560000612983851484642723661430604025991953847245605974468908588801586956570628510442020967543510305345259657450179486123885078023002254711522124882104346266012510591391491034434135857145361929699986618362555751386470442285187833951917981734515327433697515013376646597240008933940133038781795762558295907961465772330216267620657728540842910001524398338826139010724710912504535385722576054123374506978600442359250453538350574922198405089361534297577698639133346058978789101387214111821122896960887458721753708039535217717321193111294772656616916185328202131352392833447562267093074669527252643861073608441178009717002480992683429088936116911745037690370460434494558579944382743699985668316788721489642958356459785932142578783439583179070762076742915200904421142905490320878705516617793
  | 4 => 10401192671978059139055733117845214300193464784950787177138130318239585429479414534807766511365675448406189373038097321690459100638837924995346643502470449534052233038685358433159383902993643106777222759043649438218767981254706204247545424115593927776448255736050244043610709631888047658247363166033881377317355610903885526563191197599523193900907634167280274017522769228765820419314205340245210274076914493873813245237423218456648668465298172679878797455010813086766781169608145487244797788694311485916215116451468585736010734551408184276388459496042391720690751239558905600238357647347817470550962842538985536106173883094475424333580137769343720597461058601813083536806628031993549863020520567719502785820806498183603303349039368781887101381305160952793975265359349532569553930989672996193944824917407944779379232441291887171104199786071235906813598508586920386860319242895085737772962356548579792281104949313
  | 5 => 10401192674981555042770081016491084001221474554054539356040610176660881343920812690360053416419041984003788137909873717289323739186409111688286921361156417982935036305527782959698680938890535755495539184427184722910070160496638948288330863957074810377055399532987981799202914809548930000836420978520958881610128385543745889280670846907283588679462263097172868255851296689317715022812076562363118552872983163971436833585464706987894603365816489575033926999328076655612365023542689637740527903646593924088287689743597633379674325067127522583859141687093614599546171928543690307340867557442973637016351498585799512688150162658990951363149431519118974720911435352509429075878875065117281696575270895348281931222514192868381467755762162341556329640584694093033066470745540493665649085072510109987854278127074852520983172522899083347540105867556214206015820651035755293155141725331107360848619164520502592505740536640
  | 6 => 10401192677384351765741559335407779817943637951611064758523862337443925749961958424016040629292300100423997258523976630435480287085435176119838603974867981144091351112266695518272222800745668766743158404248325148493178994313714451265896468749461982927602852289974413433513384597733754233502294166738679812950264316074751254734642745558145199240286793135893068156163585218192254940878517695107831786461549257596448322919139609665001202458310124598685274385197663467008000908120958689152378578836182748559077934742636547364225457441611074560478144012941075517641164046269959836692616582508533888784287637165943542505547183289703352511128290783042241484539541697294853887874249667126773944246536305515355859394575344838283416845891070074765924991144407473166914517208436304155941326974808575534000322094050248174861722086426398097743475867944817453536305222656289804885266737970972748057147841527646052797746913345
  | 7 => 10401192678585750127227298494866127679721589998508846780167901244662381149367995180431018970379581371084670630522209948242889689573371884080564391207411272766049238547787438688921134017674940796466468612892509062578560904219319849490778305358088555212124182317945651364798037693239681222836400724867543546042196202552698545730788996571524217774700796019754000826347811896030874399615472219333489527757143449908005773066979007632961570223023212664148334419980269131250967724794027681937241797122592664000679361333489493555446443678722680806782983841655452433968009089389067084842016224066697896978136978191437161395239044352876674129338265999644937523521218028292156979396025536103476234473771595445178928585912829823645628016433473969506743706032028110837680489954928222746605871625444901778364782331451433973947037256239245673005989960087081336652981039524047393360296714004631954001812301821345060172760227905
  | 8 => 10401192680988546850198776813782823465388333628135636816339337697632757054342929680883324508306864948930004974969506993146629899610413982576589351515487037398696285233617320119664660442069378645115497322501536441332101682886904400639850833000257809697899098873693575423360734681264928186497151253020469972851024120976453452640067775711853648230038564366900094858584869588612809022459405398674036057077788859728632638555650638586862416377464733806379441468790020452832465094580476622697298588758749816742694615478868674159099965595297461325465601860567922416250308541494575731950754553107431629987646904349404243911841839619466088946050964984876921768054411856711033776542000157996270068359926179560501327768363355385899742980667164053986651528047034927321283730563103235420380319806115285520671610130416178236470830312171650654587060566583850746589650485112524714172041861626654391884731707124996354044630937920
  | 9 => 10401192684592741934655994292157867174943868840491434867038171696392377078114942937190764515624477334324060514311434627130445599428256477064325472968481444915136126863139444206381645616389850189223613124691190959890159250775882212570775512370500790954531542942846065732380944534280367201930002522818817437913903912763600480163661087903693313760827405777841546424830173377789688043470345290050344693955302951263672099293249178396432456315065127568221256167704646963386549144643544370867902452568616148335620581433321119407890268253666887475863414244992746164310029387237289670487700219705205069732490865063986909040529600518670546578437373997734231472847949855847709266136910234170711997593790384765397105395000303715585284205294650047605664744147037179492747326077774914562407359806385032524509391806884486362836145640592164468819008248725011168972881278545241930974319768244177512978947711516468486473623412801
  | 10 => 10401192687596237838370342190803736875971878609595187045940651554804342091713682472560636018472609110170818821918615139672655941543662006724458097015564488415571716290097424722401096181449911776758668267801807789640500587700251050853853381558451097908198805509073075435103490488271075621086217057510628835739933013045406564050727647056291368803158390377278508154113572111179339373224815880568144485740395320099906585331175258907159151549363769263551897972670034902672603093995021773293224360621025384741517796889562279198715335741160811363021621277996562704255570255805779612809378257216250592320600763220955776666849397766720081271203623792978337050970432378743117467242497369036690535295036040050533312667208749716363752645094349672590254202802613591203682516229426415938914146509714946196337599856477465800832716781232374995527418159822087479243482438106422171683605356333962945220894888537599228908924182593
  | 11 => 10401192688797636199856081350262084768805250424408582064026369781294195496265091518336753940009304983604852734250262825078895236051776822357752308871141700909469076633922166941259796887246863879674355339612706660573446660916256574522046420583183791113432240459497927325104144643180303218099540095109762363695890830797039568928771293603294176567328260429720745259564071196790610816783279706331113424181785261638227952233999124324650492339127403327704140795762338903275334412760656348365035271433762577270523256251078768652368027446369163029486331066431545684312709386738596344495147715186141985275803088158171018266392381971847745115286062475635444257571417849973742907478969603932711454020065746589547137930429504053763297248191384029762836817000391478594684588531910376498314484370033648784100736323788690068113423486141329239144261593661021705744841724802320742397839349634086645222936919566822622888692037312
  | 12 => 10401192690599733742084690089449606608055308146649858145960151703822219531050478019453709621036906907428291293247079951773060708020437058850155457330671816661584035331092606544373144567342027357647890382550898557540312817827839412724607750133148162632343041635565236591316462941986146514582054017506058292792680488160829497048471034000529771728207633116125849689730494340273174300931971110526190802160291857404248109377261503116834029881854683934689016541894874588534413461842064261258499569675022314860244463805070577472520724163756639841528631348417427171001520347598795515707481622954677849243725519807484120819319236835653876671594474491654277300049588961707530091734068756597518276435995732848731190877719443671265205834946668339037041341211982719273263981499606025879963522389196515255520123182629157788398401154524744984084575074949362935661958235488816293756861884865922665862763416456398635158614712385
  | 13 => 10401192693002530465056168408366302393722051776276648182131588156792595443691561324825416917461817518089459869373490440503264390821569272771414776846432082134759617083304118701626258053866284683994892441487066510471645385759856492391361274355158284204541942950379813520395799709733361689400146425265149337687643638364833948454688773777404549951003693002792232043706355913130160192083868179136558603305458103674391372659392453005488555660233089846582227620159030635157841429165235285603419008005088908601980736207977112119331426541136444871754095042762258648011243983265194308960179188149456618184579775724272185540337558976749139737917688337628728695281438985481793980073218823907428843687745452330234175623157412846350122931616624023225909698132633722849378286152934555590296826365300367418994146896906758339680385843757624038545824838217134546636577349814709690091889156624776145231123013428928520509707008960
  | _ => 0

def rd (s : Fin 14) (i : Fin 8) (c1 c2 : Fin 3) (f : ℕ) : ℤ :=
  tget (ruleT s.val) 7 64 (((i.val * 3 + c1.val) * 3 + c2.val) * 6 + f)

def rk (s : Fin 14) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 0).toNat

def re (s : Fin 14) (i : Fin 8) (c1 c2 : Fin 3) : ℕ := (rd s i c1 c2 1).toNat

def r1 (s : Fin 14) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 2

def r2 (s : Fin 14) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 3

def r0 (s : Fin 14) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 4

def rg (s : Fin 14) (i : Fin 8) (c1 c2 : Fin 3) : ℤ := rd s i c1 c2 5

def ruleOK (s : Fin 14) (i : Fin 8) (c1 c2 : Fin 3) : Bool :=
  if rk s i c1 c2 = 0 then
    decide (re s i c1 c2 < 56 ∧ srcv (re s i c1 c2) = s.val ∧ dlvN (re s i c1 c2) i.val + 1 ≤ 8 ∧
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
theorem far_cert (s : Fin 14) (i j : Fin 8) (hij : nonadj i j) : farCert s i j := by
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

theorem point_contra (x y : ℤ) (s : Fin 14) (i : Fin 8) (c1 c2 : ℤ) (u1 u2 u0 : ℤ) (hu0 : 0 < u0)
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
theorem far_step (s : Fin 14) (i : Fin 8) (x y : ℤ) (h : F (x, y, s) = pot (x, y, s) i)
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
theorem farkas_ub (x y : ℤ) (s : Fin 14) (a1 a2 a3 : Fin 8) (t l1 l2 l3 px py q lq : ℤ)
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

theorem box_c0 : ∀ s : Fin 14, 0 < 6 * (Cc s 0 - 10) + 6 * (Cc s 7 - 10) + 0 * (Cc s 0 - 10) + 24 * 6 := by
  decide +kernel

theorem box_c1 : ∀ s : Fin 14, 0 < 6 * (Cc s 3 - 10) + 6 * (Cc s 4 - 10) + 0 * (Cc s 0 - 10) + 24 * 6 := by
  decide +kernel

theorem box_c2 : ∀ s : Fin 14, 0 < 2 * (Cc s 1 - 10) + 1 * (Cc s 3 - 10) + 0 * (Cc s 0 - 10) + 22 * 3 := by
  decide +kernel

theorem box_c3 : ∀ s : Fin 14, 0 < 2 * (Cc s 5 - 10) + 1 * (Cc s 7 - 10) + 0 * (Cc s 0 - 10) + 22 * 3 := by
  decide +kernel

theorem box_c4 : ∀ s : Fin 14, 0 < 2 * (Cc s 3 - (-1)) + 2 * (Cc s 7 - (-1)) + 0 * (Cc s 0 - (-1)) + 0 * 0 := by
  decide +kernel

/-- Every vertex with F at most 10 lies in the cells |x| ≤ 5, |y| ≤ 2 (one certificate per
direction for all classes). -/
theorem near_box (x y : ℤ) (s : Fin 14) (hF : F (x, y, s) ≤ 10) :
    -5 ≤ x ∧ x ≤ 5 ∧ -2 ≤ y ∧ y ≤ 2 := by
  have u := fun k => (le_F (x, y, s) k).trans hF
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc
  · exact farkas_ub x y s 0 7 0 10 6 6 0 1 0 6 24 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c0 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 3 4 0 10 6 6 0 (-1) 0 6 24 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c1 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 1 3 0 10 2 1 0 0 1 3 22 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c2 s⟩ (u _) (u _) (u _) (by omega)
  · exact farkas_ub x y s 5 7 0 10 2 1 0 0 (-1) 3 22 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c3 s⟩ (u _) (u _) (u _) (by omega)

theorem F_nonneg (v : V) : 0 ≤ F v := by
  obtain ⟨x, y, s⟩ := v
  by_contra hc
  have u := fun k => (le_F (x, y, s) k).trans (show F (x, y, s) ≤ -1 by omega)
  exact farkas_ub x y s 3 7 0 (-1) 2 2 0 0 0 0 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide +kernel, by decide +kernel, box_c4 s⟩ (u _) (u _) (u _) (by norm_num)

/-- For the cell (a - 5, b - 2) and class s of the box, the position in E of an edge along which
F descends (0 where none is needed). -/
def hint (a b s : ℕ) : ℕ := 124555831686604446583123513351661806748429850479165776258730925123137356053202554814439749874242656963918789721310964466972440317826640208678226806693111468628609898989835054257937408364193447048075270244473598837258695352909857829897277136941975596491419620295678356411204260879873381338779901248003142625975312664482590291186934210095625168158167062303028980041337476508621215222750784385970529042959275071271681588198857414206613986224718091866701593591635557444090565632681566917226854372950482086184769760216010012048099791951403855387508670764709799182692859991841313068269832122431096167152117348891919883055669564143781330117297025596463576934978425095647033582132243051158279152382120278827039511900765430578605888875902226668810224900479018933567142044190167699436645978164232197647447436027654849874372009574805479151491971954268192861648689341734788377499307590754008740459411624384459718326810775672118836372547958248457816357226747115096176284270494598427378608334000647227335381436482767448283982934516878510162649539984719915080859379914407496149963956358853887275235281365259332846028948695697381560227084736399665506759047121874922878039617617455521536331433557234100641725856605644495234734132529433958347346044736107895932469508495871590179819033259175030737433787743894656624163048664714454307110326980332890695116259328 >>> (6 * ((a * 5 + b) * 14 + s)) % 2 ^ 6

/-- The near box in natural numbers: at the cell (a - 5, b - 2) and class s, potential i plus
24 + 2 a + 8 b, with non-negative coefficients. -/
def fnt (a b s : ℕ) (i : Fin 8) : ℕ :=
  tgetN 1178733600 5 i.val * a + tgetN 498767822850 5 i.val * b + tgetN 7420312988640863007433422537801024712678119202469761761813103117113577815343956945673334340115536548453416040788083234018951806446256915527784605361159636216618565215885000265206472705240529679508192240 6 (s * 8 + i.val)

def FN (a b s : ℕ) : ℕ := max (max (max (max (max (max (max (fnt a b s 0) (fnt a b s 1)) (fnt a b s 2)) (fnt a b s 3)) (fnt a b s 4)) (fnt a b s 5)) (fnt a b s 6)) (fnt a b s 7)

theorem fnt_tab : ∀ s : Fin 14, ∀ i : Fin 8, (tgetN 1178733600 5 i.val : ℤ) = Ac i + 2 ∧
    (tgetN 498767822850 5 i.val : ℤ) = Bc i + 8 ∧
    (tgetN 7420312988640863007433422537801024712678119202469761761813103117113577815343956945673334340115536548453416040788083234018951806446256915527784605361159636216618565215885000265206472705240529679508192240 6 (s.val * 8 + i.val) : ℤ) = Cc s i - Ac i * 5 - Bc i * 2 + 24 := by
  decide +kernel

theorem fnt_eq (a b : ℕ) (s : Fin 14) (i : Fin 8) :
    (fnt a b s.val i : ℤ) = pot ((a : ℤ) - 5, (b : ℤ) - 2, s) i + (24 + 2 * a + 8 * b) := by
  obtain ⟨h1, h2, h3⟩ := fnt_tab s i
  simp only [fnt, pot]
  push_cast
  rw [h1, h2, h3]
  ring

theorem FN_eq (a b : ℕ) (s : Fin 14) :
    (FN a b s.val : ℤ) = F ((a : ℤ) - 5, (b : ℤ) - 2, s) + (24 + 2 * a + 8 * b) := by
  simp only [FN, F, Nat.cast_max, fnt_eq, max_add_add_right]

/-- Every vertex of the box with F at most 10, other than v0, has a neighbor where F is one less:
the edge at position hint (FN of the neighbor + 1 + (2 + 8) 1 = FN + 2 dx' + 8 dy', with
dx' = dx + 1 and dy' = dy + 1). -/
def nearOK : Bool :=
  (List.range 11).all fun a => (List.range 5).all fun b => (List.range 14).all fun s =>
    Nat.blt (34 + 2 * a + 8 * b) (FN a b s) || (a == 5 && b == 2 && s == 7) ||
      (Nat.blt (hint a b s) 56 && srcv (hint a b s) == s && Nat.ble 1 (a + dxv (hint a b s)) &&
        Nat.ble 1 (b + dyv (hint a b s)) &&
        FN (a + dxv (hint a b s) - 1) (b + dyv (hint a b s) - 1) (dstv (hint a b s)) + 1 + 10 ==
          FN a b s + 2 * dxv (hint a b s) + 8 * dyv (hint a b s))

theorem nearOK_eq : nearOK = true := by
  decide +kernel

theorem near_desc (v : V) (hF : F v ≤ 10) (hv : v ≠ v0) : ∃ w, G.Adj v w ∧ F w + 1 = F v := by
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
    have cw1 : (((a + dxv (hint a b s.val) - 1 : ℕ) : ℤ)) - 5 = x + dx := by omega
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
from below, and for n ≥ 7 the other facets lie below by Farkas certificates (`certG_ok`,
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
def AW (i : ℕ) : ℕ := tgetN 497732371950 5 i

def BW (i : ℕ) : ℕ := tgetN 782512759050 5 i

def CW (s i : ℕ) : ℕ := tgetN (CcT s) 5 i

theorem A_W (i : Fin 8) : Ac i = (AW i.val : ℤ) - 16 := rfl

theorem B_W (i : Fin 8) : Bc i = (BW i.val : ℤ) - 16 := rfl

theorem C_W (s : Fin 14) (i : Fin 8) : Cc s i = (CW s.val i.val : ℤ) - 16 := rfl

def gcV (k : ℕ) : ℕ := ctabN 38550 2 k

def gcN (k : ℕ) : ℤ := (gcV k : ℤ)

def gc (i : Fin 8) : ℤ := gcN i.val

def ApV (k : ℕ) : ℕ := ctabN 2720 2 k

def ApN (k : ℕ) : ℤ := (ApV k : ℤ) - 1

def Ap (i : Fin 8) : ℤ := ApN i.val

def BpV (k : ℕ) : ℕ := ctabN 395685560325 5 k

def BpN (k : ℕ) : ℤ := (BpV k : ℤ) - 8

def Bp (i : Fin 8) : ℤ := BpN i.val

def alV (k : ℕ) : ℕ := ctabN 2720 2 k

def alN (k : ℕ) : ℤ := (alV k : ℤ) - 1

def al (i : Fin 8) : ℤ := alN i.val

def beV (k : ℕ) : ℕ := ctabN 0 1 k

def beN (k : ℕ) : ℤ := (beV k : ℤ)

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
def par (s : Fin 14) (i : Fin 8) (c u : ℤ) : V :=
  (al i * c + Bp i * u, be i * c - Ap i * u, s)

theorem pot_par (s : Fin 14) (i j : Fin 8) (c u : ℤ) :
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

theorem par_inj (s : Fin 14) (i : Fin 8) (c : ℤ) : Function.Injective (par s i c) := by
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
(pot_i ≤ pot_j) plus cf0 times (7 ≤ pot_i) is a contradiction, for every class. -/

def cf1V (k : ℕ) : ℕ := ctabN 275691551904643094266314302834529038335321621587112087377728322936949968896 4 k

def cf2V (k : ℕ) : ℕ := ctabN 31839481334486676360921973262888558291449705773382737630382225327952808704 4 k

def cf3V (k : ℕ) : ℕ := ctabN 90241627565070896635306782982786945612121633725247138397652441703636878592 4 k

def cf0V (k : ℕ) : ℕ := ctabN 664668031509720436216830827964672672 2 k

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
def certC (s : Fin 14) (i j : Fin 8) : Prop :=
  let h := i - 1
  let k := i + 1
  0 < cf1 i j * (Cc s h - Cc s i + (if h < i then 1 else 0)) +
    cf2 i j * (Cc s k - Cc s i + (if k < i then 1 else 0)) + cf3 i j * (Cc s i - Cc s j) +
    cf0 i j * (7 - Cc s i)

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
    (Nat.add (Nat.add (Nat.add (Nat.mul (cf1V (Nat.add j (Nat.mul 8 i))) (Nat.add (CW s (prevF i)) (ehV i))) (Nat.mul (cf2V (Nat.add j (Nat.mul 8 i))) (Nat.add (CW s (nextF i)) (ekV i)))) (Nat.mul (cf3V (Nat.add j (Nat.mul 8 i))) (CW s i))) (Nat.mul (cf0V (Nat.add j (Nat.mul 8 i))) 23))

def certGK : PLift ((allR 8 fun i => allR 8 fun j => nearB i j || certGN i j) = true) :=
  ⟨by decide +kernel⟩

/-- The constant parts of the certificates for class s. -/
noncomputable def certS (s : ℕ) : Bool := allR 8 fun i => allR 8 fun j => nearB i j || certCN s i j

/-! The constant parts, checked by the kernel in pieces of consecutive classes. -/

def certCK0 : PLift (allI 0 14 certS = true) :=
  ⟨by decide +kernel⟩

theorem cert_ok (s : ℕ) (hs : s < 14) : certS s = true := by
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
theorem certC_ok (s : Fin 14) (i j : Fin 8) (e1 : j ≠ i - 1) (e2 : j ≠ i) (e3 : j ≠ i + 1) :
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
def lev (s : Fin 14) (i : Fin 8) (n : ℤ) : ℤ := (n - Cc s i) / gc i

theorem lev_mul (s : Fin 14) (i : Fin 8) (n : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    gc i * lev s i n = n - Cc s i :=
  Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hd)

/-- The bound R in Dm i j * u ≤ R that says pot_j ≤ n - [j < i] on the piece (s, i). -/
def Rb (s : Fin 14) (i j : Fin 8) (n : ℤ) : ℤ :=
  n - (if j < i then 1 else 0) - ka i j * lev s i n - Cc s j

def hi (s : Fin 14) (i : Fin 8) (n : ℤ) : ℤ := Rb s i (i - 1) n / Dm i (i - 1)

def lo (s : Fin 14) (i : Fin 8) (n : ℤ) : ℤ := -(Rb s i (i + 1) n / (-Dm i (i + 1)))

theorem pot_le_iff (s : Fin 14) (i j : Fin 8) (n u : ℤ) :
    pot (par s i (lev s i n) u) j ≤ n - (if j < i then 1 else 0) ↔ Dm i j * u ≤ Rb s i j n := by
  rw [pot_par, Rb]
  constructor <;> intro h <;> linarith

theorem le_hi_iff (s : Fin 14) (i : Fin 8) (n u : ℤ) :
    u ≤ hi s i n ↔ Dm i (i - 1) * u ≤ Rb s i (i - 1) n := by
  rw [hi, Int.le_ediv_iff_mul_le (orient i).1, mul_comm]

theorem lo_le_iff (s : Fin 14) (i : Fin 8) (n u : ℤ) :
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

theorem pot_par_self (s : Fin 14) (i : Fin 8) (n u : ℤ) (hd : (n - Cc s i) % gc i = 0) :
    pot (par s i (lev s i n) u) i = n := by
  rw [pot_par, ka_self, Dm_self, lev_mul s i n hd]
  ring

/-- From n = 7 on, the points of the interval [lo, hi] are the piece. -/
theorem par_piece (s : Fin 14) (i : Fin 8) (n u : ℤ) (hn : 7 ≤ n)
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
  exact farkas4 (par s i (lev s i n) u) (i - 1) i (i + 1) j _ _ 7 _ _ _ _ ⟨c1, c2, c3, c0⟩ cx cy cc
    (by rw [hi']; exact hh) (by rw [hi']; exact hk) f3 (by rw [hi']; exact hn)

/-- The class constants lie in [-6, 6]: a natural-number check. -/
def cbK : PLift ((allR 14 fun s => allR 8 fun i => Nat.ble (CW s i) 22 && Nat.ble 16 (Nat.add (CW s i) 6)) = true) :=
  ⟨by decide +kernel⟩

theorem Cbound (s : Fin 14) (j : Fin 8) : -6 ≤ Cc s j ∧ Cc s j ≤ 6 := by
  have h := (allR_iff _ _).1 ((allR_iff _ _).1 cbK.down s.val s.isLt) j.val j.isLt
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
  rw [C_W]
  omega

/-- The box that holds the sphere F = n. -/
noncomputable def Bx (n : ℤ) : Finset V :=
  Finset.Icc (-(1 * n + 6)) (1 * n + 6) ×ˢ
    (Finset.Icc (-(1 * n + 6)) (1 * n + 6) ×ˢ Finset.univ)

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
theorem coord_le (x y : ℤ) (s : Fin 14) :
    4 * x ≤ 2 * F (x, y, s) + 12 ∧
    4 * (-x) ≤ 2 * F (x, y, s) + 12 ∧
    16 * y ≤ 2 * F (x, y, s) + 12 ∧
    16 * (-y) ≤ 2 * F (x, y, s) + 12 := by
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
noncomputable def PF (s : Fin 14) (i : Fin 8) (n : ℤ) : Finset V :=
  (Bx n).filter (fun v => v.2.2 = s ∧ F v = n ∧ fi v = i)

theorem piece_eq (s : Fin 14) (i : Fin 8) (n : ℤ) (hn : 7 ≤ n) :
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
def inner (s : Fin 14) (i : Fin 8) (n : ℤ) : ℤ :=
  if (n - Cc s i) % gc i = 0 then hi s i n + 1 - lo s i n else 0

theorem card_piece (s : Fin 14) (i : Fin 8) (n : ℤ) (hn : 7 ≤ n) :
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

theorem cnt_eq_sum (n : ℤ) : cnt n = ∑ p : Fin 14 × Fin 8, (PF p.1 p.2 n).card := by
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
def S (n : ℤ) : ℤ := ∑ p : Fin 14 × Fin 8, inner p.1 p.2 n

/-! Shifting n by 40 = gc i * Lq i moves each quotient of a piece length by an integer. -/

def LqV (k : ℕ) : ℕ := ctabN 90752999918100 6 k

def LqN (k : ℕ) : ℤ := (LqV k : ℤ)

def Lq (i : Fin 8) : ℤ := LqN i.val

def mhV (k : ℕ) : ℕ := ctabN 2298775812 4 k

def mhN (k : ℕ) : ℤ := (mhV k : ℤ) - 4

def mh (i : Fin 8) : ℤ := mhN i.val

def mkV (k : ℕ) : ℕ := ctabN 1083719832 4 k

def mkN (k : ℕ) : ℤ := (mkV k : ℤ) - 4

def mk (i : Fin 8) : ℤ := mkN i.val

def shift_okK : PLift (∀ i : Fin 8, (40 : ℤ) = gc i * Lq i ∧ 40 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 40 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i) :=
  ⟨by decide +kernel⟩

theorem shift_ok : ∀ i : Fin 8, (40 : ℤ) = gc i * Lq i ∧ 40 - ka i (i - 1) * Lq i = Dm i (i - 1) * mh i ∧ 40 - ka i (i + 1) * Lq i = (-Dm i (i + 1)) * mk i := shift_okK.down

theorem inner_shift (s : Fin 14) (i : Fin 8) (n : ℤ) :
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
  ∑ q : Fin 14 × Fin 8, (if (n - Cc q.1 q.2) % gc q.2 = 0 then mh q.2 + mk q.2 else 0)

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
the window start, n = 7 + r with r < 40: the level is QQ - 0 + tauN with tauN = (PP + r) / gc i, on
the levels with gc i ∣ PP + r, and the two numerators plus dh i WH, dk i WK are the natural numbers
numH, numK (`piece_facts`, `inner_nat`). -/

def uhPV (k : ℕ) : ℕ := ctabN 24672 2 k

def uhMV (k : ℕ) : ℕ := ctabN 34 1 k

def ukPV (k : ℕ) : ℕ := ctabN 2313 2 k

def ukMV (k : ℕ) : ℕ := ctabN 68 1 k

def dhV (k : ℕ) : ℕ := ctabN 189326868812 5 k

def dkV (k : ℕ) : ℕ := ctabN 423596796421 5 k

def mhkV (k : ℕ) : ℕ := ctabN 8702028 3 k

def uh (i : Fin 8) : ℤ := (uhPV i.val : ℤ) - uhMV i.val

def uk (i : Fin 8) : ℤ := (ukPV i.val : ℤ) - ukMV i.val

def dh (i : Fin 8) : ℤ := dhV i.val

def dk (i : Fin 8) : ℤ := dkV i.val

def tab_facetK : PLift (∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i) :=
  ⟨by decide +kernel⟩

theorem tab_facet : ∀ i : Fin 8, uh i = gc i - ka i (i - 1) ∧ dh i = Dm i (i - 1) ∧ uk i = gc i - ka i (i + 1) ∧ dk i = -Dm i (i + 1) ∧ (mhkV i.val : ℤ) = mh i + mk i := tab_facetK.down

def PP (s i : ℕ) : ℕ := ctabN 3103208834495150139312668573468825 1 (Nat.add i (Nat.mul 8 s))

def QQ (s i : ℕ) : ℕ := ctabN 106329519503955982491528686233160775220653693202712005236407425547061990032769747403826834247543333508988244395260287972258051421124434 4 (Nat.add i (Nat.mul 8 s))

def AH (s i : ℕ) : ℕ := ctabN 158711271672806912954417990135111158985474085693956457413736489024655494055589191634056408973563814205519773453939799725862295242489697640609497410066530458528302312578 5 (Nat.add i (Nat.mul 8 s))

def AK (s i : ℕ) : ℕ := ctabN 137757870399945046615732346767680131754561641116104735604577590130915733772608300515848286968881412790748121342270003116952691070146829773424299893019642555116384488834 5 (Nat.add i (Nat.mul 8 s))

def WH (s i : ℕ) : ℕ := ctabN 1367373876164938324948316072483246514401027848963666246672549659498781609621754412574481048932618280 3 (Nat.add i (Nat.mul 8 s))

def WK (s i : ℕ) : ℕ := ctabN 10943196234047126817401735658742764610989719563495584471095927242396435097583329965351305106649514304 3 (Nat.add i (Nat.mul 8 s))

/-- The constants of every piece at the window start, a natural-number check. -/
noncomputable def pieceOK : Bool :=
  allR 14 fun s => allR 8 fun i =>
    Nat.blt (PP s i) (gcV i) &&
    Nat.beq 23 (Nat.add (Nat.add (Nat.mul (gcV i) (QQ s i)) (PP s i)) (CW s i)) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AH s i) (Nat.mul (uhMV i) (QQ s i))) (CW s (prevF i))) (ehV i)) (Nat.mul (uhMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (uhPV i) (QQ s i)) (CW s i)) (Nat.mul (dhV i) (WH s i))) &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (AK s i) (Nat.mul (ukMV i) (QQ s i))) (CW s (nextF i))) (ekV i)) (Nat.mul (ukMV i) (LqV i)))
      (Nat.add (Nat.add (Nat.mul (ukPV i) (QQ s i)) (CW s i)) (Nat.mul (dkV i) (WK s i)))

def pieceOK_eqK : PLift (pieceOK = true) :=
  ⟨by decide +kernel⟩

theorem pieceOK_eq : pieceOK = true := pieceOK_eqK.down

theorem piece_facts (s : Fin 14) (i : Fin 8) :
    PP s.val i.val < gcV i.val ∧
    (7 : ℤ) - Cc s i = gc i * ((QQ s.val i.val : ℤ) - 0) + PP s.val i.val ∧
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

/-- Piece (s, i) at n = 7 + r: the level step, whether the level has points, the two numerators
shifted by WH and WK, and the length plus WH + WK. -/
def tauN (s i r : ℕ) : ℕ := Nat.div (Nat.add (PP s i) r) (gcV i)

def divN (s i r : ℕ) : Bool := Nat.beq (Nat.mod (Nat.add (PP s i) r) (gcV i)) 0

def numH (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AH s i) (Nat.mul (uhPV i) (tauN s i r))) (Nat.mul (uhMV i) (Nat.sub (LqV i) (tauN s i r)))

def numK (s i r : ℕ) : ℕ :=
  Nat.add (Nat.add (AK s i) (Nat.mul (ukPV i) (tauN s i r))) (Nat.mul (ukMV i) (Nat.sub (LqV i) (tauN s i r)))

def lenN (s i r : ℕ) : ℕ := Nat.add (Nat.add (Nat.div (numH s i r) (dhV i)) (Nat.div (numK s i r) (dkV i))) 1

def wN (s i : ℕ) : ℕ := Nat.add (WH s i) (WK s i)

/-- The length of piece (s, i) at 7 + r from its natural-number form. -/
def innerZ (s i r : ℕ) : ℤ := if divN s i r = true then (lenN s i r : ℤ) - (wN s i : ℤ) else 0

theorem ediv_shift (X : ℤ) (N W d : ℕ) (hd : 0 < d) (h : X + d * W = N) :
    X / d = ((N / d : ℕ) : ℤ) - W := by
  rw [Int.natCast_ediv, show X = (N : ℤ) + (-(W : ℤ)) * d by linear_combination h,
    Int.add_mul_ediv_right _ _ (by exact_mod_cast hd.ne')]
  ring

theorem div_nat (s : Fin 14) (i : Fin 8) (r : ℕ) :
    ((7 : ℤ) + r - Cc s i) % gc i = 0 ↔ divN s.val i.val r = true := by
  obtain ⟨-, hQ, -, -⟩ := piece_facts s i
  rw [show (7 : ℤ) + r - Cc s i = ((PP s.val i.val + r : ℕ) : ℤ) + gc i * ((QQ s.val i.val : ℤ) - 0) by
    push_cast; linear_combination hQ, Int.add_mul_emod_self_left]
  simp only [divN, Nat.beq_eq, Nat.add_eq, nmod]
  rw [show gc i = ((gcV i.val : ℕ) : ℤ) from rfl, ← Int.natCast_emod, Nat.cast_eq_zero]

theorem inner_nat (s : Fin 14) (i : Fin 8) (r : ℕ) (hr : r < 40) :
    inner s i ((7 : ℤ) + r) = innerZ s.val i.val r := by
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
    have hl : lev s i ((7 : ℤ) + r) = ((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r := by
      rw [lev, show (7 : ℤ) + r - Cc s i = gc i * (((QQ s.val i.val : ℤ) - 0) + tauN s.val i.val r) by
        linear_combination hQ + hτg, Int.mul_ediv_cancel_left _ (ne_of_gt (prim i).2.2.1)]
    have hka : ka i (i - 1) = gc i - uh i := by linarith
    have hkb : ka i (i + 1) = gc i - uk i := by linarith
    have kh : Rb s i (i - 1) ((7 : ℤ) + r) + (dhV i.val : ℤ) * (WH s.val i.val : ℤ) =
        (numH s.val i.val r : ℤ) := by
      simp only [numH, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      push_cast [Nat.cast_sub hτ]
      rw [Rb, hl, hka]
      simp only [uh, dh] at hAh ⊢
      linear_combination hQ + hτg - hAh
    have kk : Rb s i (i + 1) ((7 : ℤ) + r) + (dkV i.val : ℤ) * (WK s.val i.val : ℤ) =
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

def dtabV (k : ℕ) : ℕ := ctabN 1407238517783187818989661359358763746091193567670265354318050941624050642867245538838657374922920 8 k

def tblV (k : ℕ) : ℕ := ctabN 1407107122961649962193785769174441718029930072385490936140186873285497692715001202396604798863364 8 k

def initV (k : ℕ) : ℕ := ctabN 1 1 k

/-- The step of the closed form at residue t mod 40. -/
def dv (t : ℕ) : ℕ := dtabV (t % 40)

/-- The sequence in closed form: b(n + 40) = b(n) + dv (n - 1) for n ≥ 1. -/
def b (n : ℕ) : ℕ :=
  if n < 1 then initV n else dv (n - 1) * ((n - 1) / 40) + tblV ((n - 1) % 40)

theorem b_step (n : ℕ) (hn : 1 ≤ n) : b (n + 40) = b n + dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 40 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 40 - 1 = n - 1 + 40 by omega, dv, dv, Nat.add_mod_right,
    Nat.add_div_right _ (by norm_num : 0 < 40)]
  ring

theorem b_shift (n : ℕ) (hn : 1 ≤ n) : b (n + 40) = b n + 1 * dv (n - 1) := by
  rw [b, b, if_neg (show ¬ (n + 40 < 1) by omega), if_neg (show ¬ (n < 1) by omega),
    show n + 40 - 1 = n - 1 + 40 * 1 by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 40)]
  ring

/-- b on the residue class of 1 + j mod 40. -/
theorem b_res (k j : ℕ) (hj : j < 40) : b (40 * k + (1 + j)) = dv j * k + tblV j := by
  rw [b, if_neg (show ¬ (40 * k + (1 + j) < 1) by omega),
    show 40 * k + (1 + j) - 1 = j + 40 * k by omega, dv, dv, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 40), Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]
  ring

/-- The window at n = 7 + r: every piece length is nonnegative, the closed form agrees with b, and
the growth over 40 terms agrees with the steps. -/
noncomputable def periodR (r : ℕ) : Bool :=
  (allR 14 fun s => allR 8 fun i => !divN s i r || Nat.ble (wN s i) (lenN s i r)) &&
    Nat.beq (sumR 14 fun s => sumR 8 fun i => cond (divN s i r) (Nat.sub (lenN s i r) (wN s i)) 0)
      (b (Nat.add 7 r)) &&
    Nat.beq (sumR 14 fun s => sumR 8 fun i => cond (divN s i r) (mhkV i) 0)
      (Nat.mul 1 (dv (Nat.add 6 r)))

/-! The window n = 7, ..., 46, checked by the kernel in pieces of consecutive levels. -/

def periodK0 : PLift (allI 0 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK1 : PLift (allI 13 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK2 : PLift (allI 26 13 periodR = true) :=
  ⟨by decide +kernel⟩

def periodK3 : PLift (allI 39 1 periodR = true) :=
  ⟨by decide +kernel⟩

theorem period_facts (r : ℕ) (hr : r < 40) :
    (∀ s, s < 14 → ∀ i, i < 8 → divN s i r = true → wN s i ≤ lenN s i r) ∧
    (sumR 14 fun s => sumR 8 fun i => cond (divN s i r) (lenN s i r - wN s i) 0) = b (7 + r) ∧
    (sumR 14 fun s => sumR 8 fun i => cond (divN s i r) (mhkV i) 0) = 1 * dv (6 + r) := by
  have h : periodR r = true := by
    rcases (show r < 13 ∨ (13 ≤ r ∧ r < 26) ∨ (26 ≤ r ∧ r < 39) ∨ 39 ≤ r by omega) with h | h | h | h
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

theorem innerZ_eq (s i r : ℕ) (hs : s < 14) (hi : i < 8) (hr : r < 40) :
    innerZ s i r = ((cond (divN s i r) (lenN s i r - wN s i) 0 : ℕ) : ℤ) := by
  rw [innerZ]
  cases hd : divN s i r
  · simp
  · rw [if_pos rfl, cond_true, Nat.cast_sub ((period_facts r hr).1 s hs i hi hd)]

theorem sumR2 (f : ℕ → ℕ → ℕ) :
    ((sumR 14 fun s => sumR 8 fun i => f s i : ℕ) : ℤ) = ∑ q : Fin 14 × Fin 8, (f q.1.val q.2.val : ℤ) := by
  rw [Fintype.sum_prod_type, sumR_eq, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun s => ((sumR 8 fun i => f s i : ℕ) : ℤ)) 14]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [sumR_eq, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (f s.val i : ℤ)) 8]

theorem S_window (r : ℕ) (hr : r < 40) : S ((7 : ℤ) + r) = b (7 + r) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (period_facts r hr).2.1
  rw [sumR2] at h
  rw [← h, S]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [inner_nat q.1 q.2 r hr, innerZ_eq _ _ _ q.1.isLt q.2.isLt hr]

theorem Gs_window (r : ℕ) (hr : r < 40) : Gs ((7 : ℤ) + r) = ((1 * dv (6 + r) : ℕ) : ℤ) := by
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

/-- Every piece length is nonnegative from n = 7 on: checked on one period, then shifted. -/
theorem inner_nonneg (s : Fin 14) (i : Fin 8) (n : ℤ) (hn : 7 ≤ n) : 0 ≤ inner s i n := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = 7 + t := ⟨(n - 7).toNat, by omega⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < 40
    · rw [inner_nat s i t ht, innerZ_eq _ _ _ s.isLt i.isLt ht]
      exact Nat.cast_nonneg _
    · have := ih (t - 40) (by omega) (by omega)
      have e : (7 : ℤ) + t = (7 + (t - 40 : ℕ)) + 40 := by
        push_cast [Nat.cast_sub (by omega : 40 ≤ t)]; ring
      rw [e, inner_shift]
      have hpos : 0 ≤ mh i + mk i := by
        rw [← (tab_facet i).2.2.2.2]
        exact Nat.cast_nonneg _
      split_ifs <;> linarith

theorem cnt_eq_S (n : ℤ) (hn : 7 ≤ n) : (cnt n : ℤ) = S n := by
  rw [cnt_eq_sum, S, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [card_piece p.1 p.2 n hn]
  exact Int.toNat_of_nonneg (inner_nonneg p.1 p.2 n hn)

/-- The growth of b over 40 terms is that of S, from the window by periodicity. -/
theorem grow (n : ℕ) (hn : 7 ≤ n) : (1 : ℤ) * (dv (n - 1) : ℤ) = Gs n := by
  have hr : (n - 7) % 40 < 40 := Nat.mod_lt _ (by norm_num)
  have e1 : (n : ℤ) = ((7 : ℤ) + (((n - 7) % 40 : ℕ) : ℤ)) + 40 * (((n - 7) / 40 : ℕ) : ℤ) := by
    omega
  have e2 : dv (n - 1) = dv (6 + (n - 7) % 40) := by
    simp only [dv]
    congr 1
    omega
  rw [e1, Gs_periodic, Gs_window _ hr, e2]
  push_cast
  ring

theorem S_eq_b (n : ℕ) (hn : 7 ≤ n) : S n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 47
    · obtain ⟨r, rfl⟩ : ∃ r, n = 7 + r := ⟨n - 7, by omega⟩
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

The points with F ≤ 6 lie in the box -6 ≤ x ≤ 6, -1 ≤ y ≤ 1 (`small_box`). In natural-number
coordinates a = x + 6, b = y + 1 every potential is PtN - NtN (`pot_box`), so F is their largest
difference FN (`F_FN`), and the kernel counts the box points on each level (`smallOK`). -/

theorem small_box (x y : ℤ) (s : Fin 14) (h : F (x, y, s) ≤ 6) :
    -6 ≤ x ∧ x ≤ 6 ∧ -1 ≤ y ∧ y ≤ 1 := by
  obtain ⟨b1, b2, b3, b4⟩ := coord_le x y s
  omega

/-- Potential i at the box point ((a : ℤ) - 6, (b : ℤ) - 1, s) is PtN i a b s - NtN i a b. -/
def PtN (i a b s : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) a) 112) (Nat.mul (BW i) b)) (CW s i)

def NtN (i a b : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.mul (AW i) 6) (BW i)) 16) (Nat.add (Nat.mul 16 a) (Nat.mul 16 b))

theorem pot_box (a b : ℕ) (s : Fin 14) (i : Fin 8) :
    pot ((a : ℤ) - 6, (b : ℤ) - 1, s) i = (PtN i.val a b s.val : ℤ) - NtN i.val a b := by
  simp only [pot, PtN, NtN, A_W, B_W, C_W, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring

/-- F at the box point (a, b, s), in natural numbers. -/
noncomputable def FN (a b s : ℕ) : ℕ := maxR 8 fun i => Nat.sub (PtN i a b s) (NtN i a b)

theorem F_FN (a b : ℕ) (s : Fin 14) : F ((a : ℤ) - 6, (b : ℤ) - 1, s) = (FN a b s.val : ℤ) := by
  have h0 := F_nonneg ((a : ℤ) - 6, (b : ℤ) - 1, s)
  simp only [FN, Nat.sub_eq]
  apply le_antisymm
  · obtain ⟨k, hk⟩ := F_attained ((a : ℤ) - 6, (b : ℤ) - 1, s)
    have h1 := pot_box a b s k
    have h2 := le_maxR 8 (fun i => PtN i a b s.val - NtN i a b) k.val k.isLt
    omega
  · have h3 : (maxR 8 fun i => PtN i a b s.val - NtN i a b) ≤
        (F ((a : ℤ) - 6, (b : ℤ) - 1, s)).toNat := by
      apply maxR_le
      intro k hk
      have h1 : pot ((a : ℤ) - 6, (b : ℤ) - 1, s) ⟨k, hk⟩ = (PtN k a b s.val : ℤ) - NtN k a b :=
        pot_box a b s ⟨k, hk⟩
      have h2 := le_F ((a : ℤ) - 6, (b : ℤ) - 1, s) ⟨k, hk⟩
      omega
    omega

/-- The number of box points with FN = f. -/
noncomputable def cntB (f : ℕ) : ℕ :=
  sumR 13 fun a => sumR 3 fun b => sumR 14 fun s => cond (Nat.beq (FN a b s) f) 1 0

/-- The small sphere f agrees with b. -/
noncomputable def smallR (f : ℕ) : Bool := Nat.beq (cntB f) (b f)

/-! The small spheres 0 .. 6, checked by the kernel in pieces of consecutive levels. -/

def smallK0 : PLift (allI 0 7 smallR = true) :=
  ⟨by decide +kernel⟩

theorem small_eq (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 7) : cntB n = b n := by
  have h : smallR n = true := by
    exact allI_get _ _ _ smallK0.down n (by omega) (by omega)
  simpa only [smallR, Nat.beq_eq] using h

/-- The box points by natural-number coordinates. -/
def ib (q : ℕ × ℕ × Fin 14) : V := ((q.1 : ℤ) - 6, (q.2.1 : ℤ) - 1, q.2.2)

theorem ib_inj : Function.Injective ib := by
  rintro ⟨a, b, s⟩ ⟨a', b', s'⟩ h
  simp only [ib, Prod.mk.injEq] at h
  obtain ⟨h1, h2, rfl⟩ := h
  have e1 : a = a' := by omega
  have e2 : b = b' := by omega
  rw [e1, e2]

theorem cnt_small (f : ℕ) (hf : f ≤ 6) : cnt f = cntB f := by
  have hs : {v : V | F v = (f : ℤ)} = ↑(((Finset.range 13 ×ˢ (Finset.range 3 ×ˢ Finset.univ)).filter
      (fun q : ℕ × ℕ × Fin 14 => FN q.1 q.2.1 q.2.2.val = f)).image ib) := by
    ext ⟨x, y, s⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true, Prod.exists]
    constructor
    · intro h
      obtain ⟨hx1, hx2, hy1, hy2⟩ := small_box x y s (by omega)
      refine ⟨(x + 6).toNat, (y + 1).toNat, s, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have e := F_FN (x + 6).toNat (y + 1).toNat s
        rw [show (((x + 6).toNat : ℕ) : ℤ) - 6 = x by omega,
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
  rw [sumR_eq, ← Fin.sum_univ_eq_sum_range (fun s => cond (Nat.beq (FN a b s) f) 1 0) 14]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  dsimp only
  cases h : Nat.beq (FN a b s.val) f
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

/-! ## The coordination sequence

`a n` counts the level set F = n (`a_eq_cnt`, from `dist_eq`). The terms below 7 are counted in the
box, those from 7 on are S(n), and both agree with the closed form b (`a_eq_b`). The step from n to
n + 40, the closed form per residue (`a_closed`), the controls, the recurrence and the g.f. follow,
their base cases checked by the kernel on b. -/

/-- The sphere of radius n in the graph is the level set F = n. -/
theorem a_eq_cnt (n : ℕ) : a n = cnt n := by
  rw [a, cnt]
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, dist_eq]
  have := F_nonneg v
  omega

theorem a_eq_S (n : ℕ) (hn : 7 ≤ n) : (a n : ℤ) = S n := by
  rw [a_eq_cnt]
  exact cnt_eq_S n (by exact_mod_cast hn)

/-- The coordination sequence in closed form. -/
theorem a_eq_b (n : ℕ) : a n = b n := by
  rcases (show n < 7 ∨ 7 ≤ n by omega) with h | h
  · rw [a_eq_cnt, cnt_small _ (by omega)]
    exact small_eq n (by omega) h
  · have h1 := a_eq_S n h
    rw [S_eq_b n h] at h1
    exact_mod_cast h1

def dconst_baseK : PLift (∀ r : ℕ, r < 40 → dtabV r = 168) :=
  ⟨by decide +kernel⟩

theorem dconst_base : ∀ r : ℕ, r < 40 → dtabV r = 168 := dconst_baseK.down

theorem dv_const : ∀ t : ℕ, dv t = 168 := by
  intro t
  rw [dv]
  exact dconst_base _ (Nat.mod_lt _ (by norm_num))

/-- The step a(n + 40) = a(n) + 168 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 40) = a n + 168 := by
  rw [a_eq_b, a_eq_b, b_step n hn, dv_const]

/-! The steps and the values on one period, by the kernel in pieces of 8 residues, and the closed form
per residue on each piece. -/

def closedK0 : PLift (dv 0 = 168 ∧ tblV 0 = 4 ∧ dv 1 = 168 ∧ tblV 1 = 8 ∧ dv 2 = 168 ∧ tblV 2 = 12 ∧ dv 3 = 168 ∧ tblV 3 = 17 ∧ dv 4 = 168 ∧ tblV 4 = 21 ∧ dv 5 = 168 ∧ tblV 5 = 24 ∧ dv 6 = 168 ∧ tblV 6 = 29 ∧ dv 7 = 168 ∧ tblV 7 = 35) :=
  ⟨by decide +kernel⟩

def closedK1 : PLift (dv 8 = 168 ∧ tblV 8 = 40 ∧ dv 9 = 168 ∧ tblV 9 = 43 ∧ dv 10 = 168 ∧ tblV 10 = 45 ∧ dv 11 = 168 ∧ tblV 11 = 49 ∧ dv 12 = 168 ∧ tblV 12 = 54 ∧ dv 13 = 168 ∧ tblV 13 = 58 ∧ dv 14 = 168 ∧ tblV 14 = 62 ∧ dv 15 = 168 ∧ tblV 15 = 67) :=
  ⟨by decide +kernel⟩

def closedK2 : PLift (dv 16 = 168 ∧ tblV 16 = 73 ∧ dv 17 = 168 ∧ tblV 17 = 78 ∧ dv 18 = 168 ∧ tblV 18 = 81 ∧ dv 19 = 168 ∧ tblV 19 = 84 ∧ dv 20 = 168 ∧ tblV 20 = 87 ∧ dv 21 = 168 ∧ tblV 21 = 90 ∧ dv 22 = 168 ∧ tblV 22 = 95 ∧ dv 23 = 168 ∧ tblV 23 = 101) :=
  ⟨by decide +kernel⟩

def closedK3 : PLift (dv 24 = 168 ∧ tblV 24 = 106 ∧ dv 25 = 168 ∧ tblV 25 = 110 ∧ dv 26 = 168 ∧ tblV 26 = 114 ∧ dv 27 = 168 ∧ tblV 27 = 119 ∧ dv 28 = 168 ∧ tblV 28 = 123 ∧ dv 29 = 168 ∧ tblV 29 = 125 ∧ dv 30 = 168 ∧ tblV 30 = 128 ∧ dv 31 = 168 ∧ tblV 31 = 133) :=
  ⟨by decide +kernel⟩

def closedK4 : PLift (dv 32 = 168 ∧ tblV 32 = 139 ∧ dv 33 = 168 ∧ tblV 33 = 144 ∧ dv 34 = 168 ∧ tblV 34 = 147 ∧ dv 35 = 168 ∧ tblV 35 = 151 ∧ dv 36 = 168 ∧ tblV 36 = 156 ∧ dv 37 = 168 ∧ tblV 37 = 160 ∧ dv 38 = 168 ∧ tblV 38 = 164 ∧ dv 39 = 168 ∧ tblV 39 = 168) :=
  ⟨by decide +kernel⟩

theorem a_closed0 (k : ℕ) :
    a (40 * k + 1) = 168 * k + 4 ∧
    a (40 * k + 2) = 168 * k + 8 ∧
    a (40 * k + 3) = 168 * k + 12 ∧
    a (40 * k + 4) = 168 * k + 17 ∧
    a (40 * k + 5) = 168 * k + 21 ∧
    a (40 * k + 6) = 168 * k + 24 ∧
    a (40 * k + 7) = 168 * k + 29 ∧
    a (40 * k + 8) = 168 * k + 35 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := closedK0.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 40 * k + 1 = 40 * k + (1 + 0) from rfl, b_res k 0 (by decide), c0, c1]
  · rw [show 40 * k + 2 = 40 * k + (1 + 1) from rfl, b_res k 1 (by decide), c2, c3]
  · rw [show 40 * k + 3 = 40 * k + (1 + 2) from rfl, b_res k 2 (by decide), c4, c5]
  · rw [show 40 * k + 4 = 40 * k + (1 + 3) from rfl, b_res k 3 (by decide), c6, c7]
  · rw [show 40 * k + 5 = 40 * k + (1 + 4) from rfl, b_res k 4 (by decide), c8, c9]
  · rw [show 40 * k + 6 = 40 * k + (1 + 5) from rfl, b_res k 5 (by decide), c10, c11]
  · rw [show 40 * k + 7 = 40 * k + (1 + 6) from rfl, b_res k 6 (by decide), c12, c13]
  · rw [show 40 * k + 8 = 40 * k + (1 + 7) from rfl, b_res k 7 (by decide), c14, c15]

theorem a_closed1 (k : ℕ) :
    a (40 * k + 9) = 168 * k + 40 ∧
    a (40 * k + 10) = 168 * k + 43 ∧
    a (40 * k + 11) = 168 * k + 45 ∧
    a (40 * k + 12) = 168 * k + 49 ∧
    a (40 * k + 13) = 168 * k + 54 ∧
    a (40 * k + 14) = 168 * k + 58 ∧
    a (40 * k + 15) = 168 * k + 62 ∧
    a (40 * k + 16) = 168 * k + 67 := by
  obtain ⟨c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31⟩ := closedK1.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 40 * k + 9 = 40 * k + (1 + 8) from rfl, b_res k 8 (by decide), c16, c17]
  · rw [show 40 * k + 10 = 40 * k + (1 + 9) from rfl, b_res k 9 (by decide), c18, c19]
  · rw [show 40 * k + 11 = 40 * k + (1 + 10) from rfl, b_res k 10 (by decide), c20, c21]
  · rw [show 40 * k + 12 = 40 * k + (1 + 11) from rfl, b_res k 11 (by decide), c22, c23]
  · rw [show 40 * k + 13 = 40 * k + (1 + 12) from rfl, b_res k 12 (by decide), c24, c25]
  · rw [show 40 * k + 14 = 40 * k + (1 + 13) from rfl, b_res k 13 (by decide), c26, c27]
  · rw [show 40 * k + 15 = 40 * k + (1 + 14) from rfl, b_res k 14 (by decide), c28, c29]
  · rw [show 40 * k + 16 = 40 * k + (1 + 15) from rfl, b_res k 15 (by decide), c30, c31]

theorem a_closed2 (k : ℕ) :
    a (40 * k + 17) = 168 * k + 73 ∧
    a (40 * k + 18) = 168 * k + 78 ∧
    a (40 * k + 19) = 168 * k + 81 ∧
    a (40 * k + 20) = 168 * k + 84 ∧
    a (40 * k + 21) = 168 * k + 87 ∧
    a (40 * k + 22) = 168 * k + 90 ∧
    a (40 * k + 23) = 168 * k + 95 ∧
    a (40 * k + 24) = 168 * k + 101 := by
  obtain ⟨c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47⟩ := closedK2.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 40 * k + 17 = 40 * k + (1 + 16) from rfl, b_res k 16 (by decide), c32, c33]
  · rw [show 40 * k + 18 = 40 * k + (1 + 17) from rfl, b_res k 17 (by decide), c34, c35]
  · rw [show 40 * k + 19 = 40 * k + (1 + 18) from rfl, b_res k 18 (by decide), c36, c37]
  · rw [show 40 * k + 20 = 40 * k + (1 + 19) from rfl, b_res k 19 (by decide), c38, c39]
  · rw [show 40 * k + 21 = 40 * k + (1 + 20) from rfl, b_res k 20 (by decide), c40, c41]
  · rw [show 40 * k + 22 = 40 * k + (1 + 21) from rfl, b_res k 21 (by decide), c42, c43]
  · rw [show 40 * k + 23 = 40 * k + (1 + 22) from rfl, b_res k 22 (by decide), c44, c45]
  · rw [show 40 * k + 24 = 40 * k + (1 + 23) from rfl, b_res k 23 (by decide), c46, c47]

theorem a_closed3 (k : ℕ) :
    a (40 * k + 25) = 168 * k + 106 ∧
    a (40 * k + 26) = 168 * k + 110 ∧
    a (40 * k + 27) = 168 * k + 114 ∧
    a (40 * k + 28) = 168 * k + 119 ∧
    a (40 * k + 29) = 168 * k + 123 ∧
    a (40 * k + 30) = 168 * k + 125 ∧
    a (40 * k + 31) = 168 * k + 128 ∧
    a (40 * k + 32) = 168 * k + 133 := by
  obtain ⟨c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63⟩ := closedK3.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 40 * k + 25 = 40 * k + (1 + 24) from rfl, b_res k 24 (by decide), c48, c49]
  · rw [show 40 * k + 26 = 40 * k + (1 + 25) from rfl, b_res k 25 (by decide), c50, c51]
  · rw [show 40 * k + 27 = 40 * k + (1 + 26) from rfl, b_res k 26 (by decide), c52, c53]
  · rw [show 40 * k + 28 = 40 * k + (1 + 27) from rfl, b_res k 27 (by decide), c54, c55]
  · rw [show 40 * k + 29 = 40 * k + (1 + 28) from rfl, b_res k 28 (by decide), c56, c57]
  · rw [show 40 * k + 30 = 40 * k + (1 + 29) from rfl, b_res k 29 (by decide), c58, c59]
  · rw [show 40 * k + 31 = 40 * k + (1 + 30) from rfl, b_res k 30 (by decide), c60, c61]
  · rw [show 40 * k + 32 = 40 * k + (1 + 31) from rfl, b_res k 31 (by decide), c62, c63]

theorem a_closed4 (k : ℕ) :
    a (40 * k + 33) = 168 * k + 139 ∧
    a (40 * k + 34) = 168 * k + 144 ∧
    a (40 * k + 35) = 168 * k + 147 ∧
    a (40 * k + 36) = 168 * k + 151 ∧
    a (40 * k + 37) = 168 * k + 156 ∧
    a (40 * k + 38) = 168 * k + 160 ∧
    a (40 * k + 39) = 168 * k + 164 ∧
    a (40 * k + 40) = 168 * k + 168 := by
  obtain ⟨c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79⟩ := closedK4.down
  simp only [a_eq_b]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 40 * k + 33 = 40 * k + (1 + 32) from rfl, b_res k 32 (by decide), c64, c65]
  · rw [show 40 * k + 34 = 40 * k + (1 + 33) from rfl, b_res k 33 (by decide), c66, c67]
  · rw [show 40 * k + 35 = 40 * k + (1 + 34) from rfl, b_res k 34 (by decide), c68, c69]
  · rw [show 40 * k + 36 = 40 * k + (1 + 35) from rfl, b_res k 35 (by decide), c70, c71]
  · rw [show 40 * k + 37 = 40 * k + (1 + 36) from rfl, b_res k 36 (by decide), c72, c73]
  · rw [show 40 * k + 38 = 40 * k + (1 + 37) from rfl, b_res k 37 (by decide), c74, c75]
  · rw [show 40 * k + 39 = 40 * k + (1 + 38) from rfl, b_res k 38 (by decide), c76, c77]
  · rw [show 40 * k + 40 = 40 * k + (1 + 39) from rfl, b_res k 39 (by decide), c78, c79]

/-- The closed form per residue of n mod 40, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (40 * k + 1) = 168 * k + 4 ∧
    a (40 * k + 2) = 168 * k + 8 ∧
    a (40 * k + 3) = 168 * k + 12 ∧
    a (40 * k + 4) = 168 * k + 17 ∧
    a (40 * k + 5) = 168 * k + 21 ∧
    a (40 * k + 6) = 168 * k + 24 ∧
    a (40 * k + 7) = 168 * k + 29 ∧
    a (40 * k + 8) = 168 * k + 35 ∧
    a (40 * k + 9) = 168 * k + 40 ∧
    a (40 * k + 10) = 168 * k + 43 ∧
    a (40 * k + 11) = 168 * k + 45 ∧
    a (40 * k + 12) = 168 * k + 49 ∧
    a (40 * k + 13) = 168 * k + 54 ∧
    a (40 * k + 14) = 168 * k + 58 ∧
    a (40 * k + 15) = 168 * k + 62 ∧
    a (40 * k + 16) = 168 * k + 67 ∧
    a (40 * k + 17) = 168 * k + 73 ∧
    a (40 * k + 18) = 168 * k + 78 ∧
    a (40 * k + 19) = 168 * k + 81 ∧
    a (40 * k + 20) = 168 * k + 84 ∧
    a (40 * k + 21) = 168 * k + 87 ∧
    a (40 * k + 22) = 168 * k + 90 ∧
    a (40 * k + 23) = 168 * k + 95 ∧
    a (40 * k + 24) = 168 * k + 101 ∧
    a (40 * k + 25) = 168 * k + 106 ∧
    a (40 * k + 26) = 168 * k + 110 ∧
    a (40 * k + 27) = 168 * k + 114 ∧
    a (40 * k + 28) = 168 * k + 119 ∧
    a (40 * k + 29) = 168 * k + 123 ∧
    a (40 * k + 30) = 168 * k + 125 ∧
    a (40 * k + 31) = 168 * k + 128 ∧
    a (40 * k + 32) = 168 * k + 133 ∧
    a (40 * k + 33) = 168 * k + 139 ∧
    a (40 * k + 34) = 168 * k + 144 ∧
    a (40 * k + 35) = 168 * k + 147 ∧
    a (40 * k + 36) = 168 * k + 151 ∧
    a (40 * k + 37) = 168 * k + 156 ∧
    a (40 * k + 38) = 168 * k + 160 ∧
    a (40 * k + 39) = 168 * k + 164 ∧
    a (40 * k + 40) = 168 * k + 168 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := a_closed0 k
  obtain ⟨x8, x9, x10, x11, x12, x13, x14, x15⟩ := a_closed1 k
  obtain ⟨x16, x17, x18, x19, x20, x21, x22, x23⟩ := a_closed2 k
  obtain ⟨x24, x25, x26, x27, x28, x29, x30, x31⟩ := a_closed3 k
  obtain ⟨x32, x33, x34, x35, x36, x37, x38, x39⟩ := a_closed4 k
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39⟩

def controlsK : PLift ((List.range 50).map b = [1, 4, 8, 12, 17, 21, 24, 29, 35, 40, 43, 45, 49, 54, 58, 62, 67, 73, 78, 81, 84, 87, 90, 95, 101, 106, 110, 114, 119, 123, 125, 128, 133, 139, 144, 147, 151, 156, 160, 164, 168, 172, 176, 180, 185, 189, 192, 197, 203, 208]) :=
  ⟨by decide +kernel⟩

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 12, 17, 21, 24, 29, 35, 40, 43, 45, 49, 54, 58, 62, 67, 73, 78, 81, 84, 87, 90, 95, 101, 106, 110, 114, 119, 123, 125, 128, 133, 139, 144, 147, 151, 156, 160, 164, 168, 172, 176, 180, 185, 189, 192, 197, 203, 208] := by
  rw [show a = b from funext a_eq_b]
  exact controlsK.down

/-! The steps satisfy the recurrence, on one period of the residues (negative terms moved across). -/

def drec_baseK : PLift (∀ t : ℕ, t < 40 → dv (t + 16) + 3 * dv (t + 14) + 5 * dv (t + 12) + 7 * dv (t + 10) + 8 * dv (t + 8) + 7 * dv (t + 6) + 5 * dv (t + 4) + 3 * dv (t + 2) + dv (t + 0) = 2 * dv (t + 15) + 4 * dv (t + 13) + 6 * dv (t + 11) + 8 * dv (t + 9) + 8 * dv (t + 7) + 6 * dv (t + 5) + 4 * dv (t + 3) + 2 * dv (t + 1)) :=
  ⟨by decide +kernel⟩

theorem drec_base : ∀ t : ℕ, t < 40 → dv (t + 16) + 3 * dv (t + 14) + 5 * dv (t + 12) + 7 * dv (t + 10) + 8 * dv (t + 8) + 7 * dv (t + 6) + 5 * dv (t + 4) + 3 * dv (t + 2) + dv (t + 0) = 2 * dv (t + 15) + 4 * dv (t + 13) + 6 * dv (t + 11) + 8 * dv (t + 9) + 8 * dv (t + 7) + 6 * dv (t + 5) + 4 * dv (t + 3) + 2 * dv (t + 1) := drec_baseK.down

theorem drec (t : ℕ) : (dv (t + 16) : ℤ) = 2 * (dv (t + 15) : ℤ) - 3 * (dv (t + 14) : ℤ) + 4 * (dv (t + 13) : ℤ) - 5 * (dv (t + 12) : ℤ) + 6 * (dv (t + 11) : ℤ) - 7 * (dv (t + 10) : ℤ) + 8 * (dv (t + 9) : ℤ) - 8 * (dv (t + 8) : ℤ) + 8 * (dv (t + 7) : ℤ) - 7 * (dv (t + 6) : ℤ) + 6 * (dv (t + 5) : ℤ) - 5 * (dv (t + 4) : ℤ) + 4 * (dv (t + 3) : ℤ) - 3 * (dv (t + 2) : ℤ) + 2 * (dv (t + 1) : ℤ) - (dv (t + 0) : ℤ) := by
  have e : ∀ o : ℕ, dv (t + o) = dv (t % 40 + o) := fun o => by
    rw [dv, dv, Nat.mod_add_mod]
  rw [e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9, e 10, e 11, e 12, e 13, e 14, e 15, e 16]
  have h := congrArg (Nat.cast : ℕ → ℤ) (drec_base (t % 40) (Nat.mod_lt _ (by norm_num)))
  push_cast at h
  linarith

/-! The recurrence on its first 40 terms, by the kernel (negative terms moved across). -/

def recur_baseK : PLift (∀ q : ℕ, q < 40 → b (q + 17) + 3 * b (q + 15) + 5 * b (q + 13) + 7 * b (q + 11) + 8 * b (q + 9) + 7 * b (q + 7) + 5 * b (q + 5) + 3 * b (q + 3) + b (q + 1) = 2 * b (q + 16) + 4 * b (q + 14) + 6 * b (q + 12) + 8 * b (q + 10) + 8 * b (q + 8) + 6 * b (q + 6) + 4 * b (q + 4) + 2 * b (q + 2)) :=
  ⟨by decide +kernel⟩

theorem recur_base : ∀ q : ℕ, q < 40 → b (q + 17) + 3 * b (q + 15) + 5 * b (q + 13) + 7 * b (q + 11) + 8 * b (q + 9) + 7 * b (q + 7) + 5 * b (q + 5) + 3 * b (q + 3) + b (q + 1) = 2 * b (q + 16) + 4 * b (q + 14) + 6 * b (q + 12) + 8 * b (q + 10) + 8 * b (q + 8) + 6 * b (q + 6) + 4 * b (q + 4) + 2 * b (q + 2) := recur_baseK.down

theorem b_recur (q : ℕ) : (b (q + 17) : ℤ) = 2 * b (q + 16) - 3 * b (q + 15) + 4 * b (q + 14) - 5 * b (q + 13) + 6 * b (q + 12) - 7 * b (q + 11) + 8 * b (q + 10) - 8 * b (q + 9) + 8 * b (q + 8) - 7 * b (q + 7) + 6 * b (q + 6) - 5 * b (q + 5) + 4 * b (q + 4) - 3 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases (show q < 40 ∨ 40 ≤ q by omega) with hq | hq
    · have h := congrArg (Nat.cast : ℕ → ℤ) (recur_base q hq)
      push_cast at h
      linarith
    · obtain ⟨v, rfl⟩ : ∃ v, q = v + 40 := ⟨q - 40, by omega⟩
      have h0 : (b (v + 17) : ℤ) = 2 * b (v + 16) - 3 * b (v + 15) + 4 * b (v + 14) - 5 * b (v + 13) + 6 * b (v + 12) - 7 * b (v + 11) + 8 * b (v + 10) - 8 * b (v + 9) + 8 * b (v + 8) - 7 * b (v + 7) + 6 * b (v + 6) - 5 * b (v + 5) + 4 * b (v + 4) - 3 * b (v + 3) + 2 * b (v + 2) - b (v + 1) := ih (v + 0) (by omega)
      have hd := drec v
      have s1 : (b (v + 41) : ℤ) = b (v + 1) + dv (v + 0) := by
        have h := b_step (v + 1) (le_trans (by decide : 1 ≤ 1) (Nat.le_add_left _ v))
        rw [show v + 1 + 40 = v + 41 from Nat.add_assoc _ _ _,
          show v + 1 - 1 = v + 0 from Nat.add_sub_assoc (by decide : 1 ≤ 1) v] at h
        exact_mod_cast h
      have s2 : (b (v + 42) : ℤ) = b (v + 2) + dv (v + 1) := by
        have h := b_step (v + 2) (le_trans (by decide : 1 ≤ 2) (Nat.le_add_left _ v))
        rw [show v + 2 + 40 = v + 42 from Nat.add_assoc _ _ _,
          show v + 2 - 1 = v + 1 from Nat.add_sub_assoc (by decide : 1 ≤ 2) v] at h
        exact_mod_cast h
      have s3 : (b (v + 43) : ℤ) = b (v + 3) + dv (v + 2) := by
        have h := b_step (v + 3) (le_trans (by decide : 1 ≤ 3) (Nat.le_add_left _ v))
        rw [show v + 3 + 40 = v + 43 from Nat.add_assoc _ _ _,
          show v + 3 - 1 = v + 2 from Nat.add_sub_assoc (by decide : 1 ≤ 3) v] at h
        exact_mod_cast h
      have s4 : (b (v + 44) : ℤ) = b (v + 4) + dv (v + 3) := by
        have h := b_step (v + 4) (le_trans (by decide : 1 ≤ 4) (Nat.le_add_left _ v))
        rw [show v + 4 + 40 = v + 44 from Nat.add_assoc _ _ _,
          show v + 4 - 1 = v + 3 from Nat.add_sub_assoc (by decide : 1 ≤ 4) v] at h
        exact_mod_cast h
      have s5 : (b (v + 45) : ℤ) = b (v + 5) + dv (v + 4) := by
        have h := b_step (v + 5) (le_trans (by decide : 1 ≤ 5) (Nat.le_add_left _ v))
        rw [show v + 5 + 40 = v + 45 from Nat.add_assoc _ _ _,
          show v + 5 - 1 = v + 4 from Nat.add_sub_assoc (by decide : 1 ≤ 5) v] at h
        exact_mod_cast h
      have s6 : (b (v + 46) : ℤ) = b (v + 6) + dv (v + 5) := by
        have h := b_step (v + 6) (le_trans (by decide : 1 ≤ 6) (Nat.le_add_left _ v))
        rw [show v + 6 + 40 = v + 46 from Nat.add_assoc _ _ _,
          show v + 6 - 1 = v + 5 from Nat.add_sub_assoc (by decide : 1 ≤ 6) v] at h
        exact_mod_cast h
      have s7 : (b (v + 47) : ℤ) = b (v + 7) + dv (v + 6) := by
        have h := b_step (v + 7) (le_trans (by decide : 1 ≤ 7) (Nat.le_add_left _ v))
        rw [show v + 7 + 40 = v + 47 from Nat.add_assoc _ _ _,
          show v + 7 - 1 = v + 6 from Nat.add_sub_assoc (by decide : 1 ≤ 7) v] at h
        exact_mod_cast h
      have s8 : (b (v + 48) : ℤ) = b (v + 8) + dv (v + 7) := by
        have h := b_step (v + 8) (le_trans (by decide : 1 ≤ 8) (Nat.le_add_left _ v))
        rw [show v + 8 + 40 = v + 48 from Nat.add_assoc _ _ _,
          show v + 8 - 1 = v + 7 from Nat.add_sub_assoc (by decide : 1 ≤ 8) v] at h
        exact_mod_cast h
      have s9 : (b (v + 49) : ℤ) = b (v + 9) + dv (v + 8) := by
        have h := b_step (v + 9) (le_trans (by decide : 1 ≤ 9) (Nat.le_add_left _ v))
        rw [show v + 9 + 40 = v + 49 from Nat.add_assoc _ _ _,
          show v + 9 - 1 = v + 8 from Nat.add_sub_assoc (by decide : 1 ≤ 9) v] at h
        exact_mod_cast h
      have s10 : (b (v + 50) : ℤ) = b (v + 10) + dv (v + 9) := by
        have h := b_step (v + 10) (le_trans (by decide : 1 ≤ 10) (Nat.le_add_left _ v))
        rw [show v + 10 + 40 = v + 50 from Nat.add_assoc _ _ _,
          show v + 10 - 1 = v + 9 from Nat.add_sub_assoc (by decide : 1 ≤ 10) v] at h
        exact_mod_cast h
      have s11 : (b (v + 51) : ℤ) = b (v + 11) + dv (v + 10) := by
        have h := b_step (v + 11) (le_trans (by decide : 1 ≤ 11) (Nat.le_add_left _ v))
        rw [show v + 11 + 40 = v + 51 from Nat.add_assoc _ _ _,
          show v + 11 - 1 = v + 10 from Nat.add_sub_assoc (by decide : 1 ≤ 11) v] at h
        exact_mod_cast h
      have s12 : (b (v + 52) : ℤ) = b (v + 12) + dv (v + 11) := by
        have h := b_step (v + 12) (le_trans (by decide : 1 ≤ 12) (Nat.le_add_left _ v))
        rw [show v + 12 + 40 = v + 52 from Nat.add_assoc _ _ _,
          show v + 12 - 1 = v + 11 from Nat.add_sub_assoc (by decide : 1 ≤ 12) v] at h
        exact_mod_cast h
      have s13 : (b (v + 53) : ℤ) = b (v + 13) + dv (v + 12) := by
        have h := b_step (v + 13) (le_trans (by decide : 1 ≤ 13) (Nat.le_add_left _ v))
        rw [show v + 13 + 40 = v + 53 from Nat.add_assoc _ _ _,
          show v + 13 - 1 = v + 12 from Nat.add_sub_assoc (by decide : 1 ≤ 13) v] at h
        exact_mod_cast h
      have s14 : (b (v + 54) : ℤ) = b (v + 14) + dv (v + 13) := by
        have h := b_step (v + 14) (le_trans (by decide : 1 ≤ 14) (Nat.le_add_left _ v))
        rw [show v + 14 + 40 = v + 54 from Nat.add_assoc _ _ _,
          show v + 14 - 1 = v + 13 from Nat.add_sub_assoc (by decide : 1 ≤ 14) v] at h
        exact_mod_cast h
      have s15 : (b (v + 55) : ℤ) = b (v + 15) + dv (v + 14) := by
        have h := b_step (v + 15) (le_trans (by decide : 1 ≤ 15) (Nat.le_add_left _ v))
        rw [show v + 15 + 40 = v + 55 from Nat.add_assoc _ _ _,
          show v + 15 - 1 = v + 14 from Nat.add_sub_assoc (by decide : 1 ≤ 15) v] at h
        exact_mod_cast h
      have s16 : (b (v + 56) : ℤ) = b (v + 16) + dv (v + 15) := by
        have h := b_step (v + 16) (le_trans (by decide : 1 ≤ 16) (Nat.le_add_left _ v))
        rw [show v + 16 + 40 = v + 56 from Nat.add_assoc _ _ _,
          show v + 16 - 1 = v + 15 from Nat.add_sub_assoc (by decide : 1 ≤ 16) v] at h
        exact_mod_cast h
      have s17 : (b (v + 57) : ℤ) = b (v + 17) + dv (v + 16) := by
        have h := b_step (v + 17) (le_trans (by decide : 1 ≤ 17) (Nat.le_add_left _ v))
        rw [show v + 17 + 40 = v + 57 from Nat.add_assoc _ _ _,
          show v + 17 - 1 = v + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) v] at h
        exact_mod_cast h
      show (b (v + 57) : ℤ) = 2 * b (v + 56) - 3 * b (v + 55) + 4 * b (v + 54) - 5 * b (v + 53) + 6 * b (v + 52) - 7 * b (v + 51) + 8 * b (v + 50) - 8 * b (v + 49) + 8 * b (v + 48) - 7 * b (v + 47) + 6 * b (v + 46) - 5 * b (v + 45) + 4 * b (v + 44) - 3 * b (v + 43) + 2 * b (v + 42) - b (v + 41)
      linear_combination s17 - (2) * s16 - (-3) * s15 - (4) * s14 - (-5) * s13 - (6) * s12 - (-7) * s11 - (8) * s10 - (-8) * s9 - (8) * s8 - (-7) * s7 - (6) * s6 - (-5) * s5 - (4) * s4 - (-3) * s3 - (2) * s2 - (-1) * s1 + h0 + hd

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 16 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 8 * a (n - 8) + 8 * a (n - 9) - 7 * a (n - 10) + 6 * a (n - 11) - 5 * a (n - 12) + 4 * a (n - 13) - 3 * a (n - 14) + 2 * a (n - 15) - a (n - 16) := by
  intro n hn
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 17 := ⟨n - 17, by omega⟩
  rw [show q + 17 - 1 = q + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) q, show q + 17 - 2 = q + 15 from Nat.add_sub_assoc (by decide : 2 ≤ 17) q, show q + 17 - 3 = q + 14 from Nat.add_sub_assoc (by decide : 3 ≤ 17) q, show q + 17 - 4 = q + 13 from Nat.add_sub_assoc (by decide : 4 ≤ 17) q, show q + 17 - 5 = q + 12 from Nat.add_sub_assoc (by decide : 5 ≤ 17) q, show q + 17 - 6 = q + 11 from Nat.add_sub_assoc (by decide : 6 ≤ 17) q, show q + 17 - 7 = q + 10 from Nat.add_sub_assoc (by decide : 7 ≤ 17) q, show q + 17 - 8 = q + 9 from Nat.add_sub_assoc (by decide : 8 ≤ 17) q, show q + 17 - 9 = q + 8 from Nat.add_sub_assoc (by decide : 9 ≤ 17) q, show q + 17 - 10 = q + 7 from Nat.add_sub_assoc (by decide : 10 ≤ 17) q, show q + 17 - 11 = q + 6 from Nat.add_sub_assoc (by decide : 11 ≤ 17) q, show q + 17 - 12 = q + 5 from Nat.add_sub_assoc (by decide : 12 ≤ 17) q, show q + 17 - 13 = q + 4 from Nat.add_sub_assoc (by decide : 13 ≤ 17) q, show q + 17 - 14 = q + 3 from Nat.add_sub_assoc (by decide : 14 ≤ 17) q, show q + 17 - 15 = q + 2 from Nat.add_sub_assoc (by decide : 15 ≤ 17) q, show q + 17 - 16 = q + 1 from Nat.add_sub_assoc (by decide : 16 ≤ 17) q]
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
def gfL (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (b n) (Nat.mul 3 (bk n 2))) (Nat.mul 5 (bk n 4))) (Nat.mul 7 (bk n 6))) (Nat.mul 8 (bk n 8))) (Nat.mul 7 (bk n 10))) (Nat.mul 5 (bk n 12))) (Nat.mul 3 (bk n 14))) (bk n 16)

def gfR (n : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul 2 (bk n 1)) (Nat.mul 4 (bk n 3))) (Nat.mul 6 (bk n 5))) (Nat.mul 8 (bk n 7))) (Nat.mul 8 (bk n 9))) (Nat.mul 6 (bk n 11))) (Nat.mul 4 (bk n 13))) (Nat.mul 2 (bk n 15))) (ind n 0)) (Nat.mul 2 (ind n 1))) (Nat.mul 3 (ind n 2))) (Nat.mul 4 (ind n 3))) (Nat.mul 6 (ind n 4))) (Nat.mul 5 (ind n 5))) (Nat.mul 8 (ind n 6))) (Nat.mul 8 (ind n 7))) (Nat.mul 10 (ind n 8))) (Nat.mul 8 (ind n 9))) (Nat.mul 8 (ind n 10))) (Nat.mul 5 (ind n 11))) (Nat.mul 6 (ind n 12))) (Nat.mul 4 (ind n 13))) (Nat.mul 3 (ind n 14))) (Nat.mul 2 (ind n 15))) (ind n 16)

def gfK : PLift ((allR 17 fun n => Nat.beq (gfL n) (gfR n)) = true) :=
  ⟨by decide +kernel⟩

/-- The coefficient identity of the g.f. below 17, from the kernel check. -/
theorem gf_low (n : ℕ) (hn : n < 17) :
    1 * (b (n) : ℚ) - 2 * (if 1 ≤ n then (b (n - 1) : ℚ) else 0) + 3 * (if 2 ≤ n then (b (n - 2) : ℚ) else 0) - 4 * (if 3 ≤ n then (b (n - 3) : ℚ) else 0) + 5 * (if 4 ≤ n then (b (n - 4) : ℚ) else 0) - 6 * (if 5 ≤ n then (b (n - 5) : ℚ) else 0) + 7 * (if 6 ≤ n then (b (n - 6) : ℚ) else 0) - 8 * (if 7 ≤ n then (b (n - 7) : ℚ) else 0) + 8 * (if 8 ≤ n then (b (n - 8) : ℚ) else 0) - 8 * (if 9 ≤ n then (b (n - 9) : ℚ) else 0) + 7 * (if 10 ≤ n then (b (n - 10) : ℚ) else 0) - 6 * (if 11 ≤ n then (b (n - 11) : ℚ) else 0) + 5 * (if 12 ≤ n then (b (n - 12) : ℚ) else 0) - 4 * (if 13 ≤ n then (b (n - 13) : ℚ) else 0) + 3 * (if 14 ≤ n then (b (n - 14) : ℚ) else 0) - 2 * (if 15 ≤ n then (b (n - 15) : ℚ) else 0) + 1 * (if 16 ≤ n then (b (n - 16) : ℚ) else 0) =
      (if n = 0 then (1 : ℚ) else 0) * 1 + (if n = 1 then (1 : ℚ) else 0) * 2 + (if n = 2 then (1 : ℚ) else 0) * 3 + (if n = 3 then (1 : ℚ) else 0) * 4 + (if n = 4 then (1 : ℚ) else 0) * 6 + (if n = 5 then (1 : ℚ) else 0) * 5 + (if n = 6 then (1 : ℚ) else 0) * 8 + (if n = 7 then (1 : ℚ) else 0) * 8 + (if n = 8 then (1 : ℚ) else 0) * 10 + (if n = 9 then (1 : ℚ) else 0) * 8 + (if n = 10 then (1 : ℚ) else 0) * 8 + (if n = 11 then (1 : ℚ) else 0) * 5 + (if n = 12 then (1 : ℚ) else 0) * 6 + (if n = 13 then (1 : ℚ) else 0) * 4 + (if n = 14 then (1 : ℚ) else 0) * 3 + (if n = 15 then (1 : ℚ) else 0) * 2 + (if n = 16 then (1 : ℚ) else 0) * 1 := by
  have h := (allR_iff _ _).1 gfK.down n hn
  rw [Nat.beq_eq] at h
  have hq := congrArg (Nat.cast : ℕ → ℚ) h
  simp only [gfL, gfR, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, cast_bk, cast_ind] at hq
  linarith

/-- The coefficient identity of the g.f. from 17 on, from the recurrence. -/
theorem gf_high (q : ℕ) :
    1 * (b (q + 17) : ℚ) - 2 * (if 1 ≤ q + 17 then (b (q + 17 - 1) : ℚ) else 0) + 3 * (if 2 ≤ q + 17 then (b (q + 17 - 2) : ℚ) else 0) - 4 * (if 3 ≤ q + 17 then (b (q + 17 - 3) : ℚ) else 0) + 5 * (if 4 ≤ q + 17 then (b (q + 17 - 4) : ℚ) else 0) - 6 * (if 5 ≤ q + 17 then (b (q + 17 - 5) : ℚ) else 0) + 7 * (if 6 ≤ q + 17 then (b (q + 17 - 6) : ℚ) else 0) - 8 * (if 7 ≤ q + 17 then (b (q + 17 - 7) : ℚ) else 0) + 8 * (if 8 ≤ q + 17 then (b (q + 17 - 8) : ℚ) else 0) - 8 * (if 9 ≤ q + 17 then (b (q + 17 - 9) : ℚ) else 0) + 7 * (if 10 ≤ q + 17 then (b (q + 17 - 10) : ℚ) else 0) - 6 * (if 11 ≤ q + 17 then (b (q + 17 - 11) : ℚ) else 0) + 5 * (if 12 ≤ q + 17 then (b (q + 17 - 12) : ℚ) else 0) - 4 * (if 13 ≤ q + 17 then (b (q + 17 - 13) : ℚ) else 0) + 3 * (if 14 ≤ q + 17 then (b (q + 17 - 14) : ℚ) else 0) - 2 * (if 15 ≤ q + 17 then (b (q + 17 - 15) : ℚ) else 0) + 1 * (if 16 ≤ q + 17 then (b (q + 17 - 16) : ℚ) else 0) =
      (if q + 17 = 0 then (1 : ℚ) else 0) * 1 + (if q + 17 = 1 then (1 : ℚ) else 0) * 2 + (if q + 17 = 2 then (1 : ℚ) else 0) * 3 + (if q + 17 = 3 then (1 : ℚ) else 0) * 4 + (if q + 17 = 4 then (1 : ℚ) else 0) * 6 + (if q + 17 = 5 then (1 : ℚ) else 0) * 5 + (if q + 17 = 6 then (1 : ℚ) else 0) * 8 + (if q + 17 = 7 then (1 : ℚ) else 0) * 8 + (if q + 17 = 8 then (1 : ℚ) else 0) * 10 + (if q + 17 = 9 then (1 : ℚ) else 0) * 8 + (if q + 17 = 10 then (1 : ℚ) else 0) * 8 + (if q + 17 = 11 then (1 : ℚ) else 0) * 5 + (if q + 17 = 12 then (1 : ℚ) else 0) * 6 + (if q + 17 = 13 then (1 : ℚ) else 0) * 4 + (if q + 17 = 14 then (1 : ℚ) else 0) * 3 + (if q + 17 = 15 then (1 : ℚ) else 0) * 2 + (if q + 17 = 16 then (1 : ℚ) else 0) * 1 := by
  have h : (b (q + 17) : ℤ) = 2 * b (q + 16) - 3 * b (q + 15) + 4 * b (q + 14) - 5 * b (q + 13) + 6 * b (q + 12) - 7 * b (q + 11) + 8 * b (q + 10) - 8 * b (q + 9) + 8 * b (q + 8) - 7 * b (q + 7) + 6 * b (q + 6) - 5 * b (q + 5) + 4 * b (q + 4) - 3 * b (q + 3) + 2 * b (q + 2) - b (q + 1) := b_recur (q + 0)
  have hq := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hq
  simp only [show q + 17 - 1 = q + 16 from Nat.add_sub_assoc (by decide : 1 ≤ 17) q, show q + 17 - 2 = q + 15 from Nat.add_sub_assoc (by decide : 2 ≤ 17) q, show q + 17 - 3 = q + 14 from Nat.add_sub_assoc (by decide : 3 ≤ 17) q, show q + 17 - 4 = q + 13 from Nat.add_sub_assoc (by decide : 4 ≤ 17) q, show q + 17 - 5 = q + 12 from Nat.add_sub_assoc (by decide : 5 ≤ 17) q, show q + 17 - 6 = q + 11 from Nat.add_sub_assoc (by decide : 6 ≤ 17) q, show q + 17 - 7 = q + 10 from Nat.add_sub_assoc (by decide : 7 ≤ 17) q, show q + 17 - 8 = q + 9 from Nat.add_sub_assoc (by decide : 8 ≤ 17) q, show q + 17 - 9 = q + 8 from Nat.add_sub_assoc (by decide : 9 ≤ 17) q, show q + 17 - 10 = q + 7 from Nat.add_sub_assoc (by decide : 10 ≤ 17) q, show q + 17 - 11 = q + 6 from Nat.add_sub_assoc (by decide : 11 ≤ 17) q, show q + 17 - 12 = q + 5 from Nat.add_sub_assoc (by decide : 12 ≤ 17) q, show q + 17 - 13 = q + 4 from Nat.add_sub_assoc (by decide : 13 ≤ 17) q, show q + 17 - 14 = q + 3 from Nat.add_sub_assoc (by decide : 14 ≤ 17) q, show q + 17 - 15 = q + 2 from Nat.add_sub_assoc (by decide : 15 ≤ 17) q, show q + 17 - 16 = q + 1 from Nat.add_sub_assoc (by decide : 16 ≤ 17) q, show 1 ≤ q + 17 from le_trans (by decide : 1 ≤ 17) (Nat.le_add_left 17 q), show 2 ≤ q + 17 from le_trans (by decide : 2 ≤ 17) (Nat.le_add_left 17 q), show 3 ≤ q + 17 from le_trans (by decide : 3 ≤ 17) (Nat.le_add_left 17 q), show 4 ≤ q + 17 from le_trans (by decide : 4 ≤ 17) (Nat.le_add_left 17 q), show 5 ≤ q + 17 from le_trans (by decide : 5 ≤ 17) (Nat.le_add_left 17 q), show 6 ≤ q + 17 from le_trans (by decide : 6 ≤ 17) (Nat.le_add_left 17 q), show 7 ≤ q + 17 from le_trans (by decide : 7 ≤ 17) (Nat.le_add_left 17 q), show 8 ≤ q + 17 from le_trans (by decide : 8 ≤ 17) (Nat.le_add_left 17 q), show 9 ≤ q + 17 from le_trans (by decide : 9 ≤ 17) (Nat.le_add_left 17 q), show 10 ≤ q + 17 from le_trans (by decide : 10 ≤ 17) (Nat.le_add_left 17 q), show 11 ≤ q + 17 from le_trans (by decide : 11 ≤ 17) (Nat.le_add_left 17 q), show 12 ≤ q + 17 from le_trans (by decide : 12 ≤ 17) (Nat.le_add_left 17 q), show 13 ≤ q + 17 from le_trans (by decide : 13 ≤ 17) (Nat.le_add_left 17 q), show 14 ≤ q + 17 from le_trans (by decide : 14 ≤ 17) (Nat.le_add_left 17 q), show 15 ≤ q + 17 from le_trans (by decide : 15 ≤ 17) (Nat.le_add_left 17 q), show 16 ≤ q + 17 from le_trans (by decide : 16 ≤ 17) (Nat.le_add_left 17 q), show ¬ q + 17 = 0 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 1 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 2 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 3 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 3 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 4 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 5 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 6 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 6 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 7 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 8 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 8 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 9 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 9 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 10 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 10 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 11 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 11 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 12 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 12 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 13 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 13 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 14 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 14 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 15 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 15 < 17) (Nat.le_add_left 17 q)), show ¬ q + 17 = 16 from Nat.ne_of_gt (lt_of_lt_of_le (by decide : 16 < 17) (Nat.le_add_left 17 q)), if_true, if_false]
  linear_combination (1) * hq

open PowerSeries in
/-- The denominator times A, as a sum of monomials. -/
theorem gf_den (A : ℚ⟦X⟧) : A * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) = C 1 * A - C 2 * (A * X ^ 1) + C 3 * (A * X ^ 2) - C 4 * (A * X ^ 3) + C 5 * (A * X ^ 4) - C 6 * (A * X ^ 5) + C 7 * (A * X ^ 6) - C 8 * (A * X ^ 7) + C 8 * (A * X ^ 8) - C 8 * (A * X ^ 9) + C 7 * (A * X ^ 10) - C 6 * (A * X ^ 11) + C 5 * (A * X ^ 12) - C 4 * (A * X ^ 13) + C 3 * (A * X ^ 14) - C 2 * (A * X ^ 15) + C 1 * (A * X ^ 16) := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The numerator as a sum of monomials. -/
theorem gf_num : (X ^ 16 + 2 * X ^ 15 + 3 * X ^ 14 + 4 * X ^ 13 + 6 * X ^ 12 + 5 * X ^ 11 + 8 * X ^ 10 + 8 * X ^ 9 + 10 * X ^ 8 + 8 * X ^ 7 + 8 * X ^ 6 + 5 * X ^ 5 + 6 * X ^ 4 + 4 * X ^ 3 + 3 * X ^ 2 + 2 * X + 1 : ℚ⟦X⟧) = X ^ 0 * C 1 + X ^ 1 * C 2 + X ^ 2 * C 3 + X ^ 3 * C 4 + X ^ 4 * C 6 + X ^ 5 * C 5 + X ^ 6 * C 8 + X ^ 7 * C 8 + X ^ 8 * C 10 + X ^ 9 * C 8 + X ^ 10 * C 8 + X ^ 11 * C 5 + X ^ 12 * C 6 + X ^ 13 * C 4 + X ^ 14 * C 3 + X ^ 15 * C 2 + X ^ 16 * C 1 := by
  simp only [map_ofNat, map_one]
  ring

open PowerSeries in
/-- The generating function. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 16 + 2 * X ^ 15 + 3 * X ^ 14 + 4 * X ^ 13 + 6 * X ^ 12 + 5 * X ^ 11 + 8 * X ^ 10 + 8 * X ^ 9 + 10 * X ^ 8 + 8 * X ^ 7 + 8 * X ^ 6 + 5 * X ^ 5 + 6 * X ^ 4 + 4 * X ^ 3 + 3 * X ^ 2 + 2 * X + 1 := by
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
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 16 + 2 * X ^ 15 + 3 * X ^ 14 + 4 * X ^ 13 + 6 * X ^ 12 + 5 * X ^ 11 + 8 * X ^ 10 + 8 * X ^ 9 + 10 * X ^ 8 + 8 * X ^ 7 + 8 * X ^ 6 + 5 * X ^ 5 + 6 * X ^ 4 + 4 * X ^ 3 + 3 * X ^ 2 + 2 * X + 1 := Count.gf

/-- The recurrence. -/
theorem recur : ∀ n : ℕ, 16 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 8 * a (n - 8) + 8 * a (n - 9) - 7 * a (n - 10) + 6 * a (n - 11) - 5 * a (n - 12) + 4 * a (n - 13) - 3 * a (n - 14) + 2 * a (n - 15) - a (n - 16) := Count.recur

/-- Controls: the entry's data a(0..49). -/
theorem controls : (List.range 50).map a =
    [1, 4, 8, 12, 17, 21, 24, 29, 35, 40, 43, 45, 49, 54, 58, 62, 67, 73, 78, 81, 84, 87, 90, 95, 101, 106, 110, 114, 119, 123, 125, 128, 133, 139, 144, 147, 151, 156, 160, 164, 168, 172, 176, 180, 185, 189, 192, 197, 203, 208] := Count.controls

/-- The step a(n + 40) = a(n) + 168 for n ≥ 1. -/
theorem a_step (n : ℕ) (hn : 1 ≤ n) : a (n + 40) = a n + 168 := Count.a_step n hn

/-- The closed form per residue of n mod 40, for n ≥ 1. -/
theorem a_closed (k : ℕ) :
    a (40 * k + 1) = 168 * k + 4 ∧
    a (40 * k + 2) = 168 * k + 8 ∧
    a (40 * k + 3) = 168 * k + 12 ∧
    a (40 * k + 4) = 168 * k + 17 ∧
    a (40 * k + 5) = 168 * k + 21 ∧
    a (40 * k + 6) = 168 * k + 24 ∧
    a (40 * k + 7) = 168 * k + 29 ∧
    a (40 * k + 8) = 168 * k + 35 ∧
    a (40 * k + 9) = 168 * k + 40 ∧
    a (40 * k + 10) = 168 * k + 43 ∧
    a (40 * k + 11) = 168 * k + 45 ∧
    a (40 * k + 12) = 168 * k + 49 ∧
    a (40 * k + 13) = 168 * k + 54 ∧
    a (40 * k + 14) = 168 * k + 58 ∧
    a (40 * k + 15) = 168 * k + 62 ∧
    a (40 * k + 16) = 168 * k + 67 ∧
    a (40 * k + 17) = 168 * k + 73 ∧
    a (40 * k + 18) = 168 * k + 78 ∧
    a (40 * k + 19) = 168 * k + 81 ∧
    a (40 * k + 20) = 168 * k + 84 ∧
    a (40 * k + 21) = 168 * k + 87 ∧
    a (40 * k + 22) = 168 * k + 90 ∧
    a (40 * k + 23) = 168 * k + 95 ∧
    a (40 * k + 24) = 168 * k + 101 ∧
    a (40 * k + 25) = 168 * k + 106 ∧
    a (40 * k + 26) = 168 * k + 110 ∧
    a (40 * k + 27) = 168 * k + 114 ∧
    a (40 * k + 28) = 168 * k + 119 ∧
    a (40 * k + 29) = 168 * k + 123 ∧
    a (40 * k + 30) = 168 * k + 125 ∧
    a (40 * k + 31) = 168 * k + 128 ∧
    a (40 * k + 32) = 168 * k + 133 ∧
    a (40 * k + 33) = 168 * k + 139 ∧
    a (40 * k + 34) = 168 * k + 144 ∧
    a (40 * k + 35) = 168 * k + 147 ∧
    a (40 * k + 36) = 168 * k + 151 ∧
    a (40 * k + 37) = 168 * k + 156 ∧
    a (40 * k + 38) = 168 * k + 160 ∧
    a (40 * k + 39) = 168 * k + 164 ∧
    a (40 * k + 40) = 168 * k + 168 := Count.a_closed k

/-- The deviation a n - 21 n / 5 repeats with period 40, since a (n + 40) = a n + 168 for n ≥ 1
and 168 / 40 = 21 / 5, so it is bounded. -/
theorem a_dev_bound : ∃ M : ℝ, ∀ n : ℕ, |(a n : ℝ) - 21 * (n : ℝ) / 5| ≤ M := by
  refine ⟨∑ j ∈ Finset.range (40 + 1), |(a j : ℝ) - 21 * (j : ℝ) / 5|, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ 40
    · exact Finset.single_le_sum (f := fun j => |(a j : ℝ) - 21 * (j : ℝ) / 5|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 40 := ⟨n - 40, by omega⟩
      have h1 : (a (m + 40) : ℝ) = (a m : ℝ) + 168 := by exact_mod_cast a_step m (by omega)
      have e : (a (m + 40) : ℝ) - 21 * ((m + 40 : ℕ) : ℝ) / 5 = (a m : ℝ) - 21 * (m : ℝ) / 5 := by
        rw [h1]
        push_cast
        ring
      rw [e]
      exact ih m (by omega)

/-- Conjunct 3 of main: a(n) ~ 21 n / 5. -/
theorem conj3 : Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => 21 * (n : ℝ) / 5) := by
  obtain ⟨M, hM⟩ := a_dev_bound
  have hO : ((fun n : ℕ => (a n : ℝ)) - (fun n : ℕ => 21 * (n : ℝ) / 5)) =O[Filter.atTop] (fun _ => (1 : ℝ)) :=
    Asymptotics.IsBigO.of_bound M (Filter.Eventually.of_forall fun n => by simpa using hM n)
  have ht : Filter.Tendsto (fun n : ℕ => 21 * (n : ℝ) / 5) Filter.atTop Filter.atTop := by
    exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)).atTop_div_const (by norm_num)
  have ho : (fun _ : ℕ => (1 : ℝ)) =o[Filter.atTop] (fun n : ℕ => 21 * (n : ℝ) / 5) := by
    rw [Asymptotics.isLittleO_one_left_iff]
    first
    | simpa [Real.norm_eq_abs, Function.comp_def] using ht
    | simpa [Real.norm_eq_abs, Function.comp_def] using Filter.tendsto_abs_atTop_atTop.comp ht
  exact hO.trans_isLittleO ho

open PowerSeries in
/-- main of the statement, word for word. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (X ^ 2 + 1) * (X ^ 4 + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X ^ 16 + 2 * X ^ 15 + 3 * X ^ 14 + 4 * X ^ 13 + 6 * X ^ 12 + 5 * X ^ 11 + 8 * X ^ 10 + 8 * X ^ 9 + 10 * X ^ 8 + 8 * X ^ 7 + 8 * X ^ 6 + 5 * X ^ 5 + 6 * X ^ 4 + 4 * X ^ 3 + 3 * X ^ 2 + 2 * X + 1 ∧
    (∀ n : ℕ, 16 < n → (a n : ℤ) = 2 * a (n - 1) - 3 * a (n - 2) + 4 * a (n - 3) - 5 * a (n - 4) + 6 * a (n - 5) - 7 * a (n - 6) + 8 * a (n - 7) - 8 * a (n - 8) + 8 * a (n - 9) - 7 * a (n - 10) + 6 * a (n - 11) - 5 * a (n - 12) + 4 * a (n - 13) - 3 * a (n - 14) + 2 * a (n - 15) - a (n - 16)) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => 21 * (n : ℝ) / 5) :=
  ⟨gf, recur, conj3⟩

end OMA.S_oeis_a311416

theorem OMA.solution : type_of% @OMA.S_oeis_a311416.main :=
  OMA.S_oeis_a311416.conjecture
