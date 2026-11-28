import OMAStatements.S_oeis_a227266

/-!
Proof for A227266. Count indicator arrays by a subset construction read from the top row down. A
state is a row of the larger array with one flag per pair of adjacent columns, true while those two
columns are still equal; Acc m q B says that some sorted larger array continues from the state q and
indicates B. For a set S of states, W m S counts the arrays B that some state of S accepts, and
W (m + 1) S is a sum of W m over the image sets. The reachable sets are listed as bit masks of state
codes with their transition table; the kernel checks the one-step images, the tables of W at the
first levels, and the recurrence at its first level, and the recurrence then holds at every level for
every reachable set. The g.f. step follows the pattern of the merged proof of oeis-a202456 by @jleguina.
-/

namespace OMA.S_oeis_a227266

open PowerSeries Finset

abbrev Row := Fin 4 → Fin 2
abbrev Ltr := Fin 3 → Fin 2
abbrev Flg := Fin 3 → Bool
abbrev St := Row × Flg

theorem lex_cons {m : ℕ} (x y : Fin (m + 1) → Fin 2) :
    LexLE x y ↔ x 0 ≤ y 0 ∧ (x 0 = y 0 → LexLE (Fin.tail x) (Fin.tail y)) := by
  unfold LexLE
  rw [Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨h0 (fun i hi => absurd hi (Fin.not_lt_zero i)), fun he p hp => hs p ?_⟩
    intro i hi
    induction i using Fin.cases with
    | zero => exact he
    | succ i' => exact hp i' (Fin.succ_lt_succ_iff.mp hi)
  · rintro ⟨h0, ht⟩
    refine ⟨fun _ => h0, fun p hp => ?_⟩
    have he : x 0 = y 0 := hp 0 (Fin.succ_pos p)
    exact ht he p (fun i hi => hp i.succ (Fin.succ_lt_succ_iff.mpr hi))

theorem lex_zero (x y : Fin 0 → Fin 2) : LexLE x y := fun p => p.elim0

/-- The indicator letter of the row pair (r, s). -/
def ltr (r s : Row) : Ltr := fun j =>
  if blk (r j.castSucc) (r j.succ) (s j.castSucc) (s j.succ) then 1 else 0

/-- The flagged column pairs of the rows below the first are in nondecreasing order. -/
def ColsOK {m : ℕ} (g : Flg) (A : Fin (m + 1) → Row) : Prop :=
  ∀ j, g j = true → LexLE (fun i : Fin m => A i.succ j.castSucc) (fun i => A i.succ j.succ)

/-- Some sorted continuation of the state q indicates B. -/
def Acc (m : ℕ) (q : St) (B : Fin m → Ltr) : Prop :=
  ∃ A : Fin (m + 1) → Row, A 0 = q.1 ∧ (∀ i : Fin m, LexLE (A i.castSucc) (A i.succ)) ∧
    ColsOK q.2 A ∧ ind A = B

/-- The flags after the row s. -/
def nxt (g : Flg) (s : Row) : Flg := fun j => g j && decide (s j.castSucc = s j.succ)

/-- One step of the automaton, reading the letter b. -/
def Trans (q : St) (b : Ltr) (q' : St) : Prop :=
  LexLE q.1 q'.1 ∧ (∀ j, q.2 j = true → q'.1 j.castSucc ≤ q'.1 j.succ) ∧ ltr q.1 q'.1 = b ∧
    q'.2 = nxt q.2 q'.1

instance (q : St) (b : Ltr) (q' : St) : Decidable (Trans q b q') := by
  unfold Trans; infer_instance

theorem acc_zero (q : St) (B : Fin 0 → Ltr) : Acc 0 q B :=
  ⟨fun _ => q.1, rfl, fun i => i.elim0, fun _ _ => lex_zero _ _, funext fun i => i.elim0⟩

theorem acc_succ (m : ℕ) (q : St) (b : Ltr) (B : Fin m → Ltr) :
    Acc (m + 1) q (Fin.cons b B) ↔ ∃ q', Trans q b q' ∧ Acc m q' B := by
  constructor
  · rintro ⟨A, h0, hr, hc, hi⟩
    refine ⟨(A (Fin.succ 0), nxt q.2 (A (Fin.succ 0))), ⟨?_, ?_, ?_, rfl⟩, Fin.tail A, rfl, ?_, ?_, ?_⟩
    · have := hr 0
      rwa [Fin.castSucc_zero, h0] at this
    · intro j hj
      exact ((lex_cons _ _).1 (hc j hj)).1
    · have := congrFun hi 0
      rw [Fin.cons_zero] at this
      rw [← this, ← h0]
      rfl
    · intro i
      exact hr i.succ
    · intro j hj
      simp only [nxt, Bool.and_eq_true, decide_eq_true_eq] at hj
      exact ((lex_cons _ _).1 (hc j hj.1)).2 hj.2
    · funext i
      have := congrFun hi i.succ
      rw [Fin.cons_succ] at this
      rw [← this]
      rfl
  · rintro ⟨q', ⟨ht1, ht2, ht3, ht4⟩, A', h0, hr, hc, hi⟩
    refine ⟨Fin.cons q.1 A', rfl, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero =>
        show LexLE q.1 (A' 0)
        rw [h0]; exact ht1
      | succ i =>
        show LexLE (A' i.castSucc) (A' i.succ)
        exact hr i
    · intro j hj
      rw [lex_cons]
      refine ⟨?_, fun he => ?_⟩
      · show A' 0 j.castSucc ≤ A' 0 j.succ
        rw [h0]; exact ht2 j hj
      · have hg : q'.2 j = true := by
          rw [ht4]
          simp only [nxt, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨hj, ?_⟩
          have he' : A' 0 j.castSucc = A' 0 j.succ := he
          rwa [h0] at he'
        exact hc j hg
    · funext i
      induction i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero, ← ht3, ← h0]
        rfl
      | succ i =>
        rw [Fin.cons_succ, ← hi]
        rfl

open Classical in
/-- The number of arrays B accepted by some state of S. -/
noncomputable def W (m : ℕ) (S : St → Prop) : ℕ :=
  (univ.filter fun B : Fin m → Ltr => ∃ q, S q ∧ Acc m q B).card

theorem W_succ (m : ℕ) (S : St → Prop) :
    W (m + 1) S = ∑ b : Ltr, W m (fun q' => ∃ q, S q ∧ Trans q b q') := by
  unfold W
  rw [Finset.card_filter, ← (Fin.consEquiv fun _ => Ltr).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  have e : (∃ q, S q ∧ Acc (m + 1) q (Fin.cons b B)) ↔
      ∃ q', (∃ q, S q ∧ Trans q b q') ∧ Acc m q' B := by
    simp only [acc_succ]
    constructor
    · rintro ⟨q, hq, q', ht, ha⟩; exact ⟨q', ⟨q, hq, ht⟩, ha⟩
    · rintro ⟨q', ⟨q, hq, ht⟩, ha⟩; exact ⟨q, hq, q', ht, ha⟩
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (e.1 h1) h2
  · exact absurd (e.2 h2) h1
  · rfl

open Classical in
theorem W_zero (S : St → Prop) : W 0 S = if ∃ q, S q then 1 else 0 := by
  unfold W
  rw [Finset.card_filter, Fintype.sum_unique]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (let ⟨q, hq, _⟩ := h1; ⟨q, hq⟩) h2
  · exact absurd (let ⟨q, hq⟩ := h2; ⟨q, hq, acc_zero q _⟩) h1
  · rfl

/-- The code of a state. -/
def enc (q : St) : ℕ := 1 * (q.1 0).val + 2 * (q.1 1).val + 4 * (q.1 2).val + 8 * (q.1 3).val + 16 * (q.2 0).toNat + 32 * (q.2 1).toNat + 64 * (q.2 2).toNat

/-- The state of a code. -/
def dec (t : ℕ) : St :=
  (fun j => ⟨t / 2 ^ j.val % 2, Nat.mod_lt _ (by norm_num)⟩, fun j => decide (t / 2 ^ (4 + j.val) % 2 = 1))

/-- The code of a letter. -/
def encB (b : Ltr) : ℕ := 1 * (b 0).val + 2 * (b 1).val + 4 * (b 2).val

theorem st_eta (q : St) : q = (![q.1 0, q.1 1, q.1 2, q.1 3], ![q.2 0, q.2 1, q.2 2]) := by
  obtain ⟨r, g⟩ := q
  refine Prod.ext ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

theorem ltr_eta (b : Ltr) : b = ![b 0, b 1, b 2] := by
  funext j; fin_cases j <;> rfl

theorem forall_st {P : St → Prop} (h : ∀ a0 a1 a2 a3 : Fin 2, ∀ g0 g1 g2 : Bool, P (![a0, a1, a2, a3], ![g0, g1, g2])) :
    ∀ q, P q := fun q => by rw [st_eta q]; exact h _ _ _ _ _ _ _

theorem enc_lt : ∀ q, enc q < 128 := forall_st (by decide)

theorem enc_dec : ∀ t, t < 128 → enc (dec t) = t := by decide

theorem encB_lt (b : Ltr) : encB b < 8 := by
  have h : ∀ b0 b1 b2 : Fin 2, encB ![b0, b1, b2] < 8 := by decide
  rw [ltr_eta b]; exact h _ _ _

/-- The one-step image masks, indexed by state code and letter code. -/
def imgT : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 65535],
   [0, 0, 0, 0, 0, 0, 0, 43690],
   [0, 0, 0, 0, 0, 0, 0, 61166],
   [0, 0, 0, 0, 0, 0, 34952, 0],
   [0, 0, 0, 0, 0, 0, 0, 65278],
   [0, 0, 0, 0, 0, 0, 0, 43176],
   [0, 0, 0, 0, 0, 49344, 0, 10794],
   [0, 0, 0, 0, 32896, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 65534],
   [0, 0, 0, 0, 0, 0, 0, 43688],
   [0, 0, 0, 0, 0, 0, 0, 61162],
   [0, 0, 0, 0, 0, 0, 34944, 0],
   [0, 0, 0, 61440, 0, 0, 0, 3822],
   [0, 0, 0, 40960, 0, 0, 0, 2184],
   [0, 49152, 0, 8192, 0, 128, 0, 2602],
   [32768, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2576958532],
   [0, 0, 0, 0, 0, 0, 0, 2290614272],
   [0, 0, 0, 0, 0, 0, 0, 2290631748],
   [0, 0, 0, 0, 0, 0, 2290614272, 0],
   [0, 0, 0, 0, 0, 0, 0, 2560115780],
   [0, 0, 0, 0, 0, 0, 0, 2290614272],
   [0, 0, 0, 0, 0, 2155888704, 0, 134742016],
   [0, 0, 0, 0, 2155872256, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2576892996],
   [0, 0, 0, 0, 0, 0, 0, 2290614272],
   [0, 0, 0, 0, 0, 0, 0, 2290631744],
   [0, 0, 0, 0, 0, 0, 2290089984, 0],
   [0, 0, 0, 2415935488, 0, 0, 0, 143131716],
   [0, 0, 0, 2147483648, 0, 0, 0, 143130624],
   [0, 2147500032, 0, 0, 0, 8388608, 0, 134742016],
   [2147483648, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 215242286051376],
   [0, 0, 0, 0, 0, 0, 0, 143494857367584],
   [0, 0, 0, 0, 0, 0, 0, 214138479452192],
   [0, 0, 0, 0, 0, 0, 141287244169216, 0],
   [0, 0, 0, 0, 0, 0, 0, 214138479456304],
   [0, 0, 0, 0, 0, 0, 0, 141287244177440],
   [0, 0, 0, 0, 0, 211930866253824, 0, 2207613198368],
   [0, 0, 0, 0, 141287244169216, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 215237991084080],
   [0, 0, 0, 0, 0, 0, 0, 143486267432992],
   [0, 0, 0, 0, 0, 0, 0, 214138479452192],
   [0, 0, 0, 0, 0, 0, 141287244169216, 0],
   [0, 0, 0, 211106232545280, 0, 0, 0, 3032246911008],
   [0, 0, 0, 140737488363520, 0, 0, 0, 549755813888],
   [0, 211106232532992, 0, 8192, 0, 549755813888, 0, 2207613190176],
   [140737488355328, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 9331810546779947008],
   [0, 0, 0, 0, 0, 0, 0, 9259400833873739776],
   [0, 0, 0, 0, 0, 0, 0, 9259471477495824384],
   [0, 0, 0, 0, 0, 0, 9259400833873739776, 0],
   [0, 0, 0, 0, 0, 0, 0, 9259471477765308416],
   [0, 0, 0, 0, 0, 0, 0, 9259400833873739776],
   [0, 0, 0, 0, 0, 9259471477495824384, 0, 0],
   [0, 0, 0, 0, 9259400833873739776, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 9331529071803236352],
   [0, 0, 0, 0, 0, 0, 0, 9259400833873739776],
   [0, 0, 0, 0, 0, 0, 0, 9259471477495824384],
   [0, 0, 0, 0, 0, 0, 9259400833873739776, 0],
   [0, 0, 0, 9223442405867388928, 0, 0, 0, 36029071896870912],
   [0, 0, 0, 9223372036854775808, 0, 0, 0, 36028797018963968],
   [0, 9223442405598953472, 0, 0, 0, 36028797018963968, 0, 0],
   [9223372036854775808, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1133644657049820494565120],
   [0, 0, 0, 0, 0, 0, 0, 755763104699880329710080],
   [0, 0, 0, 0, 0, 0, 0, 1058068346579832461594112],
   [0, 0, 0, 0, 0, 0, 604610483759904263768064, 0],
   [0, 0, 0, 0, 0, 0, 0, 1133626210305746785013248],
   [0, 0, 0, 0, 0, 0, 0, 755726211211732910606336],
   [0, 0, 0, 0, 0, 906694364710971881029632, 0, 151300194892565742356992],
   [0, 0, 0, 0, 604462909807314587353088, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 1133626210305746785013504],
   [0, 0, 0, 0, 0, 0, 0, 755726211211732910606848],
   [0, 0, 0, 0, 0, 0, 0, 1057994559603537623387648],
   [0, 0, 0, 0, 0, 0, 604462909807314587355136, 0],
   [0, 0, 0, 1133367955888714851287040, 0, 0, 0, 258254417031933726208],
   [0, 0, 0, 755578637259143234191360, 0, 0, 0, 147573952589676414976],
   [0, 906694364710971881029632, 0, 151115727451828646838272, 0, 0, 0, 184467440737095518720],
   [604462909807314587353088, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 44577024051892101511223706624],
   [0, 0, 0, 0, 0, 0, 0, 39623752663689085830303842304],
   [0, 0, 0, 0, 0, 0, 0, 39624054968930965782435726336],
   [0, 0, 0, 0, 0, 0, 39623752663689085830303842304, 0],
   [0, 0, 0, 0, 0, 0, 0, 44575815126072486882032223232],
   [0, 0, 0, 0, 0, 0, 0, 39623752663689085830303842304],
   [0, 0, 0, 0, 0, 39614383488587072454065651712, 0, 9671406556917033531867136],
   [0, 0, 0, 0, 39614081257132168796771975168, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 44575815126072486882049000448],
   [0, 0, 0, 0, 0, 0, 0, 39623752663689085830303842304],
   [0, 0, 0, 0, 0, 0, 0, 39624054895143989487597519872],
   [0, 0, 0, 0, 0, 0, 39614081257132168796906192896, 0],
   [0, 0, 0, 44566143645728593553662148608, 0, 0, 0, 9671480343893328370074624],
   [0, 0, 0, 39614081257132168796771975168, 0, 0, 0, 9671406556917033531867136],
   [0, 39614383488587072454065651712, 0, 0, 0, 0, 0, 9671406556917033531867136],
   [39614081257132168796771975168, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 3894460328615337105591694383906816],
   [0, 0, 0, 0, 0, 0, 0, 2596306885743558070394462922604544],
   [0, 0, 0, 0, 0, 0, 0, 3894381100377264977527087004909568],
   [0, 0, 0, 0, 0, 0, 2596148429267413814265248164610048, 0],
   [0, 0, 0, 0, 0, 0, 0, 3894381100452822841253001328328704],
   [0, 0, 0, 0, 0, 0, 0, 2596148429418529541717076811448320],
   [0, 0, 0, 0, 0, 3894222643901120721397872246915072, 0, 158456476144256129214757994496],
   [0, 0, 0, 0, 2596148429267413814265248164610048, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 3894381100452822841254100839956480],
   [0, 0, 0, 0, 0, 0, 0, 2596148429418529541719275834703872],
   [0, 0, 0, 0, 0, 0, 0, 3894381100377264977527087004909568],
   [0, 0, 0, 0, 0, 0, 2596148429267413814265248164610048, 0],
   [0, 0, 0, 3894222644127794312575615217172480, 0, 0, 0, 158456325028528677386111156224],
   [0, 0, 0, 2596148429418529541717076811448320, 0, 0, 0, 0],
   [0, 3894222643901120721397872246915072, 0, 151115727451828646838272, 0, 0, 0, 158456325028528677386111156224],
   [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 170147673836494160423436545529930055680],
   [0, 0, 0, 0, 0, 0, 0, 170141183460469231731687303715884105728],
   [0, 0, 0, 0, 0, 0, 0, 170142481534683865438594436339966410752],
   [0, 0, 0, 0, 0, 0, 170141183460469231731687303715884105728, 0],
   [0, 0, 0, 0, 0, 0, 0, 170142481539635625595735957439562907648],
   [0, 0, 0, 0, 0, 0, 0, 170141183460469231731687303715884105728],
   [0, 0, 0, 0, 0, 170142481534683865438594436339966410752, 0, 0],
   [0, 0, 0, 0, 170141183460469231731687303715884105728, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 170142481539635625595808015033600835584],
   [0, 0, 0, 0, 0, 0, 0, 170141183460469231731687303715884105728],
   [0, 0, 0, 0, 0, 0, 0, 170142481534683865438594436339966410752],
   [0, 0, 0, 0, 0, 0, 170141183460469231731687303715884105728, 0],
   [0, 0, 0, 170142481539635625595735957439562907648, 0, 0, 0, 0],
   [0, 0, 0, 170141183460469231731687303715884105728, 0, 0, 0, 0],
   [0, 170142481534683865438594436339966410752, 0, 0, 0, 0, 0, 0],
   [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0]]

def img (t c : ℕ) : ℕ := (imgT.getD t []).getD c 0

theorem img_ok_00 : ∀ a2 a3 b0 b1 b2 c0 c1 c2 c3 : Fin 2, ∀ g0 g1 g2 h0 h1 h2 : Bool,
    Trans (![(0 : Fin 2), (0 : Fin 2), a2, a3], ![g0, g1, g2]) ![b0, b1, b2] (![c0, c1, c2, c3], ![h0, h1, h2]) ↔ (img (enc (![(0 : Fin 2), (0 : Fin 2), a2, a3], ![g0, g1, g2])) (encB ![b0, b1, b2])).testBit (enc (![c0, c1, c2, c3], ![h0, h1, h2])) = true := by
  decide +kernel

theorem img_ok_01 : ∀ a2 a3 b0 b1 b2 c0 c1 c2 c3 : Fin 2, ∀ g0 g1 g2 h0 h1 h2 : Bool,
    Trans (![(0 : Fin 2), (1 : Fin 2), a2, a3], ![g0, g1, g2]) ![b0, b1, b2] (![c0, c1, c2, c3], ![h0, h1, h2]) ↔ (img (enc (![(0 : Fin 2), (1 : Fin 2), a2, a3], ![g0, g1, g2])) (encB ![b0, b1, b2])).testBit (enc (![c0, c1, c2, c3], ![h0, h1, h2])) = true := by
  decide +kernel

theorem img_ok_10 : ∀ a2 a3 b0 b1 b2 c0 c1 c2 c3 : Fin 2, ∀ g0 g1 g2 h0 h1 h2 : Bool,
    Trans (![(1 : Fin 2), (0 : Fin 2), a2, a3], ![g0, g1, g2]) ![b0, b1, b2] (![c0, c1, c2, c3], ![h0, h1, h2]) ↔ (img (enc (![(1 : Fin 2), (0 : Fin 2), a2, a3], ![g0, g1, g2])) (encB ![b0, b1, b2])).testBit (enc (![c0, c1, c2, c3], ![h0, h1, h2])) = true := by
  decide +kernel

theorem img_ok_11 : ∀ a2 a3 b0 b1 b2 c0 c1 c2 c3 : Fin 2, ∀ g0 g1 g2 h0 h1 h2 : Bool,
    Trans (![(1 : Fin 2), (1 : Fin 2), a2, a3], ![g0, g1, g2]) ![b0, b1, b2] (![c0, c1, c2, c3], ![h0, h1, h2]) ↔ (img (enc (![(1 : Fin 2), (1 : Fin 2), a2, a3], ![g0, g1, g2])) (encB ![b0, b1, b2])).testBit (enc (![c0, c1, c2, c3], ![h0, h1, h2])) = true := by
  decide +kernel

theorem img_ok' : ∀ a0 a1 a2 a3 b0 b1 b2 c0 c1 c2 c3 : Fin 2, ∀ g0 g1 g2 h0 h1 h2 : Bool,
    Trans (![a0, a1, a2, a3], ![g0, g1, g2]) ![b0, b1, b2] (![c0, c1, c2, c3], ![h0, h1, h2]) ↔ (img (enc (![a0, a1, a2, a3], ![g0, g1, g2])) (encB ![b0, b1, b2])).testBit (enc (![c0, c1, c2, c3], ![h0, h1, h2])) = true := by
  intro a0 a1 a2 a3 b0 b1 b2 c0 c1 c2 c3 g0 g1 g2 h0 h1 h2
  fin_cases a0 <;> fin_cases a1
  · exact img_ok_00 a2 a3 b0 b1 b2 c0 c1 c2 c3 g0 g1 g2 h0 h1 h2
  · exact img_ok_01 a2 a3 b0 b1 b2 c0 c1 c2 c3 g0 g1 g2 h0 h1 h2
  · exact img_ok_10 a2 a3 b0 b1 b2 c0 c1 c2 c3 g0 g1 g2 h0 h1 h2
  · exact img_ok_11 a2 a3 b0 b1 b2 c0 c1 c2 c3 g0 g1 g2 h0 h1 h2

theorem img_ok (q : St) (b : Ltr) (q' : St) :
    Trans q b q' ↔ (img (enc q) (encB b)).testBit (enc q') = true := by
  have h := img_ok' (q.1 0) (q.1 1) (q.1 2) (q.1 3) (b 0) (b 1) (b 2) (q'.1 0) (q'.1 1) (q'.1 2) (q'.1 3) (q.2 0) (q.2 1) (q.2 2) (q'.2 0) (q'.2 1) (q'.2 2)
  rwa [← st_eta q, ← st_eta q', ← ltr_eta b] at h

/-- The image mask of the set with mask M under the letter with code c. -/
def dm (M c : ℕ) : ℕ :=
  (List.range 128).foldr (fun t acc => if M.testBit t = true then img t c ||| acc else acc) 0

theorem testBit_fold (l : List ℕ) (M c u : ℕ) :
    (l.foldr (fun t acc => if M.testBit t = true then img t c ||| acc else acc) 0).testBit u = true ↔
      ∃ t ∈ l, M.testBit t = true ∧ (img t c).testBit u = true := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.foldr_cons]
    split_ifs with h
    · rw [Nat.testBit_lor, Bool.or_eq_true, ih]
      simp only [List.mem_cons]
      constructor
      · rintro (h1 | ⟨t', ht', h2⟩)
        · exact ⟨t, Or.inl rfl, h, h1⟩
        · exact ⟨t', Or.inr ht', h2⟩
      · rintro ⟨t', (rfl | ht'), h2, h3⟩
        · exact Or.inl h3
        · exact Or.inr ⟨t', ht', h2, h3⟩
    · rw [ih]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨t', ht', h2⟩; exact ⟨t', Or.inr ht', h2⟩
      · rintro ⟨t', (rfl | ht'), h2, h3⟩
        · exact absurd h2 h
        · exact ⟨t', ht', h2, h3⟩

/-- The reachable sets of states, as masks of state codes. -/
def masks : List ℕ :=
  [170147673836494160423436545529930055680, 170141183460469231731687303715884105728, 0, 3894222643901120721397872246915072, 44566294761456045382308986880, 170147673994960156941568587722176594944, 2596148429267413814265248164610048, 151115727451828646838272, 158456325028528677386111156224, 39614081257132168796771975168, 906694364710971881029632, 44566899224365852696896339968, 9671664811334065465593344, 170141183460469231740910675752738881536, 9259400833873739776, 39623752663689085832459714560, 3894222643901120721608978479448064, 211930866253824, 44566294761456045384724930560, 170150270143390482349942597805955149550, 755578637259143234191360, 147573952589676414976, 2596306885743558070535750166781984, 604462909807314587353088, 184467440737095518720, 39614685720041976111359328256, 39624357274172845736723515520, 1058068346579832461651690, 9223372036854775808, 39614081257132168798919458816, 2155872256, 2596148429267413814405985652965376, 549755813888, 151115727451828646846464, 158456325028528677394701090848, 140737488355328, 141287244169216, 211106232532992, 8192, 2207613198368, 906694364710971881078784, 128, 44566899224365852699312316416, 9671664811334065474506478, 170143779608899103617634889055126716416, 9259542123273814144, 39624357274172845736724039816, 3894222644807815086319950360526848, 211930866303168, 604610483759904263800960, 755578637259143234232320, 2596306885743705644488339843229864, 755763104699880329751208, 39614685720041976113506844672, 2155905152, 604462909807314587385856, 32896, 604610483759904263800968, 49344, 2147483648, 147573952589676415112, 2596306885743558070535758756751528, 2207613190176, 40960, 2184, 143494857402536, 184467440737095518762, 1058068346579832461651694, 9223512776490647552, 2596148429871876724213300240351232, 549755814016, 158456325212996118131796609578, 140737488388096, 141287244202112, 211106232582144, 2207613200938, 2596148429267413814405985652998144, 2147516416, 32768, 49152, 10794, 34952, 2596306885743705644488348433164456, 755763104699880329751210, 2596306886348205447783810439621290, 2207613192746, 143494857403050, 2602, 43690]

/-- The transition table of the reachable sets. -/
def sgT : List (List ℕ) :=
  [[1, 3, 2, 4, 2, 2, 2, 5], [1, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2], [6, 3, 2, 7, 2, 2, 2, 8], [9, 10, 2, 11, 2, 2, 2, 12], [13, 16, 2, 18, 14, 17, 15, 19], [6, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 20, 2, 2, 2, 21], [2, 2, 2, 2, 2, 2, 2, 22], [9, 2, 2, 2, 2, 2, 2, 2], [23, 10, 2, 7, 2, 2, 2, 24], [25, 10, 2, 11, 2, 2, 2, 12], [2, 2, 2, 2, 2, 2, 26, 27], [13, 2, 2, 2, 2, 2, 2, 2], [28, 2, 2, 2, 14, 2, 2, 2], [29, 2, 2, 2, 30, 2, 15, 2], [31, 16, 2, 33, 2, 32, 2, 34], [35, 37, 2, 38, 36, 17, 2, 39], [29, 40, 2, 42, 2, 41, 2, 43], [44, 47, 2, 42, 45, 48, 46, 19], [23, 2, 2, 20, 2, 2, 2, 21], [2, 2, 2, 2, 2, 2, 49, 2], [31, 2, 2, 50, 36, 2, 2, 51], [23, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 49, 52], [25, 2, 2, 2, 2, 2, 2, 2], [53, 2, 2, 2, 54, 2, 26, 2], [55, 40, 2, 50, 56, 58, 57, 27], [28, 2, 2, 2, 2, 2, 2, 2], [29, 2, 2, 2, 2, 2, 2, 2], [59, 2, 2, 2, 30, 2, 2, 2], [31, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 36, 2, 2, 2], [2, 2, 2, 50, 2, 2, 2, 60], [2, 2, 2, 2, 2, 2, 2, 61], [35, 2, 2, 2, 2, 2, 2, 2], [35, 2, 2, 2, 36, 2, 2, 2], [35, 37, 2, 38, 2, 32, 2, 62], [2, 2, 2, 63, 2, 2, 2, 64], [2, 2, 2, 63, 2, 2, 2, 65], [55, 40, 2, 33, 2, 41, 2, 66], [2, 2, 2, 2, 56, 2, 2, 2], [53, 40, 2, 42, 2, 41, 2, 43], [2, 2, 2, 2, 54, 58, 46, 67], [44, 2, 2, 2, 2, 2, 2, 2], [68, 2, 2, 2, 45, 2, 2, 2], [53, 2, 2, 2, 54, 2, 46, 2], [69, 47, 2, 33, 2, 70, 2, 71], [72, 74, 2, 38, 73, 48, 2, 75], [55, 2, 2, 2, 56, 2, 49, 2], [55, 2, 2, 50, 2, 2, 2, 60], [76, 2, 2, 50, 73, 2, 57, 51], [55, 2, 2, 50, 56, 2, 57, 52], [53, 2, 2, 2, 2, 2, 2, 2], [77, 2, 2, 2, 54, 2, 2, 2], [55, 2, 2, 2, 2, 2, 2, 2], [78, 2, 2, 2, 56, 2, 2, 2], [55, 2, 2, 2, 56, 2, 57, 2], [78, 79, 2, 38, 56, 58, 2, 80], [59, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 56, 2, 57, 2], [76, 2, 2, 50, 73, 2, 81, 82], [2, 2, 2, 2, 2, 2, 2, 65], [78, 2, 2, 63, 2, 2, 2, 64], [2, 2, 2, 2, 56, 2, 81, 2], [72, 2, 2, 63, 73, 2, 81, 65], [2, 2, 2, 2, 2, 2, 57, 83], [55, 40, 2, 50, 56, 58, 57, 67], [68, 2, 2, 2, 2, 2, 2, 2], [69, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 73, 2, 2, 2], [2, 2, 2, 2, 2, 2, 57, 84], [72, 2, 2, 2, 2, 2, 2, 2], [72, 2, 2, 2, 73, 2, 2, 2], [72, 74, 2, 38, 2, 70, 2, 85], [2, 2, 2, 63, 2, 2, 81, 86], [76, 2, 2, 2, 2, 2, 2, 2], [77, 2, 2, 2, 2, 2, 2, 2], [78, 2, 2, 2, 2, 2, 2, 2], [78, 79, 2, 38, 2, 41, 2, 87], [2, 2, 2, 63, 2, 2, 81, 88], [78, 2, 2, 2, 56, 2, 81, 2], [76, 2, 2, 50, 73, 2, 57, 82], [55, 2, 2, 50, 56, 2, 57, 83], [69, 2, 2, 50, 73, 2, 57, 84], [2, 2, 2, 2, 2, 2, 81, 86], [72, 2, 2, 63, 73, 2, 81, 86], [2, 2, 2, 2, 2, 2, 81, 88], [78, 2, 2, 63, 56, 2, 81, 88]]

def M (i : ℕ) : ℕ := masks.getD i 0

def sg (i c : ℕ) : ℕ := (sgT.getD i []).getD c 0

theorem check_sg : ∀ i, i < 89 → ∀ c, c < 8 → sg i c < 89 := by decide

theorem check_dm : ∀ i, i < 89 → ∀ c, c < 8 → dm (M i) c = M (sg i c) := by decide +kernel

/-- The set of states with mask number i. -/
def S (i : ℕ) (q : St) : Prop := (M i).testBit (enc q) = true

theorem delta_eq (i : ℕ) (hi : i < 89) (b : Ltr) :
    (fun q' => ∃ q, S i q ∧ Trans q b q') = S (sg i (encB b)) := by
  funext q'
  apply propext
  unfold S
  rw [← check_dm i hi (encB b) (encB_lt b), dm, testBit_fold]
  constructor
  · rintro ⟨q, hq, ht⟩
    exact ⟨enc q, List.mem_range.2 (enc_lt q), hq, (img_ok q b q').1 ht⟩
  · rintro ⟨t, ht, hM, hI⟩
    have e := enc_dec t (List.mem_range.1 ht)
    refine ⟨dec t, ?_, (img_ok _ _ _).2 ?_⟩
    · rwa [e]
    · rwa [e]

/-- W at the reachable set number i. -/
noncomputable def cnt (m i : ℕ) : ℕ := W m (S i)

theorem cnt_succ (m i : ℕ) (hi : i < 89) : cnt (m + 1) i = ∑ b : Ltr, cnt m (sg i (encB b)) := by
  unfold cnt
  rw [W_succ]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [delta_eq i hi b]

theorem sum_ltr (f : Ltr → ℕ) : ∑ b : Ltr, f b = ∑ b0 : Fin 2, ∑ b1 : Fin 2, ∑ b2 : Fin 2, f ![b0, b1, b2] := by
  rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b0 _ => ?_)
  rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b1 _ => ?_)
  rw [← (Fin.consEquiv fun _ => Fin 2).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b2 _ => ?_)
  rw [Fintype.sum_unique]
  congr 1 <;> funext j <;> fin_cases j <;> rfl

/-- The tables of cnt at the first levels. -/
def tb : List (List ℕ) :=
  [[1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [4, 1, 0, 4, 4, 7, 1, 2, 1, 1, 4, 4, 2, 1, 2, 3, 5, 6, 5, 7, 3, 1, 4, 1, 2, 1, 3, 7, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5, 1, 5, 4, 1, 2, 3, 5, 6, 3, 3, 5, 5, 1, 2, 1, 2, 3, 6, 1, 2, 5, 1, 3, 2, 5, 2, 7, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 5, 3, 3, 5, 5, 5, 2, 5, 2, 5],
   [16, 1, 0, 8, 11, 29, 1, 4, 4, 1, 9, 11, 10, 1, 3, 6, 10, 18, 16, 29, 5, 3, 11, 1, 8, 1, 6, 27, 1, 1, 3, 1, 2, 5, 5, 1, 3, 10, 5, 8, 11, 2, 16, 18, 1, 3, 6, 11, 19, 6, 6, 14, 14, 1, 3, 1, 3, 6, 19, 1, 5, 14, 5, 6, 5, 14, 8, 27, 1, 1, 2, 8, 1, 3, 11, 11, 1, 1, 1, 11, 11, 6, 14, 14, 14, 8, 14, 8, 14],
   [49, 1, 0, 17, 31, 83, 1, 8, 11, 1, 22, 31, 33, 1, 4, 10, 23, 45, 48, 85, 9, 6, 24, 1, 20, 1, 10, 73, 1, 1, 4, 1, 3, 11, 14, 1, 4, 23, 11, 20, 27, 3, 48, 55, 1, 4, 10, 27, 50, 10, 12, 30, 30, 1, 4, 1, 4, 10, 50, 1, 9, 30, 14, 12, 9, 30, 20, 73, 1, 1, 3, 20, 1, 4, 27, 26, 1, 1, 1, 27, 26, 10, 30, 30, 30, 20, 30, 20, 30],
   [132, 1, 0, 37, 87, 216, 1, 15, 24, 1, 51, 87, 83, 1, 5, 15, 52, 104, 134, 225, 16, 10, 47, 1, 40, 1, 15, 177, 1, 1, 5, 1, 4, 21, 30, 1, 5, 52, 21, 42, 62, 4, 134, 137, 1, 5, 15, 62, 119, 15, 22, 57, 57, 1, 5, 1, 5, 15, 119, 1, 14, 57, 30, 22, 14, 57, 40, 177, 1, 1, 4, 40, 1, 5, 62, 52, 1, 1, 1, 62, 52, 15, 57, 57, 57, 40, 57, 40, 57],
   [341, 1, 0, 77, 222, 536, 1, 26, 47, 1, 107, 222, 192, 1, 6, 21, 108, 225, 338, 561, 27, 15, 85, 1, 72, 1, 21, 401, 1, 1, 6, 1, 5, 36, 57, 1, 6, 108, 36, 79, 128, 5, 338, 316, 1, 6, 21, 128, 260, 21, 37, 100, 100, 1, 6, 1, 6, 21, 260, 1, 20, 100, 57, 37, 20, 100, 72, 401, 1, 1, 5, 72, 1, 6, 128, 94, 1, 1, 1, 128, 94, 21, 100, 100, 100, 72, 100, 72, 100],
   [836, 1, 0, 151, 522, 1260, 1, 42, 85, 1, 206, 522, 422, 1, 7, 28, 207, 455, 788, 1315, 43, 21, 144, 1, 121, 1, 28, 854, 1, 1, 7, 1, 6, 57, 100, 1, 7, 207, 57, 137, 242, 6, 788, 688, 1, 7, 28, 242, 525, 28, 58, 165, 165, 1, 7, 1, 7, 28, 525, 1, 27, 165, 100, 58, 27, 165, 121, 854, 1, 1, 6, 121, 1, 7, 242, 158, 1, 1, 1, 242, 158, 28, 165, 165, 165, 121, 165, 121, 165],
   [1934, 1, 0, 279, 1151, 2801, 1, 64, 144, 1, 370, 1151, 882, 1, 8, 36, 371, 864, 1725, 2906, 65, 28, 231, 1, 193, 1, 36, 1715, 1, 1, 8, 1, 7, 85, 165, 1, 8, 371, 85, 223, 427, 7, 1725, 1414, 1, 8, 36, 427, 990, 36, 86, 259, 259, 1, 8, 1, 8, 36, 990, 1, 35, 259, 165, 86, 35, 259, 193, 1715, 1, 1, 7, 193, 1, 8, 427, 251, 1, 1, 1, 427, 251, 36, 259, 259, 259, 193, 259, 193, 259],
   [4232, 1, 0, 488, 2404, 5911, 1, 93, 231, 1, 628, 2404, 1751, 1, 9, 45, 629, 1552, 3574, 6093, 94, 36, 354, 1, 295, 1, 45, 3263, 1, 1, 9, 1, 8, 121, 259, 1, 9, 629, 121, 345, 713, 8, 3574, 2749, 1, 9, 45, 713, 1762, 45, 122, 390, 390, 1, 9, 1, 9, 45, 1762, 1, 44, 390, 259, 122, 44, 390, 295, 3263, 1, 1, 8, 295, 1, 9, 713, 381, 1, 1, 1, 713, 381, 45, 390, 390, 390, 295, 390, 295, 390],
   [8804, 1, 0, 813, 4784, 11903, 1, 130, 354, 1, 1017, 4784, 3308, 1, 10, 55, 1018, 2657, 7045, 12197, 131, 45, 522, 1, 435, 1, 55, 5915, 1, 1, 10, 1, 9, 166, 390, 1, 10, 1018, 166, 512, 1138, 9, 7045, 5079, 1, 10, 55, 1138, 2987, 55, 167, 567, 567, 1, 10, 1, 10, 55, 2987, 1, 54, 567, 390, 167, 54, 567, 435, 5915, 1, 1, 9, 435, 1, 10, 1138, 557, 1, 1, 1, 1138, 557, 55, 567, 567, 567, 435, 567, 435, 567],
   [17501, 1, 0, 1298, 9110, 22983, 1, 176, 522, 1, 1583, 9110, 5970, 1, 11, 66, 1584, 4364, 13272, 23433, 177, 55, 745, 1, 622, 1, 66, 10273, 1, 1, 11, 1, 10, 221, 567, 1, 11, 1584, 221, 734, 1749, 10, 13272, 8967, 1, 11, 66, 1749, 4859, 66, 222, 800, 800, 1, 11, 1, 11, 66, 4859, 1, 65, 800, 567, 222, 65, 800, 622, 10273, 1, 1, 10, 622, 1, 11, 1749, 789, 1, 1, 1, 1749, 789, 66, 800, 800, 800, 622, 800, 622, 800],
   [33392, 1, 0, 1997, 16664, 42731, 1, 232, 745, 1, 2382, 16664, 10339, 1, 12, 78, 2383, 6915, 23999, 43391, 233, 66, 1034, 1, 866, 1, 78, 17181, 1, 1, 12, 1, 11, 287, 800, 1, 12, 2383, 287, 1022, 2603, 11, 23999, 15209, 1, 12, 78, 2603, 7630, 78, 288, 1100, 1100, 1, 12, 1, 12, 78, 7630, 1, 77, 1100, 800, 288, 77, 1100, 866, 17181, 1, 1, 11, 866, 1, 12, 2603, 1088, 1, 1, 1, 2603, 1088, 78, 1100, 1100, 1100, 866, 1100, 866, 1100],
   [61393, 1, 0, 2975, 29386, 76779, 1, 299, 1034, 1, 3481, 29386, 17259, 1, 13, 91, 3482, 10620, 41823, 77714, 300, 78, 1401, 1, 1178, 1, 91, 27793, 1, 1, 13, 1, 12, 365, 1100, 1, 13, 3482, 365, 1388, 3768, 12, 41823, 24901, 1, 13, 91, 3768, 11621, 91, 366, 1479, 1479, 1, 13, 1, 13, 91, 11621, 1, 90, 1479, 1100, 366, 90, 1479, 1178, 27793, 1, 1, 12, 1178, 1, 13, 3768, 1466, 1, 1, 1, 3768, 1466, 91, 1479, 1479, 1479, 1178, 1479, 1178, 1479],
   [109141, 1, 0, 4309, 50127, 133744, 1, 378, 1401, 1, 4959, 50127, 27884, 1, 14, 105, 4960, 15869, 70505, 135031, 379, 91, 1859, 1, 1570, 1, 105, 43653, 1, 1, 14, 1, 13, 456, 1479, 1, 14, 4960, 456, 1845, 5324, 13, 70505, 39518, 1, 14, 105, 5324, 17234, 105, 457, 1950, 1950, 1, 14, 1, 14, 105, 17234, 1, 104, 1950, 1479, 457, 104, 1950, 1570, 43653, 1, 1, 13, 1570, 1, 14, 5324, 1936, 1, 1, 1, 5324, 1936, 105, 1950, 1950, 1950, 1570, 1950, 1570, 1950],
   [188181, 1, 0, 6089, 82971, 226485, 1, 470, 1859, 1, 6908, 82971, 43758, 1, 15, 120, 6909, 23145, 115361, 228214, 471, 105, 2422, 1, 2055, 1, 120, 66788, 1, 1, 15, 1, 14, 561, 1950, 1, 15, 6909, 561, 2407, 7364, 14, 115361, 61006, 1, 15, 120, 7364, 24965, 120, 562, 2527, 2527, 1, 15, 1, 15, 120, 24965, 1, 119, 2527, 1950, 562, 119, 2527, 2055, 66788, 1, 1, 14, 2055, 1, 15, 7364, 2512, 1, 1, 1, 7364, 2512, 120, 2527, 2527, 2527, 2055, 2527, 2055, 2527]]

def look (m i : ℕ) : ℕ := (tb.getD m []).getD i 0

def CT (m : ℕ) : Prop := ∀ i, i < 89 → cnt m i = look m i

theorem ex_iff (i : ℕ) : (∃ q, S i q) ↔ ∃ t, t < 128 ∧ (M i).testBit t = true := by
  constructor
  · rintro ⟨q, hq⟩; exact ⟨enc q, enc_lt q, hq⟩
  · rintro ⟨t, ht, h⟩
    refine ⟨dec t, ?_⟩
    unfold S
    rwa [enc_dec t ht]

theorem ct0_check : ∀ i, i < 89 → ((∃ t, t < 128 ∧ (M i).testBit t = true) ↔ look 0 i = 1) := by decide +kernel

theorem look0 : ∀ i, i < 89 → look 0 i ≤ 1 := by decide

theorem CT0 : CT 0 := by
  intro i hi
  unfold cnt
  rw [W_zero]
  split_ifs with h
  · exact ((ct0_check i hi).1 ((ex_iff i).1 h)).symm
  · have h1 : look 0 i ≠ 1 := fun h1 => h ((ex_iff i).2 ((ct0_check i hi).2 h1))
    have := look0 i hi
    omega

theorem tstep (m : ℕ) (hm : ∀ i, i < 89 → look (m + 1) i = ∑ b0 : Fin 2, ∑ b1 : Fin 2, ∑ b2 : Fin 2, look m (sg i (encB ![b0, b1, b2])))
    (h : CT m) : CT (m + 1) := by
  intro i hi
  rw [cnt_succ m i hi, hm i hi, ← sum_ltr (fun b => look m (sg i (encB b)))]
  exact Finset.sum_congr rfl fun b _ => h _ (check_sg i hi _ (encB_lt b))

theorem CT1 : CT 1 := tstep 0 (by decide +kernel) CT0

theorem CT2 : CT 2 := tstep 1 (by decide +kernel) CT1

theorem CT3 : CT 3 := tstep 2 (by decide +kernel) CT2

theorem CT4 : CT 4 := tstep 3 (by decide +kernel) CT3

theorem CT5 : CT 5 := tstep 4 (by decide +kernel) CT4

theorem CT6 : CT 6 := tstep 5 (by decide +kernel) CT5

theorem CT7 : CT 7 := tstep 6 (by decide +kernel) CT6

theorem CT8 : CT 8 := tstep 7 (by decide +kernel) CT7

theorem CT9 : CT 9 := tstep 8 (by decide +kernel) CT8

theorem CT10 : CT 10 := tstep 9 (by decide +kernel) CT9

theorem CT11 : CT 11 := tstep 10 (by decide +kernel) CT10

theorem CT12 : CT 12 := tstep 11 (by decide +kernel) CT11

theorem CT13 : CT 13 := tstep 12 (by decide +kernel) CT12

theorem CT14 : CT 14 := tstep 13 (by decide +kernel) CT13

theorem rec_base : ∀ i, i < 89 → look 14 i + 45 * look 12 i + 210 * look 10 i + 210 * look 8 i + 45 * look 6 i + look 4 i = 10 * look 13 i + 120 * look 11 i + 252 * look 9 i + 120 * look 7 i + 10 * look 5 i := by decide +kernel

theorem crec (m : ℕ) : ∀ i, i < 89 → cnt (m + 14) i + 45 * cnt (m + 12) i + 210 * cnt (m + 10) i + 210 * cnt (m + 8) i + 45 * cnt (m + 6) i + cnt (m + 4) i = 10 * cnt (m + 13) i + 120 * cnt (m + 11) i + 252 * cnt (m + 9) i + 120 * cnt (m + 7) i + 10 * cnt (m + 5) i := by
  induction m with
  | zero =>
    intro i hi
    simp only [Nat.zero_add]
    rw [CT4 i hi, CT5 i hi, CT6 i hi, CT7 i hi, CT8 i hi, CT9 i hi, CT10 i hi, CT11 i hi, CT12 i hi, CT13 i hi, CT14 i hi]
    exact rec_base i hi
  | succ m ih =>
    intro i hi
    rw [show m + 1 + 4 = m + 4 + 1 from by omega, show m + 1 + 5 = m + 5 + 1 from by omega, show m + 1 + 6 = m + 6 + 1 from by omega, show m + 1 + 7 = m + 7 + 1 from by omega, show m + 1 + 8 = m + 8 + 1 from by omega, show m + 1 + 9 = m + 9 + 1 from by omega, show m + 1 + 10 = m + 10 + 1 from by omega, show m + 1 + 11 = m + 11 + 1 from by omega, show m + 1 + 12 = m + 12 + 1 from by omega, show m + 1 + 13 = m + 13 + 1 from by omega, show m + 1 + 14 = m + 14 + 1 from by omega]
    simp only [cnt_succ _ i hi, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => ih _ (check_sg i hi _ (encB_lt b))

/-- The start set: first rows whose adjacent entries are nondecreasing, flags set where equal. -/
def S0 (q : St) : Prop :=
  (∀ j : Fin 3, q.1 j.castSucc ≤ q.1 j.succ) ∧ q.2 = fun j => decide (q.1 j.castSucc = q.1 j.succ)

instance (q : St) : Decidable (S0 q) := by unfold S0; infer_instance

theorem S0_eq : S0 = S 0 := by
  funext q
  apply propext
  revert q
  refine forall_st ?_
  unfold S
  decide +kernel

theorem a_W (n : ℕ) : a n = W n S0 := by
  classical
  unfold a W
  congr 1
  ext B
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, hs, rfl⟩
    refine ⟨(A 0, fun j => decide (A 0 j.castSucc = A 0 j.succ)), ⟨fun j => ?_, rfl⟩, A, rfl, hs.1, ?_, rfl⟩
    · exact ((lex_cons _ _).1 (hs.2 j)).1
    · intro j hj
      simp only [decide_eq_true_eq] at hj
      exact ((lex_cons _ _).1 (hs.2 j)).2 hj
  · rintro ⟨q, ⟨hq1, hq2⟩, A, h0, hr, hc, hi⟩
    refine ⟨A, ⟨hr, fun j => ?_⟩, hi⟩
    rw [lex_cons]
    refine ⟨?_, fun he => ?_⟩
    · show A 0 j.castSucc ≤ A 0 j.succ
      rw [h0]; exact hq1 j
    · apply hc j
      rw [hq2]
      simp only [decide_eq_true_eq]
      have he' : A 0 j.castSucc = A 0 j.succ := he
      rwa [h0] at he'

theorem a_cnt (n : ℕ) : a n = cnt n 0 := by
  rw [a_W, S0_eq]; rfl

theorem val1 : a 1 = 4 := by rw [a_cnt, CT1 0 (by norm_num)]; rfl

theorem val2 : a 2 = 16 := by rw [a_cnt, CT2 0 (by norm_num)]; rfl

theorem val3 : a 3 = 49 := by rw [a_cnt, CT3 0 (by norm_num)]; rfl

theorem val4 : a 4 = 132 := by rw [a_cnt, CT4 0 (by norm_num)]; rfl

theorem val5 : a 5 = 341 := by rw [a_cnt, CT5 0 (by norm_num)]; rfl

theorem val6 : a 6 = 836 := by rw [a_cnt, CT6 0 (by norm_num)]; rfl

theorem val7 : a 7 = 1934 := by rw [a_cnt, CT7 0 (by norm_num)]; rfl

theorem val8 : a 8 = 4232 := by rw [a_cnt, CT8 0 (by norm_num)]; rfl

theorem val9 : a 9 = 8804 := by rw [a_cnt, CT9 0 (by norm_num)]; rfl

theorem val10 : a 10 = 17501 := by rw [a_cnt, CT10 0 (by norm_num)]; rfl

theorem val11 : a 11 = 33392 := by rw [a_cnt, CT11 0 (by norm_num)]; rfl

theorem val12 : a 12 = 61393 := by rw [a_cnt, CT12 0 (by norm_num)]; rfl

theorem val13 : a 13 = 109141 := by rw [a_cnt, CT13 0 (by norm_num)]; rfl

theorem val14 : a 14 = 188181 := by rw [a_cnt, CT14 0 (by norm_num)]; rfl

theorem recurrence (n : ℕ) (hn : 13 < n) : (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  rcases Nat.lt_or_ge n 14 with h | h
  · omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 14 := ⟨n - 14, by omega⟩
    have hc := crec m 0 (by norm_num)
    simp only [show m + 14 - 1 = m + 13 from by omega, show m + 14 - 2 = m + 12 from by omega, show m + 14 - 3 = m + 11 from by omega, show m + 14 - 4 = m + 10 from by omega, show m + 14 - 5 = m + 9 from by omega, show m + 14 - 6 = m + 8 from by omega, show m + 14 - 7 = m + 7 from by omega, show m + 14 - 8 = m + 6 from by omega, show m + 14 - 9 = m + 5 from by omega, show m + 14 - 10 = m + 4 from by omega, a_cnt]
    have hz := congrArg (Nat.cast : ℕ → ℤ) hc
    push_cast at hz
    linarith

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
    X * (4 - 24 * X + 69 * X ^ 2 - 118 * X ^ 3 + 146 * X ^ 4 - 162 * X ^ 5 + 177 * X ^ 6 - 156 * X ^ 7 + 90 * X ^ 8 - 31 * X ^ 9 + 9 * X ^ 10 - 4 * X ^ 11 + X ^ 12) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 10 = A - C 10 * (A * X ^ 1) + C 45 * (A * X ^ 2) - C 120 * (A * X ^ 3) + C 210 * (A * X ^ 4) - C 252 * (A * X ^ 5) + C 210 * (A * X ^ 6) - C 120 * (A * X ^ 7) + C 45 * (A * X ^ 8) - C 10 * (A * X ^ 9) + (A * X ^ 10) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (4 - 24 * X + 69 * X ^ 2 - 118 * X ^ 3 + 146 * X ^ 4 - 162 * X ^ 5 + 177 * X ^ 6 - 156 * X ^ 7 + 90 * X ^ 8 - 31 * X ^ 9 + 9 * X ^ 10 - 4 * X ^ 11 + X ^ 12) : ℤ⟦X⟧) = X ^ 1 * C 4 - X ^ 2 * C 24 + X ^ 3 * C 69 - X ^ 4 * C 118 + X ^ 5 * C 146 - X ^ 6 * C 162 + X ^ 7 * C 177 - X ^ 8 * C 156 + X ^ 9 * C 90 - X ^ 10 * C 31 + X ^ 11 * C 9 - X ^ 12 * C 4 + X ^ 13 * C 1 := by
    simp only [map_ofNat, map_one]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 14 with hn | hn
  · interval_cases n <;> simp [val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 14 := ⟨n - 14, by omega⟩
    have hr := recurrence (q + 14) (by omega)
    simp only [show q + 14 - 1 = q + 13 by omega, show q + 14 - 2 = q + 12 by omega, show q + 14 - 3 = q + 11 by omega, show q + 14 - 4 = q + 10 by omega, show q + 14 - 5 = q + 9 by omega, show q + 14 - 6 = q + 8 by omega, show q + 14 - 7 = q + 7 by omega, show q + 14 - 8 = q + 6 by omega, show q + 14 - 9 = q + 5 by omega, show q + 14 - 10 = q + 4 by omega] at hr ⊢
    simp only [show ¬ q + 14 = 0 by omega, show ¬ q + 13 = 0 by omega, show ¬ q + 12 = 0 by omega, show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega, show 1 ≤ q + 14 by omega, show 2 ≤ q + 14 by omega, show 3 ≤ q + 14 by omega, show 4 ≤ q + 14 by omega, show 5 ≤ q + 14 by omega, show 6 ≤ q + 14 by omega, show 7 ≤ q + 14 by omega, show 8 ≤ q + 14 by omega, show 9 ≤ q + 14 by omega, show 10 ≤ q + 14 by omega, show ¬ q + 14 = 0 by omega, show ¬ q + 14 = 1 by omega, show ¬ q + 14 = 2 by omega, show ¬ q + 14 = 3 by omega, show ¬ q + 14 = 4 by omega, show ¬ q + 14 = 5 by omega, show ¬ q + 14 = 6 by omega, show ¬ q + 14 = 7 by omega, show ¬ q + 14 = 8 by omega, show ¬ q + 14 = 9 by omega, show ¬ q + 14 = 10 by omega, show ¬ q + 14 = 11 by omega, show ¬ q + 14 = 12 by omega, show ¬ q + 14 = 13 by omega, if_true, if_false]
    rw [hr]
    ring

theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
    X * (4 - 24 * X + 69 * X ^ 2 - 118 * X ^ 3 + 146 * X ^ 4 - 162 * X ^ 5 + 177 * X ^ 6 - 156 * X ^ 7 + 90 * X ^ 8 - 31 * X ^ 9 + 9 * X ^ 10 - 4 * X ^ 11 + X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a227266

theorem OMA.solution : type_of% @OMA.S_oeis_a227266.main :=
  OMA.S_oeis_a227266.conjecture
