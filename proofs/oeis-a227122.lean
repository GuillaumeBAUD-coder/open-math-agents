import OMAStatements.S_oeis_a227122

/-!
Proof for A227122. Count indicator arrays by a subset construction read from the top row down. A
state is a row of the larger array with one flag per pair of adjacent columns, true while those two
columns are still equal; Acc m q B says that some sorted larger array continues from the state q and
indicates B. For a set S of states, W m S counts the arrays B that some state of S accepts, and
W (m + 1) S is a sum of W m over the image sets. The reachable sets are listed as bit masks of state
codes with their transition table; the kernel checks the one-step images, the tables of W at the
first levels, and the recurrence at its first level, and the recurrence then holds at every level for
every reachable set. The g.f. step follows the pattern of the merged proof of oeis-a202456 by @jleguina.
-/

namespace OMA.S_oeis_a227122

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
  [[60640, 4112, 512, 256, 12, 0, 2, 1],
   [43168, 0, 512, 0, 8, 0, 2, 0],
   [61152, 0, 0, 0, 14, 0, 0, 0],
   [34944, 0, 0, 0, 8, 0, 0, 0],
   [61166, 4112, 0, 0, 0, 0, 0, 0],
   [43176, 0, 0, 0, 0, 0, 0, 0],
   [60138, 0, 0, 0, 0, 0, 0, 0],
   [32896, 0, 0, 0, 0, 0, 0, 0],
   [60652, 4112, 514, 256, 0, 0, 0, 0],
   [43176, 0, 512, 0, 0, 0, 0, 0],
   [61162, 0, 0, 0, 0, 0, 0, 0],
   [34944, 0, 0, 0, 0, 0, 0, 0],
   [61166, 4096, 0, 0, 0, 0, 0, 0],
   [43144, 0, 0, 0, 0, 0, 0, 0],
   [60074, 0, 0, 0, 0, 0, 0, 0],
   [32768, 0, 0, 0, 0, 0, 0, 0],
   [2290107456, 269484032, 0, 16777216, 524292, 0, 0, 65536],
   [2290089984, 0, 0, 0, 524288, 0, 0, 0],
   [2290107456, 0, 0, 0, 524292, 0, 0, 0],
   [2290089984, 0, 0, 0, 524288, 0, 0, 0],
   [2290631748, 269484032, 0, 0, 0, 0, 0, 0],
   [2290614272, 0, 0, 0, 0, 0, 0, 0],
   [2290630720, 0, 0, 0, 0, 0, 0, 0],
   [2155872256, 0, 0, 0, 0, 0, 0, 0],
   [2290631748, 269484032, 0, 16777216, 0, 0, 0, 0],
   [2290614272, 0, 0, 0, 0, 0, 0, 0],
   [2290631744, 0, 0, 0, 0, 0, 0, 0],
   [2290089984, 0, 0, 0, 0, 0, 0, 0],
   [2290631748, 268435456, 0, 0, 0, 0, 0, 0],
   [2290614272, 0, 0, 0, 0, 0, 0, 0],
   [2290630656, 0, 0, 0, 0, 0, 0, 0],
   [2147483648, 0, 0, 0, 0, 0, 0, 0],
   [211930866262048, 4112, 2199023255552, 1099511627776, 0, 0, 8589934592, 4294967296],
   [141287244177440, 0, 2199023255552, 0, 0, 0, 8589934592, 0],
   [214129889517600, 0, 0, 0, 8589934592, 0, 0, 0],
   [141287244169216, 0, 0, 0, 0, 0, 0, 0],
   [214138479452192, 4112, 0, 0, 0, 0, 0, 0],
   [141287244177440, 0, 0, 0, 0, 0, 0, 0],
   [214138479452192, 0, 0, 0, 0, 0, 0, 0],
   [141287244169216, 0, 0, 0, 0, 0, 0, 0],
   [211930866262048, 4112, 2207613190144, 1099511627776, 0, 0, 0, 0],
   [141287244177440, 0, 2199023255552, 0, 0, 0, 0, 0],
   [214138479452192, 0, 0, 0, 0, 0, 0, 0],
   [141287244169216, 0, 0, 0, 0, 0, 0, 0],
   [214138479452192, 4096, 0, 0, 0, 0, 0, 0],
   [141287244177408, 0, 0, 0, 0, 0, 0, 0],
   [213863601545248, 0, 0, 0, 0, 0, 0, 0],
   [140737488355328, 0, 0, 0, 0, 0, 0, 0],
   [9259471477495824384, 269484032, 0, 72057594037927936, 0, 0, 0, 281474976710656],
   [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
   [9259471477495824384, 0, 0, 0, 0, 0, 0, 0],
   [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
   [9259471477495824384, 269484032, 0, 0, 0, 0, 0, 0],
   [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
   [9259471477495824384, 0, 0, 0, 0, 0, 0, 0],
   [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
   [9259471477495824384, 269484032, 0, 72057594037927936, 0, 0, 0, 0],
   [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
   [9259471477495824384, 0, 0, 0, 0, 0, 0, 0],
   [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
   [9259471477495824384, 268435456, 0, 0, 0, 0, 0, 0],
   [9259400833873739776, 0, 0, 0, 0, 0, 0, 0],
   [9259471202617917440, 0, 0, 0, 0, 0, 0, 0],
   [9223372036854775808, 0, 0, 0, 0, 0, 0, 0],
   [1057810092162800527870976, 75557863725914323419136, 512, 256, 221360928884514619392, 0, 36893488147419103232, 18446744073709551616],
   [755578637259143234193408, 0, 512, 0, 147573952589676412928, 0, 36893488147419103232, 0],
   [1057810092162800527871488, 0, 0, 0, 258254417031933722624, 0, 0, 0],
   [604462909807314587355136, 0, 0, 0, 147573952589676412928, 0, 0, 0],
   [1058068346579832461594112, 75557863725914323419136, 0, 0, 0, 0, 0, 0],
   [755726211211732910606336, 0, 0, 0, 0, 0, 0, 0],
   [1057994559603537623386624, 0, 0, 0, 0, 0, 0, 0],
   [604462909807314587353088, 0, 0, 0, 0, 0, 0, 0],
   [1058031453091685042490368, 75557863725914323419136, 36893488147419103744, 256, 0, 0, 0, 0],
   [755726211211732910606336, 0, 512, 0, 0, 0, 0, 0],
   [1057994559603537623387648, 0, 0, 0, 0, 0, 0, 0],
   [604462909807314587355136, 0, 0, 0, 0, 0, 0, 0],
   [1058068346579832461594112, 75557863725914323419136, 0, 0, 0, 0, 0, 0],
   [755726211211732910606336, 0, 0, 0, 0, 0, 0, 0],
   [1057994559603537623386624, 0, 0, 0, 0, 0, 0, 0],
   [604462909807314587353088, 0, 0, 0, 0, 0, 0, 0],
   [39614383488587072454199870464, 4951760157141521099596496896, 0, 16777216, 9671480343893328235855872, 0, 0, 1208925819614629174706176],
   [39614081257132168796906192896, 0, 0, 0, 9671406556917033397649408, 0, 0, 0],
   [39614383488587072454199870464, 0, 0, 0, 9671480343893328235855872, 0, 0, 0],
   [39614081257132168796906192896, 0, 0, 0, 9671406556917033397649408, 0, 0, 0],
   [39624054968930965782435726336, 4951760157141521099596496896, 0, 0, 0, 0, 0, 0],
   [39623752663689085830303842304, 0, 0, 0, 0, 0, 0, 0],
   [39624054895143989487597518848, 0, 0, 0, 0, 0, 0, 0],
   [39614081257132168796771975168, 0, 0, 0, 0, 0, 0, 0],
   [39624054968930965782435726336, 4951760157141521099596496896, 0, 16777216, 0, 0, 0, 0],
   [39623752663689085830303842304, 0, 0, 0, 0, 0, 0, 0],
   [39624054895143989487597519872, 0, 0, 0, 0, 0, 0, 0],
   [39614081257132168796906192896, 0, 0, 0, 0, 0, 0, 0],
   [39624054968930965782435726336, 4951760157141521099596496896, 0, 0, 0, 0, 0, 0],
   [39623752663689085830303842304, 0, 0, 0, 0, 0, 0, 0],
   [39624054895143989487597518848, 0, 0, 0, 0, 0, 0, 0],
   [39614081257132168796771975168, 0, 0, 0, 0, 0, 0, 0],
   [3894222644052236448849700893753344, 75557863725914323419136, 2199023255552, 1099511627776, 0, 0, 158456325028528675187087900672, 79228162514264337593543950336],
   [2596148429418529541717076811448320, 0, 2199023255552, 0, 0, 0, 158456325028528675187087900672, 0],
   [3894222644052236448851899917008896, 0, 0, 0, 158456325028528675187087900672, 0, 0, 0],
   [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
   [3894381100377264977527087004909568, 75557863725914323419136, 0, 0, 0, 0, 0, 0],
   [2596148429418529541717076811448320, 0, 0, 0, 0, 0, 0, 0],
   [3894381100377264977527087004909568, 0, 0, 0, 0, 0, 0, 0],
   [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
   [3894222644052236448849700893753344, 75557863725914323419136, 158456325028528677386111156224, 1099511627776, 0, 0, 0, 0],
   [2596148429418529541717076811448320, 0, 2199023255552, 0, 0, 0, 0, 0],
   [3894381100377264977527087004909568, 0, 0, 0, 0, 0, 0, 0],
   [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
   [3894381100377264977527087004909568, 75557863725914323419136, 0, 0, 0, 0, 0, 0],
   [2596148429418529541717076811448320, 0, 0, 0, 0, 0, 0, 0],
   [3894381100377264977527087004909568, 0, 0, 0, 0, 0, 0, 0],
   [2596148429267413814265248164610048, 0, 0, 0, 0, 0, 0, 0],
   [170142481534683865438594436339966410752, 4951760157141521099596496896, 0, 72057594037927936, 0, 0, 0, 5192296858534827628530496329220096],
   [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
   [170142481534683865438594436339966410752, 0, 0, 0, 0, 0, 0, 0],
   [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
   [170142481534683865438594436339966410752, 4951760157141521099596496896, 0, 0, 0, 0, 0, 0],
   [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
   [170142481534683865438594436339966410752, 0, 0, 0, 0, 0, 0, 0],
   [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
   [170142481534683865438594436339966410752, 4951760157141521099596496896, 0, 72057594037927936, 0, 0, 0, 0],
   [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
   [170142481534683865438594436339966410752, 0, 0, 0, 0, 0, 0, 0],
   [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
   [170142481534683865438594436339966410752, 4951760157141521099596496896, 0, 0, 0, 0, 0, 0],
   [170141183460469231731687303715884105728, 0, 0, 0, 0, 0, 0, 0],
   [170142481534683865438594436339966410752, 0, 0, 0, 0, 0, 0, 0],
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
  [170147673836494160423436545529930055680, 170145077881193663974855268062820566016, 0, 4951760157141521099865980928, 72057594037927936, 5192296858534827628530496329220096, 170145077881184597141888764084257615594, 9671664811334065331372032, 2199023255552, 158456325028528675187087900672, 39624054968930965784592139332, 9259471477495824384, 269484032, 170142481534683865438594436339966410752, 4951760157141521099596496896, 147573952589676412936, 2199023256064, 158456325065422163343096938498, 39615139067224331597434064384, 512, 36893488147419103232, 141287244177440, 2596148429418529541717076811448320, 39615139251691772336685510378, 9671664811334065331896334, 9259614972353191968, 2290631748, 170145077841569608996664830802889015296, 39624054968930965782435726336, 604462909807314587388032, 141287244212392, 2596148430022992451665678643013792, 43176, 755578637259143234193408, 147573952589676412928, 2596148430023140025476981075216384, 36893488147419103234, 39615139067224331599589994208, 9259614972353226920, 8589934592, 2290151146, 524302, 170145077841570213607148731994396960800, 8, 2596148430023140025618268319426728, 755726211211732910639232, 604462909807314587355136, 2596148430023140025476981075249280, 755578637259143234234528, 2, 2290151136, 170145077841570213607148731994396993704, 34944, 755726211211732910647464, 43168]

/-- The transition table of the reachable sets. -/
def sgT : List (List ℕ) :=
  [[1, 3, 2, 4, 2, 2, 2, 5], [6, 2, 8, 2, 7, 2, 9, 2], [2, 2, 2, 2, 2, 2, 2, 2], [10, 3, 2, 2, 2, 2, 2, 2], [11, 12, 2, 4, 2, 2, 2, 2], [13, 14, 2, 4, 2, 2, 2, 5], [6, 2, 16, 2, 15, 2, 17, 2], [18, 2, 19, 2, 7, 2, 20, 2], [21, 2, 8, 2, 2, 2, 2, 2], [22, 2, 8, 2, 2, 2, 9, 2], [23, 2, 2, 2, 24, 2, 2, 2], [25, 2, 2, 2, 2, 2, 2, 2], [26, 12, 2, 2, 2, 2, 2, 2], [27, 2, 2, 2, 2, 2, 2, 2], [28, 14, 2, 2, 2, 2, 2, 2], [29, 2, 2, 2, 15, 2, 2, 2], [30, 2, 16, 2, 2, 2, 2, 2], [31, 2, 16, 2, 15, 2, 17, 2], [23, 2, 19, 2, 2, 2, 2, 2], [32, 2, 19, 2, 2, 2, 2, 2], [33, 2, 19, 2, 34, 2, 20, 2], [30, 2, 2, 2, 2, 2, 2, 2], [35, 2, 2, 2, 2, 2, 2, 2], [23, 2, 19, 2, 15, 2, 36, 2], [37, 2, 19, 2, 24, 2, 36, 2], [38, 2, 8, 2, 2, 2, 39, 2], [40, 2, 2, 2, 41, 2, 2, 2], [42, 2, 8, 2, 2, 2, 9, 2], [23, 2, 2, 2, 7, 2, 2, 2], [29, 2, 2, 2, 2, 2, 2, 2], [30, 2, 2, 2, 43, 2, 2, 2], [44, 2, 2, 2, 2, 2, 2, 2], [32, 2, 2, 2, 43, 2, 2, 2], [45, 2, 2, 2, 2, 2, 2, 2], [46, 2, 2, 2, 34, 2, 2, 2], [47, 2, 2, 2, 34, 2, 2, 2], [48, 2, 19, 2, 15, 2, 36, 2], [23, 2, 19, 2, 2, 2, 2, 2], [38, 2, 8, 2, 43, 2, 39, 2], [21, 2, 8, 2, 2, 2, 39, 2], [40, 2, 19, 2, 43, 2, 49, 2], [50, 2, 19, 2, 41, 2, 49, 2], [51, 2, 8, 2, 34, 2, 9, 2], [52, 2, 2, 2, 43, 2, 2, 2], [44, 2, 2, 2, 15, 2, 2, 2], [45, 2, 2, 2, 34, 2, 2, 2], [29, 2, 2, 2, 2, 2, 2, 2], [47, 2, 2, 2, 34, 2, 2, 2], [53, 2, 2, 2, 2, 2, 2, 2], [54, 2, 19, 2, 43, 2, 49, 2], [40, 2, 19, 2, 2, 2, 2, 2], [51, 2, 8, 2, 15, 2, 9, 2], [52, 2, 2, 2, 2, 2, 2, 2], [53, 2, 2, 2, 15, 2, 2, 2], [32, 2, 2, 2, 2, 2, 2, 2]]

def M (i : ℕ) : ℕ := masks.getD i 0

def sg (i c : ℕ) : ℕ := (sgT.getD i []).getD c 0

theorem check_sg : ∀ i, i < 55 → ∀ c, c < 8 → sg i c < 55 := by decide

theorem check_dm : ∀ i, i < 55 → ∀ c, c < 8 → dm (M i) c = M (sg i c) := by decide +kernel

/-- The set of states with mask number i. -/
def S (i : ℕ) (q : St) : Prop := (M i).testBit (enc q) = true

theorem delta_eq (i : ℕ) (hi : i < 55) (b : Ltr) :
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

theorem cnt_succ (m i : ℕ) (hi : i < 55) : cnt (m + 1) i = ∑ b : Ltr, cnt m (sg i (encB b)) := by
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
  [[1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [4, 4, 0, 2, 3, 4, 4, 4, 2, 3, 2, 1, 2, 1, 2, 2, 2, 4, 2, 2, 4, 1, 1, 4, 4, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 2, 4, 2, 4, 3, 4, 4, 4, 2, 2, 2, 1, 2, 1, 4, 2, 4, 1, 2, 1],
   [13, 13, 0, 4, 6, 10, 12, 12, 3, 6, 8, 3, 4, 3, 4, 3, 4, 9, 6, 4, 9, 2, 2, 12, 12, 9, 8, 9, 8, 1, 4, 2, 4, 2, 3, 4, 9, 6, 11, 6, 12, 12, 11, 3, 4, 4, 1, 4, 2, 9, 6, 11, 1, 4, 2],
   [33, 33, 0, 12, 13, 23, 28, 31, 5, 11, 24, 9, 12, 9, 12, 4, 8, 18, 16, 8, 18, 4, 4, 28, 31, 20, 24, 20, 24, 1, 7, 4, 7, 4, 4, 7, 18, 16, 23, 11, 28, 31, 23, 4, 7, 7, 1, 7, 4, 18, 16, 23, 1, 7, 4],
   [81, 75, 0, 36, 34, 57, 58, 73, 9, 20, 59, 20, 36, 20, 36, 5, 15, 34, 36, 15, 34, 7, 7, 58, 73, 39, 59, 39, 59, 1, 11, 7, 11, 7, 5, 11, 34, 36, 43, 20, 58, 73, 43, 5, 11, 11, 1, 11, 7, 34, 36, 43, 1, 11, 7],
   [202, 160, 0, 95, 90, 147, 112, 158, 16, 36, 131, 39, 95, 39, 95, 6, 26, 61, 73, 26, 61, 11, 11, 112, 158, 72, 131, 72, 131, 1, 16, 11, 16, 11, 6, 16, 61, 73, 77, 36, 112, 158, 77, 6, 16, 16, 1, 16, 11, 61, 73, 77, 1, 16, 11],
   [492, 322, 0, 226, 224, 371, 205, 318, 27, 63, 270, 72, 226, 72, 226, 7, 42, 104, 138, 42, 104, 16, 16, 205, 318, 129, 270, 129, 270, 1, 22, 16, 22, 16, 7, 22, 104, 138, 135, 63, 205, 318, 135, 7, 22, 22, 1, 22, 16, 104, 138, 135, 1, 22, 16],
   [1143, 613, 0, 496, 522, 893, 358, 602, 43, 106, 523, 129, 496, 129, 496, 8, 64, 169, 247, 64, 169, 22, 22, 358, 602, 225, 523, 225, 523, 1, 29, 22, 29, 22, 8, 29, 169, 247, 232, 106, 358, 602, 232, 8, 29, 29, 1, 29, 22, 169, 247, 232, 1, 29, 22],
   [2524, 1109, 0, 1019, 1147, 2040, 599, 1082, 65, 171, 960, 225, 1019, 225, 1019, 9, 93, 263, 422, 93, 263, 29, 29, 599, 1082, 381, 960, 381, 960, 1, 37, 29, 37, 29, 9, 37, 263, 422, 389, 171, 599, 1082, 389, 9, 37, 37, 1, 37, 29, 263, 422, 389, 1, 37, 29],
   [5315, 1917, 0, 1979, 2391, 4431, 964, 1860, 94, 265, 1681, 381, 1979, 381, 1979, 10, 130, 394, 692, 130, 394, 37, 37, 964, 1860, 625, 1681, 625, 1681, 1, 46, 37, 46, 37, 10, 46, 394, 692, 634, 265, 964, 1860, 634, 10, 46, 46, 1, 46, 37, 394, 692, 634, 1, 46, 37],
   [10718, 3183, 0, 3660, 4751, 9182, 1498, 3076, 131, 396, 2824, 625, 3660, 625, 3660, 11, 176, 571, 1094, 176, 571, 46, 46, 1498, 3076, 993, 2824, 993, 2824, 1, 56, 46, 56, 46, 11, 56, 571, 1094, 1003, 396, 1498, 3076, 1003, 11, 56, 56, 1, 56, 46, 571, 1094, 1003, 1, 56, 46],
   [20776, 5101, 0, 6484, 9036, 18218, 2256, 4917, 177, 573, 4574, 993, 6484, 993, 6484, 12, 232, 804, 1674, 232, 804, 56, 56, 2256, 4917, 1530, 4574, 1530, 4574, 1, 67, 56, 67, 56, 12, 67, 804, 1674, 1541, 573, 2256, 4917, 1541, 12, 67, 67, 1, 67, 56, 804, 1674, 1541, 1, 67, 56],
   [38839, 7923, 0, 11058, 16513, 34731, 3304, 7627, 233, 806, 7173, 1530, 11058, 1530, 11058, 13, 299, 1104, 2488, 299, 1104, 67, 67, 3304, 7627, 2291, 7173, 2291, 7173, 1, 79, 67, 79, 67, 13, 79, 1104, 2488, 2303, 806, 3304, 7627, 2303, 13, 79, 79, 1, 79, 67, 1104, 2488, 2303, 1, 79, 67],
   [70225, 11970, 0, 18231, 29101, 63832, 4720, 11518, 300, 1106, 10931, 2291, 18231, 2291, 18231, 14, 378, 1483, 3603, 378, 1483, 79, 79, 4720, 11518, 3342, 10931, 3342, 10931, 1, 92, 79, 92, 79, 14, 92, 1483, 3603, 3355, 1106, 4720, 11518, 3355, 14, 92, 92, 1, 92, 79, 1483, 3603, 3355, 1, 92, 79]]

def look (m i : ℕ) : ℕ := (tb.getD m []).getD i 0

def CT (m : ℕ) : Prop := ∀ i, i < 55 → cnt m i = look m i

theorem ex_iff (i : ℕ) : (∃ q, S i q) ↔ ∃ t, t < 128 ∧ (M i).testBit t = true := by
  constructor
  · rintro ⟨q, hq⟩; exact ⟨enc q, enc_lt q, hq⟩
  · rintro ⟨t, ht, h⟩
    refine ⟨dec t, ?_⟩
    unfold S
    rwa [enc_dec t ht]

theorem ct0_check : ∀ i, i < 55 → ((∃ t, t < 128 ∧ (M i).testBit t = true) ↔ look 0 i = 1) := by decide +kernel

theorem look0 : ∀ i, i < 55 → look 0 i ≤ 1 := by decide

theorem CT0 : CT 0 := by
  intro i hi
  unfold cnt
  rw [W_zero]
  split_ifs with h
  · exact ((ct0_check i hi).1 ((ex_iff i).1 h)).symm
  · have h1 : look 0 i ≠ 1 := fun h1 => h ((ex_iff i).2 ((ct0_check i hi).2 h1))
    have := look0 i hi
    omega

theorem tstep (m : ℕ) (hm : ∀ i, i < 55 → look (m + 1) i = ∑ b0 : Fin 2, ∑ b1 : Fin 2, ∑ b2 : Fin 2, look m (sg i (encB ![b0, b1, b2])))
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

theorem rec_base : ∀ i, i < 55 → look 13 i + 45 * look 11 i + 210 * look 9 i + 210 * look 7 i + 45 * look 5 i + look 3 i = 10 * look 12 i + 120 * look 10 i + 252 * look 8 i + 120 * look 6 i + 10 * look 4 i := by decide +kernel

theorem crec (m : ℕ) : ∀ i, i < 55 → cnt (m + 13) i + 45 * cnt (m + 11) i + 210 * cnt (m + 9) i + 210 * cnt (m + 7) i + 45 * cnt (m + 5) i + cnt (m + 3) i = 10 * cnt (m + 12) i + 120 * cnt (m + 10) i + 252 * cnt (m + 8) i + 120 * cnt (m + 6) i + 10 * cnt (m + 4) i := by
  induction m with
  | zero =>
    intro i hi
    simp only [Nat.zero_add]
    rw [CT3 i hi, CT4 i hi, CT5 i hi, CT6 i hi, CT7 i hi, CT8 i hi, CT9 i hi, CT10 i hi, CT11 i hi, CT12 i hi, CT13 i hi]
    exact rec_base i hi
  | succ m ih =>
    intro i hi
    rw [show m + 1 + 3 = m + 3 + 1 from by omega, show m + 1 + 4 = m + 4 + 1 from by omega, show m + 1 + 5 = m + 5 + 1 from by omega, show m + 1 + 6 = m + 6 + 1 from by omega, show m + 1 + 7 = m + 7 + 1 from by omega, show m + 1 + 8 = m + 8 + 1 from by omega, show m + 1 + 9 = m + 9 + 1 from by omega, show m + 1 + 10 = m + 10 + 1 from by omega, show m + 1 + 11 = m + 11 + 1 from by omega, show m + 1 + 12 = m + 12 + 1 from by omega, show m + 1 + 13 = m + 13 + 1 from by omega]
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

theorem val2 : a 2 = 13 := by rw [a_cnt, CT2 0 (by norm_num)]; rfl

theorem val3 : a 3 = 33 := by rw [a_cnt, CT3 0 (by norm_num)]; rfl

theorem val4 : a 4 = 81 := by rw [a_cnt, CT4 0 (by norm_num)]; rfl

theorem val5 : a 5 = 202 := by rw [a_cnt, CT5 0 (by norm_num)]; rfl

theorem val6 : a 6 = 492 := by rw [a_cnt, CT6 0 (by norm_num)]; rfl

theorem val7 : a 7 = 1143 := by rw [a_cnt, CT7 0 (by norm_num)]; rfl

theorem val8 : a 8 = 2524 := by rw [a_cnt, CT8 0 (by norm_num)]; rfl

theorem val9 : a 9 = 5315 := by rw [a_cnt, CT9 0 (by norm_num)]; rfl

theorem val10 : a 10 = 10718 := by rw [a_cnt, CT10 0 (by norm_num)]; rfl

theorem val11 : a 11 = 20776 := by rw [a_cnt, CT11 0 (by norm_num)]; rfl

theorem val12 : a 12 = 38839 := by rw [a_cnt, CT12 0 (by norm_num)]; rfl

theorem val13 : a 13 = 70225 := by rw [a_cnt, CT13 0 (by norm_num)]; rfl

theorem recurrence (n : ℕ) (hn : 12 < n) : (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  rcases Nat.lt_or_ge n 13 with h | h
  · omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
    have hc := crec m 0 (by norm_num)
    simp only [show m + 13 - 1 = m + 12 from by omega, show m + 13 - 2 = m + 11 from by omega, show m + 13 - 3 = m + 10 from by omega, show m + 13 - 4 = m + 9 from by omega, show m + 13 - 5 = m + 8 from by omega, show m + 13 - 6 = m + 7 from by omega, show m + 13 - 7 = m + 6 from by omega, show m + 13 - 8 = m + 5 from by omega, show m + 13 - 9 = m + 4 from by omega, show m + 13 - 10 = m + 3 from by omega, a_cnt]
    have hz := congrArg (Nat.cast : ℕ → ℤ) hc
    push_cast at hz
    linarith

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
    X * (4 - 27 * X + 83 * X ^ 2 - 144 * X ^ 3 + 157 * X ^ 4 - 121 * X ^ 5 + 87 * X ^ 6 - 62 * X ^ 7 + 28 * X ^ 8 - X ^ 9 - 4 * X ^ 10 + X ^ 11) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 10 = A - C 10 * (A * X ^ 1) + C 45 * (A * X ^ 2) - C 120 * (A * X ^ 3) + C 210 * (A * X ^ 4) - C 252 * (A * X ^ 5) + C 210 * (A * X ^ 6) - C 120 * (A * X ^ 7) + C 45 * (A * X ^ 8) - C 10 * (A * X ^ 9) + (A * X ^ 10) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (4 - 27 * X + 83 * X ^ 2 - 144 * X ^ 3 + 157 * X ^ 4 - 121 * X ^ 5 + 87 * X ^ 6 - 62 * X ^ 7 + 28 * X ^ 8 - X ^ 9 - 4 * X ^ 10 + X ^ 11) : ℤ⟦X⟧) = X ^ 1 * C 4 - X ^ 2 * C 27 + X ^ 3 * C 83 - X ^ 4 * C 144 + X ^ 5 * C 157 - X ^ 6 * C 121 + X ^ 7 * C 87 - X ^ 8 * C 62 + X ^ 9 * C 28 - X ^ 10 * C 1 - X ^ 11 * C 4 + X ^ 12 * C 1 := by
    simp only [map_ofNat, map_one]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 13 with hn | hn
  · interval_cases n <;> simp [val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 13 := ⟨n - 13, by omega⟩
    have hr := recurrence (q + 13) (by omega)
    simp only [show q + 13 - 1 = q + 12 by omega, show q + 13 - 2 = q + 11 by omega, show q + 13 - 3 = q + 10 by omega, show q + 13 - 4 = q + 9 by omega, show q + 13 - 5 = q + 8 by omega, show q + 13 - 6 = q + 7 by omega, show q + 13 - 7 = q + 6 by omega, show q + 13 - 8 = q + 5 by omega, show q + 13 - 9 = q + 4 by omega, show q + 13 - 10 = q + 3 by omega] at hr ⊢
    simp only [show ¬ q + 13 = 0 by omega, show ¬ q + 12 = 0 by omega, show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega, show 1 ≤ q + 13 by omega, show 2 ≤ q + 13 by omega, show 3 ≤ q + 13 by omega, show 4 ≤ q + 13 by omega, show 5 ≤ q + 13 by omega, show 6 ≤ q + 13 by omega, show 7 ≤ q + 13 by omega, show 8 ≤ q + 13 by omega, show 9 ≤ q + 13 by omega, show 10 ≤ q + 13 by omega, show ¬ q + 13 = 0 by omega, show ¬ q + 13 = 1 by omega, show ¬ q + 13 = 2 by omega, show ¬ q + 13 = 3 by omega, show ¬ q + 13 = 4 by omega, show ¬ q + 13 = 5 by omega, show ¬ q + 13 = 6 by omega, show ¬ q + 13 = 7 by omega, show ¬ q + 13 = 8 by omega, show ¬ q + 13 = 9 by omega, show ¬ q + 13 = 10 by omega, show ¬ q + 13 = 11 by omega, show ¬ q + 13 = 12 by omega, if_true, if_false]
    rw [hr]
    ring

theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
    X * (4 - 27 * X + 83 * X ^ 2 - 144 * X ^ 3 + 157 * X ^ 4 - 121 * X ^ 5 + 87 * X ^ 6 - 62 * X ^ 7 + 28 * X ^ 8 - X ^ 9 - 4 * X ^ 10 + X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a227122

theorem OMA.solution : type_of% @OMA.S_oeis_a227122.main :=
  OMA.S_oeis_a227122.conjecture
